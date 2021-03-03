/* 
 * Simple, 32-bit and 64-bit clean allocator based on implicit free
 * lists, first-fit placement, and boundary tag coalescing, as described
 * in the CS:APP3e text. Blocks must be aligned to doubleword (8 byte) 
 * boundaries. Minimum block size is 16 bytes. 
 * 
 * Finished by Sizhe Li, 1900013061
 * 
 * In this program, we insert blocks into 11 different linked lists by size.
 * In addition to the smallest linked list, we use bidirectional linked list
 * to organize the other lists. Here's a detail that the tail block doesn't
 * have a prev ptr.
 * We insert all the 11 tails into the prologue block, so the size of the
 * prologue equals to 24 words.
 * 
 * We coalesce the free blocks at once. And we use the add and delete function
 * to manipulate the list.
 * The add operation happens when we extend the heap, coalesce the blocks, free
 * a block or place a block. The remove operation happens when we coalesce the
 * blocks, malloc a new space or place a block.
 * 
 * To find the best place to insert the free block, we find the free list of
 * the smallest available size, then we look through it. If no block in this
 * list meets the need, we then look through next list.
 * In the first 9 list, we use first-fit search, while in the last 2 lists, we
 * use best-fit search.
 * 
 */
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include "mm.h"
#include "memlib.h"

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */ 
#define DSIZE       8       /* Double word size (bytes) */
#define CHUNKSIZE  (1<<9)  /* Extend heap by this amount (bytes) */ 

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc)) 

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))            
#define PUT(p, val)  (*(unsigned int *)(p) = (val))    

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)                   
#define GET_ALLOC(p) (GET(p) & 0x1)                    

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)                      
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) 

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) 
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) 

/* Given a ptr to find the previous/next block in the free block */
#define GET_PRED_PTR(bp)    (*(char**)((bp) + DSIZE))
#define GET_NEXT_PTR(bp)    (*(char**)(bp))

/* Set the previous/next block in the free block */
#define PUT_PRED_PTR(bp, newptr)   (GET_PRED_PTR(bp) = newptr)
#define PUT_NEXT_PTR(bp, newptr)   (GET_NEXT_PTR(bp) = newptr)


/* Global variables */
static char *heap_listp = 0;  /* Pointer to first block */

/* some other ptrs in the heap, pointint to the start of each free block */
static char *free_list_head_16, *free_list_head_32, *free_list_head_64;
static char *free_list_head_128, *free_list_head_256, *free_list_head_512;
static char *free_list_head_1024, *free_list_head_2048, *free_list_head_4096;
static char *free_list_head_8192, *free_list_head_max;


/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void *place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void add_to_free_list(void* bp);
static void remove_frome_free_list(void* bp);
static void print_each_block();
static void print_free_block();
static void* find_list_tail(size_t size);
static void* find_list_head(size_t size);
static void set_list_head(size_t size, void* newptr);

#define DEBUGx

/* The following 2 functions are used to check the heap or the free list */
static void print_each_block(int lineno)
{
    void *bp = heap_listp;
    if(GET_SIZE(HDRP(bp)) % 8 != 0)
    {
        if(lineno)
            printf("the prologue not aligns to DSIZE!\n");
        exit(0);
    }
            
    for (; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) 
    {
        if(GET_SIZE(HDRP(bp)) != GET_SIZE(FTRP(bp)))
        {
            if(lineno)
                printf("the header and foot not matches\n");
            exit(0);
        }
        if(lineno)
            printf("address: %p, size: %x, alloc: %d\n", 
                bp, GET_SIZE(HDRP(bp)), GET_ALLOC(HDRP(bp)));
    }

    if(!GET_ALLOC(HDRP(bp)) || GET_SIZE(HDRP(bp)))
    {
        if(lineno)
            printf("the epilogue is invalid\n");
        exit(0);
    }
}
static void print_free_block(int lineno)
{
    char *free_list_tail = heap_listp;
    int cnt = 16;
    for(;free_list_tail != heap_listp + 11 * DSIZE; free_list_tail += DSIZE)
    {
        if(lineno)
        {
            if(cnt !=16384)
                printf("FREE LIST BELOW %x\n", cnt);
            else printf("FREE LIST OVER 1000\n");
        }
        
        cnt *= 2;
        void *bp = free_list_tail;
        if(!GET_NEXT_PTR(bp))
            continue;
        do
        {
            bp = GET_NEXT_PTR(bp);
            if(lineno)
            {
                printf("address: %p, size: %x, alloc: %d\n", 
                    bp, GET_SIZE(HDRP(bp)), GET_ALLOC(HDRP(bp)));
                printf("next address: %p\n", GET_NEXT_PTR(bp));
            }            
        }while(GET_NEXT_PTR(bp));
    }
    
}

/* to find the tail of the selected list in the heap */
static void* find_list_tail(size_t size)
{
    if(size <= 16)
        return heap_listp;
    if(size <= 32)
        return heap_listp + DSIZE;
    if(size <= 64)
        return heap_listp + DSIZE * 2;
    if(size <= 128)
        return heap_listp + DSIZE * 3;
    if(size <= 256)
        return heap_listp + DSIZE * 4;
    if(size <= 512)
        return heap_listp + DSIZE * 5;
    if(size <= 1024)
        return heap_listp + DSIZE * 6;
    if(size <= 2048)
        return heap_listp + DSIZE * 7;
    if(size <= 4096)
        return heap_listp + DSIZE * 8;
    if(size <= 8192)
        return heap_listp + DSIZE * 9;
    return heap_listp + DSIZE * 10;
}

/* to find the head of the selected list */
static void* find_list_head(size_t size)
{
    if(size <= 16)
        return free_list_head_16;
    if(size <= 32)
        return free_list_head_32;
    if(size <= 64)
        return free_list_head_64;
    if(size <= 128)
        return free_list_head_128;
    if(size <= 256)
        return free_list_head_256;
    if(size <= 512)
        return free_list_head_512;
    if(size <= 1024)
        return free_list_head_1024;
    if(size <= 2048)
        return free_list_head_2048;
    if(size <= 4096)
        return free_list_head_4096;
    if(size <= 8192)
        return free_list_head_8192;
    return free_list_head_max;
}

/* to set the head of the selected list */
static void set_list_head(size_t size, void* newptr)
{
    if(size <= 16)
        free_list_head_16 = newptr;
    else if(size <= 32)
        free_list_head_32 = newptr;
    else if(size <= 64)
        free_list_head_64 =newptr;
    else if(size <= 128)
        free_list_head_128 = newptr;
    else if(size <= 256)
        free_list_head_256 = newptr;
    else if(size <= 512)
        free_list_head_512 = newptr;
    else if(size <= 1024)
        free_list_head_1024 = newptr;
    else if(size <= 2048)
        free_list_head_2048 = newptr;
    else if(size <= 4096)
        free_list_head_4096 = newptr;
    else if(size <= 8192)
        free_list_head_8192 = newptr;
    else free_list_head_max = newptr;
}

/* 
 * mm_init - Initialize the memory manager
 * There are a header, a footer and 11 ptrs in the prologue block, whose siz
 * is 24 words. The 11 ptrs each points to the first block of the list.
 */
int mm_init(void) 
{
#ifdef DEBUG
    printf(" ********** init begin! **********\n");
#endif
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(26*WSIZE)) == (void *)-1) 
        return -1;
    PUT(heap_listp, 0);                          /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE * 12, 1)); /* Prologue header */ 
    PUT(heap_listp + (24*WSIZE), PACK(DSIZE * 12, 1)); /* Prologue footer */ 
    PUT(heap_listp + (25*WSIZE), PACK(0, 1));     /* Epilogue header */
    heap_listp += (2*WSIZE);

    /* the 11 ptrs */
    PUT_NEXT_PTR(heap_listp, NULL); 
    PUT_NEXT_PTR(heap_listp + DSIZE, NULL);     
    PUT_NEXT_PTR(heap_listp + DSIZE * 2, NULL);   
    PUT_NEXT_PTR(heap_listp + DSIZE * 3, NULL);
    PUT_NEXT_PTR(heap_listp + DSIZE * 4, NULL);
    PUT_NEXT_PTR(heap_listp + DSIZE * 5, NULL);   
    PUT_NEXT_PTR(heap_listp + DSIZE * 6, NULL);   
    PUT_NEXT_PTR(heap_listp + DSIZE * 7, NULL);
    PUT_NEXT_PTR(heap_listp + DSIZE * 8, NULL); 
    PUT_NEXT_PTR(heap_listp + DSIZE * 9, NULL); 
    PUT_NEXT_PTR(heap_listp + DSIZE * 10, NULL); 

    /* At begin, each list is empty, and the head equals to the tail */
    free_list_head_16 = heap_listp; 
    free_list_head_32 = heap_listp + DSIZE; 
    free_list_head_64 = heap_listp + DSIZE * 2; 
    free_list_head_128 = heap_listp + DSIZE * 3;
    free_list_head_256 = heap_listp + DSIZE * 4;
    free_list_head_512 = heap_listp + DSIZE * 5;
    free_list_head_1024 = heap_listp + DSIZE * 6;
    free_list_head_2048 = heap_listp + DSIZE * 7;
    free_list_head_4096 = heap_listp + DSIZE * 8;
    free_list_head_8192 = heap_listp + DSIZE * 9;
    free_list_head_max = heap_listp + DSIZE * 10;   

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) 
        return -1;
    
    return 0;
}

/* 
 * malloc - Allocate a block with at least size bytes of payload 
 */
void *malloc(size_t size) 
{
#ifdef DEBUG
    printf(" ********** malloc begin! **********\n");
    printf(" ********** size = %x **************\n", size);
    printf("############### ALL BLOCKS ##############\n");
    print_each_block();
    printf("############### FREE BLOCKS ##############\n");
    print_free_block();
#endif
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;      

    if (heap_listp == 0){
        mm_init();
    }
    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)                                          
        asize = 2*DSIZE;                                        
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE); 

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {  
//        place(bp, asize);                  
//        return bp;
        return place(bp, asize);
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);                 
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)  
        return NULL;                                  
                                     
    return place(bp, asize);
} 

/* 
 * free - Free a block 
 */
void free(void *bp)
{
#ifdef DEBUG
    printf("ptr ro free: %p\n", bp);
    printf(" ********** free begin! **********\n");
    printf("################ print_each_block ################\n");
    print_each_block();
    printf("################ print_free_block ################\n");
    print_free_block();
    
#endif
    if (bp == 0) 
        return;

    size_t size = GET_SIZE(HDRP(bp));
    if (heap_listp == 0){
        mm_init();
    }

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    add_to_free_list(bp);
    coalesce(bp);
}

/*
 * realloc - Naive implementation of realloc
 * Firstly, we check if the old block is big enough.
 * If so, we directly allocate its space to the new block.
 * Otherwise, we check if the next block is empty.
 * If so, we coalesce these blocks and repeat the steps.
 * Otherwise, we malloc a new space.
 */
void *realloc(void *ptr, size_t size)
{
#ifdef DEBUG
    printf(" ********** realloc begin! **********\n");
    
#endif
    size_t oldsize;
    void *newptr;

    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0) {
        mm_free(ptr);
        return 0;
    }

    /* If oldptr is NULL, then this is just malloc. */
    if(ptr == NULL) {
        return mm_malloc(size);
    }

    /* Copy the old data. */
    oldsize = GET_SIZE(HDRP(ptr));
    size_t asize;
    if (size <= DSIZE)                                          
        asize = 2*DSIZE;                                        
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    /* the old block can be separated to a new block and a new free block. */
    if(oldsize >= asize + 2 * DSIZE) 
    {
        PUT(HDRP(ptr), PACK(asize, 1));
        PUT(FTRP(ptr), PACK(asize, 1));
        PUT(HDRP(NEXT_BLKP(ptr)), PACK(oldsize - asize, 1));
        PUT(FTRP(NEXT_BLKP(ptr)), PACK(oldsize - asize, 1));
        free(NEXT_BLKP(ptr));
        return ptr;
    }

    /*  the old block is not big enough to contain a new allocated block 
     *  and a minimal free block.                                           */
    else if(oldsize >= asize)
    {
        return ptr;
    }

    /* the next block of the old block is empty */
    else if(!GET_ALLOC(HDRP(NEXT_BLKP(ptr))))
    {
        size_t nowsize = oldsize + GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        /* After coalescing, the new block is big enough to contain
           a free block and an allocated block */
        if(nowsize >= asize + 2 * DSIZE) 
        {
            remove_frome_free_list(NEXT_BLKP(ptr));
            PUT(HDRP(ptr), PACK(asize, 1));
            PUT(FTRP(ptr), PACK(asize, 1));
            PUT(HDRP(NEXT_BLKP(ptr)), PACK(nowsize - asize, 0));
            PUT(FTRP(NEXT_BLKP(ptr)), PACK(nowsize - asize, 0));
            add_to_free_list(NEXT_BLKP(ptr));
            return ptr;
        }
        else if(nowsize >= asize)
        {
            remove_frome_free_list(NEXT_BLKP(ptr));
            PUT(HDRP(ptr), PACK(nowsize, 1));
            PUT(FTRP(ptr), PACK(nowsize, 1));
            return ptr;
        }
    }

    newptr = mm_malloc(asize);

    /* If realloc() fails the original block is left untouched  */
    if(!newptr) {
        return 0;
    }
    memcpy(newptr, ptr, oldsize);

    /* Free the old block. */
    mm_free(ptr);

    return newptr;
}

/*
 * calloc - Allocate the block and set it to zero.
 */
void *calloc (size_t nmemb, size_t size)
{
    size_t bytes = nmemb * size;
    void *newptr;

    newptr = malloc(bytes);
    memset(newptr, 0, bytes);

    return newptr;
}

/* 
 * mm_checkheap - Check the heap for correctness. Helpful hint: You
 *                can call this function using mm_checkheap(__LINE__);
 *                to identify the line number of the call site.
 * we print the heap and list to debug.
 */
void mm_checkheap(int lineno)  
{ 
    print_each_block(lineno); // check the heap
    print_free_block(lineno); // check the list
}

/* 
 * The remaining routines are internal helper routines 
 */

/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
static void *extend_heap(size_t words) 
{
#ifdef DEBUG
    printf(" ********** extend begin! **********\n");
#endif
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; 
    if ((long)(bp = mem_sbrk(size)) == -1)  
        return NULL;                                        

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */   
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */   
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */ 
#ifdef DEBUG
    printf("in function extend\n");
    printf("size: %x\n", GET_SIZE(HDRP(bp)));
    printf("bp: %p\n", bp);
#endif
    add_to_free_list(bp);

    /* Coalesce if the previous block was free */
    return coalesce(bp);                                          
}

/* remove a block from the free list
 * pay attention that only the smallest free list is a one-way list. */
static void remove_frome_free_list(void* bp)
{
    /* find the tail of the selected list */
    char* free_list_tail = find_list_tail(GET_SIZE(HDRP(bp)));

#ifdef DEBUG
    printf("\n ********** remove begin! **********\n");
    printf("pointer to remove: %p\n", bp);
    
    printf("its next ptr is %p\n", GET_NEXT_PTR(bp));
#endif
    /* if not the smallest list */    
    if(GET_SIZE(HDRP(bp)) > 16)
    {
        /* we want to remove the head of this list */
        if(GET_NEXT_PTR(bp) == NULL)
        {
            set_list_head(GET_SIZE(HDRP(bp)), GET_PRED_PTR(bp));
            PUT_NEXT_PTR(find_list_head(GET_SIZE(HDRP(bp))), NULL);
        }
        else
        {
            PUT_NEXT_PTR(GET_PRED_PTR(bp), GET_NEXT_PTR(bp));
            PUT_PRED_PTR(GET_NEXT_PTR(bp), GET_PRED_PTR(bp));
        }
    }
    /* the smallest list which is a one-way list */
    else
    {
        void* bp_pred;
        /* we ergodic the list to find the previous ptr */
        for(bp_pred = free_list_tail; GET_NEXT_PTR(bp_pred) != bp; bp_pred = GET_NEXT_PTR(bp_pred));

        /* we want to remove the head of this list */
        if(GET_NEXT_PTR(bp) == NULL)
        {
            set_list_head(GET_SIZE(HDRP(bp)), bp_pred);
            PUT_NEXT_PTR(find_list_head(GET_SIZE(HDRP(bp))), NULL);
        }
        else
        {
            PUT_NEXT_PTR(bp_pred, GET_NEXT_PTR(bp));
        }
    }
#ifdef DEBUG
    printf("\n ********** remove finish! **********\n");
    printf("################ print_each_block ################\n");
    print_each_block();
    printf("################ print_free_block ################\n");
    print_free_block();
#endif
    return;
}

/* add a block to the free list, using FIFO
 * pay attention that only the smallest free list is a one-way list. */
static void add_to_free_list(void* bp)
{
#ifdef DEBUG
    printf("\n ********** add begin! **********\n");
    printf("################ print_each_block ################\n");
    print_each_block();
    printf("################ print_free_block ################\n");
    print_free_block();

    printf("ready to add!\n");
    printf("bp address: %p\n", bp);
    printf("size: %lx\n", GET_SIZE(HDRP(bp)));
#endif
    void* free_list_head = find_list_head(GET_SIZE(HDRP(bp)));
    /* If it is a Bidirectional list, we need to set both prev and next ptr */
    if(GET_SIZE(HDRP(bp)) > 16)
    {
        PUT_NEXT_PTR(free_list_head, bp);
        PUT_PRED_PTR(bp, free_list_head);
        PUT_NEXT_PTR(bp, NULL);
        set_list_head(GET_SIZE(HDRP(bp)),bp);
    }
    else
    {
        PUT_NEXT_PTR(free_list_head, bp);
        PUT_NEXT_PTR(bp, NULL);
        set_list_head(GET_SIZE(HDRP(bp)),bp);
    }
    
    
#ifdef DEBUG
    printf("free_list_head: %p\n", free_list_head);
    printf("################ print_each_block ################\n");
    print_each_block();
    printf("################ print_free_block ################\n");
    print_free_block();

    printf(" ********** add finish! **********\n");
#endif
}

/*
 * coalesce - Boundary tag coalescing. Return ptr to coalesced block
 */
static void *coalesce(void *bp) 
{
#ifdef DEBUG
    printf(" ********** coalesce begin! **********\n");
    /*
    printf("######## FREE ########\n");
    print_free_block();
    printf("######## EACH ########\n");
    print_each_block();
    printf("bp: %p\n", bp);
    printf("PREV_BLKP(bp): %p\n", PREV_BLKP(bp));
    */
#endif
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {            /* Case 1 */
        return bp;
    }

    else if (prev_alloc && !next_alloc) {      /* Case 2 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        remove_frome_free_list(bp);
        remove_frome_free_list(NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size,0));
        add_to_free_list(bp);
    }

    else if (!prev_alloc && next_alloc) {      /* Case 3 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        remove_frome_free_list(PREV_BLKP(bp));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        remove_frome_free_list(bp);
        bp = PREV_BLKP(bp);
        add_to_free_list(bp);
    }

    else {                                     /* Case 4 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
            GET_SIZE(FTRP(NEXT_BLKP(bp)));
        remove_frome_free_list(PREV_BLKP(bp));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        remove_frome_free_list(NEXT_BLKP(bp));
        remove_frome_free_list(bp);
        bp = PREV_BLKP(bp);
        add_to_free_list(bp);
    }
    return bp;
}

/* 
 * place - Place block of asize bytes at start of free block bp 
 *         and split if remainder would be at least minimum block size
 */
static void* place(void *bp, size_t asize)
{
#ifdef DEBUG
    printf(" ********** place begin! **********\n");
#endif
    size_t csize = GET_SIZE(HDRP(bp));
//    printf("csize-asize: %x\n", csize-asize);

    if ((csize - asize) >= (2*DSIZE)) { 
        remove_frome_free_list(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
            
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        add_to_free_list(PREV_BLKP(bp)); 
        return bp;         
 #ifdef DEBUG
    printf("################ print_each_block ################\n");
    print_each_block();
    printf("################ print_free_block ################\n");
    print_free_block();
#endif           
        
    }
    else { 
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
        remove_frome_free_list(bp);
        return bp;
    }
}

/* 
 * find_fit - Find a fit for a block with asize bytes 
 * For the first 9 lists, we use first-fit. If found the first block,
 * then return. Otherwise, we continue to search the next list.
 * For the last 2 lists, we use best-fit. We look through the whole list
 * and find the best block.
 */
static void *find_fit(size_t asize)
{

#ifdef DEBUG
    printf(" ********** find_fit begin! **********\n");
    printf("need size: %lx\n", asize);
#endif

    /* First-fit search */
    void *bp;
    char* free_list_tail = find_list_tail(asize);
    for(;free_list_tail != heap_listp + 2 * DSIZE &&free_list_tail != heap_listp + 3 * DSIZE &&free_list_tail != heap_listp + 4 * DSIZE &&
    free_list_tail != heap_listp + 7 * DSIZE &&free_list_tail != heap_listp + 8 * DSIZE &&  free_list_tail != heap_listp + 9 * DSIZE && 
            free_list_tail != heap_listp + 5 * DSIZE &&free_list_tail != heap_listp + 6 * DSIZE &&free_list_tail != heap_listp + 10 * DSIZE; free_list_tail += DSIZE)
    {
        for(bp = GET_NEXT_PTR(free_list_tail); 
                bp != NULL; bp = GET_NEXT_PTR(bp))
        {
            if(asize <= GET_SIZE(HDRP(bp)))
            {
                return bp;
            }
        }
    }

    /* Best-fit search */
    void *bp_best = NULL;
    size_t t = (1 << 30);

    for(; free_list_tail != heap_listp + 11 * DSIZE; free_list_tail += DSIZE)
    {
        for(bp = GET_NEXT_PTR(free_list_tail); bp != NULL; bp = GET_NEXT_PTR(bp))
        {
            if(asize <= GET_SIZE(HDRP(bp)))
            {
                if(GET_SIZE(HDRP(bp)) <= t)
                {
                    t = GET_SIZE(HDRP(bp));
                    bp_best = bp;
                }
            }
        }
        /*If found in the smaller list, we do not need to check the next list*/
        if(bp_best)
            return bp_best; 
    }

    return NULL; /* No fit */
}

