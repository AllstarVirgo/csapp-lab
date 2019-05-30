/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

#define WSIZE     4
#define DSIZE     8

#define INITCHUNKSIZE (1<<6)
#define CHUNKSIZE (1<<12)

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define MIN(x, y) ((x) < (y) ? (x) : (y))

#define PACK(size, alloc) ((size) | (alloc))

/* 下面对指针所在的内存赋值时要注意类型转换，否则会有警告 */
#define GET(p)            (*(unsigned int *)(p))
#define PUT(p, val)       (*(unsigned int *)(p) = (val))

#define SET_PTR(p, ptr) (*(unsigned int *)(p) = (unsigned int)(ptr))

#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(ptr) ((char *)(ptr) - WSIZE)
#define FTRP(ptr) ((char *)(ptr) + GET_SIZE(HDRP(ptr)) - DSIZE)

#define NEXT_BLKP(ptr) ((char *)(ptr) + GET_SIZE((char *)(ptr) - WSIZE))
#define PREV_BLKP(ptr) ((char *)(ptr) - GET_SIZE((char *)(ptr) - DSIZE))

#define PRED_PTR(ptr) ((char *)(ptr))
#define SUCC_PTR(ptr) ((char *)(ptr) + WSIZE)

#define PRED(ptr) (*(char **)(ptr))
#define SUCC(ptr) (*(char **)(SUCC_PTR(ptr)))

static char *heap_listp;
static void *root;

static void *extend_heap(size_t size);
static void *coalesce(void *bp);
static void place(void *bp,size_t asize);
static void *find_fit(size_t asize);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if((heap_listp = mem_sbrk(4*WSIZE))==(void *)-1) 
        return -1;
    root = heap_listp;
    PUT(heap_listp,0);
    PUT(heap_listp+(1*WSIZE),PACK(DSIZE,1));
    PUT(heap_listp+(2*WSIZE),PACK(DSIZE,1));
    PUT(heap_listp+(3*WSIZE),PACK(0,1));
    heap_listp+=(2*WSIZE);

    if(extend_heap(CHUNKSIZE/WSIZE)==NULL)
        return -1;
    return 0;
}

static void *extend_heap(size_t words){
    char *bp;
    size_t size;

    size = (words%2)?(words+1)*WSIZE:words*WSIZE;
    if((long)(bp=mem_sbrk(size))==-1)
        return NULL;
    PUT(HDRP(bp),PACK(size,0));
    PUT(FTRP(bp),PACK(size,0));
    PUT(HDRP(NEXT_BLKP(bp)),PACK(0,1));
    if(GET(root)==0)
        /*root is 4 bytes sie*/
        PUT(root,(unsigned int)(bp));
    else{
        char * old_first = (char *)GET(root);        
        PUT(root,(unsigned int)(bp));
        PUT(SUCC_PTR(bp),(unsigned int)old_first);
        PUT(PRED_PTR(old_first),(unsigned int)(bp));
    }
   return coalesce(bp);
}

/*modify adjacent chunk,modify pointer of free list*/
static void *coalesce(void *bp){
    size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    if(prev_alloc&&next_alloc){
        SET_PTR(SUCC_PTR(bp),GET(root));
        SET_PTR(PRED_PTR(GET(root)),bp);
        SET_PTR(root,bp);
        return bp;
    }
    else if (!prev_alloc&&next_alloc){
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        /*modify bp's prev and succ list poniter*/
        char *pre_list_next = SUCC_PTR(PRED_PTR(PREV_BLKP(bp)));
        char *succ_list_prev = PRED_PTR(SUCC_PTR(PREV_BLKP(bp)));
        PUT(pre_list_next,(unsigned int)SUCC_PTR(bp));
        PUT(succ_list_prev,(unsigned int)PRED_PTR(bp));
        /*modify bp's pointer*/
        char *old_first = (char *)GET(root);
        PUT(FTRP(bp),PACK(size,0));
        PUT(HDRP(PREV_BLKP(bp)),PACK(size,0));
        PUT(SUCC_PTR(PREV_BLKP(bp)),(unsigned int)old_first);
        /*set pred_ptr of pre'bp to NULL*/ 
        SET_PTR(PRED_PTR(PREV_BLKP(bp)),0);
        PUT(PRED_PTR(old_first),(unsigned int)(PREV_BLKP(bp)));
        PUT(root,(unsigned int)(PREV_BLKP(bp)));
        /*set bp's prev and succ to zero*/
        PUT(PRED_PTR(bp),0);
        PUT(SUCC_PTR(bp),0);
    }else if(prev_alloc&&!next_alloc){
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        /*modify bp's prev and succ list pointer*/
        char *pre_list_next = SUCC_PTR(PRED_PTR(NEXT_BLKP(bp)));
        char *succ_list_prev = PRED_PTR(SUCC_PTR(bp));
        PUT(pre_list_next,(unsigned int)SUCC_PTR(bp));
        PUT(succ_list_prev,(unsigned int)PRED_PTR(bp));
        /*modify bp's pointer*/
        PUT(HDRP(bp),PACK(size,0));
        PUT(FTRP(NEXT_BLKP(bp)),PACK(size,0));
        SET_PTR(SUCC_PTR(bp),GET(root));
        SET_PTR(PRED_PTR(GET(root)),bp);
        SET_PTR(PRED_PTR(NEXT_BLKP(bp)),0);
        PUT(root,(unsigned int)bp);
    }else{
        size += GET_SIZE(HDRP(PREV_BLKP(bp)))+GET_SIZE(FTRP(NEXT_BLKP(bp)));        
        /*modify two bp's prev and succ list pointer*/
        /*modify bp's adjacent chunk poninter*/
        char *pre_list_next = SUCC_PTR(PRED_PTR(PREV_BLKP(bp)));
        char *succ_list_prev = PRED_PTR(SUCC_PTR(PREV_BLKP(bp)));
        PUT(pre_list_next,(unsigned int)SUCC_PTR(bp));
        PUT(succ_list_prev,(unsigned int)PRED_PTR(bp));

        pre_list_next = SUCC_PTR(PRED_PTR(NEXT_BLKP(bp)));
        succ_list_prev = PRED_PTR(SUCC_PTR(bp));
        PUT(pre_list_next,(unsigned int)SUCC_PTR(bp));
        PUT(succ_list_prev,(unsigned int)PRED_PTR(bp));

        PUT(HDRP(PREV_BLKP(bp)),PACK(size,0));
        PUT(FTRP(NEXT_BLKP(bp)),PACK(size,0));
        SET_PTR(SUCC_PTR(bp),GET(root));
        SET_PTR(PRED_PTR(GET(root)),bp);
        SET_PTR(PRED_PTR(NEXT_BLKP(bp)),0);
        SET_PTR(PRED_PTR(PREV_BLKP(bp)),0);
        PUT(root,(unsigned int)bp);
    }
    return bp;
}
/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t extendsize;
    char* bp;
    if(size == 0)
        return NULL;
    int newsize = ALIGN(size);
    if((bp=find_fit(newsize))!=NULL){
        place(bp,newsize);
        return bp;
    }

    extendsize = MAX(newsize,CHUNKSIZE);
    if((bp=extend_heap(extendsize/WSIZE))==NULL)
        return NULL;
    place(bp,newsize);
    return bp;
}
/*
 * mm_free - Freeing a block does nothing.
 * modify head and foot
 */
void mm_free(void *ptr)
{
    size_t size =GET_ALLOC(HDRP(ptr));
    PUT(HDRP(ptr),PACK(size,0));
    PUT(FTRP(ptr),PACK(size,0));
    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    copySize = *(size_t *)((char *)oldptr);
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}

static void *find_fit(size_t asize){
    void *bp;

    for(bp=(char *)GET(root);GET_SIZE(HDRP(bp))>0;bp=SUCC_PTR(bp)){
        if(!GET_ALLOC(HDRP(bp))&&(asize<=GET_SIZE(HDRP(bp))))
            return bp;
    }

    return NULL;
}

static void place(void *bp,size_t asize){
    size_t csize = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp),PACK(asize,1));
    PUT(FTRP(bp),PACK(asize,1));

    if((csize-asize)>=(2*DSIZE)){
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp),PACK(csize-asize,0));
        PUT(FTRP(bp),PACK(csize-asize,0));
        SET_PTR(SUCC_PTR(bp),GET(root));
        SET_PTR(PRED_PTR(GET(root)),bp);
        SET_PTR(root,bp);        
    }
}

int mem_check(void){
    void *current = root+3*WSIZE;
    if(GET_SIZE(current)==0){
        printf("%p is the end of heap",current);
        return 1;
    }
    void *bp;
    for(bp=(char *)GET(root);GET_SIZE(HDRP(bp));bp=SUCC_PTR(bp)){
        if(bp>mem_heap_hi()){
            printf("%p's succ bp is outbound\n",bp);
            printf("bp's size is %d\n",GET_SIZE(HDRP(bp)));
            return 0;
        }
    }
    return 1;
}









