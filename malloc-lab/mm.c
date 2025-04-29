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
    "team8",
    /* First member's full name */
    "Seokjoo Youn",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))




//csapp implicit 구현


//기본 상수 및 매크로
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1<<12) //합 추가 때 쓰는 사이즈. 2^12, 4096 바이트

#define MAX(x, y) ((x) > (y) ? (x) : (y))
//사이즈 | 할당여부 패키징
#define PACK(size, alloc) ((size) | (alloc))

//주소p 에서 한개 워드 읽고 쓰기
#define GET(p) (*(unsigned int *)(p))
#define PUT(p,val) (*(unsigned int *)(p) = (val))

//주소 p로부터 사이즈,할당여부  필드 읽기
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

//주어진 블록 포인터로 해당 블록의 헤더와 풋터 계산
#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp)+ GET_SIZE(HDRP(bp))- DSIZE)

//주어진 블록 포인터 bp에서 다음과 이전 블록 주소 계산
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) //footer에서 사이즈 얻음
//explicit 매크로
#define PREV_FREE(bp) (*(void**)(bp))
#define NEXT_FREE(bp) (*(void**)(bp + DSIZE))

//init이랑 find에서 둘다 쓸거고 main은 make로 만드니까 static으로 선언
static char* heap_listp;
//root
static void* root;

//next fit findptr
static void* findptr;

/*
 * mm_init - initialize the malloc package.
 */
// free list에서 bp를 제거
static void remove_from_free_list(void *bp) {
    if (PREV_FREE(bp)) {
        NEXT_FREE(PREV_FREE(bp)) = NEXT_FREE(bp);
    } else {
        root = NEXT_FREE(bp);
    }
    if (NEXT_FREE(bp)) {
        PREV_FREE(NEXT_FREE(bp)) = PREV_FREE(bp);
    }
}

// place(), free(), coalesce()에서 필요할 때 호출

//coalesce 함수
static void *coalesce(void *bp){
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc){//case1: 앞뒤 블록이 할당되어있을때
        return bp;
    }
    else if (prev_alloc && !next_alloc){//case2: next만 가용일때
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); //  다음블록 사이즈를 현재사이즈에 +
        remove_from_free_list(NEXT_BLKP(bp));//다음블록 리스트에서 제거.
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        
    }
    else if (!prev_alloc && next_alloc){//case3: prev 블록만 가용일때
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        remove_from_free_list(PREV_BLKP(bp));//이전블록 리스트에서 제거.
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    else{//case4: 앞뒤로 가용 블록일때
        size += GET_SIZE(HDRP(PREV_BLKP(bp)))+GET_SIZE(HDRP(NEXT_BLKP(bp)));
        remove_from_free_list(NEXT_BLKP(bp));//다음블록 리스트에서 제거.
        remove_from_free_list(PREV_BLKP(bp));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp= PREV_BLKP(bp);
    }

    return bp; 
}

static void *extend_heap(size_t words){
    char *bp;
    size_t size;
    //짝수의 워드로 할당.더블워드 정렬
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1) // 블록포인터, 헤더와 페이로드의 경계부분을 새 힙영역 시작부분으로 설정
        return NULL;
    
    // 헤더, 풋터 free 해주고 새 에필로그 해더 설정
    PUT(HDRP(bp), PACK(size,0)); //free header
    PUT(FTRP(bp), PACK(size, 0));// free footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // new epilogue header

    //빈 공간 있으면 결합
    bp = coalesce(bp);

    //새로 만들어진 free 블록을 free list에 추가
    NEXT_FREE(bp) = root;
    PREV_FREE(bp) = NULL;
    if (root != NULL)
        PREV_FREE(root) = bp;
    root = bp;

    return bp;
}
int mm_init(void)
{
    //implicit 구현부
    // if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
    //     return -1;
    // PUT(heap_listp, 0); /* Alignment padding */
    // PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    // PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    // PUT(heap_listp + (3*WSIZE), PACK(0, 1)); /* Epilogue header */
    // heap_listp += (2*WSIZE);

    // if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
    //     return -1;
    // return 0;

    //explicit 구현부

    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
    return -1;
    PUT(heap_listp, 0); /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1)); /* Epilogue header */
    heap_listp += (2*WSIZE);

    void *bp = extend_heap(CHUNKSIZE/WSIZE);
    if (bp == NULL)
        return -1;
    root = bp; //첫 노드 payload 위치에 root 설정
    findptr = root;
    NEXT_FREE(root)=NULL;
    PREV_FREE(root)=NULL;
    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */

static void *find_fit(size_t asize){
    //first fit
    // void *bp;

    // for (bp = root; bp != NULL;bp = NEXT_FREE(bp)){
    //     // printf("loop");
    //     if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
    //         return bp;
    //     }
    // }
    //next fit

    void *bp = findptr;
    
    // 먼저 findptr부터 끝까지
    for (; bp != NULL; bp = NEXT_FREE(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            findptr = NEXT_FREE(bp); // 다음부터 시작하게 업데이트
            return bp;
        }
    }

    // 못 찾으면 root부터 findptr 직전까지 다시 탐색
    for (bp = root; bp != findptr; bp = NEXT_FREE(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            findptr = NEXT_FREE(bp);
            return bp;
        }
    }
    return NULL;
}
static void place(void *bp, size_t asize){
    size_t csize =  GET_SIZE(HDRP(bp));
    remove_from_free_list(bp);

    if((csize - asize) >= (3*DSIZE)){ //남는공간이 최소공간인 더블사이즈*2보다 크면 -> 리눅스 64비트로 컴파일 한다고 함.
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp=NEXT_BLKP(bp); //asize만큼 감
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
        NEXT_FREE(bp) = root;// 현재 노드를 루트로 만들기
        PREV_FREE(bp) = NULL;
        if (root != NULL) {
            PREV_FREE(root) = bp;
        }
        root = bp; //현재 split 된 노드가 루트가 됨

    }
    else{//최소공간 안나오면 다씀.
        
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

void *mm_malloc(size_t size)
{
    // int newsize = ALIGN(size + SIZE_T_SIZE);
    // void *p = mem_sbrk(newsize);
    // if (p == (void *)-1)
    //     return NULL;
    // else
    // {
    //     *(size_t *)p = size;
    //     return (void *)((char *)p + SIZE_T_SIZE);
    // }
    size_t asize; //블록사이즈 조절
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;

   
    if (size == 0)
        return NULL;

  
    if (size <= DSIZE)
        asize = 2*DSIZE; //헤더와 풋터까지 반영
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);//size + (헤더+풋터 사이즈 DSISE) + 올림을 위한 DSIZE-1

    //fit block 찾기
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    // 빈공간 못찾으면 확장
    extendsize = MAX(asize,CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;

}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size  = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    void * coalbp = coalesce(bp);
    NEXT_FREE(coalbp) = root;// coalesce한 노드를 루트로 만들기
    PREV_FREE(coalbp) = NULL;
    if (root != NULL) {
        PREV_FREE(root) = coalbp;
    }
    root = coalbp; //현재 coalesce한 노드가 루트가 됨

}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    // if (size <= 0){
    //     mm_free(ptr);
    //     return 0;
    // }
    // if (ptr == NULL){
    //     return mm_malloc(size);
    // }
    // void *oldptr = ptr;
    // void *newptr;
    // size_t copySize;

    // newptr = mm_malloc(size);
    // if (newptr == NULL)
    //     return NULL;
    // copySize = GET_SIZE(HDRP(oldptr))-DSIZE;
    // if (size < copySize)
    //     copySize = size;
    // memcpy(newptr, oldptr, copySize);
    // mm_free(oldptr);
    // return newptr;

    
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    // copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    copySize = GET_SIZE(HDRP(oldptr)) - DSIZE;

    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}