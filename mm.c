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
#include "mm.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include "memlib.h"
#define mode 1
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
    ""};
/* single word (4) or double word (8) alignment */
#if mode == 1
#define ALIGNMENT 8
/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
/*
 * mm_init - initialize the malloc package.
 */
/* Basic constants and macros */
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1 << 12)
#define MAX(x, y) ((x) > (y) ? (x) : (y))
/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))
/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))
/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp)- WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE((char *)(bp)-WSIZE))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE((char *)(bp)-DSIZE))
/* Given block ptr bp, compute address of its predecessor and successor */


#define FIND_PRED(bp) (*(char **)(bp))
#define FIND_SUCC(bp) (*(char **)((char *)(bp) + WSIZE))

static char *heap_listp;
static char *free_listp;
static void *coalesce(void *bp);

static void remove_list(void *bp)
{
  if (bp == free_listp)
  {
    free_listp = FIND_SUCC(bp);
    return;
  }
    FIND_SUCC(FIND_PRED(bp)) = FIND_SUCC(bp);
    if (FIND_SUCC(bp) != NULL)
      FIND_PRED(FIND_SUCC(bp)) = FIND_PRED(bp);
  return;
}
static void add_list(void *bp)
{
    FIND_SUCC(bp) = free_listp;
    if (free_listp != NULL)
      FIND_PRED(free_listp) = bp;
    free_listp = bp;
}

static void *coalesce(void *bp) {
  size_t size = GET_SIZE(HDRP(bp));
  // char prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))) ? 'ALLOCATED' : 'FREE';
  // char next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))) ? 'ALLOCATED' : 'FREE';
  size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(bp)));
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
  if (prev_alloc && next_alloc) {
    add_list(bp);
    return bp;
  } else if (prev_alloc && !next_alloc) {
    remove_list(NEXT_BLKP(bp));
    size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
  } else if (!prev_alloc && next_alloc) {
    remove_list(PREV_BLKP(bp));
    size += GET_SIZE(HDRP(PREV_BLKP(bp)));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    bp = PREV_BLKP(bp);
  } else {
    remove_list(PREV_BLKP(bp));
    remove_list(NEXT_BLKP(bp));
    size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
    bp = PREV_BLKP(bp);
  }
  add_list(bp);
  return bp;
}
static void *extend_heap(size_t words) {
  char *bp;
  size_t size;
  /* Allocate an even number of words to maintain alignment */
  size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
  if ((long)(bp = mem_sbrk(size)) == -1) return NULL;
  /* Initialize free block header/footer and the epilogue header */
  PUT(HDRP(bp), PACK(size, 0));
  PUT(FTRP(bp), PACK(size, 0));
  PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));
  return coalesce(bp);
}

int mm_init(void) {
  /* Create the initial empty heap */
  if ((heap_listp = mem_sbrk(6 * WSIZE)) == (void *)-1) return -1;
  PUT(heap_listp, 0);
  PUT(heap_listp + (1 * WSIZE), PACK(2*DSIZE, 1));
  PUT(heap_listp + (2 * WSIZE), NULL); // predecessor
  PUT(heap_listp + (3 * WSIZE), NULL); // successor
  PUT(heap_listp + (4 * WSIZE), PACK(2*DSIZE, 1));
  PUT(heap_listp + (5 * WSIZE), PACK(0, 1));
  free_listp = heap_listp + 2*WSIZE;
  /* Extend the empty heap with a free block of CHUNKSIZE bytes */
  if (extend_heap(CHUNKSIZE / WSIZE) == NULL) return -1;
  return 0;
}
/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
static void *find_fit(size_t asize) {
  char *bp = free_listp;
  // size_t size;
  while (GET_ALLOC(HDRP(bp)) != 1) {
    if (asize <= GET_SIZE(HDRP(bp)))
      return bp;
    bp = FIND_SUCC(bp);
  }
  return NULL;
}

static void place(void *bp, size_t asize) {
  remove_list(bp);
  size_t old_size = GET_SIZE(HDRP(bp));
  if ((old_size - asize) >= (2 * DSIZE)) {
    PUT(HDRP(bp), PACK(asize, 1));
    PUT(FTRP(bp), PACK(asize, 1));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(old_size - asize, 0));
    PUT(FTRP(NEXT_BLKP(bp)), PACK(old_size - asize, 0));
    add_list(NEXT_BLKP(bp));
  } else {
    PUT(HDRP(bp), PACK(old_size, 1));
    PUT(FTRP(bp), PACK(old_size, 1));
    }
}
void *mm_malloc(size_t size) {
  size_t asize;
  size_t extendsize;
  char *bp;
  if (size == 0) return NULL;
  if (size <= DSIZE)
    asize = 2 * DSIZE;
  else
    asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
  /* Search the free list for a fit */
  if ((bp = find_fit(asize)) != NULL) {
    place(bp, asize);
    return bp;
  }
  /* No fit found. Get more memory and place the block*/
  extendsize = MAX(asize, CHUNKSIZE);
  if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
    return NULL;
  place(bp, asize);
  return bp;
}
/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp) {
  size_t size = GET_SIZE(HDRP(bp));
  PUT(HDRP(bp), PACK(size, 0));
  PUT(FTRP(bp), PACK(size, 0));
  coalesce(bp);
}
/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size) {
  if (ptr == NULL) {
    return mm_malloc(size);
  }
  if (size <= 0) {
    mm_free(ptr);
    return 0;
  }
  void *oldptr = ptr;
  void *newptr;
  size_t copySize;
  newptr = mm_malloc(size);
  if (newptr == NULL) return NULL;
  // copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
  copySize = GET_SIZE(HDRP(ptr)) - DSIZE;
  if (size < copySize) copySize = size;
  memcpy(newptr, oldptr, copySize);
  mm_free(oldptr);
  return newptr;
}
#else

#define ALIGNMENT 8

#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

/* 기본 상수 */
#define WSIZE 4             // word size
#define DSIZE 8             // double word size
#define CHUNKSIZE (1 << 12) // 힙 확장을 위한 기본 크기 (= 초기 빈 블록의 크기)

/* 힙에 접근/순회하는 데 사용할 매크로 */
#define MAX(x, y) (x > y ? x : y)
#define PACK(size, alloc) (size | alloc)                              // size와 할당 비트를 결합, header와 footer에 저장할 값
#define GET(p) (*(unsigned int *)(p))                                 // p가 참조하는 워드 반환 (포인터라서 직접 역참조 불가능 -> 타입 캐스팅)
#define PUT(p, val) (*(unsigned int *)(p) = (val))                    // p에 val 저장
#define GET_SIZE(p) (GET(p) & ~0x7)                                   // 사이즈 (~0x7: ...11111000, '&' 연산으로 뒤에 세자리 없어짐)
#define GET_ALLOC(p) (GET(p) & 0x1)                                   // 할당 상태
#define HDRP(bp) ((char *)(bp)-WSIZE)                                 // Header 포인터
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)          // Footer 포인터 (🚨Header의 정보를 참조해서 가져오기 때문에, Header의 정보를 변경했다면 변경된 위치의 Footer가 반환됨에 유의)
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE))) // 다음 블록의 포인터
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))   // 이전 블록의 포인터

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

int mm_init(void)
{
    // 초기 힙 생성
    char *heap_listp;
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1) // 4워드 크기의 힙 생성, heap_listp에 힙의 시작 주소값 할당
        return -1;
    PUT(heap_listp, 0);                            // 정렬 패딩
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); // 프롤로그 Header
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); // 프롤로그 Footer
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     // 에필로그 Header: 프로그램이 할당한 마지막 블록의 뒤에 위치하며, 블록이 할당되지 않은 상태를 나타냄

    // 힙을 CHUNKSIZE bytes로 확장
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
}

void *mm_malloc(size_t size)
{
    size_t asize;      // 조정된 블록 사이즈
    size_t extendsize; // 확장할 사이즈
    char *bp;

    // 잘못된 요청 분기
    if (size == 0)
        return NULL;

    /* 사이즈 조정 */
    if (size <= DSIZE)     // 8바이트 이하이면
        asize = 2 * DSIZE; // 최소 블록 크기 16바이트 할당 (헤더 4 + 푸터 4 + 저장공간 8)
    else
        asize = DSIZE * ((size + DSIZE + DSIZE - 1) / DSIZE); // 8배수로 올림 처리

    /* 가용 블록 검색 */
    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize); // 할당
        return bp;        // 새로 할당된 블록의 포인터 리턴
    }

    /* 적합한 블록이 없을 경우 힙확장 */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

// 기존에 할당된 메모리 블록의 크기 변경
// `기존 메모리 블록의 포인터`, `새로운 크기`
void *mm_realloc(void *ptr, size_t size)
{
    /* 예외 처리 */
    if (ptr == NULL) // 포인터가 NULL인 경우 할당만 수행
        return mm_malloc(size);

    if (size <= 0) // size가 0인 경우 메모리 반환만 수행
    {
        mm_free(ptr);
        return 0;
    }

    /* 새 블록에 할당 */
    void *newptr = mm_malloc(size); // 새로 할당한 블록의 포인터
    if (newptr == NULL)
        return NULL; // 할당 실패

    /* 데이터 복사 */
    size_t copySize = GET_SIZE(HDRP(ptr)) - DSIZE; // payload만큼 복사
    if (size < copySize)                           // 기존 사이즈가 새 크기보다 더 크면
        copySize = size;                           // size로 크기 변경 (기존 메모리 블록보다 작은 크기에 할당하면, 일부 데이터만 복사)

    memcpy(newptr, ptr, copySize); // 새 블록으로 데이터 복사

    /* 기존 블록 반환 */
    mm_free(ptr);

    return newptr;
}

static void *extend_heap(size_t words)
{
    char *bp;

    // 더블 워드 정렬 유지
    // size: 확장할 크기
    size_t size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE; // 2워드의 가장 가까운 배수로 반올림 (홀수면 1 더해서 곱함)

    if ((long)(bp = mem_sbrk(size)) == -1) // 힙 확장
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));         // 새 빈 블록 헤더 초기화
    PUT(FTRP(bp), PACK(size, 0));         // 새 빈 블록 푸터 초기화
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 에필로그 블록 헤더 초기화

    return coalesce(bp); // 병합 후 coalesce 함수에서 리턴된 블록 포인터 반환
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전 블록 할당 상태
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음 블록 할당 상태
    size_t size = GET_SIZE(HDRP(bp));                   // 현재 블록 사이즈

    if (prev_alloc && next_alloc) // 모두 할당된 경우
        return bp;

    else if (prev_alloc && !next_alloc) // 다음 블록만 빈 경우
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0)); // 현재 블록 헤더 재설정
        PUT(FTRP(bp), PACK(size, 0)); // 다음 블록 푸터 재설정 (위에서 헤더를 재설정했으므로, FTRP(bp)는 합쳐질 다음 블록의 푸터가 됨)
    }
    else if (!prev_alloc && next_alloc) // 이전 블록만 빈 경우
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록 헤더 재설정
        PUT(FTRP(bp), PACK(size, 0));            // 현재 블록 푸터 재설정
        bp = PREV_BLKP(bp);                      // 이전 블록의 시작점으로 포인터 변경
    }
    else // 이전 블록과 다음 블록 모두 빈 경우
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록 헤더 재설정
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); // 다음 블록 푸터 재설정
        bp = PREV_BLKP(bp);                      // 이전 블록의 시작점으로 포인터 변경
    }

    return bp; // 병합된 블록의 포인터 반환
}

static void *find_fit(size_t asize)
{
    void *bp = mem_heap_lo() + 2 * WSIZE; // 첫번째 블록(주소: 힙의 첫 부분 + 8bytes)부터 탐색 시작
    while (GET_SIZE(HDRP(bp)) > 0)
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) // 가용 상태이고, 사이즈가 적합하면
            return bp;                                             // 해당 블록 포인터 리턴
        bp = NEXT_BLKP(bp);                                        // 조건에 맞지 않으면 다음 블록으로 이동해서 탐색을 이어감
    }
    return NULL;
}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp)); // 현재 블록의 크기

    if ((csize - asize) >= (2 * DSIZE)) // 차이가 최소 블록 크기 16보다 같거나 크면 분할
    {
        PUT(HDRP(bp), PACK(asize, 1)); // 현재 블록에는 필요한 만큼만 할당
        PUT(FTRP(bp), PACK(asize, 1));

        PUT(HDRP(NEXT_BLKP(bp)), PACK((csize - asize), 0)); // 남은 크기를 다음 블록에 할당(가용 블록)
        PUT(FTRP(NEXT_BLKP(bp)), PACK((csize - asize), 0));
    }
    else
    {
        PUT(HDRP(bp), PACK(csize, 1)); // 해당 블록 전부 사용
        PUT(FTRP(bp), PACK(csize, 1));
    }
}









#endif
