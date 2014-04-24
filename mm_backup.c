/* 
 * mm-implicit.c -  Simple allocator based on implicit free lists, 
 *                  first fit placement, and boundary tag coalescing. 
 *
 * Each block has header and footer of the form:
 * 
 *      31                     3  2  1  0 
 *      -----------------------------------
 *     | s  s  s  s  ... s  s  s  0  0  a/f
 *      ----------------------------------- 
 * 
 * where s are the meaningful size bits and a/f is set 
 * iff the block is allocated. The list has the following form:
 *
 * begin                                                          end
 * heap                                                           heap  
 *  -----------------------------------------------------------------   
 * |  pad   | hdr(8:a) | ftr(8:a) | zero or more usr blks | hdr(8:a) |
 *  -----------------------------------------------------------------
 *          |       prologue      |                       | epilogue |
 *          |         block       |                       | block    |
 *
 * The allocated prologue and epilogue blocks are overhead that
 * eliminate edge conditions during coalescing.
 */
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <memory.h>
#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
  /* Team name */
  "Tranquil",
  /* First member's full name */
  "Dylan Shepard",
  /* First member's email address */
  "dylanshepard@me.com",
  /* Second member's full name (leave blank if none) */
  "Max Harris",
  /* Second member's email address (leave blank if none) */
  "mharris@colorado.edu"
};

/////////////////////////////////////////////////////////////////////////////
// Constants and macros
//
// These correspond to the material in Figure 9.43 of the text
// The macros have been turned into C++ inline functions to
// make debugging code easier.
//
/////////////////////////////////////////////////////////////////////////////
#define WSIZE       4       /* word size (bytes) */  
#define DSIZE       8       /* doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* initial heap size (bytes) */
#define OVERHEAD    8       /* overhead of header and footer (bytes) */

static inline int MAX(int x, int y) {
  return x > y ? x : y;
}

//
// Pack a size and allocated bit into a word
// We mask of the "alloc" field to insure only
// the lower bit is used
// // THe book doesn't mask the alloc field...
static inline size_t PACK(size_t size, int alloc) {
  return ((size) | ((alloc) & 0x1));
}

//
// Read and write a word at address p
//
static inline size_t GET(void *p) { return  *(size_t *)p; }
static inline void PUT( void *p, size_t val)
{
  *((size_t *)p) = val;
}

//
// Read the size and allocated fields from address p
//
static inline size_t GET_SIZE( void *p )  { 
  return GET(p) & ~0x7;
}

static inline int GET_ALLOC( void *p  ) {
  return GET(p) & 0x1;
}

//
// Given block ptr bp, compute address of its header and footer
//
static inline void *HDRP(void *bp) {

  return ((char *)(bp) - WSIZE);
}
static inline void *FTRP(void *bp) {
  return ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE);
}

//
// Given block ptr bp, compute address of next and previous blocks
//
static inline void *NEXT_BLKP(void *bp) {
  return  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)));
}

static inline void* PREV_BLKP(void *bp){
  return  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)));
}

/////////////////////////////////////////////////////////////////////////////
//
// Global Variables
//

static char *heap_listp;  /* pointer to first block */  

//
// function prototypes for internal helper routines
//
static void *extend_heap(size_t words);
static void place(void *bp, size_t adjsize);
static void *find_fit(size_t adjsize);
static void *coalesce(void *bp);
static void printblock(void *bp); 
static void checkblock(void *bp);

//
// mm_init - Initialize the memory manager 
//
int mm_init(void) 
{
        if ((heap_listp = mem_sbrk(4*WSIZE)) == NULL)
                return -1;
        PUT(heap_listp, 0); //alignment padding
        PUT(heap_listp+WSIZE, PACK(OVERHEAD, 1)); //pre header
        PUT(heap_listp+DSIZE, PACK(OVERHEAD, 1)); //pre footer
        PUT(heap_listp+WSIZE+DSIZE, PACK(0, 1)); //post footer
        heap_listp += DSIZE;

        if (extend_heap(CHUNKSIZE/WSIZE) == NULL) //Extend with free block of CHUNKSIZE bytes
                return -1;
        return 0;
}


//
// extend_heap - Extend heap with free block and return its block pointer
//
static void *extend_heap(size_t words) 
{
        char *bp;
        size_t size;
        
        size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
        //Allocate even number of words to maintain alignment
        if ((int)(bp = mem_sbrk(size)) < 0)
                return NULL;

        // Initializef ree block header/footer and epilogue header
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

        return coalesce(bp);
}


//
// Practice problem 9.8
//
// find_fit - Find a fit for a block with asize bytes 
//
static void *find_fit(size_t adjsize)
{
        void *bp;

        for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
                if (!GET_ALLOC(HDRP(bp)) && (adjsize <= GET_SIZE(HDRP(bp)))) {
                        return bp; //Once it finds a fit, it places it.
                }
        }
  return NULL; /* no fit */
}

// 
// mm_free - Free a block 
//
void mm_free(void *bp)
{
        size_t size = GET_SIZE(HDRP(bp));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        coalesce(bp);
}

//
// coalesce - boundary tag coalescing. Return ptr to coalesced block
//
static void *coalesce(void *bp) 
{
        size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
        size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
        size_t size = GET_SIZE(HDRP(bp));
        if (prev_alloc && next_alloc) {
                return bp;
        }
        else if (prev_alloc && !next_alloc) {
                size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
                PUT(HDRP(bp), PACK(size, 0));
                PUT(FTRP(bp), PACK(size, 0));
                return bp;
        }
        else if (!prev_alloc && next_alloc) {
                size += GET_SIZE(HDRP(PREV_BLKP(bp)));
                PUT(FTRP(bp), PACK(size, 0));
                PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
                return(PREV_BLKP(bp));
        }
        else {
                size =+ GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
                PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
                PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
                return (PREV_BLKP(bp));
        }
}

//
// mm_malloc - Allocate a block with at least size bytes of payload 
//
void *mm_malloc(size_t size) 
{
        size_t adjsize;
        size_t extendsize;
        char *bp;

        if (size <= 0)
                return NULL;
        //ironic

        if (size <= DSIZE) //Adjust block size to include overhead and alignment.
                adjsize = DSIZE + OVERHEAD;
        else
                adjsize = DSIZE * ((size + (OVERHEAD) + (DSIZE-1)) / DSIZE);

        if ((bp = find_fit(adjsize)) != NULL) { 
                //Search free list for a fitting chunk.
                place(bp, adjsize);
                return bp;
        }
                //No fit found. Get more memory and move the block.
        extendsize = MAX(adjsize, CHUNKSIZE);
        if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
                return NULL;
        place(bp, adjsize);
        return bp;
} 

//
//
// Practice problem 9.9
//
// place - Place block of asize bytes at start of free block bp 
//         and split if remainder would be at least minimum block size
//
static void place(void *bp, size_t adjsize)
{
        size_t chunksize = GET_SIZE(HDRP(bp));
        if ((chunksize - adjsize) >= (DSIZE + OVERHEAD)) {
                PUT(HDRP(bp), PACK(adjsize, 1));
                PUT(FTRP(bp), PACK(adjsize, 1));
                bp = NEXT_BLKP(bp);
                PUT(HDRP(bp), PACK(chunksize - adjsize, 0));
                PUT(FTRP(bp), PACK(chunksize - adjsize, 0));
        }
        else {
                PUT(HDRP(bp), PACK(chunksize, 1));
                PUT(FTRP(bp), PACK(chunksize, 1));
        }
}


//
// mm_realloc -- implemented for you
//
void *mm_realloc(void *ptr, size_t size)
{
  void *newp;
  size_t copySize;

  newp = mm_malloc(size);
  if (newp == NULL) {
    printf("ERROR: mm_malloc failed in mm_realloc\n");
    exit(1);
  }
  copySize = GET_SIZE(HDRP(ptr));
  if (size < copySize) {
    copySize = size;
  }
  memcpy(newp, ptr, copySize);
  mm_free(ptr);
  return newp;
}

//
// mm_checkheap - Check the heap for consistency 
//
void mm_checkheap(int verbose) 
{
  //
  // This provided implementation assumes you're using the structure
  // of the sample solution in the text. If not, omit this code
  // and provide your own mm_checkheap
  //
  void *bp = heap_listp;
  
  if (verbose) {
    printf("Heap (%p):\n", heap_listp);
  }

  if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp))) {
	printf("Bad prologue header\n");
  }
  checkblock(heap_listp);

  for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
    if (verbose)  {
      printblock(bp);
    }
    checkblock(bp);
  }
     
  if (verbose) {
    printblock(bp);
  }

  if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp)))) {
    printf("Bad epilogue header\n");
  }
}

static void printblock(void *bp) 
{
  size_t hsize, halloc, fsize, falloc;

  hsize = GET_SIZE(HDRP(bp));
  halloc = GET_ALLOC(HDRP(bp));  
  fsize = GET_SIZE(FTRP(bp));
  falloc = GET_ALLOC(FTRP(bp));  
    
  if (hsize == 0) {
    printf("%p: EOL\n", bp);
    return;
  }

  printf("%p: header: [%d:%c] footer: [%d:%c]\n",
	 bp, 
	 (int) hsize, (halloc ? 'a' : 'f'), 
	 (int) fsize, (falloc ? 'a' : 'f')); 
}

static void checkblock(void *bp) 
{
  if ((size_t)bp % 8) {
    printf("Error: %p is not doubleword aligned\n", bp);
  }
  if (GET(HDRP(bp)) != GET(FTRP(bp))) {
    printf("Error: header does not match footer\n");
  }
}

