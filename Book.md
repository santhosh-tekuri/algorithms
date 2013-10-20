#Binary Heap

Binary Heap is a binary tree with two additional constraints.

  1. ***shape property***:
    the tree nearly complete binary tree. i.e all levels are completely filled except possibly the lowest, which is filled from left up to a point
  2. ***heap property***:
    the nodes are either >=(max-heap) or <=(min-heap) each of its children


Heaps are commonly implemented using arrays with `A[0]` as root.
```
int left(int i){
    return 2*i+1;
}

int right(int i){
    return 2*i+2;
}

int parent(int i){
    return Math.floor((i-1)/2);
}

int height(int n){
    return Math.floor(log2(n));
}
```
in max-heap:

* $A[parent[i]]\geq A[i]$  
* largest element is at root

in min-heap:

* $A[parent[i]]\leq A[i]$  
* smallest element is at root

root is said to be at level 0  
\#elements at level $L = 2^L$  
total #elements from root to level $L = 2^0+2^1+2^2+…+2^L = 2^{L+1}-1$

height of n element heap = $\lfloor(log_2n)\rfloor$  
min #elements in heap of height h = ?  
max #elements in heap of height h = ?

##Operations

###Addition

   * add new element to end of heap
   * keep moving it up until it is larger than its parent
```
void add(int a[], int size, int v){
    a[size] = v;
    siftUp(a, size);
}

void siftUp(int a[], int i){
    while(i>0){
        int ip = parent(i);
        if(a[ip]<a[i]){
            swap(a, ip, i);
            i = ip;
        }else
            return;
    }
}
```
>Note: `siftUp` assumes `a[0…i-1]` is heap

Running Time: $O(\log_2n)$

###Deletion

   * replace element to be deleted with last element of heap
   * keep moving down until it is smaller than its children
```
void delete(int a[], int size, int i){
    a[i] = a[size-1];
    siftDown(a i, size-1);
}

void siftDown(int a[], int size, int i){
    while(left(i)<size){ // i is not leaf
        int max = i;
        
        int left = left(i);
        if(a[left]>a[max])
            max = left;

        int right = right(i);
        if(right<size && a[right]>a[max]) // right child exists and it is bigger
            max = right;

        if(max!=root){
            swap(a, i, max);
            i = max;
        }else
            break;
    }
}
```

   * `siftDown` assumes that, binary trees rooted at `left(i)` and `right(i)` are max-heaps but `a[i]` may be smaller than its children, thus violating max-heap property
   * In `siftDown`, `a[i]` flow-down so that, subtree rooted at `a[i]` becomes a max-heap
   * notice that `siftDown` is actually merging two heaps

Running Time: $O(\log_2n)$

###Replace

if new element is less than element being replaced do `siftDown`, otherwise do `siftUp`
```
// replace a[i] with v
void replace(int a[], int size, int i, int v){
    int oldV = a[i];
    a[i] = v;
    if(v<oldV)
        siftDown(a, end, i);
    else if(v>oldV)
        siftUp(a, i);
    return oldV;
}
```
Running Time: $O(\log_2n)$

##Heapify

array elements $\lfloor length[A]/2\rfloor \cdots1$ are all leaves of the tree  
these leaves can be treated as each is one-element heap.
```
void heapify(int a[], int size){
    for(int i=size/2-1; i>=0; i--) // from index of last parent node
        siftDown(a, size, i);
}
```

Running Time: $O(n)$

alternatively `heapify` can be implemented using `siftUp`:
```
void heapify(int a[], int size){
    for(int i=1; i<size; i++)
        siftUp(a, i);
}
```
Running Time: $O(n\log_2n)$

----------

Finding the `k` smallest of `N` items, where $k<<N$?
```
void findLargest(int a[], int k){
    heapify(a, k); // create max-heap with first k elements
    for(int i=k+1; i<a.length; i++){
        if(a[i]<a[0])
            replace(a, k, 0); // replace with root
    }
}
```

Running Time: $O(N)+O(N\log_2k)$

##Heap Sort
```
void heapSort(int a[], int count){
    heapify(a, count);

    int end = count-1;
    while(end>0){
        swap(a[0], a[end]);
        end--;
        siftDown(a, 0, end);
    }
}
```

Runing Time: $O(n\log_2n)$

>NOTE: heap sort is not stable

##Merge K Sorted Linked Lists [<i class="icon-link"></i>][1]

extend `merge` of `merge-sort` to `k` sorted lists  
to find min of all list heads use min-heap
```
void merge(Node lists[]){
    if(lists.length==0)
        return null;
    else if(lists.length==1)
        return lists[0];

    int heapSize = lists.length;

    // compare values of head nodes
    minHeapify(lists, lists.length);

    Node head=null, tail=null;
    while(heapSize>1){
        Node min = lists[0];
        if(min.next==null)
            remove(lists, heapSize--, 0);
        else
            replace(lists, heapSize, 0, min.next);

        if(head==null)
            head = tail = min;
        else
            tail = min;
    }

    tail.next = lists[0];
}
```
minHeapify takes $O(k)$  
while loop runs `n` times where `n`=sum of sorted list sizes  
each while loop takes $log_2k$ times

Running Time: $O(k)+O(n\log_2k)=O(n\log_2k)$

##Sort k-sorted array [<i class="icon-link"></i>][2]

in ***k-sorted array***, each element is at most `k` positions away from its target position  
i.e `i` the element in sorted array, should is in `a[i-k…i+k]`

if we use Insertion Sort, the inner loop runs at most k times.  
so running-time: $O(nk)$

we can use selection sort, where min element is selected repeatedly  
in k-sorted array, the min element must be in first `k+1` positions  
so use min-heap, to effectively find min
```
void sort(int a[], int k){
   int b[k+1];
   copy a[0…k+1] to b 
   heapify(b, k+1);
   
   for(int i=0,j=k+1; i<a.length; i++,j++){
       a[i] = b[0];
       if(j<a.length)
           replace(b, k+1, 0, a[j]);
       else
           remove(b, k+a.length-j, 0);
   }
}
```
`heapify` takes $O(k)$  
`n` heap operations each taking $O(\log_2k)$  
so running-time: $O(n\log_2k)$  
auxiliary-space: $O(k)$

##Median of Integer Stream [<i class="icon-link"></i>][3]

***median*** is the middle element in an odd length sorted array, and in the even case it’s the average of the middle elements

Given a stream of unsorted integers, find the median element in sorted order at any given time ?

use 2 heaps simultaneously, a max-heap and a min-heap with following invariants

   * **order invariant**
      * max-heap contains the smallest half of the numbers and min-heap contains the largest half
      * So the numbers in max-heap are always less than or equal to the numbers in min-heap 
   * **size invariant**
      * \#elements in max-heap is either equal to or `1` more than #elements in the min-heap
      * so if we received `2N` elements(even) up to now, max-heap and min-heap will both contain `N` elements. 
      * if we have received `2N+1` elements(odd), max-heap will contain `N+1` and min-heap `N`

```
double getMedian(int maxHeap[], int minHeap[], int size){
    if(size%2==0)
        return (maxHeap[0]+minHeap[0])/2.0;
    else
        return maxHeap[0];
}

void append(int maxHeap[], int minHeap[], int size, int v){
    if(size%2==0){
        // sizes: N, N
        if(v<=minHeap[0])
            add(maxHeap, size/2, v); // N+1, N
        else{
            add(minHeap, size/2, v); // N, N+1

            // move minHeap root to maxHeap
            add(maxHeap, size/2, minHeap[0]);
            delete(minHeap, (size/2)+1, 0);
        }
    }else{
        // sizes: N+1, N
        if(v>=maxHeap[0])
            add(minHeap, size/2, v);
        else{
            add(maxHeap, (size/2)+1, v); // N+2, N
            
            // move maxHeap root to minHeap
            add(minHeap, size/2, maxHeap[0]);
            delete(maxHeap, (size/2)+2, 0);
        }
    }
}
```

#Divide and Conquer

##Median of two sorted arrays 

Median of sorted array:
```
int median(int a[]){
    int m = a.length/2;
    if(a.length%2==0)
        return (a[m-1]+a[m])/2;
    else
        return a[m];
}
```

Given two sorted arrays `a` and `b` of sizes `m` and `n` respectively. Find median of array obtained by merging those arrays?

###Count while merging [<i class="icon-link"></i>][4]
```
double median(int a[], int b[]){
    int total = a.length+b.length;

    int curr = -1;
    int prev = -1;
    for(int count=0, i=0, j=0; count<=total/2; count++){
        prev = curr;
        if(i<a.length && j<b.length){
            if(a[i]<b[j])
                curr = a[i++];
            else{
                curr = b[j++];
        }else{
            int offset = total/2-count-1;
            if(i==a.length){
                curr = b[j+offset];
                if(offset>0)
                    prev = b[j+offset-1];
            }else{
                curr = a[i+offset];
                if(offset>0)
                    prev = a[i+offset-1];
            }
            break;
        }
    }
    return total%2==0 ? (prev+cur)/2.0 : cur;
}
```
Running Time: $O(n)$

###Comparing medians [<i class="icon-link"></i>][5][<i class="icon-link"></i>][6]
```
int median3(int a, int b, int c){
    int min = min(a, b, c);
    int max = max(a, b, c);
    return a+b+c-min-max;
}

double median4(int a, int b, int c, int d){
    int min = min(a, b, c, d);
    int max = max(a, b, c, d);
    return (a+b+c+d-min-max)/2.0;
}

int median(int a[], int b[]){
    if(a.length<=b.length)
        return median(a, 0, a.length-1, b, 0, b.length-1);
    else
        return median(b, 0, b.length-1, a, 0, a.length-1);
}

double median(int a[], int ai, int aj, int b[], int bi, bj){
    int aSize = aj-ai+1;
    int bSize = bj-ai+1;
    assert aSize<=bSize;

    if(aSize==1){
        if(bSize==1)
            return (a[i]+b[j])/2;
        int m = bi+(bSize/2);
        if(bSize%2==1)
            return (b[m/2]+median3(a[i], b[m-1], b[m+1]))/2
        else
            return median3(a[i], b[m-1], b[m]);
    }
    if(aSize==2){
        if(bSize==2)
            return median4(a[i], a[i+1], b[j], b[j+1]);
        int m = bi+(bSize/2);
        if(bSize%2==1)
            return median3(b[m], min(a[i], b[m+1]), max(a[i+1], b[m-1]);
        else
            return median4(b[m-1], b[m], min(a[i], b[m+1]), max(a[i+1], b[m-1]));
    }

    int am = ai+aSize/2;
    int bm = bi+bSize/2;
    if(a[am]<b[bm]){
        if(aSize%2==0)
            am--;
        int aLeftCount = am-ai;
        int bRightCount = bj-bm;
        int minRemoved = min(aLeftCount, bRightCount);
        return median(a, ai+minRemoved, aj, b, bi, bj-minRemoved);
    }else{
        if(bSize%2==0)
            bm--;
        int aRightCount = aj-am;
        int bLeftCount = bm-bi;
        int minRemoved = min(aRightCount, bLeftCount;
        return median(a, ai, aj-minRemoved, b, bi+minRemoved, bj);
    }
}
```
###Binary search for median [<i class="icon-link"></i>][7][<i class="icon-link"></i>][8]
>TODO
##Find Peak [<i class="icon-play"></i>][9][<i class="icon-link"></i>][10][<i class="icon-link"></i>][11]

###Find Peak: 1D
Given array `A[1…n]`, element `A[i]` is peak if it is not smaller than its neighbors

Neighbors of `A[i]` are `A[i-1] A[i+1]`  
i.e each element has at most `2` neighbors

```
if A[i] is peak, then
   * if i=1: A[1]>=A[2]
   * if i=n: A[n]>=A[n-1]
   * otherwise: A[i]>=A[i-1] and A[i]>=A[i+1]
```
$\{10, \underline{13}, 5, \underline{8}, 3, 2, 1\}$, here `13` and `8` are peaks

Max element in array is not smaller than its neighbors  
hence every array contains at least one peak


**Naive Implementation**

```
scan array from left to right
compare each element with its neighbors
exit when peak found
```
```
int findPeak(int A[]){
    for(int i=0; i<A.length; i++){
        if((i>0||A[i]>=A[i-1]) && (i==n-1||A[i]>=A[i+1])
            return i;
    }
}
```
Running Time: $O(n)$


**Divide and Conquer**

```
take middle element of array, A[n/2]
if A[n/2-1]>A[n/2]
    find peak in A[1…n/2-1] => claim 1
if(A[n/2+1]>A[n/2]
    find peak in A[n/2+1…n] => claim 2
otherwise A[n/2] is peak
```
![FindPeak01.png][12]

**Claim1:** if `a>m`, then red subarray indeed contains a peak of `A`
```
if a is max in red subarray
    then a is not smaller than its left neighbor
    since a>m, i.e a is not smaller than its right neighbor
    hence a is peak of A
if max is something other than a
   it must also be peak of A
```

**Claim 2:** any peak in red subarray is indeed peak of `A`
```
if a is peak of red subarray
    then a is not smaller than its left neighbor
    since a>m, i.e a is not smaller than its left neighbor
    hence a is peak of A
if peak is something other than a
    it must also be peak of A
```
```
int findPeak(int A[]){
    int begin=0, end=A.length-1;
    while(true){
        int mid = begin+(end-begin)/2;
        if(mid-1>=begin && a[mid-1]>a[mid])
            end = mid-1;
        else if(mid+1<=end && a[mid+1]>a[mid])
            begin = mid+1;
        else
            return mid;
     }
}
```
$$T(n)= T(n/2)+O(1)= \sum_{1}^{log_2n} O(1)=O(log_2n)$$

###Find Peak: 2D

Given array `A[1…n,1…m]`, `A[i,j]` is peak if is not smaller than its neighbors

Neighbors of `A[i,j]` are `A[i-1,j] A[i+1,j] A[i,j-1] A[i,j+1]`  
i.e each element has at most `4` neighbors

$
\begin{matrix}
10 & 8 & 5\\ 
3 & {\color{Blue} 2} & 1\\ 
{\color{Blue} 7} & {\color{Red} 9 } & {\color{Blue} 4} \\
6 & {\color{Blue} 8} & 3 
\end{matrix}
$  
here 9 is peak

**Idea 1**

Construct `B[1…m]`, where `B[i]` is max of <code>i<sup>th</sup></code> column of `A`  
here `B = 10 9 5`

then `2D` peak of `A` = `1D` peak of `B`


Correctness:
```
say B[k] is 1D peak

as per definition of B, B[k] is >= kth column of A
    i.e top and bottom neighbors of B[k] are <= B[k]

if B[k] is 1D peak, then B[k-1]<=B[k]. and B[k-1] is >= k-1th column of A
    i.e left neighbor of B[k] <= B[k]

if B[k] is 1D peak, then B[k+1]<=B[k]. and B[k+1] is >= k+1th column of A
    i.e right neighbor of B[k] <= B[k]
```

time to compute an element of `B` is $O(n)$  
there are `m` elements in `B`  
so time to compute `B` is $O(nm)$


Observation: 

   * 1D peak-finder uses only $log_2m$ elements of `B`
   * so compute `B[j]` only when needed
   * running time to compute those elements is $O(n\log_2m)$

![FindPeak02.png][13]

```
take middle column m/2
find maximum element in that column, say a = A[i,m/2]
    if m=1 i,e A has only one column 
        then a is peak
    compare a with its left neighbor say b=A[i-1,m/2] and right neighbor say c=A[i+1,m/2]
    if b>a, find peak in left columns
    if c>a, find peak in right columns
    otherwise, a is peak
```
$$T(n,m)= T(n,m/2)+O(n)= \sum_{1}^{log_2m} O(n)=O(n\log_2m)$$

**Idea 2**
```
take window frame formed by first, middle and last row, and first, middle and last column
find max of these 3m+3n elements say x
if x is greater than its neighbors
    then x is 2D peak
otherwise 
    find the neighbor say a, that is greater than x
    note that a cannot in the yellow window frame
    thus it must me in one of 4 quadrants
    recurse and use this algorithm on that quadrant
```
![FindPeak03.png][14]


**Claim 1:** if `a>x`, then red quadrant indeed has 2D peak of `A`
```
let m is max in red quadrant
    then m>=a
    since a>x, we have m>x
    the red quadrant is surrounded by yellow frame
    any number in yellow frame <=x
    so any number in yellow cross <m
    hence m is 2D peak of A
```

**Claim 2**: the peak found by this algorithm in red quadrant, is indeed 2D peak of `A`
```
window frame of red quadrant, contains a
say g is max in that window frame, thus g>=a
since a>x, then g>x
if g is on boundary, and g is peak of red quadrant
    neighbors of g on yellow frame, must be <=x
    hence g is 2D peak of A
if g is not on boundary, and g is peak of red quadrant
    clearly g is >= its 4 neighbors
    hence g is 2D peak of A
```
$
\begin{align*}T(n,m)
 &= T(n/2,m/2) + O(m+n)\\ 
 &= T(n/4,m/4)+O(m/2+n/2) + O(m+n)\\ 
 &= O(m+n)+O(m/2+n/2)+O(m/4,n/4)+\cdots \\ 
 &= O(m+m/2+m/4+\cdots) + O(n+n/2+n/4+\cdots)\\ 
 &= O(m+n)
\end{align*}
$
#Dynamic Programming

##Matrix-chain multiplication

Given a chain $A_1, A_2, …, A_n$ of `n` matrices  
matrix $A_i$ has dimension $p_{i-1}\times p_i$.

Fully parenthesize the product $A_1A_2…A_n$ in a way that minimizes #scalar multiplications?


**Brute Force Approach:**

Let $P(n)$ is number of ways $n$ matrices can be paranthesized.  

when $n=1$, there is only one way  
when $n\geq2$, we can split between $k^{th}$ and $(k+1)^{st}$ matrices for any $k=1, 2, …,n-1$

$$
P(n)=\begin{cases}
1 & \text{ if } n= 1\\ 
\sum_{k=1}^{n-1}P(k)P(n-k) & \text{ if } n\geq 2 
\end{cases}
$$

number of solutions is exponential in $n$  
so brute force will be exhaustive search.

**Step 1:**

let $A_{i\cdots j}$ denotes product $A_iA_{i+1}\cdots A_j$

suppose an optimal parenthesization splits between $A_k$ and $A_{k+1}$  
then the paranthesization of $A_{i\cdots k}$, and $A_{k+1\cdots n}$ must be optimal.  
otherwise substituting optimal parenthesization would produce cost less than the optimum: contradiction

**Step 2:**

Let $m[i,j]$ is minimum number of multiplications required to compute $A_{i\cdots j}$

$$m[i,j]=\begin{cases}
0 & \text{ if } i=j\\ 
\min_{i \leq k< j}\{m[i,k]+m[k+1,j]+p_{i-1}p_kp_j\} & \text{ if } i< j 
\end{cases}$$

**Step 3:**
```
int matrixChainOrder(int p[]){
    int n = p.length-1;

    int m[n][n];
    for(int i=0; i<n; i++)
        m[i][i] = 0;

    int split[n][n];
    for(int len=2; len<=n; len++){
        for(int i=0; i<=n-len; i++){
            int j = i+len-1;
            m[i][j] = INFINITY;
            for(int k=i; k<j; k++){
                int cost = m[i][k]+m[k+1][j]+p[i-1]*p[k]*p[j]
                if(cost<m[i][j]){
                    m[i][j] = cost;
                    split[i][j] = k;
            }
        }
    }

    printSolution(split, 0, n-1);
    return m[0][n-1];
}
```

**Step 4:**
```
void printSolution(int split[][], int i, int j){
    if(i==j)
        print "A"_i
     else{
         print "("
         printSolution(split, i, split[i][j]);
         printSolution(split, split[i][j]+1, j);
         print ")"
     }
}
```
##Boolean Paranthesizations [<i class="icon-link"></i>][15]

operand array `opd[1..n]`, where `opd[i] = T/F`  
operator array `opr[1..n-1]` where `opr[i] = and/or/xor`

if `opd[]={T, F, T, F}`, `opr[]={or, and, xor}`  
then boolean expression is: `T or F and T xor F`  
i.e `opr[i]` is the operand between `opd[i], opd[i+1]`

count #ways to parenthesize given expression such that it evaluates to true?

----------

let `T[i,j]` = #ways to parenthesize `opd[i]…opd[j]` such that it evaluates to ***true***  
let `F[i,j]` = #ways to parenthesize `opd[i]…opd[j]` such that it evaluates to ***false***

$
T[i,i]= \begin{cases}
1 & \text{ if } opd[i]=T \\ 
0 & \text{ otherwise }
\end{cases}
$

$
F[i,i]= \begin{cases}
0 & \text{ if } opd[i]=F \\ 
1 & \text{ otherwise }
\end{cases}
$

$
\begin{align*}Total[i,j]
 &= \#ways\;to\; parenthesize\;opd[i]…opd[j]\\ 
 &= T[i,j]+F[i,j]
\end{align*}
$

$$
T[i,j]=\sum_{k=i}^{j-1} \begin{cases}
T[i,k].T[k+1,j] & \text{ if } opr[k]=and \\ 
Total[i,k].Total[k+1,j] - F[i,k].F[k+1,j] & \text{ if } opr[k]=or \\
T[i,k].F[k+1,j] + F[i,k].T[k+1,j] & \text{ if } opr[k]=xor
\end{cases}
$$

$$
F[i,j]=\sum_{k=i}^{j-1} \begin{cases}
Total[i,k].Total[k+1,j] - T[i,k].T[k+1,j] & \text{ if } opr[k]=and \\ 
F[i,k].F[k+1,j] & \text{ if } opr[k]=or \\
T[i,k].T[k+1,j] + F[i,k].F[k+1,j] & \text{ if } opr[k]=xor
\end{cases}
$$

Answer: $T[1,n]$  
Running Time: $O(n^3)$

##Longest Increasing Subsequence (LIS) [<i class="icon-book"></i>][16][<i class="icon-link"></i>][17]

Given a sequence $X = x_1, x_2, …, x_m$, Find longest subsequence whose elements are in strictly increasing order

Let $L[j]$ is longest increasing subsequence ending at position $j$

$$
L[j]=\begin{cases}
1 & \text{ if } j=1\\
\max_{i=1}^{j-1}\{L[i]\;: x_i<x_j\}+1 & \text{ if } j>1
\end{cases}
$$
then
$$LIS(X) = \max_{j=1}^nL[j]$$

```
int LIS(int x[]){
    int L[x.length], b[x.length];

    L[0] = 1;
    b[0] = -1;
    int maxIndex = 0;
    for(int j=1; j<x.length; j++){
        int max = 0;
        b[j] = -1;
        for(int i=0; i<j; i++){
            if(L[i]>max && x[i]<x[j]){
               max = L[i];
               b[j] = i;
            }
        }
        L[j] = max+1;
        if(L[j]>L[maxIndex])
            maxIndex = j;
    }

    printLIS(x, b, maxIndex);
    return L[maxIndex];
}

void printLIS(int x[], int b[], int i){
    if(b[i]!=-1)
        print(x, b, b[i]);
    print x[i];
}
```
Running Time = $O(n^2)$

>NOTE: LIS can also be found as `LCS(X, Y)` where `Y` is result of sorting `X`

>NOTE: LIS can be solved more efficiently using binary search in $O(n\log_2n)$

##Longest Bitonic Subsequence

Bitonic?
```
a sequence is called bitonic, if it is first increasing and then decreasing
a sequence in increasing order is bitonic with decreasing part as empty
a sequence in decreasing order is bitonic with increasing part as empty
```
Let $lis[j]$ is longest increasing subsequence ending at $x_j$  
Let $lds[j]$ is longest decreasing subsequence starting at $x_j$

then length of longest bitonic subsequence is:  
$$\max_{i=1}^n\{lis[i]+lds[i]-1\}$$

```
int LBS(int x[]){
    int lis[x.length], lisB[x.length];
    lis[0] = 1;
    lisB[0] = -1;
    for(int j=1; j<x.length; j++){
        int max = 0;
        lisB[j] = -1;
        for(int i=0; i<j; i++){
            if(x[i]<x[j] && lis[i]>max){
                max = lis[i];
                lisB[j] = i;
            }
        }
        lis[j] = max+1;
    }

    int lds[x.length], ldsB[x.length];
    lds[x.length-1] = 1;
    ldsB[x.length-1] = -1;
    for(int j=x.length-2; j>=0; j--){
        int max = 0;
        ldsB[j] = -1;
        for(int i=x.length-1; i>j; i--){
            if(x[i]<x[j] && lds[i]>max){
                max = lis[i];
                ldsB[j] = i;
            }
        }
        lds[j] = max+1;
    }

    int maxIndex = 0;
    for(int i=1; i<x.length; i++){
        if(lis[i]+lds[j]>lis[maxIndex]+lds[maxIndex])
            maxIndex = i;
    }
    printSolution(x, lisb, ldsb, maxIndex);
    return lis[maxIndex]+lds[maxIndex]-1;
}

void printSolution(int x[], int lisB[], int ldsB[], int i){
    printLIS(x, lisB, i);

    i = ldsB[i];
    while(i!=-1){
        print x[i];
        i = ldsB[i];
    }
}
```
##Longest ZigZag Subsequence

Given sequence of numbers $X = x_1, x_2, …, x_n$, find longest zigzag subsequence?

ZigZag?
```
Sequence of numbers is called ZigZag, if the difference between successive numbers strictly alternate between positive and negative.  
The first difference(if one exists) may be either positive or negative
```

Let $incr[i]$ is longest length of zigzag subsequence ending at $x_i$, with last step is increasing  
Let $decr[i]$ is longest length of zigzag subsequence ending at $x_i$, with last step is decreasing

$$
incr[i]=\begin{cases}
1 & \text{ if } i=1 \\
\max_{j=1}^i\{decr[j]\;:x_j<x_i\} & \text{ if } i>1
\end{cases}
$$

$$
decr[i]=\begin{cases}
1 & \text{ if } i=1 \\
\max_{j=1}^i\{incr[j]\;:x_j>x_i\} & \text{ if } i>1
\end{cases}
$$

then length of longest zigzag subsequence = $max(incr, decr)$

to simplify implemenation, rather than using two arrays, use `m[2][n]` where first row is `incr[]` and second row is `decr[]`
```
int LZS(int x[]){
    int m[2][x.length];
    int maxi, maxj;

    m[0][0] = m[1][0] = 1;
    maxi = maxj = 0;
    for(int i=1; i<x.length; i++){
        for(int j=0; j<i; j++){
            int max0 = max1 = 0;
            if(x[j]<x[i]){
                if(m[1][j]>max1)
                    max1 = m[1][j];
            }else if(x[j]>x[i]){
                if(m[0][j]>max0)
                    max0 = m[0][j];
            }
        }
        m[0][i] = max1+1;
        m[1][i] = max0+1;
        if(m[0][i]>m[maxi][maxj]){
            maxi = 0; maxj = i;
        }
        if(m[1][i]>m[maxi][maxj]){
            maxi = 1; maxj = i;
        }
    }
    
    return m[maxi][maxj];
}
```
Running Time = $O(n^2)$

> NOTE: this can be solved in $O(n)$ time as [here](#LZS-Linear)

##Maximum Sum Subarray [<i class="icon-link"></i>][18]

Given sequence of numbers $X = x_1, x_2, …, x_n$, find a subarray $x_i, x_{i+1}, …, x_j$ for which sum of elements in subarray is maximized.

Let $m[j]$ is max sum over all subarrays ending at $j$

$
m[j]=\begin{cases}
x_i & \text{ if } j=1 \\
\max\{m[j-1]+x_j, x_j\} & otherwise
\end{cases}
$

Answer is max value in $m[]$

To compute $m[j]$, we simply need its previous value $m[j-1]$. so we do not need to use array here
```

int maxSumSubarray(int x[]){
    int m = x[0];
    int mBegin = 0;

    int max = m;
    int maxBegin = 0;
    int maxEnd = 0;

    for(int j=1; j<x.length; j++){
        if(m+x[j]>x[j])
            m = m+x[j];            
        else{
            m = x[j];
            mBegin = j;
        }

        if(m>max){
            max = m;
            maxBegin = mBegin;
            maxEnd = j;
        }
    }

    print "subarray "+maxBegin+"…"+maxEnd;
    return max;
}
```
Running Time: $O(n)$  
This is actually ***kadane's algorithm***

----------
###If wrap enabled

Find maximum sum subarray in a circular array with both positive and negative numbers?


there are 2 cases based on whether elements that contribute to maximum sum are arranged such that:

1.  no wrapping is there
> this can be solved using above algorithm

2.  wrapping is there
> to solve this: change wrapping to non-wrapping. Wrapping of contributing elements implies non-wrapping of non-contributing elements. To find them, invert sign of each element and run above algorithm. To get sum of contributing elements, we can subtract sum of non-contributing elements from total sum

```
int maxSumCircularSubarray(int x[]){
    in sum1 = maxSumSubarray(x);

    int total = 0;
    for(int i=0; i<x.length; i++){
        total += x[i];
        x[i] = -x[i];
    }
    int sum2 = total + maxSumSubarray(x);

    return max(sum1, sum2);
}
```

##Maximum Product Subarray [<i class="icon-link"></i>][19]

Given sequence of numbers $X = x_1, x_2, …, x_n$, containing both +ve and -ve numbers. Find a subarray $x_i, x_{i+1}, …, x_j$ for which product of elements in subarray is maximized.

Let $b[j]$ is max product over all sequences ending at $j$  
Let $s[j]$ is min product over all sequences ending at $j$

$
b[j]=\begin{cases}
x_i & \text{ if } j=1 \\
max\begin{Bmatrix}
b[j-1].x_j,\;x_j & \text{ if }x_j\geq0 \\
s[j-1].x_j,\;x_j & \text{ if }x_j<0
\end{Bmatrix}
& otherwize
\end{cases}
$

$
s[j]=\begin{cases}
x_i & \text{ if } j=1 \\
max\begin{Bmatrix}
s[j-1].x_j,\;x_j & \text{ if }x_j\geq0 \\
b[j-1].x_j,\;x_j & \text{ if }x_j<0
\end{Bmatrix}
& otherwize
\end{cases}
$

Answer is max in $b[]$

To compute $b[j]$ and $s[j]$, we simply need their previous value $b[j-1]$ or $s[j-1]$. so we don't need to use arrays here
```
int maxProdSubarray(int x[]){
    int b = x[0];
    int bBegin = 0;
    int biggest = b;
    int biggestBegin = 0;
    int biggestEnd = 0;

    int s = x[0];
    int sBegin = 0;

    for(int j=1; j<x.length; j++){
        if(x[j]>=0){
            if(b*x[j]>x[j])
                b = b*x[j];
            else{
                b = x[j];
                bBegin = j;
            }

            if(s*x[j]<x[j])
                s = s*x[j];
            else{
                s = x[j];
                sBegin = j;
            }
        }else{
            int bPrev = b;
            int bBeginPrev = bBegin;
            if(s*x[j]>x[j]){
                b = s*x[j];
                bBegin = sBegin;
            }else{
                b = x[j];
                bBegin = j;
            }

            if(bPrev*x[j]<x[j]){
                s = bPrev*x[j];
                sBegin = bBeginPrev;
            }else{
                s = x[j];
                sBegin = j;
            }
        }
        if(b>biggest){
            biggest = b;
            biggestBegin = bBegin;
            biggestEnd = j;
        }
    }

    print "subarray "+biggestBegin+"…"+biggestEnd;
    return biggest;
}
```
Running Time: $O(n)$

##Max Sum Pair of non-adjacent elements [<i class="icon-link"></i>][20]

Given $a[1…n]$, find a pair $(a[i],a[j])$ such that $i<j-1$, where $a[i]+a[j]$ is maximized?

Let $p[j]$ = partner of max sum pair ending at $a[j]$  
i.e pair is $(p[j], a[j])$

$
p[j]=\begin{cases}
a[1] & \text{ if } j=3 \\
\max\{p[j-1],\;a[j-2]\} & \text{ if } j>3
\end{cases}
$

Answer is $(p[j], a[j])$ such such that $p[j]+a[j]$ is maximized

To compute $p[j]$ we just need $p[j-1]$. so we don't need to use array
```
int[] maxSumPair(int a[]){
    int j = 2;
    int pj = a[0];

    int maxj = 2;
    int maxpj = a[0];
    while(j<a.length){
        j++;
        pj = max(pj, a[j-2]);
        if(pj+a[j]>maxpj+a[maxj]){
            maxpj = pj;
            maxj = j;
        }
    }

    return {maxpj, a[maxj]);
}
```
Running Time: $O(n)$

----------

The solution can be formulated differently as below:

Let $m[j]$ is max value in $a[1…j]$  
then max sum pair ending at $a[j]$ is $(m[j-2], a[j])$

$
m[j]=\begin{cases}
a[1] & \text{ if } j=1 \\
\max\{m[j-1],\;a[j]\} & \text{ if } j>1
\end{cases}
$

Answer is $(m[j-2],\;a[j])$ such such that $m[j-2]+a[j]$ is maximized

##Edit Distance [<i class="icon-book"></i>][21][<i class="icon-link"></i>][22]

Transform source string of text $x[1..m]$ to target string $y[1..n]$. The intermediate and final result will be in $z$ array.

Let $i$ indices into $x[]$ and $j$ indices into $z[]$

The transformations available are:

*  Copy
   * $z[j] = x[i]$
   * $i++;\; j++$
*  Replace
   * $z[j] = c$ // replaced by $c$
   * $i++;\; j++$
*  Delete
   * $i++$
*  Insert
   * $z[j] = c$ // inserted $c$
   * $j++$
*  Twiddle or Exchange
   * $z[j] = x[i+1]$
   * $z[j+1] = x[i]$
   * $i+=2;\;j+=2$
*  Kill (must be final operation)
   * $i = m+1$

Each transformation has an associated cost. Find the least expensive transformation sequence?

Assume individual costs of `copy` and `replace` are less than combined cost of `delete` and `insert`. Otherwise `copy` and `replace` would not be used

----------

There are two ways to transform x to y

  1. transform a prefix of x into y (without kill), and then use final kill
  2. transform all of x into y (without final kill)

Let $c[i,j]$ denotes cost of transforming $x[1\cdots i]$ to $y[1\cdots j]$ using way 2  
Let $c'[i,j, t]$ denotes cost of transforming $x[1\cdots i]$ to $y[1\cdots j]$ using way 2, with $t$ being last transformation applied

$$
c[i, j] = \min_{t=copy}^{twiddle}c'[i, j, t]
$$


$
c'[i, j, copy] = \begin{cases}
c[i-1, j-1] + cost[copy] & \text{ if } x[i]=y[j] \\
\infty & otherwise
\end{cases}
$

$ c'[i, j, replace] = c[i-1, j-1] + cost[replace] $

$ c'[i, j, delete] = c[i-1, j] + cost[delete] $

$ c'[i, j, insert] = c[i, j-1] + cost[insert] $

$
c'[i, j, twiddle] = \begin{cases}
c[i-2, j-2] + cost[twiddle] & \text{ if }x[i-1]=y[j] \;and\; x[i]=y[j-1] \\
\infty & otherwise
\end{cases}
$

Along with $c[i, j]$ store the values of $t$ that leads $t$ minimal cost

Once $c[1\cdots m, 1\cdots n]$ is completely calculated:  
$$minimal cost = min\{c[m, n], \min_{i=1}^{m-1}(c[i, n]+cost[kill])\}$$

Running Time: $O(mn)$

----------

Find similarities between two DNA sequences by aligning them. spaces are used to align them.

say DNA sequences are `x = GATCGGCAT` and `y = CAATGTGAATC`, one alignment is

```
x' = G ATCG GCAT 
y' = CAAT GTGAATC
     -*++*+*+-++-
```
Scorings are as below:
```
if(x'[i]=space || y'[i]=space)
    score = -2 // denoted by *
else if(x'[i]=y'[i])
    score = +1 // denoted by +
else
    score = -1 // denoted by -
```

We can solve this using previous algorithm by using following scores
```
* means
    insert, if x'[i]=space
    delete, if y'[i]=space
+ means
    copy
- means
    replace
```
i.e,
```
score(insert)  = -2
score(delete)  = -2
score(copy)    = +1
score(replace) = -1
score(other)   = +INFINITY
```

##Knapsack Problems [<i class="icon-book"></i>][23]

During a robbery, a burglar finds much more loot than he expected and has to decide what to take. His bag/knapsack will hold a total weight of at most $W$ pounds. There are $n$ items to pick from, of weight $w_1,…,w_n$ and dollar value of $v_1,…,v_n$. what is most valuable combination of items he can fit in his bag?


there are two versions of this problem:

  1. there are unlimited quantities of each item available. this is called unbounded ***knapsack problem*** or ***knapsack with repetition***
  2. there is only one of each item available. this is called ***0/1 knapsack problem*** or ***knapsack without repetition***

###Knapsack with repetition

let $k[w]$ = maximum value achievable with knapsack of capacity $w$

$$
k[w]=\begin{cases}
0 & \text{ if } w=0 \\
\max_{i=1}^n\{k[w-w_i]+v_i\;:w_i\leq w\} & otherwise
\end{cases}
$$

```
int knapsack(int wt[], int v[], int W){
    int k[W+1];
    k[0] = 0;
    for(int w=1; w<k.length; w++){
        int max = 0;
        for(int i=0; i<v.length; i++){
            if(k[w-wt[i]]+v[i]>max)
                max = k[w-wt[i]]+v[i]>max;
        }
        k[w] = max;
    }
    return k[W];
}
```
**with memorization:**
```
int knapsack(int wt[], int v[], int W){
    return knapsack(wt, v, W, W);
}

HashTable ht;
int knapsack(int wt[], int v[], int W, int w){
    if(ht[w]!=null)
        return ht[w];

    int max = 0;
    for(int i=0; i<v.length; i++){
        if(knapsack(wt, v, W, w-wt[i])+v[i]>max)
            max = k[w-wt[i]]+v[i]>max;
    }
    ht[w] = max;
    return max;
}
```

In this case, memorization pays off. Without memorization we solve every subproblem that could conceivably needed, while with memorization we only end up solving the ones that are actually used. 

For example, $W$ and all the weights $w_i$ are multiples of $100$,  
any $k[w]$ is useless if $w$ is not multiple of $100$

**Variants:**

Given weights of each item $w_i$ and knapsack weight $W$, find the combination of items where sum of weights is greatest?
>this is special case of previous problem where value and weight of item are the same

###Knapsack without repetition

Let $k[w,j]$ = maximum value achievable using knapsack of capacity $w$ and items $1\cdots j$

$
k[w,j]=\begin{cases}
0 & \text{ if } w=0\;or\;j=0 \\
max\begin{Bmatrix} 
k[w-w_j,j-1],&\text{ if } w_j\leq w&//item\;j\;included\\
k[w,j-1]&&// item\;j\;not\;included
\end{Bmatrix} & otherwise
\end{cases}
$

```
int knapsack(int wt[], int v[], int W){
    int n = wt.length;
    int k[W+1][n+1];
    for(int w=0; w<=W; w++){
        for(int j=0; j<=n; j++){
            if(w==0 || j==0)
                k[w][j] = 0;
            else{
                k[w][j] = k[w][j-1];
                if(w[j]<=w)
                    k[w][j] = max(k[w][j], k[w-w[j]][j-1]+v[j]);
            }
        }
    }
    return k[W][n];
}
```

**Variants:**

$n$ projects are available to an investor and profit obtained from $j^{th}$ project is $p_j$. It costs $c_j$ to invest in project $j$ and only $c$ dollars are available. Find projects to be chosen to maximize the profit?


----------


Knapsack problem generalizes wide variety of resource-constrained selection tasks.

   * replace ***weight*** with CPU units, and ***only W pounds can be taken*** with ***only W units of CPU time are available***
   * replace ***weight*** with bandwidth

#Miscellaneous

##Find Missing Element

given two arrays. first array contains non-negative integers. second array contains the all elements of first array in random order except one element. find that missing element.

this can be done in $O(n)$:
```
int findMissing(int arr1[], int arr2[]){
    return sum(arr1)-sum(arr2);
}
```
but this is problematic because integer overflow will occur for large arrays.

trick is to use `xor`:
```
int findMissing(int arr1[], int arr2[]){
    int result = 0;
    for(int v: arr1)
        result ^= v;
    for(int v: arr2)
        result ^= v;

    return result;
}
```
##Convert Array [<i class="icon-link"></i>][24]

convert array `[a1,a2,…,an,b1,b2,…,bn,c1,c2,…,cn]` to `[a1,b1,c1,a2,b2,c2,…,an,bn,cn]` in-place without using extra space?

```
// returns index in original array 
// for ith position in final array
int getIndex(int i, int n){
    return (i%3)*n+i/3;
}
```

   * convert array from left to right
   * find `swapIndex` using `getIndex`
   * if `swapIndex>curIndex`, swap elements
   * otherwise
      * it means element at `swapIndex` was replaced with another element in previous iterations
      * now it is somewhere else. so we should keep looking for that element
      * this can be done repeatedly calling `getIndex` on `swapIndex` until `swapIndex<curIndex`

```
void convert(int a[]){
   int n = a/3;
   for(int curIndex=0; curIndex<a.length; curIndex++){
      int swapIndex = getIndex(curIndex, n);
      while(swapIndex<curIndex)
          swapIndex = getIndex(swapIndex, n);
      swap(a, curIndex, swapIndex);
   }
}
```
Running Time ≈ $O(n^{1.3})$

##Apply Permutation

Given array `a` of integers of size `n` and array `p` containing a permutation of `0…n-1`
rearrange `a` such that `a[i] = a[p[i]]`
```
void permute(int a[], int p[]){
    for(int i=0; i<a.length; i++){
        while(p[i]!=i){
            swap(a, i, p[i]);
            swap(p, i, p[i]);
        }
    }
}
```
>NOTE: the above algorithm modifies `p` array

```
void permute(int a[], int p[]){
    for(int curIndex=0; curIndex<a.length; curIndex++){
        int swapIndex = p[curIndex];
        while(swapIndex<i)
            swapIndex = p[swapIndex];
        if(curIndex!=swapIndex)
            swap(a, curIndex, swapIndex);
    }
}
```

##Magic Square [<i class="icon-link"></i>][25]

A [magic square][26] of order `n` is an arrangement of <code>n<sup>2</sup></code> numbers, usually distinct integers, in a square, such that all rows, all columns, and both diagonals sum to the same constant, which is called [magic constant or magic sum][27].

Magic Constant $M = \frac{n(n^2+1)}{2}$

Magic Square of odd:
```
order=3        order=5
 8 1 6    17  24   1   8  15
 3 5 7    23   5   7  14  16
 4 9 2     4   6  13  20  22
          10  12  19  21   3
          11  18  25   2   9
```

* start in the central column of the first row with the number `1`
* start filling the squares in diagonally up and right, one step at a time
* if a filled square is encountered, one moves vertically down one square instead, then continues as before
* when an "up and to the right" move would leave the square, it is wrapped around to the last row or first column, respectively

```
int[][] generateMagicSquare(int n){
    int square[n][n];

    int i = 0;
    int j = n/2;

    for(int num=1; num<=n*n;){
        square[i][j] = num++;

        int nextI = i==0 ? n-1 : i-1;
        int nextJ = j==n-1 ? 0 : j+1;
        if(square[nextI][nextJ]!=0){
            nextI = i==n-1 ? 0 : i+1;
            nextJ = j;
        }
        i = nextI; j = nextJ;
    }    

    return square;
}
```
##Leaders in array

An element is leader if it is greater than all the elements to its right side.

>Note: that last element of array is always a leader.

In array $\{16, \underline{17}, 4, 3, \underline{5}, \underline{2}\}$ leaders are $17, 5, 2$
```
Scan array from right to left, keeping track of maximum till now.
When maximum changes its value print it.
```
```
void printLeaders(int arr[]){
    if(arr.length==0)
        return;

    int max = arr[arr.length-1];
    print(max);
    for(int i=arr.length-2; i>=0; i--){
        if(arr[i]>max){
            print(arr[i]);
            max = arr[i];
        }
    }
}
```
##Pair in Array

###With given sum/product [<i class="icon-link"></i>][28]
$
\overset{i++,\;while\;a_i+a_j>sum}{
  \overrightarrow{
      \square \square \square \square \square \square \square \square\square \square
  }
}
\square \square
\underset{j--,\;otherwise}{
  \underleftarrow{
      \square \square \square \square \square \square \square \square\square \square
  }
}
$
```
int[] findPair(int a[], int sum){
    sort(a);
    int i=0, j=a.length-1;
    while(i<j){
        int s = a[i]+a[j];
        if(s==sum)
            return {i, j};
        else if(s>sum)
            i++;
        else
            j--;
    }
    return null;
}
```
sorting takes $O(n \log_2n)$ and finding pair takes $O(n)$  
Running Time: $O(n \log_2n)$

**with hashing:**

* traverse array and fill hash table with array elements as keys
* traverse array again and for each element `x`, look for `sum-x` in hash table

Running Time: $O(n)$

**with binary-search:**

* sort array in $O(n log2n)$
* for each element `a[i]`, binary search for `sum-a[i]` in `a[i+1…]`

Running Time: $O(n \log2n)$ again

>Note: find pair with given product is also same


<p style="page-break-before: always;"></p>


###With given difference[<i class="icon-link"></i>][29]
```
int[] findPair(int a[], int diff){
    sort(a);
    int i=0, j=1;
    while(j<a.length){
        int d = a[j]-a[i];
        if(d==diff)
            return {i, j};
        else if(d<diff)
            j++;
        else{
            i++;
            if(i==j)
                j++;
        }
    }
}
```
----------
###Sum Closest to Zero[<i class="icon-link"></i>][30]
>NOTE: array can have both +ve and -ve numbers

$
\overset{i++,\;while\;a_i+a_j<0}{
  \overrightarrow{
      \square \square \square \square \square \square \square \square\square \square
  }
}
\square \square
\underset{j--,\;otherwise}{
  \underleftarrow{
      \square \square \square \square \square \square \square \square\square \square
  }
}
$

```
int[] findPair(int a[]){
    sort(a);
    int i=0, j=a.length-1;
    int iClosest=i, jClosest=j;
    int closestSum = abs(a[i]+a[j]);
    while(i<j){
        int d = arr[i]+arr[j];
        if(abs(d)<closestSum){
            closestSum = abs(d);
            iClosest = i;
            jClosest = j;
        }


        if(d<0)
            i++;
        else
            j--;
    }
}
```

##Equilibrium Index [<i class="icon-link"></i>][31]

Equilibrium index of an array is an index such that:
>sum of elements at lower indexes = sum of elements at higher indexes

$[3, \underline{-3}, \underline{3}, 3, -3]$ has two equilibrium indexes

```
int equilibriumIndex(int a[]){
    int sum = sum(a);

    int leftSum = 0;
    int rightSum = sum;
    for(int i=0; i<a.length; i++){
        rightSum -= a[i];
        if(leftSum==rightSum)
            return i;
        leftSum += a[i];
    }
    return -1;
}
```

we are iterating array twice  
Running Time: $O(n)$

if array contains non-negative integers, we need only single iteration
```
int equilibriumIndex(int a[]){
    int i=0;
    int sumi = a[i]; // sum(a[0…i])

    int j=a.length-1;
    int sumj = a[a.length-1]; // sum(a[j…])

    while(i!=j){
        if(sumi<sumj){
            i++;
            sumi += a[i];
        }else{
            j--;
            sumj += a[j];
        }
    }
    return sumi==sumj ? i : -1;
}
```

##Average of large integer stream [<i class="icon-link"></i>][32]

if we know average of `n` numbers, can we find average of `n+1` numbers?
$$
newAverage = \frac{avg.n + newNumber}{n+1}
$$

to avoid overflow, it can be rewritten as:
$$
\left(\frac{avg}{n+1}\right)n+\left(\frac{newNumber}{n+1}\right)
$$

##Palindrome Number? [<i class="icon-link"></i>][33]

Determine whether given positive number is palindrome ?

If the number is same as its reverse, then it is palindrome.
```
boolean isPalindrome(int n){
    return n==0 || n==reverse(n);
}

int reverse(int n){
    int reverse = 1;
    while(num!=0){
        int lastDigit = n%10;
        reverse = reverse*10 + lastDigit; // add lastDigit to reverse
        n = n/10;
    }
    return reverse;
}
```

>NOTE: the reverse number might overflow 

Chop of one digit from both ends until they are same.  
if there are no more digits left then it is palindrome
```
boolean isPalindrome(int n){
    if(n==0)
        return true;

    int div = 1;
    while(n/div>10)
        div *= 10;

    while(n>0){
        int firstDigit = x/div;
        int lastDigit = x%10;
        if(firstDigit!=lastDigit)
            return false;
        x = (x%div)/10;
        div = div/100;
    }
    return true;
}
```

##Min-Max [<i class="icon-book"></i>][34]

###minimum or maximum
```
int minimum(int a[]){
    if(a.length==0)
        return null;
    int min = a[0];
    for(i=1; i<a.length; i++){
        if(a[i]<min)
            min = a[i];
    }
    return min;
}
```

\#comparisons = `n-1`

----------

###both minimum and maximum
```
int[] minMax(int a[]){
    if(a.length==0)
        return null;

    int min = a[0];
    int max = a[0];
    for(int i=1; i<a.length; i++){
        if(a[i]<min)
            min = a[i];
        if(a[i]>max)
            max = a[i];
    }
    return { min, max };
}
```

for each element we are doing `2` comparisons. so we used `2(n-1)` comparisons

If we compare pairs of elements from input first with each other, and then compare smaller to current minimum and larger to current maximum, we need `3` comparisons for every `2` elements.

Initially:

   * if `n` is odd, we set both min and max to first element. so we need $\frac{3(n-1)}{2}$ comparisons
   * if `n` is even, we perform 1 comparison on first 2 elements to determine initial values of min and max. so we need $1+\frac{3(n-2)}{2}$ i.e $\frac{3n}{2}-2$ comparisons

Thus in either case, we need at most $3\lfloor\frac{n}{2}\rfloor$ comparisons
   
```
int[] minMax(int a[]){
    if(a.length==0)
        return null;

    int min, max, i;
    if(n%2==0){
        if(a[0]<a[1]){
            min = a[0];
            max = a[1];
        }else{
            min = a[1];
            max = a[0];
        }
        i = 2;
    }else{
        min = max = a[0];
        i = 1;
    }

    while(i<a.length-1){
        if(a[i]<a[i+1]){
            if(a[i]<min)
                min = a[i];
            if(a[i+1]>max)
                max = a[i+1];
        }else{
            if(a[i+1]<min)
                min = a[i+1];
            if(a[i]>max)
                max = a[i];
        }
        i += 2;
    }
    return { min, max };
}
```


----------
###Smallest and 2<sup>nd</sup> Smallest [<i class="icon-book"></i>][35]

the smallest of `n` elements can be found with `n-1` comparisons through a cup of tournament.
```
1   2 3   4 5   6 7   8
 \ /   \ /   \ /   \ /
  1     3     5     7
   \   /     /     /
    \ /     /     /
     1     /     /
      \   /     /
       \ /     /
        1     /
         \   /
          \ /
           1
```
after $\lceil\log_2n\rceil$ rounds we get smallest element.  
the second smallest is any of $\lceil\log_2n\rceil$ elements that has been compared to smallest.  
i.e second smallest can be found with $\lceil\log_2n\rceil-1$ comparisons

i.e total of $n+\lceil\log_2n\rceil-2$ comparisons

in above example `1` is smallest.  
so the second smallest must be one of `2, 3, 5, 7`
```
int minSecondMin(int a[]){
    if(a.length<2)
        return null;

    int min, i;
    stack knockouts;
    if(a.length%2==0){
        if(a[0]<a[1]){
            min = a[0];
            knockouts.push(a[1]);
        }else{
            min = a[1];
            knockouts.push(a[0]);
        }
        i = 2;
    }else{
        min = a[0];
        i = 1;
    }

    while(i<a.length-1){
        if(a[i]<a[i+1]){
            if(a[i]<min){
                knockouts.clear();
                knockouts.push(a[i+1]);
                knockouts.push(min);
                min = a[i];
            }else
                knockouts.push(a[i]);
        }else{
            if(a[i+1]<min){
                knockouts.clear();
                knockouts.push(a[i]);
                knockouts.push(min);
                min = a[i+1];
            }else
                knockouts.push(a[i+1]);
        }
        i += 2;
    }

    int min2 = knockouts.pop();
    while(!knockouts.isEmpty()){
        int v = knockouts.pop();
        if(v<min2)
            min2 = v;
    }
    
    return { min, min2 };
}
```
##Stable Marriage Problem [<i class="icon-link"></i>][36]

Given `n` men and `n` women, where each person has ranked all members of the opposite sex with a unique number between `1` and `n` in order of preference. Marry the men and women together such that there are no two people of opposite sex who would both rather have each other than their current partners. If there are no such people, all the marriages are ***stable***.

let us say men represented by `{A,B,C,…}` and women represented by `{a,b,c,…}`  
given married pairs `X-a, Y-b` is unstable, if  
man `X` prefers another woman `b` over his current wife `a` AND  
woman `b` prefers `X` more than her current husband `Y`  
in this case `X-b` is called ***rouge couple***

```
while(there is unengaged man){
    pick unengaged man X
    pick first woman w in his list
    remove w from his list so that she will not be picked again
    if(w is not engaged)
       X is engaged with w
    else{
       if(w prefers X over his current partner Y){
           X is engaged with w
           Y becomes unpaired
       }
    }
}
```

>**NOTE:**
once woman becomes engaged, she remains engaged, but can change partner for a better mate that proposes to her. Does this makes this algorithm greedy for women?

>**NOTE:**
man never proposes a girl more than once

**Does the algorithm terminate ?**

in each iteration, a man eliminates a choice from his list.  
So if there are `N` men and `N` women, the #choices is <code>N<sup>2</sup></code>.  
So the max #iterations to exhaust them is <code>N<sup>2</sup></code>

**Are resulting marriages stable?**

assume there is rouge couple `X-b`, where the marriages are `X-a` and `Y-b`  
then X.preferences = `…b…a…` and b.preferences = `…X…Y…`  
in such case `X` must have proposed to `b` before `a`  
  
there are only two scenarios where `Y-b` can be formed  

1. woman `b` rejected `X`. means `b` has better partner than `X`. then when `Y` proposes her, she must have rejected => contradiction
2. woman `b` accepted `X`, later dropped `X` for better partner. but `Y` is not better partner than `X` => contradiction

```
final int FREE = -1;
int stableMarriage(int mPref[][], int wPref[][]){
    int n = mPref.length;

    // woman i is engaged to wEngaged[i]
    int wEngaged[m.length];
    for(int i=0; i<n; i++)
        wEngaged[i] = FREE;
    
    Stack freeMen = new Stack();
    for(int i=0; i<n; i++)
        freeMen.add(i);

    int next[n]; // next woman to be proposed

    while(!freeMean.isEmpty()){
        int m = freeMen.peek();
        int w = mPref[m][next[m]];
        next[m]++;
        if(wEngaged[w]==-1){
            wEngaged[w] = m;
            freeMen.pop();
        }else{
            int mEngaged = wEngaged[w];
            if(prefers(wPref[w], m, mEngaged)){
                wEngaged[w] = m;
                freeMen.push(mEngaged);
            }
        }
    }

    return wEngaged;
}

// true if m1 is preferred over m2
boolean prefers(int pref[], int m1, int m2){
    for(int m: pref){
        if(m==m1)
            return true;
        if(m==m2)
            return false;
    }
}
```
##Min Length Unsorted Subarray [<i class="icon-link"></i>][37]

Given unsorted array a, find minimum length subarray such that sorting that subarray makes the whole array sorted

$\{10, 12, 20, \underline{30, 25, 40, 32, 31, 35}, 50, 60\}$

$\{0, 1, \underline{15, 25, 6, 7}, 30, 40, 50\}$



**step1: find the candidate of unsorted array**
```
s = smallest index such that a[s]>a[s+1]  
note that no such s exists if a is already sorted

e = largest index such that a[e]<a[e-1]
note that s<e always holds
```
$\{10, 12, 20, \underline{\overset{s}{30}, 25, 40, 32, \overset{e}{31}}, 35, 50, 60\}$

**step2: grow it to find answer if necessary**
```
min = min in a[s...e] // 25  
max = max in a[s...e] // 40

decrement s while a[s-1]>min
increment e while a[e+1]<max

answer is a[s...e]
```

```
int[] minLengthUnsoredSubarray(int a[]){
    int n = a.length;

    int s = 0;
    while(s<n-1 && a[s]<=a[s+1])
        s++;
    if(s==n-1)
        return null; // a[] is already sorted

    int e = n-1;
    while(e>0 && a[e]>=a[e-1])
        e--;
    // assert e>s

    int min = min(a, s, e);
    int max = max(a, s, e);
    
    while(s>0 && a[s-1]>min)
        s--;
    while(e<n-1 && a[e+1]<max)
        e++;
    return {s, e};
}
```
Running Time: $O(n)$

##Merge Overlapping Intervals [<i class="icon-link"></i>][38]

Given list of intervals, merge overlapping intervals into one.  
i.e the output should have only mutually exclusive intervals

**Naive Implementation:**

try all pair combinations and merge if they overlap

```
boolean overlap(Node x, Node y){
    if(x.high<y.low) // xy
        return false;
    if(y.high<x.low) // yx
        return false;
    return true;
}

void merge(Node n){
   while(n!=null){ 
       Node x = n.next;
       while(x!=null){
           if(overlap(n, x)){
               n.low = min(n.low, x.low)
               n.high = max(n.high, x.high);
           }
           x = x.next;
           remove(x.prev);
       }
       n = n.next;
   }
}
```
Running Time: $O(n^2)$

**Efficient Implementation:**
```
void merge(Interval a[]){
    sort(a, #Interval.low);
    int last=0;
    //assert: a[0…last] contains mutually exclusive intervals
    for(int i=1; i<a.length; i++){
        if(a[last].high<a[i].low) // don't overlap
            a[++last] = a[i];
        else
            a[last].high = a[i].high;
    }
    
    while(++last<a.length)
        a[last] = null;
}
```
Running Time: $O(n\log_2n)$

##Circular Tour with Petrol pumps

There are $n$ petrol pumps $p_1, p_2,…,p_n$ arranged circularly. given 

   * $c_1,c_2,…,c_n$ where $c_i$ is amount of petrol available at $p_i$
   * $d_1,d_2,…,d_n$, where
      * $d_1$ = distance between $p_1$ and $p_2$
      * $d_2$ = distance between $p_2$ and $p_3$
      * $d_n$ = distance between $p_n$ and $p_1$

assume,

   * with 1 liter of petrol, truck goes 1 unit distance
   * truck has petrol tank of infinite capacity
   * truck has no petrol initially

Find first point from where a truck will be able to complete the circle?

----------

**simple solution**

check whether each starting point is valid or not
```
int findStartingPoint(int c[], int d[]){
    int n = c.length;
    for(int i=0; i<n; i++){
        int tank = 0;
        int cur = i;
        while(true){
            tank += c[cur]; // fill petrol

            tank -= d[cur]; // continue ride
            if(tank<0)
                break;
            cur = (cur+1)%n;
            if(cur==i)
                return i;
        }
    }
    return -1;
}
```
Running Rime: $O(n^2)$


**Efficient Solution**

Start from any random petrol pump say `A`.  
If you can go from `A->B->C` but not from `C->D`, try starting from `D`.  
We don't have to check for `B` and `C`(obvious).

Running Time: $O(n)$
```
int findStartingPoint(int c[], int d[]){
    int n = c.length;
    int i = 0;
    do{
        int tank = 0;
        int cur = i;
        while(true){
            tank += c[cur]; // fill petrol

            tank -= d[cur]; // continue ride
            cur = (cur+1)%n;
            if(tank<0){
                i = cur;
                break;
            }
            if(cur==i)
                return i;
        }
    }while(i!=0)
    return -1;
}
```

##Largest Multiple of 3 [<i class="icon-link"></i>][39]

Given array of non-negative integers. Find largest multiple of 3, that can be formed from array elements?

>NOTE: number of digits in array elements can vary

```
void largest3Multiple(int a[]){
    sort(a);
    int remainder = sum(a)%3;
    int ri = -1;
    int rj = -1;

    if(remainder==1){
        // remove smallest element with remainder 1
        ri = indexOf(a, 0, 1);
        if(ri==-1){
            // remove 2 smallest elements with remainder 2
            ri = indexOf(a, 0, 2);
            if(ri==-1)
                return;
            rj = indexOf(a, ri+1, 2);
            if(rj==-1)
                return;
        }        
    }else if(remainder==2){
        // remove smallest element with remainder 2
        ri = indexOf(a, 0, 2);
        if(ri==-1){
            // remove 2 smallest elements with remainder 1
            ri = indexOf(a, 0, 1);
            if(ri==-1)
                return;
            rj = indexOf(a, ri+1, 1);
            if(rj==-1)
                return;
        }        
    }
    
    // convert indexes to be removed to values
    if(ri!=-1)
        ri = a[ri];
    if(rj!=-1)
        rj = a[rj];

    if(countDigits(a[0])!=countDigits(a.length-1))
        sort(a, Integer#toString#reverse);
    
    // print array in decreasing order, but skip ri and rj
    for(int i=a.length-1; i>=0; i--){
        if(a[i]==ri)
            ri = -1;
        else if(a[i]==rj)
            rj = -1;
        else
            print(a[i]);
    }
}
```

Running Time: $O(n\log_2n)$

```
int indexOf(int a[], int from, int remainder){
    while(from<a.length){
        if(a[from]%3==remainder)
            return from;
        from++;
    }
    return -1;
}

int countDigits(int x){
    int count = 1;
    int div = 1;
    while(x/div>10){
        div *= 10;
        count++;
    }
    return count;
}
```

----------

**Largest multiple of 2, 3 and 5** [<i class="icon-link"></i>][40]

```
a number divisible by both 2 and 5, must be divisible by 10
let x is smallest element in array that is divisible by 10
find largest multiple of 3 in remaining array, and append x to end
```

##Longest Bitonic Subarray [<i class="icon-link"></i>][41]

Bitonic?
```
a sequence is called bitonic, if it is first increasing and then decreasing
a sequence in increasing order is bitonic with decreasing part as empty
a sequence in decreasing order is bitonic with increasing part as empty
```
if `a[i…j]` is the longest bitonic subarray starting at `a[i]`, it is enough to start searching from `a[j]` for next bitonic subarray
```
int[] longestBitonicSubarray(int a[]){
    int maxStart = 0;
    int maxLen = 0;

    int i = 0;
    while(i+maxLen<a.length-1){
        int j = i+1;
        while(j<a.length && a[j]>a[j-1])
            j++;
        while(j<a.length && a[j]<a[j-1])
            j++;
        if(j-i>maxLen){
            maxLen = j-i;
            maxStart = i;
        }
        i = j-1;
    }
}
```

Running Time: $O(n)$

##Majority Element [<i class="icon-link"></i>][42]

A majority element in array of size `n`, is an element that appears more than `n/2` times
>NOTE: there is ***at most one*** such element in any array

majority of `[3, 3, 4, 2, 4, 4, 2, 4, 4]` = `4`  
majority of `[3, 3, 4, 2, 4, 4, 2, 4]` = `none`

```
// returns index of majority element if present
// returns -1 if no majority element found
int findMajorityIndex(int a[]){
    int candidateIndex = findCandidateIndex(a);
    
    int count = 0;
    for(int v: a){
        if(v==a[candidateIndex])
            count++;
    }

    return count>a.length/2 ? candidate : -1;
}

// Moore’s Voting Algorithm
int findCandidateIndex(int a[]){
    int candidateIndex = 0;
    int count = 1; // resetting count

    for(int i=1; i<a.length; i++){
        if(a[candidateIndex]==a[i])
            count++;
        else
            count--;

        if(count==0){
            candidateIndex = i;
            count = 1; //resetting count
        }
    }

    return candidateIndex;
}
```
Running Time: $O(n)$

----------


Let us say we want to find element appearing $\geq\frac{n}{2}$ times in array

the above algorithm doesn't work.  
for example, `findCandidateIndex({1, 2, 1, 3})` returns index `3` rather than index `0` or `2`

>TIP: resetting `count` to `2` instead of `1` in `findCandidateIndex` works

##Longest ZigZag Subsequence {#LZS-Linear}

Given sequence of numbers $X = x_1, x_2, …, x_n$, find longest zigzag subsequence?

ZigZag?
```
Sequence of numbers is called ZigZag, if the difference between successive numbers strictly alternate between positive and negative.  
The first difference(if one exists) may be either positive or negative
```

Construct another sequence $Y = y_1, y_2, …, y_(n-1)$, where 

$
yi=\begin{cases}
0 & \text{ if } x_i=x_{i+1} \\
+1 & \text{ if } x_i>x_{i+1} \\
-1 & \text{ if } x_i<x_{i+1}
\end{cases}
$

$Y$ can be computed in $O(n)$

consider $Y = [+1,+1,+1,+1,+1,-1,+1,+1,+1,+1,-1,+1,+1,+1,-1]$  
take first element in $Y$, and take element if next element is of different sign, ignoring zeros  
this can be done in $O(n)$

```
int LZS(int x[]){
    if(x.lengh==1)
        return 1;

    int y[x.length-1];
    for(int i=0; i<y.length; i++){
        int diff = x[i]-x[i+1];
        if(diff>0)
            y[i] = 1; // decresing
        else if(diff<0)
            y[i] = -1 // increasing
        else
            y[i] = 0; // same
    }
    
    int prevSign = diff[0];
    int count = prevSign==0 ? 0 : 1;
    for(int i=1; i<y.length; i++){
        if(prevSign*y[i]==-1){ // different sign
            prevSign = y[i];
            count++;
        }
    }
    return count+1;
}
```


  [1]: http://www.geeksforgeeks.org/merge-k-sorted-arrays/
  [2]: http://www.geeksforgeeks.org/nearly-sorted-algorithm/
  [3]: http://www.ardendertat.com/2011/11/03/programming-interview-questions-13-median-of-integer-stream/
  [4]: http://www.geeksforgeeks.org/median-of-two-sorted-arrays/
  [5]: http://ideone.com/FtqjM
  [6]: http://leetcode.com/2011/03/median-of-two-sorted-arrays.html
  [7]: http://www.geeksforgeeks.org/median-of-two-sorted-arrays/
  [8]: http://www2.myoops.org/course_material/mit/NR/rdonlyres/Electrical-Engineering-and-Computer-Science/6-046JFall-2005/30C68118-E436-4FE3-8C79-6BAFBB07D935/0/ps9sol.pdf
  [9]: http://www.youtube.com/watch?v=HtSuA80QTyo&list=SPUl4u3cNGP61Oq3tWYp6V_F-5jb5L2iHb
  [10]: http://courses.csail.mit.edu/6.006/fall10/lectures/lec02.pdf
  [11]: http://courses.csail.mit.edu/6.006/spring11/rec/rec02.pdf
  [12]: https://raw.github.com/santhosh-tekuri/algorithms/master/images/FindPeak01.png
  [13]: https://raw.github.com/santhosh-tekuri/algorithms/master/images/FindPeak02.png
  [14]: https://raw.github.com/santhosh-tekuri/algorithms/master/images/FindPeak03.png
  [15]: http://people.csail.mit.edu/bdean/6.046/dp/
  [16]: http://dasgupta/chapters/6.2
  [17]: http://people.csail.mit.edu/bdean/6.046/dp/
  [18]: http://people.csail.mit.edu/bdean/6.046/dp/
  [19]: http://www.geeksforgeeks.org/maximum-product-subarray/
  [20]: http://www.geeksforgeeks.org/maximum-sum-such-that-no-two-elements-are-adjacent/
  [21]: http://cormen/exercises/15-3
  [22]: http://web.eecs.umich.edu/~martinjs/math416/soln15-16.pdf
  [23]: http://dasgupta/chapters/6.4
  [24]: http://www.ardendertat.com/2011/10/18/programming-interview-questions-9-convert-array/
  [25]: http://www.geeksforgeeks.org/archives/22238
  [26]: http://en.wikipedia.org/wiki/Magic_square
  [27]: http://en.wikipedia.org/wiki/Magic_constant
  [28]: http://www.geeksforgeeks.org/write-a-c-program-that-given-a-set-a-of-n-numbers-and-another-number-x-determines-whether-or-not-there-exist-two-elements-in-s-whose-sum-is-exactly-x/
  [29]: http://www.geeksforgeeks.org/find-a-pair-with-the-given-difference/
  [30]: http://www.geeksforgeeks.org/two-elements-whose-sum-is-closest-to-zero/
  [31]: http://www.geeksforgeeks.org/equilibrium-index-of-an-array/
  [32]: http://www.careercup.com/question?id=13876739
  [33]: http://www.leetcode.com/2012/01/palindrome-number.html
  [34]: http://cormen/chapters/9.1
  [35]: http://cormen/exercises/9.1-1
  [36]: http://www.csee.wvu.edu/~ksmani/courses/fa01/random/lecnotes/lecture5.pdf
  [37]: http://www.geeksforgeeks.org/minimum-length-unsorted-subarray-sorting-which-makes-the-complete-array-sorted/
  [38]: http://www.geeksforgeeks.org/merging-intervals/
  [39]: http://www.geeksforgeeks.org/find-the-largest-number-multiple-of-3/
  [40]: http://www.geeksforgeeks.org/find-the-largest-multiple-of-2-3-and-5/
  [41]: http://www.geeksforgeeks.org/maximum-length-bitonic-subarray/
  [42]: http://www.geeksforgeeks.org/majority-element/