# Route E grade-recurrent entropy-spread reservoir cube admission

- **ID:** `ROUTE-E-GRADE-RECURRENT-SPARSE-RESERVOIR-CUBE-001`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / EXPLICIT SOURCE RELATION / ROW-ADMISSION SURVIVOR
- **Parent:** `../../1-in-progress/route-e-squarefree-exponential-gibbs-parity.md`
- **Source:** `OPEN-SOURCE-001`
- **RH used:** no
- **Computation used:** no
- **Lean status:** Proposition 3's finite physical-incidence/factorial-capacity core is formalized
  in `RHTower/Sieve/HarmonicReservoirCapacity.lean`; the analytic all-interval structured (E_3)
  input and asymptotic annular-pool statements are not formalized
- **Statement:** Every central squarefree integer at scale (X) is the distinguished corner of a
  source-predeclared family of multiplicative cubes whose coordinate replacements reverse parity,
  change Wold breadth by exactly one with total terminal drift zero or one, keep every corner
  central, spread their subpower-prime reservoirs over a source-independent pool, and have total
  mixed Gibbs cost
  (X^{-1/2+o(1)}) per anchored cube.

## Goal

The active Route E card ended with an unnamed physical relation (R_X).  Fixed-factor (E_3/E_4)
tokens do not define a viable central relation when applied to high-breadth blocks: a replacement
of a block of breadth (k) by three or four primes creates a macroscopic Wold-grade drift, so a
positive cube load at central anchors also loads an off-normal terminal corner.  The off-normal
reservoir is too small to carry central density.

The theorem below removes that defect without assuming Möbius cancellation.  A block of breadth
(k) is replaced by a product of

```text
  k-2 or k-4 fresh reservoir primes  times  one structured E3 token.
```

The replacement has breadth (k+1) or (k-1), hence opposite Möbius parity.  Alternating the two
types over robust active blocks makes full-terminal breadth equal to source breadth or exceed it by
one, while total reservoir product remains (X^{o(1)}).  Reservoirs range over all admissible
allocations from a pool with critical harmonic mass; they are not the least primes missing from
the source.  This choice is forced by the capacity obstructions proved in §6.  The resulting
hypergraph simultaneously passes:

1. positive-density smooth-state admission;
2. central Wold-grade recurrence;
3. joint squarefreeness and coprimality;
4. macroscopic-jump compatibility with the proved sublinear-transport obstruction; and
5. the strict-half mixed Gibbs budget; and
6. the common-terminal-divisor obstruction for deterministic reservoirs; and
7. the harmonic-sparsity obstruction for small reservoir pools.

It does **not** prove incoming physical capacity or co-moving cutoff flux.  Those are isolated at
the end as one exact conjecture on this explicit hypergraph.

## Gates

- [x] 0 → 1 in-progress: explicit source rule, anti-circularity conditions, predecessor no-gos
- [x] 1 → 2 fully-proven: dependency-closed proof below from the existing structured (E_3) input
- [ ] 2 → 3 formalized: requires an unconditional Lean formalization of the structured all-interval
  (E_3) theorem and remaining asymptotic pool laws; no axiom or route hypothesis is admitted
- [ ] 3 → 4 publication-ready: standalone priority and significance audit

## 1. Sparse-forbidden-support (E_3) lemma

The fixed-(B) theorem in `route-e-forbidden-support-e3-stability.md` controls every prime divisor
of (Ale y^B).  Growing-breadth cubes need a different uniformity: the forbidden integer may be
large, but its prime support has only (O(loglog y)) elements.  That sparsity is enough.

### Lemma 1 `[PAPER-PROVED]`

Fix (C>0).  Put

\[
 P_1=(\log y)^{1.1},\qquad
 R={1\over2}\sqrt{y/P_1},\qquad
 h=\sqrt y(\log y)^{1.55}.
\tag{1}
\]

For all sufficiently large (y), uniformly over every finite prime set ({\cal F}) with

\[
 \#{\cal F}\le C\log\log y,
\tag{2}
\]

the interval ((y,y+h]) contains a squarefree product (m=p_1p_2p_3), coprime to
(\prod_{p\in{\cal F}}p), in the structured ranges

\[
 p_1\asymp P_1,\qquad p_2,p_3\asymp R.
\tag{3}
\]

More strongly, deleting ({\cal F}) leaves the same order of lower bound

\[
 \gg {\sqrt y\over(\log y)^{0.45}\log\log y}
\tag{4}
\]

as the structured all-interval theorem.

### Proof

Before deletion, the quantitative structured (E_3) theorem gives `(4)`.  Only forbidden primes
lying in one of the three factor ranges matter.

Fix a forbidden prime (ell\asymp P_1) in the small factor range.  Once (p_2) is chosen, the
condition

\[
 y<\ell p_2p_3\le y+h
\]

places (p_3) in an interval containing (O(\log y)) integers.  The number of primes in the
dyadic (p_2)-range is (O(R/\log R)).  Hence the number of structured products using this
(ell) is

\[
 O\!\left({R\over\log R}\log y\right)
 =O\!\left({\sqrt y\over(\log y)^{0.55}}\right).
\tag{5}
\]

After summing `(5)` over at most (C\log\log y) forbidden small factors, its ratio to `(4)` is

\[
 O_C\!\left({(\log\log y)^2\over(\log y)^{0.1}}\right)=o_C(1).
\tag{6}
\]

Now fix a forbidden prime (ell\asymp R) in either large factor range.  There are
(O(P_1/\log P_1)) possible small primes (p_1), and for each one the other large factor again
lies in an interval containing (O(\log y)) integers.  Thus one forbidden large prime removes at
most

\[
 O\!\left({P_1\log y\over\log P_1}\right)
 =O\!\left({(\log y)^{2.1}\over\log\log y}\right)
\tag{7}
\]

products.  Even (C\log\log y) times `(7)` is (o((4))).  The three factor ranges are disjoint,
and the diagonal (p_2=p_3) was already removed in the structured squarefree theorem.  Therefore
the forbidden products are (o_C(1)) of the original lower bound, proving the lemma. ∎

## 2. Source-predeclared block and reservoir rule

Let (X\to\infty), put

\[
 L=\log\log X,\qquad k=\lfloor\sqrt L\rfloor,
 \qquad Y=\exp((\log X)^{1/3}).
\tag{8}
\]

Let (n\in[X,2X]) be squarefree and satisfy

\[
 {1\over2}L\le\omega(n)\le2L.
\tag{9}
\]

Write (s=\omega(n)), (r=\lceil s/k\rceil), order the prime factors of (n) increasingly, and
split that ordered list into (r) consecutive blocks whose cardinalities differ by at most one.
Let (u_i) be the product of block (i), and (k_i=\omega(u_i)).  For large (X),

\[
 {k\over2}\le k_i\le k,
 \qquad r\le3\sqrt L.
\tag{10}
\]

This partition is a function only of the ordinary factorization of (n) and (X).

Let

\[
 W=\exp(\exp(\sqrt L)),\qquad
 Z=\exp\!\left({\log X\over L^2}\right),\qquad
 {\cal P}_X=\{p\text{ prime}:W<p\le Z\},\qquad M_X=\#{\cal P}_X.
\tag{11}
\]

Since (W=o(Z)), the elementary prime-counting bounds give

\[
 M_X\gg {Z\over\log Z}>4L
\tag{12}
\]

for large (X).

Define the **robust active set**, before choosing any reservoir, by

\[
 I=\left\{i:u_i\ge YZ^{k_i-2}\right\},
 \qquad a=\prod_{i\notin I}u_i.
\tag{13}
\]

Every inactive block satisfies (u_i<YZ^{k_i-2}), so

\[
 a\le Y^rZ^s
 =\exp\!\left(O(\sqrt L(\log X)^{1/3}+\log X/L)\right)
 =X^{o(1)}.
\tag{14}
\]

In particular (I\ne\varnothing) for large (X), since otherwise (n=a=X^{o(1)}), contrary
to (n\ge X).  Write the active indices as (i_1<\cdots<i_d).  Set

\[
 \sigma_{i_j}=(-1)^{j+1}\in\{+1,-1\},\qquad
 b_{i_j}=k_{i_j}-3+\sigma_{i_j}.
\tag{15}
\]

Thus (b_i=k_i-2) on odd active positions and (b_i=k_i-4) on even active positions.  For large
(X), every (b_i) is positive, and

\[
 \sum_{i\in I}\sigma_i\in\{0,1\},
 \qquad K:=\sum_{i\in I}b_i\le s.
\tag{16}
\]

Choose **any** ordered tuple of pairwise disjoint sets

\[
 R_i\subseteq{\cal P}_X\setminus\{p:p\mid n\},
 \qquad \#R_i=b_i\quad(i\in I),
\tag{17}
\]

and put

\[
 t_i=\prod_{p\in R_i}p,\qquad T=\prod_{i\in I}t_i.
\tag{18}
\]

At most (K\le s\le2L) reservoir primes are required, while the source excludes at most (s) pool
primes, so `(12)` makes `(17)` possible.  Uniformly over every allocation,

\[
 T\le Z^K\le Z^s
 =\exp\!\left({s\log X\over L^2}\right)
 =X^{O(1/L)}=X^{o(1)}.
\tag{18a}
\]

The relation contains all allocations `(17)`.  No allocation is selected after inspecting a
Möbius imbalance.  Reservoir and structured-(E_3) factor ranges may overlap; this causes no
collision because every reservoir prime is inserted into the forbidden support in §3, and Lemma 1
is uniform over that (O(L))-element set.

## 3. Grade-recurrent replacements

For (i\in I), `(13)`, `(15)`, and `(17)` give

\[
 y_i:={u_i\over t_i}\ge {u_i\over Z^{k_i-2}}\ge Y.
\tag{18b}
\]

Process the active indices in increasing order.  At stage (i), forbid every prime dividing

```text
n, every reservoir t_j, and every earlier E3 token m_j.
```

The forbidden set has cardinality at most

\[
 2L+2L+3r\le5L.
\tag{19}
\]

Since (y_i\ge Y),

\[
 \log\log y_i\ge {1\over3}L,
\tag{20}
\]

so `(19)` is at most (15\log\log y_i).  Lemma 1 with (C=15) supplies a structured
squarefree (E_3) number

\[
 y_i<m_i\le y_i+\sqrt{y_i}(\log y_i)^{1.55}
\tag{21}
\]

avoiding every forbidden prime.  Define

\[
 q_i=t_im_i.
\tag{22}
\]

Then all (q_i) are pairwise coprime and coprime to (a), and

\[
 \omega(q_i)=b_i+3=k_i+\sigma_i,
 \qquad \mu(q_i)=-\mu(u_i).
\tag{23}
\]

Moreover

\[
 0<q_i-u_i
 \le \sqrt{u_it_i}(\log u_i)^{1.55}.
\tag{24}
\]

The reservoir is the key point: `(23)` reverses parity while changing Wold breadth by exactly
(\sigma_i\in\{+1,-1\}), independent of the original block breadth (k_i\to\infty).  The alternating
source-predeclared signs retain the local checkerboard while preventing a monotone drift into a
single Wold tail.

## 4. The explicit cube relation

For every (S\subseteq I), define the physical corner

\[
 v_S
 =a\prod_{i\in S}q_i\prod_{i\in I\setminus S}u_i.
\tag{25}
\]

Let ({\cal R}^{\mathrm{gr}}_X) be the family of all cubes `(25)` obtained from **all** reservoir
allocations `(17)` and **all** admissible sequential choices `(21)`.  This is the explicit
source-predeclared Route E hypergraph.  It depends only on (X), ordinary factorization, ordered
primes, and the structured almost-prime ranges.  It does not inspect (M(X)), a partial-sum sign,
an exceptional set chosen from Möbius imbalance, or a divisor point.

Joint coprimality gives the exact checkerboard law

\[
 \mu(v_S)=(-1)^{|S|}\mu(n).
\tag{26}
\]

It also gives the exact Wold-grade law

\[
 \omega(v_S)=\omega(n)+\sum_{i\in S}\sigma_i.
\tag{27}
\]

In particular, `(16)` gives the sharp full-terminal law

\[
 \omega(v_I)-\omega(n)\in\{0,1\}.
\tag{27a}
\]

Since (|\sum_{i\in S}\sigma_i|\le|I|\le3\sqrt L=o(L)), every corner remains in the same central
normal sector:

\[
 {\omega(n)\over L}\longrightarrow1
 \quad\Longrightarrow\quad
 \max_{S\subseteq I}\left|{\omega(v_S)\over L}-1\right|\longrightarrow0.
\tag{28}
\]

The corners are also co-moving on one multiplicative scale.  From `(18b)` and `(24)`, uniformly in
(i\in I),

\[
 {q_i-u_i\over u_i}
 \le Y^{-1/2}(\log X)^{1.55}.
\tag{29}
\]

The right side decays faster than every power of (1/\log X), while (|I|=O(\sqrt L)).  Hence

\[
 \max_{S\subseteq I}{v_S\over n}=1+o(1).
\tag{30}
\]

The numerical jumps in `(30)` may be (X^{1-o(1)}).  This is required, not a defect: the proved
smooth-state obstruction excludes every uniformly sublinear first-order transport.  What stays
critical is the full mixed difference.

## 5. Strict-half mixed Gibbs cost

Let (d=|I|), (x\asymp X^{-1}), and attach to cube `(25)` the full (d)-fold exponential
difference.  The all-breadth mixed derivative theorem `(G72)`--`(G74)` in the parent card bounds
its absolute value by

\[
 x d^d a\prod_{i\in I}|q_i-u_i|.
\tag{31}
\]

Using `(24)`, (\prod_{i\in I}u_i=n/a), and (\prod_{i\in I}t_i\le T), the right side is at most

\[
 x d^d a
 \sqrt{{n\over a}T}\,(\log X)^{1.55d}
 =x d^d\sqrt{anT}\,(\log X)^{1.55d}.
\tag{32}
\]

Equations `(10)`, `(14)`, and `(18a)` imply

\[
 d^d(\log X)^{1.55d}\sqrt{aT}=X^{o(1)}.
\tag{33}
\]

Since (n\asymp X) and (x\asymp X^{-1}), `(32)`--`(33)` prove

\[
 x d^d a\prod_{i\in I}|q_i-u_i|
 =X^{-1/2+o(1)}.
\tag{34}
\]

Thus one anchored cube per (O(X)) squarefree vertices has aggregate analytic cost
(X^{1/2+o(1)}).  No short numerical edge, pointwise Möbius estimate, or cumulative Mertens input
is used.

## 6. Deterministic-reservoir no-go and positive survivor

The first version of this construction assigned to each block the least reservoir primes missing
from the source.  That rule passes every row calculation above and still fails physical capacity.
The failure is not heuristic.

### Proposition 2 `[PAPER-PROVED NO-GO]`

Let a source-predeclared cube family have distinguished anchors (n\in A), and suppose every cube
anchored in (A) has a terminal corner in ([cX,CX]) divisible by one fixed integer (P>1).  If
nonnegative cube weights give every physical terminal load at most one, then the total anchored
load on (A) is at most

\[
 O_{c,C}(X/P+1).
\tag{35}
\]

Consequently its uncovered anchor load is at least

\[
 \#A-O_{c,C}(X/P+1).
\tag{36}
\]

#### Proof

Every weighted cube contributes the same coefficient to its distinguished anchor and its chosen
terminal.  Sum first over cubes and then over physical terminals.  All terminals are multiples of
(P), there are (O_{c,C}(X/P+1)) of those in ([cX,CX]), and each has load at most one.  This proves
`(35)`.  Subtracting anchored load from the unit capacity of (A) proves `(36)`. ∎

### Application to least-missing-prime reservoirs

Let ({\cal Q}_X) be the first (4L) primes.  The squarefree integers in ([X,2X]) coprime to
(\prod_{p\in{\cal Q}_X}p) have cardinality

\[
 \gg {X\over\log L}.
\tag{37}
\]

Indeed, expanding the squarefree indicator and then the coprimality condition gives the main
factor

\[
 {6\over\pi^2}\prod_{p\in{\cal Q}_X}{p\over p+1}\asymp {1\over\log L},
\]

with error (O(\sqrt X\,2^{4L})=X^{1/2+o(1)}).  The existing two-sided Wold deviation bound removes
the noncentral part without changing the order in `(37)`.

Now use the least-missing-prime rule with (b_i) reservoir primes in active block (i).  On this
family, after fixing (s=\omega(n)) and the active set (I), the complete ordered reservoir list is
the same list of the first (K=\sum_{i\in I}b_i) primes.  Partition `(37)` by (s) and by (I).
There are at most
(O(L)2^{3\sqrt L}=\exp(O(\sqrt L))) classes, so one nonempty-active class (A) has

\[
 \#A\ge X\exp(-O(\sqrt L)).
\tag{38}
\]

For that class, the product (P) of reservoir primes assigned to the active blocks is fixed, divides
every full terminal corner, and contains at least (k/2-4) distinct primes.  Hence

\[
 \log P\gg \sqrt L\log L.
\tag{39}
\]

All terminal corners lie in ([cX,CX]) by `(30)`.  Equations `(35)`, `(38)`, and `(39)` force

\[
 \text{uncovered load}\ge
 X\exp(-O(\sqrt L))-X\exp(-\Omega(\sqrt L\log L))
 =X^{1-o(1)}.
\tag{40}
\]

Thus a deterministic least-prime reservoir fails far above the strict-half scale even though its
row admission, parity, central grade, and mixed Gibbs cost are all correct.  This is a new
separation between analytic row quality and physical terminal capacity.

The entropy-spread relation `(17)` is the strongest immediate survivor.  For every anchor it
contains every admissible (K)-prime allocation from a pool of size (M_X\gg Z/\log Z).  Given any fixed
packet (B) with (\#B\le M_X-2s), that row contains allocations disjoint from (B); no nontrivial
source-independent packet divides all of its terminal corners.  Lemma 1 and `(24)` are uniform in
the allocation, so this repair loses no row supply or mixed-cost exponent.  It removes the exact
obstruction above; it does not by itself prove arbitrary-subset Hall expansion.

That repair still leaves a second obstruction: set cardinality of the prime pool is irrelevant if
its reciprocal mass is too small.

### Proposition 3 `[PAPER-PROVED NO-GO / SHARP NECESSARY SCALE]`

Let ({\cal P}) be a finite prime pool and

\[
 S({\cal P})=\sum_{p\in{\cal P}}{1\over p}.
\tag{41}
\]

The number of integers (v\in[cX,CX]) having at least (K) distinct prime divisors from ({\cal P})
is at most

\[
 CX\,e_K\bigl((1/p)_{p\in{\cal P}}\bigr)
 \le CX\,{S({\cal P})^K\over K!}
 \le CX\left({eS({\cal P})\over K}\right)^K.
\tag{42}
\]

Here (e_K) is the elementary symmetric polynomial.  Indeed,

\[
 {f1}_{\omega_{\cal P}(v)\ge K}
 \le {\omega_{\cal P}(v)\choose K};
\]

summing and exchanging the order of summation leaves, for every (K)-set (R\subseteq{\cal P}),
at most (CX/\prod_{p\in R}p) multiples.  The first inequality in `(42)` follows.  Expanding
(S({\cal P})^K) counts every distinct (K)-tuple (K!) times and also counts repeated tuples, giving
the second; (K!\ge(K/e)^K) gives the third. ∎

Every full terminal of the cube relation contains the reservoir of one active block, hence at
least (K_0=\lfloor k/2\rfloor-4) primes from ({\cal P}_X).  If the earlier polynomial pool
({\cal P}_X=\{p\le L^4\}) were used, Mertens' reciprocal-prime law would give

\[
 S({\cal P}_X)=O(\log\log L)=o(K_0).
\tag{43}
\]

Then `(42)` would bound the complete physical terminal set by

\[
 X\exp(-\Omega(\sqrt L\log L)),
\tag{44}
\]

so terminal load at most one would leave (X-o(X)) of the central anchor capacity uncovered.  Thus
even a nondeterministic pool with enormous raw cardinality fails if it is harmonically sparse.

The annular aperture `(11)` is the first simple scale used here which passes both obstructions
without spending a power
of (X).  Mertens' law gives

\[
 S({\cal P}_X)=\log\log Z-\log\log W+O(1)
 =L-2\log L-\sqrt L+O(1),
\tag{45}
\]

while `(18a)` gives (T=X^{O(1/L)}).  On the central sector (s=(1+o(1))L), every active reservoir
breadth is at most (s), so `(45)` reaches the full physical breadth scale; at the same time total
reservoir size remains subpower.  More generally, `(42)` proves the necessary design law

\[
 S({\cal P}_X)\not=o(K_X)
\tag{46}
\]

for any fixed-pool relation forcing (K_X\to\infty) pool primes into every terminal.  The new pool
passes this necessary gate.  Proving sufficient interval Hall expansion remains open.

### Proposition 4 `[PAPER-PROVED POSITIVE SURVIVOR]`

Put (x_p=1/p).  For (O\subseteq{\cal P}_X) with (\#O\le2L), write

\[
 S_O=\sum_{p\in{\cal P}_X\setminus O}x_p.
\]

Uniformly for (1\le m\le2L),

\[
 S_O^m-{m\choose2}{1\over W}S_O^{m-1}
 \le m!e_m\bigl((x_p)_{p\in{\cal P}_X\setminus O}\bigr)
 \le S_O^m.
\tag{47}
\]

The upper bound is immediate by expanding (S_O^m): the distinct ordered (m)-tuples contribute
exactly (m!e_m), and all repeated tuples have nonnegative weight.  For the lower bound, every
repeated tuple has some equal pair of positions.  A union bound over those pairs gives total
repeated weight at most

\[
 {m\choose2}\sum_p x_p^2 S_O^{m-2}
 \le {m\choose2}{1\over W}S_O^{m-1},
\]

because every pool prime exceeds (W).  This proves `(47)`.

Source exclusion is asymptotically invisible:

\[
 0\le S({\cal P}_X)-S_O\le{2L\over W}=o(1).
\tag{48}
\]

Together with `(45)` and `(47)`, this gives, uniformly over every central source support and every
(m\le2L),

\[
 e_m\bigl((1/p)_{p\in{\cal P}_X\setminus O}\bigr)
 ={S({\cal P}_X)^m\over m!}(1+o(1)).
\tag{49}
\]

There is also an exact ordered-block identity.  For nonnegative block sizes
(b_1+\cdots+b_r=m),

\[
 \sum_{\substack{R_i\subseteq{\cal P}_X\setminus O,\ \#R_i=b_i\\
                     R_i\cap R_j=\varnothing\ (i\ne j)}}
       \prod_{i=1}^r{1\over\prod_{p\in R_i}p}
 ={m!\over\prod_i b_i!}
   e_m\bigl((1/p)_{p\in{\cal P}_X\setminus O}\bigr).
\tag{50}
\]

Indeed, first choose the union (R) and then assign its (m) elements to labeled blocks of sizes
(b_i); every union has exactly (m!/\prod_i b_i!) assignments.  Equations `(49)`--`(50)` give a
canonical source-predeclared row probability: weight a reservoir allocation proportionally to
(1/T).  Its normalizing constant is source-uniform up to (1+o(1)), despite adversarial central
source support.  This closes harmonic row normalization and exclusion stability.  It does not
identify equal physical terminal integers coming from different anchors or prove interval Hall.

### Proposition 5 `[PAPER-PROVED POSITIVE SEAM ADMISSION]`

Let the moving large-prime aperture (z=z(X)) satisfy

\[
 {z\over\sqrt X}\longrightarrow\infty,
 \qquad \log z=\left({1\over2}+o(1)\right)\log X.
\tag{51}
\]

This includes the critical Route E schedule.  For large (X), every prime factor of every
replacement (q_i) is at most (z).  Indeed, reservoir factors are at most
(Z=X^{1/L^2}=o(\sqrt X)); the structured small factor is ((\log y_i)^{1.1}=X^{o(1)}); and the two
balanced factors are at most (\sqrt{y_i/P_1}\le\sqrt{2X}).

Suppose an anchor (n) has exactly one prime factor (p>z), and let (j) be its block.  Then

\[
 \log t_j\le k_j\log Z\le{\log X\over L^{3/2}},
 \qquad
 \log {u_j\over t_j}\ge\left({1\over2}-o(1)\right)\log X.
\tag{52}
\]

Hence (u_j/t_j\ge Y), so (j\in I) for every reservoir allocation.  Since all replacement factors
are (z)-smooth, the cube has the exact sector law

\[
 \#\{p>z:p\mid v_S\}=
 \begin{cases}
 1,&j\notin S,\\
 0,&j\in S.
 \end{cases}
\tag{53}
\]

If (n) has no prime factor above (z), every corner also remains in the zero-large-prime sector.
Thus the explicit relation admits the critical (1\to0) seam through one distinguished coordinate
on every one-large-prime anchor; it never invents a large prime on the friable face.  Static full
cube summation can still cancel this sector marginal, so `(53)` is admission, not the required
co-moving weighted flux theorem.

## 7. Hostile audit

### What is closed

- **Positive-density smooth states.**  Blocks for which the reservoir dominates are absorbed into
  (a=X^{o(1)}); they cannot consume a positive-scale part of (n).  Active blocks therefore carry
  (n/X^{o(1)}), even on a globally friable source integer.
- **Wold marginal drift.**  Fixed (E_3/E_4) tokens can move a high-breadth block to bounded
  breadth.  Here every coordinate changes breadth by exactly (+1) or (-1), and full-terminal drift
  is exactly zero or one by `(27a)`; arbitrary corners move by only (O(\sqrt L)=o(L)).
- **Sublinear-transport obstruction.**  Individual corners are allowed macroscopic movement;
  only the mixed volume `(34)` is small.
- **Finite-block ceiling.**  The number of coordinates grows.  Sparse-forbidden Lemma 1 replaces
  the fixed-(B), fixed-coordinate hypothesis of the earlier admission theorem.
- **Source theatre.**  Relation ({\cal R}^{\mathrm{gr}}_X) is defined before any Möbius imbalance
  is observed.  Its parity comes from exact factor count `(23)`, not from a sign-density theorem.
- **Deterministic terminal concentration.**  Proposition 2 kills least-prime reservoirs.  Relation
  ({\cal R}^{\mathrm{gr}}_X) retains all entropy-spread allocations and has no forced common
  reservoir divisor.
- **Harmonic terminal scarcity.**  Proposition 3 kills every pool with reciprocal mass
  (o(\sqrt L)), including every fixed polylogarithmic aperture.  The critical subpower pool `(11)`
  has reciprocal mass ((1-o(1))L) while its total reservoir product is still (X^{o(1)}).
- **Reservoir exclusion stability.**  Proposition 4 proves exact weighted allocation identity
  `(50)` and uniform asymptotic `(49)`.  Source prime support cannot drain the annular pool, so
  reciprocal allocation weights are row-normalized without post hoc balancing.
- **Seam geometry.**  Proposition 5 identifies one forced-active crossing coordinate on every
  one-large-prime anchor and proves exact zero/one sector law `(53)`.  Remaining seam problem is
  weighted co-moving flux, not existence of sector-crossing cells.

### What is not closed

Row admission is not fractional physical capacity.  Different anchored cubes may reuse the same
physical corners.  Arbitrarily normalizing representation labels cannot increase the neighbor
union.  Static complete cubes also conserve zero/one-large-prime sector marginals; their only
admissible use at the moving aperture is through cutoff-crossing flux.

Therefore this theorem does not imply a Möbius bound or RH.

## 8. New exact Route E conjecture

`[CONJECTURE: ENTROPY-SPREAD-GRADE-RECURRENT-CUBE-CAPACITY]`

At the critical aperture, restrict the **explicit** hypergraph
({\cal R}^{\mathrm{gr}}_X) to an extended multiplicative window containing all corners `(25)`.
There are nonnegative cube weights (c_R), chosen from this source relation alone, such that:

1. every physical integer corner has total load at most one;
2. central uncovered Gibbs load is (X^{1/2+o(1)});
3. the restrictions of the loaded cubes to every physical interval satisfy the exact
   interval-Hall/Carleson capacity inequality after projecting cube corners to opposite parity;
4. at the moving zero/one-large-prime cutoff, the two sector fluxes reproduce the normalized
   friable charge (-1) and one-large-prime charge (+1); and
5. the aggregate mixed cost is (X^{1/2+o(1)}).

`[OPEN CORE]` Prove items 1--4.  Item 5 and source-pure row admission are now theorems.  This is no
longer an existential (R_X): the only permitted edges and higher cells are those of
({\cal R}^{\mathrm{gr}}_X).

## 9. Scientific status

`[PAPER-PROVED] [NOVELTY UNVERIFIED]` for Lemma 1 and the row-admission/mixed-cost theorem
`(8)`--`(34)` and for Propositions 2--5.

`[CONJECTURE]` for the capacity and co-moving-flux statement in §8.

`[LEAN-PROVED]` for the finite physical incidence inequality, reciprocal-layer factorial bound,
and combined harmonic terminal-capacity theorem in
`formal/GaloisForLFunctions/RHTower/Sieve/HarmonicReservoirCapacity.lean`.  Axiom audit reports
only `[propext, Classical.choice, Quot.sound]`.

The mathematical delta has five parts.  First, grade-recurrent reservoir representation retains
growing Wold breadth physically while a structured (E_3) theorem supplies every parity-reversing
coordinate at subpower total reservoir cost.  Second, Proposition 2 discovers a hidden terminal
divisibility obstruction which invalidates deterministic least-prime reservoirs and forces the
entropy-spread source relation.  Third, Proposition 3 proves that raw reservoir entropy is
irrelevant below the harmonic threshold and identifies (Z=X^{1/L^2}) as a pool with central
reciprocal mass but subpower total product.  Fourth, Proposition 4 proves a source-uniform
reciprocal allocation law on the annular pool, giving the first canonical row weighting for this
relation.  Fifth, Proposition 5 proves literal zero/one-large-prime seam admission through a
forced-active coordinate.  Prior Route E cube statements had neither a formula valid on the
smooth central bulk nor these two row-versus-physical-capacity separations and their positive
weighted and seam survivors.

## Log

- 2026-08-04 — proved sparse-forbidden (E_3) stability for (O(\log\log y)) adversarial prime
  support; constructed the explicit grade-recurrent sparse-reservoir cube relation; proved central
  corner retention and (X^{-1/2+o(1)}) per-row mixed Gibbs cost; isolated physical capacity and
  co-moving flux as the sole remaining conjectural clauses.
- 2026-08-04 — hostile capacity audit killed deterministic least-missing-prime reservoirs by the
  common-terminal-divisor no-go `(35)`--`(40)`; replaced them with all allocations from the
  source-independent pool ({\cal P}_X); rechecked row admission, squarefreeness, multiplicative
  scale, and mixed Gibbs cost uniformly over every allocation.
- 2026-08-04 — second capacity audit killed the polynomial pool (p\le L^4): despite its large
  cardinality, its reciprocal mass is (o(\sqrt L)), so the binomial-divisor moment `(42)` makes its
  whole terminal set (X\exp(-\Omega(\sqrt L\log L))).  Replaced it by the critical harmonic
  annulus (\exp(\exp\sqrt L)<p\le X^{1/L^2}), whose reciprocal mass is
  (L-2\log L-\sqrt L+O(1)) while every total reservoir product is (X^{O(1/L)}); proved general
  necessary design law `(46)` and exact source-uniform reciprocal allocation law `(47)`--`(50)`.
- 2026-08-04 — proved critical seam admission `(51)`--`(53)`: replacement tokens are uniformly
  below the moving aperture, while the block containing a unique large source prime is active for
  every reservoir allocation.  Exact (1\to0) cube coordinate now exists; weighted co-moving flux
  across that coordinate remains open.
- 2026-08-04 — killed monotone (+3)-per-coordinate grade choice: its full terminal can sit a fixed
  number of Wold standard deviations above the anchor.  Replaced it by robust source-defined
  active blocks and alternating (+1,-1) grade changes using reservoir breadths (k_i-2,k_i-4).
  Full-terminal Wold drift is now exactly zero or one, without changing parity or mixed-cost scale.
- 2026-08-04 — formalized Proposition 3's finite core as
  `Sieve/HarmonicReservoirCapacity.lean`: physical target-to-divisor-subset incidence, reciprocal
  elementary-symmetric layer weight, and factorial harmonic capacity.  Targeted module build and
  axiom audit pass; no full build run.
