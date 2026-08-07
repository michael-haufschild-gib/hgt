# Route E antiscale first-trace frame law

- **ID:** `ROUTE-E-ANTISCALE-FIRST-TRACE-FRAME-001`
- **Stage:** 2-fully-proven
- **Type:** `[EXACT CHANNEL CLASSIFICATION]` / `[POSITIVE FRAME]` / `[NORMALIZATION NO-GO]`
- **Scientific status:** `[PAPER-PROVED] [INTERNAL COLLISION-AUDITED] [EXTERNAL NOVELTY UNVERIFIED]`
- **Parent:** `../../1-in-progress/route-e-cofinal-parity-energy-covariance-accumulation.md`
- **RH used:** no
- **Computation used:** no

## Purpose

The prime-sieve normalization audit left a possible signed first-trace/Bockstein
countertransport at the normalized reciprocal-prime layer.  This card determines exactly what
every **scalar** such countertransport can do.  It also identifies the first non-scalar replacement:
the all-prime harmonic antiscale frame supplied by the new character-distance theorems.

The result does not bound the Route E current.  It removes an invalid scalar continuation and
replaces the vague phrase “moving-antiscale estimate” by one exact unresolved handoff: transport
the prefix-dependent Gibbs seams into the common harmonic frame without losing the coherent mode.

## 1. Exact two-channel insertion law

Let (A,B>0) and (x,y\in\mathbb R).  In the Gibbs specialization,

\[
 A=Z_S(u),\qquad B=Z_S(pu),\qquad
 x=\psi_S(u),\qquad y=\psi_S(pu).
\]

Put

\[
 \beta={B\over A+B},\qquad
 \alpha={A-B\over A+B}=1-2\beta,
\]

and introduce the antiscale and same-sign coordinates

\[
 a={x-y\over2},\qquad s={x+y\over2}.
\]

The normalized signed insertion is

\[
 h={Ax-By\over A+B}=x-\beta(x+y).
\]

Therefore

\[
 \boxed{h=a+\alpha s.}                                      \tag{1}
\]

Thus insertion is diagonal in the ((a,s)) channels: the antiscale channel is transmitted with
coefficient exactly (1), while only the same-sign channel sees the contraction (alpha).
The null direction of the earlier positive dissipation is consequently not just a zero set of a
quadratic form; it is the exact unit-eigenvalue channel of signed insertion.

### Proof

Use (x=a+s), (y=s-a):

\[
 {A(a+s)-B(s-a)\over A+B}
 =a+{A-B\over A+B}s.
\]

No estimate is involved.

## 2. Scalar first-trace/Bockstein classification

Let (q\ne0) be a scalar source normalization and let the post-insertion normalization be
(q'=\lambda q), where (lambda\ne1).  Its normalized first difference is

\[
 \mathfrak B_\lambda(x,y)
 ={qx-q'h\over q-q'}={x-\lambda h\over1-\lambda}.
\]

Substituting `(1)` gives the exact classification

\[
 \boxed{
 \mathfrak B_\lambda(x,y)
 =a+{1-\lambda\alpha\over1-\lambda}s
 =x+{\lambda\beta\over1-\lambda}(x+y).
 }                                                           \tag{2}
\]

In particular,

\[
 y=-x\quad\Longrightarrow\quad
 \boxed{\mathfrak B_\lambda(x,-x)=x.}                       \tag{3}
\]

Every scalar normalization Bockstein is therefore the identity on the exact Route E escape mode.
It can add, subtract, or amplify only the same-sign channel.  This includes the coprime-sieve
normalization (lambda=1-p^{-1}) and the reciprocal critical Euler normalization.  Their precise
coefficients differ, but their antiscale restriction is identical.

### Consequence

The “signed first-trace/Bockstein countertransport” left by the prime-sieve normalization wall
cannot be scalar.  A viable countertransport must retain at least two channels and act
nontrivially on (a), using cross-prime information.  Scalar rescaling before positive norm cannot
cancel the normalized (p^{-1}) transition when antiscale coherence occurs.

## 3. Exact harmonic antiscale frame

For a finite prime set (P), a real Mellin frequency (t), and

\[
 \chi_t(p)=e^{it\log p},
\]

the same-sign seam multiplier is (1+\chi_t(p)).  Since

\[
 |1+e^{i\theta}|^2=2(1+\cos\theta),
\]

the character-distance identity for a function taking value (-1) on (P) gives

\[
 \boxed{
 \sum_{p\in P}{|1+\chi_t(p)|^2\over p}
 =2D(-1,\chi_t;P)^2.
 }                                                           \tag{4}
\]

This is the exact spectral frame energy of the same-sign channels.  In particular, the corpus
theorem `exists_mulDistSqPair_ge_uniform` implies that there is an absolute (C) such that, for
(z\ge3), (T\ge9), (|t|\le T), and

\[
 {1\over\log z}\le {A_\zeta\over(\log T)^9},
\]

one has

\[
 \boxed{
 \sum_{p\le z}{|1+\chi_t(p)|^2\over p}
 \ge2\bigl(\log\log z-7\log\log T-C\bigr).
 }                                                           \tag{5}
\]

Hence no single Mellin phase can remain antiscale-coherent across the full harmonic prime packet.
The moving terminal resonance (t=\pi/\log z) aligns the terminal window, but earlier primes force
the global frame energy in `(5)`.  The terminal resonance no-go and the global frame theorem are
compatible: one is local in prime scale, the other retains all reciprocal-prime weights.

### Sharp harmonic ceiling

The frame is globally coercive but cannot by itself generate a power of the physical scale.  For
every \(t\),

\[
 \boxed{
 \sum_{p\in P}{|1+\chi_t(p)|^2\over p}
 \le 4\sum_{p\in P}{1\over p}.
 }                                                           \tag{5a}
\]

Equality holds at \(t=0\).  Thus complete cofinal frame mass is only
\(4\log\log z+O(1)\).  Exponentiating independent harmonic contractions can produce at most
powers of \(\log z\), precisely the already-known scale-invariant
\(\prod_{p\le z}(p-1)/(p+1)\) baseline.  A claim that \((5)\) alone yields \(x^{1/2}\) invents
missing mass.  Any power gain must come from nonproduct moving-boundary dependence of literal
integer source.

## 4. Order-free batch dispersion

Let (S,P) be disjoint finite prime sets.  For (T\subseteq P), put

\[
 m_T=\prod_{p\in T}p,\qquad
 w_T=Z_S(m_Tu)>0,\qquad
 g_T=(-1)^{|T|}\psi_S(m_Tu),\qquad W=\sum_{T\subseteq P}w_T.
\]

Repeated use of the exact current/partition insertion laws gives

\[
 Z_{S\cup P}(u)=W,\qquad
 J_{S\cup P}(u)=\sum_{T\subseteq P}w_Tg_T.                \tag{6}
\]

Define the leaf energy and batch dispersion by

\[
 \mathcal L_{S,P}(u)=\sum_{T\subseteq P}w_Tg_T^2,
\]

\[
 \mathcal R_{S,P}(u)=
 {1\over2W}\sum_{T,U\subseteq P}w_Tw_U(g_T-g_U)^2.
\]

The finite weighted-variance identity yields

\[
 \boxed{
 {J_{S\cup P}(u)^2\over Z_{S\cup P}(u)}
 +\mathcal R_{S,P}(u)=\mathcal L_{S,P}(u).
 }                                                           \tag{7}
\]

Moreover (mathcal R_{S,P}(u)=0) exactly when all (g_T) agree, equivalently

\[
 \psi_S(m_Tu)=(-1)^{|T|}c\qquad(T\subseteq P)             \tag{8}
\]

for one scalar (c).  Thus full batch escape is simultaneous checkerboard antiscale coherence of
one common prefix current, not a collection of unrelated prefix conditions.  Sequential sums of
the one-prime dissipations in any insertion order equal the same order-free residual
(mathcal R_{S,P}).

### Proof

Equation `(6)` follows by induction on (P).  Normalize the positive weights by (W).  Then

\[
 {1\over2W}\sum_{T,U}w_Tw_U(g_T-g_U)^2
 =\sum_Tw_Tg_T^2-{(\sum_Tw_Tg_T)^2\over W},
\]

which, together with `(6)`, proves `(7)`.  Positivity of every (w_T) proves the null-space
classification `(8)`.  Iterating the one-step polarization law and comparing with `(7)` proves
order independence.

## 5. New exact frontier

Equations \((1)\)--\((3)\) close scalar Bockstein question negatively.  Equations
\((4)\)--\((5)\) prove that a **common linear Mellin phase** cannot realize global harmonic
antiscale coherence, while \((5a)\) proves that this frame alone remains logarithmic.  Equation
\((7)\) removes changing-prefix ambiguity by placing a whole prime block over one base current.

The surviving hard theorem is now:

> **`GIBBS-MOVING-BOUNDARY-NONPRODUCT-FRAME`.**  At the physical moving aperture, prove that the
> literal Gibbs leaf law in \((7)\) has a boundary-correlation component, absent from its
> reciprocal-prime product approximation, whose checkerboard dispersion is
> \(1-x^{1-o(1)}\) of relevant leaf energy.  Proof must retain Gibbs weights \(w_T\), full subset
> checkerboard, and moving prime blocks.

This is not \((A1)\) restated: \((5)\) is an independently proved arithmetic frame inequality,
\((5a)\) fixes its exact ceiling, and \((7)\) is an independently proved source batch identity.
Open handoff is concrete failure of harmonic product approximation at multiplicative cutoff.  It
must prove all three:

1. prefix stabilization inside a batch, so the seams are observations of one common log signal;
2. high-log-frequency control strong enough to prevent terminal resonance from carrying whole
   leaf energy;
3. a quantitative moving-boundary correlation supplying missing power beyond \(\sum 1/p\).

None follows from endpoint identity \((A7)\).  Generic Fourier truncation is insufficient, and a
product Bernoulli approximation is provably too weak by \((5a)\).  This returns load-bearing
problem to integer boundary interaction isolated independently by physical Hall lane.

## Hostile audit

1. `(2)` is a classification/no-go, not Route E closure.
2. \((5)\) has only harmonic logarithmic size, sharply certified by \((5a)\).  Repeating or
   exponentiating it yields only log powers; claiming a physical power would be theatre.
3. The character-distance phase is common across primes.  Actual one-step Gibbs seams have changing
   prefixes; `(7)` is the exact infrastructure needed to address that mismatch.
4. The terminal resonance remains real.  Any high-frequency remainder estimate that assumes it
   absent is false.
5. No Mertens bound, RH-equivalent endpoint estimate, zero-free half-plane, or computation enters
   `(1)`--`(7)`.
6. `OPEN-SOURCE-001` and RH remain open.

## Formalization target

Formalize unconditionally:

- the two-channel insertion identity `(1)`;
- scalar Bockstein classification `(2)` and antiscale restriction `(3)`;
- harmonic frame identity `(4)` and uniform lower bound `(5)` from
  `Sieve.MoebiusUniformFrequency`;
- sharp harmonic ceiling \((5a)\);
- finite weighted batch dispersion algebra `(7)` and its exact null space.

Source-specific subset expansion \((6)\), source batch polarization \((7)\), and checkerboard null
space are formalized by reusing existing Gibbs insertion recursion.  No new analytic assumption
is permitted.
