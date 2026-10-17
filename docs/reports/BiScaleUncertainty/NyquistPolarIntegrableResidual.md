# Nyquist polar production with an absolutely summable residual

## Domain and status

Dependency-closed paper proof and Lean certificate; package 14, counted once. The topic
remains infinite-grid tail rigidity for general signed correlations. The field
README is read-only. Existing Nyquist producer constants and their pointwise error
bounds are reused inputs, not new results.

For n>=1 write a_n=log n, I_n=[a_n,a_(n+1)], and
C_n=cosh((log n)/2). Define the nonnegative continuous cell error

    e_n(x)=cosh(x/2)-C_n,  x in I_n.

The existing explicit producer theorem gives 0<=e_n(x)<=1/(4 sqrt(n)).
The cell length satisfies log(n+1)-log n=log(1+1/n)<=1/n. Consequently,

    alpha_n=integral_I_n e_n <= 1/(4 n sqrt(n)).

## 1. An explicit telescoping majorant

For every real n>=1,

    1/(4 n sqrt(n)) <= 1/sqrt(n)-1/sqrt(n+1).

Indeed, rationalizing the right side gives
1/[sqrt(n)sqrt(n+1)(sqrt(n+1)+sqrt(n))]. Multiplying positive denominators
reduces the assertion to

    n+1+sqrt(n(n+1)) <= 4n.

Here n+1<=2n and sqrt(n(n+1))<=2n, the latter following by squaring two
nonnegative sides and using n+1<=4n. Therefore, for integers M>=N>=1,

    sum_(n=N..M) alpha_n <= 1/sqrt(N)-1/sqrt(M+1).

Every alpha_n is nonnegative. Monotone partial sums and the vanishing reciprocal
square root prove absolute summability and the unconditional tail estimate

    A_N=sum_(n>=N) alpha_n <= 1/sqrt(N).

This controls the complete infinite tail, independently of source support or
the number of cells. It is stronger in domain than a bound on one dyadic window.

## 2. A bounded positive residual functional

Let H be any bounded continuous real function on the real line. Define actual
cell residuals and their infinite tail by

    r_n(H)=integral_I_n H(x)e_n(x) dx,
    R_N(H)=sum_(n>=N) r_n(H).

Continuity ensures each finite-cell integral exists. Nonnegativity of e_n gives
|r_n(H)|<=||H||_infinity alpha_n. Thus the series is absolutely convergent and

    |R_N(H)| <= A_N ||H||_infinity <= ||H||_infinity/sqrt(N).

Finite integral linearity and absolute convergence prove linearity of R_N.
For H>=0 pointwise, every summand is nonnegative, so R_N is positive. Applying
the same estimate to H-G gives

    |R_N(H)-R_N(G)| <= A_N ||H-G||_infinity.

The exact operator norm on bounded continuous real functions is A_N: the upper
bound was proved, and the constant function one has norm one and R_N(1)=A_N.
This is an exact norm statement, not a claim that the coarser N^-1/2 constant
is optimal. In particular the residual operator norms vanish on distant tails.

One can equivalently assemble the cell errors on half-open cells into a
nonnegative measurable function e on [0,infinity). The cells are a countable
partition; continuity on each cell gives measurability. Countable additivity for
nonnegative integrals and the preceding bound give integral_(log N,infinity)e=A_N.
Changing the countable cell endpoints does not change these integrals. Hence
R_N(H)=integral_(log N,infinity)H e. This realizes the correction as an actual
integrable kernel, rather than an assumed approximation interface.

## 3. Exact polar decomposition for compact support

For compactly supported continuous H, define the explicit cell-average producer

    Q(H)=sum_(n>=1) C_n integral_I_n H(x) dx.

This series has finite support: once log n exceeds the positive support radius,
H vanishes on the whole cell. The same is true of r_n(H). Choose a cell endpoint
beyond that support. Additivity over the finitely many consecutive intervals,
followed by the cell identity cosh=C_n+e_n, gives exactly

    P(H)=integral_(0,infinity)H(x)cosh(x/2) dx = Q(H)+R_1(H).

For any N>=1 the same finite partition from log N gives

    integral_(log N,infinity)H(x)cosh(x/2) dx
      = sum_(n>=N) C_n integral_I_n H(x) dx + R_N(H),

with error at most ||H||_infinity/sqrt(N). No interchange of conditionally
convergent series or subtraction of divergent integrals occurs.

Actual normalized compact-source correlations H_f=h_f/h_f(0) are continuous,
compactly supported, and bounded in absolute value by one. Thus their polar
integral admits this explicit producer with error <=1/sqrt(N) on every tail,
without an energy, derivative, support-size or grid-zero premise beyond their
actual source definition.

## 4. Stable correction and the remaining polar escape

Suppose compactly supported continuous H_j converge globally uniformly to a
compactly supported H. The residual estimate proves R_1(H_j)->R_1(H). Therefore
the exact identity gives

    P(H_j)->P(H) iff Q(H_j)->Q(H).

The value here is the constructed producer and its unconditional vanishing tail
error. The equivalence does not assume an unknown Chebyshev estimate or prove
positivity of an unrelated functional.

For the actual diffuse trains in `FiniteTrainTopologyAndDiffuseEscape.md`,
||H_j||_infinity<=1 and P(H_j)>=((j+2)/4)P(H_f), where P(H_f)>0. Consequently

    Q(H_j) >= ((j+2)/4)P(H_f)-1 -> infinity.

Their correlations converge globally, their energies converge under one ceiling,
and their signed logarithmic traces decay uniformly over the family. Nonetheless,
the explicit produced polar cell-average term diverges. The bounded residual
cannot account for this escape. This locates the remaining obstruction in the
weighted cell averages, while supplying a complete positive survivor: the
absolutely summable correction, its exact operator norm, and an explicit all-tail
error bound.

## Scope and novelty boundary

The producer uses exact cell averages, not point samples or prime weights.
No floor counterterm subtraction, arithmetic positivity assertion, or deduction
of global polar closedness from unweighted tail decay is made. The existing cell
L2 and dyadic error theorems are not counted anew. The additional object is the
bounded residual operator on the whole half-line, together with its stable
decomposition of actual polar escape. Corpus search and the formal certificate
are recorded on the associated pipeline card.

## Lean certificate

Six leaves certify the complete result: `NyquistResidualMass`,
`NyquistResidualPartition`, `NyquistResidualKernel`, `NyquistResidualOperator`,
`NyquistPolarDecomposition`, `NyquistPolarSourceEscape`. Implementation indexes
cell k by [log(k+1),log(k+2)] and tail N by log(N+1); its bound
`nyquistResidualTailScale N=1/sqrt(N+1)` is exactly the positive-integer indexing
used above. The kernel uses half-open cells `(log n,log(n+1)]`.

All six direct leaf checks pass without diagnostics. All 81 public declarations
(67 theorems, 14 definitions) have only standard logical axioms. All 81 exact
API entries, all six umbrella imports and unchanged source hashes are verified.
The source endpoint constructs actual diffuse smooth sources, with divergent
producer values, convergent residuals and energies, compact correlation closure
and uniform signed logarithmic trace tails.

Index refresh passes. Global lint reports nine unrelated missing umbrella imports;
none concerns this package, and that snapshot reports no active proof hole.
The full list, logs and manifests are in
`docs/drafts/pipeline/3-formalized/nyquist-polar-integrable-residual-2026-10-17.md`.
The field README remains unchanged and read-only. No full or umbrella build ran.
