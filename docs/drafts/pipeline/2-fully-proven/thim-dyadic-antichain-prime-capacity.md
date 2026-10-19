# Dyadic-antichain Fermi observability and odd-prime capacity

- **ID:** thim-dyadic-antichain-prime-capacity
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper); Lean and significance audits pending
- **Source:** Native selected Fermi boundary trace, physical reciprocal-pronic
  energy, dyadic valuation transport, and odd divisor Gram correlations.
- **Statement:** Uniform physical Fermi observability on dyadic-antichain
  coefficient supports is equivalent to finite reciprocal mass
  of the allowed odd primes.

## Goal and counting

Qualified programme count remains **1/100**. No result on this card is counted.
The dependency-closed paper proof appears below. The five-public-declaration
native energy-comparison leaf passes its source/olean and final imported axiom
checks. The classification remains unformalized. Classical GCD
matrix positivity, prime-cube diagonalization, and Euler products are prior
ingredients, not proposed contributions.

Let `P(c)` be the native full sieve reciprocal-pronic energy and `Q(c)` the
native Fermi jump energy on odd boundaries and boundaries divisible by four.
All coefficient packets have finite positive-integer support. A support is a
**dyadic antichain** when each odd part occurs at at most one valuation of two.
Let `Pi` be a set of odd primes and require all odd parts of active indices to
have prime factors in `Pi`.

**Theorem A (paper).** The following are equivalent:

1. There is a finite `C` such that `P(c) <= C Q(c)` for every such packet.
2. The same assertion holds for nonnegative packets.
3. `sum_(p in Pi) 1/p` converges, equivalently the finite subsums are bounded.

This tests a concrete support restriction on the existing physical operator.
The intended new content is the necessary and sufficient prime-capacity
criterion. Renaming the classical GCD kernel alone would not qualify.

## Prior work checked

- Deep corpus queries: `dyadic antichain physical Fermi inverse gcd Gram
  spectral angles odd prime Euler parity` and `disjoint divisor supports nearly
  collinear gcd matrix squarefree prime cube Euler product`. Inspected all 20
  candidate statements and 20 source-argument statements from each, proposed
  ingredient sets, and all returned prose/source heads. Both searches completed;
  semantic coverage was unmeasured and most compiler entries remained pending
  or stale. Empty lexical intersections are not novelty evidence.
- `BiScaleUncertainty/FoldFreeKernelGramAndFranelGcdCancellation.lean` already
  proves the exact Franel GCD kernel and alternating Fermi–Franel Gram law.
  Relevant source statements and proofs at lines 502–540 and 591–721 were read.
- `BezoutValuationIncidence/AllDepthHilbertDilationCubeAndHyperCubeGramFactorization.lean`
  contains all-depth coherent Ramanujan dilation-cube identities. Declaration
  heads and retrieved exact energy-centered statement were inspected; these
  concern different weights and do not by themselves prove Conjecture A.
- `critical-prime-poisson-gcd-mobius-vacuum.md` was read in full. It explicitly
  identifies classical GCD positivity and a scalar-normalization obstruction.
  Its kernel is `gcd(n,m)/sqrt(nm)`, whereas the normalized divisor Gram needed
  here is `gcd(n,m)^2/(nm)`. Its squarefree tensor gate was still unchecked on
  that card; do not assume its prose supplies a Lean theorem.
- A lexical `research 'gcd Gram' --mode lexical --per-module 0 --explore 0`
  search returned 62 declarations. All four pages, with offsets 0, 20, 40, and
  60, were triaged by declaration and source location. Relevant exact Gram
  statements above were checked in source.
- External primary-source search recovered Titus Hilberdink,
  [The group of squarefree integers (2014)](https://doi.org/10.1016/j.laa.2014.05.037),
  with the relevant character/eigenvalue product mechanism. Full-text comparison
  remains pending. No novelty is claimed for this mechanism.

## Initial proof plan (superseded by the proof below)

1. Replace `1/(n(n+1))` by `1/n^2`. Both native nonnegative energy sums differ
   by factors between `1/2` and `1`; this preserves existence of a uniform bound.
2. Split integers into dyadic rays. In the Hilbert space of odd integers with
   weight `1/b^2`, set `u_k(b)=2^(-k) A_c(2^k b)`. Then homogeneous full energy
   is `sum_k ||u_k||^2`, while selected energy is
   `||u_0||^2 + sum_(k>=2) ||u_(k-1)-u_k||^2`.
3. Normalize odd divisor atoms as `d * 1_(d divides b)`. Their Gram, divided
   by the common positive odd reciprocal-square mass, is `gcd(d,e)^2/(de)`.
4. For finite odd-prime alphabet `T`, bound this Gram between
   `B(T)^(-1) I` and `B(T) I`, where `B(T)=product_(p in T)(p+1)/(p-1)`.
   Dyadic antichain support makes each scalar odd-divisor coordinate a single
   input impulse. Its homogeneous full/selected ratio is at most four.
   This suggests the physical bound `8 B(T)^2`, hence
   `8 exp(6 sum_(p in Pi) 1/p)` when the reciprocal sum is finite.
5. If the reciprocal sum diverges, select arbitrarily many disjoint finite
   prime banks with `theta(T)=product_(p in T)(p-1)/(p+1)` arbitrarily small.
   In each squarefree divisor cube, even/odd parity packets have equal norms
   and normalized correlation `(1-theta)/(1+theta)`.
6. Use one-hot parity patterns across the banks to construct arbitrarily many
   positive odd-divisor packets with disjoint coefficient supports and pairwise
   correlations near one. Assign packet `j` only to dyadic level `j`.
7. A first input amplitude one and subsequent amplitudes one half give a nearly
   constant normalized sieve ray over an arbitrarily long interval. Full energy
   grows with its length; selected energy remains bounded after the banks are
   chosen accurately enough. All coefficients remain nonnegative and the
   support is a dyadic antichain.

Required audits: exact normalization in steps 2–3; finite-prime Gram bounds for
arbitrary prime powers; disjointness of encoded coefficient supports; uniform
control of the infinite dyadic tail; all finite/infinite sum interchanges;
external overlap and significance. No numerical computation is authorized.

## Dependency-closed paper proof

All assertions in this section are proved here from finite linear algebra,
geometric series, unique prime factorization, and the native boundary identity
`J(2m)=2 A(m)-A(2m)`, `J(2m+1)=-A(2m+1)`. No prime number theorem or numerical
experiment is used. The proof applies to arbitrary sets of odd primes.

### 1. Homogeneous comparison and the odd Hilbert space

Extend a finite coefficient packet by zero and put

```text
A(n) = sum_(d divides n) c(d),                n >= 1,
J(2m) = 2 A(m)-A(2m),   J(2m+1) = -A(2m+1).
P_h = sum_(n>=1) A(n)^2/n^2,
Q_h = sum_(n odd) J(n)^2/n^2 + sum_(4 divides n, n>0) J(n)^2/n^2.
```

If `M=sum_d |c(d)|`, then `|A(n)|<=M` and `|J(n)|<=3M`, so both series
converge absolutely. Termwise comparison gives

```text
P_h/2 <= P <= P_h,                 Q_h/2 <= Q <= Q_h.       (1)
```

Let `H` be real functions on positive odd integers with squared norm
`sum_(b odd) f(b)^2/b^2`. Set `Z=sum_(b odd) 1/b^2`; it is finite and positive.
For odd positive `d`, define `e_d(b)=d 1_(d divides b)`. Reindexing odd multiples
of the odd integer `lcm(d,e)` gives

```text
<e_d,e_e>_H = Z gcd(d,e)^2/(de).                             (2)
```

There are only finitely many active divisor atoms, so expanding their Gram
forms interchanges a finite sum with an absolutely convergent series only.

Write `alpha_(j,d)=c(2^j d)/(2^j d)` for odd `d` and define

```text
v_j = sum_d alpha_(j,d) e_d,
u_k = sum_(j<=k) 2^(j-k) v_j = 2^(-k) A(2^k b).
```

Unique dyadic factorization and the native jump identity yield

```text
P_h = sum_(k>=0) ||u_k||^2,
Q_h = ||u_0||^2 + sum_(k>=2) ||u_(k-1)-u_k||^2.             (3)
```

Every summand is nonnegative; reindexing is justified by the absolute bounds
above, or by Tonelli before finiteness is established. Above the last active
valuation `L`, `u_(L+r)=2^(-r)u_L`. Thus all later dyadic tails are exact
geometric series, including when the first active valuation is zero or one.

### 2. Finite-prime Gram bounds (classical ingredient)

For a finite set `T` of odd primes, put

```text
B(T) = product_(p in T) (p+1)/(p-1).
```

For any finitely supported real array `x_d` on the `T`-smooth odd integers,

```text
B(T)^(-1) sum_d x_d^2
  <= sum_(d,e) x_d x_e gcd(d,e)^2/(de)
  <= B(T) sum_d x_d^2.                                     (4)
```

Here is a finite proof. For `0<r<1`, the matrix `K_(i,j)=r^|i-j|` on
`0,...,m` has row sums at most `(1+r)/(1-r)`. The inequality
`2|x_i x_j|<=x_i^2+x_j^2` proves its upper quadratic bound. Set
`y_k=sum_(j=k)^m r^(j-k)x_j` and `y_(m+1)=0`. Expanding the finite sums gives

```text
x^t K x = y_0^2 + (1-r^2) sum_(k=1)^m y_k^2,
x_k = y_k-r y_(k+1).
```

The first identity follows by summing the finite geometric series in each
coefficient of `x_i x_j`. The Euclidean triangle inequality and contraction of
the forward shift give `sum x_k^2 <= (1+r)^2 sum y_k^2`. Consequently
`x^t K x >= (1-r)/(1+r) sum x_k^2`.

Enlarge the finite support to the full box of prime exponents appearing in it
and extend `x` by zero. Unique factorization writes the Gram matrix as the
tensor product of these matrices with `r=1/p`. Orthogonally diagonalizing each
finite real symmetric factor shows that the eigenvalues of the product are
products of factor eigenvalues. Multiplying the preceding bounds proves (4).
The empty-prime case is the one-dimensional identity matrix.

These are classical generalized GCD bounds; compare
[Aistleitner–Berkes–Seip, Theorem 6](https://arxiv.org/pdf/1210.0741).
The same paper's Poisson representation gives (4) directly. Neither (2) nor
(4) is claimed as new. The broader multiplicative tensor mechanism is also
the subject of Hilberdink's
[2017 paper](https://doi.org/10.1016/j.laa.2017.06.037); only its abstract and
search-accessible introduction were available, so no full-text audit is claimed.

### 3. Finite prime capacity implies uniform physical observability

For a dyadic antichain, each odd divisor coordinate has at most one nonzero
input `alpha_(j,d)`. A single scalar input `a` at level `j` has normalized
trajectory `0` before `j` and `2^(j-k)a` from level `j` onward. Its full square
mass is `4a^2/3`. Its selected square mass, as in (3), is

```text
13a^2/12  if j=0;       a^2/3  if j=1;       4a^2/3  if j>=2.   (5)
```

All three formulas are geometric-series evaluations, with the separate odd
observation included only at `j=0`. Hence the sum of scalar full energies is
at most four times the sum of scalar selected energies.

Let `T` contain the odd prime divisors of the active coefficient support.
Apply (4) at each dyadic level in (3), using the same matrix for the selected
differences. Equation (2) contributes the same factor `Z` on both sides.
Together with (5) this proves

```text
P_h <= 4 B(T)^2 Q_h,               P <= 8 B(T)^2 Q.          (6)
```

If all finite reciprocal subsums in `Pi` are at most `S`, then `S>=0` and,
because `p>=3`,

```text
log B(T) = sum_(p in T) log(1+2/(p-1))
         <= sum_(p in T) 2/(p-1) <= 3S.
```

Thus the unconditional choice `C=8 exp(6S)` works for all signed packets.
It also works for their nonnegative subcone. This constant is an explicit
bound, not a claim of optimality.

### 4. Divergent prime capacity gives disjoint, nearly equal positive packets

Suppose finite reciprocal subsums in `Pi` are unbounded. Deleting any finite
set leaves them unbounded: its contribution is a fixed finite number. For any
integer `L>=2`, choose successively disjoint finite banks `T_1,...,T_L` in
`Pi`, each with reciprocal sum at least `2L`. Each bank is nonempty. Put

```text
theta_i = product_(p in T_i) (p-1)/(p+1).
```

Expanding a product of positive `1+x` factors gives

```text
theta_i^(-1) = product_(p in T_i) (1+2/(p-1))
             >= 1+2 sum_(p in T_i) 1/p >= 1+4L,
0 < theta_i < 1/(4L).                                      (7)
```

On one bank's squarefree divisor cube, the normalized Gram in (2) is the
tensor product of `[[1,1/p],[1/p,1]]`. Let `U` be the all-ones coefficient
vector and `V` the vector `(-1)^omega(d)`. They are orthogonal in this Gram
inner product: the local constant and sign vectors are orthogonal, and the
bank is nonempty. Their squared norms are

```text
A_i = 2^|T_i| product_(p in T_i)(1+1/p),
D_i = 2^|T_i| product_(p in T_i)(1-1/p).
```

The even/odd parity indicator vectors `(U+V)/2`, `(U-V)/2` therefore have the
same positive squared norm `E_i=(A_i+D_i)/4` and correlation

```text
rho_i = (A_i-D_i)/(A_i+D_i) = (1-theta_i)/(1+theta_i),
1-1/(2L) < rho_i < 1.                                     (8)
```

In the combined squarefree cube on all banks, let `C_j` consist of divisors
having odd parity in bank `j` and even parity in every other bank. These sets
are pairwise disjoint and nonempty. Put

```text
H_0 = Z product_i E_i > 0,
w_j = H_0^(-1/2) sum_(d in C_j) e_d.
```

Unique factorization across disjoint banks and the finite tensor calculation
give exactly

```text
||w_j||^2=1;
<w_j,w_k> = rho_j rho_k >= 1-1/L  for j != k.               (9)
```

The diagonal also lies in `[1-1/L,1]`. Every atom coefficient is positive.
The normalization has one factor `Z`, not one per bank. This follows directly
from (2); the factorization concerns its normalized arithmetic kernel.

### 5. Realization inside the native Fermi trace

Set `v_0=0`, `v_1=w_1`, `v_j=w_j/2` for `2<=j<=L`, and `v_j=0` afterward.
Realize these inputs by the literal finite coefficient packet

```text
c(2^j d) = 2^j d a_j / sqrt(H_0)  for d in C_j,
a_1=1,  a_j=1/2 for 2<=j<=L,
c(n)=0 otherwise.
```

All coefficients are nonnegative. Unique odd-part factorization makes this
definition unambiguous. Since the sets `C_j` are disjoint, no odd part occurs
at two dyadic levels. All active odd prime factors belong to `Pi`. The horizon
`N=2^L product_(p in union_i T_i) p` contains the whole support.

For `1<=k<=L`, the vector `u_k` in (3) is a convex combination of
`w_1,...,w_k`: `u_1=w_1` and `u_k=(u_(k-1)+w_k)/2`. Equation (9) gives

```text
1-1/L <= ||u_k||^2 <= 1,
<u_(k-1),w_k> >= 1-1/L.
```

Consequently each interior selected difference has squared norm at most
`1/(2L)`. Beyond `L`, the selected difference tail has squared mass exactly
`||u_L||^2/3`. The odd observation is zero. Therefore

```text
P_h >= L-1,
0 < Q_h <= (L-1)/(2L)+1/3 < 5/6,
P >= (L-1)/2,                       0 < Q < 5/6.             (10)
```

Positivity of `Q_h` follows from `||u_L||^2>=1-1/L>0` and its geometric tail;
(1) then gives positivity of `Q`. Given any `C>=0`, choose integer `L>=2`
with `(L-1)/2>5C/6`. Equation (10) implies `P>C Q`. Thus even the nonnegative
antichain class has no uniform inverse bound when reciprocal capacity is
infinite. This proves the remaining implication in Theorem A.

For a nonnegative prime-indexed family, bounded finite subsums are equivalent
to summability. This identifies the finite-subsum statement used throughout
with the reciprocal-series formulation of the theorem.

## Scope and novelty audit after the paper proof

The finite Gram bounds, squarefree character diagonalization, and reciprocal
prime products are classical. The corpus also contains the native dyadic
observation identity and unrestricted long-chain instability. The proposed
additional content is the **exact prime-capacity classification after every
coefficient dyadic chain has been removed**, including positive counterexamples.
The distinction is that disjoint odd-divisor coefficient supports can generate
nearly identical physical profiles; a long coefficient chain is unnecessary.

The retrieved primary sources establish the classical ingredients but did not
state this selected-Fermi antichain classification in the passages inspected.
This is a bounded prior-work comparison, not proof of global novelty. Lean
verification and final significance judgment remain open; count stays 1/100.

## Positive survivor required if the naive support criterion fails

The conjectured survivor is the exact finite-reciprocal-prime-capacity
classification, with a quantitative uniform bound and constructive failure
when capacity diverges. A bare antichain counterexample does not close the
route. If the stronger classification fails, record the actual obstruction
and audit the strongest remaining positive statement before retirement.

## Gates

- [x] Native question and source-pure mechanism isolated; corpus searches run.
- [ ] Finish relevant corpus and external prior-work comparison.
- [x] Dependency-closed paper proof of Theorem A, including the positive classification.
- [ ] Audit significance independently of proof success.
- [ ] Formalize exact surviving theorem, verify named leaves and all axioms.
- [ ] Wire imports; regenerate index; pass formal lint; clean owned scratch.

## Log

- 2026-10-19 — Created after closing corrupted valuation-clock recovery as
  formalized but uncounted. Current candidate remains conjectural.
- 2026-10-19 — Completed symbolic paper proof of the prime-capacity equivalence.
  No Lean theorem or new qualified contribution is claimed at this checkpoint.
- 2026-10-19 — Additional deep searches for geometric Toeplitz bounds and GCD
  prime-product bounds inspected all returned candidate/source statements and
  prose/source heads. The latter query was explicitly partial after a reranking
  deadline and malformed local-model JSON; it does not certify absence. A
  newly created copy of this card in its old stage-one location was a self-hit,
  not prior evidence. No applicable existing finite-prime frame bound was
  recovered. The external Theorem 6 cited above supplies the classical paper
  comparison; a native-energy formal bridge is the next owned Lean step.
- 2026-10-19 — `FermiHomogeneousEnergyAndPronicComparison.lean` passes its
  named source/olean check. It defines the two homogeneous ray energies, proves
  summability, and bounds each native pronic energy between half its homogeneous
  energy and the full homogeneous energy. This is an uncounted analytic bridge;
  final imported audit of all five public declarations passed, with only
  `propext`, `Classical.choice`, and `Quot.sound`.
- 2026-10-19 — Repeated the actual deep corpus search for the complete proposed
  antichain classification. Triaged all 20 candidate statements and 20 source
  argument statements, plus prose/source-passage paths. Existing signed and
  nonnegative Fermi no-go results allow dyadic chains; they do not establish the
  antichain obstruction. Current self-hits are not independent prior work.
  Retrieval completed without errors over 74,313 inventoried files, but compiler
  metadata has pending/stale entries, semantic coverage is unmeasured, and refresh
  was incomplete while the background indexer ran. No global absence claim.
- 2026-10-19 — Classical-name lexical search was narrowed from a broad 606-hit
  query to exact `Murdock geometricGram geometricKernel`. All eight exact hits
  were inspected: theta-tail Gram integrals, continuous-map Cauchy kernels, and a
  Gamma-pole kernel. None gives the required finite prime-exponent quadratic
  bound. The broad Szego/Kac search is not claimed exhaustively audited. Direct
  Mathlib source search found no Kac--Murdock--Szego/geometric-Toeplitz naming hit.
  The finite completion-of-squares proof is now source/olean and final imported
  axiom verified in `FermiPrimeExponentGramBounds.lean` (two public declarations,
  only standard axioms). It is not a proposed new contribution.
- 2026-10-19 — `FermiPrimeBoxGramBounds.lean` now proves the classical finite-box
  PSD and quadratic-form product bounds. It reuses Mathlib's
  `Matrix.PosSemidef.kronecker`, `Matrix.PosSemidef.submatrix`, and `Fin.consEquiv`.
  All three public declarations pass named source/olean and final imported axiom
  checks; only standard axioms occur. The three supporting leaves (ten public
  declarations total) are wired. Index regeneration and
  `scripts/formal_tools.py lint --check-generated` passed. This does not
  establish the native antichain classification or add a qualified contribution.
- 2026-10-19 — Further deep corpus search for the arithmetic GCD/exponent bridge
  returned 20 candidate statements and 20 source arguments, all triaged. Source
  inspection confirms reusable `RHTower.WeilAbscissa.gcd_eq_prod_min` in
  `RHTower/WeilConeHarmonicPinning.lean`, reconstruction in
  `RHTower/WeilFiniteSupportRigidity.lean`, and prime-power product factorization
  in `HTGeometry/OrbitSumKorobovParameters.lean` and
  `RHTower/JointAncestryLagAggregatePositivityAbscissa.lean`. `IsSmoothOver`
  requires `2 <= n`, so unit coefficients need separate treatment. The retrieved
  BiScale reduced-coprime-projection angle polynomial concerns a different
  operator. This retrieval completed over 74,342 inventoried files without an
  engine error; compiler metadata and semantic coverage have the same limitations
  recorded above. Existing arithmetic and matrix results remain prior work.

### Current formal boundary

Verified supporting leaves are `FermiHomogeneousEnergyAndPronicComparison`,
`FermiPrimeExponentGramBounds`, `FermiPrimeBoxGramBounds`,
`FermiGcdGramPrimeProductBounds`, `FermiOddDivisorGramAndFrameBounds`, and
`FermiDyadicAntichainCoordinates`, together with `FermiBooleanParityGram`.
The full support-to-parameter representation, finite-prime
uniform physical bound, and disjoint positive prime-bank construction still
require formalization. Neither direction of the full native equivalence is
claimed as a Lean theorem yet.

The arithmetic bridge reuses Mathlib's `Nat.factorization_gcd`, finite-support
factorization products, and `Nat.eq_of_factorization_eq`. Their actual use is
verified in the fourth leaf. The existing corpus GCD-product and smooth-number
wrappers were inspected, including their unit/positivity restrictions. The fifth
leaf proves the exact odd-divisor Gram identity and both finite-packet frame
bounds. The sixth proves literal antichain coordinates and the scalar impulse
energy bound. The Boolean parity leaf proves exact algebraic bank Gram formulas.
All forty-one public declarations have imported standard-axiom audits; all seven
leaves are wired and indexed. The first six passed global generated lint. The
latest run reports one concurrent unreachable BezoutValuationIncidence module,
with no THIM finding.

The next native bridge parameterizes an antichain by a finite set `S` of odd
integers, one depth `j(d)` per `d`, and normalized amplitudes `a(d)`. Its literal
coefficient at `2^j(d) d` is `2^j(d) d a(d)`. For any horizon containing those
indices, divisibility gives
`2^j d | 2^k b` iff `j ≤ k` and `d | b` for odd `d,b`. Therefore the native
normalized ray divided by `b` is the odd-divisor packet with coordinates
`a(d) 2^j(d)/2^k` when `j(d) ≤ k`, and zero otherwise. This is the coordinate
identity in the paper proof; its Lean implementation is certified in the sixth
leaf, together with the native jump formula, exact coefficient values,
injectivity, positivity preservation, full impulse mass `4/3`, and selected
impulse mass at least `1/3`.

The earlier support-package verification processes are terminal. Removed 22 exact owned completed
scratch/log files after certification; retained active corpus-search evidence.

- 2026-10-19 — Next arithmetic bridge: the exact normalized GCD prime-product
  identity and its Mathlib API probes pass scratch Lean, including the unit case.
  The finite-support matrix and quadratic bounds now pass named source/olean and
  final imported axiom checks in `FermiGcdGramPrimeProductBounds.lean`. All four
  public declarations use only standard axioms. Distinct positive integers embed
  into the exponent box; unit and empty-prime cases are included. The fourth leaf
  is wired and its index refresh passed. Global generated-lint currently reports
  nine concurrent BiScale modules missing umbrella imports; no THIM error was
  reported. These are classical
  ingredients, with no count increment.
- 2026-10-19 — Odd-divisor Gram search: all 20 deep candidates and 20 source
  arguments were triaged. Inventory is complete over 74,353 files; compiler and
  semantic coverage remain limited. A narrower lexical `tsum indicator dvd`
  query returns one exact hit, a private Schwartz-specialized lemma in
  `RHTower/CCMRationalUnitInvariantMobiusPoissonCompression.lean:204`. Its proof
  uses subtype reindexing; it is not a public reciprocal-square API. Inspected
  `RHTower/LiClockPairedEtaInfinitePartitionDensityTail.lean:495` for its existing
  odd reciprocal-square summability proof, and found the public exact odd-square
  mass identity at line 507. The next bridge can use the same Mathlib summability
  and injective-tsum APIs. Current self-hits are excluded from novelty evidence.
- 2026-10-19 — The odd-divisor Gram identity, finite-packet energy identity, and
  prime-product frame bounds pass scratch verification, named module compilation,
  and all seven imported axiom checks in `FermiOddDivisorGramAndFrameBounds`.
  The last named compilation's terminal handle was lost during compaction; its
  empty log, newer olean, and successful imported audit certify the resulting
  module. Index and global generated lint pass after the concurrent BiScale
  imports were fixed. These are support results, not a new qualified contribution.
- 2026-10-19 — The normalized-dyadic decomposition audit triaged all twenty deep
  candidates and twenty source arguments, plus all eight declarations returned
  by the targeted lexical `fermiNormalizedDyadicSieve` query. The deep inventory
  covers 74,358 files with no inventory errors; semantic coverage is unmeasured,
  refresh is incomplete, and compiler metadata remain mostly pending/stale.
  Existing native tail/depth identities and the private odd-ray divisibility
  proof were recovered. BiScale's `order_odd_decomposition` is also prior work;
  the parameterized antichain bridge can avoid importing that large dependency.
- 2026-10-19 — The further dyadic impulse deep query triaged all twenty candidate
  statements and twenty source arguments; its results concern other mechanisms.
  The targeted lexical `impulse` query within THIM returns one existing pronic
  compensation theorem, whose statement was inspected and is different from the
  scalar Fermi impulse estimate. Coverage has the same limits as above. The
  literal antichain coefficient-to-normalized-ray identity now passes scratch
  Lean after correcting elaboration issues, with no changed mathematical claim.
  Removed twenty-three exact owned terminal arithmetic/analytic scratch and log
  files after certification; corpus-search evidence is retained.
- 2026-10-19 — `FermiDyadicAntichainCoordinates` passes named source/olean and all
  nine imported axiom checks (standard axioms only), then wiring, index, and
  global generated lint. Exact full and selected native homogeneous energy
  identities also pass scratch verification in the next support module. The
  finite-prime physical bound is now in scratch verification. No full capacity
  classification or new qualified contribution is claimed.
- 2026-10-19 — Reciprocal-prime product search recovered the exact existing
  `RHTower.Sieve.dampedCorrBound_le_exp` in `Sieve/DampedCorrExp.lean:42`.
  At `c=1` its Euler correction is exactly `prod (p+1)/(p-1)` and its exponent
  is `3 sum 1/p`; this is being reused for the native `8 exp(6 M)` bound.
  All twenty deep candidate and twenty source-argument statements were triaged;
  inventory covers 74,362 files, partial=false, errors empty, with the same
  compiler/semantic/refresh limitations. The canonical PM prime-aperture norm
  threshold card was also inspected: it concerns damped Mellin/Fermi source
  norms and a damping threshold, not the present coefficient-antichain energy
  ratio. Current self-hits remain excluded from prior-work evidence.
  Removed twelve exact owned terminal sixth-leaf scratch/log files after
  certification. The next scratch includes the parameterized bounded-capacity
  forward implication; it is not yet certified.
- 2026-10-19 — Positive-bank prior audit: all twenty deep candidates and twenty
  source-argument statements were triaged, plus all six lexical `Walsh kernel`
  hits and their relevant source definitions. The inventory is complete over
  74,362 files, with the same compiler/semantic/refresh limits. Existing biased
  Walsh completeness and Route E hard-core eigenlaws were inspected; their
  weight/kernel differs from the symmetric normalized GCD cube here. Existing
  squarefree CRT packets, exponential parity partitions, and inclusive linear
  GCD Gram forms were also checked. `Fintype.prod_add`/`prod_sum` supply the
  reusable finite product-sum mechanism. The already-audited Franel GCD identity
  is prior work; the current odd-divisor Gram self-hit adds no novelty evidence.
- 2026-10-19 — A concurrent build temporarily removed the transitive dependency
  `RHTower/Sieve/SelbergGcdLogLocalIdentity.olean`. Its owning build was observed
  regenerating it; no foreign process or source was changed. The object now
  exists, and the corrected full forward-bound scratch check has resumed.
- 2026-10-19 — The next forward check encountered a second temporarily missing
  object, `SelbergLogPowerGeneralAsymptotic.olean`, in the same active foreign
  build. That object has since appeared; the owning build is still running.
  Independent algebraic work continued: the Boolean kernel, constant/parity
  eigenlaws, and exact two-parity Gram formula pass scratch Lean. For arbitrary
  real local parameters, product-sum expansion gives
  `Gram(a+b*parity,c+d*parity) = card(cube)*(a*c*prod(1+r)+b*d*prod(1-r))`.
  Hence the two zero-one parity indicators have common norm square
  `card(cube)*(prod(1+r)+prod(1-r))/4` and cross Gram with the minus sign. This is
  the algebraic identity already used in the paper bank proof, not a new
  qualified contribution. `FermiBooleanParityGram` passes named compilation;
  final imported axiom verification is pending. Its arithmetic squarefree
  pullback remains to be formalized.
- 2026-10-19 — The exact lexical `factorization_prod_pow` query returned eight
  declarations; all were triaged, reusing earlier inspections where applicable.
  `HTGeometry.OrbitVanishing.factorization_prod_pow` is the relevant existing
  prime-product coordinate interface. The other arithmetic hits reconstruct
  factorizations; the analytic/cyclotomic hits concern different products.
- 2026-10-19 — `FermiBooleanParityGram` now passes all eleven imported axiom
  checks with standard axioms only, wiring, and index. The latest global lint
  reports only the concurrent, unwired
  `BezoutValuationIncidence.CofinalMobiusMagnitudeObservablesAndGradient`.
  The existing `OrbitVanishing.factorization_prod_pow` interface and its actual
  import pass scratch Lean; the literal squarefree-cube arithmetic bridge is
  now in scratch verification. No qualified count change.
- 2026-10-19 — The arithmetic cube bridge passes full scratch Lean, including
  positivity, oddness, prime support, injectivity, exact GCD product, and the
  native odd-divisor Gram pullback with one global mass factor. Its named
  `FermiBooleanPrimeCube` module and all-eight axiom audit are prepared but not
  yet run. The finite-prime native theorem has been separated from the existing
  Euler-correction wrapper to keep their dependencies distinct; the native-only
  scratch is now checking. The full capacity scratch remains retained.
