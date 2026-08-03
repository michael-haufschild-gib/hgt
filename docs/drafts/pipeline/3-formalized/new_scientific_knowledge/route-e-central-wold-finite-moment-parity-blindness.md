# Route E central Wold finite-moment parity blindness

- **ID:** ROUTE-E-CENTRAL-WOLD-MOMENT-BLINDNESS
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / THEOREM (Lean pending final audit)
- **Source:** central normal-order survivor of `OPEN-SOURCE-001`
- **Statement:** Every fixed polynomial panel in Wold breadth admits two positive measures on
  adjacent breadth layers with identical reported moments and opposite deterministic Möbius parity.

## Goal

After reciprocal markers transport every fixed off-normal breadth deviation, determine whether a
finite panel of normal-order Wold moments can orient the remaining squarefree Möbius sign.

## Gates

- [x] 0 → 1 in-progress: exact adjacent-layer packet identified
- [x] 1 → 2 fully-proven: complete finite-difference proof
- [x] 2 → 3 formalized: targeted module build and axiom audit
- [ ] 3 → 4 publication-ready: external priority audit and paper integration

## Theorem `[PROVED HERE]`

Fix integers \(r\ge0\), \(d\ge0\), and put \(n=d+1\).  On adjacent Wold breadths
\[
r,r+1,\ldots,r+n
\]
define signed weights
\[
c_k=(-1)^{n-k}\binom nk,\qquad 0\le k\le n.
\tag{1}
\]
Then:

1. for every polynomial \(P\) of degree at most \(d\),
   \[
   \sum_{k=0}^n c_kP(r+k)=0;
   \tag{2}
   \]
2. the Möbius-parity response is maximal:
   \[
   \sum_{k=0}^n c_k(-1)^{r+k}
   =(-1)^{n+r}2^n\ne0;
   \tag{3}
   \]
3. writing \(c=c^+-c^-\), the positive measures
   \[
   \nu_\pm=2^{-(n-1)}
      \sum_{k=0}^n c_k^\pm\,\delta_{r+k}
   \tag{4}
   \]
   are probability measures, have identical moments through degree \(d\), and have opposite
   deterministic parity:
   \[
   \int P\,d\nu_+=\int P\,d\nu_-,
   \qquad
   \int(-1)^t\,d\nu_+=-\int(-1)^t\,d\nu_-\in\{-1,+1\}.
   \tag{5}
   \]

The same construction can be centered at any normal-order breadth \(r\); increasing \(r\) does not
weaken the obstruction.

## Proof

Equation `(2)` is the order-\(n\) forward difference of \(P\) at \(r\).  Forward differences lower
degree, so \(\Delta^nP=0\) when \(\deg P<n=d+1\).

For `(3)`, each summand has the same sign because \(k\le n\):
\[
(-1)^{n-k}(-1)^{r+k}=(-1)^{n+r}.
\]
Therefore the absolute binomial masses add:
\[
\sum_{k=0}^n c_k(-1)^{r+k}
=(-1)^{n+r}\sum_{k=0}^n\binom nk
=(-1)^{n+r}2^n.
\]

Since \(n>0\), applying `(2)` to \(P=1\) shows total positive and negative masses agree.  Their
sum is \(\sum_k|c_k|=2^n\), so each is \(2^{n-1}\); `(4)` gives probabilities.  Splitting `(2)`
gives moment equality.  The sign computation above shows parity is constant on each coefficient
sign class and opposite between classes, proving `(5)`.

## New scientific knowledge

Normal-order localization does not make finite Wold statistics sufficient.  Even a reporter that
knows every moment through arbitrarily large but fixed degree cannot distinguish two
adjacent-normal-layer laws whose Möbius parities are exactly opposite.  This is stronger and more
specific than generic finite-dimensional reporter blindness:

- witness lives on consecutive Wold layers;
- all weights are explicit binomial masses;
- target distinction is literal squarefree Möbius sign;
- parity response is maximal rather than merely nonzero.

Thus a central-band Route E source cannot be a fixed finite Wold-moment closure.  Its breadth order
must grow cofinally, or it must retain a non-polynomial/relation-valued parity coordinate before
scalarization.

The lower bound is sharp.  If a polynomial \(Q\) agrees with
\((-1)^t\) on \(n+1\) consecutive layers \(r,\ldots,r+n\), applying packet `(1)` to \(Q\) and to
parity shows \(\deg Q\ge n\).  Conversely Lagrange interpolation on those \(n+1\) distinct layers
produces a polynomial of degree at most \(n\).  Therefore exact polynomial parity reading on a
width-\(n\) breadth window has minimal order exactly \(n\).  This is the positive survivor:
polynomial reading is possible only with order growing linearly with resolved breadth width.

Its conditioning cost is exact.  The first visible raw moment is
\[
\sum_{k=0}^n c_k(r+k)^n=n!,
\tag{6}
\]
independent of \(r\).  Hence the two normalized probabilities in `(4)` differ in their \(n\)-th
moment by \(n!/2^{n-1}\).  If breadth is normalized by a scale \(L\) and a degree-\(n\) moment
reader \(Q(t/L)=\sum_{j=0}^na_j(t/L)^j\) returns the two parity values, all lower moments cancel
and necessarily
\[
|a_n|=\frac{2^nL^n}{n!}.
\tag{7}
\]
For every resolved central width \(n\le L\), this is at least \(2^n\).  Thus the sharp positive
survivor is necessarily exponentially ill-conditioned in breadth resolution; it belongs to the
singular/nonclosable source category demanded by the updated modular-superselection paper, not to
a bounded moment completion.

Crucially, this does **not** kill the survivor at Route E scale.  If the off-normal transport is
diagonalized to a central window of width \(n=o(L)\), Stirling gives
\[
\log\frac{2^nL^n}{n!}
=n\log\frac{2eL}{n}+O(\log n)
=o(L).
\tag{8}
\]
Since \(L=\log\log X\),
\[
\frac{2^nL^n}{n!}
=\exp(o(\log\log X))
=(\log X)^{o(1)}
=X^{o(1)}.
\tag{9}
\]
The required unbounded Wold reader is therefore singular in source topology but still affordable
inside a strict-half \(X^{1/2+o(1)}\) Gibbs budget.  This is a genuine positive route survivor:
cofinally growing normal-order parity reconstruction is not excluded by conditioning alone.

## Sharp breadth-patch seam

The survivor cannot be used as one unlocalized moment polynomial.  Let \(Q\) have degree at most
\(n\) and agree with parity on \(r,\ldots,r+n\).  Its value at the first unresolved adjacent layer
is forced:
\[
Q(r+n+1)
=(-1)^{r+n+1}\bigl(1-2^{n+1}\bigr).
\tag{10}
\]
Therefore
\[
Q(r+n+1)-(-1)^{r+n+1}
=-(-1)^{r+n+1}2^{n+1}.
\tag{11}
\]
Proof: \(\Delta^{n+1}Q(r)=0\); insert the \(n+1\) known parity values, whose complete
order-\(n+1\) parity difference is \((-1)^{r+n+1}2^{n+1}\), and solve for final value.

Thus exact local parity interpolation creates an exponentially charged boundary one layer later.
Although \(2^n=X^{o(1)}\) for \(n=o(\log\log X)\), adjacent normal-order layers have macroscopic
population.  Their error cannot be discarded by off-normal marker transport.  A viable
growing-order source now needs a **co-moving breadth-patch seam law** that cancels `(11)` between
overlapping source-defined patches before scalar moment evaluation.  Merely evaluating one
interpolant globally is closed.

The seam is one-dimensional, which is the strongest positive survivor.  Let \(Q_r,Q_{r+1}\) be
degree-at-most-\(n\) parity interpolants on consecutive windows
\([r,r+n]\) and \([r+1,r+n+1]\).  They agree on the \(n\) shared layers, so
\[
Q_{r+1}(t)-Q_r(t)
=\frac{(-1)^{r+n+1}2^{n+1}}{n!}
  \prod_{j=1}^n\bigl(t-r-j\bigr).
\tag{12}
\]
Indeed the difference has those \(n\) roots and degree at most \(n\); evaluation at
\(t=r+n+1\) uses `(11)` and the product value \(n!\).  Hence patching does not create an
arbitrary new all-order error.  Every adjacent transition lies in one explicit top
falling-factorial channel.  The remaining arithmetic problem is to orient and cancel the
co-moving coefficients of this rank-one breadth seam jointly with the already identified
integer-delay physical seam.

For integral breadth \(t\ge r+n+1\), that channel is literal incidence:
\[
\prod_{j=1}^n(t-r-j)
=n!\binom{t-r-1}{n}.
\tag{13}
\]
Thus factorial-normalized seam charge counts \(n\)-subsets of excess prime factors.  This gives
an exact interface to Route E's existing binomial incidence-capacity lift, but also imports its
Hall warning: subset labels do not create physical capacity.  A proof must use the incidence
coordinate to distribute a source-defined co-moving flux without counting the same integer more
than its physical load.

The source-horizon paper's label-blind factorization law applies literally here.  Equation `(2)`
with \(P=1\) gives \(\sum c_k=0\), so every bounded label-blind scalarization factors through total
mass and kills this packet.  Equation `(3)` shows Möbius parity does not.  Hence the packet is an
explicit central-Wold element of the separation defect: parity must be read while breadth labels
remain distinct, not reconstructed after label-blind fusion.

## Anti-theatre audit

1. **No arithmetic distribution is asserted.**  The theorem is an exact source-information
   obstruction.  It does not claim ordinary integers realize either artificial measure locally.
2. **No RH equivalent is renamed.**  It removes all fixed-order Wold-moment producers but does not
   bound a Möbius sum.
3. **Positive witnesses are explicit.**  Signed relation `(1)` splits into two genuine probability
   measures; this is not a formal kernel vector with unphysical negative mass.
4. **Unbounded order remains live.**  A degree growing with \(\log\log X\), an exact parity
   character, non-prime-power singular support, and relation-valued transport are not excluded.

## Lean status

Module:
`GaloisForLFunctions/RHTower/MobiusWoldFiniteMomentParityBlindness.lean`.

Unconditional theorems:

- `woldAdjacentMomentBlind_monomial_eq_zero`
- `woldAdjacentMomentBlind_firstVisibleMoment_eq_factorial`
- `woldAdjacentMomentBlind_polynomial_eq_zero`
- `woldAdjacentMomentBlind_totalMass_eq_zero`
- `woldAdjacentMomentBlind_constantReadout_eq_zero`
- `woldAdjacentMomentBlind_parityResponse`
- `woldAdjacentMomentBlind_parityResponse_ne_zero`
- `natDegree_ge_of_eval_eq_woldParity_on_adjacent`
- `natDegree_ge_of_eval_eq_woldParity_on_adjacent_rat`
- `leadingCoeff_mul_factorial_of_eval_eq_woldParity_on_adjacent`
- `eval_next_of_eval_eq_woldParity_on_adjacent`
- `adjacentParityInterpolants_nextDifference`
- `woldPatchExcessIncidence_eq_factorial_mul_choose`
- `woldPatchExcessIncidence_firstExterior`

Direct `lake env lean` check passes and umbrella is wired.  Positive/negative probability
normalization is a paper corollary of zero total mass and binomial total mass; Lean formalizes the
stronger signed moment and exact parity identities from which it follows.

## Novelty audit

Finite-difference moment annihilation is classical.  Candidate new content is its exact
Route E/Wold interpretation as two adjacent-layer positive laws with identical fixed polynomial
reporters and opposite deterministic Möbius parity, after off-normal breadth transport has
localized the hard current.  Claim is project-new synthesis; external priority unverified.

## Log

- 2026-08-01 — constructed adjacent-binomial central-layer witness; proved fixed-moment
  blindness and maximal parity response on paper and in Lean.

## Stage 2 → 3 audit (2026-08-03)

- Targeted module build: `lake build GaloisForLFunctions.RHTower.MobiusWoldFiniteMomentParityBlindness`
  — `Build completed successfully`.
- Axiom audit (in-file `#print axioms` via `lake env lean`): all fourteen listed unconditional
  theorems depend only on `[propext, Classical.choice, Quot.sound]`.
- Umbrella wiring confirmed: `GaloisForLFunctions/RHTower.lean:2291`.

Card promoted to `3-formalized/new_scientific_knowledge`.
