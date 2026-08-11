# Local-Exponential Test-Closure Mechanics

- **ID:** ULF-LETCM-1
- **Stage:** 1-in-progress
- **Type:** FIELD PIVOT / SOURCE-GENERATED COFINAL TEST CLOSURE
- **Statement:** A finite local exponential window should make the log-clock polynomial and phase
  calculi jointly reconstruct matrix-valued source order, while the boundary of that window should
  measure the exact failure of positive execution.
- **Status:** `[MECHANISM NOT OBJECT] [FROZEN CONJECTURE] [PRE-RH] [NO LEAN YET]`

## Goal

Complete Test-Closure Mechanics has an exact finite fusion theorem, but an invertible finite
Vandermonde transform is still kinematics.  The next non-theatrical gate is an infinite arithmetic
source whose own intervention flow generates a complete test calculus.

The proposed mechanism is

\[
 \boxed{
 \text{local exponential execution}
 \Longrightarrow \text{polynomial closure}
 \Longleftrightarrow \text{phase closure}
 \Longrightarrow \text{complete order reflection}.}
 \tag{LETC.1}
\]

Its failure boundary is the abscissa at which the exponential source ceases to normalize.  This
connects source generation, moment/Hankel tests, phase/history tests, matrix order, and completion
without declaring those organs isomorphic.

## Frozen conjecture

Let `mu` be a finite positive Borel measure on `R` satisfying

\[
 \int e^{a|x|}\,d\mu(x)<\infty
 \qquad\text{for some }a>0.
 \tag{LETC.2}
\]

Let `J(x)` be an essentially bounded measurable Hermitian `d x d` matrix field.  Define matrix
moments

\[
 M_n(J)=\int x^nJ(x)\,d\mu(x)
 \tag{LETC.3}
\]

and every finite block Hankel section

\[
 \mathcal H_N(J)=[M_{i+j}(J)]_{0\le i,j<N}.
 \tag{LETC.4}
\]

The conjecture is the three-way equivalence

\[
 \boxed{
 J\succeq0\ \mu\text{-a.e.}
 \Longleftrightarrow
 \mathcal H_N(J)\succeq0\ \forall N
 \Longleftrightarrow
 Q_J(p)\ge0\ \forall\text{ finite rational phase packets }p,}
 \tag{LETC.5}
\]

where

\[
 Q_J(p)=\int p(x)^*J(x)p(x)\,d\mu(x).
 \tag{LETC.6}
\]

The polynomial and phase test families must each be generated from the same marked clock `x`.
No observer family may be inserted after inspecting `J`.

## Literal arithmetic realization sought

For the Euler-shell Gibbs source

\[
 \mu_{m,\sigma}
 =\frac1{S_m(\sigma)}\sum_{n\ge2}a_m(n)n^{-\sigma}\delta_{\log n},
 \qquad \sigma>1,
 \tag{LETC.7}
\]

the source clock is `x=log n`, the real intervention flow is the Gibbs translation
`sigma -> sigma+t`, and the phase flow is multiplication by `n^{-it}`.  For every
`0<a<sigma-1`,

\[
 \int e^{ax}\,d\mu_{m,\sigma}(x)
 =\frac{S_m(\sigma-a)}{S_m(\sigma)}<\infty.
 \tag{LETC.8}
\]

Thus `(LETC.5)` would give a literal pre-zero arithmetic realization of cofinal complete test
closure on the safe Gibbs side.

## Conjecture attacks

1. **Entire exponential moments are necessary.**  Attack by a strip-holomorphy proof from one
   local exponential moment.
2. **Scalar polynomial tests automatically reconstruct matrix order.**  Attack with a positive
   but not completely positive map; retain vector-polynomial amplification if needed.
3. **Every finite Hankel depth already reflects source order.**  Attack by finite-dimensional
   annihilators of the first moment constraints.
4. **Complete order reflection implies straight source admission.**  Attack with an unbounded
   negative Euler score whose nonlinear exponential flow exists.
5. **The safe Gibbs theorem crosses the physical half-density automatically.**  Attack using the
   exact normalization wall `sigma=1` and the matching condition `sigma=1/m`.

## Expected laws if the conjecture survives

1. **Local-Laplace density:** polynomials are dense in `L^2(mu)` under `(LETC.2)`.
2. **Matrix sign-cone law:** vector-polynomial positivity equals pointwise matrix positivity.
3. **Phase/Hankel gauge conservation:** every compensation-feasible set is identical in the two
   generated calculi.
4. **Finite negative witness:** every negative source channel is detected at some finite test
   depth, although no uniform depth is promised.
5. **Normalization-wall law:** test completeness can hold throughout the positive chart while the
   desired physical fibre lies outside that chart.

## Internal parents and non-collisions

- `CompleteHankelSignCone.lean` proves the scalar sign-cone theorem under the much stronger
  hypothesis of entire bilateral exponential moments.
- `fourier-kernel-admission-reconstruction-and-contact-localization-law.md` proves phase-kernel
  order reconstruction for finite signed measures.
- `complex-time-exponential-generation-phase-recurrence-and-normalization-wall-law.md` constructs
  the literal Euler-shell complex-time flow and its normalization wall.
- `complete-atomic-fourier-hankel-order-and-inertia-fusion-law.md` proves finite atomic fusion by
  invertible Vandermonde transforms.

The unoccupied target is their cofinal matrix-valued local-exponential synthesis on one literal
arithmetic source.  The parent ingredients may be classical; the source-generated field law is
the object of this programme.

## Gates

- [x] 0 -> 1: source-pure statement and falsifiers fixed;
- [ ] scalar local-exponential polynomial density proved without an absolute-continuity premise;
- [ ] matrix-valued order-reflection theorem dependency-closed;
- [ ] phase and Hankel feasible-set conservation proved;
- [ ] Euler-shell specialization proved before divisor specialization;
- [ ] hostile no-go loops and exact normalization boundary recorded;
- [ ] dependency-closed theorem promoted to Stage 2;
- [ ] Lean formalization only after paper promotion.

## Log

- 2026-08-11 — frozen after finite complete-test fusion was judged insufficiently source-level.

