# Seam-Log Hankel RH Equivalence

- **ID:** seam-log-hankel-rh-equivalence
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / route normalization
- **Source:** `fe-orbit-quotient-half-trace-moments.md`;
  `source-aware-q0-alone-reciprocal-positivity.md`;
  `shifted-reciprocal-moments-determine-divisor.md`
- **Statement:** The canonical all-order seam log jet of the completed function gives
  the shifted reciprocal tower by an exact coefficient formula, and all-order Hankel
  positivity of that source-built tower is equivalent to RH.

## Setup

Write

`Xi(w)=xi(1/2+w)`.

The functional equation makes `Xi` even, so there is a unique entire quotient
function

`Phi(z)=Xi(sqrt(z))`.

Since `Xi(0)=xi(1/2) != 0`, the logarithm of `Phi(z)/Phi(0)` is holomorphic near
`z=0`. Define its seam-log coefficients by

`ell_k = [z^k] log(Phi(z)/Phi(0))`, `k>=1`.

Define

`T_k^src = -2 k (-1)^k ell_k`.

For a real polynomial `p(y)=sum_i c_i y^i`, set

`Q_0^src[p] = sum_{i,j} c_i c_j T_{i+j+1}^src`.

## Theorem

For the canonical completed Riemann `xi` function,

`RH <=> Q_0^src[p] >= 0 for every real polynomial p`.

Equivalently, the source-built all-order seam-log tower lands in the shifted
Stieltjes cone if and only if all nontrivial zeros lie on the critical line.

## Proof

By `fe-orbit-quotient-half-trace-moments.md`, if `w=rho-1/2` and

`y_rho = -w^(-2)`,

then the bridge reciprocal trace moments satisfy

`T_k = -2 k (-1)^k [z^k] log Phi(z)`.

The constant `log Phi(0)` has no positive-degree coefficients, so `T_k=T_k^src` for
every `k>=1`.

By `source-aware-q0-alone-reciprocal-positivity.md`, for the actual reciprocal
divisor moments, all-order positivity of

`Q_0[p]=sum_{i,j} c_i c_j T_{i+j+1}`

for all real polynomials `p` is equivalent to every reciprocal atom

`y_rho = -(rho-1/2)^(-2)`

lying in `R_{>0}`, which is equivalent to `rho-1/2` being purely imaginary for every
nontrivial zero `rho`. That is RH.

Substituting `T_k=T_k^src` gives the claimed equivalence.

## Consequence for the RH Route

This card removes one ambiguity in the source-built programme.

The source construction of the shifted tower is not the missing theorem: the
canonical all-order seam log jet already gives it exactly. The missing theorem is the
positivity statement

`Q_0^src[p] >= 0 for every real polynomial p`.

That positivity is not a finite computation, not a finite Taylor claim, and not a
rank-one chart identity. It is precisely the all-order RH wall, now written in
canonical source coordinates.

Thus a non-mirror proof must supply a new reason why the canonical seam-log
coefficients land in the shifted Stieltjes cone. Merely deriving the coefficients
from `Xi` is a bridge, not a proof of RH.

## Source Boundary

This is a synthesis theorem from existing proven cards. It claims no new positivity
result. Its purpose is route normalization: it distinguishes the already-available
source coordinate from the still-open positivity theorem.

The statement is gauge-sensitive. It uses the canonical completed `xi`
normalization; zero-free even gauge multipliers shift log-defined coefficients, as
recorded in `hd3-li-gauge-shift.md` and related gauge-extraction notes.

## Gates

- [x] 0 -> 1 in-progress: seam-log source coordinate isolated.
- [x] 1 -> 2 fully-proven: exact formula plus source-aware `Q_0` theorem combined.
- [ ] 2 -> 3 formalized: depends on formal wrappers for the quotient-log coefficient
  formula and the source-aware reciprocal positivity theorem.

## Log

- 2026-06-24 -- Professor: created under the RH-only goal. After the shifted tower
  was classified as zero-complete, this card records the complementary fact: the
  canonical seam log jet source-builds the tower, so the remaining obstruction is
  exactly all-order positivity.

## 2026-06-24 finite-part source-domain bridge

`even-seam-finite-part-canonicality.md` connects the seam-log Hankel chart to the singular Weil-pullback route at the domain level. The even completed finite part of the reciprocal pullback is forced to be Hankel in the polynomial coefficients, matching the all-order shifted tower shape.

The equivalence here remains the RH wall in source coordinates. The finite-part theorem proves canonicality of the source domain, not positivity of the Hankel form.

## 2026-06-24 canonical gauge requirement

`reciprocal-seam-canonical-gauge-extraction.md` gives the exact gauge law behind the source tower used here. If `Xi(w)` is replaced by `exp(q(w^2))Xi(w)`, then `T_k` shifts by `2k(-1)^{k+1}a_k`. Therefore the seam-log Hankel equivalence uses the canonical completed `xi` representative, not an arbitrary zero-free even gauge.

## 2026-06-24 finite shifted prefixes are undecisive

`finite-markov-prefix-nonselection.md` records the moment-prefix form of the all-order burden. A finite list of shifted source moments can be held fixed while a later Hankel square test is made negative. Therefore finite shifted-Hankel evidence cannot certify the seam-log tower's membership in the Stieltjes cone.

The missing theorem remains an all-order source theorem for the canonical tower, not a finite prefix check.

## 2026-06-24 all adjacent Turan inequalities are insufficient

`all-order-log-convexity-does-not-imply-stieltjes.md` adds the all-order low-rank warning for the canonical seam-log tower. Even if the source coefficients satisfied every adjacent log-convex/Turan inequality, that would not imply the shifted Stieltjes cone: an explicit positive log-convex sequence has a negative `3 x 3` Hankel determinant.

Thus the missing source theorem is not coefficient positivity, complete monotonicity, or adjacent `2 x 2` control. It must prove full Hankel positivity, or an independent source principle that implies it.

## 2026-06-24 fixed-rank shifted Hankel control is insufficient

`../../3-formalized/not_new_scientific_knowledge/fixed-rank-hankel-tests-do-not-imply-stieltjes.md` adds the bounded-size form of the all-order warning. For each fixed `r`, every shifted block `H_{N,k}` with `k<=r` may be positive definite while `H_{0,r+1}` fails positivity.

Thus the missing source theorem for the canonical seam-log tower cannot stop at a fixed block size, even uniformly over all shifts. It must reach the full Hankel cone or prove a source upgrade that makes bounded-rank control decisive.

## 2026-06-24 all-order seam-log jet is function-complete

`all-order-seam-jet-function-complete.md` adds the coordinate warning: the full coefficient sequence of `log(Phi(z)/Phi(0))` determines `Xi` up to scalar, hence its zero divisor. The equivalence here is therefore a faithful source coordinate only after the coefficients are produced from Euler/Gamma/FE data; giving the all-order jet as input is already function-complete.

## 2026-06-24 triangular coordinate recodings do not soften the wall

`triangular-seam-coordinates-function-complete.md` generalizes the all-order seam-log warning. Any full coordinate system that recursively reconstructs the seam-log coefficients, including continued-fraction, Jacobi, cumulant, Hankel-ratio, or Pade-style coordinates on their invertible loci, is function-complete. The source theorem must therefore force Stieltjes/Markov positivity in that coordinate from Euler/Gamma/FE data; the coordinate change itself is not progress across the wall.
