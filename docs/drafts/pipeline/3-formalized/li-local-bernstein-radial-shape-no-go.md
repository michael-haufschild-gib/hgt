# LI local Bernstein radial-shape no-go

- **ID:** LI-LOCAL-BERNSTEIN-NOGO
- **Stage:** 3-formalized
- **Type:** FALSIFIED
- **Status:** `[FORMALIZED]`
- **RH chain killed:** `local all-order Bernstein shape of exact radial response → nonnegative adjacent-current coefficients → paired Li positivity → RH`.

## Theorem

For `b ∈ ℂ` put
`A_b(v) = v b / (v+b)^2`.  The real rational response

`R(v) = 7 A_{1/2}(v) + A_{3/4+i}(v) + A_{3/4-i}(v)`

is real-valued and strictly Bernstein on `0 ≤ v ≤ 1/4`: `R(v) ≥ 0` and
`(-1)^(m-1) R^(m)(v) > 0` for every `m ≥ 1`.  Nevertheless its completed-Abel
endpoint mode

`7 L_3(1/4,1/2) + L_3(1/4,3/4+i) + L_3(1/4,3/4-i)`

is negative, where
`L_n(v,b) = (1-T_{2(n+1)}((v-b)/(v+b)))/4`.

## Proof

For every `m ≥ 1`, direct differentiation gives

`A_b^(m)(v) = (-1)^(m-1) m! b (m b-v)/(b+v)^(m+2)`.

For `a=1/2`, `0≤v≤1/4`,

`(-1)^(m-1) A_a^(m)(v)
 ≥ m! (m/8) (4/3)^(m+2) > 0`,

because `ma-v ≥ m/4` and `a+v ≤ 3/4`.  For `b=3/4+i`, conjugation and the
triangle inequality give

`|(-1)^(m-1)(A_b^(m)(v)+A_conj(b)^(m)(v))|
 ≤ m! (15m/4) (4/5)^(m+2)`,

using `|b|=5/4`, `|b+v|≥5/4`, and `|mb-v|≤3m/2`.  Relative to the preceding
lower bound this is at most

`30(3/5)^(m+2) ≤ 30(3/5)^3 = 162/25 < 7`.

Hence all required signed derivatives of `R` are strictly positive.  Also
`R(0)=0`; the positive first derivative yields `R(v)≥0` on the interval.

At `v=1/4`, the off-axis Cayley coordinate is

`(v-b)/(v+b) = -3/4-i/4 = (u+u⁻¹)/2`,  `u=-1-i`.

Since `u^8=16`, the Chebyshev identity gives
`T_8((u+u⁻¹)/2)=(u^8+u⁻8)/2=257/32`.  Each off-axis atom therefore equals
`-225/128`; the pair contributes `-225/64`.  The on-axis coordinate is `-1/3`,
so `-1≤T_8(-1/3)≤1` and each on-axis atom is at most `1/2`.  Thus the complete
mode is at most

`7/2 - 225/64 = -1/64 < 0`.

The squared-node multiset is conjugation-symmetric and lifts, by taking both
square roots of each node, to an even Schwarz-real finite divisor.  Therefore
the counterexample respects the algebraic symmetries used by the LI source law.

## No-go closure

- **Exact killing mechanism:** Local derivative signs measure pole-distance domination. Seven nearer positive-real poles mask the full derivative tower of a farther off-axis conjugate pair, while a single Chebyshev mode detects its phase.
- **Strongest positive survivor:** Any viable radial-shape implication to LI must be global and singularity-faithful: e.g. a complete-Bernstein/Stieltjes extension whose analytic continuation constrains all singularities. No condition depending only on the complete derivative jet over the physical interval can exclude off-axis squared nodes.
- **New insight:** Exact LI coefficient orientation is not a local real-variable shape problem. It requires analytic continuation/support exhaustion capable of reading pole location, not arbitrarily high local derivative order.
- **Lean certificate:** `RHTower/LiEvenCrossLocalBernsteinShapeNoGo.lean`; capstones `strictBernsteinOnLIInterval_liLocalBernsteinResponse`, `liLocalCompletedAbelEndpointMode_three_re_neg`, and `not_localBernsteinShapeForcesEndpointModes`.

## Novelty audit

Bombieri--Lagarias gives general multiset Li criteria; Voros gives asymptotic oscillation from off-line zeros. Corpus has exact LI radial generating law and finite-prefix oscillation no-gos. Bounded search through 2026-08 found no theorem combining strict all-order Bernstein shape on the full physical LI interval with an explicit negative completed-Abel Li mode. External novelty remains `[NOVELTY UNVERIFIED]` pending expert priority review.

## Verification

- `lake env lean GaloisForLFunctions/RHTower/LiEvenCrossLocalBernsteinShapeNoGo.lean`: PASS.
- `lake build GaloisForLFunctions.RHTower.LiEvenCrossLocalBernsteinShapeNoGo`: PASS.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- Wired into `GaloisForLFunctions/RHTower.lean`; lint sees module reachable. Remaining lint failures are unrelated pre-existing unreachable modules.

