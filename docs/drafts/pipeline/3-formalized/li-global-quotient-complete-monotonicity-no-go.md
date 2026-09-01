# LI global quotient complete-monotonicity no-go

- **ID:** LI-GLOBAL-QUOTIENT-CM-NOGO
- **Stage:** 3-formalized
- **Type:** FALSIFIED
- **Status:** `[FORMALIZED]`
- **RH chain killed:** `global complete monotonicity of radial response / v on v≥0 → endpoint adjacent-mode nonnegativity → LI criterion → RH`.

## Theorem

For `Q_b(v)=b/(v+b)^2`, the conjugation-symmetric packet

`G(v)=7 Q_(1/2)(v)+Q_(3/4+i)(v)+Q_(3/4-i)(v)`

satisfies `(-1)^m G^(m)(v)>0` for every `m≥0` and every `v≥0`. Its completed-Abel endpoint mode `n=3` is nevertheless strictly negative.

## Proof

Direct differentiation gives

`(-1)^m Q_b^(m)(v)=(m+1)! b/(v+b)^(m+2)`.

Put `F=(m+1)!/(v+1/2)^(m+2)>0`. The on-axis atom contributes exactly `F/2`. For either off-axis node, `|b|=5/4` and

`|v+3/4±i|²=(v+3/4)²+1 ≥ (v+1/2)²`,

so its signed derivative has norm at most `(5/4)F`. Hence the pair's real part is at least `-(5/2)F`, while seven on-axis atoms contribute `(7/2)F`; total is at least `F>0`, uniformly in `m,v`.

The existing exact Chebyshev evaluation for the same packet proves its completed-Abel endpoint mode `n=3` is negative.

## No-go closure

- **Exact obstruction:** A positive real pole can mask a conjugate off-axis pair in every derivative order on the entire positive ray, while an endpoint Chebyshev mode detects its phase.
- **Positive survivor:** LI coefficient orientation needs complex analytic continuation or singularity-support exhaustion excluding off-axis squared nodes. No condition consisting only of all real-axis derivative signs of the quotient response suffices.
- **Lean certificate:** `RHTower/LiEvenCrossGlobalQuotientCompleteMonotonicityNoGo.lean`; capstones `strictCompletelyMonotoneOnPositiveRay_liLocalQuotientResponse`, `liLocalQuotient_counterexample_and_negative_fourthMode`, `not_globalQuotientCompleteMonotonicityForcesEndpointModes`.

## Novelty audit

Bounded corpus and literature search through 2026-08 found Li/Bombieri--Lagarias coefficient criteria, Voros off-line oscillation, and complete-monotonicity theorems for logarithmic derivatives under real-zero hypotheses, but no result showing that an explicit symmetric off-axis packet can retain strict complete monotonicity at every order on the full positive ray while violating a Li mode. External priority remains `[NOVELTY UNVERIFIED]`.

## Verification

- `lake env lean GaloisForLFunctions/RHTower/LiEvenCrossGlobalQuotientCompleteMonotonicityNoGo.lean`: PASS.
- `lake build GaloisForLFunctions.RHTower.LiEvenCrossGlobalQuotientCompleteMonotonicityNoGo`: PASS.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- Formal lint reports only unrelated pre-existing unreachable modules; this module is umbrella-reachable and has no forbidden declarations.
