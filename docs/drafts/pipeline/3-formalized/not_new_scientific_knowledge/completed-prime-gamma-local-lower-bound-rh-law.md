# Completed prime--Gamma local lower-bound RH law

- **ID:** `completed-prime-gamma-local-lower-bound-rh-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scientific status:** `[FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** `formal/GaloisForLFunctions/RHTower/XiGuinandWeilExplicitFormula.lean` and `PrimeArchSourceUpperBoundGate.lean`
- **Statement:** RH is equivalent to pointwise local lower boundedness of the real completed prime--Gamma flux throughout the open left half of the critical strip.

## Goal

Replace the existing global finite-bound source criterion by its weakest local pole-exclusion form.  The resulting RH premise has no growth rate, asymptotic tail, uniform constant, positivity cone, or test-function regularity obligation: around each point of the open left half-strip, the continued prime--Gamma flux merely has some finite real lower bound on nearby regular points.

This is a proof-burden reduction, not a claim of scientific novelty.  At a hypothetical off-line zero, the reflected zero lies in the left half-strip and the negative logarithmic derivative has a negative real pole along a rightward approach.  Conversely RH gives the sharper global lower bound zero.

## Gates

- [x] 0 -> 1 in-progress: source-pure statement and pole-residue proof identified
- [x] 1 -> 2 fully-proven: complete paper proof, no open dependency
- [x] 2 -> 3 formalized: Lean theorem `riemannHypothesis_iff_forall_exists_completedPrimeGamma_local_lowerBound`, focused build green, axiom audit passes
- [ ] 3 -> 4 publication-ready: not planned independently; may support an RH leverage section

## Approach

1. State local lower boundedness with explicit radii and constants, quantified at every point of `0 < Re(s) < 1/2`.
2. Under failure of RH, reflect a right-half Xi zero to a left-half zero `sigma`.
3. Along `s_n = sigma + 1/(n+1)`, use `xi_normalizedLogDeriv_tendsto_order` to obtain positive normalized logarithmic-derivative residue.
4. Rewrite the completed prime--Gamma flux as the negative Xi logarithmic derivative at a selected nearby regular point, contradicting the local lower bound.
5. Under RH, use the already-proven global accretivity bound `0 <= Re(completedPrimeGammaFlux s)`.

## Numerical sign pre-check

For the local model `Xi(s)=s-sigma`, the completed flux principal part is `-1/(s-sigma)`.  At rightward offsets `0.1`, `0.01`, and `0.001`, its real values are `-10`, `-100`, and `-1000`, confirming the sign and the local lower-bound obstruction before formalization.

## Log

- 2026-07-12 -- created after auditing the resolvent Guinand--Weil formula and the existing global source upper-bound criterion.
- 2026-07-12 -- formalized in `PrimeArchSourceLocalBoundGate.lean`; direct theorem statement exposes all quantifiers and has no named proposition interface.
