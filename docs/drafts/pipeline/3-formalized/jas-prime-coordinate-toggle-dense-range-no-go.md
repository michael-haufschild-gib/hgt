# JAS prime-coordinate toggle dense-range no-go

Status: `[PROVED IN LEAN] [CORPUS-NOVEL ROUTE THEOREM] [TARGETED EXTERNAL NO-MATCH]`
Novelty: `[NOVELTY UNVERIFIED]`

Lean module:
`GaloisForLFunctions.RHTower.JointAncestryPrimeCoordinateToggleDenseRangeNoGo`

## RH proof chain tested

Candidate contribution was:

1. coefficient-faithful source-linear landing of literal positive and negative prime-Poisson
   coordinate actions on a reversible Gamma--theta Boolean dilation;
2. literal Gamma--theta creator recovered as a compression/corner;
3. divisor-independent prime-support/actual-theta-grade synchronization;
4. `XiPrimePoissonReflectionSewing rho` at every Xi divisor `rho`;
5. `xiPrimePoissonReflectionSewing_iff_internalOnly`;
6. `xiDivisorSyndromeIsInternalOnly_iff_re_eq_half`;
7. RH.

This theorem kills step 1 for the canonical one-toggle dilation.

## Corpus origin

Required `scripts/formal_tools.py research` searches found and drove the conjecture:

- `jasGammaThetaToggleUnitary`: canonical Boolean support toggle;
- `jasPrimeCoordinateMul` and its positive/negative inverse laws: actual source actions;
- `denseRange_lpBoundedMulCLM_of_ae_ne_zero`: dense-range self-adjoint multiplier theorem;
- `measurePreserving_eval_infinitePi`: exact one-coordinate product marginal;
- `circlePoissonMeasure`: local Poisson law as a circle-Haar density;
- `circleLebesgue_singleton`: circle Haar atomlessness.

No corpus theorem contained the same-target dense-difference relation rigidity or the actual
prime-Poisson/Boolean-toggle no-go.

## New theorem

Let `R` be a closed densely defined single-valued complex Hilbert relation. Suppose two bounded
source actions `Aplus`, `Aminus` are both sent by `R` to one bounded target action `B`. If some
scalar multiple `T = c (Aplus - Aminus)` has dense range, every output in `R` is zero.

This needs no unitarity, involutivity, injectivity, spectral law, or dense range for `B`.

For the actual prime-Poisson source,

`T = I * (chi_p - chi_p⁻¹)`.

Its symbol is real-valued and vanishes only when the fixed prime coordinate is `+1` or `-1`.
Every fixed-coordinate singleton fibre is prime-Poisson-null at every positive aperture because
the marginal is a circle-Poisson law with a density against atomless circle Haar measure. Hence
`T` is an almost-everywhere nonzero self-adjoint multiplier and has dense range.

Therefore no nonzero closed densely defined single-valued relation can assign both actual inverse
prime-coordinate actions to the same canonical Gamma--theta Boolean toggle.

## Formalized declarations

- `jasCirclePoissonMeasure_singleton_eq_zero`
- `jasAddCirclePoissonMeasure_singleton_eq_zero`
- `primePoissonMeasure_coordinate_singleton_eq_zero`
- `jasLocalOddCharacter_eq_zero_imp`
- `jasPrimeCoordinateOddSymbol_ne_zero_ae`
- `jasPrimeCoordinateOddSymbol_star`
- `jasPrimeCoordinateOddMul_denseRange`
- `jasPrimeCoordinateOddMul_apply`
- `hilbertRelation_output_eq_zero_of_closed_denseDomain_denseZeroAction`
- `hilbertRelation_output_eq_zero_of_closed_denseDomain_sameTarget`
- `jasPrimeCoordinateToggle_relation_output_eq_zero`
- `not_JASPrimeCoordinateGammaThetaToggleClosedLanding`

## Route decision and positive survivor

Retire canonical one-toggle reversible landing. This is stronger than failure of the literal
square-zero creator: even its most immediate unitary Boolean dilation cannot simultaneously carry
`p` and `p⁻¹`.

Positive survivor: any nonzero JAS landing must distinguish target images of positive and negative
prime coordinates. A viable dilation needs at least an oriented/bilateral target coordinate
`V_p`, with `p` acting by `V_p` and `p⁻¹` by a genuinely distinct inverse action, before creation
is obtained by compression. Exact new construction burden:

`oriented coefficient-faithful bilateral landing`
→ `creator compression with synchronized support/grade coefficients`
→ `divisor-independent Xi sewing`
→ `internal-only divisors`
→ `critical line`
→ RH.

## Literature audit

Targeted searches through August 2026 covered closed linear relations, dense operator ranges,
same-target intertwining, infinite-torus RH formulations, and prime/Poisson Boolean dilations.
Closest general background:

- Hassi--Sebestyén--de Snoo--Szafraniec,
  [A canonical decomposition for linear operators and linear relations](https://arxiv.org/abs/math/0611045),
  develops regular/singular decomposition of relations but not this same-target dense-difference
  theorem.
- Shi--Xu--Ren,
  [Boundedness and closedness of linear relations](https://arxiv.org/abs/1604.07979),
  studies closedness and bounded perturbations but not the rigidity proved here.
- Mirotin,
  [Some assertions that are equivalent to Riemann hypothesis](https://arxiv.org/abs/1902.11234),
  treats infinite-torus RH equivalences but not prime-Poisson product measures, Boolean Gamma--theta
  toggles, or this obstruction.

No exact match was found. This is evidence only, not a global novelty certification.

## Verification

- `lake env lean GaloisForLFunctions/RHTower/JointAncestryPrimeCoordinateToggleDenseRangeNoGo.lean`:
  passed;
- `lake build GaloisForLFunctions.RHTower.JointAncestryPrimeCoordinateToggleDenseRangeNoGo`:
  passed (`12128/12128`, exact leaf only);
- `#print axioms` for eleven core declarations: only `propext`, `Classical.choice`, and
  `Quot.sound`;
- `scripts/formal_tools.py lint`: no forbidden declaration or new-module error; nonzero exit comes
  from pre-existing large-file warnings and pre-existing umbrella reachability errors;
- `git diff --check`: passed;
- no full or umbrella build was run.
