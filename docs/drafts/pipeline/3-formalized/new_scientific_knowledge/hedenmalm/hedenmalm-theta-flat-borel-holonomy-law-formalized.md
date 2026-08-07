# Formalization certificate: theta-flat Borel holonomy law

- **ID:** `hedenmalm-theta-flat-borel-holonomy-law-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `hedenmalm-theta-flat-borel-holonomy-law.md`

## Lean modules

```text
formal/GaloisForLFunctions/RHTower/XiHedenmalmThetaBorelHolonomy.lean
formal/GaloisForLFunctions/RHTower/XiHedenmalmThetaBorelHilbert.lean
formal/GaloisForLFunctions/RHTower/XiHedenmalmThetaBorelConditionNumber.lean
formal/GaloisForLFunctions/RHTower/XiHedenmalmThetaBorelCyclic.lean
formal/GaloisForLFunctions/RHTower/XiHedenmalmBorelSoninApertureComparison.lean
formal/GaloisForLFunctions/RHTower/BurnolSoninEvaluationAperture.lean
formal/GaloisForLFunctions/RHTower/BurnolSoninEvenCosineAperture.lean
formal/GaloisForLFunctions/RHTower/BurnolCoPoissonMellinNonvanishing.lean
formal/GaloisForLFunctions/RHTower/BurnolCoPoissonSubWindowSource.lean
formal/GaloisForLFunctions/RHTower/ArchimedeanMellinFourier.lean
```

## Formal theorem chain

Namespace `RHTower`.

| # | card statement | Lean declaration |
|---|---|---|
| Thm 1 `(4)` | logarithmic chart and exact Borel-tail factorization | `hedenmalmBorelChart`, `image_hedenmalmBorelChart`, `injOn_hedenmalmBorelChart`, `hasDerivAt_hedenmalmBorelChart`, `integral_Ioi_eq_integral_hedenmalmBorelChart`, `integrableOn_Ioi_iff_hedenmalmBorelChart`, `xiHedenmalmBoundaryEigenfunction_eq_borelTail` |
| Thm 1 `(5)` | positivity and mass law | `hedenmalmBorelDensity_pos`, `integral_Ioi_hedenmalmBorelDensity` |
| Thm 2 `(7)` | the tilts are square integrable on the divisor strip | `memLp_hedenmalmBorelHolonomyFun`, `abs_im_lt_half_of_XiC_eq_zero` |
| Thm 2 `(8)` | exact sesquilinear law and matrix coefficient | `inner_hedenmalmBorelHolonomyVector`, `inner_self_hedenmalmBorelVector`, `norm_sq_hedenmalmBorelVector`, `inner_hedenmalmBorelVector_holonomy`, `inner_hedenmalmBorelVector_eq_neg_eigenfunction` |
| Thm 2 | cyclicity of the theta-tail vector | `dense_hedenmalmBorelCyclicSet` |
| Thm 3 `(9)`--`(11)` | character identities and norm | `hedenmalmBorelCharacter_neg`, `conj_hedenmalmBorelCharacter`, `norm_hedenmalmBorelCharacter`, `norm_hedenmalmBorelCharacter_rpow` |
| Thm 3 `(12)` | contraction/unitary/reflected trichotomy | `hedenmalmBorelCharacter_norm_le_one_iff`, `hedenmalmBorelCharacter_norm_eq_one_iff`, `hedenmalmBorelCharacter_bounded_reflected_iff` |
| Thm 3 `(13)` | reflection equals adjunction iff `Re rho = 1/2` | `hedenmalmBorelCharacter_bounded_reflected_iff_re_eq_half` |
| Thm 4 `(16b)` | Sonine dilation character is the square root | `soninDilationCharacter`, `soninDilationCharacter_sqrt_eq_hedenmalmBorelCharacter` |
| Thm 4 `(16c)`/`(16g)` | geometric sample and determinant torsion | `hedenmalmBorelCharacter_geometric_sample`, `norm_sq_hedenmalmBorelCharacter_geometric_sample`, `norm_hedenmalmBorelCharacter_geometric_sample_rpow` |
| Thm 4 `(16d)` | exact two-sided condition number | `essSup_norm_mul_essSup_norm_hedenmalmBorelCharacter`, `hedenmalmBorelWeight_ne_zero_of_isOpen` |
| Thm 4 `(16e)`/`(16f)` | geometric-sample form and exponent limit | `essSup_norm_mul_essSup_norm_hedenmalmBorelCharacter_geometric_sample`, `tendsto_log_condition_number_geometric_sample`, `essSup_norm_mul_essSup_norm_hedenmalmBorelCharacter_eq_one_iff` |
| `(16f)` | the two aperture exponents agree, and vanish only on the line | `borel_and_sonin_aperture_exponents_agree`, `borel_sonin_aperture_exponent_eq_zero_iff` |
| `(10)`/`(11)`/`(12)`/`(13)` | Burnol evaluator: nonvanishing off the zeta zero set, lower bound, two-sided law, exponent limit | `burnolExtendedSoninEvaluationVector_ne_zero_of_subWindow`, `burnolExtendedSoninReflectedEvaluationVector_ne_zero_of_riemannZeta_ne_zero`, `norm_soninMellinEvaluation_le_aperture`, `norm_soninMellinEvaluation_le_geometric_sample`, `tendsto_log_norm_burnolExtendedSoninEvaluationVector_of_riemannZeta_ne_zero` |
| — | the co-Poisson no-go: every source vector is annihilated at a zeta zero | `soninMellinEvaluation_burnolCoPoissonSource` |

## Verification

Fifty-one of the fifty-three backticked identifiers in the card's Lean status section resolve to
declarations in the tree; the two exceptions are the open-core marker
`THETA_BOREL_REFLECTED_COMMON_DOMAIN` and the mathematical symbol `lambda_r`.  Twelve headline
declarations were `#print axioms`-checked in a single scratch file: only `propext`,
`Classical.choice`, `Quot.sound`.

```bash
cd formal
lake build GaloisForLFunctions.RHTower
```

## What remains open on the paper card

- Burnol's quotient dimension count, i.e. nonvanishing of the evaluator **at** a hypothetical zeta
  zero.  The card proves this is unreachable from the co-Poisson side
  (`soninMellinEvaluation_burnolCoPoissonSource`), so the residual is an orthogonal-complement
  statement, not formalization debt.
- `[OPEN CORE: THETA_BOREL_REFLECTED_COMMON_DOMAIN]`.
- Independent specialist novelty audit.
