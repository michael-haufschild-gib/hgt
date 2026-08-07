# Formalization certificate: reflection-folded Dirac source defect

- **ID:** `hedenmalm-reflection-folded-dirac-source-defect-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `hedenmalm-reflection-folded-dirac-source-defect.md`

## Lean modules

```text
formal/GaloisForLFunctions/RHTower/XiHedenmalmFourierEquation.lean
formal/GaloisForLFunctions/RHTower/XiHedenmalmReflectionFoldedDirac.lean
formal/GaloisForLFunctions/RHTower/XiHedenmalmInvariantHomogenization.lean
formal/GaloisForLFunctions/RHTower/XiHedenmalmMultiplicityChain.lean
formal/GaloisForLFunctions/RHTower/HedenmalmRankOneDilationObstruction.lean
formal/GaloisForLFunctions/RHTower/HedenmalmTwoEndedVolterraDefect.lean
formal/GaloisForLFunctions/RHTower/XiRealAxisNonvanishing.lean
formal/GaloisForLFunctions/RHTower/XiPolynomialDensity.lean
formal/GaloisForLFunctions/RHTower/XiCSchwartzRestriction.lean
formal/GaloisForLFunctions/RHTower/ThetaCuspComplexStrip.lean
formal/GaloisForLFunctions/RHTower/ThetaCuspFourierLaplace.lean
formal/GaloisForLFunctions/RHTower/ExpDecayFourierAnalytic.lean
```

## Formal theorem chain

Namespace `RHTower`.

| # | card statement | Lean declaration |
|---|---|---|
| `(1)` | source-pointed Fourier equation `(alpha - z) U = -i XiC` | `xiThetaEigenFourier_equation` |
| `(2)` | reflection of the source-pointed solution | `xiThetaEigenFourier_reflection` |
| `(3)`/`(4)` | the two reflection folds on the Fourier side | `xiHedenmalmEvenFold`, `xiHedenmalmOddFold`, `xiHedenmalmEvenFold_neg`, `xiHedenmalmOddFold_neg` |
| `(4a)` | each parity channel retains the first conormal | `xiHedenmalmEvenFold_self`, `xiHedenmalmOddFold_self`, `xiHedenmalmFolds_self_ne_zero_of_deriv_ne_zero`, `xiHedenmalmEvenFold_ne_zero`, `ne_zero_of_XiC_eq_zero` |
| `(5)`/`(7)` | the parity-graded first-order system | `xiHedenmalmEvenFold_equation`, `xiHedenmalmOddFold_equation` |
| `(6)`/`(8)` | its second-order form | `xiHedenmalmEvenFold_quadratic`, `xiHedenmalmOddFold_quadratic` |
| `(9a)` | minimal invariant homogenization, and the divided quotient is outside it | `eval_mul_XiC_mem_of_coordinateMultiplication_stable`, `xiThetaEigenFourier_notMem_xiPolynomialModule` |
| — | multiplicity: divided-chain order exactly `m-1` | `xiThetaDividedChain_partial_factorization` |
| `(10)`/`(11)` | rank-one dilation characteristic function, its passivity and reality | `rankOneDilationCharacteristic_ne_zero`, `im_rankOneDilationCharacteristic_neg` |
| `(10)`/`(11)` | the ansatz is *not* the Hedenmalm characteristic function | `not_forall_rankOneDilationCharacteristic_eq_XiC`, `XiC_ne_zero_of_rankOneDilationCharacteristic_eq` |
| `(12)` | causal/anti-causal Volterra defect and the zero criterion | `hedenmalmCausalVolterra_sub_antiCausal`, `hedenmalmCausalVolterra_eq_antiCausal_iff` |
| — | reality step: a centered zero with real square is real | `XiC_im_eq_zero_of_sq_im_eq_zero` |
| — | ordinary-`L2` quotient is zero (Fourier-side density) | `ae_eq_zero_of_orthogonal_polynomial_XiC`, `ae_eq_zero_of_moments_eq_zero`, `expFourier_eq_zero_of_moments` |
| — | strip analyticity of the theta source and its transform | `thetaCuspStripSource_ofReal`, `thetaCuspStripSource_neg`, `integrable_thetaCuspStripSource_horizontal`, `thetaCuspFourierLaplace_eq_XiC_on_strip` |

## Verification

```bash
cd formal
lake build GaloisForLFunctions.RHTower
```

`#print axioms` on every declaration in the table reports only `propext`, `Classical.choice` and
`Quot.sound`; twenty were checked in one scratch file with the twelve modules above imported.

## What remains open on the paper card

Two items on the card are explicitly *paper-level open cores*, i.e. they are not proved on the
card and therefore carry no formalization debt:

- the singular **infinite** source dilation with unsquared Weyl transfer `XiC` (the finite
  rank-one case is closed negatively by `(10)`--`(11)`, which *is* formalized);
- the prime-tail/Hedenmalm boundary transgression.

The remaining unchecked gate is an independent specialist novelty audit.
