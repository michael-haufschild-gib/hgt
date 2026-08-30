# ULF-PMPG-1 — Lean certification record

Card: `posterior-contrast-projection-pythagoras-sufficiency-and-global-reconstruction-law.md`
Promoted to Stage 3 on 2026-08-30.

## Modules (all new)

| Module | Card sections |
|---|---|
| `GaloisForLFunctions.HTGeometry.OrthogonalHistoryDecomposition` | the abstract content of §5 and §6 |
| `GaloisForLFunctions.HTGeometry.PosteriorContrastProjection` | §1, §2, §3 |
| `GaloisForLFunctions.HTGeometry.PosteriorSufficiencyRecovery` | §4 |
| `GaloisForLFunctions.HTGeometry.PosteriorHistoryFiltration` | §5, §6, §7 |
| `GaloisForLFunctions.RHTower.PosteriorMobiusHardyCell` | §8 |

The four `HTGeometry` modules are imported by
`GaloisForLFunctions.HTGeometry.UniversalLawField`, which `GaloisForLFunctions.HTGeometry`
imports; the P/R module is imported by `GaloisForLFunctions.RHTower`.

## Card result → Lean declaration

| Card | Lean |
|---|---|
| `(PMP.1)` balanced law | `balancedLaw`, `two_smul_balancedLaw`, `isProbabilityMeasure_balancedLaw`, `absolutelyContinuous_balancedLaw_left/right`, `balancedLaw_self` |
| `(PMP.2)` posterior contrast | `posteriorContrast`, `rnDeriv_add_rnDeriv_balancedLaw`, `rnDeriv_left_toReal`, `rnDeriv_right_toReal`, `abs_posteriorContrast_le_one`, `posteriorContrast_self` |
| `(PMP.4)` observed laws | `balancedLaw_comp` |
| `(PMP.5)` joint observation law | `(balancedLaw P Q) ⊗ₘ κ` throughout |
| **Theorem 2.1**, `(PMP.6)`, `(PMP.7)` | `integral_mul_posteriorContrast`, `kernelPairing`, `integral_comp_eq`, `integral_observedContrast`, `integral_observedContrast_snd` |
| `(PMP.8)` vertical current | `informationCurrent`, `measurable_informationCurrent` |
| `(PMP.9)` orthogonality | `integral_mul_informationCurrent` |
| `(PMP.10)`, `(PMP.11)` | `triangularDiscrimination`, `coherenceWork`, `coherenceWork_eq_two_mul`, `triangularDiscrimination_eq` (the `∫ (dP-dQ)²/(dP+dQ)` form) |
| **Theorem 3.1**, `(PMP.12)`, `(PMP.13)` | `coherenceWork_eq_add`, `triangularDiscrimination_eq_add`; monotonicity `triangularDiscrimination_comp_le` |
| **Theorem 4.1** 1–4, `(PMP.14)`, `(PMP.15)` | `zeroInformationCurrent_tfae` (a four-way `List.TFAE`), with `swapJoint`, `recoveryKernel` (`condKernel` of the swapped joint law), `swapJoint_disintegration`, `rnDeriv_eq_of_informationCurrent`, `rnDeriv_right_eq_of_informationCurrent`, `comp_recoveryKernel_of_rnDeriv`, `absolutelyContinuous_comp` |
| `(PMP.16)`, `(PMP.22)` observation tower | `historySpace`, `antitone_historySpace`, `historySpace_zero`, `hasOrthogonalProjection_historySpace`, `lpMeas_mono`, `lpMeas_top` |
| `(PMP.17)`, `(PMP.23)` | `historyStage`, `historyResidual`, `historyStage_eq_condExpL2` |
| **Theorem 5.1**, `(PMP.18)`, `(PMP.19)` | abstract: `eq_historyStage_add_sum_residual`, `norm_sq_eq_historyStage_add_sum`; filtration form: `eq_condExpL2_add_sum`, `norm_sq_eq_condExpL2_add_sum`; orthogonality `inner_historyResidual_historyResidual`, `inner_historyResidual_historyStage` |
| **Corollary 5.2**, `(PMP.20)`, `(PMP.21)` | `historyAnalysis`, `norm_historyAnalysis`, `historyIsometry`, `historyIsometry_injective`, `historyIsometry_isClosedEmbedding` |
| **Theorem 6.1**, `(PMP.24)` | `cauchySeq_historyStage`, `historyLimit`, `tendsto_historyStage`, `norm_sq_eq_historyLimit_add_tsum`; filtration form `tailProjection`, `norm_sq_eq_tailProjection_add_tsum` |
| `(PMP.25)`, `(PMP.26)` | `memℓp_historyResidual`, `historyResidualLp`, `norm_sq_historyResidualLp`, `historyAnalysisInf` (a `LinearIsometry` into `WithLp 2 (E × lp (fun _ : ℕ => E) 2)`) |
| **Corollary 6.2**, `(PMP.27)`, `(PMP.28)` | `eq_zero_iff_tailProjection_and_residuals` |
| §7, `(PMP.29)`–`(PMP.31)` | `tendsto_starProjection`, `tendsto_norm_sq_split` |
| §8, `(PMP.32)`–`(PMP.36)` | `twoPointSign`, `twoPointWeight`, `twoPointLawPos/Neg`, `balancedLaw_twoPoint` (the balanced law is uniform), `rnDeriv_twoPointLawPos`, `posteriorContrast_twoPoint` (`d(ε) = ε·tanh δ`), `signForget`, `comp_signForget`, `posteriorContrast_signForget`, `informationCurrent_twoPoint`, `coherenceWork_twoPoint`, `integral_sq_informationCurrent_twoPoint`, capstone `mobiusHardyCell_posterior_certificate` |

§9 is a hostile-conjecture log, §10–§12 are literature and scope commentary; neither carries a
theorem.

## Design notes

* **`(PMP.7)` never invokes `condExp`.**  The conditional-expectation statement is proved and used
  in its defining *test-function* form, `∫ g(y)·d_X(x) dρ = ∫ g(y)·d_Y(y) dρ` for every bounded
  measurable `g`.  Both sides are computed to `∫ g dP_Y − ∫ g dη_Y`.  This makes §3 elementary:
  the Pythagoras identity needs only `g := truncContrast`, the contrast truncated to `[-1,1]`,
  which is bounded *everywhere* and almost everywhere equal to the contrast.
* **§5–§6 are proved once, abstractly.**  `OrthogonalHistoryDecomposition` states them for an
  arbitrary decreasing chain of orthogonally complemented subspaces starting at `⊤`; the
  measure-theoretic instance is `V k := lpMeas ℝ ℝ (m k) 2 μ`, where `historyStage = condExpL2`
  holds by `rfl` because mathlib *defines* `condExpL2 hm` as `(lpMeas …).orthogonalProjectionOnto`.
* **Theorem 4.1's kernel is constructed, not assumed.**  `recoveryKernel` is the `condKernel` of
  the swapped joint law; `2 ⟹ 4` runs the density through `compProd_withDensity_fst` and
  `map_withDensity_comp`, and `4 ⟹ 3` is data processing applied in both directions.

## Verification

* All five modules elaborate with 0 errors and 0 warnings and build.
* `#print axioms` over every public theorem of the five modules (106 declarations) reports only
  `propext`, `Classical.choice`, `Quot.sound`.
