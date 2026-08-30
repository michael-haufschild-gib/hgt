# ULF-LPCM-1 — Lean certification record

Card: `reflected-binary-experiment-julia-lift-coherence-information-and-properness-law.md`
Promoted to Stage 3 on 2026-08-30.

## Modules

| Module | Card sections | new? |
|---|---|---|
| `GaloisForLFunctions.HTGeometry.LikelihoodJuliaLift` | §2, §3, §7 — the abstract likelihood Julia datum | new |
| `GaloisForLFunctions.HTGeometry.ReflectedLikelihoodJuliaRealization` | §2 — the reflected binary experiment realizes the datum | new |
| `GaloisForLFunctions.HTGeometry.LikelihoodPolarizationInformation` | §4, §5 | new |
| `GaloisForLFunctions.HTGeometry.TanhSelfBound` | support: `tanh x ≤ x`, `x ≤ artanh x` | new |
| `GaloisForLFunctions.HTGeometry.LikelihoodJeffreysBound` | §4 — the Jeffreys ceiling | new |
| `GaloisForLFunctions.HTGeometry.LikelihoodPolarizationFusion` | §6 | new |
| `GaloisForLFunctions.HTGeometry.ReflectedExponentialFisher` | §8, Theorem 8.1 | new |
| `GaloisForLFunctions.HTGeometry.BoundedMultiplierNonclosedRange` | §7 support — the exact failure of the likelihood gap | new |
| `GaloisForLFunctions.RHTower.ThetaCarrierPolarizationFisher` | Corollary 8.2 | new |

All eight `HTGeometry` modules are imported by `GaloisForLFunctions.HTGeometry.UniversalLawField`,
which `GaloisForLFunctions.HTGeometry` imports; the `RHTower` module is imported by
`GaloisForLFunctions.RHTower`.

## Card result → Lean declaration

| Card | Lean |
|---|---|
| `(LPC.1)`, `(LPC.2)` polarization `a = sech χ`, `d = tanh χ`, `a² + d² = 1` | `ReflectedPair.visibilitySymbol`, `ReflectedPair.contrastSymbol`, `visibilitySymbol_sq_add_contrastSymbol_sq` |
| `(LPC.3)`, `(LPC.5)` the two multipliers | `visibilityOp`, `contrastOp` (both `lpBoundedMulCLM` on `L²(η)`), `isSelfAdjoint_visibilityOp`, `isSelfAdjoint_contrastOp`, `visibilityOp_sq_add_contrastOp_sq`, `visibilityOp_contrastOp_comm` |
| `(LPC.9)`–`(LPC.11)` reflected experiment | `ReflectedPair`, `target`, `map_target`, `map_balanced`, `measurePreserving_reflection`, `posteriorContrast_reflection`, `truncContrast_reflection` |
| `(LPC.10)` Koopman involution | `koopmanOp`, `koopmanOp_involutive`, `isSelfAdjoint_koopmanOp`, `koopmanOp_visibilityOp`, `koopmanOp_contrastOp` |
| **Theorem 2.1** the source-generated Julia cycle | `LikelihoodJuliaDatum` (the axioms), `ReflectedPair.juliaDatum` (the realization), `dilation`, `coDilation`, `adjoint_dilation`, `norm_dilation` (isometry), `coDilation_comp_dilation` (`Q₀C = I`), `juliaReflection`, `juliaReflection_involutive`, `inner_juliaReflection_left`, capstone `juliaCycle_certificate` |
| `(LPC.14)`, `(LPC.17)` the two lifts | `blindLift`, `polarizedLift`, `polarizedLift_dilation`, `polarizedLift_juliaReflection` |
| **Theorem 3.1**, `(LPC.16)` exact defect `‖F₊Cf − F₋Cf‖ = 2‖df‖` | `coherenceDefect`, `coherenceDefect_fst`, `coherenceDefect_snd`, `norm_coherenceDefect` |
| **Corollary 3.2**, `(LPC.18)` state-level selection | `blindLift_eq_polarizedLift_iff`, `ker_coherenceDefect` |
| `(LPC.20)`–`(LPC.22)` Hellinger, triangular discrimination, coherence energy | `visibilityDensity`, `hellingerSqMeasure`, `hellingerSqMeasure_eq`, `coherenceWork`, `triangularDiscrimination` |
| **Theorem 4.1**, `(LPC.23)`, `(LPC.24)` the hierarchy `2H² ≤ E ≤ 4H²` | `two_mul_hellingerSq_le_coherenceWork`, `coherenceWork_le_four_mul_hellingerSq` |
| `(LPC.25)` the Jeffreys ceiling `E ≤ J` | `coherenceWork_le_formationJeffreys`, with `klDiv_eq_lintegral_balanced`, `formationJeffreys_eq_lintegral`, `abs_posteriorContrast_lt_one`, and the elementary `sq_le_mul_artanh` (`t² ≤ t·artanh t`) |
| **Theorem 5.1**, `(LPC.28)` common-recovery neutrality | `balancedLaw_compProd`, `rnDeriv_compProd_left`, `posteriorContrast_compProd`, `coherenceWork_compProd`, `triangularDiscrimination_compProd`, `hellingerSqMeasure_compProd`, `formationJeffreys_compProd` |
| **Theorem 6.1**, `(LPC.31)`–`(LPC.33)` product fusion | `withDensity_fusion`, `posteriorContrast_prod` (the nonlinear `(d₁+d₂)/(1+d₁d₂)` law), `visibility_fusion_real`, `artanh_fusion` (rapidities add), `formationJeffreys_prod` |
| **Theorem 7.1** closed range ⟺ likelihood gap | `hasTransverseLowerBound_coherenceDefect_iff`, `isClosed_range_coherenceDefect_iff` |
| `(LPC.38)` reflected exponential family | `ReflectedExponentialFamily`, `tilt`, `cumulant`, `mgf_neg`, `cumulant_neg` (the cgf is even), `integral_stat_eq_zero` |
| `(LPC.39)` tilt polarization | `balancedLaw_tilt` (a `cosh` density), `posteriorContrast_tilt` = `tanh(t·T)` |
| **Theorem 8.1**, `(LPC.40)`–`(LPC.42)` | `coherenceWork_tilt`, `formationJeffreys_tilt` = `4t·A′(t)`, `iteratedDeriv_two_cumulant_zero`, `tendsto_coherenceWork_div_sq`, `tendsto_coherenceWork_div_sq_cumulant` (`E(t)/t² → 4·A″(0)`) |
| **Corollary 8.2 (1)** | `thetaCarrier`, `thetaCarrier_tilt` (the abstract tilt *is* the corpus `thetaTiltProb`), `thetaCarrier_posteriorContrast` = `tanh(a·x)`, `thetaCarrier_visibilityDensity` = `sech(a·x)` |
| **Corollary 8.2 (2)** | `thetaCarrier_coherenceWork`, `thetaCarrier_coherenceWork_pos`, `thetaCarrier_coherenceWork_eq_zero_iff`; also `thetaCarrier_formationJeffreys` = `4a·F′(a)` and `thetaCarrier_formationJeffreys_eq_zero_iff` |
| **Corollary 8.2 (3)** | `thetaPair_blindLift_eq_polarizedLift_iff` — the two lift doctrines agree on the whole packet exactly at `a = 0` |
| **Corollary 8.2 (4)** | `thetaCarrier_integral_sq`, `thetaCarrier_tendsto_coherenceWork_div_sq` → `4·Var_{P₀}(X)` |
| **Corollary 8.2 (5)** | `thetaPair_contrastOp_injective`, `thetaPair_contrastOp_denseRange`, `thetaPair_contrastOp_not_isClosed_range`, `thetaPair_coherenceDefect_not_isClosed_range` |
| Loop C refutation | exactly the pair `thetaCarrier_coherenceWork_pos` (energy positive off centre) and `thetaPair_coherenceDefect_not_isClosed_range` (range still nonclosed) |
| Loop D refutation | `posteriorContrast_prod`, whose right-hand side is not additive |

§9 is a bridge table, §10 the hostile-conjecture log, §11–§12 literature and gates; none carries a
further theorem beyond the ones listed.

## Design notes

* **The Julia cycle is proved once, abstractly.**  `LikelihoodJuliaDatum` axiomatizes only what the
  card's §2 actually uses: two commuting self-adjoint operators with `a² + d² = 1` and a
  self-adjoint involution exchanging them up to sign.  Everything in §3 and §7 — the isometric
  dilation into `WithLp 2 (H × H)`, the reflection, the two lifts, the exact defect
  `‖Df‖ = 2‖df‖`, and the closed-range classification — is a consequence of those axioms.
  `ReflectedLikelihoodJuliaRealization` then supplies the *only* model needed: the multipliers by
  the truncated posterior contrast and the Hellinger visibility on `L²` of the balanced law, with
  the Koopman operator of the reflection.
* **`bhattacharyya` and the Hellinger machinery were built for this lane** (see ULF-FRM-2); mathlib
  carries no `f`-divergence beyond `klDiv`.
* **`Real.tanh x ≤ x` is in neither mathlib nor the corpus.**  `TanhSelfBound` proves it from the
  monotonicity of `x·cosh x − sinh x`, and derives `x ≤ artanh x` and `t² ≤ t·artanh t`; the last
  is exactly the pointwise inequality behind the Jeffreys ceiling `(LPC.25)`.
* **Theorem 8.1's Fisher limit is dominated convergence, not a formal expansion.**  The dominating
  function is `T²·cosh(δ·T)`, integrable because `±δ` lie in the interior of the integrability set;
  the limit is then identified with `A″(0)` through `iteratedDeriv_two_cgf_eq_integral` and the
  vanishing first cumulant that reflection-oddness forces.
* **Corollary 8.2 uses the corpus's literal theta source, not a Gaussian stand-in.**
  `thetaCarrier.base` is `thetaTiltProb 0`, the completed even positive theta source normalized to
  a probability, and `thetaCarrier_tilt` proves that the abstract exponential tilt coincides with
  the corpus's `thetaTiltProb a` on the whole tilt interval.  Consequently
  `thetaCarrier_formationJeffreys` reproduces the corpus's own reflected-work functional
  `4a·F′(a)`, and `thetaCarrier_formationJeffreys_eq_zero_iff` is the information form of
  `thetaTiltReflectedWork_eq_zero_iff`.
* **Item (5) is proved, not asserted.**  `BoundedMultiplierNonclosedRange` gives the general
  criterion: a multiplication operator whose symbol is arbitrarily small on sets of positive finite
  measure has no transverse lower bound, hence (by the corpus's
  `hasTransverseLowerBound_iff_isClosed_range`) no closed range.  For the theta carrier the
  witnessing sets are the intervals `(-c/|a|, c/|a|)`, which the strictly positive theta density
  charges; `|tanh y| ≤ |y|` supplies the bound and `thetaTiltProb_Ioo_ne_zero` the positivity.

## Verification

* All nine modules elaborate with 0 errors and 0 warnings and build.
* `#print axioms` over every public declaration of the two modules added in this session
  (`BoundedMultiplierNonclosedRange`, `ThetaCarrierPolarizationFisher`) reports only `propext`,
  `Classical.choice`, `Quot.sound`; the other seven were audited when they were installed.
* 216 declarations in total across the nine modules.
