import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheThetaCoefficientsHaveTheHeckeBound
import GaloisForLFunctions.MetaplecticMobiusDescent.TheCubicInitialResolventMatching

/-!
# The Eisenstein pairing continues across `4/3`

For `G` square integrable on the fundamental set `D_Γ` of the level-three group, the pairing with the
cubic Eisenstein series splits as (`integral_mul_eisenstein_eq`, `Re s > 4`, `Im s > 0`)

`∫_{D_Γ} G · E(s) = ∫_{D_Γ} G · seed(s) + ⟨G, Corr(s)⟩`,

where `seed(s)` is the smooth cusp seed of `v^s` (cutoff `[2, 3]`) and `Corr(s) = R(s(2 − s)) defect(s)`
is MMD's `L²` correction on the kernel quotient. The second term is continuous linear in `Corr(s)`
(`levelPairing`, through the measure-preserving pullback to the kernel fundamental set, which contains
`D_Γ`), so it inherits the analytic structure of the resolvent:

* `levelPairing_correction_analyticAt`: analytic at every `s` with `Re s ≠ 1`, `Im s ≠ 0`;
* `levelPairing_correction_center`: `(s − 4/3) ⟨G, Corr(s)⟩` agrees near `4/3` with the analytic
  `⟨G, N(s)⟩`, whose value at `4/3` pairs `G` with the residue vector (at most a simple pole).

The seed term is the Mellin transform of the constant term of `G` against the seed profile
(`integral_mul_seed_eq`): `seed(s) = E(· ∣ χ v^s)` is an incomplete Eisenstein series.
-/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Classical Topology ComplexConjugate InnerProductSpace

namespace GaloisForLFunctions.SpectralTheoryOfTheCubicCover

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicKubota
  MetaplecticMobiusDescent.CubicEisenstein

/-! ### Pairing on `D_Γ` with vectors of the kernel quotient -/

/-- The fundamental set of the kernel, carrying the quotient measure. -/
abbrev kernelSet : Set HyperbolicSpace := hyperbolicFundamentalSet globalKubotaKernel

/-- Pullback from the kernel quotient to its fundamental set, an isometry of `L²`. -/
def kernelPullback : KernelQuotientL2 →ₗᵢ[ℂ] Lp ℂ 2 (hyperbolicVolume.restrict kernelSet) :=
  Lp.compMeasurePreservingₗᵢ ℂ (integralOrbitProjection globalKubotaKernel)
    (quotient_projection_measurePreserving globalKubotaKernel)

theorem kernelPullback_ae (u : KernelQuotientL2) :
    kernelPullback u =ᵐ[hyperbolicVolume.restrict kernelSet]
      fun w => u (integralOrbitProjection globalKubotaKernel w) :=
  Lp.coeFn_compMeasurePreserving u _

theorem restrict_kernelSet_levelSet :
    (hyperbolicVolume.restrict kernelSet).restrict levelSet = hyperbolicVolume.restrict levelSet := by
  rw [Measure.restrict_restrict (hyperbolicFundamentalSet_measurable _),
    Set.inter_eq_left.mpr levelSet_subset_kernelSet]

theorem memLp_levelTest (G : HyperbolicSpace → ℂ) (hG : MemLp G 2 (hyperbolicVolume.restrict levelSet)) :
    MemLp (levelSet.indicator fun w => conj (G w)) 2 (hyperbolicVolume.restrict kernelSet) := by
  refine (memLp_indicator_iff_restrict (hyperbolicFundamentalSet_measurable _)).mpr ?_
  rw [restrict_kernelSet_levelSet]
  exact Complex.conjCLE.toContinuousLinearMap.comp_memLp' hG

/-- The test vector `1_{D_Γ} Ḡ` on the kernel fundamental set. -/
def levelTest (G : HyperbolicSpace → ℂ) (hG : MemLp G 2 (hyperbolicVolume.restrict levelSet)) :
    Lp ℂ 2 (hyperbolicVolume.restrict kernelSet) :=
  (memLp_levelTest G hG).toLp _

/-- `u ↦ ∫_{D_Γ} G · u`, a continuous linear functional on `L²` of the kernel quotient. -/
def levelPairing (G : HyperbolicSpace → ℂ) (hG : MemLp G 2 (hyperbolicVolume.restrict levelSet)) :
    KernelQuotientL2 →L[ℂ] ℂ :=
  (innerSL ℂ (levelTest G hG)).comp kernelPullback.toContinuousLinearMap

theorem levelPairing_apply (G : HyperbolicSpace → ℂ) (hG : MemLp G 2 (hyperbolicVolume.restrict levelSet))
    (u : KernelQuotientL2) :
    levelPairing G hG u = ∫ w in levelSet,
      G w * u (integralOrbitProjection globalKubotaKernel w) ∂hyperbolicVolume := by
  rw [levelPairing, ContinuousLinearMap.comp_apply, innerSL_apply_apply, L2.inner_def]
  have h1 := (memLp_levelTest G hG).coeFn_toLp
  have h2 := kernelPullback_ae u
  calc ∫ w, ⟪levelTest G hG w, kernelPullback.toContinuousLinearMap u w⟫_ℂ
        ∂(hyperbolicVolume.restrict kernelSet)
      = ∫ w, levelSet.indicator (fun w => G w * u (integralOrbitProjection globalKubotaKernel w)) w
          ∂(hyperbolicVolume.restrict kernelSet) := by
        refine integral_congr_ae ?_
        filter_upwards [h1, h2] with w hw1 hw2
        change ⟪levelTest G hG w, kernelPullback u w⟫_ℂ = _
        rw [levelTest, hw1, hw2, RCLike.inner_apply]
        by_cases hw : w ∈ levelSet <;> simp [Set.indicator, hw, mul_comm]
    _ = _ := by
        rw [integral_indicator (hyperbolicFundamentalSet_measurable _), restrict_kernelSet_levelSet]

/-! ### The correction term -/

/-- The cubic Eisenstein `L²` correction with seed cutoff `[2, 3]`. -/
abbrev eisensteinCorrection (s : ℂ) : KernelQuotientL2 :=
  kernelEisensteinL2Correction 2 3 (by norm_num) (by norm_num) s

/-- The correction numerator `N(s) = (s − 4/3) Corr(s)`, analytic at `4/3`. -/
abbrev correctionNumerator (s : ℂ) : KernelQuotientL2 :=
  kernelEisensteinCorrectionNumerator 2 3 (by norm_num) (by norm_num) s

theorem levelPairing_correction_analyticAt (G : HyperbolicSpace → ℂ)
    (hG : MemLp G 2 (hyperbolicVolume.restrict levelSet)) (s : ℂ) (hs : s.re ≠ 1) (hi : s.im ≠ 0) :
    AnalyticAt ℂ (fun s => levelPairing G hG (eisensteinCorrection s)) s :=
  ((levelPairing G hG).analyticAt _).comp
    (kernelEisensteinL2Correction_analyticAt_nonreal 2 3 (by norm_num) (by norm_num) s hs hi)

/-- **At most a simple pole at `4/3`.** `(s − 4/3) ⟨G, Corr(s)⟩ = ⟨G, N(s)⟩` near `4/3`, `⟨G, N⟩` is
analytic at `4/3`, and `N(4/3)` is the residue vector `θ` of the cubic Eisenstein series. -/
theorem levelPairing_correction_center (G : HyperbolicSpace → ℂ)
    (hG : MemLp G 2 (hyperbolicVolume.restrict levelSet)) :
    AnalyticAt ℂ (fun s => levelPairing G hG (correctionNumerator s)) (4 / 3) ∧
      (∀ᶠ s in 𝓝[≠] (4 / 3 : ℂ), (s - 4 / 3) * levelPairing G hG (eisensteinCorrection s) =
        levelPairing G hG (correctionNumerator s)) ∧
      correctionNumerator (4 / 3) = cubicEisensteinResidue := by
  refine ⟨((levelPairing G hG).analyticAt _).comp
    (kernelEisensteinCorrectionNumerator_analyticAt 2 3 (by norm_num) (by norm_num)), ?_,
    kernelEisensteinCorrectionNumerator_center 2 3 (by norm_num) (by norm_num)⟩
  filter_upwards [kernelEisensteinCorrectionNumerator_eventually 2 3 (by norm_num) (by norm_num)]
    with s hs
  change (s - 4 / 3) * levelPairing G hG (kernelEisensteinL2Correction 2 3 _ _ s) =
    levelPairing G hG (kernelEisensteinCorrectionNumerator 2 3 _ _ s)
  rw [← hs, map_smul, smul_eq_mul]

/-- For `Re s > 4`, `Im s > 0`, the correction pairs as the remainder `E(s) − seed(s)`. -/
theorem levelPairing_correction_eq (G : HyperbolicSpace → ℂ)
    (hG : MemLp G 2 (hyperbolicVolume.restrict levelSet)) (s : ℂ) (hs : 4 < s.re) (hi : 0 < s.im) :
    levelPairing G hG (eisensteinCorrection s) = ∫ w in levelSet,
      G w * (hyperbolicEisenstein s w - smoothCuspSeed 2 3 s w) ∂hyperbolicVolume := by
  rw [levelPairing_apply]
  have hov := kernelEisensteinL2Correction_initial_overlap 2 3 (by norm_num) (by norm_num) s hs hi
  have hpull := (quotient_projection_measurePreserving globalKubotaKernel).quasiMeasurePreserving.ae_eq_comp hov
  have hpull' := ae_restrict_of_ae_restrict_of_subset levelSet_subset_kernelSet hpull
  refine integral_congr_ae ?_
  filter_upwards [hpull'] with w hw
  simp only [Function.comp_apply] at hw
  rw [hw]
  rfl

/-! ### The full pairing -/

theorem eisenstein_sub_seed_continuous (s : ℂ) (hs : 2 < s.re) :
    Continuous (fun w => hyperbolicEisenstein s w - smoothCuspSeed 2 3 s w) :=
  (kernelEisensteinRemainder_smooth 2 3 (by norm_num) (by norm_num) s hs).continuous.comp
    (continuous_integralOrbitProjection _)

theorem levelSet_volume_lt_top : hyperbolicVolume levelSet < ⊤ := by
  letI : globalKubotaKernel.FiniteIndex := globalKubotaKernel_finiteIndex
  exact (measure_mono levelSet_subset_kernelSet).trans_lt
    (hyperbolicFundamentalSet_volume_lt_top globalKubotaKernel globalKubotaKernel_le_levelThree)

/-- **The pairing with the Eisenstein series, split.** For `Re s > 4`, `Im s > 0`, if `G · seed(s)` is
integrable on `D_Γ`: `∫_{D_Γ} G · E(s) = ∫_{D_Γ} G · seed(s) + ⟨G, Corr(s)⟩`. -/
theorem integral_mul_eisenstein_eq (G : HyperbolicSpace → ℂ)
    (hG : MemLp G 2 (hyperbolicVolume.restrict levelSet)) (s : ℂ) (hs : 4 < s.re) (hi : 0 < s.im)
    (hseed : IntegrableOn (fun w => G w * smoothCuspSeed 2 3 s w) levelSet hyperbolicVolume) :
    ∫ w in levelSet, G w * hyperbolicEisenstein s w ∂hyperbolicVolume =
      ∫ w in levelSet, G w * smoothCuspSeed 2 3 s w ∂hyperbolicVolume +
        levelPairing G hG (eisensteinCorrection s) := by
  haveI : IsFiniteMeasure (hyperbolicVolume.restrict levelSet) :=
    isFiniteMeasure_restrict.mpr levelSet_volume_lt_top.ne
  have hG1 : Integrable G (hyperbolicVolume.restrict levelSet) := hG.integrable one_le_two
  have hrem : IntegrableOn (fun w => G w * (hyperbolicEisenstein s w - smoothCuspSeed 2 3 s w))
      levelSet hyperbolicVolume := by
    have h := hG1.bdd_mul (c := eisensteinRemainderBound 3 s)
      (eisenstein_sub_seed_continuous s (by linarith)).aestronglyMeasurable
      (Eventually.of_forall fun w => eisenstein_sub_seed_bounded 2 3 (by norm_num) (by norm_num) s hs w)
    refine h.congr (Eventually.of_forall fun w => ?_)
    exact mul_comm _ _
  rw [levelPairing_correction_eq G hG s hs hi, ← integral_add hseed hrem]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  ring

/-! ### The seed term -/

/-- The smooth seed is the incomplete Eisenstein series of its profile `χ v^s`. -/
theorem smoothCuspSeed_eq (s : ℂ) (w : HyperbolicSpace) :
    smoothCuspSeed 2 3 s w = incompleteEisenstein (cuspSeedProfile 2 3 s) w := by
  rw [smoothCuspSeed, cuspCutoffCorrection, incompleteEisenstein]
  refine tsum_congr fun x => ?_
  rw [cuspCutoffTerm]
  split_ifs with h
  · rfl
  · rw [cuspSeedProfile_zero 2 3 s _ (by norm_num) (by linarith [not_lt.mp h]), mul_zero]

/-- **The seed term is a Mellin transform of the constant term.** For `G` of multiplier `κ⁻¹` with
`G · χ v^s` integrable on the strip:
`∫_{D_Γ} G · seed(s) = ∫_0^∞ χ(v) v^s (∫_P G(z + jv) dz) v^{−3} dv`. -/
theorem integral_mul_seed_eq (G : HyperbolicSpace → ℂ)
    (hF : ∀ (M : levelThree) (w : HyperbolicSpace), G (complexMatrix M • w) = (complexCharacter M)⁻¹ * G w)
    (s : ℂ) (hint : IntegrableOn (unfolded G (cuspSeedProfile 2 3 s)) cuspStripSet hyperbolicVolume) :
    ∫ w in levelSet, G w * smoothCuspSeed 2 3 s w ∂hyperbolicVolume =
      ∫ v in Set.Ioi (0 : ℝ), cuspSeedProfile 2 3 s v *
        (∫ z in periodDomain, G (cuspCoordinateLift (v, z))) / (v : ℂ) ^ 3 := by
  simp_rw [smoothCuspSeed_eq]
  exact integral_mul_incompleteEisenstein_eq_constantTerm G hF _ hint

end GaloisForLFunctions.SpectralTheoryOfTheCubicCover
