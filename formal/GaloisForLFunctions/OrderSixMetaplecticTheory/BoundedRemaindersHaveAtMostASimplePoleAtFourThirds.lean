import GaloisForLFunctions.OrderSixMetaplecticTheory.TheHeckeAtFourTraceIsEightThetaSquaresUpToABoundedRemainder
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheSquaredThetaSeriesHasADoublePole

/-!
# Bounded remainders have at most a simple pole at four thirds

A Rankin–Selberg tool for functions **without growth**. Let `G` have the multiplier `κ⁻¹` of `θ²` on `Γ(3)`, be
measurable, bounded on `ℍ³` and `O(v^{−7/3})` on the standard strip above height `2` (`RemainderData`). Then:

* `∫_{D_Γ} G E(s) = ∫_0^∞ v^s a₀(G)(v) v^{−3} dv` for `2 < Re s < 13/3` (`RemainderData.integral_mul_eisenstein`);
* for `4 < Re s < 13/3`, `Im s > 0` the pairing equals `S(s) + C(s)` (`RemainderData.pairing_eq`), the seed term
  `S` holomorphic on `0 < Re s < 13/3` and the resolvent correction `C` holomorphic off the real axis with
  `(s − 4/3) C(s)` holomorphic at `4/3`;
* hence `Λ_G = S + C` is holomorphic on `{1 < Re s < 13/3, Im s > 0}` and on a punctured neighbourhood of `4/3`, and
  `(s − 4/3)² Λ_G(s) → 0` (`RemainderData.sq_mul_tendsto_zero`): **at most a simple pole**.

The double pole of a squared theta series comes only from growth at the cusps; a function whose growth has been
matched exactly contributes none.
-/

noncomputable section

open MeasureTheory Filter Function Asymptotics
open scoped BigOperators Classical MatrixGroups ComplexConjugate ENNReal Topology

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicKubota
  MetaplecticMobiusDescent.CubicEisenstein SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

/-- A bounded, square integrable function of multiplier `κ⁻¹`, `O(v^{−7/3})` high on the standard strip. -/
structure RemainderData (G : HyperbolicSpace → ℂ) : Prop where
  automorphy : ∀ (M : levelThree) (w : HyperbolicSpace), G (complexMatrix M • w) = (complexCharacter M)⁻¹ * G w
  measurable : Measurable G
  bounded : ∃ B : ℝ, ∀ w, ‖G w‖ ≤ B
  high : ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : ℂ) (v : ℝ) (hv : 0 < v), 2 ≤ v → ‖G (upperPoint z v hv)‖ ≤ C * v ^ (-(7 : ℝ) / 3)
  memLp : MemLp G 2 (hyperbolicVolume.restrict levelSet)

namespace RemainderData

variable {G : HyperbolicSpace → ℂ} (hG : RemainderData G)
include hG

/-- `∫_{strip} |G| v^σ dμ < ∞` for `2 < σ < 13/3`. -/
theorem strip_lintegral_lt_top {σ : ℝ} (hσ2 : 2 < σ) (hσ : σ < 13 / 3) :
    ∫⁻ w in cuspStripSet, ‖G w‖ₑ * ENNReal.ofReal (hyperbolicHeight w ^ σ) ∂hyperbolicVolume < ⊤ := by
  obtain ⟨B, hB⟩ := hG.bounded
  obtain ⟨C, hC, hhigh⟩ := hG.high
  set B' := max B 0
  have hB' : ∀ w, ‖G w‖ ≤ B' := fun w => (hB w).trans (le_max_left _ _)
  have hm : Measurable (fun w => ‖G w‖ₑ * ENNReal.ofReal (hyperbolicHeight w ^ σ)) :=
    hG.measurable.enorm.mul (ENNReal.measurable_ofReal.comp (hyperbolicHeight_continuous.measurable.pow_const σ))
  rw [cuspStrip_lintegral _ hm]
  set g : ℝ → ℝ := fun v => (Set.Ioc 0 2).indicator (fun v => B' * periodAreaReal * v ^ (σ - 3)) v +
    (Set.Ioi 2).indicator (fun v => C * periodAreaReal * v ^ (σ - 3 - 7 / 3)) v with hgdef
  have hg1 : IntegrableOn (fun v : ℝ => B' * periodAreaReal * v ^ (σ - 3)) (Set.Ioc 0 2) := by
    have := intervalIntegral.intervalIntegrable_rpow' (r := σ - 3) (by linarith) (a := 0) (b := 2)
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp this).const_mul _
  have hg2 : IntegrableOn (fun v : ℝ => C * periodAreaReal * v ^ (σ - 3 - 7 / 3)) (Set.Ioi 2) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)).const_mul _
  have hg : IntegrableOn g (Set.Ioi 0) :=
    (((integrable_indicator_iff measurableSet_Ioc).mpr hg1).add
      ((integrable_indicator_iff measurableSet_Ioi).mpr hg2)).integrableOn
  have hg0 : ∀ v, 0 ≤ g v := by
    intro v
    simp only [hgdef]
    refine add_nonneg (Set.indicator_nonneg (fun v hv => ?_) _) (Set.indicator_nonneg (fun v hv => ?_) _)
    · have : (0 : ℝ) < v := hv.1
      positivity
    · have : (0 : ℝ) < v := lt_trans (by norm_num) hv
      positivity
  have hP : volume periodDomain = ENNReal.ofReal periodAreaReal := periodDomain_volume
  calc ∫⁻ v in Set.Ioi (0 : ℝ), ∫⁻ z in periodDomain,
        ‖G (cuspCoordinateLift (v, z))‖ₑ *
          ENNReal.ofReal (hyperbolicHeight (cuspCoordinateLift (v, z)) ^ σ) * ENNReal.ofReal ((v ^ 3)⁻¹)
      ≤ ∫⁻ v in Set.Ioi (0 : ℝ), ENNReal.ofReal (g v) := by
        refine setLIntegral_mono' measurableSet_Ioi fun v (hv : 0 < v) => ?_
        have hlift : ∀ z, cuspCoordinateLift (v, z) = upperPoint z v hv := fun z =>
          cuspCoordinateLift_positive v z hv
        simp only [hlift, hyperbolicHeight_upperPoint]
        have hpow : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x * ENNReal.ofReal (v ^ σ) * ENNReal.ofReal ((v ^ 3)⁻¹) =
            ENNReal.ofReal (x * v ^ (σ - 3)) := by
          intro x hx
          rw [← ENNReal.ofReal_mul hx, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [Real.rpow_sub hv, mul_assoc, div_eq_mul_inv]
          norm_cast
        by_cases hv2 : v ≤ 2
        · have hgv : g v = B' * periodAreaReal * v ^ (σ - 3) := by
            simp only [hgdef, Set.indicator_of_mem (show v ∈ Set.Ioc 0 2 from ⟨hv, hv2⟩),
              Set.indicator_of_notMem (show v ∉ Set.Ioi 2 from fun h => absurd hv2 (not_le.mpr h)), add_zero]
          calc ∫⁻ z in periodDomain, ‖G (upperPoint z v hv)‖ₑ * ENNReal.ofReal (v ^ σ) *
                ENNReal.ofReal ((v ^ 3)⁻¹)
              ≤ ∫⁻ _z in periodDomain, ENNReal.ofReal (B' * v ^ (σ - 3)) := by
                refine lintegral_mono fun z => ?_
                rw [← hpow B' (le_max_right _ _)]
                gcongr
                rw [← ofReal_norm]
                exact ENNReal.ofReal_le_ofReal (hB' _)
            _ = ENNReal.ofReal (g v) := by
                rw [setLIntegral_const, hP, ← ENNReal.ofReal_mul (by positivity), hgv]
                ring_nf
        · have hv2' : 2 < v := not_le.mp hv2
          have hgv : g v = C * periodAreaReal * v ^ (σ - 3 - 7 / 3) := by
            simp only [hgdef, Set.indicator_of_notMem (show v ∉ Set.Ioc 0 2 from fun h => hv2 h.2),
              Set.indicator_of_mem (show v ∈ Set.Ioi 2 from hv2'), zero_add]
          calc ∫⁻ z in periodDomain, ‖G (upperPoint z v hv)‖ₑ * ENNReal.ofReal (v ^ σ) *
                ENNReal.ofReal ((v ^ 3)⁻¹)
              ≤ ∫⁻ _z in periodDomain, ENNReal.ofReal (C * v ^ (-(7 : ℝ) / 3) * v ^ (σ - 3)) := by
                refine lintegral_mono fun z => ?_
                rw [← hpow (C * v ^ (-(7 : ℝ) / 3)) (by positivity)]
                gcongr
                rw [← ofReal_norm]
                exact ENNReal.ofReal_le_ofReal (hhigh z v hv hv2'.le)
            _ = ENNReal.ofReal (g v) := by
                rw [setLIntegral_const, hP, ← ENNReal.ofReal_mul (by positivity), hgv]
                congr 1
                rw [show σ - 3 - 7 / 3 = -(7 : ℝ) / 3 + (σ - 3) by ring, Real.rpow_add hv]
                ring
    _ = ENNReal.ofReal (∫ v in Set.Ioi (0 : ℝ), g v) :=
        (ofReal_integral_eq_lintegral_ofReal hg (Eventually.of_forall hg0)).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

theorem integrableOn_unfolded (ψ : ℝ → ℂ) (hψm : Measurable ψ) {σ : ℝ} (hσ2 : 2 < σ)
    (hσ : σ < 13 / 3) (hψ : ∀ v : ℝ, 0 < v → ‖ψ v‖ ≤ v ^ σ) :
    IntegrableOn (unfolded G ψ) cuspStripSet hyperbolicVolume := by
  refine ⟨(hG.measurable.mul (hψm.comp hyperbolicHeight_continuous.measurable)).aestronglyMeasurable, ?_⟩
  refine lt_of_le_of_lt (lintegral_mono fun w => ?_) (hG.strip_lintegral_lt_top hσ2 hσ)
  rw [unfolded, enorm_mul]
  gcongr
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (hψ _ (hyperbolicHeight_pos w))

theorem integrableOn_mul_incomplete (ψ : ℝ → ℂ) (hψm : Measurable ψ) {σ : ℝ}
    (hσ2 : 2 < σ) (hσ : σ < 13 / 3) (hψ : ∀ v : ℝ, 0 < v → ‖ψ v‖ ≤ v ^ σ) :
    IntegrableOn (fun w => G w * incompleteEisenstein ψ w) levelSet hyperbolicVolume := by
  have hun := hG.integrableOn_unfolded ψ hψm hσ2 hσ hψ
  refine ⟨(hG.measurable.mul (incompleteEisenstein_measurable ψ hψm)).aestronglyMeasurable, ?_⟩
  have heq := lintegral_norm_mul_incompleteEisenstein CuspDomain.strip G hG.automorphy ψ
    (hG.measurable.mul (hψm.comp hyperbolicHeight_continuous.measurable)).enorm.aemeasurable
  change ∫⁻ w in levelSet, ‖G w * incompleteEisenstein ψ w‖ₑ ∂hyperbolicVolume < ⊤
  refine lt_of_le_of_lt (lintegral_mono fun w => ?_) (heq.trans_lt hun.2)
  rw [enorm_mul, ENNReal.tsum_mul_left, incompleteEisenstein]
  gcongr
  refine enorm_tsum_le_tsum_enorm.trans (le_of_eq (tsum_congr fun x => ?_))
  rw [enorm_mul, ← ofReal_norm ((cosetCharacter x)⁻¹), norm_inv, norm_cosetCharacter, inv_one,
    ENNReal.ofReal_one, one_mul]

/-- **The unfolding.** `∫_{D_Γ} G E(s) = ∫_0^∞ v^s a₀(G)(v) v^{−3} dv` for `2 < Re s < 13/3`. -/
theorem integral_mul_eisenstein (s : ℂ) (hs2 : 2 < s.re) (hs : s.re < 13 / 3) :
    ∫ w in levelSet, G w * hyperbolicEisenstein s w ∂hyperbolicVolume =
      ∫ v in Set.Ioi (0 : ℝ), (v : ℂ) ^ s * (∫ z in periodDomain, G (cuspCoordinateLift (v, z))) /
        (v : ℂ) ^ 3 := by
  have hψ : ∀ v : ℝ, 0 < v → ‖(v : ℂ) ^ s‖ ≤ v ^ s.re := fun v hv =>
    (Complex.norm_cpow_eq_rpow_re_of_pos hv s).le
  exact integral_mul_hyperbolicEisenstein_eq_constantTerm G hG.automorphy s
    (hG.integrableOn_unfolded _ (Complex.measurable_ofReal.pow_const s) hs2 hs hψ)

end RemainderData


/-! ### The seed pairing and the correction pairing -/

/-- The seed pairing `S(s) = ∫_0^∞ χ(v) v^s a₀(G)(v) v^{−3} dv`. -/
def remainderSeed (G : HyperbolicSpace → ℂ) (s : ℂ) : ℂ :=
  ∫ v in Set.Ioi (0 : ℝ), cuspSeedProfile 2 3 s v * cuspConstantTerm G v / (v : ℂ) ^ 3

/-- `χ(v) a₀(G)(v) v^{−2}`. -/
def remainderSeedKernel (G : HyperbolicSpace → ℂ) (v : ℝ) : ℂ :=
  (cuspTransition 2 3 v : ℂ) * cuspConstantTerm G v / (v : ℂ) ^ 2

namespace RemainderData

variable {G : HyperbolicSpace → ℂ} (hG : RemainderData G)
include hG

theorem norm_cuspConstantTerm_high :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, 2 ≤ v → ‖cuspConstantTerm G v‖ ≤ C * v ^ (-(7 : ℝ) / 3) := by
  obtain ⟨C, hC, hhigh⟩ := hG.high
  refine ⟨C * periodAreaReal, by positivity, fun v hv => ?_⟩
  have hv0 : 0 < v := by linarith
  have := norm_cuspConstantTerm_le G v hv0 _ fun z => hhigh z v hv0 hv
  linarith [this]

omit hG in
theorem remainderSeedKernel_eq_zero (v : ℝ) (hv : v ≤ 2) : remainderSeedKernel G v = 0 := by
  rw [remainderSeedKernel, cuspTransition_zero 2 3 v (by norm_num) hv, Complex.ofReal_zero, zero_mul, zero_div]

theorem remainderSeedKernel_measurable : Measurable (remainderSeedKernel G) := by
  unfold remainderSeedKernel
  exact ((Complex.continuous_ofReal.measurable.comp (cuspTransition_contDiff 2 3).continuous.measurable).mul
    (cuspConstantTerm_measurable _ hG.measurable).measurable).div (Complex.measurable_ofReal.pow_const 2)

theorem norm_remainderSeedKernel_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, 2 ≤ v → ‖remainderSeedKernel G v‖ ≤ C * v ^ (-(13 : ℝ) / 3) := by
  obtain ⟨C, hC, hb⟩ := hG.norm_cuspConstantTerm_high
  refine ⟨C, hC, fun v hv => ?_⟩
  have hv0 : 0 < v := by linarith
  have h0 : 0 ≤ cuspTransition 2 3 v := Real.smoothTransition.nonneg _
  have h1 : cuspTransition 2 3 v ≤ 1 := Real.smoothTransition.le_one _
  rw [remainderSeedKernel, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg h0, norm_pow,
    Complex.norm_real, Real.norm_of_nonneg hv0.le]
  have hpow : v ^ (-(7 : ℝ) / 3) / v ^ 2 = v ^ (-(13 : ℝ) / 3) := by
    rw [show -(13 : ℝ) / 3 = -(7 : ℝ) / 3 - 2 by norm_num, Real.rpow_sub hv0]
    norm_cast
  calc cuspTransition 2 3 v * ‖cuspConstantTerm G v‖ / v ^ 2
      ≤ 1 * (C * v ^ (-(7 : ℝ) / 3)) / v ^ 2 := by
        gcongr
        exact hb v hv
    _ = C * v ^ (-(13 : ℝ) / 3) := by rw [one_mul, mul_div_assoc, hpow]

omit hG in
theorem remainderSeed_eq_mellin (s : ℂ) : remainderSeed G s = mellin (remainderSeedKernel G) s := by
  rw [remainderSeed, mellin]
  refine setIntegral_congr_fun measurableSet_Ioi fun v (hv : 0 < v) => ?_
  have hv0 : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
  rw [cuspSeedProfile, positiveHeightPower_eq_cpow s v hv, remainderSeedKernel, smul_eq_mul,
    Complex.cpow_sub _ _ hv0, Complex.cpow_one]
  field_simp

/-- **The seed pairing is holomorphic on `0 < Re s < 13/3`.** -/
theorem remainderSeed_differentiableAt (s : ℂ) (hs0 : 0 < s.re) (hs : s.re < 13 / 3) :
    DifferentiableAt ℂ (remainderSeed G) s := by
  obtain ⟨C, hC, hb⟩ := hG.norm_remainderSeedKernel_le
  have hfun : remainderSeed G = mellin (remainderSeedKernel G) := funext remainderSeed_eq_mellin
  rw [hfun]
  have hint : IntegrableOn (remainderSeedKernel G) (Set.Ioi 0) := by
    have hg : IntegrableOn (fun v : ℝ => C * v ^ (-(13 : ℝ) / 3)) (Set.Ioi 2) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)).const_mul _
    have h2 : IntegrableOn (remainderSeedKernel G) (Set.Ioi 2) :=
      hg.mono' hG.remainderSeedKernel_measurable.aestronglyMeasurable
        (ae_restrict_of_forall_mem measurableSet_Ioi fun v (hv : 2 < v) => hb v hv.le)
    refine h2.of_forall_sdiff_eq_zero measurableSet_Ioi fun v hv => ?_
    exact remainderSeedKernel_eq_zero v (not_lt.mp hv.2)
  refine mellin_differentiableAt_of_isBigO_rpow (a := 13 / 3) (b := 0) hint.locallyIntegrableOn ?_ hs ?_ hs0
  · refine IsBigO.of_bound C ?_
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with v hv
    have hv0 : 0 < v := by linarith
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hv0.le _)]
    have := hb v hv
    rwa [show -(13 : ℝ) / 3 = -(13 / 3) by norm_num] at this
  · refine IsBigO.of_bound 0 ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 2 by norm_num)] with v hv
    rw [remainderSeedKernel_eq_zero v hv.2.le, norm_zero, zero_mul]

/-- The Eisenstein pairing `Λ_G(s) = S(s) + C(s)`. -/
def pairing (s : ℂ) : ℂ := remainderSeed G s + levelPairing G hG.memLp (eisensteinCorrection s)

/-- **The pairing identity.** For `4 < Re s < 13/3`, `Im s > 0`: `∫_{D_Γ} G E(s) = Λ_G(s)`. -/
theorem pairing_eq (s : ℂ) (hs4 : 4 < s.re) (hs : s.re < 13 / 3) (hi : 0 < s.im) :
    ∫ w in levelSet, G w * hyperbolicEisenstein s w ∂hyperbolicVolume = hG.pairing s := by
  have hσ2 : 2 < s.re := by linarith
  have hseed : IntegrableOn (fun w => G w * smoothCuspSeed 2 3 s w) levelSet hyperbolicVolume := by
    simp_rw [smoothCuspSeed_eq]
    exact hG.integrableOn_mul_incomplete _ (cuspSeedProfile_measurable s) hσ2 hs (norm_cuspSeedProfile_le s)
  have hint := hG.integrableOn_unfolded _ (cuspSeedProfile_measurable s) hσ2 hs (norm_cuspSeedProfile_le s)
  rw [integral_mul_eisenstein_eq G hG.memLp s hs4 hi hseed, integral_mul_seed_eq G hG.automorphy s hint]
  rfl

theorem pairing_differentiableAt (s : ℂ) (hs1 : 1 < s.re) (hs : s.re < 13 / 3) (hi : 0 < s.im) :
    DifferentiableAt ℂ hG.pairing s :=
  (hG.remainderSeed_differentiableAt s (by linarith) hs).add
    (levelPairing_correction_analyticAt G hG.memLp s (by linarith) hi.ne').differentiableAt

/-- **At most a simple pole at `4/3`.** `Λ_G` is holomorphic on a punctured neighbourhood of `4/3` and
`(s − 4/3)² Λ_G(s) → 0`. -/
theorem pairing_near_four_thirds :
    (∀ᶠ s in 𝓝[≠] (4 / 3 : ℂ), DifferentiableAt ℂ hG.pairing s) ∧
      Tendsto (fun s => (s - 4 / 3) ^ 2 * hG.pairing s) (𝓝[≠] (4 / 3 : ℂ)) (𝓝 0) := by
  obtain ⟨hN, hev, -⟩ := levelPairing_correction_center G hG.memLp
  set N := fun s => levelPairing G hG.memLp (correctionNumerator s)
  constructor
  · rw [eventually_nhdsWithin_iff] at hev
    have hP := (hN.eventually_analyticAt.and (hev.and near_four_thirds)).eventually_nhds
    rw [eventually_nhdsWithin_iff]
    filter_upwards [hP] with t ht htc
    have htc' : t ≠ 4 / 3 := htc
    have hne : t - 4 / 3 ≠ 0 := sub_ne_zero.mpr htc'
    obtain ⟨hNt, -, hre1, hre2, -⟩ := ht.self_of_nhds
    have hcorr_eq : (fun u => levelPairing G hG.memLp (eisensteinCorrection u)) =ᶠ[𝓝 t]
        fun u => N u / (u - 4 / 3) := by
      have hne' : ∀ᶠ u in 𝓝 t, u ≠ 4 / 3 := isOpen_ne.mem_nhds htc'
      filter_upwards [ht, hne'] with u hu hu'
      rw [eq_div_iff (sub_ne_zero.mpr hu'), mul_comm]
      exact hu.2.1 hu'
    have hcorr : DifferentiableAt ℂ (fun u => levelPairing G hG.memLp (eisensteinCorrection u)) t :=
      (hNt.differentiableAt.div (differentiableAt_id.sub_const _) hne).congr_of_eventuallyEq hcorr_eq
    exact (hG.remainderSeed_differentiableAt t (by linarith) hre2).add hcorr
  · have hseed := hG.remainderSeed_differentiableAt (4 / 3) (by norm_num) (by norm_num)
    set F : ℂ → ℂ := fun s => (s - 4 / 3) ^ 2 * remainderSeed G s + (s - 4 / 3) * N s with hFdef
    have hlin : ContinuousAt (fun s : ℂ => s - 4 / 3) (4 / 3) := (continuous_id.sub continuous_const).continuousAt
    have hFc : ContinuousAt F (4 / 3) :=
      ((hlin.pow 2).mul hseed.continuousAt).add (hlin.mul hN.continuousAt)
    have hF0 : F (4 / 3) = 0 := by simp [hFdef]
    rw [← hF0]
    refine (hFc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [hev] with s hs
    have hs' : (s - 4 / 3) * levelPairing G hG.memLp (eisensteinCorrection s) = N s := hs
    simp only [hFdef, pairing]
    linear_combination (-(s - 4 / 3)) * hs'

end RemainderData

end GaloisForLFunctions.OrderSixMetaplecticTheory
