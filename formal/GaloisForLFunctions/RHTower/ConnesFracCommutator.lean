import GaloisForLFunctions.RHTower.ConnesCutoffCommutatorLocal
import GaloisForLFunctions.RHTower.ConnesFracConvDecay
import GaloisForLFunctions.RHTower.ConnesCutoffTailTwoSided
import GaloisForLFunctions.RHTower.ConnesCutoffBesovMass

/-!
# The commutator of the fractional kernel with the cut-off

Preparation for §VII (42) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

Three things are established.

* The thickened supremum `Sup_{|ε| ≤ 1}|η(x+ε)|` of a continuous function is *continuous* in `x`,
  and dominates each of the values it is a supremum of.  Without this the tail estimates of
  §VII (47) would be statements about a possibly non-measurable integrand, hence vacuous.
* The `ε`-integrands of (39), both for `η` and for `ε_Λ η`, are absolutely integrable, so the
  commutator identity of `ConnesCutoffCommutator` integrates to the operator identity

    `C_{α,v} * (ε_Λ η) = ε_Λ · (C_{α,v} * η) + [C_{α,v}, ε_Λ] η`.

* The commutator vanishes identically once `|x| ≤ Λ − 1`, i.e. it is supported in Connes'
  thickened tail `X_Λ`.
-/

open MeasureTheory Real Set Filter Topology
open scoped SchwartzMap Real

namespace GaloisForLFunctions.RHTower

noncomputable section

/-! ## The thickened supremum -/

theorem connesUnitSup_bddAbove {f : ℝ → ℂ} (hf : Continuous f) (x : ℝ) :
    BddAbove (Set.range fun ε : ↥(Icc (-1 : ℝ) 1) => ‖f (x + (ε : ℝ))‖) := by
  have hK : IsCompact (Icc (-1 : ℝ) 1) := isCompact_Icc
  have himg : IsCompact ((fun ε : ℝ => ‖f (x + ε)‖) '' Icc (-1 : ℝ) 1) :=
    hK.image ((hf.comp (continuous_const.add continuous_id)).norm)
  have hb := himg.bddAbove
  refine hb.mono ?_
  rintro y ⟨ε, rfl⟩
  exact ⟨(ε : ℝ), ε.2, rfl⟩

/-- Each value is dominated by the thickened supremum. -/
theorem le_connesUnitSup {f : ℝ → ℂ} (hf : Continuous f) (x : ℝ) {ε : ℝ} (hε : |ε| ≤ 1) :
    ‖f (x + ε)‖ ≤ connesUnitSup f x := by
  have hmem : ε ∈ Icc (-1 : ℝ) 1 := Set.mem_Icc.mpr (abs_le.mp hε)
  exact le_ciSup (connesUnitSup_bddAbove hf x) (⟨ε, hmem⟩ : ↥(Icc (-1 : ℝ) 1))

/-- **The thickened supremum is continuous.**  Its index set is compact. -/
theorem connesUnitSup_continuous {f : ℝ → ℂ} (hf : Continuous f) :
    Continuous (connesUnitSup f) := by
  have hK : IsCompact (Icc (-1 : ℝ) 1) := isCompact_Icc
  have hc : Continuous (Function.uncurry fun (x : ℝ) (ε : ℝ) => ‖f (x + ε)‖) :=
    (hf.comp (continuous_fst.add continuous_snd)).norm
  have h := hK.continuous_sSup (f := fun (x : ℝ) (ε : ℝ) => ‖f (x + ε)‖) hc
  have heq : (fun x : ℝ => sSup ((fun ε : ℝ => ‖f (x + ε)‖) '' Icc (-1 : ℝ) 1))
      = connesUnitSup f := by
    funext x
    rw [connesUnitSup, sSup_image']
  rwa [heq] at h

theorem connesUnitSup_measurable {f : ℝ → ℂ} (hf : Continuous f) :
    Measurable (connesUnitSup f) := (connesUnitSup_continuous hf).measurable

/-! ## Integrability of the two `ε`-integrands -/

theorem connes_fracConv_integrand_integrable {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ψ : ℝ → ℝ} (hψc : Continuous ψ) (hψ0 : ∀ t, 0 ≤ ψ t) (hψ1 : ∀ t, ψ t ≤ 1)
    (hψsupp : ∀ t : ℝ, 1 < t → ψ t = 0) (η : 𝓢(ℝ, ℂ)) (x : ℝ) :
    Integrable (fun ε : ℝ => ((connesFracWeight α ψ ε : ℝ) : ℂ) * (η (x + ε) - η x)) volume := by
  obtain ⟨C, hC0, hC⟩ := connes_schwartz_deriv_weight_order η 0
  have hJint : Integrable (Set.indicator (Icc (-1 : ℝ) 1) (fun ε : ℝ => |ε| ^ (-α))) volume :=
    connes_fracEps_integrable hα1
  have hwmeas : Measurable (connesFracWeight α ψ) :=
    connesFracWeight_measurable (by linarith) hψc
  refine MeasureTheory.Integrable.mono' (hJint.const_mul (2 ^ (0 : ℕ) * C)) ?_
    (Filter.Eventually.of_forall fun ε => ?_)
  · refine (Measurable.mul ?_ ?_).aestronglyMeasurable
    · exact Complex.measurable_ofReal.comp hwmeas
    · exact ((η.continuous.comp (continuous_const.add continuous_id)).sub
        continuous_const).measurable
  · by_cases hmem : ε ∈ Icc (-1 : ℝ) 1
    · have hεle : |ε| ≤ 1 := abs_le.mpr ⟨hmem.1, hmem.2⟩
      have hind : Set.indicator (Icc (-1 : ℝ) 1) (fun ε : ℝ => |ε| ^ (-α)) ε = |ε| ^ (-α) :=
        Set.indicator_of_mem hmem (fun ε : ℝ => |ε| ^ (-α))
      rw [hind, norm_mul]
      have hwabs : ‖(((connesFracWeight α ψ ε : ℝ)) : ℂ)‖ ≤ |ε| ^ (-1 - α) := by
        rw [Complex.norm_real, Real.norm_eq_abs, connesFracWeight,
          abs_of_nonneg (mul_nonneg (hψ0 _) (Real.rpow_nonneg (abs_nonneg ε) _))]
        calc ψ |ε| * |ε| ^ (-1 - α) ≤ 1 * |ε| ^ (-1 - α) :=
              mul_le_mul_of_nonneg_right (hψ1 _) (Real.rpow_nonneg (abs_nonneg ε) _)
          _ = |ε| ^ (-1 - α) := one_mul _
      have hdiff := connes_schwartz_diff_bound_order η 0 hC0 hC (y := x) (ε := ε) hεle
      simp only [pow_zero, one_mul, Nat.cast_zero, neg_zero, Real.rpow_zero, mul_one] at hdiff
      rcases eq_or_ne ε 0 with hε0 | hε0
      · subst hε0
        have : (0 : ℝ) ≤ 2 ^ (0 : ℕ) * C * |(0 : ℝ)| ^ (-α) := by
          have h1 : (0 : ℝ) ≤ |(0 : ℝ)| ^ (-α) := Real.rpow_nonneg (abs_nonneg _) _
          positivity
        simpa using this
      · have hεpos : (0 : ℝ) < |ε| := abs_pos.mpr hε0
        have hcomb : |ε| ^ (-1 - α) * |ε| = |ε| ^ (-α) := by
          rw [show (-1 - α : ℝ) = -α + -1 by ring, Real.rpow_add hεpos,
            Real.rpow_neg_one, inv_mul_cancel_right₀ (ne_of_gt hεpos)]
        calc ‖(((connesFracWeight α ψ ε : ℝ)) : ℂ)‖ * ‖η (x + ε) - η x‖
            ≤ (|ε| ^ (-1 - α)) * (C * |ε|) :=
              mul_le_mul hwabs hdiff (norm_nonneg _) (Real.rpow_nonneg (abs_nonneg ε) _)
          _ = C * (|ε| ^ (-1 - α) * |ε|) := by ring
          _ = C * |ε| ^ (-α) := by rw [hcomb]
          _ = 2 ^ (0 : ℕ) * C * |ε| ^ (-α) := by norm_num
    · have hgt : 1 < |ε| := by
        by_contra hcon
        exact hmem (Set.mem_Icc.mpr (abs_le.mp (not_lt.mp hcon)))
      have hw0 : connesFracWeight α ψ ε = 0 := connesFracWeight_eq_zero hψsupp hgt
      rw [hw0, Set.indicator_of_notMem hmem]
      simp

theorem connes_fracCommutator_integrand_integrable {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ψ : ℝ → ℝ} (hψc : Continuous ψ) (hψ0 : ∀ t, 0 ≤ ψ t) (hψ1 : ∀ t, ψ t ≤ 1)
    (hψsupp : ∀ t : ℝ, 1 < t → ψ t = 0) (L : ℝ) (η : 𝓢(ℝ, ℂ)) {x : ℝ} (hx : x ≠ 0) :
    Integrable (fun ε : ℝ => ((connesFracWeight α ψ ε : ℝ) : ℂ) *
      (((connesCutoffExcess L (x + ε) - connesCutoffExcess L x : ℝ) : ℂ) * η (x + ε))) volume := by
  set M : ℝ := connesUnitSup ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x with hM
  have hMbd : ∀ ε : ℝ, |ε| ≤ 1 → ‖(η : 𝓢(ℝ, ℂ)) (x + ε)‖ ≤ M :=
    fun ε hε => le_connesUnitSup η.continuous x hε
  set G : ℝ → ℝ := fun ε => abs (Real.log |x + ε| - Real.log |x|) * (|ε| ^ (1 + α))⁻¹ with hG
  have hGnn : ∀ ε : ℝ, 0 ≤ G ε := by
    intro ε; rw [hG]; positivity
  have hGint : Integrable G volume := connes_logShift_integrable_full hx hα0 hα1
  have hψGint : Integrable (fun ε : ℝ => M * (ψ |ε| * G ε)) volume := by
    have hbase : Integrable (fun ε : ℝ => ψ |ε| * G ε) volume := by
      refine MeasureTheory.Integrable.mono' hGint ?_ (Filter.Eventually.of_forall fun ε => ?_)
      · exact ((hψc.comp continuous_abs).aestronglyMeasurable).mul hGint.aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hψ0 _) (hGnn ε))]
        calc ψ |ε| * G ε ≤ 1 * G ε := mul_le_mul_of_nonneg_right (hψ1 _) (hGnn ε)
          _ = G ε := one_mul _
    exact hbase.const_mul M
  have hwmeas : Measurable (connesFracWeight α ψ) :=
    connesFracWeight_measurable (by linarith) hψc
  refine MeasureTheory.Integrable.mono' hψGint ?_ (Filter.Eventually.of_forall fun ε => ?_)
  · refine (Measurable.mul ?_ ?_).aestronglyMeasurable
    · exact Complex.measurable_ofReal.comp hwmeas
    · refine Measurable.mul ?_ ?_
      · refine Complex.measurable_ofReal.comp ?_
        exact ((connes_cutoffExcess_measurable L).comp
          (measurable_const.add measurable_id)).sub measurable_const
      · exact (η.continuous.comp (continuous_const.add continuous_id)).measurable
  · have hwrw : connesFracWeight α ψ ε = ψ |ε| * (|ε| ^ (1 + α))⁻¹ := by
      have hrw0 := congrFun (connes_absRpow_neg_eq (α := α) (by linarith : (-1 : ℝ) < α)) ε
      rw [connesFracWeight, hrw0]
    have hwnn : 0 ≤ connesFracWeight α ψ ε := by
      rw [hwrw]
      have : (0 : ℝ) ≤ (|ε| ^ (1 + α))⁻¹ := by positivity
      exact mul_nonneg (hψ0 _) this
    have hnormw : ‖(((connesFracWeight α ψ ε : ℝ)) : ℂ)‖ = ψ |ε| * (|ε| ^ (1 + α))⁻¹ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hwnn, hwrw]
    by_cases hεle : |ε| ≤ 1
    · have hdelta : |connesCutoffExcess L (x + ε) - connesCutoffExcess L x|
          ≤ abs (Real.log |x + ε| - Real.log |x|) := connes_cutoffExcess_diff_le L x (x + ε)
      have hη := hMbd ε hεle
      have hinv : (0 : ℝ) ≤ (|ε| ^ (1 + α))⁻¹ := by positivity
      rw [norm_mul, norm_mul, hnormw, Complex.norm_real, Real.norm_eq_abs]
      calc ψ |ε| * (|ε| ^ (1 + α))⁻¹ *
            (|connesCutoffExcess L (x + ε) - connesCutoffExcess L x| * ‖η (x + ε)‖)
          ≤ ψ |ε| * (|ε| ^ (1 + α))⁻¹ *
              (abs (Real.log |x + ε| - Real.log |x|) * M) := by
            refine mul_le_mul_of_nonneg_left
              (mul_le_mul hdelta hη (norm_nonneg _) (abs_nonneg _)) ?_
            exact mul_nonneg (hψ0 _) hinv
        _ = M * (ψ |ε| * G ε) := by rw [hG]; ring
    · have hgt : 1 < |ε| := not_le.mp hεle
      have hw0 : connesFracWeight α ψ ε = 0 := connesFracWeight_eq_zero hψsupp hgt
      have hψ0' : ψ |ε| = 0 := hψsupp |ε| hgt
      rw [hw0, hψ0']
      simp

/-! ## The commutator and the operator identity -/

/-- The commutator `[C_{α,v}, ε_Λ] η`. -/
def connesFracCommutator (α : ℝ) (ψ : ℝ → ℝ) (L : ℝ) (η : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ ε : ℝ, ((connesFracWeight α ψ ε : ℝ) : ℂ) *
    (((connesCutoffExcess L (x + ε) - connesCutoffExcess L x : ℝ) : ℂ) * η (x + ε))

/-- **The operator identity.**  `C_{α,v}*(ε_Λ η) = ε_Λ·(C_{α,v}*η) + [C_{α,v}, ε_Λ]η`. -/
theorem connes_fracConv_cutoff_split {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ψ : ℝ → ℝ} (hψc : Continuous ψ) (hψ0 : ∀ t, 0 ≤ ψ t) (hψ1 : ∀ t, ψ t ≤ 1)
    (hψsupp : ∀ t : ℝ, 1 < t → ψ t = 0) (L : ℝ) (η : 𝓢(ℝ, ℂ)) {x : ℝ} (hx : x ≠ 0) :
    connesFracConv α ψ
        (fun y => (connesCutoffExcess L y : ℂ) * ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) y) x
      = (connesCutoffExcess L x : ℂ) *
          connesFracConv α ψ ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x
        + connesFracCommutator α ψ L ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x := by
  have h1 : Integrable (fun ε : ℝ => ((connesFracWeight α ψ ε : ℝ) : ℂ) *
      (η (x + ε) - η x)) volume :=
    connes_fracConv_integrand_integrable hα0 hα1 hψc hψ0 hψ1 hψsupp η x
  have h1' : Integrable (fun ε : ℝ => (connesCutoffExcess L x : ℂ) *
      (((connesFracWeight α ψ ε : ℝ) : ℂ) * (η (x + ε) - η x))) volume := h1.const_mul _
  have h2 : Integrable (fun ε : ℝ => ((connesFracWeight α ψ ε : ℝ) : ℂ) *
      (((connesCutoffExcess L (x + ε) - connesCutoffExcess L x : ℝ) : ℂ) * η (x + ε))) volume :=
    connes_fracCommutator_integrand_integrable hα0 hα1 hψc hψ0 hψ1 hψsupp L η hx
  simp only [connesFracConv, connesFracCommutator]
  rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_add h1' h2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ε => ?_)
  have hid := connes_commutator_identity L ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x ε
  show ((connesFracWeight α ψ ε : ℝ) : ℂ) *
      ((connesCutoffExcess L (x + ε) : ℂ) * η (x + ε)
        - (connesCutoffExcess L x : ℂ) * η x)
    = (connesCutoffExcess L x : ℂ) * (((connesFracWeight α ψ ε : ℝ) : ℂ) * (η (x + ε) - η x))
      + ((connesFracWeight α ψ ε : ℝ) : ℂ) *
        (((connesCutoffExcess L (x + ε) - connesCutoffExcess L x : ℝ) : ℂ) * η (x + ε))
  push_cast
  ring

/-- **The commutator lives on the thickened tail.** -/
theorem connes_fracCommutator_eq_zero {α : ℝ} {ψ : ℝ → ℝ}
    (hψsupp : ∀ t : ℝ, 1 < t → ψ t = 0) {L : ℝ} (hL : 0 ≤ L) (η : ℝ → ℂ) {x : ℝ}
    (hx : |x| ≤ Real.exp L - 1) :
    connesFracCommutator α ψ L η x = 0 := by
  rw [connesFracCommutator]
  have hpt : ∀ ε : ℝ, ((connesFracWeight α ψ ε : ℝ) : ℂ) *
      (((connesCutoffExcess L (x + ε) - connesCutoffExcess L x : ℝ) : ℂ) * η (x + ε)) = 0 := by
    intro ε
    by_cases hεle : |ε| ≤ 1
    · rw [connes_cutoffExcess_diff_eq_zero hL hx hεle]
      simp
    · rw [connesFracWeight_eq_zero hψsupp (not_le.mp hεle)]
      simp
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  simp

/-- **§VII (46) with the thickened supremum.** -/
theorem connes_fracCommutator_norm_le {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ψ : ℝ → ℝ} (hψc : Continuous ψ) (hψ0 : ∀ t, 0 ≤ ψ t) (hψ1 : ∀ t, ψ t ≤ 1)
    (hψsupp : ∀ t : ℝ, 1 < t → ψ t = 0) (L : ℝ) (η : 𝓢(ℝ, ℂ)) {x : ℝ} (hx : x ≠ 0) :
    ‖connesFracCommutator α ψ L ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖
      ≤ connesUnitSup ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x *
        ((|x| ^ (-α)) * ∫ y : ℝ, connesLogShiftKernel α y) := by
  refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) ?_
  exact connes_cutoff_commutator_local hα0 hα1 hψc hψ0 hψ1 hψsupp L
    ((η : 𝓢(ℝ, ℂ)) : ℝ → ℂ) hx (fun ε hε => le_connesUnitSup η.continuous x hε)

end

end GaloisForLFunctions.RHTower
