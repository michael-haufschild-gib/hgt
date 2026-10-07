import GaloisForLFunctions.RHTower.WeilWorkQuantizationRadialPower

/-!
# Localized phase cancellation for the canonical radial remainder

Capping cumulative phase at a chosen radius separates signed primitive control
from an absolute exponentially damped tail. No global phase-growth bound is used.
-/
open Complex Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RHTower.WeilSpectral
open TruncatedRadial AbelianTwist IntegerMassRigidity FractionalMassRigidity PhaseLockRigidity
  HamburgerStability GaloisForLFunctions.HTGeometry

/-- Bounded monotone phase costs only its total variation. -/
theorem norm_setIntegral_twist_le_bounded {d : ℝ → ℂ} {C : ℝ → ℝ}
    (hC : Monotone C) {B β E δ : ℝ} (hB : ∀ x, C x ≤ B) (hE : 0 ≤ E) (hδ : 0 < δ)
    (hdm : AEStronglyMeasurable d volume) (hdint : IntegrableOn d (Iic (-1)))
    (herr : ∀ b, b ≤ -1 → ‖∫ t in Iic b, d t‖ ≤ E * Real.exp (b * δ)) :
    ‖∫ t in Iic (-1 : ℝ), cexp (((β * C (-t) : ℝ) : ℂ) * I) * d t‖ ≤
      E * (1 + |β| * (B - C 1)) := by
  have hdom : IntegrableOn (fun t => (C (-t) - C 1) * ‖d t‖) (Iic (-1)) := by
    refine (hdint.norm.const_mul (B - C 1)).mono' ?_ ?_
    · exact (((hC.measurable.comp measurable_neg).sub_const _).aestronglyMeasurable.mul
        hdm.norm).restrict
    filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
    have h1 := hC (show 1 ≤ -t by have : t ≤ -1 := ht; linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sub_nonneg.mpr h1) (norm_nonneg _))]
    exact mul_le_mul_of_nonneg_right (sub_le_sub_right (hB _) _) (norm_nonneg _)
  let φ : ℝ → ℝ := (Iic B).indicator (fun _ => 1)
  have hφint : IntegrableOn φ (Ioi (C 1)) := by
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Iic, IntegrableOn,
      Measure.restrict_restrict measurableSet_Iic]
    have heq : Iic B ∩ Ioi (C 1) = Ioc (C 1) B := by ext x; simp; tauto
    rw [heq]
    exact integrableOn_const (by simp [Real.volume_Ioc])
  apply norm_setIntegral_twist_le_of_profile hC hE hδ hdm hdint hdom herr
    (φ := φ) (β₀ := β) (δ := δ) (Iφ := B - C 1) (fun x => by
      by_cases hx : x ≤ B <;> simp [φ, hx])
  · intro x b hb hsup
    by_cases hx : x ≤ B
    · simp only [φ, Set.indicator_of_mem (show x ∈ Iic B from hx)]
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le)
    · have h := hsup (b - 1) (fun t _ ht => False.elim (hx (ht.trans (hB _))))
      linarith
  · exact hφint
  · rw [show φ = (Iic B).indicator (fun _ => (1 : ℝ)) from rfl,
      setIntegral_indicator measurableSet_Iic]
    have heq : Ioi (C 1) ∩ Iic B = Ioc (C 1) B := rfl
    rw [heq, setIntegral_const, Real.volume_real_Ioc, max_eq_left (sub_nonneg.mpr (hB 1))]
    simp

/-- Exponential damping controls the far tail with constants explicit in its scale. -/
theorem integral_norm_tail_le {d : ℝ → ℂ} {D δ U : ℝ} (hD : 0 ≤ D) (hδ : 0 < δ)
    (hU : 1 ≤ U) (hd : IntegrableOn d (Iic (-1)))
    (hb : ∀ t ≤ -1, ‖d t‖ ≤ D * ((1 + |t|) * Real.exp (-(2 * δ * |t|)))) :
    ∫ t in Iic (-U), ‖d t‖ ≤ D * (1 + δ⁻¹) * (Real.exp (-(δ * U)) / δ) := by
  have hs : Iic (-U) ⊆ Iic (-1 : ℝ) := Iic_subset_Iic.mpr (by linarith)
  have hi := (integrableOn_exp_mul_Iic hδ (-U)).const_mul (D * (1 + δ⁻¹))
  calc
    (∫ t in Iic (-U), ‖d t‖) ≤ (∫ t in Iic (-U),
        D * (1 + δ⁻¹) * Real.exp (δ * t)) := by
      apply integral_mono_ae (hd.mono_set hs).norm hi
      filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
      have ht1 : t ≤ -1 := hs ht
      have habs : |t| = -t := abs_of_neg (by linarith)
      have hx : 0 ≤ |t| := abs_nonneg t
      have he := Real.add_one_le_exp (δ * |t|)
      have hlinear : 1 + |t| ≤ (1 + δ⁻¹) * Real.exp (δ * |t|) := by
        have he1 : 1 ≤ Real.exp (δ * |t|) := Real.one_le_exp_iff.mpr (mul_nonneg hδ.le hx)
        have he2 : |t| ≤ δ⁻¹ * Real.exp (δ * |t|) := by
          apply (mul_le_mul_iff_right₀ hδ).mp
          simpa [mul_assoc, mul_left_comm, mul_comm, hδ.ne'] using (le_of_lt (lt_of_lt_of_le (by linarith : δ * |t| < δ * |t| + 1) he))
        nlinarith
      calc ‖d t‖ ≤ D * ((1 + |t|) * Real.exp (-(2 * δ * |t|))) := hb t ht1
        _ ≤ D * (((1 + δ⁻¹) * Real.exp (δ * |t|)) * Real.exp (-(2 * δ * |t|))) := by gcongr
        _ = D * (1 + δ⁻¹) * Real.exp (δ * t) := by
          rw [mul_assoc, ← Real.exp_add, habs]
          rw [show δ * -t + -(2 * δ * -t) = δ * t by ring]
          ring
    _ = _ := by rw [integral_const_mul, integral_exp_mul_Iic hδ]; simp only [mul_neg]

/-- Capping a monotone phase changes its integral only beyond the cap radius. -/
theorem norm_twist_sub_cap_le {d : ℝ → ℂ} {C : ℝ → ℝ} (hC : Monotone C)
    {U : ℝ} (hU : 1 ≤ U) (β : ℝ) (hd : IntegrableOn d (Iic (-1))) :
    ‖(∫ t in Iic (-1 : ℝ), cexp (((β * C (-t) : ℝ) : ℂ) * I) * d t) -
      ∫ t in Iic (-1 : ℝ), cexp (((β * min (C (-t)) (C U) : ℝ) : ℂ) * I) * d t‖ ≤
      2 * ∫ t in Iic (-U), ‖d t‖ := by
  have hcap : Measurable (fun x => min (C x) (C U)) := hC.measurable.min measurable_const
  have hi1 := integrableOn_phase_mul β hC.measurable hd
  have hi2 := integrableOn_phase_mul β hcap hd
  have hs : Iic (-U) ⊆ Iic (-1 : ℝ) := Iic_subset_Iic.mpr (by linarith)
  rw [← integral_sub hi1 hi2]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Iic hs (by
    intro t ht
    have htU : -t ≤ U := by have : ¬t ≤ -U := ht.2; linarith
    rw [min_eq_left (hC htU), sub_self])]
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_const_mul]
  apply integral_mono_ae ((hi1.sub hi2).mono_set hs).norm ((hd.mono_set hs).norm.const_mul 2)
  filter_upwards with t
  calc ‖cexp (((β * C (-t) : ℝ) : ℂ) * I) * d t -
      cexp (((β * min (C (-t)) (C U) : ℝ) : ℂ) * I) * d t‖
      ≤ ‖cexp (((β * C (-t) : ℝ) : ℂ) * I) * d t‖ +
        ‖cexp (((β * min (C (-t)) (C U) : ℝ) : ℂ) * I) * d t‖ := norm_sub_le _ _
    _ = 2 * ‖d t‖ := by simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]; ring

/-- Signed primitive and absolute tail bounds localize the entire phase cost. -/
theorem norm_twist_le_localized {d : ℝ → ℂ} {C : ℝ → ℝ} (hC : Monotone C)
    {U β E D δ : ℝ} (hU : 1 ≤ U) (hE : 0 ≤ E) (hD : 0 ≤ D) (hδ : 0 < δ)
    (hdm : AEStronglyMeasurable d volume) (hd : IntegrableOn d (Iic (-1)))
    (herr : ∀ b, b ≤ -1 → ‖∫ t in Iic b, d t‖ ≤ E * Real.exp (b * δ))
    (hb : ∀ t ≤ -1, ‖d t‖ ≤ D * ((1 + |t|) * Real.exp (-(2 * δ * |t|)))) :
    ‖∫ t in Iic (-1 : ℝ), cexp (((β * C (-t) : ℝ) : ℂ) * I) * d t‖ ≤
      E * (1 + |β| * (C U - C 1)) +
        2 * (D * (1 + δ⁻¹) * (Real.exp (-(δ * U)) / δ)) := by
  have hcap := norm_setIntegral_twist_le_bounded (hC.min monotone_const)
    (B := C U) (fun x => min_le_right _ _) hE hδ hdm hd herr (β := β)
  rw [min_eq_left (hC hU)] at hcap
  have hdiff := norm_twist_sub_cap_le hC hU β hd
  have htail := integral_norm_tail_le hD hδ hU hd hb
  have htri := norm_add_le
    ((∫ t in Iic (-1 : ℝ), cexp (((β * C (-t) : ℝ) : ℂ) * I) * d t) -
      ∫ t in Iic (-1 : ℝ), cexp (((β * min (C (-t)) (C U) : ℝ) : ℂ) * I) * d t)
    (∫ t in Iic (-1 : ℝ), cexp (((β * min (C (-t)) (C U) : ℝ) : ℂ) * I) * d t)
  rw [sub_add_cancel] at htri
  linarith

/-- The actual source remainder admits localization at any spectral radius. -/
theorem exists_quantization_twist_local_bound {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {C : ℝ → ℝ} (hC : Monotone C) (β : ℝ) {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    {m : ℕ} (hm : 1 ≤ m) :
    ∃ A D : ℝ, 0 ≤ A ∧ 0 ≤ D ∧ ∀ ε U : ℝ, 0 < ε → ε ≤ 1 → 1 ≤ U →
      ‖(ε : ℂ) * ∫ t in Iic (-1 : ℝ), cexp (((β * C (-t) : ℝ) : ℂ) * I) *
        quantizationRadialRemainder hW m ((ε : ℂ) + (m : ℂ) * I) t‖ ≤
      A * ε ^ (1 - p) * (1 + |β| * (C U - C 1)) +
        D * ε⁻¹ * Real.exp (-(ε * U / ((m : ℝ) + 1))) := by
  obtain ⟨Kr, hKr⟩ := exists_norm_quantization_radialError_le hW hp hp1 hm
  obtain ⟨CB, hCB, hpoly⟩ := exists_quantization_trace_pair_bound hW
  let M : ℝ := m + 1
  have hM : 1 ≤ M := by dsimp [M]; linarith [Nat.cast_nonneg (α := ℝ) m]
  let D₀ : ℝ := 3 * CB + ‖dirichletExp (lamLog lam) m‖ * (4 * Real.pi ^ (3 / 4 : ℝ) * M)
  have hD₀ : 0 ≤ D₀ := by dsimp [D₀]; positivity
  refine ⟨|Kr|, 4 * D₀ * M ^ 2, abs_nonneg _, by positivity, ?_⟩
  intro ε U hε hε1 hU
  let τ : ℂ := (ε : ℂ) + (m : ℂ) * I
  have hτre : τ.re = ε := by simp [τ]
  have hτre0 : 0 < τ.re := by rw [hτre]; exact hε
  have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτre0; simp at hτre0
  have hτ1 : 1 ≤ ‖τ‖ := by
    have h := Complex.abs_im_le_norm τ
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have him : τ.im = (m : ℝ) := by simp [τ]
    rw [him, abs_of_nonneg (Nat.cast_nonneg m)] at h
    exact hm1.trans h
  have hτM : ‖τ‖ ≤ M := by
    have h := norm_add_le (ε : ℂ) ((m : ℂ) * I)
    rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_natCast,
      Real.norm_eq_abs, abs_of_pos hε] at h
    dsimp [τ, M]; linarith
  let δ : ℝ := ε / ‖τ‖
  have hδ : 0 < δ := div_pos hε (by linarith)
  have hδ1 : δ ≤ 1 := (div_le_self hε.le hτ1).trans hε1
  let d : ℝ → ℂ := fun t => (ε : ℂ) * quantizationRadialRemainder hW m τ t
  have hdm : Measurable d := (measurable_quantizationRadialRemainder hW hm hτ0).const_mul _
  have hdi := (integrableOn_quantizationRadialRemainder hW hm hτre0 hτ1).const_mul (ε : ℂ)
  have herr : ∀ b, b ≤ -1 → ‖∫ t in Iic b, d t‖ ≤ (|Kr| * ε ^ (1 - p)) * Real.exp (b * δ) := by
    intro b hb
    have hphik : Integrable (fun t : ℝ => quantizationTraceF hW (2 * t) * pairKernel (2 * t) τ) :=
      integrable_defectLaplace_integrand
        ((measurable_quantizationTraceF hW).comp (measurable_const.mul measurable_id)).aestronglyMeasurable
        (fun t => (hpoly t).1) hτre0
    have hrho := (integrableOn_rhoMain hm hτre0 hτ1).mono_set (Iic_subset_Iic.mpr hb)
    simp only [d, quantizationRadialRemainder]
    rw [integral_const_mul, integral_sub hphik.integrableOn (hrho.const_mul _), integral_const_mul]
    exact (hKr ε hε hε1 b hb).trans (by gcongr; exact le_abs_self _)
  have hb : ∀ t ≤ -1, ‖d t‖ ≤ (ε * D₀) * ((1 + |t|) * Real.exp (-(2 * δ * |t|))) := by
    intro t ht
    have h := norm_quantizationRadialRemainder_le hW hCB (fun t => (hpoly t).1) hm hτre0 hτ1 ht
    rw [pow_one, hτre] at h
    simp only [d, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
    calc ε * ‖quantizationRadialRemainder hW m τ t‖ ≤ ε *
        ((3 * CB + ‖dirichletExp (lamLog lam) m‖ * (4 * Real.pi ^ (3 / 4 : ℝ) * ‖τ‖)) *
          ((1 + |t|) * Real.exp (-(2 * δ * |t|)))) := mul_le_mul_of_nonneg_left h hε.le
      _ ≤ _ := by rw [← mul_assoc]; dsimp [D₀]; gcongr
  have hloc := norm_twist_le_localized hC hU (by positivity : 0 ≤ |Kr| * ε ^ (1 - p))
    (mul_nonneg hε.le hD₀) hδ hdm.aestronglyMeasurable hdi herr hb (β := β)
  have hid : (ε : ℂ) * ∫ t in Iic (-1 : ℝ), cexp (((β * C (-t) : ℝ) : ℂ) * I) *
      quantizationRadialRemainder hW m τ t =
      ∫ t in Iic (-1 : ℝ), cexp (((β * C (-t) : ℝ) : ℂ) * I) * d t := by
    rw [← integral_const_mul]; congr 1; funext t; dsimp [d]; ring
  rw [hid]
  refine hloc.trans (add_le_add_right ?_ _)
  have hδinv : δ⁻¹ ≤ M * ε⁻¹ := by
    dsimp [δ]; rw [inv_div, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hτM (inv_nonneg.mpr hε.le)
  have hinv : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ).mpr hδ1
  have hδlow : ε / M ≤ δ := by dsimp [δ]; exact div_le_div_of_nonneg_left hε.le (by linarith) hτM
  have he : Real.exp (-(δ * U)) ≤ Real.exp (-(ε * U / M)) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right hδlow (by linarith : 0 ≤ U)
    rw [div_mul_eq_mul_div] at h
    linarith
  calc 2 * (ε * D₀ * (1 + δ⁻¹) * (Real.exp (-(δ * U)) / δ))
      ≤ 2 * (ε * D₀ * (2 * (M * ε⁻¹)) * (Real.exp (-(ε * U / M)) * (M * ε⁻¹))) := by
        rw [div_eq_mul_inv]
        gcongr
        linarith
    _ = (4 * D₀ * M ^ 2) * ε⁻¹ * Real.exp (-(ε * U / M)) := by field_simp; ring


end RHTower.WeilSpectral
