import GaloisForLFunctions.RHTower.WeilWorkQuantizationPhaseVariation
import GaloisForLFunctions.RHTower.WeilWorkQuantizationLocalPhase

/-!
# Local cancellation controlled by actual phase variation

A general Lipschitz profile on a monotone clock costs only its local variation.
Capping the clock leaves an absolute exponentially damped tail. Applying this
to the canonical circle phase retains the actual source remainder and residues.
-/

open Complex Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RHTower.WeilSpectral
open TruncatedRadial AbelianTwist IntegerMassRigidity FractionalMassRigidity PhaseLockRigidity
  HamburgerStability GaloisForLFunctions.HTGeometry

theorem integrableOn_clockProfile_mul {a b V : ℝ → ℝ}
    (ha : LipschitzWith 1 a) (hb : LipschitzWith 1 b) (hV : Measurable V)
    (hunit : ∀ x, ‖quantizationClockProfile a b (V x)‖ = 1)
    {d : ℝ → ℂ} {s : Set ℝ} (hd : IntegrableOn d s) :
    IntegrableOn (fun t => quantizationClockProfile a b (V (-t)) * d t) s := by
  apply hd.norm.mono'
  · exact (((continuous_quantizationClockProfile ha hb).measurable.comp
      (hV.comp measurable_neg)).aestronglyMeasurable.mul hd.aestronglyMeasurable)
  · filter_upwards with t
    simp only [norm_mul, hunit, one_mul, le_refl]

theorem norm_setIntegral_clockProfile_le_bounded {a b V : ℝ → ℝ}
    (hV : Monotone V) (ha : LipschitzWith 1 a) (hb : LipschitzWith 1 b)
    (hunit : ∀ x, ‖quantizationClockProfile a b (V x)‖ = 1)
    {d : ℝ → ℂ} {B E δ : ℝ} (hB : ∀ x, V x ≤ B) (hE : 0 ≤ E) (hδ : 0 < δ)
    (hdm : AEStronglyMeasurable d volume) (hdint : IntegrableOn d (Iic (-1)))
    (herr : ∀ c, c ≤ -1 → ‖∫ t in Iic c, d t‖ ≤ E * Real.exp (c * δ)) :
    ‖∫ t in Iic (-1 : ℝ), quantizationClockProfile a b (V (-t)) * d t‖ ≤
      E * (1 + 2 * (B - V 1)) := by
  have hdom : IntegrableOn (fun t => (V (-t) - V 1) * ‖d t‖) (Iic (-1)) := by
    refine (hdint.norm.const_mul (B - V 1)).mono' ?_ ?_
    · exact (((hV.measurable.comp measurable_neg).sub_const _).aestronglyMeasurable.mul
        hdm.norm).restrict
    filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
    have h1 := hV (show 1 ≤ -t by have : t ≤ -1 := ht; linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sub_nonneg.mpr h1) (norm_nonneg _))]
    exact mul_le_mul_of_nonneg_right (sub_le_sub_right (hB _) _) (norm_nonneg _)
  let φ : ℝ → ℝ := (Iic B).indicator (fun _ => 1)
  have hφint : IntegrableOn φ (Ioi (V 1)) := by
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Iic, IntegrableOn,
      Measure.restrict_restrict measurableSet_Iic]
    have heq : Iic B ∩ Ioi (V 1) = Ioc (V 1) B := by ext x; simp; tauto
    rw [heq]
    exact integrableOn_const (by simp [Real.volume_Ioc])
  suffices h : ‖∫ t in Iic (-1 : ℝ), quantizationClockProfile a b (V (-t)) * d t‖ ≤
      E * (‖quantizationClockProfile a b (V 1)‖ + 2 * (B - V 1)) by
    simpa only [hunit] using h
  apply norm_setIntegral_layer_le_of_profile hV (Ψ := quantizationClockProfile a b)
    (ψ := quantizationClockDensity a b) (by norm_num : (0:ℝ) ≤ 2)
    (measurable_quantizationClockDensity a b) (norm_quantizationClockDensity_le ha hb)
    (fun u v huv => quantizationClockProfile_eq_add_integral ha hb huv)
    hE hδ hdm hdint hdom herr (φ := φ) (Iφ := B - V 1)
  · intro x
    by_cases hx : x ≤ B <;> simp [φ, hx]
  · intro x c hc hsup
    by_cases hx : x ≤ B
    · simp only [φ, Set.indicator_of_mem (show x ∈ Iic B from hx)]
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le)
    · have h := hsup (c - 1) (fun t _ ht => False.elim (hx (ht.trans (hB _))))
      linarith
  · exact hφint
  · rw [show φ = (Iic B).indicator (fun _ => (1 : ℝ)) from rfl,
      setIntegral_indicator measurableSet_Iic]
    have heq : Ioi (V 1) ∩ Iic B = Ioc (V 1) B := rfl
    rw [heq, setIntegral_const, Real.volume_real_Ioc, max_eq_left (sub_nonneg.mpr (hB 1))]
    simp

theorem norm_clockProfile_sub_cap_le {a b V : ℝ → ℝ}
    (hV : Monotone V) (ha : LipschitzWith 1 a) (hb : LipschitzWith 1 b)
    (hunit : ∀ x, ‖quantizationClockProfile a b (V x)‖ = 1)
    {d : ℝ → ℂ} {U : ℝ} (hU : 1 ≤ U) (hd : IntegrableOn d (Iic (-1))) :
    ‖(∫ t in Iic (-1 : ℝ), quantizationClockProfile a b (V (-t)) * d t) -
      ∫ t in Iic (-1 : ℝ), quantizationClockProfile a b (min (V (-t)) (V U)) * d t‖ ≤
      2 * ∫ t in Iic (-U), ‖d t‖ := by
  have hcap : Measurable (fun x => min (V x) (V U)) := hV.measurable.min measurable_const
  have hunitcap : ∀ x, ‖quantizationClockProfile a b (min (V x) (V U))‖ = 1 := by
    intro x
    rcases le_total (V x) (V U) with h | h
    · rw [min_eq_left h, hunit]
    · rw [min_eq_right h, hunit]
  have hi1 := integrableOn_clockProfile_mul ha hb hV.measurable hunit hd
  have hi2 := integrableOn_clockProfile_mul ha hb hcap hunitcap hd
  have hs : Iic (-U) ⊆ Iic (-1 : ℝ) := Iic_subset_Iic.mpr (by linarith)
  rw [← integral_sub hi1 hi2]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Iic hs (by
    intro t ht
    have htU : -t ≤ U := by have : ¬t ≤ -U := ht.2; linarith
    rw [min_eq_left (hV htU), sub_self])]
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_const_mul]
  apply integral_mono_ae ((hi1.sub hi2).mono_set hs).norm ((hd.mono_set hs).norm.const_mul 2)
  filter_upwards with t
  calc ‖quantizationClockProfile a b (V (-t)) * d t -
      quantizationClockProfile a b (min (V (-t)) (V U)) * d t‖
      ≤ ‖quantizationClockProfile a b (V (-t)) * d t‖ +
        ‖quantizationClockProfile a b (min (V (-t)) (V U)) * d t‖ := norm_sub_le _ _
    _ = 2 * ‖d t‖ := by simp only [norm_mul, hunit, hunitcap, one_mul]; ring

theorem norm_clockProfile_le_localized {a b V : ℝ → ℝ}
    (hV : Monotone V) (ha : LipschitzWith 1 a) (hb : LipschitzWith 1 b)
    (hunit : ∀ x, ‖quantizationClockProfile a b (V x)‖ = 1)
    {d : ℝ → ℂ} {U E D δ : ℝ} (hU : 1 ≤ U) (hE : 0 ≤ E) (hD : 0 ≤ D) (hδ : 0 < δ)
    (hdm : AEStronglyMeasurable d volume) (hd : IntegrableOn d (Iic (-1)))
    (herr : ∀ c, c ≤ -1 → ‖∫ t in Iic c, d t‖ ≤ E * Real.exp (c * δ))
    (hdamp : ∀ t ≤ -1, ‖d t‖ ≤ D * ((1 + |t|) * Real.exp (-(2 * δ * |t|)))) :
    ‖∫ t in Iic (-1 : ℝ), quantizationClockProfile a b (V (-t)) * d t‖ ≤
      E * (1 + 2 * (V U - V 1)) +
        2 * (D * (1 + δ⁻¹) * (Real.exp (-(δ * U)) / δ)) := by
  have hunitcap : ∀ x, ‖quantizationClockProfile a b (min (V x) (V U))‖ = 1 := by
    intro x
    rcases le_total (V x) (V U) with h | h
    · rw [min_eq_left h, hunit]
    · rw [min_eq_right h, hunit]
  have hcap := norm_setIntegral_clockProfile_le_bounded (hV.min monotone_const) ha hb hunitcap
    (B := V U) (fun x => min_le_right _ _) hE hδ hdm hd herr
  rw [min_eq_left (hV hU)] at hcap
  have hdiff := norm_clockProfile_sub_cap_le hV ha hb hunit hU hd
  have htail := integral_norm_tail_le hD hδ hU hd hdamp
  have htri := norm_add_le
    ((∫ t in Iic (-1 : ℝ), quantizationClockProfile a b (V (-t)) * d t) -
      ∫ t in Iic (-1 : ℝ), quantizationClockProfile a b (min (V (-t)) (V U)) * d t)
    (∫ t in Iic (-1 : ℝ), quantizationClockProfile a b (min (V (-t)) (V U)) * d t)
  rw [sub_add_cancel] at htri
  linarith

theorem exists_quantization_profile_local_bound {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {V a b : ℝ → ℝ} (hV : Monotone V) (haL : LipschitzWith 1 a) (hbL : LipschitzWith 1 b)
    (hunit : ∀ x, ‖quantizationClockProfile a b (V x)‖ = 1) {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    {m : ℕ} (hm : 1 ≤ m) :
    ∃ A D : ℝ, 0 ≤ A ∧ 0 ≤ D ∧ ∀ ε U : ℝ, 0 < ε → ε ≤ 1 → 1 ≤ U →
      ‖(ε : ℂ) * ∫ t in Iic (-1 : ℝ), quantizationClockProfile a b (V (-t)) *
        quantizationRadialRemainder hW m ((ε : ℂ) + (m : ℂ) * I) t‖ ≤
      A * ε ^ (1 - p) * (1 + 2 * (V U - V 1)) +
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
  have hloc := norm_clockProfile_le_localized hV haL hbL hunit hU (by positivity : 0 ≤ |Kr| * ε ^ (1 - p))
    (mul_nonneg hε.le hD₀) hδ hdm.aestronglyMeasurable hdi herr hb
  have hid : (ε : ℂ) * ∫ t in Iic (-1 : ℝ), quantizationClockProfile a b (V (-t)) *
      quantizationRadialRemainder hW m τ t =
      ∫ t in Iic (-1 : ℝ), quantizationClockProfile a b (V (-t)) * d t := by
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

/-- The cost is the observed circle-path variation, not a chosen phase lift. -/
theorem exists_quantization_variation_local_bound {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {m : ℕ} (hm : 1 ≤ m) :
    ∃ A D : ℝ, 0 ≤ A ∧ 0 ≤ D ∧ ∀ ε U : ℝ, 0 < ε → ε ≤ 1 → 1 ≤ U →
      ‖(ε : ℂ) * ∫ t in Iic (-1 : ℝ), quantizationCirclePhase hW (-t) *
        quantizationRadialRemainder hW m ((ε : ℂ) + (m : ℂ) * I) t‖ ≤
      A * ε ^ (1 - p) * (1 + 2 * (quantizationPhaseVariation hW U - quantizationPhaseVariation hW 1)) +
        D * ε⁻¹ * Real.exp (-(ε * U / ((m : ℝ) + 1))) := by
  obtain ⟨a,b,ha,hb,heq⟩ := exists_quantization_phase_profiles hW
  have heq' : ∀ x, quantizationClockProfile a b (quantizationPhaseVariation hW x) =
      quantizationCirclePhase hW x := heq
  have hunit : ∀ x, ‖quantizationClockProfile a b (quantizationPhaseVariation hW x)‖ = 1 := by
    intro x
    rw [heq', norm_quantizationCirclePhase]
  obtain ⟨A,D,hA,hD,hbd⟩ := exists_quantization_profile_local_bound hW
    (monotone_quantizationPhaseVariation hW) ha hb hunit hp hp1 hm
  refine ⟨A,D,hA,hD,fun ε U hε hε1 hU => ?_⟩
  simpa only [heq'] using hbd ε U hε hε1 hU

end RHTower.WeilSpectral
