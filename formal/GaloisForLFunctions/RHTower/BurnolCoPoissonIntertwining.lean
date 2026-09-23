import GaloisForLFunctions.RHTower.BurnolCoPoissonPairing
import GaloisForLFunctions.HTGeometry.TsumMeasurable

/-!
# Towards Burnol's co-Poisson intertwining

The cosine transform of the co-Poisson sum of a seed is the co-Poisson sum of the reciprocal seed.
In the test-function picture the identity reads

`integral_0^infinity P_g(t) w(t) dt = integral_0^infinity P_G(t) (F w)(t) dt`

for every even Schwartz `w`, with `G` the reciprocal seed.  The proof runs through the pairing
identity, Poisson summation at the scale of the seed variable, and the inversion of the positive
ray, which is what exchanges the seed with its reciprocal seed.

This file collects the elementary ingredients: the even splitting of an integral over the line, the
total mass as the value of the transform at the origin, Fourier inversion at the origin, and the
inversion of the ray inside a dilated pairing.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped FourierTransform

noncomputable section

namespace RHTower

/-- An even integrable function integrates to twice its half-line integral. -/
theorem integral_eq_two_mul_integral_Ioi_of_even {w : ℝ → ℂ} (hw : Integrable w)
    (he : ∀ x : ℝ, w (-x) = w x) :
    (∫ x : ℝ, w x) = 2 * ∫ x in Ioi (0 : ℝ), w x := by
  have h1 : (∫ x in Ioi (0 : ℝ), w (-x)) = ∫ x in Iic (0 : ℝ), w x := by
    have h := integral_comp_neg_Ioi (0 : ℝ) w
    rwa [neg_zero] at h
  have h2 : (∫ x in Ioi (0 : ℝ), w (-x)) = ∫ x in Ioi (0 : ℝ), w x :=
    setIntegral_congr_fun measurableSet_Ioi fun x _ => he x
  have h3 := intervalIntegral.integral_Iic_add_Ioi (μ := volume) (f := w) (b := 0)
    hw.integrableOn hw.integrableOn
  rw [← h3, ← h1, h2]
  ring

/-- The total mass of a function is the value of its Fourier transform at the origin. -/
theorem integral_eq_fourier_zero (w : ℝ → ℂ) : (∫ x : ℝ, w x) = 𝓕 w 0 := by
  rw [Real.fourier_eq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  dsimp only
  have hz : (inner ℝ v (0 : ℝ) : ℝ) = 0 := by simp
  rw [hz, neg_zero]
  simp

/-- **Inversion of the ray in a dilated pairing.**  Inverting the positive ray exchanges a seed
with its reciprocal seed and turns a contraction of the argument into a dilation. -/
theorem integral_seed_inv_mul_dilate (g h : ℝ → ℂ) (m : ℝ) :
    (∫ u in Ioi (0 : ℝ), ((u : ℝ) : ℂ)⁻¹ * g u * h (m / u)) =
      ∫ v in Ioi (0 : ℝ), coPoissonReciprocalSeed g v * h (m * v) := by
  rw [integral_Ioi_comp_inv (fun u : ℝ => ((u : ℝ) : ℂ)⁻¹ * g u * h (m / u))]
  refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
  have hvpos : (0 : ℝ) < v := mem_Ioi.mp hv
  have hvne : ((v : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hvpos)
  have harg : m / v⁻¹ = m * v := by
    rw [div_eq_mul_inv, inv_inv]
  rw [harg, coPoissonReciprocalSeed, Complex.ofReal_inv, inv_inv, Complex.real_smul,
    Complex.ofReal_inv, Complex.ofReal_pow]
  rw [sq, mul_inv, ← mul_assoc, ← mul_assoc]
  congr 2
  rw [mul_assoc, inv_mul_cancel₀ hvne, mul_one]



/-! ## The contracted sum against the seed -/

/-- Norm form of the ray inversion. -/
theorem integral_norm_seed_inv_mul_dilate (g h : ℝ → ℂ) (m : ℝ) :
    (∫ u in Ioi (0 : ℝ), ‖((u : ℝ) : ℂ)⁻¹ * g u * h (m / u)‖) =
      ∫ v in Ioi (0 : ℝ), ‖coPoissonReciprocalSeed g v * h (m * v)‖ := by
  rw [integral_Ioi_comp_inv (fun u : ℝ => ‖((u : ℝ) : ℂ)⁻¹ * g u * h (m / u)‖)]
  refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
  have hvpos : (0 : ℝ) < v := mem_Ioi.mp hv
  have harg : m / v⁻¹ = m * v := by
    rw [div_eq_mul_inv, inv_inv]
  have hnorm1 : ‖(((v⁻¹ : ℝ)) : ℂ)⁻¹‖ = v := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hvpos), inv_inv]
  have hnorm2 : ‖(((v : ℝ)) : ℂ)⁻¹‖ = v⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hvpos]
  rw [harg, coPoissonReciprocalSeed]
  simp only [norm_mul, smul_eq_mul]
  rw [hnorm1, hnorm2]
  have hvne : v ≠ 0 := ne_of_gt hvpos
  field_simp

/-- Integrability of one contracted term against a window seed. -/
theorem integrableOn_seed_inv_mul_dilate {b : ℝ} (hb : 0 < b) {g : ℝ → ℂ}
    (hg : Integrable g) (hsupp : Function.support g ⊆ Icc b b⁻¹) (h : SchwartzMap ℝ ℂ) (m : ℝ) :
    IntegrableOn (fun u : ℝ => ((u : ℝ) : ℂ)⁻¹ * g u * h (m / u)) (Ioi 0) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_bound_schwartz h
  refine Integrable.mono' (g := fun u : ℝ => C / b * ‖g u‖)
    (((hg.norm).restrict (s := Ioi 0)).const_mul _) ?_ ?_
  · refine AEStronglyMeasurable.mul ?_
      ((h.continuous.measurable.comp (measurable_const.div measurable_id)).aestronglyMeasurable)
    exact (Complex.measurable_ofReal.comp measurable_id).inv.aestronglyMeasurable.mul
      (hg.aestronglyMeasurable.restrict)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hupos : (0 : ℝ) < u := mem_Ioi.mp hu
    by_cases hz : g u = 0
    · simp [hz]
    · have hmem : u ∈ Icc b b⁻¹ := hsupp (Function.mem_support.mpr hz)
      have hub : b ≤ u := hmem.1
      have hinv : u⁻¹ ≤ b⁻¹ := by
        rw [inv_le_inv₀ hupos hb]
        exact hub
      rw [norm_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hupos]
      have h1 : u⁻¹ * ‖g u‖ * ‖h (m / u)‖ ≤ b⁻¹ * ‖g u‖ * C := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right hinv (norm_nonneg _)) (hC _)
          (norm_nonneg _) (by positivity)
      refine h1.trans_eq ?_
      rw [div_eq_mul_inv, inv_eq_one_div, one_div]
      ring

/-- Summability of the contracted pairings. -/
theorem summable_integral_norm_seed_inv_mul_dilate {b : ℝ} (hb : 0 < b) {g : ℝ → ℂ}
    (hG : Integrable (coPoissonReciprocalSeed g))
    (hGsupp : Function.support (coPoissonReciprocalSeed g) ⊆ Icc b b⁻¹) (h : SchwartzMap ℝ ℂ) :
    Summable fun m : ℕ =>
      ∫ u in Ioi (0 : ℝ), ‖((u : ℝ) : ℂ)⁻¹ * g u * h (((m + 1 : ℕ) : ℝ) / u)‖ := by
  refine (summable_integral_norm_seed_mul_schwartzDilate hb hG hGsupp h).congr fun m => ?_
  exact (integral_norm_seed_inv_mul_dilate g h ((m + 1 : ℕ) : ℝ)).symm

theorem hasSum_integral_seed_inv_mul_dilate {b : ℝ} (hb : 0 < b) {g : ℝ → ℂ}
    (hg : Integrable g) (hsupp : Function.support g ⊆ Icc b b⁻¹)
    (hG : Integrable (coPoissonReciprocalSeed g))
    (hGsupp : Function.support (coPoissonReciprocalSeed g) ⊆ Icc b b⁻¹) (h : SchwartzMap ℝ ℂ) :
    HasSum (fun m : ℕ =>
        ∫ u in Ioi (0 : ℝ), ((u : ℝ) : ℂ)⁻¹ * g u * h (((m + 1 : ℕ) : ℝ) / u))
      (∫ u in Ioi (0 : ℝ),
        ∑' m : ℕ, ((u : ℝ) : ℂ)⁻¹ * g u * h (((m + 1 : ℕ) : ℝ) / u)) :=
  hasSum_integral_of_summable_integral_norm
    (fun _ => integrableOn_seed_inv_mul_dilate hb hg hsupp h _)
    (summable_integral_norm_seed_inv_mul_dilate hb hG hGsupp h)

/-- **The contracted sum against the seed is the dilated sum against the reciprocal seed.**  This
is the inversion of the positive ray, applied one term at a time and then resummed. -/
theorem integral_tsum_seed_inv_dilate_eq {b : ℝ} (hb : 0 < b) {g : ℝ → ℂ}
    (hg : Integrable g) (hsupp : Function.support g ⊆ Icc b b⁻¹)
    (hG : Integrable (coPoissonReciprocalSeed g))
    (hGsupp : Function.support (coPoissonReciprocalSeed g) ⊆ Icc b b⁻¹) (h : SchwartzMap ℝ ℂ) :
    (∫ u in Ioi (0 : ℝ), ∑' m : ℕ, ((u : ℝ) : ℂ)⁻¹ * g u * h (((m + 1 : ℕ) : ℝ) / u)) =
      ∫ v in Ioi (0 : ℝ),
        coPoissonReciprocalSeed g v * ∑' m : ℕ, h (((m + 1 : ℕ) : ℝ) * v) := by
  have hright : (∫ v in Ioi (0 : ℝ),
      ∑' m : ℕ, coPoissonReciprocalSeed g v * h (((m + 1 : ℕ) : ℝ) * v)) =
      ∫ v in Ioi (0 : ℝ),
        coPoissonReciprocalSeed g v * ∑' m : ℕ, h (((m + 1 : ℕ) : ℝ) * v) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
    exact tsum_mul_left
  rw [← hright]
  have hfun : (fun m : ℕ =>
      ∫ v in Ioi (0 : ℝ), coPoissonReciprocalSeed g v * h (((m + 1 : ℕ) : ℝ) * v)) =
      fun m : ℕ =>
        ∫ u in Ioi (0 : ℝ), ((u : ℝ) : ℂ)⁻¹ * g u * h (((m + 1 : ℕ) : ℝ) / u) := by
    funext m
    exact (integral_seed_inv_mul_dilate g h ((m + 1 : ℕ) : ℝ)).symm
  have hsum2 := hasSum_integral_seed_mul_schwartzDilate hb hG hGsupp h
  rw [hfun] at hsum2
  exact (HasSum.unique (hasSum_integral_seed_inv_mul_dilate hb hg hsupp hG hGsupp h) hsum2)



/-! ## Integrability of the three pieces -/

/-- A window seed times a function bounded on the window is integrable on the ray. -/
theorem integrableOn_seed_mul_of_bdd_on_window {b : ℝ} {g : ℝ → ℂ}
    (hg : Integrable g) (hsupp : Function.support g ⊆ Icc b b⁻¹)
    {F : ℝ → ℂ} (hF : AEStronglyMeasurable F (volume.restrict (Ioi 0)))
    {M : ℝ} (hM : ∀ u : ℝ, u ∈ Icc b b⁻¹ → ‖F u‖ ≤ M) :
    IntegrableOn (fun u : ℝ => g u * F u) (Ioi 0) := by
  refine Integrable.mono' (g := fun u : ℝ => M * ‖g u‖)
    (((hg.norm).restrict (s := Ioi 0)).const_mul _)
    (hg.aestronglyMeasurable.restrict.mul hF) ?_
  filter_upwards with u
  by_cases hz : g u = 0
  · simp [hz]
  · have hmem := hsupp (Function.mem_support.mpr hz)
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hM u hmem) (norm_nonneg _)

theorem integrableOn_seed_div {b : ℝ} (hb : 0 < b) {g : ℝ → ℂ}
    (hg : Integrable g) (hsupp : Function.support g ⊆ Icc b b⁻¹) :
    IntegrableOn (fun u : ℝ => ((u : ℝ) : ℂ)⁻¹ * g u) (Ioi 0) := by
  refine (Integrable.congr ?_ (Filter.Eventually.of_forall fun u => mul_comm (g u) _))
  refine integrableOn_seed_mul_of_bdd_on_window hg hsupp
    (Complex.measurable_ofReal.inv.aestronglyMeasurable) (M := b⁻¹) ?_
  intro u hu
  have hupos : (0 : ℝ) < u := lt_of_lt_of_le hb hu.1
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hupos, inv_le_inv₀ hupos hb]
  exact hu.1

/-- Summability of the dilated Schwartz values in the form used here. -/
theorem summable_norm_schwartzDilate' (w : SchwartzMap ℝ ℂ) {u : ℝ} (hu : 0 < u) :
    Summable fun k : ℕ => ‖w (((k + 1 : ℕ) : ℝ) * u)‖ := by
  refine (HTGeometry.summable_norm_schwartzDilate w hu).congr fun k => ?_
  rw [mul_comm]
  norm_num

theorem tsum_norm_schwartzDilate_le' {w : SchwartzMap ℝ ℂ} {C : ℝ}
    (hC : ∀ v : ℝ, 0 < v → ∑' n : ℕ, ‖w (v * ((n : ℝ) + 1))‖ ≤ C / v ^ (2 : ℕ))
    {u : ℝ} (hu : 0 < u) :
    ∑' k : ℕ, ‖w (((k + 1 : ℕ) : ℝ) * u)‖ ≤ C / u ^ (2 : ℕ) := by
  refine le_trans (le_of_eq ?_) (hC u hu)
  refine tsum_congr fun k => ?_
  rw [mul_comm]
  norm_num

theorem aestronglyMeasurable_tsum_schwartzDilate (w : SchwartzMap ℝ ℂ) :
    AEStronglyMeasurable (fun u : ℝ => ∑' k : ℕ, w (((k + 1 : ℕ) : ℝ) * u))
      (volume.restrict (Ioi 0)) := by
  refine HTGeometry.aestronglyMeasurable_tsum_nat
    (fun k => (w.continuous.comp (continuous_const.mul continuous_id)).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact (summable_norm_schwartzDilate' w (mem_Ioi.mp hu)).of_norm

theorem aestronglyMeasurable_tsum_schwartzContract (w : SchwartzMap ℝ ℂ) :
    AEStronglyMeasurable (fun u : ℝ => ∑' m : ℕ, w (((m + 1 : ℕ) : ℝ) / u))
      (volume.restrict (Ioi 0)) := by
  refine HTGeometry.aestronglyMeasurable_tsum_nat
    (fun m => ((w.continuous.measurable.comp
      (measurable_const.div measurable_id)).aestronglyMeasurable)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hupos : (0 : ℝ) < u := mem_Ioi.mp hu
  have h := (HTGeometry.summable_norm_schwartzDilate w (inv_pos.mpr hupos)).of_norm
  refine h.congr fun m => ?_
  rw [div_eq_mul_inv, mul_comm]
  norm_num

theorem integrableOn_seed_mul_tsum_schwartzDilate {b : ℝ} (hb : 0 < b) {g : ℝ → ℂ}
    (hg : Integrable g) (hsupp : Function.support g ⊆ Icc b b⁻¹) (w : SchwartzMap ℝ ℂ) :
    IntegrableOn (fun u : ℝ => g u * ∑' k : ℕ, w (((k + 1 : ℕ) : ℝ) * u)) (Ioi 0) := by
  obtain ⟨C, hC0, hC⟩ := HTGeometry.exists_tsum_norm_schwartzDilate_le w
  refine integrableOn_seed_mul_of_bdd_on_window hg hsupp
    (aestronglyMeasurable_tsum_schwartzDilate w) (M := C / b ^ (2 : ℕ)) ?_
  intro u hu
  have hupos : (0 : ℝ) < u := lt_of_lt_of_le hb hu.1
  refine le_trans (norm_tsum_le_tsum_norm (summable_norm_schwartzDilate' w hupos)) ?_
  refine le_trans (tsum_norm_schwartzDilate_le' hC hupos) ?_
  refine div_le_div_of_nonneg_left hC0 (by positivity) ?_
  nlinarith [hu.1]

theorem integrableOn_seed_mul_tsum_schwartzContract {b : ℝ} (hb : 0 < b)
    {g : ℝ → ℂ} (hg : Integrable g) (hsupp : Function.support g ⊆ Icc b b⁻¹)
    (w : SchwartzMap ℝ ℂ) :
    IntegrableOn
      (fun u : ℝ => g u * (((u : ℝ) : ℂ)⁻¹ * ∑' m : ℕ, w (((m + 1 : ℕ) : ℝ) / u))) (Ioi 0) := by
  obtain ⟨C, hC0, hC⟩ := HTGeometry.exists_tsum_norm_schwartzDilate_le w
  refine integrableOn_seed_mul_of_bdd_on_window hg hsupp
    ((Complex.measurable_ofReal.inv.aestronglyMeasurable).mul
      (aestronglyMeasurable_tsum_schwartzContract w))
    (M := C / b) ?_
  intro u hu
  have hupos : (0 : ℝ) < u := lt_of_lt_of_le hb hu.1
  have hsummable : Summable fun m : ℕ => ‖w (((m + 1 : ℕ) : ℝ) / u)‖ := by
    refine (HTGeometry.summable_norm_schwartzDilate w (inv_pos.mpr hupos)).congr fun m => ?_
    rw [div_eq_mul_inv, mul_comm]
    norm_num
  have htail : ∑' m : ℕ, ‖w (((m + 1 : ℕ) : ℝ) / u)‖ ≤ C * u ^ (2 : ℕ) := by
    have hle : ∑' m : ℕ, ‖w (u⁻¹ * ((m : ℝ) + 1))‖ ≤ C / (u⁻¹) ^ (2 : ℕ) :=
      hC u⁻¹ (inv_pos.mpr hupos)
    have hcongr : (∑' m : ℕ, ‖w (((m + 1 : ℕ) : ℝ) / u)‖) =
        ∑' m : ℕ, ‖w (u⁻¹ * ((m : ℝ) + 1))‖ := by
      refine tsum_congr fun m => ?_
      rw [div_eq_mul_inv, mul_comm]
      norm_num
    rw [hcongr]
    refine hle.trans_eq ?_
    rw [inv_pow, div_eq_mul_inv, inv_inv]
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hupos]
  have hnorm := norm_tsum_le_tsum_norm hsummable
  have hchain : ‖∑' m : ℕ, w (((m + 1 : ℕ) : ℝ) / u)‖ ≤ C * u ^ (2 : ℕ) := le_trans hnorm htail
  have hfinal : u⁻¹ * ‖∑' m : ℕ, w (((m + 1 : ℕ) : ℝ) / u)‖ ≤ u⁻¹ * (C * u ^ (2 : ℕ)) :=
    mul_le_mul_of_nonneg_left hchain (by positivity)
  refine hfinal.trans ?_
  have huC : u⁻¹ * (C * u ^ (2 : ℕ)) = C * u := by
    field_simp
  rw [huC, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left hu.2 hC0



/-! ## Poisson summation in co-Poisson form -/

theorem tsum_schwartzDilate_congr (w : ℝ → ℂ) (u : ℝ) :
    (∑' k : ℕ, w (((k + 1 : ℕ) : ℝ) * u)) = ∑' n : ℕ, w (u * ((n : ℝ) + 1)) := by
  refine tsum_congr fun k => ?_
  rw [mul_comm]
  norm_num

theorem tsum_schwartzContract_congr (w : ℝ → ℂ) (u : ℝ) :
    (∑' m : ℕ, w (((m + 1 : ℕ) : ℝ) / u)) = ∑' n : ℕ, w (((n : ℝ) + 1) / u) := by
  refine tsum_congr fun m => ?_
  norm_num

/-- **Poisson summation in the form the co-Poisson sum consumes.** -/
theorem tsum_schwartzDilate_poisson (w : SchwartzMap ℝ ℂ) (heven : ∀ x : ℝ, w (-x) = w x)
    {u : ℝ} (hu : 0 < u) :
    (∑' k : ℕ, w (((k + 1 : ℕ) : ℝ) * u)) =
      ((u : ℝ) : ℂ)⁻¹ * ((𝓕 (w : ℝ → ℂ)) 0 / 2 +
        ∑' m : ℕ, (𝓕 (w : ℝ → ℂ)) (((m + 1 : ℕ) : ℝ) / u)) - w 0 / 2 := by
  have hsum : Summable fun n : ℕ => w (u * ((n : ℝ) + 1)) :=
    HTGeometry.summable_schwartzDilate w hu
  have hsumF : Summable fun n : ℕ => (𝓕 (w : ℝ → ℂ)) (((n : ℝ) + 1) / u) := by
    have h := HTGeometry.summable_schwartzDilate (𝓕 w) (inv_pos.mpr hu)
    simp only [SchwartzMap.fourier_coe] at h
    refine h.congr fun n => ?_
    rw [div_eq_mul_inv, mul_comm]
  have hp := even_poisson_summation_dilate w heven hu hsum hsumF
  rw [tsum_schwartzDilate_congr (w : ℝ → ℂ) u,
    tsum_schwartzContract_congr (𝓕 (w : ℝ → ℂ)) u]
  linear_combination hp / 2

/-! ## Half-line masses -/

theorem fourier_zero_eq_two_mul_integral_Ioi (w : SchwartzMap ℝ ℂ)
    (heven : ∀ x : ℝ, w (-x) = w x) :
    (𝓕 (w : ℝ → ℂ)) 0 = 2 * ∫ x in Ioi (0 : ℝ), w x := by
  rw [← integral_eq_fourier_zero]
  exact integral_eq_two_mul_integral_Ioi_of_even (SchwartzMap.integrable w) heven

/-- **Fourier inversion at the origin.**  The half-line mass of the transform is half the value of
the function at the origin. -/
theorem integral_Ioi_fourier_eq (w : SchwartzMap ℝ ℂ) (heven : ∀ x : ℝ, w (-x) = w x) :
    (∫ x in Ioi (0 : ℝ), (𝓕 (w : ℝ → ℂ)) x) = w 0 / 2 := by
  have hint : Integrable (𝓕 (w : ℝ → ℂ)) := by
    rw [← SchwartzMap.fourier_coe]
    exact SchwartzMap.integrable _
  have hFeven : ∀ x : ℝ, (𝓕 (w : ℝ → ℂ)) (-x) = (𝓕 (w : ℝ → ℂ)) x :=
    fun x => fourier_even_of_even heven x
  have htotal : (∫ x : ℝ, (𝓕 (w : ℝ → ℂ)) x) = 2 * ∫ x in Ioi (0 : ℝ), (𝓕 (w : ℝ → ℂ)) x :=
    integral_eq_two_mul_integral_Ioi_of_even hint hFeven
  have hinv : (∫ x : ℝ, (𝓕 (w : ℝ → ℂ)) x) = w 0 := by
    rw [integral_eq_fourier_zero]
    have h := Continuous.fourierInv_fourier_eq (f := (w : ℝ → ℂ)) w.continuous
      (SchwartzMap.integrable w) hint
    have h0 := congrFun h 0
    rw [Real.fourierInv_eq_fourier_neg, neg_zero] at h0
    exact h0
  rw [htotal] at hinv
  linear_combination hinv / 2



/-! ## The split of the dilated pairing -/

theorem integral_seed_mul_tsum_schwartzDilate_split {b : ℝ} (hb : 0 < b) {g : ℝ → ℂ}
    (hg : Integrable g) (hsupp : Function.support g ⊆ Icc b b⁻¹)
    (w : SchwartzMap ℝ ℂ) (heven : ∀ x : ℝ, w (-x) = w x) :
    (∫ u in Ioi (0 : ℝ), g u * ∑' k : ℕ, w (((k + 1 : ℕ) : ℝ) * u)) =
      (𝓕 (w : ℝ → ℂ)) 0 / 2 * coPoissonCorrectionConstant g
        + (∫ u in Ioi (0 : ℝ),
            ∑' m : ℕ, ((u : ℝ) : ℂ)⁻¹ * g u * (𝓕 (w : ℝ → ℂ)) (((m + 1 : ℕ) : ℝ) / u))
        - w 0 / 2 * ∫ u in Ioi (0 : ℝ), g u := by
  have hi1 : IntegrableOn
      (fun u : ℝ => (𝓕 (w : ℝ → ℂ)) 0 / 2 * (((u : ℝ) : ℂ)⁻¹ * g u)) (Ioi 0) :=
    (integrableOn_seed_div hb hg hsupp).const_mul _
  have hi2 : IntegrableOn
      (fun u : ℝ =>
        ∑' m : ℕ, ((u : ℝ) : ℂ)⁻¹ * g u * (𝓕 (w : ℝ → ℂ)) (((m + 1 : ℕ) : ℝ) / u)) (Ioi 0) := by
    have h := integrableOn_seed_mul_tsum_schwartzContract hb hg hsupp (𝓕 w)
    simp only [SchwartzMap.fourier_coe] at h
    refine h.congr (Filter.Eventually.of_forall fun u => ?_)
    dsimp only
    rw [tsum_mul_left]
    ring
  have hi3 : IntegrableOn (fun u : ℝ => w 0 / 2 * g u) (Ioi 0) :=
    ((hg.restrict (s := Ioi 0)).const_mul _)
  have hi12 : IntegrableOn (fun u : ℝ =>
      (𝓕 (w : ℝ → ℂ)) 0 / 2 * (((u : ℝ) : ℂ)⁻¹ * g u)
        + ∑' m : ℕ, ((u : ℝ) : ℂ)⁻¹ * g u * (𝓕 (w : ℝ → ℂ)) (((m + 1 : ℕ) : ℝ) / u)) (Ioi 0) :=
    hi1.add hi2
  have hpt : ∀ u ∈ Ioi (0 : ℝ), g u * (∑' k : ℕ, w (((k + 1 : ℕ) : ℝ) * u)) =
      (𝓕 (w : ℝ → ℂ)) 0 / 2 * (((u : ℝ) : ℂ)⁻¹ * g u)
        + (∑' m : ℕ, ((u : ℝ) : ℂ)⁻¹ * g u * (𝓕 (w : ℝ → ℂ)) (((m + 1 : ℕ) : ℝ) / u))
        - w 0 / 2 * g u := by
    intro u hu
    rw [tsum_schwartzDilate_poisson w heven (mem_Ioi.mp hu), tsum_mul_left]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt,
    integral_sub hi12 hi3, integral_add hi1 hi2, integral_const_mul, integral_const_mul,
    coPoissonCorrectionConstant_eq_logMass]

/-! ## The co-Poisson pairing -/

theorem integral_Ioi_coPoissonSum_mul_eq_add {g : ℝ → ℂ} (w : ℝ → ℂ)
    (hw : IntegrableOn w (Ioi 0))
    (hPw : IntegrableOn (fun t => burnolCoPoissonRightSum g t * w t) (Ioi 0)) :
    (∫ t in Ioi (0 : ℝ), (∑' k : ℕ, (((k + 1 : ℕ) : ℝ) : ℂ)⁻¹ * g (t / ((k + 1 : ℕ) : ℝ))) * w t)
      = (∫ t in Ioi (0 : ℝ), burnolCoPoissonRightSum g t * w t)
        + coPoissonCorrectionConstant g * ∫ t in Ioi (0 : ℝ), w t := by
  have hpt : ∀ t ∈ Ioi (0 : ℝ),
      (∑' k : ℕ, (((k + 1 : ℕ) : ℝ) : ℂ)⁻¹ * g (t / ((k + 1 : ℕ) : ℝ))) * w t
        = burnolCoPoissonRightSum g t * w t + coPoissonCorrectionConstant g * w t := by
    intro t ht
    rw [burnolCoPoissonRightSum_eq_sub_correction, abs_of_pos (mem_Ioi.mp ht)]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt,
    integral_add hPw (hw.const_mul _), integral_const_mul]

/-- **Burnol's co-Poisson intertwining, in pairing form.**  Pairing the co-Poisson sum of a window
seed with an even Schwartz function is the same as pairing the co-Poisson sum of the reciprocal seed
with its Fourier transform. -/
theorem integral_Ioi_burnolCoPoisson_mul_eq_fourier {b : ℝ} (hb : 0 < b) {g : ℝ → ℂ}
    (hg : Integrable g) (hsupp : Function.support g ⊆ Icc b b⁻¹)
    (hG : Integrable (coPoissonReciprocalSeed g))
    (hGsupp : Function.support (coPoissonReciprocalSeed g) ⊆ Icc b b⁻¹)
    (w : SchwartzMap ℝ ℂ) (heven : ∀ x : ℝ, w (-x) = w x)
    (hPw : IntegrableOn (fun t => burnolCoPoissonRightSum g t * w t) (Ioi 0))
    (hPGw : IntegrableOn (fun t =>
      burnolCoPoissonRightSum (coPoissonReciprocalSeed g) t * (𝓕 (w : ℝ → ℂ)) t) (Ioi 0)) :
    (∫ t in Ioi (0 : ℝ), burnolCoPoissonRightSum g t * w t) =
      ∫ t in Ioi (0 : ℝ),
        burnolCoPoissonRightSum (coPoissonReciprocalSeed g) t * (𝓕 (w : ℝ → ℂ)) t := by
  have hFint : IntegrableOn (𝓕 (w : ℝ → ℂ)) (Ioi 0) := by
    have : Integrable (𝓕 (w : ℝ → ℂ)) := by
      rw [← SchwartzMap.fourier_coe]
      exact SchwartzMap.integrable _
    exact this.restrict
  -- the seed side
  have hA := integral_Ioi_coPoissonSum_mul_eq_add (g := g) (w : ℝ → ℂ)
    (SchwartzMap.integrable w).restrict hPw
  have hB := integral_coPoissonSum_mul_eq hb hg hsupp w
  have hC := integral_seed_mul_tsum_schwartzDilate_split hb hg hsupp w heven
  -- the reciprocal side
  have hA' := integral_Ioi_coPoissonSum_mul_eq_add (g := coPoissonReciprocalSeed g)
    (𝓕 (w : ℝ → ℂ)) hFint hPGw
  have hB' := integral_coPoissonSum_mul_eq hb hG hGsupp (𝓕 w)
  simp only [SchwartzMap.fourier_coe] at hB'
  have hD := integral_tsum_seed_inv_dilate_eq hb hg hsupp hG hGsupp (𝓕 w)
  simp only [SchwartzMap.fourier_coe] at hD
  -- the two constants
  have hmass : (𝓕 (w : ℝ → ℂ)) 0 / 2 = ∫ x in Ioi (0 : ℝ), w x := by
    rw [fourier_zero_eq_two_mul_integral_Ioi w heven]
    ring
  have hmass' : coPoissonCorrectionConstant (coPoissonReciprocalSeed g) *
      ∫ t in Ioi (0 : ℝ), (𝓕 (w : ℝ → ℂ)) t = w 0 / 2 * ∫ u in Ioi (0 : ℝ), g u := by
    rw [coPoissonCorrectionConstant_reciprocalSeed, integral_Ioi_fourier_eq w heven]
    ring
  rw [hmass] at hC
  rw [hB, hC, hD, ← hB'] at hA
  rw [hA', hmass'] at hA
  linear_combination -hA

end RHTower

