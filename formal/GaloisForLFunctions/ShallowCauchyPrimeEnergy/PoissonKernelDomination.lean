import GaloisForLFunctions.HTGeometry.HalfPlanePoissonKernel
import GaloisForLFunctions.RHTower.FiniteOfflineCauchyEnergy

/-!
# Shifted Cauchy kernel domination and Poisson `L²` identity

For transverse shifts `0 ≤ a, b ≤ h` (`h > 0`) and any Lorentzian width `R₀ ≥ 2h`, the `h`-shifted
transverse Cauchy kernel satisfies

`4 h · transverseCauchyKernel (h + a) (h + b) Δ ≤ 4 · R₀² / (R₀² + Δ²)`.

Evaluating the convolution semigroup `P_r ⋆ P_r = P_{2r}` of the half-plane Poisson kernel at
`r = R₀ / 2` converts any finite Lorentzian pair sum `Σ_{q₁, q₂ ∈ Z} R₀² / (R₀² + (γ_{q₁} − γ_{q₂})²)`
into `(4 / (π R₀)) ∫ G_r(t)² dt`, where `G_r(t) = Σ_{q ∈ Z} r² / (r² + (t − γ_q)²)`.
-/

noncomputable section

open MeasureTheory Set Filter Topology GaloisForLFunctions.HTGeometry
open scoped BigOperators

namespace RHTower

/-- Pointwise domination of the `h`-shifted transverse Cauchy kernel by the width-`R₀` Lorentzian
whenever `0 ≤ a, b ≤ h` (`h > 0`) and `2h ≤ R₀`. -/
theorem shift_mul_transverseCauchyKernel_le_four_mul_lorentz
    {h a b R₀ Δ : ℝ} (hh : 0 < h) (ha0 : 0 ≤ a) (ha : a ≤ h)
    (hb0 : 0 ≤ b) (hb : b ≤ h) (hR : 2 * h ≤ R₀) :
    4 * h * transverseCauchyKernel (h + a) (h + b) Δ ≤
      4 * (R₀ ^ (2 : ℕ) / (R₀ ^ (2 : ℕ) + Δ ^ (2 : ℕ))) := by
  have hRpos : 0 < R₀ := by linarith
  have hs_lo : 2 * h ≤ h + a + (h + b) := by linarith
  have hs_hi : h + a + (h + b) ≤ 4 * h := by linarith
  have hstep1 :
      4 * h * ((h + a + (h + b)) / ((h + a + (h + b)) ^ (2 : ℕ) + Δ ^ (2 : ℕ))) ≤
        4 * ((2 * h) ^ (2 : ℕ) / ((2 * h) ^ (2 : ℕ) + Δ ^ (2 : ℕ))) := by
    rw [← mul_div_assoc, ← mul_div_assoc,
      div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : 16 * h ^ (3 : ℕ) * (h + a + (h + b)) ≤
        16 * h ^ (2 : ℕ) * (h + a + (h + b)) ^ (2 : ℕ) := by
      have hhs : 2 * h * (h + a + (h + b)) ≤ (h + a + (h + b)) ^ (2 : ℕ) := by
        rw [sq]
        exact mul_le_mul_of_nonneg_right hs_lo (by linarith)
      have hh2 : 0 ≤ 8 * h ^ (2 : ℕ) := by positivity
      calc 16 * h ^ (3 : ℕ) * (h + a + (h + b))
          = 8 * h ^ (2 : ℕ) * (2 * h * (h + a + (h + b))) := by ring
        _ ≤ 8 * h ^ (2 : ℕ) * (h + a + (h + b)) ^ (2 : ℕ) :=
            mul_le_mul_of_nonneg_left hhs hh2
        _ ≤ 16 * h ^ (2 : ℕ) * (h + a + (h + b)) ^ (2 : ℕ) :=
            mul_le_mul_of_nonneg_right
              (show 8 * h ^ (2 : ℕ) ≤ 16 * h ^ (2 : ℕ) by linarith [sq_nonneg h])
              (sq_nonneg (h + a + (h + b)))
    have h2 : 4 * h * (h + a + (h + b)) * Δ ^ (2 : ℕ) ≤
        16 * h ^ (2 : ℕ) * Δ ^ (2 : ℕ) := by
      have hhs : 4 * h * (h + a + (h + b)) ≤ 16 * h ^ (2 : ℕ) := by
        calc 4 * h * (h + a + (h + b)) ≤ 4 * h * (4 * h) :=
              mul_le_mul_of_nonneg_left hs_hi (by positivity)
          _ = 16 * h ^ (2 : ℕ) := by ring
      exact mul_le_mul_of_nonneg_right hhs (sq_nonneg Δ)
    have hlhs : 4 * h * (h + a + (h + b)) * ((2 * h) ^ (2 : ℕ) + Δ ^ (2 : ℕ)) =
        16 * h ^ (3 : ℕ) * (h + a + (h + b)) + 4 * h * (h + a + (h + b)) * Δ ^ (2 : ℕ) := by ring
    have hrhs : 4 * (2 * h) ^ (2 : ℕ) * ((h + a + (h + b)) ^ (2 : ℕ) + Δ ^ (2 : ℕ)) =
        16 * h ^ (2 : ℕ) * (h + a + (h + b)) ^ (2 : ℕ) + 16 * h ^ (2 : ℕ) * Δ ^ (2 : ℕ) := by ring
    linarith
  have hstep2 :
      (2 * h) ^ (2 : ℕ) / ((2 * h) ^ (2 : ℕ) + Δ ^ (2 : ℕ)) ≤
        R₀ ^ (2 : ℕ) / (R₀ ^ (2 : ℕ) + Δ ^ (2 : ℕ)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hsq : (2 * h) ^ (2 : ℕ) ≤ R₀ ^ (2 : ℕ) := pow_le_pow_left₀ (by positivity) hR 2
    have hm := mul_le_mul_of_nonneg_right hsq (sq_nonneg Δ)
    linarith [show (2 * h) ^ (2 : ℕ) * (R₀ ^ (2 : ℕ) + Δ ^ (2 : ℕ)) =
        (2 * h) ^ (2 : ℕ) * R₀ ^ (2 : ℕ) + (2 * h) ^ (2 : ℕ) * Δ ^ (2 : ℕ) by ring,
      show R₀ ^ (2 : ℕ) * ((2 * h) ^ (2 : ℕ) + Δ ^ (2 : ℕ)) =
        (2 * h) ^ (2 : ℕ) * R₀ ^ (2 : ℕ) + R₀ ^ (2 : ℕ) * Δ ^ (2 : ℕ) by ring]
  unfold transverseCauchyKernel
  exact hstep1.trans (mul_le_mul_of_nonneg_left hstep2 (by norm_num))

/-- Finite narrow Lorentzian sum `Σ_{q ∈ Z} r² / (r² + (t − γ_q)²)`. -/
def windowNarrowSum {ι : Type*} (Z : Finset ι) (γ : ι → ℝ) (r t : ℝ) : ℝ :=
  ∑ q ∈ Z, r ^ (2 : ℕ) / (r ^ (2 : ℕ) + (t - γ q) ^ (2 : ℕ))

theorem windowNarrowSum_nonneg {ι : Type*} (Z : Finset ι) (γ : ι → ℝ) (r t : ℝ) :
    0 ≤ windowNarrowSum Z γ r t :=
  Finset.sum_nonneg fun _ _ => by positivity

theorem continuous_windowNarrowSum {ι : Type*} (Z : Finset ι) (γ : ι → ℝ)
    {r : ℝ} (hr : 0 < r) :
    Continuous (windowNarrowSum Z γ r) := by
  unfold windowNarrowSum
  refine continuous_finsetSum Z fun q _ => ?_
  refine Continuous.div continuous_const (by fun_prop) fun t => ?_
  positivity

theorem windowNarrowSum_mono_radius {ι : Type*} (Z : Finset ι) (γ : ι → ℝ)
    {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hle : r₁ ≤ r₂) (t : ℝ) :
    windowNarrowSum Z γ r₁ t ≤ windowNarrowSum Z γ r₂ t := by
  have hr₂ : 0 < r₂ := hr₁.trans_le hle
  refine Finset.sum_le_sum fun q _ => ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hsq : r₁ ^ (2 : ℕ) ≤ r₂ ^ (2 : ℕ) := pow_le_pow_left₀ hr₁.le hle 2
  have hm := mul_le_mul_of_nonneg_right hsq (sq_nonneg (t - γ q))
  linarith

theorem narrowKernel_mul_eq_poisson {r : ℝ} (hr : 0 < r) (t x y : ℝ) :
    (r ^ (2 : ℕ) / (r ^ (2 : ℕ) + (t - x) ^ (2 : ℕ))) *
        (r ^ (2 : ℕ) / (r ^ (2 : ℕ) + (t - y) ^ (2 : ℕ))) =
      (Real.pi * r) ^ (2 : ℕ) * (halfPlanePoisson r (x - t) * halfPlanePoisson r (t - y)) := by
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hd1 : r ^ (2 : ℕ) + (t - x) ^ (2 : ℕ) ≠ 0 := by positivity
  have hd2 : r ^ (2 : ℕ) + (t - y) ^ (2 : ℕ) ≠ 0 := by positivity
  have hsq : (x - t) ^ (2 : ℕ) = (t - x) ^ (2 : ℕ) := by ring
  rw [halfPlanePoisson, halfPlanePoisson, hsq]
  field_simp

theorem integrable_narrowKernel_mul {r : ℝ} (hr : 0 < r) (x y : ℝ) :
    Integrable (fun t : ℝ =>
      (r ^ (2 : ℕ) / (r ^ (2 : ℕ) + (t - x) ^ (2 : ℕ))) *
        (r ^ (2 : ℕ) / (r ^ (2 : ℕ) + (t - y) ^ (2 : ℕ)))) := by
  have hcongr : (fun t : ℝ =>
      (r ^ (2 : ℕ) / (r ^ (2 : ℕ) + (t - x) ^ (2 : ℕ))) *
        (r ^ (2 : ℕ) / (r ^ (2 : ℕ) + (t - y) ^ (2 : ℕ)))) =
      fun t : ℝ => (Real.pi * r) ^ (2 : ℕ) *
        (halfPlanePoisson r (x - t) * halfPlanePoisson r (t - y)) := by
    funext t; exact narrowKernel_mul_eq_poisson hr t x y
  rw [hcongr]
  exact (integrable_poisson_shift_product hr hr x y).const_mul _

theorem integral_narrowKernel_mul {R₀ : ℝ} (hR₀ : 0 < R₀) (x y : ℝ) :
    (∫ t : ℝ,
        ((R₀ / 2) ^ (2 : ℕ) / ((R₀ / 2) ^ (2 : ℕ) + (t - x) ^ (2 : ℕ))) *
          ((R₀ / 2) ^ (2 : ℕ) / ((R₀ / 2) ^ (2 : ℕ) + (t - y) ^ (2 : ℕ)))) =
      (Real.pi * R₀ / 4) * (R₀ ^ (2 : ℕ) / (R₀ ^ (2 : ℕ) + (x - y) ^ (2 : ℕ))) := by
  have hr : 0 < R₀ / 2 := half_pos hR₀
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hcongr : (fun t : ℝ =>
      ((R₀ / 2) ^ (2 : ℕ) / ((R₀ / 2) ^ (2 : ℕ) + (t - x) ^ (2 : ℕ))) *
        ((R₀ / 2) ^ (2 : ℕ) / ((R₀ / 2) ^ (2 : ℕ) + (t - y) ^ (2 : ℕ)))) =
      fun t : ℝ => (Real.pi * (R₀ / 2)) ^ (2 : ℕ) *
        (halfPlanePoisson (R₀ / 2) (x - t) * halfPlanePoisson (R₀ / 2) (t - y)) := by
    funext t; exact narrowKernel_mul_eq_poisson hr t x y
  rw [hcongr, MeasureTheory.integral_const_mul, integral_poisson_shift_product hr hr x y,
    show R₀ / 2 + R₀ / 2 = R₀ by ring, halfPlanePoisson]
  have hden : R₀ ^ (2 : ℕ) + (x - y) ^ (2 : ℕ) ≠ 0 := by positivity
  field_simp
  ring

theorem integrable_windowNarrowSum_sq {ι : Type*} (Z : Finset ι) (γ : ι → ℝ)
    {r : ℝ} (hr : 0 < r) :
    Integrable (fun t : ℝ => (windowNarrowSum Z γ r t) ^ (2 : ℕ)) := by
  have hrew : (fun t : ℝ => (windowNarrowSum Z γ r t) ^ (2 : ℕ)) =
      fun t : ℝ => ∑ q₁ ∈ Z, ∑ q₂ ∈ Z,
        (r ^ (2 : ℕ) / (r ^ (2 : ℕ) + (t - γ q₁) ^ (2 : ℕ))) *
          (r ^ (2 : ℕ) / (r ^ (2 : ℕ) + (t - γ q₂) ^ (2 : ℕ))) := by
    funext t
    rw [windowNarrowSum, sq, Finset.sum_mul_sum]
  rw [hrew]
  exact integrable_finsetSum Z fun q₁ _ =>
    integrable_finsetSum Z fun q₂ _ => integrable_narrowKernel_mul hr (γ q₁) (γ q₂)

/-- **Exact Poisson semigroup `L²` identity.** The Lorentzian pair sum at width `R₀ > 0` equals
`(4 / (π R₀))` times the global `L²` integral of `windowNarrowSum Z γ (R₀ / 2)`. -/
theorem lorentz_pairSum_eq_integral_windowNarrowSum_sq {ι : Type*} (Z : Finset ι) (γ : ι → ℝ)
    {R₀ : ℝ} (hR₀ : 0 < R₀) :
    (∑ q₁ ∈ Z, ∑ q₂ ∈ Z,
        R₀ ^ (2 : ℕ) / (R₀ ^ (2 : ℕ) + (γ q₁ - γ q₂) ^ (2 : ℕ))) =
      4 / (Real.pi * R₀) * ∫ t : ℝ, (windowNarrowSum Z γ (R₀ / 2) t) ^ (2 : ℕ) := by
  have hr : 0 < R₀ / 2 := half_pos hR₀
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hRne : R₀ ≠ 0 := hR₀.ne'
  have hrew : (fun t : ℝ => (windowNarrowSum Z γ (R₀ / 2) t) ^ (2 : ℕ)) =
      fun t : ℝ => ∑ q₁ ∈ Z, ∑ q₂ ∈ Z,
        ((R₀ / 2) ^ (2 : ℕ) / ((R₀ / 2) ^ (2 : ℕ) + (t - γ q₁) ^ (2 : ℕ))) *
          ((R₀ / 2) ^ (2 : ℕ) / ((R₀ / 2) ^ (2 : ℕ) + (t - γ q₂) ^ (2 : ℕ))) := by
    funext t
    rw [windowNarrowSum, sq, Finset.sum_mul_sum]
  rw [hrew, MeasureTheory.integral_finsetSum Z (fun q₁ _ =>
    integrable_finsetSum Z fun q₂ _ => integrable_narrowKernel_mul hr (γ q₁) (γ q₂))]
  have hsum_eq :
      (∑ q₁ ∈ Z, ∫ t : ℝ, ∑ q₂ ∈ Z,
          ((R₀ / 2) ^ (2 : ℕ) / ((R₀ / 2) ^ (2 : ℕ) + (t - γ q₁) ^ (2 : ℕ))) *
            ((R₀ / 2) ^ (2 : ℕ) / ((R₀ / 2) ^ (2 : ℕ) + (t - γ q₂) ^ (2 : ℕ)))) =
        (Real.pi * R₀ / 4) * ∑ q₁ ∈ Z, ∑ q₂ ∈ Z,
          R₀ ^ (2 : ℕ) / (R₀ ^ (2 : ℕ) + (γ q₁ - γ q₂) ^ (2 : ℕ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q₁ _ => ?_
    rw [MeasureTheory.integral_finsetSum Z
        (fun q₂ _ => integrable_narrowKernel_mul hr (γ q₁) (γ q₂)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun q₂ _ => integral_narrowKernel_mul hR₀ (γ q₁) (γ q₂)
  rw [hsum_eq]
  field_simp

/-- Five-piece union bound on `ℝ` for any nonnegative integrable function. -/
theorem integral_le_five_pieces {f : ℝ → ℝ} (hf : Integrable f)
    (hnn : ∀ t : ℝ, 0 ≤ f t) {T : ℝ} (_hT : 0 < T) :
    (∫ t : ℝ, f t) ≤
      (∫ t in Iic (T / 2), f t) +
        (∫ t in Icc (T / 2) T, f t) +
        (∫ t in Icc T (2 * T), f t) +
        (∫ t in Icc (2 * T) (4 * T), f t) +
        (∫ t in Ici (4 * T), f t) := by
  have hi1 : Integrable ((Iic (T / 2)).indicator f) := hf.indicator measurableSet_Iic
  have hi2 : Integrable ((Icc (T / 2) T).indicator f) := hf.indicator measurableSet_Icc
  have hi3 : Integrable ((Icc T (2 * T)).indicator f) := hf.indicator measurableSet_Icc
  have hi4 : Integrable ((Icc (2 * T) (4 * T)).indicator f) := hf.indicator measurableSet_Icc
  have hi5 : Integrable ((Ici (4 * T)).indicator f) := hf.indicator measurableSet_Ici
  have h12 : Integrable (fun t =>
      (Iic (T / 2)).indicator f t + (Icc (T / 2) T).indicator f t) := hi1.add hi2
  have h123 : Integrable (fun t =>
      ((Iic (T / 2)).indicator f t + (Icc (T / 2) T).indicator f t) +
        (Icc T (2 * T)).indicator f t) := h12.add hi3
  have h1234 : Integrable (fun t =>
      (((Iic (T / 2)).indicator f t + (Icc (T / 2) T).indicator f t) +
        (Icc T (2 * T)).indicator f t) +
        (Icc (2 * T) (4 * T)).indicator f t) := h123.add hi4
  have h12345 : Integrable (fun t =>
      ((((Iic (T / 2)).indicator f t + (Icc (T / 2) T).indicator f t) +
        (Icc T (2 * T)).indicator f t) +
        (Icc (2 * T) (4 * T)).indicator f t) +
        (Ici (4 * T)).indicator f t) := h1234.add hi5
  have hpt : ∀ t : ℝ, f t ≤
      ((((Iic (T / 2)).indicator f t +
        (Icc (T / 2) T).indicator f t) +
        (Icc T (2 * T)).indicator f t) +
        (Icc (2 * T) (4 * T)).indicator f t) +
        (Ici (4 * T)).indicator f t := by
    intro t
    have p1 := Set.indicator_nonneg (s := Iic (T / 2)) (fun x _ => hnn x) t
    have p2 := Set.indicator_nonneg (s := Icc (T / 2) T) (fun x _ => hnn x) t
    have p3 := Set.indicator_nonneg (s := Icc T (2 * T)) (fun x _ => hnn x) t
    have p4 := Set.indicator_nonneg (s := Icc (2 * T) (4 * T)) (fun x _ => hnn x) t
    have p5 := Set.indicator_nonneg (s := Ici (4 * T)) (fun x _ => hnn x) t
    by_cases h1 : t ≤ T / 2
    · rw [Set.indicator_of_mem (show t ∈ Iic (T / 2) from h1)]; linarith
    · by_cases h2 : t ≤ T
      · rw [Set.indicator_of_mem (show t ∈ Icc (T / 2) T from ⟨by linarith, h2⟩)]; linarith
      · by_cases h3 : t ≤ 2 * T
        · rw [Set.indicator_of_mem (show t ∈ Icc T (2 * T) from ⟨by linarith, h3⟩)]; linarith
        · by_cases h4 : t ≤ 4 * T
          · rw [Set.indicator_of_mem (show t ∈ Icc (2 * T) (4 * T) from ⟨by linarith, h4⟩)]
            linarith
          · rw [Set.indicator_of_mem (show t ∈ Ici (4 * T) from le_of_not_ge h4)]; linarith
  have hmono := MeasureTheory.integral_mono hf h12345 hpt
  rw [MeasureTheory.integral_add h1234 hi5,
    MeasureTheory.integral_add h123 hi4,
    MeasureTheory.integral_add h12 hi3,
    MeasureTheory.integral_add hi1 hi2,
    MeasureTheory.integral_indicator measurableSet_Iic,
    MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.integral_indicator measurableSet_Ici] at hmono
  exact hmono

end RHTower

end
