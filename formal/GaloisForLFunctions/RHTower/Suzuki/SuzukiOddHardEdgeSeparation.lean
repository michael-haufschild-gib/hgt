import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# The odd hard-edge separation

The Stieltjes factor `x(s) = ∫ s/(t+s) dμ` of a nonnegative spectral law is a probability-weighted
average of numbers in `[0,1]`, so it never exceeds one.  On the window `[0, Ls]` the integrand is at
least `1/(L+1)`, so the mass of that window is at most `(L+1)` times the factor: a small Stieltjes
factor forces a small mass on every fixed multiple of the shift scale.

Subtracting the window and the tail from the total mass leaves the annulus, which is the card's
statement that a macroscopic proportion of the odd source sits strictly above the shift scale and
strictly below every fixed threshold.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- The Stieltjes factor of a nonnegative spectral law at scale `s`. -/
def stieltjesFactor (μ : Measure ℝ) (s : ℝ) : ℝ := ∫ t, s / (t + s) ∂μ

theorem stieltjesFactor_le_one {μ : Measure ℝ} [IsProbabilityMeasure μ] {s : ℝ} (hs : 0 < s)
    (hsupp : ∀ᵐ t ∂μ, 0 ≤ t) (hint : Integrable (fun t => s / (t + s)) μ) :
    stieltjesFactor μ s ≤ 1 := by
  have hmono : ∫ t, s / (t + s) ∂μ ≤ ∫ _t : ℝ, (1 : ℝ) ∂μ := by
    refine integral_mono_ae hint (integrable_const _) ?_
    filter_upwards [hsupp] with t ht
    have h1 : (0 : ℝ) < t + s := by linarith
    rw [div_le_one h1]
    linarith
  rw [integral_const] at hmono
  simpa [stieltjesFactor] using hmono

theorem stieltjesFactor_nonneg {μ : Measure ℝ} {s : ℝ} (hs : 0 < s)
    (hsupp : ∀ᵐ t ∂μ, 0 ≤ t) : 0 ≤ stieltjesFactor μ s := by
  refine integral_nonneg_of_ae ?_
  filter_upwards [hsupp] with t ht
  have h1 : (0 : ℝ) < t + s := by linarith
  positivity

/-- **`(324)`: the mass of a fixed multiple of the shift scale is controlled by the Stieltjes
factor.** -/
theorem measureReal_Icc_le {μ : Measure ℝ} [IsProbabilityMeasure μ] {s L : ℝ} (hs : 0 < s)
    (hL : 0 ≤ L) (hsupp : ∀ᵐ t ∂μ, 0 ≤ t) (hint : Integrable (fun t => s / (t + s)) μ) :
    μ.real (Set.Icc 0 (L * s)) ≤ (L + 1) * stieltjesFactor μ s := by
  have hLpos : (0 : ℝ) < L + 1 := by linarith
  have hlow : ∀ t ∈ Set.Icc (0 : ℝ) (L * s), 1 / (L + 1) ≤ s / (t + s) := by
    intro t ht
    have ht0 : (0 : ℝ) ≤ t := ht.1
    have htL : t ≤ L * s := ht.2
    have h1 : (0 : ℝ) < t + s := by linarith
    rw [div_le_div_iff₀ hLpos h1]
    nlinarith
  have hset := setIntegral_ge_of_const_le (μ := μ) (s := Set.Icc (0 : ℝ) (L * s))
    (f := fun t => s / (t + s)) (c := 1 / (L + 1)) measurableSet_Icc
    (measure_ne_top μ _) hlow hint.integrableOn
  have hnn : 0 ≤ᵐ[μ] fun t => s / (t + s) := by
    filter_upwards [hsupp] with t ht
    have h1 : (0 : ℝ) < t + s := by linarith
    positivity
  have hsub : ∫ t in Set.Icc (0 : ℝ) (L * s), s / (t + s) ∂μ ≤ ∫ t, s / (t + s) ∂μ :=
    setIntegral_le_integral hint hnn
  have hcomb : μ.real (Set.Icc (0 : ℝ) (L * s)) * (1 / (L + 1)) ≤ stieltjesFactor μ s := by
    rw [stieltjesFactor]
    calc μ.real (Set.Icc (0 : ℝ) (L * s)) * (1 / (L + 1))
        = μ.real (Set.Icc (0 : ℝ) (L * s)) • (1 / (L + 1)) := by rw [smul_eq_mul]
      _ ≤ ∫ t in Set.Icc (0 : ℝ) (L * s), s / (t + s) ∂μ := hset
      _ ≤ ∫ t, s / (t + s) ∂μ := hsub
  have hmul : μ.real (Set.Icc (0 : ℝ) (L * s)) * (1 / (L + 1)) * (L + 1)
      ≤ stieltjesFactor μ s * (L + 1) :=
    mul_le_mul_of_nonneg_right hcomb hLpos.le
  have hsimp : μ.real (Set.Icc (0 : ℝ) (L * s)) * (1 / (L + 1)) * (L + 1)
      = μ.real (Set.Icc (0 : ℝ) (L * s)) := by
    field_simp
  rw [hsimp] at hmul
  linarith

/-- **`(322)`: at `L = 1` the window mass is at most twice the Stieltjes factor.** -/
theorem measureReal_Icc_le_two_mul {μ : Measure ℝ} [IsProbabilityMeasure μ] {s : ℝ} (hs : 0 < s)
    (hsupp : ∀ᵐ t ∂μ, 0 ≤ t) (hint : Integrable (fun t => s / (t + s)) μ) :
    μ.real (Set.Icc 0 s) ≤ 2 * stieltjesFactor μ s := by
  have h := measureReal_Icc_le (μ := μ) (s := s) (L := 1) hs (by norm_num) hsupp hint
  rw [one_mul] at h
  linarith

/-- **`(323)`: the annulus carries whatever the window and the tail do not.** -/
theorem one_le_window_annulus_tail {μ : Measure ℝ} [IsProbabilityMeasure μ] {r ε : ℝ} (hsupp : ∀ᵐ t ∂μ, 0 ≤ t) :
    1 ≤ μ.real (Set.Icc 0 r) + μ.real (Set.Ioo r ε) + μ.real (Set.Ici ε) := by
  have hcompl : μ (Set.Ici (0 : ℝ))ᶜ = 0 := by
    have h := ae_iff.mp hsupp
    have hset : {t : ℝ | ¬ (0 ≤ t)} = (Set.Ici (0 : ℝ))ᶜ := by ext t; simp
    rwa [hset] at h
  have hIci : μ (Set.Ici (0 : ℝ)) = 1 := by
    have h := measure_add_measure_compl (μ := μ) (measurableSet_Ici (a := (0 : ℝ)))
    rw [hcompl, add_zero, measure_univ] at h
    exact h
  have hIciReal : μ.real (Set.Ici (0 : ℝ)) = 1 := by
    rw [Measure.real, hIci]
    simp
  have hsub : Set.Ici (0 : ℝ)
      ⊆ (Set.Icc 0 r ∪ Set.Ioo r ε) ∪ Set.Ici ε := by
    intro t ht
    have ht0 : (0 : ℝ) ≤ t := ht
    by_cases h1 : t ≤ r
    · exact Or.inl (Or.inl ⟨ht0, h1⟩)
    · by_cases h2 : ε ≤ t
      · exact Or.inr h2
      · exact Or.inl (Or.inr ⟨lt_of_not_ge h1, lt_of_not_ge h2⟩)
  calc (1 : ℝ) = μ.real (Set.Ici (0 : ℝ)) := hIciReal.symm
    _ ≤ μ.real ((Set.Icc 0 r ∪ Set.Ioo r ε) ∪ Set.Ici ε) :=
        measureReal_mono hsub (measure_ne_top μ _)
    _ ≤ μ.real (Set.Icc 0 r ∪ Set.Ioo r ε) + μ.real (Set.Ici ε) := measureReal_union_le _ _
    _ ≤ (μ.real (Set.Icc 0 r) + μ.real (Set.Ioo r ε)) + μ.real (Set.Ici ε) := by
        have := measureReal_union_le (μ := μ) (Set.Icc (0 : ℝ) r) (Set.Ioo r ε)
        linarith

end GaloisForLFunctions.RHTower
