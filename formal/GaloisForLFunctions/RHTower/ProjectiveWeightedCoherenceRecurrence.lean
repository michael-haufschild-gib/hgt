import GaloisForLFunctions.RHTower.AnisotropicPhaseRecurrence
import GaloisForLFunctions.RHTower.ProjectiveWeightedCoherence

/-!
# Anisotropic projective weighted recurrence

This file joins the anisotropic product-box recurrence with the quadratic
positive-weight phase floor.  One coordinate is a free projective pivot, so
the exact clock cost is the product of the remaining coordinate resolutions.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- Coordinate-dependent phase errors give the corresponding weighted
quadratic coherence floor. -/
theorem nonnegative_weighted_phaseSum_norm_floor_of_anisotropic_approximation
    {d : ℕ} (n : ℕ) (ω : Fin d → ℝ) (w e : Fin d → ℝ)
    (r : Fin d → ℤ) (he : ∀ i, 0 ≤ e i)
    (hw : ∀ i, 0 ≤ w i)
    (hphase : ∀ i,
      |(n : ℝ) * ω i - 2 * Real.pi * r i| ≤ e i) :
    (∑ i, (1 - e i ^ 2 / 2) * w i) ≤
      ‖∑ i, (w i : ℂ) * Complex.exp
        (Complex.I * (((n : ℝ) * ω i : ℝ) : ℂ))‖ := by
  calc
    (∑ i, (1 - e i ^ 2 / 2) * w i) ≤
        ∑ i, ((w i : ℂ) * Complex.exp
          (Complex.I * (((n : ℝ) * ω i : ℝ) : ℂ))).re := by
      apply Finset.sum_le_sum
      intro i _hi
      have hcos := one_sub_sq_phaseError_div_two_le_re_exp_I_mul_real
        ((n : ℝ) * ω i) (e i) (r i) (he i) (hphase i)
      simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, mul_zero, sub_zero, mul_comm] using
          mul_le_mul_of_nonneg_right hcos (hw i)
    _ = (∑ i, (w i : ℂ) * Complex.exp
        (Complex.I * (((n : ℝ) * ω i : ℝ) : ℂ))).re := by
      exact (Complex.re_sum (s := Finset.univ)
        (fun i => (w i : ℂ) * Complex.exp
          (Complex.I * (((n : ℝ) * ω i : ℝ) : ℂ)))).symm
    _ ≤ ‖∑ i, (w i : ℂ) * Complex.exp
        (Complex.I * (((n : ℝ) * ω i : ℝ) : ℂ))‖ :=
      Complex.re_le_norm _

/-- Removing a common pivot phase leaves the weighted phase-sum norm
unchanged. -/
theorem norm_weighted_phaseSum_sub_pivot
    {d : ℕ} (n : ℕ) (ω : Fin d → ℝ) (w : Fin d → ℝ) (k : Fin d) :
    ‖∑ i, (w i : ℂ) * Complex.exp
        (Complex.I * (((n : ℝ) * (ω i - ω k) : ℝ) : ℂ))‖ =
      ‖∑ i, (w i : ℂ) * Complex.exp
        (Complex.I * (((n : ℝ) * ω i : ℝ) : ℂ))‖ := by
  have hterm (i : Fin d) :
      Complex.exp
          (Complex.I * (((n : ℝ) * (ω i - ω k) : ℝ) : ℂ)) =
        Complex.exp
            (-Complex.I * (((n : ℝ) * ω k : ℝ) : ℂ)) *
          Complex.exp
            (Complex.I * (((n : ℝ) * ω i : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [hterm]
  have hfactor :
      (∑ x, (w x : ℂ) *
        (Complex.exp (-Complex.I * (((n : ℝ) * ω k : ℝ) : ℂ)) *
          Complex.exp (Complex.I * (((n : ℝ) * ω x : ℝ) : ℂ)))) =
        Complex.exp (-Complex.I * (((n : ℝ) * ω k : ℝ) : ℂ)) *
          ∑ x, (w x : ℂ) *
            Complex.exp (Complex.I * (((n : ℝ) * ω x : ℝ) : ℂ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _hx
    ring
  rw [hfactor, norm_mul]
  have hunit :
      ‖Complex.exp (-Complex.I * (((n : ℝ) * ω k : ℝ) : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [hunit, one_mul]

/-- **Projective anisotropic recurrence.**  A positive probability packet
recurs with one free pivot coordinate.  The clock pays the product of the
chosen coordinate resolutions, while the weighted quadratic loss omits the
pivot exactly. -/
theorem exists_projective_nonnegative_weighted_phaseSum_recurrence_anisotropic
    {d : ℕ} (ω : Fin d → ℝ) (w : Fin d → ℝ)
    (Q : Fin d → ℕ) (k : Fin d)
    (hQ : ∀ i, 0 < Q i) (hw : ∀ i, 0 ≤ w i)
    (hmass : ∑ i, w i = 1) :
    ∃ n : ℕ, 0 < n ∧ n ≤ ∏ i, Q i ∧
      1 - (∑ i, if i = k then 0 else
          w i * ((2 * Real.pi / (Q i : ℝ)) ^ 2 / 2)) ≤
        ‖∑ i, (w i : ℂ) * Complex.exp
          (Complex.I * (((n : ℝ) * ω i : ℝ) : ℂ))‖ := by
  obtain ⟨n, hn, hnQ, r, hr⟩ :=
    exists_fin_simultaneous_two_pi_phase_approximation_anisotropic
      (fun i => ω i - ω k) Q hQ
  let r' : Fin d → ℤ := fun i => if i = k then 0 else r i
  let e : Fin d → ℝ := fun i =>
    if i = k then 0 else 2 * Real.pi / (Q i : ℝ)
  have he : ∀ i, 0 ≤ e i := by
    intro i
    by_cases hik : i = k
    · simp [e, hik]
    · simp only [e, hik, ↓reduceIte]
      positivity
  have hphase : ∀ i,
      |(n : ℝ) * (ω i - ω k) - 2 * Real.pi * r' i| ≤ e i := by
    intro i
    by_cases hik : i = k
    · subst i
      simp [r', e]
    · simpa only [r', e, hik, ↓reduceIte] using hr i
  have hfloor :=
    nonnegative_weighted_phaseSum_norm_floor_of_anisotropic_approximation
      n (fun i => ω i - ω k) w e r' he hw hphase
  refine ⟨n, hn, hnQ, ?_⟩
  calc
    1 - (∑ i, if i = k then 0 else
          w i * ((2 * Real.pi / (Q i : ℝ)) ^ 2 / 2)) =
        (∑ i, w i) - (∑ i, if i = k then 0 else
          w i * ((2 * Real.pi / (Q i : ℝ)) ^ 2 / 2)) := by rw [hmass]
    _ = ∑ i, (w i - if i = k then 0 else
          w i * ((2 * Real.pi / (Q i : ℝ)) ^ 2 / 2)) := by
      rw [Finset.sum_sub_distrib]
    _ = ∑ i, (1 - e i ^ 2 / 2) * w i := by
      apply Finset.sum_congr rfl
      intro i _hi
      by_cases hik : i = k
      · simp [e, hik]
      · simp only [e, hik, ↓reduceIte]
        ring
    _ ≤ ‖∑ i, (w i : ℂ) * Complex.exp
        (Complex.I * (((n : ℝ) * (ω i - ω k) : ℝ) : ℂ))‖ := hfloor
    _ = ‖∑ i, (w i : ℂ) * Complex.exp
        (Complex.I * (((n : ℝ) * ω i : ℝ) : ℂ))‖ :=
      norm_weighted_phaseSum_sub_pivot n ω w k

end RHTower
