import GaloisForLFunctions.RHTower.ZetaChiExplicitStationaryTerm

open Complex MeasureTheory
open scoped BigOperators
noncomputable section
namespace RHTower

private theorem continuous_chi_log_frequency (x : ℝ) :
    Continuous (fun t : ℝ => zetaChi (linePt t) * bourgainOscillation (t * Real.log x)) := by
  convert continuous_zetaChiCriticalTwistIntegrand (Real.log x) using 1
  funext t
  unfold bourgainOscillation
  congr 1
  congr 1
  push_cast
  ring

private theorem integral_chi_log_finite_sum {ι : Type*}
    (S : Finset ι) (c : ι → ℂ) (x : ι → ℝ) (l u : ℝ) :
    (∫ t in l..u, ∑ j ∈ S, c j *
      (zetaChi (linePt t) * bourgainOscillation (t * Real.log (x j)))) =
      ∑ j ∈ S, c j * ∫ t in l..u, zetaChi (linePt t) *
        bourgainOscillation (t * Real.log (x j)) := by
  rw [intervalIntegral.integral_finsetSum
    (fun j _ => ((continuous_chi_log_frequency (x j)).const_mul (c j)).intervalIntegrable l u)]
  simp_rw [intervalIntegral.integral_const_mul]

/-- A signed physical stationary transform for an arbitrary finite family
of positive frequencies. Rational frequencies retain their additive phase;
all coefficient-weighted remainders are paid. -/
theorem norm_integral_zetaChi_finite_stationary_transform_le {ι : Type*}
    (S : Finset ι) (c : ι → ℂ) (x h : ι → ℝ) (l u : ℝ)
    (hS : ∀ j ∈ S, 8 ≤ 2 * Real.pi * x j ∧ 0 < h j ∧
      h j ≤ (2 * Real.pi * x j) / 2 ∧ (2 * Real.pi * x j) / 2 ≤ l ∧
      l ≤ 2 * Real.pi * x j - h j ∧ 2 * Real.pi * x j + h j ≤ u ∧
      u ≤ 2 * (2 * Real.pi * x j)) :
    ‖(∫ t in l..u, ∑ j ∈ S, c j *
        (zetaChi (linePt t) * bourgainOscillation (t * Real.log (x j)))) -
      ∑ j ∈ S, c j * bourgainOscillation (2 * Real.pi * x j) *
        (Real.sqrt (2 * Real.pi * (2 * Real.pi * x j)) : ℂ)‖ ≤
      ∑ j ∈ S, ‖c j‖ * (78 + 4 * (h j) ^ 4 / (2 * Real.pi * x j) ^ 2 +
        40 * (2 * Real.pi * x j) / h j) := by
  have hsingle (j : ι) (hj : j ∈ S) :
      ‖(∫ t in l..u, zetaChi (linePt t) * bourgainOscillation (t * Real.log (x j))) -
        bourgainOscillation (2 * Real.pi * x j) *
          (Real.sqrt (2 * Real.pi * (2 * Real.pi * x j)) : ℂ)‖ ≤
      78 + 4 * (h j) ^ 4 / (2 * Real.pi * x j) ^ 2 + 40 * (2 * Real.pi * x j) / h j := by
    obtain ⟨h8, hh, hhalf, hl, hlh, hhu, hu⟩ := hS j hj
    have hb := norm_integral_zetaChi_sub_explicit_stationary_le h8 hh hhalf hl hlh hhu hu
    have he : (2 * Real.pi * x j) / (2 * Real.pi) = x j := by field_simp
    simpa only [he] using hb
  have he : (∫ t in l..u, ∑ j ∈ S, c j *
      (zetaChi (linePt t) * bourgainOscillation (t * Real.log (x j)))) -
      ∑ j ∈ S, c j * bourgainOscillation (2 * Real.pi * x j) *
        (Real.sqrt (2 * Real.pi * (2 * Real.pi * x j)) : ℂ) =
      ∑ j ∈ S, c j * ((∫ t in l..u, zetaChi (linePt t) *
        bourgainOscillation (t * Real.log (x j))) -
          bourgainOscillation (2 * Real.pi * x j) *
            (Real.sqrt (2 * Real.pi * (2 * Real.pi * x j)) : ℂ)) := by
    rw [integral_chi_log_finite_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [he]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hsingle j hj) (norm_nonneg _)

/-- Every finite physical family is covered: selected interior saddles
retain their signed main terms, and the entire complement pays the existing
uniform oscillatory bound. No endpoint or unselected term is discarded. -/
theorem norm_integral_zetaChi_selected_stationary_transform_le {ι : Type*} [DecidableEq ι]
    (R S : Finset ι) (hsub : S ⊆ R) (c : ι → ℂ) (x h : ι → ℝ)
    {T : ℝ} (hT : 4 ≤ T)
    (hS : ∀ j ∈ S, 8 ≤ 2 * Real.pi * x j ∧ 0 < h j ∧
      h j ≤ (2 * Real.pi * x j) / 2 ∧ (2 * Real.pi * x j) / 2 ≤ T ∧
      T ≤ 2 * Real.pi * x j - h j ∧ 2 * Real.pi * x j + h j ≤ 2 * T ∧
      2 * T ≤ 2 * (2 * Real.pi * x j)) :
    ‖(∫ t in T..(2 * T), ∑ j ∈ R, c j *
        (zetaChi (linePt t) * bourgainOscillation (t * Real.log (x j)))) -
      ∑ j ∈ S, c j * bourgainOscillation (2 * Real.pi * x j) *
        (Real.sqrt (2 * Real.pi * (2 * Real.pi * x j)) : ℂ)‖ ≤
      (∑ j ∈ S, ‖c j‖ * (78 + 4 * (h j) ^ 4 / (2 * Real.pi * x j) ^ 2 +
        40 * (2 * Real.pi * x j) / h j)) +
      (6 / Real.sqrt (1 / (100 * T))) * ∑ j ∈ R \ S, ‖c j‖ := by
  let J (U : Finset ι) : ℂ := ∫ t in T..(2 * T), ∑ j ∈ U, c j *
    (zetaChi (linePt t) * bourgainOscillation (t * Real.log (x j)))
  let M : ℂ := ∑ j ∈ S, c j * bourgainOscillation (2 * Real.pi * x j) *
    (Real.sqrt (2 * Real.pi * (2 * Real.pi * x j)) : ℂ)
  have hsel := norm_integral_zetaChi_finite_stationary_transform_le S c x h T (2 * T) hS
  have hsplit : J R = J (R \ S) + J S := by
    dsimp only [J]
    simp_rw [integral_chi_log_finite_sum]
    exact (Finset.sum_sdiff hsub).symm
  have htail : ‖J (R \ S)‖ ≤
      (6 / Real.sqrt (1 / (100 * T))) * ∑ j ∈ R \ S, ‖c j‖ := by
    dsimp only [J]
    rw [integral_chi_log_finite_sum]
    apply (norm_sum_le _ _).trans
    have hbound (j : ι) :
        ‖∫ t in T..(2 * T), zetaChi (linePt t) * bourgainOscillation (t * Real.log (x j))‖ ≤
          6 / Real.sqrt (1 / (100 * T)) := by
      have he : (fun t : ℝ => zetaChi (linePt t) * bourgainOscillation (t * Real.log (x j))) =
          fun t : ℝ => zetaChi (linePt t) * Complex.exp (((Real.log (x j) * t : ℝ) : ℂ) * I) := by
        funext t
        unfold bourgainOscillation
        congr 1
        congr 1
        push_cast
        ring
      rw [he]
      exact norm_integral_zetaChi_line_mul_exp_le hT (Real.log (x j))
    calc
      _ ≤ ∑ j ∈ R \ S, ‖c j‖ * (6 / Real.sqrt (1 / (100 * T))) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hbound j) (norm_nonneg _)
      _ = _ := by rw [← Finset.sum_mul]; ring
  change ‖J R - M‖ ≤ _
  rw [hsplit]
  calc
    _ = ‖J (R \ S) + (J S - M)‖ := by congr 1; ring
    _ ≤ ‖J (R \ S)‖ + ‖J S - M‖ := norm_add_le _ _
    _ ≤ (6 / Real.sqrt (1 / (100 * T))) * (∑ j ∈ R \ S, ‖c j‖) +
        (∑ j ∈ S, ‖c j‖ * (78 + 4 * (h j) ^ 4 / (2 * Real.pi * x j) ^ 2 +
          40 * (2 * Real.pi * x j) / h j)) := add_le_add htail hsel
    _ = _ := by ring

/-- The rational saddle phase is periodic in the numerator modulo its
positive denominator. This phase cannot be discarded from cross terms. -/
theorem bourgainOscillation_rational_saddle_add_denominator (m q : ℕ) (hq : 0 < q) :
    bourgainOscillation (2 * Real.pi * (((m + q : ℕ) : ℝ) / (q : ℝ))) =
      bourgainOscillation (2 * Real.pi * ((m : ℝ) / (q : ℝ))) := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have he : 2 * Real.pi * (((m + q : ℕ) : ℝ) / (q : ℝ)) =
      2 * Real.pi * ((m : ℝ) / (q : ℝ)) + 2 * Real.pi := by
    push_cast
    field_simp
  rw [he]
  unfold bourgainOscillation
  rw [Complex.ofReal_add, mul_add, Complex.exp_add]
  have hperiod : Complex.exp (I * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
    have he : I * ((2 * Real.pi : ℝ) : ℂ) = (1 : ℂ) * (2 * (Real.pi : ℂ) * I) := by
      push_cast
      ring
    rw [he]
    simpa only [Nat.cast_one] using Complex.exp_nat_mul_two_pi_mul_I 1
  rw [hperiod, mul_one]

end RHTower
