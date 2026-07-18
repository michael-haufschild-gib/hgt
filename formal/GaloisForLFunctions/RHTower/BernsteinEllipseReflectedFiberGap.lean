import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Choose.Bounds
import GaloisForLFunctions.RHTower.BernsteinAffineRowCrossMoment
import GaloisForLFunctions.RHTower.BernsteinEllipseRigidity

/-!
# Complete mixed-mode gap on a Bernstein ellipse

The ellipse phase and amplitude determine a nonreal Bernstein node up to the reflected complement
`u ↦ 1 - conj u`.  Different phases have a strict gap by compactness.  The remaining reflected
fibre has an exact central-binomial cross moment, whose exponential base is strictly below the
diagonal base unless the two reflected nodes coincide.  This removes the earlier half-disk
restriction from the quadratic packet theorem.
-/

open Complex
open scoped BigOperators Real ComplexConjugate

namespace RHTower

noncomputable section

/-- Equality of the two focal distances places a point on the perpendicular bisector and hence
fixes it under reflected complementation. -/
theorem eq_one_sub_conj_of_norm_eq_norm_one_sub
    {u : ℂ} (h : ‖u‖ = ‖1 - u‖) :
    u = 1 - conj u := by
  apply Complex.ext
  · have hsq := congrArg (fun x : ℝ => x ^ 2) h
    rw [Complex.sq_norm, Complex.sq_norm] at hsq
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re,
      Complex.sub_im, Complex.one_im, map_sub, map_one, Complex.conj_re] at hsq ⊢
    nlinarith
  · simp

/-- The reflected complement has the reversed conjugate Bernstein row. -/
lemma conj_bernsteinAffineRowCoefficient_one_sub_conj
    (u : ℂ) (n k : ℕ) :
    conj (bernsteinAffineRowCoefficient (1 - conj u) n k) =
      (n.choose k : ℂ) * (1 - u) ^ k * u ^ (n - k) := by
  simp only [bernsteinAffineRowCoefficient, map_mul, map_pow, map_sub, map_one,
    map_natCast, map_star, star_star]
  ring

/-- Exact central-binomial formula for the sole nontrivial equal-phase fibre. -/
theorem reflectedBernsteinCrossMoment_one_sub_conj
    (u : ℂ) (n : ℕ) :
    reflectedBernsteinCrossMoment u (1 - conj u) n =
      (Nat.centralBinom n : ℂ) * (u * (1 - u)) ^ n := by
  rw [reflectedBernsteinCrossMoment_eq_sum]
  calc
    (∑ k ∈ Finset.range (n + 1),
        bernsteinAffineRowCoefficient u n k *
          conj (bernsteinAffineRowCoefficient (1 - conj u) n k)) =
        ∑ k ∈ Finset.range (n + 1),
          ((n.choose k : ℂ) ^ 2 * (u * (1 - u)) ^ n) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      rw [conj_bernsteinAffineRowCoefficient_one_sub_conj]
      simp only [bernsteinAffineRowCoefficient]
      rw [mul_pow]
      calc
        ((n.choose k : ℂ) * u ^ k * (1 - u) ^ (n - k)) *
              ((n.choose k : ℂ) * (1 - u) ^ k * u ^ (n - k)) =
            (n.choose k : ℂ) ^ 2 *
              (u ^ k * u ^ (n - k)) *
              ((1 - u) ^ (n - k) * (1 - u) ^ k) := by ring
        _ = (n.choose k : ℂ) ^ 2 * (u ^ n * (1 - u) ^ n) := by
          rw [← pow_add, ← pow_add]
          congr 2 <;> omega
    _ = (∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) ^ 2) *
          (u * (1 - u)) ^ n := by rw [Finset.sum_mul]
    _ = (Nat.centralBinom n : ℂ) * (u * (1 - u)) ^ n := by
      congr 1
      rw [← Nat.cast_pow, ← Nat.cast_sum, Nat.sum_range_choose_sq,
        Nat.centralBinom_eq_two_mul_choose]

/-- The central binomial coefficient has the elementary exponential envelope `4^n`. -/
theorem centralBinom_le_four_pow (n : ℕ) :
    Nat.centralBinom n ≤ 4 ^ n := by
  rw [Nat.centralBinom_eq_two_mul_choose]
  calc
    (2 * n).choose n ≤ 2 ^ (2 * n) := Nat.choose_le_two_pow _ _
    _ = 4 ^ n := by
      rw [show 2 * n = n * 2 by omega, pow_mul]
      norm_num

/-- The exact reflected-fibre moment is controlled by the geometric base
`4 * |u| * |1-u|`. -/
theorem norm_reflectedBernsteinCrossMoment_one_sub_conj_le
    (u : ℂ) (n : ℕ) :
    ‖reflectedBernsteinCrossMoment u (1 - conj u) n‖ ≤
      (4 * ‖u‖ * ‖1 - u‖) ^ n := by
  rw [reflectedBernsteinCrossMoment_one_sub_conj, norm_mul, norm_pow,
    norm_mul, Complex.norm_natCast]
  have hcast : (Nat.centralBinom n : ℝ) ≤ (4 : ℝ) ^ n := by
    exact_mod_cast centralBinom_le_four_pow n
  calc
    (Nat.centralBinom n : ℝ) * (‖u‖ * ‖1 - u‖) ^ n ≤
        (4 : ℝ) ^ n * (‖u‖ * ‖1 - u‖) ^ n :=
      mul_le_mul_of_nonneg_right hcast (pow_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) n)
    _ = (4 * ‖u‖ * ‖1 - u‖) ^ n := by ring

/-- A distinct reflected pair has a strict cross base below the squared common amplitude. -/
theorem four_mul_norm_mul_norm_one_sub_lt_amplitude_sq_of_ne_reflection
    {u : ℂ} (hreflect : u ≠ 1 - conj u) :
    4 * ‖u‖ * ‖1 - u‖ < (‖u‖ + ‖1 - u‖) ^ 2 := by
  have hnorm : ‖u‖ ≠ ‖1 - u‖ := fun h =>
    hreflect (eq_one_sub_conj_of_norm_eq_norm_one_sub h)
  have hsquare : 0 < (‖u‖ - ‖1 - u‖) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hnorm)
  nlinarith

/-- **Complete equal-amplitude mixed-mode gap.**  Distinct nonreal nodes of one Bernstein ellipse
always have an exponentially strict quadratic cross gap.  Different phases use compactness; the
only equal-phase fibre uses the exact reflected central-binomial identity. -/
theorem exists_reflectedBernsteinCrossMoment_gap_of_distinct_equalAmplitude
    {u v : ℂ} {B : ℝ}
    (huim : u.im ≠ 0) (hvim : v.im ≠ 0)
    (huB : ‖u‖ + ‖1 - u‖ = B)
    (hvB : ‖v‖ + ‖1 - v‖ = B)
    (huv : u ≠ v) :
    ∃ gamma : ℝ, 0 ≤ gamma ∧ gamma < B ^ 2 ∧
      ∀ n : ℕ, ‖reflectedBernsteinCrossMoment u v n‖ ≤ gamma ^ n := by
  by_cases hphase : bernsteinEllipsePhase u = bernsteinEllipsePhase v
  · rcases eq_or_eq_one_sub_conj_of_bernsteinEllipsePhase_eq_of_amplitude_eq
        huim hvim hphase.symm (hvB.trans huB.symm) with heq | hreflect
    · exact (huv heq.symm).elim
    · subst v
      let gamma : ℝ := 4 * ‖u‖ * ‖1 - u‖
      refine ⟨gamma, by positivity, ?_, ?_⟩
      · rw [← huB]
        exact four_mul_norm_mul_norm_one_sub_lt_amplitude_sq_of_ne_reflection
          (fun h => huv h.symm)
      · intro n
        exact norm_reflectedBernsteinCrossMoment_one_sub_conj_le u n
  · obtain ⟨gamma, hgamma0, hgamma, hpoint⟩ :=
      exists_uniform_reflectedBernsteinProduct_gap_of_phase_ne
        huim hvim huB hvB hphase
    exact ⟨gamma, hgamma0, hgamma,
      norm_reflectedBernsteinCrossMoment_le_pow hpoint⟩

end

end RHTower
