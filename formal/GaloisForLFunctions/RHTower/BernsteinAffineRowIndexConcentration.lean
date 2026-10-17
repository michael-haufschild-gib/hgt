import GaloisForLFunctions.HTGeometry.FinitePacketSecondMomentConcentration
import GaloisForLFunctions.RHTower.FiniteBernsteinCoordinatePacketAsymptotic

/-!
# Index concentration of an affine Bernstein row

The modulus of an affine row is a rescaled binomial distribution. Its squared mass, under the
sharp half-order normalization, concentrates at the ratio of the two focal distances.
-/

open Complex Filter Topology
open scoped BigOperators Real unitInterval
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

theorem bernsteinAffineAmplitude_pos (u : ℂ) : 0 < ‖u‖ + ‖1 - u‖ := by
  have h : 1 ≤ ‖u‖ + ‖1 - u‖ := by
    simpa using norm_add_le u (1 - u)
  linarith

/-- The coefficient index selected by the modulus of an affine Bernstein row. -/
def bernsteinAffineOccupation (u : ℂ) : I :=
  ⟨‖u‖ / (‖u‖ + ‖1 - u‖),
    div_nonneg (norm_nonneg _) (bernsteinAffineAmplitude_pos u).le,
    (div_le_one (bernsteinAffineAmplitude_pos u)).mpr
      (le_add_of_nonneg_right (norm_nonneg _))⟩

theorem norm_bernsteinAffineRowCoefficient_eq_binomial
    (u : ℂ) (n : ℕ) (k : Fin (n + 1)) :
    ‖bernsteinAffineRowCoefficient u n k‖ =
      (‖u‖ + ‖1 - u‖) ^ n * bernstein n k (bernsteinAffineOccupation u) := by
  have hB := ne_of_gt (bernsteinAffineAmplitude_pos u)
  have hsub : 1 - ‖u‖ / (‖u‖ + ‖1 - u‖) =
      ‖1 - u‖ / (‖u‖ + ‖1 - u‖) := by field_simp; ring
  have hpow : (‖u‖ + ‖1 - u‖) ^ (k : ℕ) *
      (‖u‖ + ‖1 - u‖) ^ (n - (k : ℕ)) = (‖u‖ + ‖1 - u‖) ^ n := by
    rw [← pow_add, Nat.add_sub_of_le k.is_le]
  rw [bernsteinAffineRowCoefficient, norm_mul, norm_mul, norm_pow, norm_pow,
    Complex.norm_natCast, bernstein_apply]
  change _ = (‖u‖ + ‖1 - u‖) ^ n *
    ((n.choose k : ℝ) * (‖u‖ / (‖u‖ + ‖1 - u‖)) ^ (k : ℕ) *
      (1 - ‖u‖ / (‖u‖ + ‖1 - u‖)) ^ (n - (k : ℕ)))
  rw [hsub, div_pow, div_pow, ← hpow]
  field_simp

theorem bernsteinAffineRow_normalized_square (u : ℂ) (n : ℕ) (k : Fin (n + 1)) :
    Real.sqrt n / ((‖u‖ + ‖1 - u‖) ^ 2) ^ n *
        ‖bernsteinAffineRowCoefficient u n k‖ ^ 2 =
      Real.sqrt n * (bernstein n k (bernsteinAffineOccupation u)) ^ 2 := by
  have hpow : ((‖u‖ + ‖1 - u‖) ^ n) ^ 2 = ((‖u‖ + ‖1 - u‖) ^ 2) ^ n := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [norm_bernsteinAffineRowCoefficient_eq_binomial, mul_pow, hpow]
  field_simp [ne_of_gt (bernsteinAffineAmplitude_pos u)]

theorem bernstein_le_one (n : ℕ) (k : Fin (n + 1)) (p : I) :
    bernstein n k p ≤ 1 := by
  rw [← bernstein.probability n p]
  exact Finset.single_le_sum (fun _ _ => bernstein_nonneg) (Finset.mem_univ k)

theorem bernstein_squared_index_secondMoment_le (n : ℕ) (p : I) :
    (∑ k : Fin (n + 1), Real.sqrt n * (bernstein n k p) ^ 2 *
      dist (bernstein.z k) p ^ 2) ≤
      Real.sqrt n * ((p : ℝ) * (1 - p) / n) := by
  by_cases hn : n = 0
  · subst n
    simp
  calc
    _ ≤ Real.sqrt n * ∑ k : Fin (n + 1),
        ((p : ℝ) - (bernstein.z k : ℝ)) ^ 2 * bernstein n k p := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro k hk
      rw [dist_comm, Subtype.dist_eq, Real.dist_eq, sq_abs]
      have h0 : 0 ≤ bernstein n k p := bernstein_nonneg
      have h1 := bernstein_le_one n k p
      have hsq : (bernstein n k p) ^ 2 ≤ bernstein n k p := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hsq
        (mul_nonneg (Real.sqrt_nonneg (n : ℝ))
          (sq_nonneg ((p : ℝ) - (bernstein.z k : ℝ))))]
    _ = _ := by rw [bernstein.variance hn p]

theorem tendsto_bernstein_squared_index_secondMoment (p : I) :
    Tendsto (fun n : ℕ => ∑ k : Fin (n + 1),
      Real.sqrt n * (bernstein n k p) ^ 2 * dist (bernstein.z k) p ^ 2)
      atTop (nhds 0) := by
  apply squeeze_zero
    (fun n => Finset.sum_nonneg fun k _ => by positivity)
    (fun n => bernstein_squared_index_secondMoment_le n p)
  have hlim := (tendsto_inv_atTop_zero.comp
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)).const_mul
      ((p : ℝ) * (1 - p))
  simp only [Function.comp_def] at hlim
  convert hlim using 1
  · ext n
    by_cases hn : n = 0
    · simp [hn]
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have hs : Real.sqrt (n : ℝ) ≠ 0 := by positivity
    have hsq := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    field_simp [hn0, hs]
    rw [hsq]
    ring
  · simp

theorem tendsto_bernstein_squared_mass {u : ℂ} (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    Tendsto (fun n : ℕ => ∑ k : Fin (n + 1),
      Real.sqrt n * (bernstein n k (bernsteinAffineOccupation u)) ^ 2)
      atTop (nhds (bernsteinAffineRowHalfOrderConstant u)) := by
  have h := tendsto_sqrtNat_mul_bernsteinAffineRowEnergy_div_pow hu0 hu1
  change Tendsto _ _ (nhds (bernsteinAffineRowHalfOrderConstant u)) at h
  convert h using 1
  ext n
  simp_rw [← bernsteinAffineRow_normalized_square u n]
  rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range
    (fun k : ℕ => ‖bernsteinAffineRowCoefficient u n k‖ ^ 2) (n + 1)]
  rw [bernsteinAffineRowEnergy]
  ring

theorem tendsto_bernsteinAffineRow_weighted_error
    {u : ℂ} (hu0 : u ≠ 0) (hu1 : u ≠ 1) {g : I → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hbound : ∀ x, |g x| ≤ M)
    (hg : ContinuousAt g (bernsteinAffineOccupation u)) :
    Tendsto (fun n : ℕ => Real.sqrt n / ((‖u‖ + ‖1 - u‖) ^ 2) ^ n *
      ∑ k : Fin (n + 1), ‖bernsteinAffineRowCoefficient u n k‖ ^ 2 *
        (g (bernstein.z k) - g (bernsteinAffineOccupation u)) ^ 2)
      atTop (nhds 0) := by
  have h := tendsto_finiteWeighted_sq_error_of_secondMoment
    (fun n => (Finset.univ : Finset (Fin (n + 1))))
    (fun n k => Real.sqrt n * (bernstein n k (bernsteinAffineOccupation u)) ^ 2)
    (fun _ k => bernstein.z k) (fun n k _ => by positivity)
    (tendsto_bernstein_squared_mass hu0 hu1)
    (tendsto_bernstein_squared_index_secondMoment (bernsteinAffineOccupation u))
    hM hbound hg
  convert h using 1
  ext n
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← mul_assoc, bernsteinAffineRow_normalized_square]

theorem tendsto_bernsteinAffineRow_weighted_energy
    {u : ℂ} (hu0 : u ≠ 0) (hu1 : u ≠ 1) {g : I → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hbound : ∀ x, |g x| ≤ M)
    (hg : ContinuousAt g (bernsteinAffineOccupation u)) :
    Tendsto (fun n : ℕ => Real.sqrt n / ((‖u‖ + ‖1 - u‖) ^ 2) ^ n *
      ∑ k : Fin (n + 1), ‖bernsteinAffineRowCoefficient u n k‖ ^ 2 *
        g (bernstein.z k))
      atTop (nhds (bernsteinAffineRowHalfOrderConstant u *
        g (bernsteinAffineOccupation u))) := by
  have h := tendsto_finiteWeighted_test_of_secondMoment
    (fun n => (Finset.univ : Finset (Fin (n + 1))))
    (fun n k => Real.sqrt n * (bernstein n k (bernsteinAffineOccupation u)) ^ 2)
    (fun _ k => bernstein.z k) (fun n k _ => by positivity)
    (tendsto_bernstein_squared_mass hu0 hu1)
    (tendsto_bernstein_squared_index_secondMoment (bernsteinAffineOccupation u))
    hM hbound hg
  convert h using 1
  ext n
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← mul_assoc, bernsteinAffineRow_normalized_square]

end
end RHTower
