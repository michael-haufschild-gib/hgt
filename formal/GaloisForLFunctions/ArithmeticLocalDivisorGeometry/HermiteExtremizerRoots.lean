import GaloisForLFunctions.ArithmeticLocalDivisorGeometry.HermiteExtremizers

/-!+# The exact real divisor of a Hermite extremizer

The two outer critical roots are exactly double. Removing their squared quadratic pair
leaves an even polynomial strictly positive on the whole real axis.
-/

open Polynomial
open GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.ArithmeticLocalDivisorGeometry
noncomputable section

/-- A stationary polynomial root with nonzero second derivative is exactly double. -/
private theorem rootMultiplicity_eq_two_of_second_derivative
    {p : ℝ[X]} {x : ℝ} (hp : p.eval x = 0) (hd : (derivative p).eval x = 0)
    (hdd : (derivative (derivative p)).eval x ≠ 0) : p.rootMultiplicity x = 2 := by
  have hpne : p ≠ 0 := by
    intro h
    apply hdd
    simp only [h, derivative_zero, eval_zero]
  have hdne : derivative p ≠ 0 := by
    intro h
    apply hdd
    simp only [h, derivative_zero, eval_zero]
  have hlo := (one_lt_rootMultiplicity_iff_isRoot hpne).mpr ⟨hp, hd⟩
  have hhi : ¬ 1 < (derivative p).rootMultiplicity x := by
    intro h
    exact hdd ((one_lt_rootMultiplicity_iff_isRoot hdne).mp h).2
  have he := derivative_rootMultiplicity_of_root (show p.IsRoot x from hp)
  omega

theorem hermiteExtremizer_derivative_eval_edge (m : ℕ) :
    (derivative (hermiteExtremizer m)).eval (hermiteEdge (2 * m + 2)) = 0 := by
  rw [hermiteExtremizer, derivative_sub, derivative_C, sub_zero,
    show 2 * m + 4 = (2 * m + 3) + 1 by omega, derivative_hermiteReal_succ,
    eval_mul, eval_C]
  rw [show 2 * m + 3 = (2 * m + 2) + 1 by omega, hermiteEdge_isRoot, mul_zero]

theorem hermiteExtremizer_second_derivative_pos (m : ℕ) {x : ℝ}
    (hx : (hermiteExtremizer m).eval x = 0) :
    0 < (derivative (derivative (hermiteExtremizer m))).eval x := by
  have hd : derivative (derivative (hermiteExtremizer m)) =
      C ((2 * m + 4 : ℝ) * (2 * m + 3)) * hermiteReal (2 * m + 2) := by
    rw [hermiteExtremizer, derivative_sub, derivative_C, sub_zero,
      show 2 * m + 4 = (2 * m + 3) + 1 by omega, derivative_hermiteReal_succ,
      derivative_C_mul, show 2 * m + 3 = (2 * m + 2) + 1 by omega,
      derivative_hermiteReal_succ, ← mul_assoc, ← map_mul]
    push_cast
    ring
  have he : (-1 : ℝ) ^ (2 * m + 2) = 1 := by simp [pow_add, pow_mul]
  rcases (hermiteExtremizer_eval_eq_zero_iff m x).mp hx with rfl | rfl
  · simpa only [hermiteExtremizer, derivative_sub, derivative_C, sub_zero]
      using hermite_second_derivative_edge_pos (2 * m + 2)
  · rw [hd, eval_mul, eval_C, eval_neg_hermiteReal, he, one_mul]
    exact mul_pos (mul_pos (by positivity) (by positivity))
      (hermite_eval_pos_at_edge (le_refl _))

/-- Every real root of the extremizer has multiplicity exactly two. -/
theorem hermiteExtremizer_rootMultiplicity (m : ℕ) {x : ℝ}
    (hx : (hermiteExtremizer m).eval x = 0) :
    (hermiteExtremizer m).rootMultiplicity x = 2 := by
  have hmin : IsLocalMin (hermiteExtremizer m).eval x :=
    Filter.Eventually.of_forall fun y => by rw [hx]; exact hermiteExtremizer_nonneg m y
  exact rootMultiplicity_eq_two_of_second_derivative hx
    (hmin.hasDerivAt_eq_zero ((hermiteExtremizer m).hasDerivAt x))
    (hermiteExtremizer_second_derivative_pos m hx).ne'

private theorem squared_pair_dvd {p : ℝ[X]} {h : ℝ} (hh : 0 < h) (hp : p ≠ 0)
    (hpos : p.rootMultiplicity h = 2) (hneg : p.rootMultiplicity (-h) = 2) :
    (X ^ 2 - C (h ^ 2)) ^ 2 ∣ p := by
  have hc : IsCoprime (X - C h) (X - C (-h)) :=
    isCoprime_X_sub_C_of_isUnit_sub (isUnit_iff_ne_zero.mpr (by linarith only [hh]))
  have h1 : (X - C h) ^ 2 ∣ p := (le_rootMultiplicity_iff hp).mp (by rw [hpos])
  have h2 : (X - C (-h)) ^ 2 ∣ p := (le_rootMultiplicity_iff hp).mp (by rw [hneg])
  have hf : (X - C h) ^ 2 * (X - C (-h)) ^ 2 = (X ^ 2 - C (h ^ 2)) ^ 2 := by
    rw [map_neg, map_pow]
    ring
  rw [← hf]
  exact hc.pow.mul_dvd h1 h2

private theorem squared_pair_second_derivative (h x : ℝ) (q : ℝ[X]) (hx : x ^ 2 = h ^ 2) :
    (derivative (derivative ((X ^ 2 - C (h ^ 2)) ^ 2 * q))).eval x =
      8 * x ^ 2 * q.eval x := by
  simp only [derivative_mul, derivative_add, derivative_sub, derivative_pow,
    derivative_C, derivative_X, derivative_one, derivative_zero, derivative_C_mul,
    Nat.reduceSub, pow_one, pow_zero, mul_one, mul_zero, zero_mul, sub_zero,
    add_zero, zero_add, eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X,
    Nat.cast_ofNat, map_ofNat]
  rw [hx]
  ring

/-- The exact squared root pair has an even, everywhere strictly positive cofactor. -/
theorem hermiteExtremizer_positive_cofactor (m : ℕ) :
    ∃ q : ℝ[X], hermiteExtremizer m =
      (X ^ 2 - C (hermiteEdge (2 * m + 2) ^ 2)) ^ 2 * q ∧
      (∀ x : ℝ, 0 < q.eval x) ∧ (∀ x : ℝ, q.eval (-x) = q.eval x) ∧
      q.natDegree = 2 * m := by
  let h := hermiteEdge (2 * m + 2)
  have hh : 0 < h := hermiteEdge_pos (by omega)
  have hr : (hermiteExtremizer m).eval h = 0 := hermiteExtremizer_eval_edge m
  have hn : (hermiteExtremizer m).eval (-h) = 0 := by
    rw [hermiteExtremizer_eval_neg, hr]
  obtain ⟨q, hq⟩ := squared_pair_dvd hh (hermiteExtremizer_ne_zero m)
    (hermiteExtremizer_rootMultiplicity m hr) (hermiteExtremizer_rootMultiplicity m hn)
  have hqne : q ≠ 0 := by
    intro hz
    exact hermiteExtremizer_ne_zero m (by rw [hq, hz, mul_zero])
  have hb : ((X : ℝ[X]) ^ 2 - C (h ^ 2)) ^ 2 ≠ 0 := by
    intro hz
    exact hermiteExtremizer_ne_zero m (by rw [hq, hz, zero_mul])
  have hpositive (x : ℝ) : 0 < q.eval x := by
    by_cases hx : x ^ 2 = h ^ 2
    · have hroot : (hermiteExtremizer m).eval x = 0 := by
        rw [hq]
        simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, hx, sub_self,
          zero_pow (by omega : (2 : ℕ) ≠ 0), zero_mul]
      have hd := hermiteExtremizer_second_derivative_pos m hroot
      rw [hq, squared_pair_second_derivative h x q hx] at hd
      exact (mul_pos_iff_of_pos_left (by rw [hx]; positivity : 0 < 8 * x ^ 2)).mp hd
    · have hroot : (hermiteExtremizer m).eval x ≠ 0 := by
        intro hz
        rcases (hermiteExtremizer_eval_eq_zero_iff m x).mp hz with he | he
        · exact hx (by rw [he])
        · exact hx (by rw [he, neg_sq])
      have hp := lt_of_le_of_ne (hermiteExtremizer_nonneg m x) hroot.symm
      rw [hq, eval_mul, eval_pow, eval_sub, eval_X, eval_C] at hp
      exact (mul_pos_iff_of_pos_left (sq_pos_of_ne_zero (sub_ne_zero.mpr hx))).mp hp
  have heven : q.comp (-X) = q := by
    have hp : (hermiteExtremizer m).comp (-X) = hermiteExtremizer m := by
      apply Polynomial.funext
      intro x
      simpa only [eval_comp, eval_neg, eval_X] using hermiteExtremizer_eval_neg m x
    have hbe : (((X : ℝ[X]) ^ 2 - C (h ^ 2)) ^ 2).comp (-X) =
        (X ^ 2 - C (h ^ 2)) ^ 2 := by
      simp only [pow_comp, sub_comp, X_comp, C_comp, neg_sq]
    rw [hq, mul_comp, hbe] at hp
    exact mul_left_cancel₀ hb hp
  refine ⟨q, hq, hpositive, ?_, ?_⟩
  · intro x
    have he := congrArg (fun p : ℝ[X] => p.eval x) heven
    simpa only [eval_comp, eval_neg, eval_X] using he
  · have hd := hermiteExtremizer_degree m
    rw [hq, natDegree_mul hb hqne, natDegree_pow, natDegree_sub_C, natDegree_X_pow] at hd
    omega

/-- Positive dilation preserves the strict quadratic minima at both real roots. -/
theorem scaledHermiteExtremizer_second_derivative_pos {r : ℝ} (hr : 0 < r)
    (m : ℕ) {x : ℝ} (hx : (scaledHermiteExtremizer r m).eval x = 0) :
    0 < (derivative (derivative (scaledHermiteExtremizer r m))).eval x := by
  have hroot : (hermiteExtremizer m).eval (r⁻¹ * x) = 0 := by
    simp only [scaledHermiteExtremizer, eval_mul, eval_C, eval_comp, eval_X] at hx
    exact (mul_eq_zero.mp hx).resolve_left (pow_ne_zero _ hr.ne')
  have hd : (derivative (derivative (scaledHermiteExtremizer r m))).eval x =
      r ^ (2 * m + 4) * (r⁻¹ * (r⁻¹ *
        (derivative (derivative (hermiteExtremizer m))).eval (r⁻¹ * x))) := by
    simp only [scaledHermiteExtremizer, derivative_C_mul, derivative_comp,
      derivative_X, mul_one, eval_mul, eval_C, eval_comp, eval_X]
  rw [hd]
  exact mul_pos (pow_pos hr _) (mul_pos (inv_pos.mpr hr)
    (mul_pos (inv_pos.mpr hr) (hermiteExtremizer_second_derivative_pos m hroot)))

/-- At every positive Gaussian scale the two real roots remain exactly double. -/
theorem scaledHermiteExtremizer_rootMultiplicity {r : ℝ} (hr : 0 < r)
    (m : ℕ) {x : ℝ} (hx : (scaledHermiteExtremizer r m).eval x = 0) :
    (scaledHermiteExtremizer r m).rootMultiplicity x = 2 := by
  have hmin : IsLocalMin (scaledHermiteExtremizer r m).eval x :=
    Filter.Eventually.of_forall fun y => by rw [hx]; exact scaledHermiteExtremizer_nonneg hr m y
  exact rootMultiplicity_eq_two_of_second_derivative hx
    (hmin.hasDerivAt_eq_zero ((scaledHermiteExtremizer r m).hasDerivAt x))
    (scaledHermiteExtremizer_second_derivative_pos hr m hx).ne'

/-- The scaled extremizer has an exact squared-pair divisor and positive even cofactor. -/
theorem scaledHermiteExtremizer_positive_cofactor {r : ℝ} (hr : 0 < r) (m : ℕ) :
    ∃ q : ℝ[X], scaledHermiteExtremizer r m =
      (X ^ 2 - C ((r * hermiteEdge (2 * m + 2)) ^ 2)) ^ 2 * q ∧
      (∀ x : ℝ, 0 < q.eval x) ∧ (∀ x : ℝ, q.eval (-x) = q.eval x) ∧
      q.natDegree = 2 * m := by
  obtain ⟨q, hq, hp, he, hd⟩ := hermiteExtremizer_positive_cofactor m
  refine ⟨C (r ^ (2 * m)) * q.comp (C r⁻¹ * X), ?_, ?_, ?_, ?_⟩
  · apply Polynomial.funext
    intro x
    simp only [scaledHermiteExtremizer, hq, eval_mul, eval_C, eval_comp, eval_pow,
      eval_sub, eval_X]
    rw [pow_add]
    field_simp
    ring
  · intro x
    simp only [eval_mul, eval_C, eval_comp, eval_X]
    exact mul_pos (pow_pos hr _) (hp _)
  · intro x
    simp only [eval_mul, eval_C, eval_comp, eval_X, mul_neg, he]
  · rw [natDegree_C_mul (pow_ne_zero _ hr.ne'), natDegree_comp,
      natDegree_C_mul (inv_ne_zero hr.ne'), natDegree_X, mul_one, hd]

end
end GaloisForLFunctions.ArithmeticLocalDivisorGeometry
