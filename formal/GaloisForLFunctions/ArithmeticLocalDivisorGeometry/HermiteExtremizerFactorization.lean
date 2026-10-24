import GaloisForLFunctions.ArithmeticLocalDivisorGeometry.HermiteExtremizers

/-!
# The exact real divisor of the Hermite extremizer

Both boundary roots have multiplicity two. Removing their squared quadratic factor leaves
a monic even polynomial strictly positive everywhere on the real axis.
-/

open Polynomial
open GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.ArithmeticLocalDivisorGeometry
noncomputable section

private theorem rootMultiplicity_eq_two {p : ℝ[X]} {x : ℝ} (hp : p ≠ 0)
    (hx : p.eval x = 0) (hd : (derivative p).eval x = 0)
    (hdd : (derivative (derivative p)).eval x ≠ 0) : rootMultiplicity x p = 2 := by
  have hlt := (one_lt_rootMultiplicity_iff_isRoot hp).mpr ⟨hx, hd⟩
  have hdp : derivative p ≠ 0 := by
    intro he
    apply hdd
    rw [he, derivative_zero, eval_zero]
  have he := derivative_rootMultiplicity_of_root (show p.IsRoot x from hx)
  by_contra hn
  have hlt' : 1 < rootMultiplicity x (derivative p) := by omega
  exact hdd ((one_lt_rootMultiplicity_iff_isRoot hdp).mp hlt').2

theorem derivative_hermiteExtremizer (m : ℕ) :
    derivative (hermiteExtremizer m) = derivative (hermiteReal (2 * m + 4)) := by
  simp only [hermiteExtremizer, derivative_sub, derivative_C, sub_zero]

theorem hermiteExtremizer_derivative_eval_edge (m : ℕ) :
    (derivative (hermiteExtremizer m)).eval (hermiteEdge (2 * m + 2)) = 0 := by
  rw [derivative_hermiteExtremizer, show 2 * m + 4 = (2 * m + 2 + 1) + 1 by omega,
    derivative_hermiteReal_succ, eval_mul, eval_C, hermiteEdge_isRoot, mul_zero]

theorem hermiteExtremizer_second_derivative_edge_pos (m : ℕ) :
    0 < (derivative (derivative (hermiteExtremizer m))).eval (hermiteEdge (2 * m + 2)) := by
  rw [derivative_hermiteExtremizer]
  exact hermite_second_derivative_edge_pos (2 * m + 2)

theorem hermiteExtremizer_derivative_eval_neg_edge (m : ℕ) :
    (derivative (hermiteExtremizer m)).eval (-hermiteEdge (2 * m + 2)) = 0 := by
  rw [derivative_hermiteExtremizer, show 2 * m + 4 = (2 * m + 2 + 1) + 1 by omega,
    derivative_hermiteReal_succ, eval_mul, eval_C, eval_neg_hermiteReal,
    hermiteEdge_isRoot, mul_zero, mul_zero]

theorem hermiteExtremizer_second_derivative_neg_edge_pos (m : ℕ) :
    0 < (derivative (derivative (hermiteExtremizer m))).eval (-hermiteEdge (2 * m + 2)) := by
  have he : (-1 : ℝ) ^ (2 * m + 2) = 1 := by simp [pow_add, pow_mul]
  have heval : (derivative (derivative (hermiteExtremizer m))).eval (-hermiteEdge (2 * m + 2)) =
      (derivative (derivative (hermiteExtremizer m))).eval (hermiteEdge (2 * m + 2)) := by
    simp only [derivative_hermiteExtremizer,
      show 2 * m + 4 = (2 * m + 2 + 1) + 1 by omega,
      derivative_hermiteReal_succ, derivative_C_mul, eval_mul, eval_C,
      eval_neg_hermiteReal, he, one_mul]
  rw [heval]
  exact hermiteExtremizer_second_derivative_edge_pos m

/-- The positive and negative boundary roots are both exactly double. -/
theorem hermiteExtremizer_rootMultiplicity (m : ℕ) :
    rootMultiplicity (hermiteEdge (2 * m + 2)) (hermiteExtremizer m) = 2 ∧
    rootMultiplicity (-hermiteEdge (2 * m + 2)) (hermiteExtremizer m) = 2 := by
  constructor
  · exact rootMultiplicity_eq_two (hermiteExtremizer_ne_zero m)
      (hermiteExtremizer_eval_edge m) (hermiteExtremizer_derivative_eval_edge m)
      (hermiteExtremizer_second_derivative_edge_pos m).ne'
  · exact rootMultiplicity_eq_two (hermiteExtremizer_ne_zero m)
      (by rw [hermiteExtremizer_eval_neg, hermiteExtremizer_eval_edge])
      (hermiteExtremizer_derivative_eval_neg_edge m)
      (hermiteExtremizer_second_derivative_neg_edge_pos m).ne'

private theorem opposite_linear_factors_coprime {h : ℝ} (hh : 0 < h) :
    IsCoprime (X - C h : ℝ[X]) (X - C (-h)) := by
  refine ⟨C (-(2 * h)⁻¹), C ((2 * h)⁻¹), ?_⟩
  calc
    _ = C ((2 * h)⁻¹ * (2 * h)) := by
      simp only [map_mul, map_neg, map_ofNat]
      ring
    _ = 1 := by rw [inv_mul_cancel₀ (by positivity), map_one]

private theorem opposite_linear_square_product (h : ℝ) :
    (X - C h : ℝ[X]) ^ 2 * (X - C (-h)) ^ 2 = (X ^ 2 - C (h ^ 2)) ^ 2 := by
  simp only [map_neg, map_pow]
  ring

private theorem second_derivative_squared_pair_eval (h : ℝ) (q : ℝ[X]) :
    (derivative (derivative ((X ^ 2 - C (h ^ 2)) ^ 2 * q))).eval h =
      8 * h ^ 2 * q.eval h := by
  simp [derivative_mul, derivative_pow, derivative_sub, derivative_C,
    derivative_X, eval_mul, eval_add, eval_pow, eval_sub]
  ring

/-- The extremizer's remaining cofactor is monic, even, and strictly positive on the real line. -/
theorem hermiteExtremizer_positive_cofactor (m : ℕ) :
    ∃ q : ℝ[X], q.Monic ∧ q.natDegree = 2 * m ∧
      (∀ x : ℝ, q.eval (-x) = q.eval x) ∧ (∀ x : ℝ, 0 < q.eval x) ∧
      hermiteExtremizer m = (X ^ 2 - C (hermiteEdge (2 * m + 2) ^ 2)) ^ 2 * q := by
  let h := hermiteEdge (2 * m + 2)
  have hh : 0 < h := hermiteEdge_pos (by omega)
  have hd₁ : (X - C h : ℝ[X]) ^ 2 ∣ hermiteExtremizer m := by
    rw [← (hermiteExtremizer_rootMultiplicity m).1]
    exact pow_rootMultiplicity_dvd _ _
  have hd₂ : (X - C (-h) : ℝ[X]) ^ 2 ∣ hermiteExtremizer m := by
    rw [← (hermiteExtremizer_rootMultiplicity m).2]
    exact pow_rootMultiplicity_dvd _ _
  obtain ⟨q, hq⟩ := ((opposite_linear_factors_coprime hh).pow).mul_dvd hd₁ hd₂
  rw [opposite_linear_square_product] at hq
  have hbmonic : ((X ^ 2 - C (h ^ 2)) ^ 2 : ℝ[X]).Monic := by
    rw [← opposite_linear_square_product]
    exact ((monic_X_sub_C h).pow 2).mul ((monic_X_sub_C (-h)).pow 2)
  have hmonic : q.Monic := by
    have hc := (hermiteExtremizer_monic m).leadingCoeff
    rw [hq, leadingCoeff_mul, hbmonic.leadingCoeff, one_mul] at hc
    exact hc
  have hdegree : q.natDegree = 2 * m := by
    have hd := hermiteExtremizer_degree m
    rw [hq, natDegree_mul hbmonic.ne_zero hmonic.ne_zero,
      ← opposite_linear_square_product, natDegree_mul
        ((monic_X_sub_C h).pow 2).ne_zero ((monic_X_sub_C (-h)).pow 2).ne_zero,
      natDegree_pow, natDegree_pow] at hd
    simp only [natDegree_X_sub_C, mul_one] at hd
    omega
  have hrootval : 0 < q.eval h := by
    have hv := hermiteExtremizer_second_derivative_edge_pos m
    rw [hq, second_derivative_squared_pair_eval] at hv
    exact (mul_pos_iff_of_pos_left (by positivity : 0 < 8 * h ^ 2)).mp hv
  have hnegrootval : 0 < q.eval (-h) := by
    have hv := hermiteExtremizer_second_derivative_neg_edge_pos m
    have hfac : hermiteExtremizer m = (X ^ 2 - C ((-h) ^ 2)) ^ 2 * q := by
      simpa only [neg_sq] using hq
    rw [hfac, second_derivative_squared_pair_eval] at hv
    exact (mul_pos_iff_of_pos_left (by positivity : 0 < 8 * (-h) ^ 2)).mp hv
  have hpos : ∀ x : ℝ, 0 < q.eval x := by
    intro x
    apply zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg
    · intro y hy
      have hz : (hermiteExtremizer m).eval y = 0 := by
        rw [hq, eval_mul, hy, mul_zero]
      rcases (hermiteExtremizer_eval_eq_zero_iff m y).mp hz with he | he
      · exact ((hrootval.ne') (by simpa only [he] using hy)).elim
      · exact ((hnegrootval.ne') (by simpa only [he] using hy)).elim
    · rw [hmonic.leadingCoeff]; norm_num
  have heven : ∀ x : ℝ, q.eval (-x) = q.eval x := by
    have he : (hermiteExtremizer m).comp (C (-1) * X) = hermiteExtremizer m := by
      apply Polynomial.funext
      intro x
      simpa only [eval_comp, eval_mul, eval_C, eval_X, neg_one_mul]
        using hermiteExtremizer_eval_neg m x
    have hb : ((X ^ 2 - C (h ^ 2)) ^ 2 : ℝ[X]).comp (C (-1) * X) =
        (X ^ 2 - C (h ^ 2)) ^ 2 := by
      simp only [pow_comp, sub_comp, X_comp, C_comp, map_neg, map_one]
      ring
    rw [hq, mul_comp, hb] at he
    have heq := mul_left_cancel₀ hbmonic.ne_zero he
    intro x
    have hx := congrArg (fun f : ℝ[X] => f.eval x) heq
    simpa only [eval_comp, eval_mul, eval_C, eval_X, neg_one_mul] using hx
  exact ⟨q, hmonic, hdegree, heven, hpos, hq⟩

/-- Monic positive dilation preserves the exact squared-pair divisor and its positive cofactor. -/
theorem scaledHermiteExtremizer_positive_cofactor {r : ℝ} (hr : 0 < r) (m : ℕ) :
    ∃ q : ℝ[X], q.Monic ∧ q.natDegree = 2 * m ∧
      (∀ x : ℝ, q.eval (-x) = q.eval x) ∧ (∀ x : ℝ, 0 < q.eval x) ∧
      scaledHermiteExtremizer r m =
        (X ^ 2 - C ((r * hermiteEdge (2 * m + 2)) ^ 2)) ^ 2 * q := by
  obtain ⟨q, hmonic, hdeg, heven, hpos, hq⟩ := hermiteExtremizer_positive_cofactor m
  let Q : ℝ[X] := C (r ^ (2 * m)) * q.comp (C r⁻¹ * X)
  have hdegree : Q.natDegree = 2 * m := by
    rw [Q, natDegree_C_mul (pow_ne_zero _ hr.ne'), natDegree_comp,
      natDegree_C_mul (inv_ne_zero hr.ne'), natDegree_X, mul_one, hdeg]
  have hQmonic : Q.Monic := by
    change Q.leadingCoeff = 1
    rw [← coeff_natDegree, hdegree]
    change (C (r ^ (2 * m)) * q.comp (C r⁻¹ * X)).coeff (2 * m) = 1
    rw [coeff_C_mul, comp_C_mul_X_coeff, ← hdeg, coeff_natDegree, hmonic.leadingCoeff, one_mul,
      ← mul_pow, mul_inv_cancel₀ hr.ne', one_pow]
  refine ⟨Q, hQmonic, hdegree, ?_, ?_, ?_⟩
  · intro x
    simp only [Q, eval_mul, eval_C, eval_comp, eval_X, mul_neg, heven]
  · intro x
    simp only [Q, eval_mul, eval_C, eval_comp, eval_X]
    exact mul_pos (pow_pos hr _) (hpos _)
  · apply Polynomial.funext
    intro x
    simp only [scaledHermiteExtremizer, Q, hq, eval_mul, eval_C, eval_comp,
      eval_X, eval_pow, eval_sub]
    rw [pow_add]
    field_simp [hr.ne']
    <;> ring

/-- At any positive scale, both real roots of the extremizer have multiplicity exactly two. -/
theorem scaledHermiteExtremizer_rootMultiplicity {r : ℝ} (hr : 0 < r) (m : ℕ) :
    rootMultiplicity (r * hermiteEdge (2 * m + 2)) (scaledHermiteExtremizer r m) = 2 ∧
    rootMultiplicity (-(r * hermiteEdge (2 * m + 2))) (scaledHermiteExtremizer r m) = 2 := by
  obtain ⟨q, hmonic, hdeg, heven, hpos, hq⟩ := scaledHermiteExtremizer_positive_cofactor hr m
  let h := r * hermiteEdge (2 * m + 2)
  have hh : 0 < h := mul_pos hr (hermiteEdge_pos (by omega))
  have hp : scaledHermiteExtremizer r m ≠ 0 := by
    intro hz
    have hd := scaledHermiteExtremizer_degree hr m
    rw [hz, natDegree_zero] at hd
    omega
  have hmult (x : ℝ) (hx : x ^ 2 = h ^ 2) :
      rootMultiplicity x (scaledHermiteExtremizer r m) = 2 := by
    have hfac : scaledHermiteExtremizer r m = (X ^ 2 - C (x ^ 2)) ^ 2 * q := by
      simpa only [hx] using hq
    apply rootMultiplicity_eq_two hp
    · rw [hfac]
      simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, sub_self, zero_pow
        (by omega : 2 ≠ 0), zero_mul]
    · rw [hfac]
      simp [derivative_mul, derivative_pow, derivative_sub, derivative_C, derivative_X]
    · rw [hfac, second_derivative_squared_pair_eval]
      have hxpos : 0 < x ^ 2 := by rw [hx]; exact sq_pos_of_pos hh
      exact (mul_pos (mul_pos (by norm_num) hxpos) (hpos x)).ne'
  exact ⟨hmult h rfl, hmult (-h) (neg_sq h)⟩

end
end GaloisForLFunctions.ArithmeticLocalDivisorGeometry

#print axioms GaloisForLFunctions.ArithmeticLocalDivisorGeometry.scaledHermiteExtremizer_positive_cofactor
#print axioms GaloisForLFunctions.ArithmeticLocalDivisorGeometry.scaledHermiteExtremizer_rootMultiplicity
