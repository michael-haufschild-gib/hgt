import GaloisForLFunctions.ArithmeticLocalDivisorGeometry.HermiteSonin
import GaloisForLFunctions.ArithmeticLocalDivisorGeometry.HermiteHeatRootBarrier

/-!
# Sharp Hermite heat extremizers

Subtracting the outermost critical value gives a globally nonnegative even polynomial with
exactly two real roots. Its full coefficient cone begins at the unit Gaussian heat time;
positive dilation gives every scale, and boundary equality determines the polynomial.
-/

/-!
# Attainment of the sharp heat-root barrier

Shifting an even Hermite polynomial by its outermost critical value gives a nonnegative
extremizer. Its only real roots are the outer critical pair, and its coefficient heat cone
starts exactly at one half. Dilation gives every positive Gaussian scale.
-/

open Polynomial
open GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.ArithmeticLocalDivisorGeometry
noncomputable section

/-- The monic even Hermite polynomial shifted by its outermost critical value. -/
def hermiteExtremizer (m : ℕ) : ℝ[X] :=
  hermiteReal (2 * m + 4) - C ((hermiteReal (2 * m + 4)).eval (hermiteEdge (2 * m + 2)))

theorem hermiteExtremizer_degree (m : ℕ) : (hermiteExtremizer m).natDegree = 2 * m + 4 := by
  rw [hermiteExtremizer, natDegree_sub_eq_left_of_natDegree_lt, natDegree_hermiteReal]
  rw [natDegree_C, natDegree_hermiteReal]
  omega

theorem hermiteExtremizer_ne_zero (m : ℕ) : hermiteExtremizer m ≠ 0 := by
  intro h
  have hd := hermiteExtremizer_degree m
  rw [h, natDegree_zero] at hd
  omega

theorem hermiteExtremizer_monic (m : ℕ) : (hermiteExtremizer m).Monic := by
  change (hermiteExtremizer m).leadingCoeff = 1
  rw [← coeff_natDegree, hermiteExtremizer_degree]
  simp only [hermiteExtremizer, coeff_sub, coeff_C,
    if_neg (show 2 * m + 4 ≠ 0 by omega), sub_zero]
  rw [← natDegree_hermiteReal (2 * m + 4), coeff_natDegree]
  exact ((hermite_monic (2 * m + 4)).map (Int.castRingHom ℝ)).leadingCoeff

@[simp] theorem hermiteExtremizer_eval_edge (m : ℕ) :
    (hermiteExtremizer m).eval (hermiteEdge (2 * m + 2)) = 0 := by
  simp only [hermiteExtremizer, eval_sub, eval_C, sub_self]

theorem hermiteExtremizer_eval_neg (m : ℕ) (x : ℝ) :
    (hermiteExtremizer m).eval (-x) = (hermiteExtremizer m).eval x := by
  have he : (-1 : ℝ) ^ (2 * m + 4) = 1 := by simp [pow_add, pow_mul]
  simp only [hermiteExtremizer, eval_sub, eval_C, eval_neg_hermiteReal, he, one_mul]

/-- On the nonnegative axis the only zero is the outermost Hermite critical point. -/
theorem hermiteExtremizer_pos_nonneg (m : ℕ) {x : ℝ} (hx : 0 ≤ x)
    (hne : x ≠ hermiteEdge (2 * m + 2)) : 0 < (hermiteExtremizer m).eval x := by
  rw [hermiteExtremizer, eval_sub, eval_C, sub_pos]
  exact hermite_edge_strict_min_nonneg (2 * m + 2) hx hne

/-- The shifted Hermite polynomial attains the heat-root boundary within the nonnegative class. -/
theorem hermiteExtremizer_nonneg (m : ℕ) (x : ℝ) : 0 ≤ (hermiteExtremizer m).eval x := by
  have hhalf : ∀ y : ℝ, 0 ≤ y → 0 ≤ (hermiteExtremizer m).eval y := by
    intro y hy
    by_cases he : y = hermiteEdge (2 * m + 2)
    · rw [he, hermiteExtremizer_eval_edge]
    · exact (hermiteExtremizer_pos_nonneg m hy he).le
  by_cases hx : 0 ≤ x
  · exact hhalf x hx
  · rw [← hermiteExtremizer_eval_neg]
    exact hhalf (-x) (by linarith only [(lt_of_not_ge hx).le])

/-- Exactly the two outer critical points are real roots. -/
theorem hermiteExtremizer_eval_eq_zero_iff (m : ℕ) (x : ℝ) :
    (hermiteExtremizer m).eval x = 0 ↔
      x = hermiteEdge (2 * m + 2) ∨ x = -hermiteEdge (2 * m + 2) := by
  constructor
  · intro hz
    by_cases hx : 0 ≤ x
    · left
      by_contra hn
      exact (hermiteExtremizer_pos_nonneg m hx hn).ne' hz
    · right
      have hneg : (hermiteExtremizer m).eval (-x) = 0 := by
        rw [hermiteExtremizer_eval_neg, hz]
      have he : -x = hermiteEdge (2 * m + 2) := by
        by_contra hn
        exact (hermiteExtremizer_pos_nonneg m (by linarith only [(lt_of_not_ge hx).le]) hn).ne' hneg
      linarith only [he]
  · rintro (rfl | rfl)
    · exact hermiteExtremizer_eval_edge m
    · rw [hermiteExtremizer_eval_neg, hermiteExtremizer_eval_edge]

/-- Unit Gaussian heat leaves precisely the leading monomial and a positive constant. -/
theorem forwardPolyHeat_hermiteExtremizer (m : ℕ) :
    forwardPolyHeat (1 / 2) (hermiteExtremizer m) =
      X ^ (2 * m + 4) - C ((hermiteReal (2 * m + 4)).eval (hermiteEdge (2 * m + 2))) := by
  rw [hermiteExtremizer, sub_eq_add_neg, ← map_neg, forwardPolyHeat_add,
    forwardPolyHeat_half_hermite, forwardPolyHeat_C, map_neg, ← sub_eq_add_neg]

theorem coeffNonneg_heat_hermiteExtremizer (m : ℕ) :
    CoeffNonneg (forwardPolyHeat (1 / 2) (hermiteExtremizer m)) := by
  intro j
  rw [forwardPolyHeat_hermiteExtremizer]
  simp only [coeff_sub, coeff_X_pow, coeff_C]
  split_ifs <;> linarith only [hermite_eval_succ_edge_neg (2 * m + 2)]

/-- All real admissible heat times form exactly the ray starting at one half. -/
theorem coeffNonneg_heat_hermiteExtremizer_iff (m : ℕ) (s : ℝ) :
    CoeffNonneg (forwardPolyHeat s (hermiteExtremizer m)) ↔ (1 / 2 : ℝ) ≤ s := by
  constructor
  · intro hc
    have he : 0 < hermiteEdge (2 * m + 2) := hermiteEdge_pos (by omega)
    have hs : 0 < s := by
      by_contra hn
      have h0 := coeffNonneg_forwardPolyHeat_mono (hermiteExtremizer m) (le_of_not_gt hn) hc
      rw [forwardPolyHeat_zero] at h0
      have hpos := eval_pos_of_coeffNonneg (hermiteExtremizer_ne_zero m) h0 he
      rw [hermiteExtremizer_eval_edge] at hpos
      exact (lt_irrefl (0 : ℝ)) hpos
    have htime : 2 * s / 2 = s := by ring
    have hb := nonnegative_root_le_sqrt_mul_hermiteEdge (by positivity : 0 < 2 * s)
      (hermiteExtremizer_degree m) (hermiteExtremizer_nonneg m)
      (by simpa only [htime] using hc) (hermiteExtremizer_eval_edge m)
    have hsqrt : 1 ≤ Real.sqrt (2 * s) := (mul_le_mul_iff_of_pos_right he).mp
      (by simpa only [one_mul] using hb)
    have hsq := Real.sq_sqrt (show 0 ≤ 2 * s by positivity)
    nlinarith only [hsqrt, hsq]
  · exact fun hs => coeffNonneg_forwardPolyHeat_mono _ hs (coeffNonneg_heat_hermiteExtremizer m)

/-- Dilation with monic normalization realizes the sharp boundary at any positive scale. -/
def scaledHermiteExtremizer (r : ℝ) (m : ℕ) : ℝ[X] :=
  C (r ^ (2 * m + 4)) * (hermiteExtremizer m).comp (C r⁻¹ * X)

theorem scaledHermiteExtremizer_degree {r : ℝ} (hr : 0 < r) (m : ℕ) :
    (scaledHermiteExtremizer r m).natDegree = 2 * m + 4 := by
  rw [scaledHermiteExtremizer, natDegree_C_mul (pow_ne_zero _ hr.ne'), natDegree_comp,
    natDegree_C_mul (inv_ne_zero hr.ne'), natDegree_X, mul_one, hermiteExtremizer_degree]

theorem scaledHermiteExtremizer_nonneg {r : ℝ} (hr : 0 < r) (m : ℕ) (x : ℝ) :
    0 ≤ (scaledHermiteExtremizer r m).eval x := by
  simp only [scaledHermiteExtremizer, eval_mul, eval_C, eval_comp, eval_X]
  exact mul_nonneg (pow_nonneg hr.le _) (hermiteExtremizer_nonneg m _)

theorem scaledHermiteExtremizer_even (r : ℝ) (m : ℕ) (x : ℝ) :
    (scaledHermiteExtremizer r m).eval (-x) = (scaledHermiteExtremizer r m).eval x := by
  simp only [scaledHermiteExtremizer, eval_mul, eval_C, eval_comp, eval_X, mul_neg,
    hermiteExtremizer_eval_neg]

/-- The two real roots dilate by the exact Gaussian standard deviation. -/
theorem scaledHermiteExtremizer_eval_eq_zero_iff {r : ℝ} (hr : 0 < r) (m : ℕ) (x : ℝ) :
    (scaledHermiteExtremizer r m).eval x = 0 ↔
      x = r * hermiteEdge (2 * m + 2) ∨ x = -(r * hermiteEdge (2 * m + 2)) := by
  have hc : r ^ (2 * m + 4) ≠ 0 := pow_ne_zero _ hr.ne'
  simp only [scaledHermiteExtremizer, eval_mul, eval_C, eval_comp, eval_X,
    mul_eq_zero, hc, false_or, hermiteExtremizer_eval_eq_zero_iff]
  have hmul : r * (r⁻¹ * x) = x := by rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]
  constructor
  · rintro (h | h)
    · left
      rw [← hmul, h]
    · right
      rw [← hmul, h, mul_neg]
  · rintro (h | h)
    · left
      rw [h, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
    · right
      rw [h, mul_neg, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]

/-- Exact heat threshold at every positive scale, including the exclusion of negative times. -/
theorem coeffNonneg_heat_scaledHermiteExtremizer_iff {r : ℝ} (hr : 0 < r) (m : ℕ) (s : ℝ) :
    CoeffNonneg (forwardPolyHeat s (scaledHermiteExtremizer r m)) ↔ r ^ 2 / 2 ≤ s := by
  rw [scaledHermiteExtremizer, forwardPolyHeat_C_mul,
    coeffNonneg_C_mul_iff _ (pow_pos hr _), coeffNonneg_heat_dilation_iff s (inv_pos.mpr hr),
    coeffNonneg_heat_hermiteExtremizer_iff]
  have hs : s * r⁻¹ ^ 2 * r ^ 2 = s := by field_simp
  have hhalf : (1 / 2 : ℝ) * r ^ 2 = r ^ 2 / 2 := by ring
  rw [← mul_le_mul_iff_of_pos_right (sq_pos_of_pos hr), hs, hhalf]

/-- Every intermediate coefficient vanishes at the first heat time. -/
theorem hermiteExtremizer_heat_middle_coeff (m : ℕ) {j : ℕ}
    (hj0 : 0 < j) (hj : j < 2 * m + 4) :
    (forwardPolyHeat (1 / 2) (hermiteExtremizer m)).coeff j = 0 := by
  rw [forwardPolyHeat_hermiteExtremizer]
  simp [coeff_X_pow, show 2 * m + 4 ≠ j by omega, show j ≠ 0 by omega]

/-- The constant coefficient is positive at first contact, so contact has positive order. -/
theorem hermiteExtremizer_heat_constant_pos (m : ℕ) :
    0 < (forwardPolyHeat (1 / 2) (hermiteExtremizer m)).coeff 0 := by
  have he : (forwardPolyHeat (1 / 2) (hermiteExtremizer m)).coeff 0 =
      -(hermiteReal (2 * m + 4)).eval (hermiteEdge (2 * m + 2)) := by
    rw [forwardPolyHeat_hermiteExtremizer]
    simp [coeff_X_pow, show 2 * m + 4 ≠ 0 by omega]
  rw [he]
  exact neg_pos.mpr (hermite_eval_succ_edge_neg (2 * m + 2))

/-- Monic dilation retains a leading monomial of coefficient one at the exact threshold. -/
theorem forwardPolyHeat_scaledHermiteExtremizer {r : ℝ} (hr : 0 < r) (m : ℕ) :
    forwardPolyHeat (r ^ 2 / 2) (scaledHermiteExtremizer r m) = X ^ (2 * m + 4) -
      C (r ^ (2 * m + 4) * (hermiteReal (2 * m + 4)).eval (hermiteEdge (2 * m + 2))) := by
  have ht : r ^ 2 / 2 * r⁻¹ ^ 2 = (1 / 2 : ℝ) := by field_simp
  have hC : (C (r ^ (2 * m + 4)) : ℝ[X]) * C r⁻¹ ^ (2 * m + 4) = 1 := by
    rw [← map_pow, ← map_mul, ← mul_pow, mul_inv_cancel₀ hr.ne', one_pow, map_one]
  rw [scaledHermiteExtremizer, forwardPolyHeat_C_mul, forwardPolyHeat_comp_dilation,
    ht, forwardPolyHeat_hermiteExtremizer]
  simp only [sub_comp, pow_comp, X_comp, C_comp, mul_pow]
  calc
    _ = (C (r ^ (2 * m + 4)) * C r⁻¹ ^ (2 * m + 4)) * X ^ (2 * m + 4) -
        C (r ^ (2 * m + 4)) * C ((hermiteReal (2 * m + 4)).eval (hermiteEdge (2 * m + 2))) := by
      ring
    _ = _ := by rw [hC, one_mul, map_mul]

/-- Boundary equality selects the monic scaled extremizer up to a positive factor. -/
theorem nonnegative_boundary_eq_scaledHermiteExtremizer {p : ℝ[X]} {r : ℝ}
    (hr : 0 < r) (m : ℕ) (hdeg : p.natDegree = 2 * m + 4)
    (hp : ∀ x : ℝ, 0 ≤ p.eval x)
    (hc : CoeffNonneg (forwardPolyHeat (r ^ 2 / 2) p))
    (hx : p.eval (r * hermiteEdge (2 * m + 2)) = 0) :
    ∃ c : ℝ, 0 < c ∧ p = C c * scaledHermiteExtremizer r m := by
  obtain ⟨a, ha, he⟩ := scaled_nonnegative_edge_root_rigidity hr hdeg hp hc hx
  have hpow : 0 < r ^ (2 * m + 4) := pow_pos hr _
  refine ⟨a / r ^ (2 * m + 4), div_pos ha hpow, ?_⟩
  have hscalar : a / r ^ (2 * m + 4) * r ^ (2 * m + 4) = a := by field_simp
  rw [he, scaledHermiteExtremizer, hermiteExtremizer, sub_comp, C_comp,
    ← mul_assoc, ← map_mul, hscalar]

end
end GaloisForLFunctions.ArithmeticLocalDivisorGeometry
