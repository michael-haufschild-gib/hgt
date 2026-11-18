import GaloisForLFunctions.RHTower.AnharmonicOrbitCubicDiscriminant

/-!
# Hessian shape and real trace weights of the anharmonic orbit cubic

Oller (arXiv:2611.17965, §§3–4) uses the Hessian shape of a binary cubic
and the trace-dual coordinates obtained by division by its derivative.
For this family the Hessian shape is constant. The quadratic numerator
X(X−1) yields positive trace-one weights on all three roots.
-/

noncomputable section
namespace RHTower.OrbitCubic

/-- The binary form with coefficients given by the corpus orbit cubic. -/
def binary (q x y : ℝ) : ℝ :=
  let f := chebyshevRealOrbitCubic q
  f.a * x^3 + f.b * x^2*y + f.c*x*y^2 + f.d*y^3

/-- The normalized negative Hessian determinant of a binary cubic. -/
def hessian (f : Cubic ℝ) (x y : ℝ) : ℝ :=
  (f.b^2 - 3*f.a*f.c)*x^2 + (f.b*f.c - 9*f.a*f.d)*x*y + (f.c^2 - 3*f.b*f.d)*y^2

/-- A single hexagonal shape for the entire family. -/
theorem hessian_shape (q x y : ℝ) :
    hessian (chebyshevRealOrbitCubic q) x y = (q^2 + 27/4)*(x^2-x*y+y^2) := by
  unfold hessian chebyshevRealOrbitCubic
  ring

/-- The shape scale is the positive square root of the discriminant. -/
theorem hessian_sq (q x y : ℝ) :
    hessian (chebyshevRealOrbitCubic q) x y ^ 2 =
      (chebyshevRealOrbitCubic q).discr * (x^2-x*y+y^2)^2 := by
  rw [hessian_shape, chebyshevRealOrbitCubic_discr, mul_pow]

/-- The order-six integral rotation reverses the binary cubic. -/
theorem binary_rotate (q x y : ℝ) : binary q (x-y) x = -binary q x y := by
  simp only [binary, chebyshevRealOrbitCubic]
  ring

/-- Completing the square classifies all integral shortest directions. -/
theorem hexagonal_minima (x y : ℤ) :
    x^2-x*y+y^2 ≤ 1 ↔
      (x = 0 ∧ (y = -1 ∨ y = 0 ∨ y = 1)) ∨
      (x = 1 ∧ (y = 0 ∨ y = 1)) ∨ (x = -1 ∧ (y = 0 ∨ y = -1)) := by
  constructor
  · intro h
    have hx : x^2 ≤ 1 := by nlinarith only [h, sq_nonneg (2*y-x)]
    have hy : y^2 ≤ 1 := by nlinarith only [h, sq_nonneg (2*x-y)]
    have bound (a : ℤ) (ha : a^2 ≤ 1) : a = -1 ∨ a = 0 ∨ a = 1 := by
      by_contra! hn
      rcases lt_or_gt_of_ne hn.2.1 with h | h
      · have : a ≤ -2 := by omega
        nlinarith only [ha, this, mul_nonneg_of_nonpos_of_nonpos (show a ≤ 0 by omega) (show a+2 ≤ 0 by omega)]
      · have : 2 ≤ a := by omega
        nlinarith only [ha, this, mul_nonneg (show 0 ≤ a-2 by omega) (show 0 ≤ a by omega)]
    rcases bound x hx with rfl | rfl | rfl <;>
      rcases bound y hy with rfl | rfl | rfl <;> norm_num at *
  · rintro (⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩) <;> norm_num

/-- Every shortest nonzero direction also supplies a binary value of absolute value one. -/
theorem shortest_binary_unit (q : ℝ) (x y : ℤ) :
    x^2-x*y+y^2 = 1 ↔
      x^2-x*y+y^2 ≤ 1 ∧ |binary q x y| = 1 := by
  constructor
  · intro h
    refine ⟨h.le, ?_⟩
    rcases (hexagonal_minima x y).mp h.le with
      ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ <;>
      norm_num [binary, chebyshevRealOrbitCubic] at * <;>
      first | rw [show _ = (1 : ℝ) by ring, abs_one] | rw [show _ = (-1 : ℝ) by ring, abs_neg, abs_one]
  · rintro ⟨h,hu⟩
    rcases (hexagonal_minima x y).mp h with
      ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ <;>
      norm_num [binary, chebyshevRealOrbitCubic] at *

/-- The distinguished diagonal resolvent has numerator X(X−1).
The two poles of its self-energy are fixed throughout the family. -/
theorem arrowhead_secular (q x : ℝ) :
    binary q x 1 = (x-(q+1/2))*x*(x-1) - (x-1) - x := by
  simp only [binary, chebyshevRealOrbitCubic]
  ring

/-- The three real roots interlace the two fixed poles. -/
theorem roots_straddle_poles (q : ℝ) :
    ∃ a b c : ℝ, a < 0 ∧ 0 < b ∧ b < 1 ∧ 1 < c ∧
      binary q a 1 = 0 ∧ binary q b 1 = 0 ∧ binary q c 1 = 0 := by
  let R := |q| + 4
  have hr : 4 ≤ R := by dsimp [R]; linarith only [abs_nonneg q]
  have hplus : 3 ≤ R - (q+1/2) := by dsimp [R]; linarith only [le_abs_self q]
  have hminus : -R - (q+1/2) ≤ -3 := by dsimp [R]; linarith only [neg_abs_le q]
  have hR : 0 < binary q R 1 := by
    rw [arrowhead_secular]
    nlinarith only [hr, mul_nonneg (sub_nonneg.mpr hplus)
      (mul_nonneg (show 0 ≤ R by linarith only [hr]) (show 0 ≤ R-1 by linarith only [hr])),
      sq_nonneg (R-2)]
  have hL : binary q (-R) 1 < 0 := by
    rw [arrowhead_secular]
    nlinarith only [hr, mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hminus)
      (mul_nonneg (show 0 ≤ R by linarith only [hr]) (show 0 ≤ R+1 by linarith only [hr])),
      sq_nonneg R]
  have h0 : binary q 0 1 = 1 := by rw [arrowhead_secular]; ring
  have h1 : binary q 1 1 = -1 := by rw [arrowhead_secular]; ring
  have hc : Continuous (fun x => binary q x 1) := by simp only [arrowhead_secular]; fun_prop
  obtain ⟨a, ha, ea⟩ := intermediate_value_Icc (show -R ≤ 0 by linarith only [hr])
    hc.continuousOn (show 0 ∈ Set.Icc (binary q (-R) 1) (binary q 0 1) from ⟨hL.le, by rw [h0]; norm_num⟩)
  obtain ⟨b, hb, eb⟩ := intermediate_value_Icc' (show (0:ℝ) ≤ 1 by norm_num)
    hc.continuousOn (show 0 ∈ Set.Icc (binary q 1 1) (binary q 0 1) by rw [h0,h1]; constructor <;> norm_num)
  obtain ⟨c, hc', ec⟩ := intermediate_value_Icc (show 1 ≤ R by linarith only [hr])
    hc.continuousOn (show 0 ∈ Set.Icc (binary q 1 1) (binary q R 1) from ⟨by rw [h1]; norm_num, hR.le⟩)
  have hn0 (x : ℝ) (e : binary q x 1 = 0) : x ≠ 0 := by rintro rfl; linarith only [e,h0]
  have hn1 (x : ℝ) (e : binary q x 1 = 0) : x ≠ 1 := by rintro rfl; linarith only [e,h1]
  exact ⟨a,b,c,lt_of_le_of_ne ha.2 (hn0 _ ea),lt_of_le_of_ne hb.1 (hn0 _ eb).symm,
    lt_of_le_of_ne hb.2 (hn1 _ eb),lt_of_le_of_ne hc'.1 (hn1 _ ec).symm,ea,eb,ec⟩

end RHTower.OrbitCubic
