import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.LinearCombination


/-!
# Angular crossings of the planar concentric shell

The two boundary conditions give a product of reflection factors. The product
increases with spectral parameter and decreases with angular degree. The first
angular crossing is the smaller root of a quadratic, written in a form that
stays regular as the inner radius approaches one.
-/

namespace GaloisForLFunctions.HilbertMetric.PlanarShell

noncomputable section

private abbrev UnitInterval := Set.Ioo (0 : ℝ) 1

private def reflection (d x : ℝ) : ℝ := (d + x) / (d - x)

private theorem reflection_pos {d x : ℝ} (hx : 0 < x) (hd : x < d) :
    0 < reflection d x :=
  div_pos (add_pos (hx.trans hd) hx) (sub_pos.mpr hd)

private theorem reflection_input_lt {d x y : ℝ} (hd : 0 < d) (hxy : x < y) (hy : y < d) :
    reflection d x < reflection d y := by
  apply (div_lt_div_iff₀ (sub_pos.mpr (hxy.trans hy)) (sub_pos.mpr hy)).mpr
  nlinarith only [mul_pos hd (sub_pos.mpr hxy)]

private theorem reflection_degree_lt {d e x : ℝ} (hx : 0 < x) (hd : x < d) (hde : d < e) :
    reflection e x < reflection d x := by
  apply (div_lt_div_iff₀ (sub_pos.mpr (hd.trans hde)) (sub_pos.mpr hd)).mpr
  nlinarith only [mul_pos hx (sub_pos.mpr hde)]

/-- The coefficient for angular degree `n+1` in the diagonal boundary operator. -/
def angularCoefficient (a : UnitInterval) (n : ℕ) (z : UnitInterval) : ℝ :=
  reflection (n + 1 : ℝ) z * reflection (n + 1 : ℝ) ((a : ℝ) * z) *
    (a : ℝ) ^ (2 * (n + 1))

private theorem angularInput_lt_degree (a : UnitInterval) (n : ℕ) (z : UnitInterval) :
    (a : ℝ) * z < (n + 1 : ℝ) := by
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
  have h := mul_lt_mul_of_pos_right a.2.2 z.2.1
  have hlt : (a : ℝ) * z < (z : ℝ) := by simpa only [one_mul] using h
  exact hlt.trans (z.2.2.trans_le hn)

/-- Every angular coefficient is strictly increasing in the spectral parameter. -/
theorem angularCoefficient_strictMono (a : UnitInterval) (n : ℕ) :
    StrictMono (angularCoefficient a n) := by
  intro x y hxy
  have hxy' : (x : ℝ) < y := hxy
  have hd : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
  have h₁ := reflection_input_lt hd hxy' (y.2.2.trans_le hn)
  have h₂ := reflection_input_lt hd (mul_lt_mul_of_pos_left hxy' a.2.1)
    (angularInput_lt_degree a n y)
  have hp₁ := reflection_pos y.2.1 (y.2.2.trans_le hn)
  have hp₂ := reflection_pos (mul_pos a.2.1 x.2.1) (angularInput_lt_degree a n x)
  unfold angularCoefficient
  exact mul_lt_mul_of_pos_right
    ((mul_lt_mul_of_pos_right h₁ hp₂).trans (mul_lt_mul_of_pos_left h₂ hp₁))
    (pow_pos a.2.1 _)

/-- Larger harmonic degree delays any level-one crossing. -/
theorem angularCoefficient_strictAnti (a : UnitInterval) (z : UnitInterval) :
    StrictAnti (fun n => angularCoefficient a n z) := by
  intro m n hmn
  have hm : (1 : ℝ) ≤ (m : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg m)
  have hmn' : (m : ℝ) + 1 < (n : ℝ) + 1 := by
    exact_mod_cast Nat.add_lt_add_right hmn 1
  have hz := z.2.2.trans_le hm
  have h₁ := reflection_degree_lt z.2.1 hz hmn'
  have h₂ := reflection_degree_lt (mul_pos a.2.1 z.2.1) (angularInput_lt_degree a m z) hmn'
  have hp₁ := reflection_pos z.2.1 hz
  have hp₂ := reflection_pos (mul_pos a.2.1 z.2.1) (angularInput_lt_degree a n z)
  have hpow : (a : ℝ) ^ (2 * (n + 1)) ≤ (a : ℝ) ^ (2 * (m + 1)) :=
    pow_le_pow_of_le_one a.2.1.le a.2.2.le (by omega)
  unfold angularCoefficient
  exact (mul_le_mul_of_nonneg_left hpow
    (mul_pos (reflection_pos z.2.1 (hz.trans hmn')) hp₂).le).trans_lt
      (mul_lt_mul_of_pos_right
        ((mul_lt_mul_of_pos_right h₁ hp₂).trans (mul_lt_mul_of_pos_left h₂ hp₁))
        (pow_pos a.2.1 _))

/-- Increasing the concentric inner radius increases the boundary response at fixed
spectral parameter. -/
theorem angularCoefficient_radius_strictMono (n : ℕ) (z : UnitInterval) :
    StrictMono (fun a => angularCoefficient a n z) := by
  intro a b hab
  have hab' : (a : ℝ) < b := hab
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hp := reflection_pos z.2.1 (z.2.2.trans_le hn)
  have h := reflection_input_lt (zero_lt_one.trans_le hn)
    (mul_lt_mul_of_pos_right hab' z.2.1) (angularInput_lt_degree b n z)
  have hpow := pow_le_pow_left₀ a.2.1.le hab'.le (2 * (n + 1))
  unfold angularCoefficient
  exact (mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left h hp) (pow_pos a.2.1 _)).trans_le
    (mul_le_mul_of_nonneg_left hpow
      (mul_pos hp (reflection_pos (mul_pos b.2.1 z.2.1) (angularInput_lt_degree b n z))).le)

/-- The first angular threshold, in the rationalized form of the smaller root. -/
def crossing (a : UnitInterval) : UnitInterval := by
  let A := (a : ℝ)
  let D := Real.sqrt ((1 - A) ^ 4 + 4 * A ^ 2)
  have ha : 0 < A := a.2.1
  have h₁ : 0 < 1 - A := sub_pos.mpr a.2.2
  have hds : (1 - A) ^ 2 ≤ D := by
    rw [← Real.sqrt_sq (sq_nonneg (1 - A))]
    apply Real.sqrt_le_sqrt
    nlinarith only [sq_nonneg A]
  have hden : 0 < 1 + A ^ 2 + D := by positivity
  refine ⟨2 * (1 - A) / (1 + A ^ 2 + D), div_pos (by positivity) hden, ?_⟩
  change 2 * (1 - A) / (1 + A ^ 2 + D) < 1
  rw [div_lt_iff₀ hden, one_mul]
  nlinarith only [hds, sq_pos_of_pos ha]

/-- The explicit threshold makes the degree-one coefficient exactly one. -/
theorem angularCoefficient_crossing (a : UnitInterval) :
    angularCoefficient a 0 (crossing a) = 1 := by
  let A := (a : ℝ)
  let B := 1 + A ^ 2
  let D := Real.sqrt ((1 - A) ^ 4 + 4 * A ^ 2)
  let L := (crossing a : ℝ)
  have hd : 0 < B + D := by dsimp only [B, D]; positivity
  have hD : D ^ 2 = (1 - A) ^ 4 + 4 * A ^ 2 := Real.sq_sqrt (by positivity)
  have hpoly : (1 - A) * (1 + A * L ^ 2) = B * L := by
    change (1 - A) * (1 + A * (2 * (1 - A) / (B + D)) ^ 2) =
      B * (2 * (1 - A) / (B + D))
    field_simp [hd.ne']
    dsimp only [B]
    linear_combination (1 - A) * hD
  have hz : 0 < 1 - L := sub_pos.mpr (crossing a).2.2
  have haz : 0 < 1 - A * L := by
    simpa only [Nat.cast_zero, zero_add] using sub_pos.mpr (angularInput_lt_degree a 0 (crossing a))
  simp only [angularCoefficient, Nat.cast_zero, zero_add, reflection]
  change (1 + L) / (1 - L) * ((1 + A * L) / (1 - A * L)) * A ^ 2 = 1
  rw [div_mul_div_comm, div_mul_eq_mul_div, div_eq_iff (mul_ne_zero hz.ne' haz.ne'), one_mul]
  dsimp only [B] at hpoly
  linear_combination -(1 + A) * hpoly

/-- At the first angular threshold all higher angular modes lie strictly below one. -/
theorem angularCoefficient_higher_at_crossing (a : UnitInterval) (n : ℕ) :
    angularCoefficient a (n + 1) (crossing a) < 1 := by
  rw [← angularCoefficient_crossing a]
  exact angularCoefficient_strictAnti a (crossing a) (Nat.zero_lt_succ n)

/-- The first threshold is the unique angular crossing of degree one. -/
theorem angularCoefficient_eq_one_iff (a z : UnitInterval) :
    angularCoefficient a 0 z = 1 ↔ z = crossing a := by
  rw [← angularCoefficient_crossing a]
  exact (angularCoefficient_strictMono a 0).injective.eq_iff

/-- Thinner concentric shells cross at strictly smaller spectral parameter. -/
theorem crossing_strictAnti : StrictAnti crossing := by
  intro a b hab
  have h : angularCoefficient a 0 (crossing a) < angularCoefficient b 0 (crossing a) :=
    angularCoefficient_radius_strictMono 0 (crossing a) hab
  rw [angularCoefficient_crossing a, ← angularCoefficient_crossing b] at h
  apply lt_of_not_ge
  intro hle
  exact h.not_ge ((angularCoefficient_strictMono b 0).monotone hle)

#print axioms angularCoefficient_strictAnti
#print axioms angularCoefficient_crossing
#print axioms angularCoefficient_higher_at_crossing
#print axioms crossing_strictAnti

end

end GaloisForLFunctions.HilbertMetric.PlanarShell
