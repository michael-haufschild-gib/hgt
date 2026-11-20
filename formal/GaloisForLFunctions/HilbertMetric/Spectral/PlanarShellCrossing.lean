import Mathlib.Analysis.Real.Sqrt

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
def angularCoefficient (a : UnitInterval) (n : ℕ) (λ : UnitInterval) : ℝ :=
  reflection (n + 1 : ℝ) λ * reflection (n + 1 : ℝ) ((a : ℝ) * λ) *
    (a : ℝ) ^ (2 * (n + 1))

private theorem angularInput_lt_degree (a : UnitInterval) (n : ℕ) (λ : UnitInterval) :
    (a : ℝ) * λ < (n + 1 : ℝ) := by
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have h := mul_lt_mul_of_pos_right a.2.2 λ.2.1
  exact (by simpa only [one_mul] using h : (a : ℝ) * λ < (λ : ℝ)).trans
    (λ.2.2.trans_le hn)

/-- Every angular coefficient is strictly increasing in the spectral parameter. -/
theorem angularCoefficient_strictMono (a : UnitInterval) (n : ℕ) :
    StrictMono (angularCoefficient a n) := by
  intro x y hxy
  have hxy' : (x : ℝ) < y := hxy
  have hd : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by positivity
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
theorem angularCoefficient_strictAnti (a : UnitInterval) (λ : UnitInterval) :
    StrictAnti (fun n => angularCoefficient a n λ) := by
  intro m n hmn
  have hm : (1 : ℝ) ≤ (m : ℝ) + 1 := by positivity
  have hmn' : (m : ℝ) + 1 < (n : ℝ) + 1 := by
    exact add_lt_add_right (by exact_mod_cast hmn) 1
  have hλ := λ.2.2.trans_le hm
  have h₁ := reflection_degree_lt λ.2.1 hλ hmn'
  have h₂ := reflection_degree_lt (mul_pos a.2.1 λ.2.1) (angularInput_lt_degree a m λ) hmn'
  have hp₁ := reflection_pos λ.2.1 hλ
  have hp₂ := reflection_pos (mul_pos a.2.1 λ.2.1) (angularInput_lt_degree a n λ)
  have hpow : (a : ℝ) ^ (2 * (n + 1)) ≤ (a : ℝ) ^ (2 * (m + 1)) :=
    pow_le_pow_of_le_one a.2.1.le a.2.2.le (by omega)
  unfold angularCoefficient
  exact ((mul_le_mul_of_nonneg_left hpow
    (mul_pos (reflection_pos λ.2.1 (hλ.trans hmn')) hp₂).le).trans_lt
      (mul_lt_mul_of_pos_right
        ((mul_lt_mul_of_pos_right h₁ hp₂).trans (mul_lt_mul_of_pos_left h₂ hp₁))
        (pow_pos a.2.1 _)))

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
  have hλ : 0 < 1 - L := sub_pos.mpr (crossing a).2.2
  have haλ : 0 < 1 - A * L := by
    simpa only [Nat.cast_zero, zero_add] using sub_pos.mpr (angularInput_lt_degree a 0 (crossing a))
  change (1 + L) / (1 - L) * ((1 + A * L) / (1 - A * L)) * A ^ 2 = 1
  field_simp [hλ.ne', haλ.ne']
  dsimp only [B] at hpoly
  linear_combination -(1 + A) * hpoly

/-- At the first angular threshold all higher angular modes lie strictly below one. -/
theorem angularCoefficient_higher_at_crossing (a : UnitInterval) (n : ℕ) :
    angularCoefficient a (n + 1) (crossing a) < 1 := by
  rw [← angularCoefficient_crossing a]
  exact angularCoefficient_strictAnti a (crossing a) (Nat.zero_lt_succ n)

/-- The first threshold is the unique angular crossing of degree one. -/
theorem angularCoefficient_eq_one_iff (a λ : UnitInterval) :
    angularCoefficient a 0 λ = 1 ↔ λ = crossing a := by
  rw [← angularCoefficient_crossing a]
  exact (angularCoefficient_strictMono a 0).injective.eq_iff

#print axioms angularCoefficient_strictAnti
#print axioms angularCoefficient_crossing
#print axioms angularCoefficient_higher_at_crossing

end

end GaloisForLFunctions.HilbertMetric.PlanarShell
