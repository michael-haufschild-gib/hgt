import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A one-prime obstruction to source-cup Gram positivity

On the real absolute-Euler ray, the complete logarithmic derivative of one prime Euler
factor is a geometric prime-power series. Its negative divided-difference kernel has a
strictly negative two-node determinant for every pair of distinct positive nodes.

This excludes a prime-by-prime positive-Gram decomposition of the C1 source cup, even
when all powers of each prime are grouped before testing positivity. It does not exclude
positivity after the global prime--polar--Gamma cancellation and does not prove RH.
-/

namespace RHTower

noncomputable section

private theorem sinh_sq_gt_sq {h : ℝ} (hh : h ≠ 0) : h ^ (2 : ℕ) < (Real.sinh h) ^ (2 : ℕ) := by
  rcases lt_or_gt_of_ne hh with hneg | hpos
  · have hs : Real.sinh h < h := Real.sinh_lt_self_iff.mpr hneg
    have hsneg : Real.sinh h < 0 := hs.trans hneg
    nlinarith
  · have hs : h < Real.sinh h := Real.self_lt_sinh_iff.mpr hpos
    nlinarith

/-- Strict logarithmic-mean gap underlying the local Euler determinant. -/
theorem exp_gap_sq_gt (t x y : ℝ) (ht : 0 < t) (hxy : x ≠ y) :
    t ^ (2 : ℕ) * Real.exp (t * x) * Real.exp (t * y) * (x - y) ^ (2 : ℕ) <
      (Real.exp (t * x) - Real.exp (t * y)) ^ (2 : ℕ) := by
  let m : ℝ := t * (x + y) / 2
  let h : ℝ := t * (x - y) / 2
  let E : ℝ := Real.exp m
  have hh : h ≠ 0 := by
    dsimp [h]
    exact div_ne_zero (mul_ne_zero ht.ne' (sub_ne_zero.mpr hxy)) (by norm_num)
  have hx : t * x = m + h := by dsimp [m, h]; ring
  have hy : t * y = m - h := by dsimp [m, h]; ring
  have hsum : Real.exp (t * x) * Real.exp (t * y) = E ^ (2 : ℕ) := by
    rw [hx, hy, Real.exp_add, Real.exp_sub]
    dsimp [E]
    field_simp [Real.exp_ne_zero]
  have hdiff : Real.exp (t * x) - Real.exp (t * y) =
      2 * E * Real.sinh h := by
    rw [hx, hy, Real.exp_add, Real.exp_sub, Real.sinh_eq]
    dsimp [E]
    rw [Real.exp_neg]
    ring
  have hscale : t ^ (2 : ℕ) * (x-y) ^ (2 : ℕ) = 4 * h ^ (2 : ℕ) := by
    dsimp [h]; ring
  have hE : 0 < 4 * E ^ (2 : ℕ) := by dsimp [E]; positivity
  have hstrict := mul_lt_mul_of_pos_left (sinh_sq_gt_sq hh) hE
  calc
    t ^ (2 : ℕ) * Real.exp (t * x) * Real.exp (t * y) * (x - y) ^ (2 : ℕ) =
        (4 * E ^ (2 : ℕ)) * h ^ (2 : ℕ) := by
          calc
            _ = (Real.exp (t * x) * Real.exp (t * y)) *
                (t ^ (2 : ℕ) * (x-y) ^ (2 : ℕ)) := by ring
            _ = _ := by rw [hsum, hscale]; ring
    _ < (4 * E ^ (2 : ℕ)) * (Real.sinh h) ^ (2 : ℕ) := hstrict
    _ = (Real.exp (t * x) - Real.exp (t * y)) ^ (2 : ℕ) := by rw [hdiff]; ring

private theorem euler_det_algebra {a b t d : ℝ}
    (ha : 1 < a) (hb : 1 < b) (hd : d ≠ 0)
    (hgap : t ^ (2 : ℕ) * a * b * d ^ (2 : ℕ) < (a - b) ^ (2 : ℕ)) :
    (t * a / (a - 1) ^ (2 : ℕ)) * (t * b / (b - 1) ^ (2 : ℕ)) <
      ((a - b) / ((a - 1) * (b - 1) * d)) ^ (2 : ℕ) := by
  have ha0 : a - 1 ≠ 0 := ne_of_gt (sub_pos.mpr ha)
  have hb0 : b - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hb)
  let D : ℝ := ((a - 1) * (b - 1) * d) ^ (2 : ℕ)
  have hD : 0 < D := sq_pos_of_ne_zero (mul_ne_zero (mul_ne_zero ha0 hb0) hd)
  have heq :
      (((a - b) / ((a - 1) * (b - 1) * d)) ^ (2 : ℕ) -
          (t * a / (a - 1) ^ (2 : ℕ)) * (t * b / (b - 1) ^ (2 : ℕ))) * D =
        (a - b) ^ (2 : ℕ) - t ^ (2 : ℕ) * a * b * d ^ (2 : ℕ) := by
    dsimp [D]
    field_simp
  have hpos : 0 < (((a - b) / ((a - 1) * (b - 1) * d)) ^ (2 : ℕ) -
      (t * a / (a - 1) ^ (2 : ℕ)) * (t * b / (b - 1) ^ (2 : ℕ))) * D := by
    rw [heq]
    linarith
  have := (mul_pos_iff_of_pos_right hD).mp hpos
  linarith

/-- Negative divided difference of `s ↦ 1/(exp(t s)-1)`, with its removable diagonal. -/
noncomputable def eulerRayLoewnerKernel (t x y : ℝ) : ℝ :=
  if x = y then t * Real.exp (t * x) / (Real.exp (t * x) - 1) ^ (2 : ℕ)
  else (1 / (Real.exp (t * y) - 1) - 1 / (Real.exp (t * x) - 1)) / (x - y)

private theorem eulerRayLoewnerKernel_offdiag
    {t x y : ℝ} (ht : 0 < t) (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) :
    eulerRayLoewnerKernel t x y =
      (Real.exp (t * x) - Real.exp (t * y)) /
        ((Real.exp (t * x) - 1) * (Real.exp (t * y) - 1) * (x - y)) := by
  have ha : Real.exp (t * x) - 1 ≠ 0 :=
    ne_of_gt (sub_pos.mpr (Real.one_lt_exp_iff.mpr (mul_pos ht hx)))
  have hb : Real.exp (t * y) - 1 ≠ 0 :=
    ne_of_gt (sub_pos.mpr (Real.one_lt_exp_iff.mpr (mul_pos ht hy)))
  have hd : x - y ≠ 0 := sub_ne_zero.mpr hxy
  simp only [eulerRayLoewnerKernel, if_neg hxy]
  field_simp
  ring

/-- Every nondegenerate two-node Gram of one full geometric Euler factor has negative determinant. -/
theorem eulerRayLoewnerKernel_two_node_negative_determinant
    {t x y : ℝ} (ht : 0 < t) (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) :
    eulerRayLoewnerKernel t x x * eulerRayLoewnerKernel t y y <
      eulerRayLoewnerKernel t x y * eulerRayLoewnerKernel t y x := by
  have ha : 1 < Real.exp (t * x) := Real.one_lt_exp_iff.mpr (mul_pos ht hx)
  have hb : 1 < Real.exp (t * y) := Real.one_lt_exp_iff.mpr (mul_pos ht hy)
  have hd : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have hgap := exp_gap_sq_gt t x y ht hxy
  have hmain := euler_det_algebra ha hb hd hgap
  have hxyK := eulerRayLoewnerKernel_offdiag ht hx hy hxy
  have hyxK := eulerRayLoewnerKernel_offdiag ht hy hx hxy.symm
  have hsym : eulerRayLoewnerKernel t y x = eulerRayLoewnerKernel t x y := by
    rw [hyxK, hxyK]
    field_simp [sub_ne_zero.mpr hxy, sub_ne_zero.mpr hxy.symm,
      ne_of_gt (sub_pos.mpr ha), ne_of_gt (sub_pos.mpr hb)]
    ring
  have hxx : eulerRayLoewnerKernel t x x =
      t * Real.exp (t * x) / (Real.exp (t * x) - 1) ^ (2 : ℕ) := by
    simp [eulerRayLoewnerKernel]
  have hyy : eulerRayLoewnerKernel t y y =
      t * Real.exp (t * y) / (Real.exp (t * y) - 1) ^ (2 : ℕ) := by
    simp [eulerRayLoewnerKernel]
  rw [hxx, hyy, hsym, hxyK, ← pow_two]
  exact hmain

/-- The complete `p`-local von Mangoldt log-derivative contribution to the real source cup. -/
noncomputable def primeEulerLogDerivLoewnerKernel (p : ℕ) (x y : ℝ) : ℝ :=
  Real.log (p : ℝ) * eulerRayLoewnerKernel (Real.log (p : ℝ)) x y

/-- The local log derivative is the full positive prime-power geometric series. -/
theorem eulerPrimePowerSeries_eq_closedForm {t x : ℝ} (ht : 0 < t) (hx : 0 < x) :
    (∑' k : ℕ, t * Real.exp (-(t * x * ((k : ℝ) + 1)))) =
      t / (Real.exp (t * x) - 1) := by
  let q : ℝ := Real.exp (-(t * x))
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [mul_pos ht hx])
  have hterm (k : ℕ) : Real.exp (-(t * x * ((k : ℝ) + 1))) = q ^ (k + 1) := by
    dsimp [q]
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  simp_rw [hterm, pow_succ, ← mul_assoc]
  have hrewrite : (fun k : ℕ => t * q ^ k * q) = fun k => (t * q) * q ^ k := by
    funext k
    ring
  rw [hrewrite, tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
  dsimp [q]
  rw [Real.exp_neg]
  have he : Real.exp (t * x) ≠ 0 := Real.exp_ne_zero _
  field_simp

/-- All powers of one actual prime, in the absolute Euler half-plane. -/
theorem primeEulerLogDeriv_primePowerSeries {p : ℕ} (hp : 2 ≤ p)
    {x : ℝ} (hx : 1 < x) :
    (∑' k : ℕ, Real.log (p : ℝ) *
      Real.exp (-(Real.log (p : ℝ) * x * ((k : ℝ) + 1)))) =
        Real.log (p : ℝ) /
          (Real.exp (Real.log (p : ℝ) * x) - 1) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  exact eulerPrimePowerSeries_eq_closedForm (Real.log_pos hpR) (by linarith)

/-- Local sign failure survives grouping every power of an actual prime. -/
theorem primeEulerLogDerivLoewnerKernel_two_node_negative_determinant
    {p : ℕ} (hp : 2 ≤ p) {x y : ℝ} (hx : 1 < x) (hy : 1 < y) (hxy : x ≠ y) :
    primeEulerLogDerivLoewnerKernel p x x *
        primeEulerLogDerivLoewnerKernel p y y <
      primeEulerLogDerivLoewnerKernel p x y *
        primeEulerLogDerivLoewnerKernel p y x := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have ht : 0 < Real.log (p : ℝ) := Real.log_pos hpR
  have h := eulerRayLoewnerKernel_two_node_negative_determinant ht
      (by linarith : 0 < x) (by linarith : 0 < y) hxy
  have ht2 : 0 < (Real.log (p : ℝ)) ^ (2 : ℕ) := sq_pos_of_pos ht
  dsimp [primeEulerLogDerivLoewnerKernel]
  calc
    _ = (Real.log (p : ℝ)) ^ (2 : ℕ) *
        (eulerRayLoewnerKernel (Real.log (p : ℝ)) x x *
          eulerRayLoewnerKernel (Real.log (p : ℝ)) y y) := by ring
    _ < (Real.log (p : ℝ)) ^ (2 : ℕ) *
        (eulerRayLoewnerKernel (Real.log (p : ℝ)) x y *
          eulerRayLoewnerKernel (Real.log (p : ℝ)) y x) :=
        mul_lt_mul_of_pos_left h ht2
    _ = _ := by ring

end

end RHTower
