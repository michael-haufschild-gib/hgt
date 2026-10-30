import Mathlib

/-!
# Tools for piecewise matrix certificates

Generic steps used by the piecewise odd-four certificates: a polynomial in `t` is its affine part
up to the sum of its higher coefficients times `ρ^e` on `|t| ≤ ρ`; an entrywise affine model with
remainder radius gives a positive semidefinite matrix as soon as the two endpoint matrices, with
the row radii removed from the diagonal, are positive semidefinite; and `e^u` is affine up to `u²`
on `|u| ≤ 1`.
-/

namespace RHTower.ThetaCuspOddFourCertificateTools
noncomputable section
open Finset

/-- Higher-order part of a polynomial in `t` on `|t| ≤ ρ`. -/
theorem abs_poly_sub_affine_le (c : ℕ → ℝ) (n : ℕ) {t ρ : ℝ} (ht : |t| ≤ ρ) :
    |(∑ e ∈ range (n+2), c e * t^e) - c 0 - c 1 * t| ≤ ∑ e ∈ range n, |c (e+2)| * ρ^(e+2) := by
  have hρ : 0 ≤ ρ := (abs_nonneg t).trans ht
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [pow_zero, mul_one, pow_one, zero_add]
  rw [show (∑ e ∈ range n, c (e+1+1) * t^(e+1+1)) + c 1 * t + c 0 - c 0 - c 1 * t =
      ∑ e ∈ range n, c (e+2) * t^(e+2) by ring]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun e _ => ?_)
  rw [abs_mul, abs_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg t) ht _) (abs_nonneg _)

/-- A polynomial in `t` is bounded by the sum of its coefficients times `ρ^e`. -/
theorem abs_poly_le (c : ℕ → ℝ) (n : ℕ) {t ρ : ℝ} (ht : |t| ≤ ρ) :
    |∑ e ∈ range n, c e * t^e| ≤ ∑ e ∈ range n, |c e| * ρ^e := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun e _ => ?_)
  rw [abs_mul, abs_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg t) ht _) (abs_nonneg _)

/-- `e^u` is `1 + u` up to `u²` on `|u| ≤ 1`. -/
theorem abs_exp_sub_affine_le {u : ℝ} (hu : |u| ≤ 1) : |Real.exp u - (1 + u)| ≤ u^2 := by
  have h := Real.abs_exp_sub_one_sub_id_le hu
  rwa [show Real.exp u - 1 - u = Real.exp u - (1 + u) by ring] at h

/-- **Endpoint criterion.** If each entry of `W` is `A + tB` up to `R` with `|t| ≤ ρ`, `ρ > 0`,
and both `A ± ρB` minus the row radii of `R` on the diagonal are positive semidefinite as
quadratic forms, then `W` is positive semidefinite as a quadratic form. -/
theorem quadForm_nonneg_of_endpoints (W A B R : Fin 4 → Fin 4 → ℝ) {t ρ : ℝ} (hρ : 0 < ρ)
    (ht : |t| ≤ ρ) (hW : ∀ i j, |W i j - (A i j + t * B i j)| ≤ R i j)
    (hplus : ∀ y : Fin 4 → ℝ, 0 ≤ ∑ i, ∑ j, y i * y j * (A i j + ρ * B i j) -
      ∑ i, ((∑ j, R i j) + (∑ j, R j i))/2 * y i^2)
    (hminus : ∀ y : Fin 4 → ℝ, 0 ≤ ∑ i, ∑ j, y i * y j * (A i j - ρ * B i j) -
      ∑ i, ((∑ j, R i j) + (∑ j, R j i))/2 * y i^2)
    (y : Fin 4 → ℝ) : 0 ≤ ∑ i, ∑ j, y i * y j * W i j := by
  set Rd := ∑ i, ((∑ j, R i j) + (∑ j, R j i))/2 * y i^2 with hRd
  -- the remainder costs at most the diagonal radius form
  have hrem : -(Rd) ≤ ∑ i, ∑ j, y i * y j * (W i j - (A i j + t * B i j)) := by
    have hR0 : ∀ i j, 0 ≤ R i j := fun i j => (abs_nonneg _).trans (hW i j)
    have h1 : ∀ i j, -(R i j * ((y i^2 + y j^2)/2)) ≤ y i * y j * (W i j - (A i j + t * B i j)) := by
      intro i j
      have hy : |y i * y j| ≤ (y i^2 + y j^2)/2 := by
        rw [abs_mul]
        nlinarith [sq_nonneg (|y i| - |y j|), sq_abs (y i), sq_abs (y j)]
      have hp := mul_le_mul (hy) (hW i j) (abs_nonneg _) (by positivity)
      have := neg_abs_le (y i * y j * (W i j - (A i j + t * B i j)))
      rw [abs_mul] at this
      nlinarith
    have h2 : ∑ i, ∑ j, R i j * ((y i^2 + y j^2)/2) = Rd := by
      rw [hRd]
      simp only [Fin.sum_univ_four]
      ring
    rw [← h2, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun j _ => h1 i j
  -- the affine part is a convex combination of the endpoints
  have hconv : 0 ≤ ∑ i, ∑ j, y i * y j * (A i j + t * B i j) - Rd := by
    have hp := hplus y
    have hm := hminus y
    have ht1 : 0 ≤ ρ + t := by linarith [neg_abs_le t]
    have ht2 : 0 ≤ ρ - t := by linarith [le_abs_self t]
    have hcomb : (∑ i, ∑ j, y i * y j * (A i j + t * B i j) - Rd) * (2*ρ) =
        (ρ + t) * (∑ i, ∑ j, y i * y j * (A i j + ρ * B i j) - Rd) +
        (ρ - t) * (∑ i, ∑ j, y i * y j * (A i j - ρ * B i j) - Rd) := by
      simp only [Fin.sum_univ_four]
      ring
    have : 0 ≤ (∑ i, ∑ j, y i * y j * (A i j + t * B i j) - Rd) * (2*ρ) := by
      rw [hcomb]; positivity
    exact nonneg_of_mul_nonneg_left this (by linarith)
  have hsplit : ∑ i, ∑ j, y i * y j * W i j =
      ∑ i, ∑ j, y i * y j * (A i j + t * B i j) +
        ∑ i, ∑ j, y i * y j * (W i j - (A i j + t * B i j)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hsplit]
  linarith


/-! ### Exponential enclosures -/

/-- Upper enclosure of `e^{n+f}` for `0 ≤ f ≤ 1`. -/
theorem exp_nat_add_le (n : ℕ) {f : ℝ} (hf0 : 0 ≤ f) (hf1 : f ≤ 1) :
    Real.exp (n + f) ≤ (2.7182818286 : ℝ)^n *
      ((∑ m ∈ range 8, f^m / m.factorial) + f^8 * (9 / (40320 * 8))) := by
  rw [Real.exp_add, ← Real.exp_one_pow]
  have h1 : Real.exp 1 ^ n ≤ (2.7182818286 : ℝ)^n :=
    pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le n
  have h2 := Real.exp_bound (x := f) (by rw [abs_of_nonneg hf0]; exact hf1) (n := 8) (by norm_num)
  have h3 : Real.exp f ≤ (∑ m ∈ range 8, f^m / m.factorial) + f^8 * (9 / (40320 * 8)) := by
    have := (abs_le.mp h2).2
    rw [abs_of_nonneg hf0] at this
    norm_num [Nat.factorial] at this ⊢
    linarith
  exact mul_le_mul h1 h3 (Real.exp_pos f).le (by positivity)

/-- Lower enclosure of `e^{n+f}` for `0 ≤ f`. -/
theorem le_exp_nat_add (n : ℕ) {f : ℝ} (hf0 : 0 ≤ f) :
    (2.7182818283 : ℝ)^n * (∑ m ∈ range 8, f^m / m.factorial) ≤ Real.exp (n + f) := by
  rw [Real.exp_add, ← Real.exp_one_pow]
  have h1 : (2.7182818283 : ℝ)^n ≤ Real.exp 1 ^ n :=
    pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le n
  exact mul_le_mul h1 (Real.sum_le_exp_of_nonneg hf0 8) (by positivity) (by positivity)

/-! ### Entry components -/

/-- The linearized exponential component `c e^{-3q} P` around the piece center. -/
theorem comp_exp_bound {c E0 zl zh P p0 p1 rp Pm ρ t : ℝ} (hc : 0 ≤ c) (hzl : 0 ≤ zl)
    (hE : zl ≤ E0 ∧ E0 ≤ zh) (ht : |t| ≤ ρ) (h3ρ : 3*ρ ≤ 1)
    (hP : |P - p0 - p1*t| ≤ rp) (hPm : |P| ≤ Pm) :
    |c*(E0*Real.exp (-3*t))*P - (c*((zl+zh)/2)*p0 + c*((zl+zh)/2)*(p1 - 3*p0)*t)| ≤
      c*((zh-zl)/2)*(1+3*ρ+9*ρ^2)*Pm + c*((zl+zh)/2)*(9*ρ^2*Pm + rp + 3*ρ*(|p1| * ρ + rp)) := by
  have hρ : 0 ≤ ρ := (abs_nonneg t).trans ht
  set Zm := (zl+zh)/2 with hZm
  have hZm0 : 0 ≤ Zm := by rw [hZm]; linarith [hE.1, hE.2]
  set u := -3*t with hu
  have hu1 : |u| ≤ 1 := by rw [hu, abs_mul]; norm_num; linarith
  have hu3 : |u| ≤ 3*ρ := by rw [hu, abs_mul]; norm_num; linarith
  have hexp := abs_exp_sub_affine_le hu1
  have hexpU : Real.exp u ≤ 1+3*ρ+9*ρ^2 := by
    have := (abs_le.mp hexp).2
    have hu2 : u^2 ≤ 9*ρ^2 := by
      have := mul_le_mul hu3 hu3 (abs_nonneg _) (by positivity); rw [← abs_mul, ← pow_two, abs_pow, sq_abs] at this
      nlinarith
    linarith [le_abs_self u]
  have hEZ : |E0 - Zm| ≤ (zh-zl)/2 := by rw [abs_le, hZm]; constructor <;> linarith [hE.1, hE.2]
  have hPp : |P - p0| ≤ |p1| * ρ + rp := by
    have : |P - p0| ≤ |P - p0 - p1*t| + |p1*t| := by
      calc |P - p0| = |(P - p0 - p1*t) + p1*t| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    rw [abs_mul] at this
    nlinarith [mul_le_mul_of_nonneg_left ht (abs_nonneg p1)]
  -- decomposition
  have hdec : c*(E0*Real.exp u)*P - (c*Zm*p0 + c*Zm*(p1 - 3*p0)*t) =
      c*((E0 - Zm)*Real.exp u*P) + c*Zm*((Real.exp u - (1+u))*P) +
        c*Zm*((P - p0 - p1*t) + u*(P - p0)) := by
    rw [hu]; ring
  rw [hdec]
  have hb1 : |c*((E0 - Zm)*Real.exp u*P)| ≤ c*((zh-zl)/2)*(1+3*ρ+9*ρ^2)*Pm := by
    rw [abs_mul, abs_of_nonneg hc, abs_mul, abs_mul, abs_of_pos (Real.exp_pos u)]
    have hw0 : 0 ≤ (zh-zl)/2 := by linarith [abs_nonneg (E0 - Zm), hEZ]
    have hr0 : 0 ≤ 1+3*ρ+9*ρ^2 := by positivity
    have := mul_le_mul (mul_le_mul hEZ hexpU (Real.exp_pos u).le hw0) hPm
      (abs_nonneg _) (mul_nonneg hw0 hr0)
    nlinarith [mul_le_mul_of_nonneg_left this hc]
  have hb2 : |c*Zm*((Real.exp u - (1+u))*P)| ≤ c*Zm*(9*ρ^2*Pm) := by
    rw [abs_mul, abs_of_nonneg (mul_nonneg hc hZm0), abs_mul]
    have hu2 : u^2 ≤ 9*ρ^2 := by
      have := mul_le_mul hu3 hu3 (abs_nonneg _) (by positivity); rw [← abs_mul, ← pow_two, abs_pow, sq_abs] at this
      nlinarith
    have hPm0 : 0 ≤ Pm := (abs_nonneg _).trans hPm
    have := mul_le_mul (hexp.trans hu2) hPm (abs_nonneg _) (by positivity)
    exact mul_le_mul_of_nonneg_left this (mul_nonneg hc hZm0)
  have hb3 : |c*Zm*((P - p0 - p1*t) + u*(P - p0))| ≤ c*Zm*(rp + 3*ρ*(|p1| * ρ + rp)) := by
    rw [abs_mul, abs_of_nonneg (mul_nonneg hc hZm0)]
    refine mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add hP ?_)) (mul_nonneg hc hZm0)
    rw [abs_mul]
    exact mul_le_mul hu3 hPp (abs_nonneg _) (by positivity)
  calc _ ≤ |c*((E0 - Zm)*Real.exp u*P)| + |c*Zm*((Real.exp u - (1+u))*P)| +
        |c*Zm*((P - p0 - p1*t) + u*(P - p0))| := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := by nlinarith [hb1, hb2, hb3]

/-- A crude exponential component `c e^{-sq} P` with `e^{-sq} ≤ U`. -/
theorem comp_crude_bound {c E P U Pm : ℝ} (hc : 0 ≤ c) (hE0 : 0 ≤ E) (hE : E ≤ U)
    (hPm : |P| ≤ Pm) : |c*E*P - 0| ≤ c*U*Pm := by
  rw [sub_zero, abs_mul, abs_mul, abs_of_nonneg hc, abs_of_nonneg hE0]
  exact mul_le_mul (mul_le_mul_of_nonneg_left hE hc) hPm (abs_nonneg _)
    (mul_nonneg hc (hE0.trans hE))


/-- Reciprocal enclosure of `e^{-x}` from an enclosure of `e^x`. -/
theorem exp_neg_bounds {x L U : ℝ} (hL0 : 0 < L) (hL : L ≤ Real.exp x) (hU : Real.exp x ≤ U) :
    1/U ≤ Real.exp (-x) ∧ Real.exp (-x) ≤ 1/L := by
  rw [Real.exp_neg]
  constructor
  · rw [one_div]; exact inv_anti₀ (Real.exp_pos x) hU
  · rw [one_div]; exact inv_anti₀ hL0 hL

end
end RHTower.ThetaCuspOddFourCertificateTools
