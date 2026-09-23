import GaloisForLFunctions.HTGeometry.SturmSelfAdjoint

/-!
# The Wronskian of two Sturm solutions is constant

For two solutions of the same equation `(p u')' = q u`, the weighted Wronskian

`W = u (p v') - v (p u')`

has derivative `u (p v')' - v (p u')' = u q v - v q u = 0`.

Constancy of the Wronskian is the standard route to simplicity of a Sturm eigenvalue: if both
solutions satisfy the same boundary condition the Wronskian vanishes there, hence everywhere, and
the solutions are proportional wherever one of them is nonzero.
-/

open Set

namespace HTGeometry

/-- **The Wronskian of two solutions of the same Sturm equation has vanishing derivative.** -/
theorem hasDerivAt_sturmWronskian {p q u v u' v' pu' pv' : ℝ → ℝ} {x : ℝ}
    (hu : HasDerivAt u (u' x) x) (hv : HasDerivAt v (v' x) x)
    (hpu : HasDerivAt (fun s : ℝ => p s * u' s) (pu' x) x)
    (hpv : HasDerivAt (fun s : ℝ => p s * v' s) (pv' x) x)
    (heu : pu' x = q x * u x) (hev : pv' x = q x * v x) :
    HasDerivAt (fun s : ℝ => u s * (p s * v' s) - v s * (p s * u' s)) 0 x := by
  have h1 := hu.mul hpv
  have h2 := hv.mul hpu
  have h := h1.sub h2
  refine h.congr_deriv ?_
  rw [heu, hev]
  ring

/-- **The Wronskian is constant on an interval.** -/
theorem sturmWronskian_eq_of_hasDerivAt {p q u v u' v' pu' pv' : ℝ → ℝ} {a b : ℝ}
    (hcont : ContinuousOn (fun s : ℝ => u s * (p s * v' s) - v s * (p s * u' s)) (Icc a b))
    (hu : ∀ x ∈ Ico a b, HasDerivAt u (u' x) x)
    (hv : ∀ x ∈ Ico a b, HasDerivAt v (v' x) x)
    (hpu : ∀ x ∈ Ico a b, HasDerivAt (fun s : ℝ => p s * u' s) (pu' x) x)
    (hpv : ∀ x ∈ Ico a b, HasDerivAt (fun s : ℝ => p s * v' s) (pv' x) x)
    (heu : ∀ x ∈ Ico a b, pu' x = q x * u x)
    (hev : ∀ x ∈ Ico a b, pv' x = q x * v x) (y : ℝ) (hy : y ∈ Icc a b) :
    u y * (p y * v' y) - v y * (p y * u' y) = u a * (p a * v' a) - v a * (p a * u' a) := by
  refine constant_of_has_deriv_right_zero hcont (fun x hx => ?_) y hy
  exact (hasDerivAt_sturmWronskian (hu x hx) (hv x hx) (hpu x hx) (hpv x hx)
    (heu x hx) (hev x hx)).hasDerivWithinAt

/-- **A vanishing Wronskian makes two solutions proportional.**  Where the first solution and the
weight are nonzero, the quotient has vanishing derivative, hence is constant. -/
theorem div_eq_of_sturmWronskian_eq_zero {p u v u' v' : ℝ → ℝ} {a b : ℝ}
    (hu : ∀ x ∈ Ico a b, HasDerivAt u (u' x) x)
    (hv : ∀ x ∈ Ico a b, HasDerivAt v (v' x) x)
    (hune : ∀ x ∈ Ico a b, u x ≠ 0)
    (hpne : ∀ x ∈ Ico a b, p x ≠ 0)
    (hW : ∀ x ∈ Ico a b, u x * (p x * v' x) - v x * (p x * u' x) = 0)
    (hcont : ContinuousOn (fun x : ℝ => v x / u x) (Icc a b))
    (y : ℝ) (hy : y ∈ Icc a b) :
    v y / u y = v a / u a := by
  refine constant_of_has_deriv_right_zero hcont (fun x hx => ?_) y hy
  have hnum : v' x * u x - v x * u' x = 0 := by
    have h := hW x hx
    have hp := hpne x hx
    have hfac : p x * (u x * v' x - v x * u' x) = 0 := by
      rw [← h]
      ring
    have := (mul_eq_zero.mp hfac).resolve_left hp
    linarith [this]
  have hd : HasDerivAt (fun s : ℝ => v s / u s)
      ((v' x * u x - v x * u' x) / (u x) ^ (2 : ℕ)) x := (hv x hx).div (hu x hx) (hune x hx)
  rw [hnum, zero_div] at hd
  exact hd.hasDerivWithinAt

/-- **Simplicity.**  Under the same hypotheses the second solution is a fixed multiple of the
first. -/
theorem eq_const_mul_of_sturmWronskian_eq_zero {p u v u' v' : ℝ → ℝ} {a b : ℝ}
    (hu : ∀ x ∈ Ico a b, HasDerivAt u (u' x) x)
    (hv : ∀ x ∈ Ico a b, HasDerivAt v (v' x) x)
    (hune : ∀ x ∈ Ico a b, u x ≠ 0)
    (huneC : ∀ x ∈ Icc a b, u x ≠ 0)
    (hpne : ∀ x ∈ Ico a b, p x ≠ 0)
    (hW : ∀ x ∈ Ico a b, u x * (p x * v' x) - v x * (p x * u' x) = 0)
    (hcont : ContinuousOn (fun x : ℝ => v x / u x) (Icc a b))
    (y : ℝ) (hy : y ∈ Icc a b) :
    v y = (v a / u a) * u y := by
  have h := div_eq_of_sturmWronskian_eq_zero hu hv hune hpne hW hcont y hy
  have hy0 : u y ≠ 0 := huneC y hy
  calc v y = v y / u y * u y := (div_mul_cancel₀ (v y) hy0).symm
    _ = v a / u a * u y := by rw [h]

/-- **A vanishing weight at an endpoint forces the Wronskian to vanish identically.**  This is the
singular boundary condition of the prolate problem: the weight `1 - t^(2 : ℕ)` vanishes at the ends of the
band, so no boundary condition needs to be imposed by hand. -/
theorem sturmWronskian_eq_zero_of_weight_eq_zero {p q u v u' v' pu' pv' : ℝ → ℝ} {a b : ℝ}
    (hpa : p a = 0)
    (hcont : ContinuousOn (fun s : ℝ => u s * (p s * v' s) - v s * (p s * u' s)) (Icc a b))
    (hu : ∀ x ∈ Ico a b, HasDerivAt u (u' x) x)
    (hv : ∀ x ∈ Ico a b, HasDerivAt v (v' x) x)
    (hpu : ∀ x ∈ Ico a b, HasDerivAt (fun s : ℝ => p s * u' s) (pu' x) x)
    (hpv : ∀ x ∈ Ico a b, HasDerivAt (fun s : ℝ => p s * v' s) (pv' x) x)
    (heu : ∀ x ∈ Ico a b, pu' x = q x * u x)
    (hev : ∀ x ∈ Ico a b, pv' x = q x * v x) (y : ℝ) (hy : y ∈ Icc a b) :
    u y * (p y * v' y) - v y * (p y * u' y) = 0 := by
  have hconst := sturmWronskian_eq_of_hasDerivAt (q := q) (pu' := pu') (pv' := pv')
    hcont hu hv hpu hpv heu hev y hy
  rw [hconst, hpa]
  ring

/-- **Simplicity at a singular endpoint.**  Two solutions of the same Sturm equation on an interval
whose weight vanishes at the left endpoint are proportional. -/
theorem eq_const_mul_of_weight_eq_zero {p q u v u' v' pu' pv' : ℝ → ℝ} {a b : ℝ}
    (hpa : p a = 0)
    (hcont : ContinuousOn (fun s : ℝ => u s * (p s * v' s) - v s * (p s * u' s)) (Icc a b))
    (hqcont : ContinuousOn (fun x : ℝ => v x / u x) (Icc a b))
    (hu : ∀ x ∈ Ico a b, HasDerivAt u (u' x) x)
    (hv : ∀ x ∈ Ico a b, HasDerivAt v (v' x) x)
    (hpu : ∀ x ∈ Ico a b, HasDerivAt (fun s : ℝ => p s * u' s) (pu' x) x)
    (hpv : ∀ x ∈ Ico a b, HasDerivAt (fun s : ℝ => p s * v' s) (pv' x) x)
    (heu : ∀ x ∈ Ico a b, pu' x = q x * u x)
    (hev : ∀ x ∈ Ico a b, pv' x = q x * v x)
    (hune : ∀ x ∈ Ico a b, u x ≠ 0) (huneC : ∀ x ∈ Icc a b, u x ≠ 0)
    (hpne : ∀ x ∈ Ico a b, p x ≠ 0) (y : ℝ) (hy : y ∈ Icc a b) :
    v y = (v a / u a) * u y := by
  refine eq_const_mul_of_sturmWronskian_eq_zero hu hv hune huneC hpne ?_ hqcont y hy
  intro x hx
  exact sturmWronskian_eq_zero_of_weight_eq_zero (q := q) (pu' := pu') (pv' := pv')
    hpa hcont hu hv hpu hpv heu hev x (Ico_subset_Icc_self hx)

end HTGeometry
