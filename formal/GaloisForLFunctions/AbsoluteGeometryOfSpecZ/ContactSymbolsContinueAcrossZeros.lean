import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerContactDirichletSeries

/-!
# Holomorphic contact symbols continue across the zeros

The entire zeta residue unit clears the denominator of the contact symbol.
The identity theorem determines any holomorphic continuation from its
values in the absolute-convergence half-plane.
-/

noncomputable section

open Complex Filter Topology Set

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-- A holomorphic function with the initial contact Dirichlet symbol
agrees with that symbol throughout its open contact half-plane. -/
theorem contactSymbol_eq_of_holomorphic
    {a : ℝ} (ha : 0 < a) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F {z : ℂ | 1 - 2 * a < z.re})
    (hinitial : ∀ z : ℂ, 2 < z.re → F z =
      riemannZeta (z + ((2 * a : ℝ) : ℂ)) *
        (-deriv riemannZeta (z + (a : ℂ)) / riemannZeta (z + (a : ℂ)) -
          riemannZeta (z + (a : ℂ))))
    {s : ℂ} (hs : 1 - 2 * a < s.re) (hs1 : s + (a : ℂ) ≠ 1)
    (hζ : riemannZeta (s + (a : ℂ)) ≠ 0) :
    F s = riemannZeta (s + ((2 * a : ℝ) : ℂ)) *
      (-deriv riemannZeta (s + (a : ℂ)) / riemannZeta (s + (a : ℂ)) -
        riemannZeta (s + (a : ℂ))) := by
  let R := _root_.RHTower.zetaResidueUnit
  have hRa : ∀ z, AnalyticAt ℂ R z := _root_.RHTower.analyticAt_zetaResidueUnit
  have hderivR (z : ℂ) (hz : z ≠ 1) :
      deriv R z = riemannZeta z + (z - 1) * deriv riemannZeta z := by
    have hev : R =ᶠ[𝓝 z] fun w => (w - 1) * riemannZeta w := by
      filter_upwards [isOpen_ne.mem_nhds hz] with w hw
      exact ArithmeticCorrelationGeometry.zetaResidueUnit_of_ne' hw
    rw [hev.deriv_eq]
    have hd := ((hasDerivAt_id z).sub_const 1).mul
      (differentiableAt_riemannZeta hz).hasDerivAt
    have hh := hd.deriv
    simp only [id_eq, one_mul] at hh
    rw [show ((fun x : ℂ => x - 1) * riemannZeta) =
      (fun w => (w - 1) * riemannZeta w) from rfl] at hh
    exact hh
  let U : Set ℂ := {z | 1 - 2 * a < z.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUc : IsPreconnected U := (convex_halfSpace_re_gt (1 - 2 * a)).isPreconnected
  let H : ℂ → ℂ := fun z => R (z + a) * ((z + a - 1) *
    F z) +
    riemannZeta (z + ((2 * a : ℝ) : ℂ)) *
      (R (z + a) ^ 2 + ((z + a - 1) * deriv R (z + a) - R (z + a)))
  have hRd : DifferentiableOn ℂ (fun z : ℂ => R (z + a)) U := fun z _ =>
    ((hRa (z + a)).differentiableAt.comp z (differentiableAt_id.add_const _)).differentiableWithinAt
  have hR'd : DifferentiableOn ℂ (fun z : ℂ => deriv R (z + a)) U := fun z _ =>
    ((hRa (z + a)).deriv.differentiableAt.comp z
      (differentiableAt_id.add_const _)).differentiableWithinAt
  have hZd : DifferentiableOn ℂ (fun z : ℂ => riemannZeta (z + ((2 * a : ℝ) : ℂ))) U := by
    intro z hz
    have hne : z + ((2 * a : ℝ) : ℂ) ≠ 1 := by
      intro he
      have he' := congrArg Complex.re he
      simp only [add_re, ofReal_re, one_re] at he'
      have hh : 1 - 2 * a < z.re := hz
      linarith only [he', hh]
    exact ((differentiableAt_riemannZeta hne).comp z
      (differentiableAt_id.add_const _)).differentiableWithinAt
  have hP : DifferentiableOn ℂ (fun z : ℂ => z + (a : ℂ) - 1) U :=
    (differentiableOn_id.add_const _).sub_const _
  have hHd : DifferentiableOn ℂ H U :=
    (hRd.mul (hP.mul hF)).add
      (hZd.mul ((hRd.pow 2).add ((hP.mul hR'd).sub hRd)))
  have hxU : (3 : ℂ) ∈ U := by
    change 1 - 2 * a < (3 : ℂ).re
    norm_num
    linarith only [ha]
  have hzero : H =ᶠ[𝓝 (3 : ℂ)] 0 := by
    have ho : {z : ℂ | 2 < z.re} ∈ 𝓝 (3 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [ho] with z hz
    change 2 < z.re at hz
    have hza : 1 < (z + (a : ℂ)).re := by
      simp only [add_re, ofReal_re]
      linarith only [hz, ha]
    have hz1 : z + (a : ℂ) ≠ 1 := by
      intro he
      rw [he, one_re] at hza
      exact lt_irrefl 1 hza
    have hzne := riemannZeta_ne_zero_of_one_lt_re hza
    dsimp only [H, Pi.zero_apply]
    rw [hinitial z hz, hderivR _ hz1,
      show R (z + a) = (z + a - 1) * riemannZeta (z + a) from
        ArithmeticCorrelationGeometry.zetaResidueUnit_of_ne' hz1]
    field_simp [hzne] <;> ring
  have hEq := (hHd.analyticOnNhd hU).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    hUc hxU hzero
  have hv := hEq (show s ∈ U from hs)
  dsimp only [H, Pi.zero_apply] at hv
  rw [hderivR _ hs1, show R (s + a) = (s + a - 1) * riemannZeta (s + a) from
    ArithmeticCorrelationGeometry.zetaResidueUnit_of_ne' hs1] at hv
  have hkey : riemannZeta (s + a) * F s +
      riemannZeta (s + ((2 * a : ℝ) : ℂ)) *
        (riemannZeta (s + a) ^ 2 + deriv riemannZeta (s + a)) = 0 := by
    have hmul : (s + a - 1) ^ 2 *
        (riemannZeta (s + a) * F s +
          riemannZeta (s + ((2 * a : ℝ) : ℂ)) *
            (riemannZeta (s + a) ^ 2 + deriv riemannZeta (s + a))) = 0 := by
      linear_combination hv
    exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero 2 (sub_ne_zero.mpr hs1))
  apply mul_left_cancel₀ hζ
  calc
    _ = -riemannZeta (s + ((2 * a : ℝ) : ℂ)) *
        (riemannZeta (s + a) ^ 2 + deriv riemannZeta (s + a)) := by linear_combination hkey
    _ = _ := by field_simp [hζ] <;> ring

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
