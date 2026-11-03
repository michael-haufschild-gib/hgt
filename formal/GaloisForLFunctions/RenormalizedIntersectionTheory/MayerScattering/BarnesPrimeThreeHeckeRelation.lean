import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.BarnesHeckeRelation

/-!
# The determinant-three Barnes cones

Seven positive cones subdivide the four index-three sublattices of the integer plane.
Their boundary-weighted generating functions cover each nonzero residue once and each
vector divisible by three four times. Mellin integration gives the source Hecke relation.
-/

noncomputable section
open Complex Set MeasureTheory
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering

private def coneKernel (X Y : ℂ) : ℂ := (X + Y) / ((1 - X) * (1 - Y))

private theorem firstFan (X Y : ℂ) (hA : 1 - X ^ 3 ≠ 0)
    (hB : 1 - Y ^ 3 ≠ 0) (hU : 1 - X * Y ≠ 0) :
    coneKernel (X * Y) (Y ^ 3) + coneKernel (X ^ 3) (X * Y) =
      (X ^ 3 + Y ^ 3 + 2 * (X * Y) + 2 * (X * Y) ^ 2) /
        ((1 - X ^ 3) * (1 - Y ^ 3)) := by
  unfold coneKernel
  field_simp [hA, hB, hU]
  ring

private theorem secondFan (X Y : ℂ) (hA : 1 - X ^ 3 ≠ 0)
    (hB : 1 - Y ^ 3 ≠ 0) (hU : 1 - X ^ 2 * Y ≠ 0) (hV : 1 - X * Y ^ 2 ≠ 0) :
    coneKernel (X * Y ^ 2) (Y ^ 3) + coneKernel (X ^ 3) (X ^ 2 * Y) +
      coneKernel (X ^ 2 * Y) (X * Y ^ 2) =
      (X ^ 3 + Y ^ 3 + 2 * (X ^ 2 * Y) + 2 * (X * Y ^ 2)) /
        ((1 - X ^ 3) * (1 - Y ^ 3)) := by
  unfold coneKernel
  field_simp [hA, hB, hU, hV]
  ring

private theorem primeThreeKernel (X Y : ℂ) (hX : 1 - X ≠ 0) (hY : 1 - Y ≠ 0)
    (hA : 1 - X ^ 3 ≠ 0) (hB : 1 - Y ^ 3 ≠ 0) (hU : 1 - X * Y ≠ 0)
    (hV : 1 - X ^ 2 * Y ≠ 0) (hW : 1 - X * Y ^ 2 ≠ 0) :
    (coneKernel (X ^ 3) Y + coneKernel X (Y ^ 3)) +
      (coneKernel (X * Y) (Y ^ 3) + coneKernel (X ^ 3) (X * Y)) +
      (coneKernel (X * Y ^ 2) (Y ^ 3) + coneKernel (X ^ 3) (X ^ 2 * Y) +
        coneKernel (X ^ 2 * Y) (X * Y ^ 2)) = coneKernel X Y + 3 * coneKernel (X ^ 3) (Y ^ 3) := by
  rw [firstFan X Y hA hB hU, secondFan X Y hA hB hV hW]
  unfold coneKernel
  field_simp [hX, hY, hA, hB]
  ring

private def boundaryKernel (a b t : ℝ) : ℂ :=
  barnesConeKernel a b a t + barnesConeKernel a b b t

private theorem boundaryKernel_formula (a b t : ℝ) :
    boundaryKernel a b t = coneKernel (Real.exp (-a * t)) (Real.exp (-b * t)) := by
  unfold boundaryKernel barnesConeKernel coneKernel
  rw [add_div]

private theorem boundaryKernel_primeThree {a b t : ℝ}
    (ha : 0 < a) (hb : 0 < b) (ht : 0 < t) :
    (boundaryKernel (3 * a) b t + boundaryKernel a (3 * b) t) +
      (boundaryKernel (a + b) (3 * b) t + boundaryKernel (3 * a) (a + b) t) +
      (boundaryKernel (a + 2 * b) (3 * b) t + boundaryKernel (3 * a) (2 * a + b) t +
        boundaryKernel (2 * a + b) (a + 2 * b) t) =
      boundaryKernel a b t + 3 * boundaryKernel (3 * a) (3 * b) t := by
  have hexp (x y : ℝ) : (Real.exp (-(x + y) * t) : ℂ) =
      (Real.exp (-x * t) : ℂ) * (Real.exp (-y * t) : ℂ) := by
    rw [show -(x + y) * t = -x * t + -y * t by ring, Real.exp_add, Complex.ofReal_mul]
  have htwo (x : ℝ) : (Real.exp (-(2 * x) * t) : ℂ) = (Real.exp (-x * t) : ℂ) ^ 2 := by
    rw [show 2 * x = x + x by ring, hexp, pow_two]
  have hthree (x : ℝ) : (Real.exp (-(3 * x) * t) : ℂ) = (Real.exp (-x * t) : ℂ) ^ 3 := by
    rw [show 3 * x = 2 * x + x by ring, hexp, htwo]
    ring
  have hne (x : ℝ) (hx : 0 < x) : 1 - (Real.exp (-x * t) : ℂ) ≠ 0 := by
    intro h
    have he : Real.exp (-x * t) = 1 := by exact_mod_cast (sub_eq_zero.mp h).symm
    exact (ne_of_lt (exp_neg_mul_lt_one hx ht)) he
  have hA : 1 - (Real.exp (-a * t) : ℂ) ^ 3 ≠ 0 := by
    rw [← hthree]
    exact hne _ (by positivity)
  have hB : 1 - (Real.exp (-b * t) : ℂ) ^ 3 ≠ 0 := by
    rw [← hthree]
    exact hne _ (by positivity)
  have hU : 1 - (Real.exp (-a * t) : ℂ) * (Real.exp (-b * t) : ℂ) ≠ 0 := by
    rw [← hexp]
    exact hne _ (by positivity)
  have hV : 1 - (Real.exp (-a * t) : ℂ) ^ 2 * (Real.exp (-b * t) : ℂ) ≠ 0 := by
    rw [← htwo, ← hexp]
    exact hne _ (by positivity)
  have hW : 1 - (Real.exp (-a * t) : ℂ) * (Real.exp (-b * t) : ℂ) ^ 2 ≠ 0 := by
    rw [← htwo, ← hexp]
    exact hne _ (by positivity)
  simp only [boundaryKernel_formula, hthree, hexp, htwo]
  exact primeThreeKernel _ _ (hne a ha) (hne b hb) hA hB hU hV hW

private theorem cone_integrable {a b x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx : 0 < x) {w : ℂ} (hw : 2 < w.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (w - 1) * barnesConeKernel a b x t) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)]
  exact (integrableOn_cpow_mul_barnesConeKernel_Ioc ha hb hw).union
    (integrableOn_cpow_mul_barnesConeKernel_Ioi_one ha hb hx (by linarith))

private def boundaryIntegrand (w : ℂ) (a b t : ℝ) : ℂ :=
  (t : ℂ) ^ (w - 1) * boundaryKernel a b t

private theorem boundary_integrable {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {w : ℂ} (hw : 2 < w.re) : IntegrableOn (boundaryIntegrand w a b) (Ioi 0) := by
  refine ((cone_integrable ha hb ha hw).add (cone_integrable ha hb hb hw)).congr_fun
    (fun t _ => ?_) measurableSet_Ioi
  change (t : ℂ) ^ (w - 1) * barnesConeKernel a b a t +
    (t : ℂ) ^ (w - 1) * barnesConeKernel a b b t =
    (t : ℂ) ^ (w - 1) * (barnesConeKernel a b a t + barnesConeKernel a b b t)
  ring

private theorem boundary_mellin {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {w : ℂ} (hw : 2 < w.re) :
    Complex.Gamma w * barnesBoundaryPeriod w a b =
      ∫ t in Ioi (0 : ℝ), boundaryIntegrand w a b t := by
  rw [barnesBoundaryPeriod, mul_add,
    Gamma_mul_barnesDoubleZeta_eq_mellin ha hb ha hw,
    Gamma_mul_barnesDoubleZeta_eq_mellin ha hb hb hw]
  simp only [mellin, smul_eq_mul, boundaryIntegrand, boundaryKernel, mul_add]
  exact (integral_add (cone_integrable ha hb ha hw) (cone_integrable ha hb hb hw)).symm

/-- The seven determinant-three cones cover the quadrant once and its triple sublattice
three additional times, with the exact Barnes boundary weights. -/
theorem barnesBoundaryPeriod_hecke_three_cones {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {w : ℂ} (hw : 2 < w.re) :
    (barnesBoundaryPeriod w (3 * a) b + barnesBoundaryPeriod w a (3 * b)) +
      (barnesBoundaryPeriod w (a + b) (3 * b) + barnesBoundaryPeriod w (3 * a) (a + b)) +
      (barnesBoundaryPeriod w (a + 2 * b) (3 * b) + barnesBoundaryPeriod w (3 * a) (2 * a + b) +
        barnesBoundaryPeriod w (2 * a + b) (a + 2 * b)) =
      barnesBoundaryPeriod w a b + 3 * barnesBoundaryPeriod w (3 * a) (3 * b) := by
  have h3a : 0 < 3 * a := by positivity
  have h3b : 0 < 3 * b := by positivity
  have hab : 0 < a + b := by positivity
  have ha2b : 0 < a + 2 * b := by positivity
  have h2ab : 0 < 2 * a + b := by positivity
  have h0 := boundary_integrable h3a hb hw
  have h1 := boundary_integrable ha h3b hw
  have h2 := boundary_integrable hab h3b hw
  have h3 := boundary_integrable h3a hab hw
  have h4 := boundary_integrable ha2b h3b hw
  have h5 := boundary_integrable h3a h2ab hw
  have h6 := boundary_integrable h2ab ha2b hw
  have h01 : IntegrableOn (fun t => boundaryIntegrand w (3 * a) b t +
      boundaryIntegrand w a (3 * b) t) (Ioi 0) := h0.add h1
  have h23 : IntegrableOn (fun t => boundaryIntegrand w (a + b) (3 * b) t +
      boundaryIntegrand w (3 * a) (a + b) t) (Ioi 0) := h2.add h3
  have h45 : IntegrableOn (fun t => boundaryIntegrand w (a + 2 * b) (3 * b) t +
      boundaryIntegrand w (3 * a) (2 * a + b) t) (Ioi 0) := h4.add h5
  have h456 : IntegrableOn (fun t => boundaryIntegrand w (a + 2 * b) (3 * b) t +
      boundaryIntegrand w (3 * a) (2 * a + b) t +
      boundaryIntegrand w (2 * a + b) (a + 2 * b) t) (Ioi 0) := h45.add h6
  have h0123 : IntegrableOn (fun t =>
      (boundaryIntegrand w (3 * a) b t + boundaryIntegrand w a (3 * b) t) +
      (boundaryIntegrand w (a + b) (3 * b) t + boundaryIntegrand w (3 * a) (a + b) t))
      (Ioi 0) := h01.add h23
  apply mul_left_cancel₀ (Complex.Gamma_ne_zero_of_re_pos (by linarith : 0 < w.re))
  calc
    Complex.Gamma w * _ = ∫ t in Ioi (0 : ℝ),
        (boundaryIntegrand w (3 * a) b t + boundaryIntegrand w a (3 * b) t) +
        (boundaryIntegrand w (a + b) (3 * b) t + boundaryIntegrand w (3 * a) (a + b) t) +
        (boundaryIntegrand w (a + 2 * b) (3 * b) t + boundaryIntegrand w (3 * a) (2 * a + b) t +
          boundaryIntegrand w (2 * a + b) (a + 2 * b) t) := by
      rw [integral_add h0123 h456,
        integral_add h01 h23, integral_add h0 h1, integral_add h2 h3,
        integral_add h45 h6, integral_add h4 h5,
        ← boundary_mellin h3a hb hw, ← boundary_mellin ha h3b hw,
        ← boundary_mellin hab h3b hw, ← boundary_mellin h3a hab hw,
        ← boundary_mellin ha2b h3b hw, ← boundary_mellin h3a h2ab hw,
        ← boundary_mellin h2ab ha2b hw]
      ring
    _ = ∫ t in Ioi (0 : ℝ), boundaryIntegrand w a b t +
        3 * boundaryIntegrand w (3 * a) (3 * b) t := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      have h := congrArg (fun z : ℂ => (t : ℂ) ^ (w - 1) * z)
        (boundaryKernel_primeThree ha hb ht)
      dsimp only [boundaryIntegrand]
      linear_combination h
    _ = Complex.Gamma w * _ := by
      rw [integral_add (boundary_integrable ha hb hw)
        ((boundary_integrable h3a h3b hw).const_mul 3), integral_const_mul,
        ← boundary_mellin ha hb hw, ← boundary_mellin h3a h3b hw]
      ring

#print axioms barnesBoundaryPeriod_hecke_three_cones

private theorem boundary_scale_second (w : ℂ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    barnesBoundaryPeriod w a b =
      (b : ℂ) ^ (-w) * barnesBoundaryPeriod w (a / b) 1 := by
  have h := barnesBoundaryPeriod_scale w (c := b) (a := a / b) (b := 1)
    hb (div_pos ha hb) zero_lt_one
  rw [show b * (a / b) = a by field_simp [hb.ne'], mul_one] at h
  exact h

/-- Homogeneity turns the seven source cones into the prime-three period Hecke law. -/
theorem barnesBoundaryPeriod_hecke_three {a : ℝ} (ha : 0 < a) {w : ℂ} (hw : 2 < w.re) :
    (barnesBoundaryPeriod w (3 * a) 1 +
        (3 : ℂ) ^ (-w) * barnesBoundaryPeriod w (a / 3) 1) +
      ((3 : ℂ) ^ (-w) * barnesBoundaryPeriod w ((a + 1) / 3) 1 +
        ((a + 1 : ℝ) : ℂ) ^ (-w) * barnesBoundaryPeriod w (3 * a / (a + 1)) 1) +
      ((3 : ℂ) ^ (-w) * barnesBoundaryPeriod w ((a + 2) / 3) 1 +
        ((2 * a + 1 : ℝ) : ℂ) ^ (-w) * barnesBoundaryPeriod w (3 * a / (2 * a + 1)) 1 +
        ((a + 2 : ℝ) : ℂ) ^ (-w) * barnesBoundaryPeriod w ((2 * a + 1) / (a + 2)) 1) =
      (1 + 3 * (3 : ℂ) ^ (-w)) * barnesBoundaryPeriod w a 1 := by
  have h := barnesBoundaryPeriod_hecke_three_cones ha zero_lt_one hw
  simp only [mul_one] at h
  rw [boundary_scale_second w ha (by norm_num : (0 : ℝ) < 3),
    boundary_scale_second w (by linarith : 0 < a + 1) (by norm_num : (0 : ℝ) < 3),
    boundary_scale_second w (by positivity : 0 < 3 * a) (by linarith : 0 < a + 1),
    boundary_scale_second w (by linarith : 0 < a + 2) (by norm_num : (0 : ℝ) < 3),
    boundary_scale_second w (by positivity : 0 < 3 * a) (by linarith : 0 < 2 * a + 1),
    boundary_scale_second w (by linarith : 0 < 2 * a + 1) (by linarith : 0 < a + 2)] at h
  have hscale := barnesBoundaryPeriod_scale w (c := 3) (a := a) (b := 1)
    (by norm_num) ha zero_lt_one
  simp only [mul_one, Complex.ofReal_ofNat] at hscale
  rw [hscale] at h
  simp only [Complex.ofReal_ofNat] at h
  linear_combination h

#print axioms barnesBoundaryPeriod_hecke_three

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering
