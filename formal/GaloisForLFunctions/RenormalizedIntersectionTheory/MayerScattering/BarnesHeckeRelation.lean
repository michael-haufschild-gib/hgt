import GaloisForLFunctions.HTGeometry.BarnesDoubleZetaContinuation

/-!
# The Hecke relation of the two boundary Barnes cones

The four determinant-two cones cover the original quadrant once and its even-even sublattice
twice more, with axis points counted once and interior points twice. Their generating functions
give an exact rational identity. Mellin integration proves the corresponding Hecke eigenvalue
in the absolute chamber, without a spectral assumption.
-/

noncomputable section
open Complex Set MeasureTheory
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering

/-- The two boundary Barnes cones, including both axis rays. -/
def barnesBoundaryPeriod (w : ℂ) (a b : ℝ) : ℂ :=
  barnesDoubleZeta a b w (a : ℂ) + barnesDoubleZeta a b w (b : ℂ)

private def boundaryKernel (a b t : ℝ) : ℂ :=
  barnesConeKernel a b a t + barnesConeKernel a b b t

private theorem boundaryKernel_formula (a b t : ℝ) :
    boundaryKernel a b t =
      ((Real.exp (-a * t) : ℂ) + (Real.exp (-b * t) : ℂ)) /
        ((1 - (Real.exp (-a * t) : ℂ)) * (1 - (Real.exp (-b * t) : ℂ))) := by
  unfold boundaryKernel barnesConeKernel
  rw [add_div]

private theorem cone_rational_identity (X Y : ℂ)
    (hX : 1 - X ≠ 0) (hY : 1 - Y ≠ 0)
    (hX2 : 1 - X ^ 2 ≠ 0) (hY2 : 1 - Y ^ 2 ≠ 0) (hXY : 1 - X * Y ≠ 0) :
    (X ^ 2 + Y) / ((1 - X ^ 2) * (1 - Y)) +
      (X + Y ^ 2) / ((1 - X) * (1 - Y ^ 2)) +
      (X * Y + Y ^ 2) / ((1 - X * Y) * (1 - Y ^ 2)) +
      (X ^ 2 + X * Y) / ((1 - X ^ 2) * (1 - X * Y)) =
      (X + Y) / ((1 - X) * (1 - Y)) +
        2 * (X ^ 2 + Y ^ 2) / ((1 - X ^ 2) * (1 - Y ^ 2)) := by
  field_simp [hX, hY, hX2, hY2, hXY]
  ring

private theorem boundaryKernel_hecke {a b t : ℝ}
    (ha : 0 < a) (hb : 0 < b) (ht : 0 < t) :
    boundaryKernel (2 * a) b t + boundaryKernel a (2 * b) t +
      boundaryKernel (a + b) (2 * b) t + boundaryKernel (2 * a) (a + b) t =
      boundaryKernel a b t + 2 * boundaryKernel (2 * a) (2 * b) t := by
  have hexp (x y : ℝ) :
      (Real.exp (-(x + y) * t) : ℂ) =
        (Real.exp (-x * t) : ℂ) * (Real.exp (-y * t) : ℂ) := by
    rw [show -(x + y) * t = -x * t + -y * t by ring, Real.exp_add, Complex.ofReal_mul]
  have htwo (x : ℝ) :
      (Real.exp (-(2 * x) * t) : ℂ) = (Real.exp (-x * t) : ℂ) ^ 2 := by
    rw [show 2 * x = x + x by ring, hexp, pow_two]
  have hne (x : ℝ) (hx : 0 < x) : 1 - (Real.exp (-x * t) : ℂ) ≠ 0 := by
    intro h
    have he : Real.exp (-x * t) = 1 := by
      exact_mod_cast (sub_eq_zero.mp h).symm
    exact (ne_of_lt (exp_neg_mul_lt_one hx ht)) he
  have hX2 : 1 - (Real.exp (-a * t) : ℂ) ^ 2 ≠ 0 := by
    rw [← htwo]
    exact hne _ (by positivity)
  have hY2 : 1 - (Real.exp (-b * t) : ℂ) ^ 2 ≠ 0 := by
    rw [← htwo]
    exact hne _ (by positivity)
  have hXY : 1 - (Real.exp (-a * t) : ℂ) * (Real.exp (-b * t) : ℂ) ≠ 0 := by
    rw [← hexp]
    exact hne _ (add_pos ha hb)
  simp only [boundaryKernel_formula, htwo, hexp]
  simpa only [mul_div_assoc] using
    cone_rational_identity _ _ (hne a ha) (hne b hb) hX2 hY2 hXY

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

/-- The four determinant-two cones equal the original cone plus twice its even-even part. -/
theorem barnesBoundaryPeriod_hecke_cones {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {w : ℂ} (hw : 2 < w.re) :
    barnesBoundaryPeriod w (2 * a) b + barnesBoundaryPeriod w a (2 * b) +
      barnesBoundaryPeriod w (a + b) (2 * b) + barnesBoundaryPeriod w (2 * a) (a + b) =
      barnesBoundaryPeriod w a b + 2 * barnesBoundaryPeriod w (2 * a) (2 * b) := by
  have h2a : 0 < 2 * a := by positivity
  have h2b : 0 < 2 * b := by positivity
  have hab : 0 < a + b := add_pos ha hb
  have h1 := boundary_integrable h2a hb hw
  have h2 := boundary_integrable ha h2b hw
  have h3 := boundary_integrable hab h2b hw
  have h4 := boundary_integrable h2a hab hw
  have h5 := boundary_integrable ha hb hw
  have h6 := boundary_integrable h2a h2b hw
  have h12 : IntegrableOn (fun t => boundaryIntegrand w (2 * a) b t +
      boundaryIntegrand w a (2 * b) t) (Ioi 0) := h1.add h2
  have h123 : IntegrableOn (fun t => boundaryIntegrand w (2 * a) b t +
      boundaryIntegrand w a (2 * b) t + boundaryIntegrand w (a + b) (2 * b) t)
      (Ioi 0) := h12.add h3
  apply mul_left_cancel₀ (Complex.Gamma_ne_zero_of_re_pos (by linarith : 0 < w.re))
  calc
    Complex.Gamma w * _ =
        ∫ t in Ioi (0 : ℝ), boundaryIntegrand w (2 * a) b t + boundaryIntegrand w a (2 * b) t +
          boundaryIntegrand w (a + b) (2 * b) t + boundaryIntegrand w (2 * a) (a + b) t := by
      rw [integral_add h123 h4, integral_add h12 h3, integral_add h1 h2]
      rw [← boundary_mellin h2a hb hw, ← boundary_mellin ha h2b hw,
        ← boundary_mellin hab h2b hw, ← boundary_mellin h2a hab hw]
      ring
    _ = ∫ t in Ioi (0 : ℝ), boundaryIntegrand w a b t +
          2 * boundaryIntegrand w (2 * a) (2 * b) t := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      simp only [boundaryIntegrand]
      calc
        _ = (t : ℂ) ^ (w - 1) * (boundaryKernel (2 * a) b t +
            boundaryKernel a (2 * b) t + boundaryKernel (a + b) (2 * b) t +
            boundaryKernel (2 * a) (a + b) t) := by ring
        _ = _ := by rw [boundaryKernel_hecke ha hb ht]; ring
    _ = Complex.Gamma w * _ := by
      rw [integral_add h5 (h6.const_mul 2), integral_const_mul,
        ← boundary_mellin ha hb hw, ← boundary_mellin h2a h2b hw]
      ring

#print axioms barnesBoundaryPeriod_hecke_cones

private theorem barnesDoubleZeta_scale (w : ℂ) {c a b x : ℝ}
    (hc : 0 < c) (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) :
    barnesDoubleZeta (c * a) (c * b) w ((c * x : ℝ) : ℂ) =
      (c : ℂ) ^ (-w) * barnesDoubleZeta a b w (x : ℂ) := by
  rw [barnesDoubleZeta, barnesDoubleZeta, ← tsum_mul_left]
  apply tsum_congr
  intro p
  have hl : barnesLattice (c * a) (c * b) p = c * barnesLattice a b p := by
    unfold barnesLattice
    ring
  have hbase : 0 ≤ x + barnesLattice a b p :=
    (add_pos_of_pos_of_nonneg hx (barnesLattice_nonneg ha.le hb.le p)).le
  rw [hl, ← Complex.ofReal_add, ← mul_add, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hc.le hbase, Complex.ofReal_add]

/-- Homogeneity of the actual boundary-cone sum. -/
theorem barnesBoundaryPeriod_scale (w : ℂ) {c a b : ℝ}
    (hc : 0 < c) (ha : 0 < a) (hb : 0 < b) :
    barnesBoundaryPeriod w (c * a) (c * b) = (c : ℂ) ^ (-w) * barnesBoundaryPeriod w a b := by
  rw [barnesBoundaryPeriod, barnesBoundaryPeriod,
    barnesDoubleZeta_scale w hc ha hb ha, barnesDoubleZeta_scale w hc ha hb hb, mul_add]

/-- The four Lewis branches have eigenvalue `1 + 2 · 2⁻ʷ` on the convergent Barnes period.
The eigenvalue is derived from the source cones, not prescribed on a spectral basis. -/
theorem barnesBoundaryPeriod_hecke {a : ℝ} (ha : 0 < a) {w : ℂ} (hw : 2 < w.re) :
    barnesBoundaryPeriod w (2 * a) 1 +
      (2 : ℂ) ^ (-w) * barnesBoundaryPeriod w (a / 2) 1 +
      (2 : ℂ) ^ (-w) * barnesBoundaryPeriod w ((a + 1) / 2) 1 +
      ((a + 1 : ℝ) : ℂ) ^ (-w) * barnesBoundaryPeriod w (2 * a / (a + 1)) 1 =
      (1 + 2 * (2 : ℂ) ^ (-w)) * barnesBoundaryPeriod w a 1 := by
  have ha1 : 0 < a + 1 := by linarith
  have h2 := barnesBoundaryPeriod_scale w (c := 2) (a := a / 2) (b := 1)
    (by norm_num) (by positivity) zero_lt_one
  have h3 := barnesBoundaryPeriod_scale w (c := 2) (a := (a + 1) / 2) (b := 1)
    (by norm_num) (by positivity) zero_lt_one
  have h4 := barnesBoundaryPeriod_scale w (c := a + 1) (a := 2 * a / (a + 1)) (b := 1)
    ha1 (by positivity) zero_lt_one
  have h6 := barnesBoundaryPeriod_scale w (c := 2) (a := a) (b := 1)
    (by norm_num) ha zero_lt_one
  have he : (a + 1) * (2 * a / (a + 1)) = 2 * a := by field_simp [ha1.ne']
  simp only [show 2 * (a / 2) = a by ring, mul_one, Complex.ofReal_ofNat] at h2
  simp only [show 2 * ((a + 1) / 2) = a + 1 by ring, mul_one, Complex.ofReal_ofNat] at h3
  rw [he, mul_one] at h4
  simp only [mul_one, Complex.ofReal_ofNat] at h6
  have hcone := barnesBoundaryPeriod_hecke_cones ha zero_lt_one hw
  simp only [mul_one] at hcone
  rw [← h2, ← h3, ← h4, hcone, h6]
  ring

#print axioms barnesBoundaryPeriod_hecke

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering
