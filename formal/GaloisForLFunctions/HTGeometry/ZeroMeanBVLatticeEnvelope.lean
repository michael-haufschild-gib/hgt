import GaloisForLFunctions.HTGeometry.BoundedVariationRiemannSum

/-!
# The square-root envelope for zero-mean BV lattice quadrature

A compact one-sided source of mean zero has a first-order lattice quadrature error.  At mesh
`1 / k`, multiplying that error by the radial normalization `sqrt k` therefore leaves the exact
`k ^ (-1/2)` envelope.  This is the deterministic quadrature estimate on the source side of the
Poisson--Muntz formula; no Fourier decay or termwise absolute convergence is used.
-/

open Finset MeasureTheory Set intervalIntegral

namespace HTGeometry

noncomputable section

/-- The positive right-endpoint lattice quadrature at mesh `1 / k`. -/
def positiveLatticeQuadrature (g : ℝ → ℂ) (k : ℝ) (n : ℕ) : ℂ :=
  (1 / k : ℝ) • ∑ i ∈ Finset.range n, g ((i + 1) / k)

/-- The square-root radial normalization of the positive lattice quadrature. -/
def sqrtRadialLatticeQuadrature (g : ℝ → ℂ) (k : ℝ) (n : ℕ) : ℂ :=
  (Real.sqrt k : ℝ) • positiveLatticeQuadrature g k n

/-- A zero-mean BV source supported at the right endpoint has lattice quadrature at most twice
its total variation divided by the reciprocal mesh.  The final partial cell is included, so the
statement does not require the support endpoint to lie on the lattice. -/
theorem norm_positiveLatticeQuadrature_le_two_mul_variation_div
    {g : ℝ → ℂ} {k L : ℝ} (hk : 0 < k) {n : ℕ}
    (hnL : (n : ℝ) / k ≤ L) (hLn : L ≤ ((n : ℝ) + 1) / k)
    (hint : IntervalIntegrable g volume 0 L)
    (hvar : BoundedVariationOn g (Icc 0 L))
    (hmean : ∫ x in 0..L, g x = 0) (hL : g L = 0) :
    ‖positiveLatticeQuadrature g k n‖ ≤
      (2 / k) * (eVariationOn g (Icc 0 L)).toReal := by
  let D : ℝ := (n : ℝ) / k
  let V : ℝ := (eVariationOn g (Icc 0 L)).toReal
  have hk0 : k ≠ 0 := hk.ne'
  have hD0 : 0 ≤ D := by
    dsimp only [D]
    positivity
  have h0L : 0 ≤ L := hD0.trans hnL
  have hDL : D ≤ L := hnL
  have hLDstep : L - D ≤ 1 / k := by
    dsimp only [D]
    calc
      L - (n : ℝ) / k ≤ ((n : ℝ) + 1) / k - (n : ℝ) / k :=
        sub_le_sub_right hLn _
      _ = 1 / k := by field_simp; ring
  have hintHead : IntervalIntegrable g volume 0 D := by
    apply hint.mono_set
    rw [uIcc_of_le h0L, uIcc_of_le hD0]
    exact Icc_subset_Icc_right hDL
  have hintTail : IntervalIntegrable g volume D L := by
    apply hint.mono_set
    rw [uIcc_of_le h0L, uIcc_of_le hDL]
    exact Icc_subset_Icc_left hD0
  have hvarHead : BoundedVariationOn g (Icc 0 D) :=
    hvar.mono (Icc_subset_Icc_right hDL)
  have hVHead : (eVariationOn g (Icc 0 D)).toReal ≤ V := by
    exact ENNReal.toReal_mono hvar (eVariationOn.mono g (Icc_subset_Icc_right hDL))
  have hquad := norm_rightEndpoint_riemannSum_sub_integral_le_eVariationOn
    (g := g) (k := k) hk (n := n) hintHead hvarHead
  have hquad' :
      ‖positiveLatticeQuadrature g k n - ∫ x in 0..D, g x‖ ≤ (1 / k) * V := by
    rw [positiveLatticeQuadrature]
    exact hquad.trans (mul_le_mul_of_nonneg_left hVHead (by positivity))
  have hpoint : ∀ x ∈ Icc D L, ‖g x‖ ≤ V := by
    intro x hx
    have hxFull : x ∈ Icc 0 L := ⟨hD0.trans hx.1, hx.2⟩
    have hLFull : L ∈ Icc 0 L := ⟨h0L, le_rfl⟩
    have hd := hvar.dist_le hxFull hLFull
    simpa only [hL, dist_zero_right] using hd
  have htail : ‖∫ x in D..L, g x‖ ≤ V * (L - D) := by
    have hbound : ‖∫ x in D..L, g x‖ ≤ V * |L - D| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const_ae
      filter_upwards with x hx
      apply hpoint x
      have hx' : x ∈ uIcc D L := uIoc_subset_uIcc hx
      simpa only [uIcc_of_le hDL] using hx'
    simpa only [abs_of_nonneg (sub_nonneg.mpr hDL)] using hbound
  have htail' : ‖∫ x in D..L, g x‖ ≤ (1 / k) * V := by
    calc
      ‖∫ x in D..L, g x‖ ≤ V * (L - D) := htail
      _ ≤ V * (1 / k) := mul_le_mul_of_nonneg_left hLDstep ENNReal.toReal_nonneg
      _ = (1 / k) * V := mul_comm _ _
  have hhead : (∫ x in 0..D, g x) = -(∫ x in D..L, g x) := by
    have hadd := intervalIntegral.integral_add_adjacent_intervals hintHead hintTail
    rw [hmean] at hadd
    exact eq_neg_of_add_eq_zero_left hadd
  calc
    ‖positiveLatticeQuadrature g k n‖ =
        ‖(positiveLatticeQuadrature g k n - ∫ x in 0..D, g x) +
          ∫ x in 0..D, g x‖ := by ring_nf
    _ ≤ ‖positiveLatticeQuadrature g k n - ∫ x in 0..D, g x‖ +
        ‖∫ x in 0..D, g x‖ := norm_add_le _ _
    _ ≤ (1 / k) * V + (1 / k) * V := by
      gcongr
      rw [hhead, norm_neg]
      exact htail'
    _ = (2 / k) * V := by field_simp; ring

/-- **Square-root BV lattice envelope.**  After the radial `sqrt k` normalization, every
zero-mean compact BV source has size at most `2 Var(g) / sqrt k`. -/
theorem norm_sqrtRadialLatticeQuadrature_le_two_mul_variation_div_sqrt
    {g : ℝ → ℂ} {k L : ℝ} (hk : 0 < k) {n : ℕ}
    (hnL : (n : ℝ) / k ≤ L) (hLn : L ≤ ((n : ℝ) + 1) / k)
    (hint : IntervalIntegrable g volume 0 L)
    (hvar : BoundedVariationOn g (Icc 0 L))
    (hmean : ∫ x in 0..L, g x = 0) (hL : g L = 0) :
    ‖sqrtRadialLatticeQuadrature g k n‖ ≤
      (2 / Real.sqrt k) * (eVariationOn g (Icc 0 L)).toReal := by
  have hbase := norm_positiveLatticeQuadrature_le_two_mul_variation_div
    hk hnL hLn hint hvar hmean hL
  have hsqrt : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk
  have hratio : Real.sqrt k * (2 / k) = 2 / Real.sqrt k := by
    field_simp [hk.ne', hsqrt.ne']
    nlinarith [Real.sq_sqrt hk.le]
  rw [sqrtRadialLatticeQuadrature, norm_smul, Real.norm_eq_abs,
    abs_of_pos hsqrt]
  calc
    Real.sqrt k * ‖positiveLatticeQuadrature g k n‖ ≤
        Real.sqrt k * ((2 / k) * (eVariationOn g (Icc 0 L)).toReal) :=
      mul_le_mul_of_nonneg_left hbase hsqrt.le
    _ = (2 / Real.sqrt k) * (eVariationOn g (Icc 0 L)).toReal := by
      rw [← mul_assoc, hratio]

end

end HTGeometry
