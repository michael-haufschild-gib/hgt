import GaloisForLFunctions.RHTower.XiHurwitzOrientationBoundaryHyperbolicPlane
import GaloisForLFunctions.RHTower.CCMCliffordWeilProduct

/-!
# Sharp transverse compensation for the Route-Q boundary plane

The exact boundary hyperbolic plane has a directional repair law.  A reflection-fixed vector
orthogonal to the canonical fixed boundary axis adds its full Hilbert norm squared to Weil energy;
an anti-fixed vector orthogonal to orientation subtracts its norm squared.  Thus target-aligned
boundary fusion can be source-nonnegative only if a fixed transverse channel carries at least the
entire orientation energy.  Anti-fixed transverse mass can never repair the defect off RH.
-/

open Complex

namespace RHTower

noncomputable section

private abbrev XiWeilCarrier := lp (fun _ : XiZeroCopy => ℂ) 2

/-- Exact polarization law for adding a vector to the Xi Weil quadratic form. -/
theorem xiWeilHilbertQuadratic_add_cross (x z : XiWeilCarrier) :
    xiWeilHilbertQuadratic (x + z) =
      xiWeilHilbertQuadratic x + xiWeilHilbertQuadratic z +
        2 * (inner ℂ (xiWeilLineConjLinearIsometry x) z).re := by
  unfold xiWeilHilbertQuadratic
  simp only [map_add, inner_add_left, inner_add_right, Complex.add_re]
  have hcross :
      (inner ℂ (xiWeilLineConjLinearIsometry z) x).re =
        (inner ℂ (xiWeilLineConjLinearIsometry x) z).re := by
    rw [CliffordWeil.inner_map_left_eq_inner_map_right
      xiWeilLineConjLinearIsometry xiWeilLineConjLinearIsometry_involutive]
    exact inner_re_symm (𝕜 := ℂ) _ _
  rw [hcross]
  ring

/-- A fixed transverse direction orthogonal to the fixed boundary axis adds exactly its squared
norm to the boundary-plane hyperbolic energy. -/
theorem xiWeilHilbertQuadratic_boundaryCoordinates_add_fixedTransverse
    (α β : ℝ) (z : XiWeilCarrier)
    (hzfix : xiWeilLineConjLinearIsometry z = z)
    (hzorth : (inner ℂ xiHurwitzOrientationAbsoluteVector z).re = 0) :
    xiWeilHilbertQuadratic
        ((α : ℂ) • xiHurwitzOrientationBoundaryPlus +
          (β : ℂ) • xiHurwitzOrientationBoundaryMinus + z) =
      -α * β * xiHurwitzOrientationEnergy + ‖z‖ ^ 2 := by
  let x : XiWeilCarrier :=
    (α : ℂ) • xiHurwitzOrientationBoundaryPlus +
      (β : ℂ) • xiHurwitzOrientationBoundaryMinus
  rw [show (α : ℂ) • xiHurwitzOrientationBoundaryPlus +
      (β : ℂ) • xiHurwitzOrientationBoundaryMinus + z = x + z by rfl]
  rw [xiWeilHilbertQuadratic_add_cross,
    show xiWeilHilbertQuadratic x = -α * β * xiHurwitzOrientationEnergy by
      exact xiWeilHilbertQuadratic_boundaryCoordinates α β]
  have hqz : xiWeilHilbertQuadratic z = ‖z‖ ^ 2 := by
    unfold xiWeilHilbertQuadratic
    rw [hzfix]
    change RCLike.re (inner ℂ z z) = _
    exact inner_self_eq_norm_sq (𝕜 := ℂ) z
  rw [hqz]
  have hworth : inner ℂ xiHurwitzOrientationVector z = 0 := by
    have h := CliffordWeil.inner_map_left_eq_inner_map_right
      xiWeilLineConjLinearIsometry xiWeilLineConjLinearIsometry_involutive
      xiHurwitzOrientationVector z
    rw [xiWeilLineConjLinearIsometry_apply,
      xiWeilLineConjLp_xiHurwitzOrientationVector, hzfix, inner_neg_left] at h
    exact neg_eq_self.mp h
  have hxdecomp : x =
      (((α + β) / 2 : ℝ) : ℂ) • xiHurwitzOrientationVector +
        (((α - β) / 2 : ℝ) : ℂ) • xiHurwitzOrientationAbsoluteVector := by
    dsimp [x]
    rw [← xiHurwitzOrientationBoundaryPlus_add_boundaryMinus,
      ← xiHurwitzOrientationBoundaryPlus_sub_boundaryMinus]
    module
  have hxorth : (inner ℂ x z).re = 0 := by
    rw [hxdecomp, inner_add_left, inner_smul_left, inner_smul_left, hworth]
    simp [Complex.mul_re, Complex.div_im, Complex.sub_im, Complex.conj_im, hzorth]
  rw [CliffordWeil.inner_map_left_eq_inner_map_right
      xiWeilLineConjLinearIsometry xiWeilLineConjLinearIsometry_involutive,
    hzfix, hxorth]
  ring

/-- An anti-fixed transverse direction orthogonal to orientation subtracts exactly its squared
norm from the boundary-plane hyperbolic energy. -/
theorem xiWeilHilbertQuadratic_boundaryCoordinates_add_antiTransverse
    (α β : ℝ) (z : XiWeilCarrier)
    (hzanti : xiWeilLineConjLinearIsometry z = -z)
    (hzorth : (inner ℂ xiHurwitzOrientationVector z).re = 0) :
    xiWeilHilbertQuadratic
        ((α : ℂ) • xiHurwitzOrientationBoundaryPlus +
          (β : ℂ) • xiHurwitzOrientationBoundaryMinus + z) =
      -α * β * xiHurwitzOrientationEnergy - ‖z‖ ^ 2 := by
  let x : XiWeilCarrier :=
    (α : ℂ) • xiHurwitzOrientationBoundaryPlus +
      (β : ℂ) • xiHurwitzOrientationBoundaryMinus
  rw [show (α : ℂ) • xiHurwitzOrientationBoundaryPlus +
      (β : ℂ) • xiHurwitzOrientationBoundaryMinus + z = x + z by rfl]
  rw [xiWeilHilbertQuadratic_add_cross,
    show xiWeilHilbertQuadratic x = -α * β * xiHurwitzOrientationEnergy by
      exact xiWeilHilbertQuadratic_boundaryCoordinates α β]
  have hqz : xiWeilHilbertQuadratic z = -‖z‖ ^ 2 := by
    unfold xiWeilHilbertQuadratic
    rw [hzanti, inner_neg_left, Complex.neg_re]
    change -RCLike.re (inner ℂ z z) = _
    rw [inner_self_eq_norm_sq (𝕜 := ℂ)]
  rw [hqz]
  have heorth : inner ℂ xiHurwitzOrientationAbsoluteVector z = 0 := by
    have h := CliffordWeil.inner_map_left_eq_inner_map_right
      xiWeilLineConjLinearIsometry xiWeilLineConjLinearIsometry_involutive
      xiHurwitzOrientationAbsoluteVector z
    rw [xiWeilLineConjLinearIsometry_apply,
      xiWeilLineConjLp_xiHurwitzOrientationAbsoluteVector, hzanti,
      inner_neg_right] at h
    exact neg_eq_self.mp h.symm
  have hxdecomp : x =
      (((α + β) / 2 : ℝ) : ℂ) • xiHurwitzOrientationVector +
        (((α - β) / 2 : ℝ) : ℂ) • xiHurwitzOrientationAbsoluteVector := by
    dsimp [x]
    rw [← xiHurwitzOrientationBoundaryPlus_add_boundaryMinus,
      ← xiHurwitzOrientationBoundaryPlus_sub_boundaryMinus]
    module
  have hxorth : (inner ℂ x z).re = 0 := by
    rw [hxdecomp, inner_add_left, inner_smul_left, inner_smul_left, heorth]
    simp [Complex.mul_re, Complex.div_im, Complex.add_im, Complex.conj_im, hzorth]
  rw [CliffordWeil.inner_map_left_eq_inner_map_right
      xiWeilLineConjLinearIsometry xiWeilLineConjLinearIsometry_involutive,
    hzanti, inner_neg_right, Complex.neg_re, hxorth]
  ring

/-- A Weil-nonnegative same-sign fusion needs a fixed transverse norm large enough to pay the
entire hyperbolic boundary defect. -/
theorem mul_orientationEnergy_le_norm_sq_of_fixedTransverse_weil_nonnegative
    {α β : ℝ} (z : XiWeilCarrier)
    (hzfix : xiWeilLineConjLinearIsometry z = z)
    (hzorth : (inner ℂ xiHurwitzOrientationAbsoluteVector z).re = 0)
    (hnonneg : 0 ≤ xiWeilHilbertQuadratic
      ((α : ℂ) • xiHurwitzOrientationBoundaryPlus +
        (β : ℂ) • xiHurwitzOrientationBoundaryMinus + z)) :
    α * β * xiHurwitzOrientationEnergy ≤ ‖z‖ ^ 2 := by
  rw [xiWeilHilbertQuadratic_boundaryCoordinates_add_fixedTransverse
    α β z hzfix hzorth] at hnonneg
  linarith

/-- For the orientation direction itself, a fixed transverse correction has exact energy
`‖z‖²-E`. -/
theorem xiWeilHilbertQuadratic_orientation_add_fixedTransverse
    (z : XiWeilCarrier)
    (hzfix : xiWeilLineConjLinearIsometry z = z)
    (hzorth : (inner ℂ xiHurwitzOrientationAbsoluteVector z).re = 0) :
    xiWeilHilbertQuadratic (xiHurwitzOrientationVector + z) =
      ‖z‖ ^ 2 - xiHurwitzOrientationEnergy := by
  have h := xiWeilHilbertQuadratic_boundaryCoordinates_add_fixedTransverse
    1 1 z hzfix hzorth
  norm_num at h
  rw [xiHurwitzOrientationBoundaryPlus_add_boundaryMinus] at h
  linarith

/-- Exact minimum compensation budget in the orientation direction. -/
theorem orientationEnergy_le_norm_sq_of_fixedTransverse_weil_nonnegative
    (z : XiWeilCarrier)
    (hzfix : xiWeilLineConjLinearIsometry z = z)
    (hzorth : (inner ℂ xiHurwitzOrientationAbsoluteVector z).re = 0)
    (hnonneg : 0 ≤ xiWeilHilbertQuadratic (xiHurwitzOrientationVector + z)) :
    xiHurwitzOrientationEnergy ≤ ‖z‖ ^ 2 := by
  rw [xiWeilHilbertQuadratic_orientation_add_fixedTransverse z hzfix hzorth] at hnonneg
  linarith

/-- Anti-fixed transverse correction can only deepen the orientation defect. -/
theorem xiWeilHilbertQuadratic_orientation_add_antiTransverse
    (z : XiWeilCarrier)
    (hzanti : xiWeilLineConjLinearIsometry z = -z)
    (hzorth : (inner ℂ xiHurwitzOrientationVector z).re = 0) :
    xiWeilHilbertQuadratic (xiHurwitzOrientationVector + z) =
      -xiHurwitzOrientationEnergy - ‖z‖ ^ 2 := by
  have h := xiWeilHilbertQuadratic_boundaryCoordinates_add_antiTransverse
    1 1 z hzanti hzorth
  norm_num at h
  simpa only [one_smul, xiHurwitzOrientationBoundaryPlus_add_boundaryMinus] using h

/-- Off RH, no anti-fixed transverse correction orthogonal to orientation can restore
nonnegative energy. -/
theorem xiWeilHilbertQuadratic_orientation_add_antiTransverse_neg_of_not_rh
    (hnot : ¬RiemannHypothesis) (z : XiWeilCarrier)
    (hzanti : xiWeilLineConjLinearIsometry z = -z)
    (hzorth : (inner ℂ xiHurwitzOrientationVector z).re = 0) :
    xiWeilHilbertQuadratic (xiHurwitzOrientationVector + z) < 0 := by
  rw [xiWeilHilbertQuadratic_orientation_add_antiTransverse z hzanti hzorth]
  have hE : 0 < xiHurwitzOrientationEnergy :=
    xiHurwitzOrientationEnergy_pos_iff_not_riemannHypothesis.2 hnot
  nlinarith [sq_nonneg ‖z‖]

/-- Full transverse law: if a correction is real-orthogonal to both canonical boundary axes, its
only contribution is its intrinsic Krein energy. -/
theorem xiWeilHilbertQuadratic_boundaryCoordinates_add_transverse
    (α β : ℝ) (z : XiWeilCarrier)
    (hzw : (inner ℂ xiHurwitzOrientationVector z).re = 0)
    (hze : (inner ℂ xiHurwitzOrientationAbsoluteVector z).re = 0) :
    xiWeilHilbertQuadratic
        ((α : ℂ) • xiHurwitzOrientationBoundaryPlus +
          (β : ℂ) • xiHurwitzOrientationBoundaryMinus + z) =
      -α * β * xiHurwitzOrientationEnergy + xiWeilHilbertQuadratic z := by
  let x : XiWeilCarrier :=
    (α : ℂ) • xiHurwitzOrientationBoundaryPlus +
      (β : ℂ) • xiHurwitzOrientationBoundaryMinus
  rw [show (α : ℂ) • xiHurwitzOrientationBoundaryPlus +
      (β : ℂ) • xiHurwitzOrientationBoundaryMinus + z = x + z by rfl]
  rw [xiWeilHilbertQuadratic_add_cross,
    show xiWeilHilbertQuadratic x = -α * β * xiHurwitzOrientationEnergy by
      exact xiWeilHilbertQuadratic_boundaryCoordinates α β]
  have hxdecomp : x =
      (((α + β) / 2 : ℝ) : ℂ) • xiHurwitzOrientationVector +
        (((α - β) / 2 : ℝ) : ℂ) • xiHurwitzOrientationAbsoluteVector := by
    dsimp [x]
    rw [← xiHurwitzOrientationBoundaryPlus_add_boundaryMinus,
      ← xiHurwitzOrientationBoundaryPlus_sub_boundaryMinus]
    module
  have hJx : xiWeilLineConjLinearIsometry x =
      -(((α + β) / 2 : ℝ) : ℂ) • xiHurwitzOrientationVector +
        (((α - β) / 2 : ℝ) : ℂ) • xiHurwitzOrientationAbsoluteVector := by
    rw [hxdecomp, map_add, map_smul, map_smul,
      xiWeilLineConjLinearIsometry_apply,
      xiWeilLineConjLp_xiHurwitzOrientationVector,
      xiWeilLineConjLinearIsometry_apply,
      xiWeilLineConjLp_xiHurwitzOrientationAbsoluteVector]
    module
  have hcross : (inner ℂ (xiWeilLineConjLinearIsometry x) z).re = 0 := by
    rw [hJx, inner_add_left, inner_smul_left, inner_smul_left]
    simp [Complex.mul_re, Complex.div_im, Complex.add_im, Complex.sub_im,
      Complex.conj_im, hzw, hze]
  rw [hcross]
  ring

/-- Exact channel budget forced by a nonnegative source fusion.  Fixed transverse channel must pay
both the hyperbolic boundary defect and every anti-fixed transverse contribution. -/
theorem four_mul_orientationEnergy_add_oddChannel_le_evenChannel_of_transverse_weil_nonnegative
    {α β : ℝ} (z : XiWeilCarrier)
    (hzw : (inner ℂ xiHurwitzOrientationVector z).re = 0)
    (hze : (inner ℂ xiHurwitzOrientationAbsoluteVector z).re = 0)
    (hnonneg : 0 ≤ xiWeilHilbertQuadratic
      ((α : ℂ) • xiHurwitzOrientationBoundaryPlus +
        (β : ℂ) • xiHurwitzOrientationBoundaryMinus + z)) :
    4 * (α * β * xiHurwitzOrientationEnergy) +
        ‖z - xiWeilLineConjLinearIsometry z‖ ^ 2 ≤
      ‖z + xiWeilLineConjLinearIsometry z‖ ^ 2 := by
  rw [xiWeilHilbertQuadratic_boundaryCoordinates_add_transverse
    α β z hzw hze] at hnonneg
  have hbalance := CliffordWeil.four_mul_quadratic_eq_even_sub_odd
    xiWeilLineConjLinearIsometry xiWeilLineConjLinearIsometry_involutive z
  change 4 * xiWeilHilbertQuadratic z =
    ‖z + xiWeilLineConjLinearIsometry z‖ ^ 2 -
      ‖z - xiWeilLineConjLinearIsometry z‖ ^ 2 at hbalance
  linarith

end

end RHTower
