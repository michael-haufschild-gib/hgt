import GaloisForLFunctions.RHTower.XiHurwitzOrientationBoundaryFusionObstruction

/-!
# The Route-Q boundary pair is an exact hyperbolic plane

The two exact null boundaries are not merely nonunique closest points.  Critical-line reflection
exchanges them with a minus sign, each has squared norm half the orientation energy, and their
real two-coordinate span has exact quadratic law

`Q(alpha b₊ + beta b₋) = -alpha beta E`.

Off RH this is a genuine hyperbolic plane.  Same-sign fusion is strictly negative, opposite-sign
fusion is strictly positive, and only the two coordinate axes are null.  Thus a source-positive
reconstruction of each boundary cannot be fused toward the orientation vector inside the limiting
two-plane: the missing source theorem must supply a transverse mixed-incidence compensation.
-/

open Complex Metric Function Filter Topology
open scoped Topology BigOperators

namespace RHTower

noncomputable section

private abbrev XiWeilCarrier := lp (fun _ : XiZeroCopy => ℂ) 2

theorem xiHurwitzOrientationBoundaryPlus_sub_boundaryMinus :
    xiHurwitzOrientationBoundaryPlus - xiHurwitzOrientationBoundaryMinus =
      xiHurwitzOrientationAbsoluteVector := by
  unfold xiHurwitzOrientationBoundaryPlus xiHurwitzOrientationBoundaryMinus
  module

/-- Critical-line reflection exchanges the two null boundary rays with a minus sign. -/
theorem xiWeilLineConj_boundaryPlus :
    xiWeilLineConjLinearIsometry xiHurwitzOrientationBoundaryPlus =
      -xiHurwitzOrientationBoundaryMinus := by
  unfold xiHurwitzOrientationBoundaryPlus xiHurwitzOrientationBoundaryMinus
  have hw : xiWeilLineConjLinearIsometry xiHurwitzOrientationVector =
      -xiHurwitzOrientationVector := by
    rw [xiWeilLineConjLinearIsometry_apply,
      xiWeilLineConjLp_xiHurwitzOrientationVector]
  have he : xiWeilLineConjLinearIsometry xiHurwitzOrientationAbsoluteVector =
      xiHurwitzOrientationAbsoluteVector := by
    rw [xiWeilLineConjLinearIsometry_apply,
      xiWeilLineConjLp_xiHurwitzOrientationAbsoluteVector]
  rw [map_smul, map_add, hw, he]
  module

theorem xiWeilLineConj_boundaryMinus :
    xiWeilLineConjLinearIsometry xiHurwitzOrientationBoundaryMinus =
      -xiHurwitzOrientationBoundaryPlus := by
  unfold xiHurwitzOrientationBoundaryPlus xiHurwitzOrientationBoundaryMinus
  have hw : xiWeilLineConjLinearIsometry xiHurwitzOrientationVector =
      -xiHurwitzOrientationVector := by
    rw [xiWeilLineConjLinearIsometry_apply,
      xiWeilLineConjLp_xiHurwitzOrientationVector]
  have he : xiWeilLineConjLinearIsometry xiHurwitzOrientationAbsoluteVector =
      xiHurwitzOrientationAbsoluteVector := by
    rw [xiWeilLineConjLinearIsometry_apply,
      xiWeilLineConjLp_xiHurwitzOrientationAbsoluteVector]
  rw [map_smul, map_sub, hw, he]
  module

/-- Each null boundary ray carries exactly half the full orientation norm. -/
theorem two_mul_norm_sq_xiHurwitzOrientationBoundaryPlus :
    2 * ‖xiHurwitzOrientationBoundaryPlus‖ ^ 2 =
      xiHurwitzOrientationEnergy := by
  have h := xiHurwitzOrientationBoundaryMinus_exact.2
  rw [dist_eq_norm] at h
  have hdiff : xiHurwitzOrientationBoundaryMinus - xiHurwitzOrientationVector =
      -xiHurwitzOrientationBoundaryPlus := by
    rw [← xiHurwitzOrientationBoundaryPlus_add_boundaryMinus]
    module
  rw [hdiff, norm_neg] at h
  linarith

theorem two_mul_norm_sq_xiHurwitzOrientationBoundaryMinus :
    2 * ‖xiHurwitzOrientationBoundaryMinus‖ ^ 2 =
      xiHurwitzOrientationEnergy := by
  have h := xiHurwitzOrientationBoundaryPlus_exact.2
  rw [dist_eq_norm] at h
  have hdiff : xiHurwitzOrientationBoundaryPlus - xiHurwitzOrientationVector =
      -xiHurwitzOrientationBoundaryMinus := by
    rw [← xiHurwitzOrientationBoundaryPlus_add_boundaryMinus]
    module
  rw [hdiff, norm_neg] at h
  linarith

/-- **Exact boundary hyperbolic law.** -/
theorem xiWeilHilbertQuadratic_boundaryCoordinates (α β : ℝ) :
    xiWeilHilbertQuadratic
        ((α : ℂ) • xiHurwitzOrientationBoundaryPlus +
          (β : ℂ) • xiHurwitzOrientationBoundaryMinus) =
      -α * β * xiHurwitzOrientationEnergy := by
  unfold xiWeilHilbertQuadratic
  rw [map_add, map_smul, map_smul,
    xiWeilLineConj_boundaryPlus, xiWeilLineConj_boundaryMinus]
  have hcrossMP : (inner ℂ xiHurwitzOrientationBoundaryMinus
      xiHurwitzOrientationBoundaryPlus).re = 0 := by
    have hq := xiHurwitzOrientationBoundaryPlus_exact.1
    unfold xiWeilHilbertQuadratic at hq
    rw [xiWeilLineConj_boundaryPlus] at hq
    simpa only [inner_neg_left, neg_re, neg_eq_zero] using hq
  have hcrossPM : (inner ℂ xiHurwitzOrientationBoundaryPlus
      xiHurwitzOrientationBoundaryMinus).re = 0 := by
    have hq := xiHurwitzOrientationBoundaryMinus_exact.1
    unfold xiWeilHilbertQuadratic at hq
    rw [xiWeilLineConj_boundaryMinus] at hq
    simpa only [inner_neg_left, neg_re, neg_eq_zero] using hq
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    inner_neg_left, conj_ofReal]
  simp only [Complex.add_re, Complex.mul_re, Complex.neg_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [hcrossMP, hcrossPM]
  have hinnerPlus : (inner ℂ xiHurwitzOrientationBoundaryPlus
      xiHurwitzOrientationBoundaryPlus).re =
      ‖xiHurwitzOrientationBoundaryPlus‖ ^ 2 := by
    change RCLike.re (inner ℂ xiHurwitzOrientationBoundaryPlus
      xiHurwitzOrientationBoundaryPlus) = _
    exact inner_self_eq_norm_sq (𝕜 := ℂ) xiHurwitzOrientationBoundaryPlus
  have hinnerMinus : (inner ℂ xiHurwitzOrientationBoundaryMinus
      xiHurwitzOrientationBoundaryMinus).re =
      ‖xiHurwitzOrientationBoundaryMinus‖ ^ 2 := by
    change RCLike.re (inner ℂ xiHurwitzOrientationBoundaryMinus
      xiHurwitzOrientationBoundaryMinus) = _
    exact inner_self_eq_norm_sq (𝕜 := ℂ) xiHurwitzOrientationBoundaryMinus
  rw [hinnerPlus, hinnerMinus]
  have hp := two_mul_norm_sq_xiHurwitzOrientationBoundaryPlus
  have hm := two_mul_norm_sq_xiHurwitzOrientationBoundaryMinus
  have hp' : ‖xiHurwitzOrientationBoundaryPlus‖ ^ 2 =
      xiHurwitzOrientationEnergy / 2 := by linarith
  have hm' : ‖xiHurwitzOrientationBoundaryMinus‖ ^ 2 =
      xiHurwitzOrientationEnergy / 2 := by linarith
  rw [hp', hm']
  ring

/-- Off RH, same-sign boundary coordinates are exactly the negative cone. -/
theorem xiWeilHilbertQuadratic_boundaryCoordinates_neg_iff_of_not_rh
    (hnot : ¬RiemannHypothesis) (α β : ℝ) :
    xiWeilHilbertQuadratic
        ((α : ℂ) • xiHurwitzOrientationBoundaryPlus +
          (β : ℂ) • xiHurwitzOrientationBoundaryMinus) < 0 ↔
      0 < α * β := by
  rw [xiWeilHilbertQuadratic_boundaryCoordinates]
  have hE : 0 < xiHurwitzOrientationEnergy :=
    xiHurwitzOrientationEnergy_pos_iff_not_riemannHypothesis.2 hnot
  constructor <;> intro h <;> nlinarith

/-- Off RH, opposite-sign boundary coordinates are exactly the positive cone. -/
theorem xiWeilHilbertQuadratic_boundaryCoordinates_pos_iff_of_not_rh
    (hnot : ¬RiemannHypothesis) (α β : ℝ) :
    0 < xiWeilHilbertQuadratic
        ((α : ℂ) • xiHurwitzOrientationBoundaryPlus +
          (β : ℂ) • xiHurwitzOrientationBoundaryMinus) ↔
      α * β < 0 := by
  rw [xiWeilHilbertQuadratic_boundaryCoordinates]
  have hE : 0 < xiHurwitzOrientationEnergy :=
    xiHurwitzOrientationEnergy_pos_iff_not_riemannHypothesis.2 hnot
  constructor <;> intro h <;> nlinarith

/-- Off RH, the two boundary axes are the complete null cone inside their real span. -/
theorem xiWeilHilbertQuadratic_boundaryCoordinates_eq_zero_iff_of_not_rh
    (hnot : ¬RiemannHypothesis) (α β : ℝ) :
    xiWeilHilbertQuadratic
        ((α : ℂ) • xiHurwitzOrientationBoundaryPlus +
          (β : ℂ) • xiHurwitzOrientationBoundaryMinus) = 0 ↔
      α = 0 ∨ β = 0 := by
  rw [xiWeilHilbertQuadratic_boundaryCoordinates]
  have hE : xiHurwitzOrientationEnergy ≠ 0 :=
    (xiHurwitzOrientationEnergy_pos_iff_not_riemannHypothesis.2 hnot).ne'
  constructor
  · intro h
    have hab : α * β = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_right hE
      simpa only [neg_mul, neg_eq_zero] using h
    exact mul_eq_zero.mp hab
  · rintro (rfl | rfl) <;> ring

/-- Scaled packet fusions converge to the exact hyperbolic value. -/
theorem tendsto_xiSeparatedBoundaryPacket_scaledFusionEnergy
    (α β : ℝ) (P Q : ℕ → XiSeparatedContinuedCauchyPacket)
    (hP : Tendsto (fun n => (P n).evaluation) atTop
      (𝓝 xiHurwitzOrientationBoundaryPlus))
    (hQ : Tendsto (fun n => (Q n).evaluation) atTop
      (𝓝 xiHurwitzOrientationBoundaryMinus)) :
    Tendsto (fun n => xiWeilHilbertQuadratic
      ((α : ℂ) • (P n).evaluation + (β : ℂ) • (Q n).evaluation))
      atTop (𝓝 (-α * β * xiHurwitzOrientationEnergy)) := by
  have hsum := hP.const_smul (α : ℂ) |>.add (hQ.const_smul (β : ℂ))
  have h := continuous_xiWeilHilbertQuadratic.continuousAt.tendsto.comp hsum
  rw [xiWeilHilbertQuadratic_boundaryCoordinates α β] at h
  exact h

/-- Off RH, every same-sign scaled fusion of the two boundary reconstructions is eventually
negative, regardless of how the two diagonal packet energies approach zero. -/
theorem eventually_xiSeparatedBoundaryPacket_scaledFusionEnergy_neg_of_not_rh
    (hnot : ¬RiemannHypothesis) {α β : ℝ} (hab : 0 < α * β)
    (P Q : ℕ → XiSeparatedContinuedCauchyPacket)
    (hP : Tendsto (fun n => (P n).evaluation) atTop
      (𝓝 xiHurwitzOrientationBoundaryPlus))
    (hQ : Tendsto (fun n => (Q n).evaluation) atTop
      (𝓝 xiHurwitzOrientationBoundaryMinus)) :
    ∀ᶠ n in atTop, xiWeilHilbertQuadratic
      ((α : ℂ) • (P n).evaluation + (β : ℂ) • (Q n).evaluation) < 0 := by
  have hE : 0 < xiHurwitzOrientationEnergy :=
    xiHurwitzOrientationEnergy_pos_iff_not_riemannHypothesis.2 hnot
  exact (tendsto_xiSeparatedBoundaryPacket_scaledFusionEnergy α β P Q hP hQ).eventually
    (Iio_mem_nhds (by nlinarith))

/-- Off RH, every opposite-sign scaled fusion is eventually positive.  The asymptotic source cone
inside the boundary plane is therefore the opposite-sign quadrant, not the target quadrant. -/
theorem eventually_xiSeparatedBoundaryPacket_scaledFusionEnergy_pos_of_not_rh
    (hnot : ¬RiemannHypothesis) {α β : ℝ} (hab : α * β < 0)
    (P Q : ℕ → XiSeparatedContinuedCauchyPacket)
    (hP : Tendsto (fun n => (P n).evaluation) atTop
      (𝓝 xiHurwitzOrientationBoundaryPlus))
    (hQ : Tendsto (fun n => (Q n).evaluation) atTop
      (𝓝 xiHurwitzOrientationBoundaryMinus)) :
    ∀ᶠ n in atTop, 0 < xiWeilHilbertQuadratic
      ((α : ℂ) • (P n).evaluation + (β : ℂ) • (Q n).evaluation) := by
  have hE : 0 < xiHurwitzOrientationEnergy :=
    xiHurwitzOrientationEnergy_pos_iff_not_riemannHypothesis.2 hnot
  exact (tendsto_xiSeparatedBoundaryPacket_scaledFusionEnergy α β P Q hP hQ).eventually
    (Ioi_mem_nhds (by nlinarith))

end

end RHTower
