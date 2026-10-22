import GaloisForLFunctions.HTGeometry.HypergeometricSpatialJets
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLaplaceSolutions

/-! Original BM radial equations throughout the nonreal frequency plane. -/
namespace RHTower.D4BMLaplaceRadial
open Complex Filter Topology Set GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

private theorem radialSeries_radius_one_le (w chi : ℂ) (outer : Bool) :
    1 ≤ (radialSeries w chi outer).radius := by
  cases outer <;> exact hypergeometric_radius_one_le _ _ _

/-- Both factors have their actual first and second derivatives in the entire
open radial disk, at every frequency. -/
theorem gaussFactor_derivatives_continued {w chi z : ℂ} (outer : Bool) (hz : ‖z‖ₑ < 1) :
    HasDerivAt (gaussFactor w chi outer) (gaussFirst w chi outer z) z ∧
    HasDerivAt (gaussFirst w chi outer) (gaussSecond w chi outer z) z := by
  let p := radialSeries w chi outer
  have hp : ‖z‖ₑ < p.radius := hz.trans_le (radialSeries_radius_one_le w chi outer)
  constructor
  · exact (p.hasFDerivAt_sum hp).hasDerivAt
  · have hq := p.derivSeries.hasFDerivAt_sum (lt_of_lt_of_le hp p.radius_le_radius_derivSeries)
    simpa [gaussFirst,gaussSecond,p] using!
      (hq.clm_apply (hasFDerivAt_const (1:ℂ) z)).hasDerivAt

/-- The horizon factor solves the original reduced Gauss equation at free frequency. -/
theorem horizonFactor_equation_continued {w chi z : ℂ} (hw : w.im ≠ 0) (hz : ‖z‖ₑ < 1) :
    gaussJet w chi z (gaussFactor w chi false z) (gaussFirst w chi false z)
      (gaussSecond w chi false z)=0 := by
  have hr : ‖z‖ₑ < (horizonSeries w chi).radius := hz.trans_le (hypergeometric_radius_one_le _ _ _)
  exact ordinaryHypergeometric_standardGaussODE _ _ _ z
    (by
      intro n hn
      apply hw
      have hi := congrArg Complex.im hn
      simp only [gaussC,Complex.natCast_im,Complex.neg_im,Complex.add_im,Complex.one_im,zero_add] at hi
      linear_combination hi) hr

/-- The outer factor solves its transformed Gauss equation, with fixed
denominator 3/2 and the original independently varying numerator parameters. -/
theorem outerGauss_equation_continued {w chi z : ℂ} (hz : ‖z‖ₑ < 1) :
    z*(1-z)*gaussSecond w chi true z+
      (3/2-((gaussC w-gaussA w chi)+(gaussC w-gaussB w chi)+1)*z)*gaussFirst w chi true z-
      (gaussC w-gaussA w chi)*(gaussC w-gaussB w chi)*gaussFactor w chi true z=0 := by
  have hr : ‖z‖ₑ < (outerSeries w chi).radius := hz.trans_le (hypergeometric_radius_one_le _ _ _)
  exact ordinaryHypergeometric_standardGaussODE _ _ _ z
    (avoidsNegNat_of_re_pos (by norm_num : 0 < (3/2:ℂ).re)) hr
/-- The outer branch's two jets are actual derivatives, including the
square-root factor and the reversal of the radial coordinate. -/
theorem outerFactor_derivatives_continued {w chi : ℂ} {z : ℝ} (hz : z ∈ Ioo 0 1) :
    HasDerivAt (outerFactor w chi) (outerFirst w chi z) z ∧
    HasDerivAt (outerFirst w chi) (outerSecond w chi z) z := by
  have hx : 0 < 1-z := sub_pos.mpr hz.2
  have hnorm : ‖((1-z:ℝ):ℂ)‖ₑ < 1 := enorm_ofReal_lt_one hx (by linarith [hz.1])
  have hd := (hasDerivAt_id z).const_sub (1:ℝ)
  obtain ⟨hp,hp1⟩ := power_derivatives (1/2) hx
  obtain ⟨hF,hF1⟩ := gaussFactor_derivatives_continued (w := w) (chi := chi) true hnorm
  have hP := hp.scomp z hd
  have hP1 := hp1.scomp z hd
  have hG := hF.comp_ofReal.scomp z hd
  have hG1 := hF1.comp_ofReal.scomp z hd
  simp only [neg_smul,one_smul] at hP hP1 hG hG1
  push_cast at hG hG1
  constructor
  · convert! hP.mul hG using 1
    · funext t
      simp [outerFactor,Function.comp_def]
    · dsimp [outerFirst]
      push_cast
      ring
  · convert! (hP1.neg.mul hG).sub (hP.mul hG1) using 1
    · funext t
      simp [outerFirst,Function.comp_def]
    · dsimp [outerSecond]
      push_cast
      ring

private theorem continued_outer_transport (w chi : ℂ) {z : ℝ} (hz : z < 1) (v d dd : ℂ) :
    gaussJet w chi z (power (1/2) (1-z)*v)
      (-powerFirst (1/2) (1-z)*v-power (1/2) (1-z)*d)
      (powerSecond (1/2) (1-z)*v+2*powerFirst (1/2) (1-z)*d+power (1/2) (1-z)*dd) =
    power (1/2) (1-z)*
      ((1-z:ℂ)*(1-(1-z:ℂ))*dd+
        (3/2-((gaussC w-gaussA w chi)+(gaussC w-gaussB w chi)+1)*(1-z:ℂ))*d-
        (gaussC w-gaussA w chi)*(gaussC w-gaussB w chi)*v) := by
  have hx : (1-(z:ℂ)) ≠ 0 := by exact_mod_cast (ne_of_gt (sub_pos.mpr hz))
  dsimp [gaussJet,gaussA,gaussB,gaussC,powerFirst,powerSecond]
  push_cast
  field_simp [hx]
  ring

/-- The exact normalizable factor solves the same original reduced radial
equation as the horizon factor, at every frequency. -/
theorem outerFactor_equation_continued {w chi : ℂ} {z : ℝ} (hz : z ∈ Ioo 0 1) :
    gaussJet w chi z (outerFactor w chi z) (outerFirst w chi z) (outerSecond w chi z)=0 := by
  have hnorm : ‖((1-z:ℝ):ℂ)‖ₑ < 1 := enorm_ofReal_lt_one (by linarith [hz.2]) (by linarith [hz.1])
  have he := outerGauss_equation_continued (w := w) (chi := chi) hnorm
  push_cast at he
  dsimp [outerFactor,outerFirst,outerSecond]
  rw [continued_outer_transport w chi hz.2,he,mul_zero]
/-- The full physical horizon branch has actual first and second radial derivatives. -/
theorem horizon_derivatives_continued {w chi : ℂ} {z : ℝ} (hz : z ∈ Ioo 0 1) :
    HasDerivAt (horizon w chi) (horizonFirst w chi z) z ∧
    HasDerivAt (horizonFirst w chi) (horizonSecond w chi z) z := by
  obtain ⟨hF,hD⟩ := gaussFactor_derivatives_continued false (enorm_ofReal_lt_one hz.1 hz.2)
  exact dress_derivatives w hz.1 hF.comp_ofReal hD.comp_ofReal

/-- The full physical outer branch has actual first and second radial derivatives. -/
theorem normalizable_derivatives_continued {w chi : ℂ} {z : ℝ} (hz : z ∈ Ioo 0 1) :
    HasDerivAt (normalizable w chi) (normalizableFirst w chi z) z ∧
    HasDerivAt (normalizableFirst w chi) (normalizableSecond w chi z) z := by
  obtain ⟨hF,hD⟩ := outerFactor_derivatives_continued hz
  exact dress_derivatives w hz.1 hF hD

/-- The horizon solution obeys the original physical radial equation at free frequency. -/
theorem horizon_equation_continued {w chi : ℂ} (hw : w.im ≠ 0) {z : ℝ} (hz : z ∈ Ioo 0 1) :
    D4BMPhysicalMaster.radialJet (Complex.I*w) chi z
      (horizon w chi z) (horizonFirst w chi z) (horizonSecond w chi z)=0 := by
  unfold horizon horizonFirst horizonSecond
  rw [dress_physical w chi _ _ _ hz.1,horizonFactor_equation_continued hw (enorm_ofReal_lt_one hz.1 hz.2),mul_zero]

/-- The normalizable solution obeys the same original physical radial equation. -/
theorem normalizable_equation_continued {w chi : ℂ} {z : ℝ} (hz : z ∈ Ioo 0 1) :
    D4BMPhysicalMaster.radialJet (Complex.I*w) chi z
      (normalizable w chi z) (normalizableFirst w chi z) (normalizableSecond w chi z)=0 := by
  unfold normalizable normalizableFirst normalizableSecond
  rw [dress_physical w chi _ _ _ hz.1,outerFactor_equation_continued hz,mul_zero]

end
end RHTower.D4BMLaplaceRadial
