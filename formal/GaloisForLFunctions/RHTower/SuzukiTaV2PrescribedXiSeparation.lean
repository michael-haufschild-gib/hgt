import GaloisForLFunctions.RHTower.SuzukiTaV2PrescribedParityLimit
import GaloisForLFunctions.RHTower.CCMSuzukiCrossApertureProjectiveWronskian
import GaloisForLFunctions.RHTower.SuzukiXiFirstDefectJet

open Filter Complex
open scoped Topology
noncomputable section
namespace RHTower
open GaloisForLFunctions.RHTower

/-- The first source-Wronskian mode vanishes with both apertures independently
cofinal, for the literal actual prescribed-shift family. -/
theorem tendsto_suzukiTaV2_prescribed_anchorWronskian_zero :
    Tendsto (fun p : SuzukiPositiveAperture × SuzukiPositiveAperture =>
      suzukiTaV2CrossApertureRawWronskian p.1 p.2 I /
        (suzukiTaV2RawCharacteristicE p.2 I * suzukiTaV2RawCharacteristicE p.1 I))
      ((comap (fun a : SuzukiPositiveAperture => a.1) atTop) ×ˢ
        (comap (fun a : SuzukiPositiveAperture => a.1) atTop)) (𝓝 0) := by
  have hz := (Complex.continuous_ofReal.tendsto 0).comp
    tendsto_suzukiTaV2_prescribed_firstDefect_zero
  have h := ((hz.comp tendsto_snd).sub (hz.comp tendsto_fst)).neg.div_const (4 : ℂ)
  simpa only [suzukiTaV2CrossApertureRawWronskian_anchor_eq_defect_increment,
    Complex.ofReal_zero, sub_zero, neg_zero, zero_div, Function.comp_def] using h

/-- No cofinal aperture schedule for the actual prescribed shift identifies
the normalized Xi carrier. This obstruction concerns these exact coordinates. -/
theorem not_exists_suzukiTaV2_prescribed_cofinal_xi_limit :
    ¬ ∃ a : ℕ → SuzukiPositiveAperture,
      Tendsto (fun n => (a n).1) atTop atTop ∧
      TendstoLocallyUniformlyOn (fun n => suzukiTaV2Livsic (a n))
        xiHedenmalmLivsicTarget atTop {z : ℂ | 0 < z.im} := by
  rintro ⟨a, ha, hconv⟩
  have ha' : Tendsto a atTop
      (comap (fun b : SuzukiPositiveAperture => b.1) atTop) :=
    tendsto_comap_iff.2 ha
  have hz := (Complex.continuous_ofReal.tendsto 0).comp
    (tendsto_suzukiTaV2_prescribed_firstDefect_zero.comp ha')
  have hhol : ∀ᶠ n in atTop,
      DifferentiableOn ℂ (suzukiTaV2Livsic (a n)) {z : ℂ | 0 < z.im} :=
    Eventually.of_forall fun n =>
      differentiableOn_suzukiLivsicQuotient_upperHalfPlane
        (differentiable_suzukiTaV2CharacteristicA (a n))
        (differentiable_suzukiTaV2CharacteristicE (a n))
        (suzukiTaV2CharacteristicA_I (a n)) (suzukiTaV2_allAngleRealZeros (a n))
  have hxi := xiHedenmalmLivsic_firstDefectJet_tendsto_of_locallyUniform
    (fun n => suzukiTaV2Livsic (a n)) hconv hhol
  have hz' : Tendsto (fun n => 2 * I * deriv (suzukiTaV2Livsic (a n)) I)
      atTop (𝓝 (0 : ℂ)) := by
    simpa only [suzukiTaV2_coalescingDefectAngle_eq_two_I_mul_deriv,
      Complex.ofReal_zero, Function.comp_def] using hz
  have heq := congrArg Complex.re (tendsto_nhds_unique hz' hxi)
  simp only [Complex.zero_re, Complex.ofReal_re] at heq
  have hpos := xiHedenmalmLivsicFirstDefectJet_mem_Ioo.1
  linarith

end RHTower
end
