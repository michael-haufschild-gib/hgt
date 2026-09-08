import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalHorizonDomain
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceContinuationCorridor

/-! The original horizon domain selects the physical Gauss branch at every fundamental Xi QNM. -/
namespace RHTower.D4BMLaplaceRadial
open Complex Set Filter Topology
noncomputable section
set_option autoImplicit false

/-- The strict Xi strip puts both actual fundamental frequencies in the nonreal continuation band. -/
theorem allXi_fundamental_frequency_strip (q : XiZeroCopy) :
    ∀ w ∈ ({-Complex.I*thetaCuspHawkingTopologicalBlackHoleQNMPlus 0 (xiSpectralPoint q),
      -Complex.I*thetaCuspHawkingTopologicalBlackHoleQNMMinus 0 (xiSpectralPoint q)} : Set ℂ),
      w.im ≠ 0 ∧ |w.re| < 2 := by
  have hq := thetaCuspHawkingHypergeometricXiSpectralPoint_re_ne_zero q
  have hs := abs_im_xiSpectralPoint_lt_half q
  rw [abs_lt] at hs
  intro w hw
  show w.im ≠ 0 ∧ |w.re| < 2
  simp only [mem_insert_iff,mem_singleton_iff] at hw
  rcases hw with rfl | rfl <;>
    simp only [thetaCuspHawkingTopologicalBlackHoleQNMPlus,thetaCuspHawkingTopologicalBlackHoleQNMMinus,
      thetaCuspHawkingTopologicalBlackHoleAngularMomentum,thetaCuspHawkingTopologicalBlackHoleConformalDecay,
      Complex.mul_im,Complex.mul_re,Complex.sub_re,Complex.sub_im,Complex.neg_re,Complex.neg_im,
      Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,Complex.add_re,Complex.add_im,Complex.div_re,Complex.div_im]
  all_goals norm_num
  · exact ⟨hq,abs_lt.mpr ⟨by linarith [hs.1],by linarith [hs.2]⟩⟩
  · exact ⟨hq,abs_lt.mpr ⟨by linarith [hs.2],by linarith [hs.1]⟩⟩

/-- Every actual Xi fundamental QNM has the same C² horizon selection, with no supplied
regularity, nonresonance, boundary, or RH assumption. The original mode also obeys its actual radial equation. -/
theorem allXi_fundamental_original_horizon_domain (q : XiZeroCopy) :
    ∀ w ∈ ({-Complex.I*thetaCuspHawkingTopologicalBlackHoleQNMPlus 0 (xiSpectralPoint q),
      -Complex.I*thetaCuspHawkingTopologicalBlackHoleQNMMinus 0 (xiSpectralPoint q)} : Set ℂ),
      (∀ A B : ℂ, OriginalHorizonC2 w
        (fun b => A*horizon w (thetaCuspHawkingTopologicalBlackHoleAngularMomentum (xiSpectralPoint q)) b+B*horizon (-w) (thetaCuspHawkingTopologicalBlackHoleAngularMomentum (xiSpectralPoint q)) b) ↔ B = 0) ∧
      ∀ b ∈ Ioo (0:ℝ) 1, D4BMPhysicalMaster.radialJet (Complex.I*w) (thetaCuspHawkingTopologicalBlackHoleAngularMomentum (xiSpectralPoint q)) b
        (horizon w (thetaCuspHawkingTopologicalBlackHoleAngularMomentum (xiSpectralPoint q)) b) (horizonFirst w (thetaCuspHawkingTopologicalBlackHoleAngularMomentum (xiSpectralPoint q)) b)
        (horizonSecond w (thetaCuspHawkingTopologicalBlackHoleAngularMomentum (xiSpectralPoint q)) b) = 0 := by
  intro w hw
  have hstrip := allXi_fundamental_frequency_strip q w hw
  exact ⟨fun A B => originalHorizonC2_modes_iff w (thetaCuspHawkingTopologicalBlackHoleAngularMomentum (xiSpectralPoint q)) A B hstrip.1
    (abs_lt.mp hstrip.2).1,fun b hb => horizon_equation_continued hstrip.1 hb⟩

end
end RHTower.D4BMLaplaceRadial
