import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalNormalizableHorizonDomain
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFundamentalHorizonDomain

/-! Actual normalizable fundamental Xi modes satisfy the original fixed horizon domain. -/
open Complex Set
namespace RHTower.D4BMLaplaceRadial
noncomputable section

/-- Both literal fundamental frequencies annihilate their original connection coefficient. -/
theorem connection_fundamental_zero (chi : ℂ) :
    connection (-3/2-I*chi) chi=0 ∧ connection (-3/2+I*chi) chi=0 := by
  have hm : gaussC (-3/2-I*chi)-gaussB (-3/2-I*chi) chi=0 := by
    unfold gaussC gaussB
    ring
  have hp : gaussC (-3/2+I*chi)-gaussA (-3/2+I*chi) chi=0 := by
    unfold gaussC gaussA
    ring
  constructor
  · rw [connection,hm,Complex.Gamma_zero,mul_zero,div_zero]
  · rw [connection,hp,Complex.Gamma_zero,zero_mul,div_zero]

/-- At a nonreal fundamental frequency in the horizon strip, the actual normalizable branch is admitted. -/
theorem fundamental_normalizable_original_horizon_domain (w chi : ℂ)
    (hw : w.im ≠ 0) (hwr : -2 < w.re)
    (hf : w=-3/2-I*chi ∨ w=-3/2+I*chi) :
    OriginalHorizonC2 w (normalizable w chi) := by
  apply (normalizable_original_horizon_domain_iff w chi hw hwr).mpr
  rcases hf with rfl | rfl
  · exact (connection_fundamental_zero chi).1
  · exact (connection_fundamental_zero chi).2

/-- Every Xi fundamental QNM admits the actual normalizable mode with the matching physical angular momentum. -/
theorem allXi_fundamental_normalizable_horizon_domain (q : XiZeroCopy) :
    ∀ w ∈ ({-I*thetaCuspHawkingTopologicalBlackHoleQNMPlus 0 (xiSpectralPoint q),
      -I*thetaCuspHawkingTopologicalBlackHoleQNMMinus 0 (xiSpectralPoint q)} : Set ℂ),
      OriginalHorizonC2 w
        (normalizable w (thetaCuspHawkingTopologicalBlackHoleAngularMomentum (xiSpectralPoint q))) := by
  intro w hw
  have hstrip := allXi_fundamental_frequency_strip q w hw
  apply fundamental_normalizable_original_horizon_domain w _ hstrip.1 (abs_lt.mp hstrip.2).1
  simp only [mem_insert_iff,mem_singleton_iff] at hw
  rcases hw with rfl | rfl
  · left
    simp only [thetaCuspHawkingTopologicalBlackHoleQNMPlus,thetaCuspHawkingTopologicalBlackHoleConformalDecay]
    norm_num
    ring_nf
    simp only [Complex.I_sq]
    ring
  · right
    simp only [thetaCuspHawkingTopologicalBlackHoleQNMMinus,thetaCuspHawkingTopologicalBlackHoleConformalDecay]
    norm_num
    ring_nf
    simp only [Complex.I_sq]
    ring

end
end RHTower.D4BMLaplaceRadial
