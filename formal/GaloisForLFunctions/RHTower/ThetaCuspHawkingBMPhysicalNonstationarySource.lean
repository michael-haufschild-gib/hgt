import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFundamentalSourceMomentTransport
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNonstationaryMoment

/-! Identification of the actual physical source with the nonstationary moment family. -/
namespace RHTower.D4BMJointSource
open Complex Set MeasureTheory D4BMLaplaceRadial GaloisForLFunctions.HTGeometry
open scoped Polynomial
noncomputable section
set_option autoImplicit false

theorem physicalNonstationaryRate (q : XiZeroCopy) :
    D4BMModularCore.physicalRate q true = -2*physicalFundamentalFrequency q true-4 := by
  rw [physicalFundamentalFrequency_eq]
  norm_num [D4BMModularCore.physicalRate]
  ring

theorem physicalNonstationaryFrequency_strip (q : XiZeroCopy) :
    (physicalFundamentalFrequency q true).re ∈ Ioo (-(3/2):ℝ) (-1) := by
  have hq := xi_divisor_support_re_mem_open_unit q.1
  rw [physicalFundamentalFrequency_eq]
  norm_num [Complex.div_re]
  constructor <;> linarith [hq.1,hq.2]

theorem fundamentalJacobiCore_nonstationary (n : ℕ) (w : ℂ) {x : ℝ}
    (hx : x ∈ Icc (0:ℝ) 1) :
    fundamentalJacobiCore n (-2*w-4) x = nonstationaryCore ((1-Polynomial.X)^n) 0 w x := by
  have hb : (2-(x:ℂ)) ≠ 0 := by exact_mod_cast (show (2-x:ℝ) ≠ 0 by linarith [hx.2])
  simp only [fundamentalJacobiCore,nonstationaryCore,nonstationaryWeight,power,
    Polynomial.eval_pow,Polynomial.eval_sub,Polynomial.eval_one,Polynomial.eval_X,pow_zero,div_one,
    Complex.ofReal_sub,Complex.ofReal_ofNat]
  rw [show 2*(-2*w-4)=-4*w-(8:ℂ) by ring,Complex.cpow_sub _ _ hb]
  rw [show (2-(x:ℂ))^(8:ℂ)=(2-(x:ℂ))^(8:ℕ) from Complex.cpow_natCast _ 8]
  ring

/-- Both definitions retain the same endpoint coefficient and the same admitted source remainder. -/
theorem fundamentalJacobiMoment_nonstationary (n : ℕ) (w : ℂ) :
    fundamentalJacobiMoment n w (-2*w-4) = nonstationaryMoment ((1-Polynomial.X)^n) 0 w := by
  have h0 := fundamentalJacobiCore_nonstationary n w (by constructor <;> norm_num : (0:ℝ) ∈ Icc (0:ℝ) 1)
  dsimp only [fundamentalJacobiMoment,nonstationaryMoment,firstEndpointMellin,firstEndpointMellinRemainder]
  rw [h0]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  dsimp only
  rw [fundamentalJacobiCore_nonstationary n w ⟨hx.1.le,hx.2⟩]

theorem physicalFundamentalSourceMoment_nonstationary (q : XiZeroCopy) (a : ℂ) :
    let w := physicalFundamentalFrequency q true
    fundamentalSourceMoment w (D4BMModularCore.physicalRate q true) a =
      2*a^(2 : ℕ)*(fundamentalMomentConstant (-2*w-4)*nonstationaryMoment ((1-Polynomial.X)^(2 : ℕ)) 0 w+
        fundamentalMomentQuadratic w (-2*w-4)*nonstationaryMoment ((1-Polynomial.X)^(4 : ℕ)) 0 w) := by
  dsimp only
  rw [physicalFundamentalSourceMoment_polynomial q true true a,physicalNonstationaryRate]
  simp only [fundamentalJacobiMoment_nonstationary]

theorem nonstationarySourceConstant (w : ℂ) :
    fundamentalMomentConstant (-2*w-4) = 5*(w+1)^(2 : ℕ)+(5/2:ℂ)*(w+1)-3/2 := by
  unfold fundamentalMomentConstant
  ring

theorem nonstationarySourceQuadratic (w : ℂ) :
    fundamentalMomentQuadratic w (-2*w-4) =
      (15/2:ℂ)*(w+1)^(4 : ℕ)+(81/4:ℂ)*(w+1)^(3 : ℕ)+15*(w+1)^(2 : ℕ)+(9/4:ℂ)*(w+1) := by
  unfold fundamentalMomentQuadratic
  ring

theorem physicalFundamentalSourceMoment_amplitude (q : XiZeroCopy) (a : ℂ) :
    fundamentalSourceMoment (physicalFundamentalFrequency q true) (D4BMModularCore.physicalRate q true) a =
      a^(2 : ℕ)*fundamentalSourceMoment (physicalFundamentalFrequency q true) (D4BMModularCore.physicalRate q true) 1 := by
  rw [physicalFundamentalSourceMoment_nonstationary q a,physicalFundamentalSourceMoment_nonstationary q 1]
  ring

end
end RHTower.D4BMJointSource
