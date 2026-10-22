import GaloisForLFunctions.RHTower.Suzuki.SuzukiCCMMixedScrewWeilBridge
import GaloisForLFunctions.RHTower.HodgeNyquistExclusion
import GaloisForLFunctions.RHTower.XiZeroCountingFunction
import GaloisForLFunctions.RHTower.CompletedPrimeFluxFittingAttachment
import Zeta23.ExplicitFormula

/-!
# The actual CCM form and the multiplicity-weighted zeta Weil form

This bridge retains every multiplicity copy and both Fourier orientations.
It permits estimates on actual compact zeta tests to be used in the physical
CCM source domain, without a hypothesis on the locations of the zeros.
-/

open Complex MeasureTheory Set Zeta23
open scoped InnerProduct
noncomputable section
namespace RHTower

private theorem carrier_xi_zero (ρ : zetaZeroConfig.carrier) : xi (ρ : ℂ) = 0 := by
  have hρ : riemannZeta (ρ : ℂ) = 0 ∧ 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := ρ.2
  have h0 : (ρ : ℂ) ≠ 0 := by
    intro h
    simpa only [h, Complex.zero_re, lt_self_iff_false] using hρ.2.1
  have h1 : (ρ : ℂ) ≠ 1 := by
    intro h
    simpa only [h, Complex.one_re, lt_self_iff_false] using hρ.2.2
  rw [xi_eq_xiUnit_mul_zeta h0 h1 hρ.2.1, hρ.1, mul_zero]

/-- The two actual zero carriers agree, before accounting for their multiplicities. -/
def xiDivisorZetaCarrierEquiv : XiDivisorSupport ≃ zetaZeroConfig.carrier where
  toFun ρ := ⟨ρ, xiZeroCopy_mem_carrier
    ⟨ρ, ⟨0, by have h := xi_divisor_pos_on_support ρ; omega⟩⟩⟩
  invFun ρ := ⟨ρ, by
    change MeromorphicOn.divisor xi univ (ρ : ℂ) ≠ 0
    rw [xi_divisor_apply_of_mem (mem_univ _)]
    exact_mod_cast xi_order_toNat_ne_zero (carrier_xi_zero ρ)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem xiDivisorZetaCarrierEquiv_multiplicity (ρ : XiDivisorSupport) :
    (MeromorphicOn.divisor xi univ (ρ : ℂ)).toNat =
      zetaZeroConfig.mult (xiDivisorZetaCarrierEquiv ρ) := by
  rw [xi_divisor_apply_of_mem (mem_univ _), Int.toNat_natCast]
  change (analyticOrderAt xi (ρ : ℂ)).toNat = (analyticOrderAt riemannZeta (ρ : ℂ)).toNat
  rw [xi_analyticOrderAt_eq_riemannZeta_of_mem_strip]
  exact (xiDivisorZetaCarrierEquiv ρ).2.2

private theorem spectralPoint_eq_gammaOf (q : XiZeroCopy) :
    xiSpectralPoint q = gammaOf (q.1 : ℂ) := by
  simp only [xiSpectralPoint, gammaOf, div_eq_mul_inv, Complex.inv_I]

private theorem tsum_copies_eq_carrier (F : ℂ → ℂ)
    (hF : Summable (fun q : XiZeroCopy => F (xiSpectralPoint q))) :
    (∑' q : XiZeroCopy, F (xiSpectralPoint q)) =
      ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℂ) * F (gammaOf ρ) := by
  rw [hF.tsum_sigma]
  rw [← xiDivisorZetaCarrierEquiv.tsum_eq
    (fun ρ : zetaZeroConfig.carrier => (zetaZeroConfig.mult ρ : ℂ) * F (gammaOf ρ))]
  apply tsum_congr
  intro ρ
  simp only [spectralPoint_eq_gammaOf, tsum_fintype, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    xiDivisorZetaCarrierEquiv_multiplicity]
  rfl

/-- The Hermitian convolution is the literal zeta explicit-formula test. -/
theorem ccmSmoothHermitianConvolution_eq_weilTest {a : SuzukiPositiveAperture}
    (u v : CCMComplexSmoothInteriorSource a) :
    suzukiHermitianConvolution v.toSuzukiSmoothCompactTest u.toSuzukiSmoothCompactTest =
      EF.weilTest v u := by
  funext x
  rfl

/-- Exact mixed identification, with divisor multiplicities and the Fourier sign preserved. -/
theorem ccmRestrictedWeilForm_complexSmooth_eq_zetaWeil {a : SuzukiPositiveAperture}
    (u v : CCMComplexSmoothInteriorSource a) :
    ccmRestrictedWeilForm a u.toCCMFormVector v.toCCMFormVector = zetaZeroConfig.W v u := by
  let k := suzukiHermitianConvolution v.toSuzukiSmoothCompactTest u.toSuzukiSmoothCompactTest
  have hminus := summable_suzukiWeilDistribution_hermitianConvolution a.2.le
    v.toSuzukiSmoothCompactTest u.toSuzukiSmoothCompactTest
  have hplus : Summable (fun q : XiZeroCopy => paperFT k (xiSpectralPoint q)) := by
    have h := (xiZeroCopyReflectEquiv.summable_iff).2 hminus
    change Summable (fun q : XiZeroCopy =>
      suzukiEntireFourier k (-xiSpectralPoint (xiZeroCopyReflectEquiv q))) at h
    simpa only [xiSpectralPoint_reflect, neg_neg, suzukiEntireFourier, paperFT] using h
  have hreflect := xiZeroCopyReflectEquiv.tsum_eq
    (fun q : XiZeroCopy => suzukiEntireFourier k (-xiSpectralPoint q))
  simp only [xiSpectralPoint_reflect, neg_neg] at hreflect
  rw [ccmRestrictedWeilForm_complexSmooth_eq_suzukiWeilDistribution,
    suzukiWeilDistribution]
  change (∑' q : XiZeroCopy, suzukiEntireFourier k (-xiSpectralPoint q)) = _
  rw [← hreflect]
  change (∑' q : XiZeroCopy, paperFT k (xiSpectralPoint q)) = _
  rw [tsum_copies_eq_carrier _ hplus, ZeroConfig.W]
  apply tsum_congr
  intro ρ
  dsimp only [k]
  rw [ccmSmoothHermitianConvolution_eq_weilTest,
    EF.paperFT_weilTest v.continuous u.continuous v.hasCompactSupport u.hasCompactSupport]
  simp only [ZeroConfig.Wsummand, mul_assoc]

/-- The complete real source energy equals the actual zeta Weil energy. -/
theorem ccmRestrictedWeilSource_complexSmooth_eq_zetaWeil {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) :
    ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector = (zetaZeroConfig.W u u).re := by
  rw [← ccmRestrictedWeilForm_self_re_eq_source, ccmRestrictedWeilForm_complexSmooth_eq_zetaWeil]

end RHTower
