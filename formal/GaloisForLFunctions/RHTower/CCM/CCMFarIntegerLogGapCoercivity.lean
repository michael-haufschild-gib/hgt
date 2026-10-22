import GaloisForLFunctions.RHTower.ThetaFarIntegerLogGapCoercivity
import GaloisForLFunctions.RHTower.ThetaComplexGroundComponents

/-!
# Full complex-source coercivity across far complete integer-log gaps

Splitting real and imaginary components extends the real positive gap to
arbitrary complex phases. Exact ground reconstruction then transfers the
result to literal smooth CCM sources and their sum and difference.
-/

noncomputable section

open MeasureTheory Set
open scoped SchwartzMap

namespace RHTower

open ThetaSourceWard

theorem exists_thetaComplex_farIntegerLogGap_coercivity :
    ∃ R kappa : ℝ, 0 < R ∧ 0 < kappa ∧
      ∀ (chi eta : 𝓢(ℝ, ℂ)), HasCompactSupport chi → HasCompactSupport eta →
      ∀ c₁ c₂ r : ℝ, 0 ≤ r → R ≤ c₂ - c₁ - 2 * r →
        Function.support chi ⊆ Metric.ball c₁ r →
        Function.support eta ⊆ Metric.ball c₂ r →
        (∀ n : ℕ, 2 ≤ n → Real.log n ∉ Ioo (c₂ - c₁ - 2 * r) (c₂ - c₁ + 2 * r)) →
        kappa * (thetaGroundNormSq chi + thetaGroundNormSq eta) ≤
          thetaFullArithmeticQuadratic (chi + eta) ∧
        kappa * (thetaGroundNormSq chi + thetaGroundNormSq eta) ≤
          thetaFullArithmeticQuadratic (chi - eta) := by
  obtain ⟨R, kappa, hR, hk, hreal⟩ := exists_thetaReal_farIntegerLogGap_coercivity
  refine ⟨R, kappa, hR, hk, fun chi eta hc he c₁ c₂ r hr hsep hs ht hfree => ?_⟩
  have hRe := hreal (thetaRealComponent chi) (thetaRealComponent eta)
    (hasCompactSupport_thetaRealComponent chi hc) (hasCompactSupport_thetaRealComponent eta he)
    c₁ c₂ r hr hsep ((support_thetaRealComponent_subset chi).trans hs)
    ((support_thetaRealComponent_subset eta).trans ht) hfree
  have hIm := hreal (thetaImagComponent chi) (thetaImagComponent eta)
    (hasCompactSupport_thetaImagComponent chi hc) (hasCompactSupport_thetaImagComponent eta he)
    c₁ c₂ r hr hsep ((support_thetaImagComponent_subset chi).trans hs)
    ((support_thetaImagComponent_subset eta).trans ht) hfree
  rw [thetaGroundNormSq_realImag chi, thetaGroundNormSq_realImag eta,
    thetaFullArithmeticQuadratic_realImag, thetaFullArithmeticQuadratic_realImag,
    thetaRealComponent_add, thetaImagComponent_add, thetaRealComponent_sub, thetaImagComponent_sub]
  constructor <;> nlinarith only [hRe.1, hRe.2, hIm.1, hIm.2]

theorem support_ccmThetaGroundProfile {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) :
    Function.support (ccmThetaGroundProfile u) = Function.support u := by
  ext x
  have hk : (thetaCuspFullSource x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (show 0 < thetaCuspFullSource x from thetaCuspTiltSource.pos x).ne'
  simp only [Function.mem_support, ccmThetaGroundProfile_apply, div_ne_zero_iff]
  exact ⟨And.left, fun hu => ⟨hu, hk⟩⟩

theorem hasCompactSupport_ccmThetaGroundProfile {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) : HasCompactSupport (ccmThetaGroundProfile u) := by
  apply u.hasCompactSupport.mono
  rw [support_ccmThetaGroundProfile]

theorem ccmThetaGroundProfile_combo_add {a : SuzukiPositiveAperture}
    (u v : CCMComplexSmoothInteriorSource a) :
    ccmThetaGroundProfile (u.combo v u 1 0) = ccmThetaGroundProfile u + ccmThetaGroundProfile v := by
  ext x
  simp only [ccmThetaGroundProfile_apply, CCMComplexSmoothInteriorSource.combo_apply,
    one_mul, zero_mul, add_zero, add_apply, add_div]

theorem ccmThetaGroundProfile_combo_sub {a : SuzukiPositiveAperture}
    (u v : CCMComplexSmoothInteriorSource a) :
    ccmThetaGroundProfile (u.combo v u (-1) 0) = ccmThetaGroundProfile u - ccmThetaGroundProfile v := by
  ext x
  simp only [ccmThetaGroundProfile_apply, CCMComplexSmoothInteriorSource.combo_apply,
    neg_one_mul, zero_mul, add_zero, sub_apply, ← sub_eq_add_neg, sub_div]

/-- A uniform positive lower bound for literal full Weil energies of arbitrary complex
source pairs in this geometric class. No spectral or arithmetic positivity is assumed. -/
theorem exists_ccm_farIntegerLogGap_coercivity :
    ∃ R kappa : ℝ, 0 < R ∧ 0 < kappa ∧
      ∀ (a : SuzukiPositiveAperture) (u v : CCMComplexSmoothInteriorSource a)
        (c₁ c₂ r : ℝ), 0 ≤ r → R ≤ c₂ - c₁ - 2 * r →
        Function.support u ⊆ Metric.ball c₁ r →
        Function.support v ⊆ Metric.ball c₂ r →
        (∀ n : ℕ, 2 ≤ n → Real.log n ∉ Ioo (c₂ - c₁ - 2 * r) (c₂ - c₁ + 2 * r)) →
        kappa * (‖ccmArchimedeanFormEmbedding a u.toCCMFormVector‖ ^ 2 +
            ‖ccmArchimedeanFormEmbedding a v.toCCMFormVector‖ ^ 2) ≤
          ccmRestrictedWeilSourceQuadratic a (u.combo v u 1 0).toCCMFormVector ∧
        kappa * (‖ccmArchimedeanFormEmbedding a u.toCCMFormVector‖ ^ 2 +
            ‖ccmArchimedeanFormEmbedding a v.toCCMFormVector‖ ^ 2) ≤
          ccmRestrictedWeilSourceQuadratic a (u.combo v u (-1) 0).toCCMFormVector := by
  obtain ⟨R, kappa, hR, hk, hcomplex⟩ := exists_thetaComplex_farIntegerLogGap_coercivity
  refine ⟨R, kappa, hR, hk, fun a u v c₁ c₂ r hr hsep hs ht hfree => ?_⟩
  have h := hcomplex (ccmThetaGroundProfile u) (ccmThetaGroundProfile v)
    (hasCompactSupport_ccmThetaGroundProfile u) (hasCompactSupport_ccmThetaGroundProfile v)
    c₁ c₂ r hr hsep (by rwa [support_ccmThetaGroundProfile])
    (by rwa [support_ccmThetaGroundProfile]) hfree
  rw [thetaGroundNormSq_ccmProfile_eq_physical, thetaGroundNormSq_ccmProfile_eq_physical,
    ← ccmThetaGroundProfile_combo_add, ← ccmThetaGroundProfile_combo_sub,
    ← ccmRestrictedWeilSourceQuadratic_eq_thetaFullArithmetic,
    ← ccmRestrictedWeilSourceQuadratic_eq_thetaFullArithmetic] at h
  exact h

end RHTower
