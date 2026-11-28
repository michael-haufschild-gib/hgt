import GaloisForLFunctions.HTGeometry.RealCharacterExp
import GaloisForLFunctions.HTGeometry.LaplaceAtomicRigidity

/-! # A continuous unit phase on forward time is a single real frequency -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.UniversalResponse

open scoped NNReal

/-- Extend a forward phase to signed time by dividing its positive and negative
parts. The full-line character theorem then identifies its frequency. -/
theorem forward_character {C : ℝ≥0 → ℂ} (hc : Continuous C)
    (add : ∀ s t, C (s+t)=C s*C t) (unit : ∀ t, ‖C t‖=1) :
    ∃ freq : ℝ, ∀ t : ℝ≥0, C t=Complex.exp ((freq*(t:ℝ):ℝ)*Complex.I) := by
  have nz (t : ℝ≥0) : C t≠0 := by
    intro h
    exact zero_ne_one (by simpa only [h,norm_zero] using unit t)
  have origin : C 0=1 := by
    have h := add 0 0
    rw [add_zero] at h
    exact mul_right_cancel₀ (nz 0) (h.symm.trans (one_mul _).symm)
  let ψ (t : ℝ) := C t.toNNReal/C (-t).toNNReal
  have cont : Continuous ψ := (hc.comp continuous_real_toNNReal).div
    ((hc.comp continuous_real_toNNReal).comp continuous_neg) (fun t => nz (-t).toNNReal)
  have mulψ (s t : ℝ) : ψ (s+t)=ψ s*ψ t := by
    have balance : (s+t).toNNReal+((-s).toNNReal+(-t).toNNReal)=
        (s.toNNReal+t.toNNReal)+(-(s+t)).toNNReal := by
      apply NNReal.coe_injective
      simp only [NNReal.coe_add]
      linarith only [HTGeometry.posPart_negPart_real (s+t),HTGeometry.posPart_negPart_real s,
        HTGeometry.posPart_negPart_real t]
    have H := congrArg C balance
    simp only [add] at H
    unfold ψ
    rw [div_mul_div_comm]
    exact (div_eq_div_iff (nz _) (mul_ne_zero (nz _) (nz _))).mpr H
  have normψ (x : ℝ) : ‖ψ x‖=1 := by simp only [ψ,norm_div,unit,div_one]
  obtain ⟨freq,h⟩ := GaloisForLFunctions.exists_exp_of_continuous_character cont mulψ normψ
  refine ⟨freq,fun t => ?_⟩
  have negative : (-(t:ℝ)).toNNReal=0 := Real.toNNReal_of_nonpos (neg_nonpos.mpr t.property)
  have H := h (t:ℝ)
  change C (t:ℝ).toNNReal/C (-(t:ℝ)).toNNReal=_ at H
  rwa [Real.toNNReal_coe,negative,origin,div_one] at H

#print axioms forward_character

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.UniversalResponse
