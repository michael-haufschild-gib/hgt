import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerConvolutionSolvability

/-! # The complete Fredholm repair is a unitized original convolution

Subtract the actual finite causal projection of the source itself. Every
resonant jet disappears, while every other full block is retained.
-/

open Complex
open scoped Classical

namespace RHTower
noncomputable section

theorem exists_deningerMeyerConvolutionRepairSource (g : DeningerMeyerStrongLogTarget) :
    ∃ b : DeningerMeyerStrongLogTarget,
      1+deningerMeyerHilbertConvolution b = deningerMeyerConvolutionFredholmRepair g ∧
      ∀ rho : XiDivisorSupport, 1+deningerMeyerStrongLogMellin b (rho : ℂ) ≠ 0 := by
  let S := deningerMeyerConvolutionResonantPacket g
  let u : DeningerMeyerStrongLogCohomology := Submodule.Quotient.mk g
  obtain ⟨b, hb⟩ := (LinearMap.range deningerMeyerStrongLogSumLM).mkQ_surjective
    (u-deningerMeyerFiniteXiCausalProjector S u)
  have hhb : deningerMeyerHasseHilbertLM (Submodule.Quotient.mk b) =
      deningerMeyerHasseHilbertLM u -
        deningerMeyerConvolutionResonantProjection g (deningerMeyerHasseHilbertLM u) := by
    change deningerMeyerHasseHilbertLM
      ((LinearMap.range deningerMeyerStrongLogSumLM).mkQ b) = _
    rw [hb, map_sub, ← deningerMeyerConvolution_projection_source]
  have hcoef (rho : XiDivisorSupport) (k : ℕ) (hk : k < xiSupportMultiplicity rho) :
      deningerMeyerHasseMoment b k (rho : ℂ) =
        if rho ∈ deningerMeyerConvolutionResonance g then 0
        else deningerMeyerHasseMoment g k (rho : ℂ) := by
    have he := congrArg (fun x : DeningerArithmeticJetHilbert => x ⟨rho, ⟨k, hk⟩⟩) hhb
    change deningerMeyerHasseMoment b k (rho : ℂ) =
      deningerMeyerHasseMoment g k (rho : ℂ) -
        deningerHasseBlockProjection _ (deningerMeyerHasseHilbertLM u) ⟨rho, ⟨k, hk⟩⟩ at he
    rw [deningerHasseBlockProjection_apply] at he
    change deningerMeyerHasseMoment b k (rho : ℂ) =
      deningerMeyerHasseMoment g k (rho : ℂ) -
        (if rho ∈ deningerMeyerConvolutionResonance g then
          deningerMeyerHasseMoment g k (rho : ℂ) else 0) at he
    split_ifs at he ⊢ <;> simpa using he
  refine ⟨b, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext q
    have hc : deningerMeyerHilbertConvolution b x q =
        if q.1 ∈ deningerMeyerConvolutionResonance g then 0
        else deningerMeyerHilbertConvolution g x q := by
      rw [deningerMeyerHilbertConvolution_jets]
      by_cases hq : q.1 ∈ deningerMeyerConvolutionResonance g
      · rw [if_pos hq]
        apply Finset.sum_eq_zero
        intro k hk
        have hkm : k < xiSupportMultiplicity q.1 :=
          lt_of_le_of_lt (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) q.2.isLt
        rw [hcoef q.1 k hkm, if_pos hq, zero_mul]
      · rw [if_neg hq, deningerMeyerHilbertConvolution_jets]
        apply Finset.sum_congr rfl
        intro k hk
        have hkm : k < xiSupportMultiplicity q.1 :=
          lt_of_le_of_lt (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) q.2.isLt
        rw [hcoef q.1 k hkm, if_neg hq]
    change x q+deningerMeyerHilbertConvolution b x q = _
    rw [hc, deningerMeyerConvolutionFredholmRepair_apply]
    split_ifs <;> simp
  · intro rho
    have hc := hcoef rho 0 (xiSupportMultiplicity_pos rho)
    simp only [deningerMeyerHasseMoment, Nat.factorial_zero, Nat.cast_one, div_one,
      deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv, iteratedDeriv_zero] at hc
    rw [hc]
    by_cases hrho : rho ∈ deningerMeyerConvolutionResonance g
    · simp [hrho]
    · rw [if_neg hrho]
      exact hrho

end
end RHTower
