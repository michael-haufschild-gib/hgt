import GaloisForLFunctions.HTGeometry.FirstHitExponentLaw
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.Aliasing

/-! # A uniform phase-error floor on a translated resonant lattice -/

open Finset Real
namespace GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactRecurrence.FineAffordability
noncomputable section

/-- An integral resonance preserves the anchor's distance from zero on
that character. A simultaneous phase fit can pay at most its error times
the sum of the absolute charge coefficients. -/
theorem charge_floor {I : Type*} [Fintype I] (w : I → ℝ) (m : I → ℤ) (v τ : ℝ) (k n : ℤ)
    (hk : τ*finiteTorusCharacterDetuning m w=(k:ℝ)*(2*π)) {ε : ℝ}
    (hc : ∀ i, latticeClose ((v+(n:ℝ)*τ)*w i/(2*π)) ε) :
    latticeDist (v*finiteTorusCharacterDetuning m w/(2*π))≤ε*∑ i, |(m i:ℝ)| := by
  classical
  choose z hz using hc
  let Z : ℤ := (∑ i, m i*z i)-n*k
  let t := v+(n:ℝ)*τ
  have hbalance : v*finiteTorusCharacterDetuning m w/(2*π)-(Z:ℝ)=
      ∑ i, (m i:ℝ)*(t*w i/(2*π)-(z i:ℝ)) := by
    rw [show (∑ i, (m i:ℝ)*(t*w i/(2*π)-(z i:ℝ)))=
      t/(2*π)*finiteTorusCharacterDetuning m w-∑ i, (m i:ℝ)*(z i:ℝ) by
        simp only [finiteTorusCharacterDetuning,mul_sub,sum_sub_distrib,mul_sum]
        congr 1
        exact sum_congr rfl fun i _ => by ring]
    dsimp only [Z,t]
    push_cast
    field_simp
    linear_combination -(n:ℝ)*hk
  calc
    _ ≤ _ := latticeDist_le _ Z
    _ = _ := congrArg abs hbalance
    _ ≤ ∑ i, |(m i:ℝ)*(t*w i/(2*π)-(z i:ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |(m i:ℝ)|*ε := by
      apply sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hz i).le (abs_nonneg _)
    _ = _ := by rw [←sum_mul,mul_comm]

/-- If the anchor itself is a free period, any resonance of the step
imposes one strictly positive uniform lower accuracy on all signed ticks. -/
theorem fine_gap_of_resonance {I : Type*} [Fintype I] (w : I → ℝ) (v τ : ℝ)
    (hf : FreeAtStep w v) (hn : ¬FreeAtStep w τ) :
    ∃ ε>0, ∀ n : ℤ, ¬∀ i, latticeClose ((v+(n:ℝ)*τ)*w i/(2*π)) ε := by
  unfold FreeAtStep at hn
  push Not at hn
  obtain ⟨m,k,hk,hm⟩ := hn
  let d := latticeDist (v*finiteTorusCharacterDetuning m w/(2*π))
  have hd : 0<d := lt_of_le_of_ne (latticeDist_nonneg _) (fun he => by
    obtain ⟨j,hj⟩ := latticeDist_eq_zero_iff.mp he.symm
    exact hm (hf m j ((div_eq_iff (by positivity : (2:ℝ)*π≠0)).mp hj)))
  let C := ∑ i, |(m i:ℝ)|
  have hC : 0≤C := sum_nonneg fun _ _ => abs_nonneg _
  have hden : 0<C+1 := by linarith only [hC]
  refine ⟨d/(C+1),div_pos hd hden,fun n h => ?_⟩
  have hl := charge_floor w m v τ k n hk h
  change d≤d/(C+1)*C at hl
  have hh := div_mul_cancel₀ d hden.ne'
  linarith only [hl,hh,div_pos hd hden]

#print axioms fine_gap_of_resonance
end
end GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactRecurrence.FineAffordability
