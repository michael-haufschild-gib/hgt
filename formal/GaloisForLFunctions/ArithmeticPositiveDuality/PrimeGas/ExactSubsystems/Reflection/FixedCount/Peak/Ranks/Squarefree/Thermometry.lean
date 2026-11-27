import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.FixedCount.Peak.Ranks.Squarefree.Filling

/-! # Signed thermometry and its half-filling boundary under prime exclusion -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Peak.Ranks.Squarefree

open _root_.HTGeometry
open scoped ComplexConjugate

variable (S : Finset Nat.Primes) (k : ℕ) (h : k+1 < S.card)

def fillingDifference := gap S k h-gap S (S.card-k-2) (by omega)

theorem fillingDifference_zero_iff : fillingDifference S k h = 0 ↔ 2*(k+1) = S.card := by
  rw [fillingDifference,sub_eq_zero,gap_eq_iff]
  omega

private theorem outgoing_odds (s : ℂ) : measuredOdds S (fun _ => 1) (k+1) s =
    logOdds (finiteGibbsStateWeight (2*s.re-1) (cost primeEnergy : Sector S (k+1) → ℝ)) := by
  rw [measuredOdds_eq]
  simp_rw [prime_cost]

/-- Antisymmetrizing the two rank readings returns the difference of the filling gaps
times signed damping, including at half filling and at the uniform law. -/
theorem signed_filling_contrast (s : ℂ) :
    measuredOdds S (fun _ => 1) (k+1) s-measuredOdds S (fun _ => 1) (k+1) (1-conj s) =
      (2*s.re-1)*fillingDifference S k h := by
  obtain ⟨l,q,u,v,hl,hu,dl,du⟩ := filling_gaps S k h
  rw [outgoing_odds,outgoing_odds,
    show 2*(1-conj s).re-1 = -(2*s.re-1) by rw [Complex.sub_re,Complex.one_re,Complex.conj_re]; ring,
    odds_contrast hl hu,dl,du,fillingDifference]

theorem recover_damping_of_filling (hn : 2*(k+1) ≠ S.card) (s : ℂ) :
    (measuredOdds S (fun _ => 1) (k+1) s-measuredOdds S (fun _ => 1) (k+1) (1-conj s)) /
      fillingDifference S k h = 2*s.re-1 := by
  rw [signed_filling_contrast S k h,mul_div_cancel_right₀ _ (fun he => hn ((fillingDifference_zero_iff S k h).mp he))]

include h

theorem ranked_match_iff_half_or_isometry (s : ℂ) :
    measuredOdds S (fun _ => 1) (k+1) s = measuredOdds S (fun _ => 1) (k+1) (1-conj s) ↔
      (∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x) ∨ 2*(k+1) = S.card := by
  rw [split_isometric_iff,← sub_eq_zero,signed_filling_contrast S k h,mul_eq_zero,fillingDifference_zero_iff]
  apply or_congr_left
  constructor <;> intro hx <;> linarith only [hx]

/-- Two leading ranks agree under reflection exactly when the entire squarefree law
agrees after a permutation of its basis. -/
theorem ranked_match_iff_full_match (s : ℂ) :
    measuredOdds S (fun _ => 1) (k+1) s = measuredOdds S (fun _ => 1) (k+1) (1-conj s) ↔
      Matched S (fun _ => 1) (k+1) s := by
  rw [ranked_match_iff_half_or_isometry S k h,split_isometric_iff,matched_iff_line_or_reflection,
    feasible_iff,squarefree_reflection_iff]
  have cap : capacity (fun _ : S => 1) = S.card := by simp [capacity]
  rw [cap]
  have hk := h.le
  simp only [hk,true_and,Nat.succ_ne_zero,h.ne,false_or]

#print axioms fillingDifference_zero_iff
#print axioms signed_filling_contrast
#print axioms recover_damping_of_filling
#print axioms ranked_match_iff_half_or_isometry
#print axioms ranked_match_iff_full_match

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Peak.Ranks.Squarefree
