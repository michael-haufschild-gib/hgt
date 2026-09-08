import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceGaussFactors
import Mathlib.Analysis.Normed.Group.Bounded

/-! Growth of the actual outer Gauss coefficients, including resonant frequencies. -/

open Complex Set Filter Topology
namespace RHTower.D4BMLaplaceRadial
noncomputable section

def outerCoefficient (w chi : ℂ) (n : ℕ) : ℂ :=
  ordinaryHypergeometricCoefficient (gaussC w-gaussA w chi) (gaussC w-gaussB w chi) (3/2) n

private theorem outer_gap (w chi : ℂ) :
    (3/2:ℂ)-(gaussC w-gaussA w chi)-(gaussC w-gaussB w chi) = -w := by
  dsimp [gaussA,gaussB,gaussC]
  ring

private theorem weighted_coefficients_bounded {w chi : ℂ} (h : Chamber w chi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      ‖(n:ℂ)^(-w)*(n+1)*outerCoefficient w chi (n+1)‖ ≤ C := by
  obtain ⟨-,-,-,ha,hb⟩ := chamber_parameters h
  have ht := tendsto_normalized_ordinaryHypergeometricCoefficient
    (gaussC w-gaussA w chi) (gaussC w-gaussB w chi) (3/2)
    (avoidsNegNat_of_re_pos ha) (avoidsNegNat_of_re_pos hb)
    (avoidsNegNat_of_re_pos (by norm_num : 0 < (3/2:ℂ).re))
  rw [outer_gap] at ht
  obtain ⟨C,hC⟩ := (Metric.isBounded_range_of_tendsto _ ht).exists_norm_le
  refine ⟨max C 0,le_max_right _ _,fun n => ?_⟩
  exact (hC _ (mem_range_self n)).trans (le_max_left _ _)

/-- The original outer Gauss coefficients grow by at most the exact real
frequency power n^(Re(w)-1). No nonresonance condition on w is needed. -/
theorem outerCoefficient_growth {w chi : ℂ} (h : Chamber w chi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 0 < n → ‖outerCoefficient w chi n‖ ≤ C*(n:ℝ)^(w.re-1) := by
  obtain ⟨M,hM,hbound⟩ := weighted_coefficients_bounded h
  refine ⟨max M ‖outerCoefficient w chi 1‖,hM.trans (le_max_left _ _),?_⟩
  intro n hn
  rcases n with _ | n
  · exact False.elim (Nat.not_lt_zero _ hn)
  by_cases hn0 : n=0
  · simp only [hn0,zero_add,Nat.cast_one,Real.one_rpow,mul_one]
    exact le_max_right _ _
  have hnpos : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hnp : (0:ℝ) < (n:ℝ)+1 := by positivity
  have hp : 0 < (n:ℝ)^w.re := Real.rpow_pos_of_pos hnpos _
  have hw := hbound n
  have hns : ‖(n:ℂ)+1‖=(n:ℝ)+1 := by
    rw [← Nat.cast_one,← Nat.cast_add,norm_natCast]
    push_cast
    rfl
  rw [norm_mul,norm_mul,hns,← Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos hnpos,
    Complex.neg_re,Real.rpow_neg hnpos.le] at hw
  have hquot : ((n:ℝ)+1)*‖outerCoefficient w chi (n+1)‖/(n:ℝ)^w.re ≤ M := by
    simpa only [div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hw
  have hmul := (div_le_iff₀ hp).mp hquot
  have hmono : M*(n:ℝ)^w.re ≤ M*((n:ℝ)+1)^w.re :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hnpos.le (by linarith) (chamber_re_pos h).le) hM
  have hc : ‖outerCoefficient w chi (n+1)‖ ≤ M*((n:ℝ)+1)^(w.re-1) := by
    rw [Real.rpow_sub_one (ne_of_gt hnp),← mul_div_assoc,le_div_iff₀ hnp]
    simpa only [mul_comm] using hmul.trans hmono
  push_cast
  exact hc.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hnp.le _))

end
end RHTower.D4BMLaplaceRadial
