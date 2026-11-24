import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.EarlyHistory.Box
import Mathlib.Analysis.SpecificLimits.Normed

/-! # Probability cost of simultaneous observations through exponential time -/
open Set MeasureTheory ProbabilityTheory Filter Real Topology
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.EarlyHistory
open WeakBonds ShortWindows
noncomputable section

theorem prefix_card_bound (n : ℕ) : Fintype.card (PrefixIndex n) ≤ 12*(n+2) := by
  rw [Fintype.card_congr (pathCoeffEquiv n)]
  simp only [PathLabel,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  omega

/-- Even observing a cheap evolution continuously through time exp N
costs at most 36 N² in negative log disorder probability. -/
theorem gaussian_history_mass_rate : ∀ᶠ k : ℕ in atTop,
    let N := k+3
    ∀ (A : Set ℝ) (s : ℝ → ℕ), (∀ t ∈ A, |t|≤exp N) →
      exp (-36*(N:ℝ)^2) ≤ pathPauliDisorderLaw.real (prefixPoint k ⁻¹' affordableHistory (k+1) A s) := by
  have hbase : 1 < exp 1 := one_lt_exp_iff.mpr one_pos
  have hr := ((tendsto_pow_const_div_const_pow_of_one_lt 1 hbase).comp
    (tendsto_add_atTop_nat 3)).eventually_lt_const (by norm_num : (0:ℝ)<1/120)
  have hg := ((tendsto_pow_const_div_const_pow_of_one_lt 0 hbase).comp
    (tendsto_add_atTop_nat 3)).eventually_lt_const
      (mul_pos (by norm_num : (0:ℝ)<2) gaussianDensityFloor_pos)
  filter_upwards [hr,hg] with k hr hg
  intro N A s hA
  let m := Fintype.card (PrefixIndex (k+1))
  have hm : (m:ℝ) ≤ 12*(N:ℝ) := by exact_mod_cast prefix_card_bound (k+1)
  have hN : 0≤(N:ℝ) := Nat.cast_nonneg _
  have hex : (exp 1)^N=exp N := by rw [←exp_nat_mul,mul_one]
  change (N:ℝ)^1/(exp 1)^N < 1/120 at hr
  change (N:ℝ)^0/(exp 1)^N < 2*gaussianDensityFloor at hg
  rw [pow_one,hex] at hr
  rw [pow_zero,hex,one_div,←exp_neg] at hg
  let δ := exp (-2*(N:ℝ))
  have hδ : δ≤1 := exp_le_one_iff.mpr (by linarith only [hN])
  have hfit : (m:ℝ)*δ*exp N ≤ 1/10 := calc
    _ = (m:ℝ)/exp N := by
      rw [mul_assoc,←exp_add,show -2*(N:ℝ)+N= -N by ring,exp_neg,div_eq_mul_inv]
    _ ≤ (12*(N:ℝ))/exp N := div_le_div_of_nonneg_right hm (exp_pos _).le
    _ ≤ _ := by linarith only [show (12*(N:ℝ))/exp N=12*((N:ℝ)/exp N) by ring,hr]
  apply le_trans ?_ (gaussian_history_mass k A s hA (exp_pos _).le hδ hfit)
  have hl : exp (-3*(N:ℝ)) ≤ 2*gaussianDensityFloor*δ := by
    rw [show -3*(N:ℝ) = -N+(-2*(N:ℝ)) by ring,exp_add]
    exact mul_le_mul_of_nonneg_right hg.le (exp_pos _).le
  apply le_trans ?_ (pow_le_pow_left₀ (exp_pos _).le hl m)
  rw [←exp_nat_mul]
  apply exp_le_exp.mpr
  nlinarith only [mul_le_mul_of_nonneg_right hm hN]

#print axioms gaussian_history_mass_rate
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.EarlyHistory
