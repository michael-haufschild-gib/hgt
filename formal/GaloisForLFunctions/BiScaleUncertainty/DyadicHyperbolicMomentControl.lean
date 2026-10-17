import GaloisForLFunctions.BiScaleUncertainty.DyadicMultiplierFrameBound
import GaloisForLFunctions.BiScaleUncertainty.ProducerConsumerDualityAndNymanBeurlingBridge

/-!
# Coherent dyadic packets control the odd hyperbolic moment

Long actual translation packets turn the multiplier frame estimate into a bound
on its integral. Finite packets retain every source error. Full source logarithmic
blindness removes the support radius from the resulting odd-moment penalty.
-/

open MeasureTheory Set
open scoped BigOperators CompactlySupported

namespace GaloisForLFunctions.BiScaleUncertainty.DyadicHyperbolicMoment
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open CenteredHyperbolicGram ArithmeticMultiplierCollisions DyadicMultiplierFrame
noncomputable section

def chainPacket (g : C_c(ℝ, ℝ)) (N : ℕ) (u : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (N + 1), g (u + (i : ℝ) * Real.log 2)

/-- Length of an interval containing the actual coherent packet support. -/
def chainSpan (g : C_c(ℝ, ℝ)) (N : ℕ) : ℝ :=
  2 * (multiplierSourceRadius g + 1) + (N : ℝ) * Real.log 2

theorem chainSpan_pos (g : C_c(ℝ, ℝ)) (N : ℕ) : 0 < chainSpan g N := by
  have hB := multiplierSourceRadius_pos g
  have hd := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  unfold chainSpan
  positivity

theorem continuous_chainPacket (g : C_c(ℝ, ℝ)) (N : ℕ) : Continuous (chainPacket g N) :=
  continuous_finsetSum _ fun i _ => g.continuous.comp (continuous_add_const ((i : ℝ) * Real.log 2))

theorem chainPacket_support (g : C_c(ℝ, ℝ)) (N : ℕ) :
    Function.support (chainPacket g N) ⊆
      Ioc (-(multiplierSourceRadius g + 1) - (N : ℝ) * Real.log 2)
        (multiplierSourceRadius g + 1) := by
  intro u hu
  have hne := Function.mem_support.mp hu
  by_contra hout
  apply hne
  unfold chainPacket
  apply Finset.sum_eq_zero
  intro i hi
  by_contra hgi
  have hb := abs_le.mp (abs_le_multiplierSourceRadius g _ hgi)
  have hiN : (i : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (show i ≤ N by have := Finset.mem_range.mp hi; omega)
  have hd : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hilo : 0 ≤ (i : ℝ) * Real.log 2 := mul_nonneg (Nat.cast_nonneg i) hd
  have hihi := mul_le_mul_of_nonneg_right hiN hd
  apply hout
  constructor <;> linarith

/-- Coherent translation adds the source integral without any correlation assumption. -/
theorem integral_chainPacket (g : C_c(ℝ, ℝ)) (N : ℕ) :
    (∫ u, chainPacket g N u) = ((N : ℝ) + 1) * ∫ u, g u := by
  have hi (i : ℕ) : Integrable (fun u => g (u + (i : ℝ) * Real.log 2)) :=
    (g.continuous.comp (continuous_add_const _)).integrable_of_hasCompactSupport
      (hasCompactSupport_comp_add g.hasCompactSupport _)
  unfold chainPacket
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [integral_add_right_eq_self]
  simp

theorem chainPacket_energy (g : C_c(ℝ, ℝ)) (N : ℕ) :
    (∫ u, chainPacket g N u ^ 2) =
      translationGramEnergy g (Finset.range (N + 1)) (fun _ => 1) (chainNode (Real.log 2)) := by
  rw [translationGramEnergy_eq_integral]
  simp only [one_mul, chainPacket, chainNode]

/-- Actual packet support and energy bound the square of its coherent mass. -/
theorem integral_sq_le_chain_gram (g : C_c(ℝ, ℝ)) (N : ℕ) :
    ((N : ℝ) + 1) ^ 2 * (∫ u, g u) ^ 2 ≤
      chainSpan g N * translationGramEnergy g (Finset.range (N + 1))
        (fun _ => 1) (chainNode (Real.log 2)) := by
  let B := multiplierSourceRadius g + 1
  have hB : 0 < B := by dsimp [B]; linarith [multiplierSourceRadius_pos g]
  have hd : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hab : -B - (N : ℝ) * Real.log 2 ≤ B := by
    nlinarith [mul_nonneg (Nat.cast_nonneg N) hd]
  have hs : Function.support (chainPacket g N) ⊆ Ioc (-B - (N : ℝ) * Real.log 2) B :=
    chainPacket_support g N
  have hs2 : Function.support (fun u => chainPacket g N u ^ 2) ⊆
      Ioc (-B - (N : ℝ) * Real.log 2) B := by
    intro u hu
    apply hs
    apply Function.mem_support.mpr
    intro hz
    exact (Function.mem_support.mp hu) (by rw [hz]; norm_num)
  have h := intervalIntegral_cauchy_schwarz_sq_le (F := chainPacket g N) (G := fun _ => 1)
    hab (continuous_chainPacket g N).continuousOn continuous_const.continuousOn
  simp only [mul_one, one_pow] at h
  rw [intervalIntegral.integral_eq_integral_of_support_subset hs,
    intervalIntegral.integral_eq_integral_of_support_subset hs2,
    intervalIntegral.integral_const, integral_chainPacket, chainPacket_energy] at h
  simp only [smul_eq_mul, mul_one] at h
  dsimp [B] at h
  unfold chainSpan
  nlinarith only [h]

theorem integral_sinhCompact_eq_moment (f : C_c(ℝ, ℝ)) :
    (∫ u, sinhCompact (1 / 2) f u) = ∫ u, f u * Real.sinh (u / 2) := by
  apply integral_congr_ae
  filter_upwards [] with u
  change Real.sinh ((1 / 2 : ℝ) * u) * f u = f u * Real.sinh (u / 2)
  rw [show (1 / 2 : ℝ) * u = u / 2 by ring, mul_comm]

/-- Explicit finite-chain substitute for the negative odd hyperbolic moment. -/
def momentBudget (f : C_c(ℝ, ℝ)) (N : ℕ) : ℝ :=
  chainSpan (sinhCompact (1 / 2) f) N * max (frameGramUpper f N (fun _ => 1)) 0 /
    ((N : ℝ) + 1) ^ 2

theorem momentBudget_nonneg (f : C_c(ℝ, ℝ)) (N : ℕ) : 0 ≤ momentBudget f N :=
  div_nonneg (mul_nonneg (chainSpan_pos _ _).le (le_max_right _ _)) (sq_nonneg _)

/-- The actual odd moment is controlled without source-zero or analytic assumptions. -/
theorem odd_moment_sq_le_budget (f : C_c(ℝ, ℝ)) (N : ℕ) :
    (∫ u, oddCompactSource f u * Real.sinh (u / 2)) ^ 2 ≤ momentBudget (oddCompactSource f) N := by
  have h := integral_sq_le_chain_gram (sinhCompact (1 / 2) (oddCompactSource f)) N
  rw [integral_sinhCompact_eq_moment] at h
  have hu := mul_le_mul_of_nonneg_left
    ((odd_sinhGram_le_frameGramUpper f N (fun _ => 1)).trans (le_max_left _ 0))
    (chainSpan_pos (sinhCompact (1 / 2) (oddCompactSource f)) N).le
  unfold momentBudget
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < ((N : ℝ) + 1) ^ 2)).mpr
  nlinarith only [h, hu]

/-- Full plastic receiver with the independent odd moment replaced by measured source data. -/
theorem odd_plasticCrossover_ge_momentBudget (f : C_c(ℝ, ℝ)) (N K : ℕ) :
    (∫ y in (0 : ℝ)..Real.log 2, frameJumpBound (oddCompactSource f) K (fun _ => 1) (-y)) +
      plasticRemainderEnergy (oddCompactSource f) - 2 * momentBudget (oddCompactSource f) N ≤
        plasticCrossover (oddCompactSource f) := by
  have hm := odd_moment_sq_le_budget f N
  have hp := odd_plasticCrossover_ge_frame f K
  linarith

private theorem integral_sq_le_of_uniform_gram (g : C_c(ℝ, ℝ)) (C : ℝ)
    (hframe : ∀ N : ℕ, translationGramEnergy g (Finset.range (N + 1))
      (fun _ => 1) (chainNode (Real.log 2)) ≤ C * ((N : ℝ) + 1)) :
    (∫ u, g u) ^ 2 ≤ Real.log 2 * C := by
  by_contra hnot
  have heps : 0 < (∫ u, g u) ^ 2 - Real.log 2 * C := by linarith
  obtain ⟨N, hN⟩ := exists_nat_gt
    ((2 * (multiplierSourceRadius g + 1) * C - (∫ u, g u) ^ 2) /
      ((∫ u, g u) ^ 2 - Real.log 2 * C))
  have hlarge := (div_lt_iff₀ heps).mp hN
  have hh := (integral_sq_le_chain_gram g N).trans
    (mul_le_mul_of_nonneg_left (hframe N) (chainSpan_pos g N).le)
  have hcount : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hlin : ((N : ℝ) + 1) * (∫ u, g u) ^ 2 ≤ chainSpan g N * C :=
    le_of_mul_le_mul_right (by nlinarith only [hh]) hcount
  unfold chainSpan at hlin
  nlinarith only [hlin, hlarge]

/-- Full logarithmic source blindness removes the support radius from the odd-moment cost. -/
theorem odd_logGrid_moment_sq_le_frame (f : C_c(ℝ, ℝ))
    (hz : ∀ n : ℕ, 2 ≤ n → autocorr (oddCompactSource f) (Real.log (n : ℝ)) = 0) :
    (∫ u, oddCompactSource f u * Real.sinh (u / 2)) ^ 2 ≤
      Real.log 2 * (autocorr (sinhCompact (1 / 2) (oddCompactSource f)) 0 +
        frameRadius (oddCompactSource f)) := by
  rw [← integral_sinhCompact_eq_moment]
  apply integral_sq_le_of_uniform_gram
  intro N
  have hd := (le_abs_self _).trans (odd_logGrid_defect_abs_le_frame f N (fun _ => 1) hz)
  have hw : weightEnergy N (fun _ => 1) = (N : ℝ) + 1 := by simp [weightEnergy]
  rw [hw] at hd
  rw [sinhGram_eq_diagonal_add_defect]
  simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    Nat.cast_add, Nat.cast_one]
  nlinarith only [hd]

/-- Actual logarithmic-grid plastic receiver with no separate hyperbolic moment term. -/
theorem odd_logGrid_plasticCrossover_ge_frame (f : C_c(ℝ, ℝ)) (K : ℕ)
    (hz : ∀ n : ℕ, 2 ≤ n → autocorr (oddCompactSource f) (Real.log (n : ℝ)) = 0) :
    (∫ y in (0 : ℝ)..Real.log 2, frameJumpBound (oddCompactSource f) K (fun _ => 1) (-y)) +
      plasticRemainderEnergy (oddCompactSource f) -
        2 * Real.log 2 * (autocorr (sinhCompact (1 / 2) (oddCompactSource f)) 0 +
          frameRadius (oddCompactSource f)) ≤ plasticCrossover (oddCompactSource f) := by
  have hm := odd_logGrid_moment_sq_le_frame f hz
  have hp := odd_plasticCrossover_ge_frame f K
  nlinarith only [hm, hp]

end
end GaloisForLFunctions.BiScaleUncertainty.DyadicHyperbolicMoment
