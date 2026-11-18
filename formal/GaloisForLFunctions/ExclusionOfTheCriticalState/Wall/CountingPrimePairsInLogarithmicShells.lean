import GaloisForLFunctions.RHTower.Sieve.PrimePairAverageSharp
import GaloisForLFunctions.RHTower.Sieve.SieveRemainderBound
import GaloisForLFunctions.RHTower.MobiusWholeAnchorGlobalTerminalCapacity

/-!
# Shifted ordinary-prime pairs in logarithmic shells

The two-dimensional Selberg sieve saves both logarithms in the shell count,
uniformly in the number of shifts. A fixed power of the shell endpoint
suffices as the sifting level.
-/

noncomputable section
open Finset Filter
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open _root_.RHTower _root_.RHTower.Sieve

/-- Prime pairs with positive additive gap `d` and first prime in the shell. -/
def shellPrimePairs (v : ℝ) (d : ℕ) : Finset ℕ :=
  (Icc 1 ⌊Real.exp v⌋₊).filter fun p => p.Prime ∧ (p+d).Prime ∧ Real.exp (v-1) < p

/-- Both logarithms of the atom weights are absorbed by the prime-pair count. -/
theorem eventually_shellPrimePairs_log_square_le : ∃ A : ℝ, 0 < A ∧ ∀ᶠ v : ℝ in atTop,
    ∀ K : ℕ, v^2 * (∑ d ∈ Icc 1 K, ((shellPrimePairs v d).card : ℝ)) ≤ A*K*Real.exp v := by
  let B := mertensS 2 - meisselMertensConst + (2*mertensFirstConst+1/2)/Real.log 2
  let L := 256 * Real.exp B
  refine ⟨2*Real.exp 1*L^2 + 32*(2:ℝ)^108,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (max 512 (256*(20*mertensFirstConst)) : ℝ)] with v hv
  intro K
  have hv₁ := (le_max_left _ _).trans hv
  have hv₂ := (le_max_right _ _).trans hv
  have hv0 : 0 ≤ v := by linarith only [hv₁]
  let h := ⌈Real.exp (v/256)⌉₊
  let z := (h:ℝ)^36
  have hlo : Real.exp (v/256) ≤ (h:ℝ) := Nat.le_ceil _
  have h1 : 1 ≤ Real.exp (v/256) := Real.one_le_exp (by positivity)
  have hhi : (h:ℝ) ≤ 2*Real.exp (v/256) := by
    have hlt := Nat.ceil_lt_add_one (Real.exp_pos (v/256)).le
    change (⌈Real.exp (v/256)⌉₊:ℝ) ≤ _
    linarith only [hlt,h1]
  have hh2 : 2 ≤ h := by
    have hb := Real.add_one_le_exp (v/256)
    have : (2:ℝ) ≤ h := by linarith only [hb,hlo,hv₁]
    exact_mod_cast this
  have hp : (0:ℝ) < h := by exact_mod_cast Nat.zero_lt_of_lt hh2
  have hlog : v/256 ≤ Real.log h := (Real.le_log_iff_exp_le hp).2 hlo
  have hz : 1 ≤ z := one_le_pow₀ (h1.trans hlo)
  have hlev : (h:ℝ)^(18:ℝ) ≤ Real.sqrt z := by
    rw [show z = ((h:ℝ)^18)^2 by dsimp [z]; ring,Real.sqrt_sq (by positivity)]
    norm_num
  have hcut : (h:ℝ) ≤ Real.exp (v-1) := by
    calc _ ≤ 2*Real.exp (v/256) := hhi
      _ ≤ Real.exp 1*Real.exp (v/256) := mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp 1]) (Real.exp_pos _).le
      _ ≤ _ := by rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith only [hv₁])
  let E := Real.exp (mertensS h-mertensS 2)
  have hE : 0 < E := Real.exp_pos _
  have hL : 0 < L := by dsimp [L]; positivity
  have htE : v ≤ L*E := by
    have hb := logLog_sub_le_mertensS hh2
    change Real.log (Real.log (h:ℝ)) + _ - _ ≤ _ at hb
    have hlogpos : 0 < Real.log (h:ℝ) := by linarith only [hlog,hv₁]
    have he : Real.log (h:ℝ) ≤ Real.exp B * E := by
      rw [← Real.exp_log hlogpos,show Real.exp B*E = Real.exp (B+(mertensS h-mertensS 2)) from (Real.exp_add ..).symm]
      apply Real.exp_le_exp.mpr
      dsimp only [B]; linarith only [hb]
    dsimp only [L]; linarith only [hlog,he]
  have hcount := sum_card_primePair_le_sharp (Real.exp v) (P₁ := 2) le_rfl (h := h) K hz
    (Real.exp_pos _).le hh2 hh2 hlev (by linarith only [hlog,hv₂])
  have hrest : z^3 ≤ (2:ℝ)^108 * Real.exp (v/2) := by
    calc z^3 = (h:ℝ)^108 := by dsimp only [z]; ring
      _ ≤ (2*Real.exp (v/256))^108 := pow_le_pow_left₀ hp.le hhi _
      _ ≤ _ := by
        rw [mul_pow,← Real.exp_nat_mul]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.exp_le_exp.mpr (by norm_num; linarith only [hv0])
  have hc : (∑ d ∈ Icc 1 K, ((shellPrimePairs v d).card:ℝ)) ≤
      (2*Real.exp 1*K*Real.exp v)/E^2 + K*(2*((2:ℝ)^108 * Real.exp (v/2))) := by
    apply le_trans _ (hcount.trans (add_le_add_right
      (mul_le_mul_of_nonneg_left ((sieve_remainder_le (h := h) (P₁ := 2) le_rfl hz).trans
        (mul_le_mul_of_nonneg_left hrest (by norm_num))) (Nat.cast_nonneg K)) _))
    apply sum_le_sum fun d _ => ?_
    exact_mod_cast card_le_card (show shellPrimePairs v d ⊆ _ from fun p hp => by
      obtain ⟨hp',hpr,hpd,he⟩ := mem_filter.1 hp
      exact mem_filter.2 ⟨hp',hpr,hpd,by exact_mod_cast hcut.trans_lt he⟩)
  have hdiv : v^2/E^2 ≤ L^2 := by
    rw [← div_pow]
    exact pow_le_pow_left₀ (div_nonneg hv0 hE.le) ((div_le_iff₀ hE).2 htE) 2
  have hvexp : v^2 ≤ 16*Real.exp (v/2) := by
    have hh : v ≤ 4*Real.exp (v/4) := by linarith [Real.add_one_le_exp (v/4)]
    calc _ ≤ (4*Real.exp (v/4))^2 := pow_le_pow_left₀ hv0 hh 2
      _ = _ := by rw [mul_pow,← Real.exp_nat_mul]; norm_num; ring
  have hhalf : Real.exp (v/2)*Real.exp (v/2) = Real.exp v := by rw [← Real.exp_add]; congr 1; ring
  calc _ ≤ v^2*((2*Real.exp 1*K*Real.exp v)/E^2 + K*(2*(2^108 * Real.exp (v/2)))) :=
           mul_le_mul_of_nonneg_left hc (sq_nonneg _)
    _ = (v^2/E^2)*(2*Real.exp 1*K*Real.exp v) + v^2*(K*(2*(2^108 * Real.exp (v/2)))) := by ring
    _ ≤ L^2*(2*Real.exp 1*K*Real.exp v) + (16*Real.exp (v/2))*(K*(2*(2^108 * Real.exp (v/2)))) :=
           add_le_add (mul_le_mul_of_nonneg_right hdiv (by positivity)) (mul_le_mul_of_nonneg_right hvexp (by positivity))
    _ = _ := by linear_combination (32*K*(2:ℝ)^108)*hhalf

#print axioms eventually_shellPrimePairs_log_square_le

end GaloisForLFunctions.ExclusionOfTheCriticalState
