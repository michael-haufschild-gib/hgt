import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.RankDefectsAtTheUnitaryMidpoint
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Realizing the small-unitary-divisor chambers on prescribed primes

The subset test is a linear half-space in logarithms of the full prime
powers. Rounding each target logarithm to a positive integer multiple of
log p has error at most log p. Consequently every strict collection of
subset comparisons occurs cofinally on any prescribed nonempty prime
support. Near the equal-weight direction at odd rank this attains the
central binomial bound.
-/

open Finset Filter Topology
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

noncomputable section

/-- Small side of a weighted subset cut. -/
def logChamber (P : Finset ℕ) (w : ℕ → ℝ) : Finset (Finset ℕ) :=
  P.powerset.filter fun S => ∑ p ∈ S, w p < ∑ p ∈ P \ S, w p

private def exponent (w : ℕ → ℝ) (N p : ℕ) : ℕ :=
  ⌊((N:ℝ)+1)*w p / Real.log p⌋₊+1

private def valuations (P : Finset ℕ) (w : ℕ → ℝ) (N : ℕ) : ℕ →₀ ℕ where
  support := P
  toFun p := if p ∈ P then exponent w N p else 0
  mem_support_toFun p := by by_cases h : p ∈ P <;> simp [h,exponent]

private def sample (P : Finset ℕ) (w : ℕ → ℝ) (N : ℕ) := (valuations P w N).prod (· ^ ·)

private theorem sample_factorization {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p)
    (w : ℕ → ℝ) (N : ℕ) : (sample P w N).factorization = valuations P w N :=
  Nat.prod_pow_factorization_eq_self hP

private theorem sample_support {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p)
    (w : ℕ → ℝ) (N : ℕ) : (sample P w N).primeFactors = P :=
  congrArg Finsupp.support (sample_factorization hP w N)

private def logReading (P : Finset ℕ) (w : ℕ → ℝ) (S : Finset ℕ) (N : ℕ) : ℝ :=
  Real.log (primePowerSubset (sample P w N) S) / ((N:ℝ)+1)

private theorem block_limit (w : ℕ → ℝ) {p : ℕ} (hp : p.Prime) (hw : 0 ≤ w p) :
    Tendsto (fun N : ℕ => (exponent w N p : ℝ)*Real.log p / ((N:ℝ)+1)) atTop (𝓝 (w p)) := by
  have hp' := Real.log_pos (by exact_mod_cast hp.one_lt : (1:ℝ) < p)
  have ht : Tendsto (fun N : ℕ => w p + Real.log p * (1/((N:ℝ)+1))) atTop (𝓝 (w p)) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (Real.log p) |>.const_add (w p)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
  · intro N
    have hN : 0 < (N:ℝ)+1 := by positivity
    unfold exponent
    push_cast
    rw [le_div_iff₀ hN]
    have h := (div_lt_iff₀ hp').mp (Nat.lt_floor_add_one (((N:ℝ)+1)*w p / Real.log p))
    linarith only [h]
  · intro N
    have hN : 0 < (N:ℝ)+1 := by positivity
    have hf := (le_div_iff₀ hp').mp (Nat.floor_le
      (div_nonneg (mul_nonneg hN.le hw) hp'.le))
    unfold exponent
    push_cast
    rw [div_le_iff₀ hN]
    have e : (w p + Real.log p * (1/((N:ℝ)+1))) * ((N:ℝ)+1) = ((N:ℝ)+1) * w p + Real.log p := by
      rw [add_mul, mul_assoc, one_div, inv_mul_cancel₀ hN.ne']
      ring
    rw [e]
    linarith only [hf]

private theorem reading_limit {P S : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p)
    (w : ℕ → ℝ) (hw : ∀ p ∈ P, 0 ≤ w p) (hS : S ⊆ P) :
    Tendsto (logReading P w S) atTop (𝓝 (∑ p ∈ S, w p)) := by
  have ht := tendsto_finsetSum S (fun p hp => block_limit w (hP p (hS hp)) (hw p (hS hp)))
  apply ht.congr (fun N => ?_)
  rw [logReading,primePowerSubset, Nat.cast_prod, Real.log_prod, sum_div]
  · apply sum_congr rfl
    intro p hp
    rw [Nat.cast_pow, Real.log_pow, sample_factorization hP]
    change _ = (if p ∈ P then exponent w N p else 0 : ℕ) * Real.log p / _
    rw [if_pos (hS hp)]
  · intro p hp
    exact_mod_cast pow_ne_zero _ (hP p (hS hp)).ne_zero

private theorem reading_le_iff {P S T : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p)
    (w : ℕ → ℝ) (N : ℕ) (hs : S ⊆ P) (ht : T ⊆ P) :
    logReading P w S N ≤ logReading P w T N ↔
      primePowerSubset (sample P w N) S ≤ primePowerSubset (sample P w N) T := by
  have hpos {U : Finset ℕ} (hU : U ⊆ P) : 0 < primePowerSubset (sample P w N) U :=
    prod_pos fun p hp => pow_pos (hP p (hU hp)).pos _
  rw [logReading,logReading, div_le_div_iff_of_pos_right (by positivity),
    Real.log_le_log_iff (by exact_mod_cast hpos hs) (by exact_mod_cast hpos ht)]
  exact Nat.cast_le

private theorem samples_realize {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p)
    (w : ℕ → ℝ) (hw : ∀ p ∈ P, 0 ≤ w p)
    (ht : ∀ S ⊆ P, ∑ p ∈ S, w p ≠ ∑ p ∈ P \ S, w p) :
    ∀ᶠ N : ℕ in atTop, smallUnitarySubsets (sample P w N) = logChamber P w := by
  have hcmp : ∀ᶠ N : ℕ in atTop, ∀ S ∈ P.powerset,
      (logReading P w S N ≤ logReading P w (P \ S) N ↔ ∑ p ∈ S, w p < ∑ p ∈ P \ S, w p) := by
    rw [eventually_all_finset]
    intro S hS
    have hs := mem_powerset.mp hS
    have h₁ := reading_limit hP w hw hs
    have h₂ := reading_limit hP w hw (sdiff_subset : P \ S ⊆ P)
    rcases lt_or_gt_of_ne (ht S hs) with h | h
    · filter_upwards [h₁.eventually_lt h₂ h] with N hn using iff_of_true hn.le h
    · filter_upwards [h₂.eventually_lt h₁ h] with N hn using iff_of_false hn.not_ge h.not_gt
  filter_upwards [hcmp] with N hn
  ext S
  simp only [smallUnitarySubsets, logChamber, sample_support hP, mem_filter]
  apply and_congr_right
  intro hS
  exact ((reading_le_iff hP w N (mem_powerset.mp hS) sdiff_subset).symm).trans (hn S hS)

/-- Taking a positive power preserves all unitary midpoint decisions, including at the empty support. -/
theorem smallUnitarySubsets_pow (k n : ℕ) :
    smallUnitarySubsets (k^(n+1)) = smallUnitarySubsets k := by
  have hpow (S : Finset ℕ) : primePowerSubset (k^(n+1)) S = (primePowerSubset k S)^(n+1) := by
    unfold primePowerSubset
    rw [← Finset.prod_pow]
    apply prod_congr rfl
    intro p _
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, ← pow_mul, Nat.mul_comm]
  ext S
  simp only [smallUnitarySubsets, Nat.primeFactors_pow k (Nat.succ_ne_zero n), mem_filter,
    hpow, Nat.pow_le_pow_iff_left (Nat.succ_ne_zero n)]

/-- Every strict logarithmic chamber occurs at arbitrarily large integers on the prescribed support. -/
theorem unitary_chamber_cofinal {P : Finset ℕ} (hn : P.Nonempty) (hP : ∀ p ∈ P, Nat.Prime p)
    (w : ℕ → ℝ) (hw : ∀ p ∈ P, 0 ≤ w p)
    (ht : ∀ S ⊆ P, ∑ p ∈ S, w p ≠ ∑ p ∈ P \ S, w p) :
    ∀ B : ℕ, ∃ k > B, k.primeFactors = P ∧ smallUnitarySubsets k = logChamber P w := by
  obtain ⟨N,hN⟩ := (samples_realize hP w hw ht).exists
  let k := sample P w N
  have hs : k.primeFactors = P := sample_support hP w N
  have hk : 1 < k := Nat.nonempty_primeFactors.mp (hs ▸ hn)
  intro B
  exact ⟨k^(B+1),Nat.lt_trans (Nat.lt_succ_self B) (Nat.lt_pow_self hk),
    (Nat.primeFactors_pow k (Nat.succ_ne_zero B)).trans hs,(smallUnitarySubsets_pow k B).trans hN⟩

/-- On every prescribed odd prime support, infinitely far out the actual coefficient
attains the signed central binomial value. -/
theorem unitary_central_bound_attained {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p)
    (r : ℕ) (hr : P.card = 2*r+1) (B : ℕ) :
    ∃ k > B, k.primeFactors = P ∧ unitaryHalfWeight k = (-1 : ℤ)^r*(2*r).choose r := by
  have hn := card_pos.mp (by omega : 0 < P.card)
  have ht (S : Finset ℕ) (hS : S ⊆ P) :
      (∑ _p ∈ S, (1:ℝ)) ≠ ∑ _p ∈ P \ S, (1:ℝ) := by
    simp only [sum_const, nsmul_eq_mul, mul_one, card_sdiff_of_subset hS, ne_eq, Nat.cast_inj]
    have := card_le_card hS
    omega
  obtain ⟨k,hk,hs,hc⟩ := unitary_chamber_cofinal hn hP (fun _ => 1) (fun _ _ => zero_le_one) ht B
  refine ⟨k,hk,hs,?_⟩
  have hD : unitaryRankDefects k r = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro S hS
    obtain ⟨hl,hn⟩ := mem_filter.mp hS
    obtain ⟨hS, hcard⟩ := mem_filter.mp hl
    have hsub : S ⊆ P := hs ▸ mem_powerset.mp hS
    apply hn
    rw [hc]
    apply mem_filter.mpr ⟨mem_powerset.mpr hsub, ?_⟩
    simp only [sum_const, nsmul_eq_mul, mul_one, card_sdiff_of_subset hsub, Nat.cast_lt]
    omega
  have hf := unitaryHalfWeight_rank_formula k
  dsimp only at hf
  rw [hs,hr,if_neg (by omega),if_neg (by simp),show (2*r+1)/2 = r by omega,hD] at hf
  simpa using hf


end

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
