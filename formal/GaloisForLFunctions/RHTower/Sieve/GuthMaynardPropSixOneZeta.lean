import GaloisForLFunctions.RHTower.Sieve.GuthMaynardPropSixOneConstants
import GaloisForLFunctions.RHTower.Sieve.GuthMaynardPropSixOneFourTerm
import GaloisForLFunctions.RHTower.Sieve.GuthMaynardSTwoReductionSingleBlock
import GaloisForLFunctions.RHTower.Sieve.HeathBrownPairSumPower
import GaloisForLFunctions.RHTower.Sieve.LogPolyBlockBridge

/-!
# Guth–Maynard, Proposition 6.1 for `ζ`

Chaining the corpus pieces: (6.1) in single-block form (`gmS2_le_sixOne_single`), (6.2) by the
`k`-th power lift with the divisor bound (`hbPairSum_le_power_lift`), Heath-Brown at every block
length over a dyadic cover of the lifted range `(A^k, B^k]`
(`hbPairSum_Ioc_two_pow_le_majorant`), and the four-term assembly (`prop61_abstract4_absorbed`).

**Which Heath-Brown range the lifted length occupies.**  The block of (6.1) has length
`M₀ = 2^j ≤ M ≤ (2T)^{1+ε}/N + 1`, so the lifted blocks have lengths between `1` and
`4^k M₀^k ≤ (8 (2T)^{1+ε}/N)^k` (`liftedLength_le`).  In the Proposition 3.1 regime `T = N^{6/5}`
this is `T^{k/6 + O(ε)}`, so against the short threshold `(2T)^{1/3}` and the long threshold
`(2T)^{2/3}` the top block is short exactly for `k ≤ 2`, middle for `k = 3` and long for `k ≥ 4`
(`liftedLength_exponent_trichotomy`); the smaller blocks always run down to length `1`, so the
chain needs Heath-Brown at *every* length and uses the corpus all-lengths bound.

**The cost of the all-lengths bound.**  That bound carries a fourth term `|W|^{3/2}M²` beyond
Heath-Brown's three, which turns the second exponent of (6.4) from `2 − 1/k` into `2 − 1/(2k)`.
This is harmless for Proposition 3.1: `prop61_fourTerm_harmless` checks that at `k = 2` both `S₂`
exponents stay below the Proposition 3.1 target `(18 − 20σ)/5` for `σ ∈ [7/10, 8/10]`, which is
what the paper's `k = 4` achieves with the exact three-term bound.
-/

set_option autoImplicit false

namespace RHTower.GuthMaynard

open RHTower.Sieve Finset

noncomputable section

/-! ### Which Heath-Brown range the lifted length occupies -/

/-- **The lifted lengths.**  Every dyadic block of the lifted range has length at most
`4^k M^k`, hence at most `(8 (2T)^{1+ε}/N)^k` when `M ≤ (2T)^{1+ε}/N + 1` and `N ≤ (2T)^{1+ε}`. -/
theorem liftedLength_le {T N : ℝ} {ε : ℝ} {M k : ℕ} (hN : 0 < N)
    (hNle : N ≤ (2 * T) ^ (1 + ε)) (hM : (M : ℝ) ≤ (2 * T) ^ (1 + ε) / N + 1) :
    (4 : ℝ) ^ k * (M : ℝ) ^ k ≤ (8 * (2 * T) ^ (1 + ε) / N) ^ k := by
  have h1 : (1 : ℝ) ≤ (2 * T) ^ (1 + ε) / N := (one_le_div hN).mpr hNle
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
  have hstep : (4 : ℝ) * (M : ℝ) ≤ 8 * (2 * T) ^ (1 + ε) / N := by
    have : (M : ℝ) ≤ 2 * ((2 * T) ^ (1 + ε) / N) := by linarith
    calc (4 : ℝ) * (M : ℝ) ≤ 4 * (2 * ((2 * T) ^ (1 + ε) / N)) := by linarith
      _ = 8 * (2 * T) ^ (1 + ε) / N := by ring
  calc (4 : ℝ) ^ k * (M : ℝ) ^ k = (4 * (M : ℝ)) ^ k := by rw [mul_pow]
    _ ≤ (8 * (2 * T) ^ (1 + ε) / N) ^ k := pow_le_pow_left₀ (by positivity) hstep k

/-- **The trichotomy of ranges in the Proposition 3.1 regime `T = N^{6/5}`.**  There the lifted
top length is `T^{k/6+O(ε)}`: short (`≤ T^{1/3}`) exactly for `k ≤ 2`, long (`≥ T^{2/3}`) exactly
for `k ≥ 4`, and in the middle range exactly for `k = 3`. -/
theorem liftedLength_exponent_trichotomy (k : ℕ) :
    ((k : ℝ) / 6 ≤ 1 / 3 ↔ k ≤ 2) ∧ (2 / 3 ≤ (k : ℝ) / 6 ↔ 4 ≤ k) := by
  constructor
  · constructor
    · intro h
      by_contra hc
      have : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 3 ≤ k)
      linarith
    · intro h
      have : (k : ℝ) ≤ 2 := by exact_mod_cast h
      linarith
  · constructor
    · intro h
      by_contra hc
      have : (k : ℝ) ≤ 3 := by exact_mod_cast (by omega : k ≤ 3)
      linarith
    · intro h
      have : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast h
      linarith

/-- **The fourth Heath-Brown term is harmless for Proposition 3.1.**  At `T = N^{6/5}` the `S₂`
terms `T N |W|^{2−1/(2k)}` and `N² |W|^{2−3/(4k)} T^{1/(2k)}` of `prop61_abstract4_absorbed`
produce, after the Proposition 3.1 root operation, the `N`-exponents `(104 − 120σ)/25` and
`(212 − 240σ)/55` at `k = 2`; both are at most the Proposition 3.1 target `(18 − 20σ)/5`
throughout `σ ∈ [7/10, 8/10]`, with equality at `σ = 7/10`. -/
theorem prop61_fourTerm_harmless {σ : ℝ} (hσ : 7 / 10 ≤ σ) :
    (104 - 120 * σ) / 25 ≤ (18 - 20 * σ) / 5 ∧
      (212 - 240 * σ) / 55 ≤ (18 - 20 * σ) / 5 := by
  constructor <;> rw [div_le_div_iff₀ (by norm_num) (by norm_num)] <;> linarith

/-! ### The lifted (6.3) for one dyadic block -/

/-- The dyadic block `[2^j, 2^{j+1})` of `[1, M]` sits inside `(2^j − 1, 2^{j+1} − 1]`. -/
theorem dyadicSegmentBlock_subset_Ioc (M j : ℕ) :
    dyadicSegmentBlock M j ⊆ Finset.Ioc (2 ^ j - 1) (2 * 2 ^ j - 1) := by
  intro n hn
  have h := dyadicSegmentBlock_subset_Ico M j hn
  rw [Finset.mem_Ico] at h
  have h2 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  rw [Finset.mem_Ioc]
  omega

end

end RHTower.GuthMaynard
