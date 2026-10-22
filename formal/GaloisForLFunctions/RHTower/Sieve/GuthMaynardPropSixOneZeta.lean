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


/-! ### Small algebraic helpers for the constants -/

theorem rpow_inv_le_max {x : ℝ} (hx : 0 ≤ x) {k : ℕ} (hk : 1 ≤ k) :
    x ^ (1 / (k : ℝ)) ≤ max 1 x := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hp0 : (0 : ℝ) ≤ 1 / (k : ℝ) := by positivity
  have hp1 : 1 / (k : ℝ) ≤ 1 := by rw [div_le_one hkpos]; exact_mod_cast hk
  rcases le_total x 1 with h | h
  · exact (Real.rpow_le_one hx h hp0).trans (le_max_left _ _)
  · refine le_trans ?_ (le_max_right _ _)
    calc x ^ (1 / (k : ℝ)) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h hp1
      _ = x := Real.rpow_one x

theorem pow_rpow_inv_two {x : ℝ} (hx : 0 ≤ x) {k : ℕ} (hk : 1 ≤ k) :
    (x ^ (2 * k)) ^ (1 / (k : ℝ)) = x ^ 2 := by
  have hk0 : (k : ℝ) ≠ 0 := by
    have : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    exact ne_of_gt this
  rw [← Real.rpow_natCast x (2 * k), ← Real.rpow_mul hx]
  have he : ((2 * k : ℕ) : ℝ) * (1 / (k : ℝ)) = ((2 : ℕ) : ℝ) := by
    push_cast; field_simp
  rw [he, Real.rpow_natCast]

/-- `T'^θ ≤ 8 (T^θ Tε)` for `0 ≤ θ ≤ 1` when `T' ≤ 8 (T Tε)` and `1 ≤ Tε`. -/
theorem rpow_le_of_le_mul {T T' Tε θ : ℝ} (hT0 : 0 < T) (hT'0 : 0 < T')
    (hT'le : T' ≤ 8 * (T * Tε)) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hTε1 : 1 ≤ Tε) :
    T' ^ θ ≤ 8 * (T ^ θ * Tε) := by
  have hTε0 : (0 : ℝ) ≤ Tε := by linarith
  have h2 : (8 * (T * Tε)) ^ θ = (8 : ℝ) ^ θ * (T ^ θ * Tε ^ θ) := by
    rw [Real.mul_rpow (by norm_num) (by positivity), Real.mul_rpow hT0.le hTε0]
  have h3 : (8 : ℝ) ^ θ ≤ 8 := by
    calc (8 : ℝ) ^ θ ≤ (8 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hθ1
      _ = 8 := Real.rpow_one 8
  have h4 : Tε ^ θ ≤ Tε := by
    calc Tε ^ θ ≤ Tε ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hTε1 hθ1
      _ = Tε := Real.rpow_one Tε
  have h5 : (0 : ℝ) ≤ T ^ θ := Real.rpow_nonneg hT0.le _
  calc T' ^ θ ≤ (8 * (T * Tε)) ^ θ := Real.rpow_le_rpow hT'0.le hT'le hθ0
    _ = (8 : ℝ) ^ θ * (T ^ θ * Tε ^ θ) := h2
    _ ≤ 8 * (T ^ θ * Tε) :=
        mul_le_mul h3 (mul_le_mul_of_nonneg_left h4 h5) (by positivity) (by norm_num)

/-- Monotonicity of the four-term Heath-Brown majorant in the block length and the scale. -/
theorem majorant_mono {c P Mk M2k TH TH' : ℝ} (hc : 0 ≤ c) (hP : 0 ≤ P)
    (hPM : P ≤ Mk) (hP2 : P ^ 2 ≤ M2k) (hTH : 0 ≤ TH) (hTH' : TH ≤ TH') :
    c ^ 2 * P + c * P ^ 2 + c ^ ((5 : ℝ) / 4) * TH * P + c ^ ((3 : ℝ) / 2) * P ^ 2
      ≤ c ^ 2 * Mk + c * M2k + c ^ ((5 : ℝ) / 4) * TH' * Mk + c ^ ((3 : ℝ) / 2) * M2k := by
  have h54 : (0 : ℝ) ≤ c ^ ((5 : ℝ) / 4) := Real.rpow_nonneg hc _
  have h32 : (0 : ℝ) ≤ c ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hc _
  have hMk : 0 ≤ Mk := le_trans hP hPM
  have hTH0 : 0 ≤ TH' := le_trans hTH hTH'
  gcongr

/-- The Proposition 6.1 bracket at the auxiliary scale `T'` against the bracket at `T`. -/
theorem bracket_mono {N c T T' Tε a b s s' : ℝ} (hN : 0 ≤ N) (_hc : 0 ≤ c) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (_hs : 0 ≤ s) (_hT : 0 ≤ T) (hTε : 1 ≤ 8 * Tε)
    (hT'le : T' ≤ 8 * (T * Tε)) (hs'le : s' ≤ 8 * (s * Tε)) :
    N ^ 2 * c ^ 2 + T' * N * a + N ^ 2 * b * s' ≤
      8 * Tε * (N ^ 2 * c ^ 2 + T * N * a + N ^ 2 * b * s) := by
  have hTε0 : (0 : ℝ) ≤ Tε := by linarith
  have e1 : N ^ 2 * c ^ 2 ≤ 8 * Tε * (N ^ 2 * c ^ 2) := by
    have h0 : (0 : ℝ) ≤ N ^ 2 * c ^ 2 := by positivity
    nlinarith
  have e2 : T' * N * a ≤ 8 * Tε * (T * N * a) := by
    have h0 : (0 : ℝ) ≤ N * a := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hT'le h0]
  have e3 : N ^ 2 * b * s' ≤ 8 * Tε * (N ^ 2 * b * s) := by
    have h0 : (0 : ℝ) ≤ N ^ 2 * b := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hs'le h0]
  linarith

/-- The `k`-th root of the lifted (6.3) constant `Dv^{2k} · 8^{2k} · Cm`. -/
theorem lifted_root_le {Dv Cm Cδ E : ℝ} {k m : ℕ} (hk : 1 ≤ k) (hm : m = 2 * k)
    (hDv0 : 0 ≤ Dv) (hCm0 : 0 ≤ Cm) (hCδ : 0 ≤ Cδ) (hE1 : 1 ≤ E)
    (hDv2 : Dv ^ 2 ≤ Cδ * E) (hCmle : Cm ≤ 2 * Cδ * E) :
    (Dv ^ (2 * k) * ((8 : ℝ) ^ m * Cm)) ^ (1 / (k : ℝ)) ≤
      Cδ * E * (64 * (max 1 (2 * Cδ) * E)) := by
  subst hm
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk1nn : (0 : ℝ) ≤ 1 / (k : ℝ) := div_nonneg zero_le_one (by linarith only [hkR])
  have hexpk : 1 / (k : ℝ) ≤ 1 := by
    rw [div_le_one (by linarith only [hkR])]; linarith only [hkR]
  have hE0 : (0 : ℝ) ≤ E := le_trans zero_le_one hE1
  have hmax0 : (0 : ℝ) ≤ max 1 (2 * Cδ) := le_trans zero_le_one (le_max_left _ _)
  have h8m0 : (0 : ℝ) ≤ (8 : ℝ) ^ (2 * k) := pow_nonneg (by norm_num) _
  rw [Real.mul_rpow (pow_nonneg hDv0 _) (mul_nonneg h8m0 hCm0), Real.mul_rpow h8m0 hCm0]
  have e1 : (Dv ^ (2 * k)) ^ (1 / (k : ℝ)) = Dv ^ 2 := pow_rpow_inv_two hDv0 hk
  have e2 : ((8 : ℝ) ^ (2 * k)) ^ (1 / (k : ℝ)) = 64 := by
    rw [pow_rpow_inv_two (by norm_num : (0 : ℝ) ≤ 8) hk]; norm_num
  rw [e1, e2]
  have hEk : E ^ (1 / (k : ℝ)) ≤ E := by
    calc E ^ (1 / (k : ℝ)) ≤ E ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hE1 hexpk
      _ = E := Real.rpow_one E
  have e3 : Cm ^ (1 / (k : ℝ)) ≤ max 1 (2 * Cδ) * E := by
    have h1 : Cm ^ (1 / (k : ℝ)) ≤ (2 * Cδ * E) ^ (1 / (k : ℝ)) :=
      Real.rpow_le_rpow hCm0 hCmle hk1nn
    have h2 : (2 * Cδ * E) ^ (1 / (k : ℝ)) = (2 * Cδ) ^ (1 / (k : ℝ)) * E ^ (1 / (k : ℝ)) :=
      Real.mul_rpow (by linarith only [hCδ]) hE0
    have h3 : (2 * Cδ) ^ (1 / (k : ℝ)) ≤ max 1 (2 * Cδ) :=
      rpow_inv_le_max (by linarith only [hCδ]) hk
    have h5 : (0 : ℝ) ≤ E ^ (1 / (k : ℝ)) := Real.rpow_nonneg hE0 _
    calc Cm ^ (1 / (k : ℝ)) ≤ (2 * Cδ * E) ^ (1 / (k : ℝ)) := h1
      _ = (2 * Cδ) ^ (1 / (k : ℝ)) * E ^ (1 / (k : ℝ)) := h2
      _ ≤ max 1 (2 * Cδ) * E := mul_le_mul h3 hEk h5 hmax0
  have hc64 : (0 : ℝ) ≤ 64 * Cm ^ (1 / (k : ℝ)) := by
    have := Real.rpow_nonneg hCm0 (1 / (k : ℝ))
    linarith only [this]
  exact mul_le_mul hDv2 (mul_le_mul_of_nonneg_left e3 (by norm_num)) hc64
    (mul_nonneg hCδ hE0)

/-- The final constant collection of Proposition 6.1, over abstract reals. -/
theorem prop61_constant_step {S C₆₁ Cδ E RT BRv Xv P6 P9 : ℝ}
    (hC₆₁ : 0 ≤ C₆₁) (hCδ : 0 ≤ Cδ) (hE : 0 ≤ E) (hP6 : 0 ≤ P6) (hP9 : 0 ≤ P9)
    (hmain : S ≤ 2 * (C₆₁ * P6 * RT) * BRv)
    (hRT : RT ≤ Cδ * E * (64 * (max 1 (2 * Cδ) * E)))
    (hBR : BRv ≤ 8 * E * Xv) (hBR0 : 0 ≤ BRv) (hX0 : 0 ≤ Xv)
    (hprod : P6 * (E * (E * E)) = P9) :
    S ≤ (1024 * C₆₁ * (1 + Cδ) * (1 + 2 * Cδ) + C₆₁) * P9 * Xv := by
  have hmax0 : (0 : ℝ) ≤ max 1 (2 * Cδ) := le_trans zero_le_one (le_max_left _ _)
  have hme : (0 : ℝ) ≤ max 1 (2 * Cδ) * E := mul_nonneg hmax0 hE
  have hRTb : (0 : ℝ) ≤ Cδ * E * (64 * (max 1 (2 * Cδ) * E)) :=
    mul_nonneg (mul_nonneg hCδ hE) (by linarith only [hme])
  have hCP : (0 : ℝ) ≤ C₆₁ * P6 := mul_nonneg hC₆₁ hP6
  have hL : 2 * (C₆₁ * P6 * RT) ≤ 2 * (C₆₁ * P6 * (Cδ * E * (64 * (max 1 (2 * Cδ) * E)))) := by
    have h := mul_le_mul_of_nonneg_left hRT hCP
    linarith only [h]
  have hL0 : (0 : ℝ) ≤ 2 * (C₆₁ * P6 * (Cδ * E * (64 * (max 1 (2 * Cδ) * E)))) := by
    have := mul_nonneg hCP hRTb
    linarith only [this]
  have step : S ≤ 2 * (C₆₁ * P6 * (Cδ * E * (64 * (max 1 (2 * Cδ) * E)))) * (8 * E * Xv) :=
    hmain.trans (mul_le_mul hL hBR hBR0 hL0)
  have eq1 : 2 * (C₆₁ * P6 * (Cδ * E * (64 * (max 1 (2 * Cδ) * E)))) * (8 * E * Xv)
      = 1024 * C₆₁ * Cδ * max 1 (2 * Cδ) * (P6 * (E * (E * E))) * Xv := by ring
  rw [eq1, hprod] at step
  have hconst : 1024 * C₆₁ * Cδ * max 1 (2 * Cδ) ≤
      1024 * C₆₁ * (1 + Cδ) * (1 + 2 * Cδ) + C₆₁ := by
    have hmaxle : max 1 (2 * Cδ) ≤ 1 + 2 * Cδ :=
      max_le (by linarith only [hCδ]) (by linarith only [hCδ])
    have hA : 1024 * C₆₁ * Cδ ≤ 1024 * C₆₁ * (1 + Cδ) := by
      have h := mul_le_mul_of_nonneg_left (by linarith only [] : Cδ ≤ 1 + Cδ)
        (by linarith only [hC₆₁] : (0 : ℝ) ≤ 1024 * C₆₁)
      linarith only [h]
    have hB0 : (0 : ℝ) ≤ 1024 * C₆₁ * (1 + Cδ) :=
      mul_nonneg (by linarith only [hC₆₁]) (by linarith only [hCδ])
    have h := mul_le_mul hA hmaxle hmax0 hB0
    linarith only [h, hC₆₁]
  exact step.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hconst hP9) hX0)

/-! ### Proposition 6.1 for `ζ` -/

/-- **Guth–Maynard, Proposition 6.1 for `ζ`** (unconditional).  For every `ε ∈ (0,1]` and every
`k ≥ 1` there is `C` such that for all `T ≥ 2`, `1 ≤ N ≤ T` and every nonempty `T^ε`-separated
`W ⊆ [0,T]`,

`‖S₂‖ ≤ C T^{9ε} (N²|W|² + T N |W|^{2−1/(2k)} + N² |W|^{2−3/(4k)} T^{1/(2k)})`.

The second exponent is `2 − 1/(2k)` rather than the paper's `2 − 1/k` because the Heath-Brown
bound available at every block length carries the extra term `|W|^{3/2}M²`; `prop61_fourTerm_harmless`
checks that this costs nothing in Proposition 3.1. -/
theorem prop61_zeta (w : CGLRealSmoothBump) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {k : ℕ} (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T N : ℝ) (W : Finset ℝ), 2 ≤ T → 1 ≤ N → N ≤ T →
      IsSeparated (T ^ ε) W → (∀ t ∈ W, 0 ≤ t ∧ t ≤ T) → W.Nonempty →
      ‖gmS2 w N W‖ ≤ C * T ^ (9 * ε) *
        (N ^ 2 * (W.card : ℝ) ^ 2
          + T * N * (W.card : ℝ) ^ (2 - 1 / (2 * (k : ℝ)))
          + N ^ 2 * (W.card : ℝ) ^ (2 - 3 / (4 * (k : ℝ))) * T ^ (1 / (2 * (k : ℝ)))) := by
  classical
  obtain ⟨C₆₁, hC₆₁, h61⟩ := gmS2_le_sixOne_single w hε hε1
  have ha4 : (4 : ℝ) ≤ (32 : ℝ) ^ (4 * k) := by
    have h1 : (32 : ℝ) ^ 1 ≤ (32 : ℝ) ^ (4 * k) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    simp only [pow_one] at h1
    linarith
  have hb23 : (2 : ℝ) / 3 ≤ 4 * (k : ℝ) := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  obtain ⟨δ, hδ, Cδ, hCδ, hblk⟩ :=
    exists_blockConst_divisor_le (ε := ε) (a := (32 : ℝ) ^ (4 * k)) (b := 4 * (k : ℝ)) hε ha4 hb23
  have hbig : (0 : ℝ) ≤ 1024 * C₆₁ * (1 + Cδ) * (1 + 2 * Cδ) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  refine ⟨1024 * C₆₁ * (1 + Cδ) * (1 + 2 * Cδ) + C₆₁, by linarith, ?_⟩
  intro T N W hT hN hNT hsep hmem hWne
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have hT0 : (0 : ℝ) < T := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk0R : (0 : ℝ) < (k : ℝ) := by linarith
  have hcard1 : (1 : ℝ) ≤ (W.card : ℝ) := by
    have : 1 ≤ W.card := Finset.card_pos.mpr hWne
    exact_mod_cast this
  have hTε1 : (1 : ℝ) ≤ T ^ ε := Real.one_le_rpow hT1 hε.le
  have hTε0 : (0 : ℝ) ≤ T ^ ε := Real.rpow_nonneg hT0.le _
  have h8Tε : (1 : ℝ) ≤ 8 * T ^ ε := by linarith only [hTε1]
  have hTe6 : (T ^ ε) ^ 6 = T ^ (6 * ε) := by
    rw [← Real.rpow_natCast (T ^ ε) 6, ← Real.rpow_mul hT0.le,
      show ε * ((6 : ℕ) : ℝ) = 6 * ε from by push_cast; ring]
  have hTsum : T ^ (6 * ε) * (T ^ ε * (T ^ ε * T ^ ε)) = T ^ (9 * ε) := by
    rw [← Real.rpow_add hT0, ← Real.rpow_add hT0, ← Real.rpow_add hT0,
      show 6 * ε + (ε + (ε + ε)) = 9 * ε from by ring]
  have hprod : (T ^ ε) ^ 6 * (T ^ ε * (T ^ ε * T ^ ε)) = T ^ (9 * ε) := by
    rw [hTe6]; exact hTsum
  -- `W` is 1-separated and of diameter at most `T`
  have hW1 : IsSeparated 1 W := fun t ht t' ht' hne => hTε1.trans (hsep t ht t' ht' hne)
  have hdiam : ∀ t ∈ W, ∀ t' ∈ W, |t - t'| ≤ T := by
    intro t ht t' ht'
    obtain ⟨h1, h2⟩ := hmem t ht
    obtain ⟨h3, h4⟩ := hmem t' ht'
    rw [abs_le]; constructor <;> linarith
  -- (6.1) at one dyadic block
  obtain ⟨M, j, hM1, hjM, hMle, hS2⟩ := h61 T N W hT1 hN hsep hmem
  -- the auxiliary scale `T' = 2 (2T)^{1+ε}`
  have h2T : (1 : ℝ) ≤ 2 * T := by linarith
  have hrpow1 : 2 * T ≤ (2 * T) ^ (1 + ε) := by
    have := Real.rpow_le_rpow_of_exponent_le h2T (by linarith : (1 : ℝ) ≤ 1 + ε)
    rwa [Real.rpow_one] at this
  have hNrpow : N ≤ (2 * T) ^ (1 + ε) := by linarith
  obtain ⟨T', hT'def⟩ : ∃ T' : ℝ, T' = 2 * (2 * T) ^ (1 + ε) := ⟨_, rfl⟩
  have hT'0 : (0 : ℝ) < T' := by
    have : (0 : ℝ) < (2 * T) ^ (1 + ε) := Real.rpow_pos_of_pos (by linarith) _
    rw [hT'def]; linarith
  -- `T' ≤ 8 T · T^ε`
  have hT'le : T' ≤ 8 * (T * T ^ ε) := by
    have hsplit : (2 * T) ^ (1 + ε) = 2 ^ (1 + ε) * T ^ (1 + ε) :=
      Real.mul_rpow (by norm_num) hT0.le
    have h2e : (2 : ℝ) ^ (1 + ε) ≤ 4 := by
      have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (by linarith : (1 : ℝ) + ε ≤ 2)
      calc (2 : ℝ) ^ (1 + ε) ≤ 2 ^ (2 : ℝ) := this
        _ = 4 := by rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
    have hTe : T ^ (1 + ε) = T * T ^ ε := by
      rw [Real.rpow_add hT0, Real.rpow_one]
    have hT1e : (0 : ℝ) ≤ T ^ (1 + ε) := Real.rpow_nonneg hT0.le _
    rw [hT'def, hsplit, hTe] at *
    nlinarith [Real.rpow_nonneg hT0.le ε, mul_nonneg hT0.le (Real.rpow_nonneg hT0.le ε)]
  -- the bracket, at `T'` and at `T`
  obtain ⟨X₂, hX₂def⟩ : ∃ X₂ : ℝ, X₂ = N ^ 2 * (W.card : ℝ) ^ 2
      + T * N * (W.card : ℝ) ^ (2 - 1 / (2 * (k : ℝ)))
      + N ^ 2 * (W.card : ℝ) ^ (2 - 3 / (4 * (k : ℝ))) * T ^ (1 / (2 * (k : ℝ))) := ⟨_, rfl⟩
  rw [← hX₂def]
  have hcard0 : (0 : ℝ) ≤ (W.card : ℝ) := Nat.cast_nonneg _
  have hX₂0 : 0 ≤ X₂ := by
    have h1 : (0 : ℝ) ≤ (W.card : ℝ) ^ (2 - 1 / (2 * (k : ℝ))) := Real.rpow_nonneg hcard0 _
    have h2 : (0 : ℝ) ≤ (W.card : ℝ) ^ (2 - 3 / (4 * (k : ℝ))) := Real.rpow_nonneg hcard0 _
    have h3 : (0 : ℝ) ≤ T ^ (1 / (2 * (k : ℝ))) := Real.rpow_nonneg hT0.le _
    rw [hX₂def]; positivity
  have hTpow6 : (T ^ ε) ^ 6 ≤ T ^ (9 * ε) := by
    rw [← Real.rpow_natCast (T ^ ε) 6, ← Real.rpow_mul hT0.le]
    exact Real.rpow_le_rpow_of_exponent_le hT1 (by push_cast; linarith)
  have hT9 : (1 : ℝ) ≤ T ^ (9 * ε) := Real.one_le_rpow hT1 (by linarith)
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · -- the block `{1}`: only the first term of (6.4) is needed
    have hsub : dyadicSegmentBlock M j ⊆ ({1} : Finset ℕ) := by
      intro n hn
      have h := dyadicSegmentBlock_subset_Ico M j hn
      rw [Finset.mem_Ico, hj0] at h
      simp only [pow_zero] at h
      have hn1 : n = 1 := by omega
      simp [hn1]
    have hone : hbPairSum W ({1} : Finset ℕ) (fun _ => ((1 : ℝ) : ℂ)) = (W.card : ℝ) ^ 2 := by
      have hph : ∀ t : ℝ, hbPoly ({1} : Finset ℕ) (fun _ => ((1 : ℝ) : ℂ)) t = 1 := by
        intro t
        simp [hbPoly, hbPhase]
      unfold hbPairSum
      simp only [hph, norm_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one]
      ring
    have hXle : hbPairSum W (dyadicSegmentBlock M j) (fun _ => ((1 : ℝ) : ℂ))
        ≤ (W.card : ℝ) ^ 2 := by
      rw [← hone]
      exact hbPairSum_ofReal_mono_support W hsub (fun n _ => zero_le_one)
    have hXnn : 0 ≤ hbPairSum W (dyadicSegmentBlock M j) (fun _ => ((1 : ℝ) : ℂ)) :=
      hbPairSum_nonneg _ _ _
    have hdiv : N ^ 2 / 2 ^ j = N ^ 2 := by rw [hj0]; norm_num
    rw [hdiv] at hS2
    have hbound : ‖gmS2 w N W‖ ≤ C₆₁ * (T ^ ε) ^ 6 * (N ^ 2 * (W.card : ℝ) ^ 2) := by
      refine hS2.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      exact mul_le_mul_of_nonneg_left hXle (by positivity)
    have hstep : C₆₁ * (T ^ ε) ^ 6 * (N ^ 2 * (W.card : ℝ) ^ 2) ≤
        (1024 * C₆₁ * (1 + Cδ) * (1 + 2 * Cδ) + C₆₁) * T ^ (9 * ε) * X₂ := by
      have h1 : N ^ 2 * (W.card : ℝ) ^ 2 ≤ X₂ := by
        have h1' : (0 : ℝ) ≤ T * N * (W.card : ℝ) ^ (2 - 1 / (2 * (k : ℝ))) := by
          have : (0 : ℝ) ≤ (W.card : ℝ) ^ (2 - 1 / (2 * (k : ℝ))) := Real.rpow_nonneg hcard0 _
          positivity
        have h2' : (0 : ℝ) ≤ N ^ 2 * (W.card : ℝ) ^ (2 - 3 / (4 * (k : ℝ))) *
            T ^ (1 / (2 * (k : ℝ))) := by
          have ha : (0 : ℝ) ≤ (W.card : ℝ) ^ (2 - 3 / (4 * (k : ℝ))) := Real.rpow_nonneg hcard0 _
          have hb : (0 : ℝ) ≤ T ^ (1 / (2 * (k : ℝ))) := Real.rpow_nonneg hT0.le _
          positivity
        rw [hX₂def]; linarith
      have h2 : C₆₁ * (T ^ ε) ^ 6 ≤ (1024 * C₆₁ * (1 + Cδ) * (1 + 2 * Cδ) + C₆₁) * T ^ (9 * ε) := by
        have hle : C₆₁ ≤ 1024 * C₆₁ * (1 + Cδ) * (1 + 2 * Cδ) + C₆₁ := by linarith
        have h9 : (0 : ℝ) ≤ T ^ (9 * ε) := Real.rpow_nonneg hT0.le _
        calc C₆₁ * (T ^ ε) ^ 6 ≤ C₆₁ * T ^ (9 * ε) :=
              mul_le_mul_of_nonneg_left hTpow6 hC₆₁
          _ ≤ _ := mul_le_mul_of_nonneg_right hle h9
      have h3 : (0 : ℝ) ≤ C₆₁ * (T ^ ε) ^ 6 := by positivity
      have h4 : (0 : ℝ) ≤ N ^ 2 * (W.card : ℝ) ^ 2 := by positivity
      calc C₆₁ * (T ^ ε) ^ 6 * (N ^ 2 * (W.card : ℝ) ^ 2)
          ≤ C₆₁ * (T ^ ε) ^ 6 * X₂ := mul_le_mul_of_nonneg_left h1 h3
        _ ≤ _ := mul_le_mul_of_nonneg_right h2 hX₂0
    exact hbound.trans hstep
  · -- the generic block: lift, cover, Heath-Brown at every length
    obtain ⟨M₀, hM₀def⟩ : ∃ M₀ : ℝ, M₀ = (2 : ℝ) ^ j := ⟨_, rfl⟩
    have hM₀0 : (0 : ℝ) < M₀ := by rw [hM₀def]; positivity
    have hM₀M : M₀ ≤ (M : ℝ) := by
      have h : ((2 ^ j : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast hjM
      rw [hM₀def]
      push_cast at h
      exact h
    have hMT' : M₀ ≤ T' / N := by
      have h1 : (1 : ℝ) ≤ (2 * T) ^ (1 + ε) / N := (one_le_div hN0).mpr hNrpow
      have h2 : (M : ℝ) ≤ 2 * ((2 * T) ^ (1 + ε) / N) := by linarith
      calc M₀ ≤ (M : ℝ) := hM₀M
        _ ≤ 2 * ((2 * T) ^ (1 + ε) / N) := h2
        _ = T' / N := by rw [hT'def]; ring
    obtain ⟨A, hAdef⟩ : ∃ A : ℕ, A = 2 ^ j - 1 := ⟨_, rfl⟩
    obtain ⟨B, hBdef⟩ : ∃ B : ℕ, B = 2 * 2 ^ j - 1 := ⟨_, rfl⟩
    have h2j : 2 ≤ 2 ^ j := by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hjpos
    have hA1 : 1 ≤ A := by rw [hAdef]; omega
    have hBA : B ≤ 3 * A := by rw [hAdef, hBdef]; omega
    obtain ⟨P, hPdef⟩ : ∃ P : ℕ, P = A ^ k := ⟨_, rfl⟩
    have hP1 : 1 ≤ P := by rw [hPdef]; exact Nat.one_le_pow _ _ (by omega)
    obtain ⟨m, hmdef⟩ : ∃ m : ℕ, m = 2 * k := ⟨_, rfl⟩
    have hcover : B ^ k ≤ 2 ^ m * P := by
      calc B ^ k ≤ (3 * A) ^ k := Nat.pow_le_pow_left hBA k
        _ = 3 ^ k * A ^ k := by rw [mul_pow]
        _ ≤ 4 ^ k * A ^ k := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by norm_num) k)
        _ = 2 ^ m * P := by rw [hmdef, hPdef, pow_mul]; norm_num
    -- the divisor bound on the lifted range
    obtain ⟨Dv, hDvdef⟩ : ∃ Dv : ℝ, Dv = divisorBoundConst δ * ((B ^ k : ℕ) : ℝ) ^ δ := ⟨_, rfl⟩
    have hDv0 : 0 ≤ Dv := by
      have := (divisorBoundConst_pos hδ).le
      rw [hDvdef]; positivity
    have hDvB : ∀ u ∈ Finset.Ioc (A ^ k) (B ^ k), (u.divisors.card : ℝ) ≤ Dv := by
      intro u hu
      rw [Finset.mem_Ioc] at hu
      have hu0 : u ≠ 0 := by
        have hpk : 0 < A ^ k := by positivity
        omega
      have h1 := card_divisors_le_rpow hδ hu0
      have h2 : ((u : ℕ) : ℝ) ^ δ ≤ ((B ^ k : ℕ) : ℝ) ^ δ :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hu.2) hδ.le
      rw [hDvdef]
      exact h1.trans (mul_le_mul_of_nonneg_left h2 (divisorBoundConst_pos hδ).le)
    -- (6.2): the `k`-th power lift
    have hS : dyadicSegmentBlock M j ⊆ Finset.Ioc A B := by
      rw [hAdef, hBdef]; exact dyadicSegmentBlock_subset_Ioc M j
    have hcoefS : ∀ n ∈ dyadicSegmentBlock M j, ‖((1 : ℝ) : ℂ)‖ ≤ (n : ℝ) ^ (-(0 : ℝ)) := by
      intro n _
      rw [neg_zero, Real.rpow_zero]
      simp
    have hlift := hbPairSum_le_power_lift W hk hS (σ := 0) (a := fun _ => ((1 : ℝ) : ℂ))
      hcoefS hDvB
    have hcoef2 : (fun u : ℕ => (((u : ℝ) ^ (-(0 : ℝ)) : ℝ) : ℂ)) = fun _ : ℕ => ((1 : ℝ) : ℂ) := by
      funext u
      rw [neg_zero, Real.rpow_zero]
    rw [hcoef2] at hlift
    -- (6.3): monotone support, then the dyadic cover with the all-lengths bound
    have hmono : hbPairSum W (Finset.Ioc (A ^ k) (B ^ k)) (fun _ => ((1 : ℝ) : ℂ)) ≤
        hbPairSum W (Finset.Ioc P (2 ^ m * P)) (fun _ => ((1 : ℝ) : ℂ)) := by
      refine hbPairSum_ofReal_mono_support W ?_ (fun n _ => zero_le_one)
      have hcover' : B ^ k ≤ 2 ^ m * A ^ k := by rw [← hPdef]; exact hcover
      rw [hPdef]
      exact Finset.Ioc_subset_Ioc_right hcover'
    have hcoef1 : ∀ n : ℕ, ‖((1 : ℝ) : ℂ)‖ ≤ 1 := by intro n; simp
    have hcov := hbPairSum_Ioc_two_pow_le_majorant hW1 hT1 hdiam hδ hP1 m hcoef1
    -- sizes: `M ≤ 8T²`, hence the lifted lengths are below `32^{4k} T^{4k}`
    have hrpow2 : (2 * T) ^ (1 + ε) ≤ 4 * T ^ 2 := by
      have h := Real.rpow_le_rpow_of_exponent_le h2T (by linarith : (1 : ℝ) + ε ≤ 2)
      rwa [show ((2 : ℝ) * T) ^ (2 : ℝ) = 4 * T ^ 2 by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring] at h
    have hT2 : (1 : ℝ) ≤ T ^ 2 := one_le_pow₀ hT1
    have hMbound : (M : ℝ) ≤ 8 * T ^ 2 := by
      have hdiv : (2 * T) ^ (1 + ε) / N ≤ (2 * T) ^ (1 + ε) :=
        div_le_self (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 2 * T) (1 + ε)) hN
      linarith only [hMle, hdiv, hrpow2, hT2]
    have hM₀bound : M₀ ≤ 8 * T ^ 2 := le_trans hM₀M hMbound
    have hM₀1 : (1 : ℝ) ≤ M₀ := by
      rw [hM₀def]; exact one_le_pow₀ (by norm_num)
    have hAM : ((A : ℕ) : ℝ) ≤ M₀ := by
      have h1 : ((A : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by
        have : A ≤ 2 ^ j := by rw [hAdef]; omega
        exact_mod_cast this
      rw [hM₀def]
      push_cast at h1
      exact h1
    have hPM : ((P : ℕ) : ℝ) ≤ M₀ ^ k := by
      rw [hPdef]
      push_cast
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) hAM k
    have hM₀k0 : (0 : ℝ) ≤ M₀ ^ k := by positivity
    have hP2M : ((P : ℕ) : ℝ) ^ 2 ≤ M₀ ^ (2 * k) := by
      have he : M₀ ^ (2 * k) = (M₀ ^ k) ^ 2 := by rw [Nat.mul_comm 2 k, pow_mul]
      rw [he]
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) hPM 2
    -- the two length bounds feeding the constant lemma
    have h32 : (1 : ℝ) ≤ (32 : ℝ) ^ (4 * k) := one_le_pow₀ (by norm_num)
    have hT4k : T ^ (2 * k) ≤ T ^ (4 * (k : ℝ)) := by
      rw [← Real.rpow_natCast T (2 * k)]
      refine Real.rpow_le_rpow_of_exponent_le hT1 ?_
      push_cast; linarith
    have hT4k0 : (0 : ℝ) ≤ T ^ (4 * (k : ℝ)) := Real.rpow_nonneg hT0.le _
    have hBk : ((B ^ k : ℕ) : ℝ) ≤ (32 : ℝ) ^ (4 * k) * T ^ (4 * (k : ℝ)) := by
      have hB16 : ((B : ℕ) : ℝ) ≤ 16 * T ^ 2 := by
        have h1 : ((B : ℕ) : ℝ) ≤ 2 * (M : ℝ) := by
          have : B ≤ 2 * M := by
            have : 2 ^ j ≤ M := hjM
            rw [hBdef]; omega
          exact_mod_cast this
        linarith
      have h1 : ((B ^ k : ℕ) : ℝ) ≤ (16 * T ^ 2) ^ k := by
        push_cast
        exact pow_le_pow_left₀ (Nat.cast_nonneg _) hB16 k
      have h2 : (16 * T ^ 2 : ℝ) ^ k = 16 ^ k * T ^ (2 * k) := by
        rw [mul_pow, ← pow_mul]
      have h3 : (16 : ℝ) ^ k ≤ (32 : ℝ) ^ (4 * k) := by
        refine le_trans (pow_le_pow_left₀ (by norm_num) (by norm_num : (16:ℝ) ≤ 32) k) ?_
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      have h16 : (0 : ℝ) ≤ (16 : ℝ) ^ k := by positivity
      calc ((B ^ k : ℕ) : ℝ) ≤ 16 ^ k * T ^ (2 * k) := by rw [← h2]; exact h1
        _ ≤ (32 : ℝ) ^ (4 * k) * T ^ (4 * (k : ℝ)) := by
            exact mul_le_mul h3 hT4k (by positivity) (by positivity)
    have hPm : (((2 ^ m * P) ^ 2 : ℕ) : ℝ) ≤ (32 : ℝ) ^ (4 * k) * T ^ (4 * (k : ℝ)) := by
      have hPmle : (((2 ^ m * P : ℕ)) : ℝ) ≤ 32 ^ k * T ^ (2 * k) := by
        have h1 : (((2 ^ m * P : ℕ)) : ℝ) = 4 ^ k * ((P : ℕ) : ℝ) := by
          have h2m : (2 : ℕ) ^ m = 4 ^ k := by rw [hmdef, pow_mul]; norm_num
          rw [h2m]; push_cast; ring
        have h2 : ((P : ℕ) : ℝ) ≤ (8 * T ^ 2) ^ k :=
          hPM.trans (pow_le_pow_left₀ (by linarith) hM₀bound k)
        have h3 : (8 * T ^ 2 : ℝ) ^ k = 8 ^ k * T ^ (2 * k) := by
          rw [mul_pow, ← pow_mul]
        have h4 : (0 : ℝ) ≤ (4 : ℝ) ^ k := by positivity
        rw [h1]
        calc (4 : ℝ) ^ k * ((P : ℕ) : ℝ) ≤ 4 ^ k * (8 ^ k * T ^ (2 * k)) := by
              rw [← h3]; exact mul_le_mul_of_nonneg_left h2 h4
          _ = 32 ^ k * T ^ (2 * k) := by rw [← mul_assoc, ← mul_pow]; norm_num
      have hsq : (((2 ^ m * P) ^ 2 : ℕ) : ℝ) = ((2 ^ m * P : ℕ) : ℝ) ^ 2 := by push_cast; ring
      have h32k : ((32 : ℝ) ^ k * T ^ (2 * k)) ^ 2 = 32 ^ (2 * k) * T ^ (4 * k) := by
        rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm k 2,
          show 2 * k * 2 = 4 * k from by ring]
      have hT44 : T ^ (4 * k) ≤ T ^ (4 * (k : ℝ)) := by
        rw [← Real.rpow_natCast T (4 * k)]
        refine Real.rpow_le_rpow_of_exponent_le hT1 ?_
        push_cast; linarith
      have h322 : (32 : ℝ) ^ (2 * k) ≤ (32 : ℝ) ^ (4 * k) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      rw [hsq]
      calc (((2 ^ m * P : ℕ)) : ℝ) ^ 2 ≤ ((32 : ℝ) ^ k * T ^ (2 * k)) ^ 2 :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) hPmle 2
        _ = 32 ^ (2 * k) * T ^ (4 * k) := h32k
        _ ≤ (32 : ℝ) ^ (4 * k) * T ^ (4 * (k : ℝ)) := by
            exact mul_le_mul h322 hT44 (by positivity) (by positivity)
    have hLong : ((hbLongBlock T : ℕ) : ℝ) ≤ (32 : ℝ) ^ (4 * k) * T ^ (4 * (k : ℝ)) := by
      have h1 := hbLongBlock_le_rpow hT1
      have h2 : T ^ ((2 : ℝ) / 3) ≤ T := by
        have := Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num : (2 : ℝ) / 3 ≤ 1)
        rwa [Real.rpow_one] at this
      have h3 : T ≤ T ^ (4 * (k : ℝ)) := by
        nth_rewrite 1 [← Real.rpow_one T]
        exact Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
      have h4 : (4 : ℝ) ≤ (32 : ℝ) ^ (4 * k) := by
        have : (32 : ℝ) ^ 1 ≤ (32 : ℝ) ^ (4 * k) := pow_le_pow_right₀ (by norm_num) (by omega)
        simp only [pow_one] at this; linarith
      calc ((hbLongBlock T : ℕ) : ℝ) ≤ 4 * T ^ ((2 : ℝ) / 3) := h1
        _ ≤ 4 * T ^ (4 * (k : ℝ)) := by linarith
        _ ≤ (32 : ℝ) ^ (4 * k) * T ^ (4 * (k : ℝ)) := by
            exact mul_le_mul_of_nonneg_right h4 hT4k0
    -- (6.3) at the paper's block length `M₀`
    obtain ⟨Cm, hCmdef⟩ : ∃ Cm : ℝ, Cm = hbSmallConst T δ + hbBlockConst T δ ((2 ^ m * P) ^ 2) := ⟨_, rfl⟩
    have hCm0 : 0 ≤ Cm := by
      have h1 : 0 ≤ hbSmallConst T δ := le_trans zero_le_one (one_le_hbSmallConst hT1 hδ)
      have h2 := hbBlockConst_nonneg (T := T) (δ := δ) hT1 ((2 ^ m * P) ^ 2)
      rw [hCmdef]; linarith only [h1, h2]
    have hc54 : (0 : ℝ) ≤ (W.card : ℝ) ^ ((5 : ℝ) / 4) := Real.rpow_nonneg hcard0 _
    have hc32 : (0 : ℝ) ≤ (W.card : ℝ) ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hcard0 _
    have hTleT' : T ≤ T' := by
      have : (0 : ℝ) < (2 * T) ^ (1 + ε) := Real.rpow_pos_of_pos (by linarith) _
      rw [hT'def]; linarith only [hrpow1, this]
    have hTT' : T ^ ((1 : ℝ) / 2) ≤ T' ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow hT0.le hTleT' (by norm_num)
    have hmaj : (W.card : ℝ) ^ 2 * ((P : ℕ) : ℝ) + (W.card : ℝ) * ((P : ℕ) : ℝ) ^ 2
          + (W.card : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * ((P : ℕ) : ℝ)
          + (W.card : ℝ) ^ ((3 : ℝ) / 2) * ((P : ℕ) : ℝ) ^ 2 ≤
        (W.card : ℝ) ^ 2 * M₀ ^ k + (W.card : ℝ) * M₀ ^ (2 * k)
          + (W.card : ℝ) ^ ((5 : ℝ) / 4) * T' ^ ((1 : ℝ) / 2) * M₀ ^ k
          + (W.card : ℝ) ^ ((3 : ℝ) / 2) * M₀ ^ (2 * k) := by
      exact majorant_mono hcard0 (Nat.cast_nonneg _) hPM hP2M
        (Real.rpow_nonneg hT0.le _) hTT'
    have hDv2k : (0 : ℝ) ≤ Dv ^ (2 * k) := pow_nonneg hDv0 (2 * k)
    have h63 : Dv ^ (2 * k) *
          hbPairSum W (Finset.Ioc (A ^ k) (B ^ k)) (fun _ => ((1 : ℝ) : ℂ)) ≤
        (Dv ^ (2 * k) * ((8 : ℝ) ^ m * Cm)) *
          ((W.card : ℝ) ^ 2 * M₀ ^ k + (W.card : ℝ) * M₀ ^ (2 * k)
            + (W.card : ℝ) ^ ((5 : ℝ) / 4) * T' ^ ((1 : ℝ) / 2) * M₀ ^ k
            + (W.card : ℝ) ^ ((3 : ℝ) / 2) * M₀ ^ (2 * k)) := by
      have hstep := hmono.trans hcov
      rw [← hCmdef] at hstep
      have h8m : (0 : ℝ) ≤ (8 : ℝ) ^ m * Cm := by positivity
      calc Dv ^ (2 * k) * hbPairSum W (Finset.Ioc (A ^ k) (B ^ k)) (fun _ => ((1 : ℝ) : ℂ))
          ≤ Dv ^ (2 * k) * ((8 : ℝ) ^ m * Cm *
              ((W.card : ℝ) ^ 2 * ((P : ℕ) : ℝ) + (W.card : ℝ) * ((P : ℕ) : ℝ) ^ 2
                + (W.card : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * ((P : ℕ) : ℝ)
                + (W.card : ℝ) ^ ((3 : ℝ) / 2) * ((P : ℕ) : ℝ) ^ 2)) :=
            mul_le_mul_of_nonneg_left hstep hDv2k
        _ ≤ Dv ^ (2 * k) * ((8 : ℝ) ^ m * Cm *
              ((W.card : ℝ) ^ 2 * M₀ ^ k + (W.card : ℝ) * M₀ ^ (2 * k)
                + (W.card : ℝ) ^ ((5 : ℝ) / 4) * T' ^ ((1 : ℝ) / 2) * M₀ ^ k
                + (W.card : ℝ) ^ ((3 : ℝ) / 2) * M₀ ^ (2 * k))) := by
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmaj h8m) hDv2k
        _ = _ := by ring
    -- the four-term assembly
    have h61' : ‖gmS2 w N W‖ ≤ C₆₁ * (T ^ ε) ^ 6 * (N ^ 2 / M₀) *
        hbPairSum W (dyadicSegmentBlock M j) (fun _ => ((1 : ℝ) : ℂ)) := by
      rw [hM₀def, mul_assoc]
      exact hS2
    have hC₆₁' : (0 : ℝ) ≤ C₆₁ * (T ^ ε) ^ 6 := mul_nonneg hC₆₁ (pow_nonneg hTε0 6)
    have hC'0 : (0 : ℝ) ≤ Dv ^ (2 * k) * ((8 : ℝ) ^ m * Cm) :=
      mul_nonneg hDv2k (mul_nonneg (pow_nonneg (by norm_num) m) hCm0)
    have hY0 : (0 : ℝ) ≤ Dv ^ (2 * k) *
        hbPairSum W (Finset.Ioc (A ^ k) (B ^ k)) (fun _ => ((1 : ℝ) : ℂ)) :=
      mul_nonneg hDv2k (hbPairSum_nonneg _ _ _)
    have hmain := prop61_abstract4_absorbed (W := (W.card : ℝ)) (N := N) (M := M₀) (T := T')
      (S₂ := ‖gmS2 w N W‖)
      (X := hbPairSum W (dyadicSegmentBlock M j) (fun _ => ((1 : ℝ) : ℂ)))
      (Y := Dv ^ (2 * k) * hbPairSum W (Finset.Ioc (A ^ k) (B ^ k)) (fun _ => ((1 : ℝ) : ℂ)))
      (C := C₆₁ * (T ^ ε) ^ 6) (C' := Dv ^ (2 * k) * ((8 : ℝ) ^ m * Cm))
      hk hcard1 hN0 hM₀0 hT'0 hMT' hC₆₁' hC'0 hY0 h61' hlift h63
    -- the bracket at `T'` against the bracket at `T`
    have hexp0 : (0 : ℝ) ≤ 1 / (2 * (k : ℝ)) := by positivity
    have hexp1 : 1 / (2 * (k : ℝ)) ≤ 1 := by
      rw [div_le_one (by linarith only [hkR])]
      linarith only [hkR]
    have hhalf : T' ^ (1 / (2 * (k : ℝ))) ≤ 8 * (T ^ (1 / (2 * (k : ℝ))) * T ^ ε) :=
      rpow_le_of_le_mul hT0 hT'0 hT'le hexp0 hexp1 hTε1
    have hbr : N ^ 2 * (W.card : ℝ) ^ 2 + T' * N * (W.card : ℝ) ^ (2 - 1 / (2 * (k : ℝ)))
          + N ^ 2 * (W.card : ℝ) ^ (2 - 3 / (4 * (k : ℝ))) * T' ^ (1 / (2 * (k : ℝ)))
        ≤ 8 * T ^ ε * X₂ := by
      rw [hX₂def]
      exact bracket_mono (N := N) (c := (W.card : ℝ)) (T := T) (T' := T') (Tε := T ^ ε)
        (a := (W.card : ℝ) ^ (2 - 1 / (2 * (k : ℝ))))
        (b := (W.card : ℝ) ^ (2 - 3 / (4 * (k : ℝ))))
        (s := T ^ (1 / (2 * (k : ℝ)))) (s' := T' ^ (1 / (2 * (k : ℝ))))
        (by linarith) hcard0 (Real.rpow_nonneg hcard0 _) (Real.rpow_nonneg hcard0 _)
        (Real.rpow_nonneg hT0.le _) hT0.le h8Tε hT'le hhalf
    -- the constants are `T^{O(ε)}`
    have hexpk : 1 / (k : ℝ) ≤ 1 := by
      rw [div_le_one (by linarith only [hkR])]; linarith only [hkR]
    have hCδ1 := (hblk T hT1).1 ((2 ^ m * P) ^ 2) hPm
    have hCδ2 := (hblk T hT1).1 (hbLongBlock T) hLong
    have hCδ3 := (hblk T hT1).2 (B ^ k) hBk
    have hCmle : Cm ≤ 2 * Cδ * T ^ ε := by
      rw [hCmdef, hbSmallConst_eq_hbBlockConst]
      linarith only [hCδ1, hCδ2]
    have hDv2 : Dv ^ 2 ≤ Cδ * T ^ ε := by rw [hDvdef]; exact hCδ3
    have hmax0 : (0 : ℝ) ≤ max 1 (2 * Cδ) := le_trans zero_le_one (le_max_left _ _)
    have hroot : (Dv ^ (2 * k) * ((8 : ℝ) ^ m * Cm)) ^ (1 / (k : ℝ)) ≤
        Cδ * T ^ ε * (64 * (max 1 (2 * Cδ) * T ^ ε)) :=
      lifted_root_le hk hmdef hDv0 hCm0 hCδ hTε1 hDv2 hCmle
    -- collect
    have ha' : (0 : ℝ) ≤ (W.card : ℝ) ^ (2 - 1 / (2 * (k : ℝ))) := Real.rpow_nonneg hcard0 _
    have hb' : (0 : ℝ) ≤ (W.card : ℝ) ^ (2 - 3 / (4 * (k : ℝ))) := Real.rpow_nonneg hcard0 _
    have hs' : (0 : ℝ) ≤ T' ^ (1 / (2 * (k : ℝ))) := Real.rpow_nonneg hT'0.le _
    have t1 : (0 : ℝ) ≤ N ^ 2 * (W.card : ℝ) ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have t2 : (0 : ℝ) ≤ T' * N * (W.card : ℝ) ^ (2 - 1 / (2 * (k : ℝ))) :=
      mul_nonneg (mul_nonneg hT'0.le hN0.le) ha'
    have t3 : (0 : ℝ) ≤ N ^ 2 * (W.card : ℝ) ^ (2 - 3 / (4 * (k : ℝ))) *
        T' ^ (1 / (2 * (k : ℝ))) := mul_nonneg (mul_nonneg (sq_nonneg _) hb') hs'
    have hBR0 : (0 : ℝ) ≤ N ^ 2 * (W.card : ℝ) ^ 2
        + T' * N * (W.card : ℝ) ^ (2 - 1 / (2 * (k : ℝ)))
        + N ^ 2 * (W.card : ℝ) ^ (2 - 3 / (4 * (k : ℝ))) * T' ^ (1 / (2 * (k : ℝ))) := by
      linarith only [t1, t2, t3]
    exact prop61_constant_step (S := ‖gmS2 w N W‖) (C₆₁ := C₆₁) (Cδ := Cδ) (E := T ^ ε)
      (RT := (Dv ^ (2 * k) * ((8 : ℝ) ^ m * Cm)) ^ (1 / (k : ℝ)))
      (BRv := N ^ 2 * (W.card : ℝ) ^ 2 + T' * N * (W.card : ℝ) ^ (2 - 1 / (2 * (k : ℝ)))
        + N ^ 2 * (W.card : ℝ) ^ (2 - 3 / (4 * (k : ℝ))) * T' ^ (1 / (2 * (k : ℝ))))
      (Xv := X₂) (P6 := (T ^ ε) ^ 6) (P9 := T ^ (9 * ε))
      hC₆₁ hCδ hTε0 (pow_nonneg hTε0 6) (Real.rpow_nonneg hT0.le _) hmain hroot hbr hBR0 hX₂0
      hprod

end

end RHTower.GuthMaynard
