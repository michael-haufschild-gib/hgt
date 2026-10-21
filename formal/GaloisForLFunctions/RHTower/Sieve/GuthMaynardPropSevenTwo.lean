import GaloisForLFunctions.RHTower.Sieve.GuthMaynardPropSevenTwoSymmetry
import GaloisForLFunctions.RHTower.Sieve.GuthMaynardPropSevenTwoSmoothing

/-!
# Guth–Maynard Proposition 7.2: expansion of `S₃`

For `0 < ε ≤ 1`, `η = ε/2`, `2 ≤ T`, `T^ε ≤ N ≤ T` and a `1`-separated `W ⊂ [0, T]`:

1. (7.1) `S₃ = Σ_{0<|m_i|≤K} I_m + O(T^{−100})` with `K = ⌊T^{1+η}/N⌋` (`allNonzeroCubicSum_truncation`);
2. the box sum of `|I_m|` is at most six times its sum over `|m₁| ≤ |m₂| ≤ |m₃|`
   (`sum_norm_cubicTerm_le_six_sorted`);
3. for sorted `m`, either `|m₃| > 4|m₂| + T^η/N` and `I_m` is negligible (`prop71_negligible`), or
   `|I_m| ≪ (N²/M) Ĩ_{(m₁,−m₂,m₃)}` with `M = 2^{⌊log₂|m₂|⌋}` (`norm_cubicTerm_le_smoothedCubicTerm`);
4. the dyadic classes `(⌊log₂|m₁|⌋, ⌊log₂|m₂|⌋)` number at most `(log₂K + 1)² ≪_ε T^ε`, so one class
   `|m₁| ∼ M₁`, `|m₂| ∼ M` carries a `T^{−ε}` share of the sum (weighted pigeonhole); on it
   `M ≤ |m₃| < 9M`, and `m ↦ (m₁, −m₂, m₃)` maps it into the dyadic block.

Result (`prop72`): there are `1 ≤ M₁ ≤ M ≤ T^{1+ε}/N` with
`|S₃| ≤ C T^ε (N²/M) Σ_{M₁≤|m₁|<2M₁, M≤|m₂|<2M, M≤|m₃|<9M} Ĩ_m + C T^{−100}`,
where `Ĩ_m` uses `ψ̃₁ = innerBump (2T^{ε/2})` (support `|x| < 4T^{ε/2}`, `ψ̃₁(0) = 1`, derivatives
bounded uniformly) and `ψ̃₂ = outerBump` (support `(1/8, 33/8)`, `ψ̃₂ = 1` on `[1/4, 4]`).
-/

set_option autoImplicit false

open MeasureTheory Set

namespace RHTower.GuthMaynard

noncomputable section

/-- The dyadic block `{m : M₁ ≤ |m₁| < 2M₁, M ≤ |m₂| < 2M, M ≤ |m₃| < 9M}` of Proposition 7.2
(`|m₁| ∼ M₁`, `|m₂|, |m₃| ≍ M`). -/
def dyadicFrequencyBlock (M₁ M : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  (Finset.Icc (-(2 * M₁ : ℤ)) (2 * M₁) ×ˢ
      (Finset.Icc (-(2 * M : ℤ)) (2 * M) ×ˢ Finset.Icc (-(9 * M : ℤ)) (9 * M))).filter
    fun m => (M₁ : ℤ) ≤ |m.1| ∧ |m.1| < 2 * M₁ ∧ (M : ℤ) ≤ |m.2.1| ∧ |m.2.1| < 2 * M ∧
      (M : ℤ) ≤ |m.2.2| ∧ |m.2.2| < 9 * M

theorem mem_dyadicFrequencyBlock {M₁ M : ℕ} {m : ℤ × ℤ × ℤ} :
    m ∈ dyadicFrequencyBlock M₁ M ↔ (M₁ : ℤ) ≤ |m.1| ∧ |m.1| < 2 * M₁ ∧ (M : ℤ) ≤ |m.2.1| ∧
      |m.2.1| < 2 * M ∧ (M : ℤ) ≤ |m.2.2| ∧ |m.2.2| < 9 * M := by
  simp only [dyadicFrequencyBlock, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨⟨abs_le.mp h.2.1.le, abs_le.mp h.2.2.2.1.le, abs_le.mp h.2.2.2.2.2.le⟩, h⟩

/-- `2^{⌊log₂|k|⌋} ≤ |k| < 2 · 2^{⌊log₂|k|⌋}` for `k ≠ 0`. -/
theorem two_pow_log_le_abs {k : ℤ} (hk : k ≠ 0) :
    ((2 ^ Nat.log 2 k.natAbs : ℕ) : ℤ) ≤ |k| ∧ |k| < 2 * ((2 ^ Nat.log 2 k.natAbs : ℕ) : ℤ) := by
  have hne : k.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hk
  have h1 := Nat.pow_log_le_self 2 hne
  have h2 := Nat.lt_pow_succ_log_self one_lt_two k.natAbs
  rw [pow_succ] at h2
  rw [← Int.natCast_natAbs]
  constructor
  · exact_mod_cast h1
  · have : k.natAbs < 2 * 2 ^ Nat.log 2 k.natAbs := by linarith
    exact_mod_cast this

/-- `|{0 < |m_i| ≤ K}| ≤ (2K + 1)³`. -/
theorem card_nonzeroFrequencyBox_le (K : ℕ) :
    ((nonzeroFrequencyBox K).card : ℝ) ≤ (2 * K + 1) ^ 3 := by
  have hI : (Finset.Icc (-(K : ℤ)) K).card = 2 * K + 1 := by rw [Int.card_Icc]; omega
  have h : (nonzeroFrequencyBox K).card ≤ (2 * K + 1) ^ 3 := by
    refine (Finset.card_filter_le _ _).trans (le_of_eq ?_)
    rw [Finset.card_product, Finset.card_product, hI]; ring
  exact_mod_cast h

/-- The number of dyadic scales up to `K ≤ T²` is `≪_ε T^{ε/2}`:
`log₂K + 1 ≤ (4/(ε log 2) + 1) T^{ε/2}`. -/
theorem natLog_add_one_le {ε T : ℝ} (hε : 0 < ε) (hT : 1 ≤ T) {K : ℕ} (hK : (K : ℝ) ≤ T ^ 2) :
    ((Nat.log 2 K : ℕ) : ℝ) + 1 ≤ (4 / (ε * Real.log 2) + 1) * T ^ (ε / 2) := by
  have hT0 : 0 < T := by linarith
  have hTε : 1 ≤ T ^ (ε / 2) := Real.one_le_rpow hT (by positivity)
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hn : ((Nat.log 2 K : ℕ) : ℝ) ≤ 4 / (ε * Real.log 2) * T ^ (ε / 2) := by
    rcases Nat.eq_zero_or_pos K with hK0 | hKpos
    · simp only [hK0, Nat.log_zero_right, Nat.cast_zero]; positivity
    · have hpow : ((2 : ℝ) ^ Nat.log 2 K) ≤ K := by
        exact_mod_cast Nat.pow_log_le_self 2 hKpos.ne'
      have hlogK : (Nat.log 2 K : ℝ) * Real.log 2 ≤ Real.log K := by
        rw [← Real.log_pow]
        exact Real.log_le_log (by positivity) hpow
      have hlogT : Real.log K ≤ 2 * Real.log T := by
        have e : 2 * Real.log T = Real.log (T ^ 2) := by rw [Real.log_pow]; norm_num
        rw [e]
        exact Real.log_le_log (by exact_mod_cast hKpos) hK
      have hlogε : Real.log T ≤ T ^ (ε / 2) / (ε / 2) := Real.log_le_rpow_div hT0.le (by positivity)
      have : (Nat.log 2 K : ℝ) ≤ 2 * (T ^ (ε / 2) / (ε / 2)) / Real.log 2 := by
        rw [le_div_iff₀ hlog2]; linarith
      calc (Nat.log 2 K : ℝ) ≤ 2 * (T ^ (ε / 2) / (ε / 2)) / Real.log 2 := this
        _ = 4 / (ε * Real.log 2) * T ^ (ε / 2) := by field_simp; ring
  linarith

/-- `T^n T^{−a} = T^{n−a}`. -/
theorem pow_mul_rpow_neg {T : ℝ} (hT : 0 < T) (n : ℕ) (a : ℝ) :
    T ^ n * T ^ (-a) = T ^ ((n : ℝ) - a) := by
  rw [← Real.rpow_natCast, ← Real.rpow_add hT]; ring_nf

/-- The truncation error: `C|W|³T^{−103} ≤ 8C T^{−100}` for `|W| ≤ 2T`. -/
theorem truncation_error_le {T C : ℝ} (hT : 1 ≤ T) (hC : 0 ≤ C) {W : Finset ℝ}
    (hW : (W.card : ℝ) ≤ 2 * T) :
    C * (W.card : ℝ) ^ 3 * T ^ (-103 : ℝ) ≤ 8 * C * T ^ (-100 : ℝ) := by
  have hT0 : 0 < T := by linarith
  have hW3 : (W.card : ℝ) ^ 3 ≤ (2 * T) ^ 3 := pow_le_pow_left₀ (Nat.cast_nonneg _) hW 3
  have h : T ^ 3 * T ^ (-103 : ℝ) = T ^ (-100 : ℝ) := by
    rw [pow_mul_rpow_neg hT0]; congr 1; norm_num
  have hpos : 0 < T ^ (-103 : ℝ) := Real.rpow_pos_of_pos hT0 _
  calc C * (W.card : ℝ) ^ 3 * T ^ (-103 : ℝ) ≤ C * (2 * T) ^ 3 * T ^ (-103 : ℝ) := by gcongr
    _ = 8 * C * (T ^ 3 * T ^ (-103 : ℝ)) := by ring
    _ = 8 * C * T ^ (-100 : ℝ) := by rw [h]

/-- The box error: `(2K+1)³ N³ |W|³ T^{−112} ≤ 216 T^{−100}` for `K ≤ T²`, `N ≤ T`, `|W| ≤ 2T`. -/
theorem box_error_le {T N : ℝ} (hT : 1 ≤ T) (hN : 0 ≤ N) (hNT : N ≤ T) {K : ℕ}
    (hK : (K : ℝ) ≤ T ^ 2) {W : Finset ℝ} (hW : (W.card : ℝ) ≤ 2 * T) :
    (2 * K + 1) ^ 3 * (N ^ 3 * (W.card : ℝ) ^ 3 * T ^ (-112 : ℝ)) ≤ 216 * T ^ (-100 : ℝ) := by
  have hT0 : 0 < T := by linarith
  have h1 : (2 * (K : ℝ) + 1) ^ 3 ≤ (3 * T ^ 2) ^ 3 := by
    have : 1 ≤ T ^ 2 := one_le_pow₀ hT
    exact pow_le_pow_left₀ (by positivity) (by linarith) 3
  have h2 : N ^ 3 ≤ T ^ 3 := pow_le_pow_left₀ hN hNT 3
  have h3 : (W.card : ℝ) ^ 3 ≤ (2 * T) ^ 3 := pow_le_pow_left₀ (Nat.cast_nonneg _) hW 3
  have h : T ^ 12 * T ^ (-112 : ℝ) = T ^ (-100 : ℝ) := by
    rw [pow_mul_rpow_neg hT0]; congr 1; norm_num
  have hpos : 0 < T ^ (-112 : ℝ) := Real.rpow_pos_of_pos hT0 _
  calc (2 * (K : ℝ) + 1) ^ 3 * (N ^ 3 * (W.card : ℝ) ^ 3 * T ^ (-112 : ℝ))
      ≤ (3 * T ^ 2) ^ 3 * (T ^ 3 * (2 * T) ^ 3 * T ^ (-112 : ℝ)) := by gcongr
    _ = 216 * (T ^ 12 * T ^ (-112 : ℝ)) := by ring
    _ = 216 * T ^ (-100 : ℝ) := by rw [h]

/-- **Guth–Maynard Proposition 7.2.** For a real CGL bump and `0 < ε ≤ 1` there is `C` such that
for `2 ≤ T`, `T^ε ≤ N ≤ T` and every `1`-separated `W ⊂ [0, T]` there are dyadic scales
`1 ≤ M₁ ≤ M ≤ T^{1+ε}/N` with
`|S₃| ≤ C T^ε (N²/M) Σ_{M₁≤|m₁|<2M₁, M≤|m₂|<2M, M≤|m₃|<9M} Ĩ_m + C T^{−100}`,
where `Ĩ_m` is built from `ψ̃₁ = innerBump (2T^{ε/2})`, `ψ̃₂ = outerBump` and the scale `M`. -/
theorem prop72 (w : CGLRealSmoothBump) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C, 0 ≤ C ∧ ∀ (T N : ℝ) (W : Finset ℝ), 2 ≤ T → 1 ≤ N → N ≤ T → T ^ ε ≤ N →
      (∀ t ∈ W, t ∈ Icc 0 T) → IsSeparated 1 W →
      ∃ M₁ M : ℕ, 1 ≤ M₁ ∧ M₁ ≤ M ∧ (M : ℝ) ≤ T ^ (1 + ε) / N ∧
        ‖allNonzeroCubicSum w.toCGLSmoothBump W N‖ ≤
          C * T ^ ε * (N ^ 2 / M) * ∑ m ∈ dyadicFrequencyBlock M₁ M,
            smoothedCubicTerm (innerBump (2 * T ^ (ε / 2))) outerBump N M W m.1 m.2.1 m.2.2 +
          C * T ^ (-100 : ℝ) := by
  set η := ε / 2 with hη_def
  have hη : 0 < η := by positivity
  obtain ⟨C₁, hC₁, htrunc⟩ := allNonzeroCubicSum_truncation w.toCGLSmoothBump hη 103
  obtain ⟨C₃, hC₃, hsmooth⟩ := norm_cubicTerm_le_smoothedCubicTerm w.toCGLSmoothBump hη 112
  obtain ⟨C₄, hC₄, hneg⟩ := prop71_negligible w.toCGLSmoothBump hη 112
  set cL := 4 / (ε * Real.log 2) + 1 with hcL
  have hcL0 : 0 ≤ cL := by have := Real.log_pos one_lt_two; positivity
  refine ⟨6 * C₃ * cL ^ 2 + 1296 * (C₃ + C₄) + 8 * C₁, by positivity,
    fun T N W hT hN hNT hTεN hW hsep => ?_⟩
  classical
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hN0 : 0 < N := by linarith
  have hcard : (W.card : ℝ) ≤ 2 * T := by
    have := card_le_of_isSeparated hT0.le hW hsep; linarith
  have hTη1 : T ^ η ≤ T ^ ε := Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
  have hTηN : T ^ η / N ≤ 1 := (div_le_one hN0).mpr (hTη1.trans hTεN)
  set ψ₁ := innerBump (2 * T ^ η) with hψ₁
  -- the frequency box
  set K : ℕ := ⌊T ^ (1 + η) / N⌋₊ with hK_def
  have hKle : (K : ℝ) ≤ T ^ (1 + η) / N := Nat.floor_le (by positivity)
  have hT1η : T ≤ T ^ (1 + η) := by
    calc T = T ^ (1 : ℝ) := (Real.rpow_one T).symm
      _ ≤ T ^ (1 + η) := Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
  have hK1 : 1 ≤ K := Nat.le_floor (by
    rw [Nat.cast_one, le_div_iff₀ hN0, one_mul]; linarith)
  have hKT2 : (K : ℝ) ≤ T ^ 2 := by
    calc (K : ℝ) ≤ T ^ (1 + η) / N := hKle
      _ ≤ T ^ (1 + η) := div_le_self (by positivity) hN
      _ ≤ T ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
      _ = T ^ 2 := by exact_mod_cast Real.rpow_natCast T 2
  -- step 1: truncation
  have h1 : ‖allNonzeroCubicSum w.toCGLSmoothBump W N‖ ≤
      ∑ m ∈ nonzeroFrequencyBox K, ‖cubicTerm w.toCGLSmoothBump W N m.1 m.2.1 m.2.2‖ +
        8 * C₁ * T ^ (-100 : ℝ) := by
    have ht := htrunc T N W hT1 hN hW
    have := norm_le_insert' (allNonzeroCubicSum w.toCGLSmoothBump W N)
      (∑ m ∈ nonzeroFrequencyBox K, cubicTerm w.toCGLSmoothBump W N m.1 m.2.1 m.2.2)
    have hs := norm_sum_le (nonzeroFrequencyBox K)
      fun m => cubicTerm w.toCGLSmoothBump W N m.1 m.2.1 m.2.2
    have he := truncation_error_le hT1 hC₁ hcard
    linarith
  -- steps 2–3: sorted frequencies, negligible or smoothed
  set good : ℤ × ℤ × ℤ → Prop := fun m => |(m.2.2 : ℝ)| ≤ 4 * |(m.2.1 : ℝ)| + T ^ η / N
    with hgood
  set kOf : ℤ × ℤ × ℤ → ℕ := fun m => Nat.log 2 m.2.1.natAbs with hkOf
  set F : ℤ × ℤ × ℤ → ℝ := fun m => N ^ 2 / ((2 ^ kOf m : ℕ) : ℝ) *
      smoothedCubicTerm ψ₁ outerBump N ((2 ^ kOf m : ℕ) : ℝ) W m.1 (-m.2.1) m.2.2 with hF
  have hF0 : ∀ m, 0 ≤ F m := fun m => mul_nonneg (by positivity)
    (smoothedCubicTerm_nonneg _ _ _ _ _ _ _ _)
  set err := (C₃ + C₄) * (N ^ 3 * (W.card : ℝ) ^ 3 * T ^ (-112 : ℝ)) with herr
  have herr0 : 0 ≤ err := by have := Real.rpow_pos_of_pos hT0 (-112 : ℝ); positivity
  set Sbox := (nonzeroFrequencyBox K).filter IsSortedFrequency with hSbox
  have hpt : ∀ m ∈ Sbox, ‖cubicTerm w.toCGLSmoothBump W N m.1 m.2.1 m.2.2‖ ≤
      C₃ * (if good m then F m else 0) + err := by
    intro m hm
    obtain ⟨hmbox, hsorted⟩ := Finset.mem_filter.mp hm
    obtain ⟨hnz, -⟩ := mem_nonzeroFrequencyBox.mp hmbox
    have hNWT : 0 ≤ N ^ 3 * (W.card : ℝ) ^ 3 * T ^ (-112 : ℝ) := by
      have := Real.rpow_pos_of_pos hT0 (-112 : ℝ); positivity
    by_cases hg : good m
    · rw [if_pos hg]
      have hk := two_pow_log_le_abs hnz.2.1
      have hM : ((2 ^ kOf m : ℕ) : ℝ) ≤ |(m.2.1 : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast hk.1
      have := hsmooth T N ((2 ^ kOf m : ℕ) : ℝ) W m.1 m.2.1 m.2.2 hT1 hN0 (by positivity) hM
      have hC34 : C₃ * (N ^ 3 * (W.card : ℝ) ^ 3 * T ^ (-112 : ℝ)) ≤ err := by
        rw [herr]; exact mul_le_mul_of_nonneg_right (by linarith) hNWT
      calc ‖cubicTerm w.toCGLSmoothBump W N m.1 m.2.1 m.2.2‖
          ≤ C₃ * (N ^ 2 / ((2 ^ kOf m : ℕ) : ℝ)) *
              smoothedCubicTerm ψ₁ outerBump N ((2 ^ kOf m : ℕ) : ℝ) W m.1 (-m.2.1) m.2.2 +
            C₃ * N ^ 3 * (W.card : ℝ) ^ 3 * T ^ (-(112 : ℝ)) := this
        _ ≤ C₃ * F m + err := by
            have e1 : C₃ * (N ^ 2 / ((2 ^ kOf m : ℕ) : ℝ)) *
                smoothedCubicTerm ψ₁ outerBump N ((2 ^ kOf m : ℕ) : ℝ) W m.1 (-m.2.1) m.2.2 =
                C₃ * F m := by rw [hF]; ring
            have e2 : C₃ * N ^ 3 * (W.card : ℝ) ^ 3 * T ^ (-(112 : ℝ)) =
                C₃ * (N ^ 3 * (W.card : ℝ) ^ 3 * T ^ (-112 : ℝ)) := by ring
            rw [e1, e2]; linarith
    · rw [if_neg hg, mul_zero, zero_add]
      have h12 : |(m.1 : ℝ)| ≤ |(m.2.1 : ℝ)| := by
        rw [← Int.cast_abs, ← Int.cast_abs]; exact_mod_cast hsorted.1
      have := hneg T N W m.1 m.2.1 m.2.2 hT1 hN0 h12 (lt_of_not_ge hg)
      have hC4 : C₄ * N ^ 3 * (W.card : ℝ) ^ 3 * T ^ (-(112 : ℝ)) ≤ err := by
        calc C₄ * N ^ 3 * (W.card : ℝ) ^ 3 * T ^ (-(112 : ℝ))
            = C₄ * (N ^ 3 * (W.card : ℝ) ^ 3 * T ^ (-112 : ℝ)) := by ring
          _ ≤ err := mul_le_mul_of_nonneg_right (by linarith) hNWT
      linarith
  -- step 4: sum the pointwise bounds
  have h4 : ∑ m ∈ Sbox, ‖cubicTerm w.toCGLSmoothBump W N m.1 m.2.1 m.2.2‖ ≤
      C₃ * ∑ m ∈ Sbox.filter good, F m + (2 * K + 1) ^ 3 * err := by
    calc ∑ m ∈ Sbox, ‖cubicTerm w.toCGLSmoothBump W N m.1 m.2.1 m.2.2‖
        ≤ ∑ m ∈ Sbox, (C₃ * (if good m then F m else 0) + err) := Finset.sum_le_sum hpt
      _ = C₃ * ∑ m ∈ Sbox.filter good, F m + Sbox.card * err := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite, Finset.sum_const_zero,
            add_zero, Finset.sum_const, nsmul_eq_mul]
      _ ≤ C₃ * ∑ m ∈ Sbox.filter good, F m + (2 * K + 1) ^ 3 * err := by
          gcongr
          exact (Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans
            (card_nonzeroFrequencyBox_le K)
  -- step 5: weighted pigeonhole over the dyadic classes
  set L := Nat.log 2 K + 1 with hL
  set P := (Finset.range L ×ˢ Finset.range L).filter fun p : ℕ × ℕ => p.1 ≤ p.2 with hP
  set cls : ℤ × ℤ × ℤ → ℕ × ℕ := fun m => (Nat.log 2 m.1.natAbs, kOf m) with hcls
  set S := Sbox.filter good with hS
  have hmaps : ∀ m ∈ S, cls m ∈ P := by
    intro m hm
    obtain ⟨⟨hmbox, hsorted⟩, -⟩ := Finset.mem_filter.mp hm |>.imp_left Finset.mem_filter.mp
    obtain ⟨-, hb₁, hb₂, -⟩ := mem_nonzeroFrequencyBox.mp hmbox
    rw [← Int.natCast_natAbs] at hb₁ hb₂
    have ha₁ : m.1.natAbs ≤ K := by exact_mod_cast hb₁
    have ha₂ : m.2.1.natAbs ≤ K := by exact_mod_cast hb₂
    have ha₁₂ : m.1.natAbs ≤ m.2.1.natAbs := by
      have := hsorted.1
      rw [← Int.natCast_natAbs, ← Int.natCast_natAbs] at this
      exact_mod_cast this
    simp only [hP, hcls, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    refine ⟨⟨Nat.lt_succ_of_le (Nat.log_mono_right ha₁),
      Nat.lt_succ_of_le (Nat.log_mono_right ha₂)⟩, Nat.log_mono_right ha₁₂⟩
  have hPne : P.Nonempty := ⟨(0, 0), by simp [hP, hL]⟩
  have hPcard : (P.card : ℝ) ≤ cL ^ 2 * T ^ ε := by
    have hc : P.card ≤ L * L := (Finset.card_filter_le _ _).trans (by
      rw [Finset.card_product, Finset.card_range])
    have hLle := natLog_add_one_le hε hT1 hKT2
    have hLsq : ((L : ℕ) : ℝ) ^ 2 ≤ (cL * T ^ (ε / 2)) ^ 2 := by
      have : ((L : ℕ) : ℝ) = (Nat.log 2 K : ℝ) + 1 := by rw [hL]; push_cast; ring
      rw [this]; exact pow_le_pow_left₀ (by positivity) hLle 2
    have hTsq : (T ^ (ε / 2)) ^ 2 = T ^ ε := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]; norm_num
    calc (P.card : ℝ) ≤ ((L * L : ℕ) : ℝ) := by exact_mod_cast hc
      _ = ((L : ℕ) : ℝ) ^ 2 := by push_cast; ring
      _ ≤ (cL * T ^ (ε / 2)) ^ 2 := hLsq
      _ = cL ^ 2 * T ^ ε := by rw [mul_pow, hTsq]
  obtain ⟨p, hpP, hp⟩ := Finset.exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum
    (f := cls) (w := F) (b := (∑ m ∈ S, F m) / P.card) hmaps hPne (by
      rw [nsmul_eq_mul, mul_div_cancel₀ _ (by exact_mod_cast hPne.card_pos.ne')])
  have h5 : ∑ m ∈ S, F m ≤ P.card * ∑ m ∈ S with cls m = p, F m := by
    rwa [div_le_iff₀' (by exact_mod_cast hPne.card_pos)] at hp
  -- step 6: the maximal class sits inside one dyadic block
  set M₁ : ℕ := 2 ^ p.1 with hM₁
  set M : ℕ := 2 ^ p.2 with hM
  have hpP' := Finset.mem_filter.mp hpP
  have hp12 : p.1 ≤ p.2 := hpP'.2
  have hp2 : p.2 ≤ Nat.log 2 K := Nat.lt_succ_iff.mp (Finset.mem_range.mp
    (Finset.mem_product.mp hpP'.1).2)
  set φ : ℤ × ℤ × ℤ → ℤ × ℤ × ℤ := fun m => (m.1, -m.2.1, m.2.2) with hφ
  have hφinj : Set.InjOn φ ↑(S.filter fun m => cls m = p) := fun a _ b _ hab => by
    simp only [hφ, Prod.mk.injEq, neg_inj] at hab
    exact Prod.ext hab.1 (Prod.ext hab.2.1 hab.2.2)
  have hsub : (S.filter fun m => cls m = p).image φ ⊆ dyadicFrequencyBlock M₁ M := by
    intro m' hm'
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hm'
    obtain ⟨hmS, hcl⟩ := Finset.mem_filter.mp hm
    obtain ⟨hmSbox, hmg⟩ := Finset.mem_filter.mp hmS
    obtain ⟨hmbox, hsorted⟩ := Finset.mem_filter.mp hmSbox
    obtain ⟨hnz, -⟩ := mem_nonzeroFrequencyBox.mp hmbox
    simp only [hcls, Prod.mk.injEq] at hcl
    have hk₁ := two_pow_log_le_abs hnz.1
    have hk₂ := two_pow_log_le_abs hnz.2.1
    rw [hcl.1] at hk₁
    rw [show Nat.log 2 m.2.1.natAbs = p.2 from hcl.2] at hk₂
    -- `|m₃| ≤ 4|m₂| + 1 < 9M`
    have hg' : |(m.2.2 : ℝ)| ≤ 4 * |(m.2.1 : ℝ)| + 1 := by
      have := hmg; simp only [hgood] at this; linarith
    have hg'' : |m.2.2| ≤ 4 * |m.2.1| + 1 := by
      rw [← Int.cast_abs, ← Int.cast_abs] at hg'; exact_mod_cast hg'
    rw [mem_dyadicFrequencyBlock]
    simp only [hφ, abs_neg]
    push_cast at hk₁ hk₂ ⊢
    refine ⟨hk₁.1, hk₁.2, hk₂.1, hk₂.2, hk₂.1.trans hsorted.2, ?_⟩
    have := hk₂.2
    have h2M : (0 : ℤ) < 2 ^ p.2 := by positivity
    linarith
  have h6 : ∑ m ∈ S with cls m = p, F m ≤ N ^ 2 / (M : ℝ) * ∑ m ∈ dyadicFrequencyBlock M₁ M,
      smoothedCubicTerm ψ₁ outerBump N M W m.1 m.2.1 m.2.2 := by
    have hFeq : ∀ m ∈ S.filter (fun m => cls m = p), F m = N ^ 2 / (M : ℝ) *
        smoothedCubicTerm ψ₁ outerBump N M W (φ m).1 (φ m).2.1 (φ m).2.2 := by
      intro m hm
      have hcl := (Finset.mem_filter.mp hm).2
      simp only [hcls, Prod.mk.injEq] at hcl
      simp only [hF, hφ, hM, ← hcl.2]
    rw [Finset.sum_congr rfl hFeq, ← Finset.mul_sum]
    gcongr
    rw [← Finset.sum_image (f := fun m' => smoothedCubicTerm ψ₁ outerBump N M W m'.1 m'.2.1 m'.2.2)
      hφinj]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun m _ _ =>
      smoothedCubicTerm_nonneg _ _ _ _ _ _ _ _
  -- the scales
  have hM₁1 : 1 ≤ M₁ := Nat.one_le_two_pow
  have hM₁M : M₁ ≤ M := Nat.pow_le_pow_right (by norm_num) hp12
  have hMK : (M : ℝ) ≤ T ^ (1 + ε) / N := by
    have h2K : M ≤ K := (Nat.pow_le_pow_right (by norm_num) hp2).trans
      (Nat.pow_log_le_self 2 (by omega))
    calc (M : ℝ) ≤ K := by exact_mod_cast h2K
      _ ≤ T ^ (1 + η) / N := hKle
      _ ≤ T ^ (1 + ε) / N := by
          gcongr
          exact Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
  refine ⟨M₁, M, hM₁1, hM₁M, hMK, ?_⟩
  -- assembly
  set X := N ^ 2 / (M : ℝ) * ∑ m ∈ dyadicFrequencyBlock M₁ M,
      smoothedCubicTerm ψ₁ outerBump N M W m.1 m.2.1 m.2.2 with hX
  have hX0 : 0 ≤ X := mul_nonneg (by positivity) (Finset.sum_nonneg fun m _ =>
    smoothedCubicTerm_nonneg _ _ _ _ _ _ _ _)
  have hY0 : 0 < T ^ (-100 : ℝ) := Real.rpow_pos_of_pos hT0 _
  have hsix := sum_norm_cubicTerm_le_six_sorted w W N K
  have hboxerr : (2 * (K : ℝ) + 1) ^ 3 * err ≤ (C₃ + C₄) * (216 * T ^ (-100 : ℝ)) := by
    rw [herr, mul_left_comm]
    exact mul_le_mul_of_nonneg_left (box_error_le hT1 hN0.le hNT hKT2 hcard) (by positivity)
  have hFsum : ∑ m ∈ S, F m ≤ cL ^ 2 * T ^ ε * X := by
    calc ∑ m ∈ S, F m ≤ P.card * ∑ m ∈ S with cls m = p, F m := h5
      _ ≤ cL ^ 2 * T ^ ε * X := by
          have := Finset.sum_nonneg fun m (_ : m ∈ S.filter fun m => cls m = p) => hF0 m
          exact mul_le_mul hPcard h6 this (by positivity)
  have hTε0 : 0 ≤ T ^ ε := by positivity
  calc ‖allNonzeroCubicSum w.toCGLSmoothBump W N‖
      ≤ 6 * (C₃ * (cL ^ 2 * T ^ ε * X) + (C₃ + C₄) * (216 * T ^ (-100 : ℝ))) +
          8 * C₁ * T ^ (-100 : ℝ) := by
        have := mul_le_mul_of_nonneg_left hFsum hC₃
        linarith
    _ ≤ (6 * C₃ * cL ^ 2 + 1296 * (C₃ + C₄) + 8 * C₁) * T ^ ε * X +
          (6 * C₃ * cL ^ 2 + 1296 * (C₃ + C₄) + 8 * C₁) * T ^ (-100 : ℝ) := by
        have hA : 0 ≤ (1296 * (C₃ + C₄) + 8 * C₁) * T ^ ε * X := by positivity
        have hB : 0 ≤ 6 * C₃ * cL ^ 2 * T ^ (-100 : ℝ) := by positivity
        nlinarith
    _ = _ := by rw [hX]; ring

end

end RHTower.GuthMaynard
