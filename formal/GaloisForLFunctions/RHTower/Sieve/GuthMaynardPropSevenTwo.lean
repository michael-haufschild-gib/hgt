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

/-! ### The dyadic decomposition -/

/-- The near-diagonal condition `|m₃| ≤ 4|m₂| + δ`: for `|m₁| ≤ |m₂|`, Proposition 7.1 makes `I_m`
negligible off it. -/
def IsNearDiagonal (δ : ℝ) (m : ℤ × ℤ × ℤ) : Prop :=
  |(m.2.2 : ℝ)| ≤ 4 * |(m.2.1 : ℝ)| + δ

/-- The dyadic scale `2^{⌊log₂|m₂|⌋}` of the middle frequency. -/
def middleScale (m : ℤ × ℤ × ℤ) : ℕ :=
  2 ^ Nat.log 2 m.2.1.natAbs

/-- `(N²/M) Ĩ_{(m₁,−m₂,m₃)}` at the dyadic scale `M = 2^{⌊log₂|m₂|⌋}` of `m₂`. -/
def dyadicSmoothedTerm (ψ₁ : ℝ → ℝ) (N : ℝ) (W : Finset ℝ) (m : ℤ × ℤ × ℤ) : ℝ :=
  N ^ 2 / (middleScale m : ℝ) *
    smoothedCubicTerm ψ₁ outerBump N (middleScale m) W m.1 (-m.2.1) m.2.2

theorem dyadicSmoothedTerm_nonneg (ψ₁ : ℝ → ℝ) (N : ℝ) (W : Finset ℝ) (m : ℤ × ℤ × ℤ) :
    0 ≤ dyadicSmoothedTerm ψ₁ N W m :=
  mul_nonneg (by unfold middleScale; positivity) (smoothedCubicTerm_nonneg _ _ _ _ _ _ _ _)

/-- **One frequency of the expansion.** For `m₂ ≠ 0` and `|m₁| ≤ |m₂|`:
`|I_m| ≤ C (N²/M) Ĩ_{(m₁,−m₂,m₃)} 1[|m₃| ≤ 4|m₂| + T^η/N] + C N³|W|³T^{−A}`, `M = 2^{⌊log₂|m₂|⌋}`. -/
theorem norm_cubicTerm_le_dyadicSmoothedTerm (w : CGLSmoothBump) {η : ℝ} (hη : 0 < η) (A : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ (T N : ℝ) (W : Finset ℝ) (m : ℤ × ℤ × ℤ), 1 ≤ T → 0 < N → m.2.1 ≠ 0 →
      |m.1| ≤ |m.2.1| →
      ‖cubicTerm w W N m.1 m.2.1 m.2.2‖ ≤
        C * {m | IsNearDiagonal (T ^ η / N) m}.indicator
            (dyadicSmoothedTerm (innerBump (2 * T ^ η)) N W) m +
          C * (N ^ 3 * (W.card : ℝ) ^ 3 * T ^ (-A)) := by
  obtain ⟨C₃, hC₃, hsmooth⟩ := norm_cubicTerm_le_smoothedCubicTerm w hη A
  obtain ⟨C₄, hC₄, hneg⟩ := prop71_negligible w hη A
  refine ⟨C₃ + C₄, by positivity, fun T N W m hT hN hm₂ h12 => ?_⟩
  have hT0 : 0 < T := by linarith
  have hE : 0 ≤ N ^ 3 * (W.card : ℝ) ^ 3 * T ^ (-A) := by
    have := Real.rpow_pos_of_pos hT0 (-A); positivity
  have hD := dyadicSmoothedTerm_nonneg (innerBump (2 * T ^ η)) N W m
  by_cases hg : IsNearDiagonal (T ^ η / N) m
  · rw [indicator_of_mem (show m ∈ {m | IsNearDiagonal (T ^ η / N) m} from hg)]
    have hk := two_pow_log_le_abs hm₂
    have hM : (middleScale m : ℝ) ≤ |(m.2.1 : ℝ)| := by
      rw [← Int.cast_abs]; unfold middleScale; exact_mod_cast hk.1
    have h := hsmooth T N (middleScale m) W m.1 m.2.1 m.2.2 hT hN
      (by unfold middleScale; positivity) hM
    have e : C₃ * (N ^ 2 / (middleScale m : ℝ)) *
        smoothedCubicTerm (innerBump (2 * T ^ η)) outerBump N (middleScale m) W m.1 (-m.2.1) m.2.2 =
        C₃ * dyadicSmoothedTerm (innerBump (2 * T ^ η)) N W m := by
      unfold dyadicSmoothedTerm; ring
    rw [e] at h
    nlinarith [mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC₄ : C₃ ≤ C₃ + C₄) hD,
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC₄ : C₃ ≤ C₃ + C₄) hE]
  · rw [indicator_of_notMem (show m ∉ {m | IsNearDiagonal (T ^ η / N) m} from hg), mul_zero,
      zero_add]
    have h12' : |(m.1 : ℝ)| ≤ |(m.2.1 : ℝ)| := by
      rw [← Int.cast_abs, ← Int.cast_abs]; exact_mod_cast h12
    have h := hneg T N W m.1 m.2.1 m.2.2 hT hN h12' (lt_of_not_ge hg)
    have e : C₄ * N ^ 3 * (W.card : ℝ) ^ 3 * T ^ (-A) =
        C₄ * (N ^ 3 * (W.card : ℝ) ^ 3 * T ^ (-A)) := by ring
    rw [e] at h
    nlinarith [mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC₃ : C₄ ≤ C₃ + C₄) hE]

/-- On a sorted near-diagonal frequency (`δ ≤ 1`) of dyadic class `(l, k)`, the frequency
`(m₁, −m₂, m₃)` lies in the dyadic block of `(2^l, 2^k)`. -/
theorem mem_dyadicFrequencyBlock_of_class {δ : ℝ} (hδ : δ ≤ 1) {m : ℤ × ℤ × ℤ}
    (hnz : m.1 ≠ 0 ∧ m.2.1 ≠ 0 ∧ m.2.2 ≠ 0) (hsorted : IsSortedFrequency m)
    (hg : IsNearDiagonal δ m) :
    (m.1, -m.2.1, m.2.2) ∈
      dyadicFrequencyBlock (2 ^ Nat.log 2 m.1.natAbs) (2 ^ Nat.log 2 m.2.1.natAbs) := by
  have hk₁ := two_pow_log_le_abs hnz.1
  have hk₂ := two_pow_log_le_abs hnz.2.1
  have hg' : |(m.2.2 : ℝ)| ≤ 4 * |(m.2.1 : ℝ)| + 1 := by
    have := hg; unfold IsNearDiagonal at this; linarith
  have hg'' : |m.2.2| ≤ 4 * |m.2.1| + 1 := by
    rw [← Int.cast_abs, ← Int.cast_abs] at hg'; exact_mod_cast hg'
  rw [mem_dyadicFrequencyBlock]
  simp only [abs_neg]
  push_cast at hk₁ hk₂ ⊢
  refine ⟨hk₁.1, hk₁.2, hk₂.1, hk₂.2, hk₂.1.trans hsorted.2, ?_⟩
  have := hk₂.2
  have h2M : (0 : ℤ) < 2 ^ Nat.log 2 m.2.1.natAbs := by positivity
  linarith

/-- **Dyadic pigeonhole.** For `δ ≤ 1` and `K ≥ 1` there are `1 ≤ M₁ ≤ M ≤ K` with
`Σ_{0<|m_i|≤K, sorted, near-diagonal} (N²/M(m)) Ĩ_{(m₁,−m₂,m₃)} ≤ (log₂K + 1)² (N²/M) Σ_{block(M₁,M)} Ĩ_m`. -/
theorem exists_dyadic_block (ψ₁ : ℝ → ℝ) (N : ℝ) (W : Finset ℝ) {δ : ℝ} (hδ : δ ≤ 1) {K : ℕ}
    (hK : 1 ≤ K) :
    ∃ M₁ M : ℕ, 1 ≤ M₁ ∧ M₁ ≤ M ∧ M ≤ K ∧
      ∑ m ∈ (nonzeroFrequencyBox K).filter IsSortedFrequency,
          {m | IsNearDiagonal δ m}.indicator (dyadicSmoothedTerm ψ₁ N W) m ≤
        (((Nat.log 2 K + 1 : ℕ) : ℝ)) ^ 2 * (N ^ 2 / (M : ℝ) *
          ∑ m ∈ dyadicFrequencyBlock M₁ M, smoothedCubicTerm ψ₁ outerBump N M W m.1 m.2.1 m.2.2) := by
  classical
  have hsumS : ∑ m ∈ (nonzeroFrequencyBox K).filter IsSortedFrequency,
      {m | IsNearDiagonal δ m}.indicator (dyadicSmoothedTerm ψ₁ N W) m =
      ∑ m ∈ ((nonzeroFrequencyBox K).filter IsSortedFrequency).filter
        (fun m => IsNearDiagonal δ m), dyadicSmoothedTerm ψ₁ N W m := by
    rw [Finset.sum_filter (s := (nonzeroFrequencyBox K).filter IsSortedFrequency)]
    exact Finset.sum_congr rfl fun m _ => by simp only [Set.indicator_apply, Set.mem_setOf_eq]
  set Sbox := (nonzeroFrequencyBox K).filter IsSortedFrequency
  set S := Sbox.filter fun m => IsNearDiagonal δ m
  set L := Nat.log 2 K + 1
  set P := (Finset.range L ×ˢ Finset.range L).filter fun p : ℕ × ℕ => p.1 ≤ p.2
  set cls : ℤ × ℤ × ℤ → ℕ × ℕ := fun m => (Nat.log 2 m.1.natAbs, Nat.log 2 m.2.1.natAbs)
  set F := dyadicSmoothedTerm ψ₁ N W
  have hmaps : ∀ m ∈ S, cls m ∈ P := by
    intro m hm
    obtain ⟨hmbox, hsorted⟩ := Finset.mem_filter.mp (Finset.mem_filter.mp hm).1
    obtain ⟨-, hb₁, hb₂, -⟩ := mem_nonzeroFrequencyBox.mp hmbox
    rw [← Int.natCast_natAbs] at hb₁ hb₂
    have ha₁ : m.1.natAbs ≤ K := by exact_mod_cast hb₁
    have ha₂ : m.2.1.natAbs ≤ K := by exact_mod_cast hb₂
    have ha₁₂ : m.1.natAbs ≤ m.2.1.natAbs := by
      have := hsorted.1
      rw [← Int.natCast_natAbs, ← Int.natCast_natAbs] at this
      exact_mod_cast this
    simp only [P, cls, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    exact ⟨⟨Nat.lt_succ_of_le (Nat.log_mono_right ha₁),
      Nat.lt_succ_of_le (Nat.log_mono_right ha₂)⟩, Nat.log_mono_right ha₁₂⟩
  have hPne : P.Nonempty := ⟨(0, 0), by simp [P, L]⟩
  have hPpos : (0 : ℝ) < P.card := by exact_mod_cast hPne.card_pos
  obtain ⟨p, hpP, hp⟩ := Finset.exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum
    (f := cls) (w := F) (b := (∑ m ∈ S, F m) / P.card) hmaps hPne (by
      rw [nsmul_eq_mul, mul_div_cancel₀ _ hPpos.ne'])
  rw [div_le_iff₀' hPpos] at hp
  have hpP' := Finset.mem_filter.mp hpP
  have hp2 : p.2 ≤ Nat.log 2 K :=
    Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_product.mp hpP'.1).2)
  refine ⟨2 ^ p.1, 2 ^ p.2, Nat.one_le_two_pow, Nat.pow_le_pow_right (by norm_num) hpP'.2,
    (Nat.pow_le_pow_right (by norm_num) hp2).trans (Nat.pow_log_le_self 2 (by omega)), ?_⟩
  -- the maximal class embeds into the block via `m ↦ (m₁, −m₂, m₃)`
  set φ : ℤ × ℤ × ℤ → ℤ × ℤ × ℤ := fun m => (m.1, -m.2.1, m.2.2)
  have hφinj : Set.InjOn φ ↑(S.filter fun m => cls m = p) := fun a _ b _ hab => by
    simp only [φ, Prod.mk.injEq, neg_inj] at hab
    exact Prod.ext hab.1 (Prod.ext hab.2.1 hab.2.2)
  have hsub : (S.filter fun m => cls m = p).image φ ⊆ dyadicFrequencyBlock (2 ^ p.1) (2 ^ p.2) := by
    intro m' hm'
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hm'
    obtain ⟨hmS, hcl⟩ := Finset.mem_filter.mp hm
    obtain ⟨hmSbox, hmg⟩ := Finset.mem_filter.mp hmS
    obtain ⟨hmbox, hsorted⟩ := Finset.mem_filter.mp hmSbox
    have hcl' := Prod.ext_iff.mp hcl
    have h := mem_dyadicFrequencyBlock_of_class hδ (mem_nonzeroFrequencyBox.mp hmbox).1 hsorted hmg
    rwa [show Nat.log 2 m.1.natAbs = p.1 from hcl'.1,
      show Nat.log 2 m.2.1.natAbs = p.2 from hcl'.2] at h
  have hFeq : ∀ m ∈ S.filter (fun m => cls m = p), F m = N ^ 2 / ((2 ^ p.2 : ℕ) : ℝ) *
      smoothedCubicTerm ψ₁ outerBump N ((2 ^ p.2 : ℕ) : ℝ) W (φ m).1 (φ m).2.1 (φ m).2.2 := by
    intro m hm
    have hcl := Prod.ext_iff.mp (Finset.mem_filter.mp hm).2
    have h2 : Nat.log 2 m.2.1.natAbs = p.2 := hcl.2
    simp only [F, dyadicSmoothedTerm, middleScale, φ, h2]
  have hblock : ∑ m ∈ S with cls m = p, F m ≤ N ^ 2 / ((2 ^ p.2 : ℕ) : ℝ) *
      ∑ m ∈ dyadicFrequencyBlock (2 ^ p.1) (2 ^ p.2),
        smoothedCubicTerm ψ₁ outerBump N ((2 ^ p.2 : ℕ) : ℝ) W m.1 m.2.1 m.2.2 := by
    rw [Finset.sum_congr rfl hFeq, ← Finset.mul_sum]
    gcongr
    rw [← Finset.sum_image (f := fun m' =>
      smoothedCubicTerm ψ₁ outerBump N ((2 ^ p.2 : ℕ) : ℝ) W m'.1 m'.2.1 m'.2.2) hφinj]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun m _ _ =>
      smoothedCubicTerm_nonneg _ _ _ _ _ _ _ _
  have hPcard : (P.card : ℝ) ≤ ((L : ℕ) : ℝ) ^ 2 := by
    have hc : P.card ≤ L * L := (Finset.card_filter_le _ _).trans (by
      rw [Finset.card_product, Finset.card_range])
    calc (P.card : ℝ) ≤ ((L * L : ℕ) : ℝ) := by exact_mod_cast hc
      _ = ((L : ℕ) : ℝ) ^ 2 := by push_cast; ring
  have hfib0 : 0 ≤ ∑ m ∈ S with cls m = p, F m :=
    Finset.sum_nonneg fun m _ => dyadicSmoothedTerm_nonneg ψ₁ N W m
  rw [hsumS]
  calc ∑ m ∈ S, F m ≤ P.card * ∑ m ∈ S with cls m = p, F m := hp
    _ ≤ ((L : ℕ) : ℝ) ^ 2 * (N ^ 2 / ((2 ^ p.2 : ℕ) : ℝ) *
          ∑ m ∈ dyadicFrequencyBlock (2 ^ p.1) (2 ^ p.2),
            smoothedCubicTerm ψ₁ outerBump N ((2 ^ p.2 : ℕ) : ℝ) W m.1 m.2.1 m.2.2) :=
        mul_le_mul hPcard hblock hfib0 (by positivity)

/-- Real-number assembly of Proposition 7.2. -/
theorem prop72_assembly {s b a i X Y E C₁ C₂ L cL τ : ℝ} (hs : s ≤ b + 8 * C₁ * Y)
    (hb : b ≤ 6 * a) (ha : a ≤ C₂ * i + E) (hi : i ≤ L * X) (hL : L ≤ cL ^ 2 * τ)
    (hE : E ≤ C₂ * (216 * Y)) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hτ : 0 ≤ τ) :
    s ≤ (6 * C₂ * cL ^ 2 + 1296 * C₂ + 8 * C₁) * τ * X +
      (6 * C₂ * cL ^ 2 + 1296 * C₂ + 8 * C₁) * Y := by
  have h1 : C₂ * i ≤ C₂ * (cL ^ 2 * τ * X) :=
    mul_le_mul_of_nonneg_left (hi.trans (mul_le_mul_of_nonneg_right hL hX)) hC₂
  have h2 : 0 ≤ (1296 * C₂ + 8 * C₁) * τ * X := by positivity
  have h3 : 0 ≤ 6 * C₂ * cL ^ 2 * Y := by positivity
  nlinarith

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
          C * T ^ ε * (N ^ 2 / M * ∑ m ∈ dyadicFrequencyBlock M₁ M,
            smoothedCubicTerm (innerBump (2 * T ^ (ε / 2))) outerBump N M W m.1 m.2.1 m.2.2) +
          C * T ^ (-100 : ℝ) := by
  have hη : 0 < ε / 2 := by positivity
  obtain ⟨C₁, hC₁, htrunc⟩ := allNonzeroCubicSum_truncation w.toCGLSmoothBump hη 103
  obtain ⟨C₂, hC₂, hfreq⟩ := norm_cubicTerm_le_dyadicSmoothedTerm w.toCGLSmoothBump hη 112
  have hcL0 : 0 ≤ 4 / (ε * Real.log 2) + 1 := by have := Real.log_pos one_lt_two; positivity
  refine ⟨6 * C₂ * (4 / (ε * Real.log 2) + 1) ^ 2 + 1296 * C₂ + 8 * C₁, by positivity,
    fun T N W hT hN hNT hTεN hW hsep => ?_⟩
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hN0 : 0 < N := by linarith
  have hcard : (W.card : ℝ) ≤ 2 * T := by
    have := card_le_of_isSeparated hT0.le hW hsep; linarith
  have hTηN : T ^ (ε / 2) / N ≤ 1 := (div_le_one hN0).mpr
    ((Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)).trans hTεN)
  -- the frequency box `0 < |m_i| ≤ K`, `K = ⌊T^{1+ε/2}/N⌋`
  obtain ⟨K, hK_def⟩ : ∃ K : ℕ, K = ⌊T ^ (1 + ε / 2) / N⌋₊ := ⟨_, rfl⟩
  have hKle : (K : ℝ) ≤ T ^ (1 + ε / 2) / N := hK_def ▸ Nat.floor_le (by positivity)
  have hT1η : T ≤ T ^ (1 + ε / 2) := by
    calc T = T ^ (1 : ℝ) := (Real.rpow_one T).symm
      _ ≤ T ^ (1 + ε / 2) := Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
  have hK1 : 1 ≤ K := hK_def ▸ Nat.le_floor (by
    rw [Nat.cast_one, le_div_iff₀ hN0, one_mul]; linarith)
  have hKT2 : (K : ℝ) ≤ T ^ 2 := by
    calc (K : ℝ) ≤ T ^ (1 + ε / 2) / N := hKle
      _ ≤ T ^ (1 + ε / 2) := div_le_self (by positivity) hN
      _ ≤ T ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
      _ = T ^ 2 := by exact_mod_cast Real.rpow_natCast T 2
  obtain ⟨M₁, M, hM₁, hM₁M, hMK, hdy⟩ :=
    exists_dyadic_block (innerBump (2 * T ^ (ε / 2))) N W hTηN hK1
  refine ⟨M₁, M, hM₁, hM₁M, ?_, ?_⟩
  · calc (M : ℝ) ≤ K := by exact_mod_cast hMK
      _ ≤ T ^ (1 + ε / 2) / N := hKle
      _ ≤ T ^ (1 + ε) / N :=
          div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)) hN0.le
  -- truncation (7.1)
  have h1 : ‖allNonzeroCubicSum w.toCGLSmoothBump W N‖ ≤
      ∑ m ∈ nonzeroFrequencyBox K, ‖cubicTerm w.toCGLSmoothBump W N m.1 m.2.1 m.2.2‖ +
        8 * C₁ * T ^ (-100 : ℝ) := by
    have ht := htrunc T N W hT1 hN hW
    rw [← hK_def] at ht
    have hi := norm_le_insert' (allNonzeroCubicSum w.toCGLSmoothBump W N)
      (∑ m ∈ nonzeroFrequencyBox K, cubicTerm w.toCGLSmoothBump W N m.1 m.2.1 m.2.2)
    have hs := norm_sum_le (nonzeroFrequencyBox K)
      fun m => cubicTerm w.toCGLSmoothBump W N m.1 m.2.1 m.2.2
    have he := truncation_error_le hT1 hC₁ hcard
    linarith
  -- symmetrisation
  have h2 := sum_norm_cubicTerm_le_six_sorted w W N K
  -- one frequency at a time
  have h3 : ∑ m ∈ (nonzeroFrequencyBox K).filter IsSortedFrequency,
      ‖cubicTerm w.toCGLSmoothBump W N m.1 m.2.1 m.2.2‖ ≤
      C₂ * ∑ m ∈ (nonzeroFrequencyBox K).filter IsSortedFrequency,
          {m | IsNearDiagonal (T ^ (ε / 2) / N) m}.indicator
            (dyadicSmoothedTerm (innerBump (2 * T ^ (ε / 2))) N W) m +
        (2 * K + 1) ^ 3 * (C₂ * (N ^ 3 * (W.card : ℝ) ^ 3 * T ^ (-112 : ℝ))) := by
    have hE0 : 0 ≤ C₂ * (N ^ 3 * (W.card : ℝ) ^ 3 * T ^ (-112 : ℝ)) := by
      have := Real.rpow_pos_of_pos hT0 (-112 : ℝ); positivity
    calc ∑ m ∈ (nonzeroFrequencyBox K).filter IsSortedFrequency,
          ‖cubicTerm w.toCGLSmoothBump W N m.1 m.2.1 m.2.2‖
        ≤ ∑ m ∈ (nonzeroFrequencyBox K).filter IsSortedFrequency,
            (C₂ * {m | IsNearDiagonal (T ^ (ε / 2) / N) m}.indicator
              (dyadicSmoothedTerm (innerBump (2 * T ^ (ε / 2))) N W) m +
              C₂ * (N ^ 3 * (W.card : ℝ) ^ 3 * T ^ (-112 : ℝ))) := by
          refine Finset.sum_le_sum fun m hm => ?_
          obtain ⟨hmbox, hsorted⟩ := Finset.mem_filter.mp hm
          exact hfreq T N W m hT1 hN0 (mem_nonzeroFrequencyBox.mp hmbox).1.2.1 hsorted.1
      _ ≤ _ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
          gcongr
          exact (Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans
            (card_nonzeroFrequencyBox_le K)
  -- the number of dyadic classes
  have hL : (((Nat.log 2 K + 1 : ℕ) : ℝ)) ^ 2 ≤ (4 / (ε * Real.log 2) + 1) ^ 2 * T ^ ε := by
    have hLle := natLog_add_one_le hε hT1 hKT2
    have hTsq : (T ^ (ε / 2)) ^ 2 = T ^ ε := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]; norm_num
    calc (((Nat.log 2 K + 1 : ℕ) : ℝ)) ^ 2 = ((Nat.log 2 K : ℝ) + 1) ^ 2 := by push_cast; ring
      _ ≤ ((4 / (ε * Real.log 2) + 1) * T ^ (ε / 2)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hLle 2
      _ = (4 / (ε * Real.log 2) + 1) ^ 2 * T ^ ε := by rw [mul_pow, hTsq]
  have hX0 : 0 ≤ N ^ 2 / (M : ℝ) * ∑ m ∈ dyadicFrequencyBlock M₁ M,
      smoothedCubicTerm (innerBump (2 * T ^ (ε / 2))) outerBump N M W m.1 m.2.1 m.2.2 :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun m _ =>
      smoothedCubicTerm_nonneg _ _ _ _ _ _ _ _)
  have hboxerr : (2 * (K : ℝ) + 1) ^ 3 * (C₂ * (N ^ 3 * (W.card : ℝ) ^ 3 * T ^ (-112 : ℝ))) ≤
      C₂ * (216 * T ^ (-100 : ℝ)) := by
    rw [mul_left_comm]
    exact mul_le_mul_of_nonneg_left (box_error_le hT1 hN0.le hNT hKT2 hcard) hC₂
  exact prop72_assembly h1 h2 h3 hdy hL hboxerr hC₁ hC₂ hX0
    (Real.rpow_pos_of_pos hT0 _).le (by positivity)

end

end RHTower.GuthMaynard
