import GaloisForLFunctions.RHTower.Sieve.GuthMaynardSTwoReductionPairBounds
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIICover

/-!
# Guth–Maynard §6: dyadic classes of `|t₁ − t₂|` and the per-pair bounds

The proof of Proposition 6.1 splits the pairs `t₁ ≠ t₂` dyadically by `|t₁ − t₂| ∼ MN` and applies
Lemma 6.2 with a Dirichlet polynomial of length `M`.  Here the class of `τ` (`|τ| ≥ 1`) is
`k = ⌊log₂ ⌊|τ|⌋⌋`, so `2^k ≤ |τ| < 2^{k+1}`, and the class length is
`M_k = ⌈(2^{k+1})^{1+ε} / N⌉`, admissible in Lemma 6.2 for every `τ` of the class.  A class is
*long* when `N ≤ (2^{k+1})^{1+ε}`; then `N M_k ≤ 4 · 2^k (2T)^ε`, which converts the weight
`N³ / |τ|` of Lemma 6.2 into Guth–Maynard's `N² / M`.  In a *short* class `N > |τ|^{1+ε}` and the
decay of Lemma 4.3 makes `N³ |A(τ)|² ≤ c N²` directly.
-/

set_option autoImplicit false

open Complex Finset
open scoped FourierTransform

noncomputable section

namespace RHTower.GuthMaynard

/-- The dyadic class `k = ⌊log₂ ⌊|τ|⌋⌋` of a difference `τ`. -/
def gmClass (τ : ℝ) : ℕ := Nat.log 2 ⌊|τ|⌋₊

/-- The number of classes up to height `T`: `⌊log₂ ⌊T⌋⌋ + 1`. -/
def gmClassCount (T : ℝ) : ℕ := Nat.log 2 ⌊T⌋₊ + 1

/-- The class length `M_k = ⌈(2^{k+1})^{1+ε} / N⌉`. -/
def gmClassLength (ε N : ℝ) (k : ℕ) : ℕ := ⌈((2 : ℝ) ^ (k + 1)) ^ (1 + ε) / N⌉₊

theorem two_pow_gmClass_le {τ : ℝ} (hτ : 1 ≤ |τ|) : (2 : ℝ) ^ gmClass τ ≤ |τ| := by
  have hfl : ⌊|τ|⌋₊ ≠ 0 := by
    have := Nat.floor_pos.mpr hτ
    omega
  calc (2 : ℝ) ^ gmClass τ = ((2 ^ gmClass τ : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ (⌊|τ|⌋₊ : ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 hfl
    _ ≤ |τ| := Nat.floor_le (abs_nonneg τ)

theorem lt_two_pow_gmClass_succ (τ : ℝ) : |τ| < (2 : ℝ) ^ (gmClass τ + 1) := by
  have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ⌊|τ|⌋₊
  have h' : (⌊|τ|⌋₊ : ℝ) + 1 ≤ ((2 ^ (gmClass τ + 1) : ℕ) : ℝ) := by
    exact_mod_cast h
  calc |τ| < (⌊|τ|⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    _ ≤ _ := by push_cast at h'; exact h'

theorem gmClass_lt_count {τ T : ℝ} (hτT : |τ| ≤ T) : gmClass τ < gmClassCount T :=
  Nat.lt_succ_of_le (Nat.log_mono_right (Nat.floor_le_floor hτT))

theorem two_pow_le_of_lt_count {T : ℝ} (hT : 1 ≤ T) {k : ℕ} (hk : k < gmClassCount T) :
    (2 : ℝ) ^ k ≤ T := by
  have hfl : ⌊T⌋₊ ≠ 0 := by
    have := Nat.floor_pos.mpr hT
    omega
  have hk' : k ≤ Nat.log 2 ⌊T⌋₊ := Nat.lt_succ_iff.mp hk
  calc (2 : ℝ) ^ k ≤ (2 : ℝ) ^ Nat.log 2 ⌊T⌋₊ := pow_le_pow_right₀ (by norm_num) hk'
    _ = ((2 ^ Nat.log 2 ⌊T⌋₊ : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ (⌊T⌋₊ : ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 hfl
    _ ≤ T := Nat.floor_le (by linarith)

/-- `(2^{k+1})^{1+ε} ≤ 2 · 2^k (2T)^ε` and `≤ 4T²` when `2^k ≤ T`. -/
theorem classPower_le {ε T : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hT : 1 ≤ T) {k : ℕ}
    (hk : (2 : ℝ) ^ k ≤ T) :
    ((2 : ℝ) ^ (k + 1)) ^ (1 + ε) ≤ 2 * 2 ^ k * (2 * T) ^ ε ∧
      ((2 : ℝ) ^ (k + 1)) ^ (1 + ε) ≤ 4 * T ^ 2 := by
  have h2k : (0 : ℝ) < 2 ^ (k + 1) := by positivity
  have hle : (2 : ℝ) ^ (k + 1) ≤ 2 * T := by rw [pow_succ]; linarith
  have hsplit : ((2 : ℝ) ^ (k + 1)) ^ (1 + ε) = 2 ^ (k + 1) * ((2 : ℝ) ^ (k + 1)) ^ ε := by
    rw [Real.rpow_add h2k, Real.rpow_one]
  refine ⟨?_, ?_⟩
  · rw [hsplit]
    have h2 : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by ring
    calc (2 : ℝ) ^ (k + 1) * ((2 : ℝ) ^ (k + 1)) ^ ε ≤ (2 : ℝ) ^ (k + 1) * (2 * T) ^ ε :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow h2k.le hle hε.le) h2k.le
      _ = 2 * 2 ^ k * (2 * T) ^ ε := by rw [h2]
  · calc ((2 : ℝ) ^ (k + 1)) ^ (1 + ε) ≤ (2 * T) ^ (1 + ε) :=
          Real.rpow_le_rpow h2k.le hle (by linarith)
      _ ≤ (2 * T) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = 4 * T ^ 2 := by rw [Real.rpow_two]; ring

/-- The class length is admissible in Lemma 6.2: `1 ≤ M_k ≤ 8T²` and `|τ|^{1+ε}/N ≤ M_k` for
`|τ| < 2^{k+1}`. -/
theorem gmClassLength_spec {ε N T : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hN : 1 ≤ N) (hT : 1 ≤ T)
    {k : ℕ} (hk : (2 : ℝ) ^ k ≤ T) :
    1 ≤ gmClassLength ε N k ∧ (gmClassLength ε N k : ℝ) ≤ 8 * T ^ 2 ∧
      ∀ τ : ℝ, |τ| < (2 : ℝ) ^ (k + 1) → |τ| ^ (1 + ε) / N ≤ gmClassLength ε N k := by
  have hN0 : 0 < N := by linarith
  have hx0 : 0 < ((2 : ℝ) ^ (k + 1)) ^ (1 + ε) / N := by positivity
  obtain ⟨_, h4⟩ := classPower_le hε hε1 hT hk
  refine ⟨Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Nat.ceil_pos.mpr hx0)), ?_, ?_⟩
  · have h1 := Nat.ceil_lt_add_one hx0.le
    have h2 : ((2 : ℝ) ^ (k + 1)) ^ (1 + ε) / N ≤ 4 * T ^ 2 :=
      (div_le_self (by positivity) hN).trans h4
    have h3 : (1 : ℝ) ≤ T ^ 2 := one_le_pow₀ hT
    unfold gmClassLength
    linarith
  · intro τ hτ
    refine le_trans ?_ (Nat.le_ceil _)
    exact div_le_div_of_nonneg_right
      (Real.rpow_le_rpow (abs_nonneg τ) hτ.le (by linarith)) hN0.le

/-- In a long class (`N ≤ (2^{k+1})^{1+ε}`), `N · 2^j ≤ N M_k ≤ 4 · 2^k (2T)^ε` for every block
`2^j ≤ M_k`. -/
theorem mul_two_pow_le_of_long {ε N T : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hN : 1 ≤ N)
    (hT : 1 ≤ T) {k : ℕ} (hk : (2 : ℝ) ^ k ≤ T) (hlong : N ≤ ((2 : ℝ) ^ (k + 1)) ^ (1 + ε))
    {j : ℕ} (hj : 2 ^ j ≤ gmClassLength ε N k) :
    N * (2 : ℝ) ^ j ≤ 4 * 2 ^ k * (2 * T) ^ ε := by
  have hN0 : 0 < N := by linarith
  have hx0 : 0 < ((2 : ℝ) ^ (k + 1)) ^ (1 + ε) / N := by positivity
  obtain ⟨h2, _⟩ := classPower_le hε hε1 hT hk
  have h1 := Nat.ceil_lt_add_one hx0.le
  have hj' : (2 : ℝ) ^ j ≤ gmClassLength ε N k := by exact_mod_cast hj
  have hNM : N * (gmClassLength ε N k : ℝ) ≤ 2 * ((2 : ℝ) ^ (k + 1)) ^ (1 + ε) := by
    unfold gmClassLength at h1 ⊢
    have := mul_le_mul_of_nonneg_left h1.le hN0.le
    rw [mul_add, mul_div_cancel₀ _ hN0.ne', mul_one] at this
    linarith
  calc N * (2 : ℝ) ^ j ≤ N * (gmClassLength ε N k : ℝ) :=
        mul_le_mul_of_nonneg_left hj' hN0.le
    _ ≤ 2 * ((2 : ℝ) ^ (k + 1)) ^ (1 + ε) := hNM
    _ ≤ 2 * (2 * 2 ^ k * (2 * T) ^ ε) := by linarith
    _ = 4 * 2 ^ k * (2 * T) ^ ε := by ring

/-- The dyadic-block count: `⌊log₂ M⌋ + 1 ≤ (15 + 4/ε) T^ε` for `1 ≤ M ≤ 8T²`, `T ≥ 1`
(via the corpus `natLog_two_floor_le`: `⌊log₂ M⌋ ≤ 2 log M`). -/
theorem log_count_le {ε T : ℝ} (hε : 0 < ε) (hT : 1 ≤ T) {M : ℕ} (hM1 : 1 ≤ M)
    (hM : (M : ℝ) ≤ 8 * T ^ 2) :
    ((Nat.log 2 M + 1 : ℕ) : ℝ) ≤ (15 + 4 / ε) * T ^ ε := by
  have hT0 : 0 < T := by linarith
  have hTe : 1 ≤ T ^ ε := Real.one_le_rpow hT hε.le
  have hM1' : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hn := Sieve.natLog_two_floor_le hM1'
  rw [Nat.floor_natCast] at hn
  have hlog : Real.log M ≤ Real.log 8 + 2 * Real.log T := by
    have := Real.log_le_log (by positivity) hM
    rwa [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Nat.cast_ofNat] at this
  have hl8 : Real.log 8 ≤ 7 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8)
    linarith
  have hlT : Real.log T ≤ T ^ ε / ε := Real.log_le_rpow_div hT0.le hε
  have h4 : 4 * (T ^ ε / ε) = 4 / ε * T ^ ε := by ring
  push_cast
  nlinarith [div_pos (by norm_num : (0 : ℝ) < 4) hε]

/-- `T^{−100} ≤ T^{−2}` for `T ≥ 1`. -/
theorem rpow_neg_hundred_le_inv_sq {T : ℝ} (hT : 1 ≤ T) : T ^ (-100 : ℝ) ≤ (T ^ 2)⁻¹ := by
  rw [rpow_neg_hundred T (by linarith)]
  exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hT (by norm_num))

/-- **Long pairs.**  From Lemma 6.2 at length `M` (`2^k ≤ |τ|`):
`|A(τ)|² ≤ 4C² U 2^{−k} ∫_{−U}^{U} |D_M(τ+u)|² du + 2C² T^{−200}`. -/
theorem normSq_gmNonzero_le_long (w : CGLRealSmoothBump) {N C T U τ : ℝ} {M k : ℕ}
    (hU : 0 ≤ U) (hk : (2 : ℝ) ^ k ≤ |τ|)
    (h62 : ‖gmNonzero w N τ‖ ≤ C * |τ| ^ (-(1 / 2 : ℝ)) *
      (∫ u in (-U)..U, ‖cglGMHeadPoly M (τ + u)‖) + C * T ^ (-100 : ℝ)) :
    ‖gmNonzero w N τ‖ ^ 2 ≤ 4 * C ^ 2 * U * ((2 : ℝ) ^ k)⁻¹ *
        (∫ u in (-U)..U, ‖cglGMHeadPoly M (τ + u)‖ ^ 2) +
      2 * C ^ 2 * (T ^ (-100 : ℝ)) ^ 2 := by
  have hτ0 : 0 < |τ| := lt_of_lt_of_le (by positivity) hk
  have hD : Continuous fun u => cglGMHeadPoly M (τ + u) :=
    (continuous_cglGMHeadPoly M).comp (by fun_prop)
  have hsq := sq_le_of_lemma62 hD (norm_nonneg _) hU h62
  have hr : (|τ| ^ (-(1 / 2 : ℝ))) ^ 2 ≤ ((2 : ℝ) ^ k)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hτ0.le, show (-(1 / 2 : ℝ)) * ((2 : ℕ) : ℝ) = -1 by
      norm_num, Real.rpow_neg_one]
    exact inv_anti₀ (by positivity) hk
  have hJ : 0 ≤ ∫ u in (-U)..U, ‖cglGMHeadPoly M (τ + u)‖ ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) fun _ _ => by positivity
  calc ‖gmNonzero w N τ‖ ^ 2
      ≤ 2 * C ^ 2 * (|τ| ^ (-(1 / 2 : ℝ))) ^ 2 *
          (2 * U * ∫ u in (-U)..U, ‖cglGMHeadPoly M (τ + u)‖ ^ 2) +
        2 * C ^ 2 * (T ^ (-100 : ℝ)) ^ 2 := hsq
    _ ≤ 2 * C ^ 2 * ((2 : ℝ) ^ k)⁻¹ *
          (2 * U * ∫ u in (-U)..U, ‖cglGMHeadPoly M (τ + u)‖ ^ 2) +
        2 * C ^ 2 * (T ^ (-100 : ℝ)) ^ 2 := by gcongr
    _ = _ := by ring

/-- **Short pairs.**  If `N > |τ|^{1+ε}`, `T^ε ≤ |τ| ≤ T` and `ε²(2j−1) ≥ 1`, then
`N |A(τ)|² ≤ (2(1+Z) A_j)² 4^j` (Lemma 4.3 decay). -/
theorem mul_normSq_gmNonzero_le_short (w : CGLRealSmoothBump) {ε N T τ : ℝ} (hε : 0 < ε)
    (hT : 1 ≤ T) (hN : 1 ≤ N) (htT : T ^ ε ≤ |τ|) (hτT : |τ| ≤ T)
    (hshort : |τ| ^ (1 + ε) < N) {j : ℕ} (hj : 2 ≤ j) (hjε : 1 ≤ ε ^ 2 * (2 * j - 1)) :
    N * ‖gmNonzero w N τ‖ ^ 2 ≤
      (2 * (1 + cglGMInverseSquareMass) *
        (cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump j / (2 * Real.pi) ^ j)) ^ 2 * 4 ^ j := by
  set c : ℝ := 2 * (1 + cglGMInverseSquareMass) *
    (cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump j / (2 * Real.pi) ^ j) with hc
  have hc0 : 0 ≤ c := by
    have := cglGMInverseSquareMass_nonneg
    have := cglSmoothBumpHtAllOrderBudget_nonneg w.toCGLSmoothBump j
    positivity
  have hT0 : 0 < T := by linarith
  have hN0 : 0 < N := by linarith
  have hτ1 : 1 ≤ |τ| := (Real.one_le_rpow hT hε.le).trans htT
  have hτ0 : 0 < |τ| := by linarith
  set ρ : ℝ := (1 + |τ|) / N with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hdec : ‖gmNonzero w N τ‖ ≤ c * ρ ^ j := by
    have h := norm_gmNonzero_le_decay w hN hj τ
    rw [hρ, div_pow]
    calc _ ≤ _ := h
      _ = c * ((1 + |τ|) ^ j / N ^ j) := by rw [hc]; ring
  -- `ρ ≤ 2 / T^{ε²}`
  have hte : T ^ (ε ^ 2) ≤ |τ| ^ ε := by
    rw [sq, Real.rpow_mul hT0.le]
    exact Real.rpow_le_rpow (by positivity) htT hε.le
  have hTe0 : 0 < T ^ (ε ^ 2) := Real.rpow_pos_of_pos hT0 _
  have hρle : ρ ≤ 2 / T ^ (ε ^ 2) := by
    rw [hρ, div_le_div_iff₀ hN0 hTe0]
    have hpow : |τ| * |τ| ^ ε < N := by
      rwa [Real.rpow_add hτ0, Real.rpow_one] at hshort
    calc (1 + |τ|) * T ^ (ε ^ 2) ≤ (2 * |τ|) * |τ| ^ ε := by gcongr; linarith
      _ = 2 * (|τ| * |τ| ^ ε) := by ring
      _ ≤ 2 * N := by linarith
  have hNρ : N * ρ ≤ 2 * T := by
    rw [hρ, mul_div_cancel₀ _ hN0.ne']
    linarith
  -- `ρ^{2j−1} ≤ 2^{2j−1} / T`
  have hpow : ρ ^ (2 * j - 1) ≤ 2 ^ (2 * j - 1) / T := by
    have hexp : (1 : ℝ) ≤ ε ^ 2 * ((2 * j - 1 : ℕ) : ℝ) := by
      have : ((2 * j - 1 : ℕ) : ℝ) = 2 * j - 1 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [this]; exact hjε
    calc ρ ^ (2 * j - 1) ≤ (2 / T ^ (ε ^ 2)) ^ (2 * j - 1) := by gcongr
      _ = 2 ^ (2 * j - 1) / T ^ (ε ^ 2 * ((2 * j - 1 : ℕ) : ℝ)) := by
          rw [div_pow, Real.rpow_mul_natCast hT0.le]
      _ ≤ 2 ^ (2 * j - 1) / T := by
          refine div_le_div_of_nonneg_left (by positivity) hT0 ?_
          calc T = T ^ (1 : ℝ) := (Real.rpow_one T).symm
            _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hT hexp
  have hsplit : ρ ^ (2 * j) = ρ * ρ ^ (2 * j - 1) := by
    rw [← pow_succ']; congr 1; omega
  calc N * ‖gmNonzero w N τ‖ ^ 2 ≤ N * (c * ρ ^ j) ^ 2 := by gcongr
    _ = c ^ 2 * ((N * ρ) * ρ ^ (2 * j - 1)) := by
        rw [mul_pow, ← pow_mul, mul_comm j 2, hsplit]; ring
    _ ≤ c ^ 2 * ((2 * T) * (2 ^ (2 * j - 1) / T)) := by
        gcongr
    _ = c ^ 2 * 4 ^ j := by
        have h4 : (4 : ℝ) ^ j = 2 * 2 ^ (2 * j - 1) := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_succ']
          congr 1; omega
        rw [h4]
        field_simp

end RHTower.GuthMaynard
