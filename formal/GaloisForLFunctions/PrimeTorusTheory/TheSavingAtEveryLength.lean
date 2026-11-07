import GaloisForLFunctions.PrimeTorusTheory.TheMassOfMisalignedPrimes

/-!
# The saving at every length past the Kronecker scale

Words of height `H` trade `ℓ¹` mass against length: order `k` costs length `M ≍ k² log k / log H`. Taking `k ≍ L = log |t|` and
`log H ≍ L^{2-A} log L` reaches length `L^A` for each `1 < A ≤ 2` at the cost of a factor `H^{O(1)}`. Hence

`Σ_{p<N} (1 − cos(t log p))/√p ≥ exp(−L^β)` for `N ≥ 7 L^A`, `β > 2 − A` (`exp_neg_le_sum_primes_critical`).

So at every length past the Kronecker scale the saving against size is smaller than every power of `|t|`
(`rpow_neg_le_sum_primes_critical`).
-/

open Finset Filter Topology Real

namespace GaloisForLFunctions.PrimeTorusTheory

noncomputable section

/-- **Words of height `H` with vanishing low moments**, by pigeonhole on functions into `[0, H]`. -/
theorem exists_word_height {M k H : ℕ}
    (h : ∏ j ∈ range (k + 1), (H * (M + 1).choose (j + 1) + 1) < (H + 1) ^ (M + 1)) :
    ∃ c : ℕ → ℤ, (∀ a, |c a| ≤ H) ∧ (∀ a, M < a → c a = 0) ∧ (∃ a, c a ≠ 0) ∧
      ∀ j ≤ k, binomMoment M c j = 0 := by
  classical
  have hsum : ∀ (f : Fin (M + 1) → Fin (H + 1)) (j : Fin (k + 1)),
      ∑ i : Fin (M + 1), (f i : ℕ) * (i : ℕ).choose (j : ℕ) < H * (M + 1).choose ((j : ℕ) + 1) + 1 := by
    intro f j
    refine Nat.lt_succ_of_le ?_
    rw [← sum_range_choose_eq, Finset.mul_sum, Finset.sum_range]
    refine Finset.sum_le_sum fun i _ => ?_
    exact Nat.mul_le_mul_right _ (Nat.lt_succ_iff.mp (f i).2)
  let F : (Fin (M + 1) → Fin (H + 1)) →
      ((j : Fin (k + 1)) → Fin (H * (M + 1).choose ((j : ℕ) + 1) + 1)) :=
    fun f j => ⟨_, hsum f j⟩
  have hcard : Fintype.card ((j : Fin (k + 1)) → Fin (H * (M + 1).choose ((j : ℕ) + 1) + 1)) <
      Fintype.card (Fin (M + 1) → Fin (H + 1)) := by
    rw [Fintype.card_pi, Fintype.card_fun]
    simp only [Fintype.card_fin]
    rw [Fin.prod_univ_eq_prod_range (fun j => H * (M + 1).choose (j + 1) + 1) (k + 1)]
    exact h
  obtain ⟨f, g, hne, hFg⟩ := Fintype.exists_ne_map_eq_of_card_lt F hcard
  refine ⟨fun a => if h : a < M + 1 then ((f ⟨a, h⟩ : ℕ) : ℤ) - ((g ⟨a, h⟩ : ℕ) : ℤ) else 0,
    ?_, ?_, ?_, ?_⟩
  · intro a
    by_cases ha : a < M + 1
    · simp only [ha, dif_pos]
      have h1 := Nat.lt_succ_iff.mp (f ⟨a, ha⟩).2
      have h2 := Nat.lt_succ_iff.mp (g ⟨a, ha⟩).2
      rw [abs_le]
      constructor <;> omega
    · simp only [ha, dif_neg, not_false_eq_true, abs_zero]
      positivity
  · intro a ha
    have : ¬ a < M + 1 := by omega
    simp [this]
  · by_contra hall
    push Not at hall
    apply hne
    funext i
    have h1 := hall i
    simp only [i.2, dif_pos, Fin.eta] at h1
    exact Fin.ext (by omega)
  · intro j hj
    have hj' : j < k + 1 := Nat.lt_succ_of_le hj
    have e := congrFun hFg ⟨j, hj'⟩
    have e' : ∑ i : Fin (M + 1), (f i : ℕ) * (i : ℕ).choose j =
        ∑ i : Fin (M + 1), (g i : ℕ) * (i : ℕ).choose j := by
      simpa [F] using congrArg Fin.val e
    unfold binomMoment
    rw [Finset.sum_range]
    have e2 : ∀ i : Fin (M + 1), (if h : (i : ℕ) < M + 1 then ((f ⟨i, h⟩ : ℕ) : ℤ) - ((g ⟨i, h⟩ : ℕ) : ℤ)
        else 0) * (((i : ℕ).choose j : ℕ) : ℤ) =
        ((f i : ℕ) : ℤ) * (((i : ℕ).choose j : ℕ) : ℤ) - ((g i : ℕ) : ℤ) * (((i : ℕ).choose j : ℕ) : ℤ) := by
      intro i
      simp only [i.2, dif_pos, Fin.eta]
      ring
    simp only [e2]
    rw [Finset.sum_sub_distrib, sub_eq_zero]
    exact_mod_cast e'

/-- The pigeonhole condition for words of height `H`, in logarithmic form. -/
theorem prod_lt_pow_of_log {M k H : ℕ} (hH : 2 ≤ H) (hk : 4 * (k + 1) ≤ M + 1)
    (h : ((k : ℝ) + 2) ^ 2 * Real.log ((M : ℝ) + 1) ≤ ((M : ℝ) + 1) * Real.log H) :
    ∏ j ∈ range (k + 1), (H * (M + 1).choose (j + 1) + 1) < (H + 1) ^ (M + 1) := by
  have hHr : (2 : ℝ) ≤ H := by exact_mod_cast hH
  have hH0 : (0 : ℝ) < H := by linarith
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hM1 : (1 : ℝ) ≤ (M : ℝ) + 1 := by linarith
  have hlogH : 0 < Real.log H := Real.log_pos (by linarith)
  have hlogM : 0 ≤ Real.log ((M : ℝ) + 1) := Real.log_nonneg hM1
  have hfac : ∀ j : ℕ, ((H * (M + 1).choose (j + 1) + 1 : ℕ) : ℝ) ≤
      2 * (H : ℝ) * ((M : ℝ) + 1) ^ (j + 1) := by
    intro j
    have h1 := choose_mul_factorial_le (M + 1) j
    have hcast : (((M + 1 : ℕ) : ℝ)) = (M : ℝ) + 1 := by push_cast; ring
    rw [hcast] at h1
    have h2 : ((M + 1).choose (j + 1) : ℝ) ≤ ((M : ℝ) + 1) ^ (j + 1) := by
      refine le_trans ?_ h1
      have : (1 : ℝ) ≤ ((j + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
      nlinarith [(Nat.cast_nonneg ((M + 1).choose (j + 1)) : (0 : ℝ) ≤ _)]
    have h3 : (1 : ℝ) ≤ ((M : ℝ) + 1) ^ (j + 1) := one_le_pow₀ hM1
    push_cast
    nlinarith
  have hlogprod : Real.log ((∏ j ∈ range (k + 1), (H * (M + 1).choose (j + 1) + 1) : ℕ) : ℝ) ≤
      ∑ j ∈ range (k + 1), (2 * Real.log H + ((j : ℝ) + 1) * Real.log ((M : ℝ) + 1)) := by
    push_cast
    rw [Real.log_prod (fun j _ => by positivity)]
    refine Finset.sum_le_sum fun j _ => ?_
    have h1 := hfac j
    push_cast at h1
    refine (Real.log_le_log (by positivity) h1).trans ?_
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) hH0.ne',
      Real.log_pow]
    have h2 : Real.log 2 ≤ Real.log H := Real.log_le_log (by norm_num) hHr
    push_cast
    linarith
  have hsum : ∑ j ∈ range (k + 1), (2 * Real.log H + ((j : ℝ) + 1) * Real.log ((M : ℝ) + 1)) =
      2 * ((k : ℝ) + 1) * Real.log H + ((k : ℝ) + 1) * ((k : ℝ) + 2) / 2 * Real.log ((M : ℝ) + 1) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.sum_mul]
    have h2 := two_mul_sum_range_succ k
    have h3 : (2 : ℝ) * ∑ j ∈ range (k + 1), ((j : ℝ) + 1) = ((k : ℝ) + 1) * ((k : ℝ) + 2) := by
      exact_mod_cast h2
    have h4 : ∑ j ∈ range (k + 1), ((j : ℝ) + 1) = ((k : ℝ) + 1) * ((k : ℝ) + 2) / 2 := by linarith
    rw [h4]
    push_cast
    ring
  have hk' : 4 * ((k : ℝ) + 1) ≤ (M : ℝ) + 1 := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have htotal : Real.log ((∏ j ∈ range (k + 1), (H * (M + 1).choose (j + 1) + 1) : ℕ) : ℝ) <
      Real.log (((H + 1) ^ (M + 1) : ℕ) : ℝ) := by
    refine lt_of_le_of_lt (hlogprod.trans (le_of_eq hsum)) ?_
    push_cast
    rw [Real.log_pow]
    have h5 : Real.log H < Real.log ((H : ℝ) + 1) := Real.log_lt_log hH0 (by linarith)
    have h6 : ((k : ℝ) + 1) * ((k : ℝ) + 2) / 2 * Real.log ((M : ℝ) + 1) ≤
        ((M : ℝ) + 1) / 2 * Real.log H := by
      have h7 : ((k : ℝ) + 1) * ((k : ℝ) + 2) ≤ ((k : ℝ) + 2) ^ 2 := by nlinarith
      have h8 : ((k : ℝ) + 1) * ((k : ℝ) + 2) * Real.log ((M : ℝ) + 1) ≤
          ((k : ℝ) + 2) ^ 2 * Real.log ((M : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right h7 hlogM
      linarith
    have h9 : 2 * ((k : ℝ) + 1) * Real.log H ≤ ((M : ℝ) + 1) / 2 * Real.log H :=
      mul_le_mul_of_nonneg_right (by linarith) hlogH.le
    have h10 : ((M : ℝ) + 1) * Real.log H < ((M : ℝ) + 1) * Real.log ((H : ℝ) + 1) :=
      mul_lt_mul_of_pos_left h5 (by linarith)
    push_cast at h10 ⊢
    linarith
  have hpos : (0 : ℝ) < ((∏ j ∈ range (k + 1), (H * (M + 1).choose (j + 1) + 1) : ℕ) : ℝ) := by
    have : 0 < ∏ j ∈ range (k + 1), (H * (M + 1).choose (j + 1) + 1) :=
      Finset.prod_pos fun j _ => Nat.succ_pos _
    exact_mod_cast this
  have := (Real.log_lt_log_iff hpos (by positivity)).mp htotal
  exact_mod_cast this

/-- The size conditions at height `exp L` for length `L^A`, with `ℓ = log L` and `log H ≈ lam = 6 L^{2-A} ℓ`. -/
structure LengthSize (A β L ℓ lam : ℝ) : Prop where
  one_lt_A : 1 < A
  A_le : A ≤ 2
  log_eq : ℓ = Real.log L
  one_le : 1 ≤ ℓ
  hundred_le : 100 ≤ L
  lam_eq : lam = 6 * L ^ (2 - A) * ℓ
  lam_small : 100 * (lam + ℓ + 3) ≤ L
  length : 4 * L + 12 ≤ L ^ A
  final : 30 + 12 * lam + 8 * ℓ ≤ L ^ β

namespace LengthSize

variable {A β L ℓ lam t : ℝ}

theorem exp_eq (h : LengthSize A β L ℓ lam) : Real.exp ℓ = L := by
  rw [h.log_eq, Real.exp_log (by linarith [h.hundred_le])]

theorem rpow_le (h : LengthSize A β L ℓ lam) : L ^ A ≤ L ^ 2 := by
  have h1 := Real.rpow_le_rpow_of_exponent_le (by linarith [h.hundred_le] : 1 ≤ L) h.A_le
  rwa [Real.rpow_two] at h1

theorem lam_pos (h : LengthSize A β L ℓ lam) : 0 < lam := by
  have hL : 0 < L := by linarith [h.hundred_le]
  have hℓ : 0 < ℓ := by linarith [h.one_le]
  rw [h.lam_eq]
  positivity

/-- Bounds for the height `H = ⌈exp lam⌉`. -/
theorem height_bounds (h : LengthSize A β L ℓ lam) {H : ℕ} (hH : H = ⌈Real.exp lam⌉₊) :
    2 ≤ H ∧ lam ≤ Real.log H ∧ (H : ℝ) ≤ 2 * Real.exp lam ∧ 1 ≤ Real.log (3 * (H : ℝ)) ∧
      Real.log (3 * (H : ℝ)) ≤ lam + 3 := by
  have hl := h.lam_pos
  have hexp1 : 1 < Real.exp lam := Real.one_lt_exp_iff.mpr hl
  have h2 : 2 ≤ H := by
    rw [hH]
    have : 1 < ⌈Real.exp lam⌉₊ := Nat.lt_ceil.mpr (by exact_mod_cast hexp1)
    omega
  have hge : Real.exp lam ≤ H := by
    rw [hH]
    exact Nat.le_ceil _
  have hle : (H : ℝ) ≤ 2 * Real.exp lam := by
    have : (H : ℝ) < Real.exp lam + 1 := by
      rw [hH]
      exact Nat.ceil_lt_add_one (Real.exp_pos _).le
    linarith
  have hHpos : (0 : ℝ) < H := by linarith [Real.exp_pos lam]
  have hlogge : lam ≤ Real.log H := by
    rw [Real.le_log_iff_exp_le hHpos]
    exact hge
  have ha2 := Real.log_two_lt_d9
  have hlogle : Real.log H ≤ lam + 1 := by
    have h3 := Real.log_le_log hHpos hle
    rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at h3
    linarith
  have hlog3 : Real.log 3 ≤ 2 := by
    have : Real.log 3 ≤ 3 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  have hlog31 : 1 ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have := Real.exp_one_lt_d9
    linarith
  have hsplit : Real.log (3 * (H : ℝ)) = Real.log 3 + Real.log H :=
    Real.log_mul (by norm_num) hHpos.ne'
  have hlogHnn : 0 ≤ Real.log H := by linarith
  exact ⟨h2, hlogge, hle, by rw [hsplit]; linarith, by rw [hsplit]; linarith⟩

/-- The pigeonhole condition at the chosen parameters. -/
theorem word (h : LengthSize A β L ℓ lam) {M k H : ℕ} (hH : H = ⌈Real.exp lam⌉₊)
    (hM1 : L ^ A ≤ M) (hM2 : (M : ℝ) ≤ L ^ A + 1) (hk : (k : ℝ) ≤ L + 1) :
    ∏ j ∈ range (k + 1), (H * (M + 1).choose (j + 1) + 1) < (H + 1) ^ (M + 1) := by
  obtain ⟨h2, hlog, -, -, -⟩ := h.height_bounds hH
  have hL := h.hundred_le
  have hℓ := h.one_le
  have hL0 : 0 < L := by linarith
  have hlen := h.length
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  refine prod_lt_pow_of_log h2 ?_ ?_
  · have : (((4 * (k + 1) : ℕ)) : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast this
  · have hM3 : (M : ℝ) + 1 ≤ L ^ 3 := by
      have h1 := h.rpow_le
      have h3 : L ^ 3 = L ^ 2 * L := by ring
      have h4 : 0 < L ^ 2 := by positivity
      nlinarith
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    have hlogM : Real.log ((M : ℝ) + 1) ≤ 3 * ℓ := by
      have h1 := Real.log_le_log (by linarith) hM3
      rw [Real.log_pow] at h1
      rw [h.log_eq]
      exact_mod_cast h1
    have hlogM0 : 0 ≤ Real.log ((M : ℝ) + 1) := Real.log_nonneg (by linarith)
    have hsq : ((k : ℝ) + 2) ^ 2 ≤ 2 * L ^ 2 := by nlinarith
    have hprod : L ^ A * lam = 6 * L ^ 2 * ℓ := by
      rw [h.lam_eq]
      have e : L ^ A * L ^ (2 - A) = L ^ 2 := by
        rw [← Real.rpow_add hL0, add_sub_cancel, Real.rpow_two]
      calc L ^ A * (6 * L ^ (2 - A) * ℓ) = 6 * (L ^ A * L ^ (2 - A)) * ℓ := by ring
        _ = _ := by rw [e]
    have hl := h.lam_pos
    calc ((k : ℝ) + 2) ^ 2 * Real.log ((M : ℝ) + 1) ≤ 2 * L ^ 2 * (3 * ℓ) :=
          mul_le_mul hsq hlogM hlogM0 (by positivity)
      _ = L ^ A * lam := by rw [hprod]; ring
      _ ≤ ((M : ℝ) + 1) * Real.log H :=
          mul_le_mul (by linarith) hlog hl.le (by linarith)

theorem pow_three_mul_eq {H : ℕ} (hH : 2 ≤ H) (n : ℕ) :
    (3 * (H : ℝ)) ^ n = Real.exp ((n : ℝ) * Real.log (3 * (H : ℝ))) := by
  have : (0 : ℝ) < 3 * (H : ℝ) := by
    have : (0 : ℝ) < H := by exact_mod_cast (by omega : 0 < H)
    positivity
  rw [Real.exp_nat_mul, Real.exp_log this]

/-- A word of height `H` at height `exp L`. -/
theorem exists_setup (h : LengthSize A β L ℓ lam) (hexp : Real.exp L = |t|) {M k H N : ℕ}
    (hH : H = ⌈Real.exp lam⌉₊) (hM1 : L ^ A ≤ M) (hM2 : (M : ℝ) ≤ L ^ A + 1) (hk1 : L ≤ k)
    (hk2 : (k : ℝ) ≤ L + 1) (hN : N = ⌊L / (2 * Real.log (3 * (H : ℝ)))⌋₊) :
    ∃ c, WordSetup (H : ℝ) ((3 * (H : ℝ)) ^ 4) M k N c t := by
  obtain ⟨h2, -, -, hΛ1, hΛ2⟩ := h.height_bounds hH
  obtain ⟨c₀, hc₀, hsup, hne, hm⟩ := exists_word_height (h.word hH hM1 hM2 hk2)
  obtain ⟨ν, hν, hm'⟩ := exists_shift_zero_ne hsup hne hm
  have hL := h.hundred_le
  have hℓ := h.one_le
  have hsmall := h.lam_small
  have hl := h.lam_pos
  have hHr : (2 : ℝ) ≤ H := by exact_mod_cast h2
  have hH0 : (0 : ℝ) < H := by linarith
  set Λ := Real.log (3 * (H : ℝ)) with hΛ
  have hexpΛ : Real.exp Λ = 3 * (H : ℝ) := Real.exp_log (by positivity)
  have hNle : (N : ℝ) ≤ L / (2 * Λ) := by
    rw [hN]
    exact Nat.floor_le (by positivity)
  have hNge : L / (2 * Λ) - 1 ≤ (N : ℝ) := by
    have : L / (2 * Λ) < (N : ℝ) + 1 := by
      rw [hN]
      exact Nat.lt_floor_add_one _
    linarith
  have hNΛ : (N : ℝ) * Λ ≤ L / 2 := by
    have : (N : ℝ) * Λ ≤ L / (2 * Λ) * Λ := mul_le_mul_of_nonneg_right hNle (by linarith)
    have e : L / (2 * Λ) * Λ = L / 2 := by
      field_simp
    linarith
  have hNΛ2 : L / 2 - Λ ≤ (N : ℝ) * Λ := by
    have : (L / (2 * Λ) - 1) * Λ ≤ (N : ℝ) * Λ := mul_le_mul_of_nonneg_right hNge (by linarith)
    have e : (L / (2 * Λ) - 1) * Λ = L / 2 - Λ := by
      field_simp
    linarith
  have hHexp : (H : ℝ) ≤ Real.exp Λ := by
    rw [hexpΛ]
    linarith
  have hM3 : (M : ℝ) + 1 ≤ Real.exp (3 * ℓ) := by
    have e : Real.exp (3 * ℓ) = L ^ 3 := by
      have := Real.exp_nat_mul ℓ 3
      push_cast at this
      rw [this, h.exp_eq]
    rw [e]
    have h1 := h.rpow_le
    have h3 : L ^ 3 = L ^ 2 * L := by ring
    have h4 : 0 < L ^ 2 := by positivity
    nlinarith
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hN1 : 1 ≤ N := by
    have h5 : 1 ≤ L / (2 * Λ) := by
      rw [le_div_iff₀ (by linarith)]
      linarith
    rw [hN]
    exact Nat.le_floor (by push_cast; exact h5)
  refine ⟨fun a => c₀ (a + ν), ⟨by linarith, ?_, fun a => ?_, hm', hν, hN1, ?_, ?_, ?_⟩⟩
  · exact one_le_pow₀ (by linarith)
  · exact_mod_cast hc₀ (a + ν)
  · -- low
    rw [← hexp]
    have hπ := Real.pi_lt_four
    have hπ0 := Real.pi_pos
    have hN2 : (N : ℝ) ≤ L / 2 := by
      have : (N : ℝ) * 1 ≤ (N : ℝ) * Λ :=
        mul_le_mul_of_nonneg_left hΛ1 (Nat.cast_nonneg N)
      linarith
    have h3 : (3 * (H : ℝ)) ^ (N + 2) ≤ Real.exp (L / 2 + 2 * Λ) := by
      rw [pow_three_mul_eq h2]
      refine Real.exp_le_exp.mpr ?_
      push_cast
      nlinarith
    have h4 : 4 * ((N : ℝ) + 2) * π ≤ Real.exp (3 + ℓ) := by
      rw [Real.exp_add, h.exp_eq]
      have e3 : (16 : ℝ) ≤ Real.exp 3 := by
        have he := Real.exp_one_gt_d9
        have : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
        rw [this]
        have h1 : (2.7 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) (by linarith) 3
        linarith [show (16 : ℝ) ≤ 2.7 ^ 3 by norm_num]
      have h5 : (N : ℝ) + 2 ≤ L := by linarith
      calc 4 * ((N : ℝ) + 2) * π ≤ 4 * L * 4 := by
            refine mul_le_mul (by linarith) hπ.le hπ0.le (by linarith)
        _ = 16 * L := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right e3 (by linarith)
    calc 4 * ((N : ℝ) + 2) * (3 * (H : ℝ)) ^ (N + 2) * π =
        (4 * ((N : ℝ) + 2) * π) * (3 * (H : ℝ)) ^ (N + 2) := by ring
      _ ≤ Real.exp (3 + ℓ) * Real.exp (L / 2 + 2 * Λ) :=
          mul_le_mul h4 h3 (by positivity) (Real.exp_pos _).le
      _ = Real.exp (3 + ℓ + (L / 2 + 2 * Λ)) := (Real.exp_add _ _).symm
      _ ≤ Real.exp L := Real.exp_le_exp.mpr (by linarith)
  · -- step
    rw [← hexp]
    have hπ : (1 : ℝ) ≤ π := by linarith [Real.pi_gt_three]
    have e1 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.exp_one_gt_d9
      linarith
    have hH2 : (H : ℝ) ^ 2 ≤ Real.exp (2 * Λ) := by
      have := pow_le_pow_left₀ hH0.le hHexp 2
      rwa [← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * Λ = 2 * Λ by norm_num] at this
    have hM33 : ((M : ℝ) + 1) ^ 3 ≤ Real.exp (9 * ℓ) := by
      have := pow_le_pow_left₀ (by linarith) hM3 3
      have e : Real.exp (3 * ℓ) ^ 3 = Real.exp (9 * ℓ) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      rwa [e] at this
    have hpow : ((3 * (H : ℝ)) ^ 4) ^ N = Real.exp ((N : ℝ) * (4 * Λ)) := by
      rw [← pow_mul, pow_three_mul_eq h2]
      congr 1
      push_cast
      ring
    calc Real.exp L * (2 * (H : ℝ) ^ 2 * ((M : ℝ) + 1) ^ 3)
        ≤ Real.exp L * (Real.exp 1 * Real.exp (2 * Λ) * Real.exp (9 * ℓ)) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
          exact mul_le_mul (mul_le_mul e1 hH2 (by positivity) (Real.exp_pos _).le) hM33
            (by positivity) (by positivity)
      _ = Real.exp (L + (1 + 2 * Λ + 9 * ℓ)) := by
          rw [Real.exp_add, Real.exp_add, Real.exp_add]
      _ ≤ Real.exp ((N : ℝ) * (4 * Λ)) := by
          refine Real.exp_le_exp.mpr ?_
          nlinarith
      _ = ((3 * (H : ℝ)) ^ 4) ^ N := hpow.symm
      _ ≤ _ := le_mul_of_one_le_left (by positivity) hπ
  · -- up
    rw [← hexp]
    have hπ : (1 : ℝ) < π := by linarith [Real.pi_gt_three]
    have ha1 := Real.log_two_gt_d9
    have hH2 : (H : ℝ) ^ 2 ≤ Real.exp (2 * Λ) := by
      have := pow_le_pow_left₀ hH0.le hHexp 2
      rwa [← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * Λ = 2 * Λ by norm_num] at this
    have hM22 : ((M : ℝ) + 1) ^ 2 ≤ Real.exp (6 * ℓ) := by
      have := pow_le_pow_left₀ (by linarith) hM3 2
      have e : Real.exp (3 * ℓ) ^ 2 = Real.exp (6 * ℓ) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      rwa [e] at this
    calc Real.exp L * ((H : ℝ) ^ 2 * ((M : ℝ) + 1) ^ 2)
        ≤ Real.exp L * (Real.exp (2 * Λ) * Real.exp (6 * ℓ)) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
          exact mul_le_mul hH2 hM22 (by positivity) (Real.exp_pos _).le
      _ = Real.exp (L + (2 * Λ + 6 * ℓ)) := by rw [Real.exp_add, Real.exp_add]
      _ ≤ Real.exp ((k : ℝ) * (2 * Real.log 2)) := by
          refine Real.exp_le_exp.mpr ?_
          have h3 : L * (2 * Real.log 2) ≤ (k : ℝ) * (2 * Real.log 2) :=
            mul_le_mul_of_nonneg_right hk1 (by linarith)
          nlinarith
      _ = 4 ^ k := (four_pow_eq k).symm
      _ < π * 4 ^ k := lt_mul_of_one_lt_left (by positivity) hπ

end LengthSize

/-- The size conditions hold at every large `L`. -/
theorem eventually_lengthSize {A β : ℝ} (hA1 : 1 < A) (hA2 : A ≤ 2) (hβ : 2 - A < β) :
    ∀ᶠ L : ℝ in atTop, LengthSize A β L (Real.log L) (6 * L ^ (2 - A) * Real.log L) := by
  have hr1 : 0 < A - 1 := by linarith
  have hr2 : 0 < β - (2 - A) := by linarith
  have hβ0 : 0 < β := by linarith
  have h1 := (isLittleO_log_rpow_atTop hr1).bound (show (0 : ℝ) < 1 / 1000 by norm_num)
  have h2 := Real.isLittleO_log_id_atTop.bound (show (0 : ℝ) < 1 / 1000 by norm_num)
  have h4 := (isLittleO_log_rpow_atTop hr2).bound (show (0 : ℝ) < 1 / 288 by norm_num)
  have h3 := (tendsto_rpow_atTop hr1).eventually_ge_atTop (5 : ℝ)
  have h5 := (tendsto_rpow_atTop hβ0).eventually_ge_atTop (120 : ℝ)
  have h6 := Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)
  filter_upwards [h1, h2, h3, h4, h5, h6, eventually_ge_atTop (3000 : ℝ)] with x hx1 hx2 hx3 hx4 hx5
    hx6 hx7
  have hx0 : 0 < x := by linarith
  have hlogpos : 0 < Real.log x := by linarith
  simp only [id, Real.norm_eq_abs, abs_of_pos hlogpos, abs_of_pos hx0,
    abs_of_pos (Real.rpow_pos_of_pos hx0 _)] at hx1 hx2 hx4
  have hp : 0 < x ^ (2 - A) := Real.rpow_pos_of_pos hx0 _
  have hp1 : 1 ≤ x ^ (2 - A) := Real.one_le_rpow (by linarith) (by linarith)
  have e1 : x ^ (2 - A) * x ^ (A - 1) = x := by
    rw [← Real.rpow_add hx0, show 2 - A + (A - 1) = 1 by ring, Real.rpow_one]
  have e2 : x ^ (2 - A) * x ^ (β - (2 - A)) = x ^ β := by
    rw [← Real.rpow_add hx0, show 2 - A + (β - (2 - A)) = β by ring]
  have e3 : x ^ A = x * x ^ (A - 1) := by
    have h7 := Real.rpow_add_one hx0.ne' (A - 1)
    rw [sub_add_cancel] at h7
    rw [h7]
    ring
  have hmul1 : x ^ (2 - A) * Real.log x ≤ 1 / 1000 * x := by
    calc x ^ (2 - A) * Real.log x ≤ x ^ (2 - A) * (1 / 1000 * x ^ (A - 1)) :=
          mul_le_mul_of_nonneg_left hx1 hp.le
      _ = 1 / 1000 * (x ^ (2 - A) * x ^ (A - 1)) := by ring
      _ = _ := by rw [e1]
  have hmul2 : x ^ (2 - A) * Real.log x ≤ 1 / 288 * x ^ β := by
    calc x ^ (2 - A) * Real.log x ≤ x ^ (2 - A) * (1 / 288 * x ^ (β - (2 - A))) :=
          mul_le_mul_of_nonneg_left hx4 hp.le
      _ = 1 / 288 * (x ^ (2 - A) * x ^ (β - (2 - A))) := by ring
      _ = _ := by rw [e2]
  have hlogle : Real.log x ≤ x ^ (2 - A) * Real.log x := le_mul_of_one_le_left hlogpos.le hp1
  refine ⟨hA1, hA2, rfl, hx6, by linarith, rfl, ?_, ?_, ?_⟩
  · nlinarith
  · rw [e3]
    nlinarith
  · nlinarith

/-- The word at height `exp L`, with the size of its mass. -/
theorem LengthSize.exists_word_data {A β L ℓ lam t : ℝ} (h : LengthSize A β L ℓ lam)
    (hexp : Real.exp L = |t|) {N : ℕ} (hN : 7 * L ^ A ≤ N) :
    ∃ (H R : ℝ) (M k N₁ : ℕ) (c : ℕ → ℤ), WordSetup H R M k N₁ c t ∧ 6 * M + 6 ≤ N ∧
      96 * R * H ^ 2 * ((M : ℝ) + 1) ^ 2 ≤ Real.exp (15 + 6 * lam + 4 * ℓ) := by
  have hL := h.hundred_le
  have hℓ := h.one_le
  have hlam := h.lam_pos
  have hlen := h.length
  have hrp := h.rpow_le
  set M := ⌈L ^ A⌉₊ with hM
  set k := ⌈L⌉₊ with hk
  set H := ⌈Real.exp lam⌉₊ with hH
  set N₁ := ⌊L / (2 * Real.log (3 * (H : ℝ)))⌋₊ with hN₁
  have hLA : 0 < L ^ A := Real.rpow_pos_of_pos (by linarith) _
  have hM1 : L ^ A ≤ M := Nat.le_ceil _
  have hM2 : (M : ℝ) ≤ L ^ A + 1 := (Nat.ceil_lt_add_one hLA.le).le
  have hk1 : L ≤ k := Nat.le_ceil _
  have hk2 : (k : ℝ) ≤ L + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  obtain ⟨c, hS⟩ := h.exists_setup hexp hH hM1 hM2 hk1 hk2 hN₁
  have hNnat : 6 * M + 6 ≤ N := by
    have : ((6 * M + 6 : ℕ) : ℝ) ≤ N := by
      push_cast
      linarith
    exact_mod_cast this
  refine ⟨H, (3 * (H : ℝ)) ^ 4, M, k, N₁, c, hS, hNnat, ?_⟩
  obtain ⟨h2, -, hHle, -, -⟩ := h.height_bounds hH
  have hHr : (2 : ℝ) ≤ H := by exact_mod_cast h2
  have hH0 : (0 : ℝ) < H := by linarith
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hHpow : (3 * (H : ℝ)) ^ 4 * (H : ℝ) ^ 2 ≤ 5184 * Real.exp (6 * lam) := by
    have h6 : (H : ℝ) ^ 6 ≤ (2 * Real.exp lam) ^ 6 := pow_le_pow_left₀ hH0.le hHle 6
    have e : (2 * Real.exp lam) ^ 6 = 64 * Real.exp (6 * lam) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      norm_num
    rw [e] at h6
    calc (3 * (H : ℝ)) ^ 4 * (H : ℝ) ^ 2 = 81 * (H : ℝ) ^ 6 := by ring
      _ ≤ 81 * (64 * Real.exp (6 * lam)) := mul_le_mul_of_nonneg_left h6 (by norm_num)
      _ = _ := by ring
  have hMsq : ((M : ℝ) + 1) ^ 2 ≤ 4 * Real.exp (4 * ℓ) := by
    have e : Real.exp (4 * ℓ) = L ^ 4 := by
      have := Real.exp_nat_mul ℓ 4
      push_cast at this
      rw [this, h.exp_eq]
    rw [e]
    have h7 : (M : ℝ) + 1 ≤ 2 * L ^ 2 := by nlinarith
    calc ((M : ℝ) + 1) ^ 2 ≤ (2 * L ^ 2) ^ 2 := pow_le_pow_left₀ (by linarith) h7 2
      _ = _ := by ring
  have hconst : (1990656 : ℝ) ≤ Real.exp 15 := by
    have he := Real.exp_one_gt_d9
    have : Real.exp 15 = Real.exp 1 ^ 15 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    have h1 : (2.7 : ℝ) ^ 15 ≤ Real.exp 1 ^ 15 := pow_le_pow_left₀ (by norm_num) (by linarith) 15
    linarith [show (1990656 : ℝ) ≤ 2.7 ^ 15 by norm_num]
  calc 96 * (3 * (H : ℝ)) ^ 4 * (H : ℝ) ^ 2 * ((M : ℝ) + 1) ^ 2 =
      96 * ((3 * (H : ℝ)) ^ 4 * (H : ℝ) ^ 2) * ((M : ℝ) + 1) ^ 2 := by ring
    _ ≤ 96 * (5184 * Real.exp (6 * lam)) * (4 * Real.exp (4 * ℓ)) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hHpow (by norm_num)) hMsq (by positivity)
          (by positivity)
    _ = 1990656 * (Real.exp (6 * lam) * Real.exp (4 * ℓ)) := by ring
    _ ≤ Real.exp 15 * (Real.exp (6 * lam) * Real.exp (4 * ℓ)) :=
        mul_le_mul_of_nonneg_right hconst (by positivity)
    _ = _ := by rw [Real.exp_add, Real.exp_add]; ring

/-- **The saving at every length.** For `1 < A ≤ 2` and `β > 2 − A`, with `L = log |t|`, every `N ≥ 7 L^A` has
`Σ_{p<N} (1 − cos(t log p))/√p ≥ exp(−L^β)`. -/
theorem exp_neg_le_sum_primes_critical {A β : ℝ} (hA1 : 1 < A) (hA2 : A ≤ 2) (hβ : 2 - A < β) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ t : ℝ, T₀ ≤ |t| → ∀ N : ℕ, 7 * Real.log |t| ^ A ≤ N →
      Real.exp (-Real.log |t| ^ β) ≤
        ∑ p ∈ N.primesBelow, (1 - Real.cos (t * Real.log p)) / √(p : ℝ) := by
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp (eventually_lengthSize hA1 hA2 hβ)
  refine ⟨Real.exp L₀, Real.exp_pos _, fun t ht N hN => ?_⟩
  have htpos : 0 < |t| := lt_of_lt_of_le (Real.exp_pos _) ht
  have hLge : L₀ ≤ Real.log |t| := by
    rw [Real.le_log_iff_exp_le htpos]
    exact ht
  have h := hL₀ _ hLge
  have hexp : Real.exp (Real.log |t|) = |t| := Real.exp_log htpos
  generalize Real.log |t| = L at h hexp hN ⊢
  generalize 6 * L ^ (2 - A) * Real.log L = lam at h
  generalize Real.log L = ℓ at h
  obtain ⟨H, R, M, k, N₁, c, hS, hNnat, hden⟩ := h.exists_word_data hexp hN
  have hmass := hS.one_div_le_sum_primes hNnat
  have hcol := four_mul_sq_le_critical t N
  set P : ℝ := ∑ p ∈ N.primesBelow, phaseDist t p / p with hP
  have hH0 : 0 < H := by linarith [hS.one_le_H]
  have hR0 : 0 < R := by linarith [hS.one_le_R]
  have hPlow : Real.exp (-(15 + 6 * lam + 4 * ℓ)) ≤ P := by
    refine le_trans ?_ hmass
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by positivity) hden
  have hsq := pow_le_pow_left₀ (Real.exp_pos _).le hPlow 2
  have e : Real.exp (-(15 + 6 * lam + 4 * ℓ)) ^ 2 = Real.exp (-(30 + 12 * lam + 8 * ℓ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [e] at hsq
  have hfin : Real.exp (-L ^ β) ≤ Real.exp (-(30 + 12 * lam + 8 * ℓ)) :=
    Real.exp_le_exp.mpr (by linarith [h.final])
  have hpos := Real.exp_pos (-(30 + 12 * lam + 8 * ℓ))
  linarith

/-- **At every length past the Kronecker scale the saving against size beats every power of `|t|`.** For `A > 1` and `δ > 0`, every
`N ≥ (log |t|)^A` has `Σ_{p<N} (1 − cos(t log p))/√p ≥ |t|^{-δ}`. -/
theorem rpow_neg_le_sum_primes_critical {A δ : ℝ} (hA : 1 < A) (hδ : 0 < δ) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ t : ℝ, T₀ ≤ |t| → ∀ N : ℕ, Real.log |t| ^ A ≤ N →
      |t| ^ (-δ) ≤ ∑ p ∈ N.primesBelow, (1 - Real.cos (t * Real.log p)) / √(p : ℝ) := by
  set A' : ℝ := (1 + min A 2) / 2 with hA'
  have hmin1 : 1 < min A 2 := lt_min hA (by norm_num)
  have hmin2 : min A 2 ≤ A := min_le_left _ _
  have hmin3 : min A 2 ≤ 2 := min_le_right _ _
  have hA'1 : 1 < A' := by rw [hA']; linarith
  have hA'2 : A' ≤ 2 := by rw [hA']; linarith
  have hA'A : A' < A := by rw [hA']; linarith
  set β : ℝ := (3 - A') / 2 with hβ
  have hβ1 : 2 - A' < β := by rw [hβ]; linarith
  have hβ2 : β < 1 := by rw [hβ]; linarith
  have hβ0 : 0 < β := by linarith
  obtain ⟨T₁, hT₁, hmain⟩ := exp_neg_le_sum_primes_critical hA'1 hA'2 hβ1
  have hev1 := (tendsto_rpow_atTop (show 0 < A - A' by linarith)).eventually_ge_atTop (7 : ℝ)
  have hev2 := (tendsto_rpow_atTop (show 0 < 1 - β by linarith)).eventually_ge_atTop (1 / δ)
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp (hev1.and (hev2.and (eventually_gt_atTop (0 : ℝ))))
  refine ⟨max T₁ (Real.exp L₀), lt_of_lt_of_le hT₁ (le_max_left _ _), fun t ht N hN => ?_⟩
  have ht1 : T₁ ≤ |t| := (le_max_left _ _).trans ht
  have ht2 : Real.exp L₀ ≤ |t| := (le_max_right _ _).trans ht
  have htpos : 0 < |t| := lt_of_lt_of_le hT₁ ht1
  have hLge : L₀ ≤ Real.log |t| := by
    rw [Real.le_log_iff_exp_le htpos]
    exact ht2
  obtain ⟨h7, h1δ, hLpos⟩ := hL₀ _ hLge
  set L := Real.log |t| with hL
  have hLA' : 0 < L ^ A' := Real.rpow_pos_of_pos hLpos _
  have h7N : 7 * L ^ A' ≤ N := by
    refine le_trans ?_ hN
    have e : L ^ A = L ^ (A - A') * L ^ A' := by
      rw [← Real.rpow_add hLpos, sub_add_cancel]
    rw [e]
    exact mul_le_mul_of_nonneg_right h7 hLA'.le
  refine le_trans ?_ (hmain t ht1 N h7N)
  have e : |t| ^ (-δ) = Real.exp (-δ * L) := by
    rw [Real.rpow_def_of_pos htpos, ← hL]
    ring_nf
  rw [e]
  refine Real.exp_le_exp.mpr ?_
  have hLβ : 0 < L ^ β := Real.rpow_pos_of_pos hLpos _
  have e2 : L = L ^ (1 - β) * L ^ β := by
    rw [← Real.rpow_add hLpos, sub_add_cancel, Real.rpow_one]
  have h8 : L ^ β ≤ δ * L := by
    have h9 : (1 / δ) * L ^ β ≤ L ^ (1 - β) * L ^ β := mul_le_mul_of_nonneg_right h1δ hLβ.le
    rw [← e2] at h9
    have h10 : δ * ((1 / δ) * L ^ β) ≤ δ * L := mul_le_mul_of_nonneg_left h9 hδ.le
    have e3 : δ * ((1 / δ) * L ^ β) = L ^ β := by
      field_simp
    linarith
  linarith

end

end GaloisForLFunctions.PrimeTorusTheory
