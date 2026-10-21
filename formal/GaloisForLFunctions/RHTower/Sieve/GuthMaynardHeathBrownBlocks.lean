import GaloisForLFunctions.RHTower.Sieve.HeathBrownPairSumSmallBlock
import GaloisForLFunctions.RHTower.Sieve.GuthMaynardHeathBrownStatement

set_option autoImplicit false

/-!
# Heath-Brown's theorem in the two block ranges used by Guth–Maynard §11

The corpus proves Heath-Brown's pair-sum theorem unconditionally for short blocks
(`Sieve.sum_sum_norm_sq_exp_le_smallBlock`, `M² ≤ (2T)^{2/3}`, in particular `M ≤ T^{1/4}`) and
for long blocks (`Sieve.hbPairSum_Ioc_le_of_twoThirds`, `2T < N²`, `4T² ≤ 9N³`), with explicit
factors that are polylogarithmic in `T` times a divisor-bound constant `(C_δ X^δ)^k`. Here these
factors are shown to be `O_ε(T^ε)`, which puts both theorems into the per-block form
`HeathBrownBlockBound N T (C T^ε)`:

* `exists_heathBrownBlockBound_short`: every `1 ≤ N ≤ T^{1/4}` (the blocks `M = N/d`,
  `d ≥ N²/T`, of Guth–Maynard Lemma 11.9 when `N ≥ T^{3/4}`);
* `exists_heathBrownBlockBound_long`: every `T^{2/3} ≤ N ≤ T` (Lemma 1.5); for `T ≤ 8` the
  trivial bound `|𝒯|² N²` is used.

The middle range `T^{1/4} < N < T^{2/3}` is not covered; the §11 chain does not need it.
-/

open Finset

namespace RHTower.GuthMaynard

noncomputable section

/-! ### Polylogarithmic and divisor-bound factors are `O(T^ε)` -/

/-- `1 + log₂ T ≤ (1 + 1/(η log 2)) T^η` for `T ≥ 1`, `η > 0`. -/
theorem one_add_logb_two_le_rpow {η : ℝ} (hη : 0 < η) {T : ℝ} (hT : 1 ≤ T) :
    1 + Real.logb 2 T ≤ (1 + 1 / (η * Real.log 2)) * T ^ η := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hTη : 1 ≤ T ^ η := Real.one_le_rpow hT hη.le
  have hl : Real.log T ≤ T ^ η / η := Real.log_le_rpow_div (by linarith) hη
  have h : Real.logb 2 T ≤ T ^ η / (η * Real.log 2) := by
    rw [Real.logb, div_le_div_iff₀ hlog2 (by positivity)]
    rw [le_div_iff₀ hη] at hl
    nlinarith
  calc 1 + Real.logb 2 T ≤ T ^ η + T ^ η / (η * Real.log 2) := by linarith
    _ = (1 + 1 / (η * Real.log 2)) * T ^ η := by ring

/-- The reflection and dual factors of the corpus bounds are `O_η(T^η)`. -/
theorem exists_hbReflFactor_add_hbDualFactor_le {η : ℝ} (hη : 0 < η) :
    ∃ K, 0 ≤ K ∧ ∀ T : ℝ, 1 ≤ T → Sieve.hbReflFactor T + Sieve.hbDualFactor T + 1 ≤ K * T ^ η := by
  set c : ℝ := 1 + 1 / (η / 6 * Real.log 2)
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hc : 1 ≤ c := by
    have : 0 ≤ 1 / (η / 6 * Real.log 2) := by positivity
    linarith
  set h := Sieve.hbReflConst
  set A : ℝ := 2 + 60 * h ^ 2 + 1200000 ^ 2 * 81
  refine ⟨A * c ^ 6, by positivity, fun T hT => ?_⟩
  set L := 1 + Real.logb 2 T with hLdef
  have hL1 : 1 ≤ L := by have := Real.logb_nonneg (b := 2) (by norm_num) hT; linarith
  have hLc : L ≤ c * T ^ (η / 6) := one_add_logb_two_le_rpow (by positivity) hT
  have hT0 : 0 ≤ T := by linarith
  have hL6 : L ^ 6 ≤ c ^ 6 * T ^ η := by
    calc L ^ 6 ≤ (c * T ^ (η / 6)) ^ 6 := pow_le_pow_left₀ (by linarith) hLc 6
      _ = c ^ 6 * T ^ η := by
        rw [mul_pow, ← Real.rpow_natCast (T ^ (η / 6)), ← Real.rpow_mul hT0]
        norm_num
  have hrefl : Sieve.hbReflFactor T ≤ 1 + 60 * h ^ 2 * L ^ 3 := by
    rw [Sieve.hbReflFactor, ← hLdef]
    have hh : 0 ≤ h ^ 2 := sq_nonneg _
    have hq : (1 + L) ^ 2 + 1 ≤ 5 * L ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ 12 * h ^ 2 * L)
    nlinarith
  have hdual : Sieve.hbDualFactor T = 1200000 ^ 2 * 81 * L ^ 6 := by
    rw [Sieve.hbDualFactor, ← hLdef]; ring
  have hL36 : L ^ 3 ≤ L ^ 6 := pow_le_pow_right₀ hL1 (by norm_num)
  have h16 : 1 ≤ L ^ 6 := one_le_pow₀ hL1
  calc Sieve.hbReflFactor T + Sieve.hbDualFactor T + 1
      ≤ 1 + 60 * h ^ 2 * L ^ 3 + 1200000 ^ 2 * 81 * L ^ 6 + 1 := by rw [hdual]; linarith
    _ ≤ A * L ^ 6 := by
        have : 60 * h ^ 2 * L ^ 3 ≤ 60 * h ^ 2 * L ^ 6 :=
          mul_le_mul_of_nonneg_left hL36 (by positivity)
        simp only [A]
        nlinarith
    _ ≤ A * (c ^ 6 * T ^ η) := mul_le_mul_of_nonneg_left hL6 (by positivity)
    _ = A * c ^ 6 * T ^ η := by ring

/-- `(C_δ X^δ)^k = C_δ^k X^{kδ}`, bounded by `C_δ^k (aT)^{kδ}` when `X ≤ aT`. -/
theorem divisorFactor_pow_le {δ : ℝ} (hδ : 0 < δ) {X a T : ℝ} (hX : 0 ≤ X) (hXT : X ≤ a * T)
    (k : ℕ) :
    (Sieve.divisorBoundConst δ * X ^ δ) ^ k ≤
      Sieve.divisorBoundConst δ ^ k * ((a * T) ^ δ) ^ k := by
  rw [mul_pow]
  have hD := (Sieve.divisorBoundConst_pos hδ).le
  gcongr

/-- **The short-block constant is `O_ε(T^ε)`.** -/
theorem exists_hbSmallConst_le {ε : ℝ} (hε : 0 < ε) :
    ∃ δ, 0 < δ ∧ ∃ C, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T → Sieve.hbSmallConst T δ ≤ C * T ^ ε := by
  set δ : ℝ := ε / 20
  have hδ : 0 < δ := by positivity
  obtain ⟨K, hK, hKb⟩ := exists_hbReflFactor_add_hbDualFactor_le (η := ε / 2) (by positivity)
  set D := Sieve.divisorBoundConst δ
  have hD : 0 ≤ D := (Sieve.divisorBoundConst_pos hδ).le
  refine ⟨δ, hδ, 3584 * (D ^ 10 * (32 : ℝ) ^ (ε / 2) + 1) * K, by positivity, fun T hT => ?_⟩
  have hT0 : 0 ≤ T := by linarith
  have hTε2 : 1 ≤ T ^ (ε / 2) := Real.one_le_rpow hT (by positivity)
  -- the long block is at most `32 T / 8`
  have hL : ((8 * Sieve.hbLongBlock T : ℕ) : ℝ) ≤ 32 * T := by
    push_cast
    have h1 := Sieve.hbLongBlock_le_rpow hT
    have h2 : T ^ ((2 : ℝ) / 3) ≤ T := by
      have := Real.rpow_le_rpow_of_exponent_le hT (by norm_num : (2 : ℝ) / 3 ≤ 1)
      rwa [Real.rpow_one] at this
    linarith
  have hdiv := divisorFactor_pow_le hδ (Nat.cast_nonneg _) hL 10
  have hpow : ((32 * T) ^ δ) ^ 10 = (32 : ℝ) ^ (ε / 2) * T ^ (ε / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), Real.mul_rpow (by norm_num) hT0]
    simp only [δ]
    norm_num
    ring_nf
  rw [hpow] at hdiv
  have hfirst : (D * ((8 * Sieve.hbLongBlock T : ℕ) : ℝ) ^ δ) ^ 10 + 1 ≤
      (D ^ 10 * (32 : ℝ) ^ (ε / 2) + 1) * T ^ (ε / 2) := by
    have : D ^ 10 * ((32 : ℝ) ^ (ε / 2) * T ^ (ε / 2)) = D ^ 10 * (32 : ℝ) ^ (ε / 2) * T ^ (ε / 2) := by
      ring
    nlinarith
  have hsecond := hKb T hT
  have hsplit : T ^ ε = T ^ (ε / 2) * T ^ (ε / 2) := by
    rw [← Real.rpow_add (by linarith)]; ring_nf
  rw [Sieve.hbSmallConst, hsplit]
  have h0 : 0 ≤ Sieve.hbReflFactor T + Sieve.hbDualFactor T + 1 := by
    have := Sieve.one_le_hbReflFactor hT
    have := Sieve.hbDualFactor_nonneg T
    linarith
  calc 3584 * ((D * ((8 * Sieve.hbLongBlock T : ℕ) : ℝ) ^ δ) ^ 10 + 1) *
        (Sieve.hbReflFactor T + Sieve.hbDualFactor T + 1)
      ≤ 3584 * ((D ^ 10 * (32 : ℝ) ^ (ε / 2) + 1) * T ^ (ε / 2)) * (K * T ^ (ε / 2)) := by
        gcongr
    _ = _ := by ring

/-! ### Short blocks -/

/-- Membership in `[T₀, T₀ + T]` bounds the diameter by `T`. -/
theorem abs_sub_le_of_mem_interval {𝒯 : Finset ℝ} {T₀ T : ℝ}
    (h𝒯 : ∀ t ∈ 𝒯, T₀ ≤ t ∧ t ≤ T₀ + T) : ∀ t ∈ 𝒯, ∀ t' ∈ 𝒯, |t - t'| ≤ T := by
  intro t ht t' ht'
  have h1 := h𝒯 t ht
  have h2 := h𝒯 t' ht'
  rw [abs_le]; constructor <;> linarith

/-- **Heath-Brown's theorem for blocks `N ≤ T^{1/4}`, unconditionally:** for every `ε > 0` there is
`C` with `HeathBrownBlockBound N T (C T^ε)` whenever `T ≥ 2` and `1 ≤ N ≤ T^{1/4}`. -/
theorem exists_heathBrownBlockBound_short {ε : ℝ} (hε : 0 < ε) :
    ∃ C, 0 ≤ C ∧ ∀ (N : ℕ) (T : ℝ), 2 ≤ T → 1 ≤ N → (N : ℝ) ≤ T ^ (1 / 4 : ℝ) →
      HeathBrownBlockBound N T (C * T ^ ε) := by
  obtain ⟨δ, hδ, C, hC, hCb⟩ := exists_hbSmallConst_le hε
  refine ⟨C, hC, fun N T hT hN hNT 𝒯 a T₀ ha h𝒯 hsep => ?_⟩
  have hT1 : 1 ≤ T := by linarith
  have h := Sieve.sum_sum_norm_sq_exp_le_smallBlock hsep hT1 (abs_sub_le_of_mem_interval h𝒯) hN
    (Sieve.sq_le_rpow_two_thirds_of_le_rpow_quarter hT1 hNT) hδ (fun n _ => ha n)
  refine h.trans (mul_le_mul_of_nonneg_right (hCb T hT1)
    (heathBrownMajorant_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by linarith)))

/-! ### Long blocks -/

/-- The trivial bound `Σ_{t₁,t₂} |Σ_{N<n≤2N} a_n n^{i(t₁−t₂)}|² ≤ |𝒯|² N²` for `|a_n| ≤ 1`. -/
theorem pairSum_le_trivial (𝒯 : Finset ℝ) (N : ℕ) {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ 1) :
    ∑ t₁ ∈ 𝒯, ∑ t₂ ∈ 𝒯,
        ‖∑ n ∈ Finset.Ioc N (2 * N), a n * Complex.exp (Complex.I * (t₁ - t₂) * Real.log n)‖ ^ 2
      ≤ (𝒯.card : ℝ) ^ 2 * (N : ℝ) ^ 2 := by
  have hterm : ∀ t₁ t₂ : ℝ,
      ‖∑ n ∈ Finset.Ioc N (2 * N), a n * Complex.exp (Complex.I * (t₁ - t₂) * Real.log n)‖ ^ 2
        ≤ (N : ℝ) ^ 2 := by
    intro t₁ t₂
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    refine (norm_sum_le _ _).trans ?_
    calc ∑ n ∈ Finset.Ioc N (2 * N),
          ‖a n * Complex.exp (Complex.I * (t₁ - t₂) * Real.log n)‖
        ≤ ∑ _n ∈ Finset.Ioc N (2 * N), (1 : ℝ) := by
          refine sum_le_sum fun n _ => ?_
          rw [norm_mul, ← Complex.ofReal_sub, norm_exp_mul_log, mul_one]
          exact ha n
      _ = N := by simp [Nat.card_Ioc, two_mul]
  calc _ ≤ ∑ _t₁ ∈ 𝒯, ∑ _t₂ ∈ 𝒯, (N : ℝ) ^ 2 :=
        sum_le_sum fun t₁ _ => sum_le_sum fun t₂ _ => hterm t₁ t₂
    _ = (𝒯.card : ℝ) ^ 2 * (N : ℝ) ^ 2 := by simp; ring

/-- **Heath-Brown's theorem for blocks `T^{2/3} ≤ N ≤ T`, unconditionally:** for every `ε > 0`
there is `C` with `HeathBrownBlockBound N T (C T^ε)` (here even without the third term). -/
theorem exists_heathBrownBlockBound_long {ε : ℝ} (hε : 0 < ε) :
    ∃ C, 0 ≤ C ∧ ∀ (N : ℕ) (T : ℝ), 2 ≤ T → T ^ (2 / 3 : ℝ) ≤ N → (N : ℝ) ≤ T →
      HeathBrownBlockBound N T (C * T ^ ε) := by
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = ε / 10 := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; positivity
  obtain ⟨K, hK, hKb⟩ := exists_hbReflFactor_add_hbDualFactor_le (η := ε / 2) (by positivity)
  have hD : 0 ≤ Sieve.divisorBoundConst δ := (Sieve.divisorBoundConst_pos hδ).le
  obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ℝ,
      C₀ = (224 + 4 * Sieve.divisorBoundConst δ ^ 5 * (16 : ℝ) ^ (ε / 2)) * K := ⟨_, rfl⟩
  refine ⟨max C₀ 64, le_trans (by norm_num) (le_max_right _ _),
    fun N T hT hNT hN 𝒯 a T₀ ha h𝒯 hsep => ?_⟩
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 ≤ T := by linarith
  have hTε : 1 ≤ T ^ ε := Real.one_le_rpow hT1 hε.le
  have hTε2 : 1 ≤ T ^ (ε / 2) := Real.one_le_rpow hT1 (by positivity)
  have h23 : 1 ≤ T ^ (2 / 3 : ℝ) := Real.one_le_rpow hT1 (by norm_num)
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ N := h23.trans hNT
    exact_mod_cast this
  have hX : (0 : ℝ) ≤ 𝒯.card := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hmaj : (𝒯.card : ℝ) ^ 2 * N + 𝒯.card * (N : ℝ) ^ 2 ≤ heathBrownMajorant 𝒯.card N T := by
    unfold heathBrownMajorant
    have : 0 ≤ (𝒯.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * N := by positivity
    linarith
  have hN3 : T ^ 2 ≤ (N : ℝ) ^ 3 := by
    have h := pow_le_pow_left₀ (by positivity) hNT 3
    rwa [← Real.rpow_natCast (T ^ (2 / 3 : ℝ)), ← Real.rpow_mul hT0,
      show (2 / 3 : ℝ) * ((3 : ℕ) : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast] at h
  by_cases hlong : 2 * T < (N : ℝ) ^ 2
  · -- the corpus long-block theorem
    have h := Sieve.hbPairSum_Ioc_le_of_twoThirds hsep hT1 (abs_sub_le_of_mem_interval h𝒯) hN1
      hlong (by nlinarith) hδ (fun n _ => ha n)
    rw [Sieve.hbPairSum_eq_sum_exp] at h
    replace h := h.trans (le_of_eq (show _ = 224 * Sieve.hbReflFactor T * 𝒯.card * (N : ℝ) ^ 2 +
        4 * Sieve.hbDualFactor T * (Sieve.divisorBoundConst δ * ((8 * N : ℕ) : ℝ) ^ δ) ^ 5 *
          (𝒯.card : ℝ) ^ 2 * N by rw [Sieve.hbReflFactor, Sieve.hbDualFactor]; ring))
    have hK' := hKb T hT1
    have hr := Sieve.one_le_hbReflFactor hT1
    have hd := Sieve.hbDualFactor_nonneg T
    have hdiv : (Sieve.divisorBoundConst δ * ((8 * N : ℕ) : ℝ) ^ δ) ^ 5 ≤
        Sieve.divisorBoundConst δ ^ 5 * (16 : ℝ) ^ (ε / 2) * T ^ (ε / 2) := by
      have h8 : ((8 * N : ℕ) : ℝ) ≤ 8 * T := by push_cast; linarith
      have := divisorFactor_pow_le hδ (Nat.cast_nonneg _) h8 5
      have hp : ((8 * T) ^ δ) ^ 5 = (8 : ℝ) ^ (ε / 2) * T ^ (ε / 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), Real.mul_rpow (by norm_num) hT0,
          hδdef]
        norm_num
        ring_nf
      have h816 : (8 : ℝ) ^ (ε / 2) ≤ (16 : ℝ) ^ (ε / 2) :=
        Real.rpow_le_rpow (by norm_num) (by norm_num) (by positivity)
      rw [hp] at this
      calc _ ≤ Sieve.divisorBoundConst δ ^ 5 * ((8 : ℝ) ^ (ε / 2) * T ^ (ε / 2)) := this
        _ ≤ Sieve.divisorBoundConst δ ^ 5 * ((16 : ℝ) ^ (ε / 2) * T ^ (ε / 2)) := by gcongr
        _ = _ := by ring
    have hsplit : T ^ ε = T ^ (ε / 2) * T ^ (ε / 2) := by
      rw [← Real.rpow_add (by linarith)]; ring_nf
    have hrK : Sieve.hbReflFactor T ≤ K * T ^ (ε / 2) := by linarith
    have hdK : Sieve.hbDualFactor T ≤ K * T ^ (ε / 2) := by linarith
    obtain ⟨P, hP⟩ : ∃ P, P = T ^ (ε / 2) := ⟨_, rfl⟩
    obtain ⟨E, hE⟩ : ∃ E : ℝ, E = Sieve.divisorBoundConst δ ^ 5 * (16 : ℝ) ^ (ε / 2) := ⟨_, rfl⟩
    have hE0 : 0 ≤ E := by rw [hE]; positivity
    rw [← hP] at hTε2 hrK hdK hdiv hsplit
    rw [← hE] at hdiv
    have hC₀' : C₀ = (224 + 4 * E) * K := by rw [hC₀, hE]; ring
    calc _ ≤ 224 * Sieve.hbReflFactor T * 𝒯.card * (N : ℝ) ^ 2 + 4 * Sieve.hbDualFactor T *
          (Sieve.divisorBoundConst δ * ((8 * N : ℕ) : ℝ) ^ δ) ^ 5 * (𝒯.card : ℝ) ^ 2 * N := h
      _ ≤ 224 * (K * P) * 𝒯.card * (N : ℝ) ^ 2 + 4 * (K * P) * (E * P) * (𝒯.card : ℝ) ^ 2 * N := by
        gcongr
      _ ≤ C₀ * T ^ ε * ((𝒯.card : ℝ) ^ 2 * N + 𝒯.card * (N : ℝ) ^ 2) := by
        rw [hsplit, hC₀']
        have hA : 0 ≤ K * P * 𝒯.card * (N : ℝ) ^ 2 := by positivity
        have hA' : K * P * 𝒯.card * (N : ℝ) ^ 2 ≤ K * P * 𝒯.card * (N : ℝ) ^ 2 * P :=
          le_mul_of_one_le_right hA hTε2
        have hB : 0 ≤ K * P * P * (𝒯.card : ℝ) ^ 2 * N := by
          have : 0 ≤ P := by linarith
          positivity
        have hC : 0 ≤ E * K * (P * P) * (𝒯.card * (N : ℝ) ^ 2) := by
          have : 0 ≤ P := by linarith
          positivity
        nlinarith
      _ ≤ max C₀ 64 * T ^ ε * heathBrownMajorant 𝒯.card N T := by
        gcongr
        exact le_max_left _ _
  · -- `N² ≤ 2T` and `N ≥ T^{2/3}` force `N ≤ 8`: the trivial bound
    have hN2 : (N : ℝ) ^ 2 ≤ 2 * T := not_lt.mp hlong
    have hT8 : (N : ℝ) ≤ 8 := by nlinarith
    have htriv := pairSum_le_trivial 𝒯 N ha
    have hXN : 0 ≤ (𝒯.card : ℝ) ^ 2 * N := by positivity
    calc _ ≤ (𝒯.card : ℝ) ^ 2 * (N : ℝ) ^ 2 := htriv
      _ = (𝒯.card : ℝ) ^ 2 * N * N := by ring
      _ ≤ (𝒯.card : ℝ) ^ 2 * N * 8 := mul_le_mul_of_nonneg_left hT8 hXN
      _ ≤ 64 * T ^ ε * ((𝒯.card : ℝ) ^ 2 * N + 𝒯.card * (N : ℝ) ^ 2) := by
        have : 0 ≤ (𝒯.card : ℝ) * (N : ℝ) ^ 2 := by positivity
        nlinarith
      _ ≤ max C₀ 64 * T ^ ε * heathBrownMajorant 𝒯.card N T := by
        gcongr
        exact le_max_right _ _

end

end RHTower.GuthMaynard
