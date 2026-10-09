import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenReflectionBranches

/-!
# Matomäki–Teräväinen Lemma 3.5: reduction to short unit blocks

`MTDeshouillersIwaniecBound` and `MTWattBound` follow from their restrictions to short unit blocks
`N² ≤ T` (`mtDeshouillersIwaniecBound_of_short`, `mtWattBound_of_short`).

For `N² > T` the block `U_N(t) = ∑_{N<n≤N'} n^{-1-it}` on `[T/2, T]` is handled unconditionally:
* `T ≤ N`: the Kuzmin–Landau over-height bound;
* `N < T`, `T/(2πN) ≤ 11`: the reflection with a bounded dual sum;
* `N < T`, `T/(2πN) > 11`: the reflection to the dual blocks `(B, 2B]`, `B ∈ {M, 2M, 4M}`,
  `M = ⌊T/(4π(N' + ¼))⌋`, followed by Perron's formula, Hölder, Fubini and a vertical shift.  The
  shift turns the coefficients into `a_m m^{-iu}`, which have the same energy and the same sup
  bound, and the dual blocks satisfy `B² ≤ T'/2`, so the short bound applies on each window
  `[T'/2, T']`, `T' ∈ {T/2, T, 5T/4}`.
-/

open Complex Set MeasureTheory Filter
open scoped Real

namespace RHTower.Sieve

noncomputable section

/-- **Matomäki–Teräväinen Lemma 3.5(ii) on short unit blocks** (`N² ≤ T`). -/
def MTDeshouillersIwaniecBoundShort : Prop :=
  ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → ℂ) (A N N' : ℕ),
    1 ≤ A → 1 ≤ N → N < N' → N' ≤ 2 * N → ∀ T : ℝ, 2 ≤ T → (N : ℝ) ^ 2 ≤ T →
    (∫ t in (T / 2)..T, ‖mtWattUnitBlock N N' t‖ ^ (4 : ℕ) *
        ‖mtWattCoefficientBlock a A t‖ ^ (2 : ℕ)) ≤
      C * T ^ η *
        (((T + (A : ℝ) ^ (2 : ℕ) * Real.sqrt T + (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) /
              ((N : ℝ) ^ (2 : ℕ) * (A : ℝ)) +
            (T + (A : ℝ)) / (T ^ (4 : ℕ) * (A : ℝ))) *
          (1 / (A : ℝ)) * ∑ m ∈ Finset.Ioc A (2 * A), ‖a m‖ ^ (2 : ℕ))

/-- **Matomäki–Teräväinen Lemma 3.5(i) on short unit blocks** (`N² ≤ T`). -/
def MTWattBoundShort : Prop :=
  ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → ℂ) (A N N' : ℕ) (B : ℝ),
    1 ≤ A → 1 ≤ N → N < N' → N' ≤ 2 * N → (∀ m, ‖a m‖ ≤ B) → ∀ T : ℝ, 2 ≤ T →
    (N : ℝ) ^ 2 ≤ T →
    (∫ t in (T / 2)..T, ‖mtWattUnitBlock N N' t‖ ^ (4 : ℕ) *
        ‖mtWattCoefficientBlock a A t‖ ^ (2 : ℕ)) ≤
      C * T ^ η *
        (((T + (A : ℝ) ^ 2 * Real.sqrt T) / ((N : ℝ) ^ (2 : ℕ) * (A : ℝ)) +
            (T + (A : ℝ)) / (T ^ (4 : ℕ) * (A : ℝ))) * B ^ 2)

/-! ## The dual blocks are short -/

/-- In the reflection range the dual blocks `B ∈ {M, 2M, 4M}` satisfy `1 ≤ B`, `M ≤ B` and
`B² ≤ T'` for every window `T' ∈ {T/2, T, 5T/4}`. -/
theorem mt_dualBlock_short {N N' : ℕ} (hN : 1 ≤ N) (hNN' : N < N') (hN' : N' ≤ 2 * N) {T : ℝ}
    (hNT : (N : ℝ) < T) (hTN : T < (N : ℝ) ^ 2) (hY : 11 ≤ T / (2 * π * N)) {B : ℕ}
    (hB : B = ubDualBase N' T ∨ B = 2 * ubDualBase N' T ∨ B = 4 * ubDualBase N' T) {T' : ℝ}
    (hT' : T' = T / 2 ∨ T' = T ∨ T' = 5 * T / 4) :
    1 ≤ B ∧ ubDualBase N' T ≤ B ∧ (B : ℝ) ^ 2 ≤ T' ∧ 2 ≤ T' ∧ T / 2 ≤ T' ∧ T' ≤ 5 * T / 4 := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hT0 : 0 < T := by linarith
  obtain ⟨hM1, hMY, -⟩ := ub_dual_edges hN hNN' hN' hNT hY (t := T) (by linarith) le_rfl
  have hY2 := ub_Y_sq_le hN1 hT0 hTN
  have hT60 : 60 ≤ T := by
    have h1 : 3 ≤ π * N := by nlinarith [Real.pi_gt_three]
    have e : T = 2 * π * N * (T / (2 * π * N)) := by field_simp
    have h2 : 33 ≤ π * N * (T / (2 * π * N)) := by nlinarith
    linarith
  have hBle : (B : ℝ) ≤ 2 * (T / (2 * π * N)) := by
    rcases hB with rfl | rfl | rfl <;> push_cast <;> nlinarith
  have hB2 : (B : ℝ) ^ 2 ≤ T / 2 := by
    have := pow_le_pow_left₀ (Nat.cast_nonneg B) hBle 2
    nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases hB with rfl | rfl | rfl <;> omega
  · rcases hB with rfl | rfl | rfl <;> omega
  · rcases hT' with rfl | rfl | rfl <;> linarith
  · rcases hT' with rfl | rfl | rfl <;> linarith
  · rcases hT' with rfl | rfl | rfl <;> linarith
  · rcases hT' with rfl | rfl | rfl <;> linarith

/-- Moving the short bound from the window `T'` and block `B` to the reference `T` and base `M`. -/
private theorem mt_window_transfer {CS η T T' A B M Num Num' Q Q' E : ℝ} (hCS : 0 ≤ CS)
    (hT : 0 < T) (hT' : 0 ≤ T') (hT'T : T' ≤ 5 * T / 4) (hA : 0 < A) (hM : 0 < M) (hMB : M ≤ B)
    (hNum' : 0 ≤ Num') (hNum : Num' ≤ 5 / 4 * Num) (hQ' : 0 ≤ Q') (hQ : Q' ≤ 20 * Q)
    (hE : 0 ≤ E) (hη : 0 < η) :
    CS * T' ^ (η / 2) * ((Num' / (B ^ 2 * A) + Q') * E) ≤
      CS * (5 * T / 4) ^ (η / 2) * (5 / 4 * Num / (M ^ 2 * A) + 20 * Q) * E := by
  have h1 : T' ^ (η / 2) ≤ (5 * T / 4) ^ (η / 2) := Real.rpow_le_rpow hT' hT'T (by positivity)
  have h2 : Num' / (B ^ 2 * A) ≤ 5 / 4 * Num / (M ^ 2 * A) := by
    have hB0 : 0 < B := lt_of_lt_of_le hM hMB
    calc Num' / (B ^ 2 * A) ≤ Num' / (M ^ 2 * A) :=
          div_le_div_of_nonneg_left hNum' (by positivity)
            (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hM.le hMB 2) hA.le)
      _ ≤ 5 / 4 * Num / (M ^ 2 * A) := div_le_div_of_nonneg_right hNum (by positivity)
  have h3 : (Num' / (B ^ 2 * A) + Q') * E ≤ (5 / 4 * Num / (M ^ 2 * A) + 20 * Q) * E :=
    mul_le_mul_of_nonneg_right (add_le_add h2 hQ) hE
  calc CS * T' ^ (η / 2) * ((Num' / (B ^ 2 * A) + Q') * E) ≤
      CS * (5 * T / 4) ^ (η / 2) * ((5 / 4 * Num / (M ^ 2 * A) + 20 * Q) * E) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 hCS) h3 (by positivity) (by positivity)
    _ = _ := by ring

/-- A branch bound `X T^η R` with `X ≤ C` is a bound `C T^η R`. -/
private theorem mt_branch_le {I X C T η R : ℝ} (h : I ≤ X * T ^ η * R) (hXC : X ≤ C)
    (hT : 0 ≤ T) (hR : 0 ≤ R) : I ≤ C * T ^ η * R :=
  le_trans h (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hXC
    (Real.rpow_nonneg hT _)) hR)

/-- `(1 + log T)⁴ X ≤ (1 + 4/η)⁴ T^η X`. -/
private theorem mt_log_le {η T X : ℝ} (hη : 0 < η) (hT : 1 ≤ T) (hX : 0 ≤ X) :
    (1 + Real.log T) ^ 4 * X ≤ (1 + 1 / (η / 4)) ^ 4 * T ^ η * X := by
  have h := one_add_log_pow_four_le_mul_rpow (ε := η / 4) (by positivity) hT
  rw [show 4 * (η / 4) = η by ring] at h
  exact mul_le_mul_of_nonneg_right h hX

/-- **Lemma 3.5(ii) from its short-block case.** -/
theorem mtDeshouillersIwaniecBound_of_short (h : MTDeshouillersIwaniecBoundShort) :
    MTDeshouillersIwaniecBound := by
  intro η hη
  obtain ⟨CS, hCS, hS⟩ := h (η / 2) (by positivity)
  obtain ⟨KD, hKD, hshort⟩ := exists_mt_branch_shortDual
  obtain ⟨KR, hKR, hrefl⟩ := exists_mt_branch_reflection hη
  set KO := (2 * (6 * π + 1)) ^ 4 * (5 * π * Real.exp 1) with hKO
  set KL := (1 + 1 / (η / 4)) ^ 4 with hKL
  refine ⟨CS + KO + KD * KL + KR * (1 + CS), by positivity,
    fun a A N N' hA hN hNN' hN' T hT => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hA0 : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hT0 : 0 < T := by linarith
  obtain ⟨E, hEdef⟩ : ∃ E, E = 1 / (A : ℝ) * mtEnergy a A := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := by rw [hEdef]; exact mul_nonneg (by positivity) (mtEnergy_nonneg a A)
  obtain ⟨Num, hNum⟩ : ∃ Num, Num = T + (A : ℝ) ^ (2 : ℕ) * Real.sqrt T +
      (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ) := ⟨_, rfl⟩
  have hNum1 : T + (A : ℝ) ^ 2 * Real.sqrt T ≤ Num := by
    rw [hNum]; have : 0 ≤ (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ) := by positivity
    linarith
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = (T + (A : ℝ)) / (T ^ (4 : ℕ) * (A : ℝ)) := ⟨_, rfl⟩
  have hR : ((T + (A : ℝ) ^ (2 : ℕ) * Real.sqrt T + (A : ℝ) ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) /
      ((N : ℝ) ^ (2 : ℕ) * (A : ℝ)) + (T + (A : ℝ)) / (T ^ (4 : ℕ) * (A : ℝ))) *
      (1 / (A : ℝ)) * ∑ m ∈ Finset.Ioc A (2 * A), ‖a m‖ ^ (2 : ℕ) =
      (Num / ((N : ℝ) ^ 2 * A) + Q) * E := by
    rw [hEdef, hNum, hQ, mtEnergy]; ring
  rw [hR]
  have hP : 0 ≤ Num / ((N : ℝ) ^ 2 * A) := div_nonneg (le_trans (by positivity) hNum1)
    (by positivity)
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  have hRnn : 0 ≤ (Num / ((N : ℝ) ^ 2 * A) + Q) * E := mul_nonneg (by linarith) hE0
  have hEle : 1 / (A : ℝ) * mtEnergy a A ≤ E := le_of_eq hEdef.symm
  have hTη : 1 ≤ T ^ η := Real.one_le_rpow (by linarith) hη.le
  have hC1 : CS ≤ CS + KO + KD * KL + KR * (1 + CS) := by
    have : 0 ≤ KO := by positivity
    have : 0 ≤ KD * KL := by positivity
    have : 0 ≤ KR * (1 + CS) := by positivity
    linarith
  -- branch 1: short blocks
  by_cases h1 : (N : ℝ) ^ 2 ≤ T
  · have hb := hS a A N N' hA hN hNN' hN' T hT h1
    rw [hR] at hb
    have hη2 : T ^ (η / 2) ≤ T ^ η := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    refine le_trans hb (le_trans ?_ (mt_branch_le le_rfl hC1 hT0.le hRnn))
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hη2 hCS.le) hRnn
  push Not at h1
  -- branch 2: over height
  by_cases h2 : T ≤ N
  · have hb := mt_branch_overHeight a hA hN hNN' hN' hT h2 hEle
    rw [← hQ] at hb
    refine mt_branch_le (X := KO) (le_trans hb ?_) (by
      have : 0 ≤ CS := hCS.le; have : 0 ≤ KD * KL := by positivity
      have : 0 ≤ KR * (1 + CS) := by positivity
      linarith) hT0.le hRnn
    calc KO * (Q * E) ≤ KO * ((Num / ((N : ℝ) ^ 2 * A) + Q) * E) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hE0) (by positivity)
      _ ≤ KO * T ^ η * ((Num / ((N : ℝ) ^ 2 * A) + Q) * E) := by
          rw [mul_assoc]
          exact le_mul_of_one_le_left (by positivity) hTη |>.trans_eq' (by ring) |> fun h => by
            nlinarith [mul_le_mul_of_nonneg_right hTη (mul_nonneg (by positivity : (0 : ℝ) ≤ KO)
              hRnn)]
  push Not at h2
  -- branch 3: short dual
  by_cases h3 : T / (2 * π * N) ≤ 11
  · have hb := hshort a A N N' T E Num hA hN hNN' hN' hT h2 h1 h3 hEle hNum1
    have hlog := mt_log_le hη (by linarith : (1 : ℝ) ≤ T) (mul_nonneg hP hE0)
    refine mt_branch_le (X := KD * KL) (le_trans hb ?_) (by
      have : 0 ≤ CS := hCS.le; have : 0 ≤ KO := by positivity
      have : 0 ≤ KR * (1 + CS) := by positivity
      linarith) hT0.le hRnn
    calc KD * (1 + Real.log T) ^ 4 * (Num / ((N : ℝ) ^ 2 * A) * E) =
        KD * ((1 + Real.log T) ^ 4 * (Num / ((N : ℝ) ^ 2 * A) * E)) := by ring
      _ ≤ KD * (KL * T ^ η * (Num / ((N : ℝ) ^ 2 * A) * E)) := mul_le_mul_of_nonneg_left hlog hKD.le
      _ ≤ KD * (KL * T ^ η * ((Num / ((N : ℝ) ^ 2 * A) + Q) * E)) := by
          gcongr
          linarith
      _ = KD * KL * T ^ η * ((Num / ((N : ℝ) ^ 2 * A) + Q) * E) := by ring
  push Not at h3
  -- branch 4: reflection
  have hG : ∀ B : ℕ, (B = ubDualBase N' T ∨ B = 2 * ubDualBase N' T ∨ B = 4 * ubDualBase N' T) →
      ∀ u : ℝ, |u| ≤ T / 4 → ∀ T' : ℝ, (T' = T / 2 ∨ T' = T ∨ T' = 5 * T / 4) →
      ∫ τ in (T' / 2)..T', ‖mtWattUnitBlock B (2 * B) τ‖ ^ 4 *
        ‖mtWattCoefficientBlock (mtTwist a u) A τ‖ ^ 2 ≤
        CS * (5 * T / 4) ^ (η / 2) * (5 / 4 * Num / ((ubDualBase N' T : ℝ) ^ 2 * A) +
          20 * ((T + A) / (T ^ 4 * A))) * E := by
    intro B hB u hu T' hT'
    obtain ⟨hB1, hMB, hB2, hT'2, hT'lo, hT'hi⟩ := mt_dualBlock_short hN hNN' hN' h2 h1 h3.le hB hT'
    have hb := hS (mtTwist a u) A B (2 * B) hA hB1 (by omega) le_rfl T' hT'2 hB2
    rw [sum_normSq_mtTwist] at hb
    have hRw : ((T' + (A : ℝ) ^ (2 : ℕ) * Real.sqrt T' + (A : ℝ) ^ (5 / 4 : ℝ) * T' ^ (3 / 4 : ℝ)) /
        ((B : ℝ) ^ (2 : ℕ) * (A : ℝ)) + (T' + (A : ℝ)) / (T' ^ (4 : ℕ) * (A : ℝ))) *
        (1 / (A : ℝ)) * ∑ m ∈ Finset.Ioc A (2 * A), ‖a m‖ ^ (2 : ℕ) =
        ((T' + (A : ℝ) ^ (2 : ℕ) * Real.sqrt T' + (A : ℝ) ^ (5 / 4 : ℝ) * T' ^ (3 / 4 : ℝ)) /
          ((B : ℝ) ^ 2 * (A : ℝ)) + (T' + (A : ℝ)) / (T' ^ (4 : ℕ) * (A : ℝ))) * E := by
      rw [hEdef, mtEnergy]; ring
    rw [hRw] at hb
    refine le_trans hb ?_
    have hM0 : (0 : ℝ) < ubDualBase N' T := by
      have := (ub_dual_edges hN hNN' hN' h2 h3.le (t := T) (by linarith) le_rfl).1
      exact_mod_cast this
    refine mt_window_transfer hCS.le hT0 (by linarith) hT'hi hA0 hM0 (by exact_mod_cast hMB)
      (by positivity) ?_ (by positivity) (ub_tail_scale hT0 hA0 hT'lo hT'hi) hE0 (by positivity)
    rw [hNum]
    exact ub_numDI_scale hT0.le (by linarith) hT'hi hA0.le
  have hb := hrefl a A N N' T E Num CS hA hN hNN' hN' hT h2 h1 h3.le hEle hNum1 hCS.le hG
  rw [← hQ] at hb
  refine mt_branch_le (X := KR * (1 + CS)) hb (by
    have : 0 ≤ CS := hCS.le; have : 0 ≤ KO := by positivity
    have : 0 ≤ KD * KL := by positivity
    linarith) hT0.le hRnn

/-- The energy of a coefficient block is at most `A·B²` under a uniform bound `|a_m| ≤ B`. -/
theorem mtEnergy_le_of_norm_le {a : ℕ → ℂ} {A : ℕ} {B : ℝ} (ha : ∀ m, ‖a m‖ ≤ B) (hA : 1 ≤ A) :
    1 / (A : ℝ) * mtEnergy a A ≤ B ^ 2 := by
  have hA0 : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (ha 0)
  have h : mtEnergy a A ≤ A * B ^ 2 := by
    rw [mtEnergy]
    refine le_trans (Finset.sum_le_sum fun m _ => pow_le_pow_left₀ (norm_nonneg _) (ha m) 2) ?_
    rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, show 2 * A - A = A by omega]
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hA0]
  linarith

/-- **Lemma 3.5(i) from its short-block case.** -/
theorem mtWattBound_of_short (h : MTWattBoundShort) : MTWattBound := by
  intro η hη
  obtain ⟨CS, hCS, hS⟩ := h (η / 2) (by positivity)
  obtain ⟨KD, hKD, hshort⟩ := exists_mt_branch_shortDual
  obtain ⟨KR, hKR, hrefl⟩ := exists_mt_branch_reflection hη
  set KO := (2 * (6 * π + 1)) ^ 4 * (5 * π * Real.exp 1) with hKO
  set KL := (1 + 1 / (η / 4)) ^ 4 with hKL
  refine ⟨CS + KO + KD * KL + KR * (1 + CS), by positivity,
    fun a A N N' Bs hA hN hNN' hN' ha T hT => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hA0 : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hT0 : 0 < T := by linarith
  have hE0 : 0 ≤ Bs ^ 2 := sq_nonneg Bs
  obtain ⟨Num, hNum⟩ : ∃ Num, Num = T + (A : ℝ) ^ 2 * Real.sqrt T := ⟨_, rfl⟩
  have hNum1 : T + (A : ℝ) ^ 2 * Real.sqrt T ≤ Num := le_of_eq hNum.symm
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = (T + (A : ℝ)) / (T ^ (4 : ℕ) * (A : ℝ)) := ⟨_, rfl⟩
  have hR : ((T + (A : ℝ) ^ 2 * Real.sqrt T) / ((N : ℝ) ^ (2 : ℕ) * (A : ℝ)) +
      (T + (A : ℝ)) / (T ^ (4 : ℕ) * (A : ℝ))) * Bs ^ 2 =
      (Num / ((N : ℝ) ^ 2 * A) + Q) * Bs ^ 2 := by
    rw [hNum, hQ]
  rw [hR]
  have hP : 0 ≤ Num / ((N : ℝ) ^ 2 * A) := by rw [hNum]; positivity
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  have hRnn : 0 ≤ (Num / ((N : ℝ) ^ 2 * A) + Q) * Bs ^ 2 := mul_nonneg (by linarith) hE0
  have hEle : 1 / (A : ℝ) * mtEnergy a A ≤ Bs ^ 2 := mtEnergy_le_of_norm_le ha hA
  have hTη : 1 ≤ T ^ η := Real.one_le_rpow (by linarith) hη.le
  have hC1 : CS ≤ CS + KO + KD * KL + KR * (1 + CS) := by
    have : 0 ≤ KO := by positivity
    have : 0 ≤ KD * KL := by positivity
    have : 0 ≤ KR * (1 + CS) := by positivity
    linarith
  -- branch 1: short blocks
  by_cases h1 : (N : ℝ) ^ 2 ≤ T
  · have hb := hS a A N N' Bs hA hN hNN' hN' ha T hT h1
    rw [hR] at hb
    have hη2 : T ^ (η / 2) ≤ T ^ η := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    refine le_trans hb (le_trans ?_ (mt_branch_le le_rfl hC1 hT0.le hRnn))
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hη2 hCS.le) hRnn
  push Not at h1
  -- branch 2: over height
  by_cases h2 : T ≤ N
  · have hb := mt_branch_overHeight a hA hN hNN' hN' hT h2 hEle
    rw [← hQ] at hb
    refine mt_branch_le (X := KO) (le_trans hb ?_) (by
      have : 0 ≤ CS := hCS.le; have : 0 ≤ KD * KL := by positivity
      have : 0 ≤ KR * (1 + CS) := by positivity
      linarith) hT0.le hRnn
    have h0 : 0 ≤ KO * ((Num / ((N : ℝ) ^ 2 * A) + Q) * Bs ^ 2) := by positivity
    calc KO * (Q * Bs ^ 2) ≤ KO * ((Num / ((N : ℝ) ^ 2 * A) + Q) * Bs ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hE0) (by positivity)
      _ ≤ KO * T ^ η * ((Num / ((N : ℝ) ^ 2 * A) + Q) * Bs ^ 2) := by
          rw [mul_assoc]; exact le_mul_of_one_le_left (by positivity) hTη |>.trans (le_of_eq
            (by ring))
  push Not at h2
  -- branch 3: short dual
  by_cases h3 : T / (2 * π * N) ≤ 11
  · have hb := hshort a A N N' T (Bs ^ 2) Num hA hN hNN' hN' hT h2 h1 h3 hEle hNum1
    have hlog := mt_log_le hη (by linarith : (1 : ℝ) ≤ T) (mul_nonneg hP hE0)
    refine mt_branch_le (X := KD * KL) (le_trans hb ?_) (by
      have : 0 ≤ CS := hCS.le; have : 0 ≤ KO := by positivity
      have : 0 ≤ KR * (1 + CS) := by positivity
      linarith) hT0.le hRnn
    calc KD * (1 + Real.log T) ^ 4 * (Num / ((N : ℝ) ^ 2 * A) * Bs ^ 2) =
        KD * ((1 + Real.log T) ^ 4 * (Num / ((N : ℝ) ^ 2 * A) * Bs ^ 2)) := by ring
      _ ≤ KD * (KL * T ^ η * (Num / ((N : ℝ) ^ 2 * A) * Bs ^ 2)) :=
          mul_le_mul_of_nonneg_left hlog hKD.le
      _ ≤ KD * (KL * T ^ η * ((Num / ((N : ℝ) ^ 2 * A) + Q) * Bs ^ 2)) := by
          gcongr
          linarith
      _ = KD * KL * T ^ η * ((Num / ((N : ℝ) ^ 2 * A) + Q) * Bs ^ 2) := by ring
  push Not at h3
  -- branch 4: reflection
  have hG : ∀ B : ℕ, (B = ubDualBase N' T ∨ B = 2 * ubDualBase N' T ∨ B = 4 * ubDualBase N' T) →
      ∀ u : ℝ, |u| ≤ T / 4 → ∀ T' : ℝ, (T' = T / 2 ∨ T' = T ∨ T' = 5 * T / 4) →
      ∫ τ in (T' / 2)..T', ‖mtWattUnitBlock B (2 * B) τ‖ ^ 4 *
        ‖mtWattCoefficientBlock (mtTwist a u) A τ‖ ^ 2 ≤
        CS * (5 * T / 4) ^ (η / 2) * (5 / 4 * Num / ((ubDualBase N' T : ℝ) ^ 2 * A) +
          20 * ((T + A) / (T ^ 4 * A))) * Bs ^ 2 := by
    intro B hB u hu T' hT'
    obtain ⟨hB1, hMB, hB2, hT'2, hT'lo, hT'hi⟩ := mt_dualBlock_short hN hNN' hN' h2 h1 h3.le hB hT'
    have hb := hS (mtTwist a u) A B (2 * B) Bs hA hB1 (by omega) le_rfl
      (fun m => (norm_mtTwist_le a u m).trans (ha m)) T' hT'2 hB2
    have hRw : ((T' + (A : ℝ) ^ 2 * Real.sqrt T') / ((B : ℝ) ^ (2 : ℕ) * (A : ℝ)) +
        (T' + (A : ℝ)) / (T' ^ (4 : ℕ) * (A : ℝ))) * Bs ^ 2 =
        ((T' + (A : ℝ) ^ 2 * Real.sqrt T') / ((B : ℝ) ^ 2 * (A : ℝ)) +
          (T' + (A : ℝ)) / (T' ^ (4 : ℕ) * (A : ℝ))) * Bs ^ 2 := rfl
    rw [hRw] at hb
    refine le_trans hb ?_
    have hM0 : (0 : ℝ) < ubDualBase N' T := by
      have := (ub_dual_edges hN hNN' hN' h2 h3.le (t := T) (by linarith) le_rfl).1
      exact_mod_cast this
    refine mt_window_transfer hCS.le hT0 (by linarith) hT'hi hA0 hM0 (by exact_mod_cast hMB)
      (by positivity) ?_ (by positivity) (ub_tail_scale hT0 hA0 hT'lo hT'hi) hE0 (by positivity)
    rw [hNum]
    exact ub_numW_scale (by linarith) hT'hi
  have hb := hrefl a A N N' T (Bs ^ 2) Num CS hA hN hNN' hN' hT h2 h1 h3.le hEle hNum1 hCS.le hG
  rw [← hQ] at hb
  refine mt_branch_le (X := KR * (1 + CS)) hb (by
    have : 0 ≤ CS := hCS.le; have : 0 ≤ KO := by positivity
    have : 0 ≤ KD * KL := by positivity
    linarith) hT0.le hRnn

end

end RHTower.Sieve
