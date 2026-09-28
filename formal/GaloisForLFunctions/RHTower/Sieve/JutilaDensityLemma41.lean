import GaloisForLFunctions.RHTower.Sieve.JutilaLocalLargeValues
import GaloisForLFunctions.RHTower.Sieve.EnergyLargeValuesBound

/-!
# Jutila's large-values theorem and Lemma 4.1 up to `σ = 23/100`

Cutting the ordinates into windows of length `T₁ = N^{2-34σ/9}/Q²` and applying Jutila's local
estimate (`JutilaLocalLargeValues`, `k = 9`) with dual length `M ≍ N^{ε²/100-1} T₁` on each window
gives Matomäki–Teräväinen's Lemma 4.1 in the energy form used by Proposition 4.2: for
`N ∈ [T^{9/11-10ε}, T^{1-ε}]`, `‖a‖² ≤ Q/N`, `Q³ ≤ T^{ε²}` and `σ ∈ [5ε, 23/100 - 5ε]`, a
one-separated set on which the block exceeds `N^{-σ}` has at most `T^{2σ-ε²/5}` points.  The
exponent bookkeeping has three margins: `2σε` for the diagonal terms, `1/200` for the windowed
terms (`1 + β(-2 + 52σ/9) ≤ 2σ - 1/200`), `1/25` for the long-window term
(`1 + β(36σ - 9) ≤ 2σ - 1/25`), `β = 9/11 - 10ε`.
-/

namespace RHTower.Sieve

open Finset
open scoped InnerProductSpace

noncomputable section

/-- **Window subdivision for finite sets.**  If every subset of `S` of diameter `≤ W` has at most
`C` points, and `S` has diameter `≤ Ttot`, then `|S| ≤ (⌊Ttot/W⌋ + 1) C`. -/
theorem card_le_of_finset_window_bound {S : Finset ℝ} {W Ttot C : ℝ} (hW : 0 < W) (hC : 0 ≤ C)
    (hspread : ∀ x ∈ S, ∀ y ∈ S, |x - y| ≤ Ttot)
    (hlocal : ∀ S' ⊆ S, (∀ x ∈ S', ∀ y ∈ S', |x - y| ≤ W) → (S'.card : ℝ) ≤ C) :
    (S.card : ℝ) ≤ ((⌊Ttot / W⌋₊ : ℝ) + 1) * C := by
  classical
  rcases S.eq_empty_or_nonempty with hS | hS
  · subst hS; simp only [Finset.card_empty, Nat.cast_zero]; positivity
  set x₀ := S.min' hS with hx₀
  set f : ℝ → ℕ := fun x => ⌊(x - x₀) / W⌋₊ with hf
  have hmaps : ∀ x ∈ S, f x ∈ Finset.range (⌊Ttot / W⌋₊ + 1) := by
    intro x hx
    have h0 : x₀ ≤ x := S.min'_le x hx
    have hd := hspread x hx x₀ (S.min'_mem hS)
    rw [abs_of_nonneg (by linarith)] at hd
    have hle : (x - x₀) / W ≤ Ttot / W := div_le_div_of_nonneg_right hd hW.le
    exact Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.floor_mono hle))
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  push_cast
  have hfib : ∀ b ∈ Finset.range (⌊Ttot / W⌋₊ + 1),
      ((S.filter fun x => f x = b).card : ℝ) ≤ C := by
    intro b _
    refine hlocal _ (Finset.filter_subset _ _) fun x hx y hy => ?_
    obtain ⟨hxS, hxb⟩ := Finset.mem_filter.1 hx
    obtain ⟨hyS, hyb⟩ := Finset.mem_filter.1 hy
    have hx0 : 0 ≤ (x - x₀) / W := div_nonneg (by linarith [S.min'_le x hxS]) hW.le
    have hy0 : 0 ≤ (y - x₀) / W := div_nonneg (by linarith [S.min'_le y hyS]) hW.le
    obtain ⟨hx1, hx2⟩ := (Nat.floor_eq_iff hx0).1 hxb
    obtain ⟨hy1, hy2⟩ := (Nat.floor_eq_iff hy0).1 hyb
    have hdiff : |(x - x₀) / W - (y - x₀) / W| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    rw [← sub_div, abs_div, abs_of_pos hW, div_le_one hW] at hdiff
    rw [show x - x₀ - (y - x₀) = x - y by ring] at hdiff
    exact hdiff
  calc ∑ b ∈ Finset.range (⌊Ttot / W⌋₊ + 1), ((S.filter fun x => f x = b).card : ℝ)
      ≤ ∑ _b ∈ Finset.range (⌊Ttot / W⌋₊ + 1), C := Finset.sum_le_sum hfib
    _ = ((⌊Ttot / W⌋₊ : ℝ) + 1) * C := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

/-- Every vector of length `N` is the block coefficient vector (at `σ = 1`) of coefficients with
`∑_{N ≤ n < 2N} |c_n|²/n ≤ 2N ‖a‖²`. -/
theorem exists_blockCoeff_one_eq (N : ℕ) (a : EuclideanSpace ℂ (Fin N)) :
    ∃ c : ℕ → ℂ, blockCoeff N c 1 = a ∧
      ∑ n ∈ Finset.Ico N (2 * N), ‖c n‖ ^ 2 / (n : ℝ) ≤ 2 * N * ‖a‖ ^ 2 := by
  classical
  set c : ℕ → ℂ := fun n => (if h : n - N < N then a ⟨n - N, h⟩ else 0) * (n : ℂ) with hc
  refine ⟨c, ?_, ?_⟩
  · ext j
    simp only [blockCoeff, hc]
    have hj : N + (j : ℕ) - N < N := by have := j.2; omega
    rw [dif_pos hj]
    have hjj : (⟨N + (j : ℕ) - N, hj⟩ : Fin N) = j := by ext; simp
    rw [hjj]
    have hpos : (0 : ℝ) < ((N + (j : ℕ) : ℕ) : ℝ) := by
      have : 0 < N := lt_of_le_of_lt (Nat.zero_le _) j.2
      exact_mod_cast (by omega : 0 < N + (j : ℕ))
    rw [Real.rpow_neg_one]
    have hne : ((N : ℂ) + ((j : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast hpos.ne'
    push_cast
    field_simp
  · rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity),
      Finset.sum_Ico_eq_sum_range, show 2 * N - N = N by omega, Finset.mul_sum,
      ← Fin.sum_univ_eq_sum_range (fun i => ‖c (N + i)‖ ^ 2 / ((N + i : ℕ) : ℝ)) N]
    refine Finset.sum_le_sum fun j _ => ?_
    have hj : N + (j : ℕ) - N < N := by have := j.2; omega
    have hjj : (⟨N + (j : ℕ) - N, hj⟩ : Fin N) = j := by ext; simp
    simp only [hc, dif_pos hj, hjj]
    have hpos : (0 : ℝ) < ((N + (j : ℕ) : ℕ) : ℝ) := by
      have : 0 < N := lt_of_le_of_lt (Nat.zero_le _) j.2
      exact_mod_cast (by omega : 0 < N + (j : ℕ))
    rw [norm_mul, Complex.norm_natCast, mul_pow, sq ((N + (j : ℕ) : ℕ) : ℝ), ← mul_assoc,
      mul_div_assoc, div_self hpos.ne', mul_one]
    have hle : ((N + (j : ℕ) : ℕ) : ℝ) ≤ 2 * N := by
      have := j.2; push_cast; have : ((j : ℕ) : ℝ) ≤ N := by exact_mod_cast this.le
      linarith
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right hle (by positivity)

/-- Polylogarithms are eventually below every power. -/
theorem eventually_mul_one_add_log_pow_le_rpow (C : ℝ) (m : ℕ) {γ : ℝ} (hγ : 0 < γ) :
    ∀ᶠ T : ℝ in Filter.atTop, C * (1 + Real.log T) ^ m ≤ T ^ γ := by
  have ho := isLittleO_log_rpow_rpow_atTop (m : ℝ) hγ
  have hc : (0 : ℝ) < 1 / (|C| * 2 ^ m + 1) := by positivity
  filter_upwards [ho.bound hc, Filter.eventually_ge_atTop (Real.exp 1)] with T hT hTe
  have hT1 : 1 ≤ Real.log T := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hTe
  have hT0 : 0 < T := lt_of_lt_of_le (Real.exp_pos 1) hTe
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith) _),
    abs_of_nonneg (Real.rpow_nonneg hT0.le _), Real.rpow_natCast] at hT
  have h2 : (1 + Real.log T) ^ m ≤ 2 ^ m * Real.log T ^ m := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) (by linarith) m
  have hTg : 0 ≤ T ^ γ := Real.rpow_nonneg hT0.le _
  calc C * (1 + Real.log T) ^ m ≤ |C| * (1 + Real.log T) ^ m :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * (2 ^ m * Real.log T ^ m) := mul_le_mul_of_nonneg_left h2 (abs_nonneg C)
    _ = (|C| * 2 ^ m) * Real.log T ^ m := by ring
    _ ≤ (|C| * 2 ^ m) * (1 / (|C| * 2 ^ m + 1) * T ^ γ) :=
        mul_le_mul_of_nonneg_left hT (by positivity)
    _ ≤ T ^ γ := by
        rw [← mul_assoc, mul_one_div]
        have : |C| * 2 ^ m / (|C| * 2 ^ m + 1) ≤ 1 := by
          rw [div_le_one (by positivity)]; linarith
        nlinarith

/-- Two factors bounded by powers of `T ≥ 1` multiply to a power. -/
theorem mul_le_rpow_of_le_rpow {T x y a b e : ℝ} (hT : 1 ≤ T) (hxa : x ≤ T ^ a)
    (hy : 0 ≤ y) (hyb : y ≤ T ^ b) (he : a + b ≤ e) : x * y ≤ T ^ e := by
  have hT0 : 0 < T := by linarith
  calc x * y ≤ T ^ a * T ^ b := mul_le_mul hxa hyb hy (Real.rpow_nonneg hT0.le a)
    _ = T ^ (a + b) := (Real.rpow_add hT0 a b).symm
    _ ≤ T ^ e := Real.rpow_le_rpow_of_exponent_le hT he

/-- Positive powers of `N ≤ T^u`. -/
theorem natCast_rpow_le_of_le_rpow {T u e : ℝ} {N : ℕ} (hT : 1 ≤ T) (hN : (N : ℝ) ≤ T ^ u)
    (he : 0 ≤ e) : (N : ℝ) ^ e ≤ T ^ (u * e) := by
  have hT0 : 0 < T := by linarith
  rw [Real.rpow_mul hT0.le]
  exact Real.rpow_le_rpow (Nat.cast_nonneg _) hN he

/-- Negative powers of `N ≥ T^β`. -/
theorem natCast_rpow_le_of_rpow_le {T β e : ℝ} {N : ℕ} (hT : 1 ≤ T) (hN : T ^ β ≤ (N : ℝ))
    (he : e ≤ 0) : (N : ℝ) ^ e ≤ T ^ (β * e) := by
  have hT0 : 0 < T := by linarith
  rw [Real.rpow_mul hT0.le]
  exact Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hT0 _) hN he

/-- The large-value term of the local estimate at the threshold `V = N^{-σ}` and energy `2Q`. -/
theorem jutila_highMoment_factor_eq {N : ℕ} (hN : 1 ≤ N) (σ Q : ℝ) :
    (80 * (Real.sqrt Real.pi / Real.sqrt N) * (2 * Q) / ((N : ℝ) ^ (-σ)) ^ 2) ^ (2 * 9) =
      (160 * Real.sqrt Real.pi * Q) ^ 18 * (N : ℝ) ^ (36 * σ - 9) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : Real.sqrt N ^ 18 = (N : ℝ) ^ (9 : ℕ) := by
    rw [show (18 : ℕ) = 2 * 9 by norm_num, pow_mul, Real.sq_sqrt hN0.le]
  have hv : (((N : ℝ) ^ (-σ)) ^ 2) ^ 18 = ((N : ℝ) ^ (36 * σ))⁻¹ := by
    rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le, ← Real.rpow_neg hN0.le]
    congr 1; push_cast; ring
  have he : (N : ℝ) ^ (36 * σ - 9) = (N : ℝ) ^ (36 * σ) / (N : ℝ) ^ (9 : ℕ) := by
    rw [Real.rpow_sub hN0, show ((9 : ℝ)) = ((9 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hsN : Real.sqrt N ≠ 0 := (Real.sqrt_pos.2 hN0).ne'
  have hN36 : (N : ℝ) ^ (36 * σ) ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
  rw [show 2 * 9 = 18 by norm_num, div_pow, mul_pow, mul_pow, div_pow, hs, hv, he]
  field_simp
  ring

/-- The near-diagonal term of the local estimate at the threshold `V = N^{-σ}`. -/
theorem jutila_nearTerm_eq {N : ℕ} (hN : 1 ≤ N) (σ τ₁ G : ℝ) :
    80 * (3 * (2 * τ₁ + 1)) * G / ((N : ℝ) ^ (-σ)) ^ 2 =
      240 * (2 * τ₁ + 1) * G * (N : ℝ) ^ (2 * σ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le, show (-σ * ((2 : ℕ) : ℝ)) = -(2 * σ) by
    push_cast; ring, Real.rpow_neg hN0.le, div_inv_eq_mul]
  ring

/-- The exponent margin of the long-window term: `1 + β(36σ - 9) ≤ 2σ - 1/25`. -/
theorem jutila_exponent_margin_long {ε σ : ℝ} (hε : 0 < ε) (hεs : ε ≤ 1 / 1000)
    (hσh : σ ≤ 23 / 100 - 5 * ε) :
    1 + ((9 : ℝ) / 11 - 10 * ε) * (36 * σ - 9) ≤ 2 * σ - 1 / 25 := by
  have h1 : 0 ≤ (23 / 100 - 5 * ε - σ) * ((302 : ℝ) / 11 - 360 * ε) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- The exponent margin of the subdivided term: `1 + β(-2 + 52σ/9) ≤ 2σ - 1/200`. -/
theorem jutila_exponent_margin_windows {ε σ : ℝ} (hε : 0 < ε) (hεs : ε ≤ 1 / 1000)
    (hσh : σ ≤ 23 / 100 - 5 * ε) :
    1 + ((9 : ℝ) / 11 - 10 * ε) * (-2 + 52 / 9 * σ) ≤ 2 * σ - 1 / 200 := by
  have h1 : 0 ≤ (23 / 100 - 5 * ε - σ) * ((30 : ℝ) / 11 - 520 / 9 * ε) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- A product of a factor below `T^a/8` and a factor below `T^b` is below `T^e/8`. -/
theorem mul_le_rpow_div_eight {T x y a b e : ℝ} (hT : 1 ≤ T) (hxa : x ≤ T ^ a / 8)
    (hy : 0 ≤ y) (hyb : y ≤ T ^ b) (he : a + b ≤ e) : x * y ≤ T ^ e / 8 := by
  have h := mul_le_rpow_of_le_rpow hT (by linarith : 8 * x ≤ T ^ a) hy hyb he
  linarith

/-- The diagonal near term: `960(3 + 2 log T) Q N^{2σ} ≤ T^{2σ-ε²/5}/8`. -/
theorem jutila_term_near_diag {T Q σ ε : ℝ} {N : ℕ} (hT : 1 ≤ T) (hε : 0 < ε) (hσl : 5 * ε ≤ σ)
    (hQ0 : 0 ≤ Q) (hQ : Q ≤ T ^ (ε ^ 2 / 3)) (hN : (N : ℝ) ^ (2 * σ) ≤ T ^ ((1 - ε) * (2 * σ)))
    (hc : 960 * (3 + 2 * Real.log T) ≤ T ^ (ε ^ 2 / 100) / 8) :
    960 * (3 + 2 * Real.log T) * (Q * (N : ℝ) ^ (2 * σ)) ≤ T ^ (2 * σ - ε ^ 2 / 5) / 8 := by
  have hlog : 0 ≤ Real.log T := Real.log_nonneg hT
  refine mul_le_rpow_div_eight hT hc (by positivity)
    (mul_le_rpow_of_le_rpow hT hQ (by positivity) hN le_rfl) ?_
  nlinarith

/-- The windowed near term: `960(3 + 2 log T) Q³ T N^{2σ-λ} ≤ T^{2σ-ε²/5}/8`. -/
theorem jutila_term_near_windows {T Q σ ε : ℝ} {N : ℕ} (hT : 1 ≤ T) (hε : 0 < ε)
    (hεs : ε ≤ 1 / 1000) (hσh : σ ≤ 23 / 100 - 5 * ε) (hQ0 : 0 ≤ Q)
    (hQ : Q ^ 3 ≤ T ^ (ε ^ 2))
    (hN : (N : ℝ) ^ (-2 + 52 / 9 * σ) ≤ T ^ (((9 : ℝ) / 11 - 10 * ε) * (-2 + 52 / 9 * σ)))
    (hc : 960 * (3 + 2 * Real.log T) ≤ T ^ (ε ^ 2 / 100) / 8) :
    960 * (3 + 2 * Real.log T) * (Q ^ 3 * (T * (N : ℝ) ^ (-2 + 52 / 9 * σ))) ≤
      T ^ (2 * σ - ε ^ 2 / 5) / 8 := by
  have hlog : 0 ≤ Real.log T := Real.log_nonneg hT
  have hT0 : 0 < T := by linarith
  have hm := jutila_exponent_margin_windows hε hεs hσh
  have hTN : T * (N : ℝ) ^ (-2 + 52 / 9 * σ) ≤
      T ^ (1 + ((9 : ℝ) / 11 - 10 * ε) * (-2 + 52 / 9 * σ)) := by
    rw [Real.rpow_add hT0, Real.rpow_one]
    exact mul_le_mul_of_nonneg_left hN hT0.le
  refine mul_le_rpow_div_eight hT hc (by positivity)
    (mul_le_rpow_of_le_rpow hT hQ (by positivity) hTN le_rfl) ?_
  have : ε ^ 2 ≤ ε / 1000 := by nlinarith
  nlinarith

/-- The diagonal dual term: `8 C₀ N^{2σ+9η} P ≤ T^{2σ-ε²/5}/8` with `η = ε²/100`. -/
theorem jutila_term_dual_diag {T σ ε C₀ P : ℝ} {N : ℕ} (hT : 1 ≤ T) (hε : 0 < ε)
    (hσl : 5 * ε ≤ σ) (hP0 : 0 ≤ P)
    (hN : (N : ℝ) ^ (2 * σ + 9 * (ε ^ 2 / 100)) ≤
      T ^ ((1 - ε) * (2 * σ + 9 * (ε ^ 2 / 100))))
    (hc : 8 * C₀ ≤ T ^ (ε ^ 2 / 100) / 8) (hP : P ≤ T ^ (ε ^ 2 / 100)) :
    8 * C₀ * ((N : ℝ) ^ (2 * σ + 9 * (ε ^ 2 / 100)) * P) ≤ T ^ (2 * σ - ε ^ 2 / 5) / 8 := by
  refine mul_le_rpow_div_eight hT hc (by positivity)
    (mul_le_rpow_of_le_rpow hT hN hP0 hP le_rfl) ?_
  have h3 : 0 ≤ ε ^ 3 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hσl hε.le]

/-- The windowed dual term: `8 C₀ Q² T N^{2σ+9η-λ} P ≤ T^{2σ-ε²/5}/8`. -/
theorem jutila_term_dual_windows {T Q σ ε C₀ P : ℝ} {N : ℕ} (hT : 1 ≤ T) (hε : 0 < ε)
    (hεs : ε ≤ 1 / 1000) (hσh : σ ≤ 23 / 100 - 5 * ε)
    (hP0 : 0 ≤ P) (hQ : Q ^ 2 ≤ T ^ (2 * (ε ^ 2 / 3)))
    (hN : (N : ℝ) ^ (-2 + 52 / 9 * σ + 9 * (ε ^ 2 / 100)) ≤
      T ^ (((9 : ℝ) / 11 - 10 * ε) * (-2 + 52 / 9 * σ + 9 * (ε ^ 2 / 100))))
    (hc : 8 * C₀ ≤ T ^ (ε ^ 2 / 100) / 8) (hP : P ≤ T ^ (ε ^ 2 / 100)) :
    8 * C₀ * (Q ^ 2 * ((T * (N : ℝ) ^ (-2 + 52 / 9 * σ + 9 * (ε ^ 2 / 100))) * P)) ≤
      T ^ (2 * σ - ε ^ 2 / 5) / 8 := by
  have hT0 : 0 < T := by linarith
  have hm := jutila_exponent_margin_windows hε hεs hσh
  have hTN : T * (N : ℝ) ^ (-2 + 52 / 9 * σ + 9 * (ε ^ 2 / 100)) ≤
      T ^ (1 + ((9 : ℝ) / 11 - 10 * ε) * (-2 + 52 / 9 * σ + 9 * (ε ^ 2 / 100))) := by
    rw [Real.rpow_add hT0, Real.rpow_one]
    exact mul_le_mul_of_nonneg_left hN hT0.le
  refine mul_le_rpow_div_eight hT hc (by positivity)
    (mul_le_rpow_of_le_rpow hT hQ (by positivity)
      (mul_le_rpow_of_le_rpow hT hTN hP0 hP le_rfl) le_rfl) ?_
  have : ε ^ 2 ≤ ε / 1000 := by nlinarith
  nlinarith

/-- The long-window term: `7 (160√π)^{18} Q^{18} T N^{36σ-9} P ≤ T^{2σ-ε²/5}/8`. -/
theorem jutila_term_long {T Q σ ε C₁ P : ℝ} {N : ℕ} (hT : 1 ≤ T) (hε : 0 < ε)
    (hεs : ε ≤ 1 / 1000) (hσh : σ ≤ 23 / 100 - 5 * ε)
    (hP0 : 0 ≤ P) (hQ : Q ^ 18 ≤ T ^ (6 * ε ^ 2))
    (hN : (N : ℝ) ^ (36 * σ - 9) ≤ T ^ (((9 : ℝ) / 11 - 10 * ε) * (36 * σ - 9)))
    (hc : C₁ ≤ T ^ (ε ^ 2 / 100) / 8) (hP : P ≤ T ^ (ε ^ 2 / 100)) :
    C₁ * (Q ^ 18 * ((T * (N : ℝ) ^ (36 * σ - 9)) * P)) ≤ T ^ (2 * σ - ε ^ 2 / 5) / 8 := by
  have hT0 : 0 < T := by linarith
  have hm := jutila_exponent_margin_long hε hεs hσh
  have hTN : T * (N : ℝ) ^ (36 * σ - 9) ≤
      T ^ (1 + ((9 : ℝ) / 11 - 10 * ε) * (36 * σ - 9)) := by
    rw [Real.rpow_add hT0, Real.rpow_one]
    exact mul_le_mul_of_nonneg_left hN hT0.le
  refine mul_le_rpow_div_eight hT hc (by positivity)
    (mul_le_rpow_of_le_rpow hT hQ (by positivity)
      (mul_le_rpow_of_le_rpow hT hTN hP0 hP le_rfl) le_rfl) ?_
  have : ε ^ 2 ≤ ε / 1000 := by nlinarith
  nlinarith

/-- The window count: with `W = min(T₁, 2T)`, `⌊2T/W⌋ + 1 ≤ 2T/T₁ + 2` and
`(⌊2T/W⌋ + 1)(W + 1) ≤ 7T`. -/
theorem jutila_window_count_le {T T₁ W : ℝ} (hT : 1 ≤ T) (hT₁ : 1 ≤ T₁) (hW : W = min T₁ (2 * T)) :
    ((⌊2 * T / W⌋₊ : ℝ) + 1) ≤ 2 * T / T₁ + 2 ∧
      ((⌊2 * T / W⌋₊ : ℝ) + 1) * (W + 1) ≤ 7 * T := by
  have hW1 : 1 ≤ W := by rw [hW]; exact le_min hT₁ (by linarith)
  have hW0 : 0 < W := by linarith
  have hfl : (⌊2 * T / W⌋₊ : ℝ) ≤ 2 * T / W := Nat.floor_le (by positivity)
  rcases le_total T₁ (2 * T) with h | h
  · rw [min_eq_left h] at hW
    rw [hW] at hfl ⊢
    refine ⟨by linarith, ?_⟩
    have h2 : 2 * T / T₁ ≤ 2 * T := div_le_self (by linarith) hT₁
    have hprod : (2 * T / T₁ + 1) * (T₁ + 1) = 2 * T + 2 * T / T₁ + T₁ + 1 := by
      field_simp; ring
    calc ((⌊2 * T / T₁⌋₊ : ℝ) + 1) * (T₁ + 1) ≤ (2 * T / T₁ + 1) * (T₁ + 1) :=
          mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      _ ≤ 7 * T := by rw [hprod]; linarith
  · rw [min_eq_right h] at hW
    rw [hW]
    have h1 : 2 * T / (2 * T) = 1 := div_self (by linarith)
    rw [h1, Nat.floor_one, Nat.cast_one]
    have : 0 ≤ 2 * T / T₁ := by positivity
    constructor <;> nlinarith

/-- `K L ≤ C₀ N^{2σ+9η}`: the dual length `M ≤ 2 N^η T₁/N` with `T₁ = N^λ/Q²`,
`λ = 2 - 34σ/9`, exactly balances the high-moment factor. -/
theorem jutila_highMoment_mul_dualLength_le {N M : ℕ} (hN : 1 ≤ N) {σ Q η : ℝ} (hQ : 1 ≤ Q)
    (hM : (M : ℝ) ≤ 2 * ((N : ℝ) ^ η * ((N : ℝ) ^ (2 - 34 / 9 * σ) / Q ^ 2) / N)) :
    (160 * Real.sqrt Real.pi * Q) ^ 18 * (N : ℝ) ^ (36 * σ - 9) * (((M ^ 9 : ℕ) : ℝ)) ≤
      2 ^ 9 * (160 * Real.sqrt Real.pi) ^ 18 * (N : ℝ) ^ (2 * σ + 9 * η) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hQ0 : 0 < Q := by linarith
  have e1 : (N : ℝ) ^ η * ((N : ℝ) ^ (2 - 34 / 9 * σ) / Q ^ 2) / N =
      (N : ℝ) ^ (η + (2 - 34 / 9 * σ) - 1) / Q ^ 2 := by
    conv_rhs => rw [show η + (2 - 34 / 9 * σ) - 1 = η + (2 - 34 / 9 * σ) + (-1) by ring,
      Real.rpow_add hN0, Real.rpow_add hN0, Real.rpow_neg_one]
    field_simp
  rw [e1] at hM
  have hM9 : (((M ^ 9 : ℕ) : ℝ)) ≤ 2 ^ 9 * ((N : ℝ) ^ (9 * (η + (2 - 34 / 9 * σ) - 1)) / Q ^ 18) := by
    push_cast
    calc (M : ℝ) ^ 9 ≤ (2 * ((N : ℝ) ^ (η + (2 - 34 / 9 * σ) - 1) / Q ^ 2)) ^ 9 :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hM 9
      _ = 2 ^ 9 * ((N : ℝ) ^ (9 * (η + (2 - 34 / 9 * σ) - 1)) / Q ^ 18) := by
          have hX : ((N : ℝ) ^ (η + (2 - 34 / 9 * σ) - 1)) ^ 9 =
              (N : ℝ) ^ (9 * (η + (2 - 34 / 9 * σ) - 1)) := by
            rw [← Real.rpow_mul_natCast hN0.le]; ring_nf
          rw [mul_pow, div_pow, hX, ← pow_mul]
  have hK0 : 0 ≤ (160 * Real.sqrt Real.pi * Q) ^ 18 * (N : ℝ) ^ (36 * σ - 9) := by positivity
  calc (160 * Real.sqrt Real.pi * Q) ^ 18 * (N : ℝ) ^ (36 * σ - 9) * (((M ^ 9 : ℕ) : ℝ))
      ≤ (160 * Real.sqrt Real.pi * Q) ^ 18 * (N : ℝ) ^ (36 * σ - 9) *
          (2 ^ 9 * ((N : ℝ) ^ (9 * (η + (2 - 34 / 9 * σ) - 1)) / Q ^ 18)) :=
        mul_le_mul_of_nonneg_left hM9 hK0
    _ = 2 ^ 9 * (160 * Real.sqrt Real.pi) ^ 18 *
          ((N : ℝ) ^ (36 * σ - 9) * (N : ℝ) ^ (9 * (η + (2 - 34 / 9 * σ) - 1))) := by
        rw [mul_pow]; field_simp
    _ = 2 ^ 9 * (160 * Real.sqrt Real.pi) ^ 18 * (N : ℝ) ^ (2 * σ + 9 * η) := by
        rw [← Real.rpow_add hN0]; congr 2; ring

/-- The reflection errors of the local estimate are `≤ V²/(80 G)` once the dual length exceeds
`N^{η-1}(W + 2j + 2)` with `2jη ≥ 6`, and `τ₁ = 1 + log T`. -/
theorem jutila_reflection_error_le {T Q σ ε Cj η W : ℝ} {N M j : ℕ} (hT : 1 ≤ T)
    (hTC : 1920 * Cj ≤ T) (hT4 : 1280 ≤ T) (hε : 0 < ε) (hεs : ε ≤ 1 / 1000) (hσ0 : 0 ≤ σ)
    (hσh : σ ≤ 1 / 4) (hCj : 0 ≤ Cj) (hQ1 : 1 ≤ Q) (hQ : Q ≤ T ^ (ε ^ 2 / 3))
    (hNlo : T ^ ((9 : ℝ) / 11 - 10 * ε) ≤ (N : ℝ)) (hNhi : (N : ℝ) ≤ T ^ (1 - ε))
    (hN1 : 1 ≤ N) (hM2 : 2 ≤ M) (hM3 : (M : ℝ) ≤ 3 * T)
    (hjη : 6 ≤ 2 * j * η) (hW : 0 ≤ W) (hMN : (N : ℝ) ^ η * (W + 2 * j + 2) ≤ M * N) :
    20 * (2 * Q) * (Cj * ((W + 2 * j + 2) ^ (2 * j) * ((M : ℝ) ^ ((1 / 2 : ℝ) - 2 * j) *
        (N : ℝ) ^ (-(1 / 2) - 2 * j : ℝ))) + 2 * (Real.exp (-((1 + Real.log T) ^ 2)) /
          (1 + Real.log T))) ≤ ((N : ℝ) ^ (-σ)) ^ 2 / 4 := by
  have hT0 : 0 < T := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (by omega : 1 ≤ M)
  have hlog : 0 ≤ Real.log T := Real.log_nonneg hT
  set x : ℝ := T⁻¹ with hxdef
  have hx0 : 0 < x := inv_pos.2 hT0
  have hxT : x * T = 1 := inv_mul_cancel₀ hT0.ne'
  -- the dual length absorbs the window
  have hWle : W + 2 * j + 2 ≤ (M : ℝ) * (N : ℝ) ^ (1 - η) := by
    have hNη : 0 < (N : ℝ) ^ η := Real.rpow_pos_of_pos hN0 _
    rw [Real.rpow_sub hN0, Real.rpow_one, mul_div_assoc', le_div_iff₀ hNη]
    linarith
  have hE : (W + 2 * j + 2) ^ (2 * j) * ((M : ℝ) ^ ((1 / 2 : ℝ) - 2 * j) *
      (N : ℝ) ^ (-(1 / 2) - 2 * j : ℝ)) ≤ (M : ℝ) ^ (1 / 2 : ℝ) *
        (N : ℝ) ^ (-(1 / 2) - 2 * j * η : ℝ) := by
    have h1 : (W + 2 * j + 2) ^ (2 * j) ≤ ((M : ℝ) * (N : ℝ) ^ (1 - η)) ^ (2 * j) :=
      pow_le_pow_left₀ (by positivity) hWle _
    have h2 : ((M : ℝ) * (N : ℝ) ^ (1 - η)) ^ (2 * j) * ((M : ℝ) ^ ((1 / 2 : ℝ) - 2 * j) *
        (N : ℝ) ^ (-(1 / 2) - 2 * j : ℝ)) = (M : ℝ) ^ (1 / 2 : ℝ) *
          (N : ℝ) ^ (-(1 / 2) - 2 * j * η : ℝ) := by
      rw [mul_pow, ← Real.rpow_natCast (M : ℝ), ← Real.rpow_natCast ((N : ℝ) ^ (1 - η)),
        ← Real.rpow_mul hN0.le]
      have e1 : (M : ℝ) ^ (((2 * j : ℕ) : ℝ)) * (M : ℝ) ^ ((1 / 2 : ℝ) - 2 * j) =
          (M : ℝ) ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_add hM0]; congr 1; push_cast; ring
      have e2 : (N : ℝ) ^ ((1 - η) * ((2 * j : ℕ) : ℝ)) * (N : ℝ) ^ (-(1 / 2) - 2 * j : ℝ) =
          (N : ℝ) ^ (-(1 / 2) - 2 * j * η : ℝ) := by
        rw [← Real.rpow_add hN0]; congr 1; push_cast; ring
      calc (M : ℝ) ^ (((2 * j : ℕ) : ℝ)) * (N : ℝ) ^ ((1 - η) * ((2 * j : ℕ) : ℝ)) *
            ((M : ℝ) ^ ((1 / 2 : ℝ) - 2 * j) * (N : ℝ) ^ (-(1 / 2) - 2 * j : ℝ))
          = ((M : ℝ) ^ (((2 * j : ℕ) : ℝ)) * (M : ℝ) ^ ((1 / 2 : ℝ) - 2 * j)) *
            ((N : ℝ) ^ ((1 - η) * ((2 * j : ℕ) : ℝ)) * (N : ℝ) ^ (-(1 / 2) - 2 * j : ℝ)) := by
            ring
        _ = _ := by rw [e1, e2]
    rw [← h2]
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  have hMhalf : (M : ℝ) ^ (1 / 2 : ℝ) ≤ 3 * T := by
    calc (M : ℝ) ^ (1 / 2 : ℝ) ≤ (M : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hM1 (by norm_num)
      _ ≤ 3 * T := by rw [Real.rpow_one]; exact hM3
  have hN6 : (N : ℝ) ^ (-(1 / 2) - 2 * j * η : ℝ) ≤ x ^ 4 := by
    calc (N : ℝ) ^ (-(1 / 2) - 2 * j * η : ℝ) ≤ (N : ℝ) ^ (-6 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hNr1 (by linarith)
      _ ≤ T ^ (((9 : ℝ) / 11 - 10 * ε) * (-6)) :=
          natCast_rpow_le_of_rpow_le hT hNlo (by norm_num)
      _ ≤ T ^ (-4 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT (by nlinarith)
      _ = x ^ 4 := by
          rw [Real.rpow_neg hT0.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
            hxdef, inv_pow]
  have hQT : Q ≤ T := hQ.trans (by
    calc T ^ (ε ^ 2 / 3) ≤ T ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT (by nlinarith)
      _ = T := Real.rpow_one T)
  have hexp : Real.exp (-((1 + Real.log T) ^ 2)) ≤ x ^ 3 := by
    have h3 : Real.exp (-((1 + Real.log T) ^ 2)) ≤ Real.exp (Real.log T * (-3)) :=
      Real.exp_le_exp.2 (by nlinarith [sq_nonneg (Real.log T - 1 / 2)])
    rw [← Real.rpow_def_of_pos hT0, Real.rpow_neg hT0.le,
      show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← inv_pow] at h3
    exact h3
  have hτ : Real.exp (-((1 + Real.log T) ^ 2)) / (1 + Real.log T) ≤ x ^ 3 :=
    (div_le_self (Real.exp_pos _).le (by linarith)).trans hexp
  have hV : x ≤ ((N : ℝ) ^ (-σ)) ^ 2 := by
    have hN2 : (N : ℝ) ^ (2 * σ) ≤ T := by
      calc (N : ℝ) ^ (2 * σ) ≤ (T ^ (1 - ε)) ^ (2 * σ) :=
            Real.rpow_le_rpow hN0.le hNhi (by linarith)
        _ = T ^ ((1 - ε) * (2 * σ)) := (Real.rpow_mul hT0.le _ _).symm
        _ ≤ T ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT (by nlinarith)
        _ = T := Real.rpow_one T
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le, show -σ * ((2 : ℕ) : ℝ) = -(2 * σ) by
      push_cast; ring, Real.rpow_neg hN0.le, hxdef]
    exact inv_anti₀ (Real.rpow_pos_of_pos hN0 _) hN2
  have hEb : Cj * ((W + 2 * j + 2) ^ (2 * j) * ((M : ℝ) ^ ((1 / 2 : ℝ) - 2 * j) *
      (N : ℝ) ^ (-(1 / 2) - 2 * j : ℝ))) ≤ Cj * (3 * T * x ^ 4) :=
    mul_le_mul_of_nonneg_left (hE.trans (mul_le_mul hMhalf hN6 (by positivity) (by linarith)))
      hCj
  have hxT' : T * x = 1 := by rw [mul_comm]; exact hxT
  have h1920 : 1920 * Cj * x ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hTC hx0.le
    rw [hxT'] at this; exact this
  have h1280 : 1280 * x ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hT4 hx0.le
    rw [hxT'] at this; exact this
  have hp1 : 20 * (2 * Q) * (Cj * (3 * T * x ^ 4)) ≤ x / 8 := by
    calc 20 * (2 * Q) * (Cj * (3 * T * x ^ 4)) ≤ 20 * (2 * T) * (Cj * (3 * T * x ^ 4)) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = (1920 * Cj * x) * x * (T * x) ^ 2 / 16 := by ring
      _ = (1920 * Cj * x) * x / 16 := by rw [hxT']; ring
      _ ≤ 1 * x / 16 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h1920 hx0.le) (by norm_num)
      _ ≤ x / 8 := by linarith
  have hp2 : 20 * (2 * Q) * (2 * x ^ 3) ≤ x / 8 := by
    calc 20 * (2 * Q) * (2 * x ^ 3) ≤ 20 * (2 * T) * (2 * x ^ 3) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = (1280 * x) * x * (T * x) / 16 := by ring
      _ = (1280 * x) * x / 16 := by rw [hxT']; ring
      _ ≤ 1 * x / 16 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h1280 hx0.le) (by norm_num)
      _ ≤ x / 8 := by linarith
  have hsum : 20 * (2 * Q) * (Cj * ((W + 2 * j + 2) ^ (2 * j) * ((M : ℝ) ^ ((1 / 2 : ℝ) - 2 * j) *
      (N : ℝ) ^ (-(1 / 2) - 2 * j : ℝ))) + 2 * (Real.exp (-((1 + Real.log T) ^ 2)) /
        (1 + Real.log T))) ≤ 20 * (2 * Q) * (Cj * (3 * T * x ^ 4)) +
          20 * (2 * Q) * (2 * x ^ 3) := by
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (add_le_add hEb (by linarith)) (by positivity)
  linarith

/-- The logarithmic and divisor losses of the `k = 9` dual power with length `M ≤ 3T`. -/
def dualPowerLogFactor (C δ T : ℝ) : ℝ :=
  (1 + 9 * Real.log (3 * T)) * ((1 + 18 * Real.log (3 * T)) *
    ((C ^ 9 * (3 * T) ^ (81 * δ)) * (1 + Real.log (3 * T)) ^ 9))

/-- For `2 ≤ M ≤ 3T`, the mean value factor `(1 + 2 log L) A (1 + log M)^9` with
`L = M^9`, `A = (C L^δ)^9`, and its product with `1 + log L`, are at most
`dualPowerLogFactor C δ T`. -/
theorem dual_power_losses_le {M : ℕ} {C δ T : ℝ} (hM : 2 ≤ M) (hM3 : (M : ℝ) ≤ 3 * T)
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) :
    (1 + 2 * Real.log ((M ^ 9 : ℕ) : ℝ)) *
        ((C * (((M ^ 9 : ℕ) : ℝ)) ^ δ) ^ 9 * (1 + Real.log M) ^ 9) ≤
      dualPowerLogFactor C δ T ∧
    (1 + Real.log ((M ^ 9 : ℕ) : ℝ)) * ((1 + 2 * Real.log ((M ^ 9 : ℕ) : ℝ)) *
        ((C * (((M ^ 9 : ℕ) : ℝ)) ^ δ) ^ 9 * (1 + Real.log M) ^ 9)) ≤
      dualPowerLogFactor C δ T := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (by omega : 1 ≤ M)
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM1
  have hlogMT : Real.log M ≤ Real.log (3 * T) := Real.log_le_log hM0 hM3
  have hL : Real.log ((M ^ 9 : ℕ) : ℝ) = 9 * Real.log M := by
    push_cast; rw [Real.log_pow]; norm_num
  have hLδ : (((M ^ 9 : ℕ) : ℝ)) ^ δ ≤ (3 * T) ^ (9 * δ) := by
    push_cast
    rw [← Real.rpow_natCast, ← Real.rpow_mul hM0.le, mul_comm ((9 : ℕ) : ℝ) δ]
    rw [show (9 * δ) = δ * ((9 : ℕ) : ℝ) by push_cast; ring]
    exact Real.rpow_le_rpow (by positivity) hM3 (by positivity)
  have hA : (C * (((M ^ 9 : ℕ) : ℝ)) ^ δ) ^ 9 ≤ C ^ 9 * (3 * T) ^ (81 * δ) := by
    rw [mul_pow]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ((((M ^ 9 : ℕ) : ℝ)) ^ δ) ^ 9 ≤ ((3 * T) ^ (9 * δ)) ^ 9 :=
          pow_le_pow_left₀ (by positivity) hLδ 9
      _ = (3 * T) ^ (81 * δ) := by
          rw [← Real.rpow_mul_natCast (by linarith [hM3, hM1] : (0 : ℝ) ≤ 3 * T)]; ring_nf
  have hA0 : 0 ≤ (C * (((M ^ 9 : ℕ) : ℝ)) ^ δ) ^ 9 := by positivity
  have hPi : (1 + 2 * Real.log ((M ^ 9 : ℕ) : ℝ)) *
        ((C * (((M ^ 9 : ℕ) : ℝ)) ^ δ) ^ 9 * (1 + Real.log M) ^ 9) ≤
      (1 + 18 * Real.log (3 * T)) * ((C ^ 9 * (3 * T) ^ (81 * δ)) * (1 + Real.log (3 * T)) ^ 9) := by
    rw [hL]
    have h3T : (0 : ℝ) ≤ 3 * T := by linarith
    have hlog3 : 0 ≤ Real.log (3 * T) := hlogM.trans hlogMT
    exact mul_le_mul (by linarith) (mul_le_mul hA (pow_le_pow_left₀ (by linarith)
      (by linarith) 9) (pow_nonneg (by linarith) 9)
        (mul_nonneg (pow_nonneg hC 9) (Real.rpow_nonneg h3T _)))
      (mul_nonneg hA0 (pow_nonneg (by linarith) 9)) (by linarith)
  have hPi0 : 0 ≤ (1 + 2 * Real.log ((M ^ 9 : ℕ) : ℝ)) *
        ((C * (((M ^ 9 : ℕ) : ℝ)) ^ δ) ^ 9 * (1 + Real.log M) ^ 9) := by
    rw [hL]
    exact mul_nonneg (by linarith) (mul_nonneg hA0 (pow_nonneg (by linarith) 9))
  have hB0 : 0 ≤ (1 + 18 * Real.log (3 * T)) *
      ((C ^ 9 * (3 * T) ^ (81 * δ)) * (1 + Real.log (3 * T)) ^ 9) := hPi0.trans hPi
  have hlog3 : 0 ≤ Real.log (3 * T) := hlogM.trans hlogMT
  constructor
  · unfold dualPowerLogFactor
    calc _ ≤ (1 + 18 * Real.log (3 * T)) *
          ((C ^ 9 * (3 * T) ^ (81 * δ)) * (1 + Real.log (3 * T)) ^ 9) := hPi
      _ ≤ _ := le_mul_of_one_le_left hB0 (by linarith)
  · unfold dualPowerLogFactor
    rw [hL]
    rw [hL] at hPi hPi0
    exact mul_le_mul (by linarith) hPi hPi0 (by linarith)

/-- `dualPowerLogFactor C δ T ≤ T^γ` eventually, when `162 δ ≤ γ/2`. -/
theorem eventually_dualPowerLogFactor_le {C δ γ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hγ : 0 < γ)
    (hδγ : 162 * δ ≤ γ / 2) :
    ∀ᶠ T : ℝ in Filter.atTop, dualPowerLogFactor C δ T ≤ T ^ γ := by
  filter_upwards [eventually_mul_one_add_log_pow_le_rpow (18 * 36 * 2 ^ 9 * C ^ 9) 11
    (half_pos hγ), Filter.eventually_ge_atTop (3 : ℝ)] with T hT hT3
  have hT0 : 0 < T := by linarith
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have h3T : 3 * T ≤ T ^ 2 := by nlinarith
  have hlog3T : Real.log (3 * T) ≤ 2 * Real.log T := by
    rw [← Real.log_rpow hT0, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact Real.log_le_log (by positivity) h3T
  have hlog3T0 : 0 ≤ Real.log (3 * T) := Real.log_nonneg (by linarith)
  have hpow : (3 * T) ^ (81 * δ) ≤ T ^ (γ / 2) := by
    calc (3 * T) ^ (81 * δ) ≤ (T ^ 2) ^ (81 * δ) := Real.rpow_le_rpow (by positivity) h3T
          (by positivity)
      _ = T ^ (162 * δ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]; congr 1; push_cast; ring
      _ ≤ T ^ (γ / 2) := Real.rpow_le_rpow_of_exponent_le (by linarith) hδγ
  have hpoly : (1 + 9 * Real.log (3 * T)) * ((1 + 18 * Real.log (3 * T)) *
      (C ^ 9 * (1 + Real.log (3 * T)) ^ 9)) ≤ 18 * 36 * 2 ^ 9 * C ^ 9 * (1 + Real.log T) ^ 11 := by
    have h1 : 1 + 9 * Real.log (3 * T) ≤ 18 * (1 + Real.log T) := by linarith
    have h2 : 1 + 18 * Real.log (3 * T) ≤ 36 * (1 + Real.log T) := by linarith
    have h3 : (1 + Real.log (3 * T)) ^ 9 ≤ 2 ^ 9 * (1 + Real.log T) ^ 9 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) (by linarith) 9
    calc (1 + 9 * Real.log (3 * T)) * ((1 + 18 * Real.log (3 * T)) *
          (C ^ 9 * (1 + Real.log (3 * T)) ^ 9))
        ≤ (18 * (1 + Real.log T)) * ((36 * (1 + Real.log T)) *
          (C ^ 9 * (2 ^ 9 * (1 + Real.log T) ^ 9))) := by
          gcongr
      _ = 18 * 36 * 2 ^ 9 * C ^ 9 * (1 + Real.log T) ^ 11 := by ring
  unfold dualPowerLogFactor
  calc (1 + 9 * Real.log (3 * T)) * ((1 + 18 * Real.log (3 * T)) *
        ((C ^ 9 * (3 * T) ^ (81 * δ)) * (1 + Real.log (3 * T)) ^ 9))
      = ((1 + 9 * Real.log (3 * T)) * ((1 + 18 * Real.log (3 * T)) *
        (C ^ 9 * (1 + Real.log (3 * T)) ^ 9))) * (3 * T) ^ (81 * δ) := by ring
    _ ≤ T ^ (γ / 2) * T ^ (γ / 2) :=
        mul_le_mul (hpoly.trans hT) hpow (by positivity) (by positivity)
    _ = T ^ γ := by rw [← Real.rpow_add hT0]; ring_nf

/-- The multiplicities of `9`-fold products from `[1, M]` are at most `(C_δ (M^9)^δ)^9`. -/
theorem dualPowCount_le_divisorBound {M : ℕ} {δ : ℝ} (hδ : 0 < δ) :
    ∀ ℓ ∈ Finset.Icc 1 (M ^ 9), (dualPowCount M 9 ℓ : ℝ) ≤
      (divisorBoundConst δ * (((M ^ 9 : ℕ) : ℝ)) ^ δ) ^ 9 := by
  intro ℓ hℓ
  obtain ⟨hℓ1, hℓL⟩ := Finset.mem_Icc.1 hℓ
  have hℓ0 : ℓ ≠ 0 := by omega
  have h1 : (dualPowCount M 9 ℓ : ℝ) ≤ (ℓ.divisors.card : ℝ) ^ 9 := by
    exact_mod_cast dualPowCount_le M 9 hℓ0
  have h2 : (ℓ.divisors.card : ℝ) ≤ divisorBoundConst δ * (((M ^ 9 : ℕ) : ℝ)) ^ δ := by
    refine (card_divisors_le_rpow hδ hℓ0).trans ?_
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _)
      (by exact_mod_cast hℓL) hδ.le) (divisorBoundConst_pos hδ).le
  exact h1.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) h2 9)

/-- The final count: the window factor times the local bound is at most `T^{2σ-ε²/5}`. -/
theorem jutila_windowed_count_le {T Q σ ε η T₁ W K L P P' Pnear C₀ C₁ : ℝ} {N : ℕ}
    (hT : 1 ≤ T) (hε : 0 < ε) (hεs : ε ≤ 1 / 1000) (hσl : 5 * ε ≤ σ)
    (hσh : σ ≤ 23 / 100 - 5 * ε) (hη : η = ε ^ 2 / 100) (hN1 : 1 ≤ N) (hQ1 : 1 ≤ Q)
    (hQ3 : Q ^ 3 ≤ T ^ (ε ^ 2)) (hQe : Q ≤ T ^ (ε ^ 2 / 3)) (hQ2 : Q ^ 2 ≤ T ^ (2 * (ε ^ 2 / 3)))
    (hQ18 : Q ^ 18 ≤ T ^ (6 * ε ^ 2))
    (hNlo : T ^ ((9 : ℝ) / 11 - 10 * ε) ≤ (N : ℝ)) (hNhi : (N : ℝ) ≤ T ^ (1 - ε))
    (hT₁ : T₁ = (N : ℝ) ^ (2 - 34 / 9 * σ) / Q ^ 2) (hT₁1 : 1 ≤ T₁) (hW : W = min T₁ (2 * T))
    (hK : K = (160 * Real.sqrt Real.pi * Q) ^ 18 * (N : ℝ) ^ (36 * σ - 9))
    (hL0 : 0 ≤ L) (hKL : K * L ≤ C₀ * (N : ℝ) ^ (2 * σ + 9 * η))
    (hP0 : 0 ≤ P) (hP : P ≤ T ^ η) (hP'0 : 0 ≤ P') (hP' : P' ≤ T ^ η)
    (hPnear : Pnear = 240 * (2 * (1 + Real.log T) + 1) * (2 * Q) * (N : ℝ) ^ (2 * σ))
    (hC₁ : C₁ = 7 * (160 * Real.sqrt Real.pi) ^ 18)
    (hc1 : 960 * (3 + 2 * Real.log T) ≤ T ^ η / 8) (hc2 : 8 * C₀ ≤ T ^ η / 8)
    (hc3 : C₁ ≤ T ^ η / 8) :
    ((⌊2 * T / W⌋₊ : ℝ) + 1) * (Pnear + K * ((W + 1) * P + 4 * L * P')) ≤
      T ^ (2 * σ - ε ^ 2 / 5) := by
  subst hη
  have hT0 : 0 < T := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hQ0 : 0 < Q := by linarith
  have hlog : 0 ≤ Real.log T := Real.log_nonneg hT
  obtain ⟨hF1, hF2⟩ := jutila_window_count_le hT hT₁1 hW
  have hW1 : 1 ≤ W := by rw [hW]; exact le_min hT₁1 (by linarith)
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hPn0 : 0 ≤ Pnear := by rw [hPnear]; positivity
  have hF0 : 0 ≤ (⌊2 * T / W⌋₊ : ℝ) + 1 := by positivity
  have hTT₁ : 0 ≤ 2 * T / T₁ := by positivity
  -- the reciprocal window length
  have hinvT₁ : 2 * T / T₁ = 2 * (Q ^ 2 * (T * (N : ℝ) ^ (-(2 - 34 / 9 * σ)))) := by
    rw [hT₁, Real.rpow_neg hN0.le]; field_simp
  -- the five terms
  have X1 := jutila_term_near_diag (N := N) hT hε hσl hQ0.le hQe
    (natCast_rpow_le_of_le_rpow hT hNhi (by linarith)) hc1
  have X2 := jutila_term_near_windows (N := N) hT hε hεs hσh hQ0.le hQ3
    (natCast_rpow_le_of_rpow_le hT hNlo (by linarith)) hc1
  have X3 := jutila_term_dual_diag (N := N) hT hε hσl hP'0
    (natCast_rpow_le_of_le_rpow hT hNhi (add_nonneg (by linarith) (by positivity))) hc2 hP'
  have hε2 : ε ^ 2 ≤ (1 / 1000) ^ 2 := pow_le_pow_left₀ hε.le hεs 2
  have X4 := jutila_term_dual_windows (N := N) hT hε hεs hσh hP'0 hQ2
    (natCast_rpow_le_of_rpow_le hT hNlo (by linarith)) hc2 hP'
  have X5 := jutila_term_long (N := N) hT hε hεs hσh hP0 hQ18
    (natCast_rpow_le_of_rpow_le hT hNlo (by linarith)) hc3 hP
  -- near terms
  have hnear : ((⌊2 * T / W⌋₊ : ℝ) + 1) * Pnear ≤
      960 * (3 + 2 * Real.log T) * (Q * (N : ℝ) ^ (2 * σ)) +
        960 * (3 + 2 * Real.log T) * (Q ^ 3 * (T * (N : ℝ) ^ (-2 + 52 / 9 * σ))) := by
    have e1 : (N : ℝ) ^ (-(2 - 34 / 9 * σ)) * (N : ℝ) ^ (2 * σ) = (N : ℝ) ^ (-2 + 52 / 9 * σ) := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    calc ((⌊2 * T / W⌋₊ : ℝ) + 1) * Pnear ≤ (2 * T / T₁ + 2) * Pnear :=
          mul_le_mul_of_nonneg_right hF1 hPn0
      _ = _ := by
          rw [hinvT₁, hPnear, ← e1]; ring
  -- long-window term
  have hlong : ((⌊2 * T / W⌋₊ : ℝ) + 1) * (K * ((W + 1) * P)) ≤
      C₁ * (Q ^ 18 * ((T * (N : ℝ) ^ (36 * σ - 9)) * P)) := by
    calc ((⌊2 * T / W⌋₊ : ℝ) + 1) * (K * ((W + 1) * P)) =
          (((⌊2 * T / W⌋₊ : ℝ) + 1) * (W + 1)) * (K * P) := by ring
      _ ≤ (7 * T) * (K * P) := mul_le_mul_of_nonneg_right hF2 (by positivity)
      _ = _ := by rw [hK, hC₁, mul_pow]; ring
  -- dual terms
  have hdual : ((⌊2 * T / W⌋₊ : ℝ) + 1) * (K * (4 * L * P')) ≤
      8 * C₀ * ((N : ℝ) ^ (2 * σ + 9 * (ε ^ 2 / 100)) * P') +
        8 * C₀ * (Q ^ 2 * ((T * (N : ℝ) ^ (-2 + 52 / 9 * σ + 9 * (ε ^ 2 / 100))) * P')) := by
    have e1 : (N : ℝ) ^ (-(2 - 34 / 9 * σ)) * (N : ℝ) ^ (2 * σ + 9 * (ε ^ 2 / 100)) =
        (N : ℝ) ^ (-2 + 52 / 9 * σ + 9 * (ε ^ 2 / 100)) := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    have hKL' : K * (4 * L * P') ≤ 4 * (C₀ * (N : ℝ) ^ (2 * σ + 9 * (ε ^ 2 / 100))) * P' := by
      calc K * (4 * L * P') = 4 * (K * L) * P' := by ring
        _ ≤ 4 * (C₀ * (N : ℝ) ^ (2 * σ + 9 * (ε ^ 2 / 100))) * P' :=
            mul_le_mul_of_nonneg_right (by linarith) hP'0
    calc ((⌊2 * T / W⌋₊ : ℝ) + 1) * (K * (4 * L * P'))
        ≤ (2 * T / T₁ + 2) * (4 * (C₀ * (N : ℝ) ^ (2 * σ + 9 * (ε ^ 2 / 100))) * P') :=
          mul_le_mul hF1 hKL' (by positivity) (by positivity)
      _ = _ := by rw [hinvT₁, ← e1]; ring
  calc ((⌊2 * T / W⌋₊ : ℝ) + 1) * (Pnear + K * ((W + 1) * P + 4 * L * P'))
      = ((⌊2 * T / W⌋₊ : ℝ) + 1) * Pnear + ((⌊2 * T / W⌋₊ : ℝ) + 1) * (K * ((W + 1) * P)) +
          ((⌊2 * T / W⌋₊ : ℝ) + 1) * (K * (4 * L * P')) := by ring
    _ ≤ (960 * (3 + 2 * Real.log T) * (Q * (N : ℝ) ^ (2 * σ)) +
          960 * (3 + 2 * Real.log T) * (Q ^ 3 * (T * (N : ℝ) ^ (-2 + 52 / 9 * σ)))) +
        C₁ * (Q ^ 18 * ((T * (N : ℝ) ^ (36 * σ - 9)) * P)) +
        (8 * C₀ * ((N : ℝ) ^ (2 * σ + 9 * (ε ^ 2 / 100)) * P') +
          8 * C₀ * (Q ^ 2 * ((T * (N : ℝ) ^ (-2 + 52 / 9 * σ + 9 * (ε ^ 2 / 100))) * P'))) :=
        add_le_add (add_le_add hnear hlong) hdual
    _ ≤ (T ^ (2 * σ - ε ^ 2 / 5) / 8 + T ^ (2 * σ - ε ^ 2 / 5) / 8) +
          T ^ (2 * σ - ε ^ 2 / 5) / 8 +
        (T ^ (2 * σ - ε ^ 2 / 5) / 8 + T ^ (2 * σ - ε ^ 2 / 5) / 8) :=
        add_le_add (add_le_add (add_le_add X1 X2) X5) (add_le_add X3 X4)
    _ ≤ T ^ (2 * σ - ε ^ 2 / 5) := by
        have : 0 ≤ T ^ (2 * σ - ε ^ 2 / 5) := Real.rpow_nonneg hT0.le _
        linarith

/-- The window length `T₁ = N^{2-34σ/9}/Q²` exceeds `(2j+5) N`. -/
theorem jutila_window_length_ge {T Q σ ε J : ℝ} {N : ℕ} (hT : 1 ≤ T) (hε : 0 < ε)
    (hεs : ε ≤ 1 / 1000) (hσh : σ ≤ 23 / 100 - 5 * ε) (hN1 : 1 ≤ N) (hQ0 : 0 < Q)
    (hQ2 : Q ^ 2 ≤ T ^ (2 * (ε ^ 2 / 3))) (hJ : J ≤ T ^ (1 / 20 : ℝ))
    (hNlo : T ^ ((9 : ℝ) / 11 - 10 * ε) ≤ (N : ℝ)) :
    J * N ≤ (N : ℝ) ^ (2 - 34 / 9 * σ) / Q ^ 2 := by
  have hT0 : 0 < T := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hl : (1 : ℝ) / 10 ≤ 2 - 34 / 9 * σ - 1 := by linarith
  have h1 : J * Q ^ 2 ≤ T ^ ((1 : ℝ) / 20 + 2 * (ε ^ 2 / 3)) := by
    rw [Real.rpow_add hT0]
    exact mul_le_mul hJ hQ2 (by positivity) (Real.rpow_nonneg hT0.le _)
  have h2 : T ^ ((1 : ℝ) / 20 + 2 * (ε ^ 2 / 3)) ≤
      T ^ (((9 : ℝ) / 11 - 10 * ε) * (2 - 34 / 9 * σ - 1)) := by
    refine Real.rpow_le_rpow_of_exponent_le hT ?_
    have hε2 : ε ^ 2 ≤ (1 / 1000) ^ 2 := pow_le_pow_left₀ hε.le hεs 2
    nlinarith
  have h3 : T ^ (((9 : ℝ) / 11 - 10 * ε) * (2 - 34 / 9 * σ - 1)) ≤
      (N : ℝ) ^ (2 - 34 / 9 * σ - 1) := by
    rw [Real.rpow_mul hT0.le]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hT0.le _) hNlo (by linarith)
  have h4 : (N : ℝ) ^ (2 - 34 / 9 * σ) = N * (N : ℝ) ^ (2 - 34 / 9 * σ - 1) := by
    conv_lhs => rw [show 2 - 34 / 9 * σ = 1 + (2 - 34 / 9 * σ - 1) by ring]
    rw [Real.rpow_add hN0, Real.rpow_one]
  rw [h4, le_div_iff₀ (by positivity)]
  have := h1.trans (h2.trans h3)
  calc J * N * Q ^ 2 = N * (J * Q ^ 2) := by ring
    _ ≤ N * (N : ℝ) ^ (2 - 34 / 9 * σ - 1) := mul_le_mul_of_nonneg_left this hN0.le

/-- The dual length `M = ⌈N^η (W + 2j + 2)/N⌉ + 2`: it absorbs the window, is at most `3T`, and
at most `2 N^η T₁/N`. -/
theorem exists_jutila_dual_length {T T₁ W η : ℝ} {N j : ℕ} (hN1 : 1 ≤ N) (hη0 : 0 ≤ η)
    (hη1 : η ≤ 1) (hW1 : 1 ≤ W) (hWT₁ : W ≤ T₁) (hW2T : W ≤ 2 * T)
    (hT₁ : (2 * (j : ℝ) + 5) * N ≤ T₁) (hT : 2 * (j : ℝ) + 5 ≤ T) :
    ∃ M : ℕ, 2 ≤ M ∧ (N : ℝ) ^ η * (W + 2 * j + 2) ≤ M * N ∧ (M : ℝ) ≤ 3 * T ∧
      (M : ℝ) ≤ 2 * ((N : ℝ) ^ η * T₁ / N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  set x : ℝ := (N : ℝ) ^ η * (W + 2 * j + 2) / N with hxdef
  have hx0 : 0 ≤ x := by positivity
  refine ⟨⌈x⌉₊ + 2, by omega, ?_, ?_, ?_⟩
  · have := Nat.le_ceil x
    rw [hxdef, div_le_iff₀ hN0] at this
    push_cast
    nlinarith
  · have hNηN : (N : ℝ) ^ η ≤ N := by
      calc (N : ℝ) ^ η ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1r hη1
        _ = N := Real.rpow_one _
    have hxle : x ≤ W + 2 * j + 2 := by
      rw [hxdef, div_le_iff₀ hN0]
      calc (N : ℝ) ^ η * (W + 2 * j + 2) ≤ N * (W + 2 * j + 2) :=
            mul_le_mul_of_nonneg_right hNηN (by positivity)
        _ = (W + 2 * j + 2) * N := by ring
    have := Nat.ceil_lt_add_one hx0
    push_cast
    linarith
  · have hNη1 : 1 ≤ (N : ℝ) ^ η := Real.one_le_rpow hN1r hη0
    have h1 : (N : ℝ) ^ η * (2 * j + 2) / N + 3 ≤ (N : ℝ) ^ η * T₁ / N := by
      rw [div_add' _ _ _ hN0.ne', div_le_div_iff_of_pos_right hN0]
      have h5 : (N : ℝ) ^ η * (2 * j + 2) + 3 * N ≤ (N : ℝ) ^ η * ((2 * j + 5) * N) := by
        have : (N : ℝ) ^ η * (2 * j + 2) ≤ (N : ℝ) ^ η * ((2 * j + 2) * N) :=
          mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
        nlinarith
      exact h5.trans (mul_le_mul_of_nonneg_left hT₁ (by positivity))
    have h2 : x ≤ (N : ℝ) ^ η * T₁ / N + (N : ℝ) ^ η * (2 * j + 2) / N := by
      rw [hxdef, ← add_div, ← mul_add]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith)
        (by positivity)) hN0.le
    have := Nat.ceil_lt_add_one hx0
    push_cast
    linarith

/-- **Matomäki–Teräväinen Lemma 4.1 at Jutila strength, energy form.**  For every small `ε > 0`
there is `T₀` beyond which: for a coefficient vector `a` of length `N ∈ [T^{9/11-10ε}, T^{1-ε}]`
with `‖a‖² ≤ Q/N`, `1 ≤ Q`, `Q³ ≤ T^{ε²}`, and every `σ ∈ [5ε, 23/100 - 5ε]`, a one-separated
set of ordinates of diameter `≤ 2T` on which the dyadic Dirichlet polynomial reaches `N^{-σ}` has
at most `T^{2σ-ε²/5}` points.  The proof is Jutila's: local estimate (`k = 9`) on windows of
length `N^{2-34σ/9}/Q²`, dual length `N^{ε²/100 - 1}` times the window. -/
theorem exists_lemma41_jutila_energy {eps : ℝ} (heps : 0 < eps) (hepss : eps ≤ 1 / 1000) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ (T : ℝ) (N : ℕ) (sigma Q : ℝ) (a : EuclideanSpace ℂ (Fin N))
      (S : Finset ℝ),
      T₀ ≤ T → 1 ≤ Q → Q ^ 3 ≤ T ^ (eps ^ 2) →
      T ^ ((9 : ℝ) / 11 - 10 * eps) ≤ (N : ℝ) → (N : ℝ) ≤ T ^ (1 - eps) →
      5 * eps ≤ sigma → sigma ≤ 23 / 100 - 5 * eps →
      ‖a‖ ^ 2 ≤ Q / (N : ℝ) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|) →
      (∀ x ∈ S, ∀ y ∈ S, |x - y| ≤ 2 * T) →
      (∀ x ∈ S, (N : ℝ) ^ (-sigma) ≤ ‖⟪dyadicDirRow N x, a⟫_ℂ‖) →
      (S.card : ℝ) ≤ T ^ (2 * sigma - eps ^ 2 / 5) := by
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = eps ^ 2 / 100 := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hηdef]; positivity
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = eps ^ 2 / 32400 := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  obtain ⟨j, hjdef⟩ : ∃ j : ℕ, j = ⌈3 / η⌉₊ + 1 := ⟨_, rfl⟩
  have hj1 : 1 ≤ j := by omega
  have hjη : 6 ≤ 2 * (j : ℝ) * η := by
    have h1 : 3 / η ≤ (⌈3 / η⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (j : ℝ) = (⌈3 / η⌉₊ : ℝ) + 1 := by rw [hjdef]; push_cast; ring
    have h3 : 3 ≤ (⌈3 / η⌉₊ : ℝ) * η := by rwa [div_le_iff₀ hη0] at h1
    rw [h2]; nlinarith
  obtain ⟨Cj, hCj0, hloc⟩ := exists_card_le_jutila_local (j := j) (k := 9) hj1 (by norm_num)
  obtain ⟨Cδ, hCδdef⟩ : ∃ Cδ : ℝ, Cδ = divisorBoundConst δ := ⟨_, rfl⟩
  have hCδ0 : 0 ≤ Cδ := by rw [hCδdef]; exact (divisorBoundConst_pos hδ0).le
  obtain ⟨C₀, hC₀def⟩ : ∃ C₀ : ℝ, C₀ = 2 ^ 9 * (160 * Real.sqrt Real.pi) ^ 18 := ⟨_, rfl⟩
  obtain ⟨C₁, hC₁def⟩ : ∃ C₁ : ℝ, C₁ = 7 * (160 * Real.sqrt Real.pi) ^ 18 := ⟨_, rfl⟩
  have hev : ∀ᶠ T : ℝ in Filter.atTop, 1 ≤ T ∧
      960 * (3 + 2 * Real.log T) ≤ T ^ η / 8 ∧ 8 * C₀ ≤ T ^ η / 8 ∧ C₁ ≤ T ^ η / 8 ∧
      dualPowerLogFactor Cδ δ T ≤ T ^ η ∧ 2 * (j : ℝ) + 5 ≤ T ∧
      2 * (j : ℝ) + 5 ≤ T ^ (1 / 20 : ℝ) ∧ 1920 * Cj ≤ T ∧ 1280 ≤ T := by
    have e2 := eventually_mul_one_add_log_pow_le_rpow (8 * (960 * 3)) 1 hη0
    have e3 := eventually_mul_one_add_log_pow_le_rpow (8 * (8 * C₀)) 0 hη0
    have e4 := eventually_mul_one_add_log_pow_le_rpow (8 * C₁) 0 hη0
    have e5 := eventually_dualPowerLogFactor_le hCδ0 hδ0.le hη0 (by rw [hδdef, hηdef]; ring_nf; rfl)
    have e7 := eventually_mul_one_add_log_pow_le_rpow (2 * (j : ℝ) + 5) 0
      (by norm_num : (0 : ℝ) < 1 / 20)
    filter_upwards [e2, e3, e4, e5, e7, Filter.eventually_ge_atTop (1 : ℝ),
      Filter.eventually_ge_atTop (2 * (j : ℝ) + 5), Filter.eventually_ge_atTop (1920 * Cj),
      Filter.eventually_ge_atTop (1280 : ℝ)] with T h2 h3 h4 h5 h7 h1 h6 h8 h9
    have hlog : 0 ≤ Real.log T := Real.log_nonneg h1
    rw [pow_one] at h2
    rw [pow_zero, mul_one] at h3 h4 h7
    exact ⟨h1, by linarith, by linarith, by linarith, h5, h6, h7, h8, h9⟩
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨max T₀ 1, le_max_right _ _, ?_⟩
  intro T N sigma Q a S hT hQ1 hQ3 hNlo hNhi hsl hsh hmass hsep hspread hbig
  obtain ⟨hT1, hc1, hc2, hc3, hpoly, hT2j, hT2j', hTC, hT4⟩ :=
    hT₀ T (le_trans (le_max_left _ _) hT)
  have hT0 : 0 < T := by linarith
  have hN1r : (1 : ℝ) ≤ N := le_trans (Real.one_le_rpow hT1 (by linarith)) hNlo
  have hN1 : 1 ≤ N := by exact_mod_cast hN1r
  have hN0 : (0 : ℝ) < N := by linarith
  have hQ0 : 0 < Q := by linarith
  -- the energy bounds
  have hQe : Q ≤ T ^ (eps ^ 2 / 3) := by
    have e : (T ^ (eps ^ 2 / 3)) ^ 3 = T ^ (eps ^ 2) := by
      rw [← Real.rpow_mul_natCast hT0.le]; ring_nf
    by_contra h
    rw [not_le] at h
    have := pow_lt_pow_left₀ h (Real.rpow_nonneg hT0.le _) (by norm_num : (3 : ℕ) ≠ 0)
    rw [e] at this
    linarith
  have hQ2 : Q ^ 2 ≤ T ^ (2 * (eps ^ 2 / 3)) := by
    calc Q ^ 2 ≤ (T ^ (eps ^ 2 / 3)) ^ 2 := pow_le_pow_left₀ hQ0.le hQe 2
      _ = T ^ (2 * (eps ^ 2 / 3)) := by rw [← Real.rpow_mul_natCast hT0.le]; ring_nf
  have hQ18 : Q ^ 18 ≤ T ^ (6 * eps ^ 2) := by
    calc Q ^ 18 = (Q ^ 3) ^ 6 := by ring
      _ ≤ (T ^ (eps ^ 2)) ^ 6 := pow_le_pow_left₀ (by positivity) hQ3 6
      _ = T ^ (6 * eps ^ 2) := by rw [← Real.rpow_mul_natCast hT0.le]; ring_nf
  -- coefficients
  obtain ⟨c, hca, hcG⟩ := exists_blockCoeff_one_eq N a
  have hG : ∑ n ∈ Finset.Ico N (2 * N), ‖c n‖ ^ 2 / (n : ℝ) ≤ 2 * Q := by
    calc _ ≤ 2 * N * ‖a‖ ^ 2 := hcG
      _ ≤ 2 * N * (Q / N) := mul_le_mul_of_nonneg_left hmass (by positivity)
      _ = 2 * Q := by field_simp
  have hbig' : ∀ x ∈ S, (N : ℝ) ^ (-sigma) ≤ ‖blockPoly N c 1 x‖ := by
    intro x hx
    rw [← inner_dyadicDirRow_blockCoeff, hca]
    exact hbig x hx
  -- the window length and the dual length
  obtain ⟨T₁, hT₁def⟩ : ∃ T₁ : ℝ, T₁ = (N : ℝ) ^ (2 - 34 / 9 * sigma) / Q ^ 2 := ⟨_, rfl⟩
  have hT₁big : (2 * (j : ℝ) + 5) * N ≤ T₁ := by
    rw [hT₁def]
    exact jutila_window_length_ge hT1 heps hepss hsh hN1 hQ0 hQ2 hT2j' hNlo
  have hT₁1 : 1 ≤ T₁ := le_trans (by nlinarith) hT₁big
  obtain ⟨W, hWdef⟩ : ∃ W : ℝ, W = min T₁ (2 * T) := ⟨_, rfl⟩
  have hW1 : 1 ≤ W := by rw [hWdef]; exact le_min hT₁1 (by linarith)
  have hWT₁ : W ≤ T₁ := by rw [hWdef]; exact min_le_left _ _
  have hW2T : W ≤ 2 * T := by rw [hWdef]; exact min_le_right _ _
  have hη1 : η ≤ 1 := by
    have hε2 : eps ^ 2 ≤ (1 / 1000) ^ 2 := pow_le_pow_left₀ heps.le hepss 2
    rw [hηdef]; linarith
  obtain ⟨M, hM2, hMN, hM3T, hMT₁⟩ :=
    exists_jutila_dual_length hN1 hη0.le hη1 hW1 hWT₁ hW2T hT₁big hT2j
  -- the local estimate on every window
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hτ₁1 : 1 ≤ 1 + Real.log T := by linarith
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = ((M ^ 9 : ℕ) : ℝ) := ⟨_, rfl⟩
  have hL1 : 1 ≤ L := by rw [hLdef]; exact_mod_cast Nat.one_le_pow _ _ (by omega)
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ M))
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = (Cδ * (((M ^ 9 : ℕ) : ℝ)) ^ δ) ^ 9 := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hA : ∀ ℓ ∈ Finset.Icc 1 (M ^ 9), (dualPowCount M 9 ℓ : ℝ) ≤ A := by
    rw [hAdef, hCδdef]; exact dualPowCount_le_divisorBound hδ0
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = (1 + 2 * Real.log L) * (A * (1 + Real.log M) ^ 9) :=
    ⟨_, rfl⟩
  have hP0 : 0 ≤ P := by rw [hPdef]; positivity
  obtain ⟨Pnear, hPneardef⟩ : ∃ Pnear : ℝ,
      Pnear = 240 * (2 * (1 + Real.log T) + 1) * (2 * Q) * (N : ℝ) ^ (2 * sigma) := ⟨_, rfl⟩
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ,
      K = (160 * Real.sqrt Real.pi * Q) ^ 18 * (N : ℝ) ^ (36 * sigma - 9) := ⟨_, rfl⟩
  have hsmall := jutila_reflection_error_le (Q := Q) (σ := sigma) (Cj := Cj) (W := W) (j := j)
    hT1 hTC hT4 heps hepss (by linarith) (by linarith) hCj0 hQ1 hQe hNlo hNhi hN1 hM2 hM3T
    hjη (by linarith) hMN
  have hlocal : ∀ S' ⊆ S, (∀ x ∈ S', ∀ y ∈ S', |x - y| ≤ W) →
      (S'.card : ℝ) ≤ Pnear + K * ((W + 1) * P + 4 * L * ((1 + Real.log L) * P)) := by
    intro S' hS' hdiam
    have h := hloc N M c S' W ((N : ℝ) ^ (-sigma)) (2 * Q) (1 + Real.log T) A hN1 hM2
      (by linarith) (Real.rpow_pos_of_pos hN0 _) hτ₁1 hA0 hG hA
      (fun x hx y hy hxy => hsep x (hS' hx) y (hS' hy) hxy) hdiam
      (fun x hx => hbig' x (hS' hx)) hsmall
    rw [jutila_nearTerm_eq hN1, jutila_highMoment_factor_eq hN1, ← hLdef] at h
    refine h.trans (le_of_eq ?_)
    rw [hPneardef, hKdef, hPdef]
    ring
  have hB0 : 0 ≤ Pnear + K * ((W + 1) * P + 4 * L * ((1 + Real.log L) * P)) := by
    rw [hPneardef, hKdef]; positivity
  have hcount := card_le_of_finset_window_bound (by linarith : (0 : ℝ) < W) hB0 hspread hlocal
  -- the losses
  obtain ⟨hPle, hP'le⟩ := dual_power_losses_le (T := T) hM2 hM3T hCδ0 hδ0.le
  rw [← hAdef, ← hLdef] at hPle hP'le
  rw [← hPdef] at hPle hP'le
  have hKL := jutila_highMoment_mul_dualLength_le (M := M) hN1 (σ := sigma) (η := η) hQ1
    (by rw [← hT₁def]; exact hMT₁)
  rw [← hKdef, ← hLdef, ← hC₀def] at hKL
  refine hcount.trans ?_
  exact jutila_windowed_count_le (K := K) (L := L) (P := P) (P' := (1 + Real.log L) * P)
    (Pnear := Pnear) (C₀ := C₀) (C₁ := C₁) hT1 heps hepss hsl hsh hηdef hN1 hQ1 hQ3 hQe hQ2 hQ18
    hNlo hNhi hT₁def hT₁1 hWdef hKdef (by linarith) hKL hP0 (hPle.trans hpoly)
    (by positivity) (hP'le.trans hpoly) hPneardef hC₁def hc1 hc2 hc3

/-- Jutila's estimate gives Lemma 4.1 up to `23/100`. -/
theorem energyLargeValuesBound_jutila : EnergyLargeValuesBound (23 / 100) := by
  intro eps heps hepss
  obtain ⟨T₀, hT₀1, h⟩ := exists_lemma41_jutila_energy heps hepss
  exact ⟨T₀, hT₀1, fun T N sigma Q a S hT hQ1 hQ3 hNlo hNhi hsl hsh hmass _ hsep hspread hbig =>
    h T N sigma Q a S hT hQ1 hQ3 hNlo hNhi hsl hsh hmass hsep hspread hbig⟩

end

end RHTower.Sieve
