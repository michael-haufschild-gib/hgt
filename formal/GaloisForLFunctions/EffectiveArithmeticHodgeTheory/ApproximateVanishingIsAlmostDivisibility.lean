import GaloisForLFunctions.EffectiveArithmeticHodgeTheory.TheBezoutTheoremOfTheMultiplicativeGroup

/-!
# Approximate vanishing is almost divisibility

A producer at square-root precision needs auxiliaries that are *small*, not zero, at the primes.
This file proves that small values along a Frobenius progression are no cheaper than zeros.

On the progression `s_j = 2πij/log p` a Dirichlet polynomial of length `N` is the exponential sum
`D(s_j) = Σ_w C_w w^j` over the distinct roots of unity `w = ω_p(n) = e^{−2πi log n/log p}`, whose
coefficients `C_w` are the `p`-tower sums `Σ_k a(p^k n)` (`dirDeriv_zero_frobPoint_eq`). Exact
vanishing at all large `j` is the vanishing of every `C_w` (Bézout). Quantitatively:

* **Separation** (`norm_frobRoot_sub_ge`). Distinct roots are `4/(Np log p)` apart: the angle
  `2π(log m − log n)/log p` is at distance `|log A − log B|/log p` from `2πℤ` for integers
  `A ≠ B ≤ Np`, and integrality gives `|log A − log B| ≥ 1/max(A, B)`.
* **Mean values on a stretch** (`sum_normSq_expSum_ge`). For unimodular points `δ`-apart,
  `Σ_{j<J} |Σ_w C_w w^{J₀+j}|² ≥ (J − 2|T|/δ) Σ_w |C_w|²`: the diagonal gives `J`, and each
  off-diagonal geometric sum is at most `2/δ`.
* **Approximate Bézout** (`sum_normSq_towerSums_le`). If `|D(s_j)| ≤ ε` for `J ≥ N²p log p`
  consecutive points of the progression, then `Σ_w |C_w|² ≤ 2ε²`: every `p`-tower sum is
  `√2 ε`-small, so `D` is within `√2 ε` (in coefficients) of the multiples of `1 − p^{−s}`.

No Baker bound is needed: the frequencies `log n/log p` of a length-`N` polynomial are separated
polynomially in `N` by integrality alone, because the exponents involved are `O(log N)`.
-/

open Complex Finset Filter
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.EffectiveArithmeticHodgeTheory

/-! ### The values on a progression -/

/-- On the progression of `p`, the Dirichlet polynomial is an exponential sum in the roots `ω_p(n)`. -/
theorem dirDeriv_zero_frobPoint (a : ℕ → ℂ) (N p : ℕ) (j : ℤ) :
    dirDeriv a N 0 (frobPoint p j) = ∑ n ∈ Icc 1 N, a n * frobRoot p n ^ j := by
  rw [dirDeriv]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [pow_zero, mul_one, cpow_neg_frobPoint (by have := (Finset.mem_Icc.mp hn).1; omega)]

/-- Grouped by roots: `Σ_n a_n ω_p(n)^j = Σ_w C_w w^j`, `C_w = Σ_{ω_p(n) = w} a_n`. -/
theorem dirDeriv_zero_frobPoint_eq (a : ℕ → ℂ) (N p : ℕ) (j : ℤ) :
    dirDeriv a N 0 (frobPoint p j) = ∑ w ∈ (Icc 1 N).image (frobRoot p),
      (∑ n ∈ Icc 1 N with frobRoot p n = w, a n) * w ^ j := by
  classical
  rw [dirDeriv_zero_frobPoint, ← Finset.sum_fiberwise_of_maps_to (t := (Icc 1 N).image (frobRoot p))
    (g := frobRoot p) (fun n hn => Finset.mem_image_of_mem _ hn)]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun n hn => by rw [(Finset.mem_filter.mp hn).2]

/-! ### Separation -/

theorem frobRoot_eq_exp (p n : ℕ) :
    frobRoot p n = cexp (((-(2 * π * Real.log n / Real.log p) : ℝ) : ℂ) * I) := by
  rw [frobRoot]
  congr 1
  push_cast
  ring

theorem norm_frobRoot (p n : ℕ) : ‖frobRoot p n‖ = 1 := by
  rw [frobRoot_eq_exp, norm_exp_ofReal_mul_I]

/-- `|log A − log B| ≥ 1/max(A, B)` for distinct positive integers. -/
theorem inv_le_abs_log_sub {A B : ℕ} (hA : 0 < A) (hB : 0 < B) (hAB : A ≠ B) {M : ℝ}
    (hAM : (A : ℝ) ≤ M) (hBM : (B : ℝ) ≤ M) : 1 / M ≤ |Real.log A - Real.log B| := by
  have hA' : (0 : ℝ) < A := by exact_mod_cast hA
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hM : 0 < M := lt_of_lt_of_le hA' hAM
  rcases lt_or_gt_of_ne hAB with h | h
  · -- `A < B`: `log B − log A ≥ 1 − A/B ≥ 1/B`
    have h1 : (A : ℝ) + 1 ≤ B := by exact_mod_cast h
    have hlog : 1 - (A : ℝ) / B ≤ Real.log B - Real.log A := by
      have := Real.log_le_sub_one_of_pos (div_pos hA' hB')
      rw [Real.log_div hA'.ne' hB'.ne'] at this
      linarith
    have h2 : 1 / M ≤ 1 - (A : ℝ) / B := by
      rw [div_le_iff₀ hM]
      have : (1 - (A : ℝ) / B) = (B - A) / B := by field_simp
      rw [this, div_mul_eq_mul_div, le_div_iff₀ hB']
      nlinarith
    have hfrac : (A : ℝ) / B < 1 := (div_lt_one hB').mpr (by linarith)
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  · have h1 : (B : ℝ) + 1 ≤ A := by exact_mod_cast h
    have hlog : 1 - (B : ℝ) / A ≤ Real.log A - Real.log B := by
      have := Real.log_le_sub_one_of_pos (div_pos hB' hA')
      rw [Real.log_div hB'.ne' hA'.ne'] at this
      linarith
    have h2 : 1 / M ≤ 1 - (B : ℝ) / A := by
      rw [div_le_iff₀ hM]
      have : (1 - (B : ℝ) / A) = (A - B) / A := by field_simp
      rw [this, div_mul_eq_mul_div, le_div_iff₀ hA']
      nlinarith
    have hfrac : (B : ℝ) / A < 1 := (div_lt_one hA').mpr (by linarith)
    rw [abs_of_nonneg (by linarith)]
    linarith

/-- `|1 − e^{iθ}| ≥ 4 dist(θ/2π, ℤ)`. -/
theorem four_mul_abs_sub_round_le (x : ℝ) :
    4 * |x - round x| ≤ ‖cexp ((((2 * π * x) : ℝ) : ℂ) * I) - 1‖ := by
  rw [mul_comm _ I, norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_two]
  set y := x - round x
  have hy : |y| ≤ 1 / 2 := abs_sub_round x
  have hsin : Real.sin (2 * π * x / 2) = Real.sin (π * y) * (-1) ^ (round x) := by
    have : 2 * π * x / 2 = π * y + (round x : ℝ) * π := by simp only [y]; ring
    rw [this, Real.sin_add_int_mul_pi]
    ring
  rw [hsin, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, mul_one]
  have key : 2 * |y| ≤ |Real.sin (π * y)| := by
    rcases le_or_gt 0 y with h | h
    · rw [abs_of_nonneg h]
      have h1 : π * y ≤ π / 2 := by nlinarith [Real.pi_pos, abs_le.mp hy]
      have := Real.mul_le_sin (mul_nonneg Real.pi_pos.le h) h1
      have h0 : 0 ≤ 2 / π * (π * y) := mul_nonneg (by positivity) (mul_nonneg Real.pi_pos.le h)
      rw [abs_of_nonneg (by linarith)]
      calc 2 * y = 2 / π * (π * y) := by field_simp
        _ ≤ _ := this
    · rw [abs_of_neg h]
      have h1 : π * -y ≤ π / 2 := by nlinarith [Real.pi_pos, abs_le.mp hy]
      have hy0 : 0 ≤ -y := by linarith
      have := Real.mul_le_sin (mul_nonneg Real.pi_pos.le hy0) h1
      have h0 : 0 ≤ 2 / π * (π * -y) := mul_nonneg (by positivity) (mul_nonneg Real.pi_pos.le hy0)
      rw [show π * y = -(π * -y) by ring, Real.sin_neg, abs_neg, abs_of_nonneg (by linarith)]
      calc 2 * -y = 2 / π * (π * -y) := by field_simp
        _ ≤ _ := this
  linarith

/-- **Separation of the roots**: distinct values `ω_p(n) ≠ ω_p(m)`, `n, m ≤ N`, are at least
`4/(Np log p)` apart. -/
theorem norm_frobRoot_sub_ge {p : ℕ} (hp : p.Prime) {N n m : ℕ} (hn : n ∈ Icc 1 N)
    (hm : m ∈ Icc 1 N) (hne : frobRoot p n ≠ frobRoot p m) :
    4 / (N * p * Real.log p) ≤ ‖frobRoot p n - frobRoot p m‖ := by
  obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
  obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
  have hL : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  set x := (Real.log m - Real.log n) / Real.log p
  set r := round x
  -- `‖ω(n) − ω(m)‖ = ‖e^{2πix i} − 1‖`
  have hLc : (Real.log p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
  have hx' : x * Real.log p = Real.log m - Real.log n := by simp only [x]; field_simp
  have hratio : frobRoot p n = frobRoot p m * cexp ((((2 * π * x) : ℝ) : ℂ) * I) := by
    rw [frobRoot_eq_exp, frobRoot_eq_exp, ← Complex.exp_add]
    congr 1
    rw [← add_mul, ← Complex.ofReal_add]
    congr 2
    have h2 : 2 * π * x = 2 * π * (Real.log m - Real.log n) / Real.log p := by
      rw [← hx']; field_simp
    rw [h2]
    field_simp
    ring
  have hnorm : ‖frobRoot p n - frobRoot p m‖ = ‖cexp ((((2 * π * x) : ℝ) : ℂ) * I) - 1‖ := by
    rw [hratio, show frobRoot p m * cexp ((((2 * π * x) : ℝ) : ℂ) * I) - frobRoot p m =
      frobRoot p m * (cexp ((((2 * π * x) : ℝ) : ℂ) * I) - 1) by ring, norm_mul,
      norm_frobRoot, one_mul]
  rw [hnorm]
  refine le_trans ?_ (four_mul_abs_sub_round_le x)
  -- equal roots from a multiplicative relation
  have hroot : ∀ k : ℤ, Real.log n = Real.log m + k * Real.log p → frobRoot p n = frobRoot p m :=
    fun k hk => by
      rw [frobRoot, frobRoot, Complex.exp_eq_exp_iff_exists_int]
      refine ⟨-k, ?_⟩
      rw [hk, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_intCast]
      field_simp
      simp only [Int.cast_neg]
      ring
  -- the integers `A`, `B` with `log A − log B = (x − round x) log p`
  have hxr : |x - r| ≤ 1 / 2 := abs_sub_round x
  have hlogAB : ∃ A B : ℕ, 0 < A ∧ 0 < B ∧ A ≠ B ∧ (A : ℝ) ≤ N * p ∧ (B : ℝ) ≤ N * p ∧
      Real.log A - Real.log B = (x - r) * Real.log p := by
    have hlogNp : Real.log ((N : ℝ) * p) = Real.log N + Real.log p := Real.log_mul hN0.ne' hp0.ne'
    have hlnN : Real.log n ≤ Real.log N := Real.log_le_log (by positivity) (by exact_mod_cast hnN)
    have hlmN : Real.log m ≤ Real.log N := Real.log_le_log (by positivity) (by exact_mod_cast hmN)
    have hmulpow : ∀ (a K : ℕ), 0 < a → Real.log ((a * p ^ K : ℕ) : ℝ) = Real.log a + K * Real.log p :=
      fun a K ha => by
        push_cast
        rw [Real.log_mul (by exact_mod_cast ha.ne') (pow_pos hp0 K).ne', Real.log_pow]
    have hle : ∀ (A : ℕ), 0 < A → Real.log A ≤ Real.log ((N : ℝ) * p) → (A : ℝ) ≤ N * p :=
      fun A hA h => (Real.log_le_log_iff (by exact_mod_cast hA) (by positivity)).mp h
    rcases Int.eq_nat_or_neg r with ⟨K, hK | hK⟩
    · have hxK : |x - K| ≤ 1 / 2 := by
        have := hxr; rw [hK] at this; exact_mod_cast this
      have hlo := (abs_le.mp hxK).1
      refine ⟨m, n * p ^ K, by omega, Nat.mul_pos (by omega) (pow_pos hp.pos K), fun h => ?_,
        ?_, hle _ (Nat.mul_pos (by omega) (pow_pos hp.pos K)) ?_, ?_⟩
      · apply hne
        refine hroot (-K) ?_
        have := hmulpow n K (by omega)
        rw [← h] at this
        push_cast
        linarith
      · have : (m : ℝ) ≤ N := by exact_mod_cast hmN
        nlinarith [show (1 : ℝ) ≤ p by exact_mod_cast hp.one_lt.le]
      · rw [hmulpow n K (by omega), hlogNp]
        nlinarith [mul_le_mul_of_nonneg_right hlo hL.le]
      · rw [hmulpow n K (by omega), hK, sub_mul, hx']
        push_cast
        ring
    · have hxK : |x + K| ≤ 1 / 2 := by
        have := hxr; rw [hK] at this; push_cast at this; rwa [sub_neg_eq_add] at this
      have hhi := (abs_le.mp hxK).2
      refine ⟨m * p ^ K, n, Nat.mul_pos (by omega) (pow_pos hp.pos K), by omega, fun h => ?_,
        hle _ (Nat.mul_pos (by omega) (pow_pos hp.pos K)) ?_, ?_, ?_⟩
      · apply hne
        refine hroot K ?_
        have := hmulpow m K (by omega)
        rw [h] at this
        push_cast
        linarith
      · rw [hmulpow m K (by omega), hlogNp]
        nlinarith [mul_le_mul_of_nonneg_right hhi hL.le]
      · have : (n : ℝ) ≤ N := by exact_mod_cast hnN
        nlinarith [show (1 : ℝ) ≤ p by exact_mod_cast hp.one_lt.le]
      · rw [hmulpow m K (by omega), hK, sub_mul, hx']
        push_cast
        ring
  obtain ⟨A, B, hA, hB, hAB, hAM, hBM, hlog⟩ := hlogAB
  have hsep := inv_le_abs_log_sub hA hB hAB hAM hBM
  rw [hlog, abs_mul, abs_of_pos hL] at hsep
  have hNp : 0 < (N : ℝ) * p := by positivity
  rw [div_le_iff₀ (by positivity)]
  rw [div_le_iff₀ hNp] at hsep
  nlinarith

/-! ### Mean values on a stretch -/

/-- **Mean values of an exponential sum on a stretch.** For unimodular points `δ`-apart,
`Σ_{j<J} |Σ_t C_t t^{J₀+j}|² ≥ (J − 2|T|/δ) Σ_t |C_t|²`. -/
theorem sum_normSq_expSum_ge {T : Finset ℂ} (hT1 : ∀ t ∈ T, ‖t‖ = 1) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → δ ≤ ‖t - t'‖) (C : ℂ → ℂ) (J₀ : ℤ) (J : ℕ) :
    ((J : ℝ) - 2 * T.card / δ) * ∑ t ∈ T, ‖C t‖ ^ 2 ≤
      ∑ j ∈ range J, ‖∑ t ∈ T, C t * t ^ (J₀ + j)‖ ^ 2 := by
  have hT0 : ∀ t ∈ T, t ≠ 0 := fun t ht h => by
    have := hT1 t ht
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have hconj : ∀ t ∈ T, conj t = t⁻¹ := fun t ht => by
    have h := Complex.mul_conj t
    rw [Complex.normSq_eq_norm_sq, hT1 t ht] at h
    have h' : t * conj t = 1 := by rw [h]; simp
    exact eq_inv_of_mul_eq_one_right h'
  set S : ℂ → ℂ → ℂ := fun t t' => ∑ j ∈ range J, (t * conj t') ^ (J₀ + (j : ℤ))
  -- the mean square is a double sum
  have hsum : ∑ j ∈ range J, ‖∑ t ∈ T, C t * t ^ (J₀ + j)‖ ^ 2 =
      (∑ t ∈ T, ∑ t' ∈ T, C t * conj (C t') * S t t').re := by
    have hj : ∀ j : ℕ, ‖∑ t ∈ T, C t * t ^ (J₀ + j)‖ ^ 2 =
        (∑ t ∈ T, ∑ t' ∈ T, C t * conj (C t') * (t * conj t') ^ (J₀ + (j : ℤ))).re := fun j => by
      have h1 : (((‖∑ t ∈ T, C t * t ^ (J₀ + j)‖ ^ 2 : ℝ)) : ℂ) =
          (∑ t ∈ T, C t * t ^ (J₀ + j)) * conj (∑ t ∈ T, C t * t ^ (J₀ + j)) := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [← Complex.ofReal_re (‖_‖ ^ 2), h1, map_sum, Finset.sum_mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun t' _ => ?_
      rw [map_mul, map_zpow₀, mul_zpow]
      ring
    rw [Finset.sum_congr rfl fun j _ => hj j, ← Complex.re_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t' _ => ?_
    simp only [S, Finset.mul_sum]
  -- the diagonal and the off-diagonal geometric sums
  have hdiag : ∀ t ∈ T, S t t = J := fun t ht => by
    simp only [S, hconj t ht, mul_inv_cancel₀ (hT0 t ht), one_zpow, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one]
  have hoff : ∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → ‖S t t'‖ ≤ 2 / δ := fun t ht t' ht' hne => by
    set u := t * conj t'
    have hu1 : ‖u‖ = 1 := by simp [u, hT1 t ht, hT1 t' ht']
    have hu0 : u ≠ 0 := fun h => by simp [h] at hu1
    have hune : u ≠ 1 := by
      intro h
      apply hne
      have : t * t'⁻¹ = 1 := by rw [← hconj t' ht']; exact h
      rw [mul_inv_eq_one₀ (hT0 t' ht')] at this
      exact this
    have hu1' : ‖u - 1‖ = ‖t - t'‖ := by
      have : u - 1 = (t - t') * t'⁻¹ := by
        simp only [u, hconj t' ht']; field_simp [hT0 t' ht']
      rw [this, norm_mul, norm_inv, hT1 t' ht', inv_one, mul_one]
    have hS : S t t' = u ^ J₀ * ∑ j ∈ range J, u ^ j := by
      simp only [S, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [zpow_add₀ hu0, zpow_natCast]
    rw [hS, norm_mul, norm_zpow, hu1, one_zpow, one_mul, geom_sum_eq hune, norm_div]
    have hnum : ‖u ^ J - 1‖ ≤ 2 := by
      calc ‖u ^ J - 1‖ ≤ ‖u ^ J‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_pow, hu1, one_pow, norm_one]; norm_num
    have hden : δ ≤ ‖u - 1‖ := by rw [hu1']; exact hsep t ht t' ht' hne
    calc ‖u ^ J - 1‖ / ‖u - 1‖ ≤ 2 / ‖u - 1‖ :=
          div_le_div_of_nonneg_right hnum (norm_nonneg _)
      _ ≤ 2 / δ := div_le_div_of_nonneg_left (by norm_num) hδ hden
  -- split off the diagonal
  rw [hsum]
  have hsplit : ∑ t ∈ T, ∑ t' ∈ T, C t * conj (C t') * S t t' =
      ∑ t ∈ T, (J : ℂ) * ((‖C t‖ ^ 2 : ℝ) : ℂ) +
        ∑ t ∈ T, ∑ t' ∈ T.erase t, C t * conj (C t') * S t t' := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [← Finset.add_sum_erase T _ ht, hdiag t ht, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  rw [hsplit, Complex.add_re, Complex.re_sum]
  have hd : ∑ t ∈ T, ((J : ℂ) * ((‖C t‖ ^ 2 : ℝ) : ℂ)).re = J * ∑ t ∈ T, ‖C t‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hd]
  -- the off-diagonal is bounded by `(2/δ)(Σ ‖C‖)² ≤ (2/δ)|T| Σ ‖C‖²`
  have hoffb : |(∑ t ∈ T, ∑ t' ∈ T.erase t, C t * conj (C t') * S t t').re| ≤
      2 / δ * (∑ t ∈ T, ‖C t‖) ^ 2 := by
    refine (Complex.abs_re_le_norm _).trans ((norm_sum_le _ _).trans ?_)
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun t ht => (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset t T) fun t' _ _ => by
      positivity).trans' (Finset.sum_le_sum fun t' ht' => ?_)
    have hne : t' ≠ t := Finset.ne_of_mem_erase ht'
    rw [norm_mul, norm_mul, Complex.norm_conj]
    have := hoff t ht t' (Finset.mem_of_mem_erase ht') (Ne.symm hne)
    have h0 : 0 ≤ ‖C t‖ * ‖C t'‖ := by positivity
    nlinarith
  have hcs : (∑ t ∈ T, ‖C t‖) ^ 2 ≤ T.card * ∑ t ∈ T, ‖C t‖ ^ 2 := sq_sum_le_card_mul_sum_sq
  have h2 : 2 / δ * (∑ t ∈ T, ‖C t‖) ^ 2 ≤ 2 * T.card / δ * ∑ t ∈ T, ‖C t‖ ^ 2 := by
    have : 2 / δ * (T.card * ∑ t ∈ T, ‖C t‖ ^ 2) = 2 * T.card / δ * ∑ t ∈ T, ‖C t‖ ^ 2 := by ring
    rw [← this]
    exact mul_le_mul_of_nonneg_left hcs (by positivity)
  have := (abs_le.mp hoffb).1
  nlinarith

/-! ### Approximate Bézout -/

/-- **Approximate Bézout.** If the Dirichlet polynomial of `a`, of length `N`, is at most `ε` at
`J ≥ N²p log p` consecutive points of the Frobenius progression of `p`, then the `p`-tower sums
`C_w = Σ_{ω_p(n) = w} a_n` satisfy `Σ_w |C_w|² ≤ 2ε²`. -/
theorem sum_normSq_towerSums_le {p : ℕ} (hp : p.Prime) (a : ℕ → ℂ) {N : ℕ} {ε : ℝ} (J₀ : ℤ)
    {J : ℕ} (hJ : (N : ℝ) ^ 2 * p * Real.log p ≤ J)
    (hD : ∀ j ∈ range J, ‖dirDeriv a N 0 (frobPoint p (J₀ + j))‖ ≤ ε) :
    ∑ w ∈ (Icc 1 N).image (frobRoot p), ‖∑ n ∈ Icc 1 N with frobRoot p n = w, a n‖ ^ 2 ≤
      2 * ε ^ 2 := by
  classical
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [Finset.Icc_eq_empty_of_lt one_pos, Finset.image_empty, Finset.sum_empty]
    positivity
  set T := (Icc 1 N).image (frobRoot p)
  set C : ℂ → ℂ := fun w => ∑ n ∈ Icc 1 N with frobRoot p n = w, a n
  have hL : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  set δ := 4 / (N * p * Real.log p)
  have hδ : 0 < δ := by positivity
  have hT1 : ∀ t ∈ T, ‖t‖ = 1 := fun t ht => by
    obtain ⟨n, -, rfl⟩ := Finset.mem_image.mp ht; exact norm_frobRoot p n
  have hsep : ∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → δ ≤ ‖t - t'‖ := fun t ht t' ht' hne => by
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp ht'
    exact norm_frobRoot_sub_ge hp hn hm hne
  have hmv := sum_normSq_expSum_ge hT1 hδ hsep C J₀ J
  have hval : ∀ j : ℕ, ∑ t ∈ T, C t * t ^ (J₀ + j) = dirDeriv a N 0 (frobPoint p (J₀ + j)) :=
    fun j => (dirDeriv_zero_frobPoint_eq a N p (J₀ + j)).symm
  simp_rw [hval] at hmv
  have hJpos : (0 : ℝ) < J := lt_of_lt_of_le (by positivity) hJ
  have hε : 0 ≤ ε := by
    have hJ1 : 0 < J := by exact_mod_cast hJpos
    exact (norm_nonneg _).trans (hD 0 (Finset.mem_range.mpr hJ1))
  have hup : ∑ j ∈ range J, ‖dirDeriv a N 0 (frobPoint p (J₀ + j))‖ ^ 2 ≤ J * ε ^ 2 := by
    calc ∑ j ∈ range J, ‖dirDeriv a N 0 (frobPoint p (J₀ + j))‖ ^ 2 ≤ ∑ _j ∈ range J, ε ^ 2 :=
          Finset.sum_le_sum fun j hj => pow_le_pow_left₀ (norm_nonneg _) (hD j hj) 2
      _ = J * ε ^ 2 := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hcard : (T.card : ℝ) ≤ N := by
    have := Finset.card_image_le (s := Icc 1 N) (f := frobRoot p)
    rw [Nat.card_Icc, Nat.add_sub_cancel] at this
    exact_mod_cast this
  have hhalf : 2 * T.card / δ ≤ J / 2 := by
    have : 2 * (T.card : ℝ) / δ = T.card * (N * p * Real.log p) / 2 := by
      simp only [δ]; field_simp; ring
    rw [this]
    have : (T.card : ℝ) * (N * p * Real.log p) ≤ N * (N * p * Real.log p) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    nlinarith
  have hC0 : 0 ≤ ∑ t ∈ T, ‖C t‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  have : (J : ℝ) / 2 * ∑ t ∈ T, ‖C t‖ ^ 2 ≤ J * ε ^ 2 := by nlinarith
  have h2 : ∑ t ∈ T, ‖C t‖ ^ 2 ≤ 2 * ε ^ 2 := by
    by_contra hc
    push Not at hc
    nlinarith
  exact h2

end GaloisForLFunctions.EffectiveArithmeticHodgeTheory
