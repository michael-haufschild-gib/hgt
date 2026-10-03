import GaloisForLFunctions.RHTower.ZetaZerosLeeYangQuasicrystal
import GaloisForLFunctions.HTGeometry.DirichletCoefficientTheta
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# The Dirichlet series of `ζ(s) / (2√6 · Y_a(s))`

Let `P_a(s) = 1 + 2a·4^{−s} + 3a·9^{−s} + 6·36^{−s}`, so that `6^s P_a(s) = 2√6 · Y_a(s)` with
`Y_a = RHTower.LeeYang.leeYang a`.  For real `|a| < 1` the tail weight
`θ(σ) = 2|a|4^{−σ} + 3|a|9^{−σ} + 6·36^{−σ}` is `< 1` for `σ ≥ 1`.  The Dirichlet inverse `e` of `P_a`
satisfies `e(n) = −2a e(n/4) − 3a e(n/9) − 6 e(n/36)` for `n ≥ 2` (terms present only when the
divisibility holds), so the partial sums of `|e(n)| n^{−σ}` are at most `1 + θ(σ)` times themselves
and hence `≤ 1/(1 − θ(σ))`.

The coefficients `c(m) = [6 ∣ m]·(1 ∗ e)(m/6)` then have `c(1) = 0`, are absolutely summable
against `m^{−σ}` for every `σ > 1`, and their Dirichlet series is `ζ(s) / (2√6 · Y_a(s))` on
`Re s > 1` (`exists_coeff_dirichlet_zeta_div_leeYang`).
-/

open Complex

noncomputable section

namespace RHTower.LeeYang

/-! ## The Dirichlet polynomial `P_a` -/

/-- The coefficients of `P_a(s) = 1 + 2a·4^{−s} + 3a·9^{−s} + 6·36^{−s}`. -/
def pFun (a : ℝ) (n : ℕ) : ℂ :=
  if n = 1 then 1 else if n = 4 then 2 * a else if n = 9 then 3 * a else if n = 36 then 6 else 0

/-- `P_a` as an arithmetic function. -/
def pCoeff (a : ℝ) : ArithmeticFunction ℂ := ⟨pFun a, by simp [pFun]⟩

theorem pCoeff_apply (a : ℝ) (n : ℕ) : pCoeff a n = pFun a n := rfl

theorem pCoeff_one (a : ℝ) : pCoeff a 1 = 1 := by simp [pCoeff_apply, pFun]

/-- Multiplying by `P_a` in the Dirichlet algebra. -/
theorem pCoeff_mul_apply (a : ℝ) (f : ArithmeticFunction ℂ) {n : ℕ} (hn : n ≠ 0) :
    (pCoeff a * f) n = f n + (if 4 ∣ n then 2 * a * f (n / 4) else 0)
      + (if 9 ∣ n then 3 * a * f (n / 9) else 0) + (if 36 ∣ n then 6 * f (n / 36) else 0) := by
  classical
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun i j => pCoeff a i * f j)]
  have hsplit : ∀ d : ℕ, pCoeff a d * f (n / d) =
      (if d = 1 then f (n / d) else 0) + (if d = 4 then 2 * a * f (n / d) else 0)
        + (if d = 9 then 3 * a * f (n / d) else 0) + (if d = 36 then 6 * f (n / d) else 0) := by
    intro d
    rw [pCoeff_apply, pFun]
    by_cases h1 : d = 1
    · subst h1; simp
    by_cases h4 : d = 4
    · subst h4; simp
    by_cases h9 : d = 9
    · subst h9; simp
    by_cases h36 : d = 36
    · subst h36; simp
    simp [h1, h4, h9, h36]
  simp_rw [hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq', Nat.mem_divisors]
  simp [hn, Nat.div_one]

instance (a : ℝ) : Invertible (pCoeff a 1) := by
  rw [pCoeff_one]; exact invertibleOne

/-- The Dirichlet inverse `e_a` of `P_a`. -/
def eCoeff (a : ℝ) : ArithmeticFunction ℂ :=
  ArithmeticFunction.dirichletInverse (pCoeff a) inferInstance

theorem pCoeff_mul_eCoeff (a : ℝ) : pCoeff a * eCoeff a = 1 :=
  ArithmeticFunction.self_mul_dirichletInverse _ _

theorem eCoeff_one (a : ℝ) : eCoeff a 1 = 1 := by
  have h : (pCoeff a * eCoeff a) 1 = (1 : ArithmeticFunction ℂ) 1 := by rw [pCoeff_mul_eCoeff]
  rw [pCoeff_mul_apply a _ one_ne_zero] at h
  simpa using h

/-- **The recursion.**  For `n ≥ 2`,
`e(n) = −2a e(n/4)[4∣n] − 3a e(n/9)[9∣n] − 6 e(n/36)[36∣n]`. -/
theorem eCoeff_eq (a : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    eCoeff a n = -((if 4 ∣ n then 2 * a * eCoeff a (n / 4) else 0)
      + (if 9 ∣ n then 3 * a * eCoeff a (n / 9) else 0)
      + (if 36 ∣ n then 6 * eCoeff a (n / 36) else 0)) := by
  have h : (pCoeff a * eCoeff a) n = (1 : ArithmeticFunction ℂ) n := by rw [pCoeff_mul_eCoeff]
  have h1 : (1 : ArithmeticFunction ℂ) n = 0 := by
    rw [ArithmeticFunction.one_apply, if_neg (by omega)]
  rw [pCoeff_mul_apply a _ (by omega), h1] at h
  linear_combination h

/-! ## Summability of the inverse -/

/-- The weighted tail `θ(σ) = 2|a|4^{−σ} + 3|a|9^{−σ} + 6·36^{−σ}`. -/
def theta (a σ : ℝ) : ℝ :=
  2 * |a| * (4 : ℝ) ^ (-σ) + 3 * |a| * (9 : ℝ) ^ (-σ) + 6 * (36 : ℝ) ^ (-σ)

theorem rpow_neg_le_inv {b σ : ℝ} (hb : 1 ≤ b) (hσ : 1 ≤ σ) : b ^ (-σ) ≤ b⁻¹ := by
  calc b ^ (-σ) ≤ b ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hb (by linarith)
    _ = b⁻¹ := Real.rpow_neg_one b

theorem theta_lt_one {a : ℝ} (ha : |a| < 1) {σ : ℝ} (hσ : 1 ≤ σ) : theta a σ < 1 := by
  unfold theta
  have h4 := rpow_neg_le_inv (b := 4) (by norm_num) hσ
  have h9 := rpow_neg_le_inv (b := 9) (by norm_num) hσ
  have h36 := rpow_neg_le_inv (b := 36) (by norm_num) hσ
  have ha0 := abs_nonneg a
  have e1 : 2 * |a| * (4 : ℝ) ^ (-σ) ≤ 2 * |a| * 4⁻¹ := by gcongr
  have e2 : 3 * |a| * (9 : ℝ) ^ (-σ) ≤ 3 * |a| * 9⁻¹ := by gcongr
  have e3 : 6 * (36 : ℝ) ^ (-σ) ≤ 6 * 36⁻¹ := by gcongr
  norm_num at e1 e2 e3
  linarith

/-- The weighted modulus `G(n) = |e(n)| n^{−σ}`. -/
def wt (a σ : ℝ) (n : ℕ) : ℝ := ‖eCoeff a n‖ * (n : ℝ) ^ (-σ)

theorem wt_nonneg (a σ : ℝ) (n : ℕ) : 0 ≤ wt a σ n :=
  mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _)

theorem wt_dvd {a σ : ℝ} {d n : ℕ} (hdn : d ∣ n) (hd : 0 < d) :
    ‖eCoeff a (n / d)‖ * (n : ℝ) ^ (-σ) = (d : ℝ) ^ (-σ) * wt a σ (n / d) := by
  obtain ⟨m, rfl⟩ := hdn
  rw [Nat.mul_div_cancel_left m hd, wt, Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg d) (Nat.cast_nonneg m)]
  ring

theorem wt_le {a σ : ℝ} {n : ℕ} (hn : 2 ≤ n) :
    wt a σ n ≤ (if 4 ∣ n then 2 * |a| * (4 : ℝ) ^ (-σ) * wt a σ (n / 4) else 0)
      + (if 9 ∣ n then 3 * |a| * (9 : ℝ) ^ (-σ) * wt a σ (n / 9) else 0)
      + (if 36 ∣ n then 6 * (36 : ℝ) ^ (-σ) * wt a σ (n / 36) else 0) := by
  have hpow := Real.rpow_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) (-σ)
  have hnorm : ‖eCoeff a n‖ ≤ (if 4 ∣ n then 2 * |a| * ‖eCoeff a (n / 4)‖ else 0)
      + (if 9 ∣ n then 3 * |a| * ‖eCoeff a (n / 9)‖ else 0)
      + (if 36 ∣ n then 6 * ‖eCoeff a (n / 36)‖ else 0) := by
    rw [eCoeff_eq a hn, norm_neg]
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
    · split_ifs <;> simp [Complex.norm_real]
    · split_ifs <;> simp [Complex.norm_real]
    · split_ifs <;> simp
  calc wt a σ n = ‖eCoeff a n‖ * (n : ℝ) ^ (-σ) := rfl
    _ ≤ ((if 4 ∣ n then 2 * |a| * ‖eCoeff a (n / 4)‖ else 0)
      + (if 9 ∣ n then 3 * |a| * ‖eCoeff a (n / 9)‖ else 0)
      + (if 36 ∣ n then 6 * ‖eCoeff a (n / 36)‖ else 0)) * (n : ℝ) ^ (-σ) :=
        mul_le_mul_of_nonneg_right hnorm hpow
    _ = _ := by
      rw [add_mul, add_mul]
      congr 1; congr 1
      · split_ifs with h
        · rw [mul_assoc, wt_dvd h (by norm_num)]; push_cast; ring
        · simp
      · split_ifs with h
        · rw [mul_assoc, wt_dvd h (by norm_num)]; push_cast; ring
        · simp
      · split_ifs with h
        · rw [mul_assoc, wt_dvd h (by norm_num)]; push_cast; ring
        · simp

/-- Summing a nonnegative function over the quotients `n/d` of the multiples of `d` in
`[1, N]` gives at most its sum over `[1, N]`. -/
theorem sum_dvd_div_le {G : ℕ → ℝ} (hG : ∀ n, 0 ≤ G n) {d : ℕ} (hd : 0 < d) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (if d ∣ n then G (n / d) else 0) ≤ ∑ n ∈ Finset.Icc 1 N, G n := by
  classical
  rw [← Finset.sum_filter]
  have hinj : Set.InjOn (fun n => n / d) ((Finset.Icc 1 N).filter (d ∣ ·)) := by
    intro x hx y hy hxy
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx hy
    obtain ⟨u, rfl⟩ := hx.2
    obtain ⟨v, rfl⟩ := hy.2
    simp only [Nat.mul_div_cancel_left _ hd] at hxy
    rw [hxy]
  rw [← Finset.sum_image (g := fun n => n / d) (f := G) hinj]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => hG i)
  intro m hm
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc] at hm
  obtain ⟨n, ⟨⟨hn1, hnN⟩, ⟨u, rfl⟩⟩, rfl⟩ := hm
  rw [Nat.mul_div_cancel_left _ hd]
  simp only [Finset.mem_Icc]
  have hu : 1 ≤ u := by
    rcases Nat.eq_zero_or_pos u with h | h
    · subst h; simp at hn1
    · exact h
  exact ⟨hu, le_trans (Nat.le_mul_of_pos_left u hd) hnN⟩

/-- **Partial sums of the inverse.** -/
theorem sum_wt_le {a σ : ℝ} (hθ : theta a σ < 1) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, wt a σ n ≤ 1 / (1 - theta a σ) := by
  classical
  set S := ∑ n ∈ Finset.Icc 1 N, wt a σ n with hS
  have hw1 : wt a σ 1 = 1 := by simp [wt, eCoeff_one]
  have key : S ≤ 1 + theta a σ * S := by
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      have hS0 : S = 0 := by simp [hS]
      rw [hS0]; norm_num
    have hsplit : S = wt a σ 1 + ∑ n ∈ Finset.Icc 1 N, (if 2 ≤ n then wt a σ n else 0) := by
      rw [hS, ← Finset.add_sum_erase _ _ (Finset.mem_Icc.mpr ⟨le_rfl, hN⟩)]
      congr 1
      rw [← Finset.sum_erase_add _ _ (Finset.mem_Icc.mpr ⟨le_rfl, hN⟩)]
      simp only [show ¬ 2 ≤ 1 by norm_num, if_false, add_zero]
      refine Finset.sum_congr rfl fun n hn => ?_
      have : n ≠ 1 := Finset.ne_of_mem_erase hn
      have : 1 ≤ n := (Finset.mem_Icc.mp (Finset.mem_of_mem_erase hn)).1
      rw [if_pos (by omega)]
    have hbound : ∀ n ∈ Finset.Icc 1 N, (if 2 ≤ n then wt a σ n else 0) ≤
        2 * |a| * (4 : ℝ) ^ (-σ) * (if 4 ∣ n then wt a σ (n / 4) else 0)
        + 3 * |a| * (9 : ℝ) ^ (-σ) * (if 9 ∣ n then wt a σ (n / 9) else 0)
        + 6 * (36 : ℝ) ^ (-σ) * (if 36 ∣ n then wt a σ (n / 36) else 0) := by
      intro n _
      have h4 : 0 ≤ 2 * |a| * (4 : ℝ) ^ (-σ) := by positivity
      have h9 : 0 ≤ 3 * |a| * (9 : ℝ) ^ (-σ) := by positivity
      have h36 : 0 ≤ 6 * (36 : ℝ) ^ (-σ) := by positivity
      by_cases h2 : 2 ≤ n
      · rw [if_pos h2]
        refine (wt_le h2).trans (le_of_eq ?_)
        split_ifs <;> ring
      · rw [if_neg h2]
        have i4 : 0 ≤ (if 4 ∣ n then wt a σ (n / 4) else 0) := by
          split_ifs <;> simp [wt_nonneg]
        have i9 : 0 ≤ (if 9 ∣ n then wt a σ (n / 9) else 0) := by
          split_ifs <;> simp [wt_nonneg]
        have i36 : 0 ≤ (if 36 ∣ n then wt a σ (n / 36) else 0) := by
          split_ifs <;> simp [wt_nonneg]
        have := mul_nonneg h4 i4
        have := mul_nonneg h9 i9
        have := mul_nonneg h36 i36
        linarith
    have hsum := Finset.sum_le_sum hbound
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum] at hsum
    have b4 := sum_dvd_div_le (wt_nonneg a σ) (d := 4) (by norm_num) N
    have b9 := sum_dvd_div_le (wt_nonneg a σ) (d := 9) (by norm_num) N
    have b36 := sum_dvd_div_le (wt_nonneg a σ) (d := 36) (by norm_num) N
    have c4 : 0 ≤ 2 * |a| * (4 : ℝ) ^ (-σ) := by positivity
    have c9 : 0 ≤ 3 * |a| * (9 : ℝ) ^ (-σ) := by positivity
    have c36 : 0 ≤ 6 * (36 : ℝ) ^ (-σ) := by positivity
    have m4 := mul_le_mul_of_nonneg_left b4 c4
    have m9 := mul_le_mul_of_nonneg_left b9 c9
    have m36 := mul_le_mul_of_nonneg_left b36 c36
    rw [hw1] at hsplit
    rw [← hS] at m4 m9 m36
    have hθS : theta a σ * S = 2 * |a| * (4 : ℝ) ^ (-σ) * S + 3 * |a| * (9 : ℝ) ^ (-σ) * S
        + 6 * (36 : ℝ) ^ (-σ) * S := by rw [theta]; ring
    rw [hθS]
    linarith
  have h1 : 0 < 1 - theta a σ := by linarith
  rw [le_div_iff₀ h1]
  nlinarith

theorem summable_wt {a σ : ℝ} (hθ : theta a σ < 1) : Summable (wt a σ) := by
  refine summable_of_sum_range_le (c := 1 / (1 - theta a σ)) (wt_nonneg a σ) fun N => ?_
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have h1 : 0 < 1 - theta a σ := by linarith
    simp only [Finset.range_zero, Finset.sum_empty]
    positivity
  have hsub : Finset.range N ⊆ insert 0 (Finset.Icc 1 N) := by
    intro n hn
    rw [Finset.mem_range] at hn
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · exact Finset.mem_insert_of_mem (Finset.mem_Icc.mpr ⟨h, hn.le⟩)
  calc ∑ i ∈ Finset.range N, wt a σ i ≤ ∑ i ∈ insert 0 (Finset.Icc 1 N), wt a σ i :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => wt_nonneg a σ i)
    _ = ∑ i ∈ Finset.Icc 1 N, wt a σ i := by
        rw [Finset.sum_insert (by simp)]
        simp [wt]
    _ ≤ _ := sum_wt_le hθ N

theorem LSeriesSummable_eCoeff {a : ℝ} (ha : |a| < 1) {s : ℂ} (hs : 1 ≤ s.re) :
    LSeriesSummable (fun n => eCoeff a n) s := by
  unfold LSeriesSummable
  refine (summable_wt (theta_lt_one ha hs)).of_norm_bounded fun n => ?_
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · subst hn; simp [wt]
  · rw [wt, Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]

/-! ## The L-series of `P_a` and of its inverse -/

/-- `P_a(s) = 1 + 2a/4^s + 3a/9^s + 6/36^s`. -/
def pPoly (a : ℝ) (s : ℂ) : ℂ := 1 + 2 * a / (4 : ℂ) ^ s + 3 * a / (9 : ℂ) ^ s + 6 / (36 : ℂ) ^ s

theorem LSeries_pCoeff (a : ℝ) (s : ℂ) : LSeries (fun n => pCoeff a n) s = pPoly a s := by
  rw [LSeries, tsum_eq_sum (s := {1, 4, 9, 36})]
  · simp [LSeries.term_of_ne_zero, pCoeff_apply, pFun, pPoly]
    ring
  · intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    rw [LSeries.term_def]
    split_ifs
    · rfl
    · simp [pCoeff_apply, pFun, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2]

theorem LSeriesSummable_pCoeff (a : ℝ) (s : ℂ) : LSeriesSummable (fun n => pCoeff a n) s := by
  refine summable_of_ne_finset_zero (s := {1, 4, 9, 36}) fun n hn => ?_
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
  rw [LSeries.term_def]
  split_ifs
  · rfl
  · simp [pCoeff_apply, pFun, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2]

theorem cpow_eq_exp_log {x : ℝ} (hx : 0 < x) (s : ℂ) :
    ((x : ℂ)) ^ s = Complex.exp (s * (Real.log x : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), Complex.ofReal_log hx.le, mul_comm]

/-- **`6^s P_a(s) = 2√6 · Y_a(s)`**, in exponential form. -/
theorem pPoly_eq (a : ℝ) (s : ℂ) :
    pPoly a s = 2 * Complex.exp ((L₁ : ℂ) / 2) * Complex.exp (-(s * L₁)) * leeYang a s := by
  set A : ℝ := Real.log 2
  set B : ℝ := Real.log 3
  have hL₁ : (L₁ : ℂ) = A + B := by
    rw [L₁, show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    push_cast; rfl
  have hL₂ : (L₂ : ℂ) = B - A := by
    rw [L₂, Real.log_div (by norm_num) (by norm_num)]
    push_cast; rfl
  have h4 : (4 : ℂ) ^ s = Complex.exp (s * (2 * A)) := by
    rw [show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num, cpow_eq_exp_log (by norm_num),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; rfl
  have h9 : (9 : ℂ) ^ s = Complex.exp (s * (2 * B)) := by
    rw [show (9 : ℂ) = ((9 : ℝ) : ℂ) by norm_num, cpow_eq_exp_log (by norm_num),
      show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]
    push_cast; rfl
  have h36 : (36 : ℂ) ^ s = Complex.exp (s * (2 * (A + B))) := by
    rw [show (36 : ℂ) = ((36 : ℝ) : ℂ) by norm_num, cpow_eq_exp_log (by norm_num),
      show (36 : ℝ) = (2 * 3) ^ 2 by norm_num, Real.log_pow, Real.log_mul (by norm_num) (by norm_num)]
    push_cast; rfl
  have h2 : (2 : ℂ) = Complex.exp (A / 2) * Complex.exp (A / 2) := by
    rw [← Complex.exp_add, add_halves, ← Complex.ofReal_exp, Real.exp_log (by norm_num)]
    norm_num
  have h3 : (3 : ℂ) = Complex.exp (B / 2) * Complex.exp (B / 2) := by
    rw [← Complex.exp_add, add_halves, ← Complex.ofReal_exp, Real.exp_log (by norm_num)]
    norm_num
  set p := Complex.exp (A / 2) with hp
  set q := Complex.exp (B / 2) with hq
  set u := Complex.exp (-(s * A)) with hu
  set v := Complex.exp (-(s * B)) with hv
  have hp0 : p ≠ 0 := Complex.exp_ne_zero _
  have hq0 : q ≠ 0 := Complex.exp_ne_zero _
  have hu0 : u ≠ 0 := Complex.exp_ne_zero _
  have hv0 : v ≠ 0 := Complex.exp_ne_zero _
  have e4 : (4 : ℂ) ^ s = (u * u)⁻¹ := by
    rw [h4, hu, ← Complex.exp_add, ← Complex.exp_neg]; congr 1; ring
  have e9 : (9 : ℂ) ^ s = (v * v)⁻¹ := by
    rw [h9, hv, ← Complex.exp_add, ← Complex.exp_neg]; congr 1; ring
  have e36 : (36 : ℂ) ^ s = (u * u * v * v)⁻¹ := by
    rw [h36, hu, hv, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add,
      ← Complex.exp_neg]; congr 1; ring
  have f1 : Complex.exp ((L₁ : ℂ) / 2) = p * q := by
    rw [hL₁, hp, hq, ← Complex.exp_add]; congr 1; ring
  have f2 : Complex.exp (-(s * L₁)) = u * v := by
    rw [hL₁, hu, hv, ← Complex.exp_add]; congr 1; ring
  have f3 : Complex.exp ((s - 1 / 2) * L₁) = (u * v * p * q)⁻¹ := by
    rw [hL₁, hu, hv, hp, hq, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add,
      ← Complex.exp_neg]; congr 1; ring
  have f4 : Complex.exp (-((s - 1 / 2) * L₁)) = u * v * p * q := by
    rw [hL₁, hu, hv, hp, hq, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1; ring
  have f5 : Complex.exp ((s - 1 / 2) * L₂) = u * p * (v * q)⁻¹ := by
    rw [hL₂, hu, hv, hp, hq, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_neg,
      ← Complex.exp_add]; congr 1; ring
  have f6 : Complex.exp (-((s - 1 / 2) * L₂)) = v * q * (u * p)⁻¹ := by
    rw [hL₂, hu, hv, hp, hq, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_neg,
      ← Complex.exp_add]; congr 1; ring
  have c1 : Complex.cosh ((s - 1 / 2) * L₁) = ((u * v * p * q)⁻¹ + u * v * p * q) / 2 := by
    rw [Complex.cosh, f3, f4]
  have c2 : Complex.cosh ((s - 1 / 2) * L₂) = (u * p * (v * q)⁻¹ + v * q * (u * p)⁻¹) / 2 := by
    rw [Complex.cosh, f5, f6]
  have h6 : (6 : ℂ) = p * p * (q * q) := by rw [← h2, ← h3]; norm_num
  rw [pPoly, leeYang, c1, c2, f1, f2, e4, e9, e36, h6, h2, h3]
  field_simp
  ring

theorem pPoly_ne_zero {a : ℝ} (ha : |a| < 1) {s : ℂ} (hs : s.re ≠ 1 / 2) : pPoly a s ≠ 0 := by
  rw [pPoly_eq]
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero (Complex.exp_ne_zero _))
    (Complex.exp_ne_zero _)) ?_
  exact fun h => hs (re_eq_half_of_leeYang_eq_zero ha h)

theorem LSeries_eCoeff_mul_pPoly {a : ℝ} (ha : |a| < 1) {s : ℂ} (hs : 1 ≤ s.re) :
    LSeries (fun n => eCoeff a n) s * pPoly a s = 1 := by
  have h := ArithmeticFunction.LSeries_mul' (LSeriesSummable_pCoeff a s) (LSeriesSummable_eCoeff ha hs)
  rw [pCoeff_mul_eCoeff, LSeries_pCoeff] at h
  have h1 : (fun n => (1 : ArithmeticFunction ℂ) n) = LSeries.delta := by
    funext n; simp [ArithmeticFunction.one_apply, LSeries.delta]
  rw [h1, LSeries_delta] at h
  rw [mul_comm]
  exact h.symm

/-! ## The coefficients of `ζ / (2√6 Y_a)` -/

/-- `g = 1 ∗ e`. -/
def gCoeff (a : ℝ) : ArithmeticFunction ℂ := (ArithmeticFunction.zeta : ArithmeticFunction ℂ) * eCoeff a

theorem LSeriesSummable_zetaCoe {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (ArithmeticFunction.zeta : ArithmeticFunction ℂ) n) s := by
  simp only [ArithmeticFunction.natCoe_apply]
  exact ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs

theorem LSeriesSummable_gCoeff {a : ℝ} (ha : |a| < 1) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => gCoeff a n) s :=
  ArithmeticFunction.LSeriesSummable_mul (LSeriesSummable_zetaCoe hs) (LSeriesSummable_eCoeff ha hs.le)

theorem LSeries_gCoeff {a : ℝ} (ha : |a| < 1) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => gCoeff a n) s = riemannZeta s * LSeries (fun n => eCoeff a n) s := by
  rw [gCoeff, ArithmeticFunction.LSeries_mul' (LSeriesSummable_zetaCoe hs) (LSeriesSummable_eCoeff ha hs.le)]
  congr 1
  simp only [ArithmeticFunction.natCoe_apply]
  exact ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs

/-- `c(m) = [6 ∣ m] · g(m/6)`. -/
def cCoeff (a : ℝ) (m : ℕ) : ℂ := if 6 ∣ m then gCoeff a (m / 6) else 0

theorem cCoeff_one (a : ℝ) : cCoeff a 1 = 0 := by simp [cCoeff]

theorem term_cCoeff_six_mul (a : ℝ) (s : ℂ) (k : ℕ) :
    LSeries.term (cCoeff a) s (6 * k) = (6 : ℂ) ^ (-s) * LSeries.term (fun n => gCoeff a n) s k := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp
  rw [LSeries.term_of_ne_zero (by omega), LSeries.term_of_ne_zero hk.ne', cCoeff,
    if_pos (dvd_mul_right 6 k), Nat.mul_div_cancel_left k (by norm_num), Nat.cast_mul,
    Complex.natCast_mul_natCast_cpow, Complex.cpow_neg]
  push_cast
  ring

theorem term_cCoeff_eq_zero (a : ℝ) (s : ℂ) {m : ℕ} (hm : m ∉ Set.range (fun k => 6 * k)) :
    LSeries.term (cCoeff a) s m = 0 := by
  have h6 : ¬ 6 ∣ m := fun ⟨k, hk⟩ => hm ⟨k, hk.symm⟩
  rw [LSeries.term_def]
  split_ifs
  · rfl
  · simp [cCoeff, h6]

theorem injective_six_mul : Function.Injective (fun k : ℕ => 6 * k) :=
  fun x y h => by simpa using h

theorem LSeriesSummable_cCoeff {a : ℝ} (ha : |a| < 1) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (cCoeff a) s := by
  unfold LSeriesSummable
  rw [← injective_six_mul.summable_iff (fun m hm => term_cCoeff_eq_zero a s hm)]
  have h : (LSeries.term (cCoeff a) s ∘ fun k => 6 * k) =
      fun k => (6 : ℂ) ^ (-s) * LSeries.term (fun n => gCoeff a n) s k := by
    funext k; exact term_cCoeff_six_mul a s k
  rw [h]
  exact (LSeriesSummable_gCoeff ha hs).mul_left _

theorem LSeries_cCoeff {a : ℝ} (ha : |a| < 1) {s : ℂ} (hs : 1 < s.re) :
    LSeries (cCoeff a) s = riemannZeta s / (2 * Complex.exp ((L₁ : ℂ) / 2) * leeYang a s) := by
  rw [LSeries, ← injective_six_mul.tsum_eq (fun m hm => ?_)]
  · simp_rw [term_cCoeff_six_mul]
    rw [tsum_mul_left, ← LSeries, LSeries_gCoeff ha hs]
    have hP := LSeries_eCoeff_mul_pPoly ha hs.le
    have hP0 : pPoly a s ≠ 0 := pPoly_ne_zero ha (by linarith)
    have hE : LSeries (fun n => eCoeff a n) s = (pPoly a s)⁻¹ := eq_inv_of_mul_eq_one_left hP
    rw [hE, pPoly_eq] at *
    have hY : leeYang a s ≠ 0 := fun h => by simp [h] at hP0
    have h6 : (6 : ℂ) ^ (-s) = Complex.exp (-(s * L₁)) := by
      rw [show (6 : ℂ) = ((6 : ℝ) : ℂ) by norm_num, cpow_eq_exp_log (by norm_num)]
      rw [L₁]; congr 1; ring
    rw [h6]
    have he : Complex.exp (-(s * L₁)) ≠ 0 := Complex.exp_ne_zero _
    field_simp
  · exact Function.mem_support.mp hm |> fun h => by
      by_contra hr
      exact h (term_cCoeff_eq_zero a s hr)

/-- `coeffDirichlet c = LSeries c`. -/
theorem coeffDirichlet_eq_LSeries (c : ℕ → ℂ) (s : ℂ) :
    GaloisForLFunctions.HTGeometry.coeffDirichlet c s = LSeries c s := by
  rw [GaloisForLFunctions.HTGeometry.coeffDirichlet, LSeries,
    ← (Nat.succ_injective).tsum_eq (f := LSeries.term c s) ?_]
  · refine tsum_congr fun n => ?_
    rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n)]
    push_cast; rfl
  · intro m hm
    rcases m with _ | m
    · exact absurd (LSeries.term_zero c s) hm
    · exact ⟨m, rfl⟩

/-- **The Dirichlet series of `ζ / (2√6 · Y_a)`.** -/
theorem exists_coeff_dirichlet_zeta_div_leeYang {a : ℝ} (ha : |a| < 1) :
    ∃ c : ℕ → ℂ, c 1 = 0 ∧
      (∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖c (n + 1)‖ / ((n : ℝ) + 1) ^ σ) ∧
      ∀ s : ℂ, 1 < s.re → GaloisForLFunctions.HTGeometry.coeffDirichlet c s =
        riemannZeta s / (2 * Complex.exp ((L₁ : ℂ) / 2) * leeYang a s) := by
  refine ⟨cCoeff a, cCoeff_one a, fun σ hσ => ?_, fun s hs => ?_⟩
  · have h := LSeriesSummable_cCoeff ha (s := (σ : ℂ)) (by simpa using hσ)
    unfold LSeriesSummable at h
    have h' := (summable_nat_add_iff 1).mpr h.norm
    refine h'.congr fun n => ?_
    rw [LSeries.norm_term_eq, if_neg (Nat.succ_ne_zero n)]
    simp
  · rw [coeffDirichlet_eq_LSeries, LSeries_cCoeff ha hs]

end RHTower.LeeYang
