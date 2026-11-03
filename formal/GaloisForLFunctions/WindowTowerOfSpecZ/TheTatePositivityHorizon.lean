import GaloisForLFunctions.WindowTowerOfSpecZ.TheTateFamilyIsAnExponentialOfPointCounts

/-!
# The Tate positivity horizon

How far from dimension zero is the Tate operator `ρ_A(J_k)` a positive form? The exponential form
`J_k ≡ exp g_k` (`g_k = ℓ(n^k − 1)`) answers with the weighted norm `W_N(f) = Σ_{n≤N} f(n)/√n`:

* **Submultiplicativity** (`weightNorm_mul_le`): `W_N(f * g) ≤ W_N(f)W_N(g)` for nonnegative `f, g`,
  because `1/√(ab) = (1/√a)(1/√b)`; hence `W_N(exp g) ≤ e^{W_N(g)}` (`weightNorm_expTrunc_le`).
* **The exponent is small** (`weightNorm_tateExponent_le`): `g_k(n) ≤ kΛ(n)n^k`, so
  `W_N(g_k) ≤ kN^kψ_{1/2}(N)`, `ψ_{1/2}(N) = Σ_{n≤N}Λ(n)/√n`.
* **Positivity below the horizon** (`tateFunction_ge`, `tateFunction_nonneg_of_le_log_two`): for every
  window test, `τ_H(k) ≥ (2 − exp(kN^kψ_{1/2}(N)))‖H‖²`; in particular `ρ_A(J_k)` is a positive form as
  soon as `kN^kψ_{1/2}(N) ≤ log 2`, `N = ⌊e^A⌋`.

Since `ψ_{1/2}(e^A) ≈ 2e^{A/2}`, the Tate operators are positive for `k ≲ 0.13e^{−A/2}`. Numerically the
exact horizon is `k*(A) ≈ 1.66e^{−A/2}` (`k*(4.5) = 0.175`): the horizon shrinks to dimension zero at the
canonical rate `e^{−A/2}`, and only the tangent at `k = 0` is uniform along the tower.
-/

noncomputable section

namespace GaloisForLFunctions.WindowTowerOfSpecZ

open CohomologyOfWindowsOfSpecZ ArithmeticDegenerationTheory

/-- The weighted norm `W_N(f) = Σ_{n≤N} f(n)/√n`. -/
def weightNorm (N : ℕ) (f : ArithmeticFunction ℝ) : ℝ := ∑ n ∈ Finset.Icc 1 N, f n / Real.sqrt n

theorem weightNorm_nonneg {N : ℕ} {f : ArithmeticFunction ℝ} (hf : ∀ n, 0 ≤ f n) :
    0 ≤ weightNorm N f :=
  Finset.sum_nonneg fun n _ => div_nonneg (hf n) (Real.sqrt_nonneg _)

theorem mul_nonneg_apply {f g : ArithmeticFunction ℝ} (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n)
    (n : ℕ) : 0 ≤ (f * g) n := by
  rw [ArithmeticFunction.mul_apply]
  exact Finset.sum_nonneg fun x _ => mul_nonneg (hf _) (hg _)

/-- **The weighted norm is submultiplicative** on nonnegative functions. -/
theorem weightNorm_mul_le (N : ℕ) {f g : ArithmeticFunction ℝ} (hf : ∀ n, 0 ≤ f n)
    (hg : ∀ n, 0 ≤ g n) : weightNorm N (f * g) ≤ weightNorm N f * weightNorm N g := by
  have hexp : weightNorm N (f * g) =
      ∑ x ∈ (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun x => x.1 * x.2 ≤ N),
        f x.1 / Real.sqrt x.1 * (g x.2 / Real.sqrt x.2) := by
    rw [weightNorm, ← sum_Icc_divisorsAntidiagonal]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ArithmeticFunction.mul_apply, Finset.sum_div]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [← (Nat.mem_divisorsAntidiagonal.mp hx).1, Nat.cast_mul,
      Real.sqrt_mul (Nat.cast_nonneg _)]
    ring
  rw [hexp, weightNorm, weightNorm, Finset.sum_mul_sum, ← Finset.sum_product']
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun x _ _ =>
    mul_nonneg (div_nonneg (hf _) (Real.sqrt_nonneg _)) (div_nonneg (hg _) (Real.sqrt_nonneg _))

theorem weightNorm_one_le (N : ℕ) : weightNorm N 1 ≤ 1 := by
  rw [weightNorm]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  rw [Finset.sum_eq_single_of_mem 1 (Finset.mem_Icc.mpr ⟨le_rfl, hN⟩) fun n _ hn => by
    rw [ArithmeticFunction.one_apply, if_neg hn, zero_div]]
  simp

theorem weightNorm_pow_le (N : ℕ) {g : ArithmeticFunction ℝ} (hg : ∀ n, 0 ≤ g n) (j : ℕ) :
    weightNorm N (g ^ j) ≤ weightNorm N g ^ j := by
  induction j with
  | zero => rw [pow_zero, pow_zero]; exact weightNorm_one_le N
  | succ j ih =>
    rw [pow_succ, pow_succ]
    exact (weightNorm_mul_le N (pow_apply_nonneg hg j) hg).trans
      (mul_le_mul_of_nonneg_right ih (weightNorm_nonneg hg))

theorem weightNorm_single_one_mul (N : ℕ) (c : ℝ) (f : ArithmeticFunction ℝ) :
    weightNorm N (single 1 c * f) = c * weightNorm N f := by
  rw [weightNorm, weightNorm, Finset.mul_sum]
  exact Finset.sum_congr rfl fun n _ => by rw [single_one_mul_apply]; ring

theorem weightNorm_add (N : ℕ) (f g : ArithmeticFunction ℝ) :
    weightNorm N (f + g) = weightNorm N f + weightNorm N g := by
  rw [weightNorm, weightNorm, weightNorm, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun n _ => by rw [ArithmeticFunction.add_apply, add_div]

theorem weightNorm_sum {ι : Type*} (N : ℕ) (s : Finset ι) (f : ι → ArithmeticFunction ℝ) :
    weightNorm N (∑ i ∈ s, f i) = ∑ i ∈ s, weightNorm N (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [weightNorm]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, weightNorm_add, ih]

/-- `W_N(exp_L g) ≤ e^{W_N(g)}` for nonnegative `g`. -/
theorem weightNorm_expTrunc_le (N L : ℕ) {g : ArithmeticFunction ℝ} (hg : ∀ n, 0 ≤ g n) :
    weightNorm N (expTrunc L g) ≤ Real.exp (weightNorm N g) := by
  rw [expTrunc, weightNorm_sum]
  refine le_trans (Finset.sum_le_sum fun j _ => ?_) (Real.sum_le_exp_of_nonneg
    (weightNorm_nonneg hg) (L + 1))
  rw [weightNorm_single_one_mul, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (weightNorm_pow_le N hg j) (by positivity)

/-- `n^k − 1 ≤ k log n · n^k` for `n ≥ 1`, `k ≥ 0`. -/
theorem rpow_sub_one_le {n : ℕ} (hn : 1 ≤ n) (k : ℝ) :
    (n : ℝ) ^ k - 1 ≤ k * Real.log n * (n : ℝ) ^ k := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hy : 0 < (n : ℝ) ^ k := Real.rpow_pos_of_pos hn0 k
  have hlog : Real.log ((n : ℝ) ^ k) = k * Real.log n := Real.log_rpow hn0 k
  have h := Real.one_sub_inv_le_log_of_pos hy
  rw [hlog] at h
  have : (n : ℝ) ^ k - 1 = (1 - ((n : ℝ) ^ k)⁻¹) * (n : ℝ) ^ k := by field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_right h hy.le

/-- **The exponent is small**: `W_N(g_k) ≤ kN^kψ_{1/2}(N)`. -/
theorem weightNorm_tateExponent_le (N : ℕ) {k : ℝ} (hk : 0 ≤ k) :
    weightNorm N (tateExponent k) ≤
      k * (N : ℝ) ^ k * weightNorm N ArithmeticFunction.vonMangoldt := by
  rw [weightNorm, weightNorm, Finset.mul_sum]
  refine Finset.sum_le_sum fun n hn => ?_
  obtain ⟨h1, hN⟩ := Finset.mem_Icc.mp hn
  rw [tateExponent_apply, primePowerLog_apply]
  have hs : 0 ≤ (Real.sqrt n)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
  have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hpow : (n : ℝ) ^ k ≤ (N : ℝ) ^ k :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hN) hk
  have hsub := rpow_sub_one_le h1 k
  -- `ℓ(n)(n^k − 1) ≤ ℓ(n)·k log n·n^k = kΛ(n)n^k ≤ kΛ(n)N^k`
  have hterm : ArithmeticFunction.vonMangoldt n / Real.log n * ((n : ℝ) ^ k - 1) ≤
      k * (N : ℝ) ^ k * ArithmeticFunction.vonMangoldt n := by
    rcases eq_or_lt_of_le hlog with h0 | hpos
    · rw [← h0, div_zero, zero_mul]
      exact mul_nonneg (mul_nonneg hk (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hΛ
    · have hℓ : 0 ≤ ArithmeticFunction.vonMangoldt n / Real.log n := div_nonneg hΛ hlog
      calc ArithmeticFunction.vonMangoldt n / Real.log n * ((n : ℝ) ^ k - 1)
          ≤ ArithmeticFunction.vonMangoldt n / Real.log n * (k * Real.log n * (n : ℝ) ^ k) :=
            mul_le_mul_of_nonneg_left hsub hℓ
        _ = k * (n : ℝ) ^ k * ArithmeticFunction.vonMangoldt n := by field_simp
        _ ≤ k * (N : ℝ) ^ k * ArithmeticFunction.vonMangoldt n :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hk) hΛ
  calc ArithmeticFunction.vonMangoldt n / Real.log n * ((n : ℝ) ^ k - 1) / Real.sqrt n
      = (ArithmeticFunction.vonMangoldt n / Real.log n * ((n : ℝ) ^ k - 1)) * (Real.sqrt n)⁻¹ := by
        rw [div_eq_mul_inv]
    _ ≤ (k * (N : ℝ) ^ k * ArithmeticFunction.vonMangoldt n) * (Real.sqrt n)⁻¹ :=
        mul_le_mul_of_nonneg_right hterm hs
    _ = k * (N : ℝ) ^ k * (ArithmeticFunction.vonMangoldt n / Real.sqrt n) := by ring

/-- `W_N(J_k) ≤ exp(kN^kψ_{1/2}(N))` for `k ≥ 0`. -/
theorem weightNorm_jordan_le (N : ℕ) {k : ℝ} (hk : 0 ≤ k) :
    weightNorm N (jordanFun k) ≤
      Real.exp (k * (N : ℝ) ^ k * weightNorm N ArithmeticFunction.vonMangoldt) := by
  have hmem := expTrunc_sub_jordan_mem (N := N) (L := N)
    (Nat.lt_two_pow_self.trans (Nat.pow_lt_pow_right (by norm_num) (by omega))) k
  have heq : weightNorm N (jordanFun k) = weightNorm N (expTrunc N (tateExponent k)) := by
    refine Finset.sum_congr rfl fun n hn => ?_
    obtain ⟨h1, hN⟩ := Finset.mem_Icc.mp hn
    have := hmem n h1 hN
    rw [sub_apply', sub_eq_zero] at this
    rw [this]
  rw [heq]
  exact (weightNorm_expTrunc_le N N (tateExponent_nonneg hk)).trans
    (Real.exp_le_exp.mpr (weightNorm_tateExponent_le N hk))

/-! ### Positivity of the Tate operators -/

variable {A : ℝ} {H : ℝ → ℝ}

theorem abs_autocorr_le (hH : IsWindowTest A H) (ℓ : ℝ) :
    |∫ u, H u * H (u + ℓ)| ≤ ∫ u, H u ^ 2 := by
  have hc := hH.continuous
  have iH : MeasureTheory.Integrable fun u => H u ^ 2 :=
    _root_.RHTower.WeilMarkovPole.integrable_sq hc hH.hasCompactSupport
  have iH' : MeasureTheory.Integrable fun u => H (u + ℓ) ^ 2 := iH.comp_add_right ℓ
  have iP : MeasureTheory.Integrable fun u => H u * H (u + ℓ) :=
    (hc.mul (hc.comp (continuous_add_const ℓ))).integrable_of_hasCompactSupport
      hH.hasCompactSupport.mul_right
  have hshift : ∫ u, H (u + ℓ) ^ 2 = ∫ u, H u ^ 2 :=
    MeasureTheory.integral_add_right_eq_self (fun u => H u ^ 2) ℓ
  have iS : MeasureTheory.Integrable fun u => (H u ^ 2 + H (u + ℓ) ^ 2) / 2 :=
    (iH.add iH').div_const 2
  have hS : ∫ u, (H u ^ 2 + H (u + ℓ) ^ 2) / 2 = ∫ u, H u ^ 2 := by
    rw [MeasureTheory.integral_div, MeasureTheory.integral_add iH iH', hshift]; ring
  rw [abs_le]
  constructor
  · have := MeasureTheory.integral_mono (f := fun u => -((H u ^ 2 + H (u + ℓ) ^ 2) / 2))
      (g := fun u => H u * H (u + ℓ)) iS.neg iP fun u => by
      show -((H u ^ 2 + H (u + ℓ) ^ 2) / 2) ≤ H u * H (u + ℓ)
      nlinarith [sq_nonneg (H u + H (u + ℓ))]
    rw [MeasureTheory.integral_neg, hS] at this
    linarith
  · have := MeasureTheory.integral_mono (f := fun u => H u * H (u + ℓ))
      (g := fun u => (H u ^ 2 + H (u + ℓ) ^ 2) / 2) iP iS fun u => by
      show H u * H (u + ℓ) ≤ (H u ^ 2 + H (u + ℓ) ^ 2) / 2
      nlinarith [sq_nonneg (H u - H (u + ℓ))]
    rw [hS] at this
    linarith

/-- **The Tate function is bounded below by the weighted norm of the Jordan counts**:
`τ_H(k) ≥ (2 − W_N(J_k))‖H‖²` for `k ≥ 0`. -/
theorem tateFunction_ge_two_sub (hH : IsWindowTest A H) {k : ℝ} (hk : 0 ≤ k) :
    (2 - weightNorm (windowLevel A) (jordanFun k)) * ∫ u, H u ^ 2 ≤ tateFunction A H k := by
  set N := windowLevel A
  rw [tateFunction_eq hH]
  have hnorm : 0 ≤ ∫ u, H u ^ 2 := MeasureTheory.integral_nonneg fun u => sq_nonneg _
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · -- an empty window carries only the zero test
    have hz : ∀ u, H u = 0 := fun u => hH.vanish u fun hm => by
      have : A < 0 := by
        by_contra h
        have := Nat.one_le_floor_iff _ |>.mpr (Real.one_le_exp (not_lt.mp h))
        change 1 ≤ windowLevel A at this
        omega
      linarith [hm.1, hm.2]
    simp [hz]
  -- termwise: `J_k(n)/√n·c_n ≥ (2[n=1] − J_k(n)/√n)‖H‖²`
  have hterm : ∀ n ∈ Finset.Icc 1 N,
      (2 * (if n = 1 then 1 else 0) - jordanFun k n / Real.sqrt n) * ∫ u, H u ^ 2 ≤
        jordanTotient k n / Real.sqrt n * ∫ u, H u * H (u + Real.log n) := fun n hn => by
    have hJ : 0 ≤ jordanTotient k n / Real.sqrt n :=
      div_nonneg ((add_nonneg (by split_ifs <;> norm_num) (tateExponent_nonneg hk n)).trans
        (jordanTotient_ge_exp_tangent hk n)) (Real.sqrt_nonneg _)
    have hc := abs_le.mp (abs_autocorr_le hH (Real.log n))
    rw [jordanFun_apply]
    by_cases h1 : n = 1
    · subst h1
      have : (∫ u, H u * H (u + Real.log (1 : ℕ))) = ∫ u, H u ^ 2 := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        simp [sq]
      rw [this, if_pos rfl]
      have hJ1 : jordanTotient k 1 = 1 := by simp [jordanTotient]
      simp only [hJ1, Nat.cast_one, Real.sqrt_one, div_one]
      nlinarith
    · rw [if_neg h1]
      nlinarith [mul_le_mul_of_nonneg_left hc.1 hJ]
  have hsum := Finset.sum_le_sum hterm
  have hone : ∑ n ∈ Finset.Icc 1 N, (2 * (if n = 1 then (1 : ℝ) else 0)) = 2 := by
    rw [Finset.sum_eq_single_of_mem 1 (Finset.mem_Icc.mpr ⟨le_rfl, hpos⟩) fun n _ hn => by
      rw [if_neg hn, mul_zero]]
    simp
  rw [← Finset.sum_mul, Finset.sum_sub_distrib, hone] at hsum
  exact hsum

/-- **The Tate operators are positive below the horizon**: if `kN^kψ_{1/2}(N) ≤ log 2`, `N = ⌊e^A⌋`,
then `τ_H(k) ≥ 0` for every window test. -/
theorem tateFunction_nonneg_of_le_log_two (hH : IsWindowTest A H) {k : ℝ} (hk : 0 ≤ k)
    (hsmall : k * (windowLevel A : ℝ) ^ k *
      weightNorm (windowLevel A) ArithmeticFunction.vonMangoldt ≤ Real.log 2) :
    0 ≤ tateFunction A H k := by
  have h1 := tateFunction_ge_two_sub hH hk
  have h2 : weightNorm (windowLevel A) (jordanFun k) ≤ 2 :=
    (weightNorm_jordan_le _ hk).trans (by
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      exact Real.exp_le_exp.mpr hsmall)
  have hnorm : 0 ≤ ∫ u, H u ^ 2 := MeasureTheory.integral_nonneg fun u => sq_nonneg _
  exact le_trans (mul_nonneg (by linarith) hnorm) h1

end GaloisForLFunctions.WindowTowerOfSpecZ
