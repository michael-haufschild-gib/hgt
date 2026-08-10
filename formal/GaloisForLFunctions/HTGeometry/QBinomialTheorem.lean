import Mathlib
import GaloisForLFunctions.HTGeometry.QPochhammer

/-!
# The q-binomial theorem for a positive real nome

Euler's series `∑ aⁿ/(q;q)ₙ` sums to `1/(a;q)_∞` for every complex `a` in the open unit disc and
every nome `0 < q < 1`.  The proof is the classical one: the series satisfies the functional
equation `F(aq) = (1-a)·F(a)`, iterating it against the finite q-Pochhammer product gives
`F(a)·∏_{k<N}(1-aq^k) = F(aq^N)`, and the right-hand side tends to `1` by dominated convergence
while the product tends to `(a;q)_∞`.

This is the complex q-binomial transform announced by `QPochhammer`, where only the integral
intervention powers were closed.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

/-- The Euler q-exponential term `aⁿ/(q;q)ₙ`. -/
def qBinomialTerm (q : RealEulerNome) (a : ℂ) (n : ℕ) : ℂ :=
  a ^ n / ((realQFactorial q n : ℝ) : ℂ)

@[simp] theorem qBinomialTerm_zero (q : RealEulerNome) (a : ℂ) : qBinomialTerm q a 0 = 1 := by
  simp [qBinomialTerm, realQFactorial]

theorem realQFactorial_antitone (q : RealEulerNome) : Antitone (realQFactorial q) := by
  refine antitone_nat_of_succ_le fun n => ?_
  rw [realQFactorial_succ]
  nth_rewrite 2 [← mul_one (realQFactorial q n)]
  refine mul_le_mul_of_nonneg_left ?_ (realQFactorial_pos q n).le
  have := pow_pos q.pos (n + 1)
  linarith

/-- The infinite q-factorial is a lower bound for every finite one. -/
theorem realQFactorialInf_le (q : RealEulerNome) (n : ℕ) :
    realQFactorialInf q ≤ realQFactorial q n := by
  refine le_of_tendsto (realQFactorial_tendsto q) ?_
  filter_upwards [Filter.eventually_ge_atTop n] with m hm
  exact realQFactorial_antitone q hm

theorem realQFactorialInf_pos (q : RealEulerNome) : 0 < realQFactorialInf q := by
  have hle : realQFactorialInf q ≤ realQFactorial q 0 := realQFactorialInf_le q 0
  have hne := realQFactorialInf_ne_zero q
  have hnn : 0 ≤ realQFactorialInf q :=
    ge_of_tendsto' (realQFactorial_tendsto q) fun n => (realQFactorial_pos q n).le
  exact lt_of_le_of_ne hnn (Ne.symm hne)

theorem norm_qBinomialTerm_le (q : RealEulerNome) (a : ℂ) (n : ℕ) :
    ‖qBinomialTerm q a n‖ ≤ ‖a‖ ^ n / realQFactorialInf q := by
  rw [qBinomialTerm, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (realQFactorial_pos q n)]
  refine div_le_div_of_nonneg_left (by positivity) (realQFactorialInf_pos q) ?_
  exact realQFactorialInf_le q n

theorem qBinomialTerm_summable (q : RealEulerNome) {a : ℂ} (ha : ‖a‖ < 1) :
    Summable (qBinomialTerm q a) := by
  refine Summable.of_norm_bounded ?_ (norm_qBinomialTerm_le q a)
  exact ((summable_geometric_of_lt_one (norm_nonneg a) ha).div_const _)

/-- The Euler q-exponential sum. -/
def qBinomialSum (q : RealEulerNome) (a : ℂ) : ℂ := ∑' n : ℕ, qBinomialTerm q a n

theorem qBinomialSum_hasSum (q : RealEulerNome) {a : ℂ} (ha : ‖a‖ < 1) :
    HasSum (qBinomialTerm q a) (qBinomialSum q a) :=
  (qBinomialTerm_summable q ha).hasSum

/-- **The Euler functional equation.**  `F(aq) = (1-a)·F(a)`. -/
theorem qBinomialTerm_hasSum_mul (q : RealEulerNome) {a : ℂ} {S : ℂ}
    (hS : HasSum (qBinomialTerm q a) S) :
    HasSum (qBinomialTerm q (a * (q.val : ℂ))) ((1 - a) * S) := by
  have hstep : ∀ n : ℕ, qBinomialTerm q (a * (q.val : ℂ)) (n + 1)
      = qBinomialTerm q a (n + 1) - a * qBinomialTerm q a n := by
    intro n
    have hfac : ((realQFactorial q n : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (realQFactorial_pos q n).ne'
    have hstepfac : ((1 - q.val ^ (n + 1) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (realQFactorial_factor_pos q n).ne'
    have hsucc : ((realQFactorial q (n + 1) : ℝ) : ℂ)
        = ((realQFactorial q n : ℝ) : ℂ) * ((1 - q.val ^ (n + 1) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, realQFactorial_succ]
    rw [qBinomialTerm, qBinomialTerm, qBinomialTerm, hsucc]
    rw [mul_pow]
    field_simp
    push_cast
    ring
  have htail : HasSum (fun n : ℕ => qBinomialTerm q (a * (q.val : ℂ)) (n + 1))
      ((1 - a) * S - ∑ i ∈ Finset.range 1, qBinomialTerm q (a * (q.val : ℂ)) i) := by
    have h1 : HasSum (fun n : ℕ => qBinomialTerm q a (n + 1)) (S - qBinomialTerm q a 0) := by
      have := (hasSum_nat_add_iff' (f := qBinomialTerm q a) 1).mpr hS
      simpa using this
    have h2 : HasSum (fun n : ℕ => a * qBinomialTerm q a n) (a * S) := hS.mul_left a
    have hcomb : ((1 - a) * S - ∑ i ∈ Finset.range 1, qBinomialTerm q (a * (q.val : ℂ)) i)
        = (S - qBinomialTerm q a 0) - a * S := by
      simp only [Finset.sum_range_one, qBinomialTerm_zero]
      ring
    rw [hcomb]
    refine (h1.sub h2).congr_fun fun n => ?_
    rw [hstep n]
  exact (hasSum_nat_add_iff' (f := qBinomialTerm q (a * (q.val : ℂ))) 1).mp htail

theorem qBinomialSum_mul (q : RealEulerNome) {a : ℂ} (ha : ‖a‖ < 1) :
    qBinomialSum q (a * (q.val : ℂ)) = (1 - a) * qBinomialSum q a :=
  (qBinomialTerm_hasSum_mul q (qBinomialSum_hasSum q ha)).tsum_eq

theorem norm_mul_qpow_lt_one (q : RealEulerNome) {a : ℂ} (ha : ‖a‖ < 1) (N : ℕ) :
    ‖a * (q.val : ℂ) ^ N‖ < 1 := by
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos q.pos]
  have hq : q.val ^ N ≤ 1 := pow_le_one₀ q.pos.le q.lt_one.le
  nlinarith [norm_nonneg a, pow_pos q.pos N]

/-- Iterating the functional equation `N` times. -/
theorem qBinomialSum_mul_prod (q : RealEulerNome) {a : ℂ} (ha : ‖a‖ < 1) (N : ℕ) :
    qBinomialSum q a * ∏ k ∈ Finset.range N, (1 - a * (q.val : ℂ) ^ k)
      = qBinomialSum q (a * (q.val : ℂ) ^ N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hnorm : ‖a * (q.val : ℂ) ^ N‖ < 1 := norm_mul_qpow_lt_one q ha N
    have hstep := qBinomialSum_mul q hnorm
    rw [Finset.prod_range_succ, ← mul_assoc, ih]
    rw [show a * (q.val : ℂ) ^ (N + 1) = (a * (q.val : ℂ) ^ N) * (q.val : ℂ) by ring, hstep]
    ring

theorem tendsto_qBinomialSum_mul_qpow (q : RealEulerNome) {a : ℂ} (ha : ‖a‖ < 1) :
    Tendsto (fun N : ℕ => qBinomialSum q (a * (q.val : ℂ) ^ N)) atTop (𝓝 1) := by
  have hbound : ∀ N n : ℕ, ‖qBinomialTerm q (a * (q.val : ℂ) ^ N) n‖
      ≤ ‖a‖ ^ n / realQFactorialInf q := by
    intro N n
    refine le_trans (norm_qBinomialTerm_le q _ n) ?_
    refine div_le_div_of_nonneg_right ?_ (realQFactorialInf_pos q).le
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ n
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos q.pos]
    nth_rewrite 2 [← mul_one ‖a‖]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg a)
    exact pow_le_one₀ q.pos.le q.lt_one.le
  have hsummable : Summable (fun n : ℕ => ‖a‖ ^ n / realQFactorialInf q) :=
    (summable_geometric_of_lt_one (norm_nonneg a) ha).div_const _
  have hpoint : ∀ n : ℕ, Tendsto (fun N : ℕ => qBinomialTerm q (a * (q.val : ℂ) ^ N) n) atTop
      (𝓝 (if n = 0 then 1 else 0)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp
    · have hq : Tendsto (fun N : ℕ => (q.val : ℂ) ^ N) atTop (𝓝 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        simp only [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos q.pos]
        exact tendsto_pow_atTop_nhds_zero_of_lt_one q.pos.le q.lt_one
      have hterm : Tendsto (fun N : ℕ => (a * (q.val : ℂ) ^ N) ^ n) atTop (𝓝 0) := by
        have : Tendsto (fun N : ℕ => a * (q.val : ℂ) ^ N) atTop (𝓝 0) := by
          simpa using hq.const_mul a
        have hp := this.pow n
        simpa [zero_pow hn.ne'] using hp
      have hfac : ((realQFactorial q n : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (realQFactorial_pos q n).ne'
      have := hterm.div_const ((realQFactorial q n : ℝ) : ℂ)
      simpa [qBinomialTerm, if_neg hn.ne'] using this
  have hlim := tendsto_tsum_of_dominated_convergence (f := fun N n =>
      qBinomialTerm q (a * (q.val : ℂ) ^ N) n) hsummable hpoint
    (Filter.Eventually.of_forall fun N => hbound N)
  have hsum1 : ∑' n : ℕ, (if n = 0 then (1 : ℂ) else 0) = 1 := by
    rw [tsum_eq_single 0]
    · simp
    · intro b hb
      simp [hb]
  rw [hsum1] at hlim
  exact hlim

/-- **The q-binomial theorem.**  `∑ aⁿ/(q;q)ₙ = 1/(a;q)_∞` on the open unit disc. -/
theorem qBinomial_hasSum (q : RealEulerNome) {a : ℂ} (ha : ‖a‖ < 1) :
    HasSum (qBinomialTerm q a) (qPochhammerInf a q.toEulerNome)⁻¹ := by
  have hprod : Tendsto (fun N : ℕ => ∏ k ∈ Finset.range N, (1 - a * (q.val : ℂ) ^ k)) atTop
      (𝓝 (qPochhammerInf a q.toEulerNome)) := by
    have := qPochhammer_tendsto a q.toEulerNome
    simpa [qPochhammer, qPochhammerInf] using this
  have hlhs : Tendsto (fun N : ℕ => qBinomialSum q a
      * ∏ k ∈ Finset.range N, (1 - a * (q.val : ℂ) ^ k)) atTop
      (𝓝 (qBinomialSum q a * qPochhammerInf a q.toEulerNome)) :=
    hprod.const_mul _
  have heq : (fun N : ℕ => qBinomialSum q a
      * ∏ k ∈ Finset.range N, (1 - a * (q.val : ℂ) ^ k))
      = fun N : ℕ => qBinomialSum q (a * (q.val : ℂ) ^ N) := by
    funext N
    exact qBinomialSum_mul_prod q ha N
  rw [heq] at hlhs
  have hone : qBinomialSum q a * qPochhammerInf a q.toEulerNome = 1 :=
    tendsto_nhds_unique hlhs (tendsto_qBinomialSum_mul_qpow q ha)
  have hne : qPochhammerInf a q.toEulerNome ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hone
    exact zero_ne_one hone
  have hval : qBinomialSum q a = (qPochhammerInf a q.toEulerNome)⁻¹ :=
    eq_inv_of_mul_eq_one_left hone
  rw [← hval]
  exact qBinomialSum_hasSum q ha

end

end GaloisForLFunctions.HTGeometry
