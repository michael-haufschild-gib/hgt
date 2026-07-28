import Mathlib

/-!
# The half-weighted prime mass is of order `√X`

The prime side of a rectangular Weil window pairs the von Mangoldt weights `Λ(k)/√k` against a
compactly supported autocorrelation.  The relevant magnitude is therefore the half-weighted mass

```text
∑_{n ≤ X} Λ(n)/√n ,
```

and this file bounds it on both sides, unconditionally and without partial summation.

*Lower.*  Every term with `n ≤ X` satisfies `√n ≤ √X`, so the mass dominates `ψ(X)/√X` termwise,
and Chebyshev's unconditional bound `ψ(x) ≥ (x−1)log 2 − log(x+2)` gives `≥ (log 2 / 2)·√X`.

*Upper.*  `Λ(n) ≤ log n ≤ log X` on the range, and `∑_{n=1}^{N} 1/√n ≤ 2√N` by induction, giving
`≤ 2·log X·√X`.

So the mass is `√X` up to a logarithm.  Since the sum is dominated by the top of its range, this is
also the order of the moving-window contribution at aperture `a = ½log X`, which is the part of the
prime side that varies with the aperture.
-/

open Filter Finset Real

namespace RHTower

open ArithmeticFunction Chebyshev

/-- The half-weighted prime mass of a window reaching up to `X`. -/
noncomputable def primeMassHalf (X : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 ⌊X⌋₊, ArithmeticFunction.vonMangoldt n / Real.sqrt n

/-- **The mass dominates the flat-weighted sum.**  Each weight `1/√n` with `n ≤ X` is at least
`1/√X`, so the mass is at least `ψ(X)/√X`. -/
theorem psi_div_sqrt_le_primeMassHalf {X : ℝ} (hX : 0 ≤ X) :
    Chebyshev.psi X / Real.sqrt X ≤ primeMassHalf X := by
  rw [Chebyshev.psi_eq_sum_Icc, primeMassHalf, Finset.sum_div]
  refine Finset.sum_le_sum fun n hn => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · simp
  have hnX : (n : ℝ) ≤ X := by
    have h1 : n ≤ ⌊X⌋₊ := (Finset.mem_Icc.mp hn).2
    exact le_trans (Nat.cast_le.mpr h1) (Nat.floor_le hX)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
  have hsq : Real.sqrt n ≤ Real.sqrt X := Real.sqrt_le_sqrt hnX
  have hsqpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  exact div_le_div_of_nonneg_left (ArithmeticFunction.vonMangoldt_nonneg) hsqpos hsq

/-- **The prime mass is eventually at least `(log 2 / 2)·√X`.**  Chebyshev's unconditional lower
bound on `ψ` transfers through the previous inequality; the logarithmic correction is absorbed for
large `X`. -/
theorem eventually_sqrt_le_primeMassHalf :
    ∀ᶠ X in atTop, (Real.log 2 / 2) * Real.sqrt X ≤ primeMassHalf X := by
  have hO : (fun X : ℝ => X + 2) =O[atTop] (fun X : ℝ => X) := by
    refine Asymptotics.IsBigO.of_bound 2 ?_
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with X hX
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith),
      abs_of_nonneg (by linarith)]
    linarith
  have hlittle : (fun X : ℝ => Real.log (X + 2)) =o[atTop] (fun X : ℝ => X) :=
    (Real.isLittleO_log_id_atTop.comp_tendsto
      (tendsto_atTop_add_const_right atTop 2 tendsto_id)).trans_isBigO hO
  have hdiv := hlittle.tendsto_div_nhds_zero
  filter_upwards [hdiv.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 100 by norm_num)),
    eventually_ge_atTop (3 : ℝ)] with X h1 hX3
  have hX0 : (0 : ℝ) ≤ X := by linarith
  have hXpos : (0 : ℝ) < X := by linarith
  have hlogsmall : Real.log (X + 2) < X / 100 := by
    rw [div_lt_iff₀ hXpos] at h1
    linarith
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hsqrtpos : 0 < Real.sqrt X := Real.sqrt_pos.mpr hXpos
  have hsq : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0
  refine le_trans ?_ (psi_div_sqrt_le_primeMassHalf hX0)
  rw [le_div_iff₀ hsqrtpos]
  refine le_trans ?_ (Chebyshev.psi_ge' hX0)
  nlinarith [hsq, hlogsmall, hlog2, hX3]


/-! ### The matching upper bound

The upper direction needs no partial summation either: `Λ(n) ≤ log n ≤ log X` on the range, so the
mass is at most `log X` times the harmonic-square-root sum, which is at most `2√X`.  The extra
logarithm is harmless — it does not move the exponent, which is the only thing the precision
comparison depends on. -/

/-- `∑_{n=1}^{N} 1/√n ≤ 2√N`, by induction on `N`. -/
theorem sum_one_div_sqrt_le (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / Real.sqrt n ≤ 2 * Real.sqrt N := by
  induction N with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
    have hs : Real.sqrt ((M : ℝ) + 1) > 0 := Real.sqrt_pos.mpr hM1
    have hkey : (1 : ℝ) / Real.sqrt ((M : ℕ) + 1)
        ≤ 2 * Real.sqrt ((M : ℕ) + 1) - 2 * Real.sqrt M := by
      rw [div_le_iff₀ (by exact hs)]
      nlinarith [Real.sq_sqrt hM, Real.sq_sqrt hM1.le, Real.sqrt_nonneg (M : ℝ),
        Real.sqrt_le_sqrt (show (M : ℝ) ≤ (M : ℝ) + 1 by linarith), hs]
    push_cast at hkey ⊢
    linarith

/-- Splitting off the vanishing zeroth term. -/
theorem Icc_zero_eq_insert (N : ℕ) : Finset.Icc 0 N = insert 0 (Finset.Icc 1 N) := by
  ext n
  simp only [Finset.mem_Icc, Finset.mem_insert, Nat.zero_le, true_and]
  omega

/-- **The prime mass is at most `2·log X·√X`.**  Termwise `Λ(n) ≤ log X` on the range, and the
harmonic-square-root sum is at most `2√X`. -/
theorem primeMassHalf_le {X : ℝ} (hX : 1 ≤ X) :
    primeMassHalf X ≤ 2 * Real.log X * Real.sqrt X := by
  have hX0 : (0 : ℝ) ≤ X := by linarith
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX
  have hterm : ∀ n ∈ Finset.Icc 0 ⌊X⌋₊,
      ArithmeticFunction.vonMangoldt n / Real.sqrt n ≤ Real.log X * ((1 : ℝ) / Real.sqrt n) := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp
    have hnX : (n : ℝ) ≤ X :=
      le_trans (Nat.cast_le.mpr (Finset.mem_Icc.mp hn).2) (Nat.floor_le hX0)
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
    have hsqpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
    have hlogn : ArithmeticFunction.vonMangoldt n ≤ Real.log X :=
      le_trans ArithmeticFunction.vonMangoldt_le_log (Real.log_le_log hnpos hnX)
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right hlogn hsqpos.le
  calc primeMassHalf X ≤ ∑ n ∈ Finset.Icc 0 ⌊X⌋₊, Real.log X * ((1 : ℝ) / Real.sqrt n) :=
        Finset.sum_le_sum hterm
    _ = Real.log X * ∑ n ∈ Finset.Icc 0 ⌊X⌋₊, (1 : ℝ) / Real.sqrt n := by rw [Finset.mul_sum]
    _ = Real.log X * ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (1 : ℝ) / Real.sqrt n := by
        rw [Icc_zero_eq_insert, Finset.sum_insert (by simp)]
        simp
    _ ≤ Real.log X * (2 * Real.sqrt ⌊X⌋₊) := by
        exact mul_le_mul_of_nonneg_left (sum_one_div_sqrt_le _) hlogX
    _ ≤ 2 * Real.log X * Real.sqrt X := by
        have : Real.sqrt (⌊X⌋₊ : ℝ) ≤ Real.sqrt X := Real.sqrt_le_sqrt (Nat.floor_le hX0)
        nlinarith [Real.sqrt_nonneg (X : ℝ), Real.sqrt_nonneg ((⌊X⌋₊ : ℝ))]

/-- **Two-sided: the prime mass is `√X` up to a logarithm.**  The exponent is `1/2` on both sides,
which is all the precision comparison depends on. -/
theorem primeMassHalf_two_sided :
    ∀ᶠ X in atTop, (Real.log 2 / 2) * Real.sqrt X ≤ primeMassHalf X ∧
      primeMassHalf X ≤ 2 * Real.log X * Real.sqrt X := by
  filter_upwards [eventually_sqrt_le_primeMassHalf, eventually_ge_atTop (1 : ℝ)] with X h1 h2
  exact ⟨h1, primeMassHalf_le h2⟩


end RHTower
