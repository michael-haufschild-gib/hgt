import GaloisForLFunctions.RHTower.MertensConstantIdentification

/-!
# Mertens' third theorem

```text
∏_{p ≤ N} (1 - 1/p) · log N → e^(-γ).
```

The logarithm of the product is `B_N - ∑_{p ≤ N} 1/p` with `B_N → ∑_p (log(1-1/p) + 1/p)`, and the
Mertens constant satisfies `M = γ + ∑_p (log(1-1/p) + 1/p)`, so the exponent tends to `-γ`.
-/

open Filter Topology MeasureTheory Set
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The Mertens product `∏_{p ≤ N} (1 - 1/p)`. -/
def mertensPrimeProduct (N : ℕ) : ℝ :=
  ∏ n ∈ Finset.Icc 0 N, (if n.Prime then 1 - ((n : ℝ))⁻¹ else 1)

private theorem factor_pos {n : ℕ} : 0 < (if n.Prime then 1 - ((n : ℝ))⁻¹ else 1) := by
  by_cases hp : n.Prime
  · rw [if_pos hp]
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hp.two_le
    have : ((n : ℝ))⁻¹ ≤ 1 / 2 := by
      rw [one_div, inv_le_inv₀ (by linarith) (by norm_num)]
      exact hn2
    linarith
  · rw [if_neg hp]
    norm_num

theorem mertensPrimeProduct_pos (N : ℕ) : 0 < mertensPrimeProduct N :=
  Finset.prod_pos fun _ _ => factor_pos

/-- The partial higher-power defect `∑_{p ≤ N} (log(1 - 1/p) + 1/p)`. -/
def primeLogDefectPartial (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 N, (if n.Prime then Real.log (1 - ((n : ℝ))⁻¹) + ((n : ℝ))⁻¹ else 0)

theorem log_mertensPrimeProduct (N : ℕ) :
    Real.log (mertensPrimeProduct N) = primeLogDefectPartial N - primeRecipSum N := by
  rw [mertensPrimeProduct, Real.log_prod (fun n _ => (factor_pos (n := n)).ne'),
    primeLogDefectPartial, primeRecipSum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hp : n.Prime <;> simp [primeRecipWeight, hp]

/-! ## The limit of the partial defect -/

private theorem defectTerm_eq (n : ℕ) :
    Real.log (1 - ((n : ℝ))⁻¹) + ((n : ℝ))⁻¹ =
      -(-Real.log (1 - ((n : ℝ)) ^ (-(1 : ℝ))) - ((n : ℝ)) ^ (-(1 : ℝ))) := by
  rw [Real.rpow_neg_one]
  ring

theorem summable_defectIndicator :
    Summable (fun n : ℕ =>
      if n.Prime then Real.log (1 - ((n : ℝ))⁻¹) + ((n : ℝ))⁻¹ else 0) := by
  have hsub : Summable ((fun n : ℕ =>
      if n.Prime then Real.log (1 - ((n : ℝ))⁻¹) + ((n : ℝ))⁻¹ else 0) ∘
      (Subtype.val : {n : ℕ | n.Prime} → ℕ)) := by
    refine ((summable_primeLogDefectTerm (s := (1 : ℝ)) le_rfl).neg).congr fun p => ?_
    have hp : Nat.Prime (p : ℕ) := p.2
    rw [Function.comp_apply, if_pos hp, defectTerm_eq (p : ℕ)]
  refine (summable_subtype_iff_indicator.mp hsub).congr fun n => ?_
  by_cases hp : n.Prime
  · rw [indicator_of_mem (show n ∈ {n : ℕ | n.Prime} from hp)]
  · rw [indicator_of_notMem (by simpa using hp), if_neg hp]

theorem tsum_defectIndicator :
    (∑' n : ℕ, if n.Prime then Real.log (1 - ((n : ℝ))⁻¹) + ((n : ℝ))⁻¹ else 0) =
      -primeLogDefect 1 := by
  have hsupp : Function.support (fun n : ℕ =>
      if n.Prime then Real.log (1 - ((n : ℝ))⁻¹) + ((n : ℝ))⁻¹ else 0) ⊆
      {n : ℕ | n.Prime} := by
    intro n hn
    simp only [Function.mem_support] at hn
    by_contra hc
    simp only [Set.mem_setOf_eq] at hc
    rw [if_neg hc] at hn
    exact hn rfl
  rw [← tsum_subtype_eq_of_support_subset hsupp, primeLogDefect, ← tsum_neg]
  refine tsum_congr fun p => ?_
  have hp : Nat.Prime (p : ℕ) := p.2
  rw [if_pos hp, defectTerm_eq (p : ℕ)]

theorem tendsto_primeLogDefectPartial :
    Tendsto primeLogDefectPartial atTop (nhds (-primeLogDefect 1)) := by
  have h := summable_defectIndicator.hasSum.tendsto_sum_nat
  rw [tsum_defectIndicator] at h
  have hshift := h.comp (tendsto_add_atTop_nat 1)
  refine hshift.congr fun N => ?_
  rw [Function.comp_apply, primeLogDefectPartial]
  congr 1
  ext n
  simp [Finset.mem_Icc, Finset.mem_range]

/-! ## Mertens' third theorem -/

/-- **Mertens' third theorem.**  `∏_{p ≤ N} (1 - 1/p) · log N → e^(-γ)`. -/
theorem tendsto_mertensPrimeProduct_mul_log :
    Tendsto (fun N : ℕ => mertensPrimeProduct N * Real.log N) atTop
      (nhds (Real.exp (-Real.eulerMascheroniConstant))) := by
  have hexp : Tendsto (fun N : ℕ => Real.exp (primeLogDefectPartial N -
      (primeRecipSum N - Real.log (Real.log N)))) atTop
      (nhds (Real.exp (-primeLogDefect 1 - mertensSecondConstant))) := by
    have hinner := tendsto_primeLogDefectPartial.sub tendsto_primeRecipSum_sub_logLog
    exact (Real.continuous_exp.tendsto _).comp hinner
  have hval : -primeLogDefect 1 - mertensSecondConstant = -Real.eulerMascheroniConstant := by
    rw [mertensSecondConstant_eq]
    ring
  rw [hval] at hexp
  refine hexp.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 2] with N hN
  have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  rw [show primeLogDefectPartial N - (primeRecipSum N - Real.log (Real.log N)) =
      (primeLogDefectPartial N - primeRecipSum N) + Real.log (Real.log N) by ring,
    Real.exp_add, ← log_mertensPrimeProduct N, Real.exp_log (mertensPrimeProduct_pos N),
    Real.exp_log hlogN]

end

end RHTower
