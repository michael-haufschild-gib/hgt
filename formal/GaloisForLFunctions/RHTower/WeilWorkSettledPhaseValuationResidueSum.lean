import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseValuationTightness

/-!
# No endpoint mass escapes to infinite prime valuation

The actual real valuation endpoints are absolutely summable and sum to one.
Uniform divisibility tails justify the infinite depth passage. The endpoints
are signed: neither positivity nor canonical values are claimed.
-/

open Complex Filter Topology
noncomputable section
namespace RHTower.WeilSingularArithmetic
open WeilWorkSettledPhase

private theorem valuation_decay_lt_one {p : ℕ} (hp : p.Prime) :
    (Real.sqrt (p : ℝ))⁻¹ < 1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hs : 1 < Real.sqrt (p : ℝ) := by
    simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hp1
  exact inv_lt_one_of_one_lt₀ hs

private theorem endpoint_geometric {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {p : ℕ} (hp : p.Prime) {u : ℕ → ℝ}
    (hu : ∀ k : ℕ, Tendsto (fun s : ℝ =>
      LSeries (valuationPart p k (sourceCoeff lam)) (s : ℂ) /
        LSeries (sourceCoeff lam) (s : ℂ)) (𝓝[>] 1) (𝓝 (u k : ℂ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, |u k| ≤ C * (Real.sqrt (p : ℝ))⁻¹ ^ k := by
  obtain ⟨C, hC, hb⟩ := exists_forward_valuation_ratio_geometric hW hp
  refine ⟨C, hC, fun k => ?_⟩
  have ht : Tendsto (fun s : ℝ =>
      ‖LSeries (valuationPart p k (sourceCoeff lam)) (s : ℂ) /
        LSeries (sourceCoeff lam) (s : ℂ)‖) (𝓝[>] 1) (𝓝 |u k|) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using (hu k).norm
  exact le_of_tendsto ht (hb.mono fun s hs => hs k)

private theorem endpoint_partial_sum_bound {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {p : ℕ} (hp : p.Prime) {u : ℕ → ℝ}
    (hu : ∀ k : ℕ, Tendsto (fun s : ℝ =>
      LSeries (valuationPart p k (sourceCoeff lam)) (s : ℂ) /
        LSeries (sourceCoeff lam) (s : ℂ)) (𝓝[>] 1) (𝓝 (u k : ℂ))) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ N : ℕ,
      |1 - ∑ k ∈ Finset.range N, u k| ≤ D / Real.sqrt ((p ^ N : ℕ) : ℝ) := by
  obtain ⟨D, hD, hb⟩ := exists_forward_divisibility_ratio_bound hW
  refine ⟨D, hD, fun N => ?_⟩
  have ht := (tendsto_const_nhds (x := (1 : ℂ))).sub
    (tendsto_finsetSum (Finset.range N) fun k _ => hu k)
  have hn : Tendsto (fun s : ℝ => ‖1 -
      ∑ k ∈ Finset.range N, LSeries (valuationPart p k (sourceCoeff lam)) (s : ℂ) /
        LSeries (sourceCoeff lam) (s : ℂ)‖)
      (𝓝[>] 1) (𝓝 |1 - ∑ k ∈ Finset.range N, u k|) := by
    convert ht.norm using 1
    simp only [← Complex.ofReal_sum, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
  apply le_of_tendsto hn
  filter_upwards [self_mem_nhdsWithin, hb] with s hs hbs
  have ha : LSeries (sourceCoeff lam) (s : ℂ) ≠ 0 := by
    rw [(sourceCoeff_LSeries hW (s := (s : ℂ)) hs).2, IntegerMassRigidity.zetaOf]
    exact Complex.exp_ne_zero _
  rw [← Finset.sum_div, sum_range_valuation_LSeries
    (sourceCoeff_LSeries hW (s := (s : ℂ)) hs).1,
    sub_div, div_self ha, sub_sub_cancel]
  exact hbs (p ^ N) (pow_ne_zero _ hp.ne_zero)

/-- The actual endpoint sequence has total mass one and an absolute geometric
envelope. Full positivity is the only source premise. -/
theorem exists_forward_valuation_normalized_series {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {p : ℕ} (hp : p.Prime) :
    ∃ (u : ℕ → ℝ) (C : ℝ), 0 < u 0 ∧ 0 ≤ C ∧
      (∀ k : ℕ, Tendsto (fun s : ℝ =>
        LSeries (valuationPart p k (sourceCoeff lam)) (s : ℂ) /
          LSeries (sourceCoeff lam) (s : ℂ)) (𝓝[>] 1) (𝓝 (u k : ℂ))) ∧
      (∀ k : ℕ, |u k| ≤ C * (Real.sqrt (p : ℝ))⁻¹ ^ k) ∧
      Summable (fun k => |u k|) ∧ HasSum u 1 := by
  obtain ⟨ell, r, _, hr, _, hu⟩ := exists_forward_valuation_endpoints hW hp
  let u : ℕ → ℝ := fun k => r * valuationExponentialPolynomial ell k
  have hulim (k : ℕ) : Tendsto (fun s : ℝ =>
      LSeries (valuationPart p k (sourceCoeff lam)) (s : ℂ) /
        LSeries (sourceCoeff lam) (s : ℂ)) (𝓝[>] 1) (𝓝 (u k : ℂ)) := by
    simpa only [u, Complex.ofReal_mul] using hu k
  obtain ⟨C, hC, hbound⟩ := endpoint_geometric hW hp hulim
  have hu0 : 0 < u 0 := by
    simpa [u, valuationExponentialPolynomial, valuationPowerPolynomial] using hr
  have hs : Summable (fun k => |u k|) :=
    ((summable_geometric_of_lt_one (by positivity : 0 ≤ (Real.sqrt (p : ℝ))⁻¹)
      (valuation_decay_lt_one hp)).mul_left C).of_nonneg_of_le
        (fun _ => abs_nonneg _) hbound
  refine ⟨u, C, hu0, hC, hulim, hbound, hs, ?_⟩
  obtain ⟨D, hD, ht⟩ := endpoint_partial_sum_bound hW hp hulim
  have hpow : Tendsto (fun N : ℕ => D * (Real.sqrt (p : ℝ))⁻¹ ^ N)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by positivity : 0 ≤ (Real.sqrt (p : ℝ))⁻¹)
        (valuation_decay_lt_one hp)).const_mul D
  have htail : Tendsto (fun N : ℕ => ‖(∑ k ∈ Finset.range N, u k) - 1‖)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_) hpow
    simpa only [Real.norm_eq_abs, abs_sub_comm, sqrt_nat_pow, div_eq_mul_inv, ← inv_pow] using ht N
  apply (hasSum_iff_tendsto_nat_of_summable_norm (by simpa only [Real.norm_eq_abs] using hs)).mpr
  exact tendsto_iff_norm_sub_tendsto_zero.mpr htail

end RHTower.WeilSingularArithmetic
