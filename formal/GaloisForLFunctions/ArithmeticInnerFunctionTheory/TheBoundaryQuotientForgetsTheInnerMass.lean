import GaloisForLFunctions.ArithmeticInnerFunctionTheory.CastelnuovoConstructsTheMollifierOfACurve

/-!
# Boundary dilation quotients forget inner mass

For every finite curve datum, the mean of `|P(v)/P(ρv)|²` tends to one as `ρ → 1⁻`.
No condition on the Frobenius eigenvalues is needed. Factors with norm at most one have
the usual bound two; every other factor has a denominator bounded away from zero near
`ρ = 1`. Dominated convergence then applies off the finite boundary zero set.

The golden datum separates this boundary limit from holomorphic Abel mollification:
its quotient means tend to one, but every Abel budget is at least `φ² > 1`.
-/

open Complex Filter Topology MeasureTheory Set
open scoped Real

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

open ArithmeticCastelnuovoSeveri

noncomputable section

/-- An eventual bound for one boundary dilation quotient, including exterior roots. -/
def boundaryQuotientBound (β : ℂ) : ℝ :=
  if ‖β‖ ≤ 1 then 2 else 2 * (1 + ‖β‖) / (‖β‖ - 1)

theorem boundaryQuotientBound_nonneg (β : ℂ) : 0 ≤ boundaryQuotientBound β := by
  unfold boundaryQuotientBound
  split_ifs with h
  · norm_num
  · exact div_nonneg (by positivity) (by linarith)

/-- Exterior roots obstruct some intermediate dilations, but not dilations near one. -/
theorem eventually_boundary_factor_le (β : ℂ) :
    ∀ᶠ ρ : ℝ in 𝓝[<] 1, ∀ v : ℂ, ‖v‖ = 1 →
      ‖1 - β * v‖ / ‖1 - (ρ : ℂ) * β * v‖ ≤ boundaryQuotientBound β := by
  have hpos : ∀ᶠ ρ : ℝ in 𝓝[<] 1, 0 < ρ :=
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds zero_lt_one)
  have hlt : ∀ᶠ ρ : ℝ in 𝓝[<] 1, ρ < 1 := self_mem_nhdsWithin
  by_cases hβ : ‖β‖ ≤ 1
  · filter_upwards [hpos, hlt] with ρ hρ0 hρ1 v hv
    have hz : ‖β * v‖ ≤ 1 := by simpa [norm_mul, hv] using hβ
    have hbound := norm_one_sub_le_two_mul hρ0.le hρ1.le hz
    have hden : 0 < ‖1 - (ρ : ℂ) * β * v‖ := by
      have hn := norm_sub_norm_le (1 : ℂ) ((ρ : ℂ) * β * v)
      rw [norm_one, norm_mul, norm_mul, hv, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hρ0] at hn
      have hmul : ρ * ‖β‖ ≤ ρ := mul_le_of_le_one_right hρ0.le hβ
      linarith
    rw [boundaryQuotientBound, if_pos hβ]
    exact (div_le_iff₀ hden).mpr (by simpa only [mul_assoc] using hbound)
  · have hβ1 : 1 < ‖β‖ := lt_of_not_ge hβ
    have hlimit : Tendsto (fun ρ : ℝ => ρ * ‖β‖ - 1) (𝓝[<] 1) (𝓝 (‖β‖ - 1)) := by
      have hc : Continuous fun ρ : ℝ => ρ * ‖β‖ - 1 := by fun_prop
      simpa only [one_mul] using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
    have hgap : ∀ᶠ ρ : ℝ in 𝓝[<] 1, (‖β‖ - 1) / 2 < ρ * ‖β‖ - 1 :=
      hlimit.eventually (Ioi_mem_nhds (by linarith))
    filter_upwards [hpos, hgap] with ρ hρ hgap v hv
    have hden := norm_sub_norm_le ((ρ : ℂ) * β * v) (1 : ℂ)
    rw [norm_one, norm_mul, norm_mul, hv, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hρ, norm_sub_rev] at hden
    have hdenpos : 0 < ‖1 - (ρ : ℂ) * β * v‖ := by linarith
    have hnum : ‖1 - β * v‖ ≤ 1 + ‖β‖ := by
      simpa only [norm_one, norm_mul, hv, mul_one] using norm_sub_le (1 : ℂ) (β * v)
    rw [boundaryQuotientBound, if_neg hβ, div_le_iff₀ hdenpos]
    have hgap0 : 0 < ‖β‖ - 1 := sub_pos.mpr hβ1
    have hC0 : 0 ≤ 2 * (1 + ‖β‖) / (‖β‖ - 1) := by positivity
    have hprod := mul_le_mul_of_nonneg_left (le_of_lt (hgap.trans_le hden)) hC0
    have heq : (2 * (1 + ‖β‖) / (‖β‖ - 1)) * ((‖β‖ - 1) / 2) = 1 + ‖β‖ := by
      field_simp [hgap0.ne']
    rw [heq] at hprod
    exact hnum.trans hprod

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι)

/-- Every finite datum admits a uniform boundary bound on a terminal dilation interval. -/
theorem eventually_abs_abelRatio_le :
    ∀ᶠ ρ : ℝ in 𝓝[<] 1, ∀ v : ℂ, ‖v‖ = 1 →
      |abelRatio D ρ v| ≤ ∏ i, boundaryQuotientBound (D.β i) ^ 2 := by
  have h := eventually_all.mpr (fun i : ι => eventually_boundary_factor_le (D.β i))
  filter_upwards [h] with ρ hρ v hv
  rw [abs_of_nonneg (Finset.prod_nonneg fun _ _ => sq_nonneg _)]
  exact Finset.prod_le_prod (fun _ _ => sq_nonneg _) fun i _ =>
    pow_le_pow_left₀ (by positivity) (hρ i v hv) 2

/-- Boundary quotient means tend to one for every finite datum, irrespective of purity. -/
theorem tendsto_circleAverage_abelRatio_unconditional :
    Tendsto (fun ρ : ℝ => Real.circleAverage (abelRatio D ρ) 0 1) (𝓝[<] 1) (𝓝 1) := by
  have hcount : (circleMap 0 1 ⁻¹' {v : ℂ | lPoly D v = 0}).Countable :=
    (countable_lPoly_zeros D).preimage_circleMap 0 one_ne_zero
  have hl : ∀ᵐ θ : ℝ, Tendsto (fun ρ : ℝ => abelRatio D ρ (circleMap 0 1 θ))
      (𝓝[<] 1) (𝓝 1) := by
    filter_upwards [hcount.ae_notMem volume] with θ hθ
    exact tendsto_abelRatio hθ
  have h := tendsto_circleAverage_of_bounded (f := fun _ : ℂ => (1 : ℝ))
    (Eventually.of_forall fun ρ => measurable_abelRatio (D := D) ρ)
    (eventually_abs_abelRatio_le D) hl
  simpa only [Real.circleAverage_const] using h

/-- Quotient convergence and positive inner mass coexist for the golden datum. -/
theorem golden_boundary_limit_and_mollifier_gap :
    Tendsto (fun ρ : ℝ => Real.circleAverage (abelRatio goldenDatum ρ) 0 1)
      (𝓝[<] 1) (𝓝 1) ∧
      1 < Real.goldenRatio ^ 2 ∧
      ∀ (ρ : ℝ) (N : ℕ), Real.goldenRatio ^ 2 ≤ abelBudget goldenDatum ρ N := by
  refine ⟨tendsto_circleAverage_abelRatio_unconditional goldenDatum, ?_,
    sq_goldenRatio_le_abelBudget⟩
  nlinarith [Real.one_lt_goldenRatio]

/-- Near the boundary, no truncation of the golden Euler logarithm approximates the
quotient mean: the gap is uniform in the truncation degree. -/
theorem eventually_golden_budget_sub_quotient_ge :
    ∀ᶠ ρ : ℝ in 𝓝[<] 1, ∀ N : ℕ,
      (Real.goldenRatio ^ 2 - 1) / 2 ≤
        abelBudget goldenDatum ρ N - Real.circleAverage (abelRatio goldenDatum ρ) 0 1 := by
  have hg : 1 < Real.goldenRatio ^ 2 := golden_boundary_limit_and_mollifier_gap.2.1
  have h := (tendsto_circleAverage_abelRatio_unconditional goldenDatum).eventually
    (gt_mem_nhds (show (1 : ℝ) < (Real.goldenRatio ^ 2 + 1) / 2 by linarith))
  filter_upwards [h] with ρ hρ N
  linarith [sq_goldenRatio_le_abelBudget ρ N]

#print axioms eventually_abs_abelRatio_le
#print axioms tendsto_circleAverage_abelRatio_unconditional
#print axioms golden_boundary_limit_and_mollifier_gap
#print axioms eventually_golden_budget_sub_quotient_ge

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
