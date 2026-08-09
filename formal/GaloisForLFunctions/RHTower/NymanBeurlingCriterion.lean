import GaloisForLFunctions.RHTower.BaezDuarteL2Carrier
import GaloisForLFunctions.RHTower.ZetaXiZeroCorrespondence

/-!
# The Nyman--Beurling criterion, sufficient direction

`BaezDuarteL2Carrier` builds the carrier `L²((1,∞), du)`, the Báez-Duarte generators, the target, and the
bounded Mellin point evaluations, and shows that at a zero `ρ` of `ζ` with `½ < Re ρ < 1` the target is not
in the closed span of the generators.  The remaining step is bookkeeping about where a counterexample to
the Riemann hypothesis lives, and the corpus already has it: `rh_iff_xi_ne_zero_right` says RH is exactly
the nonvanishing of `Ξ` on `Re s > ½`, `xi_zero_re_mem_open_unit` confines a `Ξ` zero to the strip, and
`xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial` transfers it to `ζ`.

Assembling these gives the direction of the criterion that an actual proof of the Riemann hypothesis would
consume:

> **If the constant function `1_{(0,1]}` lies in the closed span of the Báez-Duarte generators, the
> Riemann hypothesis holds** (`riemannHypothesis_of_bdTarget_mem_closedSpan`).

together with its quantitative contrapositive: if RH fails, the Báez-Duarte distances are bounded below by
an explicit positive constant, uniformly in the approximant
(`exists_pos_bdDist_floor_of_not_riemannHypothesis`).

Only the *easy* analytic direction of Nyman--Beurling is used, so everything here is unconditional.  The
converse implication — RH forces the distances to zero — is not proved here and is not needed for the
criterion to be usable in this direction.
-/

open MeasureTheory Set Complex
open scoped InnerProductSpace

noncomputable section

namespace RHTower

/-- **Where a counterexample lives.**  Failure of the Riemann hypothesis produces a genuine zero of `ζ`
strictly inside the right half of the critical strip. -/
theorem exists_zetaZero_re_gt_half_of_not_riemannHypothesis (hRH : ¬ RiemannHypothesis) :
    ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 1 / 2 < ρ.re ∧ ρ.re < 1 := by
  have hnotfree : ¬ ∀ s ∈ rightHalf, xi s ≠ 0 := by
    intro hfree
    exact hRH (rh_iff_xi_ne_zero_right.mpr hfree)
  push Not at hnotfree
  obtain ⟨s, hs, hzero⟩ := hnotfree
  refine ⟨s, ?_, mem_rightHalf.mp hs, (xi_zero_re_mem_open_unit hzero).2⟩
  exact (xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.mp hzero).1

/-- **The Nyman--Beurling criterion, sufficient direction.**  If the target `1_{(0,1]}` is in the closed
span of the Báez-Duarte generators, the Riemann hypothesis holds. -/
theorem riemannHypothesis_of_bdTarget_mem_closedSpan
    (h : bdTarget ∈
      (Submodule.span ℂ (Set.range (fun i : bdIndex => bdGen i.1))).topologicalClosure) :
    RiemannHypothesis := by
  by_contra hRH
  obtain ⟨ρ, hzero, hρ, hρ1⟩ := exists_zetaZero_re_gt_half_of_not_riemannHypothesis hRH
  exact bdTarget_notMem_closedSpan_of_zero hρ hρ1 hzero h

/-- **The quantitative contrapositive.**  If the Riemann hypothesis fails there is a positive constant
below every Báez-Duarte distance — the approximation cannot merely be slow, it is obstructed. -/
theorem exists_pos_bdDist_floor_of_not_riemannHypothesis (hRH : ¬ RiemannHypothesis) :
    ∃ c : ℝ, 0 < c ∧ ∀ G ∈
      (Submodule.span ℂ (Set.range (fun i : bdIndex => bdGen i.1))).topologicalClosure,
        c ≤ ‖bdTarget - G‖ := by
  obtain ⟨ρ, hzero, hρ, hρ1⟩ := exists_zetaZero_re_gt_half_of_not_riemannHypothesis hRH
  have hρ0 : ρ ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hρ
    linarith
  refine ⟨Real.sqrt (2 * ρ.re - 1) / ‖ρ‖, ?_, fun G hG =>
    bdTarget_dist_floor_of_mem_closedSpan hρ hρ1 hzero hG⟩
  have h1 : (0 : ℝ) < 2 * ρ.re - 1 := by linarith
  exact div_pos (Real.sqrt_pos.mpr h1) (norm_pos_iff.mpr hρ0)

/-! ## The criterion for an arbitrary subfamily, and the discrete Báez-Duarte system -/

/-- **The criterion for an arbitrary subfamily of generators.**  Since shrinking the family shrinks the
span, this is stronger than the full-family statement: approximating the target by combinations of *any*
set of dilations `θ ∈ (0,1]` already forces the Riemann hypothesis. -/
theorem riemannHypothesis_of_bdTarget_mem_closedSpan_family {I : Type*} (θ : I → ℝ)
    (hθ : ∀ i, 0 < θ i ∧ θ i ≤ 1)
    (h : bdTarget ∈
      (Submodule.span ℂ (Set.range (fun i : I => bdGen (θ i)))).topologicalClosure) :
    RiemannHypothesis := by
  by_contra hRH
  obtain ⟨ρ, hzero, hρ, hρ1⟩ := exists_zetaZero_re_gt_half_of_not_riemannHypothesis hRH
  exact bdTarget_notMem_closedSpan_family_of_zero θ hθ hρ hρ1 hzero h

/-- The Báez-Duarte dilations `θ = 1/(n+1)`: the discrete system the literature works with. -/
def bdDiscrete (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem bdDiscrete_mem (n : ℕ) : 0 < bdDiscrete n ∧ bdDiscrete n ≤ 1 := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  simp only [bdDiscrete]
  refine ⟨by positivity, ?_⟩
  rw [div_le_one hpos]
  simp only [le_add_iff_nonneg_left]
  positivity

/-- **The discrete Báez-Duarte criterion.**  If the target is in the closed span of the countable family
`({u/n} − {u}/n)/u`, the Riemann hypothesis holds. -/
theorem riemannHypothesis_of_bdTarget_mem_closedSpan_discrete
    (h : bdTarget ∈
      (Submodule.span ℂ (Set.range (fun n : ℕ => bdGen (bdDiscrete n)))).topologicalClosure) :
    RiemannHypothesis :=
  riemannHypothesis_of_bdTarget_mem_closedSpan_family bdDiscrete bdDiscrete_mem h

/-- The quantitative obstruction for the discrete system. -/
theorem exists_pos_bdDist_floor_discrete_of_not_riemannHypothesis (hRH : ¬ RiemannHypothesis) :
    ∃ c : ℝ, 0 < c ∧ ∀ G ∈
      (Submodule.span ℂ (Set.range (fun n : ℕ => bdGen (bdDiscrete n)))).topologicalClosure,
        c ≤ ‖bdTarget - G‖ := by
  obtain ⟨ρ, hzero, hρ, hρ1⟩ := exists_zetaZero_re_gt_half_of_not_riemannHypothesis hRH
  have hρ0 : ρ ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hρ
    linarith
  refine ⟨Real.sqrt (2 * ρ.re - 1) / ‖ρ‖, ?_, fun G hG =>
    bdTarget_dist_floor_of_mem_closedSpan_family bdDiscrete bdDiscrete_mem hρ hρ1 hzero hG⟩
  have h1 : (0 : ℝ) < 2 * ρ.re - 1 := by linarith
  exact div_pos (Real.sqrt_pos.mpr h1) (norm_pos_iff.mpr hρ0)

/-- The criterion in equivalence form on the closed-span side: closed-span membership of the target is
*sufficient* for the Riemann hypothesis, and its failure is quantitatively obstructed. -/
theorem bdTarget_mem_closedSpan_imp_and_floor :
    (bdTarget ∈
        (Submodule.span ℂ (Set.range (fun i : bdIndex => bdGen i.1))).topologicalClosure →
      RiemannHypothesis) ∧
      (¬ RiemannHypothesis → ∃ c : ℝ, 0 < c ∧ ∀ G ∈
        (Submodule.span ℂ (Set.range (fun i : bdIndex => bdGen i.1))).topologicalClosure,
          c ≤ ‖bdTarget - G‖) :=
  ⟨riemannHypothesis_of_bdTarget_mem_closedSpan, exists_pos_bdDist_floor_of_not_riemannHypothesis⟩

end RHTower

end
