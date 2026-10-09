import GaloisForLFunctions.HTGeometry.QKrawtchoukCompanionOperator
import GaloisForLFunctions.HTGeometry.SchattenOneBanach

/-!
# Trace-norm convergence for the balanced companion limit

The geometric coefficient envelope is summable in the genuine Schatten-one
norm, not only in operator norm. Bundling each matrix entry in the existing
Schatten-one Banach space strengthens the balanced companion limit of
arXiv:2609.24149, Section 8, to trace-norm convergence. The ordinary traces
therefore converge as well.
-/

noncomputable section
open Filter RHTower
open scoped Topology

namespace HTGeometry

local notation "H" => lp (fun _ : ℕ => ℂ) 2
local notation "S" => SchattenOneOperator H

private def e (n : ℕ) : H := lp.single 2 n (1 : ℂ)

private theorem e_norm (n : ℕ) : ‖e n‖ = 1 := by
  rw [e, lp.norm_single (by norm_num), norm_one]

private def term (d a : ℝ) (n : ℕ) : S :=
  (d : ℂ) • rankOneSchattenOne (e n) (e n) +
  (a : ℂ) • rankOneSchattenOne (e (n + 1)) (e n) +
  (a : ℂ) • rankOneSchattenOne (e n) (e (n + 1))

private theorem term_norm (d a : ℝ) (n : ℕ) : ‖term d a n‖ ≤ |d| + 2 * |a| := by
  unfold term
  have h := (norm_add_le
    ((d : ℂ) • rankOneSchattenOne (e n) (e n) +
      (a : ℂ) • rankOneSchattenOne (e (n + 1)) (e n))
    ((a : ℂ) • rankOneSchattenOne (e n) (e (n + 1)))).trans
    (add_le_add (norm_add_le _ _) le_rfl)
  simpa only [norm_smul, norm_rankOneSchattenOne, e_norm, mul_one,
    Complex.norm_real, Real.norm_eq_abs, two_mul, add_assoc] using h

private theorem series_summable (d a E : ℕ → ℝ) (hE : Summable E)
    (h : ∀ n, |d n| + 2 * |a n| ≤ E n) :
    Summable (fun n => term (d n) (a n) n) :=
  hE.of_norm_bounded (fun n => (term_norm _ _ n).trans (h n))

private def limit (t u : ℝ) : S :=
  ∑' n, term (alSalamCarlitzDiagonal t u n) (alSalamCarlitzJacobiBond t u n) n

private def finite (t u : ℝ) (K : ℕ) : S :=
  ∑' n, term (qKrawtchoukCompanionBlockDiagonal t u K n)
    (qKrawtchoukCompanionBlockBond t u K n) n

private theorem limit_coe (t u : ℝ) :
    (limit t u : H →L[ℂ] H) = alSalamCarlitzJacobiCLM t u := by
  change schattenOneCoeCLM (∑' n,
    term (alSalamCarlitzDiagonal t u n) (alSalamCarlitzJacobiBond t u n) n) = _
  rw [schattenOneCoeCLM.map_tsum
    (series_summable _ _ _ (summable_alSalamCarlitzJacobiEnvelope t u)
      (alSalamCarlitzJacobi_coeff_bound t u))]
  rfl

private theorem finite_coe (t u : ℝ) (K : ℕ) :
    (finite t u K : H →L[ℂ] H) = qKrawtchoukCompanionJacobiCLM t u K := by
  change schattenOneCoeCLM (∑' n,
    term (qKrawtchoukCompanionBlockDiagonal t u K n)
      (qKrawtchoukCompanionBlockBond t u K n) n) = _
  rw [schattenOneCoeCLM.map_tsum
    (series_summable _ _ _ (summable_alSalamCarlitzJacobiEnvelope t u)
      (qKrawtchoukCompanionBlock_coeff_bound t u K))]
  rfl

private theorem finite_tendsto (t u : ℝ) :
    Tendsto (finite t u) atTop (𝓝 (limit t u)) := by
  apply tendsto_tsum_of_dominated_convergence (summable_alSalamCarlitzJacobiEnvelope t u)
  · intro n
    obtain ⟨hd, ha⟩ := qKrawtchoukCompanionBlock_coeff_tendsto t u n
    have hdc := (Complex.continuous_ofReal.tendsto _).comp hd
    have hac := (Complex.continuous_ofReal.tendsto _).comp ha
    exact ((hdc.smul_const _).add (hac.smul_const _)).add (hac.smul_const _)
  · exact Eventually.of_forall fun K n => (term_norm _ _ n).trans
      (qKrawtchoukCompanionBlock_coeff_bound t u K n)

/-- The concrete limiting companion operator is trace class. -/
theorem alSalamCarlitzJacobiCLM_memSchattenClass_one (t u : ℝ) :
    MemSchattenClass 1 (alSalamCarlitzJacobiCLM t u) := by
  rw [← limit_coe]
  exact (limit t u).property

/-- Every concrete finite companion operator is trace class on the same sequence space. -/
theorem qKrawtchoukCompanionJacobiCLM_memSchattenClass_one (t u : ℝ) (K : ℕ) :
    MemSchattenClass 1 (qKrawtchoukCompanionJacobiCLM t u K) := by
  rw [← finite_coe]
  exact (finite t u K).property

/-- The balanced companion operators converge in the genuine trace norm. -/
theorem qKrawtchoukCompanionJacobiCLM_traceNorm_tendsto (t u : ℝ) :
    Tendsto (fun K => traceNorm H
      (qKrawtchoukCompanionJacobiCLM t u K - alSalamCarlitzJacobiCLM t u)) atTop (𝓝 0) := by
  have h := tendsto_iff_norm_sub_tendsto_zero.mp (finite_tendsto t u)
  simpa only [SchattenOneOperator.norm_def, SchattenOneOperator.coe_sub,
    finite_coe, limit_coe] using h

/-- The ordinary traces of the actual finite matrices converge to the limiting trace. -/
theorem qKrawtchoukCompanionJacobiCLM_opTrace_tendsto (t u : ℝ) :
    Tendsto (fun K => ContinuousLinearMap.opTrace (qKrawtchoukCompanionJacobiCLM t u K))
      atTop (𝓝 (ContinuousLinearMap.opTrace (alSalamCarlitzJacobiCLM t u))) :=
  opTrace_tendsto_of_traceNorm_tendsto
    (qKrawtchoukCompanionJacobiCLM_memSchattenClass_one t u)
    (fun K => (qKrawtchoukCompanionJacobiCLM_memSchattenClass_one t u K).one_sub
      (alSalamCarlitzJacobiCLM_memSchattenClass_one t u))
    (qKrawtchoukCompanionJacobiCLM_traceNorm_tendsto t u)

end HTGeometry
