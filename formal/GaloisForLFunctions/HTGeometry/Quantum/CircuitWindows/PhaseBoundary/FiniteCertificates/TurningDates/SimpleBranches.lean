import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.BudgetComparisons.AnalyticCoefficients
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.FiniteFactors
import GaloisForLFunctions.HTGeometry.RealAnalyticImplicit
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! # Analytic branches of continuous algebraic time functions outside locally finite dates -/

open Set Filter Topology Polynomial ContinuousLinearMap
open scoped ContDiff
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates.TurningDates
open BudgetComparisons
noncomputable section

def graphEval (p : coefficients[X]) (z : ℝ × ℝ) : ℝ := p.eval₂ (atTime z.1) z.2

private theorem graph_analytic (p : coefficients[X]) (z : ℝ × ℝ) : AnalyticAt ℝ (graphEval p) z := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [graphEval,eval₂_add,Pi.add_def] using hp.add hq
  | monomial i a =>
    have ha := (analytic_coefficient a z.1 (mem_univ _)).comp (analyticAt_fst (𝕜:=ℝ) (p:=z))
    simpa only [graphEval,eval₂_monomial,Pi.mul_def,Pi.pow_def,Function.comp_def] using
      ha.mul ((analyticAt_snd (𝕜:=ℝ) (p:=z)).pow i)

/-- Polynomial tests on the graph remain algebraic even if the graph switches branches. -/
theorem algebraic_graph_test (p : coefficients[X]) {f : ℝ → ℝ} (ha : IsAlgebraic coefficients f) :
    IsAlgebraic coefficients (fun t => graphEval p (t,f t)) := by
  have h : IsAlgebraic coefficients (aeval f p) := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add]; exact hp.add hq
    | monomial i a => rw [aeval_monomial]; exact (isAlgebraic_algebraMap a).mul (ha.pow i)
  exact (show aeval f p=(fun t => graphEval p (t,f t)) from funext (aeval_atTime p f)) ▸ h

/-- A continuous selection of simple roots agrees locally with the analytic implicit branch. -/
private theorem branch_analytic (p : coefficients[X]) {f : ℝ → ℝ} {t : ℝ} (hf : ContinuousAt f t)
    (hz : ∀ᶠ u in 𝓝 t, graphEval p (u,f u)=0) (hd : graphEval p.derivative (t,f t)≠0) :
    AnalyticAt ℝ f t := by
  let z := (t,f t)
  let Φ := graphEval p
  have ha := graph_analytic p z
  have hline : HasDerivAt (fun w : ℝ => (t,w)) (0,1) (f t) :=
    (hasDerivAt_const (f t) t).prodMk (hasDerivAt_id _)
  have hv := ha.differentiableAt.hasFDerivAt.comp_hasDerivAt (f t) hline
  have hy : HasDerivAt (fun w => Φ (t,w)) (graphEval p.derivative z) (f t) := by
    simpa only [Φ,graphEval,Polynomial.derivative_map,Polynomial.eval_map] using (p.map (atTime t)).hasDerivAt (f t)
  have hpartial : (fderiv ℝ Φ z) (0,1)≠0 := fun h => hd ((hv.unique hy).symm.trans h)
  have cdf : ContDiffAt ℝ ω Φ z := ha.contDiffAt
  have hinv : (fderiv ℝ Φ z ∘L (.inr ℝ ℝ ℝ)).IsInvertible :=
    clm_invertible_of_apply_one_ne_real (by simpa using hpartial)
  have hω : (ω : WithTop ℕ∞)≠0 := by decide
  apply (cdf.contDiffAt_implicitFunction hω hinv).analyticAt.congr
  have hgraph : Tendsto (fun u => (u,f u)) (𝓝 t) (𝓝 z) := continuousAt_id.prodMk hf
  filter_upwards [hgraph (cdf.eventually_apply_eq_iff_implicitFunction hω hinv),hz] with u hu hu'
  exact hu.mp (hu'.trans hz.self_of_nhds.symm)

/-- On each compact interval a continuous function algebraic over real analytic
coefficients fails to be analytic at only finitely many dates. At a generic
date a selected simple factor continues to vanish on the whole nearby graph. -/
theorem finite_nonanalytic_dates {f : ℝ → ℝ} (hf : Continuous f) (ha : IsAlgebraic coefficients f)
    (a b : ℝ) : (Icc a b ∩ {t | ¬AnalyticAt ℝ f t}).Finite := by
  classical
  obtain ⟨p,hp,hroot⟩ := ha
  obtain ⟨j,hj⟩ : ∃ j : ℕ, p.coeff j≠0 := by
    by_contra! h
    exact hp (Polynomial.ext (fun j => (h j).trans (coeff_zero j).symm))
  obtain ⟨u,hu⟩ : ∃ u, atTime u (p.coeff j)≠0 := by
    by_contra! h
    exact hj (Subtype.ext (funext h))
  obtain ⟨T,hT⟩ := finite_factors p
  let S (q : coefficients[X]) := {t | graphEval q (t,f t)=0}
  have hf' (c : FactorChoice coefficients) : (Icc a b ∩ frontier (S c.factor)).Finite :=
    finite_zero_frontier (continuous_root_test c.factor hf) (algebraic_graph_test c.factor ⟨p,hp,hroot⟩) a b
  have hz := finite_zeros_of_analyticOnNhd isPreconnected_univ (analytic_coefficient (p.coeff j))
    (mem_univ u) hu isCompact_Icc (subset_univ (Icc a b))
  apply (hz.union (T.finite_toSet.biUnion (fun c _ => hf' c))).subset
  rintro t ⟨ht,hbad⟩
  by_cases hjt : atTime t (p.coeff j)=0
  · exact Or.inl ⟨ht,hjt⟩
  have hp' : p.map (atTime t)≠0 := by
    intro h
    have hn := congrArg (fun q : ℝ[X] => q.coeff j) h
    exact hjt (by simpa only [coeff_map,coeff_zero] using hn)
  have hev := (aeval_atTime p f t).symm.trans (congrFun hroot t)
  obtain ⟨c,hc,_,_,hzero,hd⟩ := hT (atTime t) (f t) hev hp'
  right
  refine mem_iUnion.mpr ⟨c,mem_iUnion.mpr ⟨hc,ht,subset_closure hzero,?_⟩⟩
  intro hi
  exact hbad (branch_analytic c.factor hf.continuousAt (mem_interior_iff_mem_nhds.mp hi) hd)

#print axioms finite_nonanalytic_dates
end
end GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates.TurningDates
