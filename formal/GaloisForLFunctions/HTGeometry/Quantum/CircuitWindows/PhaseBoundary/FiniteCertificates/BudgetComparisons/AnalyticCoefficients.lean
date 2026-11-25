import GaloisForLFunctions.HTGeometry.RealAnalyticZeroFiniteness
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.Algebra.Polynomial.Div

/-! # Level boundaries of continuous functions algebraic over real analytic functions -/

open Set Filter Topology Polynomial
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates.BudgetComparisons
noncomputable section

/-- The coefficient domain of globally real analytic functions of physical time. -/
def coefficients : Subring (ℝ → ℝ) where
  carrier := {f | AnalyticOnNhd ℝ f univ}
  zero_mem' := analyticOnNhd_const
  one_mem' := analyticOnNhd_const
  add_mem' := fun hf hg => hf.add hg
  mul_mem' := fun hf hg => hf.mul hg
  neg_mem' := fun hf => hf.neg

theorem analytic_coefficient (a : coefficients) : AnalyticOnNhd ℝ (a : ℝ → ℝ) univ := a.property

instance : NoZeroDivisors coefficients := by
  refine ⟨fun {a b} hab => ?_⟩
  by_cases ha : a=0
  · exact Or.inl ha
  right
  have ex : ∃ t, (a:ℝ → ℝ) t≠0 := by
    by_contra! h
    exact ha (Subtype.ext (funext h))
  obtain ⟨t,ht⟩ := ex
  have near := ((analytic_coefficient a) t (mem_univ _)).continuousAt.eventually_ne ht
  have hzero : (b:ℝ → ℝ) =ᶠ[𝓝 t] 0 := by
    filter_upwards [near] with u hu
    have h : (a:ℝ → ℝ) u * (b:ℝ → ℝ) u=0 :=
      congrArg (fun w : coefficients => (w:ℝ → ℝ) u) hab
    exact (mul_eq_zero.mp h).resolve_left hu
  have he := (analytic_coefficient b).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (mem_univ t) hzero
  exact Subtype.ext (funext fun u => he (mem_univ u))

instance : IsDomain coefficients := NoZeroDivisors.to_isDomain _

def atTime (t : ℝ) : coefficients →+* ℝ :=
  (Pi.evalRingHom (fun _ : ℝ => ℝ) t).comp coefficients.subtype

theorem continuous_coefficient (a : coefficients) : Continuous (fun t => atTime t a) :=
  continuous_iff_continuousAt.mpr fun t => (analytic_coefficient a t (mem_univ _)).continuousAt

/-- Evaluating a polynomial of functions commutes with evaluation at a time. -/
theorem aeval_atTime (p : coefficients[X]) (f : ℝ → ℝ) (t : ℝ) :
    (aeval f p) t=p.eval₂ (atTime t) (f t) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add,Pi.add_apply,eval₂_add,hp,hq]
  | monomial i a => simp only [aeval_monomial,eval₂_monomial,Pi.mul_apply,Pi.pow_apply]; rfl

theorem continuous_root_test (p : coefficients[X]) {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (fun t => p.eval₂ (atTime t) (f t)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [eval₂_add,Pi.add_def] using hp.add hq
  | monomial i a => simpa only [eval₂_monomial,Pi.mul_def,Pi.pow_def] using (continuous_coefficient a).mul (hf.pow i)

/-- Removing the maximal height factor leaves a nonzero constant coefficient
and an equation at every date where the function is nonzero. -/
theorem deflated_equation {f : ℝ → ℝ} (ha : IsAlgebraic coefficients f) :
    ∃ Q : coefficients[X], Q.eval 0≠0 ∧ ∀ t, f t≠0 → Q.eval₂ (atTime t) (f t)=0 := by
  obtain ⟨p,hp,hroot⟩ := ha
  let Q := p /ₘ (Polynomial.X-C (0:coefficients))^p.rootMultiplicity 0
  let c := Q.eval 0
  have hc : c≠0 := eval_divByMonic_pow_rootMultiplicity_ne_zero 0 hp
  have hz (t : ℝ) (ht : f t≠0) : Q.eval₂ (atTime t) (f t)=0 := by
    have h := congrArg (eval₂RingHom (atTime t) (f t)) (pow_mul_divByMonic_rootMultiplicity_eq p 0)
    have hr : p.eval₂ (atTime t) (f t)=0 := (aeval_atTime p f t).symm.trans (congrFun hroot t)
    change ((Polynomial.X-C (0:coefficients))^p.rootMultiplicity 0*Q).eval₂ (atTime t) (f t)=_ at h
    rw [eval₂_mul,eval₂_pow,eval₂_sub,eval₂_X,eval₂_C,map_zero,sub_zero] at h
    exact (mul_eq_zero.mp (h.trans hr)).resolve_left (pow_ne_zero _ ht)
  exact ⟨Q,hc,hz⟩

/-- A polynomial relation for a continuous function yields a single nontrivial
analytic equation on the boundary of its zero set. Strip the identically
vanishing height factor before specializing to height zero. -/
theorem finite_zero_frontier {f : ℝ → ℝ} (hf : Continuous f) (ha : IsAlgebraic coefficients f)
    (a b : ℝ) : (Icc a b ∩ frontier {t | f t=0}).Finite := by
  obtain ⟨Q,hc,hz⟩ := deflated_equation ha
  let c := Q.eval 0
  have ex : ∃ u, atTime u c≠0 := by
    by_contra! hn
    exact hc (Subtype.ext (funext hn))
  obtain ⟨u,hu⟩ := ex
  have hsub : closure {t | f t≠0} ⊆ {t | Q.eval₂ (atTime t) (f t)=0} :=
    closure_minimal (fun t ht => hz t ht) (isClosed_eq (continuous_root_test Q hf) continuous_const)
  apply (finite_zeros_of_analyticOnNhd isPreconnected_univ (analytic_coefficient c) (mem_univ u) hu
    isCompact_Icc (subset_univ _)).subset
  rintro t ⟨ht,hfr⟩
  have he : f t=0 := frontier_subset_iff_isClosed.mpr (isClosed_eq hf continuous_const) hfr
  have hfront : t∈closure {t | f t≠0} := by
    rw [frontier_eq_closure_inter_closure] at hfr
    exact hfr.2
  have h := hsub hfront
  change Q.eval₂ (atTime t) (f t)=0 at h
  rw [he] at h
  have hspec : Q.eval₂ (atTime t) (atTime t 0)=atTime t c := eval₂_at_apply ..
  rw [map_zero] at hspec
  exact ⟨ht,hspec.symm.trans h⟩

#print axioms finite_zero_frontier
end
end GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates.BudgetComparisons
