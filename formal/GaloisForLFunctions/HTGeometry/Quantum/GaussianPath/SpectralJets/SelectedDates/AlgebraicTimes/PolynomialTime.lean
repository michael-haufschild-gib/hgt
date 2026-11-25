import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicTimes.RootProjection
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.LiftCertificate
import Mathlib.Data.Finsupp.Encodable

/-! # Simple polynomial equations for times algebraic over the couplings -/

open Polynomial Set Filter MeasureTheory Topology
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicTimes
open PhaseBoundary
noncomputable section

abbrev Parameters (m : ℕ) := MvPolynomial (Fin m) ℚ

def parameterEval {m : ℕ} (x : Fin m → ℝ) : Parameters m →+* ℝ :=
  MvPolynomial.eval₂Hom (Rat.castHom ℝ) x

/-- The field of rational functions evaluated in the actual couplings. -/
abbrev parameterField {m : ℕ} (x : Fin m → ℝ) := valueField (parameterEval x)

def timeValue {m : ℕ} (q : (Parameters m)[X]) (u : (Fin m → ℝ) × ℝ) : ℝ :=
  q.eval₂ (parameterEval u.1) u.2

theorem analytic_parameterEval {m : ℕ} (p : Parameters m) (x : Fin m → ℝ) :
    AnalyticAt ℝ (fun y => parameterEval y p) x := by
  induction p using MvPolynomial.induction_on with
  | C r => simp only [parameterEval,MvPolynomial.eval₂Hom_C]; exact analyticAt_const
  | add p q hp hq => simpa only [map_add,Pi.add_def] using hp.add hq
  | mul_X p i hp =>
    have hi : AnalyticAt ℝ (fun y : Fin m → ℝ => y i) x := (ContinuousLinearMap.proj i).analyticAt x
    simpa only [map_mul,parameterEval,MvPolynomial.eval₂Hom_X',Pi.mul_def] using hp.mul hi

theorem analytic_timeValue {m : ℕ} (p : (Parameters m)[X]) (u : (Fin m → ℝ) × ℝ) :
    AnalyticAt ℝ (timeValue p) u := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [timeValue,eval₂_add,Pi.add_def] using hp.add hq
  | monomial n a =>
    simpa only [timeValue,eval₂_monomial,Pi.mul_def,Pi.pow_def,Function.comp_def] using
      ((analytic_parameterEval a u.1).comp analyticAt_fst).mul (analyticAt_snd.pow n)

theorem timeValue_vertical {m : ℕ} (p : (Parameters m)[X]) (x : Fin m → ℝ) (t : ℝ) :
    fderiv ℝ (timeValue p) (x,t) (0,1)=timeValue p.derivative (x,t) := by
  have hι : HasFDerivAt (fun u : ℝ => (x,u))
      ((0 : ℝ →L[ℝ] (Fin m → ℝ)).prod (ContinuousLinearMap.id ℝ ℝ)) t :=
    (hasFDerivAt_const x t).prodMk (hasFDerivAt_id t)
  have hc := (analytic_timeValue p (x,t)).differentiableAt.hasFDerivAt.comp t hι
  have hp : HasDerivAt (fun u => timeValue p (x,u)) (timeValue p.derivative (x,t)) t := by
    have he : (fun u => timeValue p (x,u))=fun u => (p.map (parameterEval x)).eval u :=
      funext fun u => (Polynomial.eval_map ..).symm
    rw [he]
    simpa only [timeValue,Polynomial.derivative_map,eval_map] using Polynomial.hasDerivAt (p.map (parameterEval x)) t
  have hu := hc.unique hp.hasFDerivAt
  simpa using ContinuousLinearMap.ext_iff.mp hu 1

/-- Separability and clearing denominators give a simple root at the
given coupling vector even if another time polynomial has a multiple root. -/
theorem exists_simple_time_equation {m : ℕ} (x : Fin m → ℝ) {t : ℝ} (ht : IsAlgebraic (parameterField x) t) :
    ∃ q : (Parameters m)[X], timeValue q (x,t)=0 ∧ timeValue q.derivative (x,t)≠0 := by
  let φ := parameterEval x
  let K := valueField φ
  let M := minpoly K t
  have hi : IsIntegral K t := ht.isIntegral
  obtain ⟨d,hd,q,hq⟩ := clear_polynomial φ M
  have eval (p : (Parameters m)[X]) : aeval t (p.map (specialize φ))=timeValue p (x,t) := by
    rw [aeval_def,eval₂_map]; rfl
  refine ⟨q,?_,?_⟩
  · rw [←eval,hq,map_mul,minpoly.aeval,mul_zero]
  · rw [←eval,←Polynomial.derivative_map,hq,Polynomial.derivative_C_mul,map_mul,aeval_C]
    exact mul_ne_zero hd ((minpoly.irreducible hi).separable.aeval_derivative_ne_zero (minpoly.aeval K t))

theorem parameterEval_rat {m : ℕ} (x : Fin m → ℚ) :
    parameterEval (fun i => (x i:ℝ))=(Rat.castHom ℝ).comp (MvPolynomial.eval x) := by
  apply MvPolynomial.ringHom_ext
  · intro r; simp [parameterEval]
  · intro i; simp [parameterEval]

/-- Over rational parameters a simple time root is a real algebraic number. -/
theorem rational_specialization {m : ℕ} (x : Fin m → ℚ) (t : ℝ) (q : (Parameters m)[X])
    (hz : timeValue q (fun i => (x i:ℝ),t)=0) (hd : timeValue q.derivative (fun i => (x i:ℝ),t)≠0) :
    IsAlgebraic ℚ t := by
  let p := q.map (MvPolynomial.eval x)
  have eval (Q : (Parameters m)[X]) : aeval t (Q.map (MvPolynomial.eval x))=
      timeValue Q (fun i => (x i:ℝ),t) := by
    rw [aeval_def,eval₂_map,timeValue,parameterEval_rat]; rfl
  refine ⟨p,?_,(eval q).trans hz⟩
  intro hp
  apply hd
  rw [←eval,←Polynomial.derivative_map,show q.map (MvPolynomial.eval x)=0 from hp,derivative_zero,map_zero]

#print axioms exists_simple_time_equation
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicTimes
