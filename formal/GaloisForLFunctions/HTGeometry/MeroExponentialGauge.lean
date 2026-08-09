import GaloisForLFunctions.HTGeometry.ExponentialGaugeDifferentialAlgebraic
import GaloisForLFunctions.HTGeometry.UnivMeroFieldInstances
import GaloisForLFunctions.HTGeometry.AnalyticMeroPolynomialEval

/-!
# Exponentials of entire functions in the meromorphic field

The derivation of the meromorphic field of the plane is the ordinary derivative on entire elements.
Consequently the realization of `exp ∘ P` satisfies the homogeneous first-order relation whose
coefficient is the realization of `P′`, so it is differentially algebraic as soon as `P` is, and it
is nowhere zero.

Multiplying by such an exponential therefore changes neither the differentially algebraic phase nor
the hypertranscendental one of any meromorphic element.
-/

open Set Complex Filter
open scoped Differential

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Bottcher
open scoped UnivMeroFieldInstances

/-- **The field derivation is the ordinary derivative on entire elements.** -/
theorem deriv_analyticMeroElement (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (Set.univ : Set ℂ)) :
    (analyticMeroElement f hf)′ = analyticMeroElement (deriv f) hf.deriv := by
  have h1 : differentialJet 1 (analyticMeroElement f hf)
      = analyticMeroElement (deriv f) hf.deriv := by
    rw [differentialJet_analyticMeroElement isOpen_univ isPreconnected_univ Set.univ_nonempty,
      analyticMeroElement, analyticJetElement, analyticFunctionElement]
    congr 1
    apply Subtype.ext
    exact congrArg
      (fun h : ℂ → ℂ => (Filter.Germ.coeRingHom (Filter.principal (Set.univ : Set ℂ)) h))
      (iteratedDeriv_one (f := f))
  rw [← h1, differentialJet_succ, differentialJet_zero]

/-- The exponential of an entire function satisfies the homogeneous first-order relation with
coefficient the derivative of the exponent. -/
theorem deriv_analyticMeroElement_exp (P : ℂ → ℂ) (hP : AnalyticOnNhd ℂ P (Set.univ : Set ℂ)) :
    (analyticMeroElement (fun z => Complex.exp (P z)) hP.cexp)′
      = (analyticMeroElement P hP)′ *
          analyticMeroElement (fun z => Complex.exp (P z)) hP.cexp := by
  rw [deriv_analyticMeroElement, deriv_analyticMeroElement,
    ← analyticMeroElement_mul hP.deriv hP.cexp]
  refine analyticMeroElement_congr _ _ ?_
  funext z
  have hd : DifferentiableAt ℂ P z := (hP z (Set.mem_univ z)).differentiableAt
  rw [deriv_cexp hd]
  ring

/-- The exponential of an entire function is a nonzero element of the field. -/
theorem analyticMeroElement_exp_ne_zero (P : ℂ → ℂ) (hP : AnalyticOnNhd ℂ P (Set.univ : Set ℂ)) :
    analyticMeroElement (fun z => Complex.exp (P z)) hP.cexp ≠ 0 := by
  rw [Ne, analyticMeroElement_eq_zero_iff]
  intro h
  exact Complex.exp_ne_zero (P 0) (h 0 (Set.mem_univ 0))

/-- **The exponential of a differentially algebraic entire exponent is differentially
algebraic.** -/
theorem differentialAlgebraicOver_analyticMeroElement_exp (P : ℂ → ℂ)
    (hP : AnalyticOnNhd ℂ P (Set.univ : Set ℂ))
    (hDA : DifferentialAlgebraicOver (RatFunc ℂ) (analyticMeroElement P hP)) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (analyticMeroElement (fun z => Complex.exp (P z)) hP.cexp) :=
  differentialAlgebraicOver_of_deriv_eq_deriv_mul hDA (deriv_analyticMeroElement_exp P hP)

/-- **An entire exponential gauge preserves the differentially algebraic phase.** -/
theorem differentialAlgebraicOver_mul_analyticMeroElement_exp_iff
    (x : meroField (Set.univ : Set ℂ)) (P : ℂ → ℂ)
    (hP : AnalyticOnNhd ℂ P (Set.univ : Set ℂ))
    (hDA : DifferentialAlgebraicOver (RatFunc ℂ) (analyticMeroElement P hP)) :
    DifferentialAlgebraicOver (RatFunc ℂ)
        (x * analyticMeroElement (fun z => Complex.exp (P z)) hP.cexp)
      ↔ DifferentialAlgebraicOver (RatFunc ℂ) x :=
  differentialAlgebraicOver_mul_iff_of_expGauge hDA (deriv_analyticMeroElement_exp P hP)
    (analyticMeroElement_exp_ne_zero P hP)

/-- **An entire exponential gauge preserves the hypertranscendental phase.** -/
theorem hypertranscendentalOver_mul_analyticMeroElement_exp_iff
    (x : meroField (Set.univ : Set ℂ)) (P : ℂ → ℂ)
    (hP : AnalyticOnNhd ℂ P (Set.univ : Set ℂ))
    (hDA : DifferentialAlgebraicOver (RatFunc ℂ) (analyticMeroElement P hP)) :
    HypertranscendentalOver (RatFunc ℂ)
        (x * analyticMeroElement (fun z => Complex.exp (P z)) hP.cexp)
      ↔ HypertranscendentalOver (RatFunc ℂ) x :=
  hypertranscendentalOver_mul_iff_of_expGauge hDA (deriv_analyticMeroElement_exp P hP)
    (analyticMeroElement_exp_ne_zero P hP)

end GaloisForLFunctions.HTGeometry

end
