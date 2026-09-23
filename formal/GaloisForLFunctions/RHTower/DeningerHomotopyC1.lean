import GaloisForLFunctions.RHTower.DeningerPoincareKForm

/-!
# The homotopy operator is continuously differentiable

Contracting a form against a vector is continuous linear in the vector, so the integrand of the
homotopy operator is jointly continuous in the base point and the segment parameter.  The derivative
of the homotopy operator is the integral of that integrand, hence continuous.  So the primitive
produced by the Poincaré lemma is again continuously differentiable, and the lemma can be applied to
it a second time — which is what the descent along a covering needs.

* `deningerContractL` : contraction as a continuous linear map in the vector.
* `deningerHomotopyKDeriv_continuous_uncurry` : joint continuity of the integrand.
* `deningerHomotopyOperator_fderiv_continuous` : the homotopy operator is `C^(1 : ℕ)`.
-/

namespace RHTower

open ContinuousAlternatingMap

section ContractLinear

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Contraction as a continuous linear map in the vector.** -/
noncomputable def deningerContractL :
    E →L[ℂ] ((E [⋀^Fin (n + 1)]→L[ℂ] ℂ) →L[ℂ] (E [⋀^Fin n]→L[ℂ] ℂ)) :=
  LinearMap.mkContinuous
    { toFun := fun x : E => deningerContractCLM (n := n) x
      map_add' := fun x y => by
        refine ContinuousLinearMap.ext fun A => ?_
        show ContinuousAlternatingMap.curryLeft A (x + y) =
          ContinuousAlternatingMap.curryLeft A x + ContinuousAlternatingMap.curryLeft A y
        exact map_add _ _ _
      map_smul' := fun c x => by
        refine ContinuousLinearMap.ext fun A => ?_
        show ContinuousAlternatingMap.curryLeft A (c • x) =
          c • ContinuousAlternatingMap.curryLeft A x
        exact map_smul _ _ _ }
    1 (fun x => by
      rw [one_mul]
      exact deningerContractCLM_norm_le x)

@[simp]
theorem deningerContractL_apply (x : E) :
    deningerContractL (n := n) x = deningerContractCLM x := rfl

theorem deningerContractCLM_continuous :
    Continuous fun x : E => deningerContractCLM (n := n) x :=
  (deningerContractL (n := n) (E := E)).continuous

end ContractLinear

section JointContinuity

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **The integrand of the homotopy operator is jointly continuous** in the base point and the
segment parameter. -/
theorem deningerHomotopyKDeriv_continuous_uncurry {ω : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ}
    (hcont : Continuous ω) (hcont' : Continuous (fderiv ℂ ω)) :
    Continuous (Function.uncurry fun (x : E) (t : ℝ) => deningerHomotopyKDeriv ω x t) := by
  have hscale : Continuous fun p : E × ℝ => deningerScale p.2 p.1 := by
    show Continuous fun p : E × ℝ => ((p.2 : ℂ) • p.1)
    fun_prop
  have h1 : Continuous fun p : E × ℝ =>
      ContinuousAlternatingMap.curryLeft (ω (deningerScale p.2 p.1)) :=
    ((ContinuousAlternatingMap.curryLeftLI (𝕜 := ℂ) (E := E) (F := ℂ)
      (n := n)).toContinuousLinearMap).continuous.comp (hcont.comp hscale)
  have h2 : Continuous fun p : E × ℝ => fderiv ℂ ω (deningerScale p.2 p.1) :=
    hcont'.comp hscale
  have h3 : Continuous fun p : E × ℝ => deningerContractCLM (n := n) p.1 :=
    deningerContractCLM_continuous.comp continuous_fst
  have h4 : Continuous fun p : E × ℝ =>
      (deningerContractCLM (n := n) p.1).comp (fderiv ℂ ω (deningerScale p.2 p.1)) :=
    isBoundedBilinearMap_comp.continuous.comp (h3.prodMk h2)
  have h5 : Continuous fun p : E × ℝ => ((p.2 : ℂ) ^ n) := by fun_prop
  have h6 : Continuous fun p : E × ℝ => ((p.2 : ℂ)) := by fun_prop
  exact h5.smul (h1.add (h6.smul h4))

end JointContinuity

section OperatorC1

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- Continuity of a parametric interval integral, with the target abstract so that instance search
succeeds on iterated continuous-linear-map spaces. -/
theorem deningerContinuous_parametric_integral {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {Y : Type*} [TopologicalSpace Y] [FirstCountableTopology Y]
    {f : Y → ℝ → X} (hf : Continuous (Function.uncurry f)) :
    Continuous fun y => ∫ t in (0 : ℝ)..1, f y t :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hf 0 1

/-- **The homotopy operator is continuously differentiable**: its derivative is the integral of the
jointly continuous integrand. -/
theorem deningerHomotopyOperator_fderiv_continuous {ω : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ}
    (hdiff : Differentiable ℂ ω) (hcont' : Continuous (fderiv ℂ ω)) :
    Continuous (fderiv ℂ (deningerHomotopyOperator ω)) := by
  have hfd : fderiv ℂ (deningerHomotopyOperator ω) =
      fun x => ∫ t in (0 : ℝ)..1, deningerHomotopyKDeriv ω x t := by
    funext x
    exact (deningerHomotopyOperator_hasFDerivAt hdiff hcont' x).fderiv
  rw [hfd]
  exact deningerContinuous_parametric_integral
    (deningerHomotopyKDeriv_continuous_uncurry hdiff.continuous hcont')

/-- **The primitive produced by the Poincaré lemma is again continuously differentiable**, so the
lemma can be applied to forms built from it. -/
theorem deningerHomotopyOperator_differentiable {ω : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ}
    (hdiff : Differentiable ℂ ω) (hcont' : Continuous (fderiv ℂ ω)) :
    Differentiable ℂ (deningerHomotopyOperator ω) :=
  fun x => (deningerHomotopyOperator_hasFDerivAt hdiff hcont' x).differentiableAt

end OperatorC1

end RHTower
