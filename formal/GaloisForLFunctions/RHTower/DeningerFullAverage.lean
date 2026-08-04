import GaloisForLFunctions.RHTower.DeningerFlowInvariance

/-!
# Averaging in every direction

Averaging a closed periodic form over the periods of all coordinates in turn produces a form
invariant under every period flow, hence with constant coefficients, and each averaging step changes
the form only by an exact form with a periodic primitive.  So every closed periodic form of class
`C^1` on the covering space is a constant form plus the exterior derivative of a periodic form.

* `DeningerAveragedData` : a form averaged over a list of directions, with its primitive.
* `deningerAveragedData` : the averaged data, built by recursion over the list.
* `deningerPeriodic_closed_eq_const_add_exact` : the decomposition of a closed periodic form.
-/

namespace RHTower

open Complex ContinuousAlternatingMap

section AveragedData

variable {r n : ℕ}

/-- **A closed periodic form averaged over a list of coordinate directions**, together with the
periodic primitive of its difference from the given form. -/
structure DeningerAveragedData (β : (Fin r → ℂ) → (Fin r → ℂ) [⋀^Fin (n + 1)]→L[ℂ] ℂ)
    (L : List (Fin r)) where
  /-- The averaged form. -/
  form : (Fin r → ℂ) → (Fin r → ℂ) [⋀^Fin (n + 1)]→L[ℂ] ℂ
  /-- The averaged form is differentiable. -/
  diff : Differentiable ℂ form
  /-- The averaged form is continuously differentiable. -/
  fderivCont : Continuous (fderiv ℂ form)
  /-- The averaged form is periodic in every coordinate. -/
  periodic : ∀ (l : Fin r) (w : Fin r → ℂ),
    form (w + (2 * Real.pi * Complex.I) • (Pi.single l (1 : ℂ) : Fin r → ℂ)) = form w
  /-- The averaged form is closed. -/
  closed : ∀ w : Fin r → ℂ, extDeriv form w = 0
  /-- The averaged form is invariant under the flows of the listed directions. -/
  invariant : ∀ j ∈ L, deningerFlowInvariant form j
  /-- The primitive of the difference. -/
  prim : (Fin r → ℂ) → (Fin r → ℂ) [⋀^Fin n]→L[ℂ] ℂ
  /-- The primitive is differentiable. -/
  primDiff : Differentiable ℂ prim
  /-- The primitive is continuously differentiable. -/
  primFderivCont : Continuous (fderiv ℂ prim)
  /-- The primitive is periodic in every coordinate. -/
  primPeriodic : ∀ (l : Fin r) (w : Fin r → ℂ),
    prim (w + (2 * Real.pi * Complex.I) • (Pi.single l (1 : ℂ) : Fin r → ℂ)) = prim w
  /-- The primitive is a primitive of the difference. -/
  primDeriv : ∀ w : Fin r → ℂ, extDeriv prim w = form w - β w

/-- The exterior derivative of a constant form vanishes. -/
theorem deningerExtDeriv_const (A : (Fin r → ℂ) [⋀^Fin n]→L[ℂ] ℂ) (w : Fin r → ℂ) :
    extDeriv (fun _ : Fin r → ℂ => A) w = 0 := by
  rw [extDeriv, fderiv_const_apply]
  show alternatizeUncurryFin (0 : (Fin r → ℂ) →L[ℂ] ((Fin r → ℂ) [⋀^Fin n]→L[ℂ] ℂ)) = 0
  exact _root_.map_zero (alternatizeUncurryFinCLM ℂ (Fin r → ℂ) ℂ (n := n))

/-- **The averaged data, built by recursion over the list of directions.** -/
noncomputable def deningerAveragedData
    {β : (Fin r → ℂ) → (Fin r → ℂ) [⋀^Fin (n + 1)]→L[ℂ] ℂ} (hdiff : Differentiable ℂ β)
    (hcont' : Continuous (fderiv ℂ β))
    (hper : ∀ (l : Fin r) (w : Fin r → ℂ),
      β (w + (2 * Real.pi * Complex.I) • (Pi.single l (1 : ℂ) : Fin r → ℂ)) = β w)
    (hclosed : ∀ w : Fin r → ℂ, extDeriv β w = 0) :
    ∀ L : List (Fin r), DeningerAveragedData β L
  | [] =>
    { form := β
      diff := hdiff
      fderivCont := hcont'
      periodic := hper
      closed := hclosed
      invariant := fun j hj => absurd hj (List.not_mem_nil)
      prim := fun _ => 0
      primDiff := differentiable_const _
      primFderivCont := by
        have hfd : fderiv ℂ (fun _ : Fin r → ℂ => (0 : (Fin r → ℂ) [⋀^Fin n]→L[ℂ] ℂ)) =
            fun _ => 0 := by
          funext w
          exact fderiv_const_apply _
        rw [hfd]
        exact continuous_const
      primPeriodic := fun _ _ => rfl
      primDeriv := fun w => by
        rw [deningerExtDeriv_const, sub_self] }
  | j :: L =>
    let d := deningerAveragedData hdiff hcont' hper hclosed L
    let γ : (Fin r → ℂ) → (Fin r → ℂ) [⋀^Fin n]→L[ℂ] ℂ :=
      fun y => deningerContractCLM
        ((2 * Real.pi * Complex.I) • (Pi.single j (1 : ℂ) : Fin r → ℂ)) (d.form y)
    have hγdiff : Differentiable ℂ γ := fun y =>
      ((deningerContractCLM (n := n)
        ((2 * Real.pi * Complex.I) • (Pi.single j (1 : ℂ) : Fin r → ℂ))).differentiableAt).comp y
        (d.diff y)
    have hγcont : Continuous (fderiv ℂ γ) := by
      have hfun : fderiv ℂ γ = fun y => (deningerContractCLM
          ((2 * Real.pi * Complex.I) • (Pi.single j (1 : ℂ) : Fin r → ℂ))).comp
            (fderiv ℂ d.form y) := by
        funext y
        exact (((deningerContractCLM (n := n)
          ((2 * Real.pi * Complex.I) • (Pi.single j (1 : ℂ) : Fin r → ℂ))).hasFDerivAt).comp y
            (d.diff y).hasFDerivAt).fderiv
      rw [hfun]
      exact isBoundedBilinearMap_comp.continuous.comp (continuous_const.prodMk d.fderivCont)
    { form := deningerAverageOp d.form j
      diff := deningerAverageOp_differentiable d.diff d.fderivCont j
      fderivCont := deningerAverageOp_fderiv_continuous d.diff d.fderivCont j
      periodic := fun l w => deningerAverageOp_periodic j (d.periodic l) w
      closed := fun w => by
        rw [deningerAverageOp_extDeriv d.diff d.fderivCont j w,
          intervalIntegral.integral_congr
            (g := fun _ : ℝ => (0 : (Fin r → ℂ) [⋀^Fin (n + 1 + 1)]→L[ℂ] ℂ))
            (fun s _ => d.closed _)]
        exact intervalIntegral.integral_zero
      invariant := fun i hi => by
        rcases List.mem_cons.1 hi with rfl | hiL
        · exact deningerAverageOp_flowInvariant i (d.periodic i)
        · exact deningerAverageOp_flowInvariant_of j (d.invariant i hiL)
      prim := fun w => d.prim w + deningerWeightHomotopy γ j w
      primDiff := fun w =>
        (d.primDiff w).add ((deningerWeightHomotopy_differentiable hγdiff hγcont j) w)
      primFderivCont := by
        haveI : ContinuousAdd ((Fin r → ℂ) →L[ℂ] ((Fin r → ℂ) [⋀^Fin n]→L[ℂ] ℂ)) := by
          have htag : IsTopologicalAddGroup
              ((Fin r → ℂ) →L[ℂ] ((Fin r → ℂ) [⋀^Fin n]→L[ℂ] ℂ)) := inferInstance
          exact htag.toContinuousAdd
        have hfd : fderiv ℂ (fun w => d.prim w + deningerWeightHomotopy γ j w) =
            fun w => fderiv ℂ d.prim w + fderiv ℂ (deningerWeightHomotopy γ j) w := by
          funext w
          exact fderiv_fun_add (d.primDiff w)
            ((deningerWeightHomotopy_differentiable hγdiff hγcont j) w)
        rw [hfd]
        exact d.primFderivCont.add (deningerWeightHomotopy_fderiv_continuous hγdiff hγcont j)
      primPeriodic := fun l w => by
        show d.prim (w + (2 * Real.pi * Complex.I) • (Pi.single l (1 : ℂ) : Fin r → ℂ)) +
            deningerWeightHomotopy γ j
              (w + (2 * Real.pi * Complex.I) • (Pi.single l (1 : ℂ) : Fin r → ℂ)) =
          d.prim w + deningerWeightHomotopy γ j w
        rw [d.primPeriodic l w]
        congr 1
        refine deningerWeightHomotopy_periodic j (fun y => ?_) w
        show deningerContractCLM _ (d.form (y + (2 * Real.pi * Complex.I) •
          (Pi.single l (1 : ℂ) : Fin r → ℂ))) = deningerContractCLM _ (d.form y)
        rw [d.periodic l y]
      primDeriv := fun w => by
        rw [extDeriv_fun_add (d.primDiff w)
          ((deningerWeightHomotopy_differentiable hγdiff hγcont j) w), d.primDeriv w,
          deningerAverageOp_sub_eq_extDeriv d.diff d.fderivCont d.closed j w]
        abel }

end AveragedData

end RHTower

namespace RHTower

open Complex ContinuousAlternatingMap

section ConstantDecomposition

variable {r n : ℕ}

/-- Scaling an alternating form by minus one is negation. -/
theorem deningerNegOneSmul {m : ℕ} (A : (Fin r → ℂ) [⋀^Fin m]→L[ℂ] ℂ) : (-1 : ℂ) • A = -A := by
  ext v
  show (-1 : ℂ) • (A v) = (-A) v
  rw [show ((-A) v) = -(A v) from rfl, smul_eq_mul, neg_one_mul]

/-- **A closed periodic form of class `C^1` on the covering space is a constant form plus the
exterior derivative of a periodic form of class `C^1`.**  Averaging over every coordinate period in
turn makes the form invariant under all the period flows, hence constant, and each step changes it
by an exact form with a periodic primitive. -/
theorem deningerPeriodic_closed_eq_const_add_exact
    {β : (Fin r → ℂ) → (Fin r → ℂ) [⋀^Fin (n + 1)]→L[ℂ] ℂ} (hdiff : Differentiable ℂ β)
    (hcont' : Continuous (fderiv ℂ β))
    (hper : ∀ (l : Fin r) (w : Fin r → ℂ),
      β (w + (2 * Real.pi * Complex.I) • (Pi.single l (1 : ℂ) : Fin r → ℂ)) = β w)
    (hclosed : ∀ w : Fin r → ℂ, extDeriv β w = 0) :
    ∃ (α : (Fin r → ℂ) [⋀^Fin (n + 1)]→L[ℂ] ℂ)
      (η : (Fin r → ℂ) → (Fin r → ℂ) [⋀^Fin n]→L[ℂ] ℂ),
      Differentiable ℂ η ∧ Continuous (fderiv ℂ η) ∧
      (∀ (l : Fin r) (w : Fin r → ℂ), η (w + (2 * Real.pi * Complex.I) •
        (Pi.single l (1 : ℂ) : Fin r → ℂ)) = η w) ∧
      ∀ w : Fin r → ℂ, β w = α + extDeriv η w := by
  classical
  set d := deningerAveragedData hdiff hcont' hper hclosed (List.finRange r) with hd
  have hinv : ∀ j : Fin r, deningerFlowInvariant d.form j :=
    fun j => d.invariant j (List.mem_finRange j)
  have hconst : ∀ w : Fin r → ℂ, d.form w = d.form 0 :=
    fun w => deningerConst_of_flowInvariant d.diff hinv w 0
  refine ⟨d.form 0, fun w => (-1 : ℂ) • d.prim w, ?_, ?_, ?_, ?_⟩
  · show Differentiable ℂ ((-1 : ℂ) • d.prim)
    exact fun w => (d.primDiff w).const_smul (-1 : ℂ)
  · have hfd : fderiv ℂ (fun w => (-1 : ℂ) • d.prim w) =
        fun w => (-1 : ℂ) • fderiv ℂ d.prim w := by
      funext w
      exact fderiv_const_smul (d.primDiff w) (-1 : ℂ)
    rw [hfd]
    exact d.primFderivCont.const_smul (-1 : ℂ)
  · intro l w
    show (-1 : ℂ) • d.prim (w + (2 * Real.pi * Complex.I) •
      (Pi.single l (1 : ℂ) : Fin r → ℂ)) = (-1 : ℂ) • d.prim w
    rw [d.primPeriodic l w]
  · intro w
    show β w = d.form 0 + extDeriv ((-1 : ℂ) • d.prim) w
    rw [extDeriv_smul, d.primDeriv w, hconst w, deningerNegOneSmul]
    abel

end ConstantDecomposition

end RHTower
