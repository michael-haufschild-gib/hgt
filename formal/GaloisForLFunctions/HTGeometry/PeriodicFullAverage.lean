import GaloisForLFunctions.HTGeometry.PeriodicConstantForm

/-!
# Averaging in every direction

Averaging a closed periodic form over the periods of all coordinates in turn produces a form
invariant under every period flow, hence with constant coefficients, and each averaging step changes
the form only by an exact form with a periodic primitive.  So every closed periodic form of class
`C^1` on a coordinate space is a constant form plus the exterior derivative of a periodic form, and
by the vanishing of constant forms with periodic primitives the constant form is unique.

* `PeriodicAveragedData` : a form averaged over a list of directions, with its primitive.
* `periodicAveragedData` : the averaged data, built by recursion over the list.
* `periodic_closed_eq_const_add_exact` : the decomposition of a closed periodic form.
* `periodic_const_add_exact_unique` : the constant form of the decomposition is unique.
-/

namespace GaloisForLFunctions.HTGeometry

open ContinuousAlternatingMap

section AveragedData

variable {𝕜 : Type*} [RCLike 𝕜] {r n : ℕ}

/-- **A closed periodic form averaged over a list of coordinate directions**, together with the
periodic primitive of its difference from the given form. -/
structure PeriodicAveragedData (p : 𝕜) (β : (Fin r → 𝕜) → (Fin r → 𝕜) [⋀^Fin (n + 1)]→L[𝕜] 𝕜)
    (L : List (Fin r)) where
  /-- The averaged form. -/
  form : (Fin r → 𝕜) → (Fin r → 𝕜) [⋀^Fin (n + 1)]→L[𝕜] 𝕜
  /-- The averaged form is differentiable. -/
  diff : Differentiable 𝕜 form
  /-- The averaged form is continuously differentiable. -/
  fderivCont : Continuous (fderiv 𝕜 form)
  /-- The averaged form is periodic in every coordinate. -/
  periodic : ∀ (l : Fin r) (w : Fin r → 𝕜),
    form (w + p • (Pi.single l (1 : 𝕜) : Fin r → 𝕜)) = form w
  /-- The averaged form is closed. -/
  closed : ∀ w : Fin r → 𝕜, extDeriv form w = 0
  /-- The averaged form is invariant under the flows of the listed directions. -/
  invariant : ∀ j ∈ L, FlowInvariant p form j
  /-- The primitive of the difference. -/
  prim : (Fin r → 𝕜) → (Fin r → 𝕜) [⋀^Fin n]→L[𝕜] 𝕜
  /-- The primitive is differentiable. -/
  primDiff : Differentiable 𝕜 prim
  /-- The primitive is continuously differentiable. -/
  primFderivCont : Continuous (fderiv 𝕜 prim)
  /-- The primitive is periodic in every coordinate. -/
  primPeriodic : ∀ (l : Fin r) (w : Fin r → 𝕜),
    prim (w + p • (Pi.single l (1 : 𝕜) : Fin r → 𝕜)) = prim w
  /-- The primitive is a primitive of the difference. -/
  primDeriv : ∀ w : Fin r → 𝕜, extDeriv prim w = form w - β w

/-- The exterior derivative of a constant form vanishes. -/
theorem extDeriv_const (A : (Fin r → 𝕜) [⋀^Fin n]→L[𝕜] 𝕜) (w : Fin r → 𝕜) :
    extDeriv (fun _ : Fin r → 𝕜 => A) w = 0 := by
  rw [extDeriv, fderiv_const_apply]
  show alternatizeUncurryFin (0 : (Fin r → 𝕜) →L[𝕜] ((Fin r → 𝕜) [⋀^Fin n]→L[𝕜] 𝕜)) = 0
  exact _root_.map_zero (alternatizeUncurryFinCLM 𝕜 (Fin r → 𝕜) 𝕜 (n := n))

/-- **The averaged data, built by recursion over the list of directions.** -/
noncomputable def periodicAveragedData {p : 𝕜}
    {β : (Fin r → 𝕜) → (Fin r → 𝕜) [⋀^Fin (n + 1)]→L[𝕜] 𝕜} (hdiff : Differentiable 𝕜 β)
    (hcont' : Continuous (fderiv 𝕜 β))
    (hper : ∀ (l : Fin r) (w : Fin r → 𝕜),
      β (w + p • (Pi.single l (1 : 𝕜) : Fin r → 𝕜)) = β w)
    (hclosed : ∀ w : Fin r → 𝕜, extDeriv β w = 0) :
    ∀ L : List (Fin r), PeriodicAveragedData p β L
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
        have hfd : fderiv 𝕜 (fun _ : Fin r → 𝕜 => (0 : (Fin r → 𝕜) [⋀^Fin n]→L[𝕜] 𝕜)) =
            fun _ => 0 := by
          funext w
          exact fderiv_const_apply _
        rw [hfd]
        exact continuous_const
      primPeriodic := fun _ _ => rfl
      primDeriv := fun w => by
        rw [extDeriv_const, sub_self] }
  | j :: L =>
    let d := periodicAveragedData hdiff hcont' hper hclosed L
    let γ : (Fin r → 𝕜) → (Fin r → 𝕜) [⋀^Fin n]→L[𝕜] 𝕜 :=
      fun y => contractCLM (𝕜 := 𝕜) (p • (Pi.single j (1 : 𝕜) : Fin r → 𝕜)) (d.form y)
    have hγdiff : Differentiable 𝕜 γ := fun y =>
      ((contractCLM (𝕜 := 𝕜) (n := n)
        (p • (Pi.single j (1 : 𝕜) : Fin r → 𝕜))).differentiableAt).comp y (d.diff y)
    have hγcont : Continuous (fderiv 𝕜 γ) := by
      have hfun : fderiv 𝕜 γ = fun y => (contractCLM (𝕜 := 𝕜)
          (p • (Pi.single j (1 : 𝕜) : Fin r → 𝕜))).comp (fderiv 𝕜 d.form y) := by
        funext y
        exact (((contractCLM (𝕜 := 𝕜) (n := n)
          (p • (Pi.single j (1 : 𝕜) : Fin r → 𝕜))).hasFDerivAt).comp y (d.diff y).hasFDerivAt).fderiv
      rw [hfun]
      exact isBoundedBilinearMap_comp.continuous.comp (continuous_const.prodMk d.fderivCont)
    { form := averageOp p d.form j
      diff := averageOp_differentiable d.diff d.fderivCont j
      fderivCont := averageOp_fderiv_continuous d.diff d.fderivCont j
      periodic := fun l w => averageOp_periodic j (d.periodic l) w
      closed := fun w => by
        rw [averageOp_extDeriv d.diff d.fderivCont j w,
          intervalIntegral.integral_congr
            (g := fun _ : ℝ => (0 : (Fin r → 𝕜) [⋀^Fin (n + 1 + 1)]→L[𝕜] 𝕜))
            (fun s _ => d.closed _)]
        exact intervalIntegral.integral_zero
      invariant := fun i hi => by
        rcases List.mem_cons.1 hi with rfl | hiL
        · exact averageOp_flowInvariant i (d.periodic i)
        · exact averageOp_flowInvariant_of j (d.invariant i hiL)
      prim := fun w => d.prim w + weightHomotopy p γ j w
      primDiff := fun w =>
        (d.primDiff w).add ((weightHomotopy_differentiable hγdiff hγcont j) w)
      primFderivCont := by
        haveI : ContinuousAdd ((Fin r → 𝕜) →L[𝕜] ((Fin r → 𝕜) [⋀^Fin n]→L[𝕜] 𝕜)) := by
          have htag : IsTopologicalAddGroup
              ((Fin r → 𝕜) →L[𝕜] ((Fin r → 𝕜) [⋀^Fin n]→L[𝕜] 𝕜)) := inferInstance
          exact htag.toContinuousAdd
        have hfd : fderiv 𝕜 (fun w => d.prim w + weightHomotopy p γ j w) =
            fun w => fderiv 𝕜 d.prim w + fderiv 𝕜 (weightHomotopy p γ j) w := by
          funext w
          exact fderiv_fun_add (d.primDiff w)
            ((weightHomotopy_differentiable hγdiff hγcont j) w)
        rw [hfd]
        exact d.primFderivCont.add (weightHomotopy_fderiv_continuous hγdiff hγcont j)
      primPeriodic := fun l w => by
        show d.prim (w + p • (Pi.single l (1 : 𝕜) : Fin r → 𝕜)) +
            weightHomotopy p γ j (w + p • (Pi.single l (1 : 𝕜) : Fin r → 𝕜)) =
          d.prim w + weightHomotopy p γ j w
        rw [d.primPeriodic l w]
        congr 1
        refine weightHomotopy_periodic j (fun y => ?_) w
        show contractCLM (𝕜 := 𝕜) _ (d.form (y + p • (Pi.single l (1 : 𝕜) : Fin r → 𝕜))) =
          contractCLM (𝕜 := 𝕜) _ (d.form y)
        rw [d.periodic l y]
      primDeriv := fun w => by
        rw [extDeriv_fun_add (d.primDiff w)
          ((weightHomotopy_differentiable hγdiff hγcont j) w), d.primDeriv w,
          averageOp_sub_eq_extDeriv d.diff d.fderivCont d.closed j w]
        abel }

end AveragedData

section ConstantDecomposition

variable {𝕜 : Type*} [RCLike 𝕜] {r n : ℕ}

/-- Scaling an alternating form by minus one is negation. -/
theorem negOne_smul_alternating {m : ℕ} (A : (Fin r → 𝕜) [⋀^Fin m]→L[𝕜] 𝕜) :
    (-1 : 𝕜) • A = -A := by
  ext v
  show (-1 : 𝕜) • (A v) = (-A) v
  rw [show ((-A) v) = -(A v) from rfl, smul_eq_mul, neg_one_mul]

/-- **A closed periodic form of class `C^1` on a coordinate space is a constant form plus the
exterior derivative of a periodic form of class `C^1`.**  Averaging over every coordinate period in
turn makes the form invariant under all the period flows, hence constant, and each step changes it
by an exact form with a periodic primitive. -/
theorem periodic_closed_eq_const_add_exact {p : 𝕜} (hp : p ≠ 0)
    {β : (Fin r → 𝕜) → (Fin r → 𝕜) [⋀^Fin (n + 1)]→L[𝕜] 𝕜} (hdiff : Differentiable 𝕜 β)
    (hcont' : Continuous (fderiv 𝕜 β))
    (hper : ∀ (l : Fin r) (w : Fin r → 𝕜),
      β (w + p • (Pi.single l (1 : 𝕜) : Fin r → 𝕜)) = β w)
    (hclosed : ∀ w : Fin r → 𝕜, extDeriv β w = 0) :
    ∃ (α : (Fin r → 𝕜) [⋀^Fin (n + 1)]→L[𝕜] 𝕜)
      (η : (Fin r → 𝕜) → (Fin r → 𝕜) [⋀^Fin n]→L[𝕜] 𝕜),
      Differentiable 𝕜 η ∧ Continuous (fderiv 𝕜 η) ∧
      (∀ (l : Fin r) (w : Fin r → 𝕜), η (w + p • (Pi.single l (1 : 𝕜) : Fin r → 𝕜)) = η w) ∧
      ∀ w : Fin r → 𝕜, β w = α + extDeriv η w := by
  classical
  set d := periodicAveragedData hdiff hcont' hper hclosed (List.finRange r) with hd
  have hinv : ∀ j : Fin r, FlowInvariant p d.form j :=
    fun j => d.invariant j (List.mem_finRange j)
  have hconst : ∀ w : Fin r → 𝕜, d.form w = d.form 0 :=
    fun w => const_of_flowInvariant hp d.diff hinv w 0
  refine ⟨d.form 0, fun w => (-1 : 𝕜) • d.prim w, ?_, ?_, ?_, ?_⟩
  · show Differentiable 𝕜 ((-1 : 𝕜) • d.prim)
    exact fun w => (d.primDiff w).const_smul (-1 : 𝕜)
  · have hfd : fderiv 𝕜 (fun w => (-1 : 𝕜) • d.prim w) =
        fun w => (-1 : 𝕜) • fderiv 𝕜 d.prim w := by
      funext w
      exact fderiv_const_smul (d.primDiff w) (-1 : 𝕜)
    rw [hfd]
    exact d.primFderivCont.const_smul (-1 : 𝕜)
  · intro l w
    show (-1 : 𝕜) • d.prim (w + p • (Pi.single l (1 : 𝕜) : Fin r → 𝕜)) = (-1 : 𝕜) • d.prim w
    rw [d.primPeriodic l w]
  · intro w
    show β w = d.form 0 + extDeriv ((-1 : 𝕜) • d.prim) w
    rw [extDeriv_smul, d.primDeriv w, hconst w, negOne_smul_alternating]
    abel

/-- **The constant form of the decomposition is unique.**  Two constant forms differing by an exact
form with a periodic primitive are equal. -/
theorem periodic_const_add_exact_unique {p : 𝕜} (hp : p ≠ 0)
    {α α' : (Fin r → 𝕜) [⋀^Fin (n + 1)]→L[𝕜] 𝕜}
    {η : (Fin r → 𝕜) → (Fin r → 𝕜) [⋀^Fin n]→L[𝕜] 𝕜} (hdiff : Differentiable 𝕜 η)
    (hcont' : Continuous (fderiv 𝕜 η))
    (hper : ∀ (l : Fin r) (w : Fin r → 𝕜), η (w + p • (Pi.single l (1 : 𝕜) : Fin r → 𝕜)) = η w)
    (heq : ∀ w : Fin r → 𝕜, α = α' + extDeriv η w) : α = α' := by
  have hd : ∀ w : Fin r → 𝕜, extDeriv η w = α - α' := by
    intro w
    rw [heq w]
    abel
  have hzero : α - α' = 0 := constantForm_eq_zero hp n (α - α') η hdiff hcont' hper hd
  exact sub_eq_zero.1 hzero

end ConstantDecomposition

end GaloisForLFunctions.HTGeometry
