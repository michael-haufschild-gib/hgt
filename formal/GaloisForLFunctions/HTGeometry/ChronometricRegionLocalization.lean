import GaloisForLFunctions.HTGeometry.ChronometricGaugeRigidity

/-!
# Chronometric rigidity from a bounded laboratory region

Clock data are collected inside a worldtube, not on the whole event set. This file separates what a
bounded region does and does not determine.

*What it determines.* Squared clock intervals inside a region determine the chronometric field
inside that region, so any law that is a function of the field over the region is determined by the
region's branch-safe solution graph. A laboratory identifies the law of its own region completely.

*What it does not determine.* In the model class of the rigidity theorem — indexed families of
symmetric bilinear forms, with no field equation relating different events — a proper subregion
never determines the field outside it. Two fields agreeing on the region but differing at one
outside event are separated by laws with identical region graphs.

The two statements meet in an exact criterion: region data give full rigidity precisely when the
restriction map is injective, that is, precisely when unique continuation from the region holds.
Supplying that continuation is the role of a field equation and is outside this model class.
-/

namespace GaloisForLFunctions.HTGeometry

universe u v w

namespace ChronometricMetricField

variable {Event : Type u} {Tangent : Type v} [AddCommGroup Tangent] [Module ℝ Tangent]

/-- Restriction of a chronometric field to a region of events. -/
def restrictRegion (W : Set Event) (g : ChronometricMetricField Event Tangent) :
    ChronometricMetricField (↥W) Tangent where
  form := fun x => g.form x.1
  symmetric := fun x u v => g.symmetric x.1 u v

@[simp] theorem restrictRegion_form (W : Set Event) (g : ChronometricMetricField Event Tangent)
    (x : ↥W) : (restrictRegion W g).form x = g.form x.1 := rfl

/-- Squared clock intervals measured only inside a region. -/
def regionObservation (W : Set Event) (g : ChronometricMetricField Event Tangent) :
    ↥W → Tangent → ℝ :=
  (restrictRegion W g).squaredInterval

@[simp] theorem regionObservation_apply (W : Set Event)
    (g : ChronometricMetricField Event Tangent) (x : ↥W) (v : Tangent) :
    regionObservation W g x v = g.form x.1 v v := rfl

/-- **A laboratory determines the chronometric field of its own region.** -/
theorem restrictRegion_eq_of_regionObservation_eq {W : Set Event}
    {g h : ChronometricMetricField Event Tangent}
    (heq : regionObservation W g = regionObservation W h) :
    restrictRegion W g = restrictRegion W h :=
  squaredInterval_injective heq

/-- A law is a function of the chronometric field over the region. -/
def FactorsThroughRegion (W : Set Event)
    (law : ChronometricMetricField Event Tangent → Source) : Prop :=
  ∀ g h, restrictRegion W g = restrictRegion W h → law g = law h

/-- **Branch-safe rigidity from region data.** Two nonlinear laws that are functions of the
chronometric field over a region have identical region solution graphs exactly when they are the
same operator. -/
theorem chronometricRegionRigidity {W : Set Event} {Source : Type w}
    {law₁ law₂ : ChronometricMetricField Event Tangent → Source}
    (h₁ : FactorsThroughRegion W law₁) (h₂ : FactorsThroughRegion W law₂) :
    chronometricSolutionGraph (regionObservation W) law₁ =
        chronometricSolutionGraph (regionObservation W) law₂ ↔
      law₁ = law₂ := by
  refine chronometricSolutionGraph_eq_iff_of_fiberConstant ?_ ?_
  · exact fun a b hab => h₁ a b (restrictRegion_eq_of_regionObservation_eq hab)
  · exact fun a b hab => h₂ a b (restrictRegion_eq_of_regionObservation_eq hab)

/-! ### Unique continuation is exactly what region data lack -/

/-- Unique continuation from a region: a chronometric field is determined by its restriction. -/
def UniqueContinuation (W : Set Event) (Tangent : Type v)
    [AddCommGroup Tangent] [Module ℝ Tangent] : Prop :=
  ∀ g h : ChronometricMetricField Event Tangent,
    restrictRegion W g = restrictRegion W h → g = h

/-- **Region data are injective exactly when unique continuation holds.** -/
theorem injective_regionObservation_iff_uniqueContinuation (W : Set Event) :
    Function.Injective
        (regionObservation W : ChronometricMetricField Event Tangent → ↥W → Tangent → ℝ) ↔
      UniqueContinuation W Tangent := by
  constructor
  · intro hinj g h hres
    refine hinj ?_
    simp only [regionObservation, hres]
  · intro hcont g h hobs
    exact hcont g h (restrictRegion_eq_of_regionObservation_eq hobs)

/-- **With unique continuation, region data give unrestricted rigidity.** -/
theorem chronometricRegionRigidity_of_uniqueContinuation {W : Set Event} {Source : Type w}
    (hcont : UniqueContinuation W Tangent)
    (law₁ law₂ : ChronometricMetricField Event Tangent → Source) :
    chronometricSolutionGraph (regionObservation W) law₁ =
        chronometricSolutionGraph (regionObservation W) law₂ ↔
      law₁ = law₂ :=
  chronometricSolutionGraph_eq_iff_of_injective
    ((injective_regionObservation_iff_uniqueContinuation W).2 hcont) law₁ law₂

/-! ### A proper subregion never continues, absent a field equation -/

/-- The chronometric field that carries a prescribed form at one event and vanishes elsewhere. -/
noncomputable def pointForm (x₀ : Event) (B : LinearMap.BilinForm ℝ Tangent)
    (hB : ∀ u v, B u v = B v u) : ChronometricMetricField Event Tangent := by
  classical
  exact
    { form := fun x => if x = x₀ then B else 0
      symmetric := by
        intro x u v
        by_cases hx : x = x₀ <;> simp [hx, hB u v] }

theorem pointForm_form_self (x₀ : Event) (B : LinearMap.BilinForm ℝ Tangent)
    (hB : ∀ u v, B u v = B v u) : (pointForm x₀ B hB).form x₀ = B := by
  classical
  simp [pointForm]

theorem pointForm_form_of_ne {x x₀ : Event} (hx : x ≠ x₀)
    (B : LinearMap.BilinForm ℝ Tangent) (hB : ∀ u v, B u v = B v u) :
    (pointForm x₀ B hB).form x = 0 := by
  classical
  simp [pointForm, hx]

/-- The identically vanishing chronometric field. -/
def zeroField : ChronometricMetricField Event Tangent where
  form := fun _ => 0
  symmetric := fun _ _ _ => rfl

/-- **A proper subregion does not determine the chronometric field.** Absent any relation between
different events, a form planted outside the region is invisible to it. -/
theorem not_uniqueContinuation_of_exists_notMem {W : Set Event} {x₀ : Event} (hx₀ : x₀ ∉ W)
    (B : LinearMap.BilinForm ℝ Tangent) (hB : ∀ u v, B u v = B v u) (hBne : B ≠ 0) :
    ¬ UniqueContinuation W Tangent := by
  intro hcont
  have hres : restrictRegion W (zeroField : ChronometricMetricField Event Tangent) =
      restrictRegion W (pointForm x₀ B hB) := by
    refine ext ?_
    funext x
    have hne : (x : Event) ≠ x₀ := by
      intro h
      exact hx₀ (h ▸ x.2)
    rw [restrictRegion_form, restrictRegion_form, pointForm_form_of_ne hne]
    rfl
  have hEq := hcont _ _ hres
  have hzero : (zeroField : ChronometricMetricField Event Tangent).form x₀ = 0 := rfl
  have hpoint : (pointForm x₀ B hB).form x₀ = B := pointForm_form_self x₀ B hB
  have : (0 : LinearMap.BilinForm ℝ Tangent) = B := by
    rw [← hzero, ← hpoint, hEq]
  exact hBne this.symm

/-- **Worldtube data alone cannot determine an arbitrary nonlinear law.** For a proper subregion
and a nonzero symmetric form, two laws separating a field planted outside the region have identical
region solution graphs. -/
theorem exists_ne_law_regionGraph_eq {W : Set Event} {x₀ : Event} (hx₀ : x₀ ∉ W)
    (B : LinearMap.BilinForm ℝ Tangent) (hB : ∀ u v, B u v = B v u) (hBne : B ≠ 0) :
    ∃ law₁ law₂ : ChronometricMetricField Event Tangent → Prop,
      chronometricSolutionGraph (regionObservation W) law₁ =
          chronometricSolutionGraph (regionObservation W) law₂ ∧
        law₁ ≠ law₂ := by
  refine exists_ne_law_graph_eq_of_not_injective ?_
  intro hinj
  exact not_uniqueContinuation_of_exists_notMem hx₀ B hB hBne
    ((injective_regionObservation_iff_uniqueContinuation W).1 hinj)

end ChronometricMetricField

/-- A nonzero symmetric real bilinear form exists on `ℝ`, so the region no-go is not vacuous. -/
theorem exists_ne_zero_symmetric_bilinForm_real :
    ∃ B : LinearMap.BilinForm ℝ ℝ, (∀ u v, B u v = B v u) ∧ B ≠ 0 := by
  refine ⟨LinearMap.mul ℝ ℝ, fun u v => mul_comm u v, ?_⟩
  intro hzero
  have := congrFun (congrFun (congrArg (fun f : LinearMap.BilinForm ℝ ℝ =>
    fun u v => f u v) hzero) 1) 1
  simp at this

end GaloisForLFunctions.HTGeometry
