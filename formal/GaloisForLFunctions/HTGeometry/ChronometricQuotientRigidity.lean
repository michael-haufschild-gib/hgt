import Mathlib.GroupTheory.GroupAction.Quotient
import GaloisForLFunctions.HTGeometry.ContinuumChronometricGravity

/-!
# Chronometric rigidity modulo label-preserving equivalences

The branch-safe rigidity statement uses fixed event and tangent labels. This file removes that
restriction: a group of frame automorphisms acts on geometries, on squared-interval observations
and on calibrated source labels, and the rigidity theorem descends to the orbit quotients.

The abstract half is that an injective equivariant encoding induces an injective map of orbit
quotients, so equality of quotient solution graphs forces the two laws to agree *up to the action*.

The concrete half constructs the acting group in the trivialized case: a clock frame automorphism
is a relabelling of events together with a linear reframing of each tangent fiber. Its action on
metric fields is pullback, and squared clock intervals are equivariant for it.
-/

namespace GaloisForLFunctions.HTGeometry

universe u v w

/-! ## Orbit quotients of an equivariant encoding -/

section OrbitQuotient

variable {Γ : Type*} [Group Γ] {α : Type u} {β : Type v}
  [MulAction Γ α] [MulAction Γ β]

/-- The map induced on orbit quotients by an equivariant map. -/
def orbitQuotientMap (f : α → β) (hf : ∀ (γ : Γ) (a : α), f (γ • a) = γ • f a) :
    Quotient (MulAction.orbitRel Γ α) → Quotient (MulAction.orbitRel Γ β) :=
  Quotient.lift (fun a => Quotient.mk (MulAction.orbitRel Γ β) (f a)) (by
    intro a b hab
    apply Quotient.sound
    simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hab ⊢
    obtain ⟨γ, hγ⟩ := hab
    exact ⟨γ, by rw [← hf γ b, hγ]⟩)

@[simp] theorem orbitQuotientMap_mk (f : α → β)
    (hf : ∀ (γ : Γ) (a : α), f (γ • a) = γ • f a) (a : α) :
    orbitQuotientMap f hf (Quotient.mk (MulAction.orbitRel Γ α) a) =
      Quotient.mk (MulAction.orbitRel Γ β) (f a) := rfl

/-- An injective equivariant map induces an injective map of orbit quotients. -/
theorem orbitQuotientMap_injective (f : α → β)
    (hf : ∀ (γ : Γ) (a : α), f (γ • a) = γ • f a) (hinj : Function.Injective f) :
    Function.Injective (orbitQuotientMap f hf) := by
  intro x y hxy
  induction x using Quotient.inductionOn with
  | h a =>
    induction y using Quotient.inductionOn with
    | h b =>
      rw [orbitQuotientMap_mk, orbitQuotientMap_mk] at hxy
      have hrel := Quotient.exact hxy
      simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
      obtain ⟨γ, hγ⟩ := hrel
      apply Quotient.sound
      simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
      refine ⟨γ, hinj ?_⟩
      rw [hf γ b, hγ]

end OrbitQuotient

/-! ## Quotient chronometric rigidity -/

section QuotientRigidity

variable {Γ : Type*} [Group Γ]
  {Geometry : Type u} {Source : Type v} {Observation : Type w}
  [MulAction Γ Geometry] [MulAction Γ Source] [MulAction Γ Observation]

/-- **Chronometric operator rigidity modulo a group of label-preserving equivalences.**

If the observation encoding is injective and equivariant, and both laws are equivariant, then
their solution graphs on orbit quotients coincide exactly when the two laws agree up to the
action. Equality of laws is replaced by equivalence, not weakened away. -/
theorem chronometricSolutionGraph_orbitQuotient_eq_iff
    {encode : Geometry → Observation}
    (hencode : ∀ (γ : Γ) (g : Geometry), encode (γ • g) = γ • encode g)
    (hinj : Function.Injective encode)
    {law₁ law₂ : Geometry → Source}
    (h₁ : ∀ (γ : Γ) (g : Geometry), law₁ (γ • g) = γ • law₁ g)
    (h₂ : ∀ (γ : Γ) (g : Geometry), law₂ (γ • g) = γ • law₂ g) :
    chronometricSolutionGraph (orbitQuotientMap encode hencode)
          (orbitQuotientMap law₁ h₁) =
        chronometricSolutionGraph (orbitQuotientMap encode hencode)
          (orbitQuotientMap law₂ h₂) ↔
      ∀ g : Geometry, ∃ γ : Γ, law₁ g = γ • law₂ g := by
  rw [chronometricSolutionGraph_eq_iff_of_injective
    (orbitQuotientMap_injective encode hencode hinj)]
  constructor
  · intro hlaw g
    have hpt := congrFun hlaw (Quotient.mk (MulAction.orbitRel Γ Geometry) g)
    rw [orbitQuotientMap_mk, orbitQuotientMap_mk] at hpt
    have hrel := Quotient.exact hpt
    simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
    obtain ⟨γ, hγ⟩ := hrel
    exact ⟨γ, hγ.symm⟩
  · intro hlaw
    funext x
    induction x using Quotient.inductionOn with
    | h g =>
      rw [orbitQuotientMap_mk, orbitQuotientMap_mk]
      apply Quotient.sound
      simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
      obtain ⟨γ, hγ⟩ := hlaw g
      exact ⟨γ, hγ.symm⟩

end QuotientRigidity

/-! ## Clock frame automorphisms of a trivialized tangent bundle -/

/-- A clock-label-preserving frame automorphism: a relabelling of events together with a linear
reframing of each tangent fiber. This is the trivialized model of a bundle automorphism covering
a diffeomorphism. -/
structure ClockFrameAut (Event : Type u) (Tangent : Type v)
    [AddCommGroup Tangent] [Module ℝ Tangent] where
  /-- Relabelling of events. -/
  base : Equiv.Perm Event
  /-- Linear reframing of the fiber over each event. -/
  fiber : Event → (Tangent ≃ₗ[ℝ] Tangent)

namespace ClockFrameAut

variable {Event : Type u} {Tangent : Type v} [AddCommGroup Tangent] [Module ℝ Tangent]

@[ext] theorem ext {a b : ClockFrameAut Event Tangent}
    (hbase : a.base = b.base) (hfiber : a.fiber = b.fiber) : a = b := by
  cases a
  cases b
  simp_all

instance : Group (ClockFrameAut Event Tangent) where
  mul a b := ⟨a.base * b.base, fun x => (b.fiber x).trans (a.fiber (b.base x))⟩
  one := ⟨1, fun _ => LinearEquiv.refl ℝ Tangent⟩
  inv a := ⟨a.base⁻¹, fun x => (a.fiber (a.base⁻¹ x)).symm⟩
  mul_assoc a b c := by
    refine ext (mul_assoc _ _ _) ?_
    funext x
    exact (LinearEquiv.trans_assoc _ _ _).symm
  one_mul a := by
    refine ext (one_mul _) ?_
    funext x
    exact LinearEquiv.trans_refl _
  mul_one a := by
    refine ext (mul_one _) ?_
    funext x
    exact LinearEquiv.refl_trans _
  inv_mul_cancel a := by
    refine ext (inv_mul_cancel _) ?_
    funext x
    have hbase : a.base⁻¹ (a.base x) = x := a.base.symm_apply_apply x
    show (a.fiber x).trans ((a.fiber (a.base⁻¹ (a.base x))).symm) = LinearEquiv.refl ℝ Tangent
    rw [hbase]
    exact LinearEquiv.self_trans_symm _

@[simp] theorem mul_base (a b : ClockFrameAut Event Tangent) :
    (a * b).base = a.base * b.base := rfl

@[simp] theorem mul_fiber (a b : ClockFrameAut Event Tangent) (x : Event) :
    (a * b).fiber x = (b.fiber x).trans (a.fiber (b.base x)) := rfl

@[simp] theorem one_base : (1 : ClockFrameAut Event Tangent).base = 1 := rfl

@[simp] theorem one_fiber (x : Event) :
    (1 : ClockFrameAut Event Tangent).fiber x = LinearEquiv.refl ℝ Tangent := rfl

@[simp] theorem inv_base (a : ClockFrameAut Event Tangent) : a⁻¹.base = a.base⁻¹ := rfl

@[simp] theorem inv_fiber (a : ClockFrameAut Event Tangent) (x : Event) :
    a⁻¹.fiber x = (a.fiber (a.base⁻¹ x)).symm := rfl

/-- Reframing transported to the fiber over `x` by the inverse automorphism. -/
def pullbackFiber (a : ClockFrameAut Event Tangent) (x : Event) : Tangent ≃ₗ[ℝ] Tangent :=
  (a.fiber (a.base⁻¹ x)).symm

theorem pullbackFiber_one (x : Event) :
    pullbackFiber (1 : ClockFrameAut Event Tangent) x = LinearEquiv.refl ℝ Tangent := by
  simp [pullbackFiber]

theorem pullbackFiber_mul (a b : ClockFrameAut Event Tangent) (x : Event) (u : Tangent) :
    pullbackFiber (a * b) x u = pullbackFiber b (a.base⁻¹ x) (pullbackFiber a x u) := by
  have hbase : (a.base * b.base)⁻¹ x = b.base⁻¹ (a.base⁻¹ x) := by
    rw [mul_inv_rev]
    rfl
  have happ : b.base (b.base⁻¹ (a.base⁻¹ x)) = a.base⁻¹ x :=
    b.base.apply_symm_apply _
  simp only [pullbackFiber, mul_base, mul_fiber, hbase, happ]
  rfl

end ClockFrameAut

/-- Signed squared-interval clock data, carrying the frame-automorphism action. -/
structure ChronometricObservation (Event : Type u) (Tangent : Type v) where
  /-- Squared interval of each tangent direction at each event. -/
  data : Event → Tangent → ℝ

namespace ChronometricObservation

variable {Event : Type u} {Tangent : Type v}

@[ext] theorem ext {Q R : ChronometricObservation Event Tangent} (h : Q.data = R.data) : Q = R := by
  cases Q
  cases R
  simp_all

theorem mk_injective :
    Function.Injective (ChronometricObservation.mk : (Event → Tangent → ℝ) → _) := by
  intro Q R h
  exact congrArg ChronometricObservation.data h

end ChronometricObservation

section ClockFrameAction

variable {Event : Type u} {Tangent : Type v} [AddCommGroup Tangent] [Module ℝ Tangent]

instance : MulAction (ClockFrameAut Event Tangent) (ChronometricObservation Event Tangent) where
  smul a Q := ⟨fun x v => Q.data (a.base⁻¹ x) (ClockFrameAut.pullbackFiber a x v)⟩
  one_smul Q := by
    refine ChronometricObservation.ext ?_
    funext x v
    show Q.data ((1 : ClockFrameAut Event Tangent).base⁻¹ x)
        (ClockFrameAut.pullbackFiber 1 x v) = Q.data x v
    rw [ClockFrameAut.pullbackFiber_one]
    simp
  mul_smul a b Q := by
    refine ChronometricObservation.ext ?_
    funext x v
    show Q.data ((a * b).base⁻¹ x) (ClockFrameAut.pullbackFiber (a * b) x v) =
      Q.data (b.base⁻¹ (a.base⁻¹ x))
        (ClockFrameAut.pullbackFiber b (a.base⁻¹ x) (ClockFrameAut.pullbackFiber a x v))
    rw [ClockFrameAut.pullbackFiber_mul]
    congr 1

@[simp] theorem chronometricObservation_smul_data
    (a : ClockFrameAut Event Tangent) (Q : ChronometricObservation Event Tangent)
    (x : Event) (v : Tangent) :
    (a • Q).data x v = Q.data (a.base⁻¹ x) (ClockFrameAut.pullbackFiber a x v) := rfl

instance : MulAction (ClockFrameAut Event Tangent)
    (ChronometricMetricField Event Tangent) where
  smul a g :=
    { form := fun x =>
        (g.form (a.base⁻¹ x)).compl₁₂
          ((ClockFrameAut.pullbackFiber a x : Tangent ≃ₗ[ℝ] Tangent) : Tangent →ₗ[ℝ] Tangent)
          ((ClockFrameAut.pullbackFiber a x : Tangent ≃ₗ[ℝ] Tangent) : Tangent →ₗ[ℝ] Tangent)
      symmetric := by
        intro x u v
        simp only [LinearMap.compl₁₂_apply]
        exact g.symmetric _ _ _ }
  one_smul g := by
    refine ChronometricMetricField.ext ?_
    funext x
    apply LinearMap.ext
    intro u
    apply LinearMap.ext
    intro v
    show g.form ((1 : ClockFrameAut Event Tangent).base⁻¹ x)
        (ClockFrameAut.pullbackFiber 1 x u) (ClockFrameAut.pullbackFiber 1 x v) = g.form x u v
    rw [ClockFrameAut.pullbackFiber_one]
    simp
  mul_smul a b g := by
    refine ChronometricMetricField.ext ?_
    funext x
    apply LinearMap.ext
    intro u
    apply LinearMap.ext
    intro v
    show g.form ((a * b).base⁻¹ x) (ClockFrameAut.pullbackFiber (a * b) x u)
        (ClockFrameAut.pullbackFiber (a * b) x v) =
      g.form (b.base⁻¹ (a.base⁻¹ x))
        (ClockFrameAut.pullbackFiber b (a.base⁻¹ x) (ClockFrameAut.pullbackFiber a x u))
        (ClockFrameAut.pullbackFiber b (a.base⁻¹ x) (ClockFrameAut.pullbackFiber a x v))
    rw [ClockFrameAut.pullbackFiber_mul, ClockFrameAut.pullbackFiber_mul]
    congr 1

@[simp] theorem chronometricMetricField_smul_form
    (a : ClockFrameAut Event Tangent) (g : ChronometricMetricField Event Tangent)
    (x : Event) (u v : Tangent) :
    (a • g).form x u v =
      g.form (a.base⁻¹ x) (ClockFrameAut.pullbackFiber a x u)
        (ClockFrameAut.pullbackFiber a x v) := rfl

/-- Squared-interval data of a metric field, as a frame-automorphism module element. -/
def chronometricObservationOf (g : ChronometricMetricField Event Tangent) :
    ChronometricObservation Event Tangent :=
  ⟨ChronometricMetricField.squaredInterval g⟩

theorem chronometricObservationOf_injective :
    Function.Injective
      (chronometricObservationOf :
        ChronometricMetricField Event Tangent → ChronometricObservation Event Tangent) :=
  ChronometricObservation.mk_injective.comp
    ChronometricMetricField.squaredInterval_injective

/-- **Squared clock intervals are equivariant for clock frame automorphisms.** -/
theorem chronometricObservationOf_equivariant (a : ClockFrameAut Event Tangent)
    (g : ChronometricMetricField Event Tangent) :
    chronometricObservationOf (a • g) = a • chronometricObservationOf g := by
  refine ChronometricObservation.ext ?_
  funext x v
  rfl

end ClockFrameAction

/-! ### The frame-automorphism action is not trivial -/

section Nontriviality

variable {Event : Type u} {Tangent : Type v} [AddCommGroup Tangent] [Module ℝ Tangent]

/-- Uniform rescaling of a fiber by a nonzero scalar. -/
noncomputable def fiberScaling (c : ℝ) (hc : c ≠ 0) : Tangent ≃ₗ[ℝ] Tangent where
  toFun v := c • v
  map_add' x y := by simp [smul_add]
  map_smul' r x := smul_comm c r x
  invFun v := c⁻¹ • v
  left_inv v := by simp [smul_smul, inv_mul_cancel₀ hc]
  right_inv v := by simp [smul_smul, mul_inv_cancel₀ hc]

@[simp] theorem fiberScaling_apply (c : ℝ) (hc : c ≠ 0) (v : Tangent) :
    fiberScaling c hc v = c • v := rfl

@[simp] theorem fiberScaling_symm_apply (c : ℝ) (hc : c ≠ 0) (v : Tangent) :
    (fiberScaling (Tangent := Tangent) c hc).symm v = c⁻¹ • v := rfl

/-- Uniform conformal reframing of every fiber, with the event labels untouched. -/
noncomputable def ClockFrameAut.scaling (c : ℝ) (hc : c ≠ 0) :
    ClockFrameAut Event Tangent :=
  ⟨1, fun _ => fiberScaling (Tangent := Tangent) c hc⟩

theorem ClockFrameAut.pullbackFiber_scaling (c : ℝ) (hc : c ≠ 0) (x : Event) (v : Tangent) :
    ClockFrameAut.pullbackFiber (ClockFrameAut.scaling (Event := Event) (Tangent := Tangent) c hc) x v = c⁻¹ • v := rfl

/-- A conformal reframing rescales every squared clock interval by `c⁻²`. -/
theorem smul_form_scaling (c : ℝ) (hc : c ≠ 0)
    (g : ChronometricMetricField Event Tangent) (x : Event) (u v : Tangent) :
    ((ClockFrameAut.scaling (Event := Event) (Tangent := Tangent) c hc) • g).form x u v =
      c⁻¹ * c⁻¹ * g.form x u v := by
  have hbase : (ClockFrameAut.scaling (Event := Event) (Tangent := Tangent) c hc).base⁻¹ x = x :=
    rfl
  rw [chronometricMetricField_smul_form, ClockFrameAut.pullbackFiber_scaling,
    ClockFrameAut.pullbackFiber_scaling, hbase]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- **The action is genuinely coarser than equality.** A conformal reframing with `c⁻² ≠ 1` moves
every metric field with a nonzero component, so the quotient rigidity theorem is not a restatement
of the fixed-label theorem. -/
theorem smul_scaling_ne_self (c : ℝ) (hc : c ≠ 0) (hcsq : c⁻¹ * c⁻¹ ≠ 1)
    (g : ChronometricMetricField Event Tangent) {x : Event} {u v : Tangent}
    (hg : g.form x u v ≠ 0) :
    (ClockFrameAut.scaling (Event := Event) (Tangent := Tangent) c hc) • g ≠ g := by
  intro hEq
  have hcomp :
      ((ClockFrameAut.scaling (Event := Event) (Tangent := Tangent) c hc) • g).form x u v =
        g.form x u v := by rw [hEq]
  rw [smul_form_scaling] at hcomp
  refine hcsq ?_
  have hfactor : (c⁻¹ * c⁻¹ - 1) * g.form x u v = 0 := by linarith
  rcases mul_eq_zero.mp hfactor with h | h
  · linarith [sub_eq_zero.mp h]
  · exact absurd h hg

end Nontriviality

/-- **Chronometric operator rigidity modulo clock frame automorphisms.**

Two arbitrary nonlinear gravity laws, equivariant under relabelling of events and linear
reframing of tangent fibers, have identical squared-clock solution graphs on the orbit quotients
exactly when they agree pointwise up to a frame automorphism of the source labels. -/
theorem chronometricOperatorRigidity_mod_frameAut
    {Event : Type u} {Tangent : Type v} [AddCommGroup Tangent] [Module ℝ Tangent]
    {Source : Type w} [MulAction (ClockFrameAut Event Tangent) Source]
    {law₁ law₂ : ChronometricMetricField Event Tangent → Source}
    (h₁ : ∀ (a : ClockFrameAut Event Tangent) (g : ChronometricMetricField Event Tangent),
      law₁ (a • g) = a • law₁ g)
    (h₂ : ∀ (a : ClockFrameAut Event Tangent) (g : ChronometricMetricField Event Tangent),
      law₂ (a • g) = a • law₂ g) :
    chronometricSolutionGraph
          (orbitQuotientMap chronometricObservationOf chronometricObservationOf_equivariant)
          (orbitQuotientMap law₁ h₁) =
        chronometricSolutionGraph
          (orbitQuotientMap chronometricObservationOf chronometricObservationOf_equivariant)
          (orbitQuotientMap law₂ h₂) ↔
      ∀ g : ChronometricMetricField Event Tangent,
        ∃ a : ClockFrameAut Event Tangent, law₁ g = a • law₂ g :=
  chronometricSolutionGraph_orbitQuotient_eq_iff
    chronometricObservationOf_equivariant chronometricObservationOf_injective h₁ h₂

end GaloisForLFunctions.HTGeometry
