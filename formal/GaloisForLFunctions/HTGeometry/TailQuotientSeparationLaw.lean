import GaloisForLFunctions.HTGeometry.FiniteGaugeTailCharge
import Mathlib.Topology.Instances.Nat

/-!
# Finite-observation / quotient-completion separation

Let a quotient identify records under every finite modification.  Every
finite-coordinate observation cylinder then surjects onto the entire
quotient.  Hence every quotient reporter determined by any fixed finite
observation is constant.  The same conclusion holds for sequential tail
quotients that identify eventually equal histories.

The result requires no algebra, topology, positivity, or boundedness on the
alphabet or reporter codomain.
-/

open Filter

namespace GaloisForLFunctions.HTGeometry

/-- A reporter has one value on its whole domain. -/
def ReporterConstant {X Y : Type*} (F : X → Y) : Prop :=
  ∀ x y, F x = F y

/-- Two records agree on every coordinate in an arbitrary observation
support. -/
def CoordinatesAgreeOn
    {I A : Type*} (E : Set I) (u v : I → A) : Prop :=
  ∀ i ∈ E, u i = v i

/-- Splice an arbitrary observed support onto a target completion record. -/
def coordinateSupportSplice
    {I A : Type*} (E : Set I) [DecidablePred (· ∈ E)]
    (observed tail : I → A) (i : I) : A :=
  if i ∈ E then observed i else tail i

theorem coordinateSupportSplice_agrees
    {I A : Type*} (E : Set I) [DecidablePred (· ∈ E)]
    (observed tail : I → A) :
    CoordinatesAgreeOn E (coordinateSupportSplice E observed tail) observed := by
  intro i hi
  simp [coordinateSupportSplice, hi]

theorem setOf_coordinateSupportSplice_ne_tail_subset
    {I A : Type*} (E : Set I) [DecidablePred (· ∈ E)]
    (observed tail : I → A) :
    {i | coordinateSupportSplice E observed tail i ≠ tail i} ⊆ E := by
  intro i hi
  by_contra hnot
  exact hi (by simp [coordinateSupportSplice, hnot])

/-- A quotient is saturated along support `E` when every modification
confined to `E` preserves completion phase. -/
def ModificationSaturatedOn
    {I A : Type*} (r : Setoid (I → A)) (E : Set I) : Prop :=
  ∀ ⦃u v : I → A⦄, {i | u i ≠ v i} ⊆ E → r u v

/-- **Universal support-cylinder law.** If completion erases every change
supported in `E`, then every `E`-observation cylinder contains a
representative of every completion phase. -/
theorem coordinateSupportCylinder_surjective_quotient
    {I A : Type*} (r : Setoid (I → A)) (E : Set I)
    (hr : ModificationSaturatedOn r E)
    (observed : I → A) (q : Quotient r) :
    ∃ record : I → A,
      CoordinatesAgreeOn E record observed ∧ Quotient.mk r record = q := by
  classical
  obtain ⟨tail, rfl⟩ := Quotient.exists_rep q
  refine ⟨coordinateSupportSplice E observed tail,
    coordinateSupportSplice_agrees E observed tail, ?_⟩
  exact Quotient.sound
    (hr (setOf_coordinateSupportSplice_ne_tail_subset E observed tail))

/-- A quotient reporter is determined on observation support `E` when
agreement throughout `E` forces equal reports. -/
def CoordinateQuotientReporterDeterminedOn
    {I A Y : Type*} (r : Setoid (I → A))
    (E : Set I) (F : Quotient r → Y) : Prop :=
  ∀ u v : I → A,
    CoordinatesAgreeOn E u v → F (Quotient.mk r u) = F (Quotient.mk r v)

/-- **Observation-support / completion separation law.** Any completion
reporter determined on a support whose modifications completion erases is
constant. -/
theorem coordinateSupport_quotientReporter_constant
    {I A Y : Type*} (r : Setoid (I → A)) (E : Set I)
    (hr : ModificationSaturatedOn r E)
    (F : Quotient r → Y)
    (hF : CoordinateQuotientReporterDeterminedOn r E F) :
    ReporterConstant F := by
  intro q₁ q₂
  obtain ⟨u, rfl⟩ := Quotient.exists_rep q₁
  obtain ⟨w, hcoordinates, hw⟩ :=
    coordinateSupportCylinder_surjective_quotient r E hr u q₂
  rw [← hw]
  exact hF u w fun i hi => (hcoordinates i hi).symm

/-- A family of negligible supports is erased by the completion quotient
when saturation holds on every member. -/
def ObservationSupportFamilySaturated
    {I A : Type*} (r : Setoid (I → A)) (𝒩 : Set (Set I)) : Prop :=
  ∀ E ∈ 𝒩, ModificationSaturatedOn r E

/-- Family form of the universal support-cylinder law. -/
theorem observationSupportFamilyCylinder_surjective_quotient
    {I A : Type*} (r : Setoid (I → A)) (𝒩 : Set (Set I))
    (hr : ObservationSupportFamilySaturated r 𝒩)
    {E : Set I} (hE : E ∈ 𝒩) (observed : I → A) (q : Quotient r) :
    ∃ record : I → A,
      CoordinatesAgreeOn E record observed ∧ Quotient.mk r record = q :=
  coordinateSupportCylinder_surjective_quotient r E (hr E hE) observed q

/-- Two records agree on a finite set of observed coordinates. -/
def FiniteCoordinatesAgree
    {I A : Type*} (s : Finset I) (u v : I → A) : Prop :=
  ∀ i ∈ s, u i = v i

/-- Splice finitely many observed coordinates to an arbitrary record. -/
def finiteCoordinateSplice
    {I A : Type*} [DecidableEq I]
    (s : Finset I) (observed tail : I → A) (i : I) : A :=
  if i ∈ s then observed i else tail i

theorem finiteCoordinateSplice_agrees
    {I A : Type*} [DecidableEq I]
    (s : Finset I) (observed tail : I → A) :
    FiniteCoordinatesAgree s (finiteCoordinateSplice s observed tail) observed := by
  intro i hi
  simp [finiteCoordinateSplice, hi]

theorem finite_setOf_finiteCoordinateSplice_ne_tail
    {I A : Type*} [DecidableEq I]
    (s : Finset I) (observed tail : I → A) :
    Set.Finite {i | finiteCoordinateSplice s observed tail i ≠ tail i} := by
  apply s.finite_toSet.subset
  intro i hi
  by_cases his : i ∈ s
  · simpa using his
  · exact (hi (by simp [finiteCoordinateSplice, his])).elim

/-- A record setoid is finite-modification-saturated when changing finitely
many coordinates preserves its equivalence class. -/
def FiniteModificationSaturated
    {I A : Type*} (r : Setoid (I → A)) : Prop :=
  ∀ ⦃u v : I → A⦄, Set.Finite {i | u i ≠ v i} → r u v

/-- **Universal finite-coordinate cylinder law.** Every finite observation
cylinder surjects onto every quotient insensitive to finite modifications. -/
theorem finiteCoordinateCylinder_surjective_quotient
    {I A : Type*} [DecidableEq I]
    (r : Setoid (I → A)) (hr : FiniteModificationSaturated r)
    (s : Finset I) (observed : I → A) (q : Quotient r) :
    ∃ record : I → A,
      FiniteCoordinatesAgree s record observed ∧ Quotient.mk r record = q := by
  obtain ⟨tail, rfl⟩ := Quotient.exists_rep q
  refine ⟨finiteCoordinateSplice s observed tail,
    finiteCoordinateSplice_agrees s observed tail, ?_⟩
  exact Quotient.sound
    (hr (finite_setOf_finiteCoordinateSplice_ne_tail s observed tail))

/-- A reporter on a finite-modification quotient is determined by the
coordinates in `s` when records agreeing there receive the same report. -/
def FiniteCoordinateQuotientReporterDeterminedBy
    {I A Y : Type*} (r : Setoid (I → A))
    (s : Finset I) (F : Quotient r → Y) : Prop :=
  ∀ u v : I → A,
    FiniteCoordinatesAgree s u v →
      F (Quotient.mk r u) = F (Quotient.mk r v)

/-- **Finite-observation / quotient-completion separation law.** Every
reporter on a finite-modification quotient that is determined by finitely
many coordinates is constant. -/
theorem finiteCoordinate_quotientReporter_constant
    {I A Y : Type*} [DecidableEq I]
    (r : Setoid (I → A)) (hr : FiniteModificationSaturated r)
    (s : Finset I) (F : Quotient r → Y)
    (hF : FiniteCoordinateQuotientReporterDeterminedBy r s F) :
    ReporterConstant F := by
  intro q₁ q₂
  obtain ⟨u, rfl⟩ := Quotient.exists_rep q₁
  obtain ⟨w, hcoordinates, hw⟩ :=
    finiteCoordinateCylinder_surjective_quotient r hr s u q₂
  rw [← hw]
  exact hF u w fun i hi => (hcoordinates i hi).symm

/-- Every nonconstant finite-modification-quotient reporter escapes every
finite coordinate observation. -/
theorem nonconstant_finiteModificationQuotientReporter_not_determinedBy
    {I A Y : Type*} [DecidableEq I]
    (r : Setoid (I → A)) (hr : FiniteModificationSaturated r)
    (F : Quotient r → Y) (hF : ¬ ReporterConstant F) (s : Finset I) :
    ¬ FiniteCoordinateQuotientReporterDeterminedBy r s F := by
  intro hfinite
  exact hF (finiteCoordinate_quotientReporter_constant r hr s F hfinite)

/-- Every class of a finite-modification quotient is dense in the product
topology on records. -/
theorem finiteModificationQuotient_fiber_dense
    {I A : Type*} [TopologicalSpace A]
    (r : Setoid (I → A)) (hr : FiniteModificationSaturated r)
    (x : I → A) :
    Dense ((Quotient.mk r) ⁻¹' {Quotient.mk r x}) := by
  apply GaloisForLFunctions.dense_fiber_of_finiteModification_invariant
  intro u v huv
  apply Quotient.sound
  apply hr
  change Set.Finite {i | v i ≠ u i} at huv
  exact huv

/-- The quotient topology induced by a finite-modification quotient map is
indiscrete. -/
theorem finiteModificationQuotient_coinduced_eq_indiscrete
    {I A : Type*} [TopologicalSpace A]
    (r : Setoid (I → A)) (hr : FiniteModificationSaturated r) :
    TopologicalSpace.coinduced (Quotient.mk r)
      (inferInstance : TopologicalSpace (I → A)) = ⊤ := by
  apply GaloisForLFunctions.coinduced_eq_indiscrete_of_dense_fibers
  · exact Quotient.mk_surjective
  · intro q
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    exact finiteModificationQuotient_fiber_dense r hr x

/-- A reporter on a finite-modification quotient whose pullback is
continuous at even one record, with values in a `T₁` space, is constant. -/
theorem continuousAt_pullback_finiteModificationQuotientReporter_constant
    {I A Y : Type*} [TopologicalSpace A] [TopologicalSpace Y] [T1Space Y]
    (r : Setoid (I → A)) (hr : FiniteModificationSaturated r)
    (F : Quotient r → Y) (x : I → A)
    (hF : ContinuousAt (F ∘ Quotient.mk r) x) :
    ReporterConstant F := by
  have hdense : ∀ y : I → A,
      Dense ((Quotient.mk r) ⁻¹' {Quotient.mk r y}) :=
    fun y => finiteModificationQuotient_fiber_dense r hr y
  have hconstant :=
    GaloisForLFunctions.continuousAt_constant_of_dense_fibers
      (Quotient.mk r) (F ∘ Quotient.mk r) x hF hdense
      (fun y z hyz => congrArg F hyz)
  intro q₁ q₂
  obtain ⟨u, rfl⟩ := Quotient.exists_rep q₁
  obtain ⟨v, rfl⟩ := Quotient.exists_rep q₂
  exact (hconstant u).trans (hconstant v).symm

/-- Two histories have the same observed prefix through horizon `N`. -/
def FinitePrefixAgree {A : Type*} (N : ℕ) (u v : ℕ → A) : Prop :=
  ∀ n ≤ N, u n = v n

/-- Splice one observed prefix to an arbitrary tail. -/
def finitePrefixTailSplice {A : Type*}
    (N : ℕ) (observed tail : ℕ → A) (n : ℕ) : A :=
  if n ≤ N then observed n else tail n

theorem finitePrefixTailSplice_agrees
    {A : Type*} (N : ℕ) (observed tail : ℕ → A) :
    FinitePrefixAgree N (finitePrefixTailSplice N observed tail) observed := by
  intro n hn
  simp [finitePrefixTailSplice, hn]

theorem finitePrefixTailSplice_eventuallyEq_tail
    {A : Type*} (N : ℕ) (observed tail : ℕ → A) :
    finitePrefixTailSplice N observed tail =ᶠ[atTop] tail := by
  filter_upwards [Filter.eventually_ge_atTop (N + 1)] with n hn
  simp [finitePrefixTailSplice]
  omega

/-- A history setoid is tail-saturated when eventual equality implies its
equivalence relation. -/
def TailSaturated {A : Type*} (r : Setoid (ℕ → A)) : Prop :=
  ∀ ⦃u v : ℕ → A⦄, u =ᶠ[atTop] v → r u v

/-- **Universal finite-cylinder law.** Every finite cylinder surjects onto
every quotient whose equivalence relation ignores finite modifications. -/
theorem finiteCylinder_surjective_tailQuotient
    {A : Type*} (r : Setoid (ℕ → A)) (hr : TailSaturated r)
    (N : ℕ) (observed : ℕ → A) (q : Quotient r) :
    ∃ history : ℕ → A,
      FinitePrefixAgree N history observed ∧
        Quotient.mk r history = q := by
  obtain ⟨tail, rfl⟩ := Quotient.exists_rep q
  refine ⟨finitePrefixTailSplice N observed tail,
    finitePrefixTailSplice_agrees N observed tail, ?_⟩
  exact Quotient.sound
    (hr (finitePrefixTailSplice_eventuallyEq_tail N observed tail))

/-- A reporter on a tail quotient is determined by horizon `N` when equal
observed prefixes always give equal reports. -/
def TailQuotientReporterDeterminedBy
    {A Y : Type*} (r : Setoid (ℕ → A))
    (N : ℕ) (F : Quotient r → Y) : Prop :=
  ∀ u v : ℕ → A,
    FinitePrefixAgree N u v → F (Quotient.mk r u) = F (Quotient.mk r v)

/-- **Finite-prefix / tail-quotient separation law.** Every reporter on a
tail-saturated quotient that is determined by one finite horizon is
constant. -/
theorem finiteHorizon_tailQuotientReporter_constant
    {A Y : Type*} (r : Setoid (ℕ → A)) (hr : TailSaturated r)
    (N : ℕ) (F : Quotient r → Y)
    (hF : TailQuotientReporterDeterminedBy r N F) :
    ReporterConstant F := by
  intro q₁ q₂
  obtain ⟨u, rfl⟩ := Quotient.exists_rep q₁
  obtain ⟨w, hprefix, hw⟩ :=
    finiteCylinder_surjective_tailQuotient r hr N u q₂
  rw [← hw]
  exact hF u w fun n hn => (hprefix n hn).symm

/-- Every nonconstant tail-quotient reporter escapes every fixed finite
observation horizon. -/
theorem nonconstant_tailQuotientReporter_not_determinedBy
    {A Y : Type*} (r : Setoid (ℕ → A)) (hr : TailSaturated r)
    (F : Quotient r → Y) (hF : ¬ ReporterConstant F) (N : ℕ) :
    ¬ TailQuotientReporterDeterminedBy r N F := by
  intro hfinite
  exact hF (finiteHorizon_tailQuotientReporter_constant r hr N F hfinite)

end GaloisForLFunctions.HTGeometry
