import GaloisForLFunctions.HTGeometry.ConstitutiveTVConflictColoring

namespace HTGeometry

noncomputable section

/-!
# Mandatory-identification and conflict interference

Mandatory identifications propagate through their equivalence closure.  Total-variation tasks
generate forbidden identifications.  A respecting lossless observer exists exactly when these two
relations do not meet.  Two individually compatible identification doctrines can become jointly
incompatible by completing a path across a conflict edge.
-/

def finiteObserverRespects {P K : Type*}
    (R : P → P → Prop) (kappa : P → K) : Prop :=
  ∀ x y, R x y → kappa x = kappa y

/-- A map respects supplied identifications exactly when it respects their equivalence closure. -/
theorem finiteObserverRespects_eqvGen_iff
    {P K : Type*} (R : P → P → Prop) (kappa : P → K) :
    finiteObserverRespects (Relation.EqvGen R) kappa ↔
      finiteObserverRespects R kappa := by
  constructor
  · intro h x y hxy
    exact h x y (Relation.EqvGen.rel x y hxy)
  · intro h x y hxy
    induction hxy with
    | rel x y hxy => exact h x y hxy
    | refl x => rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ hxy hyz => exact hxy.trans hyz

def finiteIdentificationConflictCompatible {J P : Type*}
    (R : P → P → Prop) (u v : J → P → ℝ) : Prop :=
  ∀ x y, Relation.EqvGen R x y → ¬ finiteTaskConflict u v x y

/-- Any respecting lossless observer forces compatibility of mandatory and forbidden pairs. -/
theorem finiteIdentificationConflictCompatible_of_respecting_lossless
    {J P K : Type*} [Fintype P] [Fintype K]
    [DecidableEq P] [DecidableEq K]
    (R : P → P → Prop) (u v : J → P → ℝ) (kappa : P → K)
    (hrespect : finiteObserverRespects R kappa)
    (hlossless : finiteTaskLossless u v kappa) :
    finiteIdentificationConflictCompatible R u v := by
  have hclosure : finiteObserverRespects (Relation.EqvGen R) kappa :=
    (finiteObserverRespects_eqvGen_iff R kappa).2 hrespect
  have hproper := (finiteTaskLossless_iff_properColoring u v kappa).1 hlossless
  intro x y hxy hconflict
  exact hproper x y hconflict (hclosure x y hxy)

/-- The canonical quotient by mandatory identifications is lossless exactly under compatibility. -/
theorem finiteQuotientTaskLossless_iff_compatible
    {J P : Type*} [Fintype P] [DecidableEq P]
    (R : P → P → Prop) (u v : J → P → ℝ) :
    letI : DecidableEq (Quot R) := Classical.decEq _
    letI : Fintype (Quot R) := Fintype.ofSurjective (Quot.mk R) Quot.exists_rep
    finiteTaskLossless u v (Quot.mk R) ↔
      finiteIdentificationConflictCompatible R u v := by
  letI : DecidableEq (Quot R) := Classical.decEq _
  letI : Fintype (Quot R) := Fintype.ofSurjective (Quot.mk R) Quot.exists_rep
  rw [finiteTaskLossless_iff_properColoring]
  constructor
  · intro hproper x y hxy hconflict
    exact hproper x y hconflict (Quot.eqvGen_sound hxy)
  · intro hcompatible x y hconflict hsame
    exact hcompatible x y (Quot.eqvGen_exact hsame) hconflict

def finiteRespectingTaskObserverWidthAtMost {J P : Type*} [Fintype P]
    (R : P → P → Prop) (u v : J → P → ℝ) (q : ℕ) : Prop :=
  ∃ kappa : P → Fin q,
    finiteObserverRespects R kappa ∧ finiteTaskLossless u v kappa

def finiteQuotientConflictColorable {J P : Type*}
    (R : P → P → Prop) (u v : J → P → ℝ) (q : ℕ) : Prop :=
  ∃ color : Quot R → Fin q,
    ∀ x y, finiteTaskConflict u v x y → color (Quot.mk R x) ≠ color (Quot.mk R y)

/-- After mandatory contraction, finite observer width is quotient-conflict chromatic width. -/
theorem finiteRespectingTaskObserverWidthAtMost_iff_quotientConflictColorable
    {J P : Type*} [Fintype P] [DecidableEq P]
    (R : P → P → Prop) (u v : J → P → ℝ) (q : ℕ) :
    finiteRespectingTaskObserverWidthAtMost R u v q ↔
      finiteQuotientConflictColorable R u v q := by
  constructor
  · rintro ⟨kappa, hrespect, hlossless⟩
    refine ⟨Quot.lift kappa hrespect, ?_⟩
    intro x y hconflict
    exact (finiteTaskLossless_iff_properColoring u v kappa).1 hlossless x y hconflict
  · rintro ⟨color, hcolor⟩
    refine ⟨fun x => color (Quot.mk R x), ?_, ?_⟩
    · intro x y hxy
      exact congrArg color (Quot.sound hxy)
    · apply (finiteTaskLossless_iff_properColoring _ _ _).2
      exact hcolor

/-- A conflict edge in the generated identification closure forces strict TV loss. -/
theorem generatedIdentificationConflict_forces_strict_loss
    {J P K : Type*} [Fintype P] [Fintype K]
    [DecidableEq P] [DecidableEq K]
    (R : P → P → Prop) (u v : J → P → ℝ) (kappa : P → K)
    {j : J} {x y : P}
    (hrespect : finiteObserverRespects R kappa)
    (hclosure : Relation.EqvGen R x y)
    (hneg : (u j x - v j x) * (u j y - v j y) < 0) :
    finiteProfileTotalVariation
        (fun k => finiteSignedFiberMass (u j) kappa k)
        (fun k => finiteSignedFiberMass (v j) kappa k) <
      finiteProfileTotalVariation (u j) (v j) := by
  have hrespectClosure : finiteObserverRespects (Relation.EqvGen R) kappa :=
    (finiteObserverRespects_eqvGen_iff R kappa).2 hrespect
  exact finiteTaskConflict_collapsed_strict_loss u v kappa hneg
    (hrespectClosure x y hclosure)

def finiteRelationUnion {P : Type*}
    (R S : P → P → Prop) (x y : P) : Prop :=
  R x y ∨ S x y

/-- A generated path using two identification doctrines forces loss for every joint observer. -/
theorem joinedIdentificationConflict_forces_strict_loss
    {J P K : Type*} [Fintype P] [Fintype K]
    [DecidableEq P] [DecidableEq K]
    (R S : P → P → Prop) (u v : J → P → ℝ) (kappa : P → K)
    {j : J} {x y : P}
    (hrespectR : finiteObserverRespects R kappa)
    (hrespectS : finiteObserverRespects S kappa)
    (hclosure : Relation.EqvGen (finiteRelationUnion R S) x y)
    (hneg : (u j x - v j x) * (u j y - v j y) < 0) :
    finiteProfileTotalVariation
        (fun k => finiteSignedFiberMass (u j) kappa k)
        (fun k => finiteSignedFiberMass (v j) kappa k) <
      finiteProfileTotalVariation (u j) (v j) := by
  apply generatedIdentificationConflict_forces_strict_loss
      (finiteRelationUnion R S) u v kappa
  · intro a b hab
    exact hab.elim (hrespectR a b) (hrespectS a b)
  · exact hclosure
  · exact hneg

/-! ## Minimal three-doctrine witness -/

def threePointLeftIdentification (x y : Fin 3) : Prop :=
  x = 0 ∧ y = 1

def threePointRightIdentification (x y : Fin 3) : Prop :=
  x = 1 ∧ y = 2

def threePointLeftProfile (_ : Unit) (x : Fin 3) : ℝ :=
  if x = 0 then 1 else 0

def threePointRightProfile (_ : Unit) (x : Fin 3) : ℝ :=
  if x = 2 then 1 else 0

def threePointLeftObserver (x : Fin 3) : Fin 2 :=
  if x = 2 then 1 else 0

def threePointRightObserver (x : Fin 3) : Fin 2 :=
  if x = 0 then 0 else 1

theorem threePointConflict_iff (x y : Fin 3) :
    finiteTaskConflict threePointLeftProfile threePointRightProfile x y ↔
      (x = 0 ∧ y = 2) ∨ (x = 2 ∧ y = 0) := by
  fin_cases x <;> fin_cases y <;>
    simp [finiteTaskConflict, threePointLeftProfile, threePointRightProfile]

theorem threePointLeftObserver_respects :
    finiteObserverRespects threePointLeftIdentification threePointLeftObserver := by
  rintro x y ⟨rfl, rfl⟩
  rfl

theorem threePointRightObserver_respects :
    finiteObserverRespects threePointRightIdentification threePointRightObserver := by
  rintro x y ⟨rfl, rfl⟩
  rfl

theorem threePointLeftObserver_lossless :
    finiteTaskLossless threePointLeftProfile threePointRightProfile threePointLeftObserver := by
  apply (finiteTaskLossless_iff_properColoring _ _ _).2
  intro x y hconflict
  rw [threePointConflict_iff] at hconflict
  rcases hconflict with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    decide

theorem threePointRightObserver_lossless :
    finiteTaskLossless threePointLeftProfile threePointRightProfile threePointRightObserver := by
  apply (finiteTaskLossless_iff_properColoring _ _ _).2
  intro x y hconflict
  rw [threePointConflict_iff] at hconflict
  rcases hconflict with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    decide

theorem threePoint_joinedClosure_zero_two :
    Relation.EqvGen
        (finiteRelationUnion threePointLeftIdentification threePointRightIdentification)
        (0 : Fin 3) (2 : Fin 3) := by
  exact Relation.EqvGen.trans 0 1 2
    (Relation.EqvGen.rel 0 1 (Or.inl ⟨rfl, rfl⟩))
    (Relation.EqvGen.rel 1 2 (Or.inr ⟨rfl, rfl⟩))

/-- Every observer respecting both individually harmless identifications loses TV strictly. -/
theorem threePoint_jointObserver_strict_loss
    {K : Type*} [Fintype K] [DecidableEq K]
    (kappa : Fin 3 → K)
    (hleft : finiteObserverRespects threePointLeftIdentification kappa)
    (hright : finiteObserverRespects threePointRightIdentification kappa) :
    finiteProfileTotalVariation
        (fun k => finiteSignedFiberMass (threePointLeftProfile ()) kappa k)
        (fun k => finiteSignedFiberMass (threePointRightProfile ()) kappa k) <
      finiteProfileTotalVariation (threePointLeftProfile ()) (threePointRightProfile ()) := by
  apply joinedIdentificationConflict_forces_strict_loss
      threePointLeftIdentification threePointRightIdentification
      threePointLeftProfile threePointRightProfile kappa
      hleft hright threePoint_joinedClosure_zero_two
  simp [threePointLeftProfile, threePointRightProfile,
    show (0 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 0 by decide]

/-- Pairwise realizability does not imply joint realizability for three doctrines. -/
theorem threePoint_no_joint_respecting_lossless_observer
    {K : Type*} [Fintype K] [DecidableEq K] :
    ¬ ∃ kappa : Fin 3 → K,
        finiteObserverRespects threePointLeftIdentification kappa ∧
        finiteObserverRespects threePointRightIdentification kappa ∧
        finiteTaskLossless threePointLeftProfile threePointRightProfile kappa := by
  rintro ⟨kappa, hleft, hright, hlossless⟩
  have hstrict := threePoint_jointObserver_strict_loss kappa hleft hright
  exact (ne_of_lt hstrict) (hlossless ())

/-- Capstone: saturation, compatibility, and strict critical-triple response. -/
theorem identificationConflictInterference_mechanism_closed
    {J P K : Type*} [Fintype P] [Fintype K]
    [DecidableEq P] [DecidableEq K]
    (R : P → P → Prop) (u v : J → P → ℝ) (kappa : P → K)
    (hrespect : finiteObserverRespects R kappa)
    (hlossless : finiteTaskLossless u v kappa) :
    finiteObserverRespects (Relation.EqvGen R) kappa ∧
      finiteIdentificationConflictCompatible R u v := by
  exact ⟨(finiteObserverRespects_eqvGen_iff R kappa).2 hrespect,
    finiteIdentificationConflictCompatible_of_respecting_lossless
      R u v kappa hrespect hlossless⟩

end

end HTGeometry
