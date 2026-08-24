import GaloisForLFunctions.HTGeometry.ConstitutiveNonabelianRecoveryHolonomy
import GaloisForLFunctions.HTGeometry.ClockReadoutWitnesses

open Equiv

/-!
# Nonabelian Hasse classification of recovery ledgers

A primitive permutation cycle is treated as a local place.  Its invariant is the conjugacy class
of group-valued holonomy.  The resulting packet, indexed once per cycle, completely separates
global gauge classes.  Thus inequivalence always has a concrete cycle-place obstruction, and the
global gauge quotient embeds into the space of all local conjugacy packets.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {S G : Type*} [Fintype S] [Group G]

/-- One conjugacy-class-valued holonomy coordinate for each primitive permutation cycle. -/
def groupPrimitiveHolonomyHassePacket (T : Perm S) (c : S → G) :
    Quotient (Perm.SameCycle.setoid T) → ConjClasses G :=
  fun q => Quotient.liftOn q
    (fun s => ConjClasses.mk (groupCycleHolonomy T c s)) (by
      intro s t hst
      rw [ConjClasses.mk_eq_mk_iff_isConj]
      exact groupCycleHolonomy_isConj_of_sameCycle T c hst)

@[simp] theorem groupPrimitiveHolonomyHassePacket_mk (T : Perm S) (c : S → G)
    (s : S) :
    groupPrimitiveHolonomyHassePacket T c
        (Quotient.mk (Perm.SameCycle.setoid T) s) =
      ConjClasses.mk (groupCycleHolonomy T c s) := rfl

/-- **Nonabelian Hasse classification.**  Two global ledgers are gauge equivalent exactly when
their conjugacy-class holonomy coordinates agree at every primitive cycle-place. -/
theorem groupGaugeEquivalent_iff_primitiveHolonomyHassePacket_eq
    (T : Perm S) (c d : S → G) :
    GroupGaugeEquivalent T c d ↔
      groupPrimitiveHolonomyHassePacket T c =
        groupPrimitiveHolonomyHassePacket T d := by
  constructor
  · intro hgauge
    have hlocal := (groupGaugeEquivalent_iff_cycleHolonomy_isConj T c d).mp hgauge
    funext q
    induction q using Quotient.inductionOn with
    | _ s =>
        simp only [groupPrimitiveHolonomyHassePacket_mk]
        rw [ConjClasses.mk_eq_mk_iff_isConj]
        exact hlocal s
  · intro hpacket
    apply (groupGaugeEquivalent_iff_cycleHolonomy_isConj T c d).mpr
    intro s
    have hs := congrFun hpacket (Quotient.mk (Perm.SameCycle.setoid T) s)
    simpa only [groupPrimitiveHolonomyHassePacket_mk,
      ConjClasses.mk_eq_mk_iff_isConj] using hs

/-- Failure of global gauge equivalence is witnessed at one primitive cycle-place. -/
theorem not_groupGaugeEquivalent_iff_exists_primitiveHolonomy_obstruction
    (T : Perm S) (c d : S → G) :
    ¬ GroupGaugeEquivalent T c d ↔
      ∃ q : Quotient (Perm.SameCycle.setoid T),
        groupPrimitiveHolonomyHassePacket T c q ≠
          groupPrimitiveHolonomyHassePacket T d q := by
  rw [groupGaugeEquivalent_iff_primitiveHolonomyHassePacket_eq]
  constructor
  · intro hne
    by_contra hno
    apply hne
    funext q
    by_contra hq
    exact hno ⟨q, hq⟩
  · rintro ⟨q, hq⟩ heq
    exact hq (congrFun heq q)

/-- Gauge equivalence as the equivalence relation induced by the complete local packet. -/
def groupGaugeSetoid (T : Perm S) : Setoid (S → G) where
  r := GroupGaugeEquivalent T
  iseqv := {
    refl := fun c =>
      (groupGaugeEquivalent_iff_primitiveHolonomyHassePacket_eq T c c).mpr rfl
    symm := fun {c d} h =>
      (groupGaugeEquivalent_iff_primitiveHolonomyHassePacket_eq T d c).mpr
        ((groupGaugeEquivalent_iff_primitiveHolonomyHassePacket_eq T c d).mp h).symm
    trans := fun {c d e} hcd hde =>
      (groupGaugeEquivalent_iff_primitiveHolonomyHassePacket_eq T c e).mpr
        (((groupGaugeEquivalent_iff_primitiveHolonomyHassePacket_eq T c d).mp hcd).trans
          ((groupGaugeEquivalent_iff_primitiveHolonomyHassePacket_eq T d e).mp hde))
  }

/-- Global group-valued ledgers modulo vertex gauge. -/
def GroupGaugeClasses (T : Perm S) (G : Type*) [Group G] :=
  Quotient (groupGaugeSetoid (G := G) T)

/-- The Hasse map from global gauge classes to primitive-cycle conjugacy packets. -/
def groupGaugeClassHasseMap (T : Perm S) :
    GroupGaugeClasses T G →
      (Quotient (Perm.SameCycle.setoid T) → ConjClasses G) :=
  Quotient.lift (groupPrimitiveHolonomyHassePacket T)
    (fun c d h =>
      (groupGaugeEquivalent_iff_primitiveHolonomyHassePacket_eq T c d).mp h)

@[simp] theorem groupGaugeClassHasseMap_mk (T : Perm S) (c : S → G) :
    groupGaugeClassHasseMap T
        (Quotient.mk (groupGaugeSetoid (G := G) T) c) =
      groupPrimitiveHolonomyHassePacket T c := rfl

/-- Primitive-cycle conjugacy data separate global nonabelian gauge classes. -/
theorem groupGaugeClassHasseMap_injective (T : Perm S) :
    Function.Injective (groupGaugeClassHasseMap (G := G) T) := by
  intro qc qd h
  induction qc using Quotient.inductionOn with
  | _ c =>
      induction qd using Quotient.inductionOn with
      | _ d =>
          apply Quotient.sound
          change GroupGaugeEquivalent T c d
          apply (groupGaugeEquivalent_iff_primitiveHolonomyHassePacket_eq T c d).mpr
          exact h

end

end GaloisForLFunctions.HTGeometry
