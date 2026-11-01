import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerHyperbolicLength
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerPrimitiveOrientation

/-! Matrix inversion on primitive Gauss pair cycles and the exact one-or-two
fibers obtained by forgetting inverse orientation. -/

open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerCoding MayerHyperbolic MayerGaussCoding MayerPrimitiveCycles MayerCycleIndex
open MayerPairMultiplier MayerOrbitWords MayerOrientation MayerHyperbolicLength
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerInverseCycles

local instance : DecidableEq Orbit := Classical.decEq _

private abbrev PairWord := {u : List (ℕ × ℕ) // Primitive u}

private theorem reversedPairs_twice (u : List (ℕ × ℕ)) :
    reversedPairs (reversedPairs u) = u := by
  simp [reversedPairs,← List.map_reverse,List.map_map,Function.comp_def]

private theorem reversedPairs_append (u v : List (ℕ × ℕ)) :
    reversedPairs (u++v) = reversedPairs v++reversedPairs u := by
  simp only [reversedPairs,List.reverse_append,List.map_append]

private theorem reversedPairs_wordPower (u : List (ℕ × ℕ)) (n : ℕ) :
    reversedPairs (wordPower u n) = wordPower (reversedPairs u) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change reversedPairs (u++wordPower u n) = wordPower (reversedPairs u) (n+1)
    rw [reversedPairs_append,ih,wordPower_add]
    simp only [wordPower,List.append_nil]

private theorem primitive_reversedPairs {u : List (ℕ × ℕ)} (hu : Primitive u) :
    Primitive (reversedPairs u) := by
  refine ⟨?_,?_⟩
  · intro h
    apply hu.1
    simpa only [reversedPairs_twice,show reversedPairs []=[] from rfl] using
      congrArg reversedPairs h
  · intro v n hn he
    apply hu.2 (reversedPairs v) n hn
    simpa only [reversedPairs_twice,reversedPairs_wordPower] using congrArg reversedPairs he

private def inverseWord (u : PairWord) : PairWord :=
  ⟨reversedPairs u.val,primitive_reversedPairs u.property⟩

private theorem inverseWord_twice (u : PairWord) : inverseWord (inverseWord u)=u :=
  Subtype.ext (reversedPairs_twice u.val)

private theorem inverseWord_rotated {u v : PairWord}
    (h : List.IsRotated u.val v.val) :
    List.IsRotated (inverseWord u).val (inverseWord v).val :=
  h.reverse.map (fun p => (p.2,p.1))

/-- Inversion of the actual primitive integral matrix class. -/
def inverseCycle : Orbit → Orbit :=
  Quotient.map inverseWord (fun _ _ h => inverseWord_rotated h)

theorem inverseCycle_involutive : Function.Involutive inverseCycle := by
  intro c
  refine Quotient.inductionOn c (fun u => ?_)
  change Quotient.mk (primitiveSetoid (ℕ × ℕ)) (inverseWord (inverseWord u)) =
    Quotient.mk (primitiveSetoid (ℕ × ℕ)) u
  rw [inverseWord_twice]

private theorem inverseCycle_representative (c : Orbit) :
    inverseCycle c = Quotient.mk (primitiveSetoid (ℕ × ℕ)) (inverseWord (representative c)) :=
  (congrArg inverseCycle (Quotient.out_eq c)).symm

theorem inverseCycle_eq_iff_rotated (c d : Orbit) :
    inverseCycle c=d ↔
      List.IsRotated (reversedPairs (representative c).val) (representative d).val := by
  constructor
  · intro h
    exact Quotient.exact ((inverseCycle_representative c).symm.trans
      (h.trans (Quotient.out_eq d).symm))
  · intro h
    exact (inverseCycle_representative c).trans ((Quotient.sound h).trans (Quotient.out_eq d))

private theorem rotated_iff_split (u v : List (ℕ × ℕ)) :
    List.IsRotated u v ↔ ∃ a b : List (ℕ × ℕ), u=a++b ∧ v=b++a := by
  constructor
  · intro h
    obtain ⟨n,hn,he⟩ := List.isRotated_iff_mod.mp h
    refine ⟨u.take n,u.drop n,(List.take_append_drop n u).symm,?_⟩
    rw [List.rotate_eq_drop_append_take hn] at he
    exact he.symm
  · rintro ⟨a,b,rfl,rfl⟩
    exact List.isRotated_append

/-- The cycle involution is precisely inverse conjugacy by an integral determinant-one matrix. -/
theorem inverseCycle_eq_iff_inverse_conjugacy (c d : Orbit) :
    inverseCycle c=d ↔
      ∃ C : IntMatrix, C.det=1 ∧
        C*integralInverse (actualPairedMatrix (representative c).val) =
          actualPairedMatrix (representative d).val*C := by
  rw [inverseCycle_eq_iff_rotated,actualPairedMatrix_inverse_conjugacy_iff _ _
    (representative c).property.1 (representative d).property.1]
  exact rotated_iff_split _ _

private theorem representative_rotated (u : PairWord) :
    List.IsRotated (representative (Quotient.mk (primitiveSetoid (ℕ × ℕ)) u)).val u.val :=
  Quotient.exact (Quotient.out_eq (Quotient.mk (primitiveSetoid (ℕ × ℕ)) u))

private theorem cycleLength_mk (u : PairWord) :
    cycleLength (Quotient.mk (primitiveSetoid (ℕ × ℕ)) u) = u.val.length := by
  obtain ⟨k,hk⟩ := representative_rotated u
  simpa only [cycleLength,List.length_rotate] using congrArg List.length hk

private theorem multiplier_mk (u : PairWord) :
    multiplier (Quotient.mk (primitiveSetoid (ℕ × ℕ)) u) = pairMultiplier u.val := by
  obtain ⟨k,hk⟩ := representative_rotated u
  change pairMultiplier (representative (Quotient.mk (primitiveSetoid (ℕ × ℕ)) u)).val = _
  calc
    _ = pairMultiplier ((representative (Quotient.mk (primitiveSetoid (ℕ × ℕ)) u)).val.rotate k) :=
      (pairMultiplier_rotate _ k).symm
    _ = pairMultiplier u.val := congrArg pairMultiplier hk

theorem cycleLength_inverseCycle (c : Orbit) : cycleLength (inverseCycle c)=cycleLength c := by
  refine Quotient.inductionOn c (fun u => ?_)
  change cycleLength (Quotient.mk (primitiveSetoid (ℕ × ℕ)) (inverseWord u)) =
    cycleLength (Quotient.mk (primitiveSetoid (ℕ × ℕ)) u)
  rw [cycleLength_mk,cycleLength_mk]
  simp only [inverseWord,reversedPairs,List.length_map,List.length_reverse]

theorem multiplier_inverseCycle (c : Orbit) : multiplier (inverseCycle c)=multiplier c := by
  refine Quotient.inductionOn c (fun u => ?_)
  change multiplier (Quotient.mk (primitiveSetoid (ℕ × ℕ)) (inverseWord u)) =
    multiplier (Quotient.mk (primitiveSetoid (ℕ × ℕ)) u)
  rw [multiplier_mk,multiplier_mk]
  change pairMultiplier (reversedPairs u.val)=pairMultiplier u.val
  simp only [pairMultiplier,actualPairedMatrix_reversedPairs,Matrix.transpose_apply]

theorem orbitTranslationLength_inverseCycle (c : Orbit) :
    orbitTranslationLength (inverseCycle c)=orbitTranslationLength c := by
  rw [orbitTranslationLength_eq,orbitTranslationLength_eq,multiplier_inverseCycle]

private theorem primitive_singleton (a b : ℕ) : Primitive [(a,b)] := by
  refine ⟨by simp,?_⟩
  intro v n hn he
  have h := congrArg List.length he
  simp only [List.length_singleton,wordPower_length] at h
  by_cases hv : v.length=0
  · simp only [hv,Nat.mul_zero] at h
    omega
  · have hv1 : 1 ≤ v.length := by omega
    nlinarith [hn]

def singletonCycle (a b : ℕ) : Orbit :=
  Quotient.mk (primitiveSetoid (ℕ × ℕ)) ⟨[(a,b)],primitive_singleton a b⟩

/-- A one-pair primitive matrix class is conjugate to its inverse exactly when its digits agree. -/
theorem inverseCycle_singleton_eq_iff (a b : ℕ) :
    inverseCycle (singletonCycle a b)=singletonCycle a b ↔ a=b := by
  constructor
  · intro h
    have hr : List.IsRotated [(b,a)] [(a,b)] := Quotient.exact h
    have he := List.isRotated_singleton_iff.mp hr
    have hp : (b,a)=(a,b) := List.singleton_injective he
    exact congrArg Prod.snd hp
  · intro h
    subst b
    apply Quotient.sound
    exact List.IsRotated.refl [(a,a)]

private theorem inverse_eq_iff (c d : Orbit) : inverseCycle c=d ↔ c=inverseCycle d :=
  ⟨fun h => (inverseCycle_involutive c).symm.trans (congrArg inverseCycle h),
    fun h => (congrArg inverseCycle h).trans (inverseCycle_involutive d)⟩

/-- Identifying a primitive integral conjugacy class with its inverse. -/
def inverseSetoid : Setoid Orbit where
  r c d := c=d ∨ inverseCycle c=d
  iseqv := by
    refine ⟨fun _ => Or.inl rfl,?_,?_⟩
    · intro c d h
      rcases h with h | h
      · exact Or.inl h.symm
      · exact Or.inr ((congrArg inverseCycle h).symm.trans (inverseCycle_involutive c))
    · intro c d e hcd hde
      rcases hcd with rfl | hcd
      · exact hde
      rcases hde with hde | hde
      · exact Or.inr (hcd.trans hde)
      · exact Or.inl ((inverseCycle_involutive c).symm.trans
          ((congrArg inverseCycle hcd).trans hde))

def UnorientedOrbit := Quotient inverseSetoid

def unoriented (c : Orbit) : UnorientedOrbit := Quotient.mk inverseSetoid c

def chosenOrientation (u : UnorientedOrbit) : Orbit := Quotient.out u

theorem unoriented_chosenOrientation (u : UnorientedOrbit) : unoriented (chosenOrientation u)=u :=
  Quotient.out_eq u

theorem unoriented_eq_iff (c d : Orbit) : unoriented c=unoriented d ↔ c=d ∨ inverseCycle c=d := by
  change Quotient.mk inverseSetoid c=Quotient.mk inverseSetoid d ↔ inverseSetoid.r c d
  exact Quotient.eq_iff_equiv

theorem unoriented_inverseCycle (c : Orbit) : unoriented (inverseCycle c)=unoriented c :=
  Quotient.sound (Or.inr (inverseCycle_involutive c))

/-- The complete orientation fiber, with duplicate self-inverse classes removed. -/
def orientations (u : UnorientedOrbit) : Finset Orbit := by
  classical
  exact {chosenOrientation u,inverseCycle (chosenOrientation u)}

theorem mem_orientations (c : Orbit) (u : UnorientedOrbit) :
    c ∈ orientations u ↔ unoriented c=u := by
  classical
  simp only [orientations,Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro (rfl | rfl)
    · exact unoriented_chosenOrientation u
    · exact (unoriented_inverseCycle _).trans (unoriented_chosenOrientation u)
  · intro h
    have he := (unoriented_eq_iff c (chosenOrientation u)).mp
      (h.trans (unoriented_chosenOrientation u).symm)
    rcases he with he | he
    · exact Or.inl he
    · exact Or.inr ((inverse_eq_iff c (chosenOrientation u)).mp he)

theorem orientations_unoriented (c : Orbit) : orientations (unoriented c)={c,inverseCycle c} := by
  classical
  ext d
  rw [mem_orientations,unoriented_eq_iff,Finset.mem_insert,Finset.mem_singleton,inverse_eq_iff]

/-- Exact number of oriented primitive classes above an inverse-unoriented class. -/
def multiplicity (u : UnorientedOrbit) : ℕ := (orientations u).card

theorem multiplicity_unoriented (c : Orbit) :
    multiplicity (unoriented c) = if inverseCycle c=c then 1 else 2 := by
  classical
  rw [multiplicity,orientations_unoriented]
  by_cases h : inverseCycle c=c
  · simp [h]
  · have hc : c ≠ inverseCycle c := Ne.symm h
    simp [h,hc]

theorem multiplicity_one_or_two (u : UnorientedOrbit) : multiplicity u=1 ∨ multiplicity u=2 := by
  have h := multiplicity_unoriented (chosenOrientation u)
  rw [unoriented_chosenOrientation] at h
  split_ifs at h
  · exact Or.inl h
  · exact Or.inr h

theorem multiplicity_singleton (a b : ℕ) :
    multiplicity (unoriented (singletonCycle a b)) = if a=b then 1 else 2 := by
  simp only [multiplicity_unoriented,inverseCycle_singleton_eq_iff]

/-- Pair length descends through the inverse-class quotient. -/
def unorientedPairLength : UnorientedOrbit → ℕ :=
  Quotient.lift cycleLength (fun c d h => by
    rcases h with h | h
    · exact congrArg cycleLength h
    · exact (cycleLength_inverseCycle c).symm.trans (congrArg cycleLength h))

/-- Actual hyperbolic translation length descends through the inverse-class quotient. -/
def unorientedTranslationLength : UnorientedOrbit → ℝ :=
  Quotient.lift orbitTranslationLength (fun c d h => by
    rcases h with h | h
    · exact congrArg orbitTranslationLength h
    · exact (orbitTranslationLength_inverseCycle c).symm.trans
        (congrArg orbitTranslationLength h))

theorem unorientedPairLength_mk (c : Orbit) : unorientedPairLength (unoriented c)=cycleLength c := rfl

theorem unorientedTranslationLength_mk (c : Orbit) :
    unorientedTranslationLength (unoriented c)=orbitTranslationLength c := rfl

#print axioms inverseCycle_involutive
#print axioms inverseCycle_eq_iff_inverse_conjugacy
#print axioms cycleLength_inverseCycle
#print axioms multiplier_inverseCycle
#print axioms orbitTranslationLength_inverseCycle
#print axioms inverseCycle_singleton_eq_iff
#print axioms mem_orientations
#print axioms orientations_unoriented
#print axioms multiplicity_unoriented
#print axioms multiplicity_one_or_two
#print axioms multiplicity_singleton
#print axioms unorientedPairLength_mk
#print axioms unorientedTranslationLength_mk

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerInverseCycles
