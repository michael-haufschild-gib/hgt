import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.GroupTheory.Index

/-!
# Nilpotent counts under reduction

A ring map with nilpotent kernel detects nilpotence. If it is surjective,
every nilpotent element downstairs has one full additive-kernel fiber of
nilpotent lifts. The resulting cardinal identity preserves the nilpotent
proportion whenever both rings are finite.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting

variable {R S : Type*} [Ring R] [Ring S]

/-- A predicate pulled back through a surjective additive map has one kernel-sized fiber
over each element satisfying the predicate downstairs. -/
def additivePredicateReductionEquiv (f : R →+ S) (hf : Function.Surjective f)
    (P : R → Prop) (Q : S → Prop) (h : ∀ x, P x ↔ Q (f x)) :
    {x : R // P x} ≃ ({y : S // Q y} × f.ker) := by
  let e := Equiv.sigmaSubtypeFiberEquivSubtype f h
  let ef (y : {y : S // Q y}) : {x : R // f x = y.1} ≃ f.ker := by
    let x := (hf y.1).choose
    have hx : f x = y.1 := (hf y.1).choose_spec
    simpa only [Set.preimage, Set.mem_singleton_iff, hx] using f.fiberEquivKer x
  exact e.symm.trans ((Equiv.sigmaCongrRight ef).trans (Equiv.sigmaEquivProd _ _))

/-- Pullback of any predicate preserves its counting proportion. -/
theorem card_additivePredicate_reduction_mul_card (f : R →+ S)
    (hf : Function.Surjective f) (P : R → Prop) (Q : S → Prop)
    (h : ∀ x, P x ↔ Q (f x)) :
    Nat.card {x : R // P x} * Nat.card S = Nat.card {y : S // Q y} * Nat.card R := by
  have hc := AddSubgroup.card_mul_index f.ker
  rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hf,
    Nat.card_congr (AddSubgroup.topEquiv : (⊤ : AddSubgroup S) ≃+ S).toEquiv] at hc
  rw [Nat.card_congr (additivePredicateReductionEquiv f hf P Q h),
    Nat.card_prod, mul_assoc, hc]

/-- A nilpotent image lifts to a nilpotent element when the kernel consists of nilpotents. -/
theorem isNilpotent_map_iff_of_nilpotent_kernel (f : R →+* S)
    (hker : ∀ x : R, f x = 0 → IsNilpotent x) (x : R) :
    IsNilpotent (f x) ↔ IsNilpotent x := by
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨m, hm⟩ := hker (x ^ n) (by rwa [map_pow])
    exact ⟨n * m, by rwa [pow_mul]⟩
  · exact fun h => h.map f

/-- Nilpotent lifts are parameterized by a nilpotent residue and an additive-kernel element. -/
def nilpotentReductionEquiv (f : R →+* S) (hf : Function.Surjective f)
    (hker : ∀ x : R, f x = 0 → IsNilpotent x) :
    {x : R // IsNilpotent x} ≃ ({y : S // IsNilpotent y} × f.toAddMonoidHom.ker) := by
  let e := Equiv.sigmaSubtypeFiberEquivSubtype f
    (fun x => (isNilpotent_map_iff_of_nilpotent_kernel f hker x).symm)
  let ef (y : {y : S // IsNilpotent y}) :
      {x : R // f x = y.1} ≃ f.toAddMonoidHom.ker := by
    let x := (hf y.1).choose
    have hx : f x = y.1 := (hf y.1).choose_spec
    simpa only [Set.preimage, Set.mem_singleton_iff, hx] using
      f.toAddMonoidHom.fiberEquivKer x
  exact e.symm.trans ((Equiv.sigmaCongrRight ef).trans (Equiv.sigmaEquivProd _ _))

/-- Each nilpotent residue has exactly one kernel-sized fiber of nilpotent lifts. -/
theorem card_nilpotent_reduction (f : R →+* S) (hf : Function.Surjective f)
    (hker : ∀ x : R, f x = 0 → IsNilpotent x) :
    Nat.card {x : R // IsNilpotent x} =
      Nat.card {y : S // IsNilpotent y} * Nat.card f.toAddMonoidHom.ker := by
  rw [Nat.card_congr (nilpotentReductionEquiv f hf hker), Nat.card_prod]

/-- Cross multiplication expresses preservation of the nilpotent proportion without division. -/
theorem card_nilpotent_reduction_mul_card (f : R →+* S) (hf : Function.Surjective f)
    (hker : ∀ x : R, f x = 0 → IsNilpotent x) :
    Nat.card {x : R // IsNilpotent x} * Nat.card S =
      Nat.card {y : S // IsNilpotent y} * Nat.card R :=
  card_additivePredicate_reduction_mul_card f.toAddMonoidHom hf IsNilpotent IsNilpotent
    (fun x => (isNilpotent_map_iff_of_nilpotent_kernel f hker x).symm)

#print axioms nilpotentReductionEquiv
#print axioms card_nilpotent_reduction_mul_card

end GaloisForLFunctions.RepresentationLifting
