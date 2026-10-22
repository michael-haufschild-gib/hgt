import GaloisForLFunctions.RHTower.Deninger.DeningerPrimeResidueSheaf
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Stalks of the direct sum of skyscrapers

The sheaf `⨁_{p ∈ P} i_{p,*} ℤ` has stalk `ℤ` at each closed point of `P` and zero elsewhere: at a
prime of `P` every neighbourhood contains that prime, so evaluation there identifies the colimit
with `ℤ`; at any other point some neighbourhood misses every prime of `P`, so the sections there
already vanish.  This is the statement that the sheaf is the extension by zero of `ℤ` from the
closed points of `P`.

* `deningerClosedPt_isClosed` : the closed points are closed.
* `deningerResidueStalkDesc` : evaluation at a prime, on the stalk.
* `deningerResidueStalk_bijective` : it is bijective, so the stalk at a prime of `P` is `ℤ`.
* `deningerResidueStalk_eq_zero` : the stalk vanishes away from the primes of `P`.
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopCat

/-- **A closed point of the arithmetic curve is closed**: the ideal it cuts out is maximal. -/
theorem deningerClosedPt_isClosed (p : Nat.Primes) :
    IsClosed ({deningerClosedPt p} : Set deningerArithBase) := by
  have hprime : Prime ((p : ℕ) : ℤ) := by
    rw [Int.prime_iff_natAbs_prime]
    simpa using p.2
  have hmax : (deningerClosedPt p).asIdeal.IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hprime.irreducible
  exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal (deningerClosedPt p)).2 hmax

theorem deningerClosedPts_isClosed (P : Finset Nat.Primes) :
    IsClosed (⋃ p ∈ (P : Set Nat.Primes), ({deningerClosedPt p} : Set deningerArithBase)) :=
  Set.Finite.isClosed_biUnion P.finite_toSet (fun p _ => deningerClosedPt_isClosed p)

/-- The open set of points that are not closed points of `P`. -/
def deningerAvoid (P : Finset Nat.Primes) : Opens deningerArithBase :=
  ⟨(⋃ p ∈ (P : Set Nat.Primes), ({deningerClosedPt p} : Set deningerArithBase))ᶜ,
    (deningerClosedPts_isClosed P).isOpen_compl⟩

theorem deningerAvoid_mem {P : Finset Nat.Primes} {z : deningerArithBase} :
    z ∈ deningerAvoid P ↔ ∀ p ∈ P, z ≠ deningerClosedPt p := by
  simp [deningerAvoid]

theorem deningerAvoid_idx_isEmpty (P : Finset Nat.Primes) (V : Opens deningerArithBase)
    (hV : V ≤ deningerAvoid P) : IsEmpty (deningerLogIdx P V) :=
  ⟨fun i => (deningerAvoid_mem.1 (hV i.2.2)) (i : Nat.Primes) i.2.1 rfl⟩

section Stalk

variable (P : Finset Nat.Primes) {p : Nat.Primes} (hp : p ∈ P)

/-- Evaluation of a residue section at a prime of `P`, as a cocone on the stalk diagram. -/
def deningerResidueEvalCocone :
    Cocone ((OpenNhds.inclusion (deningerClosedPt p)).op ⋙ deningerResidueAddPresheaf P ℤ) where
  pt := AddCommGrpCat.of ℤ
  ι :=
    { app := fun U => AddCommGrpCat.ofHom
        { toFun := fun f => f ⟨p, hp, U.unop.2⟩
          map_zero' := rfl
          map_add' := fun _ _ => rfl }
      naturality := fun _ _ _ => rfl }

/-- Evaluation at a prime of `P`, on the stalk. -/
noncomputable def deningerResidueStalkDesc :
    (deningerResidueAddPresheaf P ℤ).stalk (deningerClosedPt p) ⟶ AddCommGrpCat.of ℤ :=
  colimit.desc _ (deningerResidueEvalCocone P hp)

theorem deningerResidueStalkDesc_germ (U : Opens deningerArithBase)
    (hU : deningerClosedPt p ∈ U) (s : deningerLogIdx P U → ℤ) :
    ConcreteCategory.hom (deningerResidueStalkDesc P hp)
        (ConcreteCategory.hom ((deningerResidueAddPresheaf P ℤ).germ U _ hU) s) =
      s ⟨p, hp, hU⟩ := by
  have h := colimit.ι_desc (deningerResidueEvalCocone P hp) (op ⟨U, hU⟩)
  exact congrFun (congrArg (fun w => (ConcreteCategory.hom w : _ → ℤ)) h) s

/-- **The stalk of the residue sheaf at a prime of `P` is `ℤ`.** -/
theorem deningerResidueStalk_bijective :
    Function.Bijective (ConcreteCategory.hom (deningerResidueStalkDesc P hp)) := by
  classical
  constructor
  · refine (injective_iff_map_eq_zero _).2 (fun t ht => ?_)
    obtain ⟨U, hU, s, hs⟩ := (deningerResidueAddPresheaf P ℤ).exists_germ_eq t
    have hval : s ⟨p, hp, hU⟩ = 0 := by
      rw [← deningerResidueStalkDesc_germ P hp U hU s, hs]
      exact ht
    have hVp : deningerClosedPt p ∈ U ⊓ deningerAvoid (P.erase p) := by
      refine ⟨hU, deningerAvoid_mem.2 (fun q hq hqe => ?_)⟩
      exact (Finset.mem_erase.1 hq).1 (deningerClosedPt_injective hqe).symm
    have hle : U ⊓ deningerAvoid (P.erase p) ≤ U := inf_le_left
    have hres : deningerResidueRes hle s = 0 := by
      funext i
      have h1 : (i : Nat.Primes) = p := by
        by_contra hne
        exact (deningerAvoid_mem.1 i.2.2.2) (i : Nat.Primes)
          (Finset.mem_erase.2 ⟨hne, i.2.1⟩) rfl
      have h2 : (⟨(i : Nat.Primes), i.2.1, hle i.2.2⟩ : deningerLogIdx P U) = ⟨p, hp, hU⟩ :=
        Subtype.ext h1
      show s ⟨(i : Nat.Primes), i.2.1, hle i.2.2⟩ = 0
      rw [h2]
      exact hval
    have hgerm := (deningerResidueAddPresheaf P ℤ).germ_res (homOfLE hle)
      (deningerClosedPt p) hVp
    have hgerm' := congrFun (congrArg (fun w => (ConcreteCategory.hom w :
      (deningerLogIdx P U → ℤ) → _)) hgerm) s
    rw [← hs, ← hgerm']
    show ConcreteCategory.hom ((deningerResidueAddPresheaf P ℤ).germ _ _ hVp)
      (deningerResidueRes hle s) = 0
    rw [hres]
    exact map_zero _
  · intro n
    refine ⟨ConcreteCategory.hom ((deningerResidueAddPresheaf P ℤ).germ ⊤ _ trivial)
      (fun _ => n), ?_⟩
    exact deningerResidueStalkDesc_germ P hp ⊤ trivial (fun _ => n)

end Stalk

/-- **The stalk of the residue sheaf vanishes away from the primes of `P`.** -/
theorem deningerResidueStalk_eq_zero (P : Finset Nat.Primes) (z : deningerArithBase)
    (hz : ∀ p ∈ P, z ≠ deningerClosedPt p)
    (t : ToType ((deningerResidueAddPresheaf P ℤ).stalk z)) : t = 0 := by
  classical
  obtain ⟨U, hU, s, hs⟩ := (deningerResidueAddPresheaf P ℤ).exists_germ_eq t
  have hVz : z ∈ U ⊓ deningerAvoid P := ⟨hU, deningerAvoid_mem.2 hz⟩
  have hle : U ⊓ deningerAvoid P ≤ U := inf_le_left
  haveI : IsEmpty (deningerLogIdx P (U ⊓ deningerAvoid P)) :=
    deningerAvoid_idx_isEmpty P _ inf_le_right
  have hres : deningerResidueRes hle s = 0 := funext (fun i => isEmptyElim i)
  have hgerm := (deningerResidueAddPresheaf P ℤ).germ_res (homOfLE hle) z hVz
  have hgerm' := congrFun (congrArg (fun w => (ConcreteCategory.hom w :
    (deningerLogIdx P U → ℤ) → _)) hgerm) s
  rw [← hs, ← hgerm']
  show ConcreteCategory.hom ((deningerResidueAddPresheaf P ℤ).germ _ _ hVz)
    (deningerResidueRes hle s) = 0
  rw [hres]
  exact map_zero _

/-- The stalk of the residue sheaf away from the primes of `P` is the zero group. -/
theorem deningerResidueStalk_isZero (P : Finset Nat.Primes) (z : deningerArithBase)
    (hz : ∀ p ∈ P, z ≠ deningerClosedPt p) :
    IsZero ((deningerResidueAddPresheaf P ℤ).stalk z) := by
  rw [IsZero.iff_id_eq_zero]
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun t => ?_)
  exact deningerResidueStalk_eq_zero P z hz t

end RHTower
