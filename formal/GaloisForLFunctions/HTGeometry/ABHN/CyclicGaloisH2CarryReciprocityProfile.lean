/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisH2CarryTorsionCharacter
import GaloisForLFunctions.HTGeometry.ABHN.FiniteTorsionInvariantSum

/-!
# Finite reciprocity profiles of literal carry classes

Finite families of literal cyclic carry classes inherit a torsion-valued invariant sum and a
faithful global circle character.  The global phase is the product of local carry phases, and it is
one exactly when the invariant sum vanishes.  This is the route-neutral finite-profile interface
needed before an arithmetic specialization can identify places, Frobenius data, or a global class.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

universe u

/-- Sum a finite profile of literal cyclic `H²` classes in its common torsion coordinate. -/
noncomputable def cyclicGaloisCarryH2ProfileInvariantSumAddHom
    (ι : Type u) (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (n : ℕ) (hn : n ≠ 0)
    (qEquiv : Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L ≃+ ZMod n) :
    (ι →₀ cyclicGaloisH2 K L) →+ ratModIntNTorsion n := by
  classical
  let e := cyclicGaloisCarryH2TorsionEquiv K L n hn qEquiv
  exact
    { toFun := fun f => f.sum fun _ z => e z
      map_zero' := Finsupp.sum_zero_index
      map_add' := fun f g => Finsupp.sum_add_index
        (by intros; exact e.map_zero) (by intros; exact e.map_add _ _) }

/-- A singleton carry profile sums to its local torsion invariant. -/
@[simp] theorem cyclicGaloisCarryH2ProfileInvariantSumAddHom_single
    (ι : Type u) (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (n : ℕ) (hn : n ≠ 0)
    (qEquiv : Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L ≃+ ZMod n)
    (i : ι) (z : cyclicGaloisH2 K L) :
    cyclicGaloisCarryH2ProfileInvariantSumAddHom ι K L n hn qEquiv
        (Finsupp.single i z) =
      cyclicGaloisCarryH2TorsionEquiv K L n hn qEquiv z := by
  change (Finsupp.single i z).sum
    (fun _ z => cyclicGaloisCarryH2TorsionEquiv K L n hn qEquiv z) = _
  exact Finsupp.sum_single_index (map_zero _)

/-- Global circle character of a finite profile of literal carry classes. -/
noncomputable def cyclicGaloisCarryH2ProfileStdAddChar
    (ι : Type u) (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (n : ℕ) (hn : n ≠ 0)
    (qEquiv : Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L ≃+ ZMod n) :
    AddChar (ι →₀ cyclicGaloisH2 K L) ℂ :=
  (ratModIntNTorsionStdAddChar n hn).compAddMonoidHom
    (cyclicGaloisCarryH2ProfileInvariantSumAddHom ι K L n hn qEquiv)

/-- A singleton global profile phase is its local carry phase. -/
@[simp] theorem cyclicGaloisCarryH2ProfileStdAddChar_single
    (ι : Type u) (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (n : ℕ) (hn : n ≠ 0)
    (qEquiv : Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L ≃+ ZMod n)
    (i : ι) (z : cyclicGaloisH2 K L) :
    cyclicGaloisCarryH2ProfileStdAddChar ι K L n hn qEquiv
        (Finsupp.single i z) =
      cyclicGaloisCarryH2TorsionStdAddChar K L n hn qEquiv z := by
  rw [cyclicGaloisCarryH2ProfileStdAddChar, AddChar.compAddMonoidHom_apply,
    cyclicGaloisCarryH2ProfileInvariantSumAddHom_single]
  rfl

/-- Global carry-profile character is the finite product of all local carry phases. -/
theorem cyclicGaloisCarryH2ProfileStdAddChar_eq_finsupp_prod
    (ι : Type u) (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (n : ℕ) (hn : n ≠ 0)
    (qEquiv : Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L ≃+ ZMod n)
    (f : ι →₀ cyclicGaloisH2 K L) :
    cyclicGaloisCarryH2ProfileStdAddChar ι K L n hn qEquiv f =
      f.prod fun _ z => cyclicGaloisCarryH2TorsionStdAddChar K L n hn qEquiv z := by
  classical
  induction f using Finsupp.induction with
  | zero =>
      simp [cyclicGaloisCarryH2ProfileStdAddChar]
  | single_add i z f hif hz ih =>
      rw [(cyclicGaloisCarryH2ProfileStdAddChar ι K L n hn qEquiv).map_add_eq_mul,
        ih, Finsupp.prod_add_index']
      · rw [cyclicGaloisCarryH2ProfileStdAddChar_single, Finsupp.prod_single_index]
        exact (cyclicGaloisCarryH2TorsionStdAddChar K L n hn qEquiv).map_zero_eq_one
      · intro _
        exact (cyclicGaloisCarryH2TorsionStdAddChar K L n hn qEquiv).map_zero_eq_one
      · intro _ a b
        exact (cyclicGaloisCarryH2TorsionStdAddChar K L n hn qEquiv).map_add_eq_mul a b

/-- Finite-profile reciprocity: product of local carry phases is one exactly when their common
torsion invariant sum is zero. -/
theorem cyclicGaloisCarryH2Profile_product_eq_one_iff_sum_eq_zero
    (ι : Type u) (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (n : ℕ) (hn : n ≠ 0)
    (qEquiv : Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L ≃+ ZMod n)
    (f : ι →₀ cyclicGaloisH2 K L) :
    f.prod (fun _ z => cyclicGaloisCarryH2TorsionStdAddChar K L n hn qEquiv z) = 1 ↔
      cyclicGaloisCarryH2ProfileInvariantSumAddHom ι K L n hn qEquiv f = 0 := by
  rw [← cyclicGaloisCarryH2ProfileStdAddChar_eq_finsupp_prod]
  constructor
  · intro hf
    apply ratModIntNTorsionStdAddChar_injective n hn
    simpa [cyclicGaloisCarryH2ProfileStdAddChar] using hf
  · intro hf
    rw [cyclicGaloisCarryH2ProfileStdAddChar, AddChar.compAddMonoidHom_apply, hf]
    exact (ratModIntNTorsionStdAddChar n hn).map_zero_eq_one

/-- At a one-place profile, the product-one law for a literal carry parameter is exactly the field
norm criterion. -/
theorem cyclicGaloisCarryH2Profile_single_carryClass_product_eq_one_iff_mem_normImage
    (ι : Type u) (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (n : ℕ) (hn : n ≠ 0)
    (qEquiv : Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L ≃+ ZMod n)
    (i : ι) (a : Additive Kˣ) :
    (Finsupp.single i (cyclicGaloisCarryH2Class K L a)).prod
        (fun _ z => cyclicGaloisCarryH2TorsionStdAddChar K L n hn qEquiv z) = 1 ↔
      a ∈ cyclicGaloisH2BaseNormImage K L := by
  rw [Finsupp.prod_single_index]
  · exact cyclicGaloisCarryH2TorsionStdAddChar_carryClass_eq_one_iff_mem_normImage
      K L n hn qEquiv a
  · exact (cyclicGaloisCarryH2TorsionStdAddChar K L n hn qEquiv).map_zero_eq_one

/-- Literal cyclic `H²` profiles realize every finite torsion invariant as soon as there is one
place.  This is the surjectivity end of the finite carry-model ABHN sequence. -/
theorem cyclicGaloisCarryH2ProfileInvariantSumAddHom_surjective
    (ι : Type u) [Nonempty ι]
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (n : ℕ) (hn : n ≠ 0)
    (qEquiv : Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L ≃+ ZMod n) :
    Function.Surjective
      (cyclicGaloisCarryH2ProfileInvariantSumAddHom ι K L n hn qEquiv) := by
  intro q
  let i : ι := Classical.choice inferInstance
  obtain ⟨z, rfl⟩ := (cyclicGaloisCarryH2TorsionEquiv K L n hn qEquiv).surjective q
  exact ⟨Finsupp.single i z,
    cyclicGaloisCarryH2ProfileInvariantSumAddHom_single ι K L n hn qEquiv i z⟩

/-- Modulo reciprocal carry profiles, finite families of literal cyclic `H²` classes recover the
common torsion invariant group. -/
noncomputable def cyclicGaloisCarryH2ProfileInvariantSumQuotientAddEquiv
    (ι : Type u) [Nonempty ι]
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (n : ℕ) (hn : n ≠ 0)
    (qEquiv : Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L ≃+ ZMod n) :
    ((ι →₀ cyclicGaloisH2 K L) ⧸
      (cyclicGaloisCarryH2ProfileInvariantSumAddHom ι K L n hn qEquiv).ker) ≃+
        ratModIntNTorsion n :=
  QuotientAddGroup.quotientKerEquivOfSurjective
    (cyclicGaloisCarryH2ProfileInvariantSumAddHom ι K L n hn qEquiv)
    (cyclicGaloisCarryH2ProfileInvariantSumAddHom_surjective ι K L n hn qEquiv)

/-- Finite literal-carry reciprocity sequence is exact at the local-profile term. -/
theorem cyclicGaloisCarryH2ProfileInvariantSum_zeroSum_exact
    (ι : Type u)
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (n : ℕ) (hn : n ≠ 0)
    (qEquiv : Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L ≃+ ZMod n) :
    Function.Exact
      (cyclicGaloisCarryH2ProfileInvariantSumAddHom ι K L n hn qEquiv).ker.subtype
      (cyclicGaloisCarryH2ProfileInvariantSumAddHom ι K L n hn qEquiv) := by
  intro x
  constructor
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    exact y.property

/-- The exact-sequence kernel of literal carry profiles is precisely the product-one locus of
their faithful local phases. -/
theorem cyclicGaloisCarryH2Profile_product_eq_one_iff_mem_invariantSum_kernel
    (ι : Type u)
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (n : ℕ) (hn : n ≠ 0)
    (qEquiv : Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L ≃+ ZMod n)
    (f : ι →₀ cyclicGaloisH2 K L) :
    f.prod (fun _ z => cyclicGaloisCarryH2TorsionStdAddChar K L n hn qEquiv z) = 1 ↔
      f ∈ (cyclicGaloisCarryH2ProfileInvariantSumAddHom ι K L n hn qEquiv).ker := by
  rw [cyclicGaloisCarryH2Profile_product_eq_one_iff_sum_eq_zero]
  rfl

end

end GaloisForLFunctions.HTGeometry.ABHN
