/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HeterogeneousTorsionReciprocity
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisH2CarryTorsionCharacter

/-!
# Heterogeneous reciprocity for literal cyclic carry classes

This is the place-dependent finite layer missing from the homogeneous carry profile: every place
may use a different base field, cyclic splitting field, and torsion order.  Literal carry `H²`
classes nevertheless sum in the common `ℚ/ℤ` target.  Their local phases satisfy product-one
reciprocity exactly on the zero-sum kernel, and a singleton phase is trivial exactly for field
norms at that place.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

universe u

variable {ι : Type u} [DecidableEq ι]
  (K L : ι → Type)
  [(i : ι) → Field (K i)] [(i : ι) → Field (L i)]
  [(i : ι) → Algebra (K i) (L i)]
  [(i : ι) → FiniteDimensional (K i) (L i)]
  [(i : ι) → IsGalois (K i) (L i)]
  [(i : ι) → IsCyclic Gal(L i / K i)]
  (n : ι → ℕ) (hn : ∀ i, n i ≠ 0)
  (qEquiv : ∀ i,
    Additive (K i)ˣ ⧸ cyclicGaloisH2BaseNormImage (K i) (L i) ≃+ ZMod (n i))

local instance cyclicGaloisCarryH2HeterogeneousDecidableEq (i : ι) :
    DecidableEq (cyclicGaloisH2 (K i) (L i)) := Classical.decEq _

/-- Placewise literal carry `H²` in its own finite torsion coordinate. -/
noncomputable def cyclicGaloisCarryH2HeterogeneousTorsionEquiv (i : ι) :
    cyclicGaloisH2 (K i) (L i) ≃+ ratModIntNTorsion (n i) :=
  cyclicGaloisCarryH2TorsionEquiv (K i) (L i) (n i) (hn i) (qEquiv i)

/-- A placewise carry class embedded in the common global `ℚ/ℤ` target. -/
noncomputable def cyclicGaloisCarryH2HeterogeneousLocalInvariantAddHom (i : ι) :
    cyclicGaloisH2 (K i) (L i) →+ RatModInt :=
  heterogeneousTorsionLocalInvariantAddHom
    (fun i => cyclicGaloisH2 (K i) (L i)) n
    (cyclicGaloisCarryH2HeterogeneousTorsionEquiv K L n hn qEquiv) i

/-- Sum of place-dependent literal carry classes in `ℚ/ℤ`. -/
noncomputable def cyclicGaloisCarryH2HeterogeneousInvariantSumAddHom :
    (Π₀ i, cyclicGaloisH2 (K i) (L i)) →+ RatModInt :=
  heterogeneousTorsionProfileInvariantSumAddHom
    (fun i => cyclicGaloisH2 (K i) (L i)) n
    (cyclicGaloisCarryH2HeterogeneousTorsionEquiv K L n hn qEquiv)

/-- Global character of a heterogeneous finite-support carry profile. -/
noncomputable def cyclicGaloisCarryH2HeterogeneousStdAddChar :
    AddChar (Π₀ i, cyclicGaloisH2 (K i) (L i)) ℂ :=
  heterogeneousTorsionProfileStdAddChar
    (fun i => cyclicGaloisH2 (K i) (L i)) n
    (cyclicGaloisCarryH2HeterogeneousTorsionEquiv K L n hn qEquiv)

/-- Global carry character is the product of all place-dependent local carry phases. -/
theorem cyclicGaloisCarryH2HeterogeneousStdAddChar_eq_dfinsupp_prod
    (f : Π₀ i, cyclicGaloisH2 (K i) (L i)) :
    cyclicGaloisCarryH2HeterogeneousStdAddChar K L n hn qEquiv f =
      f.prod fun i z => ratModIntStdAddChar
        (cyclicGaloisCarryH2HeterogeneousLocalInvariantAddHom K L n hn qEquiv i z) :=
  heterogeneousTorsionProfileStdAddChar_eq_dfinsupp_prod
    (fun i => cyclicGaloisH2 (K i) (L i)) n
    (cyclicGaloisCarryH2HeterogeneousTorsionEquiv K L n hn qEquiv) f

/-- Heterogeneous carry reciprocity: product of local phases is one exactly when the global
`ℚ/ℤ` invariant sum is zero. -/
theorem cyclicGaloisCarryH2Heterogeneous_product_eq_one_iff_sum_eq_zero
    (f : Π₀ i, cyclicGaloisH2 (K i) (L i)) :
    f.prod (fun i z => ratModIntStdAddChar
        (cyclicGaloisCarryH2HeterogeneousLocalInvariantAddHom K L n hn qEquiv i z)) = 1 ↔
      cyclicGaloisCarryH2HeterogeneousInvariantSumAddHom K L n hn qEquiv f = 0 :=
  heterogeneousTorsionProfile_product_eq_one_iff_sum_eq_zero
    (fun i => cyclicGaloisH2 (K i) (L i)) n
    (cyclicGaloisCarryH2HeterogeneousTorsionEquiv K L n hn qEquiv) f

/-- Heterogeneous carry reciprocity is exact at the local-profile term. -/
theorem cyclicGaloisCarryH2HeterogeneousInvariantSum_exact :
    Function.Exact
      (cyclicGaloisCarryH2HeterogeneousInvariantSumAddHom K L n hn qEquiv).ker.subtype
      (cyclicGaloisCarryH2HeterogeneousInvariantSumAddHom K L n hn qEquiv) :=
  heterogeneousTorsionProfileInvariantSum_exact
    (fun i => cyclicGaloisH2 (K i) (L i)) n
    (cyclicGaloisCarryH2HeterogeneousTorsionEquiv K L n hn qEquiv)

/-- Heterogeneous carry profiles modulo reciprocity equal the subgroup of `ℚ/ℤ` they realize. -/
noncomputable def cyclicGaloisCarryH2HeterogeneousInvariantSumQuotientEquivRange :
    (Π₀ i, cyclicGaloisH2 (K i) (L i)) ⧸
        (cyclicGaloisCarryH2HeterogeneousInvariantSumAddHom K L n hn qEquiv).ker ≃+
      (cyclicGaloisCarryH2HeterogeneousInvariantSumAddHom K L n hn qEquiv).range :=
  heterogeneousTorsionProfileInvariantSumQuotientEquivRange
    (fun i => cyclicGaloisH2 (K i) (L i)) n
    (cyclicGaloisCarryH2HeterogeneousTorsionEquiv K L n hn qEquiv)

/-- At one place, product-one for a literal carry parameter is exactly the field-norm criterion
at that place. -/
theorem cyclicGaloisCarryH2Heterogeneous_single_carryClass_product_eq_one_iff_mem_normImage
    (i : ι) (a : Additive (K i)ˣ) :
    (DFinsupp.single i (cyclicGaloisCarryH2Class (K i) (L i) a)).prod
        (fun j z => ratModIntStdAddChar
          (cyclicGaloisCarryH2HeterogeneousLocalInvariantAddHom K L n hn qEquiv j z)) = 1 ↔
      a ∈ cyclicGaloisH2BaseNormImage (K i) (L i) := by
  rw [DFinsupp.prod_single_index]
  · change ratModIntStdAddChar
      ((cyclicGaloisCarryH2TorsionEquiv (K i) (L i) (n i) (hn i) (qEquiv i)
        (cyclicGaloisCarryH2Class (K i) (L i) a) : ratModIntNTorsion (n i)) : RatModInt) = 1 ↔ _
    rw [ratModIntStdAddChar_subtype_eq_ratModIntNTorsionStdAddChar]
    exact cyclicGaloisCarryH2TorsionStdAddChar_carryClass_eq_one_iff_mem_normImage
      (K i) (L i) (n i) (hn i) (qEquiv i) a
  · rw [map_zero]
    exact ratModIntStdAddChar.map_zero_eq_one

end

end GaloisForLFunctions.HTGeometry.ABHN
