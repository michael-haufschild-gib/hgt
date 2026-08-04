import GaloisForLFunctions.HilbertMetric.SymmetricFockShadow

/-!
# Involutive parity decomposition of invariant subspaces

An ambient involution splits the whole carrier into its even and odd
eigenspaces when two is invertible.  The statement needed for Hall expansion
is stronger in its quantifiers: every subspace preserved by the involution
must split internally.  This file proves that basis-free subspace theorem.

It supplies the exact bridge from a symmetry-fixed canonical Hall obstruction
to its parity-resolved pieces.  No orthogonality, diagonalization, chosen
basis, or positivity hypothesis is used.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Even eigenspace of a linear involution candidate. -/
def involutiveEvenSubspace
    {K X : Type*} [Field K] [AddCommGroup X] [Module K X]
    (C : X ≃ₗ[K] X) : Submodule K X :=
  LinearMap.ker ((C : X →ₗ[K] X) - LinearMap.id)

/-- Odd eigenspace of a linear involution candidate. -/
def involutiveOddSubspace
    {K X : Type*} [Field K] [AddCommGroup X] [Module K X]
    (C : X ≃ₗ[K] X) : Submodule K X :=
  LinearMap.ker ((C : X →ₗ[K] X) + LinearMap.id)

theorem mem_involutiveEvenSubspace_iff
    {K X : Type*} [Field K] [AddCommGroup X] [Module K X]
    (C : X ≃ₗ[K] X) (x : X) :
    x ∈ involutiveEvenSubspace C ↔ C x = x := by
  change C x - x = 0 ↔ _
  exact sub_eq_zero

theorem mem_involutiveOddSubspace_iff
    {K X : Type*} [Field K] [AddCommGroup X] [Module K X]
    (C : X ≃ₗ[K] X) (x : X) :
    x ∈ involutiveOddSubspace C ↔ C x = -x := by
  change C x + x = 0 ↔ _
  exact add_eq_zero_iff_eq_neg

/-- In characteristic different from two, even and odd eigenspaces have
trivial intersection. -/
theorem disjoint_involutiveEvenSubspace_involutiveOddSubspace
    {K X : Type*} [Field K] [AddCommGroup X] [Module K X]
    (C : X ≃ₗ[K] X) (h2 : (2 : K) ≠ 0) :
    Disjoint (involutiveEvenSubspace C) (involutiveOddSubspace C) := by
  rw [disjoint_iff]
  apply le_antisymm
  · intro x hx
    have hEven := (mem_involutiveEvenSubspace_iff C x).mp hx.1
    have hOdd := (mem_involutiveOddSubspace_iff C x).mp hx.2
    have hxneg : x = -x := hEven.symm.trans hOdd
    have hxx : x + x = 0 :=
      (congrArg (fun y : X => x + y) hxneg).trans (add_neg_cancel x)
    have h2x : (2 : K) • x = 0 := by
      simpa [two_smul] using hxx
    have hxzero : x = 0 := (smul_eq_zero.mp h2x).resolve_left h2
    simp [hxzero]
  · exact bot_le

/-- Every subspace preserved by an involution is the internal sum of its
even and odd parts.  Preservation in one direction suffices because the
ambient map is involutive. -/
theorem invariantSubspace_eq_even_sup_odd
    {K X : Type*} [Field K] [AddCommGroup X] [Module K X]
    (C : X ≃ₗ[K] X) (hC : ∀ x, C (C x) = x)
    (h2 : (2 : K) ≠ 0) (U : Submodule K X)
    (hstable : U.map (C : X →ₗ[K] X) ≤ U) :
    U = (U ⊓ involutiveEvenSubspace C) ⊔
      (U ⊓ involutiveOddSubspace C) := by
  apply le_antisymm
  · intro x hx
    have hCx : C x ∈ U := hstable (Submodule.mem_map_of_mem hx)
    let e : X := (2 : K)⁻¹ • (x + C x)
    let o : X := (2 : K)⁻¹ • (x - C x)
    have heU : e ∈ U := U.smul_mem _ (U.add_mem hx hCx)
    have hoU : o ∈ U := U.smul_mem _ (U.sub_mem hx hCx)
    have hCe : C e = e := by
      dsimp [e]
      rw [map_smul, map_add, hC]
      module
    have hCo : C o = -o := by
      dsimp [o]
      rw [map_smul, map_sub, hC]
      module
    have he : e ∈ U ⊓ involutiveEvenSubspace C :=
      ⟨heU, (mem_involutiveEvenSubspace_iff C e).mpr hCe⟩
    have ho : o ∈ U ⊓ involutiveOddSubspace C :=
      ⟨hoU, (mem_involutiveOddSubspace_iff C o).mpr hCo⟩
    have heo : e + o = x := by
      dsimp [e, o]
      calc
        (2 : K)⁻¹ • (x + C x) + (2 : K)⁻¹ • (x - C x) =
            (2 : K)⁻¹ • ((x + C x) + (x - C x)) := by
              module
        _ = (2 : K)⁻¹ • ((2 : K) • x) := by
              congr 1
              module
        _ = ((2 : K)⁻¹ * 2) • x := by rw [smul_smul]
        _ = x := by rw [inv_mul_cancel₀ h2, one_smul]
    rw [← heo]
    exact add_mem
      ((le_sup_left : U ⊓ involutiveEvenSubspace C ≤ _) he)
      ((le_sup_right : U ⊓ involutiveOddSubspace C ≤ _) ho)
  · exact sup_le inf_le_left inf_le_left

/-- Finite-dimensional form of the internal parity splitting: dimensions of
the invariant even and odd pieces add without overlap. -/
theorem invariantSubspace_finrank_eq_even_add_odd
    {K X : Type*} [Field K] [AddCommGroup X] [Module K X]
    [FiniteDimensional K X]
    (C : X ≃ₗ[K] X) (hC : ∀ x, C (C x) = x)
    (h2 : (2 : K) ≠ 0) (U : Submodule K X)
    (hstable : U.map (C : X →ₗ[K] X) ≤ U) :
    Module.finrank K U =
      Module.finrank K ↥(U ⊓ involutiveEvenSubspace C) +
        Module.finrank K ↥(U ⊓ involutiveOddSubspace C) := by
  let E := U ⊓ involutiveEvenSubspace C
  let O := U ⊓ involutiveOddSubspace C
  have hdecomp : U = E ⊔ O :=
    invariantSubspace_eq_even_sup_odd C hC h2 U hstable
  have hdisjoint : Disjoint E O :=
    (disjoint_involutiveEvenSubspace_involutiveOddSubspace C h2).mono
      inf_le_right inf_le_right
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq E O
  rw [hdisjoint.eq_bot, finrank_bot K X, add_zero, ← hdecomp] at hdim
  exact hdim

/-- If two linear equivalences commute, the even part for the first remains
stable under the second whenever the original subspace does. -/
theorem evenPart_map_le_of_commuting_involutions
    {K X : Type*} [Field K] [AddCommGroup X] [Module K X]
    (C D : X ≃ₗ[K] X) (hcomm : ∀ x, C (D x) = D (C x))
    (U : Submodule K X) (hDstable : U.map (D : X →ₗ[K] X) ≤ U) :
    (U ⊓ involutiveEvenSubspace C).map (D : X →ₗ[K] X) ≤
      U ⊓ involutiveEvenSubspace C := by
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨hDstable (Submodule.mem_map_of_mem hx.1), ?_⟩
  apply (mem_involutiveEvenSubspace_iff C (D x)).mpr
  calc
    C (D x) = D (C x) := hcomm x
    _ = D x := by rw [(mem_involutiveEvenSubspace_iff C x).mp hx.2]

/-- If two linear equivalences commute, the odd part for the first remains
stable under the second whenever the original subspace does. -/
theorem oddPart_map_le_of_commuting_involutions
    {K X : Type*} [Field K] [AddCommGroup X] [Module K X]
    (C D : X ≃ₗ[K] X) (hcomm : ∀ x, C (D x) = D (C x))
    (U : Submodule K X) (hDstable : U.map (D : X →ₗ[K] X) ≤ U) :
    (U ⊓ involutiveOddSubspace C).map (D : X →ₗ[K] X) ≤
      U ⊓ involutiveOddSubspace C := by
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨hDstable (Submodule.mem_map_of_mem hx.1), ?_⟩
  apply (mem_involutiveOddSubspace_iff C (D x)).mpr
  calc
    C (D x) = D (C x) := hcomm x
    _ = D (-x) := by rw [(mem_involutiveOddSubspace_iff C x).mp hx.2]
    _ = -D x := map_neg D x

/-- Every subspace stable under two commuting involutions is the sum of its
four simultaneous parity sectors. -/
theorem invariantSubspace_eq_commutingInvolution_bigrading
    {K X : Type*} [Field K] [AddCommGroup X] [Module K X]
    (C D : X ≃ₗ[K] X)
    (hC : ∀ x, C (C x) = x) (hD : ∀ x, D (D x) = x)
    (hcomm : ∀ x, C (D x) = D (C x))
    (h2 : (2 : K) ≠ 0) (U : Submodule K X)
    (hCstable : U.map (C : X →ₗ[K] X) ≤ U)
    (hDstable : U.map (D : X →ₗ[K] X) ≤ U) :
    U =
      (((U ⊓ involutiveEvenSubspace C) ⊓ involutiveEvenSubspace D) ⊔
        ((U ⊓ involutiveEvenSubspace C) ⊓ involutiveOddSubspace D)) ⊔
      (((U ⊓ involutiveOddSubspace C) ⊓ involutiveEvenSubspace D) ⊔
        ((U ⊓ involutiveOddSubspace C) ⊓ involutiveOddSubspace D)) := by
  let CE := U ⊓ involutiveEvenSubspace C
  let CO := U ⊓ involutiveOddSubspace C
  have hsplitC : U = CE ⊔ CO :=
    invariantSubspace_eq_even_sup_odd C hC h2 U hCstable
  have hCEstable : CE.map (D : X →ₗ[K] X) ≤ CE :=
    evenPart_map_le_of_commuting_involutions C D hcomm U hDstable
  have hCOstable : CO.map (D : X →ₗ[K] X) ≤ CO :=
    oddPart_map_le_of_commuting_involutions C D hcomm U hDstable
  have hsplitCE : CE =
      (CE ⊓ involutiveEvenSubspace D) ⊔
        (CE ⊓ involutiveOddSubspace D) :=
    invariantSubspace_eq_even_sup_odd D hD h2 CE hCEstable
  have hsplitCO : CO =
      (CO ⊓ involutiveEvenSubspace D) ⊔
        (CO ⊓ involutiveOddSubspace D) :=
    invariantSubspace_eq_even_sup_odd D hD h2 CO hCOstable
  calc
    U = CE ⊔ CO := hsplitC
    _ =
        ((CE ⊓ involutiveEvenSubspace D) ⊔
          (CE ⊓ involutiveOddSubspace D)) ⊔
        ((CO ⊓ involutiveEvenSubspace D) ⊔
          (CO ⊓ involutiveOddSubspace D)) :=
      congrArg₂ (fun A B : Submodule K X => A ⊔ B) hsplitCE hsplitCO
    _ = _ := rfl

/-- Dimensions of the four simultaneous parity sectors add exactly inside
a finite-dimensional subspace invariant under two commuting involutions. -/
theorem invariantSubspace_finrank_eq_commutingInvolution_bigrading
    {K X : Type*} [Field K] [AddCommGroup X] [Module K X]
    [FiniteDimensional K X]
    (C D : X ≃ₗ[K] X)
    (hC : ∀ x, C (C x) = x) (hD : ∀ x, D (D x) = x)
    (hcomm : ∀ x, C (D x) = D (C x))
    (h2 : (2 : K) ≠ 0) (U : Submodule K X)
    (hCstable : U.map (C : X →ₗ[K] X) ≤ U)
    (hDstable : U.map (D : X →ₗ[K] X) ≤ U) :
    Module.finrank K U =
      Module.finrank K ↥((U ⊓ involutiveEvenSubspace C) ⊓
        involutiveEvenSubspace D) +
      Module.finrank K ↥((U ⊓ involutiveEvenSubspace C) ⊓
        involutiveOddSubspace D) +
      Module.finrank K ↥((U ⊓ involutiveOddSubspace C) ⊓
        involutiveEvenSubspace D) +
      Module.finrank K ↥((U ⊓ involutiveOddSubspace C) ⊓
        involutiveOddSubspace D) := by
  let CE := U ⊓ involutiveEvenSubspace C
  let CO := U ⊓ involutiveOddSubspace C
  have hsplitC :=
    invariantSubspace_finrank_eq_even_add_odd C hC h2 U hCstable
  have hCEstable : CE.map (D : X →ₗ[K] X) ≤ CE :=
    evenPart_map_le_of_commuting_involutions C D hcomm U hDstable
  have hCOstable : CO.map (D : X →ₗ[K] X) ≤ CO :=
    oddPart_map_le_of_commuting_involutions C D hcomm U hDstable
  have hsplitCE :=
    invariantSubspace_finrank_eq_even_add_odd D hD h2 CE hCEstable
  have hsplitCO :=
    invariantSubspace_finrank_eq_even_add_odd D hD h2 CO hCOstable
  dsimp [CE, CO] at hsplitC hsplitCE hsplitCO ⊢
  omega

end

end GaloisForLFunctions.HTGeometry
