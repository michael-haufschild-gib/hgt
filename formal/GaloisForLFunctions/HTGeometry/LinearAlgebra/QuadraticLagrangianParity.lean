import GaloisForLFunctions.HTGeometry.LinearAlgebra.AlternatingRank
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.Prod
import Mathlib.Algebra.Module.Projective

/-!
# Parity of quadratic Lagrangian intersections

For three Lagrangians of a nondegenerate quadratic space, intersection codimensions
form a cocycle modulo two. On `(X + Y) ∩ Z`, the polar form pairs the `X` component
of one vector with the other vector. Its radical is `(X ∩ Z) + (Y ∩ Z)`.
Even rank of this alternating form gives the parity identity in every characteristic.
-/

open Module
open LinearMap (BilinForm)
namespace GaloisForLFunctions.HTGeometry.LinearAlgebra
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Orthogonal complement exchanges sums and intersections. -/
theorem bilin_orthogonal_sup (B : BilinForm K V) (X Y : Submodule K V) :
    B.orthogonal (X ⊔ Y) = B.orthogonal X ⊓ B.orthogonal Y := by
  ext z
  constructor
  · intro hz
    exact ⟨fun x hx => hz x ((show X ≤ X ⊔ Y from le_sup_left) hx),
      fun y hy => hz y ((show Y ≤ X ⊔ Y from le_sup_right) hy)⟩
  · rintro ⟨hx, hy⟩ z hz
    rcases Submodule.mem_sup.mp hz with ⟨x, hx', y, hy', rfl⟩
    simp only [map_add, LinearMap.add_apply, hx x hx', hy y hy', add_zero]

/-- Nondegeneracy gives the converse orthogonal De Morgan law. -/
theorem bilin_orthogonal_inf [FiniteDimensional K V] {B : BilinForm K V}
    (hB : B.IsRefl) (hnd : B.Nondegenerate) (X Y : Submodule K V) :
    B.orthogonal (X ⊓ Y) = B.orthogonal X ⊔ B.orthogonal Y := by
  calc
    B.orthogonal (X ⊓ Y) =
        B.orthogonal (B.orthogonal (B.orthogonal X ⊔ B.orthogonal Y)) := by
      rw [bilin_orthogonal_sup, B.orthogonal_orthogonal hnd hB,
        B.orthogonal_orthogonal hnd hB]
    _ = _ := B.orthogonal_orthogonal hnd hB _

/-- Reducing a self-orthogonal subspace along an isotropic subspace preserves
self-orthogonality. -/
theorem selfOrthogonal_reduction [FiniteDimensional K V] {B : BilinForm K V}
    (hB : B.IsRefl) (hnd : B.Nondegenerate) {X W : Submodule K V}
    (hX : B.orthogonal X = X) (hW : W ≤ B.orthogonal W) :
    B.orthogonal ((B.orthogonal W ⊓ X) ⊔ W) = (B.orthogonal W ⊓ X) ⊔ W := by
  rw [bilin_orthogonal_sup, bilin_orthogonal_inf hB hnd,
    B.orthogonal_orthogonal hnd hB, hX, sup_inf_assoc_of_le X hW]
  rw [inf_comm X, sup_comm]

/-- A self-orthogonal subspace has half the ambient dimension. -/
theorem selfOrthogonal_finrank [FiniteDimensional K V] {B : BilinForm K V}
    (hnd : B.Nondegenerate) {X : Submodule K V} (hX : B.orthogonal X = X) :
    finrank K X + finrank K X = finrank K V := by
  have h := BilinForm.finrank_add_finrank_orthogonal' (B := B) X
  rw [hX, hnd.ker_eq_bot, inf_bot_eq, finrank_bot, add_zero] at h
  exact h

/-- Addition from a product of subspaces onto their sum. -/
def subspaceSumMap (X Y : Submodule K V) : (X × Y) →ₗ[K] ↥(X ⊔ Y) :=
  (X.subtype.coprod Y.subtype).codRestrict (X ⊔ Y) (fun v =>
    Submodule.mem_sup.mpr ⟨v.1, v.1.property, v.2, v.2.property, rfl⟩)

theorem subspaceSumMap_surjective (X Y : Submodule K V) :
    Function.Surjective (subspaceSumMap X Y) := by
  rintro ⟨z, hz⟩
  rcases Submodule.mem_sup.mp hz with ⟨x, hx, y, hy, hxy⟩
  exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), Subtype.ext hxy⟩

/-- A linear choice of decomposition in a sum of subspaces. -/
noncomputable def subspaceSumSection (X Y : Submodule K V) :
    ↥(X ⊔ Y) →ₗ[K] (X × Y) :=
  (LinearMap.exists_rightInverse_of_surjective (subspaceSumMap X Y)
    (LinearMap.range_eq_top.mpr (subspaceSumMap_surjective X Y))).choose

theorem subspaceSumSection_add (X Y : Submodule K V) (z : ↥(X ⊔ Y)) :
    ((subspaceSumSection X Y z).1 : V) + ((subspaceSumSection X Y z).2 : V) = z := by
  have h := (LinearMap.exists_rightInverse_of_surjective (subspaceSumMap X Y)
    (LinearMap.range_eq_top.mpr (subspaceSumMap_surjective X Y))).choose_spec
  exact congrArg Subtype.val (LinearMap.congr_fun h z)

#print axioms selfOrthogonal_reduction
#print axioms subspaceSumSection_add
end GaloisForLFunctions.HTGeometry.LinearAlgebra

namespace GaloisForLFunctions.HTGeometry.LinearAlgebra
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- A quadratic Lagrangian is totally singular and equal to its polar orthogonal complement. -/
def IsQuadraticLagrangian (Q : QuadraticForm K V) (X : Submodule K V) : Prop :=
  (∀ x ∈ X, Q x = 0) ∧ BilinForm.orthogonal Q.polarBilin X = X

theorem quadratic_polar_isRefl (Q : QuadraticForm K V) : Q.polarBilin.IsRefl := by
  intro x y h
  change QuadraticMap.polar Q y x = 0
  rw [QuadraticMap.polar_comm]
  exact h

/-- The first component of a linear decomposition of the intersection with a sum. -/
noncomputable def intersectionLeft (X Y Z : Submodule K V) :
    ↥((X ⊔ Y) ⊓ Z) →ₗ[K] V :=
  X.subtype.comp ((LinearMap.fst K X Y).comp
    ((subspaceSumSection X Y).comp (Submodule.inclusion inf_le_left)))

/-- The second component of the same decomposition. -/
noncomputable def intersectionRight (X Y Z : Submodule K V) :
    ↥((X ⊔ Y) ⊓ Z) →ₗ[K] V :=
  Y.subtype.comp ((LinearMap.snd K X Y).comp
    ((subspaceSumSection X Y).comp (Submodule.inclusion inf_le_left)))

theorem intersectionLeft_mem (X Y Z : Submodule K V) (z : ↥((X ⊔ Y) ⊓ Z)) :
    intersectionLeft X Y Z z ∈ X :=
  (subspaceSumSection X Y ⟨z, z.property.1⟩).1.property

theorem intersectionRight_mem (X Y Z : Submodule K V) (z : ↥((X ⊔ Y) ⊓ Z)) :
    intersectionRight X Y Z z ∈ Y :=
  (subspaceSumSection X Y ⟨z, z.property.1⟩).2.property

theorem intersectionLeft_add_right (X Y Z : Submodule K V) (z : ↥((X ⊔ Y) ⊓ Z)) :
    intersectionLeft X Y Z z + intersectionRight X Y Z z = z :=
  subspaceSumSection_add X Y ⟨z, z.property.1⟩

/-- The intersection form pairs the first component of one decomposition with the
other vector. For quadratic Lagrangians it is independent of the chosen decomposition. -/
noncomputable def lagrangianIntersectionForm (Q : QuadraticForm K V)
    (X Y Z : Submodule K V) : BilinForm K ↥((X ⊔ Y) ⊓ Z) :=
  Q.polarBilin.compl₁₂ (intersectionLeft X Y Z) ((X ⊔ Y) ⊓ Z).subtype

/-- Total singularity of the three subspaces makes the intersection form alternating. -/
theorem lagrangianIntersectionForm_isAlt (Q : QuadraticForm K V)
    {X Y Z : Submodule K V} (hX : IsQuadraticLagrangian Q X)
    (hY : IsQuadraticLagrangian Q Y) (hZ : IsQuadraticLagrangian Q Z) :
    (lagrangianIntersectionForm Q X Y Z).IsAlt := by
  intro z
  let x := intersectionLeft X Y Z z
  let y := intersectionRight X Y Z z
  have hx : Q x = 0 := hX.1 _ (intersectionLeft_mem X Y Z z)
  have hy : Q y = 0 := hY.1 _ (intersectionRight_mem X Y Z z)
  have hz : Q (z : V) = 0 := hZ.1 _ z.property.2
  have hxy : x + y = z := intersectionLeft_add_right X Y Z z
  change Q.polarBilin x (z : V) = 0
  rw [← hxy, map_add]
  have hxx : Q.polarBilin x x = 0 := by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, hx, nsmul_zero]
  have hpair : Q.polarBilin x y = 0 := by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, hxy, hx, hy, hz]
    simp only [sub_zero]
  rw [hxx, hpair, add_zero]

#print axioms lagrangianIntersectionForm_isAlt
end GaloisForLFunctions.HTGeometry.LinearAlgebra

namespace GaloisForLFunctions.HTGeometry.LinearAlgebra
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The intersection form can be evaluated using any decomposition in the first two
Lagrangians. Their common part pairs trivially with their sum. -/
theorem lagrangianIntersectionForm_apply_of_sum (Q : QuadraticForm K V)
    {X Y Z : Submodule K V} (hX : IsQuadraticLagrangian Q X)
    (hY : IsQuadraticLagrangian Q Y) (z w : ↥((X ⊔ Y) ⊓ Z))
    {x y : V} (hx : x ∈ X) (hy : y ∈ Y) (hxy : x + y = z) :
    lagrangianIntersectionForm Q X Y Z z w = Q.polarBilin x w := by
  have hleft := intersectionLeft_mem X Y Z z
  have hright := intersectionRight_mem X Y Z z
  have hsum := intersectionLeft_add_right X Y Z z
  have hdiffX := X.sub_mem hleft hx
  have heq : intersectionLeft X Y Z z - x = y - intersectionRight X Y Z z := by
    rw [eq_sub_of_add_eq hsum, eq_sub_of_add_eq hxy]
    abel
  have hdiffY : intersectionLeft X Y Z z - x ∈ Y := by
    rw [heq]
    exact Y.sub_mem hy hright
  have horth : intersectionLeft X Y Z z - x ∈ BilinForm.orthogonal Q.polarBilin (X ⊔ Y) := by
    rw [bilin_orthogonal_sup, hX.2, hY.2]
    exact ⟨hdiffX, hdiffY⟩
  have hzero := quadratic_polar_isRefl Q _ _ (horth (w : V) w.property.1)
  change Q.polarBilin (intersectionLeft X Y Z z) w = Q.polarBilin x w
  exact sub_eq_zero.mp (by
    simpa only [map_sub, LinearMap.sub_apply] using hzero)

/-- The sum of the two pairwise intersections lies in the intersection domain. -/
theorem pairwise_intersections_le_domain (X Y Z : Submodule K V) :
    (X ⊓ Z) ⊔ (Y ⊓ Z) ≤ (X ⊔ Y) ⊓ Z := by
  refine sup_le ?_ ?_
  · exact inf_le_inf_right Z le_sup_left
  · exact inf_le_inf_right Z le_sup_right

/-- The orthogonal reduction along the first two Lagrangians' common part. -/
theorem intersection_domain_selfOrthogonal [FiniteDimensional K V]
    (Q : QuadraticForm K V) (hnd : Q.polarBilin.Nondegenerate)
    {X Y Z : Submodule K V} (hX : IsQuadraticLagrangian Q X)
    (hY : IsQuadraticLagrangian Q Y) (hZ : IsQuadraticLagrangian Q Z) :
    BilinForm.orthogonal Q.polarBilin (((X ⊔ Y) ⊓ Z) ⊔ (X ⊓ Y)) =
      ((X ⊔ Y) ⊓ Z) ⊔ (X ⊓ Y) := by
  have hD : X ⊓ Y ≤ BilinForm.orthogonal Q.polarBilin (X ⊓ Y) := by
    calc
      X ⊓ Y ≤ X := inf_le_left
      _ = BilinForm.orthogonal Q.polarBilin X := hX.2.symm
      _ ≤ BilinForm.orthogonal Q.polarBilin (X ⊓ Y) :=
        LinearMap.BilinForm.orthogonal_le inf_le_left
  have horth : BilinForm.orthogonal Q.polarBilin (X ⊓ Y) = X ⊔ Y := by
    rw [bilin_orthogonal_inf (quadratic_polar_isRefl Q) hnd, hX.2, hY.2]
  simpa only [horth] using
    selfOrthogonal_reduction (quadratic_polar_isRefl Q) hnd hZ.2 hD

/-- The radical of the intersection form is exactly the sum of the pairwise
intersections. This is the algebraic input to the three-Lagrangian parity law. -/
theorem lagrangianIntersectionForm_ker [FiniteDimensional K V]
    (Q : QuadraticForm K V) (hnd : Q.polarBilin.Nondegenerate)
    {X Y Z : Submodule K V} (hX : IsQuadraticLagrangian Q X)
    (hY : IsQuadraticLagrangian Q Y) (hZ : IsQuadraticLagrangian Q Z) :
    (lagrangianIntersectionForm Q X Y Z).ker =
      ((X ⊓ Z) ⊔ (Y ⊓ Z)).comap ((X ⊔ Y) ⊓ Z).subtype := by
  ext z
  constructor
  · intro hz
    let x := intersectionLeft X Y Z z
    let y := intersectionRight X Y Z z
    have hx : x ∈ X := intersectionLeft_mem X Y Z z
    have hy : y ∈ Y := intersectionRight_mem X Y Z z
    have hxy : x + y = z := intersectionLeft_add_right X Y Z z
    have horthU : x ∈ BilinForm.orthogonal Q.polarBilin ((X ⊔ Y) ⊓ Z) := by
      intro w hw
      have hzero : Q.polarBilin x w = 0 :=
        congrArg (fun f : ↥((X ⊔ Y) ⊓ Z) →ₗ[K] K => f ⟨w, hw⟩) hz
      exact quadratic_polar_isRefl Q _ _ hzero
    have horthD : x ∈ BilinForm.orthogonal Q.polarBilin (X ⊓ Y) := by
      intro d hd
      exact (show x ∈ BilinForm.orthogonal Q.polarBilin X by rw [hX.2]; exact hx) d hd.1
    have hxS : x ∈ ((X ⊔ Y) ⊓ Z) ⊔ (X ⊓ Y) := by
      rw [← intersection_domain_selfOrthogonal Q hnd hX hY hZ,
        bilin_orthogonal_sup]
      exact ⟨horthU, horthD⟩
    rcases Submodule.mem_sup.mp hxS with ⟨u, hu, d, hd, hud⟩
    have huX : u ∈ X := by
      rw [eq_sub_of_add_eq hud]
      exact X.sub_mem hx hd.1
    have hyZ : y + d ∈ Z := by
      have heq : y + d = (z : V) - u := by
        rw [← hxy, ← hud]
        abel
      rw [heq]
      exact Z.sub_mem z.property.2 hu.2
    change (z : V) ∈ (X ⊓ Z) ⊔ (Y ⊓ Z)
    refine Submodule.mem_sup.mpr ⟨u, ⟨huX, hu.2⟩, y + d,
      ⟨Y.add_mem hy hd.2, hyZ⟩, ?_⟩
    rw [← hxy, ← hud]
    abel
  · intro hz
    change (z : V) ∈ (X ⊓ Z) ⊔ (Y ⊓ Z) at hz
    rcases Submodule.mem_sup.mp hz with ⟨x, hx, y, hy, hxy⟩
    ext w
    rw [lagrangianIntersectionForm_apply_of_sum Q hX hY z w hx.1 hy.1 hxy]
    have hxorth : x ∈ BilinForm.orthogonal Q.polarBilin Z := by rw [hZ.2]; exact hx.2
    exact quadratic_polar_isRefl Q _ _ (hxorth w w.property.2)

#print axioms lagrangianIntersectionForm_ker
end GaloisForLFunctions.HTGeometry.LinearAlgebra

namespace GaloisForLFunctions.HTGeometry.LinearAlgebra
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V]

/-- The dimensions of three pairwise intersections have the parity of a Lagrangian.
The radical calculation reduces this to even rank of an alternating form. -/
theorem quadraticLagrangian_intersection_parity (Q : QuadraticForm K V)
    (hnd : Q.polarBilin.Nondegenerate) {X Y Z : Submodule K V}
    (hX : IsQuadraticLagrangian Q X) (hY : IsQuadraticLagrangian Q Y)
    (hZ : IsQuadraticLagrangian Q Z) :
    (finrank K ↥(X ⊓ Y) + finrank K ↥(Y ⊓ Z) + finrank K ↥(X ⊓ Z)) % 2 =
      finrank K X % 2 := by
  let U := (X ⊔ Y) ⊓ Z
  let D := X ⊓ Y
  let R := (X ⊓ Z) ⊔ (Y ⊓ Z)
  let T := (X ⊓ Y) ⊓ Z
  let B := lagrangianIntersectionForm Q X Y Z
  have hker : finrank K B.ker = finrank K R := by
    rw [lagrangianIntersectionForm_ker Q hnd hX hY hZ]
    exact (Submodule.comapSubtypeEquivOfLe (pairwise_intersections_le_domain X Y Z)).finrank_eq
  have hrank := LinearMap.finrank_range_add_finrank_ker B
  rw [hker] at hrank
  obtain ⟨r, hr⟩ := even_finrank_range_of_isAlt
    (lagrangianIntersectionForm_isAlt Q hX hY hZ)
  change finrank K B.range = r + r at hr
  rw [hr] at hrank
  have hS : finrank K ↥(U ⊔ D) = finrank K X := by
    have h1 := selfOrthogonal_finrank hnd
      (intersection_domain_selfOrthogonal Q hnd hX hY hZ)
    have h2 := selfOrthogonal_finrank hnd hX.2
    change finrank K ↥(U ⊔ D) + finrank K ↥(U ⊔ D) = finrank K V at h1
    omega
  have hUD : U ⊓ D = T := by
    apply le_antisymm
    · intro z hz
      exact ⟨hz.2, hz.1.2⟩
    · intro z hz
      exact ⟨⟨(show X ≤ X ⊔ Y from le_sup_left) hz.1.1, hz.2⟩, hz.1⟩
  have hRT : (X ⊓ Z) ⊓ (Y ⊓ Z) = T := by
    ext z
    constructor
    · rintro ⟨⟨hx, hz⟩, hy, _⟩
      exact ⟨⟨hx, hy⟩, hz⟩
    · rintro ⟨⟨hx, hy⟩, hz⟩
      exact ⟨⟨hx, hz⟩, hy, hz⟩
  have hdimU := Submodule.finrank_sup_add_finrank_inf_eq U D
  rw [hS, hUD] at hdimU
  have hdimR := Submodule.finrank_sup_add_finrank_inf_eq (X ⊓ Z) (Y ⊓ Z)
  rw [hRT] at hdimR
  change finrank K R + finrank K T = _ at hdimR
  change r + r + finrank K R = finrank K U at hrank
  change finrank K X + finrank K T = finrank K U + finrank K D at hdimU
  change (finrank K D + _ + _) % 2 = _
  omega

/-- The sum of the three cyclic intersection codimensions is even. -/
theorem quadraticLagrangian_codimension_parity (Q : QuadraticForm K V)
    (hnd : Q.polarBilin.Nondegenerate) {X Y Z : Submodule K V}
    (hX : IsQuadraticLagrangian Q X) (hY : IsQuadraticLagrangian Q Y)
    (hZ : IsQuadraticLagrangian Q Z) :
    Even ((finrank K X - finrank K ↥(X ⊓ Y)) +
      (finrank K Y - finrank K ↥(Y ⊓ Z)) +
      (finrank K Z - finrank K ↥(X ⊓ Z))) := by
  have hp := quadraticLagrangian_intersection_parity Q hnd hX hY hZ
  have hdx := selfOrthogonal_finrank hnd hX.2
  have hdy := selfOrthogonal_finrank hnd hY.2
  have hdz := selfOrthogonal_finrank hnd hZ.2
  have hxy : finrank K ↥(X ⊓ Y) ≤ finrank K X := Submodule.finrank_mono inf_le_left
  have hyz : finrank K ↥(Y ⊓ Z) ≤ finrank K Y := Submodule.finrank_mono inf_le_left
  have hxz : finrank K ↥(X ⊓ Z) ≤ finrank K X := Submodule.finrank_mono inf_le_left
  refine ⟨((finrank K X - finrank K ↥(X ⊓ Y)) +
    (finrank K Y - finrank K ↥(Y ⊓ Z)) +
    (finrank K Z - finrank K ↥(X ⊓ Z))) / 2, ?_⟩
  omega

#print axioms quadraticLagrangian_intersection_parity
#print axioms quadraticLagrangian_codimension_parity
end GaloisForLFunctions.HTGeometry.LinearAlgebra

namespace GaloisForLFunctions.HTGeometry.LinearAlgebra
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The dimension lost when intersecting the first subspace with the second. -/
noncomputable def intersectionCodimension (X Y : Submodule K V) : ℕ :=
  finrank K (X ⧸ Y.comap X.subtype)

theorem intersectionCodimension_eq [FiniteDimensional K V] (X Y : Submodule K V) :
    intersectionCodimension X Y = finrank K X - finrank K ↥(X ⊓ Y) := by
  have hc : Y.comap X.subtype = (X ⊓ Y).comap X.subtype := by
    ext x
    exact ⟨fun h => ⟨x.property, h⟩, fun h => h.2⟩
  have hd : finrank K ↥(Y.comap X.subtype) = finrank K ↥(X ⊓ Y) := by
    rw [hc]
    exact (Submodule.comapSubtypeEquivOfLe (show X ⊓ Y ≤ X from inf_le_left)).finrank_eq
  have h := Submodule.finrank_quotient_add_finrank (Y.comap X.subtype)
  rw [hd] at h
  unfold intersectionCodimension
  omega

/-- Intersection defects of quadratic Lagrangians form a parity cocycle. -/
theorem quadraticLagrangian_defect_cocycle [FiniteDimensional K V]
    (Q : QuadraticForm K V) (hnd : Q.polarBilin.Nondegenerate)
    {X Y Z : Submodule K V} (hX : IsQuadraticLagrangian Q X)
    (hY : IsQuadraticLagrangian Q Y) (hZ : IsQuadraticLagrangian Q Z) :
    intersectionCodimension X Z % 2 =
      (intersectionCodimension X Y + intersectionCodimension Y Z) % 2 := by
  obtain ⟨r, hr⟩ := quadraticLagrangian_codimension_parity Q hnd hX hY hZ
  rw [intersectionCodimension_eq, intersectionCodimension_eq, intersectionCodimension_eq]
  have hx := selfOrthogonal_finrank hnd hX.2
  have hz := selfOrthogonal_finrank hnd hZ.2
  have heq : finrank K Z = finrank K X := by omega
  rw [heq] at hr
  omega

#print axioms quadraticLagrangian_defect_cocycle
end GaloisForLFunctions.HTGeometry.LinearAlgebra
