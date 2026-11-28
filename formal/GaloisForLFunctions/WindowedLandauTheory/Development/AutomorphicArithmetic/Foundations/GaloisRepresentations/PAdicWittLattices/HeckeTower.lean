import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.GroupTheory.Index

/-! In a Hecke tower the group conjugation relations index the
transition maps. At the identity, the transition maps are finite
étale covers with the prescribed geometric fibre actions. -/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace UpperTheory.Gal.G3

abbrev sp (k : Type) [CommRing k] : Scheme.{0} := Spec (CommRingCat.of k)

structure Tower (B : Scheme.{0}) (G : Type) [Group G] where
  ι : Type
  K : ι → Subgroup G
  Δ : Submonoid G
  K_le : ∀ i, ∀ k ∈ K i, k ∈ Δ
  deep : ∀ (j : ι) (S : Finset (ι × G)), ∃ m, K m ≤ K j ∧
    (∀ k ∈ K j, ∀ u ∈ K m, k * u * k⁻¹ ∈ K m) ∧
    ∀ x ∈ S, ∀ u ∈ K m, x.2 * u * x.2⁻¹ ∈ K x.1
  idx : ∀ i j, (K i).relIndex (K j) ≠ 0
  Z : ι → Scheme.{0}
  q : ∀ i, Z i ⟶ B
  tr : ∀ (i j : ι) (h : G), h ∈ Δ → (∀ u ∈ K i, h * u * h⁻¹ ∈ K j) → (Z i ⟶ Z j)
  tr_q : ∀ i j h a b, tr i j h a b ≫ q j = q i
  tr_self : ∀ i k a b, k ∈ K i → tr i i k a b = 𝟙 _
  tr_mul : ∀ i j m h h' a b a' b' a'' b'',
    tr i j h a b ≫ tr j m h' a' b' = tr i m (h' * h) a'' b''
  fin : ∀ i j a b, IsFinite (tr i j 1 a b)
  etale : ∀ i j a b, Etale (tr i j 1 a b)
  onto : ∀ i j a b, Surjective (tr i j 1 a b)
  trans : ∀ i j a b, (∀ k ∈ K j, ∀ u ∈ K i, k * u * k⁻¹ ∈ K i) →
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x y : sp Ω ⟶ Z i),
      x ≫ tr i j 1 a b = y ≫ tr i j 1 a b → ∃ k ∈ K j, ∃ a' b', y = x ≫ tr i i k a' b'
  free : ∀ i j, K i ≤ K j → ∀ k ∈ K j, ∀ a b (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : sp Ω ⟶ Z i),
    x ≫ tr i i k a b = x → k ∈ K i

namespace Tower

variable {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G)

def admitted (i j : X.ι) (h : G) : Prop :=
  h ∈ X.Δ ∧ ∀ u ∈ X.K i, h * u * h⁻¹ ∈ X.K j

structure Endo where
  e : ∀ i, X.Z i ⟶ X.Z i
  e_q : ∀ i, e i ≫ X.q i = X.q i
  comm : ∀ i j h a b, e i ≫ X.tr i j h a b = X.tr i j h a b ≫ e j

end Tower

end UpperTheory.Gal.G3
