import GaloisForLFunctions.RHTower.KRealKernelCokernel
import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Real cyclic modules and the algebra-quotient typing obstruction

Connes--Consani--Marcolli's relative object is a cokernel in the abelian category of cyclic
modules.  It is not, merely from that construction, a quotient algebra.  This file supplies a
literal cyclic-module interface: the simplicial identities are carried by a mathlib
`SimplicialObject`, while the extra cyclic generator satisfies Connes' order, face, and
degeneracy relations.  Morphisms commute with the whole simplicial object and with the cyclic
generator.

The second part isolates the exact obstruction to treating a linear cokernel as an algebra
quotient.  If multiplication on a quotient module is compatible with multiplication of
representatives and has the two zero laws, then the quotienting submodule must absorb
multiplication on both sides.  Thus an idempotent has no literal image in a CCM cyclic cokernel
until a two-sided-ideal theorem has been proved.  A cyclic Chern class remains type-correct and
does not require such an algebra structure.

No analytic completion, arithmetic comparison, positivity, zero-spectrum statement, or
Riemann-hypothesis premise occurs here.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.SimplicialObject
open scoped Simplicial

universe u v

namespace GaloisForLFunctions
namespace RHTower

/-- Iterated composition of an endomorphism in an arbitrary category. -/
def categoricalEndIterate {C : Type u} [Category.{v} C] {X : C}
    (f : X ⟶ X) : ℕ → (X ⟶ X)
  | 0 => 𝟙 X
  | n + 1 => categoricalEndIterate f n ≫ f

@[simp]
theorem categoricalEndIterate_zero {C : Type u} [Category.{v} C] {X : C}
    (f : X ⟶ X) : categoricalEndIterate f 0 = 𝟙 X :=
  rfl

@[simp]
theorem categoricalEndIterate_succ {C : Type u} [Category.{v} C] {X : C}
    (f : X ⟶ X) (n : ℕ) :
    categoricalEndIterate f (n + 1) = categoricalEndIterate f n ≫ f :=
  rfl

/--
A cyclic `R`-module: a simplicial module together with Connes' cyclic generator in every
degree.  Face and degeneracy conventions agree with the rotation
`(a₀,...,aₙ) ↦ (aₙ,a₀,...,aₙ₋₁)`.
-/
structure CyclicModule (R : Type u) [CommRing R] where
  simplicial : SimplicialObject (ModuleCat.{v} R)
  cyclic : ∀ n : ℕ, simplicial _⦋n⦌ ⟶ simplicial _⦋n⦌
  cyclic_order : ∀ n, categoricalEndIterate (cyclic n) (n + 1) = 𝟙 _
  cyclic_face_zero : ∀ n,
    cyclic (n + 1) ≫ simplicial.δ (0 : Fin (n + 2)) =
      simplicial.δ (Fin.last (n + 1))
  cyclic_face_succ : ∀ n (i : Fin (n + 1)),
    cyclic (n + 1) ≫ simplicial.δ i.succ =
      simplicial.δ (Fin.castSucc i) ≫ cyclic n
  cyclic_degeneracy_zero : ∀ n,
    cyclic n ≫ simplicial.σ (0 : Fin (n + 1)) =
      simplicial.σ (Fin.last n) ≫ cyclic (n + 1) ≫ cyclic (n + 1)
  cyclic_degeneracy_succ : ∀ n (i : Fin n),
    cyclic n ≫ simplicial.σ i.succ =
      simplicial.σ (Fin.castSucc i) ≫ cyclic (n + 1)

namespace CyclicModule

variable {R : Type u} [CommRing R]

/-- Morphism of cyclic modules, including cyclic-generator naturality. -/
structure Hom (X Y : CyclicModule R) where
  simplicial : X.simplicial ⟶ Y.simplicial
  cyclic_naturality : ∀ n,
    X.cyclic n ≫ simplicial.app (.op (.mk n)) =
      simplicial.app (.op (.mk n)) ≫ Y.cyclic n

@[ext]
theorem Hom.ext {X Y : CyclicModule R} (f g : Hom X Y)
    (h : f.simplicial = g.simplicial) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- Identity morphism of a cyclic module. -/
def Hom.id (X : CyclicModule R) : Hom X X where
  simplicial := 𝟙 X.simplicial
  cyclic_naturality n := by simp

/-- Composition of cyclic-module morphisms. -/
def Hom.comp {X Y Z : CyclicModule R} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  simplicial := f.simplicial ≫ g.simplicial
  cyclic_naturality n := by
    simp only [NatTrans.comp_app]
    calc
      X.cyclic n ≫
          (f.simplicial.app (.op (.mk n)) ≫ g.simplicial.app (.op (.mk n))) =
        (X.cyclic n ≫ f.simplicial.app (.op (.mk n))) ≫
          g.simplicial.app (.op (.mk n)) := (Category.assoc _ _ _).symm
      _ = (f.simplicial.app (.op (.mk n)) ≫ Y.cyclic n) ≫
          g.simplicial.app (.op (.mk n)) := by rw [f.cyclic_naturality]
      _ = f.simplicial.app (.op (.mk n)) ≫
          (Y.cyclic n ≫ g.simplicial.app (.op (.mk n))) :=
        Category.assoc _ _ _
      _ = f.simplicial.app (.op (.mk n)) ≫
          (g.simplicial.app (.op (.mk n)) ≫ Z.cyclic n) := by
        rw [g.cyclic_naturality]
      _ = (f.simplicial.app (.op (.mk n)) ≫
          g.simplicial.app (.op (.mk n))) ≫ Z.cyclic n :=
        (Category.assoc _ _ _).symm

/-- A Real or quaternionic structure on every degree of a cyclic module. -/
structure KReal (odd : Bool) (X : CyclicModule ℂ) where
  real : ∀ n, KRealStructure odd (X.simplicial _⦋n⦌)
  face_naturality : ∀ n (i : Fin (n + 2)) (x : X.simplicial _⦋n + 1⦌),
    (real n).sigma (X.simplicial.δ i x) =
      X.simplicial.δ i ((real (n + 1)).sigma x)
  degeneracy_naturality : ∀ n (i : Fin (n + 1)) (x : X.simplicial _⦋n⦌),
    (real (n + 1)).sigma (X.simplicial.σ i x) =
      X.simplicial.σ i ((real n).sigma x)
  cyclic_naturality : ∀ n (x : X.simplicial _⦋n⦌),
    (real n).sigma (X.cyclic n x) = X.cyclic n ((real n).sigma x)

/-- A cyclic morphism equivariant for degreewise Real/quaternionic structures. -/
structure KRealHom {odd : Bool} {X Y : CyclicModule ℂ}
    (KX : KReal odd X) (KY : KReal odd Y) extends Hom X Y where
  real_naturality : ∀ n (x : X.simplicial _⦋n⦌),
    (KY.real n).sigma (toHom.simplicial.app (.op (.mk n)) x) =
      toHom.simplicial.app (.op (.mk n)) ((KX.real n).sigma x)

end CyclicModule

section QuotientTyping

variable {R A : Type*} [CommRing R] [Ring A] [Module R A]

/-- A scalar submodule of a possibly noncommutative algebra absorbs both-sided products. -/
def IsTwoSidedSubmodule (S : Submodule R A) : Prop :=
  (∀ a s, s ∈ S → a * s ∈ S) ∧
    (∀ s a, s ∈ S → s * a ∈ S)

/--
Necessary typing law for multiplication on a linear quotient: compatibility with representatives
forces the quotienting submodule to be two-sided.  No associativity or distributivity on the
putative quotient multiplication is needed for this obstruction.
-/
theorem quotient_multiplication_forces_twoSided
    (S : Submodule R A) [Mul (A ⧸ S)]
    (hmul_zero : ∀ x : A ⧸ S, x * 0 = 0)
    (hzero_mul : ∀ x : A ⧸ S, 0 * x = 0)
    (hdesc : ∀ a b : A, S.mkQ (a * b) = S.mkQ a * S.mkQ b) :
    IsTwoSidedSubmodule S := by
  constructor
  · intro a s hs
    rw [← S.ker_mkQ]
    rw [LinearMap.mem_ker, hdesc]
    have hz : S.mkQ s = 0 := by
      rw [← LinearMap.mem_ker, S.ker_mkQ]
      exact hs
    rw [hz, hmul_zero]
  · intro s a hs
    rw [← S.ker_mkQ]
    rw [LinearMap.mem_ker, hdesc]
    have hz : S.mkQ s = 0 := by
      rw [← LinearMap.mem_ker, S.ker_mkQ]
      exact hs
    rw [hz, hzero_mul]

/-- Contrapositive: a non-two-sided linear cokernel cannot carry descended multiplication. -/
theorem no_descended_quotient_multiplication_of_not_twoSided
    (S : Submodule R A) (hS : ¬IsTwoSidedSubmodule S) :
    ¬∃ (_ : Mul (A ⧸ S)),
      (∀ x : A ⧸ S, x * 0 = 0) ∧
      (∀ x : A ⧸ S, 0 * x = 0) ∧
      ∀ a b : A, S.mkQ (a * b) = S.mkQ a * S.mkQ b := by
  rintro ⟨inst, hmul_zero, hzero_mul, hdesc⟩
  letI : Mul (A ⧸ S) := inst
  exact hS (quotient_multiplication_forces_twoSided S hmul_zero hzero_mul hdesc)

end QuotientTyping

end RHTower
end GaloisForLFunctions
