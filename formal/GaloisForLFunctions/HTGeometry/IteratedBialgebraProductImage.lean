import GaloisForLFunctions.HTGeometry.TensorProductAlgClosedDomain
import GaloisForLFunctions.HTGeometry.FiniteTypePrimeChainStabilization
import Mathlib.RingTheory.Bialgebra.Basic

/-!
# Iterated product images of affine bialgebras

For a map from an affine bialgebra into a finite-type domain, this file constructs the coordinate
maps of all nonempty finite products.  If the source variety contains the identity, the prime
image kernels form an antitone sequence, hence stabilize by finite Krull dimension.
-/

open scoped TensorProduct
open Coalgebra Bialgebra

namespace GaloisForLFunctions.HTGeometry

universe u

noncomputable section

/-- A universe-preserving bundled commutative algebra used by the recursive tensor construction. -/
structure CommAlgebraBundle (k : Type u) [CommRing k] where
  carrier : Type u
  [commRing : CommRing carrier]
  [algebra : Algebra k carrier]

/-- The recursively bundled tensor product of `m+1` copies of `B`. -/
@[reducible] noncomputable def iteratedTensorAlgebraBundle
    (k B : Type u) [CommRing k] [CommRing B] [Algebra k B] :
    ℕ → CommAlgebraBundle k
  | 0 => { carrier := B }
  | Nat.succ m => by
      let T := iteratedTensorAlgebraBundle k B m
      letI := T.commRing
      letI := T.algebra
      exact { carrier := B ⊗[k] T.carrier }

/-- Tensor product of `m+1` copies of a commutative `k`-algebra. -/
abbrev IteratedTensorAlgebra
    (k B : Type u) [CommRing k] [CommRing B] [Algebra k B] (m : ℕ) : Type u :=
  (iteratedTensorAlgebraBundle k B m).carrier

noncomputable instance iteratedTensorAlgebraCommRing
    (k B : Type u) [CommRing k] [CommRing B] [Algebra k B] (m : ℕ) :
    CommRing (IteratedTensorAlgebra k B m) :=
  (iteratedTensorAlgebraBundle k B m).commRing

noncomputable instance iteratedTensorAlgebraAlgebra
    (k B : Type u) [CommRing k] [CommRing B] [Algebra k B] (m : ℕ) :
    Algebra k (IteratedTensorAlgebra k B m) :=
  (iteratedTensorAlgebraBundle k B m).algebra

/-- Every nonempty finite tensor power of a finite-type domain over an algebraically closed field
is a domain. -/
theorem iteratedTensorAlgebra_isDomain
    (k B : Type u) [Field k] [IsAlgClosed k] [CommRing B] [Algebra k B]
    [IsDomain B] [Algebra.FiniteType k B] (m : ℕ) :
    IsDomain (IteratedTensorAlgebra k B m) := by
  induction m with
  | zero =>
      change IsDomain B
      exact inferInstance
  | succ m ih =>
      change IsDomain (B ⊗[k] (iteratedTensorAlgebraBundle k B m).carrier)
      letI := (iteratedTensorAlgebraBundle k B m).commRing
      letI := (iteratedTensorAlgebraBundle k B m).algebra
      letI := ih
      exact isDomain_tensorProduct_of_finiteType

/-- Tensor product of two algebra homomorphisms. -/
def tensorAlgHom
    {k A₁ A₂ B₁ B₂ : Type u} [CommRing k]
    [CommRing A₁] [CommRing A₂] [CommRing B₁] [CommRing B₂]
    [Algebra k A₁] [Algebra k A₂] [Algebra k B₁] [Algebra k B₂]
    (f : A₁ →ₐ[k] B₁) (g : A₂ →ₐ[k] B₂) :
    A₁ ⊗[k] A₂ →ₐ[k] B₁ ⊗[k] B₂ :=
  Algebra.TensorProduct.lift
    ((Algebra.TensorProduct.includeLeft : B₁ →ₐ[k] B₁ ⊗[k] B₂).comp f)
    ((Algebra.TensorProduct.includeRight : B₂ →ₐ[k] B₁ ⊗[k] B₂).comp g)
    (fun _ _ => Commute.all _ _)

@[simp] theorem tensorAlgHom_tmul
    {k A₁ A₂ B₁ B₂ : Type u} [CommRing k]
    [CommRing A₁] [CommRing A₂] [CommRing B₁] [CommRing B₂]
    [Algebra k A₁] [Algebra k A₂] [Algebra k B₁] [Algebra k B₂]
    (f : A₁ →ₐ[k] B₁) (g : A₂ →ₐ[k] B₂) (a : A₁) (b : A₂) :
    tensorAlgHom f g (a ⊗ₜ[k] b) = f a ⊗ₜ[k] g b := by
  simp [tensorAlgHom]

/-- Pullback on coordinate algebras for an `(m+1)`-fold product of the same affine map. -/
def iteratedProductMap
    {k A B : Type u} [CommRing k] [CommRing A] [CommRing B]
    [Algebra k B] [Bialgebra k A]
    (f : A →ₐ[k] B) : (m : ℕ) → A →ₐ[k] IteratedTensorAlgebra k B m
  | 0 => f
  | Nat.succ m =>
      (tensorAlgHom f (iteratedProductMap f m)).comp (Bialgebra.comulAlgHom k A)

/-- Specialize the head tensor factor at one `k`-point. -/
@[reducible] def iteratedTensorHeadSpecialization
    {k B : Type u} [CommRing k] [CommRing B] [Algebra k B]
    (e : B →ₐ[k] k) (m : ℕ) :
    IteratedTensorAlgebra k B (m + 1) →ₐ[k] IteratedTensorAlgebra k B m := by
  change (B ⊗[k] (iteratedTensorAlgebraBundle k B m).carrier) →ₐ[k]
    (iteratedTensorAlgebraBundle k B m).carrier
  letI := (iteratedTensorAlgebraBundle k B m).commRing
  letI := (iteratedTensorAlgebraBundle k B m).algebra
  exact Algebra.TensorProduct.lift
    ((Algebra.ofId k (IteratedTensorAlgebra k B m)).comp e)
    (AlgHom.id k (IteratedTensorAlgebra k B m))
    (fun _ _ => Commute.all _ _)

@[simp] theorem iteratedTensorHeadSpecialization_tmul
    {k B : Type u} [CommRing k] [CommRing B] [Algebra k B]
    (e : B →ₐ[k] k) (m : ℕ) (b : B) (t : IteratedTensorAlgebra k B m) :
    iteratedTensorHeadSpecialization e m (b ⊗ₜ[k] t) = e b • t := by
  change algebraMap k (IteratedTensorAlgebra k B m) (e b) * t = e b • t
  rw [Algebra.smul_def]

/-- If `e` maps the original affine map to the bialgebra counit, specializing the first product
factor at `e` removes that factor. -/
theorem iteratedTensorHeadSpecialization_comp_iteratedProductMap
    {k A B : Type u} [CommRing k] [CommRing A] [CommRing B]
    [Algebra k B] [Bialgebra k A]
    (f : A →ₐ[k] B) (e : B →ₐ[k] k)
    (he : e.comp f = Bialgebra.counitAlgHom k A) (m : ℕ) :
    (iteratedTensorHeadSpecialization e m).comp (iteratedProductMap f (m + 1)) =
      iteratedProductMap f m := by
  ext a
  change iteratedTensorHeadSpecialization e m
      (tensorAlgHom f (iteratedProductMap f m)
        (Bialgebra.comulAlgHom k A a)) = iteratedProductMap f m a
  let g := iteratedProductMap f m
  let Ψ : k ⊗[k] A →ₐ[k] IteratedTensorAlgebra k B m :=
    Algebra.TensorProduct.lift
      (Algebra.ofId k (IteratedTensorAlgebra k B m)) g
      (fun _ _ => Commute.all _ _)
  have hfactor (z : A ⊗[k] A) :
      iteratedTensorHeadSpecialization e m (tensorAlgHom f g z) =
        Ψ (TensorProduct.map (Bialgebra.counitAlgHom k A).toLinearMap
          (LinearMap.id (R := k) (M := A)) z) := by
    induction z using TensorProduct.induction_on with
    | zero => exact map_zero _
    | add x y hx hy =>
        rw [map_add, map_add, hx, hy, map_add]
        exact (map_add Ψ _ _).symm
    | tmul x y =>
        have hex : e (f x) = Bialgebra.counitAlgHom k A x :=
          DFunLike.congr_fun he x
        rw [tensorAlgHom_tmul, iteratedTensorHeadSpecialization_tmul]
        simp [Ψ, hex, Algebra.smul_def]
  rw [hfactor]
  have hcounit := DFunLike.congr_fun
    (Coalgebra.rTensor_counit_comp_comul (R := k) (A := A)) a
  change TensorProduct.map (Bialgebra.counitAlgHom k A).toLinearMap
      (LinearMap.id (R := k) (M := A)) (Bialgebra.comulAlgHom k A a) =
    (1 : k) ⊗ₜ[k] a at hcounit
  rw [hcounit]
  simp [Ψ, g]

/-- Prime ideal cutting out the closure of the image of an `(m+1)`-fold product map. -/
def iteratedProductKernel
    {k A B : Type u} [CommRing k] [CommRing A] [CommRing B]
    [Algebra k B] [Bialgebra k A]
    (f : A →ₐ[k] B) (m : ℕ) : Ideal A :=
  RingHom.ker (iteratedProductMap f m).toRingHom

/-- Iterated product-image kernels are prime when the source variety is an integral finite-type
affine variety over an algebraically closed field. -/
theorem iteratedProductKernel_isPrime
    {k A B : Type u} [Field k] [IsAlgClosed k] [CommRing A] [CommRing B]
    [Algebra k B] [Bialgebra k A] [IsDomain B] [Algebra.FiniteType k B]
    (f : A →ₐ[k] B) (m : ℕ) :
    (iteratedProductKernel f m).IsPrime := by
  letI : IsDomain (IteratedTensorAlgebra k B m) :=
    iteratedTensorAlgebra_isDomain k B m
  exact RingHom.ker_isPrime (iteratedProductMap f m).toRingHom

/-- Adding an identity-valued factor can only shrink the product-image kernel. -/
theorem iteratedProductKernel_succ_le
    {k A B : Type u} [CommRing k] [CommRing A] [CommRing B]
    [Algebra k B] [Bialgebra k A]
    (f : A →ₐ[k] B) (e : B →ₐ[k] k)
    (he : e.comp f = Bialgebra.counitAlgHom k A) (m : ℕ) :
    iteratedProductKernel f (m + 1) ≤ iteratedProductKernel f m := by
  intro a ha
  change iteratedProductMap f m a = 0
  have hmap := congrArg (iteratedTensorHeadSpecialization e m) ha
  change iteratedTensorHeadSpecialization e m (iteratedProductMap f (m + 1) a) =
    iteratedTensorHeadSpecialization e m 0 at hmap
  rw [map_zero] at hmap
  have hcomp := DFunLike.congr_fun
    (iteratedTensorHeadSpecialization_comp_iteratedProductMap f e he m) a
  exact hcomp ▸ hmap

/-- Product-image kernels form an antitone sequence when the original image contains identity. -/
theorem iteratedProductKernel_antitone
    {k A B : Type u} [CommRing k] [CommRing A] [CommRing B]
    [Algebra k B] [Bialgebra k A]
    (f : A →ₐ[k] B) (e : B →ₐ[k] k)
    (he : e.comp f = Bialgebra.counitAlgHom k A) :
    Antitone (iteratedProductKernel f) :=
  antitone_nat_of_succ_le (iteratedProductKernel_succ_le f e he)

/-- Prime kernels of nonempty finite product images eventually stabilize. -/
theorem exists_iteratedProductKernel_stabilizes
    {k A B : Type u} [Field k] [IsAlgClosed k] [CommRing A] [CommRing B]
    [Nontrivial A] [Algebra k B] [Bialgebra k A]
    [Algebra.FiniteType k A] [IsDomain B] [Algebra.FiniteType k B]
    (f : A →ₐ[k] B) (e : B →ₐ[k] k)
    (he : e.comp f = Bialgebra.counitAlgHom k A) :
    ∃ m, iteratedProductKernel f (m + 1) = iteratedProductKernel f m := by
  exact exists_eq_succ_of_antitone_prime (k := k) (R := A)
    (iteratedProductKernel f)
    (iteratedProductKernel_isPrime (k := k) f)
    (iteratedProductKernel_antitone f e he)

end

end GaloisForLFunctions.HTGeometry
