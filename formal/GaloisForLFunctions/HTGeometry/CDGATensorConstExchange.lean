import GaloisForLFunctions.HTGeometry.CDGATensorSingle
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Tensoring with a constant module passes through the graded tensor product

The carrier of a graded tensor product is a product over the finitely many decompositions of the
total degree, and a *finite* product commutes with tensoring.  So tensoring degreewise with a fixed
module can be moved from the second graded factor to the outside.

Finiteness is what makes this work, and it is available: `tensorIndexFintype` says the bidegrees of
a fixed total degree form a finite type.

* `HTGeometry.tensorConstExchange` : the exchange, degreewise.
-/

universe u v w

namespace GaloisForLFunctions.HTGeometry

variable {R : Type u} [CommRing R]
  {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  {N : ℕ → Type w} [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)]

/-- **Tensoring with a constant module passes through the graded tensor product.**  The bidegrees of
a fixed total degree are finite, and a finite product commutes with tensoring. -/
noncomputable def tensorConstExchange (V : Type w) [AddCommGroup V] [Module R V] (n : ℕ) :
    TensorProduct R (TensorCarrier (R := R) M N n) V
      ≃ₗ[R] TensorCarrier (R := R) M (fun m => TensorProduct R (N m) V) n :=
  (TensorProduct.comm R (TensorCarrier (R := R) M N n) V).trans
    ((TensorProduct.piRight R R V (fun p : {ab : ℕ × ℕ // ab.1 + ab.2 = n} =>
        TensorProduct R (M p.1.1) (N p.1.2))).trans
      (LinearEquiv.piCongrRight fun p =>
        (TensorProduct.comm R V (TensorProduct R (M p.1.1) (N p.1.2))).trans
          (TensorProduct.assoc R (M p.1.1) (N p.1.2) V)))

theorem tensorConstExchange_bijective (V : Type w) [AddCommGroup V] [Module R V] (n : ℕ) :
    Function.Bijective (tensorConstExchange (R := R) (M := M) (N := N) V n) :=
  (tensorConstExchange (R := R) (M := M) (N := N) V n).bijective

end GaloisForLFunctions.HTGeometry
