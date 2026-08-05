import GaloisForLFunctions.HTGeometry.QuantumOrientationFracture

/-!
# Associative products exist

The orientation-fracture laws are stated for an arbitrary binary product, with associativity as an
interface.  Every semigroup multiplication satisfies it, and so do the two projections — which
between them show that associativity alone forces neither commutativity nor cancellation.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **Every semigroup multiplication is an associative product.** -/
theorem isAssociativeProduct_mul {A : Type u} [Semigroup A] :
    IsAssociativeProduct (fun x y : A => x * y) := fun x y z => mul_assoc x y z

/-- The left projection is an associative product. -/
theorem isAssociativeProduct_left {A : Type u} :
    IsAssociativeProduct (fun x _ : A => x) := fun _ _ _ => rfl

/-- The right projection is an associative product. -/
theorem isAssociativeProduct_right {A : Type u} :
    IsAssociativeProduct (fun _ y : A => y) := fun _ _ _ => rfl

end GaloisForLFunctions.HTGeometry
