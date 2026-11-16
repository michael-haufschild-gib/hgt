import Mathlib.RingTheory.FiniteType

/-!
# Finite-valued points of finitely generated algebras

An algebra map is determined by its values on a finite generating set.
Consequently, maps into a finite algebra form a finite set.
-/

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- A finitely generated algebra has finitely many points in every finite target algebra. -/
instance finiteTypeAlgebraPoints_finite (K B E : Type*)
    [CommSemiring K] [Semiring B] [Semiring E] [Algebra K B] [Algebra K E]
    [Algebra.FiniteType K B] [Finite E] : Finite (B →ₐ[K] E) := by
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out (R := K) (A := B))
  refine Finite.of_injective (fun f : B →ₐ[K] E => fun x : s => f x) ?_
  intro f g h
  apply AlgHom.ext_of_adjoin_eq_top hs
  intro x hx
  exact congrFun h ⟨x, hx⟩

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
