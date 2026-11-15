import GaloisForLFunctions.HTGeometry.LinearAlgebra.PolynomialSquareRoot
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Equivariant congruence of bilinear forms

For nondegenerate forms `B` and `C`, the relative automorphism `e` is characterized
by `B(e x,y) = C(x,y)`. If both forms are symmetric, or both are alternating, then
`e` is self-adjoint for `B`. Its polynomial square root gives an isometry from
`C` to `B` over an algebraically closed field of characteristic different from two.

The same isometry commutes with every common similitude having the same multiplier,
and with every endomorphism self-adjoint for both forms. The alternating case is
the algebraic rigidity mechanism in Proposition 4.10 of Garai–Jha–Shekhar,
*p-parity conjecture for Panchishkin Galois representations*.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]


/-- The invertible relative operator characterized by `B(e x,y) = C(x,y)`. -/
def relativeBilinearEquiv (B C : LinearMap.BilinForm K V)
    (hB : B.Nondegenerate) (hC : C.Nondegenerate) : V ≃ₗ[K] V :=
  (C.toDual hC).trans (B.toDual hB).symm

/-- Evaluating the relative operator recovers the second form. -/
theorem relativeBilinearEquiv_apply (B C : LinearMap.BilinForm K V)
    (hB : B.Nondegenerate) (hC : C.Nondegenerate) (x y : V) :
    B (relativeBilinearEquiv B C hB hC x) y = C x y := by
  exact LinearMap.BilinForm.apply_toDual_symm_apply (hB := hB) (C.toDual hC x) y

/-- Alternation of both forms makes their relative operator self-adjoint. -/
theorem relativeBilinearEquiv_selfAdjoint_of_isAlt (B C : LinearMap.BilinForm K V)
    (hB : B.Nondegenerate) (hC : C.Nondegenerate) (hBa : B.IsAlt) (hCa : C.IsAlt) :
    B.IsSelfAdjoint (relativeBilinearEquiv B C hB hC) := by
  intro x y
  calc
    B (relativeBilinearEquiv B C hB hC x) y = C x y :=
      relativeBilinearEquiv_apply B C hB hC x y
    _ = -C y x := (LinearMap.IsAlt.neg hCa y x).symm
    _ = -B (relativeBilinearEquiv B C hB hC y) x := by
      rw [relativeBilinearEquiv_apply]
    _ = B x (relativeBilinearEquiv B C hB hC y) := LinearMap.IsAlt.neg hBa _ _

/-- Symmetry of both forms makes their relative operator self-adjoint. -/
theorem relativeBilinearEquiv_selfAdjoint_of_isSymm (B C : LinearMap.BilinForm K V)
    (hB : B.Nondegenerate) (hC : C.Nondegenerate)
    (hBs : ∀ x y, B x y = B y x) (hCs : ∀ x y, C x y = C y x) :
    B.IsSelfAdjoint (relativeBilinearEquiv B C hB hC) := by
  intro x y
  rw [relativeBilinearEquiv_apply, hCs, hBs, relativeBilinearEquiv_apply]

/-- A common similitude with equal multipliers commutes with the relative operator. -/
theorem relativeBilinearEquiv_commute_similitude (B C : LinearMap.BilinForm K V)
    (hB : B.Nondegenerate) (hC : C.Nondegenerate) (t : V ≃ₗ[K] V) (c : K)
    (hBt : ∀ x y, B (t x) (t y) = c * B x y)
    (hCt : ∀ x y, C (t x) (t y) = c * C x y) :
    Commute (t : Module.End K V) (relativeBilinearEquiv B C hB hC : Module.End K V) := by
  apply LinearMap.ext
  intro x
  apply sub_eq_zero.mp
  apply hB.1
  intro y
  obtain ⟨z, rfl⟩ := t.surjective y
  change B (t (relativeBilinearEquiv B C hB hC x) -
    relativeBilinearEquiv B C hB hC (t x)) (t z) = 0
  rw [map_sub, LinearMap.sub_apply, hBt, relativeBilinearEquiv_apply,
    relativeBilinearEquiv_apply, hCt, sub_self]

/-- A common self-adjoint operator commutes with the relative operator. -/
theorem relativeBilinearEquiv_commute_selfAdjoint (B C : LinearMap.BilinForm K V)
    (hB : B.Nondegenerate) (hC : C.Nondegenerate) (t : Module.End K V)
    (hBt : B.IsSelfAdjoint t) (hCt : C.IsSelfAdjoint t) :
    Commute t (relativeBilinearEquiv B C hB hC : Module.End K V) := by
  apply LinearMap.ext
  intro x
  apply sub_eq_zero.mp
  apply hB.1
  intro y
  change B (t (relativeBilinearEquiv B C hB hC x) -
    relativeBilinearEquiv B C hB hC (t x)) y = 0
  rw [map_sub, LinearMap.sub_apply, hBt, relativeBilinearEquiv_apply,
    relativeBilinearEquiv_apply, hCt, sub_self]

private theorem exists_equivariant_isometry_of_relative_selfAdjoint
    [NeZero (2 : K)] [IsAlgClosed K]
    (B C : LinearMap.BilinForm K V) (hB : B.Nondegenerate) (hC : C.Nondegenerate)
    (he : B.IsSelfAdjoint (relativeBilinearEquiv B C hB hC)) :
    ∃ s : V ≃ₗ[K] V, (∀ x y, B (s x) (s y) = C x y) ∧
      (∀ (t : V ≃ₗ[K] V) (c : K),
        (∀ x y, B (t x) (t y) = c * B x y) →
        (∀ x y, C (t x) (t y) = c * C x y) →
        ∀ x, t (s x) = s (t x)) ∧
      (∀ t : Module.End K V, B.IsSelfAdjoint t → C.IsSelfAdjoint t →
        Commute t (s : Module.End K V)) := by
  let e := relativeBilinearEquiv B C hB hC
  obtain ⟨s, _, hcomm, hforms⟩ := exists_simultaneous_polynomial_square_root e
  obtain ⟨_, hs⟩ := hforms B he
  refine ⟨s, ?_, ?_, ?_⟩
  · intro x y
    rw [hs, ← he]
    exact relativeBilinearEquiv_apply B C hB hC x y
  · intro t c hBt hCt x
    have h := hcomm (t : Module.End K V)
      (relativeBilinearEquiv_commute_similitude B C hB hC t c hBt hCt)
    have hx := congrArg (fun f : Module.End K V => f x) h.eq
    simpa only [Module.End.mul_apply, LinearEquiv.coe_coe] using hx
  · intro t hBt hCt
    exact hcomm t (relativeBilinearEquiv_commute_selfAdjoint B C hB hC t hBt hCt)

/-- Nondegenerate alternating forms admit a single isometry commuting with all their
common similitudes of equal multiplier and all their common self-adjoint operators. -/
theorem exists_equivariant_alternating_isometry [NeZero (2 : K)] [IsAlgClosed K]
    (B C : LinearMap.BilinForm K V) (hB : B.Nondegenerate) (hC : C.Nondegenerate)
    (hBa : B.IsAlt) (hCa : C.IsAlt) :
    ∃ s : V ≃ₗ[K] V, (∀ x y, B (s x) (s y) = C x y) ∧
      (∀ (t : V ≃ₗ[K] V) (c : K),
        (∀ x y, B (t x) (t y) = c * B x y) →
        (∀ x y, C (t x) (t y) = c * C x y) →
        ∀ x, t (s x) = s (t x)) ∧
      (∀ t : Module.End K V, B.IsSelfAdjoint t → C.IsSelfAdjoint t →
        Commute t (s : Module.End K V)) :=
  exists_equivariant_isometry_of_relative_selfAdjoint B C hB hC
    (relativeBilinearEquiv_selfAdjoint_of_isAlt B C hB hC hBa hCa)

/-- Nondegenerate symmetric forms admit a single isometry commuting with all their
common similitudes of equal multiplier and all their common self-adjoint operators. -/
theorem exists_equivariant_symmetric_isometry [NeZero (2 : K)] [IsAlgClosed K]
    (B C : LinearMap.BilinForm K V) (hB : B.Nondegenerate) (hC : C.Nondegenerate)
    (hBs : ∀ x y, B x y = B y x) (hCs : ∀ x y, C x y = C y x) :
    ∃ s : V ≃ₗ[K] V, (∀ x y, B (s x) (s y) = C x y) ∧
      (∀ (t : V ≃ₗ[K] V) (c : K),
        (∀ x y, B (t x) (t y) = c * B x y) →
        (∀ x y, C (t x) (t y) = c * C x y) →
        ∀ x, t (s x) = s (t x)) ∧
      (∀ t : Module.End K V, B.IsSelfAdjoint t → C.IsSelfAdjoint t →
        Commute t (s : Module.End K V)) :=
  exists_equivariant_isometry_of_relative_selfAdjoint B C hB hC
    (relativeBilinearEquiv_selfAdjoint_of_isSymm B C hB hC hBs hCs)

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.exists_equivariant_alternating_isometry
#print axioms GaloisForLFunctions.HTGeometry.exists_equivariant_symmetric_isometry
