import GaloisForLFunctions.HTGeometry.LinearAlgebra.EquivariantBilinearIsometry
import GaloisForLFunctions.HTGeometry.SymplecticDoublingFree

/-!
# Equivariant uniqueness of doubled symplectic realizations

Over an algebraically closed field of characteristic different from two,
two nondegenerate symmetric forms making the same operator family self-adjoint
are isometric through one map commuting with that family. Its diagonal lift
identifies their doubled alternating forms and preserves both summands.

Thus the auxiliary symmetric form used in symplectic doubling does not change
the equivariant isometry class, even for a nonsemisimple operator family.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
variable {K V : Type*} [Field K] [NeZero (2 : K)] [IsAlgClosed K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]


/-- One change of basis identifies the original forms and their symplectic doubles,
while commuting with every endomorphism self-adjoint for both original forms. -/
theorem exists_doubledForm_equivariant_isometry
    (S T : LinearMap.BilinForm K V) (hS : S.Nondegenerate) (hT : T.Nondegenerate)
    (hSs : ∀ x y, S x y = S y x) (hTs : ∀ x y, T x y = T y x) :
    ∃ s : V ≃ₗ[K] V, (∀ x y, S (s x) (s y) = T x y) ∧
      (∀ x y, doubledForm S (s.prodCongr s x) (s.prodCongr s y) = doubledForm T x y) ∧
      ∀ t : Module.End K V, S.IsSelfAdjoint t → T.IsSelfAdjoint t →
        Commute t (s : Module.End K V) ∧
        Commute (t.prodMap t) (s.prodCongr s : Module.End K (V × V)) := by
  obtain ⟨s, hs, _, ht⟩ := exists_equivariant_symmetric_isometry S T hS hT hSs hTs
  refine ⟨s, hs, ?_, ?_⟩
  · intro x y
    simp only [doubledForm_apply, LinearEquiv.prodCongr_apply, hs]
  · intro t hSt hTt
    have hc := ht t hSt hTt
    refine ⟨hc, ?_⟩
    have hpoint (x : V) : t (s x) = s (t x) := by
      have h := congrArg (fun f : Module.End K V => f x) hc.eq
      simpa only [Module.End.mul_apply, LinearEquiv.coe_coe] using h
    apply LinearMap.ext
    intro x
    exact Prod.ext (hpoint x.1) (hpoint x.2)

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.exists_doubledForm_equivariant_isometry
