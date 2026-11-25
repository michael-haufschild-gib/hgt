import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.Projection
import Mathlib.Algebra.Polynomial.Div

/-! # A nonzero equation survives specialization at a limiting boundary height -/

open Set Filter Polynomial Topology
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates
noncomputable section
variable {A X : Type*} [CommRing A] [TopologicalSpace X]

/-- At a limit of boundary points off a prescribed height, a nonzero
base equation must vanish. Removing the maximal power of the height
factor before taking closure also detects tangential first crossings. -/
theorem FinitelyCertified.boundary_slice {ρ : X → A →+* ℝ} (hc : ∀ a, Continuous fun x => ρ x a)
    {S : Set (X × ℝ)} (hs : FinitelyCertified (appendEval ρ) S) (a : A) :
    ∃ B : Finset A, 0∉B ∧ ∀ x : X,
      (x,ρ x a)∈closure ((S \ interior S) ∩ {z | z.2≠ρ z.1 a}) →
      ∃ b∈B, ρ x b=0 := by
  classical
  obtain ⟨T,hT⟩ := hs
  let F := T.erase 0
  let Q (p : A[X]) := p /ₘ (Polynomial.X-C a)^p.rootMultiplicity a
  let c (p : A[X]) := (Q p).eval a
  let W := ⋃ p : F, {z : X × ℝ | appendEval ρ z (Q p)=0}
  have hW : IsClosed W := isClosed_iUnion_of_finite fun p =>
    isClosed_eq (continuous_appendEval ρ hc (Q p)) continuous_const
  have hsub : (S \ interior S) ∩ {z | z.2≠ρ z.1 a} ⊆ W := by
    rintro z ⟨⟨hz,hn⟩,hd⟩
    obtain ⟨p,hp,hzero,hlocal⟩ := hT z hz
    have hne : p≠0 := by
      rintro rfl
      apply hn
      apply mem_interior_iff_mem_nhds.mpr
      exact hlocal.mono fun w hw => hw (map_zero _)
    have hdiff : appendEval ρ z (Polynomial.X-C a)≠0 := by
      change eval₂ (ρ z.1) z.2 (Polynomial.X-C a)≠0
      rwa [eval₂_sub,eval₂_X,eval₂_C,sub_ne_zero]
    have hprod := congrArg (appendEval ρ z) (pow_mul_divByMonic_rootMultiplicity_eq p a)
    rw [map_mul,map_pow] at hprod
    exact mem_iUnion.mpr ⟨⟨p,Finset.mem_erase.mpr ⟨hne,hp⟩⟩,
      (mul_eq_zero.mp (hprod.trans hzero)).resolve_left (pow_ne_zero _ hdiff)⟩
  refine ⟨F.image c,?_,?_⟩
  · rintro h
    obtain ⟨p,hp,hzero⟩ := Finset.mem_image.mp h
    exact eval_divByMonic_pow_rootMultiplicity_ne_zero a (Finset.mem_erase.mp hp).1 hzero
  · intro x hx
    obtain ⟨p,hp⟩ := mem_iUnion.mp (closure_minimal hsub hW hx)
    refine ⟨c p,Finset.mem_image_of_mem c p.property,?_⟩
    change (Q p).eval₂ (ρ x) (ρ x a)=0 at hp
    rwa [eval₂_at_apply] at hp

#print axioms FinitelyCertified.boundary_slice
end
end GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates
