import GaloisForLFunctions.HTGeometry.TorsorDecomposition
import GaloisForLFunctions.HTGeometry.PointsSeparateModule
import GaloisForLFunctions.HTGeometry.TensorProductAlgClosedReduced
import GaloisForLFunctions.HTGeometry.TensorSquareEqualizer

/-!
# Points of the torsor separate, with coefficients in the Picard--Vessiot ring

`PointSeparatingTorsorAction.fixedByPoints_eq_range` reduces the Galois correspondence to *joint
injectivity* of the rational-point evaluations, and `AffineRationalPointSeparation` supplies that
injectivity when the coefficients of the tensor product form a field.  A Picard--Vessiot ring is not
a field, so this file proves the injectivity with coefficients in the ring: through the torsor
decomposition `R ⊗_C E ≅ A`, an element of `A` killed by every `C`-point of `E` is zero.

Applied to `A = R ⊗_K R` and the element `a ⊗ 1 - 1 ⊗ a`, this is the correspondence itself: an
element of `R` fixed by every specialization lies in the base field.
-/

open scoped TensorProduct

namespace GaloisForLFunctions.HTGeometry

open Module

noncomputable section

variable {C R A : Type*} [Field C] [CommRing R] [CommRing A]
  [Algebra C R] [Algebra C A] [Algebra R A] [IsScalarTower C R A]

/-- Evaluation of the torsor coordinates at a point of the acting algebra. -/
def pointAlgHom (E : Subalgebra C A) (χ : ↥E →ₐ[C] C) : (R ⊗[C] ↥E) →ₐ[R] R :=
  Algebra.TensorProduct.lift (AlgHom.id R R) ((Algebra.ofId C R).comp χ)
    (fun _ _ => Commute.all _ _)

omit [Algebra R A] [IsScalarTower C R A] in
@[simp] theorem pointAlgHom_tmul (E : Subalgebra C A) (χ : ↥E →ₐ[C] C) (r : R) (e : ↥E) :
    pointAlgHom (R := R) E χ (r ⊗ₜ[C] e) = χ e • r := by
  rw [pointAlgHom, Algebra.TensorProduct.lift_tmul]
  simp [Algebra.smul_def, mul_comm]

/-- The `R`-algebra map attached to a point of the acting algebra. -/
def torsorPointHom (E : Subalgebra C A) {ι : Type*} (b : Basis ι C ↥E)
    (hgen : Algebra.adjoin C (Set.range (algebraMap R A) ∪ (E : Set A)) = ⊤)
    (hindep : LinearIndependent R (fun i => ((b i : ↥E) : A)))
    (χ : ↥E →ₐ[C] C) : A →ₐ[R] R :=
  (pointAlgHom (R := R) E χ).comp
    (tensorDecompositionEquiv (R := R) E b hgen hindep).symm.toAlgHom

/-- **Points of the torsor separate, with coefficients in the ring.** -/
theorem eq_zero_of_forall_torsorPointHom_eq_zero
    [IsAlgClosed C] (E : Subalgebra C A) [IsReduced ↥E] [Algebra.FiniteType C ↥E]
    {ι : Type*} (b : Basis ι C ↥E)
    (hgen : Algebra.adjoin C (Set.range (algebraMap R A) ∪ (E : Set A)) = ⊤)
    (hindep : LinearIndependent R (fun i => ((b i : ↥E) : A)))
    {x : A} (h : ∀ χ : ↥E →ₐ[C] C, torsorPointHom (R := R) E b hgen hindep χ x = 0) :
    x = 0 := by
  classical
  set eqv := tensorDecompositionEquiv (R := R) E b hgen hindep with heqv
  set z : R ⊗[C] ↥E := eqv.symm x with hz
  obtain ⟨t, r, hrep⟩ := exists_basis_tmul_repr b z
  have hsum : ∀ χ : ↥E →ₐ[C] C, (∑ i ∈ t, χ (b i) • r i) = 0 := by
    intro χ
    have hval := h χ
    rw [torsorPointHom, AlgHom.comp_apply] at hval
    change pointAlgHom (R := R) E χ z = 0 at hval
    rw [hrep, map_sum] at hval
    simpa only [pointAlgHom_tmul] using hval
  have hzero : ∀ i ∈ t, r i = 0 := by
    intro i hi
    set m := t.card with hm
    set ee : Fin m ≃ {j // j ∈ t} := (t.equivFin).symm with hee
    have hindepFin : LinearIndependent C (fun k : Fin m => b (ee k : ι)) := by
      refine b.linearIndependent.comp (fun k : Fin m => (ee k : ι)) ?_
      intro k₁ k₂ hk
      exact ee.injective (Subtype.ext hk)
    have hb : ∀ c : Fin m → C, (∑ j, c j • b (ee j : ι)) = 0 → ∀ j, c j = 0 := by
      intro c hc j
      exact Fintype.linearIndependent_iff.mp hindepFin c hc j
    have hpoint : ∀ χ : ↥E →ₐ[C] C, (∑ j : Fin m, χ (b (ee j : ι)) • r (ee j : ι)) = 0 := by
      intro χ
      have hs := hsum χ
      rw [← Finset.sum_coe_sort t (fun i => χ (b i) • r i)] at hs
      rw [← hs]
      exact Fintype.sum_equiv ee _ _ (fun k => rfl)
    have hall := eq_zero_of_forall_point_smul_eq_zero (M := R)
      (fun j : Fin m => b (ee j : ι)) hb (fun j : Fin m => r (ee j : ι)) hpoint
    have hk := hall (ee.symm ⟨i, hi⟩)
    simpa using hk
  have hz0 : z = 0 := by
    rw [hrep]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [hzero i hi, TensorProduct.zero_tmul]
  have hxz : x = eqv z := by rw [hz]; simp
  rw [hxz, hz0, map_zero]

/-- **Points of the torsor are jointly injective.**  Two elements agreeing at every point of the
acting algebra are equal.  With `A = R ⊗_K R` and the two embeddings of an element of `R`, this is
the Galois correspondence: an element fixed by every specialization lies in the equalizer of the
two embeddings, which is the base field. -/
theorem eq_of_forall_torsorPointHom_eq
    [IsAlgClosed C] (E : Subalgebra C A) [IsReduced ↥E] [Algebra.FiniteType C ↥E]
    {ι : Type*} (b : Basis ι C ↥E)
    (hgen : Algebra.adjoin C (Set.range (algebraMap R A) ∪ (E : Set A)) = ⊤)
    (hindep : LinearIndependent R (fun i => ((b i : ↥E) : A)))
    {u v : A}
    (h : ∀ χ : ↥E →ₐ[C] C,
      torsorPointHom (R := R) E b hgen hindep χ u
        = torsorPointHom (R := R) E b hgen hindep χ v) :
    u = v := by
  have hsub : u - v = 0 := by
    refine eq_zero_of_forall_torsorPointHom_eq_zero E b hgen hindep ?_
    intro χ
    rw [map_sub, h χ, sub_self]
  exact sub_eq_zero.mp hsub

end

end GaloisForLFunctions.HTGeometry
