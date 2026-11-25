import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.DehomogenizedKernels
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.GradedSaturatingGenerators
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! A finite homogeneous matrix presents a graded module after inverting any coordinate. -/

open DirectSum MvPolynomial

namespace GlobalTheory

theorem isGradedMap_mulVecLin {ι R : Type*} [CommRing R] {a b : ℕ}
    {d : Fin a → ℤ} {e : Fin b → ℤ} {Φ : Matrix (Fin a) (Fin b) (MvPolynomial ι R)}
    (hΦ : ∀ l j, Φ l j ∈ polyGrading ι R (e j - d l)) :
    IsGradedMap (grFree ι R e) (grFree ι R d) Φ.mulVecLin := by
  let S := MvPolynomial ι R
  have h : Φ.mulVecLin = Fintype.linearCombination S (fun j l => Φ l j) := by
    apply LinearMap.ext
    intro x
    funext l
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Fintype.linearCombination_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [h]
  exact isGradedMap_linearCombination _ fun j => mem_grFree.2 fun l => hΦ l j

theorem exists_graded_presentation_saturating {ι R G : Type*} [Finite ι] [CommRing R]
    [AddCommGroup G] [Module R G] [Module (MvPolynomial ι R) G] [IsScalarTower R (MvPolynomial ι R) G]
    (D : ℤ → Submodule R G) [PolyGradedSMul ι D] [Decomposition D]
    (hG : ∀ i : ι, Module.FinitePresentation (MvPolynomial ι R)
      (QuotSMulTop (X i - 1 : MvPolynomial ι R) G)) :
    ∃ (a b : ℕ) (d : Fin a → ℤ) (e : Fin b → ℤ)
      (Φ : Matrix (Fin a) (Fin b) (MvPolynomial ι R))
      (ψ : ((Fin a → MvPolynomial ι R) ⧸ LinearMap.range Φ.mulVecLin) →ₗ[MvPolynomial ι R] G),
      (∀ l j, Φ l j ∈ polyGrading ι R (e j - d l)) ∧
        IsGradedMap (grQuot (grFree ι R d) (LinearMap.range Φ.mulVecLin)) D ψ ∧
        ∀ i : ι,
          (∀ y, ψ y = 0 → ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • y = 0) ∧
          (∀ z : G, ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • z ∈ LinearMap.range ψ) := by
  obtain ⟨a, d, g, hg, hsatG⟩ := exists_homogeneous_family_saturating D (fun i => by
    letI := hG i
    infer_instance)
  let f := Fintype.linearCombination (MvPolynomial ι R) g
  have hf : IsGradedMap (grFree ι R d) D f := isGradedMap_linearCombination D hg
  have hsat (i : ι) (z : G) : ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • z ∈ LinearMap.range f := by
    rw [show f = Fintype.linearCombination (MvPolynomial ι R) g from rfl, Fintype.range_linearCombination]
    exact hsatG i z
  let K := LinearMap.ker f
  letI : Decomposition (grSub (grFree ι R d) K) := grSubDecomposition hf.isHomogeneous_ker
  obtain ⟨b, e, κ, hκ, hsatK⟩ := exists_homogeneous_family_saturating (grSub (grFree ι R d) K)
    (fun i => by
      letI := hG i
      exact finite_quotSMulTop_ker_of_graded hf i (hsat i))
  let Φ : Matrix (Fin a) (Fin b) (MvPolynomial ι R) := Matrix.of fun l j => (κ j).1 l
  have hrange : LinearMap.range Φ.mulVecLin =
      (Submodule.span (MvPolynomial ι R) (Set.range κ)).map K.subtype := by
    rw [Matrix.range_mulVecLin, Submodule.map_span, ← Set.range_comp]
    rfl
  have hle : LinearMap.range Φ.mulVecLin ≤ K := by
    rw [hrange]
    exact Submodule.map_subtype_le _ _
  refine ⟨a, b, d, e, Φ, Submodule.liftQ _ f hle,
    fun l j => mem_grFree.1 (mem_grSub.1 (hκ j)) l, hf.liftQ _ hle, fun i => ⟨?_, ?_⟩⟩
  · intro y hy
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨k, hk⟩ := hsatK i ⟨x, hy⟩
    refine ⟨k, ?_⟩
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hrange]
    exact ⟨_, hk, rfl⟩
  · rw [Submodule.range_liftQ]
    exact hsat i

end GlobalTheory
