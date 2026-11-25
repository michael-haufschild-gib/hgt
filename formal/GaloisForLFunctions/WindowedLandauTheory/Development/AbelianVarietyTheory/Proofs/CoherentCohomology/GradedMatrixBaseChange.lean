import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.GradedMatrixPresentation
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import Mathlib.RingTheory.TensorProduct.IsBaseChangeRightExact

/-! Changing the coefficients of a homogeneous polynomial matrix changes base on its cokernel. -/

open MvPolynomial

namespace GlobalTheory

theorem map_mem_polyGrading {ι B R : Type} [CommRing B] [CommRing R] (f : B →+* R)
    {p : MvPolynomial ι B} {n : ℤ} (hp : p ∈ polyGrading ι B n) :
    MvPolynomial.map f p ∈ polyGrading ι R n := by
  rw [mem_polyGrading_iff]
  intro α hα
  apply (mem_polyGrading_iff.1 hp) α
  intro h
  apply hα
  rw [MvPolynomial.coeff_map, h, map_zero]

private theorem exists_isBaseChange_coker {B R A₀ A M₁ M₂ N₁ N₂ : Type}
    [CommRing B] [CommRing R] [CommRing A₀] [CommRing A]
    [Algebra B R] [Algebra B A₀] [Algebra R A] [Algebra B A] [IsScalarTower B R A]
    [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup N₁] [AddCommGroup N₂]
    [Module B M₁] [Module B M₂] [Module A₀ M₁] [Module A₀ M₂]
    [IsScalarTower B A₀ M₁] [IsScalarTower B A₀ M₂]
    [Module B N₁] [Module B N₂] [Module R N₁] [Module R N₂] [Module A N₁] [Module A N₂]
    [IsScalarTower B R N₁] [IsScalarTower B R N₂] [IsScalarTower R A N₁] [IsScalarTower R A N₂]
    [IsScalarTower B A N₂]
    (f₀ : M₁ →ₗ[A₀] M₂) (f : N₁ →ₗ[A] N₂) (p₁ : M₁ →ₗ[B] N₁) (p₂ : M₂ →ₗ[B] N₂)
    (b₁ : IsBaseChange R p₁) (b₂ : IsBaseChange R p₂) (hcomm : ∀ x, p₂ (f₀ x) = f (p₁ x)) :
    ∃ ψ : (M₂ ⧸ LinearMap.range f₀) →ₗ[B] (N₂ ⧸ LinearMap.range f),
      IsBaseChange R ψ ∧ ∀ y, ψ (Submodule.Quotient.mk y) = Submodule.Quotient.mk (p₂ y) := by
  let q₀ : M₂ →ₗ[B] (M₂ ⧸ LinearMap.range f₀) := (LinearMap.range f₀).mkQ.restrictScalars B
  let q : N₂ →ₗ[R] (N₂ ⧸ LinearMap.range f) := (LinearMap.range f).mkQ.restrictScalars R
  have hq₀ : Function.Surjective q₀ := (LinearMap.range f₀).mkQ_surjective
  have hq : Function.Surjective q := (LinearMap.range f).mkQ_surjective
  have h₀ : Function.Exact (f₀.restrictScalars B) q₀ := LinearMap.exact_map_mkQ_range f₀
  have h₁ : Function.Exact (f.restrictScalars R) q := LinearMap.exact_map_mkQ_range f
  have hker : LinearMap.ker q₀ ≤ LinearMap.ker ((q.restrictScalars B).comp p₂) := by
    intro y hy
    obtain ⟨x, rfl⟩ := (h₀ y).1 hy
    exact (h₁ _).2 ⟨p₁ x, (hcomm x).symm⟩
  let ψ : (M₂ ⧸ LinearMap.range f₀) →ₗ[B] (N₂ ⧸ LinearMap.range f) :=
    ((LinearMap.ker q₀).liftQ _ hker).comp (q₀.quotKerEquivOfSurjective hq₀).symm.toLinearMap
  have hψ (y : M₂) : ψ (q₀ y) = q (p₂ y) := by
    have e : (q₀.quotKerEquivOfSurjective hq₀).symm (q₀ y) = Submodule.Quotient.mk y := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [ψ, LinearMap.comp_apply, LinearEquiv.coe_coe, e]
    rfl
  exact ⟨ψ, IsBaseChange.of_right_exact R (f := f₀.restrictScalars B) (g := q₀)
    (f' := f.restrictScalars R) (g' := q) p₁ p₂ ψ (LinearMap.ext hcomm) (LinearMap.ext hψ)
    b₁ b₂ h₀ hq₀ h₁ hq, hψ⟩

theorem exists_graded_matrix_baseChange {ι B R : Type} [CommRing B] [CommRing R] [Algebra B R]
    {a b : ℕ} (d : Fin a → ℤ) (Φ₀ : Matrix (Fin a) (Fin b) (MvPolynomial ι B)) :
    let Φ := Φ₀.map (MvPolynomial.map (algebraMap B R))
    ∃ ψ : ((Fin a → MvPolynomial ι B) ⧸ LinearMap.range Φ₀.mulVecLin) →ₗ[B]
        ((Fin a → MvPolynomial ι R) ⧸ LinearMap.range Φ.mulVecLin),
      IsBaseChange R ψ ∧
      (∀ (i : ι) y, ψ ((X i : MvPolynomial ι B) • y) = (X i : MvPolynomial ι R) • ψ y) ∧
      ∀ n z, z ∈ grQuot (grFree ι B d) (LinearMap.range Φ₀.mulVecLin) n →
        ψ z ∈ grQuot (grFree ι R d) (LinearMap.range Φ.mulVecLin) n := by
  intro Φ
  let f := mapAlgHom (σ := ι) (Algebra.ofId B R)
  have hf : IsBaseChange R f.toLinearMap :=
    IsBaseChange.of_equiv (algebraTensorAlgEquiv B R).toLinearEquiv fun p => by
      simp [f, mapAlgHom_apply]
  obtain ⟨ψ, hψ, hmk⟩ := exists_isBaseChange_coker Φ₀.mulVecLin Φ.mulVecLin _ _
    (IsBaseChange.finitePow (Fin b) hf) (IsBaseChange.finitePow (Fin a) hf) (by
      intro x
      funext l
      exact RingHom.map_mulVec (MvPolynomial.map (algebraMap B R)) Φ₀ x l)
  refine ⟨ψ, hψ, ?_, ?_⟩
  · intro i y
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [← Submodule.Quotient.mk_smul, hmk, hmk, ← Submodule.Quotient.mk_smul]
    congr 1
    funext j
    change MvPolynomial.map (algebraMap B R) ((X i : MvPolynomial ι B) * z j) =
      X i * MvPolynomial.map (algebraMap B R) (z j)
    rw [map_mul, MvPolynomial.map_X]
  · intro n z hz
    obtain ⟨w, hw, rfl⟩ := mem_grQuot.1 hz
    change ψ (Submodule.Quotient.mk w) ∈ _
    rw [hmk]
    exact mem_grQuot.2 ⟨_, mem_grFree.2 fun j =>
      map_mem_polyGrading (algebraMap B R) (mem_grFree.1 hw j), rfl⟩

end GlobalTheory
