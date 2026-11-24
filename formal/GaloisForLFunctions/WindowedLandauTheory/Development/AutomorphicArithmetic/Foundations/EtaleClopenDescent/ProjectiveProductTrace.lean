import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveTrace
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.FiniteEtaleFormTrace
import Mathlib.LinearAlgebra.Pi

/-! The trace of multiplication on a finite product of finite projective
algebras is the sum of the component traces. -/

noncomputable section

open TensorProduct

namespace GlobalTheory.SchemeCohomology

/-- A finite projective module admits a finite dual family that reconstructs every vector. -/
theorem exists_projectiveDualFamily (R M : Type*) [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M] :
    ∃ (n : ℕ) (a : Fin n → M) (f : Fin n → Module.Dual R M),
      ∀ x, x = ∑ j, f j x • a j := by
  obtain ⟨n, p, i, -, -, hpi⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  let b := Pi.basisFun R (Fin n)
  refine ⟨n, fun j => p (b j), fun j => b.coord j ∘ₗ i, fun x => ?_⟩
  calc
    x = p (i x) := (LinearMap.congr_fun hpi x).symm
    _ = p (∑ j : Fin n, b.repr (i x) j • b j) := congrArg p (b.sum_repr (i x)).symm
    _ = _ := by simp only [map_sum, map_smul, LinearMap.comp_apply, Module.Basis.coord_apply]

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [Module.Finite R M] [Module.Projective R M]
  [Module.Finite R N] [Module.Projective R N]

/-- The projective trace of a rank-one map is its evaluation. -/
theorem projectiveTrace_rankOne (f : Module.Dual R M) (m : M) :
    projectiveTrace R M (f.smulRight m) = f m := by
  have e : f.smulRight m = dualTensorHom R M M (f ⊗ₜ m) := by
    ext x
    exact (dualTensorHom_apply f x m).symm
  rw [e, projectiveTrace_tensor, contractLeft_apply]

/-- The trace of a composite is invariant under cyclic permutation, even for
maps between distinct finite projective modules. -/
theorem projectiveTrace_cyclic (u : M →ₗ[R] N) (v : N →ₗ[R] M) :
    projectiveTrace R N (u ∘ₗ v) = projectiveTrace R M (v ∘ₗ u) := by
  classical
  obtain ⟨n, a, f, ha⟩ := exists_projectiveDualFamily R M
  let y (j : Fin n) := u (a j)
  have hu : u = ∑ j, (f j).smulRight (y j) := by
    ext x
    simpa only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smulRight_apply, y] using
      congrArg u (ha x)
  have hl : u ∘ₗ v = ∑ j, (f j).smulRight (y j) ∘ₗ v := by
    rw [hu]
    ext x
    simp only [LinearMap.comp_apply, LinearMap.sum_apply]
  have hr : v ∘ₗ u = ∑ j, v ∘ₗ (f j).smulRight (y j) := by
    rw [hu]
    ext x
    simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  rw [hl, hr, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e₁ : (f j).smulRight (y j) ∘ₗ v = ((f j) ∘ₗ v).smulRight (y j) := by
    ext z
    rfl
  have e₂ : v ∘ₗ (f j).smulRight (y j) = (f j).smulRight (v (y j)) := by
    ext z
    exact v.map_smul (f j z) (y j)
  simp only [e₁, e₂, projectiveTrace_rankOne, LinearMap.comp_apply]

variable {B : Type*} [CommRing B] [Algebra R B] [Module.Finite R B]
  {J : Type*} [Fintype J] {C : J → Type*} [∀ j, CommRing (C j)] [∀ j, Algebra R (C j)]
  [∀ j, Module.Finite R (C j)]

/-- For a product presented by algebra homomorphisms, the trace is the sum
over the factors. -/
theorem projectiveAlgebraTrace_sum_of_coordinates [Module.Projective R B] [∀ j, Module.Projective R (C j)]
    (r : ∀ j, B →ₐ[R] C j)
    (hr : Function.Bijective fun b j => r j b) (b : B) :
    projectiveAlgebraTrace R B b = ∑ j, projectiveAlgebraTrace R (C j) (r j b) := by
  classical
  let e : B ≃ₗ[R] (∀ j, C j) :=
    LinearEquiv.ofBijective (LinearMap.pi fun j => (r j).toLinearMap) hr
  let t (j : J) : C j →ₗ[R] B := e.symm.toLinearMap ∘ₗ LinearMap.single R C j
  have ht (j : J) (y : C j) : r j (t j y) = y := by
    have h := congrFun (e.apply_symm_apply (Pi.single j y)) j
    exact h.trans (Pi.single_eq_same j y)
  have hsum (x : B) : ∑ j, t j (r j x) = x := by
    apply e.injective
    rw [map_sum]
    change ∑ j, e (e.symm (Pi.single j (r j x))) = e x
    simp only [e.apply_symm_apply, Finset.univ_sum_single]
    rfl
  have hmul : LinearMap.mul R B b =
      ∑ j, t j ∘ₗ ((r j).toLinearMap ∘ₗ LinearMap.mul R B b) := by
    ext x
    simp only [LinearMap.sum_apply, LinearMap.comp_apply]
    exact (hsum (b * x)).symm
  change projectiveTrace R B (LinearMap.mul R B b) =
    ∑ j, projectiveTrace R (C j) (LinearMap.mul R (C j) (r j b))
  rw [hmul, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [projectiveTrace_cyclic]
  congr 1
  ext y
  change r j (b * t j y) = r j b * y
  rw [map_mul, ht]

/-- Trace on a finite étale algebra splits along its finite étale factors. -/
theorem finiteEtaleAlgebraTrace_sum_of_coordinates [Algebra.Etale R B]
    [∀ j, Algebra.Etale R (C j)] (r : ∀ j, B →ₐ[R] C j)
    (hr : Function.Bijective fun b j => r j b) (b : B) :
    finiteEtaleAlgebraTrace R B b = ∑ j, finiteEtaleAlgebraTrace R (C j) (r j b) := by
  letI : Module.FinitePresentation R B := .of_finite_of_finitePresentation R B
  letI : Module.Projective R B := Module.Flat.projective_of_finitePresentation
  letI (j : J) : Module.Projective R (C j) := by
    letI : Module.FinitePresentation R (C j) := .of_finite_of_finitePresentation R (C j)
    exact Module.Flat.projective_of_finitePresentation
  exact projectiveAlgebraTrace_sum_of_coordinates r hr b

end GlobalTheory.SchemeCohomology
