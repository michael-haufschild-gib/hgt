import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveProductTrace

/-! Dual families compose in a tower, giving transitivity of the
algebra trace for finite projective algebras. -/

noncomputable section

namespace GlobalTheory.SchemeCohomology

private theorem projectiveTrace_sum_of_dualFamily {R M ι : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M] [Fintype ι]
    (a : ι → M) (f : ι → Module.Dual R M) (h : ∀ x, x = ∑ j, f j x • a j)
    (T : M →ₗ[R] M) :
    projectiveTrace R M T = ∑ j, f j (T (a j)) := by
  have hT : T = ∑ j, (f j).smulRight (T (a j)) := by
    ext x
    simpa only [LinearMap.sum_apply, LinearMap.smulRight_apply, map_sum, map_smul]
      using congrArg T (h x)
  conv_lhs => rw [hT]
  simp only [map_sum, projectiveTrace_rankOne]

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
  [Module.Finite R A] [Module.Finite A B] [Module.Finite R B]

/-- Trace of multiplication through a tower of finite projective
algebras is the composite of the successive algebra traces. -/
theorem projectiveAlgebraTrace_trans [Module.Projective R A]
    [Module.Projective A B] [Module.Projective R B] (b : B) :
    projectiveAlgebraTrace R B b =
      projectiveAlgebraTrace R A (projectiveAlgebraTrace A B b) := by
  obtain ⟨n, a, f, ha⟩ := exists_projectiveDualFamily R A
  obtain ⟨m, c, g, hc⟩ := exists_projectiveDualFamily A B
  let v (i : Fin m × Fin n) : B := a i.2 • c i.1
  let u (i : Fin m × Fin n) : Module.Dual R B := (f i.2) ∘ₗ (g i.1).restrictScalars R
  have hv (x : B) : x = ∑ i, u i x • v i := by
    rw [Fintype.sum_prod_type]
    conv_lhs => rw [hc x]
    refine Finset.sum_congr rfl fun j _ => ?_
    change g j x • c j = ∑ i, f i (g j x) • (a i • c j)
    conv_lhs => rw [ha (g j x), Finset.sum_smul]
    exact Finset.sum_congr rfl fun i _ => smul_assoc _ _ _
  have hR := projectiveTrace_sum_of_dualFamily v u hv (LinearMap.mul R B b)
  have hA := projectiveTrace_sum_of_dualFamily c g hc (LinearMap.mul A B b)
  change projectiveAlgebraTrace R B b = _ at hR
  change projectiveAlgebraTrace A B b = _ at hA
  rw [hR, hA, map_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  change (∑ i, f i (g j (b * (a i • c j)))) = projectiveAlgebraTrace R A (g j (b * c j))
  change (∑ i, f i (g j ((LinearMap.mul A B b) (a i • c j)))) =
    projectiveTrace R A (LinearMap.mul R A (g j (b * c j)))
  rw [projectiveTrace_sum_of_dualFamily a f ha]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, map_smul, LinearMap.mul_apply', smul_eq_mul, mul_comm (a i)]
  rfl

/-- The same tower law applies to traces of finite étale algebras. -/
theorem finiteEtaleAlgebraTrace_trans [Algebra.Etale R A] [Algebra.Etale A B] [Algebra.Etale R B]
    (b : B) :
    finiteEtaleAlgebraTrace R B b = finiteEtaleAlgebraTrace R A (finiteEtaleAlgebraTrace A B b) := by
  letI : Module.FinitePresentation R A := .of_finite_of_finitePresentation R A
  letI : Module.FinitePresentation R B := .of_finite_of_finitePresentation R B
  letI : Module.FinitePresentation A B := .of_finite_of_finitePresentation A B
  letI : Module.Projective R A := Module.Flat.projective_of_finitePresentation
  letI : Module.Projective R B := Module.Flat.projective_of_finitePresentation
  letI : Module.Projective A B := Module.Flat.projective_of_finitePresentation
  exact projectiveAlgebraTrace_trans b

end GlobalTheory.SchemeCohomology
