import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Instances.Matrix
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# The determinant of a linear perturbation is a polynomial in the parameter

For a fixed matrix `N`, the determinant `det (1 + t • N)` expands, by multilinearity, into a finite
sum of monomials in `t` whose coefficients are polynomial in the entries of `N`.  Integrating over a
compact set therefore produces an honest polynomial in `t`.

This is the algebraic step of the volume argument for the no-retraction theorem: the volume of the
image of a ball under the affine homotopy `x ↦ x + t (ρ x - x)` is a polynomial in `t`, so an
identity valid for small `t` persists to `t = 1`.
-/

open MeasureTheory Finset

namespace GaloisForLFunctions

/-- **Monomial expansion of a linearly perturbed determinant.**  Expanding each entry of
`1 + t • N` and distributing the product over the index set writes the determinant as a finite sum
of monomials in `t`, the coefficient of each monomial being a product of entries of `N`. -/
theorem det_one_add_smul_expand {n : ℕ} (N : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    (1 + t • N).det
      = ∑ σ : Equiv.Perm (Fin n), ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
          (((Equiv.Perm.sign σ : ℤ) : ℝ) * (∏ i ∈ S, (1 : Matrix (Fin n) (Fin n) ℝ) (σ i) i) *
              t ^ ((Finset.univ : Finset (Fin n)) \ S).card) *
            ∏ i ∈ (Finset.univ : Finset (Fin n)) \ S, N (σ i) i := by
  rw [Matrix.det_apply']
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hentry : ∀ i : Fin n, (1 + t • N) (σ i) i
      = (1 : Matrix (Fin n) (Fin n) ℝ) (σ i) i + t * N (σ i) i := by
    intro i
    simp [Matrix.add_apply, Matrix.smul_apply]
  rw [Finset.prod_congr rfl (fun i _ => hentry i), Finset.prod_add, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const]
  ring

/-- **The integrated determinant is a polynomial in the parameter.**  For a continuous family of
matrices on a compact set, the integral of `det (1 + t • N x)` over that set is the evaluation of a
single polynomial at `t`. -/
theorem exists_polynomial_setIntegral_det_one_add_smul {X : Type*} [MeasurableSpace X]
    [TopologicalSpace X] [T2Space X] [OpensMeasurableSpace X] {μ : Measure X}
    [IsFiniteMeasureOnCompacts μ] {n : ℕ} {K : Set X} (hK : IsCompact K)
    {N : X → Matrix (Fin n) (Fin n) ℝ} (hN : ContinuousOn N K) :
    ∃ Q : Polynomial ℝ, ∀ t : ℝ, ∫ x in K, (1 + t • N x).det ∂μ = Q.eval t := by
  classical
  -- the `x`-dependent factor attached to a permutation and a subset
  set F : Equiv.Perm (Fin n) → Finset (Fin n) → X → ℝ :=
    fun σ S x => ∏ i ∈ (Finset.univ : Finset (Fin n)) \ S, N x (σ i) i with hF
  have hFcont : ∀ σ S, ContinuousOn (F σ S) K := by
    intro σ S
    exact continuousOn_finsetProd _ fun i _ =>
      (continuous_id.matrix_elem (σ i) i).comp_continuousOn hN
  have hFint : ∀ σ S, IntegrableOn (F σ S) K μ := fun σ S =>
    (hFcont σ S).integrableOn_compact hK
  -- the constant factor
  set c : Equiv.Perm (Fin n) → Finset (Fin n) → ℝ :=
    fun σ S => ((Equiv.Perm.sign σ : ℤ) : ℝ) *
      (∏ i ∈ S, (1 : Matrix (Fin n) (Fin n) ℝ) (σ i) i) * ∫ x in K, F σ S x ∂μ with hc
  refine ⟨∑ σ : Equiv.Perm (Fin n), ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
      Polynomial.C (c σ S) * Polynomial.X ^ ((Finset.univ : Finset (Fin n)) \ S).card, fun t => ?_⟩
  have hstep : ∫ x in K, (1 + t • N x).det ∂μ
      = ∫ x in K, ∑ σ : Equiv.Perm (Fin n), ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
          (((Equiv.Perm.sign σ : ℤ) : ℝ) * (∏ i ∈ S, (1 : Matrix (Fin n) (Fin n) ℝ) (σ i) i) *
            t ^ ((Finset.univ : Finset (Fin n)) \ S).card) * F σ S x ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact det_one_add_smul_expand (N x) t
  rw [hstep]
  rw [MeasureTheory.integral_finsetSum _ (fun σ _ => ?_)]
  · rw [Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [MeasureTheory.integral_finsetSum _ (fun S _ => ?_)]
    · rw [Polynomial.eval_finsetSum]
      refine Finset.sum_congr rfl fun S _ => ?_
      rw [MeasureTheory.integral_const_mul, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X, hc]
      ring
    · exact ((hFint σ S).const_mul _)
  · refine MeasureTheory.integrable_finsetSum _ fun S _ => ?_
    exact ((hFint σ S).const_mul _)

end GaloisForLFunctions
