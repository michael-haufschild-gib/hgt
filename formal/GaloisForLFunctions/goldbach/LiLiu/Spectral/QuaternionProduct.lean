import GaloisForLFunctions.goldbach.LiLiu.Spectral.QuaternionSlices
import GaloisForLFunctions.goldbach.LiLiu.Spectral.EigenvalueProduct
import Mathlib.Algebra.Polynomial.AlgebraMap

/-! # The quaternionic product over the arithmetic operator spectrum

Finite factors are real polynomials in one quaternion and thus commute.
Their product can be evaluated on any complex slice through that quaternion.
Square summability gives a common limit independent of the slice.
-/

namespace GaloisForLFunctions.Goldbach.LiLiu
open Filter Polynomial HTGeometry
open scoped Topology Polynomial Quaternion
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : H →L[ℂ] H) [Fact (IsCompactOperator T)]

def spectralPolynomial (μ : ℝ) : ℝ[X] := 1-C (4*μ^2)*X*(1-X)

theorem aeval_spectralPolynomial (μ : ℝ) (q : ℍ) :
    aeval q (spectralPolynomial μ) = 1-(4*(μ:ℍ)^2)*q*(1-q) := by
  simp [spectralPolynomial]

private theorem eval_spectralPolynomial (μ : ℝ) (z : ℂ) :
    aeval z (spectralPolynomial μ) = spectralSquareFactor μ z := by
  simp [spectralPolynomial,spectralSquareFactor_eq]

def finiteSpectralPolynomial (δ : ℝ) (S : Finset (EigenIndex T)) : ℝ[X] :=
  ∏ i ∈ S, spectralPolynomial (i.1.1.re/δ)

/-- Equation (1.6), evaluated as the limit of the finite real-polynomial products. -/
def quaternionSpectralProduct (δ : ℝ) (q : ℍ) : ℍ :=
  limUnder atTop (fun S : Finset (EigenIndex T) => aeval q (finiteSpectralPolynomial T δ S))

variable {T}

private theorem finiteSpectralPolynomial_tendsto_slice (hs : T.IsSymmetric)
    (hT : ContinuousLinearMap.IsHilbertSchmidt T) (δ : ℝ) (f : ℂ →ₐ[ℝ] ℍ) (z : ℂ) :
    Tendsto (fun S : Finset (EigenIndex T) => aeval (f z) (finiteSpectralPolynomial T δ S))
      atTop (𝓝 (f (spectralProduct T δ z))) := by
  have hc : Continuous f := f.toLinearMap.continuous_of_finiteDimensional
  have hp := (infiniteSpectralSquareProduct_multipliable (scaledEigenvalues hs hT δ) z).hasProd
  change Tendsto (fun S : Finset (EigenIndex T) =>
    ∏ i ∈ S, spectralSquareFactor (i.1.1.re/δ) z) atTop (𝓝 (spectralProduct T δ z)) at hp
  simpa only [aeval_algHom_apply,finiteSpectralPolynomial,map_prod,eval_spectralPolynomial,
    Function.comp_def] using hc.continuousAt.tendsto.comp hp

/-- On every complex slice the quaternionic product restricts to the entire complex product. -/
theorem quaternionSpectralProduct_slice (hs : T.IsSymmetric)
    (hT : ContinuousLinearMap.IsHilbertSchmidt T) (δ : ℝ) (f : ℂ →ₐ[ℝ] ℍ) (z : ℂ) :
    quaternionSpectralProduct T δ (f z) = f (spectralProduct T δ z) :=
  (finiteSpectralPolynomial_tendsto_slice hs hT δ f z).limUnder_eq

theorem quaternionSpectralProduct_tendsto (hs : T.IsSymmetric)
    (hT : ContinuousLinearMap.IsHilbertSchmidt T) (δ : ℝ) (q : ℍ) :
    Tendsto (fun S : Finset (EigenIndex T) => aeval q (finiteSpectralPolynomial T δ S))
      atTop (𝓝 (quaternionSpectralProduct T δ q)) := by
  obtain ⟨f,z,rfl⟩ := quaternion_mem_complex_slice q
  rw [quaternionSpectralProduct_slice hs hT]
  exact finiteSpectralPolynomial_tendsto_slice hs hT δ f z

theorem complex_zero_of_quaternion_zeroFree (hs : T.IsSymmetric)
    (hT : ContinuousLinearMap.IsHilbertSchmidt T) (δ η : ℝ)
    (h : ∀ q : ℍ, 1-η < q.re → quaternionSpectralProduct T δ q ≠ 0) :
    ∀ z : ℂ, 1-η < z.re → spectralProduct T δ z ≠ 0 := by
  intro z hz he
  apply h (Quaternion.ofComplex z) hz
  rw [quaternionSpectralProduct_slice hs hT,he,map_zero]

theorem complex_critical_of_quaternion_critical (hs : T.IsSymmetric)
    (hT : ContinuousLinearMap.IsHilbertSchmidt T) (δ : ℝ)
    (h : ∀ q : ℍ, quaternionSpectralProduct T δ q = 0 → q.re=1/2) :
    ∀ z : ℂ, spectralProduct T δ z=0 → z.re=1/2 := by
  intro z he
  apply h (Quaternion.ofComplex z)
  rw [quaternionSpectralProduct_slice hs hT,he,map_zero]

#print axioms quaternionSpectralProduct_tendsto
#print axioms quaternionSpectralProduct_slice
end
end GaloisForLFunctions.Goldbach.LiLiu
