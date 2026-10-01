import GaloisForLFunctions.HTGeometry.ContinuousMapCauchyTransform
import Mathlib.Analysis.SpecialFunctions.Exponential

open Complex Set
noncomputable section
namespace RHTower
open GaloisForLFunctions.HTGeometry

variable (K : Set ℂ) [CompactSpace K]

/-- The translated Gaussian Cauchy kernel in the Banach algebra of continuous
functions on the compact carrier. Its literal formula is used only off the pole set. -/
def compactGaussianCauchyKernel (w : ℂ) : C(K, ℂ) :=
  NormedSpace.exp ((coordMap K + w • (1 : C(K, ℂ))) ^ 2) *
    (-resolventInv K (-w))

private theorem continuousMap_exp_apply (f : C(K, ℂ)) (z : K) :
    (NormedSpace.exp f) z = Complex.exp (f z) := by
  have h := NormedSpace.map_exp (ContinuousMap.evalAlgHom ℂ ℂ z)
    (ContinuousMap.evalCLM ℂ z).continuous f
  simpa only [ContinuousMap.evalAlgHom_apply, ← Complex.exp_eq_exp_ℂ] using h

/-- The compact-algebra kernel retains the exact Gaussian mode coefficient. -/
theorem compactGaussianCauchyKernel_apply {w : ℂ} (hw : -w ∉ K) (z : K) :
    compactGaussianCauchyKernel K w z =
      Complex.exp (((z : ℂ) + w) ^ 2) / ((z : ℂ) + w) := by
  change (NormedSpace.exp ((coordMap K + w • (1 : C(K, ℂ))) ^ 2)) z *
    (-(resolventInv K (-w) z)) = _
  rw [continuousMap_exp_apply, resolventInv_eq hw]
  change Complex.exp (((z : ℂ) + w * 1) ^ 2) * (-((-w - (z : ℂ))⁻¹)) = _
  rw [mul_one, show -w - (z : ℂ) = -((z : ℂ) + w) by ring, inv_neg, neg_neg,
    div_eq_mul_inv]

/-- Holomorphy of the full translated Gaussian kernel off the reflected carrier. -/
theorem differentiableAt_compactGaussianCauchyKernel {w : ℂ} (hw : -w ∉ K) :
    DifferentiableAt ℂ (compactGaussianCauchyKernel K) w := by
  have hpoly : Differentiable ℂ
      (fun v : ℂ => (coordMap K + v • (1 : C(K, ℂ))) ^ 2) :=
    ((differentiable_const (coordMap K)).add
      (differentiable_id.smul_const (1 : C(K, ℂ)))).pow 2
  have hexp : DifferentiableAt ℂ
      (fun v : ℂ => NormedSpace.exp ((coordMap K + v • (1 : C(K, ℂ))) ^ 2)) w :=
    (NormedSpace.exp_analytic (𝕂 := ℂ) _).differentiableAt.comp w hpoly.differentiableAt
  have hres : DifferentiableAt ℂ (fun v : ℂ => resolventInv K (-v)) w :=
    (differentiableAt_resolventInv hw).comp w (differentiable_id.neg.differentiableAt)
  exact hexp.mul hres.neg

/-- The Gaussian transform of a continuous functional is analytic off the reflected compact. -/
theorem analyticOnNhd_compactGaussianFunctional (hK : IsCompact K)
    (A : C(K, ℂ) →L[ℂ] ℂ) :
    AnalyticOnNhd ℂ (fun w : ℂ => A (compactGaussianCauchyKernel K w)) {w | -w ∉ K} := by
  have hopen : IsOpen {w : ℂ | -w ∉ K} :=
    hK.isClosed.isOpen_compl.preimage continuous_neg
  apply DifferentiableOn.analyticOnNhd _ hopen
  intro w hw
  exact (A.differentiableAt.comp w
    (differentiableAt_compactGaussianCauchyKernel K hw)).differentiableWithinAt

end RHTower
