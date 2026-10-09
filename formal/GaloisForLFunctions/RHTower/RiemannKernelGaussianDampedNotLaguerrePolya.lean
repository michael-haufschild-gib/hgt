import GaloisForLFunctions.RHTower.RiemannKernelDampedTransformNotLaguerrePolya
import GaloisForLFunctions.RHTower.DeBruijnNewmanNonnegative

/-!
# Gaussian and polynomial dampings of Riemann's kernel together

For `ε > 0`, real `c_j` and `P(u) = ∏_j(1 − ic_ju)`, the entire function

  `z ↦ ∫ Φ(u) e^{−εu²} P(u)^{−1} e^{izu} du`

is not Laguerre–Pólya (`not_laguerrePolya_gaussDampedKernelTransform`).  With
`not_laguerrePolya_dampedKernelTransform` (`ε = 0`, some `c_j ≠ 0`), every damping of `Φ` by
`e^{−εu²}/P(iu)` other than the identity leaves the Laguerre–Pólya class.

**Proof.**  The chain `∏(1 − c_jD)` maps the damped transform to `H_{−ε}(z) = ∫Φe^{−εu²}e^{izu}`
(`firstOrderChain_paperFT_kernel`) and preserves the Laguerre–Pólya class.  By Newman's theorem
`H_{−ε}` has non-real zeros (`DeBruijn.riemannHeat_neg_nonreal_zeros_infinite`), while
`H_{−ε}(0) = ∫Φe^{−εu²} > 0`; a Laguerre–Pólya function that is not identically zero has only
real zeros.
-/

open Complex MeasureTheory Filter Topology Set
open Zeta23

namespace RHTower.KernelStrip

noncomputable section

theorem expGrowth_gaussian {ε : ℝ} (hε : 0 ≤ ε) :
    ExpGrowth fun u : ℝ => ((Real.exp (-ε * u ^ 2) : ℝ) : ℂ) := by
  refine ⟨by fun_prop, 1, 0, fun u => ?_⟩
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), zero_mul, Real.exp_zero,
    mul_one, Real.exp_le_one_iff]
  nlinarith [sq_nonneg u]

/-- The Gaussian-damped transform is the backward heat flow `H_{−ε}`. -/
theorem paperFT_gaussian_eq_riemannHeat (ε : ℝ) :
    (fun z => paperFT (fun u => riemannPhiKernel u * ((Real.exp (-ε * u ^ 2) : ℝ) : ℂ)) z) =
      DeBruijn.riemannHeat (-ε) := by
  funext z
  unfold DeBruijn.riemannHeat DeBruijn.cosTransform paperFT
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only
  rw [riemannPhiKernel_eq_ofReal]
  push_cast
  ring_nf

theorem riemannHeat_zero_ne_zero (ε : ℝ) (hε : 0 ≤ ε) : DeBruijn.riemannHeat (-ε) 0 ≠ 0 := by
  have hint : Integrable fun u : ℝ => riemannKernelReal u * Real.exp (-ε * u ^ 2) := by
    obtain ⟨C, hC0, hC⟩ := exists_norm_riemannPhiKernel_le_exp 1
    refine ((RHTower.integrable_exp_neg_mul_abs' (c := 1) one_pos).const_mul C).mono'
      ((continuous_riemannKernelReal.mul (by fun_prop)).aestronglyMeasurable)
      (Eventually.of_forall fun u => ?_)
    have h := hC u
    rw [riemannPhiKernel_eq_ofReal, Complex.norm_real] at h
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have he : Real.exp (-ε * u ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg u])
    calc |riemannKernelReal u| * Real.exp (-ε * u ^ 2) ≤ |riemannKernelReal u| * 1 :=
          mul_le_mul_of_nonneg_left he (abs_nonneg _)
      _ = ‖riemannKernelReal u‖ := by rw [mul_one, Real.norm_eq_abs]
      _ ≤ C * Real.exp (-(1 * |u|)) := h
  have hpos : 0 < ∫ u : ℝ, riemannKernelReal u * Real.exp (-ε * u ^ 2) := by
    rw [integral_pos_iff_support_of_nonneg
      (fun u => (mul_pos (riemannKernelReal_pos u) (Real.exp_pos _)).le) hint]
    have hs : Function.support (fun u : ℝ => riemannKernelReal u * Real.exp (-ε * u ^ 2)) =
        univ := by
      ext u
      simp only [Function.mem_support, mem_univ, iff_true]
      exact (mul_pos (riemannKernelReal_pos u) (Real.exp_pos _)).ne'
    rw [hs, Real.volume_univ]
    exact ENNReal.zero_lt_top
  have h0 : DeBruijn.riemannHeat (-ε) 0 =
      ((∫ u : ℝ, riemannKernelReal u * Real.exp (-ε * u ^ 2) : ℝ) : ℂ) := by
    unfold DeBruijn.riemannHeat DeBruijn.cosTransform
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [mul_zero, zero_mul, Complex.exp_zero, mul_one]
  rw [h0]
  exact_mod_cast hpos.ne'

/-- **Gaussian and polynomial damping.**  For `ε > 0` and any real `c_j`, the transform of
`Φ(u)e^{−εu²}/∏_j(1 − ic_ju)` is not Laguerre–Pólya. -/
theorem not_laguerrePolya_gaussDampedKernelTransform {ε : ℝ} (hε : 0 < ε) (cs : List ℝ) :
    ¬ GaloisForLFunctions.HTGeometry.LaguerrePolya
      (fun z => paperFT (fun u => riemannPhiKernel u *
        (((Real.exp (-ε * u ^ 2) : ℝ) : ℂ) * (chainSymbol cs u)⁻¹)) z) := by
  intro hLP
  have hh := (expGrowth_gaussian hε.le).mul (expGrowth_inv_chainSymbol cs)
  have hchain := firstOrderChain_paperFT_kernel cs hh
  have hLP' := laguerrePolya_firstOrderChain cs hLP
  rw [hchain] at hLP'
  have e : (fun z => paperFT (fun u => riemannPhiKernel u *
      ((((Real.exp (-ε * u ^ 2) : ℝ) : ℂ) * (chainSymbol cs u)⁻¹) * chainSymbol cs u)) z) =
      DeBruijn.riemannHeat (-ε) := by
    rw [← paperFT_gaussian_eq_riemannHeat]
    funext z
    congr 1
    funext u
    rw [mul_assoc, inv_mul_cancel₀ (chainSymbol_ne_zero cs u), mul_one]
  rw [e] at hLP'
  obtain ⟨z, ⟨hz, him⟩⟩ := (DeBruijn.riemannHeat_neg_nonreal_zeros_infinite hε).nonempty
  exact him (GaloisForLFunctions.HTGeometry.im_eq_zero_of_laguerrePolya hLP'
    (riemannHeat_zero_ne_zero ε hε.le) hz)

end

end RHTower.KernelStrip
