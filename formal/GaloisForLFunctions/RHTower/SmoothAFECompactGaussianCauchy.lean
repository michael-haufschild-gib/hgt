import GaloisForLFunctions.RHTower.SmoothAFECompactGaussianKernel
import Mathlib.Analysis.Complex.CauchyIntegral

open Complex Set Metric Real
noncomputable section
namespace RHTower

/-- Continuous functionals commute with the compact-carrier contour integral. -/
theorem compactGaussian_circleIntegral_map (K : Set ℂ) [CompactSpace K]
    (A : C(K, ℂ) →L[ℂ] ℂ) {g : ℂ → C(K, ℂ)} {c : ℂ} {R : ℝ}
    (hg : CircleIntegrable g c R) :
    (∮ w in C(c, R), A (g w)) = A (∮ w in C(c, R), g w) := by
  simpa only [circleIntegral, map_smul] using A.intervalIntegral_comp_comm hg.out

/-- The Gaussian weight preserves the exact Cauchy reproducing value. -/
theorem gaussianCauchy_reproduces_on_disc {c z : ℂ} {r R : ℝ}
    (hr : 0 ≤ r) (hR : r < R) (hz : z ∈ closedBall c r)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (closedBall c R)) :
    (∮ w in C(-c, R), f (-w) * (Complex.exp ((z + w) ^ 2) / (z + w))) =
      (2 * π * I : ℂ) * f z := by
  have hneg : MapsTo (fun w : ℂ => -w) (closedBall (-c) R) (closedBall c R) := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm] at hw ⊢
    rwa [show -w - c = -(w - (-c)) by ring, norm_neg]
  have hdiff : DifferentiableOn ℂ
      (fun w : ℂ => f (-w) * Complex.exp ((z + w) ^ 2)) (closedBall (-c) R) := by
    exact (hf.comp differentiable_id.neg.differentiableOn hneg).mul
      (((differentiable_const z).add differentiable_id).pow 2).cexp.differentiableOn
  have hz' : -z ∈ ball (-c) R := by
    rw [mem_ball, dist_eq_norm, show -z - (-c) = -(z - c) by ring, norm_neg]
    simpa only [dist_eq_norm] using (mem_closedBall.mp hz).trans_lt hR
  have hformula := hdiff.circleIntegral_sub_inv_smul hz'
  calc
    (∮ w in C(-c, R), f (-w) * (Complex.exp ((z + w) ^ 2) / (z + w))) =
        ∮ w in C(-c, R), (w - (-z))⁻¹ •
          (f (-w) * Complex.exp ((z + w) ^ 2)) := by
      apply circleIntegral.integral_congr (hr.trans hR.le)
      intro w _
      simp only [smul_eq_mul, sub_neg_eq_add, div_eq_mul_inv]
      rw [add_comm w z]
      ring
    _ = (2 * π * I : ℂ) * f z := by
      simpa only [neg_neg, add_neg_cancel, zero_pow (by decide : 2 ≠ 0),
        Complex.exp_zero, mul_one, smul_eq_mul] using hformula

end RHTower
