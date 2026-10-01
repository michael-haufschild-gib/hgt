import GaloisForLFunctions.RHTower.SmoothAFECompactGaussianAnnihilator
import GaloisForLFunctions.RHTower.SmoothAFECompactGaussianCauchy

open Complex Set Metric Real
noncomputable section
namespace RHTower

/-- A functional annihilating every imaginary Gaussian mode annihilates every
function holomorphic on a larger disc. -/
theorem compactGaussianFunctional_annihilates_holomorphic_disc
    (c : ℂ) {r R : ℝ} [CompactSpace (closedBall c r)]
    (hr : 0 ≤ r) (hc : r < c.re) (hR : r < R)
    (A : C(closedBall c r, ℂ) →L[ℂ] ℂ)
    (haxis : ∀ t : ℝ, A (compactGaussianCauchyKernel (closedBall c r)
      ((t : ℂ) * I)) = 0)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (closedBall c R))
    (g : C(closedBall c r, ℂ)) (hg : ∀ z, g z = f z) : A g = 0 := by
  let K : Set ℂ := closedBall c r
  let G : ℂ → C(K, ℂ) := fun w => f (-w) • compactGaussianCauchyKernel K w
  have hR0 : 0 ≤ R := hr.trans hR.le
  have hdist (w : ℂ) : dist (-w) c = dist w (-c) := by
    simp only [dist_eq_norm]
    rw [show -w - c = -(w - (-c)) by ring, norm_neg]
  have hoff (w : ℂ) (hw : w ∈ sphere (-c) R) : -w ∉ K := by
    intro hwin
    have hle : dist (-w) c ≤ r := mem_closedBall.mp hwin
    rw [hdist, mem_sphere.mp hw] at hle
    exact hR.not_ge hle
  have hneg : MapsTo (fun w : ℂ => -w) (closedBall (-c) R) (closedBall c R) := by
    intro w hw
    simpa only [mem_closedBall, hdist] using hw
  have hfneg : ContinuousOn (fun w : ℂ => f (-w)) (closedBall (-c) R) :=
    (hf.comp differentiable_id.neg.differentiableOn hneg).continuousOn
  have hG : CircleIntegrable G (-c) R := by
    apply ContinuousOn.circleIntegrable hR0
    intro w hw
    exact (hfneg.mono sphere_subset_closedBall w hw).smul
      (differentiableAt_compactGaussianCauchyKernel K (hoff w hw)).continuousAt.continuousWithinAt
  have hrepro : (∮ w in C(-c, R), G w) = (2 * π * I : ℂ) • g := by
    ext z
    have heval := compactGaussian_circleIntegral_map K (ContinuousMap.evalCLM ℂ z) hG
    change (∮ w in C(-c, R), G w z) = (∮ w in C(-c, R), G w) z at heval
    rw [← heval]
    calc
      (∮ w in C(-c, R), G w z) = ∮ w in C(-c, R),
          f (-w) * (Complex.exp (((z : ℂ) + w) ^ 2) / ((z : ℂ) + w)) := by
        apply circleIntegral.integral_congr hR0
        intro w hw
        change f (-w) * compactGaussianCauchyKernel K w z = _
        rw [compactGaussianCauchyKernel_apply K (hoff w hw)]
      _ = ((2 * π * I : ℂ) • g) z := by
        simpa only [ContinuousMap.smul_apply, smul_eq_mul, hg] using
          gaussianCauchy_reproduces_on_disc hr hR z.property hf
  have hzero : (∮ w in C(-c, R), A (G w)) = 0 := by
    calc
      (∮ w in C(-c, R), A (G w)) = ∮ _w in C(-c, R), (0 : ℂ) := by
        apply circleIntegral.integral_congr hR0
        intro w hw
        change A (f (-w) • compactGaussianCauchyKernel K w) = 0
        rw [map_smul, compactGaussianFunctional_eq_zero_off_disc c hr hc A haxis w
          (hoff w hw), smul_zero]
      _ = 0 := by simp [circleIntegral]
  rw [compactGaussian_circleIntegral_map K A hG, hrepro, map_smul, smul_eq_mul] at hzero
  exact (mul_eq_zero.mp hzero).resolve_left (by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero)

end RHTower
