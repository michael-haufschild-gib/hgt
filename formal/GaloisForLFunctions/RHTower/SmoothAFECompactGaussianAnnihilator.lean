import GaloisForLFunctions.RHTower.SmoothAFECompactGaussianKernel
import GaloisForLFunctions.RHTower.SmoothAFECompactGaussianExterior

open Complex Set Metric
noncomputable section
namespace RHTower

/-- Imaginary Gaussian modes determine the functional transform everywhere
outside the reflected right-half-plane disc. -/
theorem compactGaussianFunctional_eq_zero_off_disc (c : ℂ) {r : ℝ}
    [CompactSpace (closedBall c r)] (hr : 0 ≤ r) (hc : r < c.re)
    (A : C(closedBall c r, ℂ) →L[ℂ] ℂ)
    (haxis : ∀ t : ℝ, A (compactGaussianCauchyKernel (closedBall c r)
      ((t : ℂ) * I)) = 0) :
    ∀ w : ℂ, -w ∉ closedBall c r →
      A (compactGaussianCauchyKernel (closedBall c r) w) = 0 := by
  have hset : {w : ℂ | -w ∉ closedBall c r} = (closedBall (-c) r)ᶜ := by
    ext w
    simp only [mem_setOf_eq, mem_compl_iff, mem_closedBall, dist_eq_norm]
    rw [show -w - c = -(w - (-c)) by ring, norm_neg]
  have h0 : (0 : ℂ) ∈ {w : ℂ | -w ∉ closedBall c r} := by
    have hrc : r < ‖c‖ := hc.trans_le (Complex.re_le_norm c)
    simpa using (not_le_of_gt hrc)
  have hconn : IsPreconnected {w : ℂ | -w ∉ closedBall c r} := by
    rw [hset]
    exact (isPathConnected_complex_disc_exterior (-c) hr).isConnected.isPreconnected
  exact eqOn_zero_of_analyticOnNhd_of_eq_imaginary hconn h0
    (analyticOnNhd_compactGaussianFunctional (closedBall c r)
      (isCompact_closedBall c r) A) haxis

end RHTower
