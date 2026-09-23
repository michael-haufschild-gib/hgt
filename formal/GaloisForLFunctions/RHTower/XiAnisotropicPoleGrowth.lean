import GaloisForLFunctions.RHTower.XiTaylorAnisotropicMesh
import GaloisForLFunctions.RHTower.CompletedPrimeFluxFittingAttachment

/-!
# Xi logarithmic residues on the anisotropic rational mesh

The explicit `1/n` by `1/n^(2 : ℕ)` mesh approaches every target through its punctured neighborhood.
Composing this fact with the normalized Xi logarithmic-residue theorem shows that the mesh reads
the full analytic multiplicity exactly.  Together with the mesh reciprocal amplifier, this is the
source-pole input for the sublinear finite-Taylor flux criterion.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- The normalized Xi logarithmic derivative along the anisotropic rational mesh converges to the
full analytic multiplicity at the target. -/
theorem xi_normalizedLogDeriv_anisotropicMesh_tendsto (sigma : ℂ) :
    Tendsto
      (fun n : ℕ =>
        (xiTaylorAnisotropicRightApprox sigma (n + 1) - sigma) *
          logDeriv xi (xiTaylorAnisotropicRightApprox sigma (n + 1)))
      atTop (nhds ((analyticOrderAt xi sigma).toNat : ℂ)) := by
  exact (xi_normalizedLogDeriv_tendsto_order sigma).comp
    (tendsto_xiTaylorAnisotropicRightApprox_succ sigma)

/-- At an Xi zero, the real part of the logarithmic derivative grows at a positive linear rate
along the explicit anisotropic rational mesh.  The lower rate is one tenth of the analytic
multiplicity; no Diophantine property of the zero ordinate is used. -/
theorem eventually_xiOrder_div_ten_lt_logDeriv_anisotropicMesh_re_div
    {sigma : ℂ} (hzero : xi sigma = 0) :
    ∀ᶠ n : ℕ in atTop,
      (((analyticOrderAt xi sigma).toNat : ℝ) / 10) <
        (logDeriv xi (xiTaylorAnisotropicRightApprox sigma (n + 1))).re /
          ((n + 1 : ℕ) : ℝ) := by
  let m : ℕ := (analyticOrderAt xi sigma).toNat
  have hm : 0 < m := Nat.pos_of_ne_zero (xi_order_toNat_ne_zero hzero)
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hnorm := xi_normalizedLogDeriv_anisotropicMesh_tendsto sigma
  have herr : ∀ᶠ n : ℕ in atTop,
      ‖(xiTaylorAnisotropicRightApprox sigma (n + 1) - sigma) *
          logDeriv xi (xiTaylorAnisotropicRightApprox sigma (n + 1)) - (m : ℂ)‖ <
        (m : ℝ) / 10 := by
    have hball := hnorm.eventually
      (Metric.ball_mem_nhds ((m : ℂ)) (ε := (m : ℝ) / 10)
        (div_pos hmR (by norm_num)))
    simpa only [Metric.mem_ball, dist_eq_norm, m] using hball
  filter_upwards [herr] with n hnerr
  let N : ℕ := n + 1
  let delta : ℂ := xiTaylorAnisotropicRightApprox sigma N - sigma
  let L : ℂ := logDeriv xi (xiTaylorAnisotropicRightApprox sigma N)
  let e : ℂ := delta * L - (m : ℂ)
  have hN : 0 < N := by dsimp [N]; omega
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hgeom := xiTaylorAnisotropicRightApprox_re_sub_bounds sigma hN
  have him := abs_xiTaylorAnisotropicRightApprox_im_sub_lt sigma hN
  have hdeltaRe : delta.re =
      (xiTaylorAnisotropicRightApprox sigma N - sigma).re := rfl
  have hinvRe : (N : ℝ) / 5 < delta⁻¹.re := by
    apply nat_div_five_lt_inv_re_of_anisotropic hN
    · simpa only [hdeltaRe] using hgeom.1
    · simpa only [hdeltaRe] using hgeom.2
    · simpa only [delta] using him
  have hinvNorm : ‖delta⁻¹‖ ≤ (N : ℝ) := by
    apply norm_inv_le_nat_of_inv_nat_le_re hN
    simpa only [hdeltaRe] using hgeom.1
  have hdeltaPos : 0 < delta.re := by
    have hInvPos : (0 : ℝ) < 1 / (N : ℝ) := by positivity
    exact lt_of_lt_of_le hInvPos (by simpa only [hdeltaRe] using hgeom.1)
  have hdelta : delta ≠ 0 := ne_of_apply_ne Complex.re (ne_of_gt hdeltaPos)
  have he : ‖e‖ < (m : ℝ) / 10 := by
    simpa only [e, delta, L, N] using hnerr
  have hL : L = delta⁻¹ * ((m : ℂ) + e) := by
    rw [show (m : ℂ) + e = delta * L by simp [e]]
    field_simp
  have hLre : L.re = (m : ℝ) * delta⁻¹.re + (delta⁻¹ * e).re := by
    rw [hL, mul_add, add_re, mul_re]
    simp
    ring
  have herrNorm : ‖delta⁻¹ * e‖ < (N : ℝ) * ((m : ℝ) / 10) := by
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hinvNorm (norm_nonneg e))
      (mul_lt_mul_of_pos_left he hNR)
  have herrRe : -((N : ℝ) * ((m : ℝ) / 10)) < (delta⁻¹ * e).re := by
    exact (abs_lt.mp ((Complex.abs_re_le_norm _).trans_lt herrNorm)).1
  change (m : ℝ) / 10 < L.re / (N : ℝ)
  rw [lt_div_iff₀ hNR]
  nlinarith

end

end RHTower
