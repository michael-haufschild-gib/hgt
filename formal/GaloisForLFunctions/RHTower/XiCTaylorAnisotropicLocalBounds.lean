import GaloisForLFunctions.RHTower.XiCTaylorAnisotropicScheduleLookup
import GaloisForLFunctions.RHTower.XiDeck

/-!
# Local Xi bounds on the anisotropic Taylor mesh

Xi peeling gives a quantitative lower bound for the value of `XiC` along the centered anisotropic
mesh: the value is bounded below by a positive constant times the mesh distance raised to the
local analytic order.  The derivative is eventually bounded by continuity.  These are the two
local inputs needed to convert super-accurate value and derivative approximation into stability
of logarithmic derivatives near a hypothetical zero.
-/

open Complex Metric Filter Topology

namespace RHTower

noncomputable section

/-- Along the centered anisotropic mesh, `XiC` is bounded below by a positive constant times the
inverse mesh resolution raised to its analytic order at the target. -/
theorem eventually_xiC_anisotropic_value_lower (sigma : ℂ) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ n : ℕ in atTop,
        c * (1 / (((n + 1 : ℕ) : ℝ))) ^ (analyticOrderAt xi sigma).toNat ≤
          ‖XiC (xiCTaylorAnisotropicCenteredPoint sigma n)‖ := by
  obtain ⟨R, hR, h, hhan, hh0, hfact⟩ := xi_peel_ball sigma
  let c : ℝ := ‖h sigma‖ / 2
  have hsigmaBall : sigma ∈ ball sigma R := mem_ball_self hR
  have hhSigma : h sigma ≠ 0 := hh0 sigma hsigmaBall
  have hc : 0 < c := div_pos (norm_pos_iff.mpr hhSigma) (by norm_num)
  refine ⟨c, hc, ?_⟩
  have hsTend : Tendsto
      (fun n : ℕ => xiTaylorAnisotropicRightApprox sigma (n + 1)) atTop
      (nhds sigma) :=
    (tendsto_xiTaylorAnisotropicRightApprox_succ sigma).mono_right nhdsWithin_le_nhds
  have hevBall : ∀ᶠ n : ℕ in atTop,
      xiTaylorAnisotropicRightApprox sigma (n + 1) ∈ ball sigma R :=
    hsTend.eventually (isOpen_ball.mem_nhds hsigmaBall)
  have hhCont : ContinuousAt h sigma := (hhan sigma hsigmaBall).continuousAt
  have hnormTend : Tendsto
      (fun n : ℕ => ‖h (xiTaylorAnisotropicRightApprox sigma (n + 1))‖)
      atTop (nhds ‖h sigma‖) :=
    hhCont.norm.tendsto.comp hsTend
  have hevH : ∀ᶠ n : ℕ in atTop,
      c ≤ ‖h (xiTaylorAnisotropicRightApprox sigma (n + 1))‖ := by
    have hclt : c < ‖h sigma‖ := by
      dsimp [c]
      linarith [norm_pos_iff.mpr hhSigma]
    exact (hnormTend.eventually (eventually_gt_nhds hclt)).mono fun _ hn => hn.le
  filter_upwards [hevBall, hevH] with n hnBall hnH
  let N : ℕ := n + 1
  let s : ℂ := xiTaylorAnisotropicRightApprox sigma N
  have hN : 0 < N := by dsimp [N]; omega
  have hre := (xiTaylorAnisotropicRightApprox_re_sub_bounds sigma hN).1
  have hnormLower : 1 / (N : ℝ) ≤ ‖s - sigma‖ :=
    hre.trans ((le_abs_self (s - sigma).re).trans (abs_re_le_norm (s - sigma)))
  have hpow : (1 / (N : ℝ)) ^ (analyticOrderAt xi sigma).toNat ≤
      ‖s - sigma‖ ^ (analyticOrderAt xi sigma).toNat :=
    pow_le_pow_left₀ (by positivity) hnormLower _
  rw [xiCTaylorAnisotropicCenteredPoint, XiC_xiCTaylorCenteredPoint]
  rw [hfact s hnBall, norm_mul, norm_pow]
  rw [mul_comm c]
  exact mul_le_mul hpow hnH (by positivity) (by positivity)

/-- The derivative of `XiC` is eventually bounded along every centered anisotropic mesh fibre. -/
theorem eventually_xiC_anisotropic_deriv_upper (sigma : ℂ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ n : ℕ in atTop,
        ‖deriv XiC (xiCTaylorAnisotropicCenteredPoint sigma n)‖ ≤ C := by
  let alpha : ℂ := xiCTaylorCenteredPoint sigma
  let C : ℝ := ‖deriv XiC alpha‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  have hderivCont : ContinuousAt (deriv XiC) alpha :=
    (XiC_analytic alpha (Set.mem_univ alpha)).deriv.continuousAt
  have htend : Tendsto
      (fun n : ℕ => ‖deriv XiC (xiCTaylorAnisotropicCenteredPoint sigma n)‖)
      atTop (nhds ‖deriv XiC alpha‖) :=
    hderivCont.norm.tendsto.comp (tendsto_xiCTaylorAnisotropicCenteredPoint sigma)
  have hev : ∀ᶠ n : ℕ in atTop,
      ‖deriv XiC (xiCTaylorAnisotropicCenteredPoint sigma n)‖ < C :=
    htend.eventually (eventually_lt_nhds (by dsimp [C]; linarith))
  exact hev.mono fun _ hn => hn.le

end

end RHTower
