import GaloisForLFunctions.RHTower.XiAnisotropicPoleGrowth
import GaloisForLFunctions.RHTower.PrimeArchSourceUpperBoundGate

/-!
# A sublinear anisotropic-mesh gate for RH

The anisotropic rational mesh approaches each point of the open left critical strip from the
right at horizontal scale `1 / n` and vertical scale `1 / n²`.  At an Xi zero the real part of
the logarithmic derivative therefore has a positive linear lower rate.  It follows that a merely
sublinear upper rate on these explicit mesh values excludes every off-line zero.

This premise neither quantifies over zeros nor requires a global bound: the logarithmic derivative
may be unbounded, provided its growth on each fixed mesh fibre is `o(n)` from above.
-/

open Complex Filter

namespace RHTower

noncomputable section

/-- On every anisotropic rational mesh fibre based in the open left critical strip, the real part
of the Xi logarithmic derivative has sublinear upper growth. -/
def XiAnisotropicLogDerivSublinearUpper : Prop :=
  ∀ sigma : ℂ, 0 < sigma.re → sigma.re < 1 / 2 →
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ n : ℕ in atTop,
        (logDeriv xi (xiTaylorAnisotropicRightApprox sigma (n + 1))).re /
          ((n + 1 : ℕ) : ℝ) < epsilon

/-- Sublinear upper growth of the Xi logarithmic derivative on the explicit anisotropic rational
mesh excludes reflected off-line Xi zeros and proves the Riemann hypothesis. -/
theorem riemannHypothesis_of_xiAnisotropicLogDerivSublinearUpper
    (hsub : XiAnisotropicLogDerivSublinearUpper) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro rho hrho hzero
  have hrhoHalf : 1 / 2 < rho.re := mem_rightHalf.mp hrho
  have hrhoPos : 0 < rho.re := lt_trans (by norm_num) hrhoHalf
  have hrhoOne : rho.re < 1 := xi_zero_re_lt_one hzero
  let sigma : ℂ := 1 - rho
  have hsigmaZero : xi sigma = 0 := by
    dsimp only [sigma]
    rw [xi_one_sub, hzero]
  have hsigmaPos : 0 < sigma.re := by
    dsimp only [sigma]
    simp only [sub_re, one_re]
    linarith
  have hsigmaHalf : sigma.re < 1 / 2 := by
    dsimp only [sigma]
    simp only [sub_re, one_re]
    linarith
  let m : ℕ := (analyticOrderAt xi sigma).toNat
  have hm : 0 < m := Nat.pos_of_ne_zero (xi_order_toNat_ne_zero hsigmaZero)
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hlower :=
    eventually_xiOrder_div_ten_lt_logDeriv_anisotropicMesh_re_div hsigmaZero
  have hupper := hsub sigma hsigmaPos hsigmaHalf ((m : ℝ) / 20)
    (div_pos hmR (by norm_num))
  obtain ⟨n, hnLower, hnUpper⟩ := (hlower.and hupper).exists
  change (m : ℝ) / 10 <
      (logDeriv xi (xiTaylorAnisotropicRightApprox sigma (n + 1))).re /
        ((n + 1 : ℕ) : ℝ) at hnLower
  linarith

/-- Under RH, reflection makes every point of the open left critical strip Xi-regular.  Continuity
of the logarithmic derivative along the anisotropic mesh then makes its values bounded, hence
sublinear after division by the mesh resolution. -/
theorem xiAnisotropicLogDerivSublinearUpper_of_riemannHypothesis
    (hRH : RiemannHypothesis) : XiAnisotropicLogDerivSublinearUpper := by
  intro sigma _hsigmaPos hsigmaHalf epsilon hepsilon
  have hreflectRight : 1 - sigma ∈ rightHalf := by
    rw [mem_rightHalf]
    simp only [sub_re, one_re]
    linarith
  have hreflectNe : xi (1 - sigma) ≠ 0 :=
    (rh_iff_xi_ne_zero_right.mp hRH) (1 - sigma) hreflectRight
  have hxi : xi sigma ≠ 0 := by
    rw [xi_one_sub] at hreflectNe
    exact hreflectNe
  have hmesh : Tendsto
      (fun n : ℕ => xiTaylorAnisotropicRightApprox sigma (n + 1)) atTop
      (nhds sigma) :=
    (tendsto_xiTaylorAnisotropicRightApprox_succ sigma).mono_right
      nhdsWithin_le_nhds
  have hlogAnalytic : AnalyticAt ℂ (logDeriv xi) sigma := by
    change AnalyticAt ℂ (fun z => deriv xi z / xi z) sigma
    exact (xi_analyticOnNhd_univ sigma (Set.mem_univ sigma)).deriv.div
      (xi_analyticOnNhd_univ sigma (Set.mem_univ sigma)) hxi
  have hlog : Tendsto
      (fun n : ℕ => logDeriv xi (xiTaylorAnisotropicRightApprox sigma (n + 1)))
      atTop (nhds (logDeriv xi sigma)) :=
    hlogAnalytic.continuousAt.tendsto.comp hmesh
  have hre : Tendsto
      (fun n : ℕ =>
        (logDeriv xi (xiTaylorAnisotropicRightApprox sigma (n + 1))).re)
      atTop (nhds (logDeriv xi sigma).re) :=
    Complex.continuous_re.continuousAt.tendsto.comp hlog
  have hinv : Tendsto
      (fun n : ℕ => (((n + 1 : ℕ) : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_natCast_atTop_atTop.inv_tendsto_atTop.comp
      (Filter.tendsto_add_atTop_nat 1)
  have hratio : Tendsto
      (fun n : ℕ =>
        (logDeriv xi (xiTaylorAnisotropicRightApprox sigma (n + 1))).re /
          ((n + 1 : ℕ) : ℝ))
      atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using hre.mul hinv
  exact hratio.eventually (eventually_lt_nhds hepsilon)

/-- **Exact anisotropic sublinear-growth criterion for RH.** -/
theorem xiAnisotropicLogDerivSublinearUpper_iff_riemannHypothesis :
    XiAnisotropicLogDerivSublinearUpper ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_xiAnisotropicLogDerivSublinearUpper,
    xiAnisotropicLogDerivSublinearUpper_of_riemannHypothesis⟩

end

end RHTower
