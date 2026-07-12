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
  have hrhoOne : rho.re < 1 := xi_zero_re_lt_one hrhoPos hzero
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

end

end RHTower
