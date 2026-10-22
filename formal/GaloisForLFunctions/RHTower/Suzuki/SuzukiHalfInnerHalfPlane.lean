import GaloisForLFunctions.RHTower.Suzuki.SuzukiInnerDerivative
import GaloisForLFunctions.RHTower.StrictHermiteBiehlerGivesRH
import GaloisForLFunctions.RHTower.Suzuki.SuzukiXiDonoghueTarget
import GaloisForLFunctions.RHTower.Suzuki.SuzukiWeilVerticalDecay
import GaloisForLFunctions.RHTower.XiHadamardFactorization

/-!
# The inner half `A/E` on the closed upper half-plane

Under the Riemann hypothesis the Hedenmalm pair `E = A + iA'`, `A = ξ(1/2 - iz)`, is a
Hermite--Biehler function, so `Θ = E^♯/E` is a contraction above the real axis and unimodular on
it.  This module records the three consequences that every later `L²` computation consumes, all
for the half `A/E = (1 + Θ)/2` rather than for `Θ` itself, which is `0/0` at multiple zeros:

* `‖A/E‖ ≤ 1` on the closed upper half-plane;
* `‖A/E‖² = Re (A/E)` on the real axis, the analytic form of `|Θ| = 1`;
* `A/E` is holomorphic at every point of the closed upper half-plane, the zeros of `E` on the
  axis being removable because `A` vanishes there to strictly larger order.
-/

open Complex

namespace RHTower
noncomputable section

theorem differentiable_xiHedenmalmDeBrangesE : Differentiable ℂ xiHedenmalmDeBrangesE := by
  intro z
  have hd : DifferentiableAt ℂ (deriv XiC) z :=
    ((XiC_analytic z (Set.mem_univ z)).deriv).differentiableAt
  exact (XiC_differentiable z).add (hd.const_mul I)

theorem norm_xiHedenmalmDeBrangesESharp_ofReal_eq (x : ℝ) :
    ‖xiHedenmalmDeBrangesESharp (x : ℂ)‖ = ‖xiHedenmalmDeBrangesE (x : ℂ)‖ := by
  rw [xiHedenmalmDeBrangesESharp_ofReal_eq_conj, RCLike.norm_conj]

/-- On the real axis the inner half `A/E` is a contraction, unconditionally. -/
theorem norm_suzukiHalfInner_ofReal_le_one (x : ℝ) : ‖suzukiHalfInner (x : ℂ)‖ ≤ 1 := by
  rw [suzukiHalfInner, norm_div, ← norm_xiHedenmalmDeBrangesESharp_ofReal_eq, ← norm_div]
  exact norm_XiC_div_ESharp_le_one x

/-- **The boundary energy identity.**  On the real axis `|A/E|² = Re(A/E)`, the analytic form
of `|Θ| = 1`. -/
theorem norm_sq_suzukiHalfInner_ofReal (x : ℝ) :
    ‖suzukiHalfInner (x : ℂ)‖ ^ (2 : ℕ) = (suzukiHalfInner (x : ℂ)).re := by
  have hA : XiC (x : ℂ) = (((XiC (x : ℂ)).re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [XiC_ofReal_im]
  have hD : deriv XiC (x : ℂ) = (((deriv XiC (x : ℂ)).re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [deriv_XiC_ofReal_im]
  set a : ℝ := (XiC (x : ℂ)).re
  set b : ℝ := (deriv XiC (x : ℂ)).re
  have hE : xiHedenmalmDeBrangesE (x : ℂ) = (a : ℂ) + I * (b : ℂ) := by
    rw [xiHedenmalmDeBrangesE, ← hA, ← hD]
  rw [suzukiHalfInner, hE, hA, Complex.sq_norm, Complex.normSq_div, Complex.div_re]
  simp [Complex.normSq_apply]

/-- Under RH the inner half `A/E` is a contraction on the whole closed upper half-plane. -/
theorem norm_suzukiHalfInner_le_one_of_rh (hRH : RiemannHypothesis) {z : ℂ} (hz : 0 ≤ z.im) :
    ‖suzukiHalfInner z‖ ≤ 1 := by
  rcases eq_or_lt_of_le hz with hzero | hpos
  · have hre : z = ((z.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [← hzero]
    rw [hre]
    exact norm_suzukiHalfInner_ofReal_le_one z.re
  · have hE : xiHedenmalmDeBrangesE z ≠ 0 :=
      xiHedenmalmDeBrangesE_ne_zero_upperHalf_of_rh hRH hpos
    have hHB := strict_hermiteBiehler_of_rh hRH z hpos
    rw [suzukiEntireSharp_xiHedenmalmDeBrangesE] at hHB
    have hval : suzukiHalfInner z
        = (1 + xiHedenmalmDeBrangesESharp z / xiHedenmalmDeBrangesE z) / 2 := by
      rw [suzukiHalfInner]
      field_simp
      linear_combination -(xiHedenmalmDeBrangesE_add_sharp z)
    have hw : ‖xiHedenmalmDeBrangesESharp z / xiHedenmalmDeBrangesE z‖ ≤ 1 := by
      rw [norm_div, div_le_one (by positivity)]
      exact hHB.le
    rw [hval, norm_div, Complex.norm_ofNat]
    refine div_le_one_of_le₀ ?_ (by norm_num)
    calc ‖(1 : ℂ) + xiHedenmalmDeBrangesESharp z / xiHedenmalmDeBrangesE z‖
        ≤ ‖(1 : ℂ)‖ + ‖xiHedenmalmDeBrangesESharp z / xiHedenmalmDeBrangesE z‖ :=
          norm_add_le _ _
      _ ≤ 1 + 1 := by rw [norm_one]; linarith
      _ = 2 := by norm_num

/-- If `E` vanishes at a real point then so does `A`. -/
theorem XiC_eq_zero_of_xiHedenmalmDeBrangesE_ofReal_eq_zero {x : ℝ}
    (hE : xiHedenmalmDeBrangesE (x : ℂ) = 0) : XiC (x : ℂ) = 0 := by
  have hre := congrArg Complex.re hE
  rw [xiHedenmalmDeBrangesE] at hre
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.zero_re,
    zero_mul, one_mul, zero_sub, deriv_XiC_ofReal_im, neg_zero, add_zero] at hre
  exact Complex.ext hre (XiC_ofReal_im x)

/-- Under RH, `A/E` is holomorphic at every point of the closed upper half-plane: above the
axis because `E` has no zero there, and on the axis because a zero of `E` is a zero of `A` of
strictly larger order. -/
theorem differentiableAt_suzukiHalfInner_of_rh (hRH : RiemannHypothesis) {z : ℂ}
    (hz : 0 ≤ z.im) : DifferentiableAt ℂ suzukiHalfInner z := by
  by_cases hE : xiHedenmalmDeBrangesE z = 0
  · have hzim : z.im = 0 := by
      rcases eq_or_lt_of_le hz with h | h
      · exact h.symm
      · exact absurd hE (xiHedenmalmDeBrangesE_ne_zero_upperHalf_of_rh hRH h)
    have hre : z = ((z.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hzim]
    have hXi : XiC z = 0 := by
      rw [hre]
      exact XiC_eq_zero_of_xiHedenmalmDeBrangesE_ofReal_eq_zero (by rw [← hre]; exact hE)
    set m : ℕ := (analyticOrderAt XiC z).toNat with hm
    have hord : analyticOrderAt XiC z = (m : ℕ∞) := (ENat.coe_toNat (XiC_order_ne_top z)).symm
    have hmpos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h0 | h
      · exfalso
        rw [h0] at hord
        have := (XiC_analytic z (Set.mem_univ z)).analyticOrderAt_eq_zero.mp (by exact_mod_cast hord)
        exact this hXi
      · exact h
    exact (hasDerivAt_suzukiHalfInner hmpos hord).differentiableAt
  · exact (XiC_differentiable z).div (differentiable_xiHedenmalmDeBrangesE z) hE

end
end RHTower
