import GaloisForLFunctions.Bottcher.AnalyticRoot
import GaloisForLFunctions.RHTower.HedenmalmThetaMobiusPoleUnitStrictTransverseCurvature
import GaloisForLFunctions.RHTower.TwinRigidity

/-!
# Exact arithmetic reduction of the right-half Xi square root

The pole-cleared squarefree Euler function

`((s - 1) * zeta(s)) / zeta(2s)`

is analytic on `Re s > 1/2`.  Completed Xi is its product with the explicit factor

`(s / 2) * Gamma_R(s) * zeta(2s)`.

That complementary factor is analytic and nowhere zero on the same half-plane, hence has an
analytic square root there by simple connectedness.  Consequently the pole-cleared squarefree
Euler function has exactly the Xi divisor, and its analytic square-root problem is equivalent to
`RHLadder 1` without hypotheses.

This is an exact arithmetic localization, not a proof of the first ladder rung.  It also explains
why formally halving the prime-zeta trace cannot solve the problem: continuing that half-trace
single-valuedly is precisely the square-root obligation isolated here.
-/

open Complex Filter Topology

namespace RHTower

open HedenmalmThetaSource

noncomputable section

/-- Explicit zero-free factor converting the pole-cleared squarefree Euler function into Xi. -/
def xiSquarefreePoleComplement (s : ℂ) : ℂ :=
  (s / 2 * Complex.Gammaℝ s) * riemannZeta (2 * s)

/-- The explicit completion factor is analytic throughout the strict right half-plane. -/
theorem analyticOnNhd_xiSquarefreePoleComplement_rightHalf :
    AnalyticOnNhd ℂ xiSquarefreePoleComplement rightHalf := by
  intro s hs
  have hspos : 0 < s.re := by
    rw [mem_rightHalf] at hs
    linarith
  have htwoRe : 1 < (2 * s).re := by
    rw [mem_rightHalf] at hs
    norm_num only [mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
    linarith
  have htwoOne : 2 * s ≠ 1 := by
    intro h
    rw [h] at htwoRe
    norm_num at htwoRe
  have hGamma : AnalyticAt ℂ Complex.Gammaℝ s :=
    Gammaℝ_analyticAt (Complex.Gammaℝ_ne_zero_of_re_pos hspos)
  have hZeta : AnalyticAt ℂ (fun z : ℂ => riemannZeta (2 * z)) s :=
    (analyticOn_riemannZeta (2 * s) htwoOne).comp (by fun_prop)
  exact ((show AnalyticAt ℂ (fun z : ℂ => z / 2) s by fun_prop).mul hGamma).mul hZeta

/-- The explicit completion factor never vanishes on the strict right half-plane. -/
theorem xiSquarefreePoleComplement_ne_zero_rightHalf
    {s : ℂ} (hs : s ∈ rightHalf) :
    xiSquarefreePoleComplement s ≠ 0 := by
  have hspos : 0 < s.re := by
    rw [mem_rightHalf] at hs
    linarith
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hspos
    norm_num at hspos
  have htwoRe : 1 < (2 * s).re := by
    rw [mem_rightHalf] at hs
    norm_num only [mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
    linarith
  exact mul_ne_zero
    (mul_ne_zero (div_ne_zero hs0 (by norm_num))
      (Complex.Gammaℝ_ne_zero_of_re_pos hspos))
    (riemannZeta_ne_zero_of_one_lt_re htwoRe)

/-- Exact right-half factorization of Xi through the pole-cleared squarefree Euler function. -/
theorem xi_eq_xiSquarefreePoleComplement_mul_squarefreeMobiusCriticalPoleUnit
    {s : ℂ} (hs : s ∈ rightHalf) :
    xi s = xiSquarefreePoleComplement s * squarefreeMobiusCriticalPoleUnit s := by
  have hspos : 0 < s.re := by
    rw [mem_rightHalf] at hs
    linarith
  have htwoRe : 1 < (2 * s).re := by
    rw [mem_rightHalf] at hs
    norm_num only [mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
    linarith
  have hZeta : riemannZeta (2 * s) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re htwoRe
  have hZeta' : riemannZeta (s * 2) ≠ 0 := by
    simpa [mul_comm] using hZeta
  rw [xi_eq_half_mul_Gammaℝ_mul_zetaResidueUnit hspos]
  unfold xiSquarefreePoleComplement squarefreeMobiusCriticalPoleUnit
  field_simp [hZeta']

/-- The pole-cleared squarefree Euler function is analytic on the strict right half-plane. -/
theorem analyticOnNhd_squarefreeMobiusCriticalPoleUnit_rightHalf :
    AnalyticOnNhd ℂ squarefreeMobiusCriticalPoleUnit rightHalf := by
  intro s hs
  have htwoRe : 1 < (2 * s).re := by
    rw [mem_rightHalf] at hs
    norm_num only [mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
    linarith
  have htwoOne : 2 * s ≠ 1 := by
    intro h
    rw [h] at htwoRe
    norm_num at htwoRe
  exact (analyticAt_zetaResidueUnit s).div
    ((analyticOn_riemannZeta (2 * s) htwoOne).comp (by fun_prop))
    (riemannZeta_ne_zero_of_one_lt_re htwoRe)

/-- Removing the explicit zero-free completion factor preserves the complete Xi divisor. -/
theorem analyticOrderAt_squarefreeMobiusCriticalPoleUnit_eq_xi
    {s : ℂ} (hs : s ∈ rightHalf) :
    analyticOrderAt squarefreeMobiusCriticalPoleUnit s = analyticOrderAt xi s := by
  have hev : xi =ᶠ[𝓝 s]
      fun z => xiSquarefreePoleComplement z * squarefreeMobiusCriticalPoleUnit z := by
    filter_upwards [isOpen_rightHalf.mem_nhds hs] with z hz
    exact xi_eq_xiSquarefreePoleComplement_mul_squarefreeMobiusCriticalPoleUnit hz
  have hcomp := analyticOnNhd_xiSquarefreePoleComplement_rightHalf s hs
  have hpole := analyticOnNhd_squarefreeMobiusCriticalPoleUnit_rightHalf s hs
  rw [analyticOrderAt_congr hev]
  change analyticOrderAt squarefreeMobiusCriticalPoleUnit s =
    analyticOrderAt (xiSquarefreePoleComplement * squarefreeMobiusCriticalPoleUnit) s
  rw [analyticOrderAt_mul hcomp hpole,
    hcomp.analyticOrderAt_eq_zero.mpr
      (xiSquarefreePoleComplement_ne_zero_rightHalf hs), zero_add]

/-- The explicit completion factor has an unconditional analytic square root on `rightHalf`. -/
theorem exists_rightHalf_sqrt_xiSquarefreePoleComplement :
    ∃ r : ℂ → ℂ, AnalyticOnNhd ℂ r rightHalf ∧
      ∀ s ∈ rightHalf, r s ^ 2 = xiSquarefreePoleComplement s := by
  exact Bottcher.exists_analyticOnNhd_pow_eq isSimplyConnected_rightHalf isOpen_rightHalf
    analyticOnNhd_xiSquarefreePoleComplement_rightHalf
    (fun s hs => xiSquarefreePoleComplement_ne_zero_rightHalf hs)
    (N := 2) (by norm_num)

/-- Xi has a right-half analytic square root iff the pole-cleared squarefree Euler function does. -/
theorem exists_rightHalf_sqrt_xi_iff_squarefreeMobiusCriticalPoleUnit :
    (∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g rightHalf ∧
        ∀ s ∈ rightHalf, g s ^ 2 = xi s) ↔
      ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h rightHalf ∧
        ∀ s ∈ rightHalf, h s ^ 2 = squarefreeMobiusCriticalPoleUnit s := by
  obtain ⟨r, hr, hrsq⟩ := exists_rightHalf_sqrt_xiSquarefreePoleComplement
  have hrne : ∀ s ∈ rightHalf, r s ≠ 0 := by
    intro s hs hzero
    have hsq := hrsq s hs
    rw [hzero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hsq
    exact xiSquarefreePoleComplement_ne_zero_rightHalf hs hsq.symm
  constructor
  · rintro ⟨g, hg, hgsq⟩
    refine ⟨fun s => g s / r s, hg.div hr hrne, ?_⟩
    intro s hs
    have hfac := xi_eq_xiSquarefreePoleComplement_mul_squarefreeMobiusCriticalPoleUnit hs
    rw [div_pow, hgsq s hs, hrsq s hs, hfac]
    field_simp [xiSquarefreePoleComplement_ne_zero_rightHalf hs]
  · rintro ⟨h, hh, hhsq⟩
    refine ⟨fun s => r s * h s, hr.mul hh, ?_⟩
    intro s hs
    rw [mul_pow, hrsq s hs, hhsq s hs]
    exact (xi_eq_xiSquarefreePoleComplement_mul_squarefreeMobiusCriticalPoleUnit hs).symm

/-- Exact arithmetic face of the first multiplicity-parity rung. -/
theorem rhLadder_one_iff_squarefreeMobiusCriticalPoleUnit_sqrt :
    RHLadder 1 ↔ ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h rightHalf ∧
      ∀ s ∈ rightHalf, h s ^ 2 = squarefreeMobiusCriticalPoleUnit s := by
  rw [rhLadder_one_iff_sqrt_rightHalf,
    exists_rightHalf_sqrt_xi_iff_squarefreeMobiusCriticalPoleUnit]

end

end RHTower
