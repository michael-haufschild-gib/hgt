import GaloisForLFunctions.RHTower.XiHurwitzConstraintOrientation
import GaloisForLFunctions.ArakelovW
import GaloisForLFunctions.RHTower.GelfondSchneider

/-!
# Arakelov--Hurwitz algebraicity collision

The Arakelov coordinate `w(rho) = 1 - 1/rho` and the Hurwitz monodromy character
`q(rho) = exp (-2*pi*i*rho)` cannot both be algebraic at a nonreal point.

Indeed, algebraicity of `w(rho)` makes `rho` algebraic.  On the principal branch,

`q(rho) = (-1) ^ (-2*rho)`.

Gelfond--Schneider therefore makes `q(rho)` transcendental unless `-2*rho` is rational.  Thus
simultaneous algebraicity forces `rho` real.  Since Xi has no real zero in the open critical strip,
simultaneous algebraicity at every hypothetical right-half Xi zero forces RH.

This is a static cross-coordinate constraint.  It uses no positivity, zero measure, spectral
operator, limiting approximation, or zero-location hypothesis.
-/

open Complex Set
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open HurwitzOrbit

namespace RHTower

noncomputable section

/-- Algebraicity of the Arakelov coordinate pulls back through its inverse Möbius map. -/
theorem isAlgebraic_rho_of_arakelovW
    {rho : ℂ} (h : IsAlgebraic ℚ (arakelovW rho)) :
    IsAlgebraic ℚ rho := by
  have hone : IsAlgebraic ℚ (1 : ℂ) := by
    simpa using
      (isIntegral_algebraMap : IsIntegral ℚ (algebraMap ℚ ℂ 1)).isAlgebraic
  have h_inv : IsAlgebraic ℚ (1 - arakelovW rho) := hone.sub h
  have := h_inv.inv
  simpa [arakelovW] using this

/-- The Hurwitz monodromy character is the principal Gelfond--Schneider power
`(-1)^(-2*rho)`. -/
theorem monoScalar_eq_negOne_cpow (rho : ℂ) :
    monoScalar rho = (-1 : ℂ) ^ (-2 * rho) := by
  rw [Complex.cpow_def, if_neg (by norm_num : (-1 : ℂ) ≠ 0),
    Complex.log_neg_one, monoScalar]
  congr 1
  ring

/-- Simultaneous algebraicity of the Arakelov and Hurwitz coordinates forces twice the exponent
to be rational. -/
theorem exists_rat_eq_neg_two_mul_of_arakelovW_algebraic_of_monoScalar_algebraic
    {rho : ℂ}
    (hw : IsAlgebraic ℚ (arakelovW rho))
    (hq : IsAlgebraic ℚ (monoScalar rho)) :
    ∃ r : ℚ, -2 * rho = (r : ℂ) := by
  have hrho : IsAlgebraic ℚ rho := isAlgebraic_rho_of_arakelovW hw
  have hnegTwo : IsAlgebraic ℚ (-2 : ℂ) := by
    simpa using
      (isIntegral_algebraMap : IsIntegral ℚ (algebraMap ℚ ℂ (-2))).isAlgebraic
  have hbeta : IsAlgebraic ℚ (-2 * rho) := hnegTwo.mul hrho
  by_contra hirr
  have hnegOne : IsAlgebraic ℚ (-1 : ℂ) := by
    simpa using
      (isIntegral_algebraMap : IsIntegral ℚ (algebraMap ℚ ℂ (-1))).isAlgebraic
  have htrans : Transcendental ℚ ((-1 : ℂ) ^ (-2 * rho)) := by
    apply GaloisForLFunctions.RHTower.GelfondSchneiderProof.Setup.transcendental_cpow_of_isAlgebraic_of_irrational
      (-1) (-2 * rho) hnegOne hbeta ⟨by norm_num, by norm_num⟩
    intro i j hij
    apply hirr
    refine ⟨(i : ℚ) / (j : ℚ), ?_⟩
    norm_cast at hij ⊢
  apply htrans
  rw [← monoScalar_eq_negOne_cpow rho]
  exact hq

/-- Positive constraint law: at a nonreal point, algebraicity of the Arakelov coordinate forces
transcendence of the Hurwitz monodromy character. -/
theorem monoScalar_transcendental_of_arakelovW_algebraic_of_im_ne_zero
    {rho : ℂ} (hw : IsAlgebraic ℚ (arakelovW rho)) (him : rho.im ≠ 0) :
    Transcendental ℚ (monoScalar rho) := by
  intro hq
  obtain ⟨r, hr⟩ :=
    exists_rat_eq_neg_two_mul_of_arakelovW_algebraic_of_monoScalar_algebraic hw hq
  have hrim := congrArg Complex.im hr
  norm_num at hrim
  apply him
  linarith

/-- Simultaneous algebraicity forces the exponent onto the real axis. -/
theorem im_eq_zero_of_arakelovW_algebraic_of_monoScalar_algebraic
    {rho : ℂ}
    (hw : IsAlgebraic ℚ (arakelovW rho))
    (hq : IsAlgebraic ℚ (monoScalar rho)) :
    rho.im = 0 := by
  obtain ⟨r, hr⟩ :=
    exists_rat_eq_neg_two_mul_of_arakelovW_algebraic_of_monoScalar_algebraic hw hq
  have him := congrArg Complex.im hr
  norm_num at him
  linarith

/-- No point in the open critical strip can simultaneously be an Xi zero and carry algebraic
Arakelov and Hurwitz coordinates. -/
theorem xi_ne_zero_of_openCriticalStrip_of_arakelovW_algebraic_of_monoScalar_algebraic
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (hw : IsAlgebraic ℚ (arakelovW rho))
    (hq : IsAlgebraic ℚ (monoScalar rho)) :
    xi rho ≠ 0 := by
  intro hzero
  have him : rho.im = 0 :=
    im_eq_zero_of_arakelovW_algebraic_of_monoScalar_algebraic hw hq
  have hrhoReal : rho = (rho.re : ℂ) := by
    apply Complex.ext <;> simp [him]
  have hpos := xi_pos_on_real_anchor hstrip.1 hstrip.2
  rw [hrhoReal] at hzero
  rw [hzero] at hpos
  simp at hpos

/-- Static arithmetic hypothesis on hypothetical right-half Xi divisor points. -/
def XiRightArakelovHurwitzAlgebraic : Prop :=
  ∀ rho : XiDivisorSupport, 1 / 2 < (rho : ℂ).re →
    IsAlgebraic ℚ (arakelovW (rho : ℂ)) ∧
      IsAlgebraic ℚ (xiHurwitzMonodromyCharacter rho)

/-- **Arakelov--Hurwitz algebraicity collision criterion.** If both independently defined
constraint coordinates are algebraic at every hypothetical right-half Xi zero, then RH holds. -/
theorem riemannHypothesis_of_xiRightArakelovHurwitzAlgebraic
    (h : XiRightArakelovHurwitzAlgebraic) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro rho hrho hzero
  let support : XiDivisorSupport :=
    ⟨rho, mem_xi_divisor_support_of_eq_zero hzero⟩
  have halg := h support (mem_rightHalf.mp hrho)
  exact xi_ne_zero_of_openCriticalStrip_of_arakelovW_algebraic_of_monoScalar_algebraic
    (xi_divisor_support_re_mem_open_unit support) halg.1 halg.2 hzero

end

end RHTower
