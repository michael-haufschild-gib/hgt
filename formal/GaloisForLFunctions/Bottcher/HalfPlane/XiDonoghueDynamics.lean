import GaloisForLFunctions.Bottcher.HalfPlane.AnchoredSchwarz
import GaloisForLFunctions.RHTower.Suzuki.SuzukiXiFirstDefectJet

/-!+# Periodic Xi Donoghue orbits falsify RH

The normalized map `m(z) = -XiC'(z)/(c XiC(z))` fixes `i` unconditionally, with real multiplier
strictly between `77/85` and `1`. Under RH it is a holomorphic upper-half-plane self-map.
Schwarz rigidity therefore makes Cayley radius strictly decrease away from `i`, excluding every
other upper periodic point. In particular, a second upper zero of `XiC' + c z XiC` falsifies RH.
-/

open Complex Set
open RHTower GaloisForLFunctions.HTGeometry

namespace Bottcher.HalfPlane

noncomputable section

/-- The unconditional first-jet gap excludes rotations of the disk conjugate. -/
theorem norm_deriv_xiDonoghue_I_lt_one : ‖deriv xiHedenmalmDonoghueTarget I‖ < 1 := by
  have hj := xiHedenmalmLivsicFirstDefectJet_mem_Ioo
  have hc : (xiHedenmalmLivsicFirstDefectJet : ℂ) =
      deriv xiHedenmalmDonoghueTarget I :=
    xiHedenmalmLivsicFirstDefectJet_complex.trans two_mul_I_mul_deriv_xiHedenmalmLivsicTarget_I
  rw [← hc, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (lt_trans (by norm_num) hj.1)]
  exact hj.2

private theorem differentiableAt_xiDonoghue_of_rh (hRH : RiemannHypothesis)
    (z : ℂ) (hz : 0 < z.im) : DifferentiableAt ℂ xiHedenmalmDonoghueTarget z := by
  have hXi : XiC z ≠ 0 := XiC_ne_zero_upperHalf_of_rh hRH hz
  have ha := XiC_analytic z (mem_univ z)
  have hd : DifferentiableAt ℂ (logDeriv XiC) z := by
    exact ha.deriv.differentiableAt.div ha.differentiableAt hXi
  exact hd.neg.div_const _

/-- RH forces strict contraction of the normalized Xi map in Cayley radius. -/
theorem xiDonoghue_cayleyRadius_strict_decrease_of_rh
    (hRH : RiemannHypothesis) {z : ℂ} (hz : 0 < z.im) (hzi : z ≠ I) :
    ‖upperToDisk (xiHedenmalmDonoghueTarget z)‖ < ‖upperToDisk z‖ :=
  cayleyRadius_strict_decrease (differentiableAt_xiDonoghue_of_rh hRH)
    (fun _ hz => im_xiHedenmalmDonoghueTarget_pos_of_rh hRH hz)
    xiHedenmalmDonoghueTarget_I norm_deriv_xiDonoghue_I_lt_one hz hzi

/-- Under RH, `i` is the only upper-half-plane point fixed by any positive iterate. -/
theorem xiDonoghue_periodicPoint_eq_I_of_rh
    (hRH : RiemannHypothesis) {z : ℂ} (hz : 0 < z.im) {n : ℕ} (hn : 0 < n)
    (hper : xiHedenmalmDonoghueTarget^[n] z = z) : z = I :=
  eq_I_of_iterate_eq_self (differentiableAt_xiDonoghue_of_rh hRH)
    (fun _ hz => im_xiHedenmalmDonoghueTarget_pos_of_rh hRH hz)
    xiHedenmalmDonoghueTarget_I norm_deriv_xiDonoghue_I_lt_one hz hn hper

/-- A nonanchor upper periodic point is an RH falsification certificate. -/
theorem not_riemannHypothesis_of_xiDonoghue_periodicPoint :
    (∃ z : ℂ, ∃ n : ℕ, 0 < z.im ∧ z ≠ I ∧ 0 < n ∧
      xiHedenmalmDonoghueTarget^[n] z = z) → ¬ RiemannHypothesis := by
  rintro ⟨z, n, hz, hzi, hn, hper⟩ hRH
  exact hzi (xiDonoghue_periodicPoint_eq_I_of_rh hRH hz hn hper)

/-- A second upper stationary point of the Gaussian-weighted Xi function falsifies RH.
The unavoidable anchor `i` is excluded explicitly. No nonvanishing premise is required. -/
theorem not_riemannHypothesis_of_xiGaussian_stationaryPoint :
    (∃ z : ℂ, 0 < z.im ∧ z ≠ I ∧
      deriv XiC z + (xiHedenmalmDonoghueScale : ℂ) * z * XiC z = 0) →
      ¬ RiemannHypothesis := by
  rintro ⟨z, hz, hzi, hstat⟩ hRH
  have hXi : XiC z ≠ 0 := XiC_ne_zero_upperHalf_of_rh hRH hz
  have hc : (xiHedenmalmDonoghueScale : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr xiHedenmalmDonoghueScale_pos.ne'
  have hfix : xiHedenmalmDonoghueTarget z = z := by
    rw [xiHedenmalmDonoghueTarget, logDeriv_apply]
    field_simp [hXi, hc]
    linear_combination -hstat
  exact hzi (xiDonoghue_periodicPoint_eq_I_of_rh hRH hz (n := 1) Nat.zero_lt_one
    (by simpa only [Function.iterate_one] using hfix))

/-- The excluded stationary point `i` exists unconditionally. -/
theorem xiGaussian_stationary_I :
    deriv XiC I + (xiHedenmalmDonoghueScale : ℂ) * I * XiC I = 0 := by
  have hXi : XiC I ≠ 0 := XiC_ne_zero_of_abs_re_le_nine_halves (by norm_num)
  have hc : (xiHedenmalmDonoghueScale : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr xiHedenmalmDonoghueScale_pos.ne'
  have h := xiHedenmalmDonoghueTarget_I
  rw [xiHedenmalmDonoghueTarget, logDeriv_apply] at h
  field_simp [hXi, hc] at h
  linear_combination -h

/-- Under RH the Gaussian-weighted Xi function has exactly one upper stationary point. -/
theorem xiGaussian_stationary_iff_eq_I_of_rh (hRH : RiemannHypothesis)
    {z : ℂ} (hz : 0 < z.im) :
    deriv XiC z + (xiHedenmalmDonoghueScale : ℂ) * z * XiC z = 0 ↔ z = I := by
  constructor
  · intro hstat
    by_contra hzi
    exact not_riemannHypothesis_of_xiGaussian_stationaryPoint ⟨z, hz, hzi, hstat⟩ hRH
  · rintro rfl
    exact xiGaussian_stationary_I

end
end Bottcher.HalfPlane

#print axioms Bottcher.HalfPlane.norm_deriv_xiDonoghue_I_lt_one
#print axioms Bottcher.HalfPlane.xiDonoghue_cayleyRadius_strict_decrease_of_rh
#print axioms Bottcher.HalfPlane.xiDonoghue_periodicPoint_eq_I_of_rh
#print axioms Bottcher.HalfPlane.not_riemannHypothesis_of_xiDonoghue_periodicPoint
#print axioms Bottcher.HalfPlane.not_riemannHypothesis_of_xiGaussian_stationaryPoint
#print axioms Bottcher.HalfPlane.xiGaussian_stationary_I
#print axioms Bottcher.HalfPlane.xiGaussian_stationary_iff_eq_I_of_rh
