import GaloisForLFunctions.RHTower.FZZCigarOneSidedRadialReflectionLaw

/-!
# Reflection selector for physical one-sided FZZ radial response

Real component of physical one-sided mixed receiver is odd, negative at positive momentum, and
zero exactly at reflection-fixed momentum.
-/

open Complex

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- At positive momentum real component of physical one-sided mixed receiver is negative. -/
theorem fzzMarkedRadialReplicaResponse_momentum_deriv_re_neg_of_pos
    (radialCoupling radialScale : ℝ) {momentum : ℝ} (hmomentum : 0 < momentum) :
    (deriv (fzzMarkedRadialReplicaResponse
      radialCoupling radialScale) momentum).re < 0 := by
  rw [(hasDerivAt_fzzMarkedRadialReplicaResponse_momentum
    radialCoupling radialScale momentum).deriv]
  let scale : ℝ := fzzMarkedRadialReplicaRate radialScale / Real.exp radialScale
  let T : ℂ := deriv Complex.digamma
    (1 + ((momentum / Real.exp radialScale : ℝ) : ℂ) * I)
  have hscale : 0 < scale :=
    div_pos (fzzMarkedRadialReplicaRate_pos radialScale) (Real.exp_pos radialScale)
  have htrig : T.im < 0 :=
    _root_.RHTower.deriv_digamma_vertical_im_neg zero_lt_one
      (div_pos hmomentum (Real.exp_pos radialScale))
  change (-((scale : ℂ)) * I * T).re < 0
  have hre : (-((scale : ℂ)) * I * T).re = scale * T.im := by
    simp [Complex.mul_re]
  rw [hre]
  exact mul_neg_of_pos_of_neg hscale htrig

/-- Real component vanishes exactly at reflection-fixed momentum. -/
theorem fzzMarkedRadialReplicaResponse_momentum_deriv_re_eq_zero_iff
    (radialCoupling radialScale momentum : ℝ) :
    (deriv (fzzMarkedRadialReplicaResponse
      radialCoupling radialScale) momentum).re = 0 ↔ momentum = 0 := by
  constructor
  · intro hzero
    rcases lt_trichotomy momentum 0 with hneg | heq | hpos
    · have hpos' := fzzMarkedRadialReplicaResponse_momentum_deriv_re_neg_of_pos
        radialCoupling radialScale (neg_pos.mpr hneg)
      rw [fzzMarkedRadialReplicaResponse_momentum_deriv_neg_re, hzero, neg_zero] at hpos'
      exact False.elim (lt_irrefl 0 hpos')
    · exact heq
    · have hneg' := fzzMarkedRadialReplicaResponse_momentum_deriv_re_neg_of_pos
        radialCoupling radialScale hpos
      rw [hzero] at hneg'
      exact False.elim (lt_irrefl 0 hneg')
  · rintro rfl
    have hreflect := fzzMarkedRadialReplicaResponse_momentum_deriv_neg_re
      radialCoupling radialScale 0
    simp only [neg_zero] at hreflect
    linarith

end

end GaloisForLFunctions.RHTower
