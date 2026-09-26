import GaloisForLFunctions.RHTower.FZZParityAreaResponseDyadicClockBridge
import GaloisForLFunctions.RHTower.SalemFermiModeIntegral

/-!
# The literal FZZ parity source has non-passive modes on `Re s = 1`

The parity delay `B(t) − 2B(2t)` is the Fermi kernel, whose Mellin transform is
`Γ(s)(1 − 2^{1−s})ζ(s)` on `Re s > 0`.  Besides the zeta zeros of the open strip it vanishes at the
dyadic parity points `s_k = 1 + 2πik/log 2`, `k ≠ 0`, where the dyadic factor vanishes.

At these modes the dyadic clock has modulus `√2`, so the canonical-twist replica-area response is
`3/4 + (2 + 1/2)/8 = 17/16 > 1`.  Hence the statement "every mode of the literal parity source is
passive" is false.  Any FZZ-P producer must separate the Bose (zeta) modes from the dyadic parity
modes that the parity regularization creates; a law uniform over all modes of the literal Fermi
source cannot exist.
-/

open Complex

namespace RHTower

noncomputable section

/-- The dyadic parity points `1 + 2πik/log 2`. -/
def fzzDyadicParityMode (k : ℤ) : ℂ :=
  1 + ((2 * Real.pi * (k : ℝ) / Real.log 2 : ℝ) : ℂ) * I

theorem fzzDyadicParityMode_re (k : ℤ) : (fzzDyadicParityMode k).re = 1 := by
  unfold fzzDyadicParityMode
  rw [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

theorem fzzDyadicParityMode_ne_one {k : ℤ} (hk : k ≠ 0) : fzzDyadicParityMode k ≠ 1 := by
  intro h
  have him := congrArg Complex.im h
  simp only [fzzDyadicParityMode, Complex.add_im, Complex.one_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] at him
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have : 2 * Real.pi * (k : ℝ) / Real.log 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hkR) hlog.ne'
  apply this
  linarith

/-- The dyadic factor vanishes at every parity point. -/
theorem two_cpow_one_sub_fzzDyadicParityMode (k : ℤ) :
    (2 : ℂ) ^ (1 - fzzDyadicParityMode k) = 1 := by
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  rw [Complex.cpow_def_of_ne_zero two_ne_zero]
  have hlog2 : Complex.log 2 = (Real.log 2 : ℂ) := by
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_log (by norm_num)]
  rw [hlog2]
  have hlogC : (Real.log 2 : ℂ) ≠ 0 := by exact_mod_cast hlog
  have hexp : (Real.log 2 : ℂ) * (1 - fzzDyadicParityMode k) = ((-k : ℤ) : ℂ) * (2 * Real.pi * I) := by
    simp only [fzzDyadicParityMode]
    push_cast
    field_simp [hlogC]
    ring
  rw [hexp, Complex.exp_int_mul_two_pi_mul_I]

/-- **Parity modes are modes of the literal FZZ source.** -/
theorem fzzCigarParityMellin_fzzDyadicParityMode {k : ℤ} (hk : k ≠ 0) :
    fzzCigarParityMellin (fzzDyadicParityMode k) = 0 := by
  rw [fzzCigarParityMellin_eq_salemFermiMellin,
    mellin_salemFermiKernel_eq_closedForm (by rw [fzzDyadicParityMode_re]; norm_num)
      (fzzDyadicParityMode_ne_one hk),
    two_cpow_one_sub_fzzDyadicParityMode]
  ring

/-- At a parity mode the canonical-twist area response is `17/16`. -/
theorem fzzAreaResponse_fzzDyadicParityMode (k : ℤ) :
    fzzLinearReplicaAreaNormalizedResponse 1
        (fzzCigarParityMellinTorusTwist (fzzDyadicParityMode k)).im = 17 / 16 := by
  rw [fzzAreaResponse_mellinTwist_eq_dyadicClockOrbitAverage, norm_dyadicPrimeClock,
    norm_dyadicPrimeClock, lineReflect_re, fzzDyadicParityMode_re]
  have h1 : ((2 : ℝ) ^ ((1 : ℝ) - 1 / 2)) ^ 2 = 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have h2 : ((2 : ℝ) ^ ((1 : ℝ) - 1 - 1 / 2)) ^ 2 = 1 / 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [h1, h2]
  norm_num

/-- **Uniform source-mode passivity is false.**  Infinitely many modes of the literal FZZ parity
source (all nonzero `k`) have area response strictly above one. -/
theorem not_forall_fzzParityMode_areaPassive :
    ¬ ∀ s : ℂ, 0 < s.re → fzzCigarParityMellin s = 0 →
      fzzLinearReplicaAreaNormalizedResponse 1 (fzzCigarParityMellinTorusTwist s).im ≤ 1 := by
  intro h
  have hle := h (fzzDyadicParityMode 1) (by rw [fzzDyadicParityMode_re]; norm_num)
    (fzzCigarParityMellin_fzzDyadicParityMode one_ne_zero)
  rw [fzzAreaResponse_fzzDyadicParityMode] at hle
  norm_num at hle

end

end RHTower
