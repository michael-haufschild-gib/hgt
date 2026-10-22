import GaloisForLFunctions.RHTower.EulerHedenmalmGammaStokesTransgression

/-!
# Positive two-atom theta source with an off-critical Mellin zero

The literal first Gaussian-theta seed and its scale-two copy have positive
coefficients. Mellin scaling gives an exact Dirichlet-polynomial factor.
Choosing its coefficient to be `2^(3/4)` creates a zero at real part `3/4`
inside the critical strip, where the first-atom archimedean factor is
nonzero. This countermodel shows that positivity of coefficients or of
their leading wall autocorrelations, without modular completion, cannot
force critical-line zeros. It makes no assertion about the completed
Riemann theta source.
-/

open Complex MeasureTheory

namespace RHTower

noncomputable section

def thetaTwoAtomCounterWeight : ℝ := Real.exp ((3 / 4 : ℝ) * Real.log 2)

def thetaTwoAtomCounterPoint : ℂ :=
  (3 / 4 : ℝ) + ((Real.pi / Real.log 2 : ℝ) : ℂ) * Complex.I

def thetaTwoAtomCounterSeed (t : ℝ) : ℂ :=
  (thetaCuspSeed t : ℂ) + (thetaTwoAtomCounterWeight : ℂ) * (thetaCuspSeed (2 * t) : ℂ)

private theorem counterPoint_re : thetaTwoAtomCounterPoint.re = 3 / 4 := by
  unfold thetaTwoAtomCounterPoint
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, mul_one,
    add_zero]

theorem thetaTwoAtomCounterWeight_pos : 0 < thetaTwoAtomCounterWeight := by
  exact Real.exp_pos _

theorem thetaTwoAtomCounterSeed_mellin_factor {s : ℂ} (hs : 0 < s.re) :
    mellin thetaTwoAtomCounterSeed s =
      archFactor s * (1 + (thetaTwoAtomCounterWeight : ℂ) * (2 : ℂ) ^ (-s)) := by
  let f : ℝ → ℂ := fun t => (thetaCuspSeed t : ℂ)
  have hf : MellinConvergent f s := mellinConvergent_thetaCuspSeed hs
  have hf2 : MellinConvergent (fun t => f (2 * t)) s :=
    (MellinConvergent.comp_mul_left (f := f) (s := s)
      (by norm_num : (0 : ℝ) < 2)).2 hf
  have hsum := hasMellin_add hf (hf2.const_smul (thetaTwoAtomCounterWeight : ℂ))
  have hfactor : mellin thetaTwoAtomCounterSeed s =
      mellin f s + (thetaTwoAtomCounterWeight : ℂ) * mellin (fun t => f (2 * t)) s := by
    calc
      mellin thetaTwoAtomCounterSeed s =
          mellin (fun t => f t + (thetaTwoAtomCounterWeight : ℂ) • f (2 * t)) s := rfl
      _ = mellin f s + mellin (fun t => (thetaTwoAtomCounterWeight : ℂ) • f (2 * t)) s := hsum.2
      _ = mellin f s + (thetaTwoAtomCounterWeight : ℂ) • mellin (fun t => f (2 * t)) s := by
        rw [mellin_const_smul]
      _ = _ := by simp only [smul_eq_mul]
  rw [hfactor, mellin_comp_mul_left f s (by norm_num : (0 : ℝ) < 2),
    mellin_thetaCuspSeed_eq_archFactor hs]
  simp only [smul_eq_mul, Complex.ofReal_ofNat]
  ring

private theorem counterPoint_power :
    (2 : ℂ) ^ thetaTwoAtomCounterPoint = -(thetaTwoAtomCounterWeight : ℂ) := by
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hlogC : (Real.log 2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlog
  rw [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)]
  have hlog2 : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) := by
    exact (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
  rw [hlog2]
  have harg : (Real.log 2 : ℂ) * thetaTwoAtomCounterPoint =
      ((3 / 4 * Real.log 2 : ℝ) : ℂ) + (Real.pi : ℂ) * Complex.I := by
    unfold thetaTwoAtomCounterPoint
    push_cast
    field_simp [hlog, hlogC]
  rw [harg, Complex.exp_add, Complex.exp_pi_mul_I]
  rw [show ((3 / 4 * Real.log 2 : ℝ) : ℂ) =
      (((3 / 4 : ℝ) * Real.log 2 : ℝ) : ℂ) by rfl,
    ← Complex.ofReal_exp]
  unfold thetaTwoAtomCounterWeight
  ring

private theorem counterPoint_factor_zero :
    1 + (thetaTwoAtomCounterWeight : ℂ) * (2 : ℂ) ^ (-thetaTwoAtomCounterPoint) = 0 := by
  rw [Complex.cpow_neg, counterPoint_power]
  have hc : (thetaTwoAtomCounterWeight : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr thetaTwoAtomCounterWeight_pos.ne'
  field_simp [hc]
  ring

theorem thetaTwoAtomCounterSeed_mellin_offLine_zero :
    0 < thetaTwoAtomCounterPoint.re ∧ thetaTwoAtomCounterPoint.re < 1 ∧
      thetaTwoAtomCounterPoint.re ≠ 1 / 2 ∧
      mellin thetaTwoAtomCounterSeed thetaTwoAtomCounterPoint = 0 := by
  have hre := counterPoint_re
  have hs : 0 < thetaTwoAtomCounterPoint.re := by rw [hre]; norm_num
  refine ⟨hs, ?_, ?_, ?_⟩
  · rw [hre]; norm_num
  · rw [hre]; norm_num
  · rw [thetaTwoAtomCounterSeed_mellin_factor hs, counterPoint_factor_zero]
    ring

theorem thetaFirstAtom_mellin_nonzero_at_counterPoint :
    mellin (fun t : ℝ => (thetaCuspSeed t : ℂ)) thetaTwoAtomCounterPoint ≠ 0 := by
  have hre := counterPoint_re
  have hs : 0 < thetaTwoAtomCounterPoint.re := by rw [hre]; norm_num
  have hs1 : thetaTwoAtomCounterPoint.re < 1 := by rw [hre]; norm_num
  rw [mellin_thetaCuspSeed_eq_archFactor hs]
  exact archFactor_ne_zero_strip ⟨hs, hs1⟩

end

end RHTower
