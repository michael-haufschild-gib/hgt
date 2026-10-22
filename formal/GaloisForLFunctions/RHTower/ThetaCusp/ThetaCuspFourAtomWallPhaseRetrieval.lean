import GaloisForLFunctions.RHTower.EulerHedenmalmGammaStokesTransgression

/-!
# Fixed-aperture theta-wall phase-retrieval countermodel

Two finite Gaussian-theta sources have positive integer coefficients, first
coefficient one, and identical weighted wall autocorrelations at aperture
`a=1/6`, yet their Mellin transforms differ at an off-critical-line point in the strip.
The analytic wall-limit bridge is established on paper, not in this module.
Neither source is the completed Riemann theta source.
-/

open Complex MeasureTheory

namespace RHTower

noncomputable section

private def wallAmplitudeA (i : Fin 4) : ℚ :=
  if i.val = 0 then 1 else if i.val = 1 then 17 / 4 else if i.val = 2 then 5 else 1

private def wallAmplitudeB (i : Fin 4) : ℚ :=
  if i.val = 0 then 1 else if i.val = 1 then 5 else if i.val = 2 then 17 / 4 else 1

def sourceCoefficientA (i : Fin 4) : ℚ :=
  if i.val = 0 then 1 else if i.val = 1 then 68 else if i.val = 2 then 1280 else 4096

def sourceCoefficientB (i : Fin 4) : ℚ :=
  if i.val = 0 then 1 else if i.val = 1 then 80 else if i.val = 2 then 1088 else 4096

private theorem sourceCoefficientA_weighted (i : Fin 4) :
    sourceCoefficientA i / (16 : ℚ) ^ i.val = wallAmplitudeA i := by
  fin_cases i <;> norm_num [sourceCoefficientA, wallAmplitudeA]

private theorem sourceCoefficientB_weighted (i : Fin 4) :
    sourceCoefficientB i / (16 : ℚ) ^ i.val = wallAmplitudeB i := by
  fin_cases i <;> norm_num [sourceCoefficientB, wallAmplitudeB]

private theorem sourceCoefficientA_pos (i : Fin 4) : 0 < sourceCoefficientA i := by
  fin_cases i <;> norm_num [sourceCoefficientA]

private theorem sourceCoefficientB_pos (i : Fin 4) : 0 < sourceCoefficientB i := by
  fin_cases i <;> norm_num [sourceCoefficientB]

theorem fourAtomSourceCoefficients_pos (i : Fin 4) :
    0 < sourceCoefficientA i ∧ 0 < sourceCoefficientB i :=
  ⟨sourceCoefficientA_pos i, sourceCoefficientB_pos i⟩

theorem fourAtomSourceCoefficients_first :
    sourceCoefficientA 0 = 1 ∧ sourceCoefficientB 0 = 1 := by
  norm_num [sourceCoefficientA, sourceCoefficientB]

def finiteWallReadout (w : Fin 4 → ℚ) (r : ℚ) : ℚ :=
  ∑ i : Fin 4, ∑ j : Fin 4,
    if (64 : ℚ) ^ i.val / (64 : ℚ) ^ j.val = r then w i * w j else 0

private theorem finiteWallReadout_flip (r : ℚ) :
    finiteWallReadout wallAmplitudeA r = finiteWallReadout wallAmplitudeB r := by
  classical
  simp [finiteWallReadout, wallAmplitudeA, wallAmplitudeB, Fin.sum_univ_succ]
  ring_nf

theorem normalizedFourAtomWallReadout_eq (r : ℚ) :
    finiteWallReadout (fun i => sourceCoefficientA i / (16 : ℚ) ^ i.val) r =
      finiteWallReadout (fun i => sourceCoefficientB i / (16 : ℚ) ^ i.val) r := by
  simp only [sourceCoefficientA_weighted, sourceCoefficientB_weighted]
  exact finiteWallReadout_flip r

def wallPolyA (z : ℂ) : ℂ :=
  1 + (17 / 4 : ℂ) * z + 5 * z ^ 2 + z ^ 3

def wallPolyB (z : ℂ) : ℂ :=
  1 + 5 * z + (17 / 4 : ℂ) * z ^ 2 + z ^ 3

private theorem wallPolyA_factor (z : ℂ) :
    wallPolyA z = (1 + 2 * z) ^ 2 * (1 + z / 4) := by
  unfold wallPolyA
  ring

private theorem wallPolyB_factor (z : ℂ) :
    wallPolyB z = (2 + z) ^ 2 * (1 / 4 + z) := by
  unfold wallPolyB
  ring

private theorem wallPolyA_zero : wallPolyA (-4) = 0 := by
  rw [wallPolyA_factor]
  ring

private theorem wallPolyB_zero : wallPolyB (-2) = 0 := by
  rw [wallPolyB_factor]
  ring

private theorem cpow_posReal_pow (x : ℝ) (hx : 0 < x) (n : ℕ) (s : ℂ) :
    ((x ^ n : ℝ) : ℂ) ^ s = ((x : ℂ) ^ s) ^ n := by
  have hxn : 0 < x ^ n := pow_pos hx n
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hxn.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne')]
  rw [← Complex.ofReal_log (le_of_lt hxn),
    ← Complex.ofReal_log (le_of_lt hx), Real.log_pow]
  push_cast
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

private def fourAtomSeed (c : Fin 4 → ℂ) (t : ℝ) : ℂ :=
  c 0 • (thetaCuspSeed t : ℂ) +
    c 1 • (thetaCuspSeed (64 * t) : ℂ) +
    c 2 • (thetaCuspSeed ((64 : ℝ) ^ 2 * t) : ℂ) +
    c 3 • (thetaCuspSeed ((64 : ℝ) ^ 3 * t) : ℂ)

private theorem fourAtomSeed_mellin_factor (c : Fin 4 → ℂ) {s : ℂ} (hs : 0 < s.re) :
    mellin (fourAtomSeed c) s = archFactor s *
      (c 0 + c 1 * (64 : ℂ) ^ (-s) +
        c 2 * ((64 : ℂ) ^ (-s)) ^ 2 +
        c 3 * ((64 : ℂ) ^ (-s)) ^ 3) := by
  let f : ℝ → ℂ := fun t => (thetaCuspSeed t : ℂ)
  have hf : MellinConvergent f s := mellinConvergent_thetaCuspSeed hs
  have h64 : (0 : ℝ) < 64 := by norm_num
  have hf1 : MellinConvergent (fun t => f (64 * t)) s :=
    (MellinConvergent.comp_mul_left (f := f) (s := s) h64).2 hf
  have hf2 : MellinConvergent (fun t => f ((64 : ℝ) ^ 2 * t)) s :=
    (MellinConvergent.comp_mul_left (f := f) (s := s) (pow_pos h64 2)).2 hf
  have hf3 : MellinConvergent (fun t => f ((64 : ℝ) ^ 3 * t)) s :=
    (MellinConvergent.comp_mul_left (f := f) (s := s) (pow_pos h64 3)).2 hf
  have h0 := hasMellin_const_smul hf (c 0)
  have h1 := hasMellin_const_smul hf1 (c 1)
  have h2 := hasMellin_const_smul hf2 (c 2)
  have h3 := hasMellin_const_smul hf3 (c 3)
  have h01 := hasMellin_add h0.1 h1.1
  have h012 := hasMellin_add h01.1 h2.1
  have hsum := hasMellin_add h012.1 h3.1
  have hlinear : mellin (fourAtomSeed c) s =
      mellin (fun t => c 0 • f t) s +
        mellin (fun t => c 1 • f (64 * t)) s +
        mellin (fun t => c 2 • f ((64 : ℝ) ^ 2 * t)) s +
        mellin (fun t => c 3 • f ((64 : ℝ) ^ 3 * t)) s := by
    change mellin (fun t => c 0 • f t + c 1 • f (64 * t) +
      c 2 • f ((64 : ℝ) ^ 2 * t) + c 3 • f ((64 : ℝ) ^ 3 * t)) s = _
    rw [hsum.2, h012.2, h01.2]
  rw [hlinear, mellin_const_smul, mellin_const_smul, mellin_const_smul,
    mellin_const_smul, mellin_comp_mul_left f s h64,
    mellin_comp_mul_left f s (pow_pos h64 2),
    mellin_comp_mul_left f s (pow_pos h64 3),
    mellin_thetaCuspSeed_eq_archFactor hs]
  rw [cpow_posReal_pow 64 h64 2 (-s), cpow_posReal_pow 64 h64 3 (-s)]
  simp only [smul_eq_mul, Complex.ofReal_ofNat]
  ring

def fourAtomSourceA (t : ℝ) : ℂ :=
  fourAtomSeed (fun i => (sourceCoefficientA i : ℂ)) t

def fourAtomSourceB (t : ℝ) : ℂ :=
  fourAtomSeed (fun i => (sourceCoefficientB i : ℂ)) t

theorem fourAtomSourceA_mellin_factor {s : ℂ} (hs : 0 < s.re) :
    mellin fourAtomSourceA s =
      archFactor s * wallPolyA (16 * (64 : ℂ) ^ (-s)) := by
  change mellin (fourAtomSeed (fun i => (sourceCoefficientA i : ℂ))) s = _
  rw [fourAtomSeed_mellin_factor _ hs]
  simp [sourceCoefficientA, wallPolyA]
  ring <;> simp

theorem fourAtomSourceB_mellin_factor {s : ℂ} (hs : 0 < s.re) :
    mellin fourAtomSourceB s =
      archFactor s * wallPolyB (16 * (64 : ℂ) ^ (-s)) := by
  change mellin (fourAtomSeed (fun i => (sourceCoefficientB i : ℂ))) s = _
  rw [fourAtomSeed_mellin_factor _ hs]
  simp [sourceCoefficientB, wallPolyB]
  ring <;> simp

def fourAtomOffLinePoint : ℂ :=
  (Real.log 4 / Real.log 64 : ℝ) +
    ((Real.pi / Real.log 64 : ℝ) : ℂ) * Complex.I

private theorem log64_eq_three_log4 : Real.log (64 : ℝ) = 3 * Real.log 4 := by
  calc
    Real.log (64 : ℝ) = Real.log ((4 : ℝ) ^ 3) := by norm_num
    _ = 3 * Real.log 4 := Real.log_pow 4 3

private theorem fourAtomOffLinePoint_re : fourAtomOffLinePoint.re = 1 / 3 := by
  have hlog4 : Real.log (4 : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num))
  unfold fourAtomOffLinePoint
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, mul_one, add_zero]
  rw [log64_eq_three_log4]
  field_simp [hlog4]

private theorem fourAtomOffLinePoint_power :
    (64 : ℂ) ^ fourAtomOffLinePoint = -4 := by
  have hlog : Real.log (64 : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num))
  have hlogC : (Real.log (64 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlog
  rw [Complex.cpow_def_of_ne_zero (by norm_num : (64 : ℂ) ≠ 0)]
  have hlog64 : Complex.log (64 : ℂ) = (Real.log (64 : ℝ) : ℂ) :=
    (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 64)).symm
  rw [hlog64]
  have harg : (Real.log (64 : ℝ) : ℂ) * fourAtomOffLinePoint =
      (Real.log (4 : ℝ) : ℂ) + (Real.pi : ℂ) * Complex.I := by
    unfold fourAtomOffLinePoint
    push_cast
    field_simp [hlog, hlogC]
  rw [harg, Complex.exp_add, Complex.exp_pi_mul_I, ← Complex.ofReal_exp]
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 4)]
  norm_num

private theorem fourAtomOffLinePoint_weight :
    16 * (64 : ℂ) ^ (-fourAtomOffLinePoint) = -4 := by
  rw [Complex.cpow_neg, fourAtomOffLinePoint_power]
  norm_num

theorem fourAtomWallSameButMellinZeroDiffers :
    0 < fourAtomOffLinePoint.re ∧ fourAtomOffLinePoint.re < 1 ∧
      fourAtomOffLinePoint.re ≠ 1 / 2 ∧
      mellin fourAtomSourceA fourAtomOffLinePoint = 0 ∧
      mellin fourAtomSourceB fourAtomOffLinePoint ≠ 0 := by
  have hre := fourAtomOffLinePoint_re
  have hs : 0 < fourAtomOffLinePoint.re := by rw [hre]; norm_num
  have hs1 : fourAtomOffLinePoint.re < 1 := by rw [hre]; norm_num
  have hne : fourAtomOffLinePoint.re ≠ 1 / 2 := by rw [hre]; norm_num
  refine ⟨hs, hs1, hne, ?_, ?_⟩
  · rw [fourAtomSourceA_mellin_factor hs, fourAtomOffLinePoint_weight, wallPolyA_zero]
    ring
  · rw [fourAtomSourceB_mellin_factor hs, fourAtomOffLinePoint_weight]
    exact mul_ne_zero (archFactor_ne_zero_strip ⟨hs, hs1⟩)
      (by norm_num [wallPolyB])

end
end RHTower
