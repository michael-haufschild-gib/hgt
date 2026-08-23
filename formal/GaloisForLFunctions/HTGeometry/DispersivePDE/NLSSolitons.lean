import GaloisForLFunctions.HTGeometry.DispersivePDE.Equations
import GaloisForLFunctions.HTGeometry.DispersivePDE.Profiles
import GaloisForLFunctions.HTGeometry.FDNLS.Symmetries

/-!
# Closed nonlinear Schrödinger solitons

Bright, dark, and plane-wave solutions, reusing the exact FDNLS phase already present in corpus.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE

private theorem hasDerivAt_constAddOne (c x : ℝ) :
    HasDerivAt (fun y : ℝ => c + y) 1 x := by
  have h := (hasDerivAt_const x c).add (hasDerivAt_id x)
  apply (h.congr_deriv (by simp)).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun y => by simp [id_eq]

private theorem hasDerivAt_addConstOne (c x : ℝ) :
    HasDerivAt (fun y : ℝ => y + c) 1 x := by
  have h := (hasDerivAt_id x).add_const c
  apply h.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun y => by simp [id_eq]

/-! ## The `sech` amplitude -/

noncomputable def solitonA (x : ℝ) : ℝ := 1 / Real.cosh x

noncomputable def solitonA1 (x : ℝ) : ℝ := -(solitonT x * solitonA x)

noncomputable def solitonA2 (x : ℝ) : ℝ := solitonA x - 2 * solitonA x ^ 3

theorem solitonA_pos (x : ℝ) : 0 < solitonA x := by
  exact one_div_pos.mpr (Real.cosh_pos x)

theorem solitonA_sq (x : ℝ) : solitonA x ^ 2 = solitonQ x := by
  rw [solitonQ_eq_inv_cosh_sq]
  unfold solitonA
  ring

theorem hasDerivAt_solitonA (x : ℝ) : HasDerivAt solitonA (solitonA1 x) x := by
  have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  have h := (hasDerivAt_const x (1 : ℝ)).div (Real.hasDerivAt_cosh x) hc
  change HasDerivAt (fun y : ℝ => 1 / Real.cosh y) (solitonA1 x) x
  apply h.congr_deriv
  unfold solitonA1 solitonA solitonT
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp
  ring

theorem hasDerivAt_solitonA1 (x : ℝ) : HasDerivAt solitonA1 (solitonA2 x) x := by
  have hT := hasDerivAt_solitonT x
  have hA := hasDerivAt_solitonA x
  have h := (hT.mul hA).neg
  apply (h.congr_deriv ?_).congr_of_eventuallyEq
  · filter_upwards with y
    simp [solitonA1]
  · have hunit : solitonT x ^ 2 + solitonA x ^ 2 = 1 := by
      rw [solitonA_sq]
      simp [solitonQ]
    have hsq := solitonA_sq x
    simp [solitonA1, solitonA2]
    linear_combination solitonA x * hunit + solitonA x * hsq

/-! ## Focusing bright soliton -/

noncomputable def brightPhase (t : ℝ) : ℂ :=
  GaloisForLFunctions.HTGeometry.FDNLS.staggerPhase (-1) t

theorem hasDerivAt_brightPhase (t : ℝ) :
    HasDerivAt brightPhase (brightPhase t * Complex.I) t := by
  change HasDerivAt (GaloisForLFunctions.HTGeometry.FDNLS.staggerPhase (-1))
    (GaloisForLFunctions.HTGeometry.FDNLS.staggerPhase (-1) t * Complex.I) t
  simpa using GaloisForLFunctions.HTGeometry.FDNLS.hasDerivAt_staggerPhase (-1) t

theorem norm_brightPhase (t : ℝ) : ‖brightPhase t‖ = 1 := by
  exact GaloisForLFunctions.HTGeometry.FDNLS.norm_staggerPhase (-1) t

noncomputable def nlsBrightSoliton (t x : ℝ) : ℂ := (solitonA x : ℂ) * brightPhase t

noncomputable def nlsBrightSolitonJet : ComplexEvolutionJet2 where
  u := nlsBrightSoliton
  ut := fun t x => (solitonA x : ℂ) * (brightPhase t * Complex.I)
  ux := fun t x => (solitonA1 x : ℂ) * brightPhase t
  uxx := fun t x => (solitonA2 x : ℂ) * brightPhase t
  hasDerivAt_time := by
    intro t x
    change HasDerivAt (fun s : ℝ => (solitonA x : ℂ) * brightPhase s)
      ((solitonA x : ℂ) * (brightPhase t * Complex.I)) t
    exact (hasDerivAt_brightPhase t).const_mul (solitonA x : ℂ)
  hasDerivAt_space := by
    intro t x
    change HasDerivAt (fun y : ℝ => (solitonA y : ℂ) * brightPhase t)
      ((solitonA1 x : ℂ) * brightPhase t) x
    exact (hasDerivAt_solitonA x).ofReal_comp.mul_const (brightPhase t)
  hasDerivAt_space_one := by
    intro t x
    change HasDerivAt (fun y : ℝ => (solitonA1 y : ℂ) * brightPhase t)
      ((solitonA2 x : ℂ) * brightPhase t) x
    exact (hasDerivAt_solitonA1 x).ofReal_comp.mul_const (brightPhase t)

theorem norm_nlsBrightSoliton (t x : ℝ) : ‖nlsBrightSoliton t x‖ = solitonA x := by
  rw [nlsBrightSoliton, norm_mul, norm_brightPhase, mul_one]
  simp [abs_of_pos (solitonA_pos x)]

theorem nlsBrightSoliton_solves : SolvesFocusingNLS nlsBrightSolitonJet := by
  intro t x
  simp only [nlsBrightSolitonJet, nlsBrightSoliton]
  rw [show ‖(solitonA x : ℂ) * brightPhase t‖ = solitonA x by
    simpa [nlsBrightSoliton] using norm_nlsBrightSoliton t x]
  unfold solitonA2
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-! ## Defocusing dark soliton -/

noncomputable def darkPhase (t : ℝ) : ℂ :=
  GaloisForLFunctions.HTGeometry.FDNLS.staggerPhase 2 t

theorem hasDerivAt_darkPhase (t : ℝ) :
    HasDerivAt darkPhase (darkPhase t * (-(Complex.I * 2))) t := by
  exact GaloisForLFunctions.HTGeometry.FDNLS.hasDerivAt_staggerPhase 2 t

theorem norm_darkPhase (t : ℝ) : ‖darkPhase t‖ = 1 := by
  exact GaloisForLFunctions.HTGeometry.FDNLS.norm_staggerPhase 2 t

noncomputable def nlsDarkSoliton (t x : ℝ) : ℂ := (solitonT x : ℂ) * darkPhase t

noncomputable def nlsDarkSolitonJet : ComplexEvolutionJet2 where
  u := nlsDarkSoliton
  ut := fun t x => (solitonT x : ℂ) * (darkPhase t * (-(Complex.I * 2)))
  ux := fun t x => (solitonQ x : ℂ) * darkPhase t
  uxx := fun t x => (solitonQ1 x : ℂ) * darkPhase t
  hasDerivAt_time := by
    intro t x
    change HasDerivAt (fun s : ℝ => (solitonT x : ℂ) * darkPhase s)
      ((solitonT x : ℂ) * (darkPhase t * (-(Complex.I * 2)))) t
    exact (hasDerivAt_darkPhase t).const_mul (solitonT x : ℂ)
  hasDerivAt_space := by
    intro t x
    change HasDerivAt (fun y : ℝ => (solitonT y : ℂ) * darkPhase t)
      ((solitonQ x : ℂ) * darkPhase t) x
    exact (hasDerivAt_solitonT x).ofReal_comp.mul_const (darkPhase t)
  hasDerivAt_space_one := by
    intro t x
    change HasDerivAt (fun y : ℝ => (solitonQ y : ℂ) * darkPhase t)
      ((solitonQ1 x : ℂ) * darkPhase t) x
    exact (hasDerivAt_solitonQ x).ofReal_comp.mul_const (darkPhase t)

theorem norm_nlsDarkSoliton_sq (t x : ℝ) : ‖nlsDarkSoliton t x‖ ^ 2 = solitonT x ^ 2 := by
  rw [nlsDarkSoliton, norm_mul, norm_darkPhase, mul_one]
  simp

theorem nlsDarkSoliton_solves : SolvesDefocusingNLS nlsDarkSolitonJet := by
  intro t x
  simp only [nlsDarkSolitonJet, nlsDarkSoliton]
  rw [show ‖(solitonT x : ℂ) * darkPhase t‖ ^ 2 = solitonT x ^ 2 by
    simpa [nlsDarkSoliton] using norm_nlsDarkSoliton_sq t x]
  simp only [solitonQ1]
  have hunit : solitonQ x + solitonT x ^ 2 = 1 := by simp [solitonQ]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring_nf
  have hunitC : (solitonQ x : ℂ) + (solitonT x : ℂ) ^ 2 = 1 := by
    exact_mod_cast hunit
  linear_combination -(2 * (solitonT x : ℂ) * darkPhase t) * hunitC

/-! ## Unit focusing plane wave -/

noncomputable def nlsPlaneWave (t x : ℝ) : ℂ := brightPhase (x + t)

noncomputable def nlsPlaneWaveJet : ComplexEvolutionJet2 where
  u := nlsPlaneWave
  ut := fun t x => brightPhase (x + t) * Complex.I
  ux := fun t x => brightPhase (x + t) * Complex.I
  uxx := fun t x => (brightPhase (x + t) * Complex.I) * Complex.I
  hasDerivAt_time := by
    intro t x
    have hz := hasDerivAt_constAddOne x t
    change HasDerivAt (fun s : ℝ => brightPhase (x + s)) (brightPhase (x + t) * Complex.I) t
    simpa [Function.comp_def] using
      (hasDerivAt_brightPhase (x + t)).hasFDerivAt.comp_hasDerivAt t hz
  hasDerivAt_space := by
    intro t x
    have hz := hasDerivAt_addConstOne t x
    change HasDerivAt (fun y : ℝ => brightPhase (y + t)) (brightPhase (x + t) * Complex.I) x
    simpa [Function.comp_def] using
      (hasDerivAt_brightPhase (x + t)).hasFDerivAt.comp_hasDerivAt x hz
  hasDerivAt_space_one := by
    intro t x
    have hz := hasDerivAt_addConstOne t x
    have hphase := (hasDerivAt_brightPhase (x + t)).hasFDerivAt.comp_hasDerivAt x hz
    have h := hphase.mul_const Complex.I
    simpa [Function.comp_def] using h

theorem norm_nlsPlaneWave (t x : ℝ) : ‖nlsPlaneWave t x‖ = 1 := by
  exact norm_brightPhase (x + t)

theorem nlsPlaneWave_solves : SolvesFocusingNLS nlsPlaneWaveJet := by
  intro t x
  simp only [nlsPlaneWaveJet, nlsPlaneWave]
  rw [show ‖brightPhase (x + t)‖ = 1 by exact norm_brightPhase (x + t)]
  norm_num
  ring_nf
  rw [Complex.I_sq]
  ring

end GaloisForLFunctions.HTGeometry.DispersivePDE
