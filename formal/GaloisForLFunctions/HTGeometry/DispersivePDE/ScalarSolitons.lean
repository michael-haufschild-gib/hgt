import GaloisForLFunctions.HTGeometry.DispersivePDE.Equations
import GaloisForLFunctions.HTGeometry.DispersivePDE.Profiles
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Closed scalar solutions of dispersive equations

Exact KdV, potential-KdV, modified-KdV, Airy, Kawahara, KP-I/KP-II, and
Shrira--Pesenson solutions.  No theorem in this module assumes a PDE solution or regularity premise.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE

private theorem hasDerivAt_subLinear (a x t : ℝ) :
    HasDerivAt (fun s : ℝ => x - a * s) (-a) t := by
  have h := (hasDerivAt_const t x).sub ((hasDerivAt_id t).const_mul a)
  refine (h.congr_deriv (by simp)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => ?_)
  simp [id_eq]

private theorem hasDerivAt_addLinear (a x t : ℝ) :
    HasDerivAt (fun s : ℝ => x + a * s) a t := by
  have h := (hasDerivAt_const t x).add ((hasDerivAt_id t).const_mul a)
  refine (h.congr_deriv (by simp)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => ?_)
  simp [id_eq]

private theorem hasDerivAt_subConst (c x : ℝ) :
    HasDerivAt (fun y : ℝ => y - c) 1 x := by
  have h := (hasDerivAt_id x).sub (hasDerivAt_const x c)
  refine (h.congr_deriv (by simp)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => ?_)
  simp [id_eq]

private theorem hasDerivAt_addConst (c x : ℝ) :
    HasDerivAt (fun y : ℝ => y + c) 1 x := by
  have h := (hasDerivAt_id x).add (hasDerivAt_const x c)
  refine (h.congr_deriv (by simp)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => ?_)
  simp [id_eq]

private theorem hasDerivAt_cos_addConst (c x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.cos (y + c)) (-Real.sin (x + c)) x := by
  have h := ((hasDerivAt_id x).add_const c).cos
  apply (h.congr_deriv (by simp)).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun y => by simp [id_eq]

private theorem hasDerivAt_cos_constAdd (c x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.cos (c + y)) (-Real.sin (c + x)) x := by
  have h := ((hasDerivAt_const x c).add (hasDerivAt_id x)).cos
  apply (h.congr_deriv (by simp)).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun y => by simp [id_eq]

private theorem hasDerivAt_negSin_addConst (c x : ℝ) :
    HasDerivAt (fun y : ℝ => -Real.sin (y + c)) (-Real.cos (x + c)) x := by
  have h := ((hasDerivAt_id x).add_const c).sin.neg
  apply (h.congr_deriv (by simp)).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun y => by simp [id_eq]

private theorem hasDerivAt_negCos_addConst (c x : ℝ) :
    HasDerivAt (fun y : ℝ => -Real.cos (y + c)) (Real.sin (x + c)) x := by
  have h := ((hasDerivAt_id x).add_const c).cos.neg
  apply (h.congr_deriv (by simp)).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun y => by simp [id_eq]

private theorem hasDerivAt_sin_addConst (c x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.sin (y + c)) (Real.cos (x + c)) x := by
  have h := ((hasDerivAt_id x).add_const c).sin
  apply (h.congr_deriv (by simp)).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun y => by simp [id_eq]

/-! ## KdV soliton -/

noncomputable def kdvSoliton (t x : ℝ) : ℝ := 2 * solitonQ (x - 4 * t)

noncomputable def kdvSolitonJet : RealEvolutionJet3 where
  u := kdvSoliton
  ut := fun t x => 2 * (solitonQ1 (x - 4 * t) * (-4))
  ux := fun t x => 2 * solitonQ1 (x - 4 * t)
  uxx := fun t x => 2 * solitonQ2 (x - 4 * t)
  uxxx := fun t x => 2 * solitonQ3 (x - 4 * t)
  hasDerivAt_time := by
    intro t x
    have hz := hasDerivAt_subLinear 4 x t
    have h := ((hasDerivAt_solitonQ (x - 4 * t)).comp t hz).const_mul (2 : ℝ)
    change HasDerivAt (fun s : ℝ => 2 * solitonQ (x - 4 * s))
      (2 * (solitonQ1 (x - 4 * t) * -4)) t
    simpa only [Function.comp_apply] using h
  hasDerivAt_space := by
    intro t x
    have hz := hasDerivAt_subConst (4 * t) x
    have h := ((hasDerivAt_solitonQ (x - 4 * t)).comp x hz).const_mul (2 : ℝ)
    change HasDerivAt (fun y : ℝ => 2 * solitonQ (y - 4 * t))
      (2 * solitonQ1 (x - 4 * t)) x
    simpa only [Function.comp_apply, mul_one] using h
  hasDerivAt_space_one := by
    intro t x
    have hz := hasDerivAt_subConst (4 * t) x
    have h := ((hasDerivAt_solitonQ1 (x - 4 * t)).comp x hz).const_mul (2 : ℝ)
    simpa [Function.comp_def] using h
  hasDerivAt_space_two := by
    intro t x
    have hz := hasDerivAt_subConst (4 * t) x
    have h := ((hasDerivAt_solitonQ2 (x - 4 * t)).comp x hz).const_mul (2 : ℝ)
    simpa [Function.comp_def] using h

theorem kdvSoliton_solves : SolvesKdV kdvSolitonJet := by
  intro t x
  simp only [kdvSolitonJet, kdvSoliton]
  unfold solitonQ1 solitonQ3
  ring

theorem kdvSoliton_traveling : IsTravelingWave 4 kdvSoliton := by
  intro t x
  simp [kdvSoliton]

/-! ## Potential KdV pulse -/

noncomputable def potentialKdVPulse (t x : ℝ) : ℝ := 2 * solitonT (x - 4 * t)

noncomputable def potentialKdVPulseJet : RealEvolutionJet3 where
  u := potentialKdVPulse
  ut := fun t x => 2 * (solitonQ (x - 4 * t) * (-4))
  ux := fun t x => 2 * solitonQ (x - 4 * t)
  uxx := fun t x => 2 * solitonQ1 (x - 4 * t)
  uxxx := fun t x => 2 * solitonQ2 (x - 4 * t)
  hasDerivAt_time := by
    intro t x
    have hz := hasDerivAt_subLinear 4 x t
    have h := ((hasDerivAt_solitonT (x - 4 * t)).comp t hz).const_mul (2 : ℝ)
    change HasDerivAt (fun s : ℝ => 2 * solitonT (x - 4 * s))
      (2 * (solitonQ (x - 4 * t) * -4)) t
    simpa only [Function.comp_apply] using h
  hasDerivAt_space := by
    intro t x
    have hz := hasDerivAt_subConst (4 * t) x
    have h := ((hasDerivAt_solitonT (x - 4 * t)).comp x hz).const_mul (2 : ℝ)
    change HasDerivAt (fun y : ℝ => 2 * solitonT (y - 4 * t))
      (2 * solitonQ (x - 4 * t)) x
    simpa only [Function.comp_apply, mul_one] using h
  hasDerivAt_space_one := by
    intro t x
    have hz := hasDerivAt_subConst (4 * t) x
    simpa [Function.comp_def] using
      ((hasDerivAt_solitonQ (x - 4 * t)).comp x hz).const_mul (2 : ℝ)
  hasDerivAt_space_two := by
    intro t x
    have hz := hasDerivAt_subConst (4 * t) x
    simpa [Function.comp_def] using
      ((hasDerivAt_solitonQ1 (x - 4 * t)).comp x hz).const_mul (2 : ℝ)

theorem potentialKdVPulse_solves : SolvesPotentialKdV potentialKdVPulseJet := by
  intro t x
  simp only [potentialKdVPulseJet]
  unfold solitonQ2
  ring

theorem potentialKdVPulse_traveling : IsTravelingWave 4 potentialKdVPulse := by
  intro t x
  simp [potentialKdVPulse]

/-! ## Modified KdV kink -/

noncomputable def modifiedKdVKink (t x : ℝ) : ℝ := solitonT (x + 2 * t)

noncomputable def modifiedKdVKinkJet : RealEvolutionJet3 where
  u := modifiedKdVKink
  ut := fun t x => solitonQ (x + 2 * t) * 2
  ux := fun t x => solitonQ (x + 2 * t)
  uxx := fun t x => solitonQ1 (x + 2 * t)
  uxxx := fun t x => solitonQ2 (x + 2 * t)
  hasDerivAt_time := by
    intro t x
    have hz := hasDerivAt_addLinear 2 x t
    change HasDerivAt (fun s : ℝ => solitonT (x + 2 * s))
      (solitonQ (x + 2 * t) * 2) t
    simpa only [Function.comp_def] using (hasDerivAt_solitonT (x + 2 * t)).comp t hz
  hasDerivAt_space := by
    intro t x
    have hz := hasDerivAt_addConst (2 * t) x
    change HasDerivAt (fun y : ℝ => solitonT (y + 2 * t)) (solitonQ (x + 2 * t)) x
    simpa only [Function.comp_def, mul_one] using (hasDerivAt_solitonT (x + 2 * t)).comp x hz
  hasDerivAt_space_one := by
    intro t x
    have hz := hasDerivAt_addConst (2 * t) x
    simpa [Function.comp_def] using (hasDerivAt_solitonQ (x + 2 * t)).comp x hz
  hasDerivAt_space_two := by
    intro t x
    have hz := hasDerivAt_addConst (2 * t) x
    simpa [Function.comp_def] using (hasDerivAt_solitonQ1 (x + 2 * t)).comp x hz

theorem modifiedKdVKink_solves : SolvesModifiedKdV modifiedKdVKinkJet := by
  intro t x
  simp only [modifiedKdVKinkJet, modifiedKdVKink]
  simp only [solitonQ2, solitonQ, solitonT]
  ring

theorem modifiedKdVKink_traveling : IsTravelingWave (-2) modifiedKdVKink := by
  intro t x
  simp [modifiedKdVKink]

/-! ## Linear Airy wave -/

noncomputable def airyWave (t x : ℝ) : ℝ := Real.cos (x + t)

noncomputable def airyWaveJet : RealEvolutionJet3 where
  u := airyWave
  ut := fun t x => -Real.sin (x + t)
  ux := fun t x => -Real.sin (x + t)
  uxx := fun t x => -Real.cos (x + t)
  uxxx := fun t x => Real.sin (x + t)
  hasDerivAt_time := by
    intro t x
    exact hasDerivAt_cos_constAdd x t
  hasDerivAt_space := by
    intro t x
    exact hasDerivAt_cos_addConst t x
  hasDerivAt_space_one := by
    intro t x
    exact hasDerivAt_negSin_addConst t x
  hasDerivAt_space_two := by
    intro t x
    exact hasDerivAt_negCos_addConst t x

theorem airyWave_solves : SolvesAiry airyWaveJet := by
  intro t x
  simp [airyWaveJet]

/-! ## Kawahara soliton and linear fifth-order wave -/

noncomputable def kawaharaSoliton (t x : ℝ) : ℝ := 1680 * solitonR (x - 576 * t)

noncomputable def kawaharaSolitonJet : RealEvolutionJet5 where
  toRealEvolutionJet3 := {
    u := kawaharaSoliton
    ut := fun t x => 1680 * (solitonR1 (x - 576 * t) * (-576))
    ux := fun t x => 1680 * solitonR1 (x - 576 * t)
    uxx := fun t x => 1680 * solitonR2 (x - 576 * t)
    uxxx := fun t x => 1680 * solitonR3 (x - 576 * t)
    hasDerivAt_time := by
      intro t x
      have hz := hasDerivAt_subLinear 576 x t
      have h := ((hasDerivAt_solitonR (x - 576 * t)).comp t hz).const_mul (1680 : ℝ)
      change HasDerivAt (fun s : ℝ => 1680 * solitonR (x - 576 * s))
        (1680 * (solitonR1 (x - 576 * t) * -576)) t
      simpa only [Function.comp_apply] using h
    hasDerivAt_space := by
      intro t x
      have hz := hasDerivAt_subConst (576 * t) x
      have h := ((hasDerivAt_solitonR (x - 576 * t)).comp x hz).const_mul (1680 : ℝ)
      change HasDerivAt (fun y : ℝ => 1680 * solitonR (y - 576 * t))
        (1680 * solitonR1 (x - 576 * t)) x
      simpa only [Function.comp_apply, mul_one] using h
    hasDerivAt_space_one := by
      intro t x
      have hz := hasDerivAt_subConst (576 * t) x
      simpa [Function.comp_def] using
        ((hasDerivAt_solitonR1 (x - 576 * t)).comp x hz).const_mul (1680 : ℝ)
    hasDerivAt_space_two := by
      intro t x
      have hz := hasDerivAt_subConst (576 * t) x
      simpa [Function.comp_def] using
        ((hasDerivAt_solitonR2 (x - 576 * t)).comp x hz).const_mul (1680 : ℝ)
  }
  uxxxx := fun t x => 1680 * solitonR4 (x - 576 * t)
  uxxxxx := fun t x => 1680 * solitonR5 (x - 576 * t)
  hasDerivAt_space_three := by
    intro t x
    have hz := hasDerivAt_subConst (576 * t) x
    simpa [Function.comp_def] using
      ((hasDerivAt_solitonR3 (x - 576 * t)).comp x hz).const_mul (1680 : ℝ)
  hasDerivAt_space_four := by
    intro t x
    have hz := hasDerivAt_subConst (576 * t) x
    simpa [Function.comp_def] using
      ((hasDerivAt_solitonR4 (x - 576 * t)).comp x hz).const_mul (1680 : ℝ)

theorem kawaharaSoliton_solves : SolvesScaledKawahara kawaharaSolitonJet := by
  intro t x
  simp only [kawaharaSolitonJet, kawaharaSoliton]
  unfold solitonR solitonR1 solitonR3 solitonR5
  ring

theorem kawaharaSoliton_traveling : IsTravelingWave 576 kawaharaSoliton := by
  intro t x
  simp [kawaharaSoliton]

noncomputable def kawaharaLinearWave (t x : ℝ) : ℝ := Real.cos (x + 2 * t)

noncomputable def kawaharaLinearWaveJet : RealEvolutionJet5 where
  toRealEvolutionJet3 := {
    u := kawaharaLinearWave
    ut := fun t x => -Real.sin (x + 2 * t) * 2
    ux := fun t x => -Real.sin (x + 2 * t)
    uxx := fun t x => -Real.cos (x + 2 * t)
    uxxx := fun t x => Real.sin (x + 2 * t)
    hasDerivAt_time := by
      intro t x
      have hz := hasDerivAt_addLinear 2 x t
      change HasDerivAt (fun s : ℝ => Real.cos (x + 2 * s))
        (-Real.sin (x + 2 * t) * 2) t
      exact hz.cos
    hasDerivAt_space := by
      intro t x
      exact hasDerivAt_cos_addConst (2 * t) x
    hasDerivAt_space_one := by
      intro t x
      exact hasDerivAt_negSin_addConst (2 * t) x
    hasDerivAt_space_two := by
      intro t x
      exact hasDerivAt_negCos_addConst (2 * t) x
  }
  uxxxx := fun t x => Real.cos (x + 2 * t)
  uxxxxx := fun t x => -Real.sin (x + 2 * t)
  hasDerivAt_space_three := by
    intro t x
    exact hasDerivAt_sin_addConst (2 * t) x
  hasDerivAt_space_four := by
    intro t x
    exact hasDerivAt_cos_addConst (2 * t) x

theorem kawaharaLinearWave_solves : SolvesLinearKawahara kawaharaLinearWaveJet := by
  intro t x
  simp [kawaharaLinearWaveJet]
  ring

/-! ## KP line soliton -/

noncomputable def kpLineSoliton (t x _y : ℝ) : ℝ := kdvSoliton t x

noncomputable def kpLineSolitonJet : RealEvolutionJetKP where
  u := kpLineSoliton
  ut := fun t x _ => 2 * (solitonQ1 (x - 4 * t) * (-4))
  ux := fun t x _ => 2 * solitonQ1 (x - 4 * t)
  uxx := fun t x _ => 2 * solitonQ2 (x - 4 * t)
  uxxx := fun t x _ => 2 * solitonQ3 (x - 4 * t)
  uxxxx := fun t x _ => 2 * solitonQ4 (x - 4 * t)
  utx := fun t x _ => 2 * (solitonQ2 (x - 4 * t) * (-4))
  uy := fun _ _ _ => 0
  uyy := fun _ _ _ => 0
  hasDerivAt_time := by
    intro t x y
    simpa [kpLineSoliton, kdvSolitonJet] using kdvSolitonJet.hasDerivAt_time t x
  hasDerivAt_space := by
    intro t x y
    simpa [kpLineSoliton, kdvSolitonJet] using kdvSolitonJet.hasDerivAt_space t x
  hasDerivAt_space_one := by
    intro t x y
    simpa [kdvSolitonJet] using kdvSolitonJet.hasDerivAt_space_one t x
  hasDerivAt_space_two := by
    intro t x y
    simpa [kdvSolitonJet] using kdvSolitonJet.hasDerivAt_space_two t x
  hasDerivAt_space_three := by
    intro t x y
    have hz := hasDerivAt_subConst (4 * t) x
    simpa [Function.comp_def] using
      ((hasDerivAt_solitonQ3 (x - 4 * t)).comp x hz).const_mul (2 : ℝ)
  hasDerivAt_time_space := by
    intro t x y
    have hz := hasDerivAt_subConst (4 * t) x
    simpa [Function.comp_def] using
      (((hasDerivAt_solitonQ1 (x - 4 * t)).comp x hz).mul_const (-4 : ℝ)).const_mul (2 : ℝ)
  hasDerivAt_transverse := by
    intro t x y
    exact hasDerivAt_const y (kdvSoliton t x)
  hasDerivAt_transverse_one := by
    intro t x y
    exact hasDerivAt_const y 0

theorem kpLineSoliton_solves_KPI : SolvesKP (-1) kpLineSolitonJet := by
  intro t x y
  simp only [kpLineSolitonJet, kpLineSoliton, kdvSoliton]
  simp only [solitonQ4, solitonQ2, solitonQ1, solitonQ, solitonT]
  ring

theorem kpLineSoliton_solves_KPII : SolvesKP 1 kpLineSolitonJet := by
  intro t x y
  simp only [kpLineSolitonJet, kpLineSoliton, kdvSoliton]
  simp only [solitonQ4, solitonQ2, solitonQ1, solitonQ, solitonT]
  ring

theorem kpLineSoliton_isLineWave : IsLineWave kpLineSoliton := by
  intro t x y
  rfl

/-! ## Shrira--Pesenson neutral tilt mode -/

noncomputable def shriraPesensonTilt (T Y : ℝ) : ℝ := T + Y

noncomputable def shriraPesensonTiltJet : ShriraPesensonJet where
  s := shriraPesensonTilt
  sT := fun _ _ => 1
  sTT := fun _ _ => 0
  sY := fun _ _ => 1
  sYY := fun _ _ => 0
  sYT := fun _ _ => 0
  sTY := fun _ _ => 0
  sTYY := fun _ _ => 0
  hasDerivAt_time := by
    intro T Y
    simpa [shriraPesensonTilt] using (hasDerivAt_id T).add_const Y
  hasDerivAt_time_one := by
    intro T Y
    exact hasDerivAt_const T 1
  hasDerivAt_transverse := by
    intro T Y
    change HasDerivAt (fun y : ℝ => T + y) 1 Y
    exact (hasDerivAt_id Y).const_add T
  hasDerivAt_transverse_one := by
    intro T Y
    exact hasDerivAt_const Y 1
  hasDerivAt_transverse_time := by
    intro T Y
    exact hasDerivAt_const T 1
  hasDerivAt_time_transverse := by
    intro T Y
    exact hasDerivAt_const Y 1
  hasDerivAt_time_transverse_one := by
    intro T Y
    exact hasDerivAt_const Y 0
  mixed_eq := by
    intro T Y
    rfl

theorem shriraPesensonTilt_solves :
    SolvesShriraPesenson 1 1 1 1 1 shriraPesensonTiltJet := by
  intro T Y
  simp [shriraPesensonTiltJet]

theorem shriraPesensonTilt_solves_all (α β γ₁ γ₂ ε : ℝ) :
    SolvesShriraPesenson α β γ₁ γ₂ ε shriraPesensonTiltJet := by
  intro T Y
  simp [shriraPesensonTiltJet]

/-! ## Closed profile identities and Miura images -/

theorem kdvSoliton_peak (t : ℝ) : kdvSoliton t (4 * t) = 2 := by
  simp [kdvSoliton, solitonQ, solitonT]

theorem kawaharaSoliton_peak (t : ℝ) : kawaharaSoliton t (576 * t) = 1680 := by
  simp [kawaharaSoliton, solitonR, solitonQ, solitonT]

theorem modifiedKdVKink_miura_plus (t x : ℝ) :
    modifiedKdVKinkJet.ux t x + modifiedKdVKink t x ^ 2 = 1 := by
  simp [modifiedKdVKinkJet, modifiedKdVKink, solitonQ]

theorem modifiedKdVKink_miura_minus (t x : ℝ) :
    modifiedKdVKink t x ^ 2 - modifiedKdVKinkJet.ux t x =
      1 - 2 * solitonQ (x + 2 * t) := by
  simp [modifiedKdVKinkJet, modifiedKdVKink, solitonQ]
  ring

end GaloisForLFunctions.HTGeometry.DispersivePDE
