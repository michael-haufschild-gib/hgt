import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceGreenEndpointTrace
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceGreenTortoiseJets

/-! Both original homogeneous radial modes and their exact tortoise Wronskian. -/
open Set Filter Topology
namespace RHTower.D4BMJointSource
open D4BMLaplaceRadial
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

def radialMode (outer : Bool) (w chi : ℂ) : ℝ → ℂ := if outer then normalizable w chi else horizon w chi
def radialModeFirst (outer : Bool) (w chi : ℂ) : ℝ → ℂ := if outer then normalizableFirst w chi else horizonFirst w chi
def radialModeSecond (outer : Bool) (w chi : ℂ) : ℝ → ℂ := if outer then normalizableSecond w chi else horizonSecond w chi

def tortoiseMode (outer : Bool) (w chi : ℂ) (t : ℝ) : ℂ := radialMode outer w chi (horizonCoordinate t)
def tortoiseModeFirst (outer : Bool) (w chi : ℂ) (t : ℝ) : ℂ :=
  (coordinateFirst t:ℂ)*radialModeFirst outer w chi (horizonCoordinate t)
def tortoiseModeSecond (outer : Bool) (w chi : ℂ) (t : ℝ) : ℂ :=
  (coordinateFirst t:ℂ)^2*radialModeSecond outer w chi (horizonCoordinate t)+
    (coordinateSecond t:ℂ)*radialModeFirst outer w chi (horizonCoordinate t)

private theorem radialMode_jets {w chi : ℂ} (h : Chamber w chi) (outer : Bool)
    {z : ℝ} (hz : z ∈ Ioo 0 1) :
    HasDerivAt (radialMode outer w chi) (radialModeFirst outer w chi z) z ∧
      HasDerivAt (radialModeFirst outer w chi) (radialModeSecond outer w chi z) z := by
  cases outer
  · exact horizon_derivatives h hz
  · exact normalizable_derivatives h hz

/-- Actual tortoise derivatives of both independent physical homogeneous solutions. -/
theorem tortoiseMode_hasDerivAt {w chi : ℂ} (h : Chamber w chi) (outer : Bool)
    (t : ℝ) (ht : t < 0) :
    HasDerivAt (tortoiseMode outer w chi) (tortoiseModeFirst outer w chi t) t ∧
      HasDerivAt (tortoiseModeFirst outer w chi) (tortoiseModeSecond outer w chi t) t := by
  have hd := radialMode_jets h outer (horizonCoordinate_interior t ht)
  have hc := horizonCoordinate_hasDerivAt t
  have hF := hd.1.scomp t hc
  have hF1 := hd.2.scomp t hc
  constructor
  · simpa only [tortoiseMode,tortoiseModeFirst,Function.comp_def,Complex.real_smul] using! hF
  · apply (((coordinateFirst_hasDerivAt t).ofReal_comp).mul hF1).congr_deriv
    dsimp only [tortoiseModeSecond,Function.comp_apply]
    simp only [Complex.real_smul]
    ring

/-- Both actual mode jets satisfy the original homogeneous tortoise equation. -/
theorem tortoiseMode_equation {w chi : ℂ} (h : Chamber w chi) (outer : Bool)
    (t : ℝ) (ht : t < 0) :
    tortoiseModeSecond outer w chi t =
      (w^2+(horizonCoordinate t:ℂ)*(1/4+chi^2))*tortoiseMode outer w chi t := by
  have hz := horizonCoordinate_interior t ht
  have he : D4BMPhysicalMaster.radialJet (Complex.I*w) chi (horizonCoordinate t)
      (radialMode outer w chi (horizonCoordinate t)) (radialModeFirst outer w chi (horizonCoordinate t))
        (radialModeSecond outer w chi (horizonCoordinate t))=0 := by
    cases outer
    · exact horizon_equation h hz
    · exact normalizable_equation h hz
  dsimp only [D4BMPhysicalMaster.radialJet] at he
  rw [mul_pow,Complex.I_sq] at he
  have hz0 : (horizonCoordinate t:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hz.1)
  field_simp [hz0] at he
  dsimp only [tortoiseMode,tortoiseModeSecond,coordinateFirst,coordinateSecond]
  have hu : (radialUnit t:ℂ)^2=1-(horizonCoordinate t:ℂ) := by
    simp only [horizonCoordinate,Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_pow]
    ring
  push_cast
  simp only [mul_pow,hu] at he ⊢
  linear_combination (1/8:ℂ)*he

/-- The exact tortoise Wronskian retains the original nonzero Gamma connection coefficient. -/
theorem tortoiseMode_wronskian {w chi : ℂ} (h : Chamber w chi) (t : ℝ) (ht : t < 0) :
    tortoiseMode false w chi t*tortoiseModeFirst true w chi t-
      tortoiseModeFirst false w chi t*tortoiseMode true w chi t = -connection w chi := by
  have hz := horizonCoordinate_interior t ht
  have he := wronskian_eq h hz
  have hs : Real.sqrt (1-horizonCoordinate t)=radialUnit t := by
    rw [horizonCoordinate,sub_sub_cancel,Real.sqrt_sq (radialUnit_bounds t ht).1.le]
  dsimp only [wronskian,integratingFactor] at he
  rw [power_half_eq_sqrt (sub_nonneg.mpr hz.2.le),hs] at he
  dsimp only [tortoiseMode,tortoiseModeFirst,radialMode,radialModeFirst,coordinateFirst]
  simp only [Bool.false_eq_true,if_false,if_true]
  push_cast
  linear_combination 2*he

end
end RHTower.D4BMJointSource
