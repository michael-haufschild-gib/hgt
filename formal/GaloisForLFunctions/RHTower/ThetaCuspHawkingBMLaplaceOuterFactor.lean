import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceGaussFactors
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplacePowerJets

/-! The actual outer square-root branch in the independent-frequency chamber. -/

open Complex Set Filter Topology
namespace RHTower.D4BMLaplaceRadial
noncomputable section

attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

def outerFactor (w chi : ℂ) (z : ℝ) : ℂ :=
  power (1/2) (1-z)*gaussFactor w chi true (1-z)
def outerFirst (w chi : ℂ) (z : ℝ) : ℂ :=
  -powerFirst (1/2) (1-z)*gaussFactor w chi true (1-z)-power (1/2) (1-z)*gaussFirst w chi true (1-z)
def outerSecond (w chi : ℂ) (z : ℝ) : ℂ :=
  powerSecond (1/2) (1-z)*gaussFactor w chi true (1-z)+
    2*powerFirst (1/2) (1-z)*gaussFirst w chi true (1-z)+
    power (1/2) (1-z)*gaussSecond w chi true (1-z)

/-- The outer branch's two jets are actual derivatives, including the
square-root factor and the reversal of the radial coordinate. -/
theorem outerFactor_derivatives {w chi : ℂ} (h : Chamber w chi) {z : ℝ} (hz : z ∈ Ioo 0 1) :
    HasDerivAt (outerFactor w chi) (outerFirst w chi z) z ∧
    HasDerivAt (outerFirst w chi) (outerSecond w chi z) z := by
  have hx : 0 < 1-z := sub_pos.mpr hz.2
  have hnorm : ‖((1-z:ℝ):ℂ)‖ₑ < 1 := enorm_ofReal_lt_one hx (by linarith [hz.1])
  have hd := (hasDerivAt_id z).const_sub (1:ℝ)
  obtain ⟨hp,hp1⟩ := power_derivatives (1/2) hx
  obtain ⟨hF,hF1⟩ := gaussFactor_derivatives h true hnorm
  have hP := hp.scomp z hd
  have hP1 := hp1.scomp z hd
  have hG := hF.comp_ofReal.scomp z hd
  have hG1 := hF1.comp_ofReal.scomp z hd
  simp only [neg_smul,one_smul] at hP hP1 hG hG1
  push_cast at hG hG1
  constructor
  · convert! hP.mul hG using 1
    · funext t
      simp [outerFactor,Function.comp_def]
    · dsimp [outerFirst]
      push_cast
      ring
  · convert! (hP1.neg.mul hG).sub (hP.mul hG1) using 1
    · funext t
      simp [outerFirst,Function.comp_def]
    · dsimp [outerSecond]
      push_cast
      ring

private theorem outer_transport (w chi : ℂ) {z : ℝ} (hz : z < 1) (v d dd : ℂ) :
    gaussJet w chi z (power (1/2) (1-z)*v)
      (-powerFirst (1/2) (1-z)*v-power (1/2) (1-z)*d)
      (powerSecond (1/2) (1-z)*v+2*powerFirst (1/2) (1-z)*d+power (1/2) (1-z)*dd) =
    power (1/2) (1-z)*
      ((1-z:ℂ)*(1-(1-z:ℂ))*dd+
        (3/2-((gaussC w-gaussA w chi)+(gaussC w-gaussB w chi)+1)*(1-z:ℂ))*d-
        (gaussC w-gaussA w chi)*(gaussC w-gaussB w chi)*v) := by
  have hx : (1-(z:ℂ)) ≠ 0 := by exact_mod_cast (ne_of_gt (sub_pos.mpr hz))
  dsimp [gaussJet,gaussA,gaussB,gaussC,powerFirst,powerSecond]
  push_cast
  field_simp [hx]
  ring

/-- The exact normalizable factor solves the same original reduced radial
equation as the horizon factor, at independently varying frequency. -/
theorem outerFactor_original_equation {w chi : ℂ} (h : Chamber w chi) {z : ℝ} (hz : z ∈ Ioo 0 1) :
    gaussJet w chi z (outerFactor w chi z) (outerFirst w chi z) (outerSecond w chi z)=0 := by
  have hnorm : ‖((1-z:ℝ):ℂ)‖ₑ < 1 := enorm_ofReal_lt_one (by linarith [hz.2]) (by linarith [hz.1])
  have he := outerFactor_equation h hnorm
  push_cast at he
  dsimp [outerFactor,outerFirst,outerSecond]
  rw [outer_transport w chi hz.2,he,mul_zero]

end
end RHTower.D4BMLaplaceRadial
