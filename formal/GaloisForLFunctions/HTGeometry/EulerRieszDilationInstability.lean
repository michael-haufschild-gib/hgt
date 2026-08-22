import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

/-!
# A stationary Euler--Riesz dilation profile

For the four-dimensional attractive Euler--Riesz energy with Riesz exponent `2` and polytropic
homogeneity `3 / 2`, a mass-preserving dilation has two competing homogeneous terms.  This module
records an unconditional normalized profile in which the first variation vanishes at unit scale
and the second variation is strictly negative.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- A two-homogeneity energy profile normalized to be stationary at unit scale. -/
def stationaryTwoHomogeneityDilationProfile
    (energy internalExponent interactionExponent massOffset scale : ℝ) : ℝ :=
  interactionExponent * energy * scale ^ internalExponent
    - internalExponent * energy * scale ^ interactionExponent + massOffset

/-- The scale variation of a two-homogeneity stationary profile. -/
def stationaryTwoHomogeneityDilationVariation
    (energy internalExponent interactionExponent scale : ℝ) : ℝ :=
  interactionExponent * energy * internalExponent * scale ^ (internalExponent - 1)
    - internalExponent * energy * interactionExponent * scale ^ (interactionExponent - 1)

/-- Every normalized two-homogeneity profile is stationary at unit scale. -/
theorem hasDerivAt_stationaryTwoHomogeneityDilationProfile_unit_zero
    (energy internalExponent interactionExponent massOffset : ℝ) :
    HasDerivAt
      (stationaryTwoHomogeneityDilationProfile energy internalExponent interactionExponent massOffset)
      0 1 := by
  unfold stationaryTwoHomogeneityDilationProfile
  have hp : HasDerivAt (fun x : ℝ => x ^ internalExponent)
      (internalExponent * 1 ^ (internalExponent - 1)) 1 :=
    Real.hasDerivAt_rpow_const (Or.inl one_ne_zero)
  have hq : HasDerivAt (fun x : ℝ => x ^ interactionExponent)
      (interactionExponent * 1 ^ (interactionExponent - 1)) 1 :=
    Real.hasDerivAt_rpow_const (Or.inl one_ne_zero)
  have hbase := (hp.const_mul (interactionExponent * energy)).sub
    (hq.const_mul (internalExponent * energy))
  have hzero : HasDerivAt
      (fun x : ℝ => interactionExponent * energy * x ^ internalExponent
        - internalExponent * energy * x ^ interactionExponent) 0 1 :=
    hbase.congr_deriv (by norm_num; ring)
  exact hzero.add_const massOffset

/-- The unit-scale curvature of the two-homogeneity variation. -/
theorem hasDerivAt_stationaryTwoHomogeneityDilationVariation_unit
    (energy internalExponent interactionExponent : ℝ) :
    HasDerivAt
      (stationaryTwoHomogeneityDilationVariation energy internalExponent interactionExponent)
      (internalExponent * interactionExponent * energy * (internalExponent - interactionExponent)) 1 := by
  unfold stationaryTwoHomogeneityDilationVariation
  have hp : HasDerivAt (fun x : ℝ => x ^ (internalExponent - 1))
      ((internalExponent - 1) * 1 ^ ((internalExponent - 1) - 1)) 1 :=
    Real.hasDerivAt_rpow_const (Or.inl one_ne_zero)
  have hq : HasDerivAt (fun x : ℝ => x ^ (interactionExponent - 1))
      ((interactionExponent - 1) * 1 ^ ((interactionExponent - 1) - 1)) 1 :=
    Real.hasDerivAt_rpow_const (Or.inl one_ne_zero)
  have hbase := (hp.const_mul (interactionExponent * energy * internalExponent)).sub
    (hq.const_mul (internalExponent * energy * interactionExponent))
  exact hbase.congr_deriv (by norm_num; ring)

/-- A normalized attractive Euler--Riesz energy along a mass-preserving dilation. -/
def eulerRieszDilationProfile (amplitude massOffset scale : ℝ) : ℝ :=
  2 * (amplitude ^ 2 + 1) * scale ^ (3 / 2 : ℝ)
    - (3 / 2 : ℝ) * (amplitude ^ 2 + 1) * scale ^ (2 : ℝ) + massOffset

/-- The scale derivative of the normalized Euler--Riesz profile. -/
def eulerRieszDilationVariation (amplitude scale : ℝ) : ℝ :=
  3 * (amplitude ^ 2 + 1) * scale ^ (1 / 2 : ℝ) - 3 * (amplitude ^ 2 + 1) * scale

/-- The normalized Euler--Riesz profile is a two-homogeneity stationary profile. -/
theorem eulerRieszDilationProfile_eq_stationaryTwoHomogeneity
    (amplitude massOffset scale : ℝ) :
    eulerRieszDilationProfile amplitude massOffset scale =
      stationaryTwoHomogeneityDilationProfile (amplitude ^ 2 + 1) (3 / 2 : ℝ) 2 massOffset scale := by
  unfold eulerRieszDilationProfile stationaryTwoHomogeneityDilationProfile
  ring

/-- The normalized Euler--Riesz variation is the specialized two-homogeneity variation. -/
theorem eulerRieszDilationVariation_eq_stationaryTwoHomogeneity
    (amplitude scale : ℝ) :
    eulerRieszDilationVariation amplitude scale =
      stationaryTwoHomogeneityDilationVariation (amplitude ^ 2 + 1) (3 / 2 : ℝ) 2 scale := by
  unfold eulerRieszDilationVariation stationaryTwoHomogeneityDilationVariation
  norm_num
  ring

/-- The normalized Euler--Riesz profile has the stated scale derivative at every scale. -/
theorem hasDerivAt_eulerRieszDilationProfile (amplitude massOffset scale : ℝ) :
    HasDerivAt (eulerRieszDilationProfile amplitude massOffset)
      (eulerRieszDilationVariation amplitude scale) scale := by
  unfold eulerRieszDilationProfile eulerRieszDilationVariation
  have hthree : HasDerivAt (fun x : ℝ => x ^ (3 / 2 : ℝ))
      ((3 / 2 : ℝ) * scale ^ ((3 / 2 : ℝ) - 1)) scale :=
    Real.hasDerivAt_rpow_const (Or.inr (by norm_num))
  have htwo : HasDerivAt (fun x : ℝ => x ^ (2 : ℝ))
      ((2 : ℝ) * scale ^ ((2 : ℝ) - 1)) scale :=
    Real.hasDerivAt_rpow_const (Or.inr (by norm_num))
  have hbase := (hthree.const_mul (2 * (amplitude ^ 2 + 1))).sub
    (htwo.const_mul ((3 / 2 : ℝ) * (amplitude ^ 2 + 1)))
  have hvariation : HasDerivAt
      (fun x : ℝ => 2 * (amplitude ^ 2 + 1) * x ^ (3 / 2 : ℝ)
        - (3 / 2 : ℝ) * (amplitude ^ 2 + 1) * x ^ (2 : ℝ))
      (3 * (amplitude ^ 2 + 1) * scale ^ (1 / 2 : ℝ)
        - 3 * (amplitude ^ 2 + 1) * scale) scale :=
    hbase.congr_deriv (by norm_num; simp; ring)
  exact hvariation.add_const massOffset

/-- Unit scale is stationary for the normalized Euler--Riesz profile. -/
theorem hasDerivAt_eulerRieszDilationProfile_unit_zero (amplitude massOffset : ℝ) :
    HasDerivAt (eulerRieszDilationProfile amplitude massOffset) 0 1 := by
  have h := hasDerivAt_eulerRieszDilationProfile amplitude massOffset 1
  exact h.congr_deriv (by unfold eulerRieszDilationVariation; norm_num)

/-- The Euler--Riesz scale derivative has negative slope at unit scale. -/
theorem hasDerivAt_eulerRieszDilationVariation_unit (amplitude : ℝ) :
    HasDerivAt (eulerRieszDilationVariation amplitude)
      (-(3 / 2 : ℝ) * (amplitude ^ 2 + 1)) 1 := by
  unfold eulerRieszDilationVariation
  have hhalf : HasDerivAt (fun x : ℝ => x ^ (1 / 2 : ℝ))
      ((1 / 2 : ℝ) * 1 ^ ((1 / 2 : ℝ) - 1)) 1 :=
    Real.hasDerivAt_rpow_const (Or.inl one_ne_zero)
  have hid : HasDerivAt (fun x : ℝ => x) 1 1 := hasDerivAt_id _
  have hbase := (hhalf.const_mul (3 * (amplitude ^ 2 + 1))).sub
    (hid.const_mul (3 * (amplitude ^ 2 + 1)))
  exact hbase.congr_deriv (by norm_num; ring)

/-- The derivative of the Euler--Riesz profile is its scale variation. -/
theorem deriv_eulerRieszDilationProfile (amplitude massOffset : ℝ) :
    deriv (eulerRieszDilationProfile amplitude massOffset)
      = eulerRieszDilationVariation amplitude := by
  funext scale
  exact (hasDerivAt_eulerRieszDilationProfile amplitude massOffset scale).deriv

/-- The first variation of the Euler--Riesz profile vanishes at unit scale. -/
theorem deriv_eulerRieszDilationProfile_unit (amplitude massOffset : ℝ) :
    deriv (eulerRieszDilationProfile amplitude massOffset) 1 = 0 :=
  (hasDerivAt_eulerRieszDilationProfile_unit_zero amplitude massOffset).deriv

/-- The unit-scale second variation is the exact negative curvature. -/
theorem secondDeriv_eulerRieszDilationProfile_unit (amplitude massOffset : ℝ) :
    deriv (deriv (eulerRieszDilationProfile amplitude massOffset)) 1
      = -(3 / 2 : ℝ) * (amplitude ^ 2 + 1) := by
  rw [deriv_eulerRieszDilationProfile]
  exact (hasDerivAt_eulerRieszDilationVariation_unit amplitude).deriv

/-- The normalized Euler--Riesz energy has strictly negative unit-scale second variation. -/
theorem secondDeriv_eulerRieszDilationProfile_unit_neg (amplitude massOffset : ℝ) :
    deriv (deriv (eulerRieszDilationProfile amplitude massOffset)) 1 < 0 := by
  rw [secondDeriv_eulerRieszDilationProfile_unit]
  have hpos : 0 < amplitude ^ 2 + 1 := by positivity
  nlinarith

/-- Unit scale is a strictly variationally unstable stationary dilation direction. -/
theorem eulerRieszDilationProfile_unit_strict_variational_instability
    (amplitude massOffset : ℝ) :
    deriv (eulerRieszDilationProfile amplitude massOffset) 1 = 0
      ∧ deriv (deriv (eulerRieszDilationProfile amplitude massOffset)) 1 < 0 :=
  ⟨deriv_eulerRieszDilationProfile_unit amplitude massOffset,
    secondDeriv_eulerRieszDilationProfile_unit_neg amplitude massOffset⟩

end GaloisForLFunctions.HTGeometry
