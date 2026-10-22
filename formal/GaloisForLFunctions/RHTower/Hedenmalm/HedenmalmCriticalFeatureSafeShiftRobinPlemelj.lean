/-
# Safe-shift Robin--Plemelj normal form for the HCF budget

The zero-independent Euler-safe source density on the vertical shift ray packages the full
pole--Gamma--von-Mangoldt jet as one Robin datum.  This localizes every compact corrected HCF
budget as a finite sum of source-only Robin--Plemelj defects.  No quantitative estimate is assumed.
-/
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureSourcePlemeljTrace

open Complex Function Filter Topology

namespace RHTower

noncomputable section

/-- Positive real-shift density along the Euler-safe vertical source ray. -/
def criticalFeatureSafeShiftSourceDensity (t eta : ℝ) : ℝ :=
  Real.pi⁻¹ *
    (primeArchSourceRelativeTrace
      ((t : ℂ) - (eta : ℂ) * Complex.I)).im

/-- Robin datum of the source density at the absolute-Euler point `eta = 1`. -/
def criticalFeatureSafeShiftRobinJet (t : ℝ) : ℝ :=
  2 * Real.pi *
    (criticalFeatureSafeShiftSourceDensity t 1 -
      deriv (criticalFeatureSafeShiftSourceDensity t) 1)

/-- Local Robin--Plemelj defect at one lattice center and compact cutoff. -/
def criticalFeatureSafeShiftRobinPlemeljDefect (t : ℝ) (n : ℕ) : ℝ :=
  criticalFeatureSafeShiftRobinJet t -
    limUnder (𝓝[>] (0 : ℝ))
      (criticalFeatureCompactPoleGammaObservable t n)

private theorem differentiableAt_primeArchSourceRelativeTrace_lower (t : ℝ) :
    DifferentiableAt ℂ primeArchSourceRelativeTrace
      (criticalHardyLowerPoint t : ℂ) := by
  have hH : DifferentiableAt ℂ criticalFeatureEulerVMArchCarrier
      (criticalFeatureEulerVMArchPoint t) :=
    differentiableAt_criticalFeatureEulerVMArchCarrier t
  have hcoord : HasDerivAt (fun w : ℂ => 1 / 2 + w * I) I
      (criticalHardyLowerPoint t : ℂ) := by
    simpa using
      ((hasDerivAt_id (𝕜 := ℂ) (x := (criticalHardyLowerPoint t : ℂ))).mul_const I).const_add
        (1 / 2 : ℂ)
  have hH' : DifferentiableAt ℂ criticalFeatureEulerVMArchCarrier
      (1 / 2 + (criticalHardyLowerPoint t : ℂ) * I) := by
    rw [criticalHardyLowerPoint_to_eulerPoint]
    exact hH
  have hcomp := hH'.hasDerivAt.comp (criticalHardyLowerPoint t : ℂ) hcoord
  have hscaled : HasDerivAt
      (fun w : ℂ => -I *
        criticalFeatureEulerVMArchCarrier (1 / 2 + w * I))
      (-I * (deriv criticalFeatureEulerVMArchCarrier
        (1 / 2 + (criticalHardyLowerPoint t : ℂ) * I) * I))
      (criticalHardyLowerPoint t : ℂ) :=
    hcomp.const_mul (-I)
  have htrace : primeArchSourceRelativeTrace =
      fun w : ℂ => -I *
        criticalFeatureEulerVMArchCarrier (1 / 2 + w * I) := by
    rfl
  rw [htrace]
  exact hscaled.differentiableAt

/-- The shift derivative at the safe point is minus the real part of the complex source jet. -/
theorem hasDerivAt_criticalFeatureSafeShiftSourceDensity_one (t : ℝ) :
    HasDerivAt (criticalFeatureSafeShiftSourceDensity t)
      (-(Real.pi⁻¹ *
        (deriv primeArchSourceRelativeTrace
          (criticalHardyLowerPoint t : ℂ)).re)) 1 := by
  have hpath : HasDerivAt
      (fun eta : ℝ => (t : ℂ) - (eta : ℂ) * I) (-I) 1 := by
    have hid : HasDerivAt (fun eta : ℝ => (eta : ℂ)) 1 1 :=
      (hasDerivAt_id (x := (1 : ℝ))).ofReal_comp
    have h := (hasDerivAt_const (x := (1 : ℝ)) (c := (t : ℂ))).sub
      (hid.mul_const I)
    have h' : HasDerivAt
        ((fun _ : ℝ => (t : ℂ)) - fun eta : ℝ => (eta : ℂ) * I)
        (-I) 1 := by
      simpa only [zero_sub, one_mul] using h
    exact h'.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun eta => rfl)
  have hP := differentiableAt_primeArchSourceRelativeTrace_lower t
  have hP' : DifferentiableAt ℂ primeArchSourceRelativeTrace
      ((t : ℂ) - ((1 : ℝ) : ℂ) * I) := by
    simpa [criticalHardyLowerPoint_coe] using hP
  have hcomp : HasDerivAt
      (fun eta : ℝ => primeArchSourceRelativeTrace
        ((t : ℂ) - (eta : ℂ) * I))
      (deriv primeArchSourceRelativeTrace
        ((t : ℂ) - ((1 : ℝ) : ℂ) * I) * (-I)) 1 := by
    have h := HasDerivAt.scomp 1 hP'.hasDerivAt hpath
    simpa [Function.comp_def, mul_comm] using h
  have him : HasDerivAt
      (fun eta : ℝ => (primeArchSourceRelativeTrace
        ((t : ℂ) - (eta : ℂ) * I)).im)
      (deriv primeArchSourceRelativeTrace
        ((t : ℂ) - ((1 : ℝ) : ℂ) * I) * (-I)).im 1 :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt 1 hcomp
  have hscaled := him.const_mul Real.pi⁻¹
  change HasDerivAt
    (fun eta : ℝ => Real.pi⁻¹ *
      (primeArchSourceRelativeTrace
        ((t : ℂ) - (eta : ℂ) * I)).im)
    (-(Real.pi⁻¹ *
      (deriv primeArchSourceRelativeTrace
        (criticalHardyLowerPoint t : ℂ)).re)) 1
  rw [show (t : ℂ) - ((1 : ℝ) : ℂ) * I =
      (criticalHardyLowerPoint t : ℂ) by
    simp [criticalHardyLowerPoint_coe]] at hscaled
  simpa [Complex.mul_im] using hscaled

theorem deriv_criticalFeatureSafeShiftSourceDensity_one (t : ℝ) :
    deriv (criticalFeatureSafeShiftSourceDensity t) 1 =
      -(Real.pi⁻¹ *
        (deriv primeArchSourceRelativeTrace
          (criticalHardyLowerPoint t : ℂ)).re) :=
  (hasDerivAt_criticalFeatureSafeShiftSourceDensity_one t).deriv

/-- The full Euler-safe arithmetic jet is exactly the source density's Robin datum. -/
theorem criticalFeatureSafeShiftRobinJet_eq_poleGammaVMJet (t : ℝ) :
    criticalFeatureSafeShiftRobinJet t =
      criticalFeaturePoleGammaVMJet t := by
  rw [criticalFeatureSafeShiftRobinJet,
    deriv_criticalFeatureSafeShiftSourceDensity_one]
  simp [criticalFeatureSafeShiftSourceDensity, criticalHardyLowerPoint_coe,
    criticalFeaturePoleGammaVMJet]
  field_simp [Real.pi_ne_zero]
  ring

/-- Finite safe-shift Robin lattice budget. -/
def criticalFeatureSafeShiftRobinLatticeBudget (K : Finset ℤ) : ℝ :=
  ∑ k ∈ K, criticalFeatureSafeShiftRobinJet (k : ℝ)

theorem criticalFeatureSafeShiftRobinLatticeBudget_eq_poleGammaVM
    (K : Finset ℤ) :
    criticalFeatureSafeShiftRobinLatticeBudget K =
      criticalFeaturePoleGammaVMLatticeBudget K := by
  rw [criticalFeatureSafeShiftRobinLatticeBudget,
    criticalFeaturePoleGammaVMLatticeBudget]
  apply Finset.sum_congr rfl
  intro k hk
  exact criticalFeatureSafeShiftRobinJet_eq_poleGammaVMJet (k : ℝ)

/-- Every compact corrected budget is a finite sum of local source-only Robin--Plemelj defects. -/
theorem criticalFeatureSourcePlemeljCorrectedLatticeBudget_eq_sum_robinDefects
    (K : Finset ℤ) (n : ℕ) :
    criticalFeatureSourcePlemeljCorrectedLatticeBudget K n =
      ∑ k ∈ K, criticalFeatureSafeShiftRobinPlemeljDefect (k : ℝ) n := by
  rw [criticalFeatureSourcePlemeljCorrectedLatticeBudget]
  apply Finset.sum_congr rfl
  intro k hk
  rw [criticalFeatureSafeShiftRobinPlemeljDefect,
    criticalFeatureSafeShiftRobinJet_eq_poleGammaVMJet]

/-- Local Robin--Plemelj defect sums converge to the exact corrected HCF lattice budget. -/
theorem tendsto_criticalFeatureSafeShiftRobinPlemeljDefect_sum
    (K : Finset ℤ) :
    Tendsto
      (fun n : ℕ =>
        ∑ k ∈ K, criticalFeatureSafeShiftRobinPlemeljDefect (k : ℝ) n)
      atTop (𝓝 (criticalFeaturePrimeGammaOffLineLatticeBudget K)) := by
  refine (tendsto_criticalFeatureSourcePlemeljCorrectedLatticeBudget K).congr' ?_
  exact Filter.Eventually.of_forall fun n =>
    criticalFeatureSourcePlemeljCorrectedLatticeBudget_eq_sum_robinDefects K n

end

end RHTower
