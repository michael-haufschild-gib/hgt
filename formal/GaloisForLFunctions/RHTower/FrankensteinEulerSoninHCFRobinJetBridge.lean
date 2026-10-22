import GaloisForLFunctions.RHTower.FrankensteinEulerMobiusSoninCriticalNormalBridge
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeaturePositiveShiftCellAverage

/-!
# Euler--Sonin--HCF Robin-jet bridge

The HCF pole--Gamma--von-Mangoldt Robin jet is not independent arithmetic data.  At every real
height it is the value-minus-tangent functional of the same Euler-affine completed prime--Gamma
source transport already reached by the Möbius and cofinal Sonin constructions.  The identity
persists at finite lattice level and before removal of the punctured positive displacement.

This is a carrier-identification theorem.  It supplies no upper bound for the common Robin-jet
functional; that source order estimate remains the RH-bearing obligation.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Euler-affine parameter whose centered Xi coordinate is the lower HCF Hardy point at height
`t`. -/
def hcfEulerAffineParameter (t : ℝ) : ℂ :=
  -(1 / 2 : ℂ) + (t : ℂ) * I

@[simp] theorem two_add_hcfEulerAffineParameter (t : ℝ) :
    (2 : ℂ) + hcfEulerAffineParameter t =
      criticalFeatureEulerVMArchPoint t := by
  simp [hcfEulerAffineParameter, criticalFeatureEulerVMArchPoint]
  ring

@[simp] theorem xiWardCenteredCoordinate_hcfEulerAffineParameter (t : ℝ) :
    xiWardCenteredCoordinate ((2 : ℂ) + hcfEulerAffineParameter t) =
      (criticalHardyLowerPoint t : ℂ) := by
  rw [two_add_hcfEulerAffineParameter]
  rw [xiWardCenteredCoordinate, criticalHardyLowerPoint_coe,
    criticalFeatureEulerVMArchPoint]
  ring_nf
  rw [I_sq]
  ring

/-- At every HCF height, the continued lower-Hardy source trace is `I` times the completed
Xi--Ward arithmetic current at the corresponding safe Euler point. -/
theorem continuedSource_hcfLower_eq_I_mul_current (t : ℝ) :
    continuedPrimeArchSourceRelativeTrace (criticalHardyLowerPoint t : ℂ) =
      I * xiWardCubicCompletedArithmeticCurrent
        (criticalFeatureEulerVMArchPoint t) := by
  let s : ℂ := criticalFeatureEulerVMArchPoint t
  have hs : 1 < s.re := by
    simp [s]
    norm_num
  have hspos : 0 < s.re := lt_trans zero_lt_one hs
  have hs0 : s ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [s] at hre
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [s] at hre
    norm_num at hre
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hspos
  have hGd : DifferentiableAt ℂ Gammaℝ s :=
    differentiableAt_Gammaℝ_of_re_pos hspos
  rw [continuedPrimeArchSourceRelativeTrace]
  rw [criticalHardyLowerPoint_to_eulerPoint]
  change -I * (infinitePrimeFlux s - logDeriv archFactor s) =
    I * xiWardCubicCompletedArithmeticCurrent s
  rw [infinitePrimeFlux_eq_vonMangoldtLSeries hs,
    logDeriv_archFactor_split hs0 hs1 hG hGd]
  simp only [xiWardCubicCompletedArithmeticCurrent]
  ring

/-- General safe-half-plane form of the preceding source/current identity. -/
theorem continuedSource_centered_eq_I_mul_current
    {s : ℂ} (hs : 1 < s.re) :
    continuedPrimeArchSourceRelativeTrace (xiWardCenteredCoordinate s) =
      I * xiWardCubicCompletedArithmeticCurrent s := by
  have hspos : 0 < s.re := lt_trans zero_lt_one hs
  have hs0 : s ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    rw [zero_re] at hre
    linarith
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    rw [one_re] at hre
    linarith
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hspos
  have hGd : DifferentiableAt ℂ Gammaℝ s :=
    differentiableAt_Gammaℝ_of_re_pos hspos
  rw [continuedPrimeArchSourceRelativeTrace, xiWardCenteredCoordinate_source]
  rw [infinitePrimeFlux_eq_vonMangoldtLSeries hs,
    logDeriv_archFactor_split hs0 hs1 hG hGd]
  simp only [xiWardCubicCompletedArithmeticCurrent]
  ring

/-- Completed source transport based at the Euler point `2` and evaluated in its affine
parameter. -/
def hcfEulerAffineCompletedSourceTransport (u : ℂ) : ℂ :=
  eulerAffineGammaXiWardTransportV (2 : ℂ) 1
    (eulerAffineFisherScore (2 : ℂ) 1) u

/-- The Euler-affine transport is exactly the completed Xi--Ward current throughout its safe
half-plane. -/
theorem hcfEulerAffineCompletedSourceTransport_eq
    {u : ℂ} (hu : 1 < ((2 : ℂ) + u).re) :
    hcfEulerAffineCompletedSourceTransport u =
      I * xiWardCubicCompletedArithmeticCurrent ((2 : ℂ) + u) := by
  rw [hcfEulerAffineCompletedSourceTransport,
    eulerAffineGammaXiWardTransportV_eq_continuedSource
      (by norm_num) (by simpa using hu) (by norm_num)]
  simp only [mul_one]
  exact continuedSource_centered_eq_I_mul_current hu

/-- The derivative of the common Euler-affine carrier is the rotated derivative of the completed
Xi--Ward current at every HCF height. -/
theorem hasDerivAt_hcfEulerAffineCompletedSourceTransport (t : ℝ) :
    HasDerivAt hcfEulerAffineCompletedSourceTransport
      (I * deriv xiWardCubicCompletedArithmeticCurrent
        (criticalFeatureEulerVMArchPoint t))
      (hcfEulerAffineParameter t) := by
  let u := hcfEulerAffineParameter t
  let s := criticalFeatureEulerVMArchPoint t
  have hscoord : (2 : ℂ) + u = s := by
    simp [u, s]
  have hcur : HasDerivAt xiWardCubicCompletedArithmeticCurrent
      (deriv xiWardCubicCompletedArithmeticCurrent s) s := by
    simpa [s] using
      hasDerivAt_xiWardCubicCompletedArithmeticCurrent_eulerVMArchPoint t
  have hcoord : HasDerivAt (fun v : ℂ => (2 : ℂ) + v) 1 u := by
    simpa using (hasDerivAt_id u).const_add (2 : ℂ)
  have hcomp : HasDerivAt
      (fun v : ℂ => xiWardCubicCompletedArithmeticCurrent ((2 : ℂ) + v))
      (deriv xiWardCubicCompletedArithmeticCurrent s) u := by
    have hcur' : HasDerivAt xiWardCubicCompletedArithmeticCurrent
        (deriv xiWardCubicCompletedArithmeticCurrent s) ((2 : ℂ) + u) := by
      rw [hscoord]
      exact hcur
    have h := hcur'.comp u hcoord
    simpa [Function.comp_def] using h
  have hscaled : HasDerivAt
      (fun v : ℂ => I * xiWardCubicCompletedArithmeticCurrent ((2 : ℂ) + v))
      (I * deriv xiWardCubicCompletedArithmeticCurrent s) u :=
    hcomp.const_mul I
  have hopen : IsOpen {v : ℂ | 1 < ((2 : ℂ) + v).re} :=
    isOpen_lt continuous_const
      (Complex.continuous_re.comp (continuous_const.add continuous_id))
  have huopen : u ∈ {v : ℂ | 1 < ((2 : ℂ) + v).re} := by
    change 1 < ((2 : ℂ) + u).re
    rw [hscoord]
    simp [s]
    norm_num
  have heq : hcfEulerAffineCompletedSourceTransport =ᶠ[nhds u]
      fun v : ℂ => I * xiWardCubicCompletedArithmeticCurrent ((2 : ℂ) + v) := by
    filter_upwards [hopen.mem_nhds huopen] with v hv
    exact hcfEulerAffineCompletedSourceTransport_eq hv
  simpa [u, s] using hscaled.congr_of_eventuallyEq heq

/-- **Exact HCF/Ward carrier weld.**  The height-local HCF pole--Gamma--von-Mangoldt jet is the
value-minus-tangent functional of the Euler-affine completed source transport. -/
theorem criticalFeaturePoleGammaVMJet_eq_eulerAffineTransportJet (t : ℝ) :
    criticalFeaturePoleGammaVMJet t =
      2 * ((hcfEulerAffineCompletedSourceTransport
              (hcfEulerAffineParameter t)).im -
        (deriv hcfEulerAffineCompletedSourceTransport
              (hcfEulerAffineParameter t)).im) := by
  have hvalue := hcfEulerAffineCompletedSourceTransport_eq
    (u := hcfEulerAffineParameter t) (by simp; norm_num)
  have hderiv :=
    (hasDerivAt_hcfEulerAffineCompletedSourceTransport t).deriv
  rw [criticalFeaturePoleGammaVMJet_eq_xiWardCubicRobinFinitePart,
    hvalue, hderiv]
  simp [mul_im]

/-- Finite lattice form of the exact HCF/Euler-transport Robin-jet identity. -/
theorem criticalFeaturePoleGammaVMLatticeBudget_eq_eulerAffineTransportJetSum
    (K : Finset ℤ) :
    criticalFeaturePoleGammaVMLatticeBudget K =
      ∑ k ∈ K,
        2 * ((hcfEulerAffineCompletedSourceTransport
                (hcfEulerAffineParameter (k : ℝ))).im -
          (deriv hcfEulerAffineCompletedSourceTransport
                (hcfEulerAffineParameter (k : ℝ))).im) := by
  rw [criticalFeaturePoleGammaVMLatticeBudget]
  apply Finset.sum_congr rfl
  intro k hk
  exact criticalFeaturePoleGammaVMJet_eq_eulerAffineTransportJet (k : ℝ)

/-- Positive-shift regularization written on the same Euler-affine transport carrier as the
limiting HCF Robin jet. -/
def hcfEulerAffineFiniteShiftRobinJet (t : ℝ) (eps : ℂ) : ℝ :=
  2 * ((hcfEulerAffineCompletedSourceTransport
          (hcfEulerAffineParameter t)).im -
    (I * xiWardCubicShiftArithmeticCovariance
          (criticalFeatureEulerVMArchPoint t) eps).im)

theorem hcfEulerAffineFiniteShiftRobinJet_eq_xiWard (t : ℝ) (eps : ℂ) :
    hcfEulerAffineFiniteShiftRobinJet t eps =
      criticalFeatureXiWardCubicFiniteShiftRobinJet t eps := by
  have hvalue := hcfEulerAffineCompletedSourceTransport_eq
    (u := hcfEulerAffineParameter t) (by simp; norm_num)
  rw [hcfEulerAffineFiniteShiftRobinJet,
    criticalFeatureXiWardCubicFiniteShiftRobinJet, hvalue]
  simp [mul_im]

theorem tendsto_hcfEulerAffineFiniteShiftRobinJet (t : ℝ) :
    Tendsto (hcfEulerAffineFiniteShiftRobinJet t) (𝓝[≠] 0)
      (𝓝 (criticalFeaturePoleGammaVMJet t)) := by
  have hfun : hcfEulerAffineFiniteShiftRobinJet t =
      criticalFeatureXiWardCubicFiniteShiftRobinJet t := by
    funext eps
    exact hcfEulerAffineFiniteShiftRobinJet_eq_xiWard t eps
  rw [hfun]
  exact tendsto_criticalFeatureXiWardCubicFiniteShiftRobinJet t

/-- Finite lattice of the common-carrier positive-shift regularization. -/
def hcfEulerAffineFiniteShiftRobinLatticeBudget
    (K : Finset ℤ) (eps : ℂ) : ℝ :=
  ∑ k ∈ K, hcfEulerAffineFiniteShiftRobinJet (k : ℝ) eps

theorem hcfEulerAffineFiniteShiftRobinLatticeBudget_eq_xiWard
    (K : Finset ℤ) (eps : ℂ) :
    hcfEulerAffineFiniteShiftRobinLatticeBudget K eps =
      criticalFeatureXiWardCubicFiniteShiftRobinLatticeBudget K eps := by
  apply Finset.sum_congr rfl
  intro k hk
  exact hcfEulerAffineFiniteShiftRobinJet_eq_xiWard (k : ℝ) eps

/-- Removing the punctured positive displacement after finite lattice summation recovers the exact
HCF pole--Gamma--von-Mangoldt lattice budget on the common Euler-affine carrier. -/
theorem tendsto_hcfEulerAffineFiniteShiftRobinLatticeBudget (K : Finset ℤ) :
    Tendsto (hcfEulerAffineFiniteShiftRobinLatticeBudget K) (𝓝[≠] 0)
      (𝓝 (criticalFeaturePoleGammaVMLatticeBudget K)) := by
  have hfun : hcfEulerAffineFiniteShiftRobinLatticeBudget K =
      criticalFeatureXiWardCubicFiniteShiftRobinLatticeBudget K := by
    funext eps
    exact hcfEulerAffineFiniteShiftRobinLatticeBudget_eq_xiWard K eps
  rw [hfun]
  exact tendsto_criticalFeatureXiWardCubicFiniteShiftRobinLatticeBudget K

end

end RHTower
