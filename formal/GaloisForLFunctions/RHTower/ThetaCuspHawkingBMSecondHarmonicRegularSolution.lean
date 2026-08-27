import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSecondHarmonicComplementarySolutionJet

/-!
# Exact regular BM second-harmonic hypergeometric solution

This module constructs the genuine horizon-regular `++` solution from mathlib's ordinary
hypergeometric series. Exact parameter noncollision gives radius one. Formal-multilinear-series
differentiation and the generic analytic Gauss theorem supply two actual derivatives and the
original BM radial equation, including every Xi fibre.
-/

open Complex Real Set Filter Topology Nat FormalMultilinearSeries Polynomial

namespace RHTower

noncomputable section

/-- Exact original second-harmonic horizon parameter. -/
theorem d4BMCausalRadialC_plusPlus_eq
    (n : ℕ) (chi : ℂ) :
    d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi) =
      -4 * (n : ℂ) - 2 - 2 * Complex.I * chi := by
  simp [d4BMCausalRadialC, d4BMCausalPlusPlusFrequency,
    d4BMCausalQNMPlus, d4BMCausalDecay]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Nonzero angular real part excludes every nonpositive-integral original parameter. -/
theorem d4BMPlusPlusRegularHypergeometricParameters_ne_negNat
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) (j : ℕ) :
    (j : ℂ) ≠
        -d4BMCausalHypergeometricA (d4BMCausalPlusPlusFrequency n chi) chi ∧
      (j : ℂ) ≠
        -d4BMCausalHypergeometricB (d4BMCausalPlusPlusFrequency n chi) chi ∧
      (j : ℂ) ≠
        -d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi) := by
  constructor
  · intro h
    have him := congrArg Complex.im h
    rw [d4BMCausalHypergeometricA_plusPlus] at him
    norm_num [Complex.mul_im] at him
    exact hchi (by linarith)
  constructor
  · intro h
    have him := congrArg Complex.im h
    rw [d4BMCausalHypergeometricB_plusPlus] at him
    norm_num [Complex.mul_im] at him
    exact hchi (by linarith)
  · intro h
    have him := congrArg Complex.im h
    rw [d4BMCausalRadialC_plusPlus_eq] at him
    norm_num [Complex.mul_im] at him
    exact hchi (by linarith)

/-- Formal series for the horizon-regular original `++` solution. -/
def d4BMPlusPlusRegularHypergeometricSeries
    (n : ℕ) (chi : ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  ordinaryHypergeometricSeries ℂ
    (d4BMCausalHypergeometricA (d4BMCausalPlusPlusFrequency n chi) chi)
    (d4BMCausalHypergeometricB (d4BMCausalPlusPlusFrequency n chi) chi)
    (d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi))

/-- The regular original series has exact radius one. -/
theorem d4BMPlusPlusRegularHypergeometricSeries_radius_eq_one
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    (d4BMPlusPlusRegularHypergeometricSeries n chi).radius = 1 := by
  rw [d4BMPlusPlusRegularHypergeometricSeries]
  apply ordinaryHypergeometricSeries_radius_eq_one
  exact d4BMPlusPlusRegularHypergeometricParameters_ne_negNat n chi hchi

/-- Horizon-regular original `++` solution factor. -/
def d4BMPlusPlusRegularHypergeometricSolution
    (n : ℕ) (chi z : ℂ) : ℂ :=
  (d4BMPlusPlusRegularHypergeometricSeries n chi).sum z

/-- Exact first derivative-series value of the regular solution. -/
def d4BMPlusPlusRegularHypergeometricSolutionDerivative
    (n : ℕ) (chi z : ℂ) : ℂ :=
  (((d4BMPlusPlusRegularHypergeometricSeries n chi).derivSeries.sum z) 1)

/-- Exact second derivative-series value of the regular solution. -/
def d4BMPlusPlusRegularHypergeometricSolutionSecondDerivative
    (n : ℕ) (chi z : ℂ) : ℂ :=
  ((((d4BMPlusPlusRegularHypergeometricSeries n chi).derivSeries.derivSeries.sum z)
    1) 1)

@[simp]
theorem d4BMPlusPlusRegularHypergeometricSolution_zero
    (n : ℕ) (chi : ℂ) :
    d4BMPlusPlusRegularHypergeometricSolution n chi 0 = 1 := by
  change ordinaryHypergeometric
    (d4BMCausalHypergeometricA (d4BMCausalPlusPlusFrequency n chi) chi)
    (d4BMCausalHypergeometricB (d4BMCausalPlusPlusFrequency n chi) chi)
    (d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi)) 0 = 1
  exact ordinaryHypergeometric_zero _ _ _

/-- Regular solution is complex differentiable with the exact first derivative in the unit disk. -/
theorem hasDerivAt_d4BMPlusPlusRegularHypergeometricSolution
    (n : ℕ) (chi z : ℂ) (hchi : chi.re ≠ 0) (hz : ‖z‖ₑ < 1) :
    HasDerivAt (d4BMPlusPlusRegularHypergeometricSolution n chi)
      (d4BMPlusPlusRegularHypergeometricSolutionDerivative n chi z) z := by
  let p := d4BMPlusPlusRegularHypergeometricSeries n chi
  have hzp : ‖z‖ₑ < p.radius := by
    rw [d4BMPlusPlusRegularHypergeometricSeries_radius_eq_one n chi hchi]
    exact hz
  change HasDerivAt p.sum ((p.derivSeries.sum z) 1) z
  exact (p.hasFDerivAt_sum hzp).hasDerivAt

/-- First derivative is complex differentiable with the exact second derivative in the unit disk. -/
theorem hasDerivAt_d4BMPlusPlusRegularHypergeometricSolutionDerivative
    (n : ℕ) (chi z : ℂ) (hchi : chi.re ≠ 0) (hz : ‖z‖ₑ < 1) :
    HasDerivAt (d4BMPlusPlusRegularHypergeometricSolutionDerivative n chi)
      (d4BMPlusPlusRegularHypergeometricSolutionSecondDerivative n chi z) z := by
  let p := d4BMPlusPlusRegularHypergeometricSeries n chi
  let q := p.derivSeries
  have hzp : ‖z‖ₑ < p.radius := by
    rw [d4BMPlusPlusRegularHypergeometricSeries_radius_eq_one n chi hchi]
    exact hz
  have hzq : ‖z‖ₑ < q.radius :=
    lt_of_lt_of_le hzp p.radius_le_radius_derivSeries
  have hq := q.hasFDerivAt_sum hzq
  have heval := hq.clm_apply (hasFDerivAt_const (1 : ℂ) z)
  change HasDerivAt (fun w : ℂ => (q.sum w) 1)
    (((q.derivSeries.sum z) 1) 1) z
  simpa using heval.hasDerivAt

/-- Horizon-regular solution satisfies the original BM radial equation in the unit disk. -/
theorem d4BMPlusPlusRegularHypergeometricSolution_jet_eq_zero
    (n : ℕ) (chi z : ℂ) (hchi : chi.re ≠ 0) (hz : ‖z‖ₑ < 1) :
    z * (1 - z) *
          d4BMPlusPlusRegularHypergeometricSolutionSecondDerivative n chi z +
        (d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi) -
          (d4BMCausalHypergeometricA (d4BMCausalPlusPlusFrequency n chi) chi +
            d4BMCausalHypergeometricB (d4BMCausalPlusPlusFrequency n chi) chi + 1) * z) *
          d4BMPlusPlusRegularHypergeometricSolutionDerivative n chi z -
      d4BMCausalHypergeometricA (d4BMCausalPlusPlusFrequency n chi) chi *
        d4BMCausalHypergeometricB (d4BMCausalPlusPlusFrequency n chi) chi *
          d4BMPlusPlusRegularHypergeometricSolution n chi z = 0 := by
  let a := d4BMCausalHypergeometricA (d4BMCausalPlusPlusFrequency n chi) chi
  let b := d4BMCausalHypergeometricB (d4BMCausalPlusPlusFrequency n chi) chi
  let c := d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi)
  have hc : ∀ j : ℕ, (j : ℂ) ≠ -c := by
    intro j
    exact (d4BMPlusPlusRegularHypergeometricParameters_ne_negNat n chi hchi j).2.2
  have hzr : ‖z‖ₑ < (ordinaryHypergeometricSeries ℂ a b c).radius := by
    change ‖z‖ₑ < (d4BMPlusPlusRegularHypergeometricSeries n chi).radius
    rw [d4BMPlusPlusRegularHypergeometricSeries_radius_eq_one n chi hchi]
    exact hz
  have hode := ordinaryHypergeometric_standardGaussODE a b c z hc hzr
  simpa only [a, b, c,
    d4BMPlusPlusRegularHypergeometricSolution,
    d4BMPlusPlusRegularHypergeometricSolutionDerivative,
    d4BMPlusPlusRegularHypergeometricSolutionSecondDerivative,
    d4BMPlusPlusRegularHypergeometricSeries,
    ordinaryHypergeometricFirstDerivativeSeriesValue,
    ordinaryHypergeometricSecondDerivativeSeriesValue] using hode

/-- Every Xi fibre has the exact horizon-regular original solution. -/
theorem d4BMXiPlusPlusRegularHypergeometricSolution_jet_eq_zero
    (n : ℕ) (q : XiZeroCopy) (z : ℂ) (hz : ‖z‖ₑ < 1) :
    z * (1 - z) *
          d4BMPlusPlusRegularHypergeometricSolutionSecondDerivative n
            (d4BMXiMixedHorizonAngularMomentum q) z +
        (d4BMCausalRadialC
            (d4BMCausalPlusPlusFrequency n (d4BMXiMixedHorizonAngularMomentum q)) -
          (d4BMCausalHypergeometricA
                (d4BMCausalPlusPlusFrequency n (d4BMXiMixedHorizonAngularMomentum q))
                (d4BMXiMixedHorizonAngularMomentum q) +
            d4BMCausalHypergeometricB
                (d4BMCausalPlusPlusFrequency n (d4BMXiMixedHorizonAngularMomentum q))
                (d4BMXiMixedHorizonAngularMomentum q) + 1) * z) *
          d4BMPlusPlusRegularHypergeometricSolutionDerivative n
            (d4BMXiMixedHorizonAngularMomentum q) z -
      d4BMCausalHypergeometricA
          (d4BMCausalPlusPlusFrequency n (d4BMXiMixedHorizonAngularMomentum q))
          (d4BMXiMixedHorizonAngularMomentum q) *
        d4BMCausalHypergeometricB
          (d4BMCausalPlusPlusFrequency n (d4BMXiMixedHorizonAngularMomentum q))
          (d4BMXiMixedHorizonAngularMomentum q) *
          d4BMPlusPlusRegularHypergeometricSolution n
            (d4BMXiMixedHorizonAngularMomentum q) z = 0 := by
  exact d4BMPlusPlusRegularHypergeometricSolution_jet_eq_zero n _ z
    (d4BMXiMixedHorizonAngularMomentum_re_ne_zero q) hz

end

end RHTower
