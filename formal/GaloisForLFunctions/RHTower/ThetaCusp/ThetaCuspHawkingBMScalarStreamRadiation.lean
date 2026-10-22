import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMScalarStreamGreenSourced
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSecondHarmonicRadialBoundaryUniqueness

/-!
# Radiation coefficient of the scalar–scalar `++` harmonic response

The normalizable-branch coefficient of the causal per-harmonic scalar–scalar response is the
accumulated regular-mode moment of the scalar–scalar forcing `−(r²(r²−1)/4)·ssMasterSource` against
the corpus Green weight (`ssRadiation`). This is the explicit radial source moment that the `++`
scalar–scalar block contributes to the horizon-plus-boundary radiation; its value at the physical
Xi parameters is a definite hypergeometric moment of a rational forcing.
-/

open Set

namespace RHTower.D4BMScalarStream

noncomputable section

/-- Regular-mode moment of the scalar–scalar forcing: the `++` scalar–scalar radiation coefficient
accumulated from the inner cutoff `a` to `z`. -/
def ssRadiation (n : ℕ) (chi : ℂ) (a z : ℝ) : ℂ :=
  d4BMPlusPlusContinuousGreenMoment n chi
    (fun t => d4BMPlusPlusRegularHypergeometricSolution n chi (t : ℂ))
    (ssForcing (dictRate n chi) (dictEigen chi)) a z

theorem ssRadiation_eq_integral (n : ℕ) (chi : ℂ) (a z : ℝ) :
    ssRadiation n chi a z = ∫ t in a..z, d4BMPlusPlusRegularHypergeometricSolution n chi (t : ℂ) *
      d4BMPlusPlusContinuousGreenWeight n chi t * ssForcing (dictRate n chi) (dictEigen chi) t :=
  rfl

/-- The normalizable phase coefficient of the scalar–scalar `++` master response is its radiation
coefficient. -/
theorem greenSS_normalizableCoefficient (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) (a b : ℝ) {z : ℝ}
    (hz : z ∈ Ioo (0 : ℝ) 1) :
    d4BMPlusPlusRadialNormalizableCoefficient n chi
      (d4BMPlusPlusContinuousGreenResponse n chi (ssForcing (dictRate n chi) (dictEigen chi)) a b)
      (d4BMPlusPlusContinuousGreenResponseDerivative n chi (ssForcing (dictRate n chi) (dictEigen chi)) a b) z =
      ssRadiation n chi a z :=
  d4BMPlusPlusContinuousGreenResponse_normalizableCoefficient n chi hchi _ a b hz

end
end RHTower.D4BMScalarStream
