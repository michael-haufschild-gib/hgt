import GaloisForLFunctions.RHTower.NonMarkovianLangevinCorpusApplications
import GaloisForLFunctions.RHTower.CriticalPrimeTailEulerLogPositiveDefinite
import GaloisForLFunctions.RHTower.SoninSemilocalDampedCovariancePositivity
import GaloisForLFunctions.RHTower.SuzukiCauchyReporterSecantWardCapacity
import GaloisForLFunctions.HTGeometry.JuliaDefectEquilibriumPositiveDefinite
import GaloisForLFunctions.HTGeometry.CharacteristicDefectGramCapacity
import Mathlib.Tactic

open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Every real-weight atomic Fourier series has the paper's Hermitian memory symmetry. -/
theorem atomicFourierSeries_neg
    (weight frequency : ℕ → ℝ) (t : ℝ) :
    atomicFourierSeries weight frequency (-t) =
      star (atomicFourierSeries weight frequency t) := by
  unfold atomicFourierSeries
  rw [tsum_star]
  apply tsum_congr
  intro n
  have hchar : realFourierCharacter (frequency n) (-t) =
      star (realFourierCharacter (frequency n) t) := by
    simpa [realFourierCharacter] using
      realFourierCharacter_sub (frequency n) t 0
  rw [star_mul, ← hchar]
  have hweight : star (((weight n : ℝ) : ℂ)) = (((weight n : ℝ) : ℂ)) := by
    apply Complex.ext <;> simp
  rw [hweight]
  ring

theorem schwarzschildBoseMemoryKernel_neg (t : ℝ) :
    schwarzschildBoseMemoryKernel (-t) =
      star (schwarzschildBoseMemoryKernel t) :=
  atomicFourierSeries_neg _ _ t

/-! ## Critical prime-tail Euler logarithm -/

/-- Safe-line Euler logarithm at `Re s = 3/2`, viewed as a memory kernel. -/
def criticalPrimeTailMemoryKernel : ℝ → ℂ :=
  _root_.RHTower.criticalPrimeTailEulerLogVerticalTrace 1

theorem criticalPrimeTailMemoryKernel_neg (t : ℝ) :
    criticalPrimeTailMemoryKernel (-t) =
      star (criticalPrimeTailMemoryKernel t) :=
  atomicFourierSeries_neg _ _ t

theorem norm_criticalPrimeTailMemoryKernel_le_totalMass (t : ℝ) :
    ‖criticalPrimeTailMemoryKernel t‖ ≤
      ∑' n : _root_.RHTower.DeningerPrimePowerIndex,
        _root_.RHTower.criticalPrimeTailLaplaceMass 1 n := by
  unfold criticalPrimeTailMemoryKernel
  rw [_root_.RHTower.criticalPrimeTailEulerLogVerticalTrace_eq_canonicalEulerLogZeta
    (r := (1 : ℝ)) (by norm_num)]
  exact _root_.RHTower.norm_canonicalEulerLogZeta_vertical_le_totalMass
    (r := (1 : ℝ)) (by norm_num) t

theorem positiveDefiniteOnReal_criticalPrimeTailMemoryKernel :
    PositiveDefiniteOnReal criticalPrimeTailMemoryKernel := by
  unfold criticalPrimeTailMemoryKernel
  exact positiveDefinite_atomicFourierSeries_of_nonnegative
    (_root_.RHTower.summable_abs_criticalPrimeTailFourierWeight
      (r := (1 : ℝ)) (by norm_num))
    (_root_.RHTower.criticalPrimeTailFourierWeight_nonneg 1)

/-! ## Archimedean Gamma cyclic memory -/

def gammaCyclicMemoryKernel (t : ℝ) : ℂ :=
  (_root_.RHTower.semilocalArchimedeanCharacteristic t : ℂ)

theorem gammaCyclicMemoryKernel_neg (t : ℝ) :
    gammaCyclicMemoryKernel (-t) = star (gammaCyclicMemoryKernel t) := by
  rw [gammaCyclicMemoryKernel, gammaCyclicMemoryKernel,
    _root_.RHTower.semilocalArchimedeanCharacteristic_neg]
  apply Complex.ext <;> simp

theorem norm_gammaCyclicMemoryKernel_le_zero (t : ℝ) :
    ‖gammaCyclicMemoryKernel t‖ ≤ 1 := by
  rw [gammaCyclicMemoryKernel, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (_root_.RHTower.semilocalArchimedeanCharacteristic_pos t)]
  exact _root_.RHTower.semilocalArchimedeanCharacteristic_le_one t

theorem positiveDefiniteOnReal_gammaCyclicMemoryKernel :
    PositiveDefiniteOnReal gammaCyclicMemoryKernel :=
  _root_.RHTower.positiveDefiniteOnReal_semilocalArchimedeanCharacteristic

/-! ## Cauchy half-exponential memory -/

def cauchyHalfExponentialMemoryKernel (t : ℝ) : ℂ :=
  (GaloisForLFunctions.RHTower.cauchyHalfExponentialKernel t : ℂ)

theorem cauchyHalfExponentialMemoryKernel_neg (t : ℝ) :
    cauchyHalfExponentialMemoryKernel (-t) =
      star (cauchyHalfExponentialMemoryKernel t) := by
  unfold cauchyHalfExponentialMemoryKernel
    GaloisForLFunctions.RHTower.cauchyHalfExponentialKernel
  rw [abs_neg]
  apply Complex.ext <;> simp only [Complex.ofReal_re, Complex.ofReal_im,
    neg_zero, Complex.star_def, Complex.conj_re, Complex.conj_im]

theorem norm_cauchyHalfExponentialMemoryKernel_le_zero (t : ℝ) :
    ‖cauchyHalfExponentialMemoryKernel t‖ ≤ 1 := by
  unfold cauchyHalfExponentialMemoryKernel
    GaloisForLFunctions.RHTower.cauchyHalfExponentialKernel
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (by
    have ht := abs_nonneg t
    linarith)

theorem positiveDefiniteOnReal_cauchyHalfExponentialMemoryKernel :
    PositiveDefiniteOnReal cauchyHalfExponentialMemoryKernel :=
  GaloisForLFunctions.RHTower.positiveDefiniteOnReal_cauchyHalfExponentialKernel

/-! ## Julia equilibrium attenuation memory -/

def juliaDefectMemoryKernel (t : ℝ) : ℂ :=
  (_root_.HTGeometry.juliaDefectAttenuationKernel t : ℂ)

theorem juliaDefectMemoryKernel_neg (t : ℝ) :
    juliaDefectMemoryKernel (-t) = star (juliaDefectMemoryKernel t) := by
  rw [juliaDefectMemoryKernel, juliaDefectMemoryKernel,
    _root_.HTGeometry.juliaDefectAttenuationKernel_neg]
  apply Complex.ext <;> simp

theorem norm_juliaDefectMemoryKernel_le_zero (t : ℝ) :
    ‖juliaDefectMemoryKernel t‖ ≤ 1 := by
  rw [juliaDefectMemoryKernel, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (_root_.HTGeometry.juliaDefectAttenuationKernel_pos t)]
  exact _root_.HTGeometry.juliaDefectAttenuationKernel_le_one t

theorem positiveDefiniteOnReal_juliaDefectMemoryKernel :
    PositiveDefiniteOnReal juliaDefectMemoryKernel :=
  _root_.HTGeometry.positiveDefiniteOnReal_juliaDefectAttenuationKernel

end

end GaloisForLFunctions.HTGeometry

