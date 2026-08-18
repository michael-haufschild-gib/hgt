import GaloisForLFunctions.RHTower.CCMRestrictedWeilActualHeadPrimePolarGammaProducer
import GaloisForLFunctions.RHTower.CCMGuinandWeilPrimeEntryWallFieldWeld
import GaloisForLFunctions.RHTower.SuzukiWallFieldAntidiagonalGramLift
import GaloisForLFunctions.HTGeometry.ShortcutSpectralPhase

/-!
# Actual-head signed producer on the reflected wall Gram

The Route O prime translation loss and Suzuki's far-hinge current are two polarizations of one
source block, not two operators that must be identified.  For an integer atom `n`, put

`Omega_n(xi) = sqrt(Lambda(n) / sqrt(n)) exp(I pi xi log n)`.

Its reflected chord has energy

`|Omega_n(xi) - Omega_n(-xi)|^2
  = Lambda(n) / sqrt(n) * (2 - 2 cos(2 pi xi log n))`.

At every genuine prime power this abstract Mellin wall is definitionally the literal Suzuki wall
field at height `2 pi xi`.  Thus the chord is the `(1,-1)` quadratic polarization of Suzuki's
positive two-height Gram, while the far-hinge current is the orthogonal imaginary polarization of
the same anti-diagonal.  Plancherel then identifies the integral of this wall-chord energy against
the actual head spectral density with the literal prime translation-defect energy.

Replacing the prime term in the completed-error producer by that Gram energy gives a lawful
single-source prime--polar--Gamma producer.  It neither substitutes a common-clock head nor
separates the signed cancellation.  No RH premise, estimate, numerical computation, or added
axiom is used.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct InnerProductSpace BigOperators ComplexConjugate

noncomputable section

namespace RHTower

/-! ## Universal Mellin wall and its reflected chord -/

/-- Square-root Mellin wall carried by one von-Mangoldt atom. -/
def ccmActualHeadMellinWallField (xi : ℝ) (n : ℕ) : ℂ :=
  (Real.sqrt (criticalMellinAtomWeight n) : ℂ) *
    Complex.exp ((((Real.pi * xi * Real.log n : ℝ) : ℂ) * I))

/-- Functional-equation reflected chord of one Mellin wall atom. -/
def ccmActualHeadMellinWallChord (xi : ℝ) (n : ℕ) : ℂ :=
  ccmActualHeadMellinWallField xi n - ccmActualHeadMellinWallField (-xi) n

theorem criticalMellinAtomWeight_nonneg (n : ℕ) :
    0 ≤ criticalMellinAtomWeight n := by
  unfold criticalMellinAtomWeight
  exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    (ArithmeticFunction.vonMangoldt_nonneg (n := n))

/-- Exact cosine-defect energy of the reflected Mellin wall chord. -/
theorem normSq_ccmActualHeadMellinWallChord (xi : ℝ) (n : ℕ) :
    normSq (ccmActualHeadMellinWallChord xi n) =
      criticalMellinAtomWeight n *
        (2 - 2 * Real.cos (2 * Real.pi * xi * Real.log n)) := by
  rw [ccmActualHeadMellinWallChord, ccmActualHeadMellinWallField,
    ccmActualHeadMellinWallField, ← mul_sub]
  rw [Complex.normSq_mul, Complex.normSq_ofReal]
  rw [Complex.normSq_eq_norm_sq]
  rw [GaloisForLFunctions.HTGeometry.normSq_expI_sub]
  rw [← pow_two (Real.sqrt (criticalMellinAtomWeight n)),
    Real.sq_sqrt (criticalMellinAtomWeight_nonneg n)]
  congr 2
  congr 1
  ring_nf

/-! ## Literal Suzuki prime-power identification -/

/-- At a prime power, the Mellin wall is exactly Suzuki's observer-free critical wall field. -/
theorem ccmActualHeadMellinWallField_primePower_eq_suzukiCriticalWallField
    (xi : ℝ) (p : Nat.Primes) (e : ℕ) :
    ccmActualHeadMellinWallField xi (xiGammaEulerValuationNat (p, e)) =
      suzukiCriticalWallField (2 * Real.pi * xi) p e := by
  have hamp :
      Real.sqrt (criticalMellinAtomWeight (xiGammaEulerValuationNat (p, e))) =
        suzukiCriticalEntryWallBareAmplitude p e := by
    rw [criticalMellinAtomWeight_primePower_eq_sq_suzukiCriticalEntryWallBareAmplitude]
    exact Real.sqrt_sq (suzukiCriticalEntryWallBareAmplitude_pos p e).le
  rw [ccmActualHeadMellinWallField, hamp,
    suzukiCriticalWallField_eq_bareAmplitude_mul_kernel,
    suzukiOscillatoryKernel_primePowerEntryWall_eq_criticalPhase]
  congr 2
  push_cast
  ring

/-- The reflected Mellin chord is the literal two-height Suzuki wall chord. -/
theorem ccmActualHeadMellinWallChord_primePower_eq_suzukiCriticalWallField_sub
    (xi : ℝ) (p : Nat.Primes) (e : ℕ) :
    ccmActualHeadMellinWallChord xi (xiGammaEulerValuationNat (p, e)) =
      suzukiCriticalWallField (2 * Real.pi * xi) p e -
        suzukiCriticalWallField (-(2 * Real.pi * xi)) p e := by
  rw [ccmActualHeadMellinWallChord,
    ccmActualHeadMellinWallField_primePower_eq_suzukiCriticalWallField,
    ccmActualHeadMellinWallField_primePower_eq_suzukiCriticalWallField]
  congr 2
  ring

/-- Real and imaginary anti-diagonal polarizations of the common Suzuki wall Gram. -/
theorem suzukiCriticalWallFieldGramKernel_antidiagonal_re_im
    (t : ℝ) (p : Nat.Primes) (e : ℕ) :
    let n := xiGammaEulerValuationNat (p, e)
    let w := ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ)
    (suzukiCriticalWallFieldGramKernel t (-t) p e).re =
        w * Real.cos (t * Real.log n) ∧
      (suzukiCriticalWallFieldGramKernel t (-t) p e).im =
        w * Real.sin (t * Real.log n) := by
  dsimp only
  rw [suzukiCriticalWallFieldGramKernel_antidiagonal]
  simp only [suzukiOscillatoryKernel]
  have harg :
      ((Real.log (xiGammaEulerValuationNat (p, e) : ℝ) : ℂ) *
          (I * (t : ℂ))) =
        (((t * Real.log (xiGammaEulerValuationNat (p, e) : ℝ) : ℝ) : ℂ) * I) := by
    push_cast
    ring
  rw [harg, ← Complex.ofReal_div]
  constructor
  · rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    ring
  · rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    ring

/-- **Common-block law.** Route O's prime translation loss is the real chord polarization of the
same positive anti-diagonal Gram whose imaginary polarization supplies Suzuki's far current. -/
theorem normSq_suzukiCriticalWallField_reflectedChord_eq_diagonal_sub_re_antidiagonal
    (xi : ℝ) (p : Nat.Primes) (e : ℕ) :
    normSq
        (suzukiCriticalWallField (2 * Real.pi * xi) p e -
          suzukiCriticalWallField (-(2 * Real.pi * xi)) p e) =
      2 * (ArithmeticFunction.vonMangoldt (xiGammaEulerValuationNat (p, e)) /
          Real.sqrt (xiGammaEulerValuationNat (p, e) : ℝ)) -
        2 * (suzukiCriticalWallFieldGramKernel
          (2 * Real.pi * xi) (-(2 * Real.pi * xi)) p e).re := by
  rw [← ccmActualHeadMellinWallChord_primePower_eq_suzukiCriticalWallField_sub,
    normSq_ccmActualHeadMellinWallChord]
  rw [criticalMellinAtomWeight_primePower_eq_sq_suzukiCriticalEntryWallBareAmplitude,
    sq_suzukiCriticalEntryWallBareAmplitude_eq_vonMangoldt_div_sqrt]
  have hpolar :=
    (suzukiCriticalWallFieldGramKernel_antidiagonal_re_im
      (2 * Real.pi * xi) p e).1
  rw [hpolar]
  ring

/-! ## Plancherel lift to one actual head -/

/-- One von-Mangoldt translation loss is exactly integrated reflected-wall Gram energy against
the spectral density of the same actual physical head. -/
theorem integral_ccmActualHeadMellinWallChord_eq_translationDefect
    (n : ℕ) (g : SoninL2) :
    (∫ xi : ℝ,
        normSq (ccmActualHeadMellinWallChord xi n) * ‖g xi‖ ^ 2) =
      criticalMellinAtomWeight n *
        ccmActualHeadTranslationDefect (Real.log n) (fourierUnitary.symm g) := by
  rw [ccmActualHeadTranslationDefect_fourierUnitary_symm, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with xi
  rw [normSq_ccmActualHeadMellinWallChord]
  have harg :
      2 * Real.pi * xi * Real.log n =
        2 * Real.pi * Real.log n * xi := by ring
  rw [harg]
  ring

/-- Finite sum of reflected wall-chord energies on the actual head spectrum. -/
def ccmActualHeadPrimeWallChordEnergy
    (a : SuzukiPositiveAperture) (g : SoninL2) : ℝ :=
  ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))),
    ∫ xi : ℝ,
      normSq (ccmActualHeadMellinWallChord xi n) * ‖g xi‖ ^ 2

/-- The full finite prime defect is exactly the reflected wall-Gram energy of the literal
form-domain head. -/
theorem ccmActualHeadPrimeWallChordEnergy_formDomain
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    ccmActualHeadPrimeWallChordEnergy a (ccmArchimedeanWeightedToL2 u.1) =
      ccmPrimeTranslationDefectEnergy a
        (ccmArchimedeanFormToAperture a u) := by
  unfold ccmActualHeadPrimeWallChordEnergy ccmPrimeTranslationDefectEnergy
  apply Finset.sum_congr rfl
  intro n hn
  rw [integral_ccmActualHeadMellinWallChord_eq_translationDefect]
  unfold ccmActualHeadTranslationDefect
  rw [ccmArchimedeanFormToAperture_val_eq_fourierUnitary_symm]

/-! ## Cancellation-preserving wall-Gram producer -/

/-- Signed prime--polar--Gamma producer with the prime channel kept as the positive reflected
two-height wall Gram of the same actual head spectral density. -/
def ccmRestrictedWeilActualHeadWallGramSignedProducer
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) : ℝ :=
  let f := ccmArchimedeanFormToAperture a u
  let g := ccmArchimedeanWeightedToL2 u.1
  2 * gammaHardyPhaseRate 0 * ‖f‖ ^ 2 +
    ccmActualHeadGammaAutocorrelationEnergy (f : SoninL2) +
    criticalMellinCompletedError (2 * a.1) *
      ccmActualHeadTranslationDefect (2 * a.1) f.1 +
    ccmActualHeadPrimeWallChordEnergy a g -
      ccmContinuousPolarTranslationDefectEnergy a f

/-- The wall-Gram producer is exactly the literal prime--polar--Gamma producer, not a surrogate
operator or a separately positive replacement. -/
theorem ccmRestrictedWeilActualHeadWallGramSignedProducer_eq_primePolarGammaProducer
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilActualHeadWallGramSignedProducer a u =
      ccmRestrictedWeilActualHeadPrimePolarGammaProducer a u := by
  rw [ccmRestrictedWeilActualHeadWallGramSignedProducer,
    ccmRestrictedWeilActualHeadPrimePolarGammaProducer]
  rw [ccmActualHeadPrimeWallChordEnergy_formDomain]
  unfold ccmActualHeadCompletedErrorQuadrature
  ring

/-- Exact source law for the new common wall-Gram polarization. -/
theorem ccmRestrictedWeilActualHeadWallGramSignedProducer_eq_sourceQuadratic
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilActualHeadWallGramSignedProducer a u =
      ccmRestrictedWeilSourceQuadratic a u := by
  rw [ccmRestrictedWeilActualHeadWallGramSignedProducer_eq_primePolarGammaProducer,
    ccmRestrictedWeilActualHeadPrimePolarGammaProducer_eq_sourceQuadratic]

/-- On canonical finite Gamma--Slepian heads the signed wall-Gram producer is the true ground
part plus precisely the already-certified nonnegative vanishing tail. -/
theorem ccmRestrictedWeilCanonicalGroundHead_wallGramSignedProducer_eq_ground_add_tail
    (a : SuzukiPositiveAperture) (n : ℕ) :
    ccmRestrictedWeilActualHeadWallGramSignedProducer a
        (ccmRestrictedWeilCanonicalGroundHead a n) =
      ccmRestrictedWeilGroundEnergy a *
          ‖ccmArchimedeanFormToAperture a
            (ccmRestrictedWeilCanonicalGroundHead a n)‖ ^ 2 +
        ccmRestrictedWeilCanonicalGroundHeadDefect a n := by
  rw [ccmRestrictedWeilActualHeadWallGramSignedProducer_eq_primePolarGammaProducer,
    ccmRestrictedWeilCanonicalGroundHead_primePolarGammaProducer_eq_ground_add_tail]

/-- Literal reverse-prime control is exactly nonnegativity of the new source-faithful wall-Gram
producer. -/
theorem ccmRestrictedWeilCanonicalGroundHead_reversePrimeBound_iff_wallGramSignedProducer_nonneg
    (a : SuzukiPositiveAperture) (n : ℕ) :
    CCMRestrictedWeilCanonicalGroundHeadReversePrimeBound a n ↔
      0 ≤ ccmRestrictedWeilActualHeadWallGramSignedProducer a
        (ccmRestrictedWeilCanonicalGroundHead a n) := by
  rw [ccmRestrictedWeilCanonicalGroundHead_reversePrimeBound_iff_primePolarGammaProducer_nonneg,
    ccmRestrictedWeilActualHeadWallGramSignedProducer_eq_primePolarGammaProducer]

end RHTower
