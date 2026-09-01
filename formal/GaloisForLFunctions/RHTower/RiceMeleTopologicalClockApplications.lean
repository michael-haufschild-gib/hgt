import GaloisForLFunctions.RHTower.PrimeAFCircleOperatorKOne
import GaloisForLFunctions.RHTower.WindingHomotopy
import GaloisForLFunctions.RHTower.RelationalClockLocalHorizonLaw
import GaloisForLFunctions.HTGeometry.RabiHatanoNelsonAlgebra
import GaloisForLFunctions.HTGeometry.DecoupledEvolutionFactorization
import GaloisForLFunctions.HTGeometry.HLSPhysicalAssumptions

open scoped BigOperators Matrix
open Complex

noncomputable section

namespace GaloisForLFunctions.RHTower.TopologicalClockApplications

def riceMeleDx (J delta k : ℝ) : ℝ :=
  J * ((1 + delta) + (1 - delta) * Real.cos k)

def riceMeleDy (J delta k : ℝ) : ℝ :=
  J * (1 - delta) * Real.sin k

def riceMeleNormSq (J delta Delta k : ℝ) : ℝ :=
  riceMeleDx J delta k ^ 2 + riceMeleDy J delta k ^ 2 + Delta ^ 2

theorem riceMeleNormSq_eq (J delta Delta k : ℝ) :
    riceMeleNormSq J delta Delta k =
      Delta ^ 2 + 2 * J ^ 2 *
        (1 + delta ^ 2 + (1 - delta ^ 2) * Real.cos k) := by
  simp only [riceMeleNormSq, riceMeleDx, riceMeleDy]
  have hsin : Real.sin k ^ 2 = 1 - Real.cos k ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq k]
  calc
    (J * (1 + delta + (1 - delta) * Real.cos k)) ^ 2 +
          (J * (1 - delta) * Real.sin k) ^ 2 + Delta ^ 2 =
        Delta ^ 2 + J ^ 2 *
          ((1 + delta + (1 - delta) * Real.cos k) ^ 2 +
            (1 - delta) ^ 2 * Real.sin k ^ 2) := by ring
    _ = Delta ^ 2 + J ^ 2 *
          ((1 + delta + (1 - delta) * Real.cos k) ^ 2 +
            (1 - delta) ^ 2 * (1 - Real.cos k ^ 2)) := by rw [hsin]
    _ = Delta ^ 2 + 2 * J ^ 2 *
          (1 + delta ^ 2 + (1 - delta ^ 2) * Real.cos k) := by ring

theorem riceMeleNormSq_even (J delta Delta k : ℝ) :
    riceMeleNormSq J delta Delta (-k) = riceMeleNormSq J delta Delta k := by
  simp [riceMeleNormSq, riceMeleDx, riceMeleDy, Real.cos_neg, Real.sin_neg]

def riceMeleOffDiagonal (J delta k : ℝ) : ℂ :=
  ((J * (1 + delta) : ℝ) : ℂ) +
    ((J * (1 - delta) : ℝ) : ℂ) * Complex.exp ((k : ℂ) * Complex.I)

theorem riceMeleOffDiagonal_eq_gaugedDirectionalHopping (J delta k : ℝ) :
    riceMeleOffDiagonal J delta k =
      Complex.exp (((k / 2 : ℝ) : ℂ) * Complex.I) *
        HTGeometry.RabiHatanoNelson.directionalHoppingSymbol J (J * delta) (-k / 2) := by
  let x : ℂ := (((k / 2 : ℝ) : ℂ) * Complex.I)
  have hinv : Complex.exp x * Complex.exp (-x) = 1 := by
    rw [← Complex.exp_add]
    simp
  have hsq : Complex.exp x * Complex.exp x = Complex.exp ((k : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    dsimp [x]
    push_cast
    ring
  have hneg : (((-k / 2 : ℝ) : ℂ) * Complex.I) = -x := by
    dsimp [x]
    push_cast
    ring
  have hnegneg : -(((-k / 2 : ℝ) : ℂ)) * Complex.I = x := by
    dsimp [x]
    push_cast
    ring
  rw [riceMeleOffDiagonal, HTGeometry.RabiHatanoNelson.directionalHoppingSymbol]
  rw [hneg, hnegneg]
  change _ = Complex.exp x *
    (((J + J * delta : ℝ) : ℂ) * Complex.exp (-x) +
      ((J - J * delta : ℝ) : ℂ) * Complex.exp x)
  calc
    _ = ((J + J * delta : ℝ) : ℂ) * 1 +
        ((J - J * delta : ℝ) : ℂ) * Complex.exp ((k : ℂ) * Complex.I) := by
      push_cast
      ring
    _ = ((J + J * delta : ℝ) : ℂ) *
          (Complex.exp x * Complex.exp (-x)) +
        ((J - J * delta : ℝ) : ℂ) *
          (Complex.exp x * Complex.exp x) := by rw [hinv, hsq]
    _ = Complex.exp x *
        (((J + J * delta : ℝ) : ℂ) * Complex.exp (-x) +
          ((J - J * delta : ℝ) : ℂ) * Complex.exp x) := by ring

def normalizedPumpDelta (tau : ℝ) : ℝ := (1 / 2 : ℝ) * Real.cos tau

def normalizedPumpMass (tau : ℝ) : ℝ := (1 / 2 : ℝ) * Real.sin tau

theorem normalizedPump_normSq_decomposition (k tau : ℝ) :
    riceMeleNormSq 1 (normalizedPumpDelta tau) (normalizedPumpMass tau) k =
      (1 / 4 : ℝ) + (3 / 4 : ℝ) * Real.cos tau ^ 2 +
        2 * (1 - (1 / 4 : ℝ) * Real.cos tau ^ 2) * (1 + Real.cos k) := by
  rw [riceMeleNormSq_eq]
  simp only [normalizedPumpDelta, normalizedPumpMass]
  nlinarith [Real.sin_sq_add_cos_sq tau]

theorem normalizedPump_uniform_gap_sq (k tau : ℝ) :
    (1 / 4 : ℝ) ≤
      riceMeleNormSq 1 (normalizedPumpDelta tau) (normalizedPumpMass tau) k := by
  rw [normalizedPump_normSq_decomposition]
  have hcosSq : Real.cos tau ^ 2 ≤ 1 := by
    nlinarith [Real.neg_one_le_cos tau, Real.cos_le_one tau]
  have hfactor : 0 ≤ 1 - (1 / 4 : ℝ) * Real.cos tau ^ 2 := by nlinarith
  have hbase : 0 ≤ 1 + Real.cos k := by linarith [Real.neg_one_le_cos k]
  have hproduct := mul_nonneg hfactor hbase
  nlinarith [sq_nonneg (Real.cos tau)]

theorem normalizedPump_gap_minimizer :
    riceMeleNormSq 1 (normalizedPumpDelta (Real.pi / 2))
      (normalizedPumpMass (Real.pi / 2)) Real.pi = (1 / 4 : ℝ) := by
  simp [riceMeleNormSq, riceMeleDx, riceMeleDy,
    normalizedPumpDelta, normalizedPumpMass]
  norm_num

def normalizedPumpGap (k tau : ℝ) : ℝ :=
  2 * Real.sqrt
    (riceMeleNormSq 1 (normalizedPumpDelta tau) (normalizedPumpMass tau) k)

theorem normalizedPumpGap_ge_one (k tau : ℝ) : 1 ≤ normalizedPumpGap k tau := by
  have hsqrt := Real.sqrt_le_sqrt (normalizedPump_uniform_gap_sq k tau)
  have hquarter : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by norm_num
  rw [hquarter] at hsqrt
  dsimp [normalizedPumpGap]
  linarith

theorem normalizedPumpGap_minimizer :
    normalizedPumpGap Real.pi (Real.pi / 2) = 1 := by
  rw [normalizedPumpGap, normalizedPump_gap_minimizer]
  norm_num

def linearGeometricPhase (C : ℤ) (k : ℝ) : ℝ := -(C : ℝ) * k

theorem linearGeometricPhase_endpoint_jump (C : ℤ) :
    linearGeometricPhase C Real.pi - linearGeometricPhase C (-Real.pi) =
      -2 * Real.pi * (C : ℝ) := by
  simp [linearGeometricPhase]
  ring

def phaseWithPeriodicResidual (C : ℤ) (a b c k : ℝ) : ℝ :=
  linearGeometricPhase C k + a * Real.cos k + b * Real.sin k + c

theorem periodicResidual_preserves_endpoint_jump (C : ℤ) (a b c : ℝ) :
    phaseWithPeriodicResidual C a b c Real.pi -
        phaseWithPeriodicResidual C a b c (-Real.pi) =
      -2 * Real.pi * (C : ℝ) := by
  simp [phaseWithPeriodicResidual, linearGeometricPhase, Real.cos_neg, Real.sin_neg]
  ring

def clockMomentum (C : ℤ) : HTGeometry.HLSMinkowskiVector :=
  Pi.single 0 (C : ℝ)

def clockTranslation (k : ℝ) : HTGeometry.HLSMinkowskiVector :=
  Pi.single 0 k

theorem linearGeometricPhase_as_translation_character (C : ℤ) (k : ℝ) :
    HTGeometry.hlsTranslationPhase (clockMomentum C) (clockTranslation k) =
      Complex.exp ((linearGeometricPhase C k : ℂ) * Complex.I) := by
  simp [HTGeometry.hlsTranslationPhase, HTGeometry.hlsMinkowskiPairing,
    clockMomentum, clockTranslation, linearGeometricPhase]
  congr 1
  ring

theorem unitClock_covariant (s t : ℝ) :
    RHTower.ParityForecast.spectralTimeEvolution (by norm_num : (0 : ℝ) < 1) 1 s
        (RHTower.ParityForecast.scaledInterpolatedClockAt 1 1 0 t) =
      RHTower.ParityForecast.scaledInterpolatedClockAt 1 1 0 (s + t) := by
  exact RHTower.ParityForecast.spectralTimeEvolution_scaledInterpolatedClockAt
    (by norm_num) 1 0 s t

theorem finTwoClockSystem_factorizes
    (A B : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ)
    (u v : Fin 2 → ℂ) :
    HTGeometry.unitaryEvolution (HTGeometry.kroneckerSum A B) t *ᵥ
        HTGeometry.binaryTensorVec u v =
      HTGeometry.binaryTensorVec (HTGeometry.unitaryEvolution A t *ᵥ u)
        (HTGeometry.unitaryEvolution B t *ᵥ v) := by
  exact HTGeometry.unitaryEvolution_kroneckerSum_mulVec_tensorVec A B t u v

def windowedIntegerLoop (z : ℤ) (a : ℝ) : PrimeQuasiLocalCharge.ScalarCircleLoop where
  toFun := fun t => Complex.exp (((a * Real.cos t : ℝ) : ℂ)) *
    PrimeQuasiLocalCharge.scalarCircleLoopOfInt z t
  isLoop := by
    refine ⟨Complex.continuous_exp.comp
        (Complex.continuous_ofReal.comp (continuous_const.mul Real.continuous_cos)) |>.mul
          (PrimeQuasiLocalCharge.scalarCircleLoopOfInt z).isLoop.continuous,
      fun t => mul_ne_zero (Complex.exp_ne_zero _)
        ((PrimeQuasiLocalCharge.scalarCircleLoopOfInt z).isLoop.nonzero t), ?_⟩
    simp [(PrimeQuasiLocalCharge.scalarCircleLoopOfInt z).isLoop.closed]

theorem windowedIntegerLoop_winding (z : ℤ) (a : ℝ) :
    PrimeQuasiLocalCharge.scalarCircleLoopWinding (windowedIntegerLoop z a) = z := by
  let H : ℝ → ℝ → ℂ := fun sigma t =>
    Complex.exp ((((sigma * a) * Real.cos t : ℝ) : ℂ)) *
      PrimeQuasiLocalCharge.scalarCircleLoopOfInt z t
  have hHc : Continuous (fun p : ℝ × ℝ => H p.1 p.2) := by
    dsimp [H]
    fun_prop
  have hH0 : ∀ sigma t, H sigma t ≠ 0 := by
    intro sigma t
    exact mul_ne_zero (Complex.exp_ne_zero _)
      ((PrimeQuasiLocalCharge.scalarCircleLoopOfInt z).isLoop.nonzero t)
  have hHloop : ∀ sigma, H sigma 0 = H sigma (2 * Real.pi) := by
    intro sigma
    dsimp [H]
    simp [(PrimeQuasiLocalCharge.scalarCircleLoopOfInt z).isLoop.closed]
  have hw := RHTower.windingNumber_homotopy_invariant hHc hH0 hHloop 0 1
  have hstart : H 0 = (PrimeQuasiLocalCharge.scalarCircleLoopOfInt z).toFun := by
    funext t
    simp [H]
  have hend : H 1 = (windowedIntegerLoop z a).toFun := by
    funext t
    simp [H, windowedIntegerLoop]
  rw [hstart, hend] at hw
  change PrimeQuasiLocalCharge.scalarCircleLoopWinding
      (PrimeQuasiLocalCharge.scalarCircleLoopOfInt z) =
    PrimeQuasiLocalCharge.scalarCircleLoopWinding (windowedIntegerLoop z a) at hw
  rw [PrimeQuasiLocalCharge.scalarCircleLoopOfInt_winding] at hw
  exact hw.symm

theorem no_nonvanishing_homotopy_between_zero_and_unit_charge :
    ¬ ∃ H : ℝ → ℝ → ℂ,
      Continuous (fun p : ℝ × ℝ => H p.1 p.2) ∧
      (∀ sigma t, H sigma t ≠ 0) ∧
      (∀ sigma, H sigma 0 = H sigma (2 * Real.pi)) ∧
      (∀ t, H 0 t = PrimeQuasiLocalCharge.scalarCircleLoopOfInt 0 t) ∧
      (∀ t, H 1 t = PrimeQuasiLocalCharge.scalarCircleLoopOfInt 1 t) := by
  rintro ⟨H, hHc, hH0, hHloop, hstart, hend⟩
  have hw := RHTower.windingNumber_homotopy_invariant hHc hH0 hHloop 0 1
  rw [show H 0 = (PrimeQuasiLocalCharge.scalarCircleLoopOfInt 0).toFun from funext hstart,
    show H 1 = (PrimeQuasiLocalCharge.scalarCircleLoopOfInt 1).toFun from funext hend] at hw
  change PrimeQuasiLocalCharge.scalarCircleLoopWinding
      (PrimeQuasiLocalCharge.scalarCircleLoopOfInt 0) =
    PrimeQuasiLocalCharge.scalarCircleLoopWinding
      (PrimeQuasiLocalCharge.scalarCircleLoopOfInt 1) at hw
  rw [PrimeQuasiLocalCharge.scalarCircleLoopOfInt_winding,
    PrimeQuasiLocalCharge.scalarCircleLoopOfInt_winding] at hw
  norm_num at hw

def eightSamplePhase (j : ℕ) : ℝ := -(Real.pi / 2) * j

theorem eightSamplePhase_increment (j : ℕ) :
    eightSamplePhase (j + 1) - eightSamplePhase j = -(Real.pi / 2) := by
  simp [eightSamplePhase]
  ring

theorem eightSamplePhase_nyquist_safe (j : ℕ) :
    |eightSamplePhase (j + 1) - eightSamplePhase j| < Real.pi := by
  rw [eightSamplePhase_increment]
  rw [abs_neg, abs_of_pos (by linarith [Real.pi_pos] : 0 < Real.pi / 2)]
  linarith [Real.pi_pos]

theorem eightSamplePhase_total_increment :
    ∑ j ∈ Finset.range 8,
      (eightSamplePhase (j + 1) - eightSamplePhase j) = -4 * Real.pi := by
  simp_rw [eightSamplePhase_increment]
  norm_num
  ring

theorem eightSamplePhase_readout :
    (∑ j ∈ Finset.range 8,
      (eightSamplePhase (j + 1) - eightSamplePhase j)) /
        (2 * Real.pi) = -2 := by
  rw [eightSamplePhase_total_increment]
  apply (div_eq_iff (mul_ne_zero (by norm_num) Real.pi_ne_zero)).2
  ring

end GaloisForLFunctions.RHTower.TopologicalClockApplications

end
