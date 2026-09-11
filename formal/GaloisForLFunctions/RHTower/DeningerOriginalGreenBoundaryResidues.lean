import GaloisForLFunctions.RHTower.DeningerOriginalGreenPoleCalculus
import GaloisForLFunctions.RHTower.DeningerDampedOriginalGreenMellin
import GaloisForLFunctions.RHTower.DeningerL1LocalGreenBoundary

/-!
# The same Green primitive: every pole residue is an original boundary mode

The actual damping-two source has a meromorphic Green transform on its
original strip. At every original prime harmonic, its simple-pole residue
equals the corresponding Fourier coefficient of the complete two-ended
cellwise L1 jump. The source, orientation and cell measure are unchanged.
-/

open Complex Filter Topology MeasureTheory FourierTransform
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

private theorem original_prime_period_pos (p : Nat.Primes) : 0 < Real.log (p : ℕ) :=
  Real.log_pos (by exact_mod_cast p.property.one_lt)

/-- Meromorphic continuation of the actual original Green transform, with its denominator retained. -/
def deningerDampingTwoOriginalGreenContinuation (p : Nat.Primes) (s : ℂ) : ℂ :=
  deningerMeyerStrongLogMellin (deningerDampedLogSource ⟨2,by norm_num⟩) s /
    deningerOriginalGreenDenominator (Real.log (p : ℕ)) s

/-- The continuation is the literal integral of the same primitive wherever its weight is admitted. -/
theorem deningerDampingTwoOriginalGreenContinuation_eq_integral (p : Nat.Primes)
    (s : ℂ) (hs : 0 < s.re) (hs1 : s.re < 2) :
    deningerDampingTwoOriginalGreenContinuation p s =
      deningerMeyerStrongLogMellin (deningerDampedOriginalPrimeGreen ⟨2,by norm_num⟩ p) s := by
  rw [deningerDampedOriginalPrimeGreen_mellin _ p s hs (by dsimp; linarith) hs1]
  simp only [deningerDampingTwoOriginalGreenContinuation, deningerOriginalGreenDenominator,
    deningerOriginalGreen_prime_weight]

/-- Original source analyticity supplies meromorphic admission on both sides of the boundary. -/
theorem deningerDampingTwoOriginalGreenContinuation_meromorphicOn (p : Nat.Primes) :
    MeromorphicOn (deningerDampingTwoOriginalGreenContinuation p)
      {s : ℂ | -1 < s.re ∧ s.re < 2} := by
  intro s hs
  have hN := analyticOnNhd_deningerDampedLogSource_mellin ⟨2,by norm_num⟩ s
    ⟨by change 1-(2 : ℝ) < s.re; linarith [hs.1],hs.2⟩
  have hD : AnalyticAt ℂ (deningerOriginalGreenDenominator (Real.log (p : ℕ))) s := by
    unfold deningerOriginalGreenDenominator
    fun_prop
  exact hN.meromorphicAt.div hD.meromorphicAt

private theorem source_analytic_at_original_pole (L : ℝ) (k : ℤ) :
    AnalyticAt ℂ (deningerMeyerStrongLogMellin (deningerDampedLogSource ⟨2,by norm_num⟩))
      (deningerOriginalGreenPole L k) := by
  apply analyticOnNhd_deningerDampedLogSource_mellin
  change 1-(2 : ℝ) < (deningerOriginalGreenPole L k).re ∧
    (deningerOriginalGreenPole L k).re < 2
  rw [deningerOriginalGreenPole_re]
  norm_num

private theorem source_nonzero_at_original_pole (L : ℝ) (k : ℤ) :
    deningerMeyerStrongLogMellin (deningerDampedLogSource ⟨2,by norm_num⟩)
      (deningerOriginalGreenPole L k) ≠ 0 := by
  apply deningerDampedLogSource_mellin_ne_zero <;>
    simp only [deningerOriginalGreenPole_re] <;> norm_num

/-- Every original prime harmonic is a simple pole of the actual continued primitive. -/
theorem deningerDampingTwoOriginalGreenContinuation_pole_order (p : Nat.Primes) (k : ℤ) :
    meromorphicOrderAt (deningerDampingTwoOriginalGreenContinuation p)
      (deningerOriginalGreenPole (Real.log (p : ℕ)) k) = (-1 : ℤ) := by
  exact deningerOriginalGreen_pole_order (original_prime_period_pos p).ne' k
    (source_analytic_at_original_pole _ k) (source_nonzero_at_original_pole _ k)

/-- The Laurent residue is the original, unnormalized source Fourier reading divided by its period. -/
theorem deningerDampingTwoOriginalGreenContinuation_residue_fourier (p : Nat.Primes) (k : ℤ) :
    laurentCoeff (deningerDampingTwoOriginalGreenContinuation p)
      (deningerOriginalGreenPole (Real.log (p : ℕ)) k) (-1) =
        (1/Real.log (p : ℕ)) • 𝓕 (deningerDampedLogSource ⟨2,by norm_num⟩)
          ((1/Real.log (p : ℕ)) * (k : ℝ)) := by
  change laurentCoeff (fun s =>
    deningerMeyerStrongLogMellin (deningerDampedLogSource ⟨2,by norm_num⟩) s /
      deningerOriginalGreenDenominator (Real.log (p : ℕ)) s)
    (deningerOriginalGreenPole (Real.log (p : ℕ)) k) (-1) = _
  rw [deningerOriginalGreen_laurentCoeff (original_prime_period_pos p).ne' k
      (source_analytic_at_original_pole _ k), deningerDampedLogSource_fourier_eq]
  simp only [deningerOriginalGreenPole, Complex.real_smul,
    div_eq_mul_inv, one_mul, Complex.ofReal_inv, mul_comm]

/-- Each residue is exactly the same mode of the complete two-ended Green jump. -/
theorem deningerDampingTwoOriginalGreenContinuation_residue_eq_jump (p : Nat.Primes) (k : ℤ) :
    laurentCoeff (deningerDampingTwoOriginalGreenContinuation p)
      (deningerOriginalGreenPole (Real.log (p : ℕ)) k) (-1) =
        fourierCoeffOn (original_prime_period_pos p)
          (deningerL1OriginalBoundaryJump deningerDampingTwo_source_endpoint_integrable.1
            (Real.log (p : ℕ))) k := by
  rw [deningerDampingTwoOriginalGreenContinuation_residue_fourier,
    deningerL1OriginalBoundaryJump_coefficient]

/-- No original boundary mode is removed by passing to the continued Green transform. -/
theorem deningerDampingTwoOriginalGreenContinuation_residue_ne_zero (p : Nat.Primes) (k : ℤ) :
    laurentCoeff (deningerDampingTwoOriginalGreenContinuation p)
      (deningerOriginalGreenPole (Real.log (p : ℕ)) k) (-1) ≠ 0 := by
  rw [deningerDampingTwoOriginalGreenContinuation_residue_eq_jump]
  exact deningerDampingTwo_originalGreenJump_coefficient_ne_zero p k

/-- An analytic extension at an original harmonic would contradict its retained boundary mode. -/
theorem deningerDampingTwoOriginalGreenContinuation_not_analyticAt (p : Nat.Primes) (k : ℤ) :
    ¬ AnalyticAt ℂ (deningerDampingTwoOriginalGreenContinuation p)
      (deningerOriginalGreenPole (Real.log (p : ℕ)) k) := by
  intro h
  exact deningerDampingTwoOriginalGreenContinuation_residue_ne_zero p k
    (laurentCoeff_eq_zero_of_analyticAt h (by norm_num))

end RHTower
