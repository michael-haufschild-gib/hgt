import GaloisForLFunctions.RHTower.SymmetricShiftEulerDiscrepancy
import GaloisForLFunctions.RHTower.EulerSupportEnergyUncertainty

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The logarithmic symmetric-shift Euler discrepancy at a prime-power layer. -/
def symmetricShiftEulerPrimePowerDiscrepancy
    {S : Set Nat.Primes} (a : SymmetricPositiveShift) (z : S × ℕ) : ℝ :=
  symmetricShiftEulerPrimeDiscrepancy
    ⟨a.1 * ((z.2 : ℝ) + 1), mul_pos a.2 (by positivity)⟩ z.1.1

/-- The weighted prime-power discrepancy at real abscissa `σ`. -/
def symmetricShiftEulerPrimePowerDiscrepancyTerm
    {S : Set Nat.Primes} (a : SymmetricPositiveShift) (sigma : ℝ) (z : S × ℕ) : ℝ :=
  symmetricShiftEulerPrimePowerDiscrepancy a z *
    Real.exp (-(RHTower.primePowerMu z) * sigma) * RHTower.primePowerWeight z

/-- Every weighted symmetric-shift prime-power discrepancy is nonnegative. -/
theorem symmetricShiftEulerPrimePowerDiscrepancyTerm_nonneg
    {S : Set Nat.Primes} (a : SymmetricPositiveShift) (sigma : ℝ) (z : S × ℕ) :
    0 ≤ symmetricShiftEulerPrimePowerDiscrepancyTerm a sigma z := by
  unfold symmetricShiftEulerPrimePowerDiscrepancyTerm symmetricShiftEulerPrimePowerDiscrepancy
  exact mul_nonneg
    (mul_nonneg (symmetricShiftEulerPrimeDiscrepancy_nonneg _ _) (Real.exp_nonneg _))
    (RHTower.primePowerWeight_nonneg _)

/-- The full prime-power coefficient is bounded by the prime-power support at shifted abscissa. -/
theorem symmetricShiftEulerPrimePowerDiscrepancyTerm_le_support
    {S : Set Nat.Primes} (a : SymmetricPositiveShift) (sigma : ℝ) (z : S × ℕ) :
    symmetricShiftEulerPrimePowerDiscrepancyTerm a sigma z ≤
      Real.exp (-(RHTower.primePowerMu z) * (sigma - a.1)) *
        RHTower.primePowerWeight z := by
  let b : SymmetricPositiveShift :=
    ⟨a.1 * ((z.2 : ℝ) + 1), mul_pos a.2 (by positivity)⟩
  have hcoeff : symmetricShiftEulerPrimePowerDiscrepancy a z ≤
      ((z.1.1.1 : ℕ) : ℝ) ^ (a.1 * ((z.2 : ℝ) + 1)) := by
    simpa [symmetricShiftEulerPrimePowerDiscrepancy, b] using
      symmetricShiftEulerPrimeDiscrepancy_le_dominant b z.1.1
  have hbase : (0 : ℝ) < ((z.1.1.1 : ℕ) : ℝ) := by
    exact_mod_cast z.1.1.2.pos
  have hweight : 0 ≤ RHTower.primePowerWeight z := RHTower.primePowerWeight_nonneg z
  unfold symmetricShiftEulerPrimePowerDiscrepancyTerm
  calc
    symmetricShiftEulerPrimePowerDiscrepancy a z *
          Real.exp (-(RHTower.primePowerMu z) * sigma) * RHTower.primePowerWeight z ≤
        (((z.1.1.1 : ℕ) : ℝ) ^ (a.1 * ((z.2 : ℝ) + 1)) *
          Real.exp (-(RHTower.primePowerMu z) * sigma)) * RHTower.primePowerWeight z := by
      gcongr
    _ = Real.exp (-(RHTower.primePowerMu z) * (sigma - a.1)) *
          RHTower.primePowerWeight z := by
      rw [RHTower.exp_primePowerMu z sigma, RHTower.exp_primePowerMu z (sigma - a.1),
        ← Real.rpow_add hbase]
      congr 2
      ring

/-- Every prime support with its shifted prime series summable has a summable full discrepancy. -/
theorem summable_symmetricShiftEulerPrimePowerDiscrepancyTerm_of_lt
    {S : Set Nat.Primes} (a : SymmetricPositiveShift) {sigma : ℝ} (hsigma : 1 + a.1 < sigma)
    (hbase : Summable fun p : S => ((p.1.1 : ℕ) : ℝ) ^ (-(sigma - a.1))) :
    Summable (fun z : S × ℕ => symmetricShiftEulerPrimePowerDiscrepancyTerm a sigma z) := by
  let u : ℝ := sigma - a.1
  have hu : 0 < u := by dsimp [u]; linarith
  have hbase' : Summable (fun p : S => ((p.1.1 : ℕ) : ℝ) ^ (-u)) := by
    simpa [u] using hbase
  have hsupport := RHTower.summable_primePowerSupport (S := S) hu hbase'
  refine Summable.of_nonneg_of_le
    (symmetricShiftEulerPrimePowerDiscrepancyTerm_nonneg a sigma) ?_ hsupport
  intro z
  simpa [u] using symmetricShiftEulerPrimePowerDiscrepancyTerm_le_support a sigma z

end

end GaloisForLFunctions.RHTower
