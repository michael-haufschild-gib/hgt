import GaloisForLFunctions.RHTower.CCM.CCMCofinalFloorCriterion

/-!
# The square mass is positive whenever it is nonzero

The cofinal floor criterion carries the hypothesis that the normalising functional is strictly
positive wherever it is nonzero.  For the square mass this is not a hypothesis: it is the integral of
a square, hence nonnegative for every trial function, integrable or not.  The criterion therefore
holds with the hypothesis removed.
-/

open MeasureTheory

namespace GaloisForLFunctions.RHTower

/-- The square mass is nonnegative: it is the integral of a square. -/
theorem sqMass_nonneg (v : ℝ → ℝ) : 0 ≤ sqMass v :=
  integral_nonneg fun x => sq_nonneg (v x)

/-- A nonzero square mass is positive. -/
theorem sqMass_pos_of_ne_zero {v : ℝ → ℝ} (h : sqMass v ≠ 0) : 0 < sqMass v :=
  lt_of_le_of_ne (sqMass_nonneg v) (Ne.symm h)

/-- The normalisation hypothesis of the cofinal floor criterion, discharged. -/
theorem sqMass_pos_apertureDomain (a : ℝ) :
    ∀ v ∈ apertureDomain a, sqMass v ≠ 0 → 0 < sqMass v :=
  fun _ _ h => sqMass_pos_of_ne_zero h

/-- **The cofinal criterion for the restricted kernel form, unconditionally.**  Positivity of the
square mass is automatic, so the criterion runs on the floor hypothesis alone. -/
theorem diffBilinForm_nonneg_of_restrictedKernelFloor_tendsto_zero_of_ne_zero (K : ℝ → ℝ)
    (hbdd : ∀ a : ℝ, BddBelow
      (rayleighQuotientSet (fun v => diffBilinForm K v v) sqMass (apertureDomain a)))
    {a : ℝ} (ha : 0 < a)
    {ι : Type*} {l : Filter ι} [l.NeBot] {aseq : ι → ℝ}
    (hseq : Filter.Tendsto aseq l Filter.atTop)
    (hlim : Filter.Tendsto (fun i => restrictedKernelFloor K (aseq i)) l (nhds 0))
    {v : ℝ → ℝ} (hv : v ∈ apertureDomain a) (hN : sqMass v ≠ 0) :
    0 ≤ diffBilinForm K v v :=
  diffBilinForm_nonneg_of_restrictedKernelFloor_tendsto_zero K hbdd ha
    (sqMass_pos_apertureDomain a) hseq hlim hv hN

end GaloisForLFunctions.RHTower
