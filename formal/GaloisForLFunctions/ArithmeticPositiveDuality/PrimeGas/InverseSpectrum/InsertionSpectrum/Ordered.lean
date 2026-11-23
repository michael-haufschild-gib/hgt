import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.InsertionSpectrum.Partition
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.InsertionSpectrum.BandAction

/-! # All ordered physical levels after multiplicative insertion -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

/-- The physical spectrum after inserting a factor is the ordered block refinement, including all ties. -/
theorem missingSpectrum_insert (a : ℕ+) (v : MissingWave) :
    missingSpectrum (insertMissing a v) = refinedSpectrum a (missingSpectrum v) := by
  apply band_eq_of_partition
  intro z hz
  rw [relativePartition_refined _ _ hz]
  exact omissionPartition_insert a v hz

theorem inserted_prefix (a : ℕ+) (v : MissingWave) {j : ℕ} (hj : j < a.val-1) :
    (missingSpectrum (insertMissing a v) j).val = occupationWeight j := by
  rw [missingSpectrum_insert,refined_prefix a _ hj]

theorem inserted_ordered_block (a : ℕ+) (v : MissingWave) (n r : ℕ) (hr : r < a.val) :
    (missingSpectrum (insertMissing a v) (sectorStart a n+r)).val =
      min (occupationWeight (sectorStart a n+r))
        (max (occupationWeight (sectorStart a n+r+1)) (sectorWeight a*(missingSpectrum v n).val)) := by
  rw [missingSpectrum_insert,refined_block a _ n r hr]

#print axioms missingSpectrum_insert
#print axioms inserted_prefix
#print axioms inserted_ordered_block

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
