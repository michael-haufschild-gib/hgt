import GaloisForLFunctions.RHTower.GaussComponentPrimeSampling
import GaloisForLFunctions.HTGeometry.HarmonicResidueTransfer

/-!
# Logarithmic residue of the sampled Gauss-component magnitude
-/

namespace RHTower

open Filter Topology Finset

noncomputable section

/-- The critical `2m`-energy of a Gauss component sampled at the positive prime logarithmic
lattice. -/
def gaussComponentPrimeMagnitudeEnergy {m : ℕ} (k : Fin m) (p : Nat.Primes) (n : ℕ) : ℝ :=
  (gaussComponentVerticalMagnitude k
    (2 * Real.pi * ((n : ℝ) + 1) / Real.log (p : ℝ))) ^ (2 * m)

theorem gaussComponentPrimeMagnitudeEnergy_mul_succ_tendsto
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) :
    Tendsto (fun n : ℕ =>
      gaussComponentPrimeMagnitudeEnergy k p n * ((n : ℝ) + 1))
      atTop (nhds (Real.log (p : ℝ))) := by
  have hbase := gaussComponentVerticalMagnitude_primeSample_tendsto hm k p
  have hshift := hbase.comp (tendsto_add_atTop_nat 1)
  simpa [gaussComponentPrimeMagnitudeEnergy, Function.comp_def, Nat.cast_add, Nat.cast_one,
    add_comm] using hshift

/-- **Exact magnitude residue.**  The logarithmic mean of the sampled critical Gauss-component
energy converges to `log p`, independently of the component label `k`. -/
theorem gaussComponentPrimeMagnitudeEnergy_logResidue
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, gaussComponentPrimeMagnitudeEnergy k p n) / Real.log N)
      atTop (nhds (Real.log (p : ℝ))) :=
  GaloisForLFunctions.tendsto_logResidue_of_mul_succ_tendsto
    (gaussComponentPrimeMagnitudeEnergy_mul_succ_tendsto hm k p)

end

end RHTower
