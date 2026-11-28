import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum.Entanglement.Weights

/-! # Purity and von Neumann entropy of the measured composition output -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum.Entanglement

open Matrix Real
open GaloisForLFunctions.HTGeometry

/-- Reduced density matrix on the vacuum and the resolved elementary labels. -/
def marginal (s : ℂ) (N : ℕ) (z : SplitParameter) :=
  pureStateReducedLeft (amplitudes s N z)

def linearEntropy (s : ℂ) (N : ℕ) (z : SplitParameter) :=
  1-(trace (marginal s N z*marginal s N z)).re

def spectralEntropy (s : ℂ) (N : ℕ) (z : SplitParameter) :=
  finiteMatrixVonNeumannEntropy (marginal s N z) (pureStateReducedLeft_isHermitian _)

open scoped Matrix in
open Polynomial in
/-- The two positive Schmidt weights and every zero mode, with multiplicity. -/
theorem characteristic (s : ℂ) (N : ℕ) (z : SplitParameter) :
    (marginal s N z).charpoly = X^(Fintype.card (PrimeAt N)-1) *
      ((X-C ((1-vacuumWeight s N z:ℝ):ℂ))*(X-C (vacuumWeight s N z:ℂ))) := by
  have two : 2 ∈ primes (cutoff (N:ℝ)) := Nat.mem_primesBelow.mpr ⟨by omega,Nat.prime_two⟩
  have hk : 0 < Fintype.card (PrimeAt N) := Fintype.card_pos_iff.mpr ⟨⟨2,two⟩⟩
  have hh : Fintype.card Bool ≤ Fintype.card (Option (PrimeAt N)) := by
    rw [Fintype.card_bool,Fintype.card_option]
    omega
  let B := columns (vacuumRow s N z) (vacuumColumn s N z)
  have h := Matrix.charpoly_mul_comm_of_le B Bᴴ hh
  dsimp only [B] at h
  rw [←left_gram,two_levels,Matrix.charpoly_diagonal,Fintype.prod_bool] at h
  have dim : Fintype.card (Option (PrimeAt N))-Fintype.card Bool=Fintype.card (PrimeAt N)-1 := by
    rw [Fintype.card_option,Fintype.card_bool]
    omega
  rw [marginal,amplitudes_eq]
  simpa only [dim,eigenWeights,column_mass,row_mass] using h

theorem linear_eq (s : ℂ) (N : ℕ) (z : SplitParameter) :
    linearEntropy s N z=2*vacuumWeight s N z*(1-vacuumWeight s N z) := by
  rw [linearEntropy,marginal,amplitudes_eq,shared_purity,row_mass,column_mass,Complex.ofReal_re]
  ring

theorem spectral_eq (s : ℂ) (N : ℕ) (z : SplitParameter) :
    spectralEntropy s N z=binEntropy (vacuumWeight s N z) := by
  let ent (ψ : Option (PrimeAt N) × Option (PrimeAt N) → ℂ) :=
    finiteMatrixVonNeumannEntropy (pureStateReducedLeft ψ) (pureStateReducedLeft_isHermitian ψ)
  change ent (amplitudes s N z)=_
  rw [amplitudes_eq]
  unfold ent
  rw [shared_entropy,row_mass,column_mass,binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  unfold negMulLog
  ring

#print axioms characteristic
#print axioms linear_eq
#print axioms spectral_eq

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum.Entanglement
