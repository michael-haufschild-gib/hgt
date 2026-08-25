import GaloisForLFunctions.RHTower.GaussOnePrimeActualCriticalResidue
import GaloisForLFunctions.RHTower.PrimeQuasiInnerResidueRigidity

/-!
# Euler reconstruction from the unlabelled one-prime residue family

The literal reduced one-prime energies have residue `gaussChannelResidue 1 p`.  Strict
monotonicity of the interpolated residue scale makes these values faithful prime labels.  Hence an
unlabelled set (or finite multiset-free packet) of measured residues determines exactly the prime
aperture and therefore every Euler product indexed by that aperture.
-/

namespace RHTower

open GaloisForLFunctions.RHTower
open scoped BigOperators

noncomputable section

/-- Residue carried by the literal reduced one-prime defect energy. -/
def gaussOnePrimeReducedDefectResidue (p : Nat.Primes) : ℝ :=
  gaussChannelResidue 1 p

/-- Every reduced one-prime defect realizes its assigned residue. -/
theorem hasSchattenLogResidue_gaussOnePrimeReducedDefect_residue (p : Nat.Primes) :
    HasSchattenLogResidue 1
      (ContinuousLinearMap.adjoint (gaussOnePrimeReducedDefect p) ∘L
        gaussOnePrimeReducedDefect p)
      (gaussOnePrimeReducedDefectResidue p) := by
  exact hasSchattenLogResidue_gaussOnePrimeReducedDefect_modulusSq p

/-- Distinct primes have distinct actual reduced-defect residues. -/
theorem gaussOnePrimeReducedDefectResidue_injective :
    Function.Injective gaussOnePrimeReducedDefectResidue := by
  intro p q hpq
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  have hq : (1 : ℝ) < (q : ℝ) := by exact_mod_cast q.prop.one_lt
  have hscale : primeQuasiInnerResidueScale (p : ℝ) =
      primeQuasiInnerResidueScale (q : ℝ) := by
    rw [primeQuasiInnerResidueScale_prime, primeQuasiInnerResidueScale_prime]
    exact hpq
  have hcast : (p : ℝ) = (q : ℝ) :=
    (primeQuasiInnerResidueScale_eq_iff hp hq).mp hscale
  apply Subtype.ext
  exact_mod_cast hcast

/-- Unlabelled residue set of an arbitrary prime aperture. -/
def gaussOnePrimeReducedDefectResidueSpectrum (S : Set Nat.Primes) : Set ℝ :=
  gaussOnePrimeReducedDefectResidue '' S

/-- An unlabelled residue set determines the exact prime aperture. -/
theorem gaussOnePrimeReducedDefectResidueSpectrum_injective :
    Function.Injective gaussOnePrimeReducedDefectResidueSpectrum := by
  intro S T hST
  ext p
  constructor
  · intro hp
    have himage : gaussOnePrimeReducedDefectResidue p ∈
        gaussOnePrimeReducedDefectResidueSpectrum T := by
      rw [← hST]
      exact ⟨p, hp, rfl⟩
    obtain ⟨q, hq, hpq⟩ := himage
    have : p = q := gaussOnePrimeReducedDefectResidue_injective hpq.symm
    simpa [this] using hq
  · intro hp
    have himage : gaussOnePrimeReducedDefectResidue p ∈
        gaussOnePrimeReducedDefectResidueSpectrum S := by
      rw [hST]
      exact ⟨p, hp, rfl⟩
    obtain ⟨q, hq, hpq⟩ := himage
    have : p = q := gaussOnePrimeReducedDefectResidue_injective hpq.symm
    simpa [this] using hq

/-- Finite unlabelled residue packet of a finite prime aperture. -/
def finiteGaussOnePrimeReducedDefectResidueSpectrum (P : Finset Nat.Primes) : Finset ℝ :=
  P.image gaussOnePrimeReducedDefectResidue

/-- Finite residue packets recover their prime packets exactly. -/
theorem finiteGaussOnePrimeReducedDefectResidueSpectrum_injective :
    Function.Injective finiteGaussOnePrimeReducedDefectResidueSpectrum := by
  intro P Q hPQ
  apply Finset.ext
  intro p
  constructor
  · intro hp
    have himage : gaussOnePrimeReducedDefectResidue p ∈
        finiteGaussOnePrimeReducedDefectResidueSpectrum Q := by
      rw [← hPQ]
      exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
    obtain ⟨q, hq, hpq⟩ := Finset.mem_image.mp himage
    have : p = q := gaussOnePrimeReducedDefectResidue_injective hpq.symm
    simpa [this] using hq
  · intro hp
    have himage : gaussOnePrimeReducedDefectResidue p ∈
        finiteGaussOnePrimeReducedDefectResidueSpectrum P := by
      rw [hPQ]
      exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
    obtain ⟨q, hq, hpq⟩ := Finset.mem_image.mp himage
    have : p = q := gaussOnePrimeReducedDefectResidue_injective hpq.symm
    simpa [this] using hq

/-- Finite Euler denominator indexed by a prime aperture. -/
def finitePrimeEulerDenominator (P : Finset Nat.Primes) (z : ℂ) : ℂ :=
  ∏ p ∈ P, (1 - (p : ℂ) ^ (-z))

/-- Equal unlabelled actual residue packets force equal finite Euler denominators. -/
theorem finitePrimeEulerDenominator_eq_of_residueSpectrum_eq
    {P Q : Finset Nat.Primes}
    (hPQ : finiteGaussOnePrimeReducedDefectResidueSpectrum P =
      finiteGaussOnePrimeReducedDefectResidueSpectrum Q) (z : ℂ) :
    finitePrimeEulerDenominator P z = finitePrimeEulerDenominator Q z := by
  rw [finiteGaussOnePrimeReducedDefectResidueSpectrum_injective hPQ]

/-- Equality of unlabelled actual residue packets recovers every prime-indexed observable. -/
theorem finset_sum_eq_of_residueSpectrum_eq {M : Type*} [AddCommMonoid M]
    {P Q : Finset Nat.Primes}
    (hPQ : finiteGaussOnePrimeReducedDefectResidueSpectrum P =
      finiteGaussOnePrimeReducedDefectResidueSpectrum Q) (F : Nat.Primes → M) :
    ∑ p ∈ P, F p = ∑ p ∈ Q, F p := by
  rw [finiteGaussOnePrimeReducedDefectResidueSpectrum_injective hPQ]

end

end RHTower
