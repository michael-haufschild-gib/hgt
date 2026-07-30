import GaloisForLFunctions.HTGeometry.OccupationVacuumAnomalyReciprocity
import GaloisForLFunctions.RHTower.PrimeWoldGammaGlobalBoundaryVolume

/-!
# Finite-prime polarized irregular occupation triple

The finite-prime Wold boundary volume, normalized occupation half-density,
unnormalized norm record, and reflected Gamma irregular gauge are four records
of one occupation line.

This is a finite-stage source identity.  It does not construct the cofinal
polarized completion, land Xi conormal fibres, or prove the Riemann Hypothesis.
-/

open Complex Filter Topology
open scoped BigOperators ENNReal InnerProductSpace

noncomputable section

namespace GaloisForLFunctions

/-- Real occupation nome at one member of a finite prime packet. -/
def finitePrimeOccupationNome
    (S : Finset Nat.Primes) (p : S) : ℝ :=
  ((((p : Nat.Primes) : ℕ) : ℝ))⁻¹

theorem finitePrimeOccupationNome_nonneg
    (S : Finset Nat.Primes) (p : S) :
    0 ≤ finitePrimeOccupationNome S p := by
  exact inv_nonneg.mpr (by
    exact_mod_cast Nat.zero_le ((p : Nat.Primes) : ℕ))

theorem finitePrimeOccupationNome_lt_one
    (S : Finset Nat.Primes) (p : S) :
    finitePrimeOccupationNome S p < 1 := by
  have hp1 : (1 : ℝ) < ((p : Nat.Primes) : ℕ) := by
    exact_mod_cast (p : Nat.Primes).2.one_lt
  exact (inv_lt_one₀ (by positivity)).2 hp1

/-- Raw finite-prime occupation half-density.  Its norm record is deliberately
not normalized away. -/
def finitePrimeRawOccupationHalfDensity
    (S : Finset Nat.Primes) :
    lp (fun _ : S →₀ ℕ => ℂ) 2 :=
  HTGeometry.finiteOccupationRawHalfDensity
    (finitePrimeOccupationNome S)
    (finitePrimeOccupationNome_nonneg S)
    (finitePrimeOccupationNome_lt_one S)

/-- Projectively normalized finite-prime occupation direction. -/
def finitePrimeNormalizedOccupationHalfDensity
    (S : Finset Nat.Primes) :
    lp (fun _ : S →₀ ℕ => ℂ) 2 :=
  HTGeometry.finiteOccupationNormalizedHalfDensity
    (finitePrimeOccupationNome S)
    (finitePrimeOccupationNome_nonneg S)
    (finitePrimeOccupationNome_lt_one S)

theorem finitePrimeOccupationBoundaryVolume_eq
    (S : Finset Nat.Primes) :
    HTGeometry.finiteOccupationBoundaryVolume
        (finitePrimeOccupationNome S) =
      finitePrimeWoldBoundaryVolume S := by
  rfl

theorem norm_finitePrimeRawOccupationHalfDensity_sq
    (S : Finset Nat.Primes) :
    ‖finitePrimeRawOccupationHalfDensity S‖ ^ 2 =
      (finitePrimeWoldBoundaryVolume S)⁻¹ := by
  rw [finitePrimeRawOccupationHalfDensity,
    HTGeometry.norm_finiteOccupationRawHalfDensity_sq]
  calc
    (∏ i, (1 - finitePrimeOccupationNome S i)⁻¹) =
        (∏ i, (1 - finitePrimeOccupationNome S i))⁻¹ :=
      Finset.prod_inv_distrib
        (s := (Finset.univ : Finset S))
        (fun i : S => 1 - finitePrimeOccupationNome S i)
    _ = (finitePrimeWoldBoundaryVolume S)⁻¹ := rfl

theorem norm_finitePrimeNormalizedOccupationHalfDensity_sq
    (S : Finset Nat.Primes) :
    ‖finitePrimeNormalizedOccupationHalfDensity S‖ ^ 2 = 1 := by
  exact HTGeometry.norm_finiteOccupationNormalizedHalfDensity_sq
    (finitePrimeOccupationNome S)
    (finitePrimeOccupationNome_nonneg S)
    (finitePrimeOccupationNome_lt_one S)

theorem norm_inner_finitePrimeVacuum_normalized_sq
    (S : Finset Nat.Primes) :
    ‖inner ℂ (HTGeometry.finiteOccupationVacuum S)
        (finitePrimeNormalizedOccupationHalfDensity S)‖ ^ 2 =
      finitePrimeWoldBoundaryVolume S := by
  simpa only [finitePrimeNormalizedOccupationHalfDensity,
    finitePrimeOccupationBoundaryVolume_eq] using
    HTGeometry.norm_inner_vacuum_normalized_sq
      (finitePrimeOccupationNome S)
      (finitePrimeOccupationNome_nonneg S)
      (finitePrimeOccupationNome_lt_one S)

/-- Exact finite-stage weld: the reflected Gamma irregular gauge is the
exponential of centered charge times the squared norm record of the same raw
occupation line. -/
theorem finitePrimeGenusOnePolarizedPhase_eq_rawNormGauge_mul
    (S : Finset Nat.Primes) (t : ℂ) :
    finitePrimeGenusOnePolarizedPhase S t =
      Complex.exp
          (2 * t * (‖finitePrimeRawOccupationHalfDensity S‖ ^ 2 : ℂ)) *
        finitePrimeGenusZeroPolarizedPhase S t := by
  rw [finitePrimeGenusOnePolarizedPhase_eq_irregularGauge_mul]
  have hnorm := norm_finitePrimeRawOccupationHalfDensity_sq S
  have hcast := congrArg (fun x : ℝ => (x : ℂ)) hnorm
  push_cast at hcast
  rw [hcast]

/-- Complete finite-prime polarized irregular triple: projective unit
direction, vacuum half-density, reciprocal raw norm record, and exact Gamma
irregular gauge all arise from one occupation line. -/
theorem finitePrimePolarizedIrregularTriple_exact
    (S : Finset Nat.Primes) (t : ℂ) :
    ‖finitePrimeNormalizedOccupationHalfDensity S‖ ^ 2 = 1 ∧
    ‖inner ℂ (HTGeometry.finiteOccupationVacuum S)
        (finitePrimeNormalizedOccupationHalfDensity S)‖ ^ 2 =
      finitePrimeWoldBoundaryVolume S ∧
    ‖finitePrimeRawOccupationHalfDensity S‖ ^ 2 =
      (finitePrimeWoldBoundaryVolume S)⁻¹ ∧
    finitePrimeGenusOnePolarizedPhase S t =
      Complex.exp
          (2 * t * (‖finitePrimeRawOccupationHalfDensity S‖ ^ 2 : ℂ)) *
        finitePrimeGenusZeroPolarizedPhase S t := by
  exact ⟨norm_finitePrimeNormalizedOccupationHalfDensity_sq S,
    norm_inner_finitePrimeVacuum_normalized_sq S,
    norm_finitePrimeRawOccupationHalfDensity_sq S,
    finitePrimeGenusOnePolarizedPhase_eq_rawNormGauge_mul S t⟩

end GaloisForLFunctions
