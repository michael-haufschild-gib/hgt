import GaloisForLFunctions.RHTower.DeningerBigWittFrobeniusPairwiseCyclicCorrectionNoGo
import GaloisForLFunctions.RHTower.XiPrimeSeamCalkinGram

/-!
# Big-Witt Frobenius source as exact Calkin energy

The Frobenius-transgressed physical coefficient of each ordered prime seam
is negative twice the squared essential norm of the actual seam-weighted
Sonin--Euler Calkin corner. Summing before scalarization identifies the
finite Big-Witt first ghost with a genuine nonnegative operator-quotient
Dirichlet energy and computes its cofinal residue exactly. This gives Route L
a canonical nonlocal completion carrier; it does not assume compactness or
submass of that carrier.
-/

open Complex Filter Topology
open scoped BigOperators
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Canonical Sonin-Calkin corner associated with an ordered prime pair. -/
def deningerBigWittPrimeSeamCalkinCorner
    (rho : ℂ) (p q : Nat.Primes) :
    ArchimedeanWeightedL2 →L[ℂ] ArchimedeanWeightedL2 :=
  orbitwisePrimeSeamCalkinGramCorner 1 (p : ℕ) (q : ℕ) rho

/-- Squared essential norm of the actual ordered Calkin corner. -/
def deningerBigWittPrimeSeamCalkinPairEnergy
    (rho : ℂ) (p q : Nat.Primes) : ℝ :=
  essentialNorm (deningerBigWittPrimeSeamCalkinCorner rho p q) ^ (2 : ℕ)

/-- The Calkin pair energy is exactly the reciprocal-prime physical
Dirichlet atom. -/
theorem deningerBigWittPrimeSeamCalkinPairEnergy_eq
    (rho : ℂ) (p q : Nat.Primes) :
    deningerBigWittPrimeSeamCalkinPairEnergy rho p q =
      deningerBigWittPrimePairExtendedPhysicalAtom p q *
        ‖orbitwiseNatPrimeSeamCharge (p : ℕ) rho -
          orbitwiseNatPrimeSeamCharge (q : ℕ) rho‖ ^ (2 : ℕ) := by
  rw [deningerBigWittPrimeSeamCalkinPairEnergy,
    deningerBigWittPrimeSeamCalkinCorner,
    essentialNorm_orbitwisePrimeSeamCalkinGramCorner
      1 (p : ℕ) (q : ℕ) rho (by norm_num) p.prop q.prop,
    deningerBigWittPrimePairExtendedPhysicalAtom_eq]
  rw [mul_pow, inv_pow]
  let P : ℝ := (p : ℝ)
  let Q : ℝ := (q : ℝ)
  have hP0 : 0 < P := by
    dsimp only [P]
    exact_mod_cast p.prop.pos
  have hQ0 : 0 < Q := by
    dsimp only [Q]
    exact_mod_cast q.prop.pos
  change
    ‖orbitwiseNatPrimeSeamCharge (p : ℕ) rho -
        orbitwiseNatPrimeSeamCharge (q : ℕ) rho‖ ^ (2 : ℕ) *
        ((Real.sqrt P * Real.sqrt Q) ^ (2 : ℕ))⁻¹ =
      1 / P * (1 / Q) *
        ‖orbitwiseNatPrimeSeamCharge (p : ℕ) rho -
          orbitwiseNatPrimeSeamCharge (q : ℕ) rho‖ ^ (2 : ℕ)
  rw [show (Real.sqrt P * Real.sqrt Q) ^ (2 : ℕ) = P * Q by
    rw [mul_pow, Real.sq_sqrt hP0.le, Real.sq_sqrt hQ0.le]]
  field_simp [hP0.ne', hQ0.ne']

/-- The Frobenius-transgressed pair coefficient is negative twice the
squared essential norm of its actual Calkin corner. -/
theorem deningerBigWittFrobeniusPrimeSeamPairCoefficient_eq_calkin
    (rho : ℂ) (p q : Nat.Primes) :
    deningerBigWittFrobeniusPrimeSeamPairCoefficient
        (fun r : Nat.Primes =>
          orbitwiseNatPrimeSeamCharge (r : ℕ) rho) p q =
      ((-2 * deningerBigWittPrimeSeamCalkinPairEnergy rho p q : ℝ) : ℂ) := by
  rw [deningerBigWittFrobeniusPrimeSeamPairCoefficient_eq,
    deningerBigWittPrimeSeamCalkinPairEnergy_eq]
  push_cast
  ring

/-- Finite squared-Calkin energy of all ordered seam corners. -/
def deningerBigWittPrimeSeamFiniteCalkinEnergy
    (rho : ℂ) (s : Finset Nat.Primes) : ℝ :=
  ∑ p ∈ s, ∑ q ∈ s,
    deningerBigWittPrimeSeamCalkinPairEnergy rho p q

/-- The operator-quotient energy is exactly the canonical Big-Witt source
Dirichlet energy. -/
theorem deningerBigWittPrimeSeamFiniteCalkinEnergy_eq_sourceEnergy
    (rho : ℂ) (s : Finset Nat.Primes) :
    deningerBigWittPrimeSeamFiniteCalkinEnergy rho s =
      deningerBigWittPrimeSeamSourceEnergy
        (fun p : Nat.Primes =>
          orbitwiseNatPrimeSeamCharge (p : ℕ) rho) s := by
  rw [deningerBigWittPrimeSeamFiniteCalkinEnergy,
    deningerBigWittPrimeSeamSourceEnergy]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  exact deningerBigWittPrimeSeamCalkinPairEnergy_eq rho p q

/-- First ghost of the finite Frobenius source is negative twice the actual
finite squared-Calkin energy. -/
theorem deningerBigWittFrobeniusTwo_polarizedAggregate_ghost_one_eq_calkin
    (rho : ℂ) (s : Finset Nat.Primes) :
    deningerBigWittGhostComponent 1 Nat.zero_lt_one
        (deningerBigWittFrobeniusTwo
          (deningerBigWittPolarizedPrimeSeamAggregateSource
            (fun p : Nat.Primes =>
              orbitwiseNatPrimeSeamCharge (p : ℕ) rho) s)) =
      ((-2 * deningerBigWittPrimeSeamFiniteCalkinEnergy rho s : ℝ) : ℂ) := by
  rw [deningerBigWittFrobeniusTwo_polarizedAggregate_ghost_one,
    deningerBigWittPrimeSeamFiniteCalkinEnergy_eq_sourceEnergy]

/-- Cofinal Calkin energy has exact one-particle seam residue. -/
theorem tendsto_deningerBigWittPrimeSeamFiniteCalkinEnergy_div_mass
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) :
    Tendsto
      (fun s : Finset Nat.Primes =>
        deningerBigWittPrimeSeamFiniteCalkinEnergy rho s /
          primeReciprocalMass s)
      atTop
      (nhds (2 * orbitwisePrimeSeamWeightedNormSq rho)) := by
  simpa only [deningerBigWittPrimeSeamFiniteCalkinEnergy_eq_sourceEnergy]
    using tendsto_deningerBigWittPrimeSeamSourceEnergy_div_mass hstrip

end


end RHTower
