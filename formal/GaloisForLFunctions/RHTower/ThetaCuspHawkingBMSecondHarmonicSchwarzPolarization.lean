import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMProjectiveCausalResponse

/-!
# BM second-harmonic Schwarz polarization

The cubic Peierls polarization law moves the physical carrier from a mixed self-pairing to an
independent `++`--`--` second-harmonic pairing. This module constructs the missing `--` frequency and
proves that its Birmingham--Mokhtari radial data at conjugate momentum are exactly the Schwarz
partners of existing `++` data.

Radial `A` and `B` parameters exchange, two chiral Jost factors exchange, and full Jost determinant
and pole-cancelled projective boundary response conjugate. These are algebraic frequency-block
identities. They do not assert that either response is an augmented Peierls boundary flux.
-/

open Complex

namespace RHTower

noncomputable section

/-- Frequency of quadratic `--` source. -/
def d4BMCausalMinusMinusFrequency (n : ℕ) (chi : ℂ) : ℂ :=
  2 * d4BMCausalQNMMinus n chi

/-- `--` frequency at conjugate momentum is minus conjugate `++` frequency. -/
theorem d4BMCausalMinusMinusFrequency_schwarz
    (n : ℕ) (chi : ℂ) :
    d4BMCausalMinusMinusFrequency n ((starRingEnd ℂ) chi) =
      -((starRingEnd ℂ) (d4BMCausalPlusPlusFrequency n chi)) := by
  simp [d4BMCausalMinusMinusFrequency, d4BMCausalPlusPlusFrequency,
    d4BMCausalQNMMinus, d4BMCausalQNMPlus, d4BMCausalDecay,
    map_sub, map_mul, map_ofNat, Complex.conj_I]
  ring

/-- `--` radial `A` parameter is conjugate `++` radial `B` parameter. -/
theorem d4BMCausalRadialA_minusMinus_schwarz
    (n : ℕ) (chi : ℂ) :
    d4BMCausalRadialA
        (d4BMCausalMinusMinusFrequency n ((starRingEnd ℂ) chi))
        ((starRingEnd ℂ) chi) =
      (starRingEnd ℂ)
        (d4BMCausalRadialB (d4BMCausalPlusPlusFrequency n chi) chi) := by
  rw [d4BMCausalMinusMinusFrequency_schwarz]
  simp [d4BMCausalRadialA, d4BMCausalRadialB,
    map_add, map_sub, map_div₀, map_mul, map_ofNat, Complex.conj_I]
  ring

/-- `--` radial `B` parameter is conjugate `++` radial `A` parameter. -/
theorem d4BMCausalRadialB_minusMinus_schwarz
    (n : ℕ) (chi : ℂ) :
    d4BMCausalRadialB
        (d4BMCausalMinusMinusFrequency n ((starRingEnd ℂ) chi))
        ((starRingEnd ℂ) chi) =
      (starRingEnd ℂ)
        (d4BMCausalRadialA (d4BMCausalPlusPlusFrequency n chi) chi) := by
  rw [d4BMCausalMinusMinusFrequency_schwarz]
  simp [d4BMCausalRadialA, d4BMCausalRadialB,
    map_sub, map_div₀, map_mul, map_ofNat, Complex.conj_I]
  ring

/-- `--` radial `C` parameter is conjugate `++` radial `C` parameter. -/
theorem d4BMCausalRadialC_minusMinus_schwarz
    (n : ℕ) (chi : ℂ) :
    d4BMCausalRadialC
        (d4BMCausalMinusMinusFrequency n ((starRingEnd ℂ) chi)) =
      (starRingEnd ℂ)
        (d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi)) := by
  rw [d4BMCausalMinusMinusFrequency_schwarz]
  simp [d4BMCausalRadialC, map_sub, map_mul, Complex.conj_I]

/-- `--` plus Jost factor is conjugate `++` minus Jost factor. -/
theorem d4BMCausalJostPlus_minusMinus_schwarz
    (n : ℕ) (chi : ℂ) :
    d4BMCausalJostPlus
        (d4BMCausalMinusMinusFrequency n ((starRingEnd ℂ) chi))
        ((starRingEnd ℂ) chi) =
      (starRingEnd ℂ)
        (d4BMCausalJostMinus (d4BMCausalPlusPlusFrequency n chi) chi) := by
  rw [d4BMCausalJostPlus, d4BMCausalJostMinus,
    d4BMCausalRadialA_minusMinus_schwarz, map_inv₀, Complex.Gamma_conj]

/-- `--` minus Jost factor is conjugate `++` plus Jost factor. -/
theorem d4BMCausalJostMinus_minusMinus_schwarz
    (n : ℕ) (chi : ℂ) :
    d4BMCausalJostMinus
        (d4BMCausalMinusMinusFrequency n ((starRingEnd ℂ) chi))
        ((starRingEnd ℂ) chi) =
      (starRingEnd ℂ)
        (d4BMCausalJostPlus (d4BMCausalPlusPlusFrequency n chi) chi) := by
  rw [d4BMCausalJostPlus, d4BMCausalJostMinus,
    d4BMCausalRadialB_minusMinus_schwarz, map_inv₀, Complex.Gamma_conj]

/-- Full `--` Jost determinant is conjugate full `++` determinant. -/
theorem d4BMCausalJost_minusMinus_schwarz
    (n : ℕ) (chi : ℂ) :
    d4BMCausalJost
        (d4BMCausalMinusMinusFrequency n ((starRingEnd ℂ) chi))
        ((starRingEnd ℂ) chi) =
      (starRingEnd ℂ)
        (d4BMCausalJost (d4BMCausalPlusPlusFrequency n chi) chi) := by
  rw [d4BMCausalJost, d4BMCausalJost,
    d4BMCausalJostPlus_minusMinus_schwarz,
    d4BMCausalJostMinus_minusMinus_schwarz, map_mul]
  ring

/-- First `--` hypergeometric parameter is conjugate second `++` parameter. -/
theorem d4BMCausalHypergeometricA_minusMinus_schwarz
    (n : ℕ) (chi : ℂ) :
    d4BMCausalHypergeometricA
        (d4BMCausalMinusMinusFrequency n ((starRingEnd ℂ) chi))
        ((starRingEnd ℂ) chi) =
      (starRingEnd ℂ)
        (d4BMCausalHypergeometricB (d4BMCausalPlusPlusFrequency n chi) chi) := by
  rw [d4BMCausalHypergeometricA, d4BMCausalHypergeometricB,
    d4BMCausalRadialA_minusMinus_schwarz]
  simp only [map_sub, map_div₀, map_one, Complex.conj_ofNat]

/-- Second `--` hypergeometric parameter is conjugate first `++` parameter. -/
theorem d4BMCausalHypergeometricB_minusMinus_schwarz
    (n : ℕ) (chi : ℂ) :
    d4BMCausalHypergeometricB
        (d4BMCausalMinusMinusFrequency n ((starRingEnd ℂ) chi))
        ((starRingEnd ℂ) chi) =
      (starRingEnd ℂ)
        (d4BMCausalHypergeometricA (d4BMCausalPlusPlusFrequency n chi) chi) := by
  rw [d4BMCausalHypergeometricA, d4BMCausalHypergeometricB,
    d4BMCausalRadialB_minusMinus_schwarz]
  simp only [map_sub, map_div₀, map_one, Complex.conj_ofNat]

/-- Pole-cancelled `--` boundary response is conjugate `++` response. -/
theorem d4BMCausalProjectiveBoundaryResponse_minusMinus_schwarz
    (n : ℕ) (chi : ℂ) :
    d4BMCausalProjectiveBoundaryResponse
        (d4BMCausalMinusMinusFrequency n ((starRingEnd ℂ) chi))
        ((starRingEnd ℂ) chi) =
      (starRingEnd ℂ)
        (d4BMCausalProjectiveBoundaryResponse
          (d4BMCausalPlusPlusFrequency n chi) chi) := by
  rw [d4BMCausalProjectiveBoundaryResponse,
    d4BMCausalProjectiveBoundaryResponse,
    d4BMCausalRadialA_minusMinus_schwarz,
    d4BMCausalRadialB_minusMinus_schwarz,
    d4BMCausalHypergeometricA_minusMinus_schwarz,
    d4BMCausalHypergeometricB_minusMinus_schwarz]
  simp only [map_mul, map_div₀, map_neg, map_ofNat, Complex.Gamma_conj]
  ring

end

end RHTower
