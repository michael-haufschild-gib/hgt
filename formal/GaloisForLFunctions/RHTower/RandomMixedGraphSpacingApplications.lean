import GaloisForLFunctions.HTGeometry.RandomMixedGraphCore
import GaloisForLFunctions.HTGeometry.DyadicLatticeCover
import GaloisForLFunctions.RHTower.GaussSampleQuantitativeRatio
import GaloisForLFunctions.RHTower.QuantumOscillationMechanics
import GaloisForLFunctions.RHTower.SelbergClass.AffineGammaPoleLattice

/-!
# Spacing ratios of rigid arithmetic spectra

Spectral spacing statistics use the consecutive ratio `(λ₃ - λ₂) / (λ₂ - λ₁)` of an ordered triple
and the second-order ratio `(λ₅ - λ₃) / (λ₃ - λ₁)` of an ordered quintuple. This module packages
four exactly equispaced sequences as ordered triples and quintuples and shows all their ratios are
exactly `1`: the unit Landau-level crossings `n + 1/2`, the prime logarithmic lattice heights
`2π i / log p`, the dyadic lattice centers with spacing `log 2`, and the real parts of the poles
`-(A + n) / b` of an affine Gamma factor `Γ(b w + A)`, `b > 0`.

## Main results

- `landauSpectralTriple_ratio`, `gaussPrimeSpectralTriple_ratio`, `dyadicSpectralTriple_ratio`,
  `affineGammaPoleSpectralTriple_ratio`: the consecutive spacing ratio equals `1`.
- `landauSpectralQuintuple_secondOrderRatio`, `gaussPrimeSpectralQuintuple_secondOrderRatio`,
  `dyadicSpectralQuintuple_secondOrderRatio`, `affineGammaPoleSpectralQuintuple_secondOrderRatio`:
  the second-order spacing ratio equals `1`.
- `gaussPrimeSpectralTriple_middle_eq_sample`, `gaussPrimeSpectralTriple_upper_eq_sample`: the
  prime-lattice triple consists of the lattice heights at indices `n`, `n + 1`, `n + 2`.

## Hypotheses

All results are unconditional; the affine Gamma statements carry the slope condition `0 < b` in
the subtype of the slope.
-/

namespace GaloisForLFunctions.RHTower.RandomMixedGraph

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.RandomMixedGraph

noncomputable section

/-- Ordered triple of consecutive unit Landau crossings `n + 1/2`, `n + 3/2`, `n + 5/2`. -/
def landauSpectralTriple (n : ℕ) : OrderedSpectralTriple where
  lower := unitLandauCrossing n
  middle := unitLandauCrossing (n + 1)
  upper := unitLandauCrossing (n + 2)
  lower_lt_middle := by
    linarith [unitLandauCrossing_spacing n]
  middle_lt_upper := by
    have hindex : n + 2 = (n + 1) + 1 := by omega
    rw [hindex]
    linarith [unitLandauCrossing_spacing (n + 1)]

/-- Consecutive Landau crossings have spacing ratio exactly `1`. -/
@[simp] theorem landauSpectralTriple_ratio (n : ℕ) :
    consecutiveSpacingRatio (landauSpectralTriple n) = 1 := by
  rw [consecutiveSpacingRatio]
  have h0 := unitLandauCrossing_spacing n
  have h1 := unitLandauCrossing_spacing (n + 1)
  have hindex : n + 2 = (n + 1) + 1 := by omega
  simp only [firstSpacing, secondSpacing, landauSpectralTriple]
  rw [hindex, h0, h1]
  norm_num

/-- Ordered triple of consecutive heights `2π i / log p` on the prime logarithmic lattice. -/
def gaussPrimeSpectralTriple (p : Nat.Primes) (n : ℕ) : OrderedSpectralTriple :=
  equispacedTriple (RHTower.gaussPrimeSampleHeightInt p (n : ℤ))
    ⟨RHTower.gaussPrimeSampleSpacing p, RHTower.gaussPrimeSampleSpacing_pos p⟩

/-- The prime logarithmic lattice has consecutive spacing ratio exactly `1`. -/
@[simp] theorem gaussPrimeSpectralTriple_ratio (p : Nat.Primes) (n : ℕ) :
    consecutiveSpacingRatio (gaussPrimeSpectralTriple p n) = 1 := by
  simp [gaussPrimeSpectralTriple]

/-- The middle point of the prime-lattice triple is the lattice height at index `n + 1`. -/
theorem gaussPrimeSpectralTriple_middle_eq_sample (p : Nat.Primes) (n : ℕ) :
    (gaussPrimeSpectralTriple p n).middle =
      RHTower.gaussPrimeSampleHeightInt p ((n + 1 : ℕ) : ℤ) := by
  rw [gaussPrimeSpectralTriple, equispacedTriple]
  rw [RHTower.gaussPrimeSampleHeightInt_nat_eq_spacing_mul p n,
    RHTower.gaussPrimeSampleHeightInt_nat_eq_spacing_mul p (n + 1)]
  push_cast
  ring

/-- The upper point of the prime-lattice triple is the lattice height at index `n + 2`. -/
theorem gaussPrimeSpectralTriple_upper_eq_sample (p : Nat.Primes) (n : ℕ) :
    (gaussPrimeSpectralTriple p n).upper =
      RHTower.gaussPrimeSampleHeightInt p ((n + 2 : ℕ) : ℤ) := by
  rw [gaussPrimeSpectralTriple, equispacedTriple]
  rw [RHTower.gaussPrimeSampleHeightInt_nat_eq_spacing_mul p n,
    RHTower.gaussPrimeSampleHeightInt_nat_eq_spacing_mul p (n + 2)]
  push_cast
  ring

/-- Ordered triple of dyadic lattice centers at indices `k + 2`, `k + 1`, `k`, spaced by `log 2`. -/
def dyadicSpectralTriple (a : ℝ) (k : ℤ) : OrderedSpectralTriple where
  lower := dyadicCenter a (k + 2)
  middle := dyadicCenter a (k + 1)
  upper := dyadicCenter a k
  lower_lt_middle := by
    have h := dyadicCenter_spacing a (k + 1)
    have hindex : k + 1 + 1 = k + 2 := by ring
    rw [hindex] at h
    linarith [log_two_pos]
  middle_lt_upper := by
    linarith [dyadicCenter_spacing a k, log_two_pos]

/-- The dyadic lattice centers have consecutive spacing ratio exactly `1`. -/
@[simp] theorem dyadicSpectralTriple_ratio (a : ℝ) (k : ℤ) :
    consecutiveSpacingRatio (dyadicSpectralTriple a k) = 1 := by
  rw [consecutiveSpacingRatio]
  have h0 := dyadicCenter_spacing a k
  have h1 := dyadicCenter_spacing a (k + 1)
  have hindex : k + 1 + 1 = k + 2 := by ring
  rw [hindex] at h1
  simp only [firstSpacing, secondSpacing, dyadicSpectralTriple]
  rw [show dyadicCenter a k - dyadicCenter a (k + 1) = Real.log 2 from h0,
    show dyadicCenter a (k + 1) - dyadicCenter a (k + 2) = Real.log 2 from h1,
    div_self (ne_of_gt log_two_pos)]

/-- Ordered triple of real parts of consecutive poles `-(A + n) / b` of `Γ(b w + A)`, `b > 0`. -/
def affineGammaPoleSpectralTriple
    (A : ℂ) (slope : {b : ℝ // 0 < b}) (n : ℕ) : OrderedSpectralTriple where
  lower := (_root_.RHTower.affineGammaAddPole A slope (n + 2)).re
  middle := (_root_.RHTower.affineGammaAddPole A slope (n + 1)).re
  upper := (_root_.RHTower.affineGammaAddPole A slope n).re
  lower_lt_middle := by
    have h := _root_.RHTower.affineGammaAddPole_re_succ A slope.property (n + 1)
    have hinv := inv_pos.mpr slope.property
    have hindex : n + 1 + 1 = n + 2 := by omega
    rw [hindex] at h
    linarith
  middle_lt_upper := by
    have h := _root_.RHTower.affineGammaAddPole_re_succ A slope.property n
    have hinv := inv_pos.mpr slope.property
    linarith

/-- The real parts of the affine Gamma poles have consecutive spacing ratio exactly `1`. -/
@[simp] theorem affineGammaPoleSpectralTriple_ratio
    (A : ℂ) (slope : {b : ℝ // 0 < b}) (n : ℕ) :
    consecutiveSpacingRatio (affineGammaPoleSpectralTriple A slope n) = 1 := by
  rw [consecutiveSpacingRatio]
  have h0 := _root_.RHTower.affineGammaAddPole_re_succ A slope.property n
  have h1 := _root_.RHTower.affineGammaAddPole_re_succ A slope.property (n + 1)
  have hindex : n + 1 + 1 = n + 2 := by omega
  rw [hindex] at h1
  have hinv : slope.val⁻¹ ≠ 0 := ne_of_gt (inv_pos.mpr slope.property)
  simp only [firstSpacing, secondSpacing, affineGammaPoleSpectralTriple]
  rw [show (_root_.RHTower.affineGammaAddPole A slope n).re -
      (_root_.RHTower.affineGammaAddPole A slope (n + 1)).re = slope.val⁻¹ by linarith,
    show (_root_.RHTower.affineGammaAddPole A slope (n + 1)).re -
      (_root_.RHTower.affineGammaAddPole A slope (n + 2)).re = slope.val⁻¹ by linarith,
    div_self hinv]

/-- Five consecutive unit Landau crossings starting at `n + 1/2`. -/
def landauSpectralQuintuple (n : ℕ) : OrderedSpectralQuintuple :=
  equispacedQuintuple (unitLandauCrossing n) ⟨1, by norm_num⟩

/-- Landau crossings have second-order spacing ratio exactly `1`. -/
@[simp] theorem landauSpectralQuintuple_secondOrderRatio (n : ℕ) :
    secondOrderSpacingRatio (landauSpectralQuintuple n) = 1 := by
  simp [landauSpectralQuintuple]

/-- Five consecutive heights of the prime logarithmic lattice starting at index `n`. -/
def gaussPrimeSpectralQuintuple (p : Nat.Primes) (n : ℕ) : OrderedSpectralQuintuple :=
  equispacedQuintuple (RHTower.gaussPrimeSampleHeightInt p (n : ℤ))
    ⟨RHTower.gaussPrimeSampleSpacing p, RHTower.gaussPrimeSampleSpacing_pos p⟩

/-- The prime logarithmic lattice has second-order spacing ratio exactly `1`. -/
@[simp] theorem gaussPrimeSpectralQuintuple_secondOrderRatio
    (p : Nat.Primes) (n : ℕ) :
    secondOrderSpacingRatio (gaussPrimeSpectralQuintuple p n) = 1 := by
  simp [gaussPrimeSpectralQuintuple]

/-- Five equispaced points with step `log 2` starting at the dyadic center of index `k + 4`. -/
def dyadicSpectralQuintuple (a : ℝ) (k : ℤ) : OrderedSpectralQuintuple :=
  equispacedQuintuple (dyadicCenter a (k + 4)) ⟨Real.log 2, log_two_pos⟩

/-- The dyadic quintuple has second-order spacing ratio exactly `1`. -/
@[simp] theorem dyadicSpectralQuintuple_secondOrderRatio (a : ℝ) (k : ℤ) :
    secondOrderSpacingRatio (dyadicSpectralQuintuple a k) = 1 := by
  simp [dyadicSpectralQuintuple]

/-- Five equispaced points with step `1/b` starting at the real part of the affine Gamma pole of
index `n + 4`. -/
def affineGammaPoleSpectralQuintuple
    (A : ℂ) (slope : {b : ℝ // 0 < b}) (n : ℕ) : OrderedSpectralQuintuple :=
  equispacedQuintuple
    (_root_.RHTower.affineGammaAddPole A slope (n + 4)).re
    ⟨slope.val⁻¹, inv_pos.mpr slope.property⟩

/-- The affine Gamma pole quintuple has second-order spacing ratio exactly `1`. -/
@[simp] theorem affineGammaPoleSpectralQuintuple_secondOrderRatio
    (A : ℂ) (slope : {b : ℝ // 0 < b}) (n : ℕ) :
    secondOrderSpacingRatio (affineGammaPoleSpectralQuintuple A slope n) = 1 := by
  simp [affineGammaPoleSpectralQuintuple]

end

end GaloisForLFunctions.RHTower.RandomMixedGraph
