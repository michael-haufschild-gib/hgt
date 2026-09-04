import GaloisForLFunctions.HTGeometry.RandomMixedGraphCore
import GaloisForLFunctions.HTGeometry.DyadicLatticeCover
import GaloisForLFunctions.RHTower.GaussSampleQuantitativeRatio
import GaloisForLFunctions.RHTower.QuantumOscillationMechanics
import GaloisForLFunctions.RHTower.SelbergClass.AffineGammaPoleLattice

namespace GaloisForLFunctions.RHTower.RandomMixedGraph

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.RandomMixedGraph

noncomputable section

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

@[simp] theorem landauSpectralTriple_ratio (n : ℕ) :
    consecutiveSpacingRatio (landauSpectralTriple n) = 1 := by
  rw [consecutiveSpacingRatio]
  have h0 := unitLandauCrossing_spacing n
  have h1 := unitLandauCrossing_spacing (n + 1)
  have hindex : n + 2 = (n + 1) + 1 := by omega
  simp only [firstSpacing, secondSpacing, landauSpectralTriple]
  rw [hindex, h0, h1]
  norm_num

def gaussPrimeSpectralTriple (p : Nat.Primes) (n : ℕ) : OrderedSpectralTriple :=
  equispacedTriple (RHTower.gaussPrimeSampleHeightInt p (n : ℤ))
    ⟨RHTower.gaussPrimeSampleSpacing p, RHTower.gaussPrimeSampleSpacing_pos p⟩

@[simp] theorem gaussPrimeSpectralTriple_ratio (p : Nat.Primes) (n : ℕ) :
    consecutiveSpacingRatio (gaussPrimeSpectralTriple p n) = 1 := by
  simp [gaussPrimeSpectralTriple]

theorem gaussPrimeSpectralTriple_middle_eq_sample (p : Nat.Primes) (n : ℕ) :
    (gaussPrimeSpectralTriple p n).middle =
      RHTower.gaussPrimeSampleHeightInt p ((n + 1 : ℕ) : ℤ) := by
  rw [gaussPrimeSpectralTriple, equispacedTriple]
  rw [RHTower.gaussPrimeSampleHeightInt_nat_eq_spacing_mul p n,
    RHTower.gaussPrimeSampleHeightInt_nat_eq_spacing_mul p (n + 1)]
  push_cast
  ring

theorem gaussPrimeSpectralTriple_upper_eq_sample (p : Nat.Primes) (n : ℕ) :
    (gaussPrimeSpectralTriple p n).upper =
      RHTower.gaussPrimeSampleHeightInt p ((n + 2 : ℕ) : ℤ) := by
  rw [gaussPrimeSpectralTriple, equispacedTriple]
  rw [RHTower.gaussPrimeSampleHeightInt_nat_eq_spacing_mul p n,
    RHTower.gaussPrimeSampleHeightInt_nat_eq_spacing_mul p (n + 2)]
  push_cast
  ring

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

def landauSpectralQuintuple (n : ℕ) : OrderedSpectralQuintuple :=
  equispacedQuintuple (unitLandauCrossing n) ⟨1, by norm_num⟩

@[simp] theorem landauSpectralQuintuple_secondOrderRatio (n : ℕ) :
    secondOrderSpacingRatio (landauSpectralQuintuple n) = 1 := by
  simp [landauSpectralQuintuple]

def gaussPrimeSpectralQuintuple (p : Nat.Primes) (n : ℕ) : OrderedSpectralQuintuple :=
  equispacedQuintuple (RHTower.gaussPrimeSampleHeightInt p (n : ℤ))
    ⟨RHTower.gaussPrimeSampleSpacing p, RHTower.gaussPrimeSampleSpacing_pos p⟩

@[simp] theorem gaussPrimeSpectralQuintuple_secondOrderRatio
    (p : Nat.Primes) (n : ℕ) :
    secondOrderSpacingRatio (gaussPrimeSpectralQuintuple p n) = 1 := by
  simp [gaussPrimeSpectralQuintuple]

def dyadicSpectralQuintuple (a : ℝ) (k : ℤ) : OrderedSpectralQuintuple :=
  equispacedQuintuple (dyadicCenter a (k + 4)) ⟨Real.log 2, log_two_pos⟩

@[simp] theorem dyadicSpectralQuintuple_secondOrderRatio (a : ℝ) (k : ℤ) :
    secondOrderSpacingRatio (dyadicSpectralQuintuple a k) = 1 := by
  simp [dyadicSpectralQuintuple]

def affineGammaPoleSpectralQuintuple
    (A : ℂ) (slope : {b : ℝ // 0 < b}) (n : ℕ) : OrderedSpectralQuintuple :=
  equispacedQuintuple
    (_root_.RHTower.affineGammaAddPole A slope (n + 4)).re
    ⟨slope.val⁻¹, inv_pos.mpr slope.property⟩

@[simp] theorem affineGammaPoleSpectralQuintuple_secondOrderRatio
    (A : ℂ) (slope : {b : ℝ // 0 < b}) (n : ℕ) :
    secondOrderSpacingRatio (affineGammaPoleSpectralQuintuple A slope n) = 1 := by
  simp [affineGammaPoleSpectralQuintuple]

end

end GaloisForLFunctions.RHTower.RandomMixedGraph
