import GaloisForLFunctions.BezoutValuationIncidence.DiscretePrimitiveEnergyAndJordanComparison
import GaloisForLFunctions.BezoutValuationIncidence.ExactFinitePrefixDiscrepancyDualityAndReturnTimes
import Mathlib.Data.Nat.Prime.Infinite

/-!
# The exact primitive-energy frontier and its universal inequality cone

At every level at least six, the least integration energy with prescribed
variance `V` and successor covariance `C` is
`max (5V+2C) (max (6V+4C) (6V+12C))/12`.
The three edges have exactly the spectral supports {2,3}, {3,4}, and {4,6}.
Four explicit modes realize every boundary point. Prime modes escape every
uniform energy/variance upper bound, completing the classification of all
universal linear inequalities in the three observables.
-/

open Finset ArithmeticFunction GaloisForLFunctions.BiScaleUncertainty RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-- Successor covariance with the harmonic mean removed. -/
def sieveSuccessorCovariance (N : ℕ) (c : ℕ → ℝ) : ℝ :=
  bezoutCoprimeQuadraticForm N c - (finiteHarmonicSum N c)^2

/-- The covariance and energy share the same finite Selberg coordinates. -/
theorem sieveSuccessorCovariance_eq_diagonal (N : ℕ) (c : ℕ → ℝ) :
    sieveSuccessorCovariance N c =
      ∑ q ∈ Finset.Icc 2 N, moebiusReal q * (selbergMultiplesCoord N c q)^2 :=
  bezout_sub_harmonic_sq_eq N c

private theorem energy_gap_diagonal (N : ℕ) (c : ℕ → ℝ) (a b : ℝ) :
    12 * sievePrimitiveEnergy N c - a * sieveVariance N c -
        b * sieveSuccessorCovariance N c =
      ∑ q ∈ Finset.Icc 2 N,
        (jordanTotient2 q - a * (Nat.totient q : ℝ) - b * moebiusReal q) *
          (selbergMultiplesCoord N c q)^2 := by
  rw [twelve_mul_sievePrimitiveEnergy_eq_jordan_diagonal,
    sieveSuccessorCovariance_eq_diagonal]
  unfold sieveVariance
  simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q _
  ring

private theorem energy_facet_and_equality (N : ℕ) (c : ℕ → ℝ)
    (a b : ℝ) (T : ℕ → Prop)
    (harith : ∀ q, 2 ≤ q →
      0 ≤ jordanTotient2 q - a * (Nat.totient q : ℝ) - b * moebiusReal q ∧
      (jordanTotient2 q - a * (Nat.totient q : ℝ) - b * moebiusReal q = 0 ↔ T q)) :
    a * sieveVariance N c + b * sieveSuccessorCovariance N c ≤ 12 * sievePrimitiveEnergy N c ∧
      (12 * sievePrimitiveEnergy N c = a * sieveVariance N c + b * sieveSuccessorCovariance N c ↔
        ∀ q ∈ Finset.Icc 2 N, ¬T q → selbergMultiplesCoord N c q = 0) := by
  have hnonneg : ∀ q ∈ Finset.Icc 2 N,
      0 ≤ (jordanTotient2 q - a * (Nat.totient q : ℝ) - b * moebiusReal q) *
        (selbergMultiplesCoord N c q)^2 := by
    intro q hq
    exact mul_nonneg (harith q (Finset.mem_Icc.mp hq).1).1 (sq_nonneg _)
  have hl := Finset.sum_nonneg hnonneg
  rw [← energy_gap_diagonal] at hl
  refine ⟨by linarith, ?_⟩
  have hz := Finset.sum_eq_zero_iff_of_nonneg hnonneg
  rw [← energy_gap_diagonal] at hz
  constructor
  · intro h q hq hnot
    have he := (hz.mp (by linarith)) q hq
    have hg : jordanTotient2 q - a * (Nat.totient q : ℝ) - b * moebiusReal q ≠ 0 :=
      fun hh => hnot ((harith q (Finset.mem_Icc.mp hq).1).2.mp hh)
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp he).resolve_left hg)
  · intro h
    have he : 12 * sievePrimitiveEnergy N c - a * sieveVariance N c -
        b * sieveSuccessorCovariance N c = 0 := by
      apply hz.mpr
      intro q hq
      by_cases ht : T q
      · rw [(harith q (Finset.mem_Icc.mp hq).1).2.mpr ht, zero_mul]
      · rw [h q hq ht, zero_pow (by omega), mul_zero]
    linarith

/-- First sharp energy facet; equality has precisely the two/three mode support. -/
theorem sievePrimitiveEnergy_first_facet (N : ℕ) (c : ℕ → ℝ) :
    5 * sieveVariance N c + 2 * sieveSuccessorCovariance N c ≤ 12 * sievePrimitiveEnergy N c ∧
      (12 * sievePrimitiveEnergy N c = 5 * sieveVariance N c + 2 * sieveSuccessorCovariance N c ↔
        ∀ q ∈ Finset.Icc 2 N, q ≠ 2 → q ≠ 3 → selbergMultiplesCoord N c q = 0) := by
  have h := energy_facet_and_equality N c 5 2 (fun q => q = 2 ∨ q = 3) (by
    intro q hq
    have hh := (jordanTotient2_sharp_successor_facets (q - 2)).1
    rw [Nat.sub_add_cancel hq] at hh
    refine ⟨by linarith [hh.1], ?_⟩
    constructor
    · intro he; exact hh.2.mp (by linarith)
    · intro he; have := hh.2.mpr he; linarith)
  simpa only [not_or, and_imp] using h

/-- Second sharp energy facet; equality has precisely the three/four mode support. -/
theorem sievePrimitiveEnergy_second_facet (N : ℕ) (c : ℕ → ℝ) :
    6 * sieveVariance N c + 4 * sieveSuccessorCovariance N c ≤ 12 * sievePrimitiveEnergy N c ∧
      (12 * sievePrimitiveEnergy N c = 6 * sieveVariance N c + 4 * sieveSuccessorCovariance N c ↔
        ∀ q ∈ Finset.Icc 2 N, q ≠ 3 → q ≠ 4 → selbergMultiplesCoord N c q = 0) := by
  have h := energy_facet_and_equality N c 6 4 (fun q => q = 3 ∨ q = 4) (by
    intro q hq
    have hh := (jordanTotient2_sharp_successor_facets (q - 2)).2.1
    rw [Nat.sub_add_cancel hq] at hh
    refine ⟨by linarith [hh.1], ?_⟩
    constructor
    · intro he; exact hh.2.mp (by linarith)
    · intro he; have := hh.2.mpr he; linarith)
  simpa only [not_or, and_imp] using h

/-- Third sharp energy facet; equality has precisely the four/six mode support. -/
theorem sievePrimitiveEnergy_third_facet (N : ℕ) (c : ℕ → ℝ) :
    6 * sieveVariance N c + 12 * sieveSuccessorCovariance N c ≤ 12 * sievePrimitiveEnergy N c ∧
      (12 * sievePrimitiveEnergy N c = 6 * sieveVariance N c + 12 * sieveSuccessorCovariance N c ↔
        ∀ q ∈ Finset.Icc 2 N, q ≠ 4 → q ≠ 6 → selbergMultiplesCoord N c q = 0) := by
  have h := energy_facet_and_equality N c 6 12 (fun q => q = 4 ∨ q = 6) (by
    intro q hq
    have hh := (jordanTotient2_sharp_successor_facets (q - 2)).2.2
    rw [Nat.sub_add_cancel hq] at hh
    refine ⟨by linarith [hh.1], ?_⟩
    constructor
    · intro he; exact hh.2.mp (by linarith)
    · intro he; have := hh.2.mpr he; linarith)
  simpa only [not_or, and_imp] using h

/-- Exact lower-bound function for prescribed variance and successor covariance. -/
def primitiveEnergyMinimum (v s : ℝ) : ℝ :=
  max (5 * v + 2 * s) (max (6 * v + 4 * s) (6 * v + 12 * s)) / 12

/-- Every finite real sieve lies above the arithmetic three-facet frontier. -/
theorem primitiveEnergyMinimum_le (N : ℕ) (c : ℕ → ℝ) :
    primitiveEnergyMinimum (sieveVariance N c) (sieveSuccessorCovariance N c) ≤
      sievePrimitiveEnergy N c := by
  unfold primitiveEnergyMinimum
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 12)).mpr
  apply max_le
  · linarith [(sievePrimitiveEnergy_first_facet N c).1]
  · apply max_le
    · linarith [(sievePrimitiveEnergy_second_facet N c).1]
    · linarith [(sievePrimitiveEnergy_third_facet N c).1]

private theorem boundary_arithmetic :
    (Nat.totient 3 = 2 ∧ Nat.totient 4 = 2 ∧ Nat.totient 6 = 2) ∧
    (moebiusReal 2 = -1 ∧ moebiusReal 3 = -1 ∧ moebiusReal 4 = 0 ∧ moebiusReal 6 = 1) ∧
    (jordanTotient2 2 = 3 ∧ jordanTotient2 3 = 8 ∧ jordanTotient2 4 = 12 ∧ jordanTotient2 6 = 24) := by
  have ht3 : Nat.totient 3 = 2 := by rw [Nat.totient_prime Nat.prime_three]
  have ht4 := wall11_totient_degeneracy_broken_by_bezout.1
  have ht6 := wall11_totient_degeneracy_broken_by_bezout.2.1
  have hm2 : moebiusReal 2 = -1 := by
    simp [moebiusReal, ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  have hm3 : moebiusReal 3 = -1 := by
    simp [moebiusReal, ArithmeticFunction.moebius_apply_prime Nat.prime_three]
  have hg4 := wall11_totient_degeneracy_broken_by_bezout.2.2.1
  have hg6 := wall11_totient_degeneracy_broken_by_bezout.2.2.2
  rw [ht4] at hg4
  rw [ht6] at hg6
  have hm4 : moebiusReal 4 = 0 := by norm_num at hg4; linarith
  have hm6 : moebiusReal 6 = 1 := by norm_num at hg6; linarith
  have hj2 := (jordanTotient2_sharp_successor_facets 0).1.2.mpr (Or.inl rfl)
  have hj3 := (jordanTotient2_sharp_successor_facets 1).1.2.mpr (Or.inr rfl)
  have hj4 := (jordanTotient2_sharp_successor_facets 2).2.1.2.mpr (Or.inr rfl)
  have hj6 := (jordanTotient2_sharp_successor_facets 4).2.2.2.mpr (Or.inr rfl)
  norm_num [ht3, ht4, ht6, hm2, hm3, hm4, hm6] at hj2 hj3 hj4 hj6
  exact ⟨⟨ht3, ht4, ht6⟩, ⟨hm2, hm3, hm4, hm6⟩, ⟨hj2, hj3, hj4, hj6⟩⟩

/-- Four nonconstant boundary coordinates and an arbitrary harmonic coordinate. -/
def primitiveFrontierProfile (h a b u v : ℝ) (q : ℕ) : ℝ :=
  if q = 1 then h else if q = 2 then a else if q = 3 then b else
    if q = 4 then u else if q = 6 then v else 0

/-- Explicit real sieve weights with the four independent boundary modes. -/
def primitiveFrontierWeight (N : ℕ) (h a b u v : ℝ) : ℕ → ℝ :=
  pmRamanujanResidueCoeff (primitiveFrontierProfile h a b u v) (N + 6)

private theorem sum_frontier_profile (N : ℕ) (w : ℕ → ℝ) (h a b u v : ℝ) :
    (∑ q ∈ Finset.Icc 2 (N + 6), w q * (primitiveFrontierProfile h a b u v q)^2) =
      w 2 * a^2 + w 3 * b^2 + w 4 * u^2 + w 6 * v^2 := by
  have hterm (q : ℕ) (hq : q ∈ Finset.Icc 2 (N + 6)) :
      w q * (primitiveFrontierProfile h a b u v q)^2 =
        (if q = 2 then w 2 * a^2 else 0) +
        (if q = 3 then w 3 * b^2 else 0) +
        (if q = 4 then w 4 * u^2 else 0) +
        (if q = 6 then w 6 * v^2 else 0) := by
    have h1 : q ≠ 1 := by have := (Finset.mem_Icc.mp hq).1; omega
    by_cases h2 : q = 2
    · subst q; simp [primitiveFrontierProfile]
    by_cases h3 : q = 3
    · subst q; simp [primitiveFrontierProfile]
    by_cases h4 : q = 4
    · subst q; simp [primitiveFrontierProfile]
    by_cases h6 : q = 6
    · subst q; simp [primitiveFrontierProfile]
    simp [primitiveFrontierProfile, h1, h2, h3, h4, h6]
  rw [Finset.sum_congr rfl hterm]
  simp_rw [Finset.sum_add_distrib]
  have h2 : 2 ≤ N + 6 := by omega
  have h3 : 3 ≤ N + 6 := by omega
  have h4 : 4 ≤ N + 6 := by omega
  have h6 : 6 ≤ N + 6 := by omega
  simp [h2, h3, h4, h6]

/-- Exact simultaneous mean, variance, covariance, and integration energy of the boundary profile. -/
theorem primitiveFrontierWeight_moments (N : ℕ) (h a b u v : ℝ) :
    finiteHarmonicSum (N + 6) (primitiveFrontierWeight N h a b u v) = h ∧
    sieveVariance (N + 6) (primitiveFrontierWeight N h a b u v) =
      a^2 + 2 * b^2 + 2 * u^2 + 2 * v^2 ∧
    sieveSuccessorCovariance (N + 6) (primitiveFrontierWeight N h a b u v) =
      -a^2 - b^2 + v^2 ∧
    12 * sievePrimitiveEnergy (N + 6) (primitiveFrontierWeight N h a b u v) =
      3 * a^2 + 8 * b^2 + 12 * u^2 + 24 * v^2 := by
  obtain ⟨⟨ht3, ht4, ht6⟩, ⟨hm2, hm3, hm4, hm6⟩, ⟨hj2, hj3, hj4, hj6⟩⟩ := boundary_arithmetic
  have heval (w : ℕ → ℝ) :
      (∑ q ∈ Finset.Icc 2 (N + 6), w q *
        (selbergMultiplesCoord (N + 6) (primitiveFrontierWeight N h a b u v) q)^2) =
        w 2 * a^2 + w 3 * b^2 + w 4 * u^2 + w 6 * v^2 := by
    unfold primitiveFrontierWeight
    calc _ = ∑ q ∈ Finset.Icc 2 (N + 6), w q * (primitiveFrontierProfile h a b u v q)^2 := by
           apply Finset.sum_congr rfl
           intro q hq
           rw [selbergMultiplesCoord_ramanujan_inverse, if_pos (by
             obtain ⟨hq2, hqN⟩ := Finset.mem_Icc.mp hq
             exact Finset.mem_Icc.mpr ⟨by omega, hqN⟩)]
         _ = _ := sum_frontier_profile N w h a b u v
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← selbergMultiplesCoord_one_eq_finiteHarmonicSum]
    unfold primitiveFrontierWeight
    rw [selbergMultiplesCoord_ramanujan_inverse, if_pos (by simp)]
    simp [primitiveFrontierProfile]
  · unfold sieveVariance
    rw [heval]
    simp [ht3, ht4, ht6]
  · rw [sieveSuccessorCovariance_eq_diagonal, heval]
    simp [hm2, hm3, hm4, hm6]
    ring
  · rw [twelve_mul_sievePrimitiveEnergy_eq_jordan_diagonal, heval, hj2, hj3, hj4, hj6]

/-- Every admissible pair of variance and covariance attains the exact energy minimum,
with arbitrary prescribed mean, at every level at least six. -/
theorem exists_sievePrimitiveEnergy_minimizer_iff (N : ℕ) (h v s : ℝ) :
    (∃ c : ℕ → ℝ, finiteHarmonicSum (N + 6) c = h ∧
      sieveVariance (N + 6) c = v ∧ sieveSuccessorCovariance (N + 6) c = s ∧
      sievePrimitiveEnergy (N + 6) c = primitiveEnergyMinimum v s) ↔
      0 ≤ v ∧ -v ≤ s ∧ 2 * s ≤ v := by
  constructor
  · rintro ⟨c, _, hv, hs, _⟩
    have hb := successor_covariance_bounds (N + 6) c
    change -sieveVariance (N + 6) c ≤ sieveSuccessorCovariance (N + 6) c ∧
      2 * sieveSuccessorCovariance (N + 6) c ≤ sieveVariance (N + 6) c at hb
    rw [hv, hs] at hb
    have hv0 : 0 ≤ sieveVariance (N + 6) c :=
      Finset.sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    exact ⟨hv ▸ hv0, hb⟩
  · rintro ⟨hv, hl, hu⟩
    by_cases hleft : 2 * s ≤ -v
    · let a := Real.sqrt (-v - 2 * s)
      let b := Real.sqrt (v + s)
      have ha : a^2 = -v - 2 * s := Real.sq_sqrt (by linarith)
      have hb : b^2 = v + s := Real.sq_sqrt (by linarith)
      obtain ⟨hm, hV, hC, hE⟩ := primitiveFrontierWeight_moments N h a b 0 0
      have hmin : primitiveEnergyMinimum v s = (5 * v + 2 * s) / 12 := by
        unfold primitiveEnergyMinimum
        rw [max_eq_left (max_le (by linarith) (by linarith))]
      refine ⟨primitiveFrontierWeight N h a b 0 0, hm, ?_, ?_, ?_⟩
      · nlinarith
      · nlinarith
      · rw [hmin]; nlinarith
    · by_cases hmiddle : s ≤ 0
      · let b := Real.sqrt (-s)
        let u := Real.sqrt ((v + 2 * s) / 2)
        have hb : b^2 = -s := Real.sq_sqrt (by linarith)
        have hu' : u^2 = (v + 2 * s) / 2 := Real.sq_sqrt (by linarith)
        obtain ⟨hm, hV, hC, hE⟩ := primitiveFrontierWeight_moments N h 0 b u 0
        have hmin : primitiveEnergyMinimum v s = (6 * v + 4 * s) / 12 := by
          unfold primitiveEnergyMinimum
          have hi : max (6 * v + 4 * s) (6 * v + 12 * s) = 6 * v + 4 * s :=
            max_eq_left (by linarith)
          rw [hi, max_eq_right (by linarith)]
        refine ⟨primitiveFrontierWeight N h 0 b u 0, hm, ?_, ?_, ?_⟩
        · nlinarith
        · nlinarith
        · rw [hmin]; nlinarith
      · let u := Real.sqrt ((v - 2 * s) / 2)
        let z := Real.sqrt s
        have hu' : u^2 = (v - 2 * s) / 2 := Real.sq_sqrt (by linarith)
        have hz : z^2 = s := Real.sq_sqrt (by linarith)
        obtain ⟨hm, hV, hC, hE⟩ := primitiveFrontierWeight_moments N h 0 0 u z
        have hmin : primitiveEnergyMinimum v s = (6 * v + 12 * s) / 12 := by
          unfold primitiveEnergyMinimum
          have hi : max (6 * v + 4 * s) (6 * v + 12 * s) = 6 * v + 12 * s :=
            max_eq_right (by linarith)
          rw [hi, max_eq_right (by linarith)]
        refine ⟨primitiveFrontierWeight N h 0 0 u z, hm, ?_, ?_, ?_⟩
        · nlinarith
        · nlinarith
        · rw [hmin]; nlinarith

private theorem pure_prime_energy_moments {p : ℕ} (hp : p.Prime) :
    ∃ c : ℕ → ℝ, finiteHarmonicSum p c = 0 ∧
      sieveVariance p c = (p : ℝ) - 1 ∧ sieveSuccessorCovariance p c = -1 ∧
      sievePrimitiveEnergy p c = ((p : ℝ)^2 - 1) / 12 := by
  let y : ℕ → ℝ := fun q => if q = p then 1 else 0
  let c := pmRamanujanResidueCoeff y p
  have heval (w : ℕ → ℝ) :
      (∑ q ∈ Finset.Icc 2 p, w q * (selbergMultiplesCoord p c q)^2) = w p := by
    calc _ = ∑ q ∈ Finset.Icc 2 p, if q = p then w q else 0 := by
           apply Finset.sum_congr rfl
           intro q hq
           have hq1 : q ∈ Finset.Icc 1 p :=
             Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hq).1; omega,
               (Finset.mem_Icc.mp hq).2⟩
           simp only [c, selbergMultiplesCoord_ramanujan_inverse, if_pos hq1, y]
           split_ifs <;> simp
         _ = w p := by simp [hp.two_le]
  have hj : jordanTotient2 p = (p : ℝ)^2 - 1 := by
    have hh := gcdPowKernel_prime_pow 2 hp (by decide : 1 ≤ 1)
    norm_cast at hh
    simpa [jordanTotient2_eq_gcdPowKernel] using hh
  refine ⟨c, ?_, ?_, ?_, ?_⟩
  · rw [← selbergMultiplesCoord_one_eq_finiteHarmonicSum]
    simp [c, selbergMultiplesCoord_ramanujan_inverse, y, hp.one_le, hp.ne_one.symm]
  · unfold sieveVariance
    rw [heval, Nat.totient_prime hp, Nat.cast_sub hp.one_le, Nat.cast_one]
  · rw [sieveSuccessorCovariance_eq_diagonal, heval]
    simp [moebiusReal, ArithmeticFunction.moebius_apply_prime hp]
  · have hh := twelve_mul_sievePrimitiveEnergy_eq_jordan_diagonal p c
    rw [heval, hj] at hh
    linarith

/-- Prime modes have arbitrarily large integration cost per unit variance,
while their mean and successor covariance remain exactly controlled. -/
theorem exists_prime_mode_with_large_primitive_energy (K : ℝ) :
    ∃ (p : ℕ) (c : ℕ → ℝ), p.Prime ∧ finiteHarmonicSum p c = 0 ∧
      sieveVariance p c = (p : ℝ) - 1 ∧ sieveSuccessorCovariance p c = -1 ∧
      sievePrimitiveEnergy p c = ((p : ℝ)^2 - 1) / 12 ∧
      1 ≤ sieveVariance p c ∧ K * sieveVariance p c < sievePrimitiveEnergy p c := by
  obtain ⟨n, hn⟩ := exists_nat_gt (12 * K + 2)
  obtain ⟨p, hnp, hp⟩ := Nat.exists_infinite_primes n
  have hnpR : (n : ℝ) ≤ p := by exact_mod_cast hnp
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  obtain ⟨c, hh, hv, hs, he⟩ := pure_prime_energy_moments hp
  refine ⟨p, c, hp, hh, hv, hs, he, ?_, ?_⟩
  · rw [hv]; linarith
  · rw [hv, he]
    have hpos : 0 < ((p : ℝ) - 1) * ((p : ℝ) + 1 - 12 * K) :=
      mul_pos (by linarith) (by linarith)
    nlinarith

/-- Complete classification of every universal linear inequality in variance,
successor covariance, and discrete primitive energy. -/
theorem universal_primitive_energy_inequality_iff (α β γ : ℝ) :
    (∀ (N : ℕ) (c : ℕ → ℝ),
      0 ≤ α * sieveVariance N c + β * sieveSuccessorCovariance N c +
        γ * sievePrimitiveEnergy N c) ↔
      0 ≤ γ ∧ 0 ≤ 4 * α - 4 * β + γ ∧ 0 ≤ 6 * α - 3 * β + 2 * γ ∧
        0 ≤ 2 * α + γ ∧ 0 ≤ 2 * α + β + 2 * γ := by
  constructor
  · intro h
    have hγ : 0 ≤ γ := by
      by_contra hneg
      have hneg' : γ < 0 := by linarith
      let K := (|α| + |β| + 1) / (-γ)
      obtain ⟨p, c, _, _, _, hs, _, hv, hE⟩ := exists_prime_mode_with_large_primitive_energy K
      have htest := h p c
      rw [hs] at htest
      have hK : (-γ) * K = |α| + |β| + 1 := by
        dsimp [K]
        field_simp [hneg'.ne]
      have hm := mul_lt_mul_of_pos_left hE (by linarith : 0 < -γ)
      rw [← mul_assoc, hK] at hm
      have ha := mul_le_mul_of_nonneg_right (le_abs_self α) (by linarith : 0 ≤ sieveVariance p c)
      have hb : -β ≤ |β| * sieveVariance p c := by
        nlinarith [neg_le_abs β, abs_nonneg β]
      nlinarith
    have h2 : 0 ≤ 4 * α - 4 * β + γ := by
      have hh := h 6 (primitiveFrontierWeight 0 0 1 0 0 0)
      obtain ⟨_, hv, hs, he⟩ := primitiveFrontierWeight_moments 0 0 1 0 0 0
      rw [hv, hs] at hh
      norm_num at hh he
      have he' : sievePrimitiveEnergy 6 (primitiveFrontierWeight 0 0 1 0 0 0) = 1 / 4 := by linarith
      rw [he'] at hh
      linarith
    have h3 : 0 ≤ 6 * α - 3 * β + 2 * γ := by
      have hh := h 6 (primitiveFrontierWeight 0 0 0 1 0 0)
      obtain ⟨_, hv, hs, he⟩ := primitiveFrontierWeight_moments 0 0 0 1 0 0
      rw [hv, hs] at hh
      norm_num at hh he
      have he' : sievePrimitiveEnergy 6 (primitiveFrontierWeight 0 0 0 1 0 0) = 2 / 3 := by linarith
      rw [he'] at hh
      linarith
    have h4 : 0 ≤ 2 * α + γ := by
      have hh := h 6 (primitiveFrontierWeight 0 0 0 0 1 0)
      obtain ⟨_, hv, hs, he⟩ := primitiveFrontierWeight_moments 0 0 0 0 1 0
      rw [hv, hs] at hh
      norm_num at hh he
      have he' : sievePrimitiveEnergy 6 (primitiveFrontierWeight 0 0 0 0 1 0) = 1 := by linarith
      rw [he'] at hh
      linarith
    have h6 : 0 ≤ 2 * α + β + 2 * γ := by
      have hh := h 6 (primitiveFrontierWeight 0 0 0 0 0 1)
      obtain ⟨_, hv, hs, he⟩ := primitiveFrontierWeight_moments 0 0 0 0 0 1
      rw [hv, hs] at hh
      norm_num at hh he
      have he' : sievePrimitiveEnergy 6 (primitiveFrontierWeight 0 0 0 0 0 1) = 2 := by linarith
      rw [he'] at hh
      linarith
    exact ⟨hγ, h2, h3, h4, h6⟩
  · rintro ⟨hγ, h2, h3, h4, h6⟩ N c
    have hb := successor_covariance_bounds N c
    change -sieveVariance N c ≤ sieveSuccessorCovariance N c ∧
      2 * sieveSuccessorCovariance N c ≤ sieveVariance N c at hb
    by_cases hleft : 2 * sieveSuccessorCovariance N c ≤ -sieveVariance N c
    · have hp2 := mul_nonneg h2 (show 0 ≤ -sieveVariance N c - 2 * sieveSuccessorCovariance N c by linarith)
      have hp3 := mul_nonneg h3 (show 0 ≤ sieveVariance N c + sieveSuccessorCovariance N c by linarith [hb.1])
      have hg := mul_nonneg hγ (show 0 ≤ 12 * sievePrimitiveEnergy N c -
          5 * sieveVariance N c - 2 * sieveSuccessorCovariance N c by
        linarith [(sievePrimitiveEnergy_first_facet N c).1])
      nlinarith only [hp2, hp3, hg]
    · by_cases hmiddle : sieveSuccessorCovariance N c ≤ 0
      · have hp3 := mul_nonneg h3 (show 0 ≤ -sieveSuccessorCovariance N c by linarith)
        have hp4 := mul_nonneg h4 (show 0 ≤ sieveVariance N c + 2 * sieveSuccessorCovariance N c by linarith)
        have hg := mul_nonneg hγ (show 0 ≤ 12 * sievePrimitiveEnergy N c -
            6 * sieveVariance N c - 4 * sieveSuccessorCovariance N c by
          linarith [(sievePrimitiveEnergy_second_facet N c).1])
        nlinarith only [hp3, hp4, hg]
      · have hp4 := mul_nonneg h4 (show 0 ≤ sieveVariance N c - 2 * sieveSuccessorCovariance N c by linarith [hb.2])
        have hp6 := mul_nonneg h6 (show 0 ≤ sieveSuccessorCovariance N c by linarith)
        have hg := mul_nonneg hγ (show 0 ≤ 12 * sievePrimitiveEnergy N c -
            6 * sieveVariance N c - 12 * sieveSuccessorCovariance N c by
          linarith [(sievePrimitiveEnergy_third_facet N c).1])
        nlinarith only [hp4, hp6, hg]

end
end GaloisForLFunctions.BezoutValuationIncidence
