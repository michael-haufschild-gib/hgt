import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.ThePrimeKernelSplitsOverAFiniteSieve

/-!
# Exact prime Grams of the finite-sieve classes

The horizon restricts the supported/unit product coordinates by `d k ≤ M`.
Different supported factors interact only on the same unit coordinate, so their
prime Gram is exactly a decimated harmonic sum.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open GaloisForLFunctions.HTGeometry
  GaloisForLFunctions.ArithmeticEffectivityTheory
  GaloisForLFunctions.ArithmeticElectrostatics
  GaloisForLFunctions.ArithmeticIntersectionTheory

/-- The pole vector on the class with supported part `d`. -/
def sieveClassPole (Q : Finset Nat.Primes) (d n : ℕ) : ℝ :=
  if d ∣ n ∧ Nat.Coprime (n / d) (sievePrimorial Q) then poleVector n else 0

/-- Positive units of a finite sieve up to the given horizon. -/
def sieveUnits (Q : Finset Nat.Primes) (M : ℕ) : Finset ℕ :=
  (Icc 1 M).filter (fun k => Nat.Coprime k (sievePrimorial Q))

/-- The natural density of the class with supported part `d`. -/
def sieveClassDensity (Q : Finset Nat.Primes) (d : ℕ) : ℝ := sieveDensity Q / d

/-- The harmonic mass of the class at horizon `M`. -/
def sieveClassMass (Q : Finset Nat.Primes) (d M : ℕ) : ℝ :=
  sievedHarmonic Q (M / d) / d

theorem sieveClassDensity_pos {Q : Finset Nat.Primes} {d : ℕ}
    (hd : SieveSupported Q d) : 0 < sieveClassDensity Q d :=
  div_pos (sieveDensity_pos Q) (by exact_mod_cast hd.pos)

/-- Distinct supported orders label disjoint classes. -/
theorem sieveClassPole_mul_eq_zero {Q : Finset Nat.Primes} {d e : ℕ}
    (hd : SieveSupported Q d) (he : SieveSupported Q e) (hde : d ≠ e) (n : ℕ) :
    sieveClassPole Q d n * sieveClassPole Q e n = 0 := by
  unfold sieveClassPole
  split_ifs with hdn hen
  · exact (hde (sieveFactorization_unique hd he hdn.2 hen.2
      ((Nat.mul_div_cancel' hdn.1).trans (Nat.mul_div_cancel' hen.1).symm)).1).elim
  all_goals simp

/-- A class is a scaled copy of the units, with the horizon decimated by its order. -/
theorem sum_sieveClassPole_mul {d : ℕ} (hd : 0 < d)
    (Q : Finset Nat.Primes) (M : ℕ) (F : ℕ → ℝ) :
    ∑ n ∈ Icc 1 M, sieveClassPole Q d n * F n =
      ∑ k ∈ sieveUnits Q (M / d), poleVector (d * k) * F (d * k) := by
  have hterm : ∀ n : ℕ, sieveClassPole Q d n * F n =
      if d ∣ n then
        (if Nat.Coprime (n / d) (sievePrimorial Q) then poleVector n * F n else 0)
      else 0 := by
    intro n
    simp only [sieveClassPole]
    split_ifs <;> simp_all
  simp_rw [hterm]
  rw [← sum_filter, multiples_Icc hd,
    sum_image fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hd h,
    sieveUnits, sum_filter]
  exact sum_congr rfl fun k _ => by rw [Nat.mul_div_cancel_left k hd]

/-- The decimated harmonic formula is the actual squared norm of the class vector. -/
theorem sieveClassMass_eq_sum {d : ℕ} (hd : 0 < d)
    (Q : Finset Nat.Primes) (M : ℕ) :
    sieveClassMass Q d M = ∑ n ∈ Icc 1 M, sieveClassPole Q d n ^ 2 := by
  symm
  calc ∑ n ∈ Icc 1 M, sieveClassPole Q d n ^ 2
      = ∑ n ∈ Icc 1 M, sieveClassPole Q d n * sieveClassPole Q d n := by
          simp only [sq]
    _ = ∑ k ∈ sieveUnits Q (M / d), poleVector (d * k) * sieveClassPole Q d (d * k) :=
      sum_sieveClassPole_mul hd Q M _
    _ = ∑ k ∈ sieveUnits Q (M / d), 1 / ((d * k : ℕ) : ℝ) := by
      refine sum_congr rfl fun k hk => ?_
      have hcop := (mem_filter.mp hk).2
      rw [sieveClassPole, if_pos ⟨dvd_mul_right d k, by rwa [Nat.mul_div_cancel_left k hd]⟩,
        ← sq, poleVector_sq]
    _ = sieveClassMass Q d M := by
      rw [sieveClassMass, sievedHarmonic, sum_div]
      refine sum_congr rfl fun k _ => ?_
      push_cast
      ring

/-- The actual prime Gram in supported/unit coordinates, with its exact cutoff. -/
theorem primeBilinear_sieveClassPole_eq_sum
    {d e : ℕ} (hd : 0 < d) (he : 0 < e) (Q : Finset Nat.Primes) (M : ℕ) :
    primeBilinear M (sieveClassPole Q d) (sieveClassPole Q e) =
      ∑ k ∈ sieveUnits Q (M / d), ∑ l ∈ sieveUnits Q (M / e),
        poleVector (d * k) * poleVector (e * l) * weilPrimeKernel (d * k) (e * l) := by
  have houter : primeBilinear M (sieveClassPole Q d) (sieveClassPole Q e) =
      ∑ n ∈ Icc 1 M, sieveClassPole Q d n *
        ∑ m ∈ Icc 1 M, sieveClassPole Q e m * weilPrimeKernel n m := by
    unfold primeBilinear
    refine sum_congr rfl fun n _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun m _ => by ring
  rw [houter, sum_sieveClassPole_mul hd]
  refine sum_congr rfl fun k _ => ?_
  rw [sum_sieveClassPole_mul he, mul_sum]
  exact sum_congr rfl fun l _ => by ring

theorem poleVector_mul_nat (d k : ℕ) :
    poleVector (d * k) = poleVector d * poleVector k := by
  rw [poleVector, poleVector, poleVector, Nat.cast_mul,
    Real.sqrt_mul (Nat.cast_nonneg d)]
  simp only [one_div, mul_inv]

/-- Pole weighting removes the square roots from the two oriented divisor edges. -/
theorem poleWeighted_primeKernel_eq {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    poleVector m * poleVector n * weilPrimeKernel m n =
      (if m ∣ n then ArithmeticFunction.vonMangoldt (n / m) / n else 0) +
        (if n ∣ m then ArithmeticFunction.vonMangoldt (m / n) / m else 0) := by
  rw [poleVector_mul_poleVector_mul hm hn, weilPrimeKernel_mul_sqrt_ratio hm hn, add_div]
  congr 1
  · by_cases hmn : m ∣ n
    · by_cases heq : m = n
      · subst n
        simp [Nat.div_self hm, ArithmeticFunction.vonMangoldt_apply_one]
      · rw [if_pos ⟨hmn, heq⟩, if_pos hmn, div_div]
        congr 1
        exact_mod_cast Nat.div_mul_cancel hmn
    · rw [if_neg (fun h => hmn h.1), if_neg hmn, zero_div]
  · by_cases hnm : n ∣ m
    · by_cases heq : n = m
      · subst m
        simp [Nat.div_self hn, ArithmeticFunction.vonMangoldt_apply_one]
      · rw [if_pos ⟨hnm, heq⟩, if_pos hnm]
    · rw [if_neg (fun h => hnm h.1), if_neg hnm, zero_div]

/-- Every divisor of a sieve unit remains a sieve unit. -/
theorem sieveUnits_filter_dvd {Q : Finset Nat.Primes} {M n : ℕ}
    (hn : n ∈ sieveUnits Q M) :
    (sieveUnits Q M).filter (fun m => m ∣ n) = n.divisors := by
  obtain ⟨hnrange, hnunit⟩ := mem_filter.mp hn
  obtain ⟨hn0, hnM⟩ := mem_Icc.mp hnrange
  ext m
  simp only [sieveUnits, mem_filter, mem_Icc, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨_, _⟩, hmn⟩
    exact ⟨hmn, by omega⟩
  · rintro ⟨hmn, _⟩
    exact ⟨⟨⟨Nat.pos_of_dvd_of_pos hmn hn0,
      (Nat.le_of_dvd hn0 hmn).trans hnM⟩,
      Nat.Coprime.coprime_dvd_left hmn hnunit⟩, hmn⟩

/-- The exact prime Gram on the units is twice their logarithmic harmonic sum. -/
theorem primeBilinear_sieveUnitPole (Q : Finset Nat.Primes) (M : ℕ) :
    primeBilinear M (sieveClassPole Q 1) (sieveClassPole Q 1) =
      2 * ∑ n ∈ sieveUnits Q M, Real.log n / (n : ℝ) := by
  rw [primeBilinear_sieveClassPole_eq_sum (by norm_num) (by norm_num)]
  simp only [Nat.div_one, one_mul]
  have hterm : ∀ m ∈ sieveUnits Q M, ∀ n ∈ sieveUnits Q M,
      poleVector m * poleVector n * weilPrimeKernel m n =
        (if m ∣ n then ArithmeticFunction.vonMangoldt (n / m) / n else 0) +
          (if n ∣ m then ArithmeticFunction.vonMangoldt (m / n) / m else 0) := by
    intro m hm n hn
    exact poleWeighted_primeKernel_eq (mem_Icc.mp (mem_filter.mp hm).1).1
      (mem_Icc.mp (mem_filter.mp hn).1).1
  rw [sum_congr rfl fun m hm => sum_congr rfl fun n hn => hterm m hm n hn]
  simp_rw [sum_add_distrib]
  have hswap : (∑ m ∈ sieveUnits Q M, ∑ n ∈ sieveUnits Q M,
      if m ∣ n then ArithmeticFunction.vonMangoldt (n / m) / n else 0) =
      ∑ n ∈ sieveUnits Q M, ∑ m ∈ sieveUnits Q M,
        if m ∣ n then ArithmeticFunction.vonMangoldt (n / m) / n else 0 := sum_comm
  rw [hswap]
  have hrow : ∀ n ∈ sieveUnits Q M,
      (∑ m ∈ sieveUnits Q M,
        if m ∣ n then ArithmeticFunction.vonMangoldt (n / m) / n else 0) =
          Real.log n / (n : ℝ) := by
    intro n hn
    rw [← sum_filter, sieveUnits_filter_dvd hn, ← sum_div,
      Nat.sum_div_divisors n ArithmeticFunction.vonMangoldt, ArithmeticFunction.vonMangoldt_sum]
  rw [sum_congr rfl hrow]
  ring

/-- A class diagonal is the unit diagonal at the decimated horizon, scaled by `1/d`. -/
theorem primeBilinear_sieveClassPole_self {d : ℕ} (hd : 0 < d)
    (Q : Finset Nat.Primes) (M : ℕ) :
    primeBilinear M (sieveClassPole Q d) (sieveClassPole Q d) =
      (2 / (d : ℝ)) * ∑ n ∈ sieveUnits Q (M / d), Real.log n / (n : ℝ) := by
  have hscale : primeBilinear M (sieveClassPole Q d) (sieveClassPole Q d) =
      primeBilinear (M / d) (sieveClassPole Q 1) (sieveClassPole Q 1) / d := by
    rw [primeBilinear_sieveClassPole_eq_sum hd hd,
      primeBilinear_sieveClassPole_eq_sum (by norm_num) (by norm_num)]
    simp only [Nat.div_one, one_mul]
    rw [sum_div]
    refine sum_congr rfl fun k _ => ?_
    rw [sum_div]
    refine sum_congr rfl fun l _ => ?_
    rw [weilPrimeKernel_mul_left hd, poleVector_mul_nat, poleVector_mul_nat]
    linear_combination (poleVector k * poleVector l * weilPrimeKernel k l) * poleVector_sq d
  rw [hscale, primeBilinear_sieveUnitPole]
  ring

/-- Exact cross-class Gram; signed combinations retain the original prime kernel. -/
theorem primeBilinear_sieveClassPole_cross
    {Q : Finset Nat.Primes} {d e : ℕ}
    (hd : SieveSupported Q d) (he : SieveSupported Q e) (hde : d < e) (M : ℕ) :
    primeBilinear M (sieveClassPole Q d) (sieveClassPole Q e) =
      poleVector d * poleVector e * weilPrimeKernel d e * sievedHarmonic Q (M / e) := by
  rw [primeBilinear_sieveClassPole_eq_sum hd.pos he.pos, sum_comm,
    sievedHarmonic, mul_sum]
  refine sum_congr rfl fun l hl => ?_
  have hlunit : Nat.Coprime l (sievePrimorial Q) := (mem_filter.mp hl).2
  have hl0 : 0 < l := (mem_Icc.mp (mem_filter.mp hl).1).1
  have hlmem : l ∈ sieveUnits Q (M / d) := by
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨hl0, ?_⟩, hlunit⟩
    exact (mem_Icc.mp (mem_filter.mp hl).1).2.trans (Nat.div_le_div_left hde.le hd.pos)
  rw [sum_eq_single l]
  · rw [show weilPrimeKernel (d * l) (e * l) = weilPrimeKernel d e by
      simpa only [mul_comm] using weilPrimeKernel_mul_left hl0 d e,
      poleVector_mul_nat, poleVector_mul_nat]
    have hpole := poleVector_sq l
    linear_combination (poleVector d * poleVector e * weilPrimeKernel d e) * hpole
  · intro k hk hkl
    have hkunit : Nat.Coprime k (sievePrimorial Q) := (mem_filter.mp hk).2
    rw [weilPrimeKernel_sieveFactors_eq_zero hd he hkunit hlunit hde.ne hkl, mul_zero]
  · exact fun h => (h hlmem).elim

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
