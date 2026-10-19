import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiBoundedPrimeCapacityObservability

/-!
# Arbitrary dyadic-antichain supports and the forward capacity bound

A coefficient packet seen through the horizon `N` is admissible for a set of
allowed primes when two distinct active indices in `[1,N]` never share their odd
part, and every prime factor of an active odd part is allowed. Every admissible
packet agrees on `[1,N]` with a literal parameterized antichain coefficient:
the odd parts form the support, each odd part carries the valuation of its unique
active index, and the normalized amplitude is the coefficient divided by that
index. Conversely every parameterized antichain coefficient is admissible.

Both native physical energies only read coefficients in `[1,N]`. Hence the
finite-prime constant `8 * B^2` and the reciprocal-capacity constant
`8 * exp(6*M)` hold for every admissible signed packet and every horizon.
-/

open scoped BigOperators
open Finset GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics
noncomputable section
set_option autoImplicit false

/-- Dyadic-antichain packets whose active odd parts have only allowed prime factors. -/
def fermiDyadicAntichainAdmissible (allowed : Set ℕ) (N : ℕ) (c : ℕ → ℝ) : Prop :=
  (∀ n ∈ Icc 1 N, ∀ m ∈ Icc 1 N, c n ≠ 0 → c m ≠ 0 →
      n / 2 ^ n.factorization 2 = m / 2 ^ m.factorization 2 → n = m) ∧
    ∀ n ∈ Icc 1 N, c n ≠ 0 → ∀ p ∈ (n / 2 ^ n.factorization 2).primeFactors, p ∈ allowed

/-- The full native sieve energy reads only the coefficients inside the horizon. -/
theorem sieveTotalPronicEnergy_congr_Icc {N : ℕ} {c b : ℕ → ℝ}
    (h : ∀ d ∈ Icc 1 N, c d = b d) :
    sieveTotalPronicEnergy N c = sieveTotalPronicEnergy N b := by
  have hs (k : ℕ) : sieveSeq N c k = sieveSeq N b k :=
    Finset.sum_congr rfl (fun d hd => h d (Finset.mem_filter.mp hd).1)
  simp only [sieveTotalPronicEnergy, sievePairedPronicEnergy, hs]

/-- The selected native Fermi energy reads only the coefficients inside the horizon. -/
theorem fermiSelectedTotalPronicEnergy_congr_Icc {N : ℕ} {c b : ℕ → ℝ}
    (h : ∀ d ∈ Icc 1 N, c d = b d) :
    fermiSelectedTotalPronicEnergy N c = fermiSelectedTotalPronicEnergy N b := by
  have hr (n : ℕ) : fermiCellResponse N c n = fermiCellResponse N b n :=
    Finset.sum_congr rfl (fun d hd => by rw [h d hd])
  simp only [fermiSelectedTotalPronicEnergy, fermiSelectedPronicEnergy, fermiBoundaryJump, hr]

private theorem odd_part_odd {n : ℕ} (hn : n ≠ 0) : Odd (n / 2 ^ n.factorization 2) :=
  Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (Nat.not_dvd_ordCompl Nat.prime_two hn))

private theorem odd_part_two_pow_mul {k d : ℕ} (hd : Odd d) :
    2 ^ k * d / 2 ^ (2 ^ k * d).factorization 2 = d := by
  have hd0 : d ≠ 0 := by obtain ⟨a, ha⟩ := hd; omega
  have hv : (2 ^ k * d).factorization 2 = k := by
    rw [Nat.factorization_mul (by positivity) hd0, Finsupp.add_apply, Nat.factorization_pow,
      Finsupp.smul_apply, Nat.prime_two.factorization_self,
      Nat.factorization_eq_zero_of_not_dvd (fun h2 => (Nat.not_even_iff_odd.mpr hd)
        (even_iff_two_dvd.mpr h2))]
    simp
  rw [hv, Nat.mul_div_cancel_left _ (by positivity)]

private theorem active_index {S : Finset ℕ} {j : S → ℕ} {a : S → ℝ} {n : ℕ}
    (h : fermiDyadicAntichainCoefficient S j a n ≠ 0) :
    ∃ d : S, n = 2 ^ (j d) * (d : ℕ) := by
  by_contra hn
  exact h (Finset.sum_eq_zero (fun d _ => if_neg (fun hd => hn ⟨d, hd⟩)))

/-- Every parameterized odd-support antichain coefficient is admissible at every horizon. -/
theorem fermiDyadicAntichainCoefficient_admissible (allowed : Set ℕ) (N : ℕ)
    (S : Finset ℕ) (j : S → ℕ) (a : S → ℝ) (hS : ∀ d ∈ S, Odd d)
    (hSP : ∀ d ∈ S, ∀ p ∈ d.primeFactors, p ∈ allowed) :
    fermiDyadicAntichainAdmissible allowed N (fermiDyadicAntichainCoefficient S j a) := by
  constructor
  · intro n _ m _ hn hm hnm
    obtain ⟨d, rfl⟩ := active_index hn
    obtain ⟨e, rfl⟩ := active_index hm
    rw [odd_part_two_pow_mul (hS d d.2), odd_part_two_pow_mul (hS e e.2)] at hnm
    rw [Subtype.ext hnm]
  · intro n _ hn
    obtain ⟨d, rfl⟩ := active_index hn
    rw [odd_part_two_pow_mul (hS d d.2)]
    exact hSP d d.2

/-- Every admissible packet is, inside its horizon, a literal parameterized antichain. -/
theorem exists_fermiDyadicAntichain_representation (allowed : Set ℕ) (N : ℕ) (c : ℕ → ℝ)
    (hc : fermiDyadicAntichainAdmissible allowed N c) :
    ∃ (S : Finset ℕ) (j : S → ℕ) (a : S → ℝ),
      (∀ d ∈ S, Odd d) ∧ (∀ d ∈ S, ∀ p ∈ d.primeFactors, p ∈ allowed) ∧
      (∀ d : S, 2 ^ (j d) * (d : ℕ) ≤ N) ∧
      (∀ n ∈ Icc 1 N, fermiDyadicAntichainCoefficient S j a n = c n) ∧
      ((∀ n, 0 ≤ c n) → ∀ d, 0 ≤ a d) := by
  classical
  obtain ⟨hanti, hprime⟩ := hc
  let A := (Icc 1 N).filter (fun n => c n ≠ 0)
  let S := A.image (fun n => n / 2 ^ n.factorization 2)
  have hpick (d : S) : ∃ n ∈ A, n / 2 ^ n.factorization 2 = (d : ℕ) :=
    Finset.mem_image.mp d.2
  choose rep hrepA hrep using hpick
  have hmemA (d : S) := Finset.mem_filter.mp (hrepA d)
  have hrep0 (d : S) : rep d ≠ 0 := by
    have := (Finset.mem_Icc.mp (hmemA d).1).1
    omega
  have hidx (d : S) : 2 ^ (rep d).factorization 2 * (d : ℕ) = rep d := by
    rw [← hrep d]
    exact Nat.ordProj_mul_ordCompl_eq_self (rep d) 2
  refine ⟨S, fun d => (rep d).factorization 2, fun d => c (rep d) / (rep d : ℝ),
    ?_, ?_, ?_, ?_, ?_⟩
  · intro d hd
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hd
    have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
    exact odd_part_odd (by omega)
  · intro d hd
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hd
    exact hprime n (Finset.mem_filter.mp hn).1 (Finset.mem_filter.mp hn).2
  · intro d
    rw [hidx d]
    exact (Finset.mem_Icc.mp (hmemA d).1).2
  · intro n hn
    have hterm (d : S) :
        (if n = 2 ^ (rep d).factorization 2 * (d : ℕ) then
          (2 : ℝ) ^ (rep d).factorization 2 * (d : ℝ) * (c (rep d) / (rep d : ℝ)) else 0) =
        if n = rep d then c n else 0 := by
      have hr : (2 : ℝ) ^ (rep d).factorization 2 * (d : ℝ) = (rep d : ℝ) := by
        exact_mod_cast hidx d
      rw [hidx d, hr, mul_div_cancel₀ _ (by exact_mod_cast hrep0 d)]
      split_ifs with h
      · rw [h]
      · rfl
    unfold fermiDyadicAntichainCoefficient
    simp only [hterm]
    by_cases hcn : c n = 0
    · rw [hcn]
      simp
    · have hnA : n ∈ A := Finset.mem_filter.mpr ⟨hn, hcn⟩
      let d0 : S := ⟨n / 2 ^ n.factorization 2, Finset.mem_image_of_mem _ hnA⟩
      have hiff (d : S) : n = rep d ↔ d = d0 := by
        constructor
        · intro h
          apply Subtype.ext
          change (d : ℕ) = n / 2 ^ n.factorization 2
          rw [h, hrep d]
        · intro h
          subst h
          exact (hanti (rep d0) (hmemA d0).1 n hn (hmemA d0).2 hcn (hrep d0)).symm
      simp only [hiff, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · intro hnn d
    exact div_nonneg (hnn _) (Nat.cast_nonneg _)

/-- Both homogeneous ray energies read only the coefficients inside the horizon. -/
theorem homogeneousEnergies_congr_Icc {N : ℕ} {c b : ℕ → ℝ}
    (h : ∀ d ∈ Icc 1 N, c d = b d) :
    sieveHomogeneousEnergy N c = sieveHomogeneousEnergy N b ∧
      fermiSelectedHomogeneousEnergy N c = fermiSelectedHomogeneousEnergy N b := by
  have hs (k : ℕ) : sieveSeq N c k = sieveSeq N b k :=
    Finset.sum_congr rfl (fun d hd => h d (Finset.mem_filter.mp hd).1)
  have hr (n : ℕ) : fermiCellResponse N c n = fermiCellResponse N b n :=
    Finset.sum_congr rfl (fun d hd => by rw [h d hd])
  constructor <;> simp only [sieveHomogeneousEnergy, fermiSelectedHomogeneousEnergy,
    fermiNormalizedDyadicSieve, fermiNormalizedDyadicJump, fermiBoundaryJump, hs, hr]

/-- Homogeneous finite-prime law `P_h ≤ 4 B^2 Q_h` for every admissible signed packet. -/
theorem fermiDyadicAntichainAdmissible_finitePrime_homogeneous_bound (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (N : ℕ) (c : ℕ → ℝ)
    (hc : fermiDyadicAntichainAdmissible (P : Set ℕ) N c) :
    sieveHomogeneousEnergy N c ≤
      4 * (∏ p ∈ P, ((p : ℝ) + 1) / ((p : ℝ) - 1))^2 * fermiSelectedHomogeneousEnergy N c := by
  obtain ⟨S, j, a, hS, hSP, hN, heq, -⟩ :=
    exists_fermiDyadicAntichain_representation (P : Set ℕ) N c hc
  rw [← (homogeneousEnergies_congr_Icc heq).1, ← (homogeneousEnergies_congr_Icc heq).2]
  let A : ℝ := ∏ p ∈ P, ((p : ℝ) - 1) / ((p : ℝ) + 1)
  let B : ℝ := ∏ p ∈ P, ((p : ℝ) + 1) / ((p : ℝ) - 1)
  have hBA : B * A = 1 := by
    dsimp only [A, B]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro p hp
    have hp1 : 1 < (p : ℝ) := by exact_mod_cast (hP p hp).one_lt
    field_simp [(sub_pos.mpr hp1).ne', show (p : ℝ) + 1 ≠ 0 by linarith]
  have h := fermiDyadicAntichain_prime_homogeneous_bounds N P S j a hP hS
    (fun d hd p hp => hSP d hd p hp) hN
  change _ ≤ 4 * B^2 * _
  calc
    _ ≤ fermiOddHomogeneousMass * B * (4/3) * (∑ d : S, (a d)^2) := h.2
    _ = 4 * B^2 * (fermiOddHomogeneousMass * A * (1/3) * (∑ d : S, (a d)^2)) := by
      calc
        _ = fermiOddHomogeneousMass * B * (4/3) * (∑ d : S, (a d)^2) * (B * A) := by
          rw [hBA, mul_one]
        _ = _ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h.1 (by positivity)

/-- Uniform native observability on every admissible signed packet over a finite prime set. -/
theorem fermiDyadicAntichainAdmissible_finitePrime_physical_bound (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (N : ℕ) (c : ℕ → ℝ)
    (hc : fermiDyadicAntichainAdmissible (P : Set ℕ) N c) :
    sieveTotalPronicEnergy N c ≤
      8 * (∏ p ∈ P, ((p : ℝ) + 1) / ((p : ℝ) - 1))^2 * fermiSelectedTotalPronicEnergy N c := by
  obtain ⟨S, j, a, hS, hSP, hN, heq, -⟩ :=
    exists_fermiDyadicAntichain_representation (P : Set ℕ) N c hc
  rw [← sieveTotalPronicEnergy_congr_Icc heq, ← fermiSelectedTotalPronicEnergy_congr_Icc heq]
  exact fermiDyadicAntichain_finitePrime_physical_bound N P S j a hP hS
    (fun d hd p hp => hSP d hd p hp) hN

/-- Bounded reciprocal capacity gives `8 * exp(6*M)` for every admissible signed packet. -/
theorem fermiDyadicAntichainAdmissible_boundedCapacity_physical_bound
    (allowed : Set ℕ) (hallowed : ∀ p ∈ allowed, p.Prime ∧ Odd p) (M : ℝ)
    (hcap : ∀ P : Finset ℕ, (∀ p ∈ P, p ∈ allowed) → (∑ p ∈ P, 1 / (p : ℝ)) ≤ M)
    (N : ℕ) (c : ℕ → ℝ) (hc : fermiDyadicAntichainAdmissible allowed N c) :
    sieveTotalPronicEnergy N c ≤
      8 * Real.exp (6 * M) * fermiSelectedTotalPronicEnergy N c := by
  obtain ⟨S, j, a, hS, hSP, hN, heq, -⟩ :=
    exists_fermiDyadicAntichain_representation allowed N c hc
  rw [← sieveTotalPronicEnergy_congr_Icc heq, ← fermiSelectedTotalPronicEnergy_congr_Icc heq]
  exact fermiDyadicAntichain_boundedCapacity_physical_bound allowed hallowed M hcap N S j a
    hS hSP hN

end
end GaloisForLFunctions.TransHorizonIncidenceMechanics
