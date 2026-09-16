import GaloisForLFunctions.RHTower.MobiusDivisorLatePrimeCompensation
import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovTunedMinLogGram

/-!
# Positive gcd-completion barrier for literal Möbius--divisor Abel channels

The inclusive gcd kernel has an exact totient-square factorization, so it is
positive despite signed channel coefficients.  This module proves its literal
late-prime diagonal is at least a fixed fraction of squared late-prime mass.
Thus this positive completion cannot be a quadratic-scale controller for the
completed source: it retains an unavoidable superlinear prime diagonal.
-/

noncomputable section
open Finset Filter Topology
namespace RHTower

/-- The inclusive gcd-kernel quadratic form of the literal signed Abel channels. -/
def mobiusDivisorInclusiveGcdGram (M : ℕ) : ℝ :=
  ∑ a ∈ Icc 1 M ×ˢ Icc 1 M,
    (Nat.gcd a.1 a.2 : ℝ) * mobiusDivisorDilationChannel M a.1 *
      mobiusDivisorDilationChannel M a.2

/-- Gauss factorization proves positivity without discarding any channel. -/
theorem mobiusDivisorInclusiveGcdGram_eq_totient_sq (M : ℕ) :
    mobiusDivisorInclusiveGcdGram M =
      ∑ g ∈ Icc 1 M, (Nat.totient g : ℝ) *
        (∑ d ∈ (Icc 1 M).filter (fun d => g ∣ d),
          mobiusDivisorDilationChannel M d) ^ 2 := by
  unfold mobiusDivisorInclusiveGcdGram
  exact RHTower.Sieve.sum_gcd_mul_weight_eq_sum_totient_mul_sq
    (mobiusDivisorDilationChannel M)
    (fun d hd => (mem_Icc.mp hd).1)
    (fun d hd => (mem_Icc.mp hd).2)

theorem mobiusDivisorInclusiveGcdGram_nonneg (M : ℕ) :
    0 ≤ mobiusDivisorInclusiveGcdGram M := by
  rw [mobiusDivisorInclusiveGcdGram_eq_totient_sq]
  exact sum_nonneg fun g _ => mul_nonneg (by positivity) (sq_nonneg _)

/-- Above half the cutoff a divisor class has only its prime generator. -/
private theorem late_prime_divisor_filter {M p : ℕ} (hp : p.Prime)
    (hpM : p ≤ M) (hM : M < 2 * p) :
    (Icc 1 M).filter (fun d => p ∣ d) = {p} := by
  ext d
  simp only [mem_filter, mem_Icc, mem_singleton]
  constructor
  · rintro ⟨⟨hd1, hdM⟩, hpd⟩
    obtain ⟨k, hk⟩ := hpd
    have hkpos : 0 < k := by
      by_contra hk0
      have hkzero : k = 0 := by omega
      rw [hkzero, Nat.mul_zero] at hk
      omega
    have hkone : k = 1 := by
      by_contra hkone
      have hktwo : 2 ≤ k := by omega
      have htwo : 2 * p ≤ d := by
        rw [hk]
        simpa [Nat.mul_comm] using Nat.mul_le_mul_left p hktwo
      omega
    calc d = p * k := hk
      _ = p := by simp [hkone]
  · intro h
    subst d
    exact ⟨⟨hp.pos, hpM⟩, dvd_rfl⟩

/-- The totient square at a late prime is its uncancellable literal diagonal. -/
private theorem late_prime_totient_component {N p : ℕ}
    (hp : p ∈ GaloisForLFunctions.HTGeometry.primesInIoc (2 * N) (4 * N)) :
    (Nat.totient p : ℝ) *
        (∑ d ∈ (Icc 1 (4 * N)).filter (fun d => p ∣ d),
          mobiusDivisorDilationChannel (4 * N) d) ^ 2 =
      ((p - 1 : ℕ) : ℝ) * (divisorUnsignedDilationChannel (4 * N) p) ^ 2 := by
  obtain ⟨hpp, hpL, hpR⟩ := GaloisForLFunctions.HTGeometry.mem_primesInIoc hp
  rw [late_prime_divisor_filter hpp hpR (by omega), sum_singleton,
    Nat.totient_prime hpp, mobiusDivisorDilationChannel_eq_moebius_unsigned,
    ArithmeticFunction.moebius_apply_prime hpp]
  push_cast
  ring

/-- The full positive gcd Gram contains every late prime's literal totient diagonal. -/
private theorem sum_late_prime_totient_diagonal_le_inclusiveGcdGram (N : ℕ) :
    (∑ p ∈ GaloisForLFunctions.HTGeometry.primesInIoc (2 * N) (4 * N),
      ((p - 1 : ℕ) : ℝ) * (divisorUnsignedDilationChannel (4 * N) p) ^ 2) ≤
      mobiusDivisorInclusiveGcdGram (4 * N) := by
  rw [mobiusDivisorInclusiveGcdGram_eq_totient_sq]
  calc
    _ = ∑ p ∈ GaloisForLFunctions.HTGeometry.primesInIoc (2 * N) (4 * N),
      (Nat.totient p : ℝ) *
        (∑ d ∈ (Icc 1 (4 * N)).filter (fun d => p ∣ d),
          mobiusDivisorDilationChannel (4 * N) d) ^ 2 := by
        apply sum_congr rfl
        intro p hp
        exact (late_prime_totient_component hp).symm
    _ ≤ ∑ g ∈ Icc 1 (4 * N), (Nat.totient g : ℝ) *
        (∑ d ∈ (Icc 1 (4 * N)).filter (fun d => g ∣ d),
          mobiusDivisorDilationChannel (4 * N) d) ^ 2 := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro p hp
          obtain ⟨hpp, _, hpR⟩ := GaloisForLFunctions.HTGeometry.mem_primesInIoc hp
          exact mem_Icc.mpr ⟨hpp.pos, hpR⟩
        · intro g _ _
          exact mul_nonneg (by positivity) (sq_nonneg _)

/-- Cauchy's inequality transfers known late-prime mass to its square mass. -/
private theorem late_prime_mass_sq_le_five_mul_square_mass (N : ℕ) (hN : 1 ≤ N) :
    (mobiusDivisorLatePrimeMass (4 * N)) ^ 2 ≤
      (5 * N : ℝ) *
        ∑ p ∈ GaloisForLFunctions.HTGeometry.primesInIoc (2 * N) (4 * N),
          (divisorUnsignedDilationChannel (4 * N) p) ^ 2 := by
  let L := GaloisForLFunctions.HTGeometry.primesInIoc (2 * N) (4 * N)
  have hcard : (L.card : ℝ) ≤ (5 * N : ℝ) := by
    have hsub : L ⊆ range (4 * N + 1) := by
      intro p hp
      obtain ⟨_, _, hpR⟩ := GaloisForLFunctions.HTGeometry.mem_primesInIoc hp
      exact mem_range.mpr (by omega)
    have hcardNat : L.card ≤ 5 * N := by
      calc L.card ≤ (range (4 * N + 1)).card := card_le_card hsub
        _ = 4 * N + 1 := card_range _
        _ ≤ 5 * N := by omega
    exact_mod_cast hcardNat
  have hcs := sq_sum_le_card_mul_sum_sq (s := L)
    (f := fun p => divisorUnsignedDilationChannel (4 * N) p)
  have hsum0 : 0 ≤ ∑ p ∈ L, (divisorUnsignedDilationChannel (4 * N) p) ^ 2 :=
    sum_nonneg fun _ _ => sq_nonneg _
  have hbound : (∑ p ∈ L, divisorUnsignedDilationChannel (4 * N) p) ^ 2 ≤
      (5 * N : ℝ) * ∑ p ∈ L, (divisorUnsignedDilationChannel (4 * N) p) ^ 2 :=
    by exact hcs.trans (mul_le_mul_of_nonneg_right hcard hsum0)
  unfold mobiusDivisorLatePrimeMass
  have hhalf : (4 * N) / 2 = 2 * N := by omega
  rw [hhalf]
  exact hbound

/-- A fixed positive fraction of squared late-prime mass is forced into every inclusive gcd Gram. -/
theorem two_fifths_late_prime_mass_sq_le_inclusiveGcdGram (N : ℕ) (hN : 1 ≤ N) :
    (2 / 5 : ℝ) * (mobiusDivisorLatePrimeMass (4 * N)) ^ 2 ≤
      mobiusDivisorInclusiveGcdGram (4 * N) := by
  let L := GaloisForLFunctions.HTGeometry.primesInIoc (2 * N) (4 * N)
  let U := fun p => divisorUnsignedDilationChannel (4 * N) p
  have hsq := late_prime_mass_sq_le_five_mul_square_mass N hN
  have hweight :
      (∑ p ∈ L, ((2 * N : ℕ) : ℝ) * (U p) ^ 2) ≤
        ∑ p ∈ L, ((p - 1 : ℕ) : ℝ) * (U p) ^ 2 := by
    apply sum_le_sum
    intro p hp
    obtain ⟨_, hpL, _⟩ := GaloisForLFunctions.HTGeometry.mem_primesInIoc hp
    have hcoef : ((2 * N : ℕ) : ℝ) ≤ ((p - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 2 * N ≤ p - 1 by omega)
    exact mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
  have hscaled :
      (2 / 5 : ℝ) * (mobiusDivisorLatePrimeMass (4 * N)) ^ 2 ≤
        ∑ p ∈ L, ((2 * N : ℕ) : ℝ) * (U p) ^ 2 := by
    calc
      _ ≤ (2 / 5 : ℝ) * ((5 * N : ℝ) * ∑ p ∈ L, (U p) ^ 2) :=
        mul_le_mul_of_nonneg_left hsq (by norm_num)
      _ = ∑ p ∈ L, ((2 * N : ℕ) : ℝ) * (U p) ^ 2 := by
        have htwo : ((2 * N : ℕ) : ℝ) = 2 * (N : ℝ) := by norm_num
        calc
          (2 / 5 : ℝ) * ((5 * N : ℝ) * ∑ p ∈ L, (U p) ^ 2) =
              (2 * (N : ℝ)) * ∑ p ∈ L, (U p) ^ 2 := by
                ring
          _ = _ := by rw [← htwo, mul_sum]
  calc
    _ ≤ ∑ p ∈ L, ((2 * N : ℕ) : ℝ) * (U p) ^ 2 := hscaled
    _ ≤ ∑ p ∈ L, ((p - 1 : ℕ) : ℝ) * (U p) ^ 2 := hweight
    _ ≤ mobiusDivisorInclusiveGcdGram (4 * N) :=
      sum_late_prime_totient_diagonal_le_inclusiveGcdGram N

end RHTower
