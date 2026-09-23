import GaloisForLFunctions.RHTower.EulerDeletionPrimeCountEndpointVariance
import GaloisForLFunctions.RHTower.EulerDeletionCoefficientPrefixEnergy
/-!
# Full physical transfer for the prime-count endpoint derivative

Möbius inversion expresses the literal endpoint derivative as finite
prime-power packets. The vector-valued identity retains every mixed term;
its scalar specialization retains harmonic balancing. The endpoint error
against any coefficient model obeys the complete-tail prefix-energy bound.

These finite identities and inequalities assume no arithmetic cancellation
estimate. They do not prove the asymptotics or signed covariance bound
required for RH.
-/

noncomputable section
set_option autoImplicit false
open Finset ArithmeticFunction Filter Topology
open scoped BigOperators
namespace RHTower.DeletionCoefficientTransfer
private theorem range_shift_eq_Icc {E : Type*} [AddCommMonoid E] (F : ℕ → E) (N : ℕ) :
    (∑ i ∈ range N,F (i+1)) = ∑ n ∈ Icc 1 N,F n := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,ih,Finset.sum_Icc_succ_top (by omega)]

/-- The same closed estimate applies to the actual endpoint error against any coefficient model. -/
theorem endpointJet_error_energy_le (c : ℕ → ℝ) (N T : ℕ) :
    ‖PrimeCountDamping.endpointJet N-source c N‖^(2 : ℕ) ≤
      4*(T : ℝ)*(prefixEnvelope (fun n => PrimeCountDamping.jetCoeff n-c n) N*
        harmonicMass N)^(2 : ℕ)+mass (fun n => PrimeCountDamping.jetCoeff n-c n) N^(2 : ℕ)/((T : ℝ)+1) := by
  have he : source (fun n => PrimeCountDamping.jetCoeff n-c n) N =
      PrimeCountDamping.endpointJet N-source c N := by
    unfold source
    simp only [Complex.ofReal_sub,sub_smul,sum_sub_distrib]
    congr 1
    unfold PrimeCountDamping.endpointJet
    rw [← range_shift_eq_Icc]
    simp only [Nat.cast_add,Nat.cast_one]
  rw [← he]
  exact source_energy_le_envelope _ N T

end RHTower.DeletionCoefficientTransfer

namespace RHTower.PrimeCountDamping

/-- Möbius inversion retains the complete prime-power forcing. -/
theorem jetCoeff_eq_primePower_convolution {n : ℕ} (hn : n  ≠  0) :
    jetCoeff n = -∑ q ∈ n.divisors,
      if IsPrimePow q then (moebius (n/q) : ℝ) else 0 := by
  have h := (sum_eq_iff_sum_mul_moebius_eq (f := jetCoeff)
    (g := fun n => if IsPrimePow n then (-1 : ℝ) else 0)).mp
    (fun n hn => sum_divisors_jet (by omega)) n (by omega)
  rw [Nat.sum_divisorsAntidiagonal' (f := fun x y => (moebius x : ℝ) *
    (if IsPrimePow y then (-1 : ℝ) else 0))] at h
  rw [← h, ← sum_neg_distrib]
  apply sum_congr rfl
  intro q hq
  split_ifs  <;> ring


/-- The convolution identity with its full vector-valued test; no norm is taken. -/
theorem sum_jetCoeff_smul {E : Type*} [AddCommGroup E] [Module ℝ E]
    (N : ℕ) (F : ℕ → E) :
    (∑ n ∈ Icc 1 N,jetCoeff n • F n) =
      -∑ q ∈ Icc 1 N,if IsPrimePow q then
        ∑ m ∈ Icc 1 (N/q),(moebius m : ℝ) • F (q*m) else 0 := by
  have hswap := Sieve.sum_divisors_swap N (fun q m =>
    if IsPrimePow q then (moebius m : ℝ) • F (q*m) else 0)
  calc
    _ = -∑ n ∈ Icc 1 N,∑ q ∈ n.divisors,
        if IsPrimePow q then (moebius (n/q) : ℝ) • F (q*(n/q)) else 0 := by
      rw [← sum_neg_distrib]
      apply sum_congr rfl
      intro n hn
      rw [jetCoeff_eq_primePower_convolution (by have := (mem_Icc.mp hn).1; omega),
        neg_smul,sum_smul]
      congr 1
      apply sum_congr rfl
      intro q hq
      rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hq)]
      split_ifs <;> simp
    _ = _ := by
      rw [hswap]
      congr 1
      apply sum_congr rfl
      intro q hq
      split_ifs <;> simp_all

/-- Exact prime-power forcing of the literal endpoint derivative in its original carrier. -/
theorem endpointJet_eq_primePower_packets (N : ℕ) :
    endpointJet N = -∑ q ∈ Icc 1 N,if IsPrimePow q then
      ∑ m ∈ Icc 1 (N/q),(moebius m : ℂ) • bdGen (1/((q*m : ℕ) : ℝ)) else 0 := by
  have h := sum_jetCoeff_smul N (fun n => bdGen (1/(n : ℝ)))
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ)] at h
  convert! h using 1

/-- Harmonic balancing is retained exactly under the same prime-power convolution. -/
theorem jetHarmonic_eq_primePower_harmonic (N : ℕ) :
    jetHarmonic N = -∑ q ∈ Icc 1 N,if IsPrimePow q then
      deningerHarmonicPartial (N/q)/(q : ℝ) else 0 := by
  have h := sum_jetCoeff_smul N (fun n => (1/(n : ℝ)))
  simp only [smul_eq_mul,mul_one_div] at h
  change jetHarmonic N = _ at h
  rw [h]
  congr 1
  apply sum_congr rfl
  intro q hq
  split_ifs
  · rw [deningerHarmonicPartial_eq_sum_Icc,sum_div]
    apply sum_congr rfl
    intro m hm
    push_cast
    ring
  · rfl

end RHTower.PrimeCountDamping
