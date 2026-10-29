import GaloisForLFunctions.ArithmeticCountingPositivity.FinitePrimeFlipsHavePositiveHarmonicDensity
import GaloisForLFunctions.TransHorizonIncidenceMechanics.MultiplicativeWeightsPretendingToOneArePaidOnlyByAVanishingLocalFactor
import Mathlib.NumberTheory.EulerProduct.Basic

/-!
# Unit conductor mass for finite prime flips

Möbius inversion makes each flipped prime contribute a geometric ladder.
The squared coefficients vanish off the supported conductors. A finite
Euler product sums their mass exactly, including all prime-power tails.
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.ArithmeticCountingPositivity

open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.BezoutValuationIncidence

private def finiteFlipAF (F : Finset ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else finiteFlip F n, by simp⟩

/-- The Möbius transform of a finite-prime sign, with value zero at zero. -/
def finiteFlipMobius (F : Finset ℕ) : ArithmeticFunction ℝ :=
  finiteFlipAF F * (ArithmeticFunction.moebius : ArithmeticFunction ℝ)

/-- The unnormalized squared conductor weight. -/
def finiteFlipSpectralWeight (F : Finset ℕ) (m : ℕ) : ℝ :=
  finiteFlipMobius F m ^ 2 / (m.totient : ℝ)

/-- The harmonic Ramanujan coefficient associated to a finite set of prime flips. -/
def finiteFlipConductorCoefficient (F : Finset ℕ) (m : ℕ) : ℝ :=
  finiteFlipHarmonicDensity F * finiteFlipMobius F m / Real.sqrt (m.totient : ℝ)

/-- Möbius inversion preserves multiplicativity of the finite-prime sign. -/
theorem finiteFlipMobius_isMultiplicative (F : Finset ℕ) :
    (finiteFlipMobius F).IsMultiplicative := by
  have hf : (finiteFlipAF F).IsMultiplicative := by
    constructor
    · simp [finiteFlipAF, finiteFlip]
    · intro m n hmn
      rcases eq_or_ne m 0 with rfl | hm
      · simp [finiteFlipAF]
      rcases eq_or_ne n 0 with rfl | hn
      · simp [finiteFlipAF]
      simp only [finiteFlipAF, ArithmeticFunction.coe_mk,
        if_neg hm, if_neg hn, if_neg (mul_ne_zero hm hn)]
      exact (finiteFlip_isSignGauge F).mul hm hn
  exact hf.mul ArithmeticFunction.isMultiplicative_moebius.intCast

/-- The coefficient transform is the literal finite Möbius divisor sum. -/
theorem finiteFlipMobius_eq_divisor_sum (F : Finset ℕ) (m : ℕ) :
    finiteFlipMobius F m =
      ∑ d ∈ m.divisors, moebiusReal (m / d) * finiteFlip F d := by
  rw [finiteFlipMobius, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b => finiteFlipAF F a *
      (ArithmeticFunction.moebius : ArithmeticFunction ℝ) b)]
  refine sum_congr rfl fun d hd => ?_
  simp only [finiteFlipAF, ArithmeticFunction.coe_mk,
    if_neg (Nat.pos_of_mem_divisors hd).ne', ArithmeticFunction.intCoe_apply, moebiusReal]
  ring

private theorem finiteFlipAF_prime_pow (F : Finset ℕ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    finiteFlipAF F (p ^ k) = if p ∈ F then (-1 : ℝ) ^ k else 1 := by
  simp only [finiteFlipAF, ArithmeticFunction.coe_mk, if_neg (pow_ne_zero _ hp.ne_zero)]
  by_cases hpF : p ∈ F
  · rw [if_pos hpF, finiteFlip, prod_eq_single p]
    · rw [hp.factorization_pow, Finsupp.single_eq_same]
    · intro q hq hqp
      rw [hp.factorization_pow, Finsupp.single_eq_of_ne hqp, pow_zero]
    · exact fun h => (h hpF).elim
  · rw [if_neg hpF, finiteFlip]
    refine prod_eq_one fun q hq => ?_
    rw [hp.factorization_pow,
      Finsupp.single_eq_of_ne (ne_of_mem_of_not_mem hq hpF), pow_zero]

/-- A prime-power Möbius coefficient is a signed two on a flipped ladder and zero otherwise. -/
theorem finiteFlipMobius_prime_pow (F : Finset ℕ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    finiteFlipMobius F (p ^ (k + 1)) =
      if p ∈ F then 2 * (-1 : ℝ) ^ (k + 1) else 0 := by
  rw [finiteFlipMobius,
    TransHorizonIncidenceMechanics.mul_moebius_apply_prime_pow (finiteFlipAF F) hp k,
    finiteFlipAF_prime_pow F hp, finiteFlipAF_prime_pow F hp]
  split_ifs
  · rw [pow_succ]
    ring
  · ring

/-- Squared coefficients retain exactly the set of prime divisors of the conductor. -/
theorem finiteFlipMobius_sq_eq_prod (F : Finset ℕ) {m : ℕ} (hm : m ≠ 0) :
    finiteFlipMobius F m ^ 2 =
      ∏ p ∈ m.primeFactors, (if p ∈ F then (4 : ℝ) else 0) := by
  let g := finiteFlipMobius F
  let v : ℕ → ℝ := fun p => if p ∈ F then 4 else 0
  have hg := finiteFlipMobius_isMultiplicative F
  have he : ArithmeticFunction.pmul g g = ArithmeticFunction.prodPrimeFactors v := by
    apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers
      (ArithmeticFunction.pmul g g) (hg.pmul hg)
      (ArithmeticFunction.prodPrimeFactors v)
      (ArithmeticFunction.IsMultiplicative.prodPrimeFactors v)).2
    intro p k hp
    change g (p ^ k) * g (p ^ k) = ArithmeticFunction.prodPrimeFactors v (p ^ k)
    cases k with
    | zero =>
        simpa only [pow_zero, g, hg.map_one, one_mul] using
          (ArithmeticFunction.IsMultiplicative.prodPrimeFactors v).map_one.symm
    | succ k =>
        change finiteFlipMobius F (p ^ (k + 1)) * finiteFlipMobius F (p ^ (k + 1)) = _
        rw [finiteFlipMobius_prime_pow F hp, ArithmeticFunction.prodPrimeFactors_apply
            (pow_ne_zero _ hp.ne_zero),
          Nat.primeFactors_prime_pow (by omega : k + 1 ≠ 0) hp, prod_singleton]
        split_ifs
        · have hs : ((-1 : ℝ) ^ (k + 1)) ^ 2 = 1 := by
            rw [sq, ← mul_pow]
            norm_num
          nlinarith only [hs]
        · norm_num
  have hh := congrArg (fun f : ArithmeticFunction ℝ => f m) he
  change g m * g m = ArithmeticFunction.prodPrimeFactors v m at hh
  rw [ArithmeticFunction.prodPrimeFactors_apply hm] at hh
  simpa only [g, v, sq] using hh

/-- The squared spectral weight is explicit on supported conductors and vanishes elsewhere. -/
theorem finiteFlipSpectralWeight_eq (F : Finset ℕ) (m : ℕ) :
    finiteFlipSpectralWeight F m = if m ∈ Nat.factoredNumbers F then
      (4 : ℝ) ^ m.primeFactors.card / (m.totient : ℝ) else 0 := by
  classical
  rcases eq_or_ne m 0 with rfl | hm
  · have hzero : (0 : ℕ) ∉ Nat.factoredNumbers F :=
      fun h => Nat.ne_zero_of_mem_factoredNumbers h rfl
    simp [finiteFlipSpectralWeight, hzero]
  rw [finiteFlipSpectralWeight, finiteFlipMobius_sq_eq_prod F hm]
  by_cases hs : m ∈ Nat.factoredNumbers F
  · rw [if_pos hs]
    congr 1
    calc
      _ = ∏ _p ∈ m.primeFactors, (4 : ℝ) :=
        prod_congr rfl fun p hp => if_pos (Nat.primeFactors_subset_of_mem_factoredNumbers hs hp)
      _ = _ := prod_const _
  · rw [if_neg hs]
    have hmiss : ∃ p ∈ m.primeFactors, p ∉ F := by
      by_contra h
      push Not at h
      apply hs
      exact ⟨hm, fun p hp => h p (Nat.mem_primeFactors_iff_mem_primeFactorsList.mpr hp)⟩
    obtain ⟨p, hp, hpF⟩ := hmiss
    rw [prod_eq_zero hp (if_neg hpF), zero_div]

private theorem spectralWeight_one (F : Finset ℕ) : finiteFlipSpectralWeight F 1 = 1 := by
  simp only [finiteFlipSpectralWeight, (finiteFlipMobius_isMultiplicative F).map_one,
    one_pow, Nat.totient_one, Nat.cast_one, div_one]

private theorem spectralWeight_mul (F : Finset ℕ) {m n : ℕ} (hmn : m.Coprime n) :
    finiteFlipSpectralWeight F (m * n) =
      finiteFlipSpectralWeight F m * finiteFlipSpectralWeight F n := by
  simp only [finiteFlipSpectralWeight,
    (finiteFlipMobius_isMultiplicative F).map_mul_of_coprime hmn,
    Nat.totient_mul hmn, Nat.cast_mul, mul_pow, mul_div_mul_comm]

private theorem spectralWeight_prime_pow (F : Finset ℕ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    finiteFlipSpectralWeight F (p ^ (k + 1)) =
      if p ∈ F then 4 / ((p : ℝ) ^ k * ((p : ℝ) - 1)) else 0 := by
  rw [finiteFlipSpectralWeight, finiteFlipMobius_prime_pow F hp]
  split_ifs
  · have hs : ((-1 : ℝ) ^ (k + 1)) ^ 2 = 1 := by
      rw [sq, ← mul_pow]
      norm_num
    rw [mul_pow, hs, mul_one, Nat.totient_prime_pow_succ hp,
      Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hp.one_le, Nat.cast_one]
    norm_num
  · simp

private theorem spectralWeight_nonneg (F : Finset ℕ) (m : ℕ) :
    0 ≤ finiteFlipSpectralWeight F m := div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

private theorem spectralWeight_ladder_hasSum (F : Finset ℕ) {p : ℕ} (hp : p.Prime) :
    HasSum (fun k : ℕ => finiteFlipSpectralWeight F (p ^ k))
      (1 + if p ∈ F then 4 * (p : ℝ) / ((p : ℝ) - 1) ^ 2 else 0) := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (p : ℝ) ≠ 0 := (lt_trans (by norm_num) hpR).ne'
  have hp1 : (p : ℝ) - 1 ≠ 0 := (sub_pos.mpr hpR).ne'
  have hx0 : 0 ≤ (p : ℝ)⁻¹ := by positivity
  have hx1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hpR
  have htail : HasSum (fun k : ℕ => finiteFlipSpectralWeight F (p ^ (k + 1)))
      (if p ∈ F then 4 * (p : ℝ) / ((p : ℝ) - 1) ^ 2 else 0) := by
    by_cases hpF : p ∈ F
    · have hgeom := (hasSum_geometric_of_lt_one hx0 hx1).mul_left (4 / ((p : ℝ) - 1))
      have he (k : ℕ) : 4 / ((p : ℝ) - 1) * ((p : ℝ)⁻¹) ^ k =
          finiteFlipSpectralWeight F (p ^ (k + 1)) := by
        rw [spectralWeight_prime_pow F hp, if_pos hpF, inv_pow]
        field_simp [hp0, hp1]
      have hv : 4 / ((p : ℝ) - 1) * (1 - (p : ℝ)⁻¹)⁻¹ =
          4 * (p : ℝ) / ((p : ℝ) - 1) ^ 2 := by
        field_simp [hp0, hp1]
      simpa only [he, hv, if_pos hpF] using hgeom
    · simp only [spectralWeight_prime_pow F hp, if_neg hpF]
      exact hasSum_zero
  have hs : Summable (fun k : ℕ => finiteFlipSpectralWeight F (p ^ k)) :=
    (summable_nat_add_iff 1).mp htail.summable
  have he : (∑' k : ℕ, finiteFlipSpectralWeight F (p ^ k)) =
      1 + if p ∈ F then 4 * (p : ℝ) / ((p : ℝ) - 1) ^ 2 else 0 := by
    rw [hs.tsum_eq_zero_add, htail.tsum_eq, pow_zero, spectralWeight_one]
  simpa only [he] using hs.hasSum

/-- The finite Euler product sums every supported conductor weight, including all tails. -/
theorem hasSum_finiteFlipSpectralWeight_supported (F : Finset ℕ)
    (hF : ∀ p ∈ F, p.Prime) :
    HasSum (fun m : Nat.factoredNumbers F => finiteFlipSpectralWeight F m)
      (∏ p ∈ F, (1 + 4 * (p : ℝ) / ((p : ℝ) - 1) ^ 2)) := by
  have hsum {p : ℕ} (hp : p.Prime) :
      Summable (fun k : ℕ => ‖finiteFlipSpectralWeight F (p ^ k)‖) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (spectralWeight_nonneg F _)] using
      (spectralWeight_ladder_hasSum F hp).summable
  have h := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (spectralWeight_one F) (fun hmn => spectralWeight_mul F hmn) hsum F).2
  have hfilter : F.filter Nat.Prime = F := filter_true_of_mem hF
  rw [hfilter] at h
  have hprod : (∏ p ∈ F, ∑' k : ℕ, finiteFlipSpectralWeight F (p ^ k)) =
      ∏ p ∈ F, (1 + 4 * (p : ℝ) / ((p : ℝ) - 1) ^ 2) := by
    exact prod_congr rfl fun p hp => by rw [(spectralWeight_ladder_hasSum F (hF p hp)).tsum_eq, if_pos hp]
  rwa [hprod] at h

/-- Squaring the normalized coefficient removes the totient square root exactly. -/
theorem finiteFlipConductorCoefficient_sq (F : Finset ℕ) (m : ℕ) :
    finiteFlipConductorCoefficient F m ^ 2 =
      finiteFlipHarmonicDensity F ^ 2 * finiteFlipSpectralWeight F m := by
  rw [finiteFlipConductorCoefficient, div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _),
    finiteFlipSpectralWeight]
  ring

/-- Every finite-prime constraint has exactly unit total squared arithmetic conductor mass. -/
theorem hasSum_finiteFlipConductorCoefficient_sq (F : Finset ℕ)
    (hF : ∀ p ∈ F, p.Prime) :
    HasSum (fun m : ℕ => finiteFlipConductorCoefficient F m ^ 2) 1 := by
  have hnorm : finiteFlipHarmonicDensity F ^ 2 *
      (∏ p ∈ F, (1 + 4 * (p : ℝ) / ((p : ℝ) - 1) ^ 2)) = 1 := by
    rw [finiteFlipHarmonicDensity, ← prod_pow, ← prod_mul_distrib]
    apply prod_eq_one
    intro p hp
    have hpR : (1 : ℝ) < p := by exact_mod_cast (hF p hp).one_lt
    have hp1 : (p : ℝ) - 1 ≠ 0 := (sub_pos.mpr hpR).ne'
    have hpplus : (p : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hp1, hpplus]
    ring
  have hs : HasSum (fun m : Nat.factoredNumbers F => finiteFlipConductorCoefficient F m ^ 2) 1 := by
    have h :=
      (hasSum_finiteFlipSpectralWeight_supported F hF).mul_left (finiteFlipHarmonicDensity F ^ 2)
    rw [hnorm] at h
    exact h.congr_fun fun m => finiteFlipConductorCoefficient_sq F m
  have hinj : Function.Injective (fun m : Nat.factoredNumbers F => (m : ℕ)) :=
    Subtype.val_injective
  have hz : ∀ m : ℕ, m ∉ Set.range (fun n : Nat.factoredNumbers F => (n : ℕ)) →
      finiteFlipConductorCoefficient F m ^ 2 = 0 := by
    intro m hm
    have hnot : m ∉ Nat.factoredNumbers F := fun h => hm ⟨⟨m, h⟩, rfl⟩
    rw [finiteFlipConductorCoefficient_sq, finiteFlipSpectralWeight_eq, if_neg hnot, mul_zero]
  exact (hinj.hasSum_iff hz).mp hs

end GaloisForLFunctions.ArithmeticCountingPositivity
