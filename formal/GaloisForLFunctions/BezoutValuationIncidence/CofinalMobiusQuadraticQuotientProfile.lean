import GaloisForLFunctions.BezoutValuationIncidence.CoprimeSquarefreeDensityAndMobiusDilationMeans
import GaloisForLFunctions.TransHorizonIncidenceMechanics.CompositeSquarefreeStepAndMultiOctaveL2Energy
import GaloisForLFunctions.TransHorizonIncidenceMechanics.ComplementaryQuotientAndSecondOctaveLaw

/-!
# Cofinal quadratic quotient profile of the Möbius sieve

Write `Q_N(M) = sum_{1 <= k <= M} (sieveSeq N moebiusReal k)^2`.
For each fixed natural B, `Q_N((B+1)*N) / N` converges to the explicit
finite profile `cofinalMobiusQuadraticProfile B` as N tends to infinity.

For q,r in [1,B], put g=gcd(q,r) and l=lcm(q,r). The corresponding
profile term is `(B+1-max(q,r))/l` times the arithmetic mean of the two
Möbius dilations with multipliers r/g and q/g. That mean is their Möbius
product times the coprime-squarefree density, a finite Euler product.

The proof expands the finite complementary-quotient sum and reindexes
common multiples exactly. Both cutoff and horizon grow together. The
profile is monotone, is zero at B=0, and equals 6/pi^2 at B=1. The limit
is for each fixed B; no uniform rate for growing B is asserted.
-/

open Finset Filter
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open RHTower RHTower.Sieve
open scoped BigOperators Topology ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-- The contribution from a complementary quotient q above the cutoff N. -/
def moebiusQuotientBandTerm (N q k : ℕ) : ℝ :=
  if q ∣ k ∧ q * N < k then moebiusReal (k / q) else 0

/-- The finite prefix sum of a pair of Möbius dilations. -/
def moebiusDilationPairPrefix (a b M : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 M, moebiusReal (a * n) * moebiusReal (b * n)

/-- For positive q, the strict band condition is exactly the complementary-divisor cutoff. -/
theorem moebiusQuotientBandTerm_eq {N q k : ℕ} (hq : 0 < q) :
    moebiusQuotientBandTerm N q k =
      if q ∣ k ∧ N < k / q then moebiusReal (k / q) else 0 := by
  by_cases hd : q ∣ k
  · have heq : q * (k / q) = k := Nat.mul_div_cancel' hd
    have hi : q * N < k ↔ N < k / q := by
      constructor <;> intro h <;> nlinarith
    simp only [moebiusQuotientBandTerm, hd, true_and, hi]
  · simp [moebiusQuotientBandTerm, hd]

/-- The Möbius sieve on a bounded ratio of horizon to cutoff is a finite quotient sum. -/
theorem sieveSeq_moebiusReal_eq_quotient_band_sum {N B k : ℕ}
    (hk : 1 ≤ k) (hhi : k ≤ (B + 1) * N) :
    sieveSeq N moebiusReal k = (if k = 1 then 1 else 0) -
      ∑ q ∈ Finset.Icc 1 B, moebiusQuotientBandTerm N q k := by
  rw [sieveSeq_eq_sum_divisors_sub_complementaryQuotientTail N hk,
    sum_divisors_moebiusReal_eq_ite_one hk,
    complementaryQuotientTail_eq_sum_Icc_of_le_mul hhi, Finset.sum_filter]
  congr 1
  exact Finset.sum_congr rfl fun q hq =>
    (moebiusQuotientBandTerm_eq (Finset.mem_Icc.mp hq).1).symm

/-- Every positive quotient-band contribution vanishes at the unit when the cutoff is positive. -/
theorem moebiusQuotientBandTerm_one {N q : ℕ} (hN : 1 ≤ N) (hq : 1 ≤ q) :
    moebiusQuotientBandTerm N q 1 = 0 := by
  have hqN : 1 ≤ q * N := by nlinarith
  simp [moebiusQuotientBandTerm, not_lt.mpr hqN]

private theorem sum_Icc_tail_eq_sub {K M : ℕ} (hKM : K ≤ M) (f : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc 1 M, if K < k then f k else 0) =
      (∑ k ∈ Finset.Icc 1 M, f k) - ∑ k ∈ Finset.Icc 1 K, f k := by
  classical
  have hs : (Finset.Icc 1 M).filter (fun k => k ≤ K) = Finset.Icc 1 K := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 M) (fun k => k ≤ K) f
  rw [hs, Finset.sum_filter] at hsplit
  simp only [not_le] at hsplit
  linarith

/-- Common divisibility reindexes a Möbius pair into coprime multipliers through the lcm. -/
theorem sum_common_divisor_moebius_pair {q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (M : ℕ) :
    (∑ k ∈ Finset.Icc 1 M,
      if q ∣ k ∧ r ∣ k then moebiusReal (k / q) * moebiusReal (k / r) else 0) =
      moebiusDilationPairPrefix (r / Nat.gcd q r) (q / Nat.gcd q r)
        (M / Nat.lcm q r) := by
  classical
  have hlq : Nat.lcm q r = q * (r / Nat.gcd q r) := by
    rw [Nat.lcm_eq_mul_div, Nat.mul_div_assoc q (Nat.gcd_dvd_right q r)]
  have hlr : Nat.lcm q r = r * (q / Nat.gcd q r) := by
    rw [Nat.lcm_comm, Nat.lcm_eq_mul_div, Nat.gcd_comm,
      Nat.mul_div_assoc r (Nat.gcd_dvd_left q r)]
  simp_rw [← Nat.lcm_dvd_iff]
  rw [← Finset.sum_filter, sum_Icc_filter_dvd_eq_sum_Icc_div (Nat.lcm_pos hq hr)]
  unfold moebiusDilationPairPrefix
  apply Finset.sum_congr rfl
  intro n hn
  have hdivq : Nat.lcm q r * n / q = (r / Nat.gcd q r) * n := by
    rw [hlq, Nat.mul_assoc, Nat.mul_div_cancel_left _ hq]
  have hdivr : Nat.lcm q r * n / r = (q / Nat.gcd q r) * n := by
    rw [hlr, Nat.mul_assoc, Nat.mul_div_cancel_left _ hr]
  rw [hdivq, hdivr]

/-- A quotient pair contributes exactly the difference of two dilation prefixes. -/
theorem moebiusQuotientBandTerm_pair {N q r M : ℕ} (hq : 0 < q) (hr : 0 < r)
    (hM : max q r * N ≤ M) :
    (∑ k ∈ Finset.Icc 1 M, moebiusQuotientBandTerm N q k * moebiusQuotientBandTerm N r k) =
      moebiusDilationPairPrefix (r / Nat.gcd q r) (q / Nat.gcd q r)
        (M / Nat.lcm q r) -
      moebiusDilationPairPrefix (r / Nat.gcd q r) (q / Nat.gcd q r)
        (max q r * N / Nat.lcm q r) := by
  classical
  have hmax (k : ℕ) : max q r * N < k ↔ q * N < k ∧ r * N < k := by
    rcases le_total q r with h | h
    · rw [max_eq_right h]
      have hm := Nat.mul_le_mul_right N h
      omega
    · rw [max_eq_left h]
      have hm := Nat.mul_le_mul_right N h
      omega
  have hpoint (k : ℕ) :
      moebiusQuotientBandTerm N q k * moebiusQuotientBandTerm N r k =
        if max q r * N < k then
          (if q ∣ k ∧ r ∣ k then moebiusReal (k / q) * moebiusReal (k / r) else 0)
        else 0 := by
    simp only [hmax]
    by_cases hqk : q ∣ k <;> by_cases hrk : r ∣ k <;>
      by_cases hqN : q * N < k <;> by_cases hrN : r * N < k <;>
      simp [moebiusQuotientBandTerm, hqk, hrk, hqN, hrN]
  simp_rw [hpoint]
  rw [sum_Icc_tail_eq_sub hM, sum_common_divisor_moebius_pair hq hr,
    sum_common_divisor_moebius_pair hq hr]

/-- The exact quadratic energy on one quotient band is one plus a finite sum of dilation windows. -/
theorem sieveL2PrefixEnergy_moebiusReal_eq_quotient_pairs {N B M : ℕ}
    (hN : 1 ≤ N) (hM : 1 ≤ M) (hlo : B * N ≤ M) (hhi : M ≤ (B + 1) * N) :
    sieveL2PrefixEnergy N M moebiusReal = 1 +
      ∑ q ∈ Finset.Icc 1 B, ∑ r ∈ Finset.Icc 1 B,
        (moebiusDilationPairPrefix (r / Nat.gcd q r) (q / Nat.gcd q r)
          (M / Nat.lcm q r) -
        moebiusDilationPairPrefix (r / Nat.gcd q r) (q / Nat.gcd q r)
          (max q r * N / Nat.lcm q r)) := by
  classical
  have hpoint (k : ℕ) (hk : k ∈ Finset.Icc 1 M) :
      (sieveSeq N moebiusReal k) ^ 2 = (if k = 1 then 1 else 0) +
        (∑ q ∈ Finset.Icc 1 B, moebiusQuotientBandTerm N q k) ^ 2 := by
    rw [sieveSeq_moebiusReal_eq_quotient_band_sum (Finset.mem_Icc.mp hk).1
      ((Finset.mem_Icc.mp hk).2.trans hhi)]
    by_cases hk1 : k = 1
    · subst k
      have hz : (∑ q ∈ Finset.Icc 1 B, moebiusQuotientBandTerm N q 1) = 0 :=
        Finset.sum_eq_zero fun q hq => moebiusQuotientBandTerm_one hN (Finset.mem_Icc.mp hq).1
      simp [hz]
    · simp [hk1]
  unfold sieveL2PrefixEnergy
  rw [Finset.sum_congr rfl hpoint, Finset.sum_add_distrib]
  have hdelta : (∑ k ∈ Finset.Icc 1 M, if k = 1 then (1 : ℝ) else 0) = 1 := by
    simp [hM]
  rw [hdelta]
  congr 1
  simp_rw [pow_two, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  apply moebiusQuotientBandTerm_pair (Finset.mem_Icc.mp hq).1 (Finset.mem_Icc.mp hr).1
  exact (Nat.mul_le_mul_right N (max_le (Finset.mem_Icc.mp hq).2 (Finset.mem_Icc.mp hr).2)).trans hlo

/-- The explicit arithmetic mean of a pair of coprime Möbius dilations. -/
def moebiusDilationPairDensity (a b : ℕ) : ℝ :=
  moebiusReal a * moebiusReal b * coprimeSquarefreeDensity (a * b)

/-- A dilation-pair prefix at any fixed positive rational multiple of N has the expected linear mean. -/
theorem tendsto_moebiusDilationPairPrefix_scaled {a b A d : ℕ}
    (hab : Nat.Coprime a b) (hA : 0 < A) (hd : 0 < d) :
    Tendsto (fun N : ℕ => moebiusDilationPairPrefix a b (A * N / d) / (N : ℝ))
      atTop (𝓝 (((A : ℝ) / d) * moebiusDilationPairDensity a b)) := by
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hnat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hscale : Tendsto (fun N : ℕ => (A : ℝ) * N / d) atTop atTop := by
    have h := (tendsto_const_mul_atTop_of_pos (div_pos hAR hdR)).mpr hnat
    simpa only [div_mul_eq_mul_div] using h
  have hmean := ((tendsto_moebius_coprime_dilation_pair_mean hab).comp hscale).const_mul
    ((A : ℝ) / d)
  change Tendsto (fun N : ℕ => (A : ℝ) / d *
    (moebiusDilationPairPrefix a b ⌊(A : ℝ) * N / d⌋₊ / ((A : ℝ) * N / d)))
    atTop (𝓝 (((A : ℝ) / d) * moebiusDilationPairDensity a b)) at hmean
  apply hmean.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hfloor : ⌊(A : ℝ) * N / d⌋₊ = A * N / d := by
    rw [← Nat.cast_mul, Nat.floor_div_eq_div]
  rw [hfloor]
  field_simp

/-- The finite Euler-product profile for quadratic sieve energy at horizon (B+1)N. -/
def cofinalMobiusQuadraticProfile (B : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 B, ∑ r ∈ Finset.Icc 1 B,
    (((B : ℝ) + 1 - (max q r : ℕ)) / Nat.lcm q r) *
      moebiusDilationPairDensity (r / Nat.gcd q r) (q / Nat.gcd q r)

/-- For every fixed natural B, the actual growing-cutoff quadratic energy divided by N converges to its explicit profile. -/
theorem tendsto_sieveL2PrefixEnergy_moebiusReal_linear_horizon (B : ℕ) :
    Tendsto (fun N : ℕ => sieveL2PrefixEnergy N ((B + 1) * N) moebiusReal / (N : ℝ))
      atTop (𝓝 (cofinalMobiusQuadraticProfile B)) := by
  classical
  have hpair (q : ℕ) (hq : q ∈ Finset.Icc 1 B) (r : ℕ) (hr : r ∈ Finset.Icc 1 B) :
      Tendsto (fun N : ℕ =>
        (moebiusDilationPairPrefix (r / Nat.gcd q r) (q / Nat.gcd q r)
          ((B + 1) * N / Nat.lcm q r) -
        moebiusDilationPairPrefix (r / Nat.gcd q r) (q / Nat.gcd q r)
          (max q r * N / Nat.lcm q r)) / (N : ℝ))
      atTop (𝓝 ((((B : ℝ) + 1 - (max q r : ℕ)) / Nat.lcm q r) *
        moebiusDilationPairDensity (r / Nat.gcd q r) (q / Nat.gcd q r))) := by
    have hq0 : 0 < q := (Finset.mem_Icc.mp hq).1
    have hr0 : 0 < r := (Finset.mem_Icc.mp hr).1
    have hg : 0 < Nat.gcd q r := Nat.gcd_pos_of_pos_left r hq0
    have hcop : Nat.Coprime (r / Nat.gcd q r) (q / Nat.gcd q r) :=
      (Nat.coprime_div_gcd_div_gcd hg).symm
    have hl : 0 < Nat.lcm q r := Nat.lcm_pos hq0 hr0
    have hmax : 0 < max q r := hq0.trans_le (le_max_left _ _)
    have h := (tendsto_moebiusDilationPairPrefix_scaled hcop (Nat.succ_pos B) hl).sub
      (tendsto_moebiusDilationPairPrefix_scaled hcop hmax hl)
    convert h using 1
    · ext N
      ring
    · congr 1
      push_cast
      ring
  have hsum := tendsto_finsetSum (Finset.Icc 1 B) fun q hq =>
    tendsto_finsetSum (Finset.Icc 1 B) fun r hr => hpair q hq r hr
  have hinv : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop :
        Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  have htotal := hinv.add hsum
  simp only [zero_add] at htotal
  apply htotal.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hM : 1 ≤ (B + 1) * N := by nlinarith
  have hlo : B * N ≤ (B + 1) * N := Nat.mul_le_mul_right N (Nat.le_succ B)
  rw [sieveL2PrefixEnergy_moebiusReal_eq_quotient_pairs hN hM hlo le_rfl,
    add_div, Finset.sum_div]
  simp_rw [Finset.sum_div]

/-- At horizon N, the normalized quadratic energy has zero limit. -/
theorem cofinalMobiusQuadraticProfile_zero : cofinalMobiusQuadraticProfile 0 = 0 := by
  simp [cofinalMobiusQuadraticProfile]

/-- At horizon 2N, the quadratic profile is the squarefree density. -/
theorem cofinalMobiusQuadraticProfile_one : cofinalMobiusQuadraticProfile 1 = squarefreeDensity := by
  simp [cofinalMobiusQuadraticProfile, moebiusDilationPairDensity,
    moebiusReal, coprimeSquarefreeDensity_one]

/-- The cofinal quadratic profile is monotone in the horizon ratio. -/
theorem monotone_cofinalMobiusQuadraticProfile : Monotone cofinalMobiusQuadraticProfile := by
  intro B C hBC
  apply le_of_tendsto_of_tendsto
    (tendsto_sieveL2PrefixEnergy_moebiusReal_linear_horizon B)
    (tendsto_sieveL2PrefixEnergy_moebiusReal_linear_horizon C)
  apply Eventually.of_forall
  intro N
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  unfold sieveL2PrefixEnergy
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    obtain ⟨hk1, hkM⟩ := Finset.mem_Icc.mp hk
    exact Finset.mem_Icc.mpr ⟨hk1, hkM.trans
      (Nat.mul_le_mul_right N (Nat.add_le_add_right hBC 1))⟩
  · intro k hk hnot
    exact sq_nonneg _

/-- Every integer horizon ratio at least two has a profile at least the squarefree density. -/
theorem squarefreeDensity_le_cofinalMobiusQuadraticProfile {B : ℕ} (hB : 1 ≤ B) :
    squarefreeDensity ≤ cofinalMobiusQuadraticProfile B := by
  rw [← cofinalMobiusQuadraticProfile_one]
  exact monotone_cofinalMobiusQuadraticProfile hB
end
end GaloisForLFunctions.BezoutValuationIncidence
