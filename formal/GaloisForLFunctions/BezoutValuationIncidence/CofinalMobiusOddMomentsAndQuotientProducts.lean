import GaloisForLFunctions.BezoutValuationIncidence.CoprimeMobiusCancellationAndOddDilationMeans
import GaloisForLFunctions.BezoutValuationIncidence.CofinalMobiusQuadraticQuotientProfile
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GCDMonoid.Finset

/-!
# Cofinal odd moments of the Möbius sieve

For every fixed pair of natural numbers B and r, the sum of the
`(2*r+1)`-st powers of `sieveSeq N moebiusReal k` over `1 <= k <= (B+1)N`,
divided by N, tends to zero as N tends to infinity.

The finite quotient expansion reduces a source power to finitely many
products of complementary-quotient contributions. A tuple q has common
multiple L and maximum H; its exact contribution is a Möbius dilation
product summed between the natural divisions HN/L and M/L. Every odd
product has zero mean by coprime Möbius cancellation, with no coprimality
assumptions on the tuple of multipliers. The unit contributes only 1/N.

The limits hold at each fixed horizon ratio and each fixed odd order.
They do not by themselves assert convergence of the even moments or of
individual sign-class densities.
-/

open Finset Filter
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open RHTower RHTower.Sieve
open scoped BigOperators Topology ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

private theorem sum_Icc_quotient_tail_eq_sub {K M : ℕ} (hKM : K ≤ M) (f : ℕ → ℝ) :
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

section Tuples
variable {ι : Type*} [Fintype ι]

/-- The common-multiple scale of a finite tuple of complementary quotients. -/
def quotientTupleLcm (q : ι → ℕ) : ℕ := Finset.univ.lcm q

/-- The largest quotient in a finite tuple, with zero for the empty tuple. -/
def quotientTupleMax (q : ι → ℕ) : ℕ := Finset.univ.sup q

/-- The finite prefix of a product of Möbius dilations. -/
def moebiusDilationProductPrefix (a : ι → ℕ) (M : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 M, ∏ i, moebiusReal (a i * n)

/-- The finite prefix of a product of complementary-quotient band contributions. -/
def moebiusQuotientProductPrefix (N : ℕ) (q : ι → ℕ) (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 M, ∏ i, moebiusQuotientBandTerm N (q i) k

/-- A tuple of positive quotients has a positive common-multiple scale. -/
theorem quotientTupleLcm_pos (q : ι → ℕ) (hq : ∀ i, 0 < q i) : 0 < quotientTupleLcm q := by
  apply Nat.pos_of_ne_zero
  exact Finset.lcm_ne_zero_iff.mpr fun i _ => (hq i).ne'

/-- A nonempty tuple of positive quotients has a positive maximum. -/
theorem quotientTupleMax_pos [Nonempty ι] (q : ι → ℕ) (hq : ∀ i, 0 < q i) :
    0 < quotientTupleMax q := by
  classical
  obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset ι) Finset.univ_nonempty q
  change 0 < Finset.univ.sup q
  rw [heq]
  exact hq i

/-- A common upper bound for the tuple also bounds its maximum. -/
theorem quotientTupleMax_le {B : ℕ} (q : ι → ℕ) (hq : ∀ i, q i ≤ B) :
    quotientTupleMax q ≤ B := Finset.sup_le_iff.mpr fun i _ => hq i

/-- A nonempty tuple is supported exactly on its common multiples above its largest band cutoff. -/
theorem moebiusQuotientBandTerm_prod [Nonempty ι] (N : ℕ) (q : ι → ℕ) (k : ℕ) :
    (∏ i, moebiusQuotientBandTerm N (q i) k) =
      if quotientTupleMax q * N < k then
        (if quotientTupleLcm q ∣ k then ∏ i, moebiusReal (k / q i) else 0)
      else 0 := by
  classical
  by_cases hd : quotientTupleLcm q ∣ k
  · rw [if_pos hd]
    by_cases hmax : quotientTupleMax q * N < k
    · rw [if_pos hmax]
      apply Finset.prod_congr rfl
      intro i hi
      have hdiv : q i ∣ k := (Finset.dvd_lcm (f := q) (Finset.mem_univ i)).trans hd
      have hle : q i ≤ quotientTupleMax q := Finset.le_sup (f := q) (Finset.mem_univ i)
      have hlt : q i * N < k := (Nat.mul_le_mul_right N hle).trans_lt hmax
      exact if_pos ⟨hdiv, hlt⟩
    · rw [if_neg hmax]
      obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset ι) Finset.univ_nonempty q
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      unfold moebiusQuotientBandTerm
      apply if_neg
      intro h
      apply hmax
      change Finset.univ.sup q * N < k
      rw [heq]
      exact h.2
  · rw [if_neg hd, ite_self]
    have hex : ∃ i, ¬ q i ∣ k := by
      by_contra h
      have hall : ∀ i, q i ∣ k := by
        intro i
        by_contra hi
        exact h ⟨i, hi⟩
      exact hd (Finset.lcm_dvd fun i _ => hall i)
    obtain ⟨i, hi⟩ := hex
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    unfold moebiusQuotientBandTerm
    exact if_neg (fun h => hi h.1)

/-- Reindexing common multiples converts a finite quotient product into a dilation product. -/
theorem sum_common_divisor_moebius_product (q : ι → ℕ) (hq : ∀ i, 0 < q i) (M : ℕ) :
    (∑ k ∈ Finset.Icc 1 M,
      if quotientTupleLcm q ∣ k then ∏ i, moebiusReal (k / q i) else 0) =
      moebiusDilationProductPrefix (fun i => quotientTupleLcm q / q i) (M / quotientTupleLcm q) := by
  classical
  rw [← Finset.sum_filter,
    sum_Icc_filter_dvd_eq_sum_Icc_div (quotientTupleLcm_pos q hq)]
  unfold moebiusDilationProductPrefix
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.prod_congr rfl
  intro i hi
  have hdiv : q i ∣ quotientTupleLcm q := Finset.dvd_lcm (f := q) (Finset.mem_univ i)
  have hfac : q i * (quotientTupleLcm q / q i) = quotientTupleLcm q := Nat.mul_div_cancel' hdiv
  have heq : quotientTupleLcm q * n / q i = (quotientTupleLcm q / q i) * n := by
    calc
      _ = (q i * (quotientTupleLcm q / q i)) * n / q i :=
        congrArg (fun t : ℕ => t * n / q i) hfac.symm
      _ = _ := by rw [Nat.mul_assoc, Nat.mul_div_cancel_left _ (hq i)]
  rw [heq]

/-- The exact tuple contribution is the difference of two dilation-product prefixes. -/
theorem moebiusQuotientProductPrefix_eq [Nonempty ι] {N M : ℕ} (q : ι → ℕ)
    (hq : ∀ i, 0 < q i) (hM : quotientTupleMax q * N ≤ M) :
    moebiusQuotientProductPrefix N q M =
      moebiusDilationProductPrefix (fun i => quotientTupleLcm q / q i) (M / quotientTupleLcm q) -
      moebiusDilationProductPrefix (fun i => quotientTupleLcm q / q i)
        (quotientTupleMax q * N / quotientTupleLcm q) := by
  unfold moebiusQuotientProductPrefix
  simp_rw [moebiusQuotientBandTerm_prod]
  rw [sum_Icc_quotient_tail_eq_sub hM, sum_common_divisor_moebius_product q hq,
    sum_common_divisor_moebius_product q hq]

end Tuples

/-- An odd dilation-product prefix at any fixed positive rational multiple of N is o(N). -/
theorem tendsto_moebiusOddDilationProductPrefix_scaled (r : ℕ) (a : Fin (2 * r + 1) → ℕ)
    {A d : ℕ} (hA : 0 < A) (hd : 0 < d) :
    Tendsto (fun N : ℕ => moebiusDilationProductPrefix a (A * N / d) / (N : ℝ))
      atTop (𝓝 0) := by
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hnat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hscale : Tendsto (fun N : ℕ => (A : ℝ) * N / d) atTop atTop := by
    have h := (tendsto_const_mul_atTop_of_pos (div_pos hAR hdR)).mpr hnat
    simpa only [div_mul_eq_mul_div] using h
  have hmean := ((tendsto_moebius_odd_dilation_product_mean r a).comp hscale).const_mul
    ((A : ℝ) / d)
  simp only [mul_zero] at hmean
  change Tendsto (fun N : ℕ => (A : ℝ) / d *
    (moebiusDilationProductPrefix a ⌊(A : ℝ) * N / d⌋₊ / ((A : ℝ) * N / d)))
    atTop (𝓝 0) at hmean
  apply hmean.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hfloor : ⌊(A : ℝ) * N / d⌋₊ = A * N / d := by
    rw [← Nat.cast_mul, Nat.floor_div_eq_div]
  rw [hfloor]
  field_simp

/-- Every fixed odd quotient tuple contributes o(N) on a fixed linear horizon. -/
theorem tendsto_moebiusQuotientProductPrefix_odd {r B : ℕ} (q : Fin (2 * r + 1) → ℕ)
    (hq : ∀ i, 0 < q i) (hB : ∀ i, q i ≤ B) :
    Tendsto (fun N : ℕ => moebiusQuotientProductPrefix N q ((B + 1) * N) / (N : ℝ))
      atTop (𝓝 0) := by
  letI : Nonempty (Fin (2 * r + 1)) := ⟨⟨0, by omega⟩⟩
  have hL := quotientTupleLcm_pos q hq
  have hH := quotientTupleMax_pos q hq
  have hHB := quotientTupleMax_le q hB
  have hlim :=
    (tendsto_moebiusOddDilationProductPrefix_scaled r
      (fun i => quotientTupleLcm q / q i) (Nat.succ_pos B) hL).sub
    (tendsto_moebiusOddDilationProductPrefix_scaled r
      (fun i => quotientTupleLcm q / q i) hH hL)
  have heq (N : ℕ) : moebiusQuotientProductPrefix N q ((B + 1) * N) / (N : ℝ) =
      moebiusDilationProductPrefix (fun i => quotientTupleLcm q / q i)
        ((B + 1) * N / quotientTupleLcm q) / (N : ℝ) -
      moebiusDilationProductPrefix (fun i => quotientTupleLcm q / q i)
        (quotientTupleMax q * N / quotientTupleLcm q) / (N : ℝ) := by
    rw [moebiusQuotientProductPrefix_eq q hq
      (Nat.mul_le_mul_right N (hHB.trans (Nat.le_succ B))), sub_div]
  simp_rw [heq]
  simpa only [sub_zero] using hlim

/-- The finite set of all odd-length tuples of quotients from one bounded band. -/
def moebiusQuotientTupleSet (r B : ℕ) : Finset (Fin (2 * r + 1) → ℕ) :=
  Fintype.piFinset fun _ => Finset.Icc 1 B

/-- The exact odd source moment is one minus a finite sum of quotient-product prefixes. -/
theorem sum_sieveSeq_odd_power_eq_quotient_products (r B N : ℕ) (hN : 1 ≤ N) :
    (∑ k ∈ Finset.Icc 1 ((B + 1) * N), (sieveSeq N moebiusReal k) ^ (2 * r + 1)) =
      1 - ∑ q ∈ moebiusQuotientTupleSet r B,
        moebiusQuotientProductPrefix N q ((B + 1) * N) := by
  classical
  have hM : 1 ≤ (B + 1) * N := by nlinarith
  have hpoint (k : ℕ) (hk : k ∈ Finset.Icc 1 ((B + 1) * N)) :
      (sieveSeq N moebiusReal k) ^ (2 * r + 1) = (if k = 1 then 1 else 0) -
        (∑ q ∈ Finset.Icc 1 B, moebiusQuotientBandTerm N q k) ^ (2 * r + 1) := by
    rw [sieveSeq_moebiusReal_eq_quotient_band_sum (Finset.mem_Icc.mp hk).1
      (Finset.mem_Icc.mp hk).2]
    by_cases hk1 : k = 1
    · subst k
      have hz : (∑ q ∈ Finset.Icc 1 B, moebiusQuotientBandTerm N q 1) = 0 :=
        Finset.sum_eq_zero fun q hq => moebiusQuotientBandTerm_one hN (Finset.mem_Icc.mp hq).1
      simp [hz]
    · simp [hk1, pow_add, pow_mul]
  rw [Finset.sum_congr rfl hpoint, Finset.sum_sub_distrib]
  have hdelta : (∑ k ∈ Finset.Icc 1 ((B + 1) * N), if k = 1 then (1 : ℝ) else 0) = 1 := by
    simp [hM]
  rw [hdelta]
  congr 1
  unfold moebiusQuotientTupleSet moebiusQuotientProductPrefix
  simp_rw [Finset.sum_pow']
  rw [Finset.sum_comm]

/-- Every fixed odd moment of the growing-cutoff Möbius sieve is o(N) on every fixed integer linear horizon. -/
theorem tendsto_sieveSeq_odd_moment_linear_horizon (B r : ℕ) :
    Tendsto (fun N : ℕ =>
      (∑ k ∈ Finset.Icc 1 ((B + 1) * N), (sieveSeq N moebiusReal k) ^ (2 * r + 1)) / (N : ℝ))
      atTop (𝓝 0) := by
  classical
  have hsum : Tendsto (fun N : ℕ =>
      ∑ q ∈ moebiusQuotientTupleSet r B,
        moebiusQuotientProductPrefix N q ((B + 1) * N) / (N : ℝ)) atTop (𝓝 0) := by
    have h := tendsto_finsetSum (moebiusQuotientTupleSet r B) fun q hq =>
      tendsto_moebiusQuotientProductPrefix_odd q
        (fun i => (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hq i)).1)
        (fun i => (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hq i)).2)
    simpa using h
  have hinv : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop :
        Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  have h := hinv.sub hsum
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  rw [sum_sieveSeq_odd_power_eq_quotient_products r B N hN, sub_div, Finset.sum_div]
end
end GaloisForLFunctions.BezoutValuationIncidence
