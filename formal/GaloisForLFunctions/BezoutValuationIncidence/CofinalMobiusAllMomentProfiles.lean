import GaloisForLFunctions.BezoutValuationIncidence.CoprimeMobiusSignAndEvenDilationMeans
import GaloisForLFunctions.BezoutValuationIncidence.CofinalMobiusOddMomentsAndQuotientProducts

/-!
# Complete arithmetic profiles for cofinal Möbius source moments

The existing quotient-tuple reindexing and odd-moment cancellation combine
with the unrestricted even dilation mean to determine every fixed source
moment on the literal horizon `(B+2)N`. The finite profile retains overlapping
prime supports and the exact unit-sample correction before taking the limit.

These moment profiles support the complete source-value law; separate value
counts and positive support still require their own proofs.
-/

open Filter Topology Finset ArithmeticFunction
open RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-- The finite Euler-product mean of a positive even tuple of Möbius dilations. -/
def moebiusEvenDilationDensity (r : ℕ) (a : Fin (2 * r + 2) → ℕ) : ℝ :=
  (∏ i, moebiusReal (a i)) * coprimeSquarefreeDensity (∏ i, a i)

private theorem even_dilation_prefix_scaled (r : ℕ) (a : Fin (2 * r + 2) → ℕ)
    {A d : ℕ} (hA : 0 < A) (hd : 0 < d) :
    Tendsto (fun N : ℕ => moebiusDilationProductPrefix a (A * N / d) / (N : ℝ))
      atTop (𝓝 (((A : ℝ) / d) * moebiusEvenDilationDensity r a)) := by
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hnat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hscale : Tendsto (fun N : ℕ => (A : ℝ) * N / d) atTop atTop := by
    have h := (tendsto_const_mul_atTop_of_pos (div_pos hAR hdR)).mpr hnat
    simpa only [div_mul_eq_mul_div] using h
  have hmean := ((tendsto_moebius_even_dilation_product_mean r a).comp hscale).const_mul
    ((A : ℝ) / d)
  change Tendsto (fun N : ℕ => (A : ℝ) / d *
    (moebiusDilationProductPrefix a ⌊(A : ℝ) * N / d⌋₊ / ((A : ℝ) * N / d)))
    atTop (𝓝 (((A : ℝ) / d) * moebiusEvenDilationDensity r a)) at hmean
  apply hmean.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hfloor : ⌊(A : ℝ) * N / d⌋₊ = A * N / d := by
    rw [← Nat.cast_mul, Nat.floor_div_eq_div]
  rw [hfloor]
  field_simp

private theorem even_quotient_prefix_limit {r B : ℕ} (q : Fin (2 * r + 2) → ℕ)
    (hq : ∀ i, 0 < q i) (hB : ∀ i, q i ≤ B + 1) :
    Tendsto (fun N : ℕ => moebiusQuotientProductPrefix N q ((B + 2) * N) / (N : ℝ))
      atTop (𝓝 ((((B + 2 : ℕ) : ℝ) - (quotientTupleMax q : ℝ)) /
        (quotientTupleLcm q : ℝ) *
          moebiusEvenDilationDensity r (fun i => quotientTupleLcm q / q i))) := by
  letI : Nonempty (Fin (2 * r + 2)) := ⟨⟨0, by omega⟩⟩
  have hL := quotientTupleLcm_pos q hq
  have hH := quotientTupleMax_pos q hq
  have hHB := quotientTupleMax_le q hB
  have hlim :=
    (even_dilation_prefix_scaled r (fun i => quotientTupleLcm q / q i)
      (show 0 < B + 2 by omega) hL).sub
    (even_dilation_prefix_scaled r (fun i => quotientTupleLcm q / q i) hH hL)
  have heq (N : ℕ) : moebiusQuotientProductPrefix N q ((B + 2) * N) / (N : ℝ) =
      moebiusDilationProductPrefix (fun i => quotientTupleLcm q / q i)
        ((B + 2) * N / quotientTupleLcm q) / (N : ℝ) -
      moebiusDilationProductPrefix (fun i => quotientTupleLcm q / q i)
        (quotientTupleMax q * N / quotientTupleLcm q) / (N : ℝ) := by
    rw [moebiusQuotientProductPrefix_eq q hq
      (Nat.mul_le_mul_right N (hHB.trans (by omega))), sub_div]
  simp_rw [heq]
  simpa only [← sub_mul, ← sub_div] using hlim

-- The unit sample contributes one; all other terms come from quotient bands.
private theorem source_even_power_expansion (r B N : ℕ) (hN : 1 ≤ N) :
    (∑ k ∈ Finset.Icc 1 ((B + 2) * N), (sieveSeq N moebiusReal k) ^ (2 * r + 2)) =
      1 + ∑ q ∈ Fintype.piFinset (fun _ : Fin (2 * r + 2) => Finset.Icc 1 (B + 1)),
        moebiusQuotientProductPrefix N q ((B + 2) * N) := by
  classical
  have hM : 1 ≤ (B + 2) * N := by nlinarith
  have hpoint (k : ℕ) (hk : k ∈ Finset.Icc 1 ((B + 2) * N)) :
      (sieveSeq N moebiusReal k) ^ (2 * r + 2) = (if k = 1 then 1 else 0) +
        (∑ q ∈ Finset.Icc 1 (B + 1), moebiusQuotientBandTerm N q k) ^ (2 * r + 2) := by
    rw [sieveSeq_moebiusReal_eq_quotient_band_sum (Finset.mem_Icc.mp hk).1
      (Finset.mem_Icc.mp hk).2]
    by_cases hk1 : k = 1
    · subst k
      have hz : (∑ q ∈ Finset.Icc 1 (B + 1), moebiusQuotientBandTerm N q 1) = 0 :=
        Finset.sum_eq_zero fun q hq => moebiusQuotientBandTerm_one hN (Finset.mem_Icc.mp hq).1
      simp [hz]
    · simp [hk1, pow_add, pow_mul]
  rw [Finset.sum_congr rfl hpoint, Finset.sum_add_distrib]
  have hdelta : (∑ k ∈ Finset.Icc 1 ((B + 2) * N), if k = 1 then (1 : ℝ) else 0) = 1 := by
    simp [hM]
  rw [hdelta]
  congr 1
  unfold moebiusQuotientProductPrefix
  simp_rw [Finset.sum_pow']
  rw [Finset.sum_comm]

/-- The exact arithmetic profile for every positive even moment on the literal linear horizon. -/
def cofinalMobiusEvenMomentProfile (B r : ℕ) : ℝ :=
  ∑ q ∈ Fintype.piFinset (fun _ : Fin (2 * r + 2) => Finset.Icc 1 (B + 1)),
    (((B + 2 : ℕ) : ℝ) - (quotientTupleMax q : ℝ)) / (quotientTupleLcm q : ℝ) *
      moebiusEvenDilationDensity r (fun i => quotientTupleLcm q / q i)

/-- All fixed positive even source moments have their explicit finite arithmetic limits. -/
theorem tendsto_sieveSeq_even_moment_linear_horizon (B r : ℕ) :
    Tendsto (fun N : ℕ =>
      (∑ k ∈ Finset.Icc 1 ((B + 2) * N), (sieveSeq N moebiusReal k) ^ (2 * r + 2)) /
        (N : ℝ)) atTop (𝓝 (cofinalMobiusEvenMomentProfile B r)) := by
  classical
  have hsum : Tendsto (fun N : ℕ =>
      ∑ q ∈ Fintype.piFinset (fun _ : Fin (2 * r + 2) => Finset.Icc 1 (B + 1)),
        moebiusQuotientProductPrefix N q ((B + 2) * N) / (N : ℝ))
      atTop (𝓝 (cofinalMobiusEvenMomentProfile B r)) := by
    exact tendsto_finsetSum _ fun q hq => even_quotient_prefix_limit q
      (fun i => (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hq i)).1)
      (fun i => (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hq i)).2)
  have hinv : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop :
        Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  have h := hinv.add hsum
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  rw [source_even_power_expansion r B N hN, add_div, Finset.sum_div]

/-- One arithmetic profile for constants, odd moments, and positive even moments. -/
def cofinalMobiusMomentProfile (B m : ℕ) : ℝ :=
  if m = 0 then ((B + 2 : ℕ) : ℝ)
  else if m % 2 = 0 then cofinalMobiusEvenMomentProfile B (m / 2 - 1)
  else 0

/-- Every fixed monomial of the literal source has its specified arithmetic mean. -/
theorem tendsto_sieveSeq_moment_linear_horizon (B m : ℕ) :
    Tendsto (fun N : ℕ =>
      (∑ k ∈ Finset.Icc 1 ((B + 2) * N), (sieveSeq N moebiusReal k) ^ m) / (N : ℝ))
      atTop (𝓝 (cofinalMobiusMomentProfile B m)) := by
  by_cases hm0 : m = 0
  · subst m
    change Tendsto (fun N : ℕ =>
      (∑ k ∈ Finset.Icc 1 ((B + 2) * N), (sieveSeq N moebiusReal k) ^ 0) / (N : ℝ))
      atTop (𝓝 (((B + 2 : ℕ) : ℝ)))
    apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => ((B + 2 : ℕ) : ℝ))
      atTop (𝓝 (((B + 2 : ℕ) : ℝ)))).congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    simp only [pow_zero, Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc,
      Nat.add_sub_cancel, Nat.cast_mul]
    field_simp
  · by_cases he : m % 2 = 0
    · have hm : m = 2 * (m / 2 - 1) + 2 := by omega
      simp only [cofinalMobiusMomentProfile, if_neg hm0, if_pos he]
      simpa only [← hm] using tendsto_sieveSeq_even_moment_linear_horizon B (m / 2 - 1)
    · have hm : m = 2 * (m / 2) + 1 := by omega
      simp only [cofinalMobiusMomentProfile, if_neg hm0, if_neg he]
      simpa only [← hm] using tendsto_sieveSeq_odd_moment_linear_horizon (B + 1) (m / 2)

end
end GaloisForLFunctions.BezoutValuationIncidence
