import GaloisForLFunctions.BezoutValuationIncidence.CofinalMobiusAllMomentProfiles
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Adjacent real-horizon transport of cofinal Möbius moments

For `A=B+2+t`, every fixed source moment on the literal horizon `floor(A*N)`,
normalized by N, interpolates affinely between the adjacent integer profiles.
One fixed upper quotient set handles the interval, including its endpoints;
limit uniqueness identifies those endpoints with the existing integer laws.

Individual value frequencies require the separate finite-alphabet extraction.
-/

open Filter Topology Finset ArithmeticFunction
open RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

private def dilation_density (m : ℕ) (a : Fin m → ℕ) : ℝ :=
  if m % 2 = 0 then (∏ i, moebiusReal (a i)) * coprimeSquarefreeDensity (∏ i, a i) else 0

private theorem dilation_mean {m : ℕ} (hm : 0 < m) (a : Fin m → ℕ) :
    Tendsto (fun x : ℝ => moebiusDilationProductPrefix a ⌊x⌋₊ / x)
      atTop (𝓝 (dilation_density m a)) := by
  by_cases he : m % 2 = 0
  · obtain ⟨r, rfl⟩ : ∃ r : ℕ, m = 2 * r + 2 := ⟨m / 2 - 1, by omega⟩
    simpa only [dilation_density, if_pos he, moebiusDilationProductPrefix, moebiusReal] using
      tendsto_moebius_even_dilation_product_mean r a
  · obtain ⟨r, rfl⟩ : ∃ r : ℕ, m = 2 * r + 1 := ⟨m / 2, by omega⟩
    simpa only [dilation_density, if_neg he, moebiusDilationProductPrefix, moebiusReal] using
      tendsto_moebius_odd_dilation_product_mean r a

private theorem dilation_prefix_real_scaled {m : ℕ} (hm : 0 < m) (a : Fin m → ℕ)
    (A : ℝ) (d : ℕ) (hA : 0 < A) (hd : 0 < d) :
    Tendsto (fun N : ℕ => moebiusDilationProductPrefix a (⌊A * N⌋₊ / d) / (N : ℝ))
      atTop (𝓝 ((A / d) * dilation_density m a)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hnat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hscale : Tendsto (fun N : ℕ => A * N / d) atTop atTop := by
    have h := (tendsto_const_mul_atTop_of_pos (div_pos hA hdR)).mpr hnat
    simpa only [div_mul_eq_mul_div] using h
  have hmean := ((dilation_mean hm a).comp hscale).const_mul (A / d)
  change Tendsto (fun N : ℕ => (A / d) *
    (moebiusDilationProductPrefix a ⌊A * N / d⌋₊ / (A * N / d)))
    atTop (𝓝 ((A / d) * dilation_density m a)) at hmean
  apply hmean.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  rw [Nat.floor_div_natCast]
  field_simp

private theorem horizon_bounds (B N : ℕ) (t : Set.Icc (0 : ℝ) 1) :
    (B + 2) * N ≤ ⌊(((B + 2 : ℕ) : ℝ) + (t : ℝ)) * N⌋₊ ∧
      ⌊(((B + 2 : ℕ) : ℝ) + (t : ℝ)) * N⌋₊ ≤ (B + 3) * N := by
  have hlo : (((B + 2) * N : ℕ) : ℝ) ≤
      (((B + 2 : ℕ) : ℝ) + (t : ℝ)) * N := by
    rw [Nat.cast_mul]
    nlinarith [mul_nonneg t.property.1 (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hhi : (((B + 2 : ℕ) : ℝ) + (t : ℝ)) * N ≤ (((B + 3) * N : ℕ) : ℝ) := by
    have hB : ((B + 3 : ℕ) : ℝ) = ((B + 2 : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [Nat.cast_mul, hB]
    nlinarith [mul_nonneg (show 0 ≤ 1 - (t : ℝ) by linarith [t.property.2])
      (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  constructor
  · simpa only [Nat.floor_natCast] using Nat.floor_mono hlo
  · simpa only [Nat.floor_natCast] using Nat.floor_mono hhi

private theorem quotient_prefix_real_limit {B m : ℕ} (hm : 0 < m)
    (t : Set.Icc (0 : ℝ) 1) (q : Fin m → ℕ)
    (hq : ∀ i, 0 < q i) (hB : ∀ i, q i ≤ B + 2) :
    Tendsto (fun N : ℕ => moebiusQuotientProductPrefix N q
      ⌊(((B + 2 : ℕ) : ℝ) + (t : ℝ)) * N⌋₊ / (N : ℝ)) atTop
      (𝓝 (((((B + 2 : ℕ) : ℝ) + (t : ℝ)) - (quotientTupleMax q : ℝ)) /
        (quotientTupleLcm q : ℝ) *
          dilation_density m (fun i => quotientTupleLcm q / q i))) := by
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hL := quotientTupleLcm_pos q hq
  have hH := quotientTupleMax_pos q hq
  have hHB := quotientTupleMax_le q hB
  have hA : 0 < ((B + 2 : ℕ) : ℝ) + (t : ℝ) := by
    have := t.property.1
    positivity
  have hlow := dilation_prefix_real_scaled hm (fun i => quotientTupleLcm q / q i)
    (quotientTupleMax q : ℝ) (quotientTupleLcm q) (by exact_mod_cast hH) hL
  simp only [← Nat.cast_mul, Nat.floor_natCast] at hlow
  have hlim := (dilation_prefix_real_scaled hm (fun i => quotientTupleLcm q / q i)
    (((B + 2 : ℕ) : ℝ) + (t : ℝ)) (quotientTupleLcm q) hA hL).sub hlow
  have heq (N : ℕ) : moebiusQuotientProductPrefix N q
      ⌊(((B + 2 : ℕ) : ℝ) + (t : ℝ)) * N⌋₊ / (N : ℝ) =
      moebiusDilationProductPrefix (fun i => quotientTupleLcm q / q i)
        (⌊(((B + 2 : ℕ) : ℝ) + (t : ℝ)) * N⌋₊ / quotientTupleLcm q) / (N : ℝ) -
      moebiusDilationProductPrefix (fun i => quotientTupleLcm q / q i)
        (quotientTupleMax q * N / quotientTupleLcm q) / (N : ℝ) := by
    rw [moebiusQuotientProductPrefix_eq q hq
      ((Nat.mul_le_mul_right N hHB).trans (horizon_bounds B N t).1), sub_div]
  simp_rw [heq]
  simpa only [← sub_mul, ← sub_div] using hlim

private theorem power_expansion (m B N M : ℕ) (hm : 0 < m) (hN : 1 ≤ N)
    (hM : 1 ≤ M) (hhi : M ≤ (B + 3) * N) :
    (∑ k ∈ Icc 1 M, (sieveSeq N moebiusReal k) ^ m) =
      1 + (-1 : ℝ) ^ m *
        ∑ q ∈ Fintype.piFinset (fun _ : Fin m => Icc 1 (B + 2)),
          moebiusQuotientProductPrefix N q M := by
  classical
  have hpoint (k : ℕ) (hk : k ∈ Icc 1 M) :
      (sieveSeq N moebiusReal k) ^ m = (if k = 1 then 1 else 0) +
        (-1 : ℝ) ^ m * (∑ q ∈ Icc 1 (B + 2), moebiusQuotientBandTerm N q k) ^ m := by
    rw [sieveSeq_moebiusReal_eq_quotient_band_sum (B := B + 2)
      (mem_Icc.mp hk).1 ((mem_Icc.mp hk).2.trans hhi)]
    by_cases hk1 : k = 1
    · subst k
      have hz : (∑ q ∈ Icc 1 (B + 2), moebiusQuotientBandTerm N q 1) = 0 :=
        Finset.sum_eq_zero fun q hq => moebiusQuotientBandTerm_one hN (mem_Icc.mp hq).1
      simp [hz, Nat.ne_of_gt hm]
    · simpa only [if_neg hk1, zero_sub, zero_add] using
        neg_pow (∑ q ∈ Icc 1 (B + 2), moebiusQuotientBandTerm N q k) m
  rw [Finset.sum_congr rfl hpoint, Finset.sum_add_distrib]
  have hdelta : (∑ k ∈ Icc 1 M, if k = 1 then (1 : ℝ) else 0) = 1 := by simp [hM]
  rw [hdelta, ← Finset.mul_sum]
  congr 2
  unfold moebiusQuotientProductPrefix
  simp_rw [Finset.sum_pow']
  rw [Finset.sum_comm]

private def real_moment_profile (B m : ℕ) (A : ℝ) : ℝ :=
  if m = 0 then A else (-1 : ℝ) ^ m *
    ∑ q ∈ Fintype.piFinset (fun _ : Fin m => Icc 1 (B + 2)),
      (A - (quotientTupleMax q : ℝ)) / (quotientTupleLcm q : ℝ) *
        dilation_density m (fun i => quotientTupleLcm q / q i)

private theorem real_moment_limit (B : ℕ) (t : Set.Icc (0 : ℝ) 1) (m : ℕ) :
    Tendsto (fun N : ℕ =>
      (∑ k ∈ Icc 1 ⌊(((B + 2 : ℕ) : ℝ) + (t : ℝ)) * N⌋₊,
        (sieveSeq N moebiusReal k) ^ m) / (N : ℝ)) atTop
      (𝓝 (real_moment_profile B m (((B + 2 : ℕ) : ℝ) + (t : ℝ)))) := by
  by_cases hm : m = 0
  · subst m
    change Tendsto _ _ (𝓝 (((B + 2 : ℕ) : ℝ) + (t : ℝ)))
    have ht := t.property.1
    simpa only [pow_zero, Finset.sum_const,
      nsmul_eq_mul, mul_one, Nat.card_Icc, Nat.add_sub_cancel, Function.comp_def] using
      (tendsto_nat_floor_mul_div_atTop (show 0 ≤ ((B + 2 : ℕ) : ℝ) + (t : ℝ) by positivity)).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  · have hmpos : 0 < m := by omega
    have hsum : Tendsto (fun N : ℕ =>
        ∑ q ∈ Fintype.piFinset (fun _ : Fin m => Icc 1 (B + 2)),
          moebiusQuotientProductPrefix N q
            ⌊(((B + 2 : ℕ) : ℝ) + (t : ℝ)) * N⌋₊ / (N : ℝ)) atTop
        (𝓝 (∑ q ∈ Fintype.piFinset (fun _ : Fin m => Icc 1 (B + 2)),
          ((((B + 2 : ℕ) : ℝ) + (t : ℝ)) - (quotientTupleMax q : ℝ)) /
            (quotientTupleLcm q : ℝ) *
              dilation_density m (fun i => quotientTupleLcm q / q i))) := by
      exact tendsto_finsetSum _ fun q hq => quotient_prefix_real_limit hmpos t q
        (fun i => (mem_Icc.mp (Fintype.mem_piFinset.mp hq i)).1)
        (fun i => (mem_Icc.mp (Fintype.mem_piFinset.mp hq i)).2)
    have hinv : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) := by
      simpa only [one_div, Function.comp_def] using
        tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop :
          Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
    have h := hinv.add (hsum.const_mul ((-1 : ℝ) ^ m))
    simp only [zero_add] at h
    simp only [real_moment_profile, if_neg hm]
    apply h.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hbound := horizon_bounds B N t
    have hM : 1 ≤ ⌊(((B + 2 : ℕ) : ℝ) + (t : ℝ)) * N⌋₊ := by
      have hp := Nat.mul_pos (show 0 < B + 2 by omega) (show 0 < N by omega)
      omega
    rw [power_expansion m B N _ hmpos hN hM hbound.2, add_div, mul_div_assoc,
      Finset.sum_div]

private theorem real_profile_affine (B m : ℕ) (t : ℝ) :
    real_moment_profile B m (((B + 2 : ℕ) : ℝ) + t) =
      (1 - t) * real_moment_profile B m ((B + 2 : ℕ) : ℝ) +
        t * real_moment_profile B m (((B + 2 : ℕ) : ℝ) + 1) := by
  classical
  by_cases hm : m = 0
  · simp only [real_moment_profile, if_pos hm]
    ring
  · simp only [real_moment_profile, if_neg hm]
    have hs : (∑ q ∈ Fintype.piFinset (fun _ : Fin m => Icc 1 (B + 2)),
        ((((B + 2 : ℕ) : ℝ) + t) - (quotientTupleMax q : ℝ)) /
          (quotientTupleLcm q : ℝ) * dilation_density m (fun i => quotientTupleLcm q / q i)) =
        (1 - t) * (∑ q ∈ Fintype.piFinset (fun _ : Fin m => Icc 1 (B + 2)),
          (((B + 2 : ℕ) : ℝ) - (quotientTupleMax q : ℝ)) /
            (quotientTupleLcm q : ℝ) * dilation_density m (fun i => quotientTupleLcm q / q i)) +
        t * (∑ q ∈ Fintype.piFinset (fun _ : Fin m => Icc 1 (B + 2)),
          ((((B + 2 : ℕ) : ℝ) + 1) - (quotientTupleMax q : ℝ)) /
            (quotientTupleLcm q : ℝ) * dilation_density m (fun i => quotientTupleLcm q / q i)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro q hq
      ring
    rw [hs]
    ring

private theorem real_profile_lower (B m : ℕ) :
    real_moment_profile B m ((B + 2 : ℕ) : ℝ) = cofinalMobiusMomentProfile B m := by
  let t : Set.Icc (0 : ℝ) 1 := ⟨0, by constructor <;> norm_num⟩
  have h := real_moment_limit B t m
  have ht : (t : ℝ) = 0 := rfl
  simp only [ht, add_zero, ← Nat.cast_mul, Nat.floor_natCast] at h
  exact tendsto_nhds_unique h (tendsto_sieveSeq_moment_linear_horizon B m)

private theorem real_profile_upper (B m : ℕ) :
    real_moment_profile B m (((B + 2 : ℕ) : ℝ) + 1) = cofinalMobiusMomentProfile (B + 1) m := by
  let t : Set.Icc (0 : ℝ) 1 := ⟨1, by constructor <;> norm_num⟩
  have h := real_moment_limit B t m
  have ht : (t : ℝ) = 1 := rfl
  have hB : ((B + 2 : ℕ) : ℝ) + 1 = (((B + 1) + 2 : ℕ) : ℝ) := by push_cast; ring
  simp only [ht, hB, ← Nat.cast_mul, Nat.floor_natCast] at h
  rw [hB]
  exact tendsto_nhds_unique h (tendsto_sieveSeq_moment_linear_horizon (B + 1) m)

/-- Every fixed source moment interpolates affinely between adjacent integer horizons. -/
theorem tendsto_sieveSeq_moment_adjacent_real_horizon (B : ℕ)
    (t : Set.Icc (0 : ℝ) 1) (m : ℕ) :
    Tendsto (fun N : ℕ =>
      (∑ k ∈ Icc 1 ⌊(((B + 2 : ℕ) : ℝ) + (t : ℝ)) * N⌋₊,
        (sieveSeq N moebiusReal k) ^ m) / (N : ℝ)) atTop
      (𝓝 ((1 - (t : ℝ)) * cofinalMobiusMomentProfile B m +
        (t : ℝ) * cofinalMobiusMomentProfile (B + 1) m)) := by
  have h := real_moment_limit B t m
  rw [real_profile_affine, real_profile_lower, real_profile_upper] at h
  exact h

end
end GaloisForLFunctions.BezoutValuationIncidence
