import GaloisForLFunctions.RHTower.ChiCubicHyperbolicPrimeVariation
import Mathlib.Topology.EMetricSpace.VariationOnFromTo

/-!
# Sampling the sharp hyperbolic prime kernel

The variation primitive pays every jump crossed by multiplicative displacement.
Overlapping displacement intervals cost only their integer overlap width.
-/

noncomputable section
open Finset Filter Topology Set
namespace RHTower

private theorem sum_truncated_difference_le {v : ℕ → ℝ} {V : ℝ}
    (hV : 0 ≤ V) (hv0 : v 0 = 0) (hv : ∀ n, 0 ≤ v n ∧ v n ≤ V) (B h : ℕ) :
    (∑ i ∈ Finset.range B, (v (i + 1) - v (i + 1 - h))) ≤ (h : ℝ) * V := by
  by_cases hh : h ≤ B
  · let k := B - h
    have hkh : k + h = B := by dsimp [k]; omega
    have hhk : h + k = B := by omega
    have hpos : (∑ i ∈ Finset.range B, v (i + 1)) =
        (∑ i ∈ Finset.range k, v (i + 1)) + ∑ i ∈ Finset.range h, v (k + i + 1) := by
      simpa only [hkh] using (Finset.sum_range_add (fun i => v (i + 1)) k h)
    have hneg : (∑ i ∈ Finset.range B, v (i + 1 - h)) =
        ∑ i ∈ Finset.range k, v (i + 1) := by
      have hhzero : (∑ i ∈ Finset.range h, v (i + 1 - h)) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have heq : i + 1 - h = 0 := by have := Finset.mem_range.1 hi; omega
        rw [heq, hv0]
      have hsum := Finset.sum_range_add (fun i => v (i + 1 - h)) h k
      rw [hhk, hhzero, zero_add] at hsum
      rw [hsum]
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      omega
    rw [Finset.sum_sub_distrib, hpos, hneg, add_sub_cancel_left]
    calc
      _ ≤ ∑ _i ∈ Finset.range h, V := Finset.sum_le_sum fun i _ => (hv _).2
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  · have hBh : B ≤ h := by omega
    calc
      _ ≤ ∑ _i ∈ Finset.range B, V := by
        apply Finset.sum_le_sum
        intro i _
        linarith [(hv (i + 1)).2, (hv (i + 1 - h)).1]
      _ = (B : ℝ) * V := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hBh) hV

private theorem norm_sub_le_variation_primitive {f : ℝ → ℂ}
    (hf : BoundedVariationOn f Set.univ) {x y : ℝ} (hxy : x ≤ y) :
    ‖f y - f x‖ ≤ variationOnFromTo f Set.univ 0 y - variationOnFromTo f Set.univ 0 x := by
  rw [variationOnFromTo.sub_right hf.locallyBoundedVariationOn
    (Set.mem_univ _) (Set.mem_univ _) (Set.mem_univ _),
    variationOnFromTo.eq_of_le _ _ hxy, Set.univ_inter]
  have h := (hf.mono (Set.subset_univ (Set.Icc x y))).dist_le
    (show y ∈ Set.Icc x y from ⟨hxy, le_rfl⟩)
    (show x ∈ Set.Icc x y from ⟨le_rfl, hxy⟩)
  simpa only [dist_eq_norm] using h

private theorem sharp_sampling_le_variation {f : ℝ → ℂ}
    (hf : BoundedVariationOn f Set.univ) (B h : ℕ) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hwidth : (1 - t) * B ≤ h) :
    (∑ i ∈ Finset.range B, ‖f (i + 1 : ℕ) - f (t * (i + 1 : ℕ))‖) ≤
      (h : ℝ) * (eVariationOn f Set.univ).toReal := by
  let v := fun x : ℝ => variationOnFromTo f Set.univ 0 x
  have hmono : Monotone v := fun x y hxy =>
    variationOnFromTo.monotoneOn hf.locallyBoundedVariationOn (Set.mem_univ _)
      (Set.mem_univ _) (Set.mem_univ _) hxy
  have hv (n : ℕ) : 0 ≤ v n ∧ v n ≤ (eVariationOn f Set.univ).toReal :=
    ⟨variationOnFromTo.nonneg_of_le _ _ (Nat.cast_nonneg n),
      (le_abs_self _).trans (variationOnFromTo.abs_le_eVariationOn hf)⟩
  have hv0 : v 0 = 0 := variationOnFromTo.self f Set.univ 0
  calc
    _ ≤ ∑ i ∈ Finset.range B, (v (i + 1 : ℕ) - v (i + 1 - h : ℕ)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hiB : i + 1 ≤ B := by have := Finset.mem_range.1 hi; omega
      have hiBR : ((i + 1 : ℕ) : ℝ) ≤ B := by exact_mod_cast hiB
      have hlow : ((i + 1 - h : ℕ) : ℝ) ≤ t * (i + 1 : ℕ) := by
        by_cases hhi : h ≤ i + 1
        · rw [Nat.cast_sub hhi]
          have h := mul_le_mul_of_nonneg_left hiBR (sub_nonneg.mpr ht1)
          nlinarith
        · have heq : i + 1 - h = 0 := by omega
          rw [heq, Nat.cast_zero]
          positivity
      have hhigh : t * (i + 1 : ℕ) ≤ (i + 1 : ℕ) := by
        exact (mul_le_mul_of_nonneg_right ht1 (Nat.cast_nonneg (i + 1))).trans_eq (one_mul _)
      have hd := norm_sub_le_variation_primitive hf hhigh
      change ‖f (i + 1 : ℕ) - f (t * (i + 1 : ℕ))‖ ≤ v (i + 1 : ℕ) - v (t * (i + 1 : ℕ)) at hd
      exact hd.trans (sub_le_sub_left (hmono hlow) _)
    _ ≤ _ := sum_truncated_difference_le ENNReal.toReal_nonneg
      (show v (0 : ℕ) = 0 by simpa only [Nat.cast_zero] using hv0) hv B h

/-- Every integer sample of the literal kernel can be displaced multiplicatively,
including across sharp boundaries, at a cost controlled by the overlap width. -/
theorem chiCubicHyperbolicPrimeKernel_sampling (M : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 4 ≤ N → 1 ≤ Real.log N →
      ∀ B h : ℕ, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (1 - t) * B ≤ h →
        (∑ i ∈ Finset.range B,
          ‖chiCubicHyperbolicPrimeKernel N M (i + 1 : ℕ) -
            chiCubicHyperbolicPrimeKernel N M (t * (i + 1 : ℕ))‖) ≤
          C * h * Real.sqrt N := by
  obtain ⟨C, hC, h⟩ := exists_chiCubicHyperbolicPrimeKernel_variation M
  refine ⟨C, hC, ?_⟩
  intro N hN hlog B k t ht0 ht1 hwidth
  have hV := h N hN hlog
  calc
    _ ≤ (k : ℝ) * (eVariationOn (chiCubicHyperbolicPrimeKernel N M) Set.univ).toReal :=
      sharp_sampling_le_variation hV.1 B k ht0 ht1 hwidth
    _ ≤ (k : ℝ) * (C * Real.sqrt N) := mul_le_mul_of_nonneg_left hV.2 (Nat.cast_nonneg k)
    _ = _ := by ring

/-- The complete von Mangoldt weights cost one logarithm in the sharp sampling
estimate. Every integer through the dual averaging cutoff is retained. -/
theorem chiCubicHyperbolicPrimeKernel_weighted_sampling (M : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 4 ≤ N → 1 ≤ Real.log N →
      ∀ B h : ℕ, (B : ℝ) ≤ 3 * N → ∀ t : ℝ,
        0 ≤ t → t ≤ 1 → (1 - t) * B ≤ h →
        ‖∑ i ∈ Finset.range B, (ArithmeticFunction.vonMangoldt (i + 1) : ℂ) *
          (chiCubicHyperbolicPrimeKernel N M (i + 1 : ℕ) -
            chiCubicHyperbolicPrimeKernel N M (t * (i + 1 : ℕ)))‖ ≤
          C * h * Real.sqrt N * Real.log (3 * N) := by
  obtain ⟨C, hC, hs⟩ := chiCubicHyperbolicPrimeKernel_sampling M
  refine ⟨C, hC, ?_⟩
  intro N hN hlog B h hB t ht0 ht1 hwidth
  have hN0 : 0 < N := by linarith
  have hlog3 : 0 ≤ Real.log (3 * N) := Real.log_nonneg (by linarith)
  calc
    _ ≤ ∑ i ∈ Finset.range B, Real.log (3 * N) *
        ‖chiCubicHyperbolicPrimeKernel N M (i + 1 : ℕ) -
          chiCubicHyperbolicPrimeKernel N M (t * (i + 1 : ℕ))‖ := by
      apply norm_sum_le_of_le
      intro i hi
      have hiB : i + 1 ≤ B := by have := Finset.mem_range.1 hi; omega
      have hiBR : ((i + 1 : ℕ) : ℝ) ≤ 3 * N :=
        (show ((i + 1 : ℕ) : ℝ) ≤ B by exact_mod_cast hiB).trans hB
      have hi0 : (0 : ℝ) < (i + 1 : ℕ) := by positivity
      rw [norm_mul, Complex.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      exact mul_le_mul_of_nonneg_right
        (ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log hi0 hiBR)) (norm_nonneg _)
    _ = Real.log (3 * N) * (∑ i ∈ Finset.range B,
        ‖chiCubicHyperbolicPrimeKernel N M (i + 1 : ℕ) -
          chiCubicHyperbolicPrimeKernel N M (t * (i + 1 : ℕ))‖) := by rw [Finset.mul_sum]
    _ ≤ Real.log (3 * N) * (C * h * Real.sqrt N) :=
      mul_le_mul_of_nonneg_left (hs N hN hlog B h t ht0 ht1 hwidth) hlog3
    _ = _ := by ring

/-- Uniform sharp displacement throughout the entire multiplicative averaging
window of the actual prime kernel, with no sampling of exceptional sets. -/
theorem chiCubicHyperbolicPrimeKernel_shortWindow_sampling (M : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 4 ≤ N → 1 ≤ Real.log N →
      ∀ t ∈ Set.Icc (1 / (1 + N ^ ((1 : ℝ) / 5 - 1))) 1,
        ‖∑ i ∈ Finset.range ⌊3 * N⌋₊, (ArithmeticFunction.vonMangoldt (i + 1) : ℂ) *
          (chiCubicHyperbolicPrimeKernel N M (i + 1 : ℕ) -
            chiCubicHyperbolicPrimeKernel N M (t * (i + 1 : ℕ)))‖ ≤
          C * (3 * N * N ^ ((1 : ℝ) / 5 - 1) + 1) * Real.sqrt N * Real.log (3 * N) := by
  obtain ⟨C, hC, hs⟩ := chiCubicHyperbolicPrimeKernel_weighted_sampling M
  refine ⟨C, hC, ?_⟩
  intro N hN hlog t ht
  have hN0 : 0 < N := by linarith
  let δ := N ^ ((1 : ℝ) / 5 - 1)
  have hδ : 0 < δ := Real.rpow_pos_of_pos hN0 _
  have ht0 : 0 ≤ t := (by positivity : (0 : ℝ) ≤ 1 / (1 + δ)).trans ht.1
  have htwidth : 1 - t ≤ δ := by
    have hlow : 1 - δ ≤ 1 / (1 + δ) := (le_div_iff₀ (by positivity)).2 (by nlinarith [sq_nonneg δ])
    have htδ : 1 / (1 + δ) ≤ t := ht.1
    linarith
  have hB : ((⌊3 * N⌋₊ : ℕ) : ℝ) ≤ 3 * N := Nat.floor_le (by positivity)
  have hwidth : (1 - t) * ((⌊3 * N⌋₊ : ℕ) : ℝ) ≤ (⌈3 * N * δ⌉₊ : ℕ) := by
    calc
      _ ≤ δ * (3 * N) := mul_le_mul htwidth hB (Nat.cast_nonneg _) hδ.le
      _ = 3 * N * δ := by ring
      _ ≤ _ := Nat.le_ceil _
  have hbound := hs N hN hlog ⌊3 * N⌋₊ ⌈3 * N * δ⌉₊ hB t ht0 ht.2 hwidth
  apply hbound.trans
  have hceil : ((⌈3 * N * δ⌉₊ : ℕ) : ℝ) ≤ 3 * N * δ + 1 :=
    (Nat.ceil_lt_add_one (by positivity : 0 ≤ 3 * N * δ)).le
  have hlog3 : 0 ≤ Real.log (3 * N) := Real.log_nonneg (by linarith)
  gcongr

/-- The complete sampled displacement is uniformly negligible at the cubic
normalization throughout the shrinking dual window. This includes all cutoff
jumps and all von Mangoldt weights, without an analytic premise. -/
theorem chiCubicHyperbolicPrimeKernel_shortWindow_sampling_tendsto (M : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℝ in atTop,
      ∀ t ∈ Set.Icc (1 / (1 + N ^ ((1 : ℝ) / 5 - 1))) 1,
        Real.log N ^ 2 / N *
          ‖∑ i ∈ Finset.range ⌊3 * N⌋₊, (ArithmeticFunction.vonMangoldt (i + 1) : ℂ) *
            (chiCubicHyperbolicPrimeKernel N M (i + 1 : ℕ) -
              chiCubicHyperbolicPrimeKernel N M (t * (i + 1 : ℕ)))‖ < ε := by
  obtain ⟨C, hC, hs⟩ := chiCubicHyperbolicPrimeKernel_shortWindow_sampling M
  have hsmall : Tendsto (fun N : ℝ => Real.log N ^ 3 / N ^ ((3 : ℝ) / 10)) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop (s := (3 : ℝ) / 10) (3 : ℕ)
      (by norm_num)).tendsto_div_nhds_zero
    simpa only [Real.rpow_natCast] using h
  have hhalf : Tendsto (fun N : ℝ => Real.log N ^ 3 / Real.sqrt N) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop (s := (1 : ℝ) / 2) (3 : ℕ)
      (by norm_num)).tendsto_div_nhds_zero
    simpa only [Real.rpow_natCast, Real.sqrt_eq_rpow] using h
  have hlim := (hsmall.const_mul (9 * C)).add (hhalf.const_mul (3 * C))
  simp only [mul_zero, add_zero] at hlim
  intro ε hε
  filter_upwards [eventually_ge_atTop (4 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1, hlim.eventually_lt_const hε] with N hN hlog hεN
  intro t ht
  have hN0 : 0 < N := by linarith
  have hlog3 : Real.log (3 * N) ≤ 3 * Real.log N := by
    rw [Real.log_mul (by norm_num) hN0.ne']
    have hthree := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  have hpow : 0 < N ^ ((3 : ℝ) / 10) := Real.rpow_pos_of_pos hN0 _
  have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hpower : N ^ ((1 : ℝ) / 5 - 1) * Real.sqrt N * N ^ ((3 : ℝ) / 10) = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hN0, ← Real.rpow_add hN0]
    norm_num
  have hδsqrt : N ^ ((1 : ℝ) / 5 - 1) * Real.sqrt N = 1 / N ^ ((3 : ℝ) / 10) :=
    (eq_div_iff hpow.ne').2 hpower
  have hsqrtdiv : Real.sqrt N / N = 1 / Real.sqrt N := by
    apply (div_eq_div_iff hN0.ne' hsqrt.ne').2
    nlinarith [Real.sq_sqrt hN0.le]
  apply lt_of_le_of_lt ?_ hεN
  calc
    _ ≤ Real.log N ^ 2 / N *
        (C * (3 * N * N ^ ((1 : ℝ) / 5 - 1) + 1) * Real.sqrt N * Real.log (3 * N)) :=
      mul_le_mul_of_nonneg_left (hs N hN hlog t ht) (by positivity)
    _ ≤ Real.log N ^ 2 / N *
        (C * (3 * N * N ^ ((1 : ℝ) / 5 - 1) + 1) * Real.sqrt N * (3 * Real.log N)) := by
      gcongr
    _ = 9 * C * Real.log N ^ 3 * (N ^ ((1 : ℝ) / 5 - 1) * Real.sqrt N) +
        3 * C * Real.log N ^ 3 * (Real.sqrt N / N) := by field_simp; ring
    _ = _ := by rw [hδsqrt, hsqrtdiv]; ring

end RHTower
end
