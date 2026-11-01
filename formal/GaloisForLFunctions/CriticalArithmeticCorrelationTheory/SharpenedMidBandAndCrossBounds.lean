import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.CompleteWeilSplitCrossBounds
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.HighConductorWeilCoercivity
import GaloisForLFunctions.HTGeometry.HarmonicQuotientTailBound

/-!
# Sharpened intermediate-band overlap, homogeneous coercivity, and `c^9` cross bounds

This module supplies the three operator-level inputs needed to close the homogeneous four-band
orthogonal decomposition of the complete Weil quadratic form up to `α = 1 / 9`:

1. **Harmonic-tail intermediate-band overlap bound (`exists_overlapMatrix_midBand_inner_le_three_halves`).**
   Replacing the coarse `O(c)` row-count estimate on `Ioc ⌊N / (linearNearRowRadius c + 1)⌋₊ (N - h)`
   by `HTGeometry.harmonic_quotient_tail_le` (`O(1 + log c)`) and keeping the exact square-root
   dependence `1 / φ(t) ≤ 2 e √c / √Q₁` sharpens the diagonal lag-autocorrelation error from
   `O(c^3 / √Q₁)` to `O(c √c (1 + log c) / √Q₁)`.
2. **2-homogeneous band coercivity (`exists_completeWeilEnergy_ge_three_quarters_log_homogeneous`
   and `exists_completeWeilEnergy_ge_quarter_log_homogeneous`).**
   Tightening the Gram remainder on `[Q, R]` when `1080 * (1 + log R) ≤ log N` recovers a
   `(3 / 4) log Q` spectral gap alongside `(1 / 8) * primeAdjunctionMass R a` and rescales both
   band lower bounds homogeneously to arbitrary packet norms without unit-sphere normalization.
3. **Subspace-localized separated cross error and unmerged `overlap - downward` cross payment
   (`norm_separatedCrossErrorMatrix_sq_le_of_mem_conductorSubspace`,
   `exists_overlap_sub_downward_sq_le_c9_split`, and
   `exists_completeWeil_cross_le_c9_split_reserves`).**
   Restricting `separatedCrossErrorMatrix` to `conductorSubspace R N` (`R^4 ≤ N`) gains `1 / log N`
   via `sum_linear_moment_sq_le_four_div_log`, while keeping the divisor-jet near kernel `K2b`
   (`|K2b| ≤ 1`) unmerged from the `O(c)` kernels `K1, K2a` reduces the `(1 + log R) * G` cross
   payment from `c^4` to `c^2` (`c^9` after dividing by the `c^{-7}` terminal reserve).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Finset
open scoped BigOperators RealInnerProductSpace Classical Matrix

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open SignedArithmeticHodgeTheory CompletedArithmeticForms RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell CriticalScaleArithmeticRigidity
  SuccessorShellArithmetic ArithmeticIntersectionTheory ArithmeticEffectivityTheory
  ArithmeticElectrostatics BezoutValuationIncidence HTGeometry
  RenormalizedBiarithmeticGeometry SpacingScaleHarmonicAnalysis

/-! ### 1. Harmonic-tail `O(c √c (1 + log c) / √Q₁)` intermediate-band overlap bound -/

private theorem mem_nearRowIndices_symm {c : ℝ} {N n j : ℕ}
    (hn : n ∈ Icc 1 N) (hj : j ∈ nearRowIndices c N n) :
    n ∈ nearRowIndices c N j := by
  obtain ⟨_, hjn, hlog⟩ := mem_filter.mp hj
  exact mem_filter.mpr ⟨hn, Ne.symm hjn, by rwa [abs_sub_comm]⟩

private theorem log_two_mul_linearNearRowRadius_le {c : ℝ} (hc1 : 1 ≤ c) :
    Real.log (2 * (linearNearRowRadius c + 1)) + 3 ≤ 10 * (1 + Real.log c) := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have he2 : Real.exp 2 ≤ 8 := by
    have h1 : Real.exp 1 ≤ 14 / 5 := by linarith [Real.exp_one_lt_d9]
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith only [h1, h2, Real.exp_pos 1]
  have hlin : 2 * (linearNearRowRadius c + 1) ≤ 34 * c := by
    unfold linearNearRowRadius
    nlinarith only [hc1, he2]
  have hlog34 : Real.log 34 ≤ 6 := by
    have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have he6 : (34 : ℝ) ≤ Real.exp 6 := by
      have hpow : (2 : ℝ) ^ 6 ≤ (Real.exp 1) ^ 6 := pow_le_pow_left₀ (by norm_num) he1 6
      rw [← Real.exp_nat_mul] at hpow
      norm_num at hpow
      linarith only [hpow]
    exact (Real.log_le_log (by norm_num) he6).trans_eq (Real.log_exp 6)
  have hlog_le : Real.log (2 * (linearNearRowRadius c + 1)) ≤ 6 + Real.log c := by
    calc
      Real.log (2 * (linearNearRowRadius c + 1)) ≤ Real.log (34 * c) :=
        Real.log_le_log (by unfold linearNearRowRadius; positivity) hlin
      _ = Real.log 34 + Real.log c := Real.log_mul (by norm_num) hc0.ne'
      _ ≤ 6 + Real.log c := by linarith only [hlog34]
  have hlc0 : 0 ≤ Real.log c := Real.log_nonneg hc1
  linarith only [hlog_le, hlc0]

private theorem sum_nearBand_sq_le_of_mem_conductorSubspace
    {R N : ℕ} {c M : ℝ} (hR : 2 ≤ R) (hlog : 18 * (1 + Real.log R) ≤ Real.log N)
    (hc1 : 1 ≤ c) (hw : c / N ≤ 1) (hM0 : 0 ≤ M)
    (hRNT : ((R * R : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N)
    (K : ℕ → ℕ → ℝ)
    (hK : ∀ n ∈ Icc 1 N, ∀ j ∈ nearRowIndices c N n, |K n j| ≤ M)
    {v : EuclideanSpace ℝ (PrimeHorizonIndex N)} (hv : v ∈ conductorSubspace R N) :
    (∑ n ∈ Icc 1 N, (∑ j ∈ nearRowIndices c N n, K n j * primeHorizonExtension v j) ^ 2) ≤
      (80 * (2 * Real.exp 2) ^ 2) * c ^ 2 * M ^ 2 *
        ((1 + Real.log c) / Real.log N) * ‖v‖ ^ 2 := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hL : 0 < Real.log N := by
    have := Real.log_natCast_nonneg R; linarith only [hlog, this]
  let T := linearNearRowRadius c + 1
  have hT1 : 1 ≤ T := by
    have h0 : 0 ≤ linearNearRowRadius c := by unfold linearNearRowRadius; positivity
    dsimp only [T]; linarith only [h0]
  let vTop : ℕ → ℝ := fun j => if (N : ℝ) / j < T then primeHorizonExtension v j else 0
  let K' : ℕ → ℕ → ℝ := fun n j => if j ∈ nearRowIndices c N n then K n j else 0
  let U : ℕ → ℕ → ℝ := fun n j => if j ∈ nearRowIndices c N n then M else 0
  have hrow_eq : ∀ n ∈ Icc 1 N,
      (∑ j ∈ nearRowIndices c N n, K n j * primeHorizonExtension v j) =
        ∑ j ∈ Icc 1 N, K' n j * vTop j := by
    intro n hn
    have hsub : nearRowIndices c N n ⊆ Icc 1 N := filter_subset _ _
    rw [← sum_subset hsub]
    · refine sum_congr rfl fun j hj => ?_
      have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp (hsub hj)).1
      have hgeom := (nearRow_geometry_small_width hc0 hn hj hw).2.2
      have hlt : (N : ℝ) / j < T := by
        have hle : (N : ℝ) / j ≤ linearNearRowRadius c := (div_le_iff₀ hj0).mpr hgeom
        dsimp only [T]; linarith only [hle]
      dsimp only [K', vTop]
      rw [if_pos hj, if_pos hlt]
    · intro j _ hj; dsimp only [K']; rw [if_neg hj, zero_mul]
  let B_row := 2 * linearNearRowRadius c * M
  have hB_row0 : 0 ≤ B_row := by dsimp only [B_row, linearNearRowRadius]; positivity
  have hU_row : ∀ n ∈ Icc 1 N, (∑ j ∈ Icc 1 N, U n j * 1) ≤ B_row := by
    intro n hn
    have hsub : nearRowIndices c N n ⊆ Icc 1 N := filter_subset _ _
    have heq : (∑ j ∈ Icc 1 N, U n j * 1) = ((nearRowIndices c N n).card : ℝ) * M := by
      simp only [U, mul_one, ← sum_filter, filter_mem_eq_inter, inter_eq_right.mpr hsub,
        sum_const, nsmul_eq_mul]
    rw [heq]
    exact mul_le_mul_of_nonneg_right (card_nearRowIndices_le_small_width hc0 hn hw) hM0
  have hU_col : ∀ j ∈ Icc 1 N, (∑ n ∈ Icc 1 N, U n j * (B_row / 1)) ≤ B_row ^ 2 := by
    intro j hj
    have hsym : ∀ n ∈ Icc 1 N, U n j * (B_row / 1) = B_row * (U j n * 1) := by
      intro n hn
      dsimp only [U]
      by_cases hjn : j ∈ nearRowIndices c N n
      · rw [if_pos hjn, if_pos (mem_nearRowIndices_symm hn hjn)]; ring
      · have hnj : n ∉ nearRowIndices c N j := fun h => hjn (mem_nearRowIndices_symm hj h)
        rw [if_neg hjn, if_neg hnj]; ring
    rw [sum_congr rfl hsym, ← mul_sum, sq]
    exact mul_le_mul_of_nonneg_left (hU_row j hj) hB_row0
  have hschur := sum_sq_abs_majorized_kernel_le' K' U vTop
    (fun _ => 1) (fun _ => B_row) (fun _ => B_row ^ 2)
    (fun _ _ _ _ => by dsimp only [U]; split_ifs <;> positivity)
    (fun n hn j _ => by
      dsimp only [K', U]
      split_ifs with hj
      · exact hK n hn j hj
      · rw [abs_zero])
    (fun _ _ => zero_lt_one) hU_row hU_col
  have hvTop_sq : (∑ j ∈ Icc 1 N, vTop j ^ 2) ≤
      20 * (1 + Real.log c) / Real.log N * ‖v‖ ^ 2 := by
    have hfilt : (∑ j ∈ Icc 1 N, vTop j ^ 2) =
        ∑ j ∈ (Icc 1 N).filter (fun j : ℕ => (N : ℝ) / j < T), primeHorizonExtension v j ^ 2 := by
      rw [sum_filter]
      exact sum_congr rfl fun j _ => by dsimp only [vTop]; split_ifs <;> simp
    rw [hfilt, div_mul_eq_mul_div, le_div_iff₀' hL]
    have hq := sum_quotient_tail_sq_le_of_mem_conductorSubspace hR hT1 hRNT hlog hv
    have hlogT := log_two_mul_linearNearRowRadius_le hc1
    exact hq.trans (mul_le_mul_of_nonneg_right (by linarith only [hlogT]) (sq_nonneg _))
  rw [sum_congr rfl fun n hn => by rw [hrow_eq n hn]]
  calc
    (∑ n ∈ Icc 1 N, (∑ j ∈ Icc 1 N, K' n j * vTop j) ^ 2) ≤
        ∑ j ∈ Icc 1 N, B_row ^ 2 * vTop j ^ 2 := hschur
    _ = B_row ^ 2 * ∑ j ∈ Icc 1 N, vTop j ^ 2 := (mul_sum ..).symm
    _ ≤ B_row ^ 2 * (20 * (1 + Real.log c) / Real.log N * ‖v‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hvTop_sq (sq_nonneg _)
    _ = (80 * (2 * Real.exp 2) ^ 2) * c ^ 2 * M ^ 2 *
          ((1 + Real.log c) / Real.log N) * ‖v‖ ^ 2 := by
      dsimp only [B_row, linearNearRowRadius]; ring

private theorem overlapMatrix_inner_eq (φ : ℝ → ℝ) (c : ℝ) (N : ℕ)
    (x y : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ⟪Matrix.toEuclideanLin (overlapMatrix φ c N) x, y⟫ =
      ∑ n ∈ Icc 1 N, primeHorizonExtension y n *
        ∑ j ∈ nearRowIndices c N n,
          (atomArchPair (atomDilate φ (c / N)) n j / (∫ t, atomDilate φ (c / N) t ^ 2) +
            (completeWeilPoleShift φ c / N) * archimedeanCenterKernel n j) *
            primeHorizonExtension x j := by
  let K_ov : ℕ → ℕ → ℝ := fun n j =>
    atomArchPair (atomDilate φ (c / N)) n j / (∫ t, atomDilate φ (c / N) t ^ 2) +
      (completeWeilPoleShift φ c / N) * archimedeanCenterKernel n j
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ n : PrimeHorizonIndex N, y.ofLp n *
    ∑ j : PrimeHorizonIndex N, overlapMatrix φ c N n j * x.ofLp j) = _
  rw [← sum_coe_sort (Icc 1 N) (fun n => primeHorizonExtension y n *
    ∑ j ∈ nearRowIndices c N n, K_ov n j * primeHorizonExtension x j)]
  refine sum_congr rfl fun n _ => ?_
  rw [primeHorizonExtension_coe y n]
  congr 1
  rw [nearRowIndices, sum_filter, ← sum_coe_sort (Icc 1 N)]
  refine sum_congr rfl fun j _ => ?_
  rw [primeHorizonExtension_coe x j]
  dsimp only [overlapMatrix, K_ov]
  by_cases h : (j : ℕ) ≠ (n : ℕ) ∧ |Real.log (j : ℕ) - Real.log (n : ℕ)| ≤ 2 * c / N
  · rw [if_pos ⟨Ne.symm h.1, by rw [← mul_div_assoc]; exact h.2⟩, if_pos h]
  · rw [if_neg fun h' => h ⟨Ne.symm h'.1, by rw [mul_div_assoc]; exact h'.2⟩, if_neg h, zero_mul]

private theorem abs_sum_Ioc_mul_le_total_variation {a b : ℕ} (hab : a ≤ b)
    (w g : ℕ → ℝ) {B_part : ℝ}
    (hB : ∀ u v : ℕ, u ≤ v → |∑ n ∈ Ico u v, g n| ≤ B_part) :
    |∑ n ∈ Ioc a b, w n * g n| ≤
      B_part * (|w b| + ∑ i ∈ range (b - a - 1), |w (a + 1 + (i + 1)) - w (a + 1 + i)|) := by
  have hB0 : 0 ≤ B_part := (abs_nonneg _).trans (hB 0 0 le_rfl)
  rcases eq_or_lt_of_le hab with rfl | hlt
  · simp only [Ioc_self, sum_empty, abs_zero]
    positivity
  · let L := b - a
    have hIoc : Ioc a b = Ico (a + 1) (b + 1) := by
      ext n; simp only [mem_Ioc, mem_Ico]; omega
    have hlen : b + 1 - (a + 1) = L := by dsimp only [L]; omega
    have hrange : (∑ n ∈ Ioc a b, w n * g n) =
        ∑ i ∈ range L, w (a + 1 + i) * g (a + 1 + i) := by
      rw [hIoc, sum_Ico_eq_sum_range, hlen]
    rw [hrange]
    have hparts := Finset.sum_range_by_parts (fun i => w (a + 1 + i)) (fun i => g (a + 1 + i)) L
    simp only [smul_eq_mul] at hparts
    rw [hparts]
    have hpartial : ∀ k : ℕ, |∑ j ∈ range k, g (a + 1 + j)| ≤ B_part := fun k => by
      have heq : (∑ j ∈ range k, g (a + 1 + j)) = ∑ n ∈ Ico (a + 1) (a + 1 + k), g n := by
        rw [sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
      rw [heq]
      exact hB (a + 1) (a + 1 + k) (Nat.le_add_right _ _)
    have hlast : a + 1 + (L - 1) = b := by dsimp only [L]; omega
    have hhead : |w (a + 1 + (L - 1)) * ∑ j ∈ range L, g (a + 1 + j)| ≤ B_part * |w b| := by
      rw [hlast, abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hpartial L) (abs_nonneg _)
    have htail :
        |∑ i ∈ range (L - 1),
            (w (a + 1 + (i + 1)) - w (a + 1 + i)) * ∑ j ∈ range (i + 1), g (a + 1 + j)| ≤
          B_part * ∑ i ∈ range (L - 1), |w (a + 1 + (i + 1)) - w (a + 1 + i)| := by
      rw [mul_sum]
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
      rw [abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hpartial (i + 1)) (abs_nonneg _)
    calc
      |w (a + 1 + (L - 1)) * (∑ j ∈ range L, g (a + 1 + j)) -
          ∑ i ∈ range (L - 1),
            (w (a + 1 + (i + 1)) - w (a + 1 + i)) * ∑ j ∈ range (i + 1), g (a + 1 + j)| ≤
          |w (a + 1 + (L - 1)) * ∑ j ∈ range L, g (a + 1 + j)| +
            |∑ i ∈ range (L - 1),
              (w (a + 1 + (i + 1)) - w (a + 1 + i)) * ∑ j ∈ range (i + 1), g (a + 1 + j)| :=
        abs_sub _ _
      _ ≤ B_part * |w b| +
            B_part * ∑ i ∈ range (L - 1), |w (a + 1 + (i + 1)) - w (a + 1 + i)| :=
        add_le_add hhead htail
      _ = B_part * (|w b| + ∑ i ∈ range (b - a - 1), |w (a + 1 + (i + 1)) - w (a + 1 + i)|) := by
        dsimp only [L]; ring

private theorem shifted_mode_osc_Ico_le {m l R₂ : ℕ} (hR₂ : 2 ≤ R₂)
    (hm : m ∈ Icc 1 R₂) (hl : l ∈ Icc 1 R₂) (h u v : ℕ) (huv : u ≤ v) :
    |∑ n ∈ Ico u v,
        (normalizedRamanujanMode m n * normalizedRamanujanMode l (n + h) -
          (if m = l then ramanujanLagCoefficient m h / (m.totient : ℝ) else 0))| ≤
      4 * (R₂ : ℝ) ^ 3 := by
  obtain ⟨hm1, hmR⟩ := mem_Icc.mp hm
  obtain ⟨hl1, hlR⟩ := mem_Icc.mp hl
  let q := m * l
  have hq0 : 0 < q := Nat.mul_pos hm1 hl1
  let μ : ℝ := if m = l then ramanujanLagCoefficient m h / (m.totient : ℝ) else 0
  let g_osc : ℕ → ℝ := fun n =>
    normalizedRamanujanMode m n * normalizedRamanujanMode l (n + h) - μ
  have hpm : ∀ n, normalizedRamanujanMode m (n + q) = normalizedRamanujanMode m n := fun n => by
    have hp := (normalizedRamanujanMode_periodic hm1).nat_mul l n
    simpa only [q, Nat.cast_id, Nat.mul_comm] using hp
  have hpl : ∀ n, normalizedRamanujanMode l (n + q + h) = normalizedRamanujanMode l (n + h) := fun n => by
    have hp := (normalizedRamanujanMode_periodic hl1).nat_mul m (n + h)
    simpa only [q, Nat.cast_id, show n + q + h = n + h + m * l by dsimp only [q]; omega] using hp
  have hper : Function.Periodic g_osc q := fun n => by
    dsimp only [g_osc]; rw [hpm n, hpl n]
  have hzero : (∑ n ∈ range q, g_osc n) = 0 := by
    dsimp only [g_osc]
    rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
    have hprod : ∀ n : ℕ, normalizedRamanujanMode m n * normalizedRamanujanMode l (n + h) =
        (Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ))⁻¹ *
          (ramanujanLagCoefficient m (n + 0) * ramanujanLagCoefficient l (n + h)) := by
      intro n
      rw [normalizedRamanujanMode_eq_coefficient hm1, normalizedRamanujanMode_eq_coefficient hl1,
        Nat.add_zero]
      ring
    rw [sum_congr rfl fun n _ => hprod n, ← mul_sum,
      sum_range_ramanujanLagCoefficient_shift_mul hm1 hl1 (dvd_mul_right m l) (dvd_mul_left l m) 0 h,
      Nat.dist_zero_left]
    dsimp only [μ, q]
    by_cases hml : m = l
    · subst l
      rw [if_pos rfl, if_pos rfl]
      have hφ0 : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm1
      rw [Real.mul_self_sqrt hφ0.le]
      field_simp [hφ0.ne']
      ring
    · rw [if_neg hml, if_neg hml, mul_zero, mul_zero, sub_self]
  have habs_le : ∀ i : ℕ, |g_osc i| ≤ 2 * (R₂ : ℝ) := by
    intro i
    dsimp only [g_osc]
    have h1 := abs_normalizedRamanujanMode_le_sqrt_totient hm1 i
    have h2 := abs_normalizedRamanujanMode_le_sqrt_totient hl1 (i + h)
    have hφm : (m.totient : ℝ) ≤ R₂ := by exact_mod_cast (Nat.totient_le m).trans hmR
    have hφl : (l.totient : ℝ) ≤ R₂ := by exact_mod_cast (Nat.totient_le l).trans hlR
    have hprod_le : |normalizedRamanujanMode m i * normalizedRamanujanMode l (i + h)| ≤ R₂ := by
      rw [abs_mul]
      calc
        _ ≤ Real.sqrt m.totient * Real.sqrt l.totient :=
          mul_le_mul h1 h2 (abs_nonneg _) (Real.sqrt_nonneg _)
        _ ≤ Real.sqrt R₂ * Real.sqrt R₂ :=
          mul_le_mul (Real.sqrt_le_sqrt hφm) (Real.sqrt_le_sqrt hφl)
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        _ = R₂ := Real.mul_self_sqrt (Nat.cast_nonneg R₂)
    have hμ_le : |μ| ≤ 1 := by
      dsimp only [μ]
      split_ifs with hml
      · have hφ0 : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm1
        rw [abs_div, abs_of_pos hφ0, div_le_one hφ0]
        exact BiScaleUncertainty.SieveMoments.abs_ramanujanLagCoefficient_le_totient m h
      · rw [abs_zero]; exact zero_le_one
    have hR2_ge1 : (1 : ℝ) ≤ R₂ := by exact_mod_cast (show 1 ≤ R₂ by omega)
    exact (abs_sub _ _).trans (by linarith only [hprod_le, hμ_le, hR2_ge1])
  have hq_le : (q : ℝ) ≤ (R₂ : ℝ) ^ 2 := by
    have hnat : m * l ≤ R₂ * R₂ := Nat.mul_le_mul hmR hlR
    have hcast : ((m * l : ℕ) : ℝ) ≤ ((R₂ * R₂ : ℕ) : ℝ) := by exact_mod_cast hnat
    simpa only [q, Nat.cast_mul, sq] using hcast
  calc
    |∑ n ∈ Ico u v, g_osc n| ≤ 2 * ∑ i ∈ range q, |g_osc i| :=
      abs_sum_Ico_le_of_periodic hq0 hper hzero u v huv
    _ ≤ 2 * ∑ _i ∈ range q, (2 * (R₂ : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_le_sum fun i _ => habs_le i) zero_le_two
    _ = 4 * (q : ℝ) * R₂ := by rw [sum_const, card_range, nsmul_eq_mul]; ring
    _ ≤ 4 * (R₂ : ℝ) ^ 2 * R₂ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq_le (by norm_num))
        (Nat.cast_nonneg R₂)
    _ = 4 * (R₂ : ℝ) ^ 3 := by ring

private theorem linearized_weight_tv_le {G : ℝ → ℝ} {K_lip : NNReal}
    (hG : LipschitzWith K_lip G) {M_φ : ℝ} (hM0 : 0 ≤ M_φ) (hM : ∀ t, |G t| ≤ M_φ)
    {c : ℝ} (hc1 : 1 ≤ c) {N h : ℕ} (hN1 : 1 ≤ N)
    (hh : h ∈ Icc 1 ⌊linearNearRowRadius c⌋₊)
    (hK0_lt : ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ < N - h) :
    let K₀ := ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊
    let b := N - h
    let w_h : ℕ → ℝ := fun n => (1 / (n : ℝ)) * G ((N : ℝ) / c * ((h : ℝ) / n))
    |w_h b| + ∑ i ∈ range (b - K₀ - 1), |w_h (K₀ + 1 + (i + 1)) - w_h (K₀ + 1 + i)| ≤
      (2 * Real.exp 2 + 1) * (2 * M_φ + 2 * Real.exp 2 * (2 * Real.exp 2 + 1) * (K_lip : ℝ)) *
        c ^ 2 / N := by
  intro K₀ b w_h
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  let A := linearNearRowRadius c + 1
  have hA0 : 0 < A := by dsimp only [A, linearNearRowRadius]; positivity
  have hA_le : A ≤ (2 * Real.exp 2 + 1) * c := by
    dsimp only [A, linearNearRowRadius]; nlinarith only [hc1]
  have hhB : (h : ℝ) ≤ 2 * Real.exp 2 * c := by
    have hle : (h : ℝ) ≤ linearNearRowRadius c :=
      (by exact_mod_cast (mem_Icc.mp hh).2 : (h : ℝ) ≤ ⌊linearNearRowRadius c⌋₊).trans
        (Nat.floor_le (by unfold linearNearRowRadius; positivity))
    simpa only [linearNearRowRadius, mul_comm c, mul_assoc] using hle
  let a₀ := K₀ + 1
  have ha0_pos : (0 : ℝ) < a₀ := by dsimp only [a₀]; positivity
  have ha0_inv : 1 / (a₀ : ℝ) ≤ A / N := by
    have hlt : (N : ℝ) / A < (K₀ : ℝ) + 1 := Nat.lt_floor_add_one _
    rw [div_le_div_iff₀ ha0_pos hN0]
    have hm := (div_lt_iff₀ hA0).mp hlt
    dsimp only [a₀]
    push_cast
    linarith only [hm]
  have ha0_le_b : a₀ ≤ b := by dsimp only [a₀]; omega
  have hb_pos : (0 : ℝ) < b := lt_of_lt_of_le ha0_pos (by exact_mod_cast ha0_le_b)
  have hb_inv : 1 / (b : ℝ) ≤ A / N :=
    (one_div_le_one_div_of_le ha0_pos (by exact_mod_cast ha0_le_b)).trans ha0_inv
  have hwb_le : |w_h b| ≤ (A / N) * M_φ := by
    dsimp only [w_h]
    rw [abs_mul, abs_of_pos (one_div_pos.mpr hb_pos)]
    exact mul_le_mul hb_inv (hM _) (abs_nonneg _) (div_nonneg hA0.le hN0.le)
  let L' := b - K₀ - 1
  let invF : ℕ → ℝ := fun i => 1 / ((a₀ + i : ℕ) : ℝ)
  let argF : ℕ → ℝ := fun i => (N : ℝ) / c * ((h : ℝ) / (a₀ + i : ℕ))
  have hstep : ∀ i : ℕ, |w_h (a₀ + (i + 1)) - w_h (a₀ + i)| ≤
      M_φ * (invF i - invF (i + 1)) +
        (A / N) * (K_lip : ℝ) * (argF i - argF (i + 1)) := by
    intro i
    have hi_pos : (0 : ℝ) < (a₀ + i : ℕ) := by dsimp only [a₀]; positivity
    have hi_le : ((a₀ + i : ℕ) : ℝ) ≤ (a₀ + (i + 1) : ℕ) := by
      exact_mod_cast (by omega : a₀ + i ≤ a₀ + (i + 1))
    have hinv_mono : invF (i + 1) ≤ invF i := one_div_le_one_div_of_le hi_pos hi_le
    have hinv_le : invF i ≤ A / N := by
      have h0 : ((a₀ : ℕ) : ℝ) ≤ (a₀ + i : ℕ) := by exact_mod_cast Nat.le_add_right a₀ i
      exact (one_div_le_one_div_of_le ha0_pos h0).trans ha0_inv
    have hinv_nonneg : 0 ≤ invF i := by dsimp only [invF]; positivity
    have harg_mono : argF (i + 1) ≤ argF i := by
      dsimp only [argF]
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left (Nat.cast_nonneg h) hi_pos hi_le) (by positivity)
    have hlip_i : |G (argF (i + 1)) - G (argF i)| ≤ (K_lip : ℝ) * (argF i - argF (i + 1)) := by
      have hdist := hG.dist_le_mul (argF (i + 1)) (argF i)
      rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr harg_mono)] at hdist
      linarith only [hdist]
    have hid : w_h (a₀ + (i + 1)) - w_h (a₀ + i) =
        (invF (i + 1) - invF i) * G (argF (i + 1)) +
          invF i * (G (argF (i + 1)) - G (argF i)) := by
      dsimp only [w_h, invF, argF]; ring
    rw [hid]
    calc
      _ ≤ |(invF (i + 1) - invF i) * G (argF (i + 1))| +
            |invF i * (G (argF (i + 1)) - G (argF i))| := abs_add_le _ _
      _ = |invF (i + 1) - invF i| * |G (argF (i + 1))| +
            invF i * |G (argF (i + 1)) - G (argF i)| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hinv_nonneg]
      _ = (invF i - invF (i + 1)) * |G (argF (i + 1))| +
            invF i * |G (argF (i + 1)) - G (argF i)| := by
        rw [abs_of_nonpos (sub_nonpos.mpr hinv_mono)]; ring
      _ ≤ (invF i - invF (i + 1)) * M_φ +
            (A / N) * ((K_lip : ℝ) * (argF i - argF (i + 1))) :=
        add_le_add
          (mul_le_mul_of_nonneg_left (hM _) (sub_nonneg.mpr hinv_mono))
          (mul_le_mul hinv_le hlip_i (abs_nonneg _) (div_nonneg hA0.le hN0.le))
      _ = M_φ * (invF i - invF (i + 1)) +
            (A / N) * (K_lip : ℝ) * (argF i - argF (i + 1)) := by ring
  have htel_inv : (∑ i ∈ range L', (invF i - invF (i + 1))) ≤ A / N := by
    rw [Finset.sum_range_sub']
    have hpos : 0 ≤ invF L' := by dsimp only [invF]; positivity
    have h0 : invF 0 = 1 / (a₀ : ℝ) := rfl
    linarith only [hpos, h0, ha0_inv]
  have htel_arg : (∑ i ∈ range L', (argF i - argF (i + 1))) ≤ 2 * Real.exp 2 * A := by
    rw [Finset.sum_range_sub']
    have hpos : 0 ≤ argF L' := by dsimp only [argF]; positivity
    have h0 : argF 0 ≤ 2 * Real.exp 2 * A := by
      have heq : argF 0 = ((N : ℝ) / c) * (h : ℝ) * (1 / (a₀ : ℝ)) := by
        dsimp only [argF]; ring
      rw [heq]
      calc
        ((N : ℝ) / c) * (h : ℝ) * (1 / (a₀ : ℝ)) ≤
            ((N : ℝ) / c) * (2 * Real.exp 2 * c) * (A / N) :=
          mul_le_mul
            (mul_le_mul_of_nonneg_left hhB (by positivity))
            ha0_inv (by positivity) (by positivity)
        _ = 2 * Real.exp 2 * A := by field_simp [hc0.ne', hN0.ne']
    linarith only [hpos, h0]
  have hsum_le :
      (∑ i ∈ range L', |w_h (a₀ + (i + 1)) - w_h (a₀ + i)|) ≤
        M_φ * (A / N) + (A / N) * (K_lip : ℝ) * (2 * Real.exp 2 * A) := by
    calc
      _ ≤ ∑ i ∈ range L', (M_φ * (invF i - invF (i + 1)) +
            (A / N) * (K_lip : ℝ) * (argF i - argF (i + 1))) :=
        sum_le_sum fun i _ => hstep i
      _ = M_φ * (∑ i ∈ range L', (invF i - invF (i + 1))) +
            (A / N) * (K_lip : ℝ) * (∑ i ∈ range L', (argF i - argF (i + 1))) := by
        rw [sum_add_distrib, ← mul_sum, ← mul_sum]
      _ ≤ M_φ * (A / N) + (A / N) * (K_lip : ℝ) * (2 * Real.exp 2 * A) :=
        add_le_add
          (mul_le_mul_of_nonneg_left htel_inv hM0)
          (mul_le_mul_of_nonneg_left htel_arg (by positivity))
  have hfactor :
      2 * M_φ + 2 * Real.exp 2 * A * (K_lip : ℝ) ≤
        (2 * M_φ + 2 * Real.exp 2 * (2 * Real.exp 2 + 1) * (K_lip : ℝ)) * c := by
    have h1 : 2 * M_φ ≤ 2 * M_φ * c := by nlinarith only [hM0, hc1]
    have h2 : 2 * Real.exp 2 * A * (K_lip : ℝ) ≤
        2 * Real.exp 2 * ((2 * Real.exp 2 + 1) * c) * (K_lip : ℝ) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hA_le (by positivity)) K_lip.2
    linarith only [h1, h2, (by ring :
      2 * M_φ * c + 2 * Real.exp 2 * ((2 * Real.exp 2 + 1) * c) * (K_lip : ℝ) =
        (2 * M_φ + 2 * Real.exp 2 * (2 * Real.exp 2 + 1) * (K_lip : ℝ)) * c)]
  calc
    |w_h b| + ∑ i ∈ range L', |w_h (a₀ + (i + 1)) - w_h (a₀ + i)| ≤
        (A / N) * M_φ + (M_φ * (A / N) + (A / N) * (K_lip : ℝ) * (2 * Real.exp 2 * A)) :=
      add_le_add hwb_le hsum_le
    _ = A * (2 * M_φ + 2 * Real.exp 2 * A * (K_lip : ℝ)) / N := by ring
    _ ≤ ((2 * Real.exp 2 + 1) * c) *
          ((2 * M_φ + 2 * Real.exp 2 * (2 * Real.exp 2 + 1) * (K_lip : ℝ)) * c) / N :=
      div_le_div_of_nonneg_right
        (mul_le_mul hA_le hfactor (by positivity) (by positivity)) hN0.le
    _ = (2 * Real.exp 2 + 1) *
          (2 * M_φ + 2 * Real.exp 2 * (2 * Real.exp 2 + 1) * (K_lip : ℝ)) * c ^ 2 / N := by
      ring

private theorem sum_offDiag_symm_eq_two_mul_sum_Icc_sub (N : ℕ) (F : ℕ → ℕ → ℝ)
    (hF : ∀ n j, F n j = F j n) :
    (∑ n ∈ Icc 1 N, ∑ j ∈ (Icc 1 N).filter (fun j => j ≠ n), F n j) =
      2 * ∑ h ∈ Icc 1 N, ∑ n ∈ Icc 1 (N - h), F n (n + h) := by
  have hsplit : ∀ n ∈ Icc 1 N,
      (∑ j ∈ (Icc 1 N).filter (fun j => j ≠ n), F n j) =
        (∑ j ∈ Icc 1 N, if j < n then F n j else 0) +
          (∑ j ∈ Icc 1 N, if n < j then F n j else 0) := by
    intro n _
    rw [sum_filter, ← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    rcases lt_trichotomy j n with hlt | rfl | hgt
    · rw [if_pos hlt.ne, if_pos hlt, if_neg (lt_asymm hlt), add_zero]
    · rw [if_neg (not_not.mpr rfl), if_neg (lt_irrefl j), add_zero]
    · rw [if_pos hgt.ne', if_neg (lt_asymm hgt), if_pos hgt, zero_add]
  have hsymm :
      (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, if j < n then F n j else 0) =
        ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, if n < j then F n j else 0 := by
    rw [sum_comm]
    exact sum_congr rfl fun j _ => sum_congr rfl fun n _ => by rw [hF n j]
  have hupper : ∀ n ∈ Icc 1 N,
      (∑ j ∈ Icc 1 N, if n < j then F n j else 0) =
        ∑ h ∈ Icc 1 N, if n ≤ N - h then F n (n + h) else 0 := by
    intro n hn
    obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
    have hIoc : (∑ j ∈ Icc 1 N, if n < j then F n j else 0) = ∑ j ∈ Ioc n N, F n j := by
      rw [← sum_filter]
      congr 1
      ext j
      simp only [mem_filter, mem_Icc, mem_Ioc]
      omega
    have hbij : (∑ j ∈ Ioc n N, F n j) = ∑ h ∈ Icc 1 (N - n), F n (n + h) := by
      refine (sum_bij (fun h _ => n + h) ?_ ?_ ?_ ?_).symm
      · intro h hh; simp only [mem_Icc, mem_Ioc] at *; omega
      · intro h₁ _ h₂ _ heq; omega
      · intro j hj
        refine ⟨j - n, ?_, ?_⟩
        · simp only [mem_Icc, mem_Ioc] at *; omega
        · simp only [mem_Ioc] at *; omega
      · intro _ _; rfl
    have hfilt : (∑ h ∈ Icc 1 (N - n), F n (n + h)) =
        ∑ h ∈ Icc 1 N, if n ≤ N - h then F n (n + h) else 0 := by
      rw [← sum_filter]
      congr 1
      ext h
      simp only [mem_filter, mem_Icc]
      omega
    rw [hIoc, hbij, hfilt]
  have hswap :
      (∑ n ∈ Icc 1 N, ∑ h ∈ Icc 1 N, if n ≤ N - h then F n (n + h) else 0) =
        ∑ h ∈ Icc 1 N, ∑ n ∈ Icc 1 (N - h), F n (n + h) := by
    rw [sum_comm]
    refine sum_congr rfl fun h hh => ?_
    obtain ⟨_, hhN⟩ := mem_Icc.mp hh
    rw [← sum_filter]
    congr 1
    ext n
    simp only [mem_filter, mem_Icc]
    omega
  rw [sum_congr rfl hsplit, sum_add_distrib, hsymm, ← two_mul, sum_congr rfl hupper, hswap]

private def midBandSubKernel (φ : ℝ → ℝ) (c : ℝ) (N n j : ℕ) : ℝ :=
  atomArchPair (atomDilate φ (c / N)) n j / (∫ t, atomDilate φ (c / N) t ^ 2) +
    (completeWeilPoleShift φ c / N) * archimedeanCenterKernel n j -
    (Real.log (1 / (c / N)) / ∫ t, φ t ^ 2) *
      shellAutocorr φ (|Real.log j - Real.log n| / (c / N))

private def midBandLeadKernel (φ : ℝ → ℝ) (c : ℝ) (N n j : ℕ) : ℝ :=
  shellAutocorr φ (|Real.log j - Real.log n| / (c / N))

private def midBandPacketMode (R₂ : ℕ) (a : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ m ∈ Icc 1 R₂, a m * normalizedRamanujanMode m k

private def midBandLinearizedWeight (φ : ℝ → ℝ) (c : ℝ) (N h n : ℕ) : ℝ :=
  (1 / (n : ℝ)) * shellAutocorr φ ((N : ℝ) / c * ((h : ℝ) / n))

private def midBandLagSum (φ : ℝ → ℝ) (R₂ N : ℕ) (c : ℝ) (a : ℕ → ℝ) : ℝ :=
  ∑ h ∈ Icc 1 ⌊linearNearRowRadius c⌋₊,
    ∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
      midBandPacketMode R₂ a n * midBandPacketMode R₂ a (n + h) * (1 / (n : ℝ)) *
        (Real.sqrt n / Real.sqrt (n + h : ℕ) *
          shellAutocorr φ ((N : ℝ) / c * (Real.log (n + h : ℕ) - Real.log n)))

private def midBandLinearizedSum (φ : ℝ → ℝ) (R₂ N : ℕ) (c : ℝ) (a : ℕ → ℝ) : ℝ :=
  ∑ h ∈ Icc 1 ⌊linearNearRowRadius c⌋₊,
    ∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
      midBandPacketMode R₂ a n * midBandPacketMode R₂ a (n + h) *
        midBandLinearizedWeight φ c N h n

private def midBandMeanSum (φ : ℝ → ℝ) (R₂ N : ℕ) (c : ℝ) (a : ℕ → ℝ) : ℝ :=
  ∑ h ∈ Icc 1 ⌊linearNearRowRadius c⌋₊, ∑ m ∈ Icc 1 R₂,
    a m ^ 2 * (ramanujanLagCoefficient m h / (m.totient : ℝ)) *
      ∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
        midBandLinearizedWeight φ c N h n

private def midBandOscMode (m l h n : ℕ) : ℝ :=
  normalizedRamanujanMode m n * normalizedRamanujanMode l (n + h) -
    if m = l then ramanujanLagCoefficient m h / (m.totient : ℝ) else 0

private def midBandOscSum (φ : ℝ → ℝ) (R₂ N : ℕ) (c : ℝ) (a : ℕ → ℝ) : ℝ :=
  ∑ h ∈ Icc 1 ⌊linearNearRowRadius c⌋₊, ∑ m ∈ Icc 1 R₂, ∑ l ∈ Icc 1 R₂,
    a m * a l *
      ∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
        midBandLinearizedWeight φ c N h n * midBandOscMode m l h n

private theorem midBand_primeHorizonExtension_eq (R₂ N : ℕ) (a : ℕ → ℝ) {k : ℕ}
    (hk : k ∈ Icc 1 N) :
    primeHorizonExtension (∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N) k =
      (Real.sqrt (Real.log N))⁻¹ * (midBandPacketMode R₂ a k / Real.sqrt k) := by
  rw [primeHorizonExtension_coe _ ⟨k, hk⟩]
  change (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : PrimeHorizonIndex N => ℝ) ⟨k, hk⟩)
      (∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N) = _
  rw [map_sum, midBandPacketMode, sum_div, mul_sum]
  exact sum_congr rfl fun m _ => by
    change a m * ((Real.sqrt (Real.log N))⁻¹ * (normalizedRamanujanMode m k / Real.sqrt k)) = _
    ring

private theorem midBandPacketMode_sq_sum_le {R₂ N : ℕ} (hL0 : 0 < Real.log N) (a : ℕ → ℝ) :
    (∑ k ∈ Icc 1 N, midBandPacketMode R₂ a k ^ 2) ≤
      (N : ℝ) * Real.log N *
        ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by
  have hpt : ∀ k ∈ Icc 1 N,
      midBandPacketMode R₂ a k ^ 2 ≤
        (N : ℝ) * Real.log N *
          primeHorizonExtension (∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N) k ^ 2 := by
    intro k hk
    have hk0 : (0 : ℝ) < k := Nat.cast_pos.mpr (mem_Icc.mp hk).1
    have hkN : (k : ℝ) ≤ N := Nat.cast_le.mpr (mem_Icc.mp hk).2
    rw [midBand_primeHorizonExtension_eq R₂ N a hk, mul_pow, inv_pow, div_pow,
      Real.sq_sqrt hL0.le, Real.sq_sqrt hk0.le]
    have hid : (N : ℝ) * Real.log N * ((Real.log N)⁻¹ * (midBandPacketMode R₂ a k ^ 2 / k)) =
        ((N : ℝ) / k) * midBandPacketMode R₂ a k ^ 2 := by
      calc
        (N : ℝ) * Real.log N * ((Real.log N)⁻¹ * (midBandPacketMode R₂ a k ^ 2 / k)) =
            (Real.log N * (Real.log N)⁻¹) * (((N : ℝ) / k) * midBandPacketMode R₂ a k ^ 2) := by
          ring
        _ = ((N : ℝ) / k) * midBandPacketMode R₂ a k ^ 2 := by
          rw [mul_inv_cancel₀ hL0.ne', one_mul]
    rw [hid]
    exact le_mul_of_one_le_left (sq_nonneg _) ((one_le_div hk0).mpr hkN)
  calc
    (∑ k ∈ Icc 1 N, midBandPacketMode R₂ a k ^ 2) ≤
        ∑ k ∈ Icc 1 N, (N : ℝ) * Real.log N *
          primeHorizonExtension
            (∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N) k ^ 2 :=
      sum_le_sum hpt
    _ = (N : ℝ) * Real.log N *
          ∑ k ∈ Icc 1 N,
            primeHorizonExtension
              (∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N) k ^ 2 := by
      rw [← mul_sum]
    _ = (N : ℝ) * Real.log N *
          ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by
      rw [sum_primeHorizonExtension_sq]

private theorem midBand_inv_le_of_floor_lt {c : ℝ} (hc1 : 1 ≤ c) {N n : ℕ} (hN0 : (0 : ℝ) < N)
    (hnK : ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ < n) :
    1 / (n : ℝ) ≤ (2 * Real.exp 2 + 1) * c / N := by
  have hArad_pos : 0 < linearNearRowRadius c + 1 := by unfold linearNearRowRadius; positivity
  have hArad_le : linearNearRowRadius c + 1 ≤ (2 * Real.exp 2 + 1) * c := by
    unfold linearNearRowRadius; nlinarith only [hc1]
  have hn_ge : ((⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ + 1 : ℕ) : ℝ) ≤ n :=
    Nat.cast_le.mpr (by omega)
  have ha0_pos : (0 : ℝ) < (⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ + 1 : ℕ) := by positivity
  have hlt : (N : ℝ) / (linearNearRowRadius c + 1) <
      (⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have ha0_inv :
      1 / ((⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ + 1 : ℕ) : ℝ) ≤
        (linearNearRowRadius c + 1) / N := by
    rw [div_le_div_iff₀ ha0_pos hN0]
    have hm := (div_lt_iff₀ hArad_pos).mp hlt
    push_cast; linarith only [hm]
  exact (one_div_le_one_div_of_le ha0_pos hn_ge).trans
    (ha0_inv.trans (div_le_div_of_nonneg_right hArad_le hN0.le))

private theorem exists_midBand_subKernel_sum_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ t, t ∉ Set.Icc 0 1 → φ t = 0)
    (hM : 0 < ∫ t, φ t ^ 2) :
    ∃ C_1 : ℝ, 0 < C_1 ∧
      ∀ {R₂ N : ℕ} {c : ℝ},
        2 ≤ R₂ → 18 * (1 + Real.log R₂) ≤ Real.log N →
        1 ≤ c → c / N ≤ 1 / 3 →
        4 * (linearNearRowRadius c + 1) ^ 2 ≤ N →
        ((R₂ * R₂ : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N →
      ∀ {u : EuclideanSpace ℝ (PrimeHorizonIndex N)}, u ∈ conductorSubspace R₂ N →
        |∑ n ∈ Icc 1 N, primeHorizonExtension u n *
            ∑ j ∈ nearRowIndices c N n, midBandSubKernel φ c N n j * primeHorizonExtension u j| ≤
          C_1 * (c ^ 2 * (1 + Real.log c) / Real.log N) * ‖u‖ ^ 2 := by
  obtain ⟨K_pair, hK_pair0, hpair⟩ := exists_abs_atomArchPair_near_sub_le hφ hsupp hM
  refine ⟨Real.sqrt (20 * (80 * (2 * Real.exp 2) ^ 2)) *
      (K_pair + (1 + Real.exp (1 / 2))) + 1, by positivity, ?_⟩
  intro R₂ N c hR₂ hlog hc1 hw1 hradN hRNT u hu_mem
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hw : c / N ≤ 1 := hw1.trans (by norm_num)
  have hN0 : (0 : ℝ) < N := by
    have : (0 : ℝ) < 4 * (linearNearRowRadius c + 1) ^ 2 := by
      unfold linearNearRowRadius; positivity
    linarith only [this, hradN]
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ 4 * (linearNearRowRadius c + 1) ^ 2 := by
      have h0 : 0 ≤ linearNearRowRadius c := by unfold linearNearRowRadius; positivity
      nlinarith only [h0]
    exact_mod_cast this.trans hradN
  have hcN2 : 2 * c ≤ N := by have := (div_le_iff₀ hN0).mp hw1; linarith only [this, hc0]
  have hL0 : 0 < Real.log N := by have := Real.log_natCast_nonneg R₂; linarith only [hlog, this]
  have hT1 : 1 ≤ linearNearRowRadius c + 1 := by
    have h0 : 0 ≤ linearNearRowRadius c := by unfold linearNearRowRadius; positivity
    linarith only [h0]
  have htop_eq :
      (∑ n ∈ Icc 1 N, primeHorizonExtension u n *
          ∑ j ∈ nearRowIndices c N n, midBandSubKernel φ c N n j * primeHorizonExtension u j) =
        ∑ n ∈ Icc 1 N,
          (if (N : ℝ) / n < linearNearRowRadius c + 1 then primeHorizonExtension u n else 0) *
            ∑ j ∈ nearRowIndices c N n, midBandSubKernel φ c N n j * primeHorizonExtension u j := by
    refine sum_congr rfl fun n hn => ?_
    split_ifs with hlt
    · rfl
    · rw [zero_mul]
      have hempty : nearRowIndices c N n = ∅ := by
        ext j
        simp only [notMem_empty, iff_false]
        intro hj
        have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (mem_Icc.mp hn).1
        have hgeom := (nearRow_geometry_small_width hc0 hn hj hw).2.1
        have hle : (N : ℝ) / n ≤ linearNearRowRadius c := (div_le_iff₀ hn0).mpr hgeom
        exact hlt (by linarith only [hle])
      rw [hempty, sum_empty, mul_zero]
  have hKsub_le : ∀ n ∈ Icc 1 N, ∀ j ∈ nearRowIndices c N n,
      |midBandSubKernel φ c N n j| ≤ (K_pair + (1 + Real.exp (1 / 2))) * c := by
    intro n hn j hj
    have hw0 : 0 < c / N := div_pos hc0 hN0
    have hs : |Real.log j - Real.log n| ≤ 2 * (c / N) := by
      simpa only [mul_div_assoc] using (mem_filter.mp hj).2.2
    have hrem :
        |atomArchPair (atomDilate φ (c / N)) n j / (∫ t, atomDilate φ (c / N) t ^ 2) -
          (Real.log (1 / (c / N)) / ∫ t, φ t ^ 2) *
            shellAutocorr φ (|Real.log j - Real.log n| / (c / N))| ≤ K_pair := by
      have h1 := hpair (c / N) hw0 hw1 n j hs
      simpa only [div_mul_eq_mul_div, mul_div_assoc] using h1
    have hnc : |(completeWeilPoleShift φ c / N) * archimedeanCenterKernel n j| ≤
        (1 + Real.exp (1 / 2)) * c := by
      have h1 := abs_nearCenter_entry_le (φ := φ) (m := 1) zero_lt_one hN1 hcN2 hn hj
      have hm1 : ∀ k, normalizedRamanujanMode 1 k = 1 := fun k => by
        rw [normalizedRamanujanMode, ramanujanMode_one, Nat.totient_one, Nat.cast_one,
          Real.sqrt_one, div_one]
      rw [hm1 j, mul_one, range_one, sum_singleton, hm1 0, abs_one, mul_one,
        abs_of_nonneg (completeWeilPoleShift_nonneg φ hc0.le)] at h1
      have hpole := completeWeilPoleShift_le hφ.continuous hsupp hM hc0.le
      exact h1.trans (by
        simpa only [mul_comm c] using mul_le_mul_of_nonneg_right hpole (by positivity))
    have hid : midBandSubKernel φ c N n j =
        (atomArchPair (atomDilate φ (c / N)) n j / (∫ t, atomDilate φ (c / N) t ^ 2) -
          (Real.log (1 / (c / N)) / ∫ t, φ t ^ 2) *
            shellAutocorr φ (|Real.log j - Real.log n| / (c / N))) +
          (completeWeilPoleShift φ c / N) * archimedeanCenterKernel n j := by
      unfold midBandSubKernel; ring
    rw [hid]
    exact (abs_add_le _ _).trans ((add_le_add hrem hnc).trans (by nlinarith only [hc1, hK_pair0]))
  have hsqA := sum_nearBand_sq_le_of_mem_conductorSubspace hR₂ hlog hc1 hw
    (by positivity) hRNT (midBandSubKernel φ c N) hKsub_le hu_mem
  have huTop_sq :
      (∑ n ∈ Icc 1 N,
        (if (N : ℝ) / n < linearNearRowRadius c + 1 then primeHorizonExtension u n else 0) ^ 2) ≤
        20 * (1 + Real.log c) / Real.log N * ‖u‖ ^ 2 := by
    have hfilt :
        (∑ n ∈ Icc 1 N,
          (if (N : ℝ) / n < linearNearRowRadius c + 1 then primeHorizonExtension u n else 0) ^ 2) =
        ∑ n ∈ (Icc 1 N).filter (fun n : ℕ => (N : ℝ) / n < linearNearRowRadius c + 1),
          primeHorizonExtension u n ^ 2 := by
      rw [sum_filter]; exact sum_congr rfl fun n _ => by split_ifs <;> simp
    rw [hfilt, div_mul_eq_mul_div, le_div_iff₀' hL0]
    have hq := sum_quotient_tail_sq_le_of_mem_conductorSubspace hR₂ hT1 hRNT hlog hu_mem
    have hlogT := log_two_mul_linearNearRowRadius_le hc1
    exact hq.trans (mul_le_mul_of_nonneg_right (by linarith only [hlogT]) (sq_nonneg _))
  rw [htop_eq]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Icc 1 N)
    (fun n => if (N : ℝ) / n < linearNearRowRadius c + 1 then primeHorizonExtension u n else 0)
    (fun n => ∑ j ∈ nearRowIndices c N n, midBandSubKernel φ c N n j * primeHorizonExtension u j)
  have hC1_sq :
      20 * (80 * (2 * Real.exp 2) ^ 2) * (K_pair + (1 + Real.exp (1 / 2))) ^ 2 ≤
        (Real.sqrt (20 * (80 * (2 * Real.exp 2) ^ 2)) *
          (K_pair + (1 + Real.exp (1 / 2))) + 1) ^ 2 := by
    have hs : Real.sqrt (20 * (80 * (2 * Real.exp 2) ^ 2)) ^ 2 =
        20 * (80 * (2 * Real.exp 2) ^ 2) := Real.sq_sqrt (by positivity)
    have hs0 : 0 ≤ Real.sqrt (20 * (80 * (2 * Real.exp 2) ^ 2)) := Real.sqrt_nonneg _
    have hM0 : 0 ≤ K_pair + (1 + Real.exp (1 / 2)) := by positivity
    nlinarith only [hs, hs0, hM0, mul_nonneg hs0 hM0]
  have habs_sq :
      |∑ n ∈ Icc 1 N,
          (if (N : ℝ) / n < linearNearRowRadius c + 1 then primeHorizonExtension u n else 0) *
            ∑ j ∈ nearRowIndices c N n, midBandSubKernel φ c N n j * primeHorizonExtension u j| ^ 2 ≤
        ((Real.sqrt (20 * (80 * (2 * Real.exp 2) ^ 2)) *
          (K_pair + (1 + Real.exp (1 / 2))) + 1) *
            (c ^ 2 * (1 + Real.log c) / Real.log N) * ‖u‖ ^ 2) ^ 2 := by
    rw [sq_abs]
    calc
      _ ≤ _ := hcs
      _ ≤ (20 * (1 + Real.log c) / Real.log N * ‖u‖ ^ 2) *
            ((80 * (2 * Real.exp 2) ^ 2) * c ^ 2 *
              ((K_pair + (1 + Real.exp (1 / 2))) * c) ^ 2 *
              ((1 + Real.log c) / Real.log N) * ‖u‖ ^ 2) :=
        mul_le_mul huTop_sq hsqA
          (sum_nonneg fun _ _ => sq_nonneg _)
          (by have := Real.log_nonneg hc1; positivity)
      _ = (20 * (80 * (2 * Real.exp 2) ^ 2) * (K_pair + (1 + Real.exp (1 / 2))) ^ 2) *
            ((c ^ 2 * (1 + Real.log c) / Real.log N) ^ 2 * (‖u‖ ^ 2) ^ 2) := by
        calc
          (20 * (1 + Real.log c) / Real.log N * ‖u‖ ^ 2) *
              ((80 * (2 * Real.exp 2) ^ 2) * c ^ 2 *
                ((K_pair + (1 + Real.exp (1 / 2))) * c) ^ 2 *
                ((1 + Real.log c) / Real.log N) * ‖u‖ ^ 2) =
            (20 * (80 * (2 * Real.exp 2) ^ 2) * (K_pair + (1 + Real.exp (1 / 2))) ^ 2) *
              (((c ^ 2 * (1 + Real.log c)) * (Real.log N)⁻¹) ^ 2 * (‖u‖ ^ 2) ^ 2) := by ring
          _ = (20 * (80 * (2 * Real.exp 2) ^ 2) * (K_pair + (1 + Real.exp (1 / 2))) ^ 2) *
                ((c ^ 2 * (1 + Real.log c) / Real.log N) ^ 2 * (‖u‖ ^ 2) ^ 2) := by
            rw [div_eq_mul_inv (c ^ 2 * (1 + Real.log c)) (Real.log N)]
      _ ≤ (Real.sqrt (20 * (80 * (2 * Real.exp 2) ^ 2)) *
            (K_pair + (1 + Real.exp (1 / 2))) + 1) ^ 2 *
            ((c ^ 2 * (1 + Real.log c) / Real.log N) ^ 2 * (‖u‖ ^ 2) ^ 2) :=
        mul_le_mul_of_nonneg_right hC1_sq (by positivity)
      _ = ((Real.sqrt (20 * (80 * (2 * Real.exp 2) ^ 2)) *
            (K_pair + (1 + Real.exp (1 / 2))) + 1) *
              (c ^ 2 * (1 + Real.log c) / Real.log N) * ‖u‖ ^ 2) ^ 2 := by ring
  have hrhs0 : 0 ≤ (Real.sqrt (20 * (80 * (2 * Real.exp 2) ^ 2)) *
      (K_pair + (1 + Real.exp (1 / 2))) + 1) *
        (c ^ 2 * (1 + Real.log c) / Real.log N) * ‖u‖ ^ 2 := by
    have := Real.log_nonneg hc1; positivity
  nlinarith only [habs_sq, abs_nonneg (∑ n ∈ Icc 1 N,
    (if (N : ℝ) / n < linearNearRowRadius c + 1 then primeHorizonExtension u n else 0) *
      ∑ j ∈ nearRowIndices c N n, midBandSubKernel φ c N n j * primeHorizonExtension u j), hrhs0]

private theorem midBand_leadKernel_sum_eq {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ t, t ∉ Set.Icc 0 1 → φ t = 0)
    {R₂ N : ℕ} {c : ℝ} (hL0 : 0 < Real.log N) (hc0 : 0 < c) (hw : c / N ≤ 1)
    (hradN : 4 * (linearNearRowRadius c + 1) ^ 2 ≤ N) (a : ℕ → ℝ) :
    (∑ n ∈ Icc 1 N,
        primeHorizonExtension (∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N) n *
          ∑ j ∈ nearRowIndices c N n, midBandLeadKernel φ c N n j *
            primeHorizonExtension (∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N) j) =
      (Real.log N)⁻¹ * (2 * midBandLagSum φ R₂ N c a) := by
  have hN0 : (0 : ℝ) < N := by
    have : (0 : ℝ) < 4 * (linearNearRowRadius c + 1) ^ 2 := by
      unfold linearNearRowRadius; positivity
    linarith only [this, hradN]
  have hlead_eq :
      (∑ n ∈ Icc 1 N,
        primeHorizonExtension (∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N) n *
          ∑ j ∈ nearRowIndices c N n, midBandLeadKernel φ c N n j *
            primeHorizonExtension (∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N) j) =
        (Real.log N)⁻¹ *
          ∑ n ∈ Icc 1 N, ∑ j ∈ (Icc 1 N).filter (fun j => j ≠ n),
            (midBandPacketMode R₂ a n * midBandPacketMode R₂ a j /
              (Real.sqrt n * Real.sqrt j)) * midBandLeadKernel φ c N n j := by
    rw [mul_sum]
    refine sum_congr rfl fun n hn => ?_
    rw [midBand_primeHorizonExtension_eq R₂ N a hn, mul_sum, mul_sum]
    have hsub : nearRowIndices c N n ⊆ (Icc 1 N).filter (fun j => j ≠ n) := fun j hj => by
      obtain ⟨hjI, hjn, _⟩ := mem_filter.mp hj
      exact mem_filter.mpr ⟨hjI, hjn⟩
    rw [← sum_subset hsub]
    · refine sum_congr rfl fun j hj => ?_
      have hjI := (mem_filter.mp hj).1
      rw [midBand_primeHorizonExtension_eq R₂ N a hjI]
      have hsqL : (Real.sqrt (Real.log N))⁻¹ * (Real.sqrt (Real.log N))⁻¹ = (Real.log N)⁻¹ := by
        rw [← mul_inv, Real.mul_self_sqrt hL0.le]
      calc
        (Real.sqrt (Real.log N))⁻¹ * (midBandPacketMode R₂ a n / Real.sqrt n) *
            (midBandLeadKernel φ c N n j *
              ((Real.sqrt (Real.log N))⁻¹ * (midBandPacketMode R₂ a j / Real.sqrt j))) =
          ((Real.sqrt (Real.log N))⁻¹ * (Real.sqrt (Real.log N))⁻¹) *
            ((midBandPacketMode R₂ a n * midBandPacketMode R₂ a j /
              (Real.sqrt n * Real.sqrt j)) * midBandLeadKernel φ c N n j) := by ring
        _ = (Real.log N)⁻¹ *
              ((midBandPacketMode R₂ a n * midBandPacketMode R₂ a j /
                (Real.sqrt n * Real.sqrt j)) * midBandLeadKernel φ c N n j) := by rw [hsqL]
    · intro j hjf hjnri
      obtain ⟨hjI, hjn⟩ := mem_filter.mp hjf
      have hgt : 2 * c / N < |Real.log j - Real.log n| := by
        by_contra hle
        exact hjnri (mem_filter.mpr ⟨hjI, hjn, not_lt.mp hle⟩)
      have hw0 : 0 < c / N := div_pos hc0 hN0
      have hge1 : 1 ≤ |(|Real.log j - Real.log n| / (c / N))| := by
        rw [abs_of_pos (div_pos (lt_of_le_of_lt (by positivity) hgt) hw0), le_div_iff₀ hw0]
        have : 2 * (c / N) < |Real.log j - Real.log n| := by simpa only [mul_div_assoc] using hgt
        linarith only [this, hw0]
      have hK0 : midBandLeadKernel φ c N n j = 0 :=
        shellAutocorr_eq_zero_of_one_le_abs hφ hsupp hge1
      rw [hK0, mul_zero, mul_zero]
  rw [hlead_eq]
  congr 1
  have hBN : ⌊linearNearRowRadius c⌋₊ ≤ N := by
    have h1 : (⌊linearNearRowRadius c⌋₊ : ℝ) ≤ linearNearRowRadius c :=
      Nat.floor_le (by unfold linearNearRowRadius; positivity)
    have h2 : linearNearRowRadius c ≤ 4 * (linearNearRowRadius c + 1) ^ 2 := by
      have : (0 : ℝ) ≤ linearNearRowRadius c := by unfold linearNearRowRadius; positivity
      nlinarith only [this]
    exact_mod_cast (h1.trans h2).trans hradN
  rw [sum_offDiag_symm_eq_two_mul_sum_Icc_sub N
    (fun n j => (midBandPacketMode R₂ a n * midBandPacketMode R₂ a j /
      (Real.sqrt n * Real.sqrt j)) * midBandLeadKernel φ c N n j)
    (fun n j => by
      unfold midBandLeadKernel
      rw [mul_comm (midBandPacketMode R₂ a n) (midBandPacketMode R₂ a j),
        mul_comm (Real.sqrt n) (Real.sqrt j), abs_sub_comm])]
  congr 1
  unfold midBandLagSum
  have hvanish : ∀ h ∈ Icc 1 N, ∀ n ∈ Icc 1 (N - h),
      (⌊linearNearRowRadius c⌋₊ < h ∨
        n ≤ ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊) →
      (midBandPacketMode R₂ a n * midBandPacketMode R₂ a (n + h) /
        (Real.sqrt n * Real.sqrt (n + h : ℕ))) * midBandLeadKernel φ c N n (n + h) = 0 := by
    intro h hh n hn hcond
    obtain ⟨hh1, _⟩ := mem_Icc.mp hh
    obtain ⟨hn1, _⟩ := mem_Icc.mp hn
    have hnI : n ∈ Icc 1 N := mem_Icc.mpr ⟨hn1, by omega⟩
    have hnhI : n + h ∈ Icc 1 N := mem_Icc.mpr ⟨by omega, by omega⟩
    have hK0 : midBandLeadKernel φ c N n (n + h) = 0 := by
      by_contra hne
      have hlt1 : |(|Real.log (n + h : ℕ) - Real.log n| / (c / N))| < 1 := by
        by_contra hge
        exact hne (shellAutocorr_eq_zero_of_one_le_abs hφ hsupp (not_lt.mp hge))
      have hw0 : 0 < c / N := div_pos hc0 hN0
      have hdiv_lt : |Real.log (n + h : ℕ) - Real.log n| / (c / N) < 1 :=
        (le_abs_self _).trans_lt hlt1
      have hlog_le : |Real.log (n + h : ℕ) - Real.log n| ≤ 2 * c / N := by
        have := (div_lt_iff₀ hw0).mp hdiv_lt
        linarith only [this, hw0, (by ring : 1 * (c / N) = c / N),
          (by ring : 2 * (c / N) = 2 * c / N)]
      have hmem : n + h ∈ nearRowIndices c N n :=
        mem_filter.mpr ⟨hnhI, by omega, hlog_le⟩
      have hgeom := nearRow_geometry_small_width hc0 hnI hmem hw
      have hh_le_B : h ≤ ⌊linearNearRowRadius c⌋₊ := by
        apply Nat.le_floor
        have hsub : |((n + h : ℕ) : ℝ) - n| = h := by
          push_cast; rw [add_sub_cancel_left, abs_of_nonneg (Nat.cast_nonneg h)]
        linarith only [hgeom.1, hsub]
      have hK0_lt_n : ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ < n := by
        have hA_pos : 0 < linearNearRowRadius c + 1 := by unfold linearNearRowRadius; positivity
        have hn_real : (1 : ℝ) ≤ n := by exact_mod_cast hn1
        have hstrict : (N : ℝ) < (linearNearRowRadius c + 1) * n := by
          nlinarith only [hgeom.2.1, hn_real]
        exact Nat.floor_lt (div_nonneg hN0.le hA_pos.le) |>.mpr ((div_lt_iff₀' hA_pos).mpr hstrict)
      rcases hcond with hBh | hnK0 <;> omega
    rw [hK0, mul_zero]
  have hsub_h : Icc 1 ⌊linearNearRowRadius c⌋₊ ⊆ Icc 1 N := Icc_subset_Icc_right hBN
  rw [← sum_subset hsub_h]
  · refine sum_congr rfl fun h hh => ?_
    have hsub_n : Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h) ⊆ Icc 1 (N - h) :=
      fun n hn => by simp only [mem_Ioc, mem_Icc] at *; omega
    rw [← sum_subset hsub_n]
    · refine sum_congr rfl fun n hn => ?_
      have hn1 : 1 ≤ n := (mem_Icc.mp (hsub_n hn)).1
      have hh1 : 1 ≤ h := (mem_Icc.mp hh).1
      have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn1
      have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
      have hlog_nonneg : 0 ≤ Real.log (n + h : ℕ) - Real.log n :=
        sub_nonneg.mpr (Real.log_le_log hn0 (Nat.cast_le.mpr (Nat.le_add_right n h)))
      have harg : |Real.log (n + h : ℕ) - Real.log n| / (c / N) =
          (N : ℝ) / c * (Real.log (n + h : ℕ) - Real.log n) := by
        rw [abs_of_nonneg hlog_nonneg, div_div_eq_mul_div]; ring
      unfold midBandLeadKernel
      rw [harg]
      have hjac : (1 / (n : ℝ)) * (Real.sqrt n / Real.sqrt (n + h : ℕ)) =
          1 / (Real.sqrt n * Real.sqrt (n + h : ℕ)) := by
        have hsqn : (n : ℝ) = Real.sqrt n * Real.sqrt n := (Real.mul_self_sqrt hn0.le).symm
        nth_rw 1 [hsqn]
        calc
          (1 / (Real.sqrt n * Real.sqrt n)) * (Real.sqrt n / Real.sqrt (n + h : ℕ)) =
              (Real.sqrt n * (Real.sqrt n)⁻¹) *
                (1 / (Real.sqrt n * Real.sqrt (n + h : ℕ))) := by ring
          _ = 1 / (Real.sqrt n * Real.sqrt (n + h : ℕ)) := by
            rw [mul_inv_cancel₀ hsn.ne', one_mul]
      calc
        (midBandPacketMode R₂ a n * midBandPacketMode R₂ a (n + h) /
            (Real.sqrt n * Real.sqrt (n + h : ℕ))) *
            shellAutocorr φ ((N : ℝ) / c * (Real.log (n + h : ℕ) - Real.log n)) =
          midBandPacketMode R₂ a n * midBandPacketMode R₂ a (n + h) *
            (1 / (Real.sqrt n * Real.sqrt (n + h : ℕ))) *
            shellAutocorr φ ((N : ℝ) / c * (Real.log (n + h : ℕ) - Real.log n)) := by ring
        _ = midBandPacketMode R₂ a n * midBandPacketMode R₂ a (n + h) *
              ((1 / (n : ℝ)) * (Real.sqrt n / Real.sqrt (n + h : ℕ))) *
              shellAutocorr φ ((N : ℝ) / c * (Real.log (n + h : ℕ) - Real.log n)) := by rw [hjac]
        _ = midBandPacketMode R₂ a n * midBandPacketMode R₂ a (n + h) * (1 / (n : ℝ)) *
              (Real.sqrt n / Real.sqrt (n + h : ℕ) *
                shellAutocorr φ ((N : ℝ) / c * (Real.log (n + h : ℕ) - Real.log n))) := by ring
    · intro n hnIcc hnIoc
      have hnK0 : n ≤ ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ := by
        simp only [mem_Icc, mem_Ioc, not_and] at hnIcc hnIoc
        omega
      exact hvanish h (hsub_h hh) n hnIcc (Or.inr hnK0)
  · intro h hhN hhB
    have hBh : ⌊linearNearRowRadius c⌋₊ < h := by
      simp only [mem_Icc, not_and, not_le] at hhN hhB
      exact hhB hhN.1
    exact sum_eq_zero fun n hn => hvanish h hhN n hn (Or.inl hBh)

private theorem exists_midBand_lag_sub_linearized_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ t, t ∉ Set.Icc 0 1 → φ t = 0)
    (hM : 0 < ∫ t, φ t ^ 2) :
    ∃ C_2 : ℝ, 0 ≤ C_2 ∧
      ∀ {R₂ N : ℕ} {c : ℝ},
        0 < Real.log N → 1 ≤ c →
        4 * (linearNearRowRadius c + 1) ^ 2 ≤ N →
      ∀ a : ℕ → ℝ,
        |midBandLagSum φ R₂ N c a - midBandLinearizedSum φ R₂ N c a| ≤
          C_2 * (c ^ 5 * Real.log N / N) *
            ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by
  obtain ⟨K_lip, hG_lip⟩ := exists_lipschitz_shellAutocorr hφ hsupp
  have hG_le : ∀ t, |shellAutocorr φ t| ≤ ∫ t, φ t ^ 2 := abs_shellAutocorr_le hφ hsupp
  refine ⟨(2 * Real.exp 2) * (2 * Real.exp 2 + 1) *
      (4 * (K_lip : ℝ) * (2 * Real.exp 2 + 1) ^ 2 * (2 * Real.exp 2) ^ 2 +
        (2 * Real.exp 2 + 1) * (2 * Real.exp 2) * (∫ t, φ t ^ 2)),
    by positivity, ?_⟩
  intro R₂ N c hL0 hc1 hradN a
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN0 : (0 : ℝ) < N := by
    have : (0 : ℝ) < 4 * (linearNearRowRadius c + 1) ^ 2 := by
      unfold linearNearRowRadius; positivity
    linarith only [this, hradN]
  have hB_le : (⌊linearNearRowRadius c⌋₊ : ℝ) ≤ (2 * Real.exp 2) * c :=
    (Nat.floor_le (by unfold linearNearRowRadius; positivity)).trans_eq
      (by unfold linearNearRowRadius; ring)
  have hArad_pos : 0 < linearNearRowRadius c + 1 := by unfold linearNearRowRadius; positivity
  have hArad_le : linearNearRowRadius c + 1 ≤ (2 * Real.exp 2 + 1) * c := by
    unfold linearNearRowRadius; nlinarith only [hc1]
  have hf_sq_sum := midBandPacketMode_sq_sum_le (R₂ := R₂) hL0 a
  have hdiff : midBandLagSum φ R₂ N c a - midBandLinearizedSum φ R₂ N c a =
      ∑ h ∈ Icc 1 ⌊linearNearRowRadius c⌋₊,
        ∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
          (midBandPacketMode R₂ a n * midBandPacketMode R₂ a (n + h)) *
            ((1 / (n : ℝ)) * (Real.sqrt n / Real.sqrt (n + h : ℕ) *
              shellAutocorr φ ((N : ℝ) / c * (Real.log (n + h : ℕ) - Real.log n)) -
              shellAutocorr φ ((N : ℝ) / c * ((h : ℝ) / n)))) := by
    unfold midBandLagSum midBandLinearizedSum midBandLinearizedWeight
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun h _ => ?_
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun n _ => by ring
  rw [hdiff]
  have hper_h : ∀ h ∈ Icc 1 ⌊linearNearRowRadius c⌋₊,
      |∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
          (midBandPacketMode R₂ a n * midBandPacketMode R₂ a (n + h)) *
            ((1 / (n : ℝ)) * (Real.sqrt n / Real.sqrt (n + h : ℕ) *
              shellAutocorr φ ((N : ℝ) / c * (Real.log (n + h : ℕ) - Real.log n)) -
              shellAutocorr φ ((N : ℝ) / c * ((h : ℝ) / n))))| ≤
        ((2 * Real.exp 2 + 1) *
          (4 * (K_lip : ℝ) * (2 * Real.exp 2 + 1) ^ 2 * (2 * Real.exp 2) ^ 2 +
            (2 * Real.exp 2 + 1) * (2 * Real.exp 2) * (∫ t, φ t ^ 2)) *
          (c ^ 4 * Real.log N / N)) *
            ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by
    intro h hh
    obtain ⟨hh1, hhB⟩ := mem_Icc.mp hh
    have hker_n : ∀ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
        |(1 / (n : ℝ)) * (Real.sqrt n / Real.sqrt (n + h : ℕ) *
            shellAutocorr φ ((N : ℝ) / c * (Real.log (n + h : ℕ) - Real.log n)) -
            shellAutocorr φ ((N : ℝ) / c * ((h : ℝ) / n)))| ≤
          (2 * Real.exp 2 + 1) *
            (4 * (K_lip : ℝ) * (2 * Real.exp 2 + 1) ^ 2 * (2 * Real.exp 2) ^ 2 +
              (2 * Real.exp 2 + 1) * (2 * Real.exp 2) * (∫ t, φ t ^ 2)) *
            c ^ 4 / (N : ℝ) ^ 2 := by
      intro n hn
      obtain ⟨hnK0, _⟩ := mem_Ioc.mp hn
      have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
      have hnh0 : (0 : ℝ) < (n + h : ℕ) := Nat.cast_pos.mpr (by omega)
      have hBr0 : 0 ≤ linearNearRowRadius c := by unfold linearNearRowRadius; positivity
      have hBr_eq : linearNearRowRadius c = (2 * Real.exp 2) * c := by
        unfold linearNearRowRadius; ring
      have hgap : |((n + h : ℕ) : ℝ) - n| ≤ linearNearRowRadius c := by
        have hsub : |((n + h : ℕ) : ℝ) - n| = h := by
          push_cast; rw [add_sub_cancel_left, abs_of_nonneg (Nat.cast_nonneg h)]
        rw [hsub]
        exact (Nat.cast_le.mpr hhB).trans (Nat.floor_le hBr0)
      have hNx : (N : ℝ) ≤ (linearNearRowRadius c + 1) * n := by
        have hlt : (N : ℝ) / (linearNearRowRadius c + 1) <
            (⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
        have hm := (div_lt_iff₀ hArad_pos).mp hlt
        have hn_ge : (⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ : ℝ) + 1 ≤ n := by
          have h1 : ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ + 1 ≤ n := by omega
          exact_mod_cast h1
        have hmul := mul_le_mul_of_nonneg_left hn_ge hArad_pos.le
        linarith only [hm, hmul]
      have hNy : (N : ℝ) ≤ (linearNearRowRadius c + 1) * (n + h : ℕ) :=
        hNx.trans (mul_le_mul_of_nonneg_left
          (Nat.cast_le.mpr (Nat.le_add_right n h)) hArad_pos.le)
      have hlarge : 2 * (linearNearRowRadius c + 1) * linearNearRowRadius c ≤ N := by
        have hle : 2 * (linearNearRowRadius c + 1) * linearNearRowRadius c ≤
            4 * (linearNearRowRadius c + 1) ^ 2 := by
          nlinarith only [hBr0, hArad_pos]
        exact hle.trans hradN
      have hlin := abs_sqrt_log_kernel_sub_linear_le hG_lip hG_le hc0 hN0
        hArad_pos.le hBr0 hn0 hnh0 hgap hNx hNy hlarge
      have harg_eq : (((n + h : ℕ) : ℝ) - n) / n = (h : ℝ) / n := by
        push_cast; rw [add_sub_cancel_left]
      rw [harg_eq] at hlin
      have hker_le :
          (4 * (K_lip : ℝ) * (linearNearRowRadius c + 1) ^ 2 * linearNearRowRadius c ^ 2 / c +
            (linearNearRowRadius c + 1) * linearNearRowRadius c * (∫ t, φ t ^ 2)) / N ≤
            (4 * (K_lip : ℝ) * (2 * Real.exp 2 + 1) ^ 2 * (2 * Real.exp 2) ^ 2 +
              (2 * Real.exp 2 + 1) * (2 * Real.exp 2) * (∫ t, φ t ^ 2)) * c ^ 3 / N := by
        refine div_le_div_of_nonneg_right ?_ hN0.le
        have hA2 : (linearNearRowRadius c + 1) ^ 2 ≤ (2 * Real.exp 2 + 1) ^ 2 * c ^ 2 := by
          have := pow_le_pow_left₀ hArad_pos.le hArad_le 2
          rwa [mul_pow] at this
        have hterm1 :
            4 * (K_lip : ℝ) * (linearNearRowRadius c + 1) ^ 2 * linearNearRowRadius c ^ 2 / c ≤
              4 * (K_lip : ℝ) * (2 * Real.exp 2 + 1) ^ 2 * (2 * Real.exp 2) ^ 2 * c ^ 3 := by
          calc
            4 * (K_lip : ℝ) * (linearNearRowRadius c + 1) ^ 2 *
                linearNearRowRadius c ^ 2 / c ≤
              4 * (K_lip : ℝ) * ((2 * Real.exp 2 + 1) ^ 2 * c ^ 2) *
                linearNearRowRadius c ^ 2 / c :=
              div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hA2 (by positivity)) (sq_nonneg _)) hc0.le
            _ = (4 * (K_lip : ℝ) * (2 * Real.exp 2 + 1) ^ 2 *
                  (2 * Real.exp 2) ^ 2 * c ^ 3) * c / c := by rw [hBr_eq]; ring
            _ = 4 * (K_lip : ℝ) * (2 * Real.exp 2 + 1) ^ 2 *
                  (2 * Real.exp 2) ^ 2 * c ^ 3 := mul_div_cancel_right₀ _ hc0.ne'
        have hterm2 :
            (linearNearRowRadius c + 1) * linearNearRowRadius c * (∫ t, φ t ^ 2) ≤
              (2 * Real.exp 2 + 1) * (2 * Real.exp 2) * (∫ t, φ t ^ 2) * c ^ 3 := by
          have hc23 : c ^ 2 ≤ c ^ 3 := pow_le_pow_right₀ hc1 (by norm_num : 2 ≤ 3)
          calc
            (linearNearRowRadius c + 1) * linearNearRowRadius c * (∫ t, φ t ^ 2) ≤
                ((2 * Real.exp 2 + 1) * c) * linearNearRowRadius c * (∫ t, φ t ^ 2) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hArad_le hBr0) hM.le
            _ = (2 * Real.exp 2 + 1) * (2 * Real.exp 2) * (∫ t, φ t ^ 2) * c ^ 2 := by
              rw [hBr_eq]; ring
            _ ≤ (2 * Real.exp 2 + 1) * (2 * Real.exp 2) * (∫ t, φ t ^ 2) * c ^ 3 :=
              mul_le_mul_of_nonneg_left hc23 (by positivity)
        linarith only [hterm1, hterm2, (by ring :
          4 * (K_lip : ℝ) * (2 * Real.exp 2 + 1) ^ 2 * (2 * Real.exp 2) ^ 2 * c ^ 3 +
            (2 * Real.exp 2 + 1) * (2 * Real.exp 2) * (∫ t, φ t ^ 2) * c ^ 3 =
            (4 * (K_lip : ℝ) * (2 * Real.exp 2 + 1) ^ 2 * (2 * Real.exp 2) ^ 2 +
              (2 * Real.exp 2 + 1) * (2 * Real.exp 2) * (∫ t, φ t ^ 2)) * c ^ 3)]
      rw [abs_mul, abs_of_pos (one_div_pos.mpr hn0)]
      calc
        _ ≤ ((2 * Real.exp 2 + 1) * c / N) *
              ((4 * (K_lip : ℝ) * (2 * Real.exp 2 + 1) ^ 2 * (2 * Real.exp 2) ^ 2 +
                (2 * Real.exp 2 + 1) * (2 * Real.exp 2) * (∫ t, φ t ^ 2)) * c ^ 3 / N) :=
          mul_le_mul (midBand_inv_le_of_floor_lt hc1 hN0 hnK0)
            (hlin.trans hker_le) (abs_nonneg _) (by positivity)
        _ = (2 * Real.exp 2 + 1) *
              (4 * (K_lip : ℝ) * (2 * Real.exp 2 + 1) ^ 2 * (2 * Real.exp 2) ^ 2 +
                (2 * Real.exp 2 + 1) * (2 * Real.exp 2) * (∫ t, φ t ^ 2)) *
              c ^ 4 / (N : ℝ) ^ 2 := by ring
    have hf_prod_sum :
        (∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
          |midBandPacketMode R₂ a n * midBandPacketMode R₂ a (n + h)|) ≤
          (N : ℝ) * Real.log N *
            ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by
      have h1 :
          (∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
            midBandPacketMode R₂ a n ^ 2) ≤
            ∑ k ∈ Icc 1 N, midBandPacketMode R₂ a k ^ 2 := by
        refine sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) fun _ _ _ => sq_nonneg _
        simp only [mem_Ioc, mem_Icc] at *; omega
      have h2 :
          (∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
            midBandPacketMode R₂ a (n + h) ^ 2) ≤
            ∑ k ∈ Icc 1 N, midBandPacketMode R₂ a k ^ 2 := by
        have himg :
            (∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
              midBandPacketMode R₂ a (n + h) ^ 2) =
              ∑ k ∈ (Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h)).image (fun x => x + h),
                midBandPacketMode R₂ a k ^ 2 :=
          (Finset.sum_image (f := fun k => midBandPacketMode R₂ a k ^ 2) (g := fun x => x + h)
            fun x _ y _ hxy => by dsimp only at hxy; omega).symm
        rw [himg]
        refine sum_le_sum_of_subset_of_nonneg (fun k hk => ?_) fun _ _ _ => sq_nonneg _
        rcases mem_image.mp hk with ⟨n, hn, rfl⟩
        simp only [mem_Ioc, mem_Icc] at *; omega
      have hpt : ∀ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
          |midBandPacketMode R₂ a n * midBandPacketMode R₂ a (n + h)| ≤
            (midBandPacketMode R₂ a n ^ 2 + midBandPacketMode R₂ a (n + h) ^ 2) / 2 :=
        fun n _ => by
          rw [abs_mul]
          nlinarith only [sq_nonneg (|midBandPacketMode R₂ a n| - |midBandPacketMode R₂ a (n + h)|),
            sq_abs (midBandPacketMode R₂ a n), sq_abs (midBandPacketMode R₂ a (n + h))]
      calc
        (∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
            |midBandPacketMode R₂ a n * midBandPacketMode R₂ a (n + h)|) ≤
            ∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
              (midBandPacketMode R₂ a n ^ 2 + midBandPacketMode R₂ a (n + h) ^ 2) / 2 :=
          sum_le_sum hpt
        _ = ((∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
                midBandPacketMode R₂ a n ^ 2) +
              (∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
                midBandPacketMode R₂ a (n + h) ^ 2)) / 2 := by
          rw [← sum_div, sum_add_distrib]
        _ ≤ ∑ k ∈ Icc 1 N, midBandPacketMode R₂ a k ^ 2 := by linarith only [h1, h2]
        _ ≤ (N : ℝ) * Real.log N *
              ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := hf_sq_sum
    have hN_sq : c ^ 4 / (N : ℝ) ^ 2 * (N : ℝ) = c ^ 4 / N := by
      rw [sq, ← div_div, div_mul_cancel₀ _ hN0.ne']
    calc
      |∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h), _| ≤
          ∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
            |midBandPacketMode R₂ a n * midBandPacketMode R₂ a (n + h)| *
              ((2 * Real.exp 2 + 1) *
                (4 * (K_lip : ℝ) * (2 * Real.exp 2 + 1) ^ 2 * (2 * Real.exp 2) ^ 2 +
                  (2 * Real.exp 2 + 1) * (2 * Real.exp 2) * (∫ t, φ t ^ 2)) *
                c ^ 4 / (N : ℝ) ^ 2) := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n hn => ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hker_n n hn) (abs_nonneg _)
      _ = ((2 * Real.exp 2 + 1) *
            (4 * (K_lip : ℝ) * (2 * Real.exp 2 + 1) ^ 2 * (2 * Real.exp 2) ^ 2 +
              (2 * Real.exp 2 + 1) * (2 * Real.exp 2) * (∫ t, φ t ^ 2)) *
            c ^ 4 / (N : ℝ) ^ 2) *
          ∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
            |midBandPacketMode R₂ a n * midBandPacketMode R₂ a (n + h)| := by
        rw [← sum_mul, mul_comm]
      _ ≤ ((2 * Real.exp 2 + 1) *
            (4 * (K_lip : ℝ) * (2 * Real.exp 2 + 1) ^ 2 * (2 * Real.exp 2) ^ 2 +
              (2 * Real.exp 2 + 1) * (2 * Real.exp 2) * (∫ t, φ t ^ 2)) *
            c ^ 4 / (N : ℝ) ^ 2) *
          ((N : ℝ) * Real.log N *
            ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hf_prod_sum (by positivity)
      _ = (2 * Real.exp 2 + 1) *
            (4 * (K_lip : ℝ) * (2 * Real.exp 2 + 1) ^ 2 * (2 * Real.exp 2) ^ 2 +
              (2 * Real.exp 2 + 1) * (2 * Real.exp 2) * (∫ t, φ t ^ 2)) *
            (c ^ 4 / (N : ℝ) ^ 2 * (N : ℝ)) * Real.log N *
            ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by ring
      _ = (2 * Real.exp 2 + 1) *
            (4 * (K_lip : ℝ) * (2 * Real.exp 2 + 1) ^ 2 * (2 * Real.exp 2) ^ 2 +
              (2 * Real.exp 2 + 1) * (2 * Real.exp 2) * (∫ t, φ t ^ 2)) *
            (c ^ 4 / N) * Real.log N *
            ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by rw [hN_sq]
      _ = ((2 * Real.exp 2 + 1) *
            (4 * (K_lip : ℝ) * (2 * Real.exp 2 + 1) ^ 2 * (2 * Real.exp 2) ^ 2 +
              (2 * Real.exp 2 + 1) * (2 * Real.exp 2) * (∫ t, φ t ^ 2)) *
            (c ^ 4 * Real.log N / N)) *
            ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by ring
  calc
    |∑ h ∈ Icc 1 ⌊linearNearRowRadius c⌋₊, _| ≤
        ∑ _h ∈ Icc 1 ⌊linearNearRowRadius c⌋₊,
          ((2 * Real.exp 2 + 1) *
            (4 * (K_lip : ℝ) * (2 * Real.exp 2 + 1) ^ 2 * (2 * Real.exp 2) ^ 2 +
              (2 * Real.exp 2 + 1) * (2 * Real.exp 2) * (∫ t, φ t ^ 2)) *
            (c ^ 4 * Real.log N / N)) *
            ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum hper_h)
    _ = (⌊linearNearRowRadius c⌋₊ : ℝ) *
          (((2 * Real.exp 2 + 1) *
            (4 * (K_lip : ℝ) * (2 * Real.exp 2 + 1) ^ 2 * (2 * Real.exp 2) ^ 2 +
              (2 * Real.exp 2 + 1) * (2 * Real.exp 2) * (∫ t, φ t ^ 2)) *
            (c ^ 4 * Real.log N / N)) *
            ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2) := by
      rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    _ ≤ ((2 * Real.exp 2) * c) *
          (((2 * Real.exp 2 + 1) *
            (4 * (K_lip : ℝ) * (2 * Real.exp 2 + 1) ^ 2 * (2 * Real.exp 2) ^ 2 +
              (2 * Real.exp 2 + 1) * (2 * Real.exp 2) * (∫ t, φ t ^ 2)) *
            (c ^ 4 * Real.log N / N)) *
            ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hB_le (by positivity)
    _ = (2 * Real.exp 2) * (2 * Real.exp 2 + 1) *
          (4 * (K_lip : ℝ) * (2 * Real.exp 2 + 1) ^ 2 * (2 * Real.exp 2) ^ 2 +
            (2 * Real.exp 2 + 1) * (2 * Real.exp 2) * (∫ t, φ t ^ 2)) *
          (c ^ 5 * Real.log N / N) *
          ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by ring

private theorem midBandLinearizedSum_eq_mean_add_osc (φ : ℝ → ℝ) (R₂ N : ℕ) (c : ℝ)
    (a : ℕ → ℝ) :
    midBandLinearizedSum φ R₂ N c a =
      midBandMeanSum φ R₂ N c a + midBandOscSum φ R₂ N c a := by
  unfold midBandLinearizedSum midBandMeanSum midBandOscSum
  rw [← sum_add_distrib]
  refine sum_congr rfl fun h _ => ?_
  have hexp : ∀ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
      midBandPacketMode R₂ a n * midBandPacketMode R₂ a (n + h) *
          midBandLinearizedWeight φ c N h n =
        ∑ m ∈ Icc 1 R₂, ∑ l ∈ Icc 1 R₂,
          (a m * a l *
            (if m = l then ramanujanLagCoefficient m h / (m.totient : ℝ) else 0) *
              midBandLinearizedWeight φ c N h n +
            a m * a l * (midBandLinearizedWeight φ c N h n * midBandOscMode m l h n)) := by
    intro n _
    unfold midBandPacketMode
    rw [sum_mul, sum_mul]
    refine sum_congr rfl fun m _ => ?_
    rw [mul_sum, sum_mul]
    refine sum_congr rfl fun l _ => ?_
    unfold midBandOscMode
    ring
  rw [sum_congr rfl hexp, sum_comm]
  have hcomm2 :
      (∑ m ∈ Icc 1 R₂, ∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
          ∑ l ∈ Icc 1 R₂,
            (a m * a l *
              (if m = l then ramanujanLagCoefficient m h / (m.totient : ℝ) else 0) *
                midBandLinearizedWeight φ c N h n +
              a m * a l * (midBandLinearizedWeight φ c N h n * midBandOscMode m l h n))) =
        (∑ m ∈ Icc 1 R₂, ∑ l ∈ Icc 1 R₂,
          a m * a l * (if m = l then ramanujanLagCoefficient m h / (m.totient : ℝ) else 0) *
            ∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
              midBandLinearizedWeight φ c N h n) +
        (∑ m ∈ Icc 1 R₂, ∑ l ∈ Icc 1 R₂,
          a m * a l *
            ∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
              midBandLinearizedWeight φ c N h n * midBandOscMode m l h n) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun m _ => ?_
    rw [sum_comm, ← sum_add_distrib]
    refine sum_congr rfl fun l _ => ?_
    rw [sum_add_distrib, ← mul_sum, ← mul_sum]
  rw [hcomm2]
  congr 1
  refine sum_congr rfl fun m hm => ?_
  have hdiag : ∀ l ∈ Icc 1 R₂,
      a m * a l * (if m = l then ramanujanLagCoefficient m h / (m.totient : ℝ) else 0) *
          (∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
            midBandLinearizedWeight φ c N h n) =
        if l = m then
          a m ^ 2 * (ramanujanLagCoefficient m h / (m.totient : ℝ)) *
            ∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
              midBandLinearizedWeight φ c N h n
        else 0 := by
    intro l _
    by_cases hlm : l = m
    · subst l; rw [if_pos rfl, if_pos rfl]; ring
    · rw [if_neg (Ne.symm hlm), if_neg hlm, mul_zero, zero_mul]
  rw [sum_congr rfl hdiag, sum_ite_eq', if_pos hm]

/-- Harmonic-quotient-tail bound for the diagonal mean lag sum, replacing `O(c^3 / √Q₁)` by
`O(c √c (1 + log c) / √Q₁)`. -/
private theorem exists_midBand_mean_sum_le_three_halves {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ t, t ∉ Set.Icc 0 1 → φ t = 0)
    (hM : 0 < ∫ t, φ t ^ 2) :
    ∃ C_3 : ℝ, 0 ≤ C_3 ∧
      ∀ {Q₁ R₂ N : ℕ} {c : ℝ},
        2 ≤ Q₁ → Q₁ ≤ R₂ → R₂ * R₂ ≤ N → 18 * (1 + Real.log R₂) ≤ Real.log N →
        1 ≤ c → 4 * (linearNearRowRadius c + 1) ^ 2 ≤ N →
      ∀ {a : ℕ → ℝ}, (∀ m ∈ Icc 1 Q₁, a m = 0) →
        |midBandMeanSum φ R₂ N c a| ≤
          C_3 * (c * Real.sqrt c * (1 + Real.log c) / Real.sqrt Q₁) *
            ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by
  have hG_le : ∀ t, |shellAutocorr φ t| ≤ ∫ t, φ t ^ 2 := abs_shellAutocorr_le hφ hsupp
  refine ⟨160 * Real.exp 2 * Real.exp 1 * (∫ t, φ t ^ 2), by positivity, ?_⟩
  intro Q₁ R₂ N c hQ₁ hQR hR₂N hlog hc1 hradN a ha0
  have hR₂ : 2 ≤ R₂ := hQ₁.trans hQR
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hlc0 : 0 ≤ Real.log c := Real.log_nonneg hc1
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ 4 * (linearNearRowRadius c + 1) ^ 2 := by
      have h0 : 0 ≤ linearNearRowRadius c := by unfold linearNearRowRadius; positivity
      nlinarith only [h0]
    exact_mod_cast this.trans hradN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hQ₁0 : (0 : ℝ) < Q₁ := Nat.cast_pos.mpr (by omega)
  have hsQ1 : 0 < Real.sqrt Q₁ := Real.sqrt_pos.mpr hQ₁0
  have hB_le : (⌊linearNearRowRadius c⌋₊ : ℝ) ≤ (2 * Real.exp 2) * c :=
    (Nat.floor_le (by unfold linearNearRowRadius; positivity)).trans_eq
      (by unfold linearNearRowRadius; ring)
  have ha_riesz :
      (∑ m ∈ Icc 1 R₂, a m ^ 2) ≤
        4 * ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by
    have hr := (half_and_three_halves_riesz_of_log_le hR₂ hR₂N hlog a).1
    nlinarith only [hr, sq_nonneg ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖]
  let T := linearNearRowRadius c + 1
  have hT1 : 1 ≤ T := by
    have h0 : 0 ≤ linearNearRowRadius c := by unfold linearNearRowRadius; positivity
    dsimp only [T]; linarith only [h0]
  have hT0 : 0 < T := zero_lt_one.trans_le hT1
  have hw_sum : ∀ h ∈ Icc 1 ⌊linearNearRowRadius c⌋₊,
      |∑ n ∈ Ioc ⌊(N : ℝ) / T⌋₊ (N - h), midBandLinearizedWeight φ c N h n| ≤
        10 * (∫ t, φ t ^ 2) * (1 + Real.log c) := by
    intro h _
    have hsub : Ioc ⌊(N : ℝ) / T⌋₊ (N - h) ⊆
        (Icc 1 N).filter (fun n : ℕ => (N : ℝ) / (n : ℝ) < T) := by
      intro n hn
      obtain ⟨hn_lo, hn_hi⟩ := mem_Ioc.mp hn
      have hn1 : 1 ≤ n := by omega
      have hnN : n ≤ N := by omega
      have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn1
      have hfloor : (N : ℝ) / T < (⌊(N : ℝ) / T⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
      have hn_ge : (⌊(N : ℝ) / T⌋₊ : ℝ) + 1 ≤ n := by
        have h1 : ⌊(N : ℝ) / T⌋₊ + 1 ≤ n := by omega
        exact_mod_cast h1
      have hNT : (N : ℝ) < n * T := (div_lt_iff₀ hT0).mp (hfloor.trans_le hn_ge)
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hn1, hnN⟩,
        (div_lt_iff₀ hn0).mpr (by linarith only [hNT, (by ring : (n : ℝ) * T = T * n)])⟩
    have hlogT := log_two_mul_linearNearRowRadius_le hc1
    have htail : (∑ n ∈ Ioc ⌊(N : ℝ) / T⌋₊ (N - h), 1 / (n : ℝ)) ≤ 10 * (1 + Real.log c) := by
      calc
        (∑ n ∈ Ioc ⌊(N : ℝ) / T⌋₊ (N - h), 1 / (n : ℝ)) ≤
            ∑ n ∈ (Icc 1 N).filter (fun n : ℕ => (N : ℝ) / (n : ℝ) < T), 1 / (n : ℝ) :=
          sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
        _ ≤ 1 + Real.log (2 * T) := HTGeometry.harmonic_quotient_tail_le hN1 hT1
        _ ≤ 10 * (1 + Real.log c) := by dsimp only [T]; linarith only [hlogT]
    calc
      |∑ n ∈ Ioc ⌊(N : ℝ) / T⌋₊ (N - h), midBandLinearizedWeight φ c N h n| ≤
          ∑ n ∈ Ioc ⌊(N : ℝ) / T⌋₊ (N - h), (1 / (n : ℝ)) * (∫ t, φ t ^ 2) := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n hn => ?_)
        have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (by have := (mem_Ioc.mp hn).1; omega)
        unfold midBandLinearizedWeight
        rw [abs_mul, abs_of_pos (one_div_pos.mpr hn0)]
        exact mul_le_mul_of_nonneg_left (hG_le _) (by positivity)
      _ = (∑ n ∈ Ioc ⌊(N : ℝ) / T⌋₊ (N - h), 1 / (n : ℝ)) * (∫ t, φ t ^ 2) := (sum_mul ..).symm
      _ ≤ (10 * (1 + Real.log c)) * (∫ t, φ t ^ 2) :=
        mul_le_mul_of_nonneg_right htail hM.le
      _ = 10 * (∫ t, φ t ^ 2) * (1 + Real.log c) := by ring
  have hm_term : ∀ h ∈ Icc 1 ⌊linearNearRowRadius c⌋₊, ∀ m ∈ Icc 1 R₂,
      |a m ^ 2 * (ramanujanLagCoefficient m h / (m.totient : ℝ)) *
          ∑ n ∈ Ioc ⌊(N : ℝ) / T⌋₊ (N - h), midBandLinearizedWeight φ c N h n| ≤
        a m ^ 2 *
          (20 * Real.exp 1 * (∫ t, φ t ^ 2) *
            (Real.sqrt c * (1 + Real.log c) / Real.sqrt Q₁)) := by
    intro h hh m hm
    obtain ⟨hh1, hhB⟩ := mem_Icc.mp hh
    obtain ⟨hm1, _⟩ := mem_Icc.mp hm
    rcases le_or_gt m Q₁ with hmQ | hmQ
    · rw [ha0 m (mem_Icc.mpr ⟨hm1, hmQ⟩), sq, zero_mul, zero_mul, zero_mul, abs_zero, zero_mul]
    · let g := Nat.gcd m h
      let t := m / g
      have hg : 0 < g := Nat.gcd_pos_of_pos_left h hm1
      have ht : 0 < t := Nat.div_pos (Nat.le_of_dvd hm1 (Nat.gcd_dvd_left m h)) hg
      have hφ0 : (0 : ℝ) < t.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr ht)
      have hh_le : (h : ℝ) ≤ (2 * Real.exp 2) * c := (Nat.cast_le.mpr hhB).trans hB_le
      have hmg : (m : ℝ) = (t : ℝ) * g := by
        exact_mod_cast (Nat.div_mul_cancel (Nat.gcd_dvd_left m h)).symm
      have htbound : (t : ℝ) ≤ 2 * (t.totient : ℝ) ^ 2 := by
        exact_mod_cast nat_le_two_mul_totient_sq t
      have hgh : (g : ℝ) ≤ h := by exact_mod_cast Nat.gcd_le_right m hh1
      have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      have hcast : (Q₁ : ℝ) ≤ (2 * Real.exp 1 * Real.sqrt c * t.totient) ^ 2 := by
        calc
          _ ≤ (m : ℝ) := by exact_mod_cast (Nat.le_of_lt hmQ)
          _ = (t : ℝ) * g := hmg
          _ ≤ (2 * (t.totient : ℝ) ^ 2) * h :=
            mul_le_mul htbound hgh (Nat.cast_nonneg g) (by positivity)
          _ ≤ (2 * (t.totient : ℝ) ^ 2) * ((2 * Real.exp 2) * c) :=
            mul_le_mul_of_nonneg_left hh_le (by positivity)
          _ = 4 * (t.totient : ℝ) ^ 2 * Real.exp 1 ^ 2 * Real.sqrt c ^ 2 := by
            rw [he2, Real.sq_sqrt hc0.le]; ring
          _ = (2 * Real.exp 1 * Real.sqrt c * t.totient) ^ 2 := by ring
      have hsqrt : Real.sqrt Q₁ ≤ 2 * Real.exp 1 * Real.sqrt c * t.totient := by
        calc
          _ ≤ Real.sqrt ((2 * Real.exp 1 * Real.sqrt c * t.totient) ^ 2) :=
            Real.sqrt_le_sqrt hcast
          _ = _ := Real.sqrt_sq (by positivity)
      have htot_inv : 1 / (t.totient : ℝ) ≤ 2 * Real.exp 1 * Real.sqrt c / Real.sqrt Q₁ := by
        rw [div_le_div_iff₀ hφ0 hsQ1, one_mul]
        exact hsqrt
      have hmu : |moebiusReal t| ≤ 1 := by
        unfold moebiusReal
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := t))
      have hdiv_le : |ramanujanLagCoefficient m h / (m.totient : ℝ)| ≤
          2 * Real.exp 1 * Real.sqrt c / Real.sqrt Q₁ := by
        change |sieveLagMultiplier m h| ≤ _
        rw [sieveLagMultiplier_eq_moebius_totient_quotient]
        change |moebiusReal t / (t.totient : ℝ)| ≤ _
        rw [abs_div, abs_of_pos hφ0]
        exact (div_le_div_of_nonneg_right hmu hφ0.le).trans htot_inv
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _), mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      calc
        |ramanujanLagCoefficient m h / (m.totient : ℝ)| *
            |∑ n ∈ Ioc ⌊(N : ℝ) / T⌋₊ (N - h), midBandLinearizedWeight φ c N h n| ≤
          (2 * Real.exp 1 * Real.sqrt c / Real.sqrt Q₁) *
            (10 * (∫ t, φ t ^ 2) * (1 + Real.log c)) :=
          mul_le_mul hdiv_le (hw_sum h hh) (abs_nonneg _) (by positivity)
        _ = 20 * Real.exp 1 * (∫ t, φ t ^ 2) *
              (Real.sqrt c * (1 + Real.log c) / Real.sqrt Q₁) := by ring
  have hK_pos :
      0 ≤ 20 * Real.exp 1 * (∫ t, φ t ^ 2) *
        (Real.sqrt c * (1 + Real.log c) / Real.sqrt Q₁) := by positivity
  have hper_h : ∀ h ∈ Icc 1 ⌊linearNearRowRadius c⌋₊,
      |∑ m ∈ Icc 1 R₂, a m ^ 2 * (ramanujanLagCoefficient m h / (m.totient : ℝ)) *
          ∑ n ∈ Ioc ⌊(N : ℝ) / T⌋₊ (N - h), midBandLinearizedWeight φ c N h n| ≤
        (80 * Real.exp 1 * (∫ t, φ t ^ 2) *
          (Real.sqrt c * (1 + Real.log c) / Real.sqrt Q₁)) *
            ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by
    intro h hh
    calc
      |∑ m ∈ Icc 1 R₂, _| ≤
          ∑ m ∈ Icc 1 R₂, a m ^ 2 *
            (20 * Real.exp 1 * (∫ t, φ t ^ 2) *
              (Real.sqrt c * (1 + Real.log c) / Real.sqrt Q₁)) :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum (hm_term h hh))
      _ = (∑ m ∈ Icc 1 R₂, a m ^ 2) *
            (20 * Real.exp 1 * (∫ t, φ t ^ 2) *
              (Real.sqrt c * (1 + Real.log c) / Real.sqrt Q₁)) := (sum_mul ..).symm
      _ ≤ (4 * ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2) *
            (20 * Real.exp 1 * (∫ t, φ t ^ 2) *
              (Real.sqrt c * (1 + Real.log c) / Real.sqrt Q₁)) :=
        mul_le_mul_of_nonneg_right ha_riesz hK_pos
      _ = (80 * Real.exp 1 * (∫ t, φ t ^ 2) *
            (Real.sqrt c * (1 + Real.log c) / Real.sqrt Q₁)) *
              ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by ring
  unfold midBandMeanSum
  have hRHS_pos :
      0 ≤ (80 * Real.exp 1 * (∫ t, φ t ^ 2) *
        (Real.sqrt c * (1 + Real.log c) / Real.sqrt Q₁)) *
          ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by positivity
  calc
    |∑ h ∈ Icc 1 ⌊linearNearRowRadius c⌋₊, _| ≤
        ∑ _h ∈ Icc 1 ⌊linearNearRowRadius c⌋₊,
          (80 * Real.exp 1 * (∫ t, φ t ^ 2) *
            (Real.sqrt c * (1 + Real.log c) / Real.sqrt Q₁)) *
              ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum hper_h)
    _ = (⌊linearNearRowRadius c⌋₊ : ℝ) *
          ((80 * Real.exp 1 * (∫ t, φ t ^ 2) *
            (Real.sqrt c * (1 + Real.log c) / Real.sqrt Q₁)) *
              ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2) := by
      rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    _ ≤ ((2 * Real.exp 2) * c) *
          ((80 * Real.exp 1 * (∫ t, φ t ^ 2) *
            (Real.sqrt c * (1 + Real.log c) / Real.sqrt Q₁)) *
              ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hB_le hRHS_pos
    _ = 160 * Real.exp 2 * Real.exp 1 * (∫ t, φ t ^ 2) *
          (c * Real.sqrt c * (1 + Real.log c) / Real.sqrt Q₁) *
          ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by ring

private theorem exists_midBand_osc_sum_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ t, t ∉ Set.Icc 0 1 → φ t = 0)
    (hM : 0 < ∫ t, φ t ^ 2) :
    ∃ C_4 : ℝ, 0 ≤ C_4 ∧
      ∀ {R₂ N : ℕ} {c : ℝ},
        2 ≤ R₂ → R₂ * R₂ ≤ N → 18 * (1 + Real.log R₂) ≤ Real.log N →
        1 ≤ c → 4 * (linearNearRowRadius c + 1) ^ 2 ≤ N →
      ∀ a : ℕ → ℝ,
        |midBandOscSum φ R₂ N c a| ≤
          C_4 * (c ^ 3 * (R₂ : ℝ) ^ 4 / N) *
            ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by
  obtain ⟨K_lip, hG_lip⟩ := exists_lipschitz_shellAutocorr hφ hsupp
  have hG_le : ∀ t, |shellAutocorr φ t| ≤ ∫ t, φ t ^ 2 := abs_shellAutocorr_le hφ hsupp
  refine ⟨16 * (2 * Real.exp 2) *
      ((2 * Real.exp 2 + 1) *
        (2 * (∫ t, φ t ^ 2) + (2 * Real.exp 2) * (2 * Real.exp 2 + 1) * (K_lip : ℝ))),
    by positivity, ?_⟩
  intro R₂ N c hR₂ hR₂N hlog hc1 hradN a
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ 4 * (linearNearRowRadius c + 1) ^ 2 := by
      have h0 : 0 ≤ linearNearRowRadius c := by unfold linearNearRowRadius; positivity
      nlinarith only [h0]
    exact_mod_cast this.trans hradN
  have hB_le : (⌊linearNearRowRadius c⌋₊ : ℝ) ≤ (2 * Real.exp 2) * c :=
    (Nat.floor_le (by unfold linearNearRowRadius; positivity)).trans_eq
      (by unfold linearNearRowRadius; ring)
  have ha_riesz :
      (∑ m ∈ Icc 1 R₂, a m ^ 2) ≤
        4 * ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by
    have hr := (half_and_three_halves_riesz_of_log_le hR₂ hR₂N hlog a).1
    nlinarith only [hr, sq_nonneg ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖]
  have ha_l1_sq :
      (∑ m ∈ Icc 1 R₂, ∑ l ∈ Icc 1 R₂, |a m| * |a l|) ≤
        4 * (R₂ : ℝ) * ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by
    have heq : (∑ m ∈ Icc 1 R₂, ∑ l ∈ Icc 1 R₂, |a m| * |a l|) =
        (∑ m ∈ Icc 1 R₂, 1 * |a m|) ^ 2 := by
      simp only [one_mul]
      rw [sq, sum_mul]
      exact sum_congr rfl fun m _ => by rw [mul_sum]
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Icc 1 R₂) (fun _ => (1 : ℝ)) (fun m => |a m|)
    have hcard : (∑ _m ∈ Icc 1 R₂, (1 : ℝ) ^ 2) = R₂ := by
      rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, one_pow, mul_one]
    rw [heq]
    calc
      (∑ m ∈ Icc 1 R₂, 1 * |a m|) ^ 2 ≤
          (∑ _m ∈ Icc 1 R₂, (1 : ℝ) ^ 2) * ∑ m ∈ Icc 1 R₂, |a m| ^ 2 := hcs
      _ = (R₂ : ℝ) * ∑ m ∈ Icc 1 R₂, a m ^ 2 := by
        rw [hcard]; congr 1; exact sum_congr rfl fun m _ => sq_abs (a m)
      _ ≤ (R₂ : ℝ) * (4 * ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2) :=
        mul_le_mul_of_nonneg_left ha_riesz (Nat.cast_nonneg R₂)
      _ = 4 * (R₂ : ℝ) *
            ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by ring
  have hosc_inner : ∀ h ∈ Icc 1 ⌊linearNearRowRadius c⌋₊, ∀ m ∈ Icc 1 R₂, ∀ l ∈ Icc 1 R₂,
      |∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
          midBandLinearizedWeight φ c N h n * midBandOscMode m l h n| ≤
        4 * (R₂ : ℝ) ^ 3 *
          (((2 * Real.exp 2 + 1) *
            (2 * (∫ t, φ t ^ 2) + (2 * Real.exp 2) * (2 * Real.exp 2 + 1) * (K_lip : ℝ))) *
              c ^ 2 / N) := by
    intro h hh m hm l hl
    rcases le_or_gt (N - h) ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ with hle | hgt
    · rw [Ioc_eq_empty_of_le hle, sum_empty, abs_zero]
      positivity
    · have hab := abs_sum_Ioc_mul_le_total_variation hgt.le
        (midBandLinearizedWeight φ c N h) (midBandOscMode m l h)
        (shifted_mode_osc_Ico_le hR₂ hm hl h)
      have htv := linearized_weight_tv_le hG_lip hM.le hG_le hc1 hN1 hh hgt
      exact hab.trans (mul_le_mul_of_nonneg_left htv (by positivity))
  have hper_h : ∀ h ∈ Icc 1 ⌊linearNearRowRadius c⌋₊,
      |∑ m ∈ Icc 1 R₂, ∑ l ∈ Icc 1 R₂,
          a m * a l *
            ∑ n ∈ Ioc ⌊(N : ℝ) / (linearNearRowRadius c + 1)⌋₊ (N - h),
              midBandLinearizedWeight φ c N h n * midBandOscMode m l h n| ≤
        (16 * ((2 * Real.exp 2 + 1) *
          (2 * (∫ t, φ t ^ 2) + (2 * Real.exp 2) * (2 * Real.exp 2 + 1) * (K_lip : ℝ))) *
            (c ^ 2 * (R₂ : ℝ) ^ 4 / N)) *
              ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by
    intro h hh
    calc
      |∑ m ∈ Icc 1 R₂, ∑ l ∈ Icc 1 R₂, _| ≤
          ∑ m ∈ Icc 1 R₂, ∑ l ∈ Icc 1 R₂,
            |a m| * |a l| *
              (4 * (R₂ : ℝ) ^ 3 *
                (((2 * Real.exp 2 + 1) *
                  (2 * (∫ t, φ t ^ 2) +
                    (2 * Real.exp 2) * (2 * Real.exp 2 + 1) * (K_lip : ℝ))) *
                  c ^ 2 / N)) := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun m hm => ?_)
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun l hl => ?_)
        rw [abs_mul, abs_mul]
        exact mul_le_mul_of_nonneg_left (hosc_inner h hh m hm l hl) (by positivity)
      _ = (∑ m ∈ Icc 1 R₂, ∑ l ∈ Icc 1 R₂, |a m| * |a l|) *
            (4 * (R₂ : ℝ) ^ 3 *
              (((2 * Real.exp 2 + 1) *
                (2 * (∫ t, φ t ^ 2) +
                  (2 * Real.exp 2) * (2 * Real.exp 2 + 1) * (K_lip : ℝ))) *
                c ^ 2 / N)) := by
        rw [sum_mul]; exact sum_congr rfl fun m _ => (sum_mul _ _ _).symm
      _ ≤ (4 * (R₂ : ℝ) *
            ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2) *
          (4 * (R₂ : ℝ) ^ 3 *
            (((2 * Real.exp 2 + 1) *
              (2 * (∫ t, φ t ^ 2) +
                (2 * Real.exp 2) * (2 * Real.exp 2 + 1) * (K_lip : ℝ))) *
              c ^ 2 / N)) :=
        mul_le_mul_of_nonneg_right ha_l1_sq (by positivity)
      _ = (16 * ((2 * Real.exp 2 + 1) *
            (2 * (∫ t, φ t ^ 2) + (2 * Real.exp 2) * (2 * Real.exp 2 + 1) * (K_lip : ℝ))) *
              (c ^ 2 * (R₂ : ℝ) ^ 4 / N)) *
                ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by ring
  unfold midBandOscSum
  calc
    |∑ h ∈ Icc 1 ⌊linearNearRowRadius c⌋₊, _| ≤
        ∑ _h ∈ Icc 1 ⌊linearNearRowRadius c⌋₊,
          (16 * ((2 * Real.exp 2 + 1) *
            (2 * (∫ t, φ t ^ 2) + (2 * Real.exp 2) * (2 * Real.exp 2 + 1) * (K_lip : ℝ))) *
              (c ^ 2 * (R₂ : ℝ) ^ 4 / N)) *
                ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum hper_h)
    _ = (⌊linearNearRowRadius c⌋₊ : ℝ) *
          ((16 * ((2 * Real.exp 2 + 1) *
            (2 * (∫ t, φ t ^ 2) + (2 * Real.exp 2) * (2 * Real.exp 2 + 1) * (K_lip : ℝ))) *
              (c ^ 2 * (R₂ : ℝ) ^ 4 / N)) *
                ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2) := by
      rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    _ ≤ ((2 * Real.exp 2) * c) *
          ((16 * ((2 * Real.exp 2 + 1) *
            (2 * (∫ t, φ t ^ 2) + (2 * Real.exp 2) * (2 * Real.exp 2 + 1) * (K_lip : ℝ))) *
              (c ^ 2 * (R₂ : ℝ) ^ 4 / N)) *
                ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hB_le (by positivity)
    _ = 16 * (2 * Real.exp 2) *
          ((2 * Real.exp 2 + 1) *
            (2 * (∫ t, φ t ^ 2) + (2 * Real.exp 2) * (2 * Real.exp 2 + 1) * (K_lip : ℝ))) *
          (c ^ 3 * (R₂ : ℝ) ^ 4 / N) *
          ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by ring

/-- **Sharpened intermediate-band `overlapMatrix` quadratic bound.**
For packets `u = ∑_{m=1}^{R₂} a_m v_m` vanishing on `1 ≤ m ≤ Q₁`, harmonic-tail weighting of the
diagonal lag-autocorrelation sum improves `c^3 / √Q₁` to `c √c (1 + log c) / √Q₁`. -/
theorem exists_overlapMatrix_midBand_inner_le_three_halves {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ t, t ∉ Set.Icc 0 1 → φ t = 0)
    (hM : 0 < ∫ t, φ t ^ 2) :
    ∃ C_mid : ℝ, 0 < C_mid ∧
      ∀ {Q₁ R₂ N : ℕ} {c : ℝ},
        2 ≤ Q₁ → Q₁ ≤ R₂ → R₂ * R₂ ≤ N → 18 * (1 + Real.log R₂) ≤ Real.log N →
        1 ≤ c → c ≤ Real.log N → c / N ≤ 1 / 3 →
        4 * (linearNearRowRadius c + 1) ^ 2 ≤ N →
        ((R₂ * R₂ : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N →
      ∀ {a : ℕ → ℝ}, (∀ m ∈ Icc 1 Q₁, a m = 0) →
        let u := ∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N
        |⟪Matrix.toEuclideanLin (overlapMatrix φ c N) u, u⟫| ≤
          C_mid * (c ^ 2 * (1 + Real.log c) / Real.log N +
            c ^ 5 * Real.log N / N +
            c * Real.sqrt c * (1 + Real.log c) / Real.sqrt Q₁ +
            c ^ 3 * (R₂ : ℝ) ^ 4 / N) * ‖u‖ ^ 2 := by
  obtain ⟨C_1, hC1_pos, hsub_le⟩ := exists_midBand_subKernel_sum_le hφ hsupp hM
  obtain ⟨C_2, hC2_nonneg, herr_le⟩ := exists_midBand_lag_sub_linearized_le hφ hsupp hM
  obtain ⟨C_3, hC3_nonneg, hmean_le⟩ := exists_midBand_mean_sum_le_three_halves hφ hsupp hM
  obtain ⟨C_4, hC4_nonneg, hosc_le⟩ := exists_midBand_osc_sum_le hφ hsupp hM
  refine ⟨C_1 + (2 / ∫ t, φ t ^ 2) * C_2 + (2 / ∫ t, φ t ^ 2) * C_3 +
      (2 / ∫ t, φ t ^ 2) * C_4 + 1, by positivity, ?_⟩
  intro Q₁ R₂ N c hQ₁ hQR hR₂N hlog hc1 _hcL hw1 hradN hRNT a ha0
  dsimp only
  have hR₂ : 2 ≤ R₂ := hQ₁.trans hQR
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hw : c / N ≤ 1 := hw1.trans (by norm_num)
  have hN0 : (0 : ℝ) < N := by
    have : (0 : ℝ) < 4 * (linearNearRowRadius c + 1) ^ 2 := by
      unfold linearNearRowRadius; positivity
    linarith only [this, hradN]
  have hcN2 : 2 * c ≤ N := by have := (div_le_iff₀ hN0).mp hw1; linarith only [this, hc0]
  have hL0 : 0 < Real.log N := by have := Real.log_natCast_nonneg R₂; linarith only [hlog, this]
  have hu_mem :
      (∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N) ∈ conductorSubspace R₂ N :=
    sum_normalizedRamanujanHorizonVector_mem_conductorSubspace R₂ N a
  have hinner_split :
      ⟪Matrix.toEuclideanLin (overlapMatrix φ c N)
          (∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N),
        ∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N⟫ =
        (∑ n ∈ Icc 1 N,
            primeHorizonExtension (∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N) n *
              ∑ j ∈ nearRowIndices c N n, midBandSubKernel φ c N n j *
                primeHorizonExtension
                  (∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N) j) +
          (Real.log (1 / (c / N)) / ∫ t, φ t ^ 2) *
            (∑ n ∈ Icc 1 N,
              primeHorizonExtension (∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N) n *
                ∑ j ∈ nearRowIndices c N n, midBandLeadKernel φ c N n j *
                  primeHorizonExtension
                    (∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N) j) := by
    rw [overlapMatrix_inner_eq φ c N, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun n _ => ?_
    have hrow :
        (∑ j ∈ nearRowIndices c N n,
          (atomArchPair (atomDilate φ (c / N)) n j / (∫ t, atomDilate φ (c / N) t ^ 2) +
            (completeWeilPoleShift φ c / N) * archimedeanCenterKernel n j) *
            primeHorizonExtension
              (∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N) j) =
          (∑ j ∈ nearRowIndices c N n, midBandSubKernel φ c N n j *
            primeHorizonExtension
              (∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N) j) +
            (Real.log (1 / (c / N)) / ∫ t, φ t ^ 2) *
              ∑ j ∈ nearRowIndices c N n, midBandLeadKernel φ c N n j *
                primeHorizonExtension
                  (∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N) j := by
      rw [mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun j _ => by unfold midBandSubKernel midBandLeadKernel; ring
    rw [hrow]; ring
  have hI_sub := hsub_le hR₂ hlog hc1 hw1 hradN hRNT hu_mem
  have hlead_eq := midBand_leadKernel_sum_eq (R₂ := R₂) hφ hsupp hL0 hc0 hw hradN a
  have hS_err := herr_le (R₂ := R₂) hL0 hc1 hradN a
  have hS_mean := hmean_le hQ₁ hQR hR₂N hlog hc1 hradN ha0
  have hS_osc := hosc_le (R₂ := R₂) hR₂ hR₂N hlog hc1 hradN a
  have hS_lag_le :
      |midBandLagSum φ R₂ N c a| ≤
        (C_2 * (c ^ 5 * Real.log N / N) +
          C_3 * (c * Real.sqrt c * (1 + Real.log c) / Real.sqrt Q₁) +
          C_4 * (c ^ 3 * (R₂ : ℝ) ^ 4 / N)) *
            ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by
    have hid : midBandLagSum φ R₂ N c a =
        (midBandLagSum φ R₂ N c a - midBandLinearizedSum φ R₂ N c a) +
          midBandMeanSum φ R₂ N c a + midBandOscSum φ R₂ N c a := by
      linarith only [midBandLinearizedSum_eq_mean_add_osc φ R₂ N c a]
    rw [hid]
    exact (abs_add_three _ _ _).trans ((add_le_add (add_le_add hS_err hS_mean) hS_osc).trans_eq
      (by ring))
  have hL_scale_le :
      |(Real.log (1 / (c / N)) / ∫ t, φ t ^ 2) * (Real.log N)⁻¹| ≤ 1 / ∫ t, φ t ^ 2 := by
    have hlog_inv : |Real.log (1 / (c / N))| ≤ Real.log N := by
      have heq : Real.log (1 / (c / N)) = Real.log N - Real.log c := by
        rw [one_div, Real.log_inv, Real.log_div hc0.ne' hN0.ne']; ring
      rw [heq, abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hc0 (by linarith only [hcN2, hc0])))]
      linarith [Real.log_nonneg hc1]
    have hdiv1 : |Real.log (1 / (c / N))| * (Real.log N)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv]
      exact div_le_one_of_le₀ hlog_inv hL0.le
    rw [abs_mul, abs_div, abs_of_pos hM, abs_inv, abs_of_pos hL0]
    calc
      (|Real.log (1 / (c / N))| / ∫ t, φ t ^ 2) * (Real.log N)⁻¹ =
          (|Real.log (1 / (c / N))| * (Real.log N)⁻¹) / ∫ t, φ t ^ 2 := by ring
      _ ≤ 1 / ∫ t, φ t ^ 2 := div_le_div_of_nonneg_right hdiv1 hM.le
  have hlc0 : 0 ≤ Real.log c := Real.log_nonneg hc1
  have hI_lead :
      |(Real.log (1 / (c / N)) / ∫ t, φ t ^ 2) *
          (∑ n ∈ Icc 1 N,
            primeHorizonExtension (∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N) n *
              ∑ j ∈ nearRowIndices c N n, midBandLeadKernel φ c N n j *
                primeHorizonExtension
                  (∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N) j)| ≤
        (2 / ∫ t, φ t ^ 2) *
          (C_2 * (c ^ 5 * Real.log N / N) +
            C_3 * (c * Real.sqrt c * (1 + Real.log c) / Real.sqrt Q₁) +
            C_4 * (c ^ 3 * (R₂ : ℝ) ^ 4 / N)) *
            ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by
    rw [hlead_eq,
      show (Real.log (1 / (c / N)) / ∫ t, φ t ^ 2) * ((Real.log N)⁻¹ * (2 * midBandLagSum φ R₂ N c a)) =
        2 * ((Real.log (1 / (c / N)) / ∫ t, φ t ^ 2) * (Real.log N)⁻¹) *
          midBandLagSum φ R₂ N c a by ring,
      abs_mul, abs_mul, abs_of_pos zero_lt_two]
    calc
      2 * |(Real.log (1 / (c / N)) / ∫ t, φ t ^ 2) * (Real.log N)⁻¹| *
          |midBandLagSum φ R₂ N c a| ≤
        2 * (1 / ∫ t, φ t ^ 2) *
          ((C_2 * (c ^ 5 * Real.log N / N) +
            C_3 * (c * Real.sqrt c * (1 + Real.log c) / Real.sqrt Q₁) +
            C_4 * (c ^ 3 * (R₂ : ℝ) ^ 4 / N)) *
            ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hL_scale_le zero_le_two)
          hS_lag_le (abs_nonneg _) (by positivity)
      _ = (2 / ∫ t, φ t ^ 2) *
            (C_2 * (c ^ 5 * Real.log N / N) +
              C_3 * (c * Real.sqrt c * (1 + Real.log c) / Real.sqrt Q₁) +
              C_4 * (c ^ 3 * (R₂ : ℝ) ^ 4 / N)) *
              ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by ring
  have h2M_nonneg : 0 ≤ 2 / ∫ t, φ t ^ 2 := by positivity
  have h2C2 : 0 ≤ (2 / ∫ t, φ t ^ 2) * C_2 := mul_nonneg h2M_nonneg hC2_nonneg
  have h2C3 : 0 ≤ (2 / ∫ t, φ t ^ 2) * C_3 := mul_nonneg h2M_nonneg hC3_nonneg
  have h2C4 : 0 ≤ (2 / ∫ t, φ t ^ 2) * C_4 := mul_nonneg h2M_nonneg hC4_nonneg
  have hT1 : 0 ≤ c ^ 2 * (1 + Real.log c) / Real.log N := by positivity
  have hT2 : 0 ≤ c ^ 5 * Real.log N / N := by positivity
  have hT3 : 0 ≤ c * Real.sqrt c * (1 + Real.log c) / Real.sqrt Q₁ := by positivity
  have hT4 : 0 ≤ c ^ 3 * (R₂ : ℝ) ^ 4 / N := by positivity
  rw [hinner_split]
  refine (abs_add_le _ _).trans ((add_le_add hI_sub hI_lead).trans ?_)
  calc
    C_1 * (c ^ 2 * (1 + Real.log c) / Real.log N) *
        ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 +
      (2 / ∫ t, φ t ^ 2) *
        (C_2 * (c ^ 5 * Real.log N / N) +
          C_3 * (c * Real.sqrt c * (1 + Real.log c) / Real.sqrt Q₁) +
          C_4 * (c ^ 3 * (R₂ : ℝ) ^ 4 / N)) *
        ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 =
      (C_1 * (c ^ 2 * (1 + Real.log c) / Real.log N) +
        ((2 / ∫ t, φ t ^ 2) * C_2) * (c ^ 5 * Real.log N / N) +
        ((2 / ∫ t, φ t ^ 2) * C_3) * (c * Real.sqrt c * (1 + Real.log c) / Real.sqrt Q₁) +
        ((2 / ∫ t, φ t ^ 2) * C_4) * (c ^ 3 * (R₂ : ℝ) ^ 4 / N)) *
        ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by ring
    _ ≤ ((C_1 + (2 / ∫ t, φ t ^ 2) * C_2 + (2 / ∫ t, φ t ^ 2) * C_3 +
          (2 / ∫ t, φ t ^ 2) * C_4 + 1) *
        (c ^ 2 * (1 + Real.log c) / Real.log N +
          c ^ 5 * Real.log N / N +
          c * Real.sqrt c * (1 + Real.log c) / Real.sqrt Q₁ +
          c ^ 3 * (R₂ : ℝ) ^ 4 / N)) *
        ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      nlinarith only [hC1_pos, h2C2, h2C3, h2C4, hT1, hT2, hT3, hT4]
    _ = (C_1 + (2 / ∫ t, φ t ^ 2) * C_2 + (2 / ∫ t, φ t ^ 2) * C_3 +
          (2 / ∫ t, φ t ^ 2) * C_4 + 1) *
        (c ^ 2 * (1 + Real.log c) / Real.log N +
          c ^ 5 * Real.log N / N +
          c * Real.sqrt c * (1 + Real.log c) / Real.sqrt Q₁ +
          c ^ 3 * (R₂ : ℝ) ^ 4 / N) *
        ‖∑ m ∈ Icc 1 R₂, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by ring

/-! ### 2. Homogeneous `(3 / 4) log Q` and `(1 / 4) log Q` band coercivity -/

private theorem primeAdjunctionMass_smul_coeffs (R : ℕ) (s : ℝ) (a : ℕ → ℝ) :
    primeAdjunctionMass R (fun m => s * a m) = s ^ 2 * primeAdjunctionMass R a := by
  unfold primeAdjunctionMass
  rw [mul_sum]
  exact sum_congr rfl fun m _ => by ring

private theorem completeWeilEnergy_smul_vec (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) (s : ℝ)
    (u : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    completeWeilEnergy φ c N (s • u) = s ^ 2 * completeWeilEnergy φ c N u := by
  unfold completeWeilEnergy
  rw [map_smul, real_inner_smul_left, real_inner_smul_right]
  ring

private theorem primeAdjunctionMass_eq_zero_of_packet_eq_zero {R N : ℕ}
    (hR : 2 ≤ R) (hRR : R * R ≤ N) (hlog : 18 * (1 + Real.log R) ≤ Real.log N)
    {a : ℕ → ℝ}
    (hu0 : (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N) = 0) :
    primeAdjunctionMass R a = 0 := by
  have hr := (half_and_three_halves_riesz_of_log_le hR hRR hlog a).1
  rw [hu0, norm_zero, sq, mul_zero] at hr
  have hsum_nonneg : 0 ≤ ∑ m ∈ Icc 1 R, a m ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hsum0 : (∑ m ∈ Icc 1 R, a m ^ 2) = 0 := by linarith only [hr, hsum_nonneg]
  have ha0 : ∀ m ∈ Icc 1 R, a m ^ 2 = 0 := fun m hm =>
    (sum_eq_zero_iff_of_nonneg fun k _ => sq_nonneg (a k)).mp hsum0 m hm
  unfold primeAdjunctionMass
  exact sum_eq_zero fun m hm => by rw [ha0 m hm, mul_zero]

private theorem abs_add_three_le' (x₁ x₂ x₃ : ℝ) :
    |x₁ + x₂ + x₃| ≤ |x₁| + |x₂| + |x₃| :=
  (abs_add_le (x₁ + x₂) x₃).trans (add_le_add (abs_add_le x₁ x₂) le_rfl)

private theorem mul_le_one_of_le_mul_le_one' {A C T S : ℝ}
    (hA : A ≤ C) (hC0 : 0 ≤ C) (hT0 : 0 ≤ T) (hTS : T ≤ S) (hCS : C * S ≤ 1) :
    A * T ≤ 1 :=
  (mul_le_mul hA hTS hT0 hC0).trans hCS

/-- Unit-sphere `(3 / 4) log Q` prime coercivity when `1080 * (1 + log R) ≤ log N`. -/
private theorem primePacket_energy_ge_three_quarters_log_unit {Q R N : ℕ}
    (hQ : 2 ≤ Q) (hQR : Q ≤ R) (hRR : R * R ≤ N)
    (hlog : 1080 * (1 + Real.log R) ≤ Real.log N)
    (a : ℕ → ℝ)
    (huQ : (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N) ∈
      (conductorSubspace Q N)ᗮ)
    (hu_unit : ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ = 1) :
    (1 / 8 : ℝ) * primeAdjunctionMass R a + (3 / 4 : ℝ) * Real.log Q -
        (Real.log 4 + 4) ≤
      renormalizedPrimeEnergy N (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N) := by
  let u := ∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N
  let v := ∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N
  let A := ∑ m ∈ Icc 1 R, a m ^ 2
  let B := ∑ m ∈ Icc 1 Q, a m ^ 2
  have hR : 2 ≤ R := hQ.trans hQR
  have hN : 2 ≤ N := by have hh := Nat.mul_le_mul hR hR; omega
  have hlogR : 0 ≤ Real.log R := Real.log_natCast_nonneg R
  have hH : 0 ≤ 1 + Real.log R := by positivity
  have h18 : 18 * (1 + Real.log R) ≤ Real.log N := by linarith only [hlog, hH]
  have hL : 0 < Real.log N := by linarith only [hlog, hlogR]
  have hQlog : Real.log Q ≤ Real.log R := Real.log_le_log
    (by exact_mod_cast (show 0 < Q by omega)) (by exact_mod_cast hQR)
  have h18Q : 18 * (1 + Real.log Q) ≤ Real.log N := by linarith only [h18, hQlog]
  have hQQ : Q * Q ≤ N := (Nat.mul_le_mul hQR hQR).trans hRR
  have hA0 : 0 ≤ A := sum_nonneg fun _ _ => sq_nonneg _
  have hgram := abs_norm_sum_normalizedRamanujanHorizonVector_sq_sub_le hR hRR a
  change |‖u‖ ^ 2 - A| ≤ 9 * (1 + Real.log R) / Real.log N * A at hgram
  have h9_100 : 9 * (1 + Real.log R) / Real.log N ≤ 1 / 100 := by
    rw [div_le_iff₀ hL]
    linarith only [hlog, hH]
  have hA_lb : 98 / 100 ≤ A := by
    have h1 : 1 - A ≤ |‖u‖ ^ 2 - A| := by
      rw [hu_unit, one_pow]
      exact le_abs_self _
    have h2 : |‖u‖ ^ 2 - A| ≤ (1 / 100 : ℝ) * A :=
      hgram.trans (mul_le_mul_of_nonneg_right h9_100 hA0)
    linarith only [h1, h2]
  have hv : ‖v‖ ≤ 1 / 20 := by
    have hh := (low_band_norm_le_of_mem_orthogonal (by omega : 1 ≤ Q) hQR hR hRR h18 huQ).2
    change ‖v‖ ≤ (54 * (1 + Real.log R) / Real.log N) * ‖u‖ at hh
    rw [hu_unit, mul_one] at hh
    exact hh.trans ((div_le_iff₀ hL).mpr (by linarith only [hlog]))
  have hB : B ≤ 1 / 200 := by
    have hh := (half_and_three_halves_riesz_of_log_le hQ hQQ h18Q a).1
    change (1 / 2 : ℝ) * B ≤ ‖v‖ ^ 2 at hh
    have hs : ‖v‖ ^ 2 ≤ (1 / 20 : ℝ) ^ 2 := pow_le_pow_left₀ (norm_nonneg v) hv 2
    linarith only [hh, hs]
  have hlow : (∑ m ∈ Icc 1 R, if m ≤ Q then a m ^ 2 else 0) = B := by
    symm
    change (∑ m ∈ Icc 1 Q, a m ^ 2) = _
    calc
      _ = ∑ m ∈ Icc 1 Q, if m ≤ Q then a m ^ 2 else 0 :=
        sum_congr rfl fun m hm => (if_pos (mem_Icc.mp hm).2).symm
      _ = _ := sum_subset (Icc_subset_Icc le_rfl hQR) fun m hm hn =>
        if_neg fun h => hn (mem_Icc.mpr ⟨(mem_Icc.mp hm).1, h⟩)
  have hdiag : Real.log Q * (A - B) ≤ primeAdjunctionMass R a := by
    rw [← hlow, show A = ∑ m ∈ Icc 1 R, a m ^ 2 from rfl, ← sum_sub_distrib, mul_sum]
    unfold primeAdjunctionMass
    apply sum_le_sum
    intro m hm
    by_cases hmQ : m ≤ Q
    · rw [if_pos hmQ, sub_self, mul_zero]
      exact mul_nonneg (add_nonneg (Real.log_natCast_nonneg m) (tameDifferent_nonneg m))
        (sq_nonneg _)
    · rw [if_neg hmQ, sub_zero]
      have hl : Real.log Q ≤ Real.log m := Real.log_le_log
        (by exact_mod_cast (show 0 < Q by omega)) (by exact_mod_cast (not_le.mp hmQ).le)
      exact mul_le_mul_of_nonneg_right
        (hl.trans (le_add_of_nonneg_right (tameDifferent_nonneg m))) (sq_nonneg _)
  have hmass : (97 / 100 : ℝ) ≤ A - B := by linarith only [hA_lb, hB]
  have hE : (97 / 100 : ℝ) * Real.log Q ≤ primeAdjunctionMass R a := by
    calc
      (97 / 100 : ℝ) * Real.log Q = Real.log Q * (97 / 100 : ℝ) := mul_comm _ _
      _ ≤ Real.log Q * (A - B) := mul_le_mul_of_nonneg_left hmass (Real.log_natCast_nonneg Q)
      _ ≤ _ := hdiag
  have htheta : (95 / 100 : ℝ) ≤ (Real.log N - 3 * Real.log R - 1) / Real.log N := by
    rw [le_div_iff₀ hL]
    linarith only [hlog, hlogR]
  have hdef := poleDefect_normalizedRamanujanPacket_ge_logarithmic hR hN a
  change ((Real.log N - 3 * Real.log R - 1) / Real.log N) * primeAdjunctionMass R a ≤
    poleDefect N (primeHorizonExtension u) at hdef
  have hd : (95 / 100 : ℝ) * primeAdjunctionMass R a ≤ poleDefect N (primeHorizonExtension u) :=
    (mul_le_mul_of_nonneg_right htheta (primeAdjunctionMass_nonneg R a)).trans hdef
  have hr := poleDefect_le_primeEnergy_add_row_cost u
  have hu_sq : ‖u‖ ^ 2 = 1 := by
    change ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 = 1
    rw [hu_unit, one_pow]
  rw [hu_sq, mul_one] at hr
  have hlogQ0 : 0 ≤ Real.log Q := Real.log_natCast_nonneg Q
  linarith only [hd, hE, hr, hlogQ0]

/-- **2-homogeneous `(3 / 4) log Q` band coercivity with `c √c (1 + log c) / √Q` mid-band error.**
For any packet `u = ∑_{m=1}^R a_m v_m ∈ (conductorSubspace Q N)ᗮ`, without unit-norm restriction,
`completeWeilEnergy` retains `(1 / 8) * primeAdjunctionMass R a` together with
`((3 / 4) * log Q - log c - C_coerc) * ‖u‖^2`. -/
theorem exists_completeWeilEnergy_ge_three_quarters_log_homogeneous :
    ∃ C_coerc C_small : ℝ, 0 < C_coerc ∧ 0 < C_small ∧
      ∀ {Q R N : ℕ} {c : ℝ},
        2 ≤ Q → Q ≤ R → R ^ 6 ≤ N → 36 * (1 + Real.log R) ≤ Real.log N →
        1 ≤ c → c ≤ Real.log N → c / N ≤ 1 / 3 →
        4 * (linearNearRowRadius c + 1) ^ 2 ≤ N →
        ((R * R : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N →
        C_small * (c * (1 + Real.log c) * (1 + Real.log R) / Real.log N +
          c * (1 + Real.log R) / Real.log N + c ^ 2 / Real.log N +
          c ^ 2 * (1 + Real.log R) * (1 + Real.log c) / Real.log N +
          c ^ 2 * (R : ℝ) * Real.sqrt (Real.log N / N) +
          c ^ 5 * Real.log N / N +
          c * Real.sqrt c * (1 + Real.log c) / Real.sqrt Q +
          c ^ 3 * (R : ℝ) ^ 4 / N + c ^ 2 * (1 + Real.log c) / Real.log N) ≤ 1 →
      ∀ a : ℕ → ℝ,
        (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N) ∈ (conductorSubspace Q N)ᗮ →
        (1 / 8 : ℝ) * primeAdjunctionMass R a +
          ((3 / 4 : ℝ) * Real.log Q - Real.log c - C_coerc) *
            ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
        completeWeilEnergy tiltedUnitSpline c N
          (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N) := by
  obtain ⟨C_dec, C_err, hC_dec, hC_err, hdec⟩ :=
    exists_completeWeilEnergy_ge_prime_sub_overlap_quadratic
  obtain ⟨C_ov, hC_ov, hov⟩ := exists_overlapMatrix_inner_le_of_mem_conductorSubspace
    contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
  obtain ⟨C_mid, hC_mid, hmid⟩ := exists_overlapMatrix_midBand_inner_le_three_halves
    contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
  refine ⟨C_dec + (Real.log 4 + 4) + 5,
    C_err + 1080 + 270 * C_ov + C_mid + 1, ?_, by positivity, ?_⟩
  · have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    positivity
  intro Q R N c hQ hQR hR6 hlog36 hc1 hcL hw hrad hsize hsmall a huQ
  let u := ∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N
  have hR : 2 ≤ R := hQ.trans hQR
  have hRR : R * R ≤ N := by
    have hh := (Nat.pow_le_pow_right (by omega : 0 < R) (by norm_num : 2 ≤ 6)).trans hR6
    simpa only [sq] using hh
  have h18 : 18 * (1 + Real.log R) ≤ Real.log N := by
    have hh := Real.log_natCast_nonneg R
    linarith only [hlog36, hh]
  by_cases hu0 : u = 0
  · have hE0 : primeAdjunctionMass R a = 0 :=
      primeAdjunctionMass_eq_zero_of_packet_eq_zero hR hRR h18 hu0
    change (1 / 8 : ℝ) * primeAdjunctionMass R a +
        ((3 / 4 : ℝ) * Real.log Q - Real.log c - (C_dec + (Real.log 4 + 4) + 5)) * ‖u‖ ^ 2 ≤
      completeWeilEnergy tiltedUnitSpline c N u
    rw [hE0, hu0, norm_zero, sq, mul_zero, mul_zero, mul_zero, add_zero]
    unfold completeWeilEnergy
    rw [map_zero, inner_zero_right]
  · have hunorm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
    let s := ‖u‖⁻¹
    have hs_pos : 0 < s := inv_pos.mpr hunorm_pos
    let a' : ℕ → ℝ := fun m => s * a m
    let u' := ∑ m ∈ Icc 1 R, a' m • normalizedRamanujanHorizonVector m N
    have hu'_eq : u' = s • u := by
      dsimp only [u', u, a']
      rw [Finset.smul_sum]
      exact sum_congr rfl fun m _ => (smul_smul s (a m) _).symm
    have hu'_unit : ‖u'‖ = 1 := by
      rw [hu'_eq, norm_smul, Real.norm_eq_abs, abs_of_pos hs_pos]
      exact inv_mul_cancel₀ hunorm_pos.ne'
    have hu'_hi : ‖u'‖ ≤ 1 := hu'_unit.le
    have hu'_Q : u' ∈ (conductorSubspace Q N)ᗮ := by
      rw [hu'_eq]
      exact Submodule.smul_mem _ s huQ
    have hu'_mem : u' ∈ conductorSubspace R N :=
      sum_normalizedRamanujanHorizonVector_mem_conductorSubspace R N a'
    have hu'_1 : u' ∈ (conductorSubspace 1 N)ᗮ := fun v hv =>
      hu'_Q v (conductorSubspace_mono (by omega : 1 ≤ Q) N hv)
    have hL : 0 < Real.log N := by
      have hh := Real.log_natCast_nonneg R
      linarith only [hlog36, hh]
    have hlogc : 0 ≤ Real.log c := Real.log_nonneg hc1
    have hlogR : 0 ≤ Real.log R := Real.log_natCast_nonneg R
    have ht1 : 0 ≤ c * (1 + Real.log c) * (1 + Real.log R) / Real.log N := by positivity
    have ht2 : 0 ≤ c * (1 + Real.log R) / Real.log N := by positivity
    have ht3 : 0 ≤ c ^ 2 / Real.log N := by positivity
    have ht4 : 0 ≤ c ^ 2 * (1 + Real.log R) * (1 + Real.log c) / Real.log N := by positivity
    have ht5 : 0 ≤ c ^ 2 * (R : ℝ) * Real.sqrt (Real.log N / N) := by positivity
    have ht6 : 0 ≤ c ^ 5 * Real.log N / N := by positivity
    have ht7 : 0 ≤ c * Real.sqrt c * (1 + Real.log c) / Real.sqrt Q := by positivity
    have ht8 : 0 ≤ c ^ 3 * (R : ℝ) ^ 4 / N := by positivity
    have ht9 : 0 ≤ c ^ 2 * (1 + Real.log c) / Real.log N := by positivity
    have hsumC : 0 ≤ C_err + 1080 + 270 * C_ov + C_mid + 1 := by positivity
    have hratio : 0 ≤ (1 + Real.log R) / Real.log N := by positivity
    have hratio_le : (1 + Real.log R) / Real.log N ≤
        c * (1 + Real.log c) * (1 + Real.log R) / Real.log N := by
      have hh : 1 ≤ c * (1 + Real.log c) := by nlinarith only [hc1, hlogc]
      have hm := mul_le_mul_of_nonneg_right hh hratio
      convert hm using 2 <;> first | rfl | ring
    have h1080 : 1080 * ((1 + Real.log R) / Real.log N) ≤ 1 :=
      mul_le_one_of_le_mul_le_one'
        (by linarith only [hC_err, hC_ov, hC_mid]) hsumC hratio
        (by linarith only [hratio_le, ht2, ht3, ht4, ht5, ht6, ht7, ht8, ht9]) hsmall
    have hlog1080 : 1080 * (1 + Real.log R) ≤ Real.log N := by
      rw [← mul_div_assoc, div_le_one hL] at h1080
      exact h1080
    have herr : C_err * (c * (1 + Real.log R) / Real.log N + c ^ 2 / Real.log N +
        c ^ 2 * (1 + Real.log R) * (1 + Real.log c) / Real.log N +
        c ^ 2 * (R : ℝ) * Real.sqrt (Real.log N / N)) ≤ 1 :=
      mul_le_one_of_le_mul_le_one'
        (by linarith only [hC_ov, hC_mid]) hsumC (by linarith only [ht2, ht3, ht4, ht5])
        (by linarith only [ht1, ht6, ht7, ht8, ht9]) hsmall
    have h270 : 270 * C_ov * (c * (1 + Real.log c) * (1 + Real.log R) / Real.log N) ≤ 1 :=
      mul_le_one_of_le_mul_le_one'
        (by linarith only [hC_err, hC_mid]) hsumC ht1
        (by linarith only [ht2, ht3, ht4, ht5, ht6, ht7, ht8, ht9]) hsmall
    have hmid1 : C_mid * (c ^ 2 * (1 + Real.log c) / Real.log N +
        c ^ 5 * Real.log N / N +
        c * Real.sqrt c * (1 + Real.log c) / Real.sqrt Q +
        c ^ 3 * (R : ℝ) ^ 4 / N) ≤ 1 :=
      mul_le_one_of_le_mul_le_one'
        (by linarith only [hC_err, hC_ov]) hsumC (by linarith only [ht9, ht6, ht7, ht8])
        (by linarith only [ht1, ht2, ht3, ht4, ht5]) hsmall
    have hbase := hdec hR hR6 h18 hc1 hw hsize herr hu'_mem hu'_1 hu'_hi
    have hprime := primePacket_energy_ge_three_quarters_log_unit hQ hQR hRR hlog1080 a' hu'_Q hu'_unit
    -- Split `u' = v_low + y_high` at `Q`.
    let v_low := ∑ m ∈ Icc 1 Q, a' m • normalizedRamanujanHorizonVector m N
    let b_hi : ℕ → ℝ := fun m => if m ≤ Q then 0 else a' m
    let y_high := ∑ m ∈ Icc 1 R, b_hi m • normalizedRamanujanHorizonVector m N
    have hv_low_R : v_low = ∑ m ∈ Icc 1 R,
        (if m ≤ Q then a' m else 0) • normalizedRamanujanHorizonVector m N := by
      dsimp only [v_low]
      have hsub : Icc 1 Q ⊆ Icc 1 R := Icc_subset_Icc le_rfl hQR
      calc
        (∑ m ∈ Icc 1 Q, a' m • normalizedRamanujanHorizonVector m N) =
            ∑ m ∈ Icc 1 Q, (if m ≤ Q then a' m else 0) • normalizedRamanujanHorizonVector m N :=
          sum_congr rfl fun m hm => by rw [if_pos (mem_Icc.mp hm).2]
        _ = _ := sum_subset hsub fun m hmR hmQ => by
          have hnot : ¬m ≤ Q := fun h => hmQ (mem_Icc.mpr ⟨(mem_Icc.mp hmR).1, h⟩)
          rw [if_neg hnot, zero_smul]
    have hsplit : u' = v_low + y_high := by
      dsimp only [u', y_high, b_hi]
      rw [hv_low_R, ← sum_add_distrib]
      refine sum_congr rfl fun m _ => ?_
      split_ifs <;> simp
    have hv_mem : v_low ∈ conductorSubspace R N :=
      conductorSubspace_mono hQR N (sum_normalizedRamanujanHorizonVector_mem_conductorSubspace Q N a')
    have hy_mem : y_high ∈ conductorSubspace R N :=
      sum_normalizedRamanujanHorizonVector_mem_conductorSubspace R N b_hi
    have hv_bound : ‖v_low‖ ≤ 54 * (1 + Real.log R) / Real.log N := by
      have hlow := (low_band_norm_le_of_mem_orthogonal (by omega : 1 ≤ Q) hQR hR hRR h18 hu'_Q).2
      change ‖v_low‖ ≤ (54 * (1 + Real.log R) / Real.log N) * ‖u'‖ at hlow
      rw [hu'_unit, mul_one] at hlow
      exact hlow
    have hv20 : ‖v_low‖ ≤ 1 / 20 := by
      have h54 : 54 * (1 + Real.log R) / Real.log N =
          54 * ((1 + Real.log R) / Real.log N) := by ring
      linarith only [hv_bound, h1080, h54]
    have hy2 : ‖y_high‖ ≤ 2 := by
      have hy_eq : y_high = u' - v_low := by rw [hsplit]; abel
      have htri : ‖y_high‖ ≤ ‖u'‖ + ‖v_low‖ := by rw [hy_eq]; exact norm_sub_le _ _
      linarith only [htri, hu'_hi, hv20]
    have hov_diff :
        |⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) u', u'⟫ -
          ⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) y_high, y_high⟫| ≤ 1 := by
      have hexp :
          ⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) u', u'⟫ -
            ⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) y_high, y_high⟫ =
          ⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) v_low, v_low⟫ +
            ⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) v_low, y_high⟫ +
            ⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) y_high, v_low⟫ := by
        rw [hsplit, map_add, inner_add_left, inner_add_right, inner_add_right]; ring
      have h1 := hov hR hR h18 h18 hc1 hcL hw hsize hsize hv_mem hv_mem
      have h2 := hov hR hR h18 h18 hc1 hcL hw hsize hsize hv_mem hy_mem
      have h3 := hov hR hR h18 h18 hc1 hcL hw hsize hsize hy_mem hv_mem
      have hnorm_sum : ‖v_low‖ * ‖v_low‖ + ‖v_low‖ * ‖y_high‖ + ‖y_high‖ * ‖v_low‖ ≤ 5 * ‖v_low‖ := by
        nlinarith only [hv20, hy2, norm_nonneg v_low]
      rw [hexp]
      calc
        |⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) v_low, v_low⟫ +
            ⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) v_low, y_high⟫ +
            ⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) y_high, v_low⟫| ≤
          |⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) v_low, v_low⟫| +
            |⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) v_low, y_high⟫| +
            |⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) y_high, v_low⟫| :=
          abs_add_three_le' _ _ _
        _ ≤ C_ov * c * (1 + Real.log c) *
              (‖v_low‖ * ‖v_low‖ + ‖v_low‖ * ‖y_high‖ + ‖y_high‖ * ‖v_low‖) := by
          linarith only [h1, h2, h3]
        _ ≤ C_ov * c * (1 + Real.log c) * (5 * (54 * (1 + Real.log R) / Real.log N)) :=
          mul_le_mul_of_nonneg_left (hnorm_sum.trans (by linarith only [hv_bound])) (by positivity)
        _ = 270 * C_ov * (c * (1 + Real.log c) * (1 + Real.log R) / Real.log N) := by ring
        _ ≤ 1 := h270
    have hb0 : ∀ m ∈ Icc 1 Q, b_hi m = 0 := fun m hm => if_pos (mem_Icc.mp hm).2
    have hmy := hmid hQ hQR hRR h18 hc1 hcL hw hrad hsize hb0
    change |⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) y_high, y_high⟫| ≤
      C_mid * (c ^ 2 * (1 + Real.log c) / Real.log N +
        c ^ 5 * Real.log N / N +
        c * Real.sqrt c * (1 + Real.log c) / Real.sqrt Q +
        c ^ 3 * (R : ℝ) ^ 4 / N) * ‖y_high‖ ^ 2 at hmy
    have hy4 : ‖y_high‖ ^ 2 ≤ 4 := by nlinarith only [hy2, norm_nonneg y_high]
    have hov_y : |⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) y_high, y_high⟫| ≤ 4 :=
      hmy.trans ((mul_le_mul hmid1 hy4 (sq_nonneg _) zero_le_one).trans_eq (one_mul _))
    have hov_u' : ⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) u', u'⟫ ≤ 5 := by
      linarith only [(abs_le.mp hov_diff).2, (abs_le.mp hov_y).2]
    have hunit_ineq :
        (1 / 8 : ℝ) * primeAdjunctionMass R a' +
          ((3 / 4 : ℝ) * Real.log Q - Real.log c - (C_dec + (Real.log 4 + 4) + 5)) ≤
        completeWeilEnergy tiltedUnitSpline c N u' := by
      linarith only [hbase, hprime, hov_u']
    rw [primeAdjunctionMass_smul_coeffs R s a, hu'_eq,
      completeWeilEnergy_smul_vec tiltedUnitSpline c N s u] at hunit_ineq
    have hmul := mul_le_mul_of_nonneg_left hunit_ineq (sq_nonneg ‖u‖)
    have hsu : ‖u‖ ^ 2 * s ^ 2 = 1 := by
      dsimp only [s]
      rw [← mul_pow, mul_inv_cancel₀ hunorm_pos.ne', one_pow]
    have hlhs :
        ‖u‖ ^ 2 *
          ((1 / 8 : ℝ) * (s ^ 2 * primeAdjunctionMass R a) +
            ((3 / 4 : ℝ) * Real.log Q - Real.log c - (C_dec + (Real.log 4 + 4) + 5))) =
        (1 / 8 : ℝ) * ((‖u‖ ^ 2 * s ^ 2) * primeAdjunctionMass R a) +
          ((3 / 4 : ℝ) * Real.log Q - Real.log c - (C_dec + (Real.log 4 + 4) + 5)) * ‖u‖ ^ 2 := by
      ring
    have hrhs :
        ‖u‖ ^ 2 * (s ^ 2 * completeWeilEnergy tiltedUnitSpline c N u) =
          (‖u‖ ^ 2 * s ^ 2) * completeWeilEnergy tiltedUnitSpline c N u := by ring
    rw [hlhs, hrhs, hsu, one_mul, one_mul] at hmul
    exact hmul

/-- **2-homogeneous `(1 / 4) log Q` band coercivity.**
Homogeneous rescaling of `exists_completeWeilEnergy_ge_adjunction_and_log` to arbitrary packet
norms without unit-sphere normalization. -/
theorem exists_completeWeilEnergy_ge_quarter_log_homogeneous :
    ∃ C_coerc C_small : ℝ, 0 < C_coerc ∧ 0 < C_small ∧
      ∀ {Q R N : ℕ} {c : ℝ},
        2 ≤ Q → Q ≤ R → R ^ 6 ≤ N → 36 * (1 + Real.log R) ≤ Real.log N →
        1 ≤ c → c ≤ Real.log N → c / N ≤ 1 / 3 →
        4 * (linearNearRowRadius c + 1) ^ 2 ≤ N →
        ((R * R : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N →
        C_small * (c * (1 + Real.log c) * (1 + Real.log R) / Real.log N +
          c * (1 + Real.log R) / Real.log N + c ^ 2 / Real.log N +
          c ^ 2 * (1 + Real.log R) * (1 + Real.log c) / Real.log N +
          c ^ 2 * (R : ℝ) * Real.sqrt (Real.log N / N) +
          c ^ 5 * Real.log N / N + c ^ 3 / Real.sqrt Q +
          c ^ 3 * (R : ℝ) ^ 4 / N + c ^ 2 * (1 + Real.log c) / Real.log N) ≤ 1 →
      ∀ a : ℕ → ℝ,
        (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N) ∈ (conductorSubspace Q N)ᗮ →
        (1 / 8 : ℝ) * primeAdjunctionMass R a +
          ((1 / 4 : ℝ) * Real.log Q - Real.log c - C_coerc) *
            ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
        completeWeilEnergy tiltedUnitSpline c N
          (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N) := by
  obtain ⟨C_coerc, C_small, hC_coerc, hC_small, hunit⟩ :=
    exists_completeWeilEnergy_ge_adjunction_and_log
  refine ⟨C_coerc, C_small, hC_coerc, hC_small, ?_⟩
  intro Q R N c hQ hQR hR6 hlog36 hc1 hcL hw hrad hsize hsmall a huQ
  let u := ∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N
  have hR : 2 ≤ R := hQ.trans hQR
  have hRR : R * R ≤ N := by
    have hh := (Nat.pow_le_pow_right (by omega : 0 < R) (by norm_num : 2 ≤ 6)).trans hR6
    simpa only [sq] using hh
  have h18 : 18 * (1 + Real.log R) ≤ Real.log N := by
    have hh := Real.log_natCast_nonneg R
    linarith only [hlog36, hh]
  by_cases hu0 : u = 0
  · have hE0 : primeAdjunctionMass R a = 0 :=
      primeAdjunctionMass_eq_zero_of_packet_eq_zero hR hRR h18 hu0
    change (1 / 8 : ℝ) * primeAdjunctionMass R a +
        ((1 / 4 : ℝ) * Real.log Q - Real.log c - C_coerc) * ‖u‖ ^ 2 ≤
      completeWeilEnergy tiltedUnitSpline c N u
    rw [hE0, hu0, norm_zero, sq, mul_zero, mul_zero, mul_zero, add_zero]
    unfold completeWeilEnergy
    rw [map_zero, inner_zero_right]
  · have hunorm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
    let s := ‖u‖⁻¹
    have hs_pos : 0 < s := inv_pos.mpr hunorm_pos
    let a' : ℕ → ℝ := fun m => s * a m
    let u' := ∑ m ∈ Icc 1 R, a' m • normalizedRamanujanHorizonVector m N
    have hu'_eq : u' = s • u := by
      dsimp only [u', u, a']
      rw [Finset.smul_sum]
      exact sum_congr rfl fun m _ => (smul_smul s (a m) _).symm
    have hu'_unit : ‖u'‖ = 1 := by
      rw [hu'_eq, norm_smul, Real.norm_eq_abs, abs_of_pos hs_pos]
      exact inv_mul_cancel₀ hunorm_pos.ne'
    have hu'_lo : 3 / 4 ≤ ‖u'‖ ^ 2 := by rw [hu'_unit]; norm_num
    have hu'_hi : ‖u'‖ ≤ 1 := hu'_unit.le
    have hu'_Q : u' ∈ (conductorSubspace Q N)ᗮ := by
      rw [hu'_eq]
      exact Submodule.smul_mem _ s huQ
    have hunit_ineq := hunit hQ hQR hR6 hlog36 hc1 hcL hw hrad hsize hsmall a' hu'_Q hu'_lo hu'_hi
    change (1 / 8 : ℝ) * primeAdjunctionMass R a' + (1 / 4 : ℝ) * Real.log Q -
        Real.log c - C_coerc ≤ completeWeilEnergy tiltedUnitSpline c N u' at hunit_ineq
    rw [primeAdjunctionMass_smul_coeffs R s a, hu'_eq,
      completeWeilEnergy_smul_vec tiltedUnitSpline c N s u] at hunit_ineq
    have hmul := mul_le_mul_of_nonneg_left hunit_ineq (sq_nonneg ‖u‖)
    have hsu : ‖u‖ ^ 2 * s ^ 2 = 1 := by
      dsimp only [s]
      rw [← mul_pow, mul_inv_cancel₀ hunorm_pos.ne', one_pow]
    have hlhs :
        ‖u‖ ^ 2 *
          ((1 / 8 : ℝ) * (s ^ 2 * primeAdjunctionMass R a) +
            (1 / 4 : ℝ) * Real.log Q - Real.log c - C_coerc) =
        (1 / 8 : ℝ) * ((‖u‖ ^ 2 * s ^ 2) * primeAdjunctionMass R a) +
          ((1 / 4 : ℝ) * Real.log Q - Real.log c - C_coerc) * ‖u‖ ^ 2 := by
      ring
    have hrhs :
        ‖u‖ ^ 2 * (s ^ 2 * completeWeilEnergy tiltedUnitSpline c N u) =
          (‖u‖ ^ 2 * s ^ 2) * completeWeilEnergy tiltedUnitSpline c N u := by ring
    rw [hlhs, hrhs, hsu, one_mul, one_mul] at hmul
    exact hmul

/-! ### 3. Subspace-localized separated cross norm and `c^9` split cross payment -/

/-- **Subspace `O(c^4 / log N)` squared-norm bound for `separatedCrossErrorMatrix φ c N`.**
On `conductorSubspace R N` (`R^4 ≤ N`), dominating `(max n j)^2 ≤ 2 j^2 + 2 |n - j|^2` feeds the
input coordinates into `sum_linear_moment_sq_le_four_div_log`, gaining `1 / log N` over the
whole-space operator norm. -/
theorem norm_separatedCrossErrorMatrix_sq_le_of_mem_conductorSubspace {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ t, t ∉ Set.Icc 0 1 → φ t = 0)
    (hM_int : 0 < ∫ t, φ t ^ 2) {c : ℝ} (hc0 : 0 < c)
    {R N : ℕ} (hR : 2 ≤ R) (hRN4 : R ^ 4 ≤ N)
    (hlog : 18 * (1 + Real.log R) ≤ Real.log N)
    {u : EuclideanSpace ℝ (PrimeHorizonIndex N)} (hu : u ∈ conductorSubspace R N) :
    ‖Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) u‖ ^ 2 ≤
      520 * (152 * (∫ t, |φ t|) ^ 2 / (∫ t, φ t ^ 2)) ^ 2 *
        (c ^ 4 / Real.log N) * ‖u‖ ^ 2 := by
  let K₀ := 152 * (∫ t, |φ t|) ^ 2 / (∫ t, φ t ^ 2)
  have hK₀ : 0 ≤ K₀ := by dsimp only [K₀]; positivity
  have hN1 : 1 ≤ N := (pow_pos (by omega : 0 < R) 4).trans_le hRN4
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hL : 0 < Real.log N := by
    have hR0 := Real.log_natCast_nonneg R
    linarith only [hlog, hR0]
  let K : ℕ → ℕ → ℝ := fun n j =>
    if 2 * (c / N) < |Real.log j - Real.log n| then
      atomCrossErrorKernel (atomDilate φ (c / N)) n j else 0
  have hmax_sq : ∀ x y : ℝ, (max x y) ^ 2 ≤ 2 * y ^ 2 + 2 * |x - y| ^ 2 := by
    intro x y
    rw [sq_abs]
    rcases le_total x y with hxy | hyx
    · rw [max_eq_right hxy]
      nlinarith only [sq_nonneg (x - y), sq_nonneg y]
    · rw [max_eq_left hyx]
      nlinarith only [sq_nonneg (y - (x - y))]
  have hK_entry : ∀ n ∈ Icc 1 N, ∀ j ∈ Icc 1 N,
      |K n j| ≤ 2 * K₀ * c ^ 2 * (((j : ℝ) / N) ^ 2 / |(n : ℝ) - j| ^ 2) +
        2 * K₀ * (c / N) ^ 2 := by
    intro n hn j hj
    by_cases hnj : n = j
    · subst j
      have hnot : ¬(2 * (c / N) < |Real.log n - Real.log n|) := by
        rw [sub_self, abs_zero]; exact not_lt.mpr (by positivity)
      dsimp only [K]
      rw [if_neg hnot, abs_zero]
      positivity
    · have hd_ne : |(n : ℝ) - j| ≠ 0 :=
        abs_ne_zero.mpr (sub_ne_zero.mpr (by exact_mod_cast hnj))
      have hd0 : 0 < |(n : ℝ) - j| ^ 2 := sq_pos_of_ne_zero hd_ne
      have hb := abs_separatedCrossError_le hφ hsupp hM_int hc0 hN1 hn hj
      calc
        |K n j| ≤ (K₀ * (c / N) ^ 2) * (max (n : ℝ) j) ^ 2 / |(n : ℝ) - j| ^ 2 := hb
        _ ≤ (K₀ * (c / N) ^ 2) * (2 * (j : ℝ) ^ 2 + 2 * |(n : ℝ) - j| ^ 2) / |(n : ℝ) - j| ^ 2 :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hmax_sq n j) (by positivity)) hd0.le
        _ = 2 * K₀ * c ^ 2 * (((j : ℝ) / N) ^ 2 / |(n : ℝ) - j| ^ 2) +
              2 * K₀ * (c / N) ^ 2 := by
          field_simp [hN0.ne', hd_ne]
  let y : ℕ → ℝ := fun j => ((j : ℝ) / N) * |primeHorizonExtension u j|
  have hy_nonneg : ∀ j, 0 ≤ y j := fun j => by dsimp only [y]; positivity
  have hy_sq : (∑ j ∈ Icc 1 N, y j ^ 2) ≤ 4 / Real.log N * ‖u‖ ^ 2 := by
    have hpt : ∀ j ∈ Icc 1 N, y j ^ 2 ≤ ((j : ℝ) / N) * primeHorizonExtension u j ^ 2 := by
      intro j hj
      have hjN : (j : ℝ) / N ≤ 1 := (div_le_one hN0).mpr (by exact_mod_cast (mem_Icc.mp hj).2)
      have hj0 : 0 ≤ (j : ℝ) / N := by positivity
      dsimp only [y]
      rw [mul_pow, sq_abs]
      have hsq : ((j : ℝ) / N) ^ 2 ≤ (j : ℝ) / N := by nlinarith only [hjN, hj0]
      exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    have hm := sum_linear_moment_sq_le_four_div_log hR hRN4 hlog hu
    rw [div_mul_eq_mul_div, le_div_iff₀' hL]
    exact (mul_le_mul_of_nonneg_left (sum_le_sum hpt) hL.le).trans hm
  let U : ℕ → ℕ → ℝ := fun n j => 1 / |(n : ℝ) - j| ^ 2
  have hU_nonneg : ∀ n ∈ Icc 1 N, ∀ j ∈ Icc 1 N, 0 ≤ U n j :=
    fun _ _ _ _ => by dsimp only [U]; positivity
  have hU_row : ∀ n ∈ Icc 1 N, (∑ j ∈ Icc 1 N, U n j * 1) ≤ 4 := fun n _ => by
    simpa only [U, mul_one] using sum_inv_sq_integer_distance_le_four (Icc 1 N) n
  have hU_col : ∀ j ∈ Icc 1 N, (∑ n ∈ Icc 1 N, U n j * (4 / 1)) ≤ 16 := fun j hj => by
    have hsym : ∀ n ∈ Icc 1 N, U n j * (4 / 1) = 4 * (U j n * 1) := fun n _ => by
      dsimp only [U]; rw [abs_sub_comm]; ring
    rw [sum_congr rfl hsym, ← mul_sum]
    linarith only [hU_row j hj]
  have hschur := sum_sq_abs_majorized_kernel_le' U U y
    (fun _ => 1) (fun _ => 4) (fun _ => 16)
    hU_nonneg
    (fun n hn j hj => by rw [abs_of_nonneg (hU_nonneg n hn j hj)])
    (fun _ _ => zero_lt_one) hU_row hU_col
  have hpart1 :
      (∑ n ∈ Icc 1 N, (∑ j ∈ Icc 1 N, U n j * y j) ^ 2) ≤ 64 / Real.log N * ‖u‖ ^ 2 := by
    calc
      (∑ n ∈ Icc 1 N, (∑ j ∈ Icc 1 N, U n j * y j) ^ 2) ≤
          ∑ j ∈ Icc 1 N, 16 * y j ^ 2 := hschur
      _ = 16 * ∑ j ∈ Icc 1 N, y j ^ 2 := (mul_sum ..).symm
      _ ≤ 16 * (4 / Real.log N * ‖u‖ ^ 2) := mul_le_mul_of_nonneg_left hy_sq (by norm_num)
      _ = 64 / Real.log N * ‖u‖ ^ 2 := by ring
  have hpart2 : (∑ j ∈ Icc 1 N, |primeHorizonExtension u j|) ^ 2 ≤ (N : ℝ) * ‖u‖ ^ 2 := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Icc 1 N)
      (fun j => |primeHorizonExtension u j|) (fun _ => (1 : ℝ))
    simp only [mul_one, sq_abs, one_pow, sum_const, Nat.card_Icc, Nat.add_sub_cancel,
      nsmul_eq_mul, sum_primeHorizonExtension_sq] at hcs
    linarith only [hcs]
  have hrow_pt : ∀ n ∈ Icc 1 N,
      (∑ j ∈ Icc 1 N, K n j * primeHorizonExtension u j) ^ 2 ≤
        8 * K₀ ^ 2 * c ^ 4 * (∑ j ∈ Icc 1 N, U n j * y j) ^ 2 +
          8 * K₀ ^ 2 * (c / N) ^ 4 * (∑ j ∈ Icc 1 N, |primeHorizonExtension u j|) ^ 2 := by
    intro n hn
    have habs :
        |∑ j ∈ Icc 1 N, K n j * primeHorizonExtension u j| ≤
          2 * K₀ * c ^ 2 * (∑ j ∈ Icc 1 N, U n j * y j) +
            2 * K₀ * (c / N) ^ 2 * (∑ j ∈ Icc 1 N, |primeHorizonExtension u j|) := by
      calc
        |∑ j ∈ Icc 1 N, K n j * primeHorizonExtension u j| ≤
            ∑ j ∈ Icc 1 N, |K n j| * |primeHorizonExtension u j| := by
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
          rw [abs_mul]
        _ ≤ ∑ j ∈ Icc 1 N,
              (2 * K₀ * c ^ 2 * (((j : ℝ) / N) ^ 2 / |(n : ℝ) - j| ^ 2) +
                2 * K₀ * (c / N) ^ 2) * |primeHorizonExtension u j| :=
          sum_le_sum fun j hj =>
            mul_le_mul_of_nonneg_right (hK_entry n hn j hj) (abs_nonneg _)
        _ ≤ ∑ j ∈ Icc 1 N,
              (2 * K₀ * c ^ 2 * (U n j * y j) +
                2 * K₀ * (c / N) ^ 2 * |primeHorizonExtension u j|) := by
          refine sum_le_sum fun j hj => ?_
          have hjN : (j : ℝ) / N ≤ 1 :=
            (div_le_one hN0).mpr (by exact_mod_cast (mem_Icc.mp hj).2)
          have hj0 : 0 ≤ (j : ℝ) / N := by positivity
          have hsq : ((j : ℝ) / N) ^ 2 ≤ (j : ℝ) / N := by nlinarith only [hjN, hj0]
          have hle : (((j : ℝ) / N) ^ 2 / |(n : ℝ) - j| ^ 2) * |primeHorizonExtension u j| ≤
              U n j * y j := by
            dsimp only [U, y]
            calc
              (((j : ℝ) / N) ^ 2 / |(n : ℝ) - j| ^ 2) * |primeHorizonExtension u j| ≤
                  (((j : ℝ) / N) / |(n : ℝ) - j| ^ 2) * |primeHorizonExtension u j| :=
                mul_le_mul_of_nonneg_right
                  (div_le_div_of_nonneg_right hsq (sq_nonneg _)) (abs_nonneg _)
              _ = 1 / |(n : ℝ) - j| ^ 2 * (((j : ℝ) / N) * |primeHorizonExtension u j|) := by ring
          have hmul := mul_le_mul_of_nonneg_left hle (show 0 ≤ 2 * K₀ * c ^ 2 by positivity)
          linarith only [hmul, (by ring :
            (2 * K₀ * c ^ 2 * (((j : ℝ) / N) ^ 2 / |(n : ℝ) - j| ^ 2) +
              2 * K₀ * (c / N) ^ 2) * |primeHorizonExtension u j| =
            2 * K₀ * c ^ 2 * ((((j : ℝ) / N) ^ 2 / |(n : ℝ) - j| ^ 2) *
              |primeHorizonExtension u j|) +
            2 * K₀ * (c / N) ^ 2 * |primeHorizonExtension u j|)]
        _ = 2 * K₀ * c ^ 2 * (∑ j ∈ Icc 1 N, U n j * y j) +
              2 * K₀ * (c / N) ^ 2 * (∑ j ∈ Icc 1 N, |primeHorizonExtension u j|) := by
          rw [sum_add_distrib, ← mul_sum, ← mul_sum]
    have hsq := pow_le_pow_left₀ (abs_nonneg _) habs 2
    rw [sq_abs] at hsq
    let X := 2 * K₀ * c ^ 2 * (∑ j ∈ Icc 1 N, U n j * y j)
    let Y := 2 * K₀ * (c / N) ^ 2 * (∑ j ∈ Icc 1 N, |primeHorizonExtension u j|)
    have h2xy : (X + Y) ^ 2 ≤ 2 * X ^ 2 + 2 * Y ^ 2 := by
      nlinarith only [sq_nonneg (X - Y)]
    exact hsq.trans (h2xy.trans_eq (by dsimp only [X, Y]; ring))
  have hinv_N2 : 1 / (N : ℝ) ^ 2 ≤ 1 / Real.log N := by
    have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have hlog_le : Real.log N ≤ (N : ℝ) ^ 2 := by
      have h1 := Real.log_le_sub_one_of_pos hN0
      nlinarith only [h1, hN1R]
    exact one_div_le_one_div_of_le hL hlog_le
  change ‖Matrix.toEuclideanLin (horizonKernelMatrix K N) u‖ ^ 2 ≤ _
  rw [← horizonProfileVector_extension u, horizonKernelMatrix_profile_norm_sq,
    horizonProfileVector_extension]
  calc
    (∑ n ∈ Icc 1 N, (∑ j ∈ Icc 1 N, K n j * primeHorizonExtension u j) ^ 2) ≤
        ∑ n ∈ Icc 1 N,
          (8 * K₀ ^ 2 * c ^ 4 * (∑ j ∈ Icc 1 N, U n j * y j) ^ 2 +
            8 * K₀ ^ 2 * (c / N) ^ 4 * (∑ j ∈ Icc 1 N, |primeHorizonExtension u j|) ^ 2) :=
      sum_le_sum hrow_pt
    _ = 8 * K₀ ^ 2 * c ^ 4 * (∑ n ∈ Icc 1 N, (∑ j ∈ Icc 1 N, U n j * y j) ^ 2) +
          (N : ℝ) * (8 * K₀ ^ 2 * (c / N) ^ 4 *
            (∑ j ∈ Icc 1 N, |primeHorizonExtension u j|) ^ 2) := by
      rw [sum_add_distrib, ← mul_sum, sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    _ ≤ 8 * K₀ ^ 2 * c ^ 4 * (64 / Real.log N * ‖u‖ ^ 2) +
          (N : ℝ) * (8 * K₀ ^ 2 * (c / N) ^ 4 * ((N : ℝ) * ‖u‖ ^ 2)) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hpart1 (by positivity))
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hpart2 (by positivity)) (by positivity))
    _ = 512 * K₀ ^ 2 * (c ^ 4 / Real.log N) * ‖u‖ ^ 2 +
          8 * K₀ ^ 2 * c ^ 4 * (1 / (N : ℝ) ^ 2) * ‖u‖ ^ 2 := by
      field_simp [hN0.ne', hL.ne']; ring
    _ ≤ 512 * K₀ ^ 2 * (c ^ 4 / Real.log N) * ‖u‖ ^ 2 +
          8 * K₀ ^ 2 * c ^ 4 * (1 / Real.log N) * ‖u‖ ^ 2 :=
      add_le_add le_rfl
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hinv_N2 (by positivity)) (sq_nonneg _))
    _ = 520 * K₀ ^ 2 * (c ^ 4 / Real.log N) * ‖u‖ ^ 2 := by ring

private theorem downwardPrimeVector_packet_apply' (φ : ℝ → ℝ) {c : ℝ} (hc : 0 < c)
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {M N : ℕ} (hN : 1 ≤ N) (a : ℕ → ℝ) (n : PrimeHorizonIndex N) :
    downwardPrimeVector φ c N
        (∑ m ∈ Icc 1 M, a m • normalizedRamanujanHorizonVector m N) n =
      ∑ m ∈ Icc 1 M,
        a m * downwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N) n := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  obtain ⟨_, hgsupp, _⟩ := atomDilate_facts hφ hsupp hw
  let g := atomDilate φ (c / N)
  let G0 := ∫ u, g u ^ 2
  let K := lagRange (Real.log N + c / N + 1)
  let u := ∑ m ∈ Icc 1 M, a m • normalizedRamanujanHorizonVector m N
  change downwardPrimeRow g N (primeHorizonExtension u) n / G0 =
    ∑ m ∈ Icc 1 M, a m *
      (downwardPrimeRow g N (primeHorizonExtension (normalizedRamanujanHorizonVector m N)) n / G0)
  have hext : ∀ j ∈ Icc 1 N, primeHorizonExtension u j =
      ∑ m ∈ Icc 1 M, a m * primeHorizonExtension (normalizedRamanujanHorizonVector m N) j := by
    intro j hj
    rw [primeHorizonExtension_coe u ⟨j, hj⟩]
    change (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : PrimeHorizonIndex N => ℝ) ⟨j, hj⟩) u = _
    dsimp only [u]
    rw [map_sum]
    refine sum_congr rfl fun m _ => ?_
    rw [primeHorizonExtension_coe _ ⟨j, hj⟩]
    rfl
  simp_rw [← mul_div_assoc, ← sum_div]
  congr 1
  rw [downwardPrimeRow_eq_sum hgsupp hw.le n.property (primeHorizonExtension u)]
  have hterm : ∀ m ∈ Icc 1 M,
      a m * downwardPrimeRow g N (primeHorizonExtension (normalizedRamanujanHorizonVector m N)) n =
        ∑ k ∈ range K, _root_.RHTower.vonMangoldtAtom k *
          ∑ j ∈ Icc 1 N, a m * primeHorizonExtension (normalizedRamanujanHorizonVector m N) j *
            (if (n : ℕ) = k * j then 0 else bumpCorr g (Real.log k - (Real.log n - Real.log j))) := by
    intro m _
    rw [downwardPrimeRow_eq_sum hgsupp hw.le n.property, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [← mul_assoc, mul_comm (a m), mul_assoc, mul_sum]
    congr 1
    exact sum_congr rfl fun j _ => by dsimp only [g]; ring
  rw [sum_congr rfl hterm, sum_comm]
  refine sum_congr rfl fun k _ => ?_
  rw [← mul_sum]
  congr 1
  rw [sum_comm]
  refine sum_congr rfl fun j hj => ?_
  rw [hext j hj, sum_mul]

private theorem sum_exterior_packet_sq_le' {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {R N : ℕ} {c : ℝ}
    (hR : 2 ≤ R) (hRN : R * R ≤ N) (hlog : 18 * (1 + Real.log R) ≤ Real.log N)
    (hc1 : 1 ≤ c) (hw1 : c / N ≤ 1 / 3) (a : ℕ → ℝ) :
    (∑ n ∈ Icc 1 N,
      (∑ m ∈ Icc 1 R, a m * ((Real.sqrt (m.totient : ℝ))⁻¹ *
        (actualExteriorDownwardRow (atomDilate φ (c / N)) N m n / Real.sqrt (Real.log N)))) ^ 2) ≤
      (36 * (Real.exp 1 + 2) * (Real.exp 1 + 1) ^ 2) *
        c ^ 3 * (R : ℝ) ^ 2 * (Real.log N / N) *
        ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hw : c / N ≤ 1 := hw1.trans (by norm_num)
  have hN1 : 1 ≤ N := (Nat.mul_pos (by omega : 0 < R) (by omega : 0 < R)).trans_le hRN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hL1 : 1 ≤ Real.log N := by have := Real.log_natCast_nonneg R; linarith only [hlog, this]
  have hL0 : 0 < Real.log N := zero_lt_one.trans_le hL1
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hsL : 0 < Real.sqrt (Real.log N) := Real.sqrt_pos.mpr hL0
  obtain ⟨hg, hgsupp, _⟩ := atomDilate_facts hφ hsupp (div_pos hc0 hN0)
  let g := atomDilate φ (c / N)
  have hG : 0 < ∫ u, g u ^ 2 := by
    dsimp only [g]
    rw [integral_atomDilate_sq (div_pos hc0 hN0)]
    exact mul_pos (div_pos hc0 hN0) hM
  have hgc : HasCompactSupport g := HasCompactSupport.intro isCompact_Icc hgsupp
  have hmode_row : ∀ m ∈ Icc 1 R, ∀ n ∈ Icc 1 N,
      |(Real.sqrt (m.totient : ℝ))⁻¹ *
          (actualExteriorDownwardRow g N m n / Real.sqrt (Real.log N))| ≤
        3 * (Real.exp 1 + 1) * c * Real.sqrt R * Real.sqrt (Real.log N / N) := by
    intro m hm n hn
    obtain ⟨hm1, hmR⟩ := mem_Icc.mp hm
    rw [actualExteriorDownwardRow, downwardRamanujanRow_sub_interior_eq hc0 hn hgsupp m]
    have hterm : ∀ ℓ ∈ Ioc N (exteriorPrimeCutoff c N),
        |horizonRamanujanMangoldt m N ℓ / Real.sqrt ℓ *
            (bumpCorr g (Real.log ℓ - Real.log n) / (∫ u, g u ^ 2))| ≤
          3 * (m.totient : ℝ) * Real.log N / Real.sqrt N := by
      intro ℓ hℓ
      have hNℓ : (N : ℝ) ≤ ℓ := by exact_mod_cast (mem_Ioc.mp hℓ).1.le
      have hℓ0 : (0 : ℝ) < ℓ := hN0.trans_le hNℓ
      have hsℓ : Real.sqrt N ≤ Real.sqrt ℓ := Real.sqrt_le_sqrt hNℓ
      have hcorr : |bumpCorr g (Real.log ℓ - Real.log n) / (∫ u, g u ^ 2)| ≤ 1 := by
        rw [abs_div, abs_of_pos hG, div_le_one hG]
        exact abs_bumpCorr_le hg.continuous hgc _
      have hℓ_le : (ℓ : ℝ) ≤ 3 * N := by
        have hcut := (exteriorPrimeCutoff_bounds_small_width hc0 hN1 hw).2
        have hℓ_nat : ℓ ≤ N + linearPrimeStrip c := (mem_Ioc.mp hℓ).2.trans hcut
        have hB := linearPrimeStrip_le hc1
        have he1 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
        have hcN : 3 * c ≤ N := by
          have := (div_le_iff₀ hN0).mp hw1; linarith only [this]
        have hcast : (ℓ : ℝ) ≤ N + linearPrimeStrip c := by exact_mod_cast hℓ_nat
        nlinarith only [hcast, hB, he1, hcN, hc0]
      have hlogℓ : Real.log ℓ ≤ 3 * Real.log N := by
        have hlog3 : Real.log 3 ≤ 2 := by
          linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)]
        calc
          Real.log ℓ ≤ Real.log (3 * N) := Real.log_le_log hℓ0 hℓ_le
          _ = Real.log 3 + Real.log N := Real.log_mul (by norm_num) hN0.ne'
          _ ≤ 3 * Real.log N := by linarith only [hlog3, hL1]
      have hjet : |horizonRamanujanMangoldt m N ℓ / Real.sqrt ℓ| ≤
          3 * (m.totient : ℝ) * Real.log N / Real.sqrt N := by
        rw [abs_div, abs_of_pos (Real.sqrt_pos.mpr hℓ0)]
        calc
          |horizonRamanujanMangoldt m N ℓ| / Real.sqrt ℓ ≤
              (m.totient : ℝ) * Real.log ℓ / Real.sqrt ℓ :=
            div_le_div_of_nonneg_right (abs_horizonRamanujanMangoldt_le m N ℓ) (Real.sqrt_nonneg _)
          _ ≤ (m.totient : ℝ) * (3 * Real.log N) / Real.sqrt ℓ :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hlogℓ (Nat.cast_nonneg _)) (Real.sqrt_nonneg _)
          _ ≤ (m.totient : ℝ) * (3 * Real.log N) / Real.sqrt N :=
            div_le_div_of_nonneg_left (by positivity) hsN hsℓ
          _ = 3 * (m.totient : ℝ) * Real.log N / Real.sqrt N := by ring
      rw [abs_mul]
      simpa only [mul_one] using mul_le_mul hjet hcorr (abs_nonneg _) (by positivity)
    have hcard : ((Ioc N (exteriorPrimeCutoff c N)).card : ℝ) ≤ (Real.exp 1 + 1) * c := by
      have hbound := (exteriorPrimeCutoff_bounds_small_width hc0 hN1 hw).2
      have hc_strip : ((Ioc N (exteriorPrimeCutoff c N)).card : ℝ) ≤ linearPrimeStrip c := by
        rw [Nat.card_Ioc]
        exact_mod_cast (show exteriorPrimeCutoff c N - N ≤ linearPrimeStrip c by omega)
      exact hc_strip.trans (linearPrimeStrip_le hc1)
    have hreg : |regroupedExteriorDownwardPrimeRow g c N m n| ≤
        3 * (Real.exp 1 + 1) * c * (m.totient : ℝ) * Real.log N / Real.sqrt N := by
      unfold regroupedExteriorDownwardPrimeRow
      calc
        _ ≤ ∑ ℓ ∈ Ioc N (exteriorPrimeCutoff c N),
              |horizonRamanujanMangoldt m N ℓ / Real.sqrt ℓ *
                (bumpCorr g (Real.log ℓ - Real.log n) / (∫ u, g u ^ 2))| :=
          abs_sum_le_sum_abs _ _
        _ ≤ ∑ _ℓ ∈ Ioc N (exteriorPrimeCutoff c N),
              (3 * (m.totient : ℝ) * Real.log N / Real.sqrt N) := sum_le_sum hterm
        _ = ((Ioc N (exteriorPrimeCutoff c N)).card : ℝ) *
              (3 * (m.totient : ℝ) * Real.log N / Real.sqrt N) := by
          rw [sum_const, nsmul_eq_mul]
        _ ≤ ((Real.exp 1 + 1) * c) * (3 * (m.totient : ℝ) * Real.log N / Real.sqrt N) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = 3 * (Real.exp 1 + 1) * c * (m.totient : ℝ) * Real.log N / Real.sqrt N := by ring
    have hsφm : 0 < Real.sqrt (m.totient : ℝ) :=
      Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr hm1)
    have hsφR : Real.sqrt (m.totient : ℝ) ≤ Real.sqrt R :=
      Real.sqrt_le_sqrt (by exact_mod_cast (Nat.totient_le m).trans hmR)
    rw [abs_mul, abs_inv, abs_of_pos hsφm, abs_div, abs_of_pos hsL]
    calc
      (Real.sqrt (m.totient : ℝ))⁻¹ * (|regroupedExteriorDownwardPrimeRow g c N m n| /
          Real.sqrt (Real.log N)) ≤
          (Real.sqrt (m.totient : ℝ))⁻¹ *
            ((3 * (Real.exp 1 + 1) * c * (m.totient : ℝ) * Real.log N / Real.sqrt N) /
              Real.sqrt (Real.log N)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hreg hsL.le) (by positivity)
      _ = 3 * (Real.exp 1 + 1) * c * Real.sqrt (m.totient : ℝ) *
            (Real.sqrt (Real.log N) / Real.sqrt N) := by
        calc
          (Real.sqrt (m.totient : ℝ))⁻¹ *
              ((3 * (Real.exp 1 + 1) * c * (m.totient : ℝ) * Real.log N / Real.sqrt N) /
                Real.sqrt (Real.log N)) =
              (Real.sqrt (m.totient : ℝ))⁻¹ *
                ((3 * (Real.exp 1 + 1) * c * (Real.sqrt (m.totient : ℝ) ^ 2) *
                  (Real.sqrt (Real.log N) ^ 2) / Real.sqrt N) / Real.sqrt (Real.log N)) := by
            rw [Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt hL0.le]
          _ = 3 * (Real.exp 1 + 1) * c * Real.sqrt (m.totient : ℝ) *
                (Real.sqrt (Real.log N) / Real.sqrt N) := by
            field_simp [hsφm.ne', hsL.ne', hsN.ne']
      _ ≤ 3 * (Real.exp 1 + 1) * c * Real.sqrt R * Real.sqrt (Real.log N / N) := by
        rw [Real.sqrt_div hL0.le]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsφR (by positivity)) (by positivity)
  let S_ext := (Icc 1 N).filter (fun n => N - linearPrimeStrip c ≤ n)
  have hrestrict :
      (∑ n ∈ Icc 1 N,
        (∑ m ∈ Icc 1 R, a m * ((Real.sqrt (m.totient : ℝ))⁻¹ *
          (actualExteriorDownwardRow g N m n / Real.sqrt (Real.log N)))) ^ 2) =
      ∑ n ∈ S_ext,
        (∑ m ∈ Icc 1 R, a m * ((Real.sqrt (m.totient : ℝ))⁻¹ *
          (actualExteriorDownwardRow g N m n / Real.sqrt (Real.log N)))) ^ 2 := by
    symm
    refine sum_subset (filter_subset _ _) fun n hn hnS => ?_
    have hout : n < N - linearPrimeStrip c :=
      lt_of_not_ge fun h => hnS (mem_filter.mpr ⟨hn, h⟩)
    have hzero : ∀ m ∈ Icc 1 R, actualExteriorDownwardRow g N m n = 0 := fun m _ => by
      rw [actualExteriorDownwardRow, downwardRamanujanRow_sub_interior_eq hc0 hn hgsupp m]
      exact regroupedExteriorDownwardPrimeRow_eq_zero_small_width hc0 hn hgsupp hw hout m
    rw [sum_eq_zero fun m hm => by rw [hzero m hm]; ring, sq, mul_zero]
  have hsum_abs_a_sq : (∑ m ∈ Icc 1 R, |a m|) ^ 2 ≤
      2 * (R : ℝ) * ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Icc 1 R) (fun m => |a m|) (fun _ => (1 : ℝ))
    simp only [mul_one, sq_abs, one_pow, sum_const, Nat.card_Icc, Nat.add_sub_cancel,
      nsmul_eq_mul] at hcs
    have hriesz := (half_and_three_halves_riesz_of_log_le hR hRN hlog a).1
    nlinarith only [hcs, hriesz, Nat.cast_nonneg (α := ℝ) R]
  have hpt_S : ∀ n ∈ S_ext,
      (∑ m ∈ Icc 1 R, a m * ((Real.sqrt (m.totient : ℝ))⁻¹ *
        (actualExteriorDownwardRow g N m n / Real.sqrt (Real.log N)))) ^ 2 ≤
        18 * (Real.exp 1 + 1) ^ 2 * c ^ 2 * (R : ℝ) ^ 2 * (Real.log N / N) *
          ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by
    intro n hnS
    have hn := (mem_filter.mp hnS).1
    let M_ext := 3 * (Real.exp 1 + 1) * c * Real.sqrt R * Real.sqrt (Real.log N / N)
    have habs :
        |∑ m ∈ Icc 1 R, a m * ((Real.sqrt (m.totient : ℝ))⁻¹ *
            (actualExteriorDownwardRow g N m n / Real.sqrt (Real.log N)))| ≤
          M_ext * ∑ m ∈ Icc 1 R, |a m| := by
      calc
        _ ≤ ∑ m ∈ Icc 1 R, |a m| * |(Real.sqrt (m.totient : ℝ))⁻¹ *
              (actualExteriorDownwardRow g N m n / Real.sqrt (Real.log N))| := by
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun m _ => ?_)
          rw [abs_mul]
        _ ≤ ∑ m ∈ Icc 1 R, |a m| * M_ext :=
          sum_le_sum fun m hm => mul_le_mul_of_nonneg_left (hmode_row m hm n hn) (abs_nonneg _)
        _ = M_ext * ∑ m ∈ Icc 1 R, |a m| := by rw [← sum_mul, mul_comm]
    have hsq := pow_le_pow_left₀ (abs_nonneg _) habs 2
    rw [sq_abs, mul_pow] at hsq
    have hM_sq : M_ext ^ 2 =
        9 * (Real.exp 1 + 1) ^ 2 * c ^ 2 * (R : ℝ) * (Real.log N / N) := by
      dsimp only [M_ext]
      rw [mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg R),
        Real.sq_sqrt (by positivity)]
      ring
    calc
      _ ≤ M_ext ^ 2 * (∑ m ∈ Icc 1 R, |a m|) ^ 2 := hsq
      _ ≤ M_ext ^ 2 * (2 * (R : ℝ) *
            ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hsum_abs_a_sq (sq_nonneg _)
      _ = 18 * (Real.exp 1 + 1) ^ 2 * c ^ 2 * (R : ℝ) ^ 2 * (Real.log N / N) *
            ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by
        rw [hM_sq]; ring
  have hcard_S : (S_ext.card : ℝ) ≤ 2 * (Real.exp 1 + 2) * c := by
    have hcontain : S_ext ⊆ Icc (N - linearPrimeStrip c) N := fun n hn =>
      mem_Icc.mpr ⟨(mem_filter.mp hn).2, (mem_Icc.mp (mem_filter.mp hn).1).2⟩
    have hnat : S_ext.card ≤ linearPrimeStrip c + 1 := by
      have h := card_le_card hcontain; rw [Nat.card_Icc] at h; omega
    have hcast : (S_ext.card : ℝ) ≤ (linearPrimeStrip c : ℝ) + 1 := by exact_mod_cast hnat
    have hB := linearPrimeStrip_le hc1
    nlinarith only [hcast, hB, hc1, Real.exp_pos 1]
  rw [hrestrict]
  calc
    _ ≤ ∑ _n ∈ S_ext,
          (18 * (Real.exp 1 + 1) ^ 2 * c ^ 2 * (R : ℝ) ^ 2 * (Real.log N / N) *
            ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2) :=
      sum_le_sum hpt_S
    _ = (S_ext.card : ℝ) *
          (18 * (Real.exp 1 + 1) ^ 2 * c ^ 2 * (R : ℝ) ^ 2 * (Real.log N / N) *
            ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2) := by
      rw [sum_const, nsmul_eq_mul]
    _ ≤ (2 * (Real.exp 1 + 2) * c) *
          (18 * (Real.exp 1 + 1) ^ 2 * c ^ 2 * (R : ℝ) ^ 2 * (Real.log N / N) *
            ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hcard_S (by positivity)
    _ = (36 * (Real.exp 1 + 2) * (Real.exp 1 + 1) ^ 2) *
          c ^ 3 * (R : ℝ) ^ 2 * (Real.log N / N) *
          ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by ring

private def nearDivisorJetKernelMatrix (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) :
    Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ := fun n j =>
  if (j : ℕ) ∈ nearRowIndices c N (n : ℕ) then
    shellAutocorr φ (|Real.log (j : ℕ) - Real.log (n : ℕ)| / (c / N)) / (∫ t, φ t ^ 2)
  else 0

private theorem nearDivisorJetKernelMatrix_row (φ : ℝ → ℝ) (c : ℝ) (N : ℕ)
    (v : EuclideanSpace ℝ (PrimeHorizonIndex N)) (n : ℕ) (hn : n ∈ Icc 1 N) :
    primeHorizonExtension (Matrix.toEuclideanLin (nearDivisorJetKernelMatrix φ c N) v) n =
      ∑ j ∈ nearRowIndices c N n,
        (shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ t, φ t ^ 2)) *
          primeHorizonExtension v j := by
  rw [primeHorizonExtension_coe _ ⟨n, hn⟩]
  change (∑ j : PrimeHorizonIndex N, nearDivisorJetKernelMatrix φ c N ⟨n, hn⟩ j * v.ofLp j) = _
  rw [nearRowIndices, sum_filter, ← sum_coe_sort (Icc 1 N)]
  refine sum_congr rfl fun j _ => ?_
  rw [primeHorizonExtension_coe v j]
  dsimp only [nearDivisorJetKernelMatrix, nearRowIndices]
  by_cases h : (j : ℕ) ∈ (Icc 1 N).filter
      (fun j => j ≠ n ∧ |Real.log (j : ℕ) - Real.log (n : ℕ)| ≤ 2 * c / N)
  · have hcond := (mem_filter.mp h).2
    rw [if_pos h, if_pos hcond]
  · have hnot : ¬((j : ℕ) ≠ n ∧ |Real.log (j : ℕ) - Real.log (n : ℕ)| ≤ 2 * c / N) :=
      fun hc => h (mem_filter.mpr ⟨j.2, hc⟩)
    rw [if_neg h, if_neg hnot, zero_mul]

private theorem divisorJetHorizonVector_eq_sum_single (R N : ℕ) (a : ℕ → ℝ) :
    divisorJetHorizonVector R N a =
      ∑ m ∈ Icc 1 R, a m • divisorJetHorizonVector R N (fun k => if k = m then 1 else 0) := by
  ext n
  have hproj :
      (∑ m ∈ Icc 1 R, a m • divisorJetHorizonVector R N (fun k => if k = m then 1 else 0)) n =
        ∑ m ∈ Icc 1 R, a m * divisorJetHorizonVector R N (fun k => if k = m then 1 else 0) n := by
    change (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : PrimeHorizonIndex N => ℝ) n) _ = _
    rw [map_sum]
    exact sum_congr rfl fun m _ => rfl
  rw [divisorJetHorizonVector_apply, hproj]
  have hsingle : ∀ m ∈ Icc 1 R,
      divisorJetHorizonVector R N (fun k => if k = m then 1 else 0) n =
        (Real.sqrt (Real.log N))⁻¹ * poleVector n *
          (ramanujanLogDivisorJet m n / Real.sqrt (m.totient : ℝ)) := by
    intro m hm
    rw [divisorJetHorizonVector_apply]
    congr 1
    have hite :
        (∑ k ∈ Icc 1 R, (if k = m then (1 : ℝ) else 0) *
          (ramanujanLogDivisorJet k n / Real.sqrt (k.totient : ℝ))) =
        ∑ k ∈ Icc 1 R, if k = m then
          ramanujanLogDivisorJet k n / Real.sqrt (k.totient : ℝ) else 0 :=
      sum_congr rfl fun k _ => by split_ifs <;> ring
    rw [hite, sum_ite_eq', if_pos hm]
  rw [mul_sum]
  refine sum_congr rfl fun m hm => ?_
  rw [hsingle m hm]
  ring

/-- **Unmerged `overlap - downward` squared-norm bound (`c^2` on `G`, `c^4` on `‖u‖^2`).**
Separating the `O(1)` divisor-jet near kernel `K2b` from the `O(c)` kernels `K1, K2a` and
interpolating `K2b` over dyadic conductor prefixes via `linear_packet_sq_le_weighted_of_prefix_bound`
reduces the `(1 + log R) * G` coefficient from `c^4` to `c^2`. -/
theorem exists_overlap_sub_downward_sq_le_c9_split {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ t, t ∉ Set.Icc 0 1 → φ t = 0)
    (hM : 0 < ∫ t, φ t ^ 2) :
    ∃ C_near : ℝ, 0 < C_near ∧
      ∀ {R N : ℕ} {c : ℝ},
        2 ≤ R → R * R ≤ N → 18 * (1 + Real.log R) ≤ Real.log N →
        1 ≤ c → c / N ≤ 1 / 3 →
        ((R * R : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N →
      ∀ a : ℕ → ℝ,
        let u := ∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N
        ‖Matrix.toEuclideanLin (overlapMatrix φ c N) u - downwardPrimeVector φ c N u‖ ^ 2 ≤
          C_near * (c ^ 2 * (1 + Real.log R) * ((1 + Real.log c) / Real.log N) *
              (∑ m ∈ Icc 1 R, (1 + Real.log m) * a m ^ 2) +
            (c ^ 4 * (1 + Real.log c) / Real.log N +
              c ^ 3 * (R : ℝ) ^ 2 * (Real.log N / N)) * ‖u‖ ^ 2) := by
  obtain ⟨K_pair, hK_pair0, hpair⟩ := exists_abs_atomArchPair_near_sub_le hφ hsupp hM
  obtain ⟨C_jet, hC_jet_pos, hC_jet⟩ := exists_divisorJetHorizonVector_norm_le
  let M_nc : ℝ := 1 + Real.exp (1 / 2)
  let M_2a : ℝ := K_pair + 2 * Real.exp 2 + 1
  let K_nb : ℝ := 80 * (2 * Real.exp 2) ^ 2
  let K_ext : ℝ := 36 * (Real.exp 1 + 2) * (Real.exp 1 + 1) ^ 2
  let C_near : ℝ := 4 * (32 * K_nb * C_jet ^ 2 + K_nb * (M_nc ^ 2 + M_2a ^ 2) + K_ext + 1)
  refine ⟨C_near, by dsimp only [C_near, K_nb, K_ext, M_nc, M_2a]; positivity, ?_⟩
  intro R N c hR hRN hlog hc1 hw1 hRNT a
  dsimp only
  let u := ∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N
  have hu : u ∈ conductorSubspace R N := sum_normalizedRamanujanHorizonVector_mem_conductorSubspace R N a
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hw : c / N ≤ 1 := hw1.trans (by norm_num)
  have hN1 : 1 ≤ N := (Nat.mul_pos (by omega : 0 < R) (by omega : 0 < R)).trans_le hRN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hcN2 : 2 * c ≤ N := by have := (div_le_iff₀ hN0).mp hw1; linarith only [this, hc0]
  have hL : 0 < Real.log N := by have := Real.log_natCast_nonneg R; linarith only [hlog, this]
  have hlc0 : 0 ≤ Real.log c := Real.log_nonneg hc1
  let g := atomDilate φ (c / N)
  let G0 := ∫ t, g t ^ 2
  let K1 : ℕ → ℕ → ℝ := fun n j =>
    completeWeilPoleShift φ c / N * archimedeanCenterKernel n j
  let K2a : ℕ → ℕ → ℝ := fun n j =>
    atomArchPair g n j / G0 -
      Real.log j * (shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ t, φ t ^ 2))
  let K2b : ℕ → ℕ → ℝ := fun n j =>
    shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ t, φ t ^ 2)
  let vJet := divisorJetHorizonVector R N a
  have hu_ext : ∀ j ∈ Icc 1 N, primeHorizonExtension u j =
      (Real.sqrt (Real.log N))⁻¹ *
        ∑ m ∈ Icc 1 R, a m * (normalizedRamanujanMode m j / Real.sqrt j) := by
    intro j hj
    rw [primeHorizonExtension_coe u ⟨j, hj⟩]
    change (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : PrimeHorizonIndex N => ℝ) ⟨j, hj⟩) u = _
    dsimp only [u]
    rw [map_sum, mul_sum]
    exact sum_congr rfl fun m _ => by
      change a m * ((Real.sqrt (Real.log N))⁻¹ * (normalizedRamanujanMode m j / Real.sqrt j)) = _
      ring
  have hvJet_ext : ∀ j ∈ Icc 1 N, primeHorizonExtension vJet j =
      (Real.sqrt (Real.log N))⁻¹ *
        ∑ m ∈ Icc 1 R, a m * (ramanujanLogDivisorJet m j /
          (Real.sqrt (m.totient : ℝ) * Real.sqrt j)) := by
    intro j hj
    rw [primeHorizonExtension_coe vJet ⟨j, hj⟩, divisorJetHorizonVector_apply R N a ⟨j, hj⟩]
    simp only [poleVector]
    rw [mul_assoc, mul_sum]
    congr 1
    exact sum_congr rfl fun m _ => by ring
  have hrow_decomp : ∀ n ∈ Icc 1 N,
      primeHorizonExtension
          (Matrix.toEuclideanLin (overlapMatrix φ c N) u - downwardPrimeVector φ c N u) n =
        (∑ j ∈ nearRowIndices c N n, K1 n j * primeHorizonExtension u j) +
        (∑ j ∈ nearRowIndices c N n, K2a n j * primeHorizonExtension u j) +
        (∑ j ∈ nearRowIndices c N n, K2b n j * primeHorizonExtension vJet j) -
        ∑ m ∈ Icc 1 R, a m * ((Real.sqrt (m.totient : ℝ))⁻¹ *
          (actualExteriorDownwardRow g N m n / Real.sqrt (Real.log N))) := by
    intro n hn
    rw [primeHorizonExtension_coe _ ⟨n, hn⟩]
    change (Matrix.toEuclideanLin (overlapMatrix φ c N) u) ⟨n, hn⟩ -
      downwardPrimeVector φ c N u ⟨n, hn⟩ = _
    have hov_sum : (Matrix.toEuclideanLin (overlapMatrix φ c N) u) ⟨n, hn⟩ =
        ∑ m ∈ Icc 1 R, a m *
          (Matrix.toEuclideanLin (overlapMatrix φ c N)
            (normalizedRamanujanHorizonVector m N)) ⟨n, hn⟩ := by
      change (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : PrimeHorizonIndex N => ℝ) ⟨n, hn⟩)
        (Matrix.toEuclideanLin (overlapMatrix φ c N) u) = _
      dsimp only [u]
      rw [map_sum, map_sum]
      exact sum_congr rfl fun m _ => by rw [map_smul, map_smul]; rfl
    have hdown_sum : downwardPrimeVector φ c N u ⟨n, hn⟩ =
        ∑ m ∈ Icc 1 R, a m *
          downwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N) ⟨n, hn⟩ :=
      downwardPrimeVector_packet_apply' φ hc0 hφ hsupp hN1 a ⟨n, hn⟩
    rw [hov_sum, hdown_sum, ← sum_sub_distrib]
    have hmode : ∀ m ∈ Icc 1 R,
        a m * (Matrix.toEuclideanLin (overlapMatrix φ c N)
            (normalizedRamanujanHorizonVector m N) ⟨n, hn⟩ -
          downwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N) ⟨n, hn⟩) =
        a m * nearCenterVector φ c N m ⟨n, hn⟩ +
          a m * ((Real.sqrt (m.totient : ℝ))⁻¹ *
            (nearGammaDownwardRow φ c N m n / Real.sqrt (Real.log N))) -
          a m * ((Real.sqrt (m.totient : ℝ))⁻¹ *
            (actualExteriorDownwardRow g N m n / Real.sqrt (Real.log N))) := by
      intro m hm
      have hm0 : 0 < m := (mem_Icc.mp hm).1
      rw [overlapMatrix_ramanujan_row_eq φ c hm0 ⟨n, hn⟩]
      have hfull := congrArg (fun v : EuclideanSpace ℝ (PrimeHorizonIndex N) => v ⟨n, hn⟩)
        (normalizedFullNearGammaDownwardVector_eq_sub hφ hsupp hc0 N m)
      change normalizedFullNearGammaDownwardVector φ c N m ⟨n, hn⟩ =
        nearGammaDownwardRow φ c N m n / Real.sqrt (Real.log N) -
          actualExteriorDownwardRow g N m n / Real.sqrt (Real.log N) at hfull
      rw [hfull]
      ring
    rw [sum_congr rfl fun m hm => by rw [← mul_sub, hmode m hm], sum_sub_distrib, sum_add_distrib]
    have hnc_sum : (∑ m ∈ Icc 1 R, a m * nearCenterVector φ c N m ⟨n, hn⟩) =
        ∑ j ∈ nearRowIndices c N n, K1 n j * primeHorizonExtension u j := by
      have h1 : ∀ m ∈ Icc 1 R, a m * nearCenterVector φ c N m ⟨n, hn⟩ =
          ∑ j ∈ nearRowIndices c N n,
            K1 n j * ((Real.sqrt (Real.log N))⁻¹ *
              (a m * (normalizedRamanujanMode m j / Real.sqrt j))) := by
        intro m _
        change a m * ((∑ j ∈ nearRowIndices c N n,
          K1 n j * normalizedRamanujanMode m j / Real.sqrt j) / Real.sqrt (Real.log N)) = _
        rw [sum_div, mul_sum]
        exact sum_congr rfl fun j _ => by ring
      rw [sum_congr rfl h1, sum_comm]
      refine sum_congr rfl fun j hj => ?_
      rw [← mul_sum, ← mul_sum, hu_ext j (mem_filter.mp hj).1]
    have hng_sum :
        (∑ m ∈ Icc 1 R, a m * ((Real.sqrt (m.totient : ℝ))⁻¹ *
          (nearGammaDownwardRow φ c N m n / Real.sqrt (Real.log N)))) =
        (∑ j ∈ nearRowIndices c N n, K2a n j * primeHorizonExtension u j) +
        (∑ j ∈ nearRowIndices c N n, K2b n j * primeHorizonExtension vJet j) := by
      have hcoeff : ∀ m ∈ Icc 1 R, ∀ j ∈ nearRowIndices c N n,
          a m * ((Real.sqrt (m.totient : ℝ))⁻¹ *
            (nearGammaDownwardCoefficient φ c N m n j / Real.sqrt j / Real.sqrt (Real.log N))) =
          K2a n j * ((Real.sqrt (Real.log N))⁻¹ *
              (a m * (normalizedRamanujanMode m j / Real.sqrt j))) +
            K2b n j * ((Real.sqrt (Real.log N))⁻¹ *
              (a m * (ramanujanLogDivisorJet m j / (Real.sqrt (m.totient : ℝ) * Real.sqrt j)))) := by
        intro m hm j hj
        have hm0 : 0 < m := (mem_Icc.mp hm).1
        have hj1 : 1 ≤ j := (mem_Icc.mp (mem_filter.mp hj).1).1
        rw [nearGammaDownwardCoefficient, sum_vonMangoldt_mul_ramanujan_eq_log_sub_jet m hj1,
          normalizedRamanujanMode_eq_coefficient hm0]
        dsimp only [K2a, K2b, g, G0]
        ring
      have hm_eq : ∀ m ∈ Icc 1 R,
          a m * ((Real.sqrt (m.totient : ℝ))⁻¹ *
            (nearGammaDownwardRow φ c N m n / Real.sqrt (Real.log N))) =
          ∑ j ∈ nearRowIndices c N n,
            (K2a n j * ((Real.sqrt (Real.log N))⁻¹ *
                (a m * (normalizedRamanujanMode m j / Real.sqrt j))) +
              K2b n j * ((Real.sqrt (Real.log N))⁻¹ *
                (a m * (ramanujanLogDivisorJet m j /
                  (Real.sqrt (m.totient : ℝ) * Real.sqrt j))))) := by
        intro m hm
        unfold nearGammaDownwardRow
        rw [sum_div, mul_sum, mul_sum]
        exact sum_congr rfl fun j hj => by simpa only [mul_assoc] using hcoeff m hm j hj
      rw [sum_congr rfl hm_eq, sum_comm, ← sum_add_distrib]
      refine sum_congr rfl fun j hj => ?_
      have hjI := (mem_filter.mp hj).1
      rw [sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum, ← mul_sum,
        hu_ext j hjI, hvJet_ext j hjI]
    rw [hnc_sum, hng_sum, add_assoc]
  have hK1_le : ∀ n ∈ Icc 1 N, ∀ j ∈ nearRowIndices c N n, |K1 n j| ≤ M_nc * c := by
    intro n hn j hj
    have h1 := abs_nearCenter_entry_le (φ := φ) (m := 1) zero_lt_one hN1 hcN2 hn hj
    have hm1 : ∀ k, normalizedRamanujanMode 1 k = 1 := fun k => by
      rw [normalizedRamanujanMode, ramanujanMode_one, Nat.totient_one, Nat.cast_one,
        Real.sqrt_one, div_one]
    rw [hm1 j, mul_one, range_one, sum_singleton, hm1 0, abs_one, mul_one,
      abs_of_nonneg (completeWeilPoleShift_nonneg φ hc0.le)] at h1
    have hpole := completeWeilPoleShift_le hφ.continuous hsupp hM hc0.le
    exact h1.trans (by
      dsimp only [M_nc]
      simpa only [mul_comm c] using mul_le_mul_of_nonneg_right hpole (by positivity))
  have hK2a_le : ∀ n ∈ Icc 1 N, ∀ j ∈ nearRowIndices c N n, |K2a n j| ≤ M_2a * c := by
    intro n hn j hj
    have hjN := (mem_filter.mp hj).1
    have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hjN).1
    have hw0 : 0 < c / N := div_pos hc0 hN0
    have hs : |Real.log j - Real.log n| ≤ 2 * (c / N) := by
      simpa only [mul_div_assoc] using (mem_filter.mp hj).2.2
    have hrem : |atomArchPair g n j / G0 - Real.log (1 / (c / N)) * K2b n j| ≤ K_pair := by
      simpa only [g, G0, K2b, mul_div_assoc] using hpair (c / N) hw0 hw1 n j hs
    have hq : |K2b n j| ≤ 1 := by
      dsimp only [K2b]
      rw [abs_div, abs_of_pos hM, div_le_one hM]
      exact abs_bumpCorr_le hφ.continuous (hasCompactSupport_profile hsupp) _
    have hquot : (N : ℝ) / j ≤ linearNearRowRadius c :=
      (div_le_iff₀ hj0).mpr (nearRow_geometry_small_width hc0 hn hj hw).2.2
    have hloglow : 0 ≤ Real.log N - Real.log j :=
      sub_nonneg.mpr (Real.log_le_log hj0 (by exact_mod_cast (mem_Icc.mp hjN).2))
    have hloghigh : Real.log N - Real.log j ≤ linearNearRowRadius c := by
      have h := Real.log_le_sub_one_of_pos (div_pos hN0 hj0)
      rw [Real.log_div hN0.ne' hj0.ne'] at h
      linarith only [h, hquot]
    have hlogc_abs : |Real.log c| ≤ c := by
      rw [abs_of_nonneg hlc0]
      linarith [Real.log_le_sub_one_of_pos hc0]
    have hlogeq : Real.log (1 / (c / N)) - Real.log j = (Real.log N - Real.log j) - Real.log c := by
      rw [one_div, Real.log_inv, Real.log_div hc0.ne' hN0.ne']; ring
    have hlog_diff : |Real.log (1 / (c / N)) - Real.log j| ≤ linearNearRowRadius c + c := by
      rw [hlogeq]
      exact (abs_sub _ _).trans (by rw [abs_of_nonneg hloglow]; linarith only [hloghigh, hlogc_abs])
    have hid : K2a n j = (atomArchPair g n j / G0 - Real.log (1 / (c / N)) * K2b n j) +
        (Real.log (1 / (c / N)) - Real.log j) * K2b n j := by
      dsimp only [K2a]; ring
    rw [hid]
    calc
      _ ≤ |atomArchPair g n j / G0 - Real.log (1 / (c / N)) * K2b n j| +
            |(Real.log (1 / (c / N)) - Real.log j) * K2b n j| := abs_add_le _ _
      _ ≤ K_pair + (linearNearRowRadius c + c) * 1 := by
        rw [abs_mul]
        exact add_le_add hrem (mul_le_mul hlog_diff hq (abs_nonneg _)
          (by unfold linearNearRowRadius; positivity))
      _ ≤ M_2a * c := by
        dsimp only [M_2a, linearNearRowRadius]
        nlinarith only [hc1, hK_pair0]
  have hK2b_le : ∀ n ∈ Icc 1 N, ∀ j ∈ nearRowIndices c N n, |K2b n j| ≤ 1 := by
    intro _ _ _ _
    dsimp only [K2b]
    rw [abs_div, abs_of_pos hM, div_le_one hM]
    exact abs_bumpCorr_le hφ.continuous (hasCompactSupport_profile hsupp) _
  have hsq1 := sum_nearBand_sq_le_of_mem_conductorSubspace hR hlog hc1 hw
    (by dsimp only [M_nc]; positivity) hRNT K1 hK1_le hu
  have hsq2a := sum_nearBand_sq_le_of_mem_conductorSubspace hR hlog hc1 hw
    (by dsimp only [M_2a]; positivity) hRNT K2a hK2a_le hu
  have hsq3 := sum_exterior_packet_sq_le' hφ hsupp hM hR hRN hlog hc1 hw1 a
  -- Interpolate the `K2b` divisor-jet near term over dyadic conductor prefixes.
  let A_2b := Matrix.toEuclideanLin (nearDivisorJetKernelMatrix φ c N)
  let f : (↥(Icc 1 R) → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (PrimeHorizonIndex N) :=
    { toFun := fun b =>
        ∑ i : ↥(Icc 1 R),
          b i • A_2b (divisorJetHorizonVector R N (fun k => if k = (i : ℕ) then 1 else 0))
      map_add' := fun b d => by simp only [Pi.add_apply, add_smul, sum_add_distrib]
      map_smul' := fun s b => by
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, smul_sum, RingHom.id_apply] }
  let w_log : ↥(Icc 1 R) → ℝ := fun i => 1 + Real.log (i : ℕ)
  have hw_log : ∀ i, 1 ≤ w_log i := fun i => by
    dsimp only [w_log]; linarith only [Real.log_natCast_nonneg (i : ℕ)]
  let C_0 := Real.sqrt K_nb * C_jet * c * Real.sqrt ((1 + Real.log c) / Real.log N)
  have hprefix : ∀ t : ℝ, 1 ≤ t → ∀ b : ↥(Icc 1 R) → ℝ,
      (∀ i, t < w_log i → b i = 0) →
      ‖f b‖ ^ 2 ≤ (2 * C_0) ^ 2 * t ^ 2 * ∑ i, b i ^ 2 := by
    intro t ht b hb
    let b' : ℕ → ℝ := fun m => if hm : m ∈ Icc 1 R then b ⟨m, hm⟩ else 0
    have hb' (m : ℕ) (hm : m ∈ Icc 1 R) : b' m = b ⟨m, hm⟩ := dif_pos hm
    have hmap : f b = A_2b (divisorJetHorizonVector R N b') := by
      rw [divisorJetHorizonVector_eq_sum_single R N b', map_sum]
      simp only [map_smul]
      change (∑ i : ↥(Icc 1 R),
          b i • A_2b (divisorJetHorizonVector R N (fun k => if k = (i : ℕ) then 1 else 0))) =
        ∑ m ∈ Icc 1 R,
          b' m • A_2b (divisorJetHorizonVector R N (fun k => if k = m then 1 else 0))
      rw [← sum_coe_sort (Icc 1 R) (fun m =>
        b' m • A_2b (divisorJetHorizonVector R N (fun k => if k = m then 1 else 0)))]
      exact sum_congr rfl fun i _ => by rw [hb' (i : ℕ) i.property]
    have hmass : (∑ m ∈ Icc 1 R, b' m ^ 2) = ∑ i, b i ^ 2 := by
      rw [← sum_coe_sort (Icc 1 R) (fun m => b' m ^ 2)]
      exact sum_congr rfl fun i _ => by rw [hb' i i.property]
    let S := (Icc 1 R).filter (fun m => b' m ≠ 0)
    by_cases hS : S.Nonempty
    · let M := max 2 (S.max' hS)
      have hM2 : 2 ≤ M := le_max_left _ _
      have htop : S.max' hS ∈ Icc 1 R := (mem_filter.mp (S.max'_mem hS)).1
      have hMR : M ≤ R := max_le hR (mem_Icc.mp htop).2
      have hzero (m : ℕ) (hm : m ∈ Icc 1 R) (hmM : m ∉ Icc 1 M) : b' m = 0 := by
        by_contra hz
        have hs : m ∈ S := mem_filter.mpr ⟨hm, hz⟩
        have hle : m ≤ M := (Finset.le_max' S m hs).trans (le_max_right _ _)
        exact hmM (mem_Icc.mpr ⟨(mem_Icc.mp hm).1, hle⟩)
      have hjet_eq : divisorJetHorizonVector R N b' = divisorJetHorizonVector M N b' := by
        ext n
        rw [divisorJetHorizonVector_apply, divisorJetHorizonVector_apply]
        congr 1
        symm
        apply sum_subset (Icc_subset_Icc le_rfl hMR)
        intro m hm hmM
        rw [hzero m hm hmM, zero_mul]
      have hHM : 1 + Real.log M ≤ 2 * t := by
        by_cases htop2 : S.max' hS ≤ 2
        · have hMeq : M = 2 := max_eq_left htop2
          rw [hMeq]
          have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
          simp only [Nat.cast_ofNat]
          linarith only [hl, ht]
        · have hMeq : M = S.max' hS := max_eq_right (le_of_not_ge htop2)
          have hbound : 1 + Real.log (S.max' hS) ≤ t := by
            by_contra h
            have hz := hb ⟨S.max' hS, htop⟩ (lt_of_not_ge h)
            have hnz := (mem_filter.mp (S.max'_mem hS)).2
            rw [hb' (S.max' hS) htop, hz] at hnz
            exact hnz rfl
          rw [hMeq]
          linarith only [hbound, ht]
      have hMM : M * M ≤ N := (Nat.mul_le_mul hMR hMR).trans hRN
      have hlM : Real.log M ≤ Real.log R := Real.log_le_log
        (by exact_mod_cast (show 0 < M by omega)) (by exact_mod_cast hMR)
      have hlogM : 18 * (1 + Real.log M) ≤ Real.log N := by linarith only [hlM, hlog]
      have hMNT : ((M * M : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N := by
        refine le_trans ?_ hRNT
        apply mul_le_mul_of_nonneg_right _ (by unfold linearNearRowRadius; positivity)
        exact_mod_cast Nat.add_le_add_right (Nat.mul_le_mul hMR hMR) 1
      have hnb := sum_nearBand_sq_le_of_mem_conductorSubspace hM2 hlogM hc1 hw zero_le_one
        hMNT K2b hK2b_le (divisorJetHorizonVector_mem_conductorSubspace M N b')
      have hnorm_2b :
          ‖A_2b (divisorJetHorizonVector M N b')‖ ^ 2 ≤
            K_nb * c ^ 2 * ((1 + Real.log c) / Real.log N) *
              ‖divisorJetHorizonVector M N b'‖ ^ 2 := by
        rw [← sum_primeHorizonExtension_sq (A_2b (divisorJetHorizonVector M N b')),
          sum_congr rfl fun n hn => by
            rw [nearDivisorJetKernelMatrix_row φ c N (divisorJetHorizonVector M N b') n hn]]
        exact hnb.trans_eq (by dsimp only [K_nb]; ring)
      have hjet_norm := pow_le_pow_left₀ (norm_nonneg _) (hC_jet hM2 hMM hlogM b') 2
      rw [mul_pow, mul_pow, Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _)] at hjet_norm
      have hm_sub : (∑ m ∈ Icc 1 M, b' m ^ 2) ≤ ∑ i, b i ^ 2 := by
        rw [← hmass]
        exact sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl hMR) fun _ _ _ => sq_nonneg _
      have hC0_sq : C_0 ^ 2 =
          K_nb * C_jet ^ 2 * c ^ 2 * ((1 + Real.log c) / Real.log N) := by
        dsimp only [C_0]
        rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by dsimp only [K_nb]; positivity),
          Real.sq_sqrt (by positivity)]
      rw [hmap, hjet_eq]
      calc
        ‖A_2b (divisorJetHorizonVector M N b')‖ ^ 2 ≤
            K_nb * c ^ 2 * ((1 + Real.log c) / Real.log N) *
              (C_jet ^ 2 * (1 + Real.log M) ^ 2 * ∑ m ∈ Icc 1 M, b' m ^ 2) :=
          hnorm_2b.trans (mul_le_mul_of_nonneg_left hjet_norm (by dsimp only [K_nb]; positivity))
        _ = C_0 ^ 2 * (1 + Real.log M) ^ 2 * ∑ m ∈ Icc 1 M, b' m ^ 2 := by
          rw [hC0_sq]; ring
        _ ≤ C_0 ^ 2 * (2 * t) ^ 2 * ∑ i, b i ^ 2 :=
          mul_le_mul
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hHM 2) (sq_nonneg C_0))
            hm_sub (sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
        _ = (2 * C_0) ^ 2 * t ^ 2 * ∑ i, b i ^ 2 := by ring
    · have hb0 : ∀ i, b i = 0 := by
        intro i
        by_contra hi
        apply hS
        exact ⟨i, mem_filter.mpr ⟨i.property, by rwa [hb' i i.property]⟩⟩
      rw [show b = 0 from funext hb0, map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)]
      positivity
  have hH1 : 1 ≤ 1 + Real.log R := by linarith only [Real.log_natCast_nonneg R]
  have hmax : ∀ i, w_log i ≤ 1 + Real.log R := fun i => by
    have hi0 : (0 : ℝ) < (i : ℕ) := by exact_mod_cast (mem_Icc.mp i.property).1
    have hiR : ((i : ℕ) : ℝ) ≤ R := by exact_mod_cast (mem_Icc.mp i.property).2
    dsimp only [w_log]
    linarith only [Real.log_le_log hi0 hiR]
  have hinterp := linear_packet_sq_le_weighted_of_prefix_bound f w_log hw_log (2 * C_0)
    hprefix hH1 hmax (fun i => a i)
  have hf_apply : f (fun i => a i) = A_2b vJet := by
    dsimp only [vJet]
    rw [divisorJetHorizonVector_eq_sum_single R N a, map_sum]
    simp only [map_smul]
    exact sum_coe_sort (Icc 1 R) (fun m =>
      a m • A_2b (divisorJetHorizonVector R N (fun k => if k = m then 1 else 0)))
  have henergy : (∑ i : ↥(Icc 1 R), w_log i * a i ^ 2) =
      ∑ m ∈ Icc 1 R, (1 + Real.log m) * a m ^ 2 :=
    sum_coe_sort (Icc 1 R) (fun m => (1 + Real.log m) * a m ^ 2)
  have hsq2b :
      (∑ n ∈ Icc 1 N, (∑ j ∈ nearRowIndices c N n, K2b n j * primeHorizonExtension vJet j) ^ 2) ≤
        32 * K_nb * C_jet ^ 2 * c ^ 2 * (1 + Real.log R) * ((1 + Real.log c) / Real.log N) *
          ∑ m ∈ Icc 1 R, (1 + Real.log m) * a m ^ 2 := by
    have hrow_eq :
        (∑ n ∈ Icc 1 N, (∑ j ∈ nearRowIndices c N n, K2b n j * primeHorizonExtension vJet j) ^ 2) =
          ‖A_2b vJet‖ ^ 2 := by
      rw [← sum_primeHorizonExtension_sq (A_2b vJet)]
      exact sum_congr rfl fun n hn => by rw [nearDivisorJetKernelMatrix_row φ c N vJet n hn]
    rw [hrow_eq]
    rw [hf_apply, henergy] at hinterp
    refine hinterp.trans_eq ?_
    dsimp only [C_0]
    rw [mul_pow, mul_pow, mul_pow, mul_pow,
      Real.sq_sqrt (by dsimp only [K_nb]; positivity), Real.sq_sqrt (by positivity)]
    ring
  have hfour : ∀ x₁ x₂ x₃ x₄ : ℝ,
      (x₁ + x₂ + x₃ - x₄) ^ 2 ≤ 4 * (x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 + x₄ ^ 2) := fun x₁ x₂ x₃ x₄ => by
    nlinarith only [sq_nonneg (x₁ - x₂), sq_nonneg (x₁ - x₃), sq_nonneg (x₁ + x₄),
      sq_nonneg (x₂ - x₃), sq_nonneg (x₂ + x₄), sq_nonneg (x₃ + x₄)]
  rw [← sum_primeHorizonExtension_sq
    (Matrix.toEuclideanLin (overlapMatrix φ c N) u - downwardPrimeVector φ c N u)]
  have hpt : ∀ n ∈ Icc 1 N,
      primeHorizonExtension
          (Matrix.toEuclideanLin (overlapMatrix φ c N) u - downwardPrimeVector φ c N u) n ^ 2 ≤
        4 * ((∑ j ∈ nearRowIndices c N n, K1 n j * primeHorizonExtension u j) ^ 2 +
          (∑ j ∈ nearRowIndices c N n, K2a n j * primeHorizonExtension u j) ^ 2 +
          (∑ j ∈ nearRowIndices c N n, K2b n j * primeHorizonExtension vJet j) ^ 2 +
          (∑ m ∈ Icc 1 R, a m * ((Real.sqrt (m.totient : ℝ))⁻¹ *
            (actualExteriorDownwardRow g N m n / Real.sqrt (Real.log N)))) ^ 2) := by
    intro n hn
    rw [hrow_decomp n hn]
    exact hfour _ _ _ _
  have hG0_nonneg : 0 ≤ ∑ m ∈ Icc 1 R, (1 + Real.log m) * a m ^ 2 :=
    sum_nonneg fun m _ => mul_nonneg (by linarith [Real.log_natCast_nonneg m]) (sq_nonneg _)
  have hT_G : 0 ≤ c ^ 2 * (1 + Real.log R) * ((1 + Real.log c) / Real.log N) *
      ∑ m ∈ Icc 1 R, (1 + Real.log m) * a m ^ 2 := by positivity
  have hT_U1 : 0 ≤ c ^ 4 * (1 + Real.log c) / Real.log N * ‖u‖ ^ 2 := by positivity
  have hT_U2 : 0 ≤ c ^ 3 * (R : ℝ) ^ 2 * (Real.log N / N) * ‖u‖ ^ 2 := by positivity
  have hKnb_pos : 0 ≤ K_nb := by dsimp only [K_nb]; positivity
  have hKext_pos : 0 ≤ K_ext := by dsimp only [K_ext]; positivity
  calc
    (∑ n ∈ Icc 1 N, primeHorizonExtension
        (Matrix.toEuclideanLin (overlapMatrix φ c N) u - downwardPrimeVector φ c N u) n ^ 2) ≤
        4 * ((∑ n ∈ Icc 1 N, (∑ j ∈ nearRowIndices c N n, K1 n j * primeHorizonExtension u j) ^ 2) +
          (∑ n ∈ Icc 1 N, (∑ j ∈ nearRowIndices c N n, K2a n j * primeHorizonExtension u j) ^ 2) +
          (∑ n ∈ Icc 1 N, (∑ j ∈ nearRowIndices c N n, K2b n j * primeHorizonExtension vJet j) ^ 2) +
          (∑ n ∈ Icc 1 N, (∑ m ∈ Icc 1 R, a m * ((Real.sqrt (m.totient : ℝ))⁻¹ *
            (actualExteriorDownwardRow g N m n / Real.sqrt (Real.log N)))) ^ 2)) := by
      refine (sum_le_sum hpt).trans_eq ?_
      rw [← mul_sum, sum_add_distrib, sum_add_distrib, sum_add_distrib]
    _ ≤ 4 * (K_nb * c ^ 2 * (M_nc * c) ^ 2 * ((1 + Real.log c) / Real.log N) * ‖u‖ ^ 2 +
          K_nb * c ^ 2 * (M_2a * c) ^ 2 * ((1 + Real.log c) / Real.log N) * ‖u‖ ^ 2 +
          32 * K_nb * C_jet ^ 2 * c ^ 2 * (1 + Real.log R) * ((1 + Real.log c) / Real.log N) *
            (∑ m ∈ Icc 1 R, (1 + Real.log m) * a m ^ 2) +
          K_ext * c ^ 3 * (R : ℝ) ^ 2 * (Real.log N / N) * ‖u‖ ^ 2) := by
      linarith only [hsq1, hsq2a, hsq2b, hsq3]
    _ = 4 * (32 * K_nb * C_jet ^ 2) *
          (c ^ 2 * (1 + Real.log R) * ((1 + Real.log c) / Real.log N) *
            ∑ m ∈ Icc 1 R, (1 + Real.log m) * a m ^ 2) +
        4 * (K_nb * (M_nc ^ 2 + M_2a ^ 2)) *
          (c ^ 4 * (1 + Real.log c) / Real.log N * ‖u‖ ^ 2) +
        4 * K_ext * (c ^ 3 * (R : ℝ) ^ 2 * (Real.log N / N) * ‖u‖ ^ 2) := by ring
    _ ≤ C_near * (c ^ 2 * (1 + Real.log R) * ((1 + Real.log c) / Real.log N) *
            (∑ m ∈ Icc 1 R, (1 + Real.log m) * a m ^ 2) +
          (c ^ 4 * (1 + Real.log c) / Real.log N +
            c ^ 3 * (R : ℝ) ^ 2 * (Real.log N / N)) * ‖u‖ ^ 2) := by
      dsimp only [C_near]
      have h1 := mul_nonneg (show 0 ≤ K_nb * (M_nc ^ 2 + M_2a ^ 2) + K_ext + 1 by positivity) hT_G
      have h2 := mul_nonneg (show 0 ≤ 32 * K_nb * C_jet ^ 2 + K_ext + 1 by positivity) hT_U1
      have h3 := mul_nonneg
        (show 0 ≤ 32 * K_nb * C_jet ^ 2 + K_nb * (M_nc ^ 2 + M_2a ^ 2) + 1 by positivity) hT_U2
      nlinarith only [h1, h2, h3]

private theorem identity_euclid_apply' {N : ℕ}
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    Matrix.toEuclideanLin (1 : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ) x = x := by
  ext n
  change ((1 : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ) *ᵥ x) n = x n
  rw [Matrix.one_mulVec]

private theorem two_abs_le_energy_payment' {z F γ y : ℝ}
    (hF : 0 ≤ F) (hγ : 0 < γ) (hz : z ^ 2 ≤ F * y ^ 2) :
    2 * |z| ≤ F / γ + γ * y ^ 2 := by
  have he : (F / γ + γ * y ^ 2) ^ 2 =
      4 * F * y ^ 2 + (F / γ - γ * y ^ 2) ^ 2 := by
    field_simp [hγ.ne']
    ring
  have hs : (2 * |z|) ^ 2 ≤ (F / γ + γ * y ^ 2) ^ 2 := by
    rw [he]
    nlinarith only [hz, sq_abs z, sq_nonneg (F / γ - γ * y ^ 2)]
  have hr : 0 ≤ F / γ + γ * y ^ 2 := by positivity
  nlinarith only [hs, hr, abs_nonneg z]

private theorem four_signed_sq' (x y z w : ℝ) :
    (x - y + z - w) ^ 2 ≤ 4 * (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) := by
  nlinarith only [sq_nonneg (x + y), sq_nonneg (x - z), sq_nonneg (x + w),
    sq_nonneg (y + z), sq_nonneg (y - w), sq_nonneg (z + w)]

/-- **Complete Weil cross bound with `c^9` terminal reserve scaling.**
Replacing the whole-space separated cross bound by
`norm_separatedCrossErrorMatrix_sq_le_of_mem_conductorSubspace` (`O(c^4 / log N)`) and the merged
`overlap - downward` cross bound by `exists_overlap_sub_downward_sq_le_c9_split` (`c^2` on `G`)
yields a nonprime cross payment whose `(1 + log R) * G / γ` coefficient scales as `c^9 (1 + log c) / log N`
at `γ ~ k₁ / c^7`. -/
theorem exists_completeWeil_cross_le_c9_split_reserves :
    ∃ C_pr C_np : ℝ, 0 < C_pr ∧ 0 < C_np ∧
      ∀ {R M N : ℕ} {c : ℝ}, 2 ≤ R → R ^ 6 ≤ N → M ≤ N →
        18 * (1 + Real.log R) ≤ Real.log N → 1 ≤ c → c / N ≤ 1 / 3 →
        ((R * R : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N →
        ((R * R : ℕ) + 1 : ℝ) * (c * Real.exp 1 + 1) ≤ N →
      ∀ a : ℕ → ℝ,
        (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N) ∈ (conductorSubspace 1 N)ᗮ →
      ∀ {w : EuclideanSpace ℝ (PrimeHorizonIndex N)}, w ∈ (conductorSubspace R N)ᗮ →
      ∀ s t γ : ℝ, 0 < s → 0 < t → 0 < γ →
        2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
            (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N), w⟫| ≤
          C_pr * ((1 + Real.log R) * (∑ m ∈ Icc 1 R, a m ^ 2) +
            (1 + Real.log R) ^ 2 * primeAdjunctionMass R a) / (Real.log N * s) +
          C_pr * ((1 + Real.log R) * (∑ m ∈ Icc 1 R, a m ^ 2) +
            (1 + Real.log R) * terminalPacketCost R M N * primeAdjunctionMass R a) /
              (Real.log N * t) +
          C_np * ((c ^ 2 * (1 + Real.log R) * (1 + Real.log c) / Real.log N) *
              (∑ m ∈ Icc 1 R, (1 + Real.log m) * a m ^ 2) +
            (c ^ 4 * (1 + Real.log c) / Real.log N +
              c ^ 3 * (R : ℝ) ^ 2 * (Real.log N / N) +
              c ^ 2 * (1 + Real.log c)) *
              ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2) / γ +
          s * (∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2) +
          t * (∑ n ∈ Ioc M N, primeHorizonExtension w n ^ 2) + γ * ‖w‖ ^ 2 := by
  obtain ⟨C_pr, hC_pr, hpr⟩ := exists_prime_cross_le_split_mass_reserves
  obtain ⟨C_near, hC_near, hnear⟩ := exists_overlap_sub_downward_sq_le_c9_split
    contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
  obtain ⟨C_up, hC_up, hup⟩ := exists_upwardPrimeVector_norm_le_of_mem_conductorSubspace
    contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
  let K₀ := 152 * (∫ t, |tiltedUnitSpline t|) ^ 2 / (∫ t, tiltedUnitSpline t ^ 2)
  let C_sep_sq := 520 * K₀ ^ 2
  have hC_sep_sq : 0 ≤ C_sep_sq := by dsimp only [C_sep_sq]; positivity
  let C_cen : ℝ := 32 * 288 ^ 2
  let C_np := 4 * (C_cen + C_near + C_sep_sq + C_up ^ 2 + 1)
  refine ⟨C_pr + 532 + 28, C_np, by positivity, by dsimp only [C_np, C_cen]; positivity, ?_⟩
  intro R M N c hR hR6 hMN hlog hc1 hw1 hsize_near hsize_up a hu1 w hw s t γ hs ht hγ
  let u := ∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N
  let H := 1 + Real.log R
  let A := ∑ m ∈ Icc 1 R, a m ^ 2
  let E := primeAdjunctionMass R a
  let G := ∑ m ∈ Icc 1 R, (1 + Real.log m) * a m ^ 2
  let B := terminalPacketCost R M N
  let X := (c ^ 2 * H * (1 + Real.log c) / Real.log N) * G
  let Y := (c ^ 4 * (1 + Real.log c) / Real.log N + c ^ 3 * (R : ℝ) ^ 2 * (Real.log N / N)) *
    ‖u‖ ^ 2
  let U := c ^ 2 * (1 + Real.log c) * ‖u‖ ^ 2
  let zc := ⟪Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift tiltedUnitSpline c) N) u, w⟫
  let zs := ⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix tiltedUnitSpline c N) u, w⟫
  let zn := ⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) u -
    downwardPrimeVector tiltedUnitSpline c N u, w⟫
  let zu := ⟪upwardPrimeVector tiltedUnitSpline c N u, w⟫
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hRR : R * R ≤ N := by
    have hh := (Nat.pow_le_pow_right (by omega : 0 < R) (by norm_num : 2 ≤ 6)).trans hR6
    simpa only [sq] using hh
  have hR4 : R ^ 4 ≤ N :=
    (Nat.pow_le_pow_right (by omega : 0 < R) (by norm_num : 4 ≤ 6)).trans hR6
  have hN2 : 2 ≤ N := by have hh := Nat.mul_le_mul hR hR; omega
  have hN1 : 1 ≤ N := by omega
  have hL : 0 < Real.log N := by linarith only [hlog, Real.log_natCast_nonneg R]
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hA : 0 ≤ A := sum_nonneg fun _ _ => sq_nonneg _
  have hE : 0 ≤ E := primeAdjunctionMass_nonneg R a
  have hG : 0 ≤ G := sum_nonneg fun m _ => by
    have := Real.log_natCast_nonneg m; positivity
  have hB : 0 ≤ B := terminalPacketCost_nonneg R hMN
  have hlogc : 0 ≤ Real.log c := Real.log_nonneg hc1
  have h1logc : 1 ≤ 1 + Real.log c := by linarith only [hlogc]
  have hX : 0 ≤ X := by dsimp only [X]; positivity
  have hY : 0 ≤ Y := by dsimp only [Y]; positivity
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  have hu : u ∈ conductorSubspace R N := sum_normalizedRamanujanHorizonVector_mem_conductorSubspace R N a
  have hw_one : w ∈ (conductorSubspace 1 N)ᗮ := fun v hv =>
    hw v (conductorSubspace_mono (by omega : 1 ≤ R) N hv)
  have huw : ⟪u, w⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hu hw
  have hpole : |completeWeilPoleShift tiltedUnitSpline c| ≤ c := by
    rw [abs_of_nonneg (completeWeilPoleShift_nonneg tiltedUnitSpline hc0.le)]
    exact completeWeilPoleShift_le contDiff_tiltedUnitSpline.continuous
      tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hc0.le
  have hcen : zc ^ 2 ≤ C_cen * X * ‖w‖ ^ 2 := by
    have hh := fullWeilCenterMatrix_cross_sq_le_logarithmic_weight
      (completeWeilPoleShift tiltedUnitSpline c) hR hR6 hlog a hu1 hw_one
    have hp : completeWeilPoleShift tiltedUnitSpline c ^ 2 ≤ c ^ 2 * (1 + Real.log c) := by
      have hp2 : completeWeilPoleShift tiltedUnitSpline c ^ 2 ≤ c ^ 2 := by
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hpole 2
      nlinarith only [hp2, hlogc]
    have hm := mul_le_mul_of_nonneg_right hp
      (show 0 ≤ C_cen * H / Real.log N * G * ‖w‖ ^ 2 by dsimp only [C_cen]; positivity)
    rw [sq_abs] at hh
    calc
      zc ^ 2 ≤ C_cen * completeWeilPoleShift tiltedUnitSpline c ^ 2 * H /
          Real.log N * G * ‖w‖ ^ 2 := hh
      _ = completeWeilPoleShift tiltedUnitSpline c ^ 2 *
          (C_cen * H / Real.log N * G * ‖w‖ ^ 2) := by ring
      _ ≤ (c ^ 2 * (1 + Real.log c)) * (C_cen * H / Real.log N * G * ‖w‖ ^ 2) := hm
      _ = C_cen * X * ‖w‖ ^ 2 := by dsimp only [X]; ring
  have hsep : zs ^ 2 ≤ C_sep_sq * Y * ‖w‖ ^ 2 := by
    have hn := norm_separatedCrossErrorMatrix_sq_le_of_mem_conductorSubspace
      contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
      hc0 hR hR4 hlog hu
    have hcs := pow_le_pow_left₀ (abs_nonneg _)
      (abs_real_inner_le_norm (Matrix.toEuclideanLin (separatedCrossErrorMatrix tiltedUnitSpline c N) u) w) 2
    rw [sq_abs, mul_pow] at hcs
    have hZ_le_Y : (c ^ 4 / Real.log N) * ‖u‖ ^ 2 ≤ Y := by
      have h1 : c ^ 4 / Real.log N ≤ c ^ 4 * (1 + Real.log c) / Real.log N :=
        div_le_div_of_nonneg_right (by nlinarith only [h1logc, show 0 ≤ c ^ 4 by positivity]) hL.le
      have h2 : 0 ≤ c ^ 3 * (R : ℝ) ^ 2 * (Real.log N / N) := by positivity
      dsimp only [Y]
      exact mul_le_mul_of_nonneg_right (by linarith only [h1, h2]) (sq_nonneg ‖u‖)
    calc
      zs ^ 2 ≤ ‖Matrix.toEuclideanLin (separatedCrossErrorMatrix tiltedUnitSpline c N) u‖ ^ 2 *
          ‖w‖ ^ 2 := hcs
      _ ≤ (C_sep_sq * (c ^ 4 / Real.log N) * ‖u‖ ^ 2) * ‖w‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hn (sq_nonneg ‖w‖)
      _ = C_sep_sq * ((c ^ 4 / Real.log N) * ‖u‖ ^ 2) * ‖w‖ ^ 2 := by ring
      _ ≤ C_sep_sq * Y * ‖w‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hZ_le_Y hC_sep_sq) (sq_nonneg ‖w‖)
  have hnear_sq : zn ^ 2 ≤ C_near * (X + Y) * ‖w‖ ^ 2 := by
    have hn := hnear hR hRR hlog hc1 hw1 hsize_near a
    have hh := pow_le_pow_left₀ (abs_nonneg _)
      (abs_real_inner_le_norm (Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) u -
        downwardPrimeVector tiltedUnitSpline c N u) w) 2
    rw [sq_abs, mul_pow] at hh
    have hn' :
        ‖Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) u -
          downwardPrimeVector tiltedUnitSpline c N u‖ ^ 2 ≤ C_near * (X + Y) :=
      hn.trans_eq (by dsimp only [X, Y, H, G, u]; ring)
    exact hh.trans ((mul_le_mul_of_nonneg_right hn' (sq_nonneg ‖w‖)).trans_eq (by ring))
  have hup_sq : zu ^ 2 ≤ C_up ^ 2 * U * ‖w‖ ^ 2 := by
    have hn := hup hR hlog hc1 hw1 hsize_up hu
    have hh := (abs_real_inner_le_norm _ w).trans
      (mul_le_mul_of_nonneg_right hn (norm_nonneg w))
    have hsq := pow_le_pow_left₀ (abs_nonneg _) hh 2
    rw [sq_abs] at hsq
    exact hsq.trans_eq (by
      dsimp only [U]
      simp only [mul_pow, Real.sq_sqrt (by linarith only [hlogc] : 0 ≤ 1 + Real.log c)]
      ring)
  have hnonprime : (zc - zs + zn - zu) ^ 2 ≤ C_np * (X + Y + U) * ‖w‖ ^ 2 := by
    have hs4 := four_signed_sq' zc zs zn zu
    have hsum := add_le_add (add_le_add (add_le_add hcen hsep) hnear_sq) hup_sq
    have hcoef : 4 * (C_cen * X + C_sep_sq * Y + C_near * (X + Y) + C_up ^ 2 * U) ≤
        C_np * (X + Y + U) := by
      have h1 := mul_nonneg (show 0 ≤ C_sep_sq + C_up ^ 2 + 1 by positivity) hX
      have h2 := mul_nonneg (show 0 ≤ C_cen + C_up ^ 2 + 1 by dsimp only [C_cen]; positivity) hY
      have h3 := mul_nonneg
        (show 0 ≤ C_cen + C_near + C_sep_sq + 1 by dsimp only [C_cen]; positivity) hU
      dsimp only [C_np]
      nlinarith only [h1, h2, h3]
    have hc' := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖w‖)
    nlinarith only [hs4, hsum, hc']
  have hpay := two_abs_le_energy_payment'
    (show 0 ≤ C_np * (X + Y + U) by dsimp only [C_np, C_cen]; positivity) hγ hnonprime
  have hprime := hpr hR hN2 hMN a hw s t hs ht
  have hprime' : 2 * |⟪Matrix.toEuclideanLin (fullPrimeMatrix N) u, w⟫| ≤
      (C_pr + 532 + 28) * (H * A + H ^ 2 * E) / (Real.log N * s) +
      (C_pr + 532 + 28) * (H * A + H * B * E) / (Real.log N * t) +
      s * (∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2) +
      t * (∑ n ∈ Ioc M N, primeHorizonExtension w n ^ 2) := by
    have h1 : C_pr * H * A + 532 * H ^ 2 * E ≤ (C_pr + 532 + 28) * (H * A + H ^ 2 * E) := by
      nlinarith only [mul_nonneg hH hA, mul_nonneg (sq_nonneg H) hE,
        mul_nonneg hC_pr.le (mul_nonneg (sq_nonneg H) hE)]
    have h2 : C_pr * H * A + 28 * H * B * E ≤ (C_pr + 532 + 28) * (H * A + H * B * E) := by
      nlinarith only [mul_nonneg hH hA, mul_nonneg (mul_nonneg hH hB) hE,
        mul_nonneg hC_pr.le (mul_nonneg (mul_nonneg hH hB) hE)]
    have h1' := div_le_div_of_nonneg_right h1 (mul_pos hL hs).le
    have h2' := div_le_div_of_nonneg_right h2 (mul_pos hL ht).le
    change 2 * |⟪Matrix.toEuclideanLin (fullPrimeMatrix N) u, w⟫| ≤
      (C_pr * H * A + 532 * H ^ 2 * E) / (Real.log N * s) +
      (C_pr * H * A + 28 * H * B * E) / (Real.log N * t) + _ + _ at hprime
    linarith only [hprime, h1', h2']
  have hpole0 := fullWeilPoleErrorMatrix_inner_eq_zero_of_orthog_one tiltedUnitSpline c hN2 hu1 hw_one
  change ⟪Matrix.toEuclideanLin (fullWeilPoleErrorMatrix tiltedUnitSpline c N) u, w⟫ = 0 at hpole0
  have hdecomp : ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) u, w⟫ =
      -⟪Matrix.toEuclideanLin (fullPrimeMatrix N) u, w⟫ + (zc - zs + zn - zu) := by
    rw [completeWeilMatrix_eq_decomposition_at_every_overlap contDiff_tiltedUnitSpline
      tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hc0 hN1]
    simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, identity_euclid_apply',
      fullWeilNonRatioMatrix_eq_downward_add_upward contDiff_tiltedUnitSpline
        tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hc0 hN1 u,
      inner_add_left, inner_sub_left, real_inner_smul_left, huw, mul_zero, hpole0]
    dsimp only [zc, zs, zn, zu]
    rw [inner_sub_left]
    ring
  have habs := abs_add_le (-⟪Matrix.toEuclideanLin (fullPrimeMatrix N) u, w⟫) (zc - zs + zn - zu)
  rw [abs_neg, ← hdecomp] at habs
  have hcost : C_np * (X + Y + U) / γ =
      C_np * ((c ^ 2 * H * (1 + Real.log c) / Real.log N) * G +
        (c ^ 4 * (1 + Real.log c) / Real.log N +
          c ^ 3 * (R : ℝ) ^ 2 * (Real.log N / N) +
          c ^ 2 * (1 + Real.log c)) * ‖u‖ ^ 2) / γ := by
    dsimp only [X, Y, U]
    ring
  rw [hcost] at hpay
  change _ ≤ (C_pr + 532 + 28) * (H * A + H ^ 2 * E) / (Real.log N * s) +
    (C_pr + 532 + 28) * (H * A + H * B * E) / (Real.log N * t) +
    C_np * ((c ^ 2 * H * (1 + Real.log c) / Real.log N) * G +
      (c ^ 4 * (1 + Real.log c) / Real.log N +
        c ^ 3 * (R : ℝ) ^ 2 * (Real.log N / N) +
        c ^ 2 * (1 + Real.log c)) * ‖u‖ ^ 2) / γ +
    s * (∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2) +
    t * (∑ n ∈ Ioc M N, primeHorizonExtension w n ^ 2) + γ * ‖w‖ ^ 2
  linarith only [habs, hprime', hpay]

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_overlapMatrix_midBand_inner_le_three_halves
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_completeWeilEnergy_ge_three_quarters_log_homogeneous
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_completeWeilEnergy_ge_quarter_log_homogeneous
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.norm_separatedCrossErrorMatrix_sq_le_of_mem_conductorSubspace
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_overlap_sub_downward_sq_le_c9_split
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_completeWeil_cross_le_c9_split_reserves
