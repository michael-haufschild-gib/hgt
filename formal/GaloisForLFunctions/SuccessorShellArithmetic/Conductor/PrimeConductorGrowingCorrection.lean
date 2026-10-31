import GaloisForLFunctions.SuccessorShellArithmetic.Conductor.PrimeConductorHeadBoundary
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheRamanujanPrimeCorrectionHasAUniformTail
import GaloisForLFunctions.RHTower.BaezDuarteLogDualEnergy
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# The centered prime correction at moving heads

A prime dilation changes a Ramanujan mode only at primes dividing its
conductor. The resulting summable majorant permits a growing prime cutoff
inside the exact hyperbolic horizon. Its torsion finite part is unchanged.
-/

open Filter Topology Finset ArithmeticFunction
namespace GaloisForLFunctions.SuccessorShellArithmetic
open BezoutValuationIncidence RenormalizedArithmeticPotentialTheory
  RenormalizedBiarithmeticGeometry ArithmeticEffectivityTheory ArithmeticIntersectionTheory
noncomputable section

private def primeDilationCorrection (m l k n : ℕ) : ℝ :=
  vonMangoldt k / (k : ℝ) *
    (normalizedRamanujanMode m n * normalizedRamanujanMode l (k * n) +
      normalizedRamanujanMode l n * normalizedRamanujanMode m (k * n) -
        2 * (normalizedRamanujanMode m n * normalizedRamanujanMode l n))

private def primeDilationCorrectionMean (m l k : ℕ) : ℝ :=
  vonMangoldt k / (k : ℝ) *
    (primeConductorDilationMean m l k + primeConductorDilationMean l m k -
      (if m = l then 2 else 0))

private def primeDilationCorrectionMajorant (m l k : ℕ) : ℝ :=
  ((m.totient : ℝ) * ramanujanCorrectionMajorant l k +
    (l.totient : ℝ) * ramanujanCorrectionMajorant m k) /
      (Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ))

private theorem correctionMajorant_nonneg (m l k : ℕ) :
    0 ≤ primeDilationCorrectionMajorant m l k := by
  exact div_nonneg (add_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (ramanujanCorrectionMajorant_nonneg _ _))
    (mul_nonneg (Nat.cast_nonneg _) (ramanujanCorrectionMajorant_nonneg _ _)))
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

private theorem summable_correctionMajorant (m l : ℕ) :
    Summable (primeDilationCorrectionMajorant m l) :=
  (((summable_ramanujanCorrectionMajorant l).mul_left (m.totient : ℝ)).add
    ((summable_ramanujanCorrectionMajorant m).mul_left (l.totient : ℝ))).div_const _

private theorem abs_primeDilationCorrection_le {m l : ℕ}
    (hm : 0 < m) (hl : 0 < l) (k n : ℕ) :
    |primeDilationCorrection m l k n| ≤ primeDilationCorrectionMajorant m l k := by
  have he : primeDilationCorrection m l k n =
      (ramanujanLagCoefficient m n *
        ((ramanujanLagCoefficient l (n * k) - ramanujanLagCoefficient l n) * vonMangoldt k / k) +
       ramanujanLagCoefficient l n *
        ((ramanujanLagCoefficient m (n * k) - ramanujanLagCoefficient m n) * vonMangoldt k / k)) /
          (Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ)) := by
    simp only [primeDilationCorrection, normalizedRamanujanMode_eq_coefficient hm,
      normalizedRamanujanMode_eq_coefficient hl, Nat.mul_comm n k]
    ring
  rw [he, abs_div, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  apply div_le_div_of_nonneg_right _ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  calc
    _ ≤ |ramanujanLagCoefficient m n| *
        |(ramanujanLagCoefficient l (n * k) - ramanujanLagCoefficient l n) * vonMangoldt k / k| +
      |ramanujanLagCoefficient l n| *
        |(ramanujanLagCoefficient m (n * k) - ramanujanLagCoefficient m n) * vonMangoldt k / k| := by
      simpa only [abs_mul] using abs_add_le
        (ramanujanLagCoefficient m n *
          ((ramanujanLagCoefficient l (n * k) - ramanujanLagCoefficient l n) * vonMangoldt k / k))
        (ramanujanLagCoefficient l n *
          ((ramanujanLagCoefficient m (n * k) - ramanujanLagCoefficient m n) * vonMangoldt k / k))
    _ ≤ _ := add_le_add
      (mul_le_mul (BiScaleUncertainty.SieveMoments.abs_ramanujanLagCoefficient_le_totient m n)
        (abs_ramanujan_up_difference_le hl n k) (abs_nonneg _) (Nat.cast_nonneg _))
      (mul_le_mul (BiScaleUncertainty.SieveMoments.abs_ramanujanLagCoefficient_le_totient l n)
        (abs_ramanujan_up_difference_le hm n k) (abs_nonneg _) (Nat.cast_nonneg _))

private theorem tendsto_undilated_harmonic {m l k : ℕ}
    (hm : 0 < m) (hl : 0 < l) (hk : 0 < k) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 (N / k), normalizedRamanujanMode m n * normalizedRamanujanMode l n / (n : ℝ)) /
        Real.log N) atTop (𝓝 (if m = l then 1 else 0)) := by
  have hpm : Function.Periodic (normalizedRamanujanMode m) (m * l) := by
    simpa only [Nat.cast_id, Nat.mul_comm] using (normalizedRamanujanMode_periodic hm).nat_mul l
  have hpl : Function.Periodic (normalizedRamanujanMode l) (m * l) := by
    simpa only [Nat.cast_id] using (normalizedRamanujanMode_periodic hl).nat_mul m
  have hp : Function.Periodic (fun n => normalizedRamanujanMode m n * normalizedRamanujanMode l n)
      (m * l) := fun n => congrArg₂ (· * ·) (hpm n) (hpl n)
  have h := tendsto_harmonic_mean_div (Nat.mul_pos hm hl) hp hk
  rwa [periodMean_normalizedRamanujanMode_mul hm hl
    (dvd_mul_right m l) (dvd_mul_left l m) (Nat.mul_pos hm hl)] at h

private theorem correction_harmonic_eq (m l k N : ℕ) :
    (∑ n ∈ Icc 1 (N / k), primeDilationCorrection m l k n / (n : ℝ)) / Real.log N =
      vonMangoldt k / (k : ℝ) *
        (((∑ n ∈ Icc 1 (N / k), normalizedRamanujanMode m n *
          normalizedRamanujanMode l (k * n) / (n : ℝ)) / Real.log N) +
         ((∑ n ∈ Icc 1 (N / k), normalizedRamanujanMode l n *
          normalizedRamanujanMode m (k * n) / (n : ℝ)) / Real.log N) -
         2 * ((∑ n ∈ Icc 1 (N / k), normalizedRamanujanMode m n *
          normalizedRamanujanMode l n / (n : ℝ)) / Real.log N)) := by
  simp only [primeDilationCorrection, mul_sub, mul_add, sub_div, add_div,
    sum_sub_distrib, sum_add_distrib, mul_div_assoc, ← mul_sum]

private theorem tendsto_correction_harmonic {m l : ℕ}
    (hm : 0 < m) (hl : 0 < l) (k : ℕ) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 (N / k), primeDilationCorrection m l k n / (n : ℝ)) / Real.log N)
      atTop (𝓝 (primeDilationCorrectionMean m l k)) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [primeDilationCorrection, primeDilationCorrectionMean,
      Nat.cast_zero, div_zero, zero_mul, zero_div, sum_const_zero]
    exact tendsto_const_nhds
  · have h := (((tendsto_primeConductorHarmonicDilationMean hm hl hk).add
      (tendsto_primeConductorHarmonicDilationMean hl hm hk)).sub
        ((tendsto_undilated_harmonic hm hl hk).const_mul 2)).const_mul
          (vonMangoldt k / (k : ℝ))
    have hδ : 2 * (if m = l then (1 : ℝ) else 0) = if m = l then 2 else 0 := by
      split_ifs <;> ring
    simp only [hδ] at h
    simpa only [correction_harmonic_eq, primeDilationCorrectionMean] using h

private theorem correction_harmonic_bound {m l : ℕ}
    (hm : 0 < m) (hl : 0 < l) {N : ℕ} (hlog : 1 ≤ Real.log N) (k : ℕ) :
    ‖(∑ n ∈ Icc 1 (N / k), primeDilationCorrection m l k n / (n : ℝ)) / Real.log N‖ ≤
      2 * primeDilationCorrectionMajorant m l k := by
  have hlog0 : 0 < Real.log (N : ℝ) := lt_of_lt_of_le zero_lt_one hlog
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hlog0]
  apply (div_le_iff₀ hlog0).mpr
  calc
    _ ≤ ∑ n ∈ Icc 1 (N / k), |primeDilationCorrection m l k n / (n : ℝ)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Icc 1 (N / k), primeDilationCorrectionMajorant m l k / (n : ℝ) := by
      apply sum_le_sum
      intro n hn
      rw [abs_div, abs_of_nonneg (a := (n : ℝ)) (Nat.cast_nonneg n)]
      exact div_le_div_of_nonneg_right (abs_primeDilationCorrection_le hm hl k n) (Nat.cast_nonneg n)
    _ = primeDilationCorrectionMajorant m l k * ∑ n ∈ Icc 1 (N / k), 1 / (n : ℝ) := by
      rw [mul_sum]
      exact sum_congr rfl fun n _ => by ring
    _ ≤ primeDilationCorrectionMajorant m l k * ∑ n ∈ Icc 1 N, 1 / (n : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (correctionMajorant_nonneg m l k)
      apply sum_le_sum_of_subset_of_nonneg
      · intro n hn
        exact mem_Icc.mpr ⟨(mem_Icc.mp hn).1, (mem_Icc.mp hn).2.trans (Nat.div_le_self N k)⟩
      · intro n _ _
        positivity
    _ ≤ primeDilationCorrectionMajorant m l k * (1 + Real.log N) :=
      mul_le_mul_of_nonneg_left (_root_.RHTower.sum_Icc_inv_le_one_add_log N)
        (correctionMajorant_nonneg m l k)
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left hlog (correctionMajorant_nonneg m l k)
      nlinarith only [h]

/-- Every growing prime head has the same centered torsion correction. -/
theorem tendsto_primeConductorGrowingHead_correction {m l : ℕ}
    (hm : 0 < m) (hl : 0 < l) {K : ℕ → ℕ} (hK : Tendsto K atTop atTop) :
    Tendsto (fun N : ℕ => primeConductorHeadPairing m l (K N) N -
      2 * ∑ k ∈ range (K N), vonMangoldt k / (k : ℝ) *
        ((∑ n ∈ Icc 1 (N / k), normalizedRamanujanMode m n * normalizedRamanujanMode l n /
          (n : ℝ)) / Real.log N)) atTop
      (𝓝 (orbitIntersection m l / (Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ)) -
        (if m = l then Real.log m + tameDifferent m else 0))) := by
  let f : ℕ → ℕ → ℝ := fun N k =>
    (∑ n ∈ Icc 1 (N / k), primeDilationCorrection m l k n / (n : ℝ)) / Real.log N
  let b : ℕ → ℝ := fun k => 2 * primeDilationCorrectionMajorant m l k
  have hb : Summable b := (summable_correctionMajorant m l).mul_left 2
  have hlog := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  have hbound : ∀ᶠ N : ℕ in atTop, ∀ k, ‖f N k‖ ≤ b k := by
    filter_upwards [hlog.eventually_ge_atTop 1] with N hN
    exact fun k => correction_harmonic_bound hm hl hN k
  have hmeanBound (k : ℕ) : ‖primeDilationCorrectionMean m l k‖ ≤ b k :=
    le_of_tendsto (tendsto_correction_harmonic hm hl k).norm
      (hbound.mono fun N hN => hN k)
  have hsum : Summable (primeDilationCorrectionMean m l) := hb.of_norm_bounded hmeanBound
  have hvalue : (∑' k, primeDilationCorrectionMean m l k) =
      orbitIntersection m l / (Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ)) -
        (if m = l then Real.log m + tameDifferent m else 0) :=
    tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat (tendsto_primeConductorHeadMean_finitePart hm hl)
  let cut : ℕ → ℕ → ℝ := fun N k => if k < K N then f N k else 0
  have hpoint (k : ℕ) : Tendsto (fun N => cut N k) atTop (𝓝 (primeDilationCorrectionMean m l k)) := by
    apply (tendsto_correction_harmonic hm hl k).congr'
    filter_upwards [hK.eventually_gt_atTop k] with N hN
    exact (if_pos hN).symm
  have hcutbound : ∀ᶠ N : ℕ in atTop, ∀ k, ‖cut N k‖ ≤ b k := by
    filter_upwards [hbound] with N hN k
    dsimp only [cut]
    split_ifs
    · exact hN k
    · simpa only [norm_zero] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (correctionMajorant_nonneg m l k)
  have h := tendsto_tsum_of_dominated_convergence hb hpoint hcutbound
  rw [hvalue] at h
  apply h.congr
  intro N
  have hfinite : (∑' k, cut N k) = ∑ k ∈ range (K N), f N k := by
    rw [tsum_eq_sum (s := range (K N)) (fun k hk => by
      simp only [mem_range, not_lt] at hk
      exact if_neg (not_lt.mpr hk))]
    exact sum_congr rfl fun k hk => if_pos (mem_range.mp hk)
  rw [hfinite, primeConductorHeadPairing, mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro k _
  dsimp only [f]
  rw [correction_harmonic_eq]
  simp only [add_div, sum_add_distrib]
  ring

#print axioms tendsto_primeConductorGrowingHead_correction

end
end GaloisForLFunctions.SuccessorShellArithmetic
