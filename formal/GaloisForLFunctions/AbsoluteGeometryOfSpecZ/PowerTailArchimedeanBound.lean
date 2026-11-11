import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailReferenceRemainder
import GaloisForLFunctions.HodgeTheoryOfAFixedPart.WeilsFormInTheGaugeOfTheFlatTail

/-!
# Archimedean size of power comb tails

The symmetric nonnegative jet matrix is bounded above by its row sums on
coefficient squares. Its harmonic rows and the logarithmic counterterm
therefore cost at most a logarithm times the square mass of a power tail.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open HodgeTheoryOfAFixedPart

private theorem harm_mono_of_le {m n : ℕ} (h : m ≤ n) : harm m ≤ harm n := by
  rw [← sum_Icc_one_div, ← sum_Icc_one_div]
  exact sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl h)
    (fun k _ _ => by positivity)

private theorem jet_row_le_harm {n N : ℕ} (hn : n ∈ Icc 1 N) :
    (∑ m ∈ (Icc 1 N).erase n, jetKernel m n) ≤ harm (2 * N) := by
  obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
  rw [sum_jetKernel_erase_Icc hn1 hnN]
  have h1 := harm_mono_of_le (show N - n ≤ 2 * N by omega)
  have h2 := harm_mono_of_le (show N + n ≤ 2 * N by omega)
  have h3 : 0 ≤ 3 / (4 * (n : ℝ)) := by positivity
  linarith only [h1, h2, h3]

/-- The nonnegative jet form is bounded by its largest harmonic row. -/
theorem sum_powerTail_jets_le (a : ℝ) (N : ℕ) :
    (∑ n ∈ Icc 1 N, ∑ m ∈ (Icc 1 N).erase n,
      powerTailWeight a m * powerTailWeight a n * jetKernel m n) ≤
        harm (2 * N) * ∑ n ∈ Icc 1 N, powerTailWeight a n ^ 2 := by
  rw [sum_mul_mul_eq_row_sub_dirichlet _ jetKernel jetKernel_comm,
    Finset.mul_sum]
  have hnonneg : 0 ≤ (∑ n ∈ Icc 1 N, ∑ m ∈ (Icc 1 N).erase n,
      (powerTailWeight a m - powerTailWeight a n) ^ 2 * jetKernel m n) / 2 := by
    exact div_nonneg (sum_nonneg fun n _ => sum_nonneg fun m _ =>
      mul_nonneg (sq_nonneg _) (jetKernel_nonneg m n)) (by norm_num)
  apply (sub_le_self _ hnonneg).trans
  apply sum_le_sum
  intro n hn
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_left (jet_row_le_harm hn) (sq_nonneg (powerTailWeight a n))

private theorem abs_counterterm_le {n N : ℕ} (hn : n ∈ Icc 1 N) :
    |counterterm n| ≤ Real.log N + |Real.log (2 * Real.pi)| := by
  obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn0 : (0 : ℝ) < n := by linarith only [hnR]
  have hNn : (n : ℝ) ≤ N := by exact_mod_cast hnN
  rw [counterterm, Real.log_div (ne_of_gt hn0) (by positivity)]
  calc
    _ ≤ |Real.log n| + |Real.log (2 * Real.pi)| := abs_sub _ _
    _ = Real.log n + |Real.log (2 * Real.pi)| := by
      rw [abs_of_nonneg (Real.log_nonneg hnR)]
    _ ≤ _ := add_le_add_right (Real.log_le_log hn0 hNn) _

/-- Absolute archimedean size before normalization, retaining the diagonal. -/
theorem abs_powerTailArchimedean_le_squareMass (a : ℝ) (N : ℕ) :
    |powerTailArchimedean a N| ≤
      (Real.log N + |Real.log (2 * Real.pi)| + harm (2 * N)) *
        ∑ n ∈ Icc 1 N, powerTailWeight a n ^ 2 := by
  have hjet0 : 0 ≤ ∑ n ∈ Icc 1 N, ∑ m ∈ (Icc 1 N).erase n,
      powerTailWeight a m * powerTailWeight a n * jetKernel m n := by
    apply sum_nonneg
    intro n _
    apply sum_nonneg
    intro m _
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg m) _)
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)) (jetKernel_nonneg m n)
  have hcounter : |∑ n ∈ Icc 1 N, powerTailWeight a n ^ 2 * counterterm n| ≤
      (Real.log N + |Real.log (2 * Real.pi)|) * ∑ n ∈ Icc 1 N, powerTailWeight a n ^ 2 := by
    apply (abs_sum_le_sum_abs _ _).trans
    rw [Finset.mul_sum]
    apply sum_le_sum
    intro n hn
    rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left
      (abs_counterterm_le hn) (sq_nonneg (powerTailWeight a n))
  unfold powerTailArchimedean
  calc
    _ ≤ |∑ n ∈ Icc 1 N, powerTailWeight a n ^ 2 * counterterm n| +
        |∑ n ∈ Icc 1 N, ∑ m ∈ (Icc 1 N).erase n,
          powerTailWeight a m * powerTailWeight a n * jetKernel m n| := abs_sub _ _
    _ ≤ (Real.log N + |Real.log (2 * Real.pi)|) *
        (∑ n ∈ Icc 1 N, powerTailWeight a n ^ 2) +
        harm (2 * N) * (∑ n ∈ Icc 1 N, powerTailWeight a n ^ 2) := by
      rw [abs_of_nonneg hjet0]
      exact add_le_add hcounter (sum_powerTail_jets_le a N)
    _ = _ := by ring

private theorem harm_le_rpow_div {e : ℝ} (he : 0 < e) (he1 : e < 1) (N : ℕ) :
    harm N ≤ (N : ℝ) ^ e / e := by
  rw [← sum_Icc_one_div]
  have h := HTGeometry.sum_rpow_sub_one_le he he1 N
  have hreindex := RHTower.sum_range_succ_eq_sourcePartialSum
    (fun n => (n : ℝ) ^ (e - 1)) N
  simp only [RHTower.sourcePartialSum, Nat.cast_add, Nat.cast_one] at hreindex
  rw [hreindex] at h
  apply le_trans ?_ h
  apply sum_le_sum
  intro n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
  rw [one_div, ← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [he])

private theorem sum_powerTailWeight_sq_le {a : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2)
    (N : ℕ) :
    (∑ n ∈ Icc 1 N, powerTailWeight a n ^ 2) ≤
      (N : ℝ) ^ (1 - 2 * a) / (1 - 2 * a) := by
  have he : (∑ n ∈ Icc 1 N, powerTailWeight a n ^ 2) = powerTailPrefix (2 * a) N := by
    simp only [powerTailPrefix, Nat.floor_natCast]
    apply sum_congr rfl
    intro n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    simp only [powerTailWeight, sq]
    rw [← Real.rpow_add hnR]
    congr 1
    ring
  rw [he]
  have h := (powerTailPrefix_sub_integral_bounds
    (show 0 < 2 * a by linarith only [ha])
    (show 2 * a < 1 by linarith only [ha2]) (Nat.cast_nonneg N)).2
  linarith only [h]

/-- Every positive power absorbs the archimedean logarithm. -/
theorem exists_powerTailArchimedean_bound {a : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      |powerTailArchimedean a N| ≤ C * ((N : ℝ) + 1) ^ (1 - 2 * a + δ) := by
  let e := min (δ / 2) (1 / 2)
  have he : 0 < e := lt_min (half_pos hδ) (by norm_num)
  have he1 : e < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have heδ : e ≤ δ := (min_le_left _ _).trans (by linarith only [hδ])
  have hc : 0 < 1 - 2 * a := by linarith only [ha2]
  let B := (1 + (2 : ℝ) ^ e) / e + |Real.log (2 * Real.pi)|
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  refine ⟨B / (1 - 2 * a), by positivity, fun N => ?_⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [powerTailArchimedean]
    positivity
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNe : 1 ≤ (N : ℝ) ^ e := Real.one_le_rpow hN1 he.le
  have hlog : Real.log N ≤ (N : ℝ) ^ e / e := Real.log_le_rpow_div hNp he
  have hharm := harm_le_rpow_div he he1 (2 * N)
  rw [Nat.cast_mul, Nat.cast_ofNat, Real.mul_rpow (by norm_num) hNp.le] at hharm
  have hconst : |Real.log (2 * Real.pi)| ≤ |Real.log (2 * Real.pi)| * (N : ℝ) ^ e :=
    le_mul_of_one_le_right (abs_nonneg _) hNe
  have hfactor : Real.log N + |Real.log (2 * Real.pi)| + harm (2 * N) ≤
      B * (N : ℝ) ^ e := by
    dsimp only [B]
    nlinarith only [hlog, hharm, hconst]
  calc
    _ ≤ (Real.log N + |Real.log (2 * Real.pi)| + harm (2 * N)) *
        ∑ n ∈ Icc 1 N, powerTailWeight a n ^ 2 := abs_powerTailArchimedean_le_squareMass a N
    _ ≤ (B * (N : ℝ) ^ e) * ((N : ℝ) ^ (1 - 2 * a) / (1 - 2 * a)) :=
      mul_le_mul hfactor (sum_powerTailWeight_sq_le ha ha2 N)
        (sum_nonneg fun n _ => sq_nonneg _) (mul_nonneg hB (Real.rpow_nonneg hNp.le _))
    _ = (B / (1 - 2 * a)) * (N : ℝ) ^ (1 - 2 * a + e) := by
      rw [Real.rpow_add hNp]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((Real.rpow_le_rpow hNp.le (by linarith) (by linarith only [hc, he])).trans
        (Real.rpow_le_rpow_of_exponent_le (by linarith only [hN1])
          (by linarith only [heδ]))) (div_nonneg hB hc.le)

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
