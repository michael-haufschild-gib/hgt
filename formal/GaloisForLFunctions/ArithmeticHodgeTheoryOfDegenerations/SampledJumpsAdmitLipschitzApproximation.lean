import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.LogarithmicAnnuliHaveUniformRowMeans

/-!
Finite sampled jump profiles admit Lipschitz ramp approximations. The square-mean error is controlled by the strip width and lattice endpoint count.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Finset Filter Topology
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

/-- The descending affine ramp across a strip of half-width η. -/
def descendingRamp (u η x : ℝ) : ℝ := max 0 (min 1 ((u + η - x) / (2 * η)))

lemma descendingRamp_bounds (u η x : ℝ) : 0 ≤ descendingRamp u η x ∧ descendingRamp u η x ≤ 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

lemma descendingRamp_eq_one {u η x : ℝ} (hη : 0 < η) (hx : x ≤ u - η) :
    descendingRamp u η x = 1 := by
  have h : (1 : ℝ) ≤ (u + η - x) / (2 * η) :=
    (le_div_iff₀ (by positivity)).mpr (by linarith only [hx])
  simp only [descendingRamp, min_eq_left h, max_eq_right zero_le_one]

lemma descendingRamp_eq_zero {u η x : ℝ} (hη : 0 < η) (hx : u + η ≤ x) :
    descendingRamp u η x = 0 := by
  have h : (u + η - x) / (2 * η) ≤ 0 := div_nonpos_of_nonpos_of_nonneg
    (by linarith only [hx]) (by positivity)
  simp only [descendingRamp, min_eq_right (h.trans zero_le_one), max_eq_left h]

/-- The ramp is globally Lipschitz, with the exact affine slope bound. -/
lemma lipschitzWith_descendingRamp {η : ℝ} (hη : 0 < η) (u : ℝ) :
    LipschitzWith (Real.toNNReal (1 / (2 * η))) (descendingRamp u η) := by
  have hbase : LipschitzWith (Real.toNNReal (1 / (2 * η)))
      (fun x : ℝ => (u + η - x) / (2 * η)) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
    have he : (u + η - x) / (2 * η) - (u + η - y) / (2 * η) = (y - x) / (2 * η) := by ring
    rw [he, abs_div, abs_of_pos (by positivity : 0 < 2 * η), abs_sub_comm]
    exact le_of_eq (by ring)
  exact (hbase.const_min 1).const_max 0

lemma descendingRamp_indicator_sq_le {η : ℝ} (hη : 0 < η) (u x : ℝ) :
    ((if x ≤ u then (1 : ℝ) else 0) - descendingRamp u η x) ^ 2 ≤
      if |x - u| ≤ η then 1 else 0 := by
  obtain ⟨hlo, hhi⟩ := descendingRamp_bounds u η x
  by_cases hstrip : |x - u| ≤ η
  · rw [if_pos hstrip]
    split_ifs <;> nlinarith only [hlo, hhi, mul_nonneg hlo (sub_nonneg.mpr hhi)]
  · rw [if_neg hstrip]
    have hout := lt_of_not_ge hstrip
    by_cases hxu : x ≤ u
    · rw [abs_of_nonpos (sub_nonpos.mpr hxu)] at hout
      have hx : x ≤ u - η := by linarith only [hout]
      rw [descendingRamp_eq_one hη hx, if_pos hxu]
      norm_num
    · rw [abs_of_pos (sub_pos.mpr (lt_of_not_ge hxu))] at hout
      have hx : u + η ≤ x := by linarith only [hout]
      rw [descendingRamp_eq_zero hη hx, if_neg hxu]
      norm_num

/-- A strip of sample coordinates has at most its length times N plus four endpoint units. -/
lemma card_samples_near_le {N : ℕ} (hN : 1 ≤ N) {u η : ℝ} (hη : 0 ≤ η) (hu : η ≤ u) :
    (((Icc 1 N).filter (fun n : ℕ => |(n : ℝ) / N - u| ≤ η)).card : ℝ) ≤
      2 * η * N + 4 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  let a := (u - η) * (N : ℝ)
  let b := (u + η) * (N : ℝ)
  have ha : 0 ≤ a := mul_nonneg (sub_nonneg.mpr hu) hN0.le
  have hab : a ≤ b := mul_le_mul_of_nonneg_right (by linarith only [hη]) hN0.le
  have hquad := abs_sum_Ioc_floor_sub_integral_le (f := fun _ => (1 : ℝ))
    ha hab zero_le_one (by norm_num : (0 : ℝ) ≤ 0)
    (by intro x hx; simp) (by intro x hx y hy; simp)
  have hclosed := abs_sum_Icc_ceil_floor_sub_sum_Ioc_floor_le (f := fun _ => (1 : ℝ))
    ha hab zero_le_one (by intro x hx; simp)
  simp only [sum_const, nsmul_eq_mul, mul_one, intervalIntegral.integral_const,
    smul_eq_mul, zero_mul, zero_add] at hquad hclosed
  have hquadUpper := (le_abs_self _).trans hquad
  have hclosedUpper := (le_abs_self _).trans hclosed
  have hcard : ((Icc ⌈a⌉₊ ⌊b⌋₊).card : ℝ) ≤ b - a + 4 := by
    linarith only [hquadUpper, hclosedUpper]
  have hsub : (Icc 1 N).filter (fun n : ℕ => |(n : ℝ) / N - u| ≤ η) ⊆ Icc ⌈a⌉₊ ⌊b⌋₊ := by
    intro n hn
    obtain ⟨_, hgap⟩ := mem_filter.mp hn
    have hg := abs_le.mp hgap
    have hlo : a ≤ (n : ℝ) := (le_div_iff₀ hN0).mp (by linarith only [hg.1])
    have hhi : (n : ℝ) ≤ b := (div_le_iff₀ hN0).mp (by linarith only [hg.2])
    exact mem_Icc.mpr ⟨Nat.ceil_le.mpr hlo, Nat.le_floor hhi⟩
  calc
    _ ≤ ((Icc ⌈a⌉₊ ⌊b⌋₊).card : ℝ) := by exact_mod_cast card_le_card hsub
    _ ≤ b - a + 4 := hcard
    _ = _ := by dsimp only [a, b]; ring

/-- Lipschitz ramps approximate sampled jumps in normalized square mean; only a strip and its
lattice endpoints contribute to the error. -/
theorem normalized_sum_indicator_sub_descendingRamp_sq_le {N : ℕ} (hN : 1 ≤ N)
    {u η : ℝ} (hη : 0 < η) (hu : η ≤ u) :
    (∑ n ∈ Icc 1 N,
      ((if (n : ℝ) / N ≤ u then (1 : ℝ) else 0) - descendingRamp u η ((n : ℝ) / N)) ^ 2) / N ≤
      2 * η + 4 / N := by
  have hsum := sum_le_sum (fun n (_hn : n ∈ Icc 1 N) =>
    descendingRamp_indicator_sq_le hη u ((n : ℝ) / N))
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one] at hsum
  have htotal := hsum.trans (card_samples_near_le hN hη.le hu)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  exact (div_le_div_of_nonneg_right htotal hN0.le).trans_eq (by field_simp [hN0.ne'])

/-- A finite collection of sampled jumps admits uniform square-mean ramp approximation;
the constant depends only on its coefficient square sum and number of jumps. -/
theorem normalized_sum_finite_jumps_sub_ramps_sq_le {N : ℕ} (hN : 1 ≤ N)
    (S : Finset ℕ) (a u : ℕ → ℝ) {η : ℝ} (hη : 0 < η) (hu : ∀ k ∈ S, η ≤ u k) :
    (∑ n ∈ Icc 1 N,
      (∑ k ∈ S, a k * ((if (n : ℝ) / N ≤ u k then (1 : ℝ) else 0) -
        descendingRamp (u k) η ((n : ℝ) / N))) ^ 2) / N ≤
      (∑ k ∈ S, a k ^ 2) * (S.card * (2 * η + 4 / N)) := by
  let d : ℕ → ℕ → ℝ := fun k n =>
    (if (n : ℝ) / N ≤ u k then 1 else 0) - descendingRamp (u k) η ((n : ℝ) / N)
  let C := ∑ k ∈ S, a k ^ 2
  have hC : 0 ≤ C := sum_nonneg fun _ _ => sq_nonneg _
  have hcs : (∑ n ∈ Icc 1 N, (∑ k ∈ S, a k * d k n) ^ 2) ≤
      C * ∑ n ∈ Icc 1 N, ∑ k ∈ S, d k n ^ 2 := by
    rw [mul_sum]
    exact sum_le_sum fun n _ => Finset.sum_mul_sq_le_sq_mul_sq S a (fun k => d k n)
  have he : (C * ∑ n ∈ Icc 1 N, ∑ k ∈ S, d k n ^ 2) / N =
      C * ∑ k ∈ S, (∑ n ∈ Icc 1 N, d k n ^ 2) / N := by
    rw [sum_comm, ← sum_div]
    ring
  have hs : (∑ k ∈ S, (∑ n ∈ Icc 1 N, d k n ^ 2) / N) ≤
      S.card * (2 * η + 4 / N) := by
    calc
      _ ≤ ∑ k ∈ S, (2 * η + 4 / N) := sum_le_sum fun k hk =>
        normalized_sum_indicator_sub_descendingRamp_sq_le hN hη (hu k hk)
      _ = _ := by rw [sum_const, nsmul_eq_mul]
  calc
    _ ≤ (C * ∑ n ∈ Icc 1 N, ∑ k ∈ S, d k n ^ 2) / N :=
      div_le_div_of_nonneg_right hcs (Nat.cast_nonneg N)
    _ = C * ∑ k ∈ S, (∑ n ∈ Icc 1 N, d k n ^ 2) / N := he
    _ ≤ _ := mul_le_mul_of_nonneg_left hs hC

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
