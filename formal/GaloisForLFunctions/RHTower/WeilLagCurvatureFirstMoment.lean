import GaloisForLFunctions.RHTower.WeilLagNativeCurvatureSign

/-!
# First absolute moment of the native curvature correction

Native scaled lag curvature differs from `(Λ(n+3)-1)/(n+3)` by a correction
whose absolute first moment is at most two. Symmetric logarithmic curvature
has a cubic reciprocal error; the complete trivial-zero contribution has a
finite first moment by discrete summation by parts. No prime cancellation
estimate or Riemann-hypothesis premise is used.
-/

open Real Set Filter Topology
namespace RHTower.IntegerLagCurvature

private noncomputable def logModel (c b x : ℝ) : ℝ :=
  x * Real.log x - (1 / c + b) * (x ^ 2 / 2) + (x - c) ^ 3 / (6 * c ^ 2)

private theorem logModel_deriv {c x : ℝ} (hc : 0 < c) (hx : 0 < x) (b : ℝ) :
    HasDerivAt (logModel c b)
      (Real.log x + 1 - (1 / c + b) * x + (x - c) ^ 2 / (2 * c ^ 2)) x := by
  have h := ((Real.hasDerivAt_mul_log hx.ne').sub
    ((((hasDerivAt_id' x).pow 2).div_const 2).const_mul (1 / c + b))).add
    ((((hasDerivAt_id' x).sub_const c).pow 3).div_const (6 * c ^ 2))
  convert! h using 1
  field_simp
  ring

private theorem logModel_deriv2 {c x : ℝ} (hc : 0 < c) (hx : 0 < x) (b : ℝ) :
    HasDerivAt (fun x : ℝ =>
      Real.log x + 1 - (1 / c + b) * x + (x - c) ^ 2 / (2 * c ^ 2))
      (x⁻¹ - (1 / c + b) + (x - c) / c ^ 2) x := by
  have h := (((Real.hasDerivAt_log hx.ne').add_const 1).sub
    ((hasDerivAt_id' x).const_mul (1 / c + b))).add
    ((((hasDerivAt_id' x).sub_const c).pow 2).div_const (2 * c ^ 2))
  convert! h using 1
  field_simp
  ring

private theorem logModel_continuous (c b : ℝ) : Continuous (logModel c b) := by
  exact (continuous_id.mul_log.sub
    (((continuous_id.pow 2).div_const 2).const_mul (1 / c + b))).add
    (((continuous_id.sub continuous_const).pow 3).div_const (6 * c ^ 2))

private theorem logModel_convex {c : ℝ} (hc : 2 ≤ c) :
    ConvexOn ℝ (Icc (c - 1) (c + 1)) (logModel c 0) := by
  have hc0 : 0 < c := by linarith
  apply convexOn_of_hasDerivWithinAt2_nonneg
    (f' := fun x => Real.log x + 1 - (1 / c + 0) * x + (x - c) ^ 2 / (2 * c ^ 2))
    (f'' := fun x => x⁻¹ - (1 / c + 0) + (x - c) / c ^ 2)
    (convex_Icc _ _)
  · exact (logModel_continuous c 0).continuousOn
  · intro x hx
    have hxI : x ∈ Icc (c - 1) (c + 1) := interior_subset hx
    exact (logModel_deriv hc0 (by linarith [hxI.1]) 0).hasDerivWithinAt
  · intro x hx
    have hxI : x ∈ Icc (c - 1) (c + 1) := interior_subset hx
    exact (logModel_deriv2 hc0 (by linarith [hxI.1]) 0).hasDerivWithinAt
  · intro x hx
    have hxI : x ∈ Icc (c - 1) (c + 1) := interior_subset hx
    have hx0 : 0 < x := by linarith [hxI.1]
    have heq : x⁻¹ - (1 / c + 0) + (x - c) / c ^ 2 =
        (x - c) ^ 2 / (c ^ 2 * x) := by field_simp; ring
    rw [heq]
    positivity

private theorem logModel_concave {c : ℝ} (hc : 2 ≤ c) :
    ConcaveOn ℝ (Icc (c - 1) (c + 1))
      (logModel c (1 / (c ^ 2 * (c - 1)))) := by
  have hc0 : 0 < c := by linarith
  apply concaveOn_of_hasDerivWithinAt2_nonpos
    (f' := fun x => Real.log x + 1 - (1 / c + 1 / (c ^ 2 * (c - 1))) * x +
      (x - c) ^ 2 / (2 * c ^ 2))
    (f'' := fun x => x⁻¹ - (1 / c + 1 / (c ^ 2 * (c - 1))) + (x - c) / c ^ 2)
    (convex_Icc _ _)
  · exact (logModel_continuous _ _).continuousOn
  · intro x hx
    have hxI : x ∈ Icc (c - 1) (c + 1) := interior_subset hx
    exact (logModel_deriv hc0 (by linarith [hxI.1]) _).hasDerivWithinAt
  · intro x hx
    have hxI : x ∈ Icc (c - 1) (c + 1) := interior_subset hx
    exact (logModel_deriv2 hc0 (by linarith [hxI.1]) _).hasDerivWithinAt
  · intro x hx
    have hxI : x ∈ Icc (c - 1) (c + 1) := interior_subset hx
    have hx0 : 0 < x := by linarith [hxI.1]
    have hcm : 0 < c - 1 := by linarith
    have heq : x⁻¹ - (1 / c + 1 / (c ^ 2 * (c - 1))) + (x - c) / c ^ 2 =
        (x - c) ^ 2 / (c ^ 2 * x) - 1 / (c ^ 2 * (c - 1)) := by
      field_simp
      ring
    rw [heq, sub_nonpos]
    have hsq : (x - c) ^ 2 ≤ 1 := by nlinarith [hxI.1, hxI.2]
    calc
      _ ≤ 1 / (c ^ 2 * x) := div_le_div_of_nonneg_right hsq (by positivity)
      _ ≤ _ := one_div_le_one_div_of_le (by positivity) (by gcongr; exact hxI.1)

theorem logCurvature_centered_bounds (n : ℕ) :
    0 ≤ logCurvature n - 1 / (n + 3 : ℝ) ∧
      logCurvature n - 1 / (n + 3 : ℝ) ≤
        1 / ((n + 3 : ℝ) ^ 2 * (n + 2 : ℝ)) := by
  let c : ℝ := n + 3
  have hc : 2 ≤ c := by dsimp [c]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hleft : c - 1 ∈ Icc (c - 1) (c + 1) := ⟨le_rfl, by linarith⟩
  have hright : c + 1 ∈ Icc (c - 1) (c + 1) := ⟨by linarith, le_rfl⟩
  have hlo := (logModel_convex hc).2 hleft hright
    (show 0 ≤ (1 / 2 : ℝ) by positivity) (show 0 ≤ (1 / 2 : ℝ) by positivity) (by ring)
  have hup := (logModel_concave hc).2 hleft hright
    (show 0 ≤ (1 / 2 : ℝ) by positivity) (show 0 ≤ (1 / 2 : ℝ) by positivity) (by ring)
  simp only [smul_eq_mul] at hlo hup
  rw [show (1 / 2 : ℝ) * (c - 1) + (1 / 2 : ℝ) * (c + 1) = c by ring] at hlo hup
  have hmodel (b : ℝ) :
      logModel c b (c + 1) - 2 * logModel c b c + logModel c b (c - 1) =
        logCurvature n - 1 / c - b := by
    dsimp [logModel, logCurvature]
    rw [show c + 1 = (n : ℝ) + 4 by dsimp [c]; ring,
      show c - 1 = (n : ℝ) + 2 by dsimp [c]; ring]
    dsimp [c]
    ring
  have hzero := hmodel 0
  have hupper := hmodel (1 / (c ^ 2 * (c - 1)))
  constructor
  · change 0 ≤ logCurvature n - 1 / c
    linarith only [hlo, hzero]
  · have hcm : c - 1 = (n : ℝ) + 2 := by dsimp [c]; ring
    change logCurvature n - 1 / c ≤ 1 / (c ^ 2 * (n + 2 : ℝ))
    rw [← hcm]
    linarith only [hup, hupper]

theorem logCurvature_firstMoment_le (n : ℕ) :
    (n + 3 : ℝ) * (logCurvature n - 1 / (n + 3 : ℝ)) ≤
      1 / (n + 2 : ℝ) - 1 / (n + 3 : ℝ) := by
  have h := mul_le_mul_of_nonneg_left (logCurvature_centered_bounds n).2
    (show 0 ≤ (n + 3 : ℝ) by positivity)
  calc
    _ ≤ (n + 3 : ℝ) * (1 / ((n + 3 : ℝ) ^ 2 * (n + 2 : ℝ))) := h
    _ = _ := by field_simp; ring

theorem logCurvature_firstMoment_prefix_le (N : ℕ) :
    ∑ n ∈ Finset.range N, (n + 3 : ℝ) * (logCurvature n - 1 / (n + 3 : ℝ)) ≤
      1 / 2 - 1 / (N + 2 : ℝ) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
      rw [Finset.sum_range_succ]
      have h := logCurvature_firstMoment_le N
      simp only [Nat.cast_add, Nat.cast_one, add_assoc]
      norm_num only [show (1 : ℝ) + 2 = 3 by norm_num]
      linarith only [ih, h]

theorem summable_logCurvature_firstMoment :
    Summable (fun n : ℕ =>
      (n + 3 : ℝ) * (logCurvature n - 1 / (n + 3 : ℝ))) := by
  apply summable_of_sum_range_le
    (fun n => mul_nonneg (by positivity) (logCurvature_centered_bounds n).1)
    (c := 1 / 2)
  intro N
  exact (logCurvature_firstMoment_prefix_le N).trans (sub_le_self _ (by positivity))

private theorem firstMoment_secondDifference (s : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, (n + 3 : ℝ) * (s (n + 2) - 2 * s (n + 1) + s n)) =
      (N + 2 : ℝ) * (s (N + 1) - s N) - s N + 3 * s 0 - 2 * s 1 := by
  induction N with
  | zero => simp; ring
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [Nat.cast_add, Nat.cast_one, Nat.add_assoc]
      ring

theorem trivialCurvature_firstMoment_prefix (N : ℕ) :
    (∑ n ∈ Finset.range N, (n + 3 : ℝ) * trivialCurvature n) =
      (N + 2 : ℝ) *
        (trivialZeroSeriesReal (N + 3 : ℝ) - trivialZeroSeriesReal (N + 2 : ℝ)) -
      trivialZeroSeriesReal (N + 2 : ℝ) +
      3 * trivialZeroSeriesReal 2 - 2 * trivialZeroSeriesReal 3 := by
  have h := firstMoment_secondDifference (fun n => trivialZeroSeriesReal (n + 2 : ℝ)) N
  simpa only [trivialCurvature, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
    Nat.cast_zero, zero_add, show (1 : ℝ) + 2 = 3 by norm_num,
    add_assoc, show (2 : ℝ) + 2 = 4 by norm_num] using h

theorem trivialCurvature_firstMoment_prefix_le (N : ℕ) :
    (∑ n ∈ Finset.range N, (n + 3 : ℝ) * trivialCurvature n) ≤
      3 * trivialZeroSeriesReal 2 - 2 * trivialZeroSeriesReal 3 := by
  rw [trivialCurvature_firstMoment_prefix]
  have hanti := trivialZeroSeriesReal_anti
    (X := (N : ℝ) + 2) (Y := (N : ℝ) + 3)
    (by linarith [Nat.cast_nonneg (α := ℝ) N]) (by linarith)
  have hnonneg := trivialZeroSeriesReal_nonneg (X := (N : ℝ) + 2)
    (by linarith [Nat.cast_nonneg (α := ℝ) N])
  have hprod : (N + 2 : ℝ) *
      (trivialZeroSeriesReal (N + 3 : ℝ) - trivialZeroSeriesReal (N + 2 : ℝ)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr hanti)
  linarith only [hprod, hnonneg]

theorem summable_trivialCurvature_firstMoment :
    Summable (fun n : ℕ => (n + 3 : ℝ) * trivialCurvature n) := by
  exact summable_of_sum_range_le
    (fun n => mul_nonneg (by positivity) (trivialCurvature_bounds n).1)
    trivialCurvature_firstMoment_prefix_le

theorem scaledCurvature_centered_firstMoment_le (n : ℕ) :
    (n + 3 : ℝ) * |scaledCurvature n -
      (ArithmeticFunction.vonMangoldt (n + 3) - 1) / (n + 3 : ℝ)| ≤
        (n + 3 : ℝ) * trivialCurvature n +
          (n + 3 : ℝ) * (logCurvature n - 1 / (n + 3 : ℝ)) := by
  have heq : scaledCurvature n -
      (ArithmeticFunction.vonMangoldt (n + 3) - 1) / (n + 3 : ℝ) =
      trivialCurvature n - (logCurvature n - 1 / (n + 3 : ℝ)) := by
    rw [scaledCurvature_eq]
    ring
  rw [heq]
  have habs := abs_add_le (trivialCurvature n) (-(logCurvature n - 1 / (n + 3 : ℝ)))
  rw [abs_neg, abs_of_nonneg (trivialCurvature_bounds n).1,
    abs_of_nonneg (logCurvature_centered_bounds n).1] at habs
  simpa only [Pi.add_apply, mul_add, sub_eq_add_neg] using
    mul_le_mul_of_nonneg_left habs (show 0 ≤ (n + 3 : ℝ) by positivity)

/-- Native lag curvature differs from the centered Mangoldt source by a correction
with finite absolute first moment. No estimate of prime cancellation is assumed. -/
theorem summable_scaledCurvature_centered_firstMoment :
    Summable (fun n : ℕ => (n + 3 : ℝ) *
      |scaledCurvature n -
        (ArithmeticFunction.vonMangoldt (n + 3) - 1) / (n + 3 : ℝ)|) := by
  exact Summable.of_nonneg_of_le (fun n => by positivity)
    scaledCurvature_centered_firstMoment_le
    (summable_trivialCurvature_firstMoment.add summable_logCurvature_firstMoment)

/-- Explicit uniform budget for the full absolute first moment. -/
theorem tsum_scaledCurvature_centered_firstMoment_le_two :
    (∑' n : ℕ, (n + 3 : ℝ) * |scaledCurvature n -
      (ArithmeticFunction.vonMangoldt (n + 3) - 1) / (n + 3 : ℝ)|) ≤ 2 := by
  apply Real.tsum_le_of_sum_range_le (fun n => by positivity)
  intro N
  have hmajor := Finset.sum_le_sum (s := Finset.range N)
    (fun n _ => scaledCurvature_centered_firstMoment_le n)
  rw [Finset.sum_add_distrib] at hmajor
  have hlog := logCurvature_firstMoment_prefix_le N
  have htriv := trivialCurvature_firstMoment_prefix_le N
  have hS2 := trivialZeroSeriesReal_le_two_div_sq (X := 2) le_rfl
  have hS3 := trivialZeroSeriesReal_nonneg (X := 3) (by norm_num)
  have hinv : 0 ≤ 1 / (N + 2 : ℝ) := by positivity
  norm_num at hS2
  linarith only [hmajor, hlog, htriv, hS2, hS3, hinv]

end RHTower.IntegerLagCurvature
