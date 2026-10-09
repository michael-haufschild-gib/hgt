import GaloisForLFunctions.RHTower.WeilLagCurvatureFirstMoment

/-!
# Green regularization of native integer-lag curvature

A correction with finite absolute first moment changes the growing discrete
Green potential by an explicit linear slope and a bounded remainder. Applied
to native lag curvature, the remainder has absolute value at most two.
The reconstruction retains the centered Mangoldt source and the full affine
normalization. It does not establish the prime cancellation bound needed for RH.
-/

open Real Set Filter Topology
namespace RHTower.IntegerLagCurvature

private theorem summable_abs_of_firstMoment {e : ℕ → ℝ}
    (h : Summable (fun n : ℕ => (n + 3 : ℝ) * |e n|)) :
    Summable (fun n => |e n|) := by
  apply Summable.of_nonneg_of_le (fun n => abs_nonneg (e n)) _ h
  intro n
  calc
    |e n| = 1 * |e n| := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by linarith only [Nat.cast_nonneg (α := ℝ) n]) (abs_nonneg (e n))

/-- Finite absolute first moment controls endpoint-growing Green sums after the
limiting slope has been subtracted. -/
theorem abs_green_sub_linear_tsum_le_firstMoment {e : ℕ → ℝ}
    (h : Summable (fun n : ℕ => (n + 3 : ℝ) * |e n|)) (N : ℕ) :
    |(∑ n ∈ Finset.range N, ((N : ℝ) - n) * e n) - (N : ℝ) * ∑' n, e n| ≤
      ∑' n : ℕ, (n + 3 : ℝ) * |e n| := by
  have ha := summable_abs_of_firstMoment h
  have he : Summable e := Summable.of_norm ha
  have hat : Summable (fun n => |e (n + N)|) := (summable_nat_add_iff N).2 ha
  have hwt : Summable (fun n : ℕ => (n + N + 3 : ℝ) * |e (n + N)|) := by
    simpa only [Nat.cast_add] using (summable_nat_add_iff N).2 h
  have hid :
      (∑ n ∈ Finset.range N, ((N : ℝ) - n) * e n) - (N : ℝ) * ∑' n, e n =
        -((∑ n ∈ Finset.range N, (n : ℝ) * e n) +
          (N : ℝ) * ∑' n, e (n + N)) := by
    rw [← he.sum_add_tsum_nat_add N]
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  have hp : |∑ n ∈ Finset.range N, (n : ℝ) * e n| ≤
      ∑ n ∈ Finset.range N, (n + 3 : ℝ) * |e n| := by
    calc
      _ ≤ ∑ n ∈ Finset.range N, |(n : ℝ) * e n| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro n hn
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
        exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg (e n))
  have ht : |(N : ℝ) * ∑' n, e (n + N)| ≤
      ∑' n : ℕ, (n + N + 3 : ℝ) * |e (n + N)| := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg N)]
    calc
      _ ≤ (N : ℝ) * ∑' n, |e (n + N)| :=
        mul_le_mul_of_nonneg_left
          (by simpa only [Real.norm_eq_abs] using
            (norm_tsum_le_tsum_norm (f := fun n : ℕ => e (n + N)) hat))
          (Nat.cast_nonneg N)
      _ = ∑' n, (N : ℝ) * |e (n + N)| := (hat.tsum_mul_left (N : ℝ)).symm
      _ ≤ _ := (hat.mul_left (N : ℝ)).tsum_le_tsum
        (fun n => by
          exact mul_le_mul_of_nonneg_right
            (by linarith only [Nat.cast_nonneg (α := ℝ) n])
            (abs_nonneg (e (n + N)))) hwt
  rw [hid, abs_neg]
  calc
    _ ≤ |∑ n ∈ Finset.range N, (n : ℝ) * e n| +
        |(N : ℝ) * ∑' n, e (n + N)| := abs_add_le _ _
    _ ≤ (∑ n ∈ Finset.range N, (n + 3 : ℝ) * |e n|) +
        ∑' n : ℕ, (n + N + 3 : ℝ) * |e (n + N)| := add_le_add hp ht
    _ = _ := by simpa only [Nat.cast_add] using h.sum_add_tsum_nat_add N

/-- Complete non-prime correction to native curvature. -/
noncomputable def archCurvatureCorrection (n : ℕ) : ℝ :=
  scaledCurvature n -
    (ArithmeticFunction.vonMangoldt (n + 3) - 1) / (n + 3 : ℝ)

theorem archCurvatureCorrection_eq (n : ℕ) :
    archCurvatureCorrection n =
      trivialCurvature n - (logCurvature n - 1 / (n + 3 : ℝ)) := by
  rw [archCurvatureCorrection, scaledCurvature_eq]
  ring

theorem summable_archCurvatureCorrection_firstMoment :
    Summable (fun n : ℕ => (n + 3 : ℝ) * |archCurvatureCorrection n|) :=
  summable_scaledCurvature_centered_firstMoment

theorem summable_archCurvatureCorrection : Summable archCurvatureCorrection :=
  Summable.of_norm (summable_abs_of_firstMoment summable_archCurvatureCorrection_firstMoment)

/-- The native and centered-prime Green sums differ only by an explicit linear
slope and a uniformly bounded remainder. This isolates, but does not bound,
the prime cancellation required for RH. -/
theorem scaledCurvature_centered_green_bound (N : ℕ) :
    |(∑ n ∈ Finset.range N, ((N : ℝ) - n) * scaledCurvature n) -
      (∑ n ∈ Finset.range N, ((N : ℝ) - n) *
        ((ArithmeticFunction.vonMangoldt (n + 3) - 1) / (n + 3 : ℝ))) -
      (N : ℝ) * ∑' n, archCurvatureCorrection n| ≤
        ∑' n : ℕ, (n + 3 : ℝ) * |archCurvatureCorrection n| := by
  have h := abs_green_sub_linear_tsum_le_firstMoment
    summable_archCurvatureCorrection_firstMoment N
  simpa only [archCurvatureCorrection, mul_sub, Finset.sum_sub_distrib] using h

private theorem green_secondDifference (f : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, ((N : ℝ) - n) *
      (f (n + 2) - 2 * f (n + 1) + f n)) =
        f (N + 1) - f 1 - (N : ℝ) * (f 1 - f 0) := by
  let d (n : ℕ) := f (n + 2) - 2 * f (n + 1) + f n
  have hsum (N : ℕ) : (∑ n ∈ Finset.range N, d n) =
      f (N + 1) - f N - f 1 + f 0 := by
    induction N with
    | zero => simp
    | succ N ih =>
        rw [Finset.sum_range_succ, ih]
        dsimp [d]
        simp only [Nat.add_assoc]
        ring
  change (∑ n ∈ Finset.range N, ((N : ℝ) - n) * d n) = _
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      have hsplit :
          (∑ n ∈ Finset.range N, (((N + 1 : ℕ) : ℝ) - n) * d n) =
          (∑ n ∈ Finset.range N, ((N : ℝ) - n) * d n) +
            ∑ n ∈ Finset.range N, d n := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro n hn
        push_cast
        ring
      rw [hsplit, ih, hsum]
      dsimp [d]
      simp only [Nat.cast_add, Nat.cast_one, Nat.add_assoc]
      ring

/-- Exact Green reconstruction of the native scaled integer lag. -/
theorem scaledCurvature_green_eq (N : ℕ) :
    (∑ n ∈ Finset.range N, ((N : ℝ) - n) * scaledCurvature n) =
      Real.sqrt (N + 3 : ℕ) * integerLag (N + 3) - Real.sqrt 3 * integerLag 3 -
        (N : ℝ) * (Real.sqrt 3 * integerLag 3 - Real.sqrt 2 * integerLag 2) := by
  have h := green_secondDifference
    (fun n => Real.sqrt (n + 2 : ℕ) * integerLag (n + 2)) N
  simpa only [scaledCurvature, Nat.add_assoc, Nat.reduceAdd, Nat.cast_ofNat] using h

/-- Native lag equals the centered-prime Green expression, with its correct
affine normalization, up to a uniform absolute error of two. -/
theorem integerLag_centered_prime_green_bound (N : ℕ) :
    |Real.sqrt (N + 3 : ℕ) * integerLag (N + 3) -
      (Real.sqrt 3 * integerLag 3 +
        (N : ℝ) * (Real.sqrt 3 * integerLag 3 - Real.sqrt 2 * integerLag 2 +
          ∑' n, archCurvatureCorrection n) +
        ∑ n ∈ Finset.range N, ((N : ℝ) - n) *
          ((ArithmeticFunction.vonMangoldt (n + 3) - 1) / (n + 3 : ℝ)))| ≤
      2 := by
  have hbudget : (∑' n : ℕ, (n + 3 : ℝ) * |archCurvatureCorrection n|) ≤ 2 :=
    tsum_scaledCurvature_centered_firstMoment_le_two
  have h := (scaledCurvature_centered_green_bound N).trans hbudget
  rw [scaledCurvature_green_eq] at h
  convert h using 1
  congr 1
  ring

end RHTower.IntegerLagCurvature
