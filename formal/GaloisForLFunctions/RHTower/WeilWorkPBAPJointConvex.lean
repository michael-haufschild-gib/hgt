import GaloisForLFunctions.HTGeometry.CofinalConvexRecurrence
import GaloisForLFunctions.RHTower.CosineSeriesBohrEnvelope


/-!
# Exact finite cosine correction

Distinct nonzero frequencies, with no opposite pairs, have zero in the interior
of the convex hull of every time tail. If the all-negative vector lies in the
tail closure, every correction mass above one admits an exact finite positive
combination. The coefficients here are nonnegative; zero coefficients may be
deleted. This is the convex bridge for the PBAP joint phase construction, with
no assertion about frequency height or Weil energy.
-/

open Filter Topology MeasureTheory intervalIntegral
noncomputable section
namespace RHTower.WeilWorkPBAP

private theorem cosine_mean (a A : ℝ) :
    Tendsto (fun T : ℝ => (∫ t in A..T, Real.cos (a * t)) / T) atTop
      (𝓝 (if a = 0 then 1 else 0)) := by
  have h := (RHTower.tendsto_integral_cos_mul_div_eight a).sub
    ((tendsto_const_nhds (x := ∫ t in (8 : ℝ)..A, Real.cos (a * t))).div_atTop tendsto_id)
  simp only [sub_zero] at h
  convert h using 1
  funext T
  have he := intervalIntegral.integral_add_adjacent_intervals
    (a := (8 : ℝ)) (b := A) (c := T) (μ := volume)
    (f := fun t => Real.cos (a * t))
    ((by fun_prop : Continuous _).intervalIntegrable _ _)
    ((by fun_prop : Continuous _).intervalIntegrable _ _)
  rw [← he]
  simp only [id_eq]
  ring

private def phaseSum {k : ℕ} (a c : Fin k → ℝ) (t : ℝ) : ℝ :=
  ∑ i, c i * Real.cos (a i * t)

private theorem phaseSum_continuous {k : ℕ} (a c : Fin k → ℝ) :
    Continuous (phaseSum a c) := by
  unfold phaseSum
  fun_prop

private theorem phaseSum_mean {k : ℕ} (a c : Fin k → ℝ)
    (ha : ∀ i, a i ≠ 0) (A : ℝ) :
    Tendsto (fun T : ℝ => (∫ t in A..T, phaseSum a c t) / T) atTop (𝓝 0) := by
  have h := tendsto_finsetSum (s := Finset.univ) (fun i _ =>
    (tendsto_const_nhds (x := c i)).mul (cosine_mean (a i) A))
  simp only [ha, if_false, mul_zero, Finset.sum_const_zero] at h
  convert h using 1
  funext T
  simp only [phaseSum]
  rw [intervalIntegral.integral_finsetSum]
  · simp only [intervalIntegral.integral_const_mul, Finset.sum_div, mul_div_assoc]
  · intro i _
    exact (by fun_prop : Continuous _).intervalIntegrable _ _

private theorem cosine_product_mean (a b A : ℝ) :
    Tendsto (fun T : ℝ => (∫ t in A..T, Real.cos (a*t) * Real.cos (b*t)) / T)
      atTop (𝓝 (((if a+b=0 then 1 else 0) + (if a-b=0 then 1 else 0)) / 2)) := by
  have h := ((cosine_mean (a+b) A).add (cosine_mean (a-b) A)).div_const 2
  convert h using 1
  funext T
  have hp : (fun t => Real.cos (a*t) * Real.cos (b*t)) =
      (fun t => (Real.cos ((a+b)*t) + Real.cos ((a-b)*t)) / 2) := by
    funext t
    rw [add_mul, sub_mul, Real.cos_add, Real.cos_sub]
    ring
  rw [hp, intervalIntegral.integral_div, intervalIntegral.integral_add]
  · ring
  · exact (by fun_prop : Continuous _).intervalIntegrable _ _
  · exact (by fun_prop : Continuous _).intervalIntegrable _ _

private theorem phaseSum_product_mean {k : ℕ} (a c : Fin k → ℝ)
    (hinj : Function.Injective a)
    (hopp : ∀ i j, a i ≠ -a j) (j : Fin k) (A : ℝ) :
    Tendsto (fun T : ℝ => (∫ t in A..T, phaseSum a c t * Real.cos (a j*t)) / T)
      atTop (𝓝 (c j / 2)) := by
  have h := tendsto_finsetSum (s := Finset.univ) (fun i _ =>
    (tendsto_const_nhds (x := c i)).mul (cosine_product_mean (a i) (a j) A))
  have hsum : (∑ i, c i *
      (((if a i+a j=0 then 1 else 0) + (if a i-a j=0 then 1 else 0)) / 2)) = c j / 2 := by
    have hplus : ∀ i, a i+a j ≠ 0 := by intro i h; exact hopp i j (by linarith)
    simp only [hplus, if_false, zero_add, sub_eq_zero, hinj.eq_iff]
    simp only [mul_ite, mul_zero, ite_div, zero_div,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  rw [hsum] at h
  convert h using 1
  funext T
  simp only [phaseSum, Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum]
  · simp only [mul_assoc, intervalIntegral.integral_const_mul, Finset.sum_div, mul_div_assoc]
  · intro i _
    exact (by fun_prop : Continuous _).intervalIntegrable _ _

private theorem phaseSum_nonneg_tail_eq_zero {k : ℕ} (a c : Fin k → ℝ)
    (ha : ∀ i, a i ≠ 0) (hinj : Function.Injective a)
    (hopp : ∀ i j, a i ≠ -a j) (R : ℝ)
    (hn : ∀ t, R < t → 0 ≤ phaseSum a c t) : c = 0 := by
  let A := R + 1
  have hm := phaseSum_mean a c ha A
  have hc := phaseSum_continuous a c
  have hpc (j : Fin k) : Continuous (fun t => phaseSum a c t * Real.cos (a j*t)) :=
    hc.mul (by fun_prop)
  funext j
  have hp := phaseSum_product_mean a c hinj hopp j A
  have hupper : c j / 2 ≤ 0 := le_of_tendsto_of_tendsto hp hm (by
    filter_upwards [eventually_ge_atTop (max A 1)] with T hT
    have hAT : A ≤ T := le_trans (le_max_left _ _) hT
    have hT0 : 0 ≤ T := le_trans (by positivity : (0 : ℝ) ≤ 1)
      (le_trans (le_max_right _ _) hT)
    apply div_le_div_of_nonneg_right _ hT0
    apply intervalIntegral.integral_mono_on hAT
      ((hpc j).intervalIntegrable _ _) (hc.intervalIntegrable _ _)
    intro t ht
    exact mul_le_of_le_one_right (hn t (by dsimp [A] at ht; linarith [ht.1]))
      (Real.cos_le_one _))
  have hlower : -(c j / 2) ≤ 0 := le_of_tendsto_of_tendsto hp.neg hm (by
    filter_upwards [eventually_ge_atTop (max A 1)] with T hT
    have hAT : A ≤ T := le_trans (le_max_left _ _) hT
    have hT0 : 0 ≤ T := le_trans (by positivity : (0 : ℝ) ≤ 1)
      (le_trans (le_max_right _ _) hT)
    rw [← neg_div, ← intervalIntegral.integral_neg]
    apply div_le_div_of_nonneg_right _ hT0
    apply intervalIntegral.integral_mono_on hAT
      ((hpc j).neg.intervalIntegrable _ _) (hc.intervalIntegrable _ _)
    intro t ht
    have hnonneg := hn t (by dsimp [A] at ht; linarith [ht.1])
    have hcos := Real.neg_one_le_cos (a j*t)
    change -(phaseSum a c t * Real.cos (a j*t)) ≤ phaseSum a c t
    nlinarith)
  change c j = 0
  linarith

theorem phaseSum_negative_cofinally {k : ℕ} (a c : Fin k → ℝ)
    (ha : ∀ i, a i ≠ 0) (hinj : Function.Injective a)
    (hopp : ∀ i j, a i ≠ -a j) (hc : c ≠ 0) (R : ℝ) :
    ∃ t, R < t ∧ (∑ i, c i * Real.cos (a i*t)) < 0 := by
  by_contra hn
  push Not at hn
  exact hc (phaseSum_nonneg_tail_eq_zero a c ha hinj hopp R hn)

private theorem linearFunctional_coordinates {k : ℕ}
    (f : (Fin k → ℝ) →L[ℝ] ℝ) (x : Fin k → ℝ) :
    f x = ∑ j, x j * f (Pi.single j 1) := by
  classical
  have hx : x = ∑ j, x j • Pi.single j 1 := by
    funext i
    simp [Pi.single_apply, Finset.sum_ite_eq]
  calc f x = f (∑ j, x j • Pi.single j 1) := congrArg f hx
       _ = _ := by simp only [map_sum, map_smul, smul_eq_mul]

theorem zero_interior_cosine_tail {k : ℕ} (a : Fin k → ℝ)
    (ha : ∀ i, a i ≠ 0) (hinj : Function.Injective a)
    (hopp : ∀ i j, a i ≠ -a j) (R : ℝ) :
    (0 : Fin k → ℝ) ∈ interior (convexHull ℝ
      ((fun t i => Real.cos (a i*t)) '' Set.Ioi R)) := by
  apply GaloisForLFunctions.HTGeometry.zero_mem_interior_convexHull_image_Ioi
  intro f hf T
  have hc : (fun j => f (Pi.single j 1)) ≠ (0 : Fin k → ℝ) := by
    intro he
    apply hf
    ext x
    rw [linearFunctional_coordinates]
    simp only [funext_iff] at he
    simp [he]
  obtain ⟨t, ht, hn⟩ := phaseSum_negative_cofinally a
    (fun j => f (Pi.single j 1)) ha hinj hopp hc T
  refine ⟨t, ht, ?_⟩
  rwa [linearFunctional_coordinates, show
    (∑ j, Real.cos (a j*t) * f (Pi.single j 1)) =
    ∑ j, f (Pi.single j 1) * Real.cos (a j*t) by
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _]

/-- A limiting all-negative phase can be corrected exactly with any mass above one. -/
theorem exists_exact_positive_cosine_correction {k : ℕ} (a : Fin k → ℝ)
    (ha : ∀ i, a i ≠ 0) (hinj : Function.Injective a)
    (hopp : ∀ i j, a i ≠ -a j) (R M : ℝ) (hM : 1 < M)
    (hz : (fun _ : Fin k => (-1 : ℝ)) ∈ closure
      ((fun t i => Real.cos (a i*t)) '' Set.Ioi R)) :
    ∃ (ι : Type) (_ : Fintype ι) (w t : ι → ℝ),
      (Fintype.card ι ≤ k+1) ∧ (∀ i, 0 < w i) ∧ (∀ i, R < t i) ∧ (∑ i, w i) = M ∧
      ∀ j, (∑ i, w i * Real.cos (a j*t i)) = -1 := by
  classical
  let C := convexHull ℝ ((fun t i => Real.cos (a i*t)) '' Set.Ioi R)
  have h0 : (0 : Fin k → ℝ) ∈ interior C := zero_interior_cosine_tail a ha hinj hopp R
  have hzC : (fun _ : Fin k => (-1 : ℝ)) ∈ closure C :=
    closure_mono (subset_convexHull ℝ _) hz
  have hM0 : 0 < M := lt_trans zero_lt_one hM
  have hi0 : 0 < M⁻¹ := inv_pos.mpr hM0
  have hi1 : M⁻¹ < 1 := (inv_lt_one₀ hM0).mpr hM
  have ht : (fun _ : Fin k => -M⁻¹) ∈ C := by
    have h := (convex_convexHull ℝ _).combo_interior_closure_mem_interior h0 hzC
      (show 0 < 1-M⁻¹ by linarith) hi0.le (by ring : 1-M⁻¹+M⁻¹=1)
    apply interior_subset at h
    simp only [smul_zero, zero_add] at h
    have he : M⁻¹ • (fun _ : Fin k => (-1 : ℝ)) = (fun _ : Fin k => -M⁻¹) := by
      funext j
      simp only [Pi.smul_apply, smul_eq_mul, mul_neg_one]
    rwa [he] at h
  obtain ⟨ι, hi, z, w, hzmem, hai, hw, hsum, hzw⟩ := eq_pos_convex_span_of_mem_convexHull ht
  letI : Fintype ι := hi
  have hcard : Fintype.card ι ≤ k+1 := by
    have h := le_trans hai.card_le_finrank_succ (Nat.add_le_add_right (Submodule.finrank_le _) 1)
    simpa using h
  choose t ht hzval using (fun i => hzmem ⟨i, rfl⟩)
  refine ⟨ι, hi, (fun i => M*w i), t, hcard, (fun i => mul_pos hM0 (hw i)),
    ht, ?_, ?_⟩
  · rw [← Finset.mul_sum, hsum, mul_one]
  · intro j
    have he := congrFun hzw j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at he
    have het : (∑ i, w i * Real.cos (a j*t i)) = -M⁻¹ := by
      convert he using 1
      exact Finset.sum_congr rfl fun i _ => congrArg (fun v => w i*v j) (hzval i)
    simp only [mul_assoc, ← Finset.mul_sum, het]
    rw [mul_neg, mul_inv_cancel₀ hM0.ne']

/-- The nonnegative-weight interface for exact cosine correction. -/
theorem exists_exact_cosine_correction {k : ℕ} (a : Fin k → ℝ)
    (ha : ∀ i, a i ≠ 0) (hinj : Function.Injective a)
    (hopp : ∀ i j, a i ≠ -a j) (R M : ℝ) (hM : 1 < M)
    (hz : (fun _ : Fin k => (-1 : ℝ)) ∈ closure
      ((fun t i => Real.cos (a i*t)) '' Set.Ioi R)) :
    ∃ (ι : Type) (_ : Fintype ι) (w t : ι → ℝ),
      (∀ i, 0 ≤ w i) ∧ (∀ i, R < t i) ∧ (∑ i, w i) = M ∧
      ∀ j, (∑ i, w i * Real.cos (a j*t i)) = -1 := by
  obtain ⟨ι, hi, w, t, _, hw, ht, hsum, hcos⟩ :=
    exists_exact_positive_cosine_correction a ha hinj hopp R M hM hz
  exact ⟨ι, hi, w, t, (fun i => (hw i).le), ht, hsum, hcos⟩

end RHTower.WeilWorkPBAP
