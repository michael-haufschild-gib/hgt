import GaloisForLFunctions.HTGeometry.MonotoneRiemannSum

/-!
# Complex bounded-variation Riemann sums

This file supplies the metric-space form of the first-order quadrature estimate needed by
compactly supported multiplicative prime windows.  Unlike the real Jordan-decomposition lemma in
`MonotoneRiemannSum`, the proof works directly for complex-valued functions: on each mesh cell the
right-endpoint error is the integral of `g(right) - g(u)`, and total variation controls that
difference.  Additivity of `eVariationOn` across adjacent closed intervals then gives the global
`1 / k` bound.
-/

open Finset MeasureTheory intervalIntegral Set

namespace HTGeometry

/-- The right-endpoint quadrature error on one interval is bounded by its length times the total
variation on that interval.  This is the complex-valued cell estimate used by BV prime windows. -/
theorem norm_rightEndpoint_sub_integral_le_eVariationOn
    {g : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hint : IntervalIntegrable g volume a b)
    (hvar : BoundedVariationOn g (Icc a b)) :
    ‖(b - a) • g b - ∫ u in a..b, g u‖ ≤
      (b - a) * (eVariationOn g (Icc a b)).toReal := by
  have hpoint : ∀ u ∈ Icc a b,
      ‖g b - g u‖ ≤ (eVariationOn g (Icc a b)).toReal := by
    intro u hu
    simpa only [dist_eq_norm] using hvar.dist_le (⟨hab, le_rfl⟩ : b ∈ Icc a b) hu
  calc
    ‖(b - a) • g b - ∫ u in a..b, g u‖ =
        ‖∫ u in a..b, (g b - g u)‖ := by
          rw [intervalIntegral.integral_sub (f := fun _ : ℝ ↦ g b) (g := g)
            intervalIntegrable_const hint, intervalIntegral.integral_const]
    _ ≤ (eVariationOn g (Icc a b)).toReal * |b - a| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const_ae
      filter_upwards with u
      intro hu
      apply hpoint u
      have hu' : u ∈ uIcc a b := uIoc_subset_uIcc hu
      simpa only [uIcc_of_le hab] using hu'
    _ = (b - a) * (eVariationOn g (Icc a b)).toReal := by
      rw [abs_of_nonneg (sub_nonneg.mpr hab)]
      ring

/-- A right-endpoint Riemann sum with mesh `1 / k` approximates a complex BV integrand with error
at most `k⁻¹` times its total variation.  No scalar Jordan decomposition is assumed: the proof
uses the metric total variation of the complex-valued function itself. -/
theorem norm_rightEndpoint_riemannSum_sub_integral_le_eVariationOn
    {g : ℝ → ℂ} {k : ℝ} (hk : 0 < k) {n : ℕ}
    (hint : IntervalIntegrable g volume 0 (n / k))
    (hvar : BoundedVariationOn g (Icc 0 (n / k))) :
    ‖(1 / k) • (∑ i ∈ Finset.range n, g ((i + 1) / k)) -
        ∫ u in 0..n / k, g u‖ ≤
      (1 / k) * (eVariationOn g (Icc 0 (n / k))).toReal := by
  let I : ℕ → ℝ := fun i ↦ i / k
  have hk0 : k ≠ 0 := hk.ne'
  have hI : Monotone I := by
    intro i j hij
    dsimp only [I]
    exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hij) hk.le
  have hIn : I n = n / k := rfl
  have hI0 : I 0 = 0 := by simp [I]
  have hcell_subset (i : ℕ) (hi : i < n) :
      Icc (I i) (I (i + 1)) ⊆ Icc 0 (n / k) := by
    intro x hx
    refine ⟨?_, ?_⟩
    · exact (show 0 = I 0 by symm; exact hI0).trans_le ((hI (Nat.zero_le i)).trans hx.1)
    · exact hx.2.trans (hI (by omega : i + 1 ≤ n))
  have hcell_int (i : ℕ) (hi : i < n) :
      IntervalIntegrable g volume (I i) (I (i + 1)) := by
    apply hint.mono_set
    intro x hx
    rw [Set.uIcc_of_le (hI (Nat.le_succ i))] at hx
    rw [Set.uIcc_of_le (by simpa only [hI0, hIn] using hI (Nat.zero_le n))]
    exact hcell_subset i hi hx
  have hcell_var (i : ℕ) (hi : i < n) :
      BoundedVariationOn g (Icc (I i) (I (i + 1))) :=
    hvar.mono (hcell_subset i hi)
  have hstep (i : ℕ) : I (i + 1) - I i = 1 / k := by
    dsimp only [I]
    field_simp [hk0]
    norm_num
  have hcell_bound (i : ℕ) (hi : i ∈ Finset.range n) :
      ‖(1 / k) • g (I (i + 1)) - ∫ u in I i..I (i + 1), g u‖ ≤
        (1 / k) * (eVariationOn g (Icc (I i) (I (i + 1)))).toReal := by
    rw [← hstep i]
    exact norm_rightEndpoint_sub_integral_le_eVariationOn (hI (Nat.le_succ i))
      (hcell_int i (Finset.mem_range.mp hi)) (hcell_var i (Finset.mem_range.mp hi))
  have hsum_int :
      (∑ i ∈ Finset.range n, ∫ u in I i..I (i + 1), g u) = ∫ u in 0..n / k, g u := by
    rw [intervalIntegral.sum_integral_adjacent_intervals
      (fun i hi ↦ hcell_int i hi), hI0, hIn]
  have hsum_var :
      (∑ i ∈ Finset.range n, (eVariationOn g (Icc (I i) (I (i + 1)))).toReal) =
        (eVariationOn g (Icc 0 (n / k))).toReal := by
    rw [← ENNReal.toReal_sum (fun i hi ↦ (hcell_var i (Finset.mem_range.mp hi))),
      eVariationOn.sum' g hI, hI0, hIn]
  calc
    ‖(1 / k) • (∑ i ∈ Finset.range n, g ((i + 1) / k)) -
        ∫ u in 0..n / k, g u‖ =
        ‖∑ i ∈ Finset.range n,
          ((1 / k) • g (I (i + 1)) - ∫ u in I i..I (i + 1), g u)‖ := by
      rw [Finset.sum_sub_distrib, hsum_int, Finset.smul_sum]
      simp only [I, Nat.cast_add, Nat.cast_one]
    _ ≤ ∑ i ∈ Finset.range n,
        ‖(1 / k) • g (I (i + 1)) - ∫ u in I i..I (i + 1), g u‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range n,
        (1 / k) * (eVariationOn g (Icc (I i) (I (i + 1)))).toReal :=
      Finset.sum_le_sum hcell_bound
    _ = (1 / k) * (eVariationOn g (Icc 0 (n / k))).toReal := by
      rw [← Finset.mul_sum, hsum_var]

end HTGeometry

namespace HTGeometry

open scoped NNReal ENNReal

/-- Multiplying a BV function by a bounded Lipschitz function preserves bounded variation, with an
explicit variation bound.  The estimate is stated for complex-valued functions on a compact real
interval because this is the exact form used by Mellin weights. -/
theorem eVariationOn_mul_le_of_norm_le_of_lipschitzOn
    {f h : ℝ → ℂ} {a b Mf Mh : ℝ} {C : ℝ≥0} (hab : a ≤ b)
    (hfvar : BoundedVariationOn f (Set.Icc a b))
    (hMf : 0 ≤ Mf) (hMh : 0 ≤ Mh)
    (hfnorm : ∀ x ∈ Set.Icc a b, ‖f x‖ ≤ Mf)
    (hhnorm : ∀ x ∈ Set.Icc a b, ‖h x‖ ≤ Mh)
    (hhlip : LipschitzOnWith C h (Set.Icc a b)) :
    eVariationOn (fun x => f x * h x) (Set.Icc a b) ≤
      ENNReal.ofReal
        (Mh * (eVariationOn f (Set.Icc a b)).toReal + Mf * (C : ℝ) * (b - a)) := by
  apply iSup_le
  rintro ⟨n, u, hu, us⟩
  have hfSum :
      (∑ i ∈ Finset.range n, dist (f (u (i + 1))) (f (u i))) ≤
        (eVariationOn f (Set.Icc a b)).toReal := by
    have h := eVariationOn.sum_le (f := f) hu us (n := n)
    have hfinite : ∀ i ∈ Finset.range n,
        edist (f (u (i + 1))) (f (u i)) ≠ ∞ := by
      intro i hi
      exact edist_ne_top _ _
    have h' := ENNReal.toReal_mono hfvar h
    rw [ENNReal.toReal_sum hfinite] at h'
    simpa only [edist_dist, ENNReal.toReal_ofReal dist_nonneg] using h'
  have hhSum :
      (∑ i ∈ Finset.range n, dist (h (u (i + 1))) (h (u i))) ≤
        (C : ℝ) * (b - a) := by
    calc
      (∑ i ∈ Finset.range n, dist (h (u (i + 1))) (h (u i))) ≤
          ∑ i ∈ Finset.range n, (C : ℝ) * dist (u (i + 1)) (u i) := by
        apply Finset.sum_le_sum
        intro i hi
        exact hhlip.dist_le_mul _ (us (i + 1)) _ (us i)
      _ = (C : ℝ) * ∑ i ∈ Finset.range n, (u (i + 1) - u i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (hu (Nat.le_succ i)))]
      _ = (C : ℝ) * (u n - u 0) := by
        rw [Finset.sum_range_sub]
      _ ≤ (C : ℝ) * (b - a) := by
        apply mul_le_mul_of_nonneg_left _ C.coe_nonneg
        exact sub_le_sub (us n).2 (us 0).1
  have hterm (i : ℕ) (hi : i ∈ Finset.range n) :
      dist (f (u (i + 1)) * h (u (i + 1))) (f (u i) * h (u i)) ≤
        Mh * dist (f (u (i + 1))) (f (u i)) +
          Mf * dist (h (u (i + 1))) (h (u i)) := by
    rw [dist_eq_norm, dist_eq_norm, dist_eq_norm]
    calc
      ‖f (u (i + 1)) * h (u (i + 1)) - f (u i) * h (u i)‖ =
          ‖h (u (i + 1)) * (f (u (i + 1)) - f (u i)) +
            f (u i) * (h (u (i + 1)) - h (u i))‖ := by
        congr 1
        ring
      _ ≤ ‖h (u (i + 1))‖ * ‖f (u (i + 1)) - f (u i)‖ +
          ‖f (u i)‖ * ‖h (u (i + 1)) - h (u i)‖ := by
        exact (norm_add_le _ _).trans_eq (by rw [norm_mul, norm_mul])
      _ ≤ Mh * ‖f (u (i + 1)) - f (u i)‖ +
          Mf * ‖h (u (i + 1)) - h (u i)‖ := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right (hhnorm _ (us (i + 1))) (norm_nonneg _))
          (mul_le_mul_of_nonneg_right (hfnorm _ (us i)) (norm_nonneg _))
  rw [show (∑ i ∈ Finset.range n,
      edist (f (u (i + 1)) * h (u (i + 1))) (f (u i) * h (u i))) =
      ENNReal.ofReal (∑ i ∈ Finset.range n,
        dist (f (u (i + 1)) * h (u (i + 1))) (f (u i) * h (u i))) by
        rw [ENNReal.ofReal_sum_of_nonneg]
        · simp only [edist_dist]
        · intro i hi
          exact dist_nonneg]
  apply ENNReal.ofReal_le_ofReal
  calc
    (∑ i ∈ Finset.range n,
        dist (f (u (i + 1)) * h (u (i + 1))) (f (u i) * h (u i))) ≤
      ∑ i ∈ Finset.range n,
        (Mh * dist (f (u (i + 1))) (f (u i)) +
          Mf * dist (h (u (i + 1))) (h (u i))) :=
      Finset.sum_le_sum hterm
    _ = Mh * (∑ i ∈ Finset.range n, dist (f (u (i + 1))) (f (u i))) +
        Mf * (∑ i ∈ Finset.range n, dist (h (u (i + 1))) (h (u i))) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ Mh * (eVariationOn f (Set.Icc a b)).toReal +
        Mf * ((C : ℝ) * (b - a)) :=
      add_le_add (mul_le_mul_of_nonneg_left hfSum hMh)
        (mul_le_mul_of_nonneg_left hhSum hMf)
    _ = Mh * (eVariationOn f (Set.Icc a b)).toReal +
        Mf * (C : ℝ) * (b - a) := by ring

/-- Concrete bounded-variation closure under multiplication by a bounded Lipschitz factor. -/
theorem BoundedVariationOn.mul_of_norm_le_of_lipschitzOn
    {f h : ℝ → ℂ} {a b Mf Mh : ℝ} {C : ℝ≥0} (hab : a ≤ b)
    (hfvar : BoundedVariationOn f (Set.Icc a b))
    (hMf : 0 ≤ Mf) (hMh : 0 ≤ Mh)
    (hfnorm : ∀ x ∈ Set.Icc a b, ‖f x‖ ≤ Mf)
    (hhnorm : ∀ x ∈ Set.Icc a b, ‖h x‖ ≤ Mh)
    (hhlip : LipschitzOnWith C h (Set.Icc a b)) :
    BoundedVariationOn (fun x => f x * h x) (Set.Icc a b) :=
  ne_top_of_le_ne_top (by simp) <|
    eVariationOn_mul_le_of_norm_le_of_lipschitzOn hab hfvar hMf hMh hfnorm hhnorm hhlip

end HTGeometry
