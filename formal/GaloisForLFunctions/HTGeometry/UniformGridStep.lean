import GaloisForLFunctions.HTGeometry.IntervalPoincare

/-!
# Uniform grids and their step functions

A uniform grid of `M` cells of mesh `h` starting at `a` cuts `(a, a + Mh]` into the half-open cells
`(a + jh, a + (j+1)h]`.  The left-endpoint step function of `f` on that grid is the finite
combination

`Σ_{j < M} f(a + jh)·1_{(a+jh, a+(j+1)h]}`,

which is constant on every cell and vanishes off the grid.  An interval integral telescopes over the
grid, so a global estimate on `(a, a+Mh]` is the sum of the cell estimates.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

/-- The `j`-th cell of the uniform grid of mesh `h` starting at `a`. -/
def gridCell (a h : ℝ) (j : ℕ) : Set ℝ := Set.Ioc (a + j * h) (a + (j + 1) * h)

theorem measurableSet_gridCell (a h : ℝ) (j : ℕ) : MeasurableSet (gridCell a h j) :=
  measurableSet_Ioc

theorem gridCell_subset {a h : ℝ} (hh : 0 ≤ h) {M j : ℕ} (hj : j < M) :
    gridCell a h j ⊆ Set.Ioc a (a + M * h) := by
  intro x hx
  obtain ⟨hx1, hx2⟩ := hx
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hjM : ((j : ℝ) + 1) ≤ (M : ℝ) := by
    have : (j : ℝ) + 1 ≤ (M : ℝ) := by exact_mod_cast hj
    exact this
  constructor
  · nlinarith
  · nlinarith

theorem gridCell_disjoint {a h : ℝ} (hh : 0 < h) {j k : ℕ} (hjk : j ≠ k) {x : ℝ}
    (hxj : x ∈ gridCell a h j) (hxk : x ∈ gridCell a h k) : False := by
  obtain ⟨hj1, hj2⟩ := hxj
  obtain ⟨hk1, hk2⟩ := hxk
  rcases Nat.lt_or_ge j k with hlt | hge
  · have hcast : ((j : ℝ) + 1) ≤ (k : ℝ) := by exact_mod_cast hlt
    nlinarith
  · have hlt : k < j := by omega
    have hcast : ((k : ℝ) + 1) ≤ (j : ℝ) := by exact_mod_cast hlt
    nlinarith

/-- The left-endpoint step function of `f` on the uniform grid. -/
noncomputable def gridStep (f : ℝ → ℝ) (a h : ℝ) (M : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range M, f (a + j * h) * (gridCell a h j).indicator 1 x

theorem gridStep_eq_of_mem {f : ℝ → ℝ} {a h : ℝ} (hh : 0 < h) {M j : ℕ}
    (hj : j ∈ Finset.range M) {x : ℝ} (hx : x ∈ gridCell a h j) :
    gridStep f a h M x = f (a + j * h) := by
  rw [gridStep, Finset.sum_eq_single j]
  · rw [Set.indicator_of_mem hx]
    simp
  · intro k _ hkj
    rw [Set.indicator_of_notMem (fun hxk => gridCell_disjoint hh (Ne.symm hkj) hx hxk)]
    simp
  · intro hcon
    exact absurd hj hcon

theorem gridStep_eq_zero {f : ℝ → ℝ} {a h : ℝ} (hh : 0 ≤ h) {M : ℕ} {x : ℝ}
    (hx : x ∉ Set.Ioc a (a + M * h)) : gridStep f a h M x = 0 := by
  rw [gridStep]
  refine Finset.sum_eq_zero fun j hj => ?_
  simp only [Finset.mem_range] at hj
  rw [Set.indicator_of_notMem (fun hxj => hx (gridCell_subset hh hj hxj))]
  simp

theorem measurable_gridStep (f : ℝ → ℝ) (a h : ℝ) (M : ℕ) :
    Measurable (gridStep f a h M) := by
  refine Finset.measurable_sum _ fun j _ => ?_
  refine measurable_const.mul ?_
  exact (measurable_indicator_const_iff (1 : ℝ)).2 (measurableSet_gridCell a h j)

/-- **Telescoping over a uniform grid.** -/
theorem integral_grid_sum {F : ℝ → ℝ} {a h : ℝ} (hh : 0 ≤ h) :
    ∀ (M : ℕ), IntervalIntegrable F volume a (a + M * h) →
      (∫ x in a..(a + M * h), F x)
        = ∑ j ∈ Finset.range M, ∫ x in (a + j * h)..(a + (j + 1) * h), F x := by
  intro M
  induction M with
  | zero =>
    intro _
    simp
  | succ M ih =>
    intro hF
    have hmono : Set.uIcc a (a + M * h) ⊆ Set.uIcc a (a + (M + 1 : ℕ) * h) := by
      have h1 : a ≤ a + (M : ℝ) * h := by
        have : (0 : ℝ) ≤ (M : ℝ) * h := mul_nonneg (Nat.cast_nonneg M) hh
        linarith
      have h2 : a + (M : ℝ) * h ≤ a + ((M : ℝ) + 1) * h := by nlinarith
      have h3 : a ≤ a + ((M : ℝ) + 1) * h := by linarith
      rw [Set.uIcc_of_le h1, show ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 by push_cast; ring,
        Set.uIcc_of_le h3]
      exact Set.Icc_subset_Icc le_rfl h2
    have hF1 : IntervalIntegrable F volume a (a + (M : ℝ) * h) := hF.mono_set hmono
    have hsub : Set.uIcc (a + (M : ℝ) * h) (a + ((M : ℝ) + 1) * h)
        ⊆ Set.uIcc a (a + ((M : ℝ) + 1) * h) := by
      have h1 : a ≤ a + (M : ℝ) * h := by
        have : (0 : ℝ) ≤ (M : ℝ) * h := mul_nonneg (Nat.cast_nonneg M) hh
        linarith
      have h2 : a + (M : ℝ) * h ≤ a + ((M : ℝ) + 1) * h := by nlinarith
      have h3 : a ≤ a + ((M : ℝ) + 1) * h := by linarith
      rw [Set.uIcc_of_le h2, Set.uIcc_of_le h3]
      exact Set.Icc_subset_Icc h1 le_rfl
    have hFcast : IntervalIntegrable F volume a (a + ((M : ℝ) + 1) * h) := by
      rw [show ((M : ℝ) + 1) * h = ((M + 1 : ℕ) : ℝ) * h by push_cast; ring]
      exact hF
    have hF2 : IntervalIntegrable F volume (a + (M : ℝ) * h) (a + ((M : ℝ) + 1) * h) :=
      hFcast.mono_set hsub
    have hadd := intervalIntegral.integral_add_adjacent_intervals hF1 hF2
    rw [show ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 by push_cast; ring, ← hadd, ih hF1,
      Finset.sum_range_succ]


theorem abs_gridStep_le (f : ℝ → ℝ) (a h : ℝ) (M : ℕ) (x : ℝ) :
    |gridStep f a h M x| ≤ ∑ j ∈ Finset.range M, |f (a + j * h)| := by
  rw [gridStep]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine Finset.sum_le_sum fun j _ => ?_
  rw [abs_mul]
  have h1 : |(gridCell a h j).indicator (1 : ℝ → ℝ) x| ≤ 1 := by
    by_cases hx : x ∈ gridCell a h j
    · rw [Set.indicator_of_mem hx]
      simp
    · rw [Set.indicator_of_notMem hx]
      simp
  nlinarith [abs_nonneg (f (a + (j : ℝ) * h))]

/-- **The grid approximation estimate.**  A differentiable function differs from its left-endpoint
step function on a uniform grid by at most the mesh times the `L²` norm of its derivative. -/
theorem integral_sub_gridStep_sq_le {f f' : ℝ → ℝ} {a h : ℝ} (hh : 0 < h) (M : ℕ)
    (hderiv : ∀ x : ℝ, HasDerivAt f (f' x) x) (hf'c : Continuous f') :
    (∫ x in Set.Ioc a (a + M * h), (f x - gridStep f a h M x) ^ (2 : ℕ))
      ≤ h ^ (2 : ℕ) * ∫ x in Set.Ioc a (a + M * h), f' x ^ (2 : ℕ) := by
  have hfc : Continuous f := by
    refine continuous_iff_continuousAt.2 fun x => ?_
    exact (hderiv x).continuousAt
  have hMh : (0 : ℝ) ≤ (M : ℝ) * h := mul_nonneg (Nat.cast_nonneg M) hh.le
  have hab : a ≤ a + (M : ℝ) * h := by linarith
  -- integrability of the squared error on the whole grid
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ x ∈ Set.Icc a (a + (M : ℝ) * h), ‖f x‖ ≤ B :=
    (isCompact_Icc (a := a) (b := a + (M : ℝ) * h)).exists_bound_of_continuousOn
      hfc.continuousOn
  have hVbound : ∀ x : ℝ, |gridStep f a h M x| ≤ ∑ j ∈ Finset.range M, |f (a + j * h)| :=
    abs_gridStep_le f a h M
  have hmeasfun : Measurable (fun x : ℝ => (f x - gridStep f a h M x) ^ (2 : ℕ)) :=
    (hfc.measurable.sub (measurable_gridStep f a h M)).pow_const 2
  have hmeas : AEStronglyMeasurable (fun x : ℝ => (f x - gridStep f a h M x) ^ (2 : ℕ)) volume :=
    hmeasfun.aestronglyMeasurable
  have hint : IntegrableOn (fun x : ℝ => (f x - gridStep f a h M x) ^ (2 : ℕ))
      (Set.Ioc a (a + (M : ℝ) * h)) volume := by
    refine MeasureTheory.Measure.integrableOn_of_bounded (M :=
      (B + ∑ j ∈ Finset.range M, |f (a + j * h)|) ^ (2 : ℕ)) measure_Ioc_lt_top.ne hmeas ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
    have hx' : x ∈ Set.Icc a (a + (M : ℝ) * h) := Set.Ioc_subset_Icc_self hx
    have h1 : |f x| ≤ B := by
      have := hB x hx'
      rwa [Real.norm_eq_abs] at this
    have h2 := hVbound x
    have hsum : (0 : ℝ) ≤ ∑ j ∈ Finset.range M, |f (a + j * h)| :=
      Finset.sum_nonneg fun j _ => abs_nonneg _
    have habs : |f x - gridStep f a h M x| ≤ B + ∑ j ∈ Finset.range M, |f (a + j * h)| := by
      have hsplit : |f x - gridStep f a h M x| ≤ |f x| + |gridStep f a h M x| := by
        have := abs_add_le (f x) (-(gridStep f a h M x))
        rw [abs_neg] at this
        simpa [sub_eq_add_neg] using this
      linarith
    have hd : (f x - gridStep f a h M x) ^ (2 : ℕ) = |f x - gridStep f a h M x| ^ (2 : ℕ) :=
      (sq_abs _).symm
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), hd]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  have hintervalErr : IntervalIntegrable (fun x : ℝ => (f x - gridStep f a h M x) ^ (2 : ℕ))
      volume a (a + (M : ℝ) * h) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact hint
  have hintervalD : IntervalIntegrable (fun x : ℝ => f' x ^ (2 : ℕ)) volume a (a + (M : ℝ) * h) :=
    ((hf'c.pow 2).intervalIntegrable _ _)
  rw [← intervalIntegral.integral_of_le hab, ← intervalIntegral.integral_of_le hab,
    integral_grid_sum hh.le M hintervalErr, integral_grid_sum hh.le M hintervalD,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  have hle : a + (j : ℝ) * h ≤ a + ((j : ℝ) + 1) * h := by nlinarith
  have hlen : (a + ((j : ℝ) + 1) * h) - (a + (j : ℝ) * h) = h := by ring
  have hcongr : ∀ x ∈ Set.Ioc (a + (j : ℝ) * h) (a + ((j : ℝ) + 1) * h),
      (f x - gridStep f a h M x) ^ (2 : ℕ) = (f x - f (a + (j : ℝ) * h)) ^ (2 : ℕ) := by
    intro x hx
    rw [gridStep_eq_of_mem hh hj (show x ∈ gridCell a h j from hx)]
  rw [intervalIntegral.integral_of_le hle, intervalIntegral.integral_of_le hle,
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioc hcongr]
  have hpoin := integral_sub_left_sq_le_of_hasDerivAt hle hderiv
    (hf'c.intervalIntegrable _ _) ((hf'c.pow 2).intervalIntegrable _ _)
    (((hfc.sub continuous_const).pow 2).integrableOn_Ioc)
  rw [hlen] at hpoin
  exact hpoin

end GaloisForLFunctions.HTGeometry
