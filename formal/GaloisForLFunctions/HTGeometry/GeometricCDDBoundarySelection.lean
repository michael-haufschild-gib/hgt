import GaloisForLFunctions.HTGeometry.GeometricCDDConstraint

/-!
# Contractive boundary selection for geometric CDD delays

The logarithmic-energy slope of a finite geometric CDD phase is a sum of rational one-shell
delays.  Scaling the energy by `q` removes the lowest shell.  This module proves the exact finite
constraint and the boundary-selection theorem behind the infinite physical solution:

if `0 ≤ q < 1`, a continuous `q`-invariant defect that vanishes at the contracting endpoint is
identically zero.  Hence a common affine scale constraint and a common endpoint value determine at
most one continuous response.

No infinite-product convergence, hypertranscendence theorem, elliptic identification, or QFT
reconstruction is claimed here.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- The positive logarithmic-energy delay contributed by one reality-paired CDD shell. -/
noncomputable def geometricCDDLogShellDelay (x : ℝ) : ℝ :=
  4 * x / (1 + x ^ 2)

/-- Finite logarithmic-energy phase delay through shells `0,...,N-1`. -/
noncomputable def geometricCDDLogPhaseSlope
    (q x : ℝ) (N : ℕ) : ℝ :=
  4 * ∑ k ∈ Finset.range N, (q ^ k * x) / (1 + (q ^ k * x) ^ 2)

@[simp]
theorem geometricCDDLogPhaseSlope_zero (q x : ℝ) :
    geometricCDDLogPhaseSlope q x 0 = 0 := by
  simp [geometricCDDLogPhaseSlope]

/-- **Finite one-shell constraint.**  Scaling by `q` shifts every old shell and leaves exactly the
scale-zero boundary delay. -/
theorem geometricCDDLogPhaseSlope_succ_constraint
    (q x : ℝ) (N : ℕ) :
    geometricCDDLogPhaseSlope q x (N + 1) =
      geometricCDDLogShellDelay x +
        geometricCDDLogPhaseSlope q (q * x) N := by
  unfold geometricCDDLogPhaseSlope geometricCDDLogShellDelay
  rw [Finset.sum_range_succ']
  simp only [pow_zero, one_mul]
  have hshift :
      (∑ k ∈ Finset.range N, q ^ (k + 1) * x / (1 + (q ^ (k + 1) * x) ^ 2)) =
        ∑ k ∈ Finset.range N,
          q ^ k * (q * x) / (1 + (q ^ k * (q * x)) ^ 2) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [pow_succ]
    ring
  rw [hshift]
  ring

/-- Every nonempty finite shell tower has strictly positive logarithmic-energy delay at positive
energy. -/
theorem geometricCDDLogPhaseSlope_pos
    {q x : ℝ} (hq : 0 < q) (hx : 0 < x) (N : ℕ) :
    0 < geometricCDDLogPhaseSlope q x (N + 1) := by
  unfold geometricCDDLogPhaseSlope
  apply mul_pos (by norm_num)
  apply Finset.sum_pos
  · intro k hk
    apply div_pos
    · exact mul_pos (pow_pos hq k) hx
    · positivity
  · exact ⟨0, by simp⟩

/-- Infinite one-sided logarithmic-energy delay.  The `tsum` is proved summable below whenever
`|q| < 1`. -/
noncomputable def geometricCDDLogPhaseDelay (q x : ℝ) : ℝ :=
  ∑' k : ℕ, 4 * (q ^ k * x) / (1 + (q ^ k * x) ^ 2)

/-- The one-sided CDD delay is absolutely summable for every real energy when `|q| < 1`. -/
theorem summable_geometricCDDLogPhaseDelay
    {q : ℝ} (hq : |q| < 1) (x : ℝ) :
    Summable (fun k : ℕ ↦
      4 * (q ^ k * x) / (1 + (q ^ k * x) ^ 2)) := by
  apply (summable_geometric_of_lt_one (abs_nonneg q) hq).mul_left (4 * |x|) |>.of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
    abs_mul, abs_pow]
  rw [abs_of_nonneg (by positivity : 0 ≤ 1 + (q ^ k * x) ^ 2)]
  have hnum : 0 ≤ 4 * (|q| ^ k * |x|) := by positivity
  calc
    4 * (|q| ^ k * |x|) / (1 + (q ^ k * x) ^ 2) ≤
        4 * (|q| ^ k * |x|) := by
          exact div_le_self hnum (by nlinarith [sq_nonneg (q ^ k * x)])
    _ = 4 * |x| * |q| ^ k := by ring

/-- **Infinite one-shell constraint.**  The convergent physical delay is a solution of the exact
affine scale equation. -/
theorem geometricCDDLogPhaseDelay_constraint
    {q : ℝ} (hq : |q| < 1) (x : ℝ) :
    geometricCDDLogPhaseDelay q x =
      geometricCDDLogShellDelay x +
        geometricCDDLogPhaseDelay q (q * x) := by
  have hs := summable_geometricCDDLogPhaseDelay hq x
  rw [geometricCDDLogPhaseDelay]
  have hsplit := hs.tsum_eq_zero_add
  rw [hsplit]
  simp only [pow_zero, one_mul]
  rw [geometricCDDLogShellDelay, geometricCDDLogPhaseDelay]
  congr 1
  apply tsum_congr
  intro k
  rw [pow_succ]
  ring

@[simp]
theorem geometricCDDLogPhaseDelay_zero (q : ℝ) :
    geometricCDDLogPhaseDelay q 0 = 0 := by
  simp [geometricCDDLogPhaseDelay]

/-- Uniform endpoint estimate for the infinite delay. -/
theorem norm_geometricCDDLogPhaseDelay_le
    {q : ℝ} (hq : |q| < 1) (x : ℝ) :
    ‖geometricCDDLogPhaseDelay q x‖ ≤
      4 * |x| * (1 - |q|)⁻¹ := by
  rw [geometricCDDLogPhaseDelay]
  apply tsum_of_norm_bounded
    ((hasSum_geometric_of_lt_one (abs_nonneg q) hq).mul_left (4 * |x|))
  intro k
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
    abs_mul, abs_pow]
  rw [abs_of_nonneg (by positivity : 0 ≤ 1 + (q ^ k * x) ^ 2)]
  have hnum : 0 ≤ 4 * (|q| ^ k * |x|) := by positivity
  calc
    4 * (|q| ^ k * |x|) / (1 + (q ^ k * x) ^ 2) ≤
        4 * (|q| ^ k * |x|) := by
          exact div_le_self hnum (by nlinarith [sq_nonneg (q ^ k * x)])
    _ = 4 * |x| * |q| ^ k := by ring

/-- The infinite physical delay continuously reaches the zero infrared endpoint. -/
theorem continuousAt_geometricCDDLogPhaseDelay_zero
    {q : ℝ} (hq : |q| < 1) :
    ContinuousAt (geometricCDDLogPhaseDelay q) 0 := by
  rw [ContinuousAt, geometricCDDLogPhaseDelay_zero]
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun x => norm_nonneg _
  · exact Filter.Eventually.of_forall fun x =>
      norm_geometricCDDLogPhaseDelay_le hq x
  · have habs : Tendsto (fun x : ℝ ↦ |x|) (nhds 0) (nhds 0) := by
      simpa only [abs_zero] using (continuous_abs.tendsto (0 : ℝ))
    have hfour : Tendsto (fun _ : ℝ ↦ (4 : ℝ)) (nhds 0) (nhds 4) :=
      tendsto_const_nhds
    simpa only [mul_zero, zero_mul] using
      ((hfour.mul habs).mul_const ((1 - |q|)⁻¹) :
        Tendsto (fun x : ℝ ↦ 4 * |x| * (1 - |q|)⁻¹)
          (nhds 0) (nhds (4 * 0 * (1 - |q|)⁻¹)))

/-- **Contractive boundary selection.**  A continuous response invariant under a contracting
scale map and zero at its endpoint is identically zero. -/
theorem contractiveScaleInvariant_eq_zero
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    {Y : ℝ → ℝ}
    (hY : ∀ x, Y x = Y (q * x))
    (hcont : ContinuousAt Y 0)
    (hzero : Y 0 = 0) :
    Y = 0 := by
  funext x
  have hiter : ∀ n : ℕ, Y x = Y (q ^ n * x) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          Y x = Y (q ^ n * x) := ih
          _ = Y (q * (q ^ n * x)) := hY _
          _ = Y (q ^ (n + 1) * x) := by
            congr 1
            rw [pow_succ]
            ring
  have harg : Tendsto (fun n : ℕ ↦ q ^ n * x) atTop (nhds 0) := by
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const x
  have hlim : Tendsto (fun _ : ℕ ↦ Y x) atTop (nhds (Y 0)) := by
    convert hcont.tendsto.comp harg using 1
    funext n
    exact hiter n
  have heq : Y x = Y 0 := tendsto_nhds_unique tendsto_const_nhds hlim
  change Y x = 0
  exact heq.trans hzero

/-- **Affine boundary uniqueness.**  Two continuous responses obeying the same one-shell law and
the same contracting-endpoint value coincide everywhere. -/
theorem contractiveScaleAffineBoundary_unique
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    {B F G : ℝ → ℝ}
    (hF : ∀ x, F x = B x + F (q * x))
    (hG : ∀ x, G x = B x + G (q * x))
    (hFcont : ContinuousAt F 0) (hGcont : ContinuousAt G 0)
    (hF0 : F 0 = G 0) :
    F = G := by
  apply sub_eq_zero.mp
  apply contractiveScaleInvariant_eq_zero hq0 hq1
  · intro x
    rw [Pi.sub_apply, Pi.sub_apply, hF x, hG x]
    ring
  · exact hFcont.sub hGcont
  · simp [hF0]

/-- **Physical boundary uniqueness.**  The convergent one-sided CDD delay is the unique continuous
solution of its one-shell constraint with zero value at the contracting endpoint. -/
theorem geometricCDDLogPhaseDelay_unique
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    {F : ℝ → ℝ}
    (hF : ∀ x, F x = geometricCDDLogShellDelay x + F (q * x))
    (hFcont : ContinuousAt F 0)
    (hF0 : F 0 = 0) :
    F = geometricCDDLogPhaseDelay q := by
  have hqabs : |q| < 1 := by simpa [abs_of_nonneg hq0] using hq1
  apply contractiveScaleAffineBoundary_unique hq0 hq1
  · exact hF
  · exact geometricCDDLogPhaseDelay_constraint hqabs
  · exact hFcont
  · exact continuousAt_geometricCDDLogPhaseDelay_zero hqabs
  · simp [hF0]

end GaloisForLFunctions.HTGeometry
