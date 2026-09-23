import GaloisForLFunctions.RHTower.BurnolResidueCriticalLineKernelL2

/-!
# Burnol residue kernels vary continuously in critical-line L²

The exact difference `K_s - K_r` is the fixed square-integrable base kernel times a bounded
rational multiplier.  This gives a quantitative `L²` difference estimate and makes the source
parameter map continuous as an actual Banach-valued map, the analytic input needed before
Bochner contour integration and strong residue convergence.
-/

open Complex MeasureTheory

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Difference multiplier for Burnol's critical-line residue kernels. -/
def burnolResidueCriticalLineDifferenceMultiplier (s r : ℂ) (t : ℝ) : ℂ :=
  (s - r) * smoothAFEZetaLeftLinePt t * (smoothAFEZetaLeftLinePt t + 2) /
    ((smoothAFEZetaLeftLinePt t - s) * (smoothAFEZetaLeftLinePt t - r))

theorem burnolResidueCriticalLineKernel_sub_eq (s r : ℂ)
    (hs : -(1 / 4 : ℝ) ≤ s.re) (hr : -(1 / 4 : ℝ) ≤ r.re) (t : ℝ) :
    burnolResidueCriticalLineKernel s t - burnolResidueCriticalLineKernel r t =
      burnolCriticalLineBaseKernel t *
        burnolResidueCriticalLineDifferenceMultiplier s r t := by
  have hz0 : smoothAFEZetaLeftLinePt t ≠ 0 := smoothAFEZetaLeftLinePt_ne_zero t
  have hz2 : smoothAFEZetaLeftLinePt t + 2 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    rw [Complex.add_re, smoothAFEZetaLeftLinePt_re] at hre
    norm_num at hre
  have hzs : smoothAFEZetaLeftLinePt t - s ≠ 0 := by
    exact norm_pos_iff.mp <| lt_of_lt_of_le (by norm_num) (quarter_le_norm_leftLine_sub hs t)
  have hzr : smoothAFEZetaLeftLinePt t - r ≠ 0 := by
    exact norm_pos_iff.mp <| lt_of_lt_of_le (by norm_num) (quarter_le_norm_leftLine_sub hr t)
  simp only [burnolResidueCriticalLineKernel, burnolCriticalLineBaseKernel,
    burnolResidueCriticalLineDifferenceMultiplier]
  field_simp
  ring

theorem norm_leftLine_add_two_div_sub_le {r : ℂ}
    (hr : -(1 / 4 : ℝ) ≤ r.re) (t : ℝ) :
    ‖smoothAFEZetaLeftLinePt t + 2‖ / ‖smoothAFEZetaLeftLinePt t - r‖ ≤
      1 + 4 * ‖r + 2‖ := by
  let z := smoothAFEZetaLeftLinePt t
  have hsep : (1 / 4 : ℝ) ≤ ‖z - r‖ := quarter_le_norm_leftLine_sub hr t
  have hpos : 0 < ‖z - r‖ := lt_of_lt_of_le (by norm_num) hsep
  have htri : ‖z + 2‖ ≤ ‖z - r‖ + ‖r + 2‖ := by
    calc
      ‖z + 2‖ = ‖(z - r) + (r + 2)‖ := by ring_nf
      _ ≤ ‖z - r‖ + ‖r + 2‖ := norm_add_le _ _
  have hrdiv : ‖r + 2‖ / ‖z - r‖ ≤ 4 * ‖r + 2‖ := by
    have hinv : ‖z - r‖⁻¹ ≤ 4 := by
      have h := (inv_le_inv₀ hpos (by norm_num : (0 : ℝ) < 1 / 4)).2 hsep
      norm_num at h ⊢
      exact h
    rw [div_eq_mul_inv]
    nlinarith [mul_le_mul_of_nonneg_left hinv (norm_nonneg (r + 2))]
  calc
    ‖z + 2‖ / ‖z - r‖ ≤ (‖z - r‖ + ‖r + 2‖) / ‖z - r‖ := by gcongr
    _ = 1 + ‖r + 2‖ / ‖z - r‖ := by field_simp
    _ ≤ 1 + 4 * ‖r + 2‖ := by linarith

theorem norm_burnolResidueCriticalLineDifferenceMultiplier_le (s r : ℂ)
    (hs : -(1 / 4 : ℝ) ≤ s.re) (hr : -(1 / 4 : ℝ) ≤ r.re) (t : ℝ) :
    ‖burnolResidueCriticalLineDifferenceMultiplier s r t‖ ≤
      ‖s - r‖ * (1 + 4 * ‖s‖) * (1 + 4 * ‖r + 2‖) := by
  let z := smoothAFEZetaLeftLinePt t
  have hzs : 0 < ‖z - s‖ :=
    lt_of_lt_of_le (by norm_num) (quarter_le_norm_leftLine_sub hs t)
  have hzr : 0 < ‖z - r‖ :=
    lt_of_lt_of_le (by norm_num) (quarter_le_norm_leftLine_sub hr t)
  have hfirst := norm_leftLine_div_sub_le hs t
  have hsecond := norm_leftLine_add_two_div_sub_le hr t
  rw [burnolResidueCriticalLineDifferenceMultiplier, norm_div, norm_mul, norm_mul,
    norm_mul]
  calc
    ‖s - r‖ * ‖z‖ * ‖z + 2‖ / (‖z - s‖ * ‖z - r‖) =
        ‖s - r‖ * (‖z‖ / ‖z - s‖) * (‖z + 2‖ / ‖z - r‖) := by
      field_simp
    _ ≤ ‖s - r‖ * (1 + 4 * ‖s‖) * (1 + 4 * ‖r + 2‖) := by
      gcongr

theorem continuous_burnolResidueCriticalLineDifferenceMultiplier (s r : ℂ)
    (hs : -(1 / 4 : ℝ) ≤ s.re) (hr : -(1 / 4 : ℝ) ≤ r.re) :
    Continuous (burnolResidueCriticalLineDifferenceMultiplier s r) := by
  have hline : Continuous smoothAFEZetaLeftLinePt := by
    unfold smoothAFEZetaLeftLinePt
    fun_prop
  rw [continuous_iff_continuousAt]
  intro t
  unfold burnolResidueCriticalLineDifferenceMultiplier
  apply ContinuousAt.div
  · fun_prop
  · fun_prop
  · exact mul_ne_zero
      (norm_pos_iff.mp <| lt_of_lt_of_le (by norm_num)
        (quarter_le_norm_leftLine_sub hs t))
      (norm_pos_iff.mp <| lt_of_lt_of_le (by norm_num)
        (quarter_le_norm_leftLine_sub hr t))

/-- Closed Burnol source half-strip used for contour parameters. -/
abbrev BurnolSourceHalfStrip := {s : ℂ // -(1 / 4 : ℝ) ≤ s.re}

/-- Burnol's residue kernel as an actual critical-line `L²` vector. -/
def burnolResidueCriticalLineKernelL2 (s : BurnolSourceHalfStrip) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  (memLp_burnolResidueCriticalLineKernel s.1 s.2).toLp
    (burnolResidueCriticalLineKernel s.1)

/-- Fixed base kernel as an actual critical-line `L²` vector. -/
def burnolCriticalLineBaseKernelL2 : Lp ℂ 2 (volume : Measure ℝ) :=
  memLp_burnolCriticalLineBaseKernel.toLp burnolCriticalLineBaseKernel

/-- Burnol's quadratic critical-line `L²` bound as an inequality between actual `L²` vectors. -/
theorem norm_burnolResidueCriticalLineKernelL2_le_quadratic
    (s : BurnolSourceHalfStrip) :
    ‖burnolResidueCriticalLineKernelL2 s‖ ≤
      9 * (1 + ‖(s : ℂ)‖ ^ (2 : ℕ)) * ‖burnolCriticalLineBaseKernelL2‖ := by
  let C : ℝ := 9 * (1 + ‖(s : ℂ)‖ ^ (2 : ℕ))
  let phi : ℝ → ℂ := burnolResidueCriticalLineMultiplier s.1
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  have hphi : ∀ t, ‖phi t‖ ≤ C := by
    intro t
    exact norm_burnolResidueCriticalLineMultiplier_le_quadratic s.2 t
  have hphiCont : Continuous phi := by
    dsimp [phi]
    have hline : Continuous smoothAFEZetaLeftLinePt := by
      unfold smoothAFEZetaLeftLinePt
      fun_prop
    unfold burnolResidueCriticalLineMultiplier
    rw [continuous_iff_continuousAt]
    intro t
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · exact norm_pos_iff.mp <| lt_of_lt_of_le (by norm_num)
        (quarter_le_norm_leftLine_sub s.2 t)
  have hphiMeas : Measurable phi := hphiCont.measurable
  let M : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
    lpBoundedMulCLM hphiMeas hC0 hphi
  have heq : burnolResidueCriticalLineKernelL2 s =
      M burnolCriticalLineBaseKernelL2 := by
    apply Lp.ext
    filter_upwards [
      MemLp.coeFn_toLp (memLp_burnolResidueCriticalLineKernel s.1 s.2),
      lpBoundedMulCLM_coeFn hphiMeas hC0 hphi burnolCriticalLineBaseKernelL2,
      MemLp.coeFn_toLp memLp_burnolCriticalLineBaseKernel] with t hs' hM hbase
    have hs'' : (burnolResidueCriticalLineKernelL2 s : ℝ → ℂ) t =
        burnolResidueCriticalLineKernel s.1 t := by
      simpa [burnolResidueCriticalLineKernelL2] using hs'
    have hM' : (M burnolCriticalLineBaseKernelL2 : ℝ → ℂ) t =
        burnolResidueCriticalLineMultiplier s.1 t *
          (burnolCriticalLineBaseKernelL2 : ℝ → ℂ) t := by
      simpa [M, phi] using hM
    have hbase' : (burnolCriticalLineBaseKernelL2 : ℝ → ℂ) t =
        burnolCriticalLineBaseKernel t := by
      simpa [burnolCriticalLineBaseKernelL2] using hbase
    rw [hs'', hM', hbase', burnolResidueCriticalLineKernel_eq]
    ring
  rw [heq]
  calc
    ‖M burnolCriticalLineBaseKernelL2‖ ≤ ‖M‖ * ‖burnolCriticalLineBaseKernelL2‖ :=
      ContinuousLinearMap.le_opNorm M _
    _ ≤ C * ‖burnolCriticalLineBaseKernelL2‖ := by
      gcongr
      exact norm_lpBoundedMulCLM_le hphiMeas hC0 hphi
    _ = 9 * (1 + ‖(s : ℂ)‖ ^ (2 : ℕ)) * ‖burnolCriticalLineBaseKernelL2‖ := rfl

theorem norm_burnolResidueCriticalLineKernelL2_sub_le
    (s r : BurnolSourceHalfStrip) :
    ‖burnolResidueCriticalLineKernelL2 s - burnolResidueCriticalLineKernelL2 r‖ ≤
      ‖(s : ℂ) - (r : ℂ)‖ * (1 + 4 * ‖(s : ℂ)‖) *
        (1 + 4 * ‖(r : ℂ) + 2‖) * ‖burnolCriticalLineBaseKernelL2‖ := by
  let C : ℝ := ‖(s : ℂ) - (r : ℂ)‖ * (1 + 4 * ‖(s : ℂ)‖) *
    (1 + 4 * ‖(r : ℂ) + 2‖)
  let phi : ℝ → ℂ := burnolResidueCriticalLineDifferenceMultiplier s.1 r.1
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  have hphi : ∀ t, ‖phi t‖ ≤ C := by
    intro t
    exact norm_burnolResidueCriticalLineDifferenceMultiplier_le s.1 r.1 s.2 r.2 t
  let M : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
    lpBoundedMulCLM
      (continuous_burnolResidueCriticalLineDifferenceMultiplier s.1 r.1 s.2 r.2).measurable
      hC0 hphi
  have heq : burnolResidueCriticalLineKernelL2 s -
      burnolResidueCriticalLineKernelL2 r = M burnolCriticalLineBaseKernelL2 := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub (burnolResidueCriticalLineKernelL2 s)
        (burnolResidueCriticalLineKernelL2 r),
      MemLp.coeFn_toLp (memLp_burnolResidueCriticalLineKernel s.1 s.2),
      MemLp.coeFn_toLp (memLp_burnolResidueCriticalLineKernel r.1 r.2),
      lpBoundedMulCLM_coeFn
        (continuous_burnolResidueCriticalLineDifferenceMultiplier s.1 r.1 s.2 r.2).measurable
        hC0 hphi burnolCriticalLineBaseKernelL2,
      MemLp.coeFn_toLp memLp_burnolCriticalLineBaseKernel] with t hsub hs' hr' hM hbase
    have hs'' : (burnolResidueCriticalLineKernelL2 s : ℝ → ℂ) t =
        burnolResidueCriticalLineKernel s.1 t := by
      simpa [burnolResidueCriticalLineKernelL2] using hs'
    have hr'' : (burnolResidueCriticalLineKernelL2 r : ℝ → ℂ) t =
        burnolResidueCriticalLineKernel r.1 t := by
      simpa [burnolResidueCriticalLineKernelL2] using hr'
    have hM' : (M burnolCriticalLineBaseKernelL2 : ℝ → ℂ) t =
        burnolResidueCriticalLineDifferenceMultiplier s.1 r.1 t *
          (burnolCriticalLineBaseKernelL2 : ℝ → ℂ) t := by
      simpa [M, phi] using hM
    have hbase' : (burnolCriticalLineBaseKernelL2 : ℝ → ℂ) t =
        burnolCriticalLineBaseKernel t := by
      simpa [burnolCriticalLineBaseKernelL2] using hbase
    rw [hsub, Pi.sub_apply, hs'', hr'', hM', hbase']
    rw [burnolResidueCriticalLineKernel_sub_eq s.1 r.1 s.2 r.2]
    ring
  rw [heq]
  calc
    ‖M burnolCriticalLineBaseKernelL2‖ ≤ ‖M‖ * ‖burnolCriticalLineBaseKernelL2‖ :=
      ContinuousLinearMap.le_opNorm M _
    _ ≤ C * ‖burnolCriticalLineBaseKernelL2‖ := by
      gcongr
      exact norm_lpBoundedMulCLM_le
        (continuous_burnolResidueCriticalLineDifferenceMultiplier s.1 r.1 s.2 r.2).measurable
        hC0 hphi
    _ = ‖(s : ℂ) - (r : ℂ)‖ * (1 + 4 * ‖(s : ℂ)‖) *
        (1 + 4 * ‖(r : ℂ) + 2‖) * ‖burnolCriticalLineBaseKernelL2‖ := by
      rfl

/-- Burnol's source-parameter residue kernel is continuous as an actual `L²`-valued map. -/
theorem continuous_burnolResidueCriticalLineKernelL2 :
    Continuous burnolResidueCriticalLineKernelL2 := by
  rw [continuous_iff_continuousAt]
  intro r
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  let B : BurnolSourceHalfStrip → ℝ := fun s =>
    ‖(s : ℂ) - (r : ℂ)‖ * (1 + 4 * ‖(s : ℂ)‖) *
      (1 + 4 * ‖(r : ℂ) + 2‖) * ‖burnolCriticalLineBaseKernelL2‖
  have hB : Continuous B := by
    dsimp [B]
    fun_prop
  have hB0 : B r = 0 := by simp [B]
  have hlim : Filter.Tendsto B (nhds r) (nhds 0) := by
    have hBr : Filter.Tendsto B (nhds r) (nhds (B r)) := hB.continuousAt
    simpa only [hB0] using hBr
  refine squeeze_zero' (Filter.Eventually.of_forall fun s => norm_nonneg _) ?_ hlim
  exact Filter.Eventually.of_forall fun s =>
    norm_burnolResidueCriticalLineKernelL2_sub_le s r

end

end RHTower
