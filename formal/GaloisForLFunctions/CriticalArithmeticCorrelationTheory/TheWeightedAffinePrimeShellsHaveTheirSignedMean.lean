import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ActualAffinePrimeWindowsAreUniformInTheirParameters
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheNonRatioPrimeRowsSplitIntoDownwardAndUpward
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheTiltedSplineKeepsAGammaReserveAtEveryOverlap

/-!
# Weighted affine prime shells and their signed means

Residue-class Mertens finite parts and real-endpoint Abel summation identify
Mangoldt readings against any smooth weight vanishing near zero. A finite
residue basis makes the source error uniform over both affine parameters.

For a compact unit profile, the reciprocal autocorrelation weight has the
exact Mellin integral of a successor shell. Summing the literal prime-power
readings realizes the signed correction from reference to completed
conductor energy. All affine parameters may vary with the real horizon.
-/

noncomputable section
open MeasureTheory Filter Topology Finset
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  BezoutValuationIncidence

/-- The actual residue-class Mangoldt source with a dilated profile weight. -/
def weightedResiduePrimeReading (q : ℕ) (F : ZMod q → ℝ) (W : ℝ → ℝ) (X : ℝ) : ℝ :=
  ∑ k ∈ Icc 1 ⌊X⌋₊,
    W ((k : ℝ) / X) * (F (k : ZMod q) * (ArithmeticFunction.vonMangoldt k : ℝ) / k)

/-- The real-endpoint remainder after removing the residue Mertens logarithm and finite part. -/
def residuePrimeRealError (q : ℕ) [NeZero q] (F : ZMod q → ℝ) (X : ℝ) : ℝ :=
  residuePrimeReading q F ⌊X⌋₊ - primeClassKappa q F * Real.log X - residuePrimeFinitePart q F

private theorem sum_Icc_zero_eq_one (a : ℕ → ℝ) (ha : a 0 = 0) (N : ℕ) :
    (∑ k ∈ Icc 0 N, a k) = ∑ k ∈ Icc 1 N, a k := by
  symm
  apply sum_subset (show Icc 1 N ⊆ Icc 0 N from fun k hk =>
    mem_Icc.mpr ⟨Nat.zero_le k, (mem_Icc.mp hk).2⟩)
  intro k hk hk'
  have hk0 : k = 0 := by
    have hkN := (mem_Icc.mp hk).2
    have : ¬ 1 ≤ k := fun h => hk' (mem_Icc.mpr ⟨h, hkN⟩)
    omega
  simpa only [hk0] using ha

/-- The residue finite-part law extends to real endpoints because `⌊X⌋/X → 1`. -/
theorem tendsto_residuePrimeRealError {q : ℕ} [NeZero q] (F : ZMod q → ℝ) :
    Tendsto (residuePrimeRealError q F) atTop (𝓝 0) := by
  have hlog : Tendsto (fun X : ℝ => Real.log (⌊X⌋₊ : ℝ) - Real.log X) atTop (𝓝 0) := by
    have h := (tendsto_nat_floor_div_atTop (R := ℝ)).log (by norm_num : (1 : ℝ) ≠ 0)
    simp only [Real.log_one] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
    have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
    have hfloor : 1 ≤ ⌊X⌋₊ := (Nat.one_le_floor_iff X).mpr hX
    rw [Real.log_div (by exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hfloor))) hX0.ne']
  have h := ((tendsto_residuePrimeReading_sub_log F).comp tendsto_nat_floor_atTop).add
    (hlog.const_mul (primeClassKappa q F))
  simp only [mul_zero, add_zero] at h
  have h' := h.sub_const (residuePrimeFinitePart q F)
  simp only [sub_self] at h'
  refine h'.congr fun X => ?_
  dsimp only [Function.comp_def, residuePrimeRealError]
  ring

/-- Exact real-endpoint Abel summation, rescaled to the fixed interval `[0,1]`. -/
theorem weightedResiduePrimeReading_abel {q : ℕ} (F : ZMod q → ℝ)
    {W : ℝ → ℝ} (hW : ContDiff ℝ 1 W) {X : ℝ} (hX : 0 < X) :
    weightedResiduePrimeReading q F W X =
      W 1 * residuePrimeReading q F ⌊X⌋₊ -
        ∫ u in (0 : ℝ)..1, deriv W u * residuePrimeReading q F ⌊X * u⌋₊ := by
  let a : ℕ → ℝ := fun k => F (k : ZMod q) * (ArithmeticFunction.vonMangoldt k : ℝ) / k
  have ha : a 0 = 0 := by simp only [a, Nat.cast_zero, div_zero]
  have hsum (Y : ℕ) : (∑ k ∈ Icc 0 Y, a k) = residuePrimeReading q F Y :=
    sum_Icc_zero_eq_one a ha Y
  let f : ℝ → ℝ := fun t => W (t / X)
  have hf : ContDiff ℝ 1 f := hW.comp (contDiff_id.div_const X)
  have hd (t : ℝ) : deriv f t = deriv W (t / X) / X := by
    have h := ((hW.differentiable (by norm_num)).differentiableAt.hasDerivAt).comp t
      ((hasDerivAt_id t).div_const X)
    simpa only [f, Function.comp_def, id_eq, one_div, div_eq_mul_inv, one_mul] using h.deriv
  have hAbel := sum_mul_eq_sub_integral_mul a hX.le
    (fun t _ => (hf.differentiable (by norm_num)) t)
    ((hf.continuous_deriv le_rfl).integrableOn_Icc)
  have hleft : (∑ k ∈ Icc 0 ⌊X⌋₊, f k * a k) = weightedResiduePrimeReading q F W X := by
    exact sum_Icc_zero_eq_one (fun k => f k * a k) (by rw [ha, mul_zero]) ⌊X⌋₊
  have hscale : (∫ t in Set.Ioc 0 X, deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, a k) =
      ∫ u in (0 : ℝ)..1, deriv W u * residuePrimeReading q F ⌊X * u⌋₊ := by
    simp_rw [hd, hsum]
    rw [← intervalIntegral.integral_of_le hX.le]
    have heq : (fun t : ℝ => deriv W (t / X) / X * residuePrimeReading q F ⌊t⌋₊) =
        fun t => X⁻¹ * ((fun u => deriv W u * residuePrimeReading q F ⌊X * u⌋₊) (t / X)) := by
      funext t
      dsimp only
      rw [mul_div_cancel₀ t hX.ne']
      ring
    rw [heq, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_div (fun u => deriv W u * residuePrimeReading q F ⌊X * u⌋₊)
        hX.ne', zero_div, div_self hX.ne', smul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ hX.ne', one_mul]
  rw [hleft, hsum, hscale] at hAbel
  simpa only [f, div_self hX.ne'] using hAbel

private theorem deriv_zero_of_flat {W : ℝ → ℝ} {a : ℝ}
    (hflat : ∀ u, |u| < a → W u = 0) {u : ℝ} (hu : |u| < a) : deriv W u = 0 := by
  have hlocal : W =ᶠ[𝓝 u] fun _ => 0 := by
    filter_upwards [continuous_abs.continuousAt.eventually (gt_mem_nhds hu)] with v hv
    exact hflat v hv
  exact ((hasDerivAt_const u (0 : ℝ)).congr_of_eventuallyEq hlocal).deriv

private theorem continuous_mul_log_of_flat {W : ℝ → ℝ} (hW : Continuous W)
    {a : ℝ} (ha : 0 < a) (hflat : ∀ u, |u| < a → W u = 0) :
    Continuous (fun u => W u * Real.log u) := by
  rw [continuous_iff_continuousAt]
  intro u
  by_cases hu : u = 0
  · subst u
    change Tendsto (fun u => W u * Real.log u) (𝓝 0) (𝓝 (W 0 * Real.log 0))
    simp only [Real.log_zero, mul_zero]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [continuous_abs.continuousAt.eventually
      (gt_mem_nhds (by simpa only [abs_zero] using ha : |(0 : ℝ)| < a))] with v hv
    simp only [hflat v hv, zero_mul]
  · exact hW.continuousAt.mul (Real.continuousAt_log hu)

private theorem continuous_div_self_of_flat {W : ℝ → ℝ} (hW : Continuous W)
    {a : ℝ} (ha : 0 < a) (hflat : ∀ u, |u| < a → W u = 0) :
    Continuous (fun u => W u / u) := by
  rw [continuous_iff_continuousAt]
  intro u
  by_cases hu : u = 0
  · subst u
    change Tendsto (fun u => W u / u) (𝓝 0) (𝓝 (W 0 / 0))
    simp only [div_zero]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [continuous_abs.continuousAt.eventually
      (gt_mem_nhds (by simpa only [abs_zero] using ha : |(0 : ℝ)| < a))] with v hv
    simp only [hflat v hv, zero_div]
  · exact hW.continuousAt.div continuousAt_id hu

/-- Flatness at zero removes the logarithmic boundary term in integration by parts. -/
theorem integral_weight_div_eq_neg_deriv_log {W : ℝ → ℝ} (hW : ContDiff ℝ 1 W)
    {a : ℝ} (ha : 0 < a) (hflat : ∀ u, |u| < a → W u = 0) :
    (∫ u in (0 : ℝ)..1, W u / u) = -(∫ u in (0 : ℝ)..1, deriv W u * Real.log u) := by
  have hD := hW.continuous_deriv le_rfl
  have hlog := continuous_mul_log_of_flat hD ha (fun u hu => deriv_zero_of_flat hflat hu)
  have hdiv := continuous_div_self_of_flat hW.continuous ha hflat
  have hderiv (u : ℝ) : HasDerivAt (fun t => W t * Real.log t)
      (deriv W u * Real.log u + W u / u) u := by
    by_cases hu : u = 0
    · subst u
      have hlocal : (fun t => W t * Real.log t) =ᶠ[𝓝 0] fun _ => 0 := by
        filter_upwards [continuous_abs.continuousAt.eventually
          (gt_mem_nhds (by simpa only [abs_zero] using ha : |(0 : ℝ)| < a))] with v hv
        simp only [hflat v hv, zero_mul]
      simpa only [Real.log_zero, mul_zero, div_zero, zero_add] using
        (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hlocal
    · convert ((hW.differentiable (by norm_num)) u).hasDerivAt.mul
        (Real.hasDerivAt_log hu) using 1 <;> rfl
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hderiv u)
    ((hlog.intervalIntegrable 0 1).add (hdiv.intervalIntegrable 0 1))
  rw [intervalIntegral.integral_add (hlog.intervalIntegrable 0 1) (hdiv.intervalIntegrable 0 1)] at h
  simp only [Real.log_one, Real.log_zero, mul_zero, sub_self] at h
  linarith only [h]

/-- A smooth derivative times the finite residue counting function is interval integrable. -/
theorem intervalIntegrable_deriv_mul_residuePrimeReading {q : ℕ} (F : ZMod q → ℝ)
    {W : ℝ → ℝ} (hW : ContDiff ℝ 1 W) {X : ℝ} (hX : 0 < X) :
    IntervalIntegrable (fun u => deriv W u * residuePrimeReading q F ⌊X * u⌋₊) volume 0 1 := by
  let a : ℕ → ℝ := fun k => F (k : ZMod q) * (ArithmeticFunction.vonMangoldt k : ℝ) / k
  have ha : a 0 = 0 := by simp only [a, Nat.cast_zero, div_zero]
  have hsum (Y : ℕ) : (∑ k ∈ Icc 0 Y, a k) = residuePrimeReading q F Y :=
    sum_Icc_zero_eq_one a ha Y
  have hcont : Continuous (fun t => deriv W (t / X)) :=
    (hW.continuous_deriv le_rfl).comp (continuous_id.div_const X)
  have hint := integrableOn_mul_sum_Icc a (m := 0) (a := (0 : ℝ)) (b := X) le_rfl
    hcont.integrableOn_Icc
  simp_rw [hsum] at hint
  have hi : IntervalIntegrable (fun t => deriv W (t / X) * residuePrimeReading q F ⌊t⌋₊)
      volume 0 X := (intervalIntegrable_iff_integrableOn_Icc_of_le hX.le).mpr hint
  have hs := hi.comp_mul_left (c := X)
  simpa only [zero_div, div_self hX.ne', mul_div_cancel_left₀ _ hX.ne'] using hs

/-- Abel summation cancels both the logarithm and residue finite part exactly. -/
theorem weightedResiduePrimeReading_sub_mean_eq {q : ℕ} [NeZero q]
    (F : ZMod q → ℝ) {W : ℝ → ℝ} (hW : ContDiff ℝ 1 W)
    {a : ℝ} (ha : 0 < a) (hflat : ∀ u, |u| < a → W u = 0)
    {X : ℝ} (hX : 0 < X) :
    weightedResiduePrimeReading q F W X -
        primeClassKappa q F * ∫ u in (0 : ℝ)..1, W u / u =
      W 1 * residuePrimeRealError q F X -
        ∫ u in (0 : ℝ)..1, deriv W u * residuePrimeRealError q F (X * u) := by
  have hD := hW.continuous_deriv le_rfl
  have hDI : IntervalIntegrable (deriv W) volume 0 1 := hD.intervalIntegrable 0 1
  have hlogI : IntervalIntegrable (fun u => deriv W u * Real.log u) volume 0 1 :=
    (continuous_mul_log_of_flat hD ha
    (fun u hu => deriv_zero_of_flat hflat hu)).intervalIntegrable 0 1
  have hreadI := intervalIntegrable_deriv_mul_residuePrimeReading F hW hX
  let K := primeClassKappa q F * Real.log X + residuePrimeFinitePart q F
  have hpoint : (fun u => deriv W u * residuePrimeRealError q F (X * u)) =
      fun u => (deriv W u * residuePrimeReading q F ⌊X * u⌋₊ - K * deriv W u) -
        primeClassKappa q F * (deriv W u * Real.log u) := by
    funext u
    by_cases hu : u = 0
    · subst u
      have hd0 : deriv W 0 = 0 := deriv_zero_of_flat hflat (by simpa only [abs_zero] using ha)
      simp only [hd0, zero_mul, mul_zero, sub_self]
    · rw [residuePrimeRealError, Real.log_mul hX.ne' hu]
      dsimp only [K]
      ring
  have herror : (∫ u in (0 : ℝ)..1, deriv W u * residuePrimeRealError q F (X * u)) =
      ((∫ u in (0 : ℝ)..1, deriv W u * residuePrimeReading q F ⌊X * u⌋₊) -
        K * ∫ u in (0 : ℝ)..1, deriv W u) -
        primeClassKappa q F * ∫ u in (0 : ℝ)..1, deriv W u * Real.log u := by
    rw [hpoint, intervalIntegral.integral_sub (hreadI.sub (hDI.const_mul K))
      (hlogI.const_mul _), intervalIntegral.integral_sub hreadI (hDI.const_mul K),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hderiv : (∫ u in (0 : ℝ)..1, deriv W u) = W 1 := by
    rw [intervalIntegral.integral_deriv_eq_sub
      (fun u _ => (hW.differentiable (by norm_num)) u) hDI,
      hflat 0 (by simpa only [abs_zero] using ha), sub_zero]
  rw [weightedResiduePrimeReading_abel F hW hX,
    integral_weight_div_eq_neg_deriv_log hW ha hflat, herror, hderiv,
    residuePrimeRealError]
  dsimp only [K]
  ring

/-- Actual weighted readings converge to their unit mean; no distribution premise is assumed. -/
theorem tendsto_weightedResiduePrimeReading {q : ℕ} [NeZero q]
    (F : ZMod q → ℝ) {W : ℝ → ℝ} (hW : ContDiff ℝ 1 W)
    {a : ℝ} (ha : 0 < a) (hflat : ∀ u, |u| < a → W u = 0) :
    Tendsto (weightedResiduePrimeReading q F W) atTop
      (𝓝 (primeClassKappa q F * ∫ u in (0 : ℝ)..1, W u / u)) := by
  have hD := hW.continuous_deriv le_rfl
  obtain ⟨u₀, hu₀, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Set.Icc (0 : ℝ) 1).Nonempty from ⟨0, le_rfl, zero_le_one⟩) hD.abs.continuousOn
  let L := |deriv W u₀|
  have hL : 0 ≤ L := abs_nonneg _
  have hDbound : ∀ u ∈ Set.Icc (0 : ℝ) 1, |deriv W u| ≤ L := fun u hu => hmax hu
  let α := min (a / 2) (1 / 2)
  have hα : 0 < α := lt_min (by positivity) (by norm_num)
  have hαa : α < a := (min_le_left _ _).trans_lt (half_lt_self ha)
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  let δ := ε / (2 * (|W 1| + L + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδeq : δ * (2 * (|W 1| + L + 1)) = ε :=
    div_mul_cancel₀ ε (by positivity)
  -- On the support of the derivative, every argument of the error tends uniformly to infinity.
  have hE : ∀ᶠ X : ℝ in atTop, |residuePrimeRealError q F X| < δ := by
    have h := (tendsto_residuePrimeRealError F).abs
    simp only [abs_zero] at h
    exact h.eventually (gt_mem_nhds hδ)
  obtain ⟨Y, hY⟩ := eventually_atTop.mp hE
  let B := max 1 Y
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨max B (B / α), ?_⟩
  intro X hX
  have hXB : B ≤ X := (le_max_left _ _).trans hX
  have hX0 : 0 < X := hB.trans_le hXB
  have hXα : B ≤ X * α := (div_le_iff₀ hα).mp ((le_max_right _ _).trans hX)
  have hEX : |residuePrimeRealError q F X| ≤ δ :=
    (hY X ((le_max_right _ _).trans hXB)).le
  have hpoint : ∀ u ∈ Set.uIoc (0 : ℝ) 1,
      ‖deriv W u * residuePrimeRealError q F (X * u)‖ ≤ L * δ := by
    intro u hu
    rw [Set.uIoc_of_le zero_le_one] at hu
    by_cases hsmall : u < α
    · have hd0 : deriv W u = 0 := deriv_zero_of_flat hflat (by
        rw [abs_of_pos hu.1]
        exact hsmall.trans hαa)
      rw [hd0, zero_mul, norm_zero]
      positivity
    · have huα : α ≤ u := le_of_not_gt hsmall
      have hXu : Y ≤ X * u := (le_max_right 1 Y).trans
        (hXα.trans (mul_le_mul_of_nonneg_left huα hX0.le))
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hDbound u ⟨hu.1.le, hu.2⟩) (hY (X * u) hXu).le
        (abs_nonneg _) hL
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  simp only [sub_zero, abs_one, mul_one, Real.norm_eq_abs] at hI
  rw [Real.dist_eq, weightedResiduePrimeReading_sub_mean_eq F hW ha hflat hX0]
  calc
    _ ≤ |W 1| * |residuePrimeRealError q F X| +
        |∫ u in (0 : ℝ)..1, deriv W u * residuePrimeRealError q F (X * u)| := by
      simpa only [abs_mul] using abs_sub (W 1 * residuePrimeRealError q F X)
        (∫ u in (0 : ℝ)..1, deriv W u * residuePrimeRealError q F (X * u))
    _ ≤ |W 1| * δ + L * δ := add_le_add
      (mul_le_mul_of_nonneg_left hEX (abs_nonneg _)) hI
    _ < ε := by nlinarith only [hδeq, hδ, hε, hL, abs_nonneg (W 1)]

/-- Every signed weighted reading decomposes into finitely many residue masses. -/
theorem weightedResiduePrimeReading_eq_indicator_sum {q : ℕ} [NeZero q]
    (F : ZMod q → ℝ) (W : ℝ → ℝ) (X : ℝ) :
    weightedResiduePrimeReading q F W X =
      ∑ r : ZMod q, F r * weightedResiduePrimeReading q (primeResidueIndicator r) W X := by
  classical
  symm
  simp only [weightedResiduePrimeReading, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun k _ => ?_
  have he : ∀ r : ZMod q,
      F r * (W ((k : ℝ) / X) * (primeResidueIndicator r (k : ZMod q) *
        (ArithmeticFunction.vonMangoldt k : ℝ) / k)) =
      if r = (k : ZMod q) then W ((k : ℝ) / X) * (F (k : ZMod q) *
        (ArithmeticFunction.vonMangoldt k : ℝ) / k) else 0 := by
    intro r
    by_cases hr : r = (k : ZMod q)
    · subst r
      simp only [primeResidueIndicator, ite_true, one_mul]
      ring
    · simp only [primeResidueIndicator, if_neg hr, if_neg (Ne.symm hr),
        zero_mul, zero_div, mul_zero]
  simp_rw [he]
  rw [sum_ite_eq', if_pos (mem_univ _)]

/-- One horizon controls every residue pattern in its full residue norm. -/
theorem eventually_weightedResiduePrimeReading_uniform {q : ℕ} [NeZero q]
    {W : ℝ → ℝ} (hW : ContDiff ℝ 1 W) {a : ℝ} (ha : 0 < a)
    (hflat : ∀ u, |u| < a → W u = 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop, ∀ F : ZMod q → ℝ,
      |weightedResiduePrimeReading q F W X -
          primeClassKappa q F * ∫ u in (0 : ℝ)..1, W u / u| ≤
        ε * ∑ r : ZMod q, |F r| := by
  have hr (r : ZMod q) : ∀ᶠ X : ℝ in atTop,
      |weightedResiduePrimeReading q (primeResidueIndicator r) W X -
        primeClassKappa q (primeResidueIndicator r) * ∫ u in (0 : ℝ)..1, W u / u| < ε := by
    have h := ((tendsto_weightedResiduePrimeReading (primeResidueIndicator r) hW ha hflat).sub_const
      (primeClassKappa q (primeResidueIndicator r) * ∫ u in (0 : ℝ)..1, W u / u)).abs
    simp only [sub_self, abs_zero] at h
    exact h.eventually (gt_mem_nhds hε)
  filter_upwards [Filter.eventually_all.mpr hr] with X hX
  intro F
  have he : weightedResiduePrimeReading q F W X -
      primeClassKappa q F * ∫ u in (0 : ℝ)..1, W u / u =
      ∑ r : ZMod q, F r * (weightedResiduePrimeReading q (primeResidueIndicator r) W X -
        primeClassKappa q (primeResidueIndicator r) * ∫ u in (0 : ℝ)..1, W u / u) := by
    rw [weightedResiduePrimeReading_eq_indicator_sum, primeClassKappa_eq_indicator_sum,
      sum_mul, ← sum_sub_distrib]
    exact sum_congr rfl fun r _ => by ring
  rw [he, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun r _ => ?_)
  rw [abs_mul, mul_comm ε]
  exact mul_le_mul_of_nonneg_left (hX r).le (abs_nonneg _)

private theorem affine_residue_cast {q : ℕ} [NeZero q] (n b k : ℕ) :
    affineRamanujanResidue q n b (k : ZMod q) = ramanujanLagCoefficient q (k * n + b) := by
  rw [affineRamanujanResidue, ZMod.val_natCast]
  have hk : Nat.ModEq q (k % q) k := by
    change (k % q) % q = k % q
    exact Nat.mod_mod k q
  have hab := (hk.mul_right n).add_right b
  unfold ramanujanLagCoefficient
  exact sum_congr rfl fun d hd => by simp only [hab.dvd_iff (Nat.dvd_of_mem_divisors hd)]

private theorem sum_abs_affine_residue_le {q : ℕ} [NeZero q] (n b : ℕ) :
    (∑ r : ZMod q, |affineRamanujanResidue q n b r|) ≤ (q : ℝ) * q.totient := by
  have hb := sum_le_sum (s := (univ : Finset (ZMod q)))
    (fun r _ => BiScaleUncertainty.SieveMoments.abs_ramanujanLagCoefficient_le_totient
      q (r.val * n + b))
  simpa only [affineRamanujanResidue, sum_const, card_univ, ZMod.card, nsmul_eq_mul] using hb

/-- The literal affine Ramanujan source, retaining every prime power. -/
def weightedAffineRamanujanPrimeReading (q n b : ℕ) (W : ℝ → ℝ) (X : ℝ) : ℝ :=
  ∑ k ∈ Icc 1 ⌊X⌋₊, (ArithmeticFunction.vonMangoldt k : ℝ) / k *
    ramanujanLagCoefficient q (k * n + b) * W ((k : ℝ) / X)

/-- The affine reading is exactly the residue reading of its periodic pattern. -/
theorem weightedAffineRamanujanPrimeReading_eq_residue {q : ℕ} [NeZero q]
    (n b : ℕ) (W : ℝ → ℝ) (X : ℝ) :
    weightedAffineRamanujanPrimeReading q n b W X =
      weightedResiduePrimeReading q (affineRamanujanResidue q n b) W X := by
  unfold weightedAffineRamanujanPrimeReading weightedResiduePrimeReading
  refine sum_congr rfl fun k _ => ?_
  rw [affine_residue_cast]
  ring

/-- The weighted affine source has its signed unit mean uniformly in multiplier and shift. -/
theorem eventually_weightedAffineRamanujanPrimeReading_uniform {q : ℕ} (hq : 0 < q)
    {W : ℝ → ℝ} (hW : ContDiff ℝ 1 W) {a : ℝ} (ha : 0 < a)
    (hflat : ∀ u, |u| < a → W u = 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop, ∀ n b : ℕ,
      |weightedAffineRamanujanPrimeReading q n b W X -
          (ramanujanLagCoefficient q n * ramanujanLagCoefficient q b / (q.totient : ℝ)) *
            ∫ u in (0 : ℝ)..1, W u / u| ≤ ε := by
  haveI : NeZero q := ⟨hq.ne'⟩
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hM : 0 < (q : ℝ) * q.totient := mul_pos hqR hφ
  filter_upwards [eventually_weightedResiduePrimeReading_uniform (q := q) hW ha hflat
    (div_pos hε hM)] with X hX
  intro n b
  have hb := hX (affineRamanujanResidue q n b)
  rw [← weightedAffineRamanujanPrimeReading_eq_residue,
    primeClassKappa_affineRamanujanResidue] at hb
  refine hb.trans ?_
  calc
    _ ≤ (ε / ((q : ℝ) * q.totient)) * ((q : ℝ) * q.totient) :=
      mul_le_mul_of_nonneg_left (sum_abs_affine_residue_le n b) (div_nonneg hε.le hM.le)
    _ = ε := div_mul_cancel₀ ε hM.ne'

/-- Reciprocal shell weight, extended by zero at the origin. -/
def reciprocalShellWeight (φ : ℝ → ℝ) (a t : ℝ) : ℝ :=
  if t = 0 then 0 else shellAutocorr φ (a / t)

section Shell

variable {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
  (hsupp : ∀ u : ℝ, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0)
include hφ hsupp

/-- Compact autocorrelation support makes the reciprocal weight vanish near zero. -/
theorem reciprocalShellWeight_zero_near {a : ℝ} (ha : 0 < a) {t : ℝ}
    (ht : |t| < a) : reciprocalShellWeight φ a t = 0 := by
  by_cases ht0 : t = 0
  · simp only [reciprocalShellWeight, if_pos ht0]
  · rw [reciprocalShellWeight, if_neg ht0]
    apply shellAutocorr_eq_zero_of_one_le_abs hφ hsupp
    rw [abs_div, abs_of_pos ha]
    exact (one_le_div (abs_pos.mpr ht0)).mpr ht.le

/-- The zero extension of a reciprocal shell weight remains twice continuously differentiable. -/
theorem contDiff_reciprocalShellWeight {a : ℝ} (ha : 0 < a) :
    ContDiff ℝ 2 (reciprocalShellWeight φ a) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : t = 0
  · subst t
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [continuous_abs.continuousAt.eventually
      (gt_mem_nhds (by simpa only [abs_zero] using ha : |(0 : ℝ)| < a))] with u hu
    exact reciprocalShellWeight_zero_near hφ hsupp ha hu
  · have hc : ContDiffAt ℝ 2 (fun u : ℝ => a / u) t :=
      contDiffAt_const.div contDiffAt_id ht
    have hcomp := (contDiff_shellAutocorr hφ hsupp).contDiffAt.comp t hc
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds ht] with u hu
    exact if_neg hu

/-- The reciprocal change of variables identifies the logarithmic shell integral. -/
theorem integral_reciprocalShellWeight {a : ℝ} (ha : 0 < a) :
    (∫ t in (0 : ℝ)..1, reciprocalShellWeight φ a t / t) =
      ∫ u in a..1, shellAutocorr φ u / u := by
  let δ := a / (1 + a)
  have hδ : 0 < δ := div_pos ha (by positivity)
  have hδ1 : δ < 1 := (div_lt_one (by positivity)).mpr (by linarith only [ha])
  have hδa : δ < a := (div_lt_iff₀ (by positivity : 0 < 1 + a)).mpr (by
    nlinarith only [sq_pos_of_pos ha])
  have hW := (contDiff_reciprocalShellWeight hφ hsupp ha).continuous
  have hWC := continuous_div_self_of_flat hW ha
    (fun t ht => reciprocalShellWeight_zero_near hφ hsupp ha ht)
  have hzero : (∫ t in (0 : ℝ)..δ, reciprocalShellWeight φ a t / t) = 0 := by
    calc
      _ = ∫ t in (0 : ℝ)..δ, (0 : ℝ) := by
        refine intervalIntegral.integral_congr fun t ht => ?_
        rw [Set.uIcc_of_le hδ.le] at ht
        rw [reciprocalShellWeight_zero_near hφ hsupp ha (by
          rw [abs_of_nonneg ht.1]
          exact ht.2.trans_lt hδa), zero_div]
      _ = 0 := intervalIntegral.integral_zero
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hWC.intervalIntegrable (μ := volume) 0 δ) (hWC.intervalIntegrable (μ := volume) δ 1)
  rw [hzero, zero_add] at hsplit
  rw [← hsplit]
  have hscale : (∫ t in δ..1, reciprocalShellWeight φ a t / t) =
      ∫ s in (δ / a)..(1 / a), s⁻¹ * shellAutocorr φ (1 * s⁻¹) := by
    have hc := intervalIntegral.integral_comp_div
      (fun s : ℝ => s⁻¹ * shellAutocorr φ (1 * s⁻¹)) ha.ne' (a := δ) (b := 1)
    have hcongr : (∫ t in δ..1, (fun s : ℝ => s⁻¹ * shellAutocorr φ (1 * s⁻¹)) (t / a)) =
        a * ∫ t in δ..1, reciprocalShellWeight φ a t / t := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le hδ1.le] at ht
      have ht0 : t ≠ 0 := (hδ.trans_le ht.1).ne'
      simp only [reciprocalShellWeight, if_neg ht0, one_mul, inv_div]
      ring
    rw [hcongr, smul_eq_mul] at hc
    exact (mul_left_cancel₀ ha.ne' hc)
  have hchange := integral_shell_change hφ hsupp (div_pos hδ ha)
    (div_le_div_of_nonneg_right hδ1.le ha.le) (j := 1) le_rfl
  simp only [Nat.cast_one] at hchange
  rw [hscale, hchange]
  have hend : (1 : ℝ) / (δ / a) = 1 + a := by
    dsimp only [δ]
    field_simp
  simp only [one_div_one_div, hend]
  have htail : (∫ u in (1 : ℝ)..(1 + a), shellAutocorr φ u / u) = 0 := by
    have h := integral_shell_eq_zero_of_one_le hφ hsupp (by linarith only [ha] : 1 ≤ 1 + a)
    rw [intervalIntegral.integral_symm] at h
    exact neg_eq_zero.mp h
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_shellAutocorr_div hφ hsupp ha zero_lt_one)
    (intervalIntegrable_shellAutocorr_div hφ hsupp zero_lt_one (by positivity : 0 < 1 + a))
  rw [htail, add_zero] at hadd
  exact hadd.symm

end Shell

/-- The literal Mangoldt source in one affine reciprocal shell. -/
def affineRamanujanPrimeShell (q n b : ℕ) (φ : ℝ → ℝ) (c : ℝ) (h : ℕ) (X : ℝ) : ℝ :=
  ∑ k ∈ Icc 1 ⌊X⌋₊, (ArithmeticFunction.vonMangoldt k : ℝ) / k *
    ramanujanLagCoefficient q (k * n + b) * shellAutocorr φ ((h : ℝ) * X / (c * k))

theorem affineRamanujanPrimeShell_eq_weighted (q n b : ℕ) (φ : ℝ → ℝ)
    {c : ℝ} (hc : 0 < c) (h : ℕ) {X : ℝ} (hX : 0 < X) :
    affineRamanujanPrimeShell q n b φ c h X =
      weightedAffineRamanujanPrimeReading q n b (reciprocalShellWeight φ (h / c)) X := by
  unfold affineRamanujanPrimeShell weightedAffineRamanujanPrimeReading
  refine sum_congr rfl fun k hk => ?_
  have hk0 : (k : ℝ) ≠ 0 := by
    have hkpos : 0 < k := (mem_Icc.mp hk).1
    exact_mod_cast hkpos.ne'
  rw [reciprocalShellWeight, if_neg (div_ne_zero hk0 hX.ne')]
  congr 2
  field_simp

/-- One horizon identifies every affine weighted shell with its signed unit mean. -/
theorem eventually_affineRamanujanPrimeShell_uniform {q : ℕ} (hq : 0 < q)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u : ℝ, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0)
    {c : ℝ} (hc : 0 < c) {h : ℕ} (hh : 1 ≤ h) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop, ∀ n b : ℕ,
      |affineRamanujanPrimeShell q n b φ c h X -
        (ramanujanLagCoefficient q n * ramanujanLagCoefficient q b / (q.totient : ℝ)) *
          ∫ u in ((h : ℝ) / c)..1, shellAutocorr φ u / u| ≤ ε := by
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have ha : 0 < (h : ℝ) / c := div_pos hhR hc
  have hw := (contDiff_reciprocalShellWeight hφ hsupp ha).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hlim := eventually_weightedAffineRamanujanPrimeReading_uniform hq hw ha
    (fun t ht => reciprocalShellWeight_zero_near hφ hsupp ha ht) hε
  rw [integral_reciprocalShellWeight hφ hsupp ha] at hlim
  filter_upwards [hlim, eventually_gt_atTop (0 : ℝ)] with X hX hX0
  intro n b
  rw [affineRamanujanPrimeShell_eq_weighted q n b φ hc h hX0]
  exact hX n b

open SpacingScaleHarmonicAnalysis in
/-- The explicit boosted spline has the same source law, with no profile premise. -/
theorem eventually_tiltedUnitSpline_affinePrimeShell_uniform {q : ℕ} (hq : 0 < q)
    {c : ℝ} (hc : 0 < c) {h : ℕ} (hh : 1 ≤ h) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop, ∀ n b : ℕ,
      |affineRamanujanPrimeShell q n b tiltedUnitSpline c h X -
        (ramanujanLagCoefficient q n * ramanujanLagCoefficient q b / (q.totient : ℝ)) *
          ∫ u in ((h : ℝ) / c)..1, shellAutocorr tiltedUnitSpline u / u| ≤ ε :=
  eventually_affineRamanujanPrimeShell_uniform hq contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero hc hh hε

/-- The sum of literal affine Mangoldt readings for all successor shells. -/
def affinePrimeShellCorrection (q n : ℕ) (φ : ℝ → ℝ) (c X : ℝ) : ℝ :=
  2 / (∫ u, φ u ^ 2) * ∑ h ∈ Ico 1 ⌈c⌉₊, affineRamanujanPrimeShell q n h φ c h X

/-- The actual weighted source realizes the full signed conductor correction. -/
theorem eventually_affinePrimeShellCorrection_uniform {q : ℕ} (hq : 0 < q)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u : ℝ, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0)
    {c : ℝ} (hc : 0 < c) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop, ∀ n : ℕ,
      |affinePrimeShellCorrection q n φ c X -
        ramanujanLagCoefficient q n * shellCorrection φ c q| ≤ ε := by
  let S := Ico 1 ⌈c⌉₊
  let A := 2 / (∫ u, φ u ^ 2)
  let δ := ε / (|A| * S.card + 1)
  have hden : 0 < |A| * (S.card : ℝ) + 1 := by positivity
  have hδ : 0 < δ := div_pos hε hden
  have hδeq : δ * (|A| * S.card + 1) = ε := div_mul_cancel₀ ε hden.ne'
  -- The overlap fixes a finite shell family, so their common horizon is uniform in the mode index.
  have hevent : ∀ᶠ X : ℝ in atTop, ∀ h : S, ∀ n b : ℕ,
      |affineRamanujanPrimeShell q n b φ c h X -
        (ramanujanLagCoefficient q n * ramanujanLagCoefficient q b / (q.totient : ℝ)) *
          ∫ u in ((h : ℕ) : ℝ) / c..1, shellAutocorr φ u / u| ≤ δ := by
    apply Filter.eventually_all.mpr
    intro h
    exact eventually_affineRamanujanPrimeShell_uniform hq hφ hsupp hc
      (mem_Ico.mp h.property).1 hδ
  filter_upwards [hevent] with X hX
  intro n
  have heq : affinePrimeShellCorrection q n φ c X -
      ramanujanLagCoefficient q n * shellCorrection φ c q =
      A * ∑ h ∈ S, (affineRamanujanPrimeShell q n h φ c h X -
        (ramanujanLagCoefficient q n * ramanujanLagCoefficient q h / (q.totient : ℝ)) *
          ∫ u in ((h : ℝ) / c)..1, shellAutocorr φ u / u) := by
    simp only [affinePrimeShellCorrection, shellCorrection, S, A, sum_sub_distrib,
      mul_sub, mul_sum, div_eq_mul_inv, mul_inv_rev]
    congr 1
    exact sum_congr rfl fun h _ => by ring
  rw [heq, abs_mul]
  calc
    _ ≤ |A| * ∑ h ∈ S, |affineRamanujanPrimeShell q n h φ c h X -
        (ramanujanLagCoefficient q n * ramanujanLagCoefficient q h / (q.totient : ℝ)) *
          ∫ u in ((h : ℝ) / c)..1, shellAutocorr φ u / u| :=
      mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (abs_nonneg _)
    _ ≤ |A| * ∑ _h ∈ S, δ := mul_le_mul_of_nonneg_left
      (sum_le_sum fun h hh => hX ⟨h, hh⟩ n h) (abs_nonneg _)
    _ ≤ ε := by
      rw [sum_const, nsmul_eq_mul]
      nlinarith only [hδeq, hδ]

/-- The source correction is exactly the decrement from reference to completed energy. -/
theorem eventually_affinePrimeShellCorrection_energy_uniform {q : ℕ} (hq : 0 < q)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u : ℝ, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0)
    {c : ℝ} (hc : 0 < c) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop, ∀ n : ℕ,
      |affinePrimeShellCorrection q n φ c X - ramanujanLagCoefficient q n *
        (completeWeilAdjunctionEnergy φ c q - completedConductorEnergy φ c q)| ≤ ε := by
  have hlim := eventually_affinePrimeShellCorrection_uniform hq hφ hsupp hc hε
  simpa only [completedConductorEnergy_eq_sub_shellCorrection hc hq, sub_sub_cancel] using hlim

open SpacingScaleHarmonicAnalysis in
/-- The explicit profile realizes the entire signed decrement to the positive completed energy. -/
theorem eventually_tiltedUnitSpline_affineShellCorrection_energy {q : ℕ} (hq : 0 < q)
    {c : ℝ} (hc : 0 < c) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop, ∀ n : ℕ,
      |affinePrimeShellCorrection q n tiltedUnitSpline c X - ramanujanLagCoefficient q n *
        (completeWeilAdjunctionEnergy tiltedUnitSpline c q -
          completedConductorEnergy tiltedUnitSpline c q)| ≤ ε :=
  eventually_affinePrimeShellCorrection_energy_uniform hq contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero hc hε

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_affineRamanujanPrimeShell_uniform
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_tiltedUnitSpline_affinePrimeShell_uniform

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_affinePrimeShellCorrection_energy_uniform

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_tiltedUnitSpline_affineShellCorrection_energy
