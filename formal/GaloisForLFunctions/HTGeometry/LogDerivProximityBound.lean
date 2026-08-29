import GaloisForLFunctions.HTGeometry.AlphaProximityEstimate
import GaloisForLFunctions.HTGeometry.LogDerivPoissonJensen

/-!
# Nevanlinna's estimate for the proximity of a logarithmic derivative

Integrating the Poisson–Jensen pointwise bound

```text
‖f'/f (w)‖ ≤ ‖∑_u n_u (1/(w−u) + ū/(R² − ū w))‖ + 2R/(R−r)² · (2T(R,f) + C₀)
```

against the `α`-power `log⁺` estimate.  The divisor enters only through the total `α`-power of its
multiplicities, because the circle average of `‖w − u‖^{-α}` is bounded uniformly in `u`; the
`log⁺` average therefore costs only the logarithm of that total, of `1/(R − r)`, and of the boundary
term.

This is the estimate the corpus's `SecondMainTheoremChain` still needed: the earlier integration of
the same pointwise bound cost `log 2` per divisor point, which is `O(T(R,f))` and so can never be an
`S(r,f)`.

The two lemmas here are the null-set bookkeeping: the pointwise Poisson–Jensen bound holds at a
circle point only away from the divisor, and the angles of a circle that hit a finite set of points
form a countable, hence null, set.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Real Metric

/-- The angles of a circle hitting a fixed point form a countable set. -/
theorem countable_circle_preimage_point {r : ℝ} (hr : 0 < r) (u : ℂ) :
    {θ : ℝ | (r : ℂ) * Complex.exp (θ * Complex.I) = u}.Countable := by
  classical
  rcases Set.eq_empty_or_nonempty {θ : ℝ | (r : ℂ) * Complex.exp (θ * Complex.I) = u} with h | h
  · rw [h]
    exact Set.countable_empty
  obtain ⟨θ₀, hθ₀⟩ := h
  have hrne : (r : ℂ) ≠ 0 := by
    simpa using ne_of_gt hr
  refine Set.Countable.mono ?_ (Set.countable_range fun n : ℤ => θ₀ + 2 * π * (n : ℝ))
  intro θ hθ
  rw [Set.mem_setOf_eq] at hθ hθ₀
  have hexp : Complex.exp ((θ : ℂ) * Complex.I) = Complex.exp ((θ₀ : ℂ) * Complex.I) := by
    have := hθ.trans hθ₀.symm
    exact mul_left_cancel₀ hrne this
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
  refine ⟨n, ?_⟩
  have hI : (Complex.I) ≠ 0 := Complex.I_ne_zero
  have hstep : (θ : ℂ) = (θ₀ : ℂ) + (n : ℂ) * (2 * π) := by
    have hfac : (θ : ℂ) * Complex.I = ((θ₀ : ℂ) + (n : ℂ) * (2 * π)) * Complex.I := by
      rw [hn]
      push_cast
      ring
    exact mul_right_cancel₀ hI hfac
  have hre : θ = θ₀ + (n : ℝ) * (2 * π) := by
    exact_mod_cast hstep
  rw [hre]
  ring

/-- The angles of a circle hitting a finite set form a countable set. -/
theorem countable_circle_preimage_finset {r : ℝ} (hr : 0 < r) (S : Finset ℂ) :
    {θ : ℝ | (r : ℂ) * Complex.exp (θ * Complex.I) ∈ (S : Set ℂ)}.Countable := by
  have heq : {θ : ℝ | (r : ℂ) * Complex.exp (θ * Complex.I) ∈ (S : Set ℂ)}
      = ⋃ u ∈ (S : Set ℂ), {θ : ℝ | (r : ℂ) * Complex.exp (θ * Complex.I) = u} := by
    ext θ
    simp
  rw [heq]
  exact Set.Countable.biUnion S.countable_toSet fun u _ => countable_circle_preimage_point hr u


/-- For an entire function whose order is finite at every point, a point of vanishing divisor is a
point where the function does not vanish. -/
theorem ne_zero_of_divisor_eq_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf0 : ∀ z, meromorphicOrderAt f z ≠ ⊤) {U : Set ℂ} (hU : MeromorphicOn f U)
    {w : ℂ} (hw : w ∈ U) (hdiv : MeromorphicOn.divisor f U w = 0) : f w ≠ 0 := by
  have hana : AnalyticAt ℂ f w := hf.analyticAt w
  have hval := MeromorphicOn.divisor_apply hU hw
  rw [hdiv] at hval
  have hord : meromorphicOrderAt f w = 0 := by
    set x := meromorphicOrderAt f w with hx
    have hxne : x ≠ ⊤ := hf0 w
    lift x to ℤ using hxne with n
    have hn : (n : ℤ) = 0 := by
      have := hval.symm
      simpa using this
    simp [hn]
  have hmap : meromorphicOrderAt f w = ENat.map Nat.cast (analyticOrderAt f w) :=
    hana.meromorphicOrderAt_eq
  rw [hmap] at hord
  have hazero : analyticOrderAt f w = 0 := by
    cases hcase : analyticOrderAt f w with
    | top =>
        rw [hcase] at hord
        simp at hord
    | coe m =>
        rw [hcase] at hord
        have hm : m = 0 := by simpa using hord
        simp [hm]
  exact (AnalyticAt.analyticOrderAt_eq_zero hana).mp hazero

open ValueDistribution in
/-- **Nevanlinna's logarithmic-derivative estimate for an entire function.**  The `log⁺` circle
average of `f'/f` at radius `r` costs only the logarithm of the total `α`-power divisor weight in the
disc of radius `R`, of `1/(R − r)`, and of the boundary term built from the characteristic. -/
theorem circleAverage_posLog_logDeriv_le_of_entire {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hR : 1 ≤ R) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hf0 : ∀ z, meromorphicOrderAt f z ≠ ⊤)
    (hbd : ∀ u ∈ sphere (0 : ℂ) |R|,
      MeromorphicOn.divisor f (closedBall (0 : ℂ) |R|) u = 0) :
    (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π),
        Real.posLog ‖logDeriv f ((r : ℂ) * Complex.exp (θ * Complex.I))‖
      ≤ (1 / α) * Real.log (1 +
          ((2 * π)⁻¹ * ((∑ᶠ u : ℂ,
              (|(MeromorphicOn.divisor f (closedBall (0 : ℂ) |R|) u : ℤ)| : ℝ) ^ α)
            * (r ^ (-α) * sinNegPowerConst α + 2 * π * (R - r) ^ (-α)))
          + (2 * R / (R - r) ^ 2
              * (2 * characteristic f ⊤ R
                + max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖|)) ^ α)) := by
  classical
  have hRpos : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR
  have habsR : |R| = R := abs_of_pos hRpos
  set CB : Set ℂ := closedBall (0 : ℂ) |R| with hCB
  set D : ℂ → ℤ := fun u => MeromorphicOn.divisor f CB u with hD
  have hana : ∀ z, AnalyticAt ℂ f z := fun z => hf.analyticAt z
  have hfm : Meromorphic f := fun z => (hana z).meromorphicAt
  have h₁f : MeromorphicOn f CB := fun z _ => hfm z
  have h₂f : ∀ u : (CB : Set ℂ), meromorphicOrderAt f u ≠ ⊤ := fun u => hf0 u
  have hfin : (Function.support D).Finite :=
    (MeromorphicOn.divisor f CB).finiteSupport (isCompact_closedBall (0 : ℂ) |R|)
  set S : Finset ℂ := hfin.toFinset with hS
  have hDsupp : ∀ u, D u ≠ 0 → u ∈ S := by
    intro u hu
    rw [hS, Set.Finite.mem_toFinset]
    exact hu
  have hDball : ∀ u ∈ S, ‖u‖ ≤ R := by
    intro u hu
    rw [hS, Set.Finite.mem_toFinset] at hu
    have hmem : u ∈ CB := (MeromorphicOn.divisor f CB).supportWithinDomain hu
    rw [hCB, mem_closedBall, dist_zero_right, habsR] at hmem
    exact hmem
  set B : ℝ := 2 * R / (R - r) ^ 2
    * (2 * characteristic f ⊤ R
      + max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖|) with hB
  have hB0 : 0 ≤ B := by
    have hchar : 0 ≤ characteristic f ⊤ R := by
      have h1 : (0 : ℝ) ≤ proximity f ⊤ R := proximity_nonneg R
      have h2 : (0 : ℝ) ≤ logCounting f ⊤ R := logCounting_nonneg hR
      have hsplit : characteristic f ⊤ R = proximity f ⊤ R + logCounting f ⊤ R := rfl
      linarith
    have hmax : 0 ≤ max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖| :=
      le_trans (abs_nonneg _) (le_max_left _ _)
    rw [hB]
    have hcoef : (0 : ℝ) ≤ 2 * R / (R - r) ^ 2 := by positivity
    have hinner : (0 : ℝ) ≤ 2 * characteristic f ⊤ R
        + max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖| := by linarith
    exact mul_nonneg hcoef hinner
  -- measurability of the integrand
  have hcircle : Continuous fun θ : ℝ => (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
    refine continuous_const.mul (Complex.continuous_exp.comp ?_)
    exact Complex.continuous_ofReal.mul continuous_const
  have hcderiv : Continuous fun θ : ℝ => deriv f ((r : ℂ) * Complex.exp (θ * Complex.I)) :=
    (hf.deriv).continuous.comp hcircle
  have hcf : Continuous fun θ : ℝ => f ((r : ℂ) * Complex.exp (θ * Complex.I)) :=
    hf.continuous.comp hcircle
  have hmeas : Measurable fun θ : ℝ =>
      ‖logDeriv f ((r : ℂ) * Complex.exp (θ * Complex.I))‖ := by
    have hEq : (fun θ : ℝ => ‖logDeriv f ((r : ℂ) * Complex.exp (θ * Complex.I))‖)
        = fun θ : ℝ => ‖deriv f ((r : ℂ) * Complex.exp (θ * Complex.I))
            / f ((r : ℂ) * Complex.exp (θ * Complex.I))‖ := by
      funext θ
      simp [logDeriv]
    rw [hEq]
    exact (hcderiv.measurable.div hcf.measurable).norm
  -- the a.e. pointwise bound
  have hae : ∀ᵐ θ : ℝ, ‖logDeriv f ((r : ℂ) * Complex.exp (θ * Complex.I))‖
      ≤ ‖∑ᶠ u : ℂ, (D u : ℂ) * (1 / ((r : ℂ) * Complex.exp (θ * Complex.I) - u)
        + (starRingEnd ℂ) u
          / ((R : ℂ) ^ 2 - (starRingEnd ℂ) u * ((r : ℂ) * Complex.exp (θ * Complex.I))))‖ + B := by
    have hnull : (volume : Measure ℝ)
        {θ : ℝ | (r : ℂ) * Complex.exp (θ * Complex.I) ∈ (S : Set ℂ)} = 0 :=
      (countable_circle_preimage_finset hr S).measure_zero volume
    have hcompl : ∀ᵐ θ : ℝ, (r : ℂ) * Complex.exp (θ * Complex.I) ∉ (S : Set ℂ) := by
      rw [MeasureTheory.ae_iff]
      simpa using hnull
    filter_upwards [hcompl] with θ hθ
    set w : ℂ := (r : ℂ) * Complex.exp (θ * Complex.I) with hw
    have hwn : ‖w‖ = r := by
      rw [hw, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      simp
    have hwball : w ∈ ball (0 : ℂ) R := by
      rw [mem_ball, dist_zero_right, hwn]
      exact hrR
    have hwdiv : MeromorphicOn.divisor f CB w = 0 := by
      by_contra hcon
      exact hθ (Finset.mem_coe.mpr (hDsupp w hcon))
    have hwCB : w ∈ CB := by
      rw [hCB, mem_closedBall, dist_zero_right, habsR, hwn]
      linarith
    have hfw : f w ≠ 0 := ne_zero_of_divisor_eq_zero hf hf0 h₁f hwCB hwdiv
    have hbase := PoissonJensen.norm_logDeriv_le_characteristic hR hfm h₂f hbd hwball
      (hana w) hfw hwdiv
    simp only [sub_zero] at hbase
    rw [hwn] at hbase
    exact hbase
  -- apply the α-power estimate
  have hkey := circleAverage_posLog_le_of_poissonJensen hα0 hα1 hr hrR D S hDsupp hDball hB0
    (logDeriv f) hmeas hae
  have hweight : (∑ᶠ u : ℂ, (|D u| : ℝ) ^ α) = ∑ u ∈ S, (|D u| : ℝ) ^ α := by
    refine finsum_eq_sum_of_support_subset _ ?_
    intro u hu
    rw [Function.mem_support] at hu
    refine Finset.mem_coe.mpr (hDsupp u ?_)
    intro hzero
    apply hu
    rw [hzero]
    simp [Real.zero_rpow (ne_of_gt hα0)]
  rw [hweight]
  exact hkey


open ValueDistribution in
/-- The proximity of `f'/f` is the `log⁺` circle average of the logarithmic derivative. -/
theorem proximity_logDeriv_eq {f : ℂ → ℂ} {r : ℝ} :
    proximity (fun z => deriv f z / f z) ⊤ r
      = (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π),
          Real.posLog ‖logDeriv f ((r : ℂ) * Complex.exp (θ * Complex.I))‖ := by
  rw [proximity_top, Real.circleAverage, smul_eq_mul]
  congr 1
  refine intervalIntegral.integral_congr fun θ _ => ?_
  have hcm : circleMap 0 r θ = (r : ℂ) * Complex.exp (θ * Complex.I) := by
    rw [circleMap, zero_add]
  rw [hcm]
  simp [logDeriv]

open ValueDistribution in
/-- The proximity of `f'/(f − a)` is the `log⁺` circle average of the logarithmic derivative of the
shift `f − a`. -/
theorem proximity_logDeriv_sub_const_eq {f : ℂ → ℂ} (hf : Differentiable ℂ f) (a : ℂ) {r : ℝ} :
    proximity (fun z => deriv f z / (f z - a)) ⊤ r
      = (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π),
          Real.posLog ‖logDeriv (fun w => f w - a)
            ((r : ℂ) * Complex.exp (θ * Complex.I))‖ := by
  have hderiv : ∀ z : ℂ, deriv (fun w => f w - a) z = deriv f z := fun z => by
    simp [deriv_sub_const]
  have hlog : ∀ z : ℂ, logDeriv (fun w => f w - a) z = deriv f z / (f z - a) := by
    intro z
    rw [logDeriv]
    simp [hderiv z]
  rw [proximity_top, Real.circleAverage, smul_eq_mul]
  congr 1
  refine intervalIntegral.integral_congr fun θ _ => ?_
  rw [hlog]
  congr 2
  rw [circleMap, zero_add]

open ValueDistribution in
/-- **The proximity of `f'/(f − a)` for an entire `f`**, in the form the corpus's second main
theorem consumes.  This is the logarithmic-derivative estimate applied to the shift `f − a`. -/
theorem proximity_logDeriv_sub_const_le {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hR : 1 ≤ R) {f : ℂ → ℂ} (a : ℂ)
    (hf : Differentiable ℂ f)
    (hf0 : ∀ z, meromorphicOrderAt (fun w => f w - a) z ≠ ⊤)
    (hbd : ∀ u ∈ sphere (0 : ℂ) |R|,
      MeromorphicOn.divisor (fun w => f w - a) (closedBall (0 : ℂ) |R|) u = 0) :
    proximity (fun z => deriv f z / (f z - a)) ⊤ r
      ≤ (1 / α) * Real.log (1 +
          ((2 * π)⁻¹ * ((∑ᶠ u : ℂ,
              (|(MeromorphicOn.divisor (fun w => f w - a) (closedBall (0 : ℂ) |R|) u : ℤ)| : ℝ) ^ α)
            * (r ^ (-α) * sinNegPowerConst α + 2 * π * (R - r) ^ (-α)))
          + (2 * R / (R - r) ^ 2
              * (2 * characteristic (fun w => f w - a) ⊤ R
                + max |Real.log ‖(fun w => f w - a) 0‖|
                  |Real.log ‖meromorphicTrailingCoeffAt (fun w => f w - a) 0‖|)) ^ α)) := by
  have hg : Differentiable ℂ (fun w => f w - a) := hf.sub_const a
  have hderiv : ∀ z : ℂ, deriv (fun w => f w - a) z = deriv f z := fun z => by
    simp [deriv_sub_const]
  have hlog : ∀ z : ℂ, logDeriv (fun w => f w - a) z = deriv f z / (f z - a) := by
    intro z
    rw [logDeriv]
    simp [hderiv z]
  have hmain := circleAverage_posLog_logDeriv_le_of_entire hα0 hα1 hr hrR hR hg hf0 hbd
  have hprox : proximity (fun z => deriv f z / (f z - a)) ⊤ r
      = (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π),
          Real.posLog ‖logDeriv (fun w => f w - a) ((r : ℂ) * Complex.exp (θ * Complex.I))‖ := by
    rw [proximity_top, Real.circleAverage, smul_eq_mul]
    congr 1
    refine intervalIntegral.integral_congr fun θ _ => ?_
    rw [hlog]
    congr 2
    rw [circleMap, zero_add]
  rw [hprox]
  exact hmain

end GaloisForLFunctions.HTGeometry
