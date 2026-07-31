import GaloisForLFunctions.HTGeometry.BohrProductSpectrum

/-!
# Metric and translation properties of the Bohr mean

Two structural facts about the mean value that every approximation argument uses.

The mean is a contraction for the supremum norm: a function bounded by `C` has mean bounded by `C`,
so the mean — and therefore each Bohr coefficient — is `1`-Lipschitz in the uniform distance.  Facts
proved for trigonometric polynomials transfer to their uniform limits through this estimate.

The mean is invariant under translation: shifting the window by a fixed amount changes the integral
only by two end pieces of bounded size, which the average kills.  Consequently translation multiplies
each Bohr coefficient by the unimodular factor `e^{iλa}` and leaves the spectrum — hence the
frequency module — unchanged.
-/

open Filter Topology

namespace GaloisForLFunctions

noncomputable section

open scoped BigOperators

/-! ### The mean is a contraction -/

/-- A uniform bound on `f` bounds its mean. -/
theorem norm_bohrMean_le {f : ℝ → ℂ} (hfc : Continuous f)
    (hfa : HTGeometry.IsBohrAlmostPeriodic f) {C : ℝ} (hC : ∀ t, ‖f t‖ ≤ C) :
    ‖bohrMean f‖ ≤ C := by
  have hlim := tendsto_windowAverage_bohrMean hfc hfa
  have hnorm : Tendsto (fun T : ℝ => ‖windowAverage f T‖) atTop (nhds ‖bohrMean f‖) :=
    (continuous_norm.tendsto _).comp hlim
  refine le_of_tendsto hnorm ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  have hint : ‖∫ t in (0 : ℝ)..T, f t‖ ≤ C * |T - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const (fun x _ => hC x)
  simp only [windowAverage, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hT.le)]
  rw [sub_zero, abs_of_nonneg hT.le] at hint
  calc T⁻¹ * ‖∫ t in (0 : ℝ)..T, f t‖ ≤ T⁻¹ * (C * T) :=
        mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr hT.le)
    _ = C := by field_simp

/-- The mean is `1`-Lipschitz for the uniform distance. -/
theorem norm_bohrMean_sub_le {f g : ℝ → ℂ} (hfc : Continuous f)
    (hfa : HTGeometry.IsBohrAlmostPeriodic f) (hgc : Continuous g)
    (hga : HTGeometry.IsBohrAlmostPeriodic g) {C : ℝ} (hC : ∀ t, ‖f t - g t‖ ≤ C) :
    ‖bohrMean f - bohrMean g‖ ≤ C := by
  rw [← bohrMean_sub hfc hfa hgc hga]
  exact norm_bohrMean_le (hfc.sub hgc) (isBohrAlmostPeriodic_sub hfc hfa hgc hga) hC

/-- Each Bohr coefficient is `1`-Lipschitz for the uniform distance. -/
theorem norm_bohrCoefficient_sub_le {f g : ℝ → ℂ} (hfc : Continuous f)
    (hfa : HTGeometry.IsBohrAlmostPeriodic f) (hgc : Continuous g)
    (hga : HTGeometry.IsBohrAlmostPeriodic g) {C : ℝ} (hC : ∀ t, ‖f t - g t‖ ≤ C) (lam : ℝ) :
    ‖bohrCoefficient f lam - bohrCoefficient g lam‖ ≤ C := by
  refine norm_bohrMean_sub_le (f := fun t => f t * bohrChar lam t)
    (g := fun t => g t * bohrChar lam t) (hfc.mul (continuous_bohrChar lam))
    (isBohrAlmostPeriodic_mul_bohrChar hfc hfa lam) (hgc.mul (continuous_bohrChar lam))
    (isBohrAlmostPeriodic_mul_bohrChar hgc hga lam) (fun t => ?_)
  rw [show f t * bohrChar lam t - g t * bohrChar lam t = (f t - g t) * bohrChar lam t from by ring,
    norm_mul, norm_bohrChar, mul_one]
  exact hC t

/-! ### The mean is translation invariant -/

theorem isBohrAlmostPeriodic_comp_add_const {f : ℝ → ℂ}
    (hfa : HTGeometry.IsBohrAlmostPeriodic f) (a : ℝ) :
    HTGeometry.IsBohrAlmostPeriodic fun t => f (t + a) := by
  intro ε hε
  obtain ⟨L, hL, hdense⟩ := hfa ε hε
  refine ⟨L, hL, fun b => ?_⟩
  obtain ⟨τ, hτmem, hτ⟩ := hdense b
  refine ⟨τ, hτmem, fun x => ?_⟩
  show ‖f (x + τ + a) - f (x + a)‖ ≤ ε
  have hshift : x + τ + a = (x + a) + τ := by ring
  rw [hshift]
  exact hτ (x + a)

/-- **Translation invariance of the mean.** -/
theorem bohrMean_comp_add_const {f : ℝ → ℂ} (hfc : Continuous f)
    (hfa : HTGeometry.IsBohrAlmostPeriodic f) (a : ℝ) :
    bohrMean (fun t => f (t + a)) = bohrMean f := by
  obtain ⟨C, hC⟩ := exists_bound_of_isBohrAlmostPeriodic hfc hfa
  have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  have hint : ∀ u v : ℝ, IntervalIntegrable f MeasureTheory.volume u v := hfc.intervalIntegrable
  have hfc' : Continuous fun t : ℝ => f (t + a) := hfc.comp (continuous_id.add continuous_const)
  have hdiff : Tendsto (fun T : ℝ =>
      windowAverage (fun t => f (t + a)) T - windowAverage f T) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (g := fun T : ℝ => (2 * (C * |a|)) / T)
      (Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      have hshift : (∫ t in (0 : ℝ)..T, f (t + a)) = ∫ t in a..(T + a), f t := by
        rw [intervalIntegral.integral_comp_add_right f a]
        norm_num
      have h1 : (∫ t in (0 : ℝ)..a, f t) + ∫ t in a..(T + a), f t = ∫ t in (0 : ℝ)..(T + a), f t :=
        intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)
      have h2 : (∫ t in (0 : ℝ)..T, f t) + ∫ t in T..(T + a), f t
          = ∫ t in (0 : ℝ)..(T + a), f t :=
        intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)
      have hsub : (∫ t in a..(T + a), f t) - ∫ t in (0 : ℝ)..T, f t
          = (∫ t in T..(T + a), f t) - ∫ t in (0 : ℝ)..a, f t := by
        rw [← h2] at h1
        linear_combination h1
      have hb1 : ‖∫ t in T..(T + a), f t‖ ≤ C * |a| := by
        refine (intervalIntegral.norm_integral_le_of_norm_le_const (fun x _ => hC x)).trans ?_
        have : |T + a - T| = |a| := by congr 1; ring
        rw [this]
      have hb2 : ‖∫ t in (0 : ℝ)..a, f t‖ ≤ C * |a| := by
        refine (intervalIntegral.norm_integral_le_of_norm_le_const (fun x _ => hC x)).trans ?_
        rw [sub_zero]
      simp only [windowAverage, hshift, ← smul_sub, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr hT.le)]
      rw [hsub]
      calc T⁻¹ * ‖(∫ t in T..(T + a), f t) - ∫ t in (0 : ℝ)..a, f t‖
          ≤ T⁻¹ * (C * |a| + C * |a|) := by
            refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hT.le)
            exact (norm_sub_le _ _).trans (add_le_add hb1 hb2)
        _ = (2 * (C * |a|)) / T := by field_simp; ring
    · exact tendsto_const_nhds.div_atTop tendsto_id
  refine bohrMean_eq hfc' (isBohrAlmostPeriodic_comp_add_const hfa a) ?_
  have := hdiff.add (tendsto_windowAverage_bohrMean hfc hfa)
  simpa using this

/-- **Translation multiplies each Bohr coefficient by a unimodular factor.** -/
theorem bohrCoefficient_comp_add_const {f : ℝ → ℂ} (hfc : Continuous f)
    (hfa : HTGeometry.IsBohrAlmostPeriodic f) (a lam : ℝ) :
    bohrCoefficient (fun t => f (t + a)) lam = expChar lam a * bohrCoefficient f lam := by
  have hchar : ∀ t : ℝ, bohrChar lam t = bohrChar lam (t + a) * expChar lam a := by
    intro t
    simp only [bohrChar, expChar, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hfun : (fun t : ℝ => f (t + a) * bohrChar lam t)
      = fun t : ℝ => expChar lam a * ((fun u : ℝ => f u * bohrChar lam u) (t + a)) := by
    funext t
    rw [hchar t]
    ring
  rw [bohrCoefficient, hfun,
    bohrMean_const_mul (f := fun t : ℝ => (fun u : ℝ => f u * bohrChar lam u) (t + a))
      (expChar lam a)
      (((hfc.mul (continuous_bohrChar lam)).comp (continuous_id.add continuous_const)))
      (isBohrAlmostPeriodic_comp_add_const
        (isBohrAlmostPeriodic_mul_bohrChar hfc hfa lam) a),
    bohrMean_comp_add_const (f := fun u : ℝ => f u * bohrChar lam u)
      (hfc.mul (continuous_bohrChar lam))
      (isBohrAlmostPeriodic_mul_bohrChar hfc hfa lam) a]
  rfl

/-- **The spectrum is translation invariant.** -/
theorem bohrSpectrum_comp_add_const {f : ℝ → ℂ} (hfc : Continuous f)
    (hfa : HTGeometry.IsBohrAlmostPeriodic f) (a : ℝ) :
    bohrSpectrum (fun t => f (t + a)) = bohrSpectrum f := by
  ext lam
  simp only [bohrSpectrum, Set.mem_setOf_eq, bohrCoefficient_comp_add_const hfc hfa a lam]
  constructor
  · intro h hz
    exact h (by rw [hz, mul_zero])
  · intro h hz
    rcases mul_eq_zero.mp hz with hc | hb
    · exact absurd hc (by
        intro hzero
        have := norm_bohrChar (-lam) a
        rw [← expChar_eq_bohrChar] at this
        rw [hzero, norm_zero] at this
        norm_num at this)
    · exact h hb

end

end GaloisForLFunctions
