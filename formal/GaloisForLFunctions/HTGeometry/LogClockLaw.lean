import GaloisForLFunctions.HTGeometry.LaplaceContinuityHalfLine

/-!
# Logarithmic clock laws of an arithmetic weight

A summable nonnegative weight on the integers, placed at the logarithms of those integers, is a law
on the half line.  Its Laplace transform at `u` is the Dirichlet series of the weight shifted by
`u`, because `e^{-u log n} = n^{-u}`.  These are the clocks of a Dirichlet weight system: the
transport layer consumes exactly this Laplace transform and this mean.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The clock law of a weight on the integers, placed at logarithmic points. -/
def logClockLaw (w : ℕ → ℝ) : Measure ℝ :=
  weightedPointLaw (fun n : ℕ => Real.log n) (fun n => ENNReal.ofReal (w n))

/-- A nonnegative weight of total mass one gives a law. -/
theorem isProbabilityMeasure_logClockLaw {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    (hsum : ∑' n, w n = 1) : IsProbabilityMeasure (logClockLaw w) := by
  refine isProbabilityMeasure_weightedPointLaw _ _ ?_
  have hsummable : Summable w := by
    by_contra hcon
    rw [tsum_eq_zero_of_not_summable hcon] at hsum
    exact absurd hsum (by norm_num)
  rw [← ENNReal.ofReal_tsum_of_nonneg hw hsummable, hsum, ENNReal.ofReal_one]

/-- A logarithmic clock law is carried by the half line. -/
theorem logClockLaw_Iio_zero (w : ℕ → ℝ) : logClockLaw w (Iio 0) = 0 :=
  weightedPointLaw_Iio_zero _ _ fun n => Real.log_natCast_nonneg n

/-- The exponential of a logarithmic point is the corresponding power. -/
theorem exp_neg_mul_log_natCast {u : ℝ} {n : ℕ} (hn : n ≠ 0) :
    Real.exp (-(u * Real.log n)) = (n : ℝ) ^ (-u) := by
  have hpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  rw [Real.rpow_def_of_pos hpos]
  ring_nf

/-- The exponential decay factor of a half-line law is integrable. -/
theorem integrable_exp_neg_logClockLaw {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    (hsum : ∑' n, w n = 1) {u : ℝ} (hu : 0 ≤ u) :
    Integrable (fun y => Real.exp (-(u * y))) (logClockLaw w) := by
  haveI := isProbabilityMeasure_logClockLaw hw hsum
  refine Integrable.mono' (integrable_const 1)
    ((Real.measurable_exp.comp ((measurable_const.mul measurable_id).neg)).aestronglyMeasurable) ?_
  filter_upwards [ae_nonneg_of_Iio_zero (logClockLaw_Iio_zero w)] with y hy
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
  nlinarith

/-- **Laplace transform of a logarithmic clock law.**  It is the Dirichlet series of the weight at
the shifted abscissa. -/
theorem integral_exp_neg_logClockLaw {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) (hw0 : w 0 = 0)
    (hsum : ∑' n, w n = 1) {u : ℝ} (hu : 0 ≤ u) :
    (∫ y, Real.exp (-(u * y)) ∂(logClockLaw w)) = ∑' n : ℕ, w n * (n : ℝ) ^ (-u) := by
  haveI := isProbabilityMeasure_logClockLaw hw hsum
  rw [logClockLaw, integral_weightedPointLaw _ _ (integrable_exp_neg_logClockLaw hw hsum hu)]
  refine tsum_congr fun n => ?_
  rw [ENNReal.toReal_ofReal (hw n)]
  by_cases hn : n = 0
  · subst hn
    rw [hw0]
    ring
  · rw [exp_neg_mul_log_natCast hn]

/-- **Mean of a logarithmic clock law.**  It is the logarithmically weighted Dirichlet sum. -/
theorem integral_id_logClockLaw {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    (hint : Integrable (id : ℝ → ℝ) (logClockLaw w)) :
    (∫ y, y ∂(logClockLaw w)) = ∑' n : ℕ, w n * Real.log n := by
  have h := integral_id_weightedPointLaw (fun n : ℕ => Real.log n)
    (fun n => ENNReal.ofReal (w n)) hint
  rw [logClockLaw, h]
  exact tsum_congr fun n => by rw [ENNReal.toReal_ofReal (hw n)]

/-- **Critical transport for logarithmic clock laws.**  If the Dirichlet series of a family of
arithmetic weights converges at every natural shift to the Laplace transform of the mean-one
exponential law, and the logarithmically weighted means converge to one, then the monotone
couplings of the clocks with that law have vanishing transport cost. -/
theorem tendsto_integral_monotoneCoupling_logClock {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] (w : ι → ℕ → ℝ) (hw : ∀ i n, 0 ≤ w i n) (hw0 : ∀ i, w i 0 = 0)
    (hsum : ∀ i, ∑' n, w i n = 1)
    (hint : ∀ i, Integrable (id : ℝ → ℝ) (logClockLaw (w i)))
    (hlap : ∀ k : ℕ, Tendsto (fun i => ∑' n : ℕ, w i n * (n : ℝ) ^ (-(k : ℝ))) l
      (𝓝 (∫ x, Real.exp (-((k : ℝ) * x)) ∂(expMeasure 1))))
    (hmean : Tendsto (fun i => ∑' n : ℕ, w i n * Real.log n) l (𝓝 1)) :
    Tendsto (fun i => ∫ z, |z.1 - z.2| ∂(monotoneCoupling (logClockLaw (w i)) (expMeasure 1))) l
      (𝓝 0) := by
  haveI : ∀ i, IsProbabilityMeasure (logClockLaw (w i)) := fun i =>
    isProbabilityMeasure_logClockLaw (hw i) (hsum i)
  refine tendsto_integral_monotoneCoupling_of_tendsto_laplace _
    (fun i => logClockLaw_Iio_zero (w i)) hint ?_ ?_
  · intro k
    refine (hlap k).congr fun i => ?_
    exact (integral_exp_neg_logClockLaw (hw i) (hw0 i) (hsum i) (by positivity)).symm
  · refine hmean.congr fun i => ?_
    exact (integral_id_logClockLaw (hw i) (hint i)).symm

/-- The logarithm of a natural number vanishes exactly at zero and one. -/
theorem log_natCast_eq_zero_iff (n : ℕ) : Real.log n = 0 ↔ n = 0 ∨ n = 1 := by
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    have h2 : 2 ≤ n := by omega
    have hlt : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    exact absurd h (ne_of_gt (Real.log_pos hlt))
  · rintro (rfl | rfl) <;> simp

/-- **The atom of a logarithmic clock at the origin.**  Only the trivial index contributes, so the
mass at the origin is the weight of one. -/
theorem logClockLaw_singleton_zero {w : ℕ → ℝ} (hw0 : w 0 = 0) :
    logClockLaw w {(0 : ℝ)} = ENNReal.ofReal (w 1) := by
  classical
  rw [logClockLaw, weightedPointLaw_apply _ _ (measurableSet_singleton (0 : ℝ))]
  have hterm : ∀ n : ℕ, ({(0 : ℝ)} : Set ℝ).indicator
      (fun _ => ENNReal.ofReal (w n)) (Real.log n)
      = if n = 1 then ENNReal.ofReal (w 1) else 0 := by
    intro n
    by_cases hn : Real.log n = 0
    · rw [Set.indicator_of_mem (by simpa using hn)]
      rcases (log_natCast_eq_zero_iff n).mp hn with h0 | h1
      · subst h0
        rw [hw0]
        simp
      · subst h1
        simp
    · rw [Set.indicator_of_notMem (by simpa using hn)]
      have hne : n ≠ 1 := by
        intro h
        exact hn (by simp [h])
      simp [hne]
  rw [tsum_congr hterm, tsum_ite_eq]

end

end GaloisForLFunctions.HTGeometry
