import GaloisForLFunctions.ArithmeticOfSquareRootPrecision.EveryRealGaugeHasAComplexCountLift
import GaloisForLFunctions.HTGeometry.LogarithmicIndependentSigns

/-!
# Product conjugation precision and the mean sine current

Independently conjugating whole Euler factors preserves every real prime-power coefficient.
For arbitrary coordinate biases, the random prime sine current differs from its deterministic
mean by square-root precision almost surely. The complex count is therefore equivalent to the
real count together with square-root control of that mean.

Fair conjugation has zero mean current. Almost every fair conjugation is consequently a complex
count lift of its real source, including when any finite prefix of phases is retained.
-/

noncomputable section
open MeasureTheory Filter Asymptotics Finset
namespace GaloisForLFunctions.ArithmeticOfSquareRootPrecision

/-- Independent choices of whether to retain each phase. Coordinate `n-1` uses bias `q n`. -/
abbrev conjugationMeasure (q : ℕ → unitInterval) : Measure (ℕ → Bool) :=
  HTGeometry.LogarithmicSigns.signLaw (fun n => q (n + 1))

/-- Conjugation acts on the whole Euler factor. Composite coordinates have no effect. -/
def conjugatedGauge (t : ℕ → ℝ) (ω : ℕ → Bool) (n : ℕ) : ℝ :=
  if ω (n - 1) then t n else -t n

/-- The deterministic mean of a prime sine coefficient under biased conjugation. -/
def meanSineWeight (t : ℕ → ℝ) (q : ℕ → unitInterval) (n : ℕ) : ℝ :=
  (2 * (q n : ℝ) - 1) * primeSineWeight t n

/-- The mean prime sine current. -/
def meanGaugeCurrent (t : ℕ → ℝ) (q : ℕ → unitInterval) : ℝ → ℝ :=
  partialSum (meanSineWeight t q)

theorem conjugatedGauge_eq_or_neg (t : ℕ → ℝ) (ω : ℕ → Bool) (n : ℕ) :
    conjugatedGauge t ω n = t n ∨ conjugatedGauge t ω n = -t n := by
  unfold conjugatedGauge
  split_ifs <;> simp

/-- Every sample preserves the real coefficient at every prime power. -/
theorem torusGauge_conjugatedGauge (t : ℕ → ℝ) (ω : ℕ → Bool) :
    torusGauge (conjugatedGauge t ω) = torusGauge t :=
  torusGauge_eq_of_pointwise_conjugate (conjugatedGauge_eq_or_neg t ω)

private theorem primeSineWeight_conjugatedGauge (t : ℕ → ℝ) (ω : ℕ → Bool) (n : ℕ) :
    primeSineWeight (conjugatedGauge t ω) (n + 1) =
      if ω n then primeSineWeight t (n + 1) else -primeSineWeight t (n + 1) := by
  by_cases hp : (n + 1).Prime
  · simp only [primeSineWeight, if_pos hp, conjugatedGauge, Nat.add_sub_cancel]
    cases ω n <;> simp [mul_neg, Real.sin_neg]
  · simp only [primeSineWeight, if_neg hp, neg_zero, ite_self]

private theorem centeredPartialSum_eq_current_sub_mean (t : ℕ → ℝ)
    (q : ℕ → unitInterval) (ω : ℕ → Bool) (N : ℕ) :
    HTGeometry.coordPartialSum
        (HTGeometry.LogarithmicSigns.term (fun n => q (n + 1)) (primeSineWeight t)) N ω =
      ((∑ n ∈ Ioc 0 N,
        (primeSineWeight (conjugatedGauge t ω) n - meanSineWeight t q n) : ℝ) : ℂ) := by
  induction N with
  | zero => simp [HTGeometry.coordPartialSum]
  | succ N ih =>
    have hs : HTGeometry.coordPartialSum
        (HTGeometry.LogarithmicSigns.term (fun n => q (n + 1)) (primeSineWeight t))
        (N + 1) ω =
      HTGeometry.coordPartialSum
        (HTGeometry.LogarithmicSigns.term (fun n => q (n + 1)) (primeSineWeight t)) N ω +
        HTGeometry.LogarithmicSigns.term (fun n => q (n + 1))
          (primeSineWeight t) N (ω N) := by
      simp only [HTGeometry.coordPartialSum, Finset.sum_range_succ]
    rw [hs, ih, Finset.sum_Ioc_succ_top (Nat.zero_le N), Complex.ofReal_add,
      primeSineWeight_conjugatedGauge]
    cases ω N <;> simp [HTGeometry.LogarithmicSigns.term, meanSineWeight]

/-- Random current differs from its deterministic mean by square-root precision almost surely,
for every phase source and every independent product bias. -/
theorem ae_gaugeCurrent_sub_mean_isBigO (t : ℕ → ℝ) (q : ℕ → unitInterval) :
    ∀ᵐ ω ∂conjugationMeasure q,
      (fun x => gaugeCurrent (conjugatedGauge t ω) x - meanGaugeCurrent t q x)
        =O[atTop] sqrtScale := by
  filter_upwards [HTGeometry.LogarithmicSigns.ae_eventually_norm_partialSum_floor_le
    (fun n => q (n + 1)) (primeSineWeight t)
      (fun n hn => primeSineWeight_abs_le t hn)] with ω hω
  refine IsBigO.of_bound 32 ?_
  filter_upwards [hω] with x hx
  rw [centeredPartialSum_eq_current_sub_mean] at hx
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (sqrtScale_nonneg x)]
  simpa only [Complex.norm_real, Real.norm_eq_abs, gaugeCurrent, meanGaugeCurrent,
    partialSum, sum_sub_distrib, sqrtScale, mul_assoc] using hx

/-- Independent conjugation adds only the deterministic mean-current obstruction to the real
count; the centered part is almost surely invisible at square-root precision. -/
theorem ae_complexCount_conjugatedGauge_iff (t : ℕ → ℝ) (q : ℕ → unitInterval) :
    ∀ᵐ ω ∂conjugationMeasure q,
      ComplexCount (complexTorusGauge (conjugatedGauge t ω)) ↔
        Count (torusGauge t) ∧ meanGaugeCurrent t q =O[atTop] sqrtScale := by
  filter_upwards [ae_gaugeCurrent_sub_mean_isBigO t q] with ω hω
  have hdiff : (fun x => partialSum
      (fun n => (complexTorusGauge (conjugatedGauge t ω) n).im) x - meanGaugeCurrent t q x)
        =O[atTop] sqrtScale := by
    have h := (imaginary_partialSum_sub_current_isBigO (conjugatedGauge t ω)).add hω
    exact h.congr_left fun x => by ring
  rw [complexCount_iff]
  change Count (torusGauge (conjugatedGauge t ω)) ∧ _ ↔ _
  rw [torusGauge_conjugatedGauge]
  refine and_congr_right fun _ => ⟨fun hi => ?_, fun hm => ?_⟩
  · simpa only [sub_sub_cancel] using hi.sub hdiff
  · simpa only [sub_add_cancel] using hdiff.add hm

/-- The complete almost-sure criterion consists of RH, real gauge distance and mean sine current. -/
theorem ae_complexCount_conjugatedGauge_iff_rh_distance_mean
    (t : ℕ → ℝ) (q : ℕ → unitInterval) :
    ∀ᵐ ω ∂conjugationMeasure q,
      ComplexCount (complexTorusGauge (conjugatedGauge t ω)) ↔
        RiemannHypothesis ∧ gaugeDistance t =O[atTop] sqrtScale ∧
          meanGaugeCurrent t q =O[atTop] sqrtScale := by
  filter_upwards [ae_complexCount_conjugatedGauge_iff t q] with ω hω
  simpa only [count_torusGauge_iff, and_assoc] using hω

/-- Fair independent conjugation probabilities. -/
def fairConjugationBias : ℕ → unitInterval := fun _ => ⟨1 / 2, by norm_num⟩

private theorem meanGaugeCurrent_fair (t : ℕ → ℝ) (x : ℝ) :
    meanGaugeCurrent t fairConjugationBias x = 0 := by
  simp [meanGaugeCurrent, partialSum, meanSineWeight, fairConjugationBias]

theorem ae_fair_gaugeCurrent_isBigO (t : ℕ → ℝ) :
    ∀ᵐ ω ∂conjugationMeasure fairConjugationBias,
      gaugeCurrent (conjugatedGauge t ω) =O[atTop] sqrtScale := by
  filter_upwards [ae_gaugeCurrent_sub_mean_isBigO t fairConjugationBias] with ω hω
  simpa only [meanGaugeCurrent_fair, sub_zero] using hω

/-- Almost every fair conjugation is a complex count lift exactly when the original real
source satisfies its count. -/
theorem ae_fair_complexCount_iff (t : ℕ → ℝ) :
    ∀ᵐ ω ∂conjugationMeasure fairConjugationBias,
      ComplexCount (complexTorusGauge (conjugatedGauge t ω)) ↔ Count (torusGauge t) := by
  have hm : meanGaugeCurrent t fairConjugationBias =O[atTop] sqrtScale := by
    refine IsBigO.of_bound 0 (Eventually.of_forall fun x => ?_)
    simp only [meanGaugeCurrent_fair, norm_zero, zero_mul, le_refl]
  filter_upwards [ae_complexCount_conjugatedGauge_iff t fairConjugationBias] with ω hω
  exact hω.trans (and_iff_left hm)

/-- Retain a finite prefix and independently conjugate the remaining Euler factors. -/
def prefixConjugatedGauge (t : ℕ → ℝ) (N : ℕ) (ω : ℕ → Bool) (n : ℕ) : ℝ :=
  if n ≤ N then t n else conjugatedGauge t ω n

/-- Fair conjugation still yields almost-sure complex count lifts when any finite phase prefix
is retained exactly. -/
theorem ae_prefix_complexCount_iff (t : ℕ → ℝ) (N : ℕ) :
    ∀ᵐ ω ∂conjugationMeasure fairConjugationBias,
      (∀ n ≤ N, prefixConjugatedGauge t N ω n = t n) ∧
      torusGauge (prefixConjugatedGauge t N ω) = torusGauge t ∧
      (ComplexCount (complexTorusGauge (prefixConjugatedGauge t N ω)) ↔ Count (torusGauge t)) := by
  filter_upwards [ae_fair_gaugeCurrent_isBigO t] with ω hω
  have hu : ∀ n, prefixConjugatedGauge t N ω n = t n ∨
      prefixConjugatedGauge t N ω n = -t n := by
    intro n
    unfold prefixConjugatedGauge
    split_ifs
    · exact Or.inl rfl
    · exact conjugatedGauge_eq_or_neg t ω n
  have hreal := torusGauge_eq_of_pointwise_conjugate hu
  have hfinite : primeSineWeight (prefixConjugatedGauge t N ω) -
      primeSineWeight (conjugatedGauge t ω) ∈ sqrtClass := by
    refine mem_sqrtClass_of_eventually_zero (N := N) fun n hn => ?_
    have hun : prefixConjugatedGauge t N ω n = conjugatedGauge t ω n :=
      if_neg (not_le.mpr hn)
    simp only [Pi.sub_apply, primeSineWeight, hun, sub_self]
  have hcurrent : gaugeCurrent (prefixConjugatedGauge t N ω) =O[atTop] sqrtScale := by
    have h := (hfinite : partialSum (primeSineWeight (prefixConjugatedGauge t N ω) -
      primeSineWeight (conjugatedGauge t ω)) =O[atTop] sqrtScale).add hω
    refine h.congr_left fun x => ?_
    rw [partialSum_sub]
    exact sub_add_cancel _ _
  refine ⟨fun n hn => if_pos hn, hreal, ?_⟩
  rw [complexCount_torusGauge_iff, ← and_assoc, ← count_torusGauge_iff, hreal]
  exact and_iff_left hcurrent

end GaloisForLFunctions.ArithmeticOfSquareRootPrecision
