import GaloisForLFunctions.RHTower.XiMassTwoRapidityCorrelationGeometry

/-!
# Source-order obstruction for the two-rapidity prime cone

The literal moving prime cone contains nonzero labelled `2 × 3` covariance terms.
Their timelike stationary pair is antiordered in frequency versus rapidity.  Hence
no termwise source-support rule can remove the T1 saddle, not even cofinally: any
surviving T1 mechanism must cancel the complete signed nonlocal covariance.

This does not assert that the *sum* of labelled terms is nonzero.  It isolates the
precise remaining alternative—genuine nonlocal cancellation—from a false
termwise-order-support escape.
-/

namespace RHTower

noncomputable section

/-- A labelled prime-pair contribution to the literal two-rapidity covariance. -/
def xiMassCriticalPrimeConeTwoRapidityTerm
    (a sigma u : ℝ) (i j : ℕ) (t s : ℝ) : ℂ :=
  xiMassCriticalPrimeConeRapidityWeight a i *
      (starRingEnd ℂ) (xiMassCriticalPrimeConeRapidityWeight a j) *
        xiMassTwoRapidityCorrelationAmplitude a sigma t s *
          Complex.exp (-(Complex.I * ((a * xiMassTwoRapidityCorrelationPhase u
            (Real.log ((i : ℝ) + 2)) (Real.log ((j : ℝ) + 2)) t s : ℝ) : ℂ)))

/-- Every genuinely prime labelled rapidity weight is nonzero for nonzero mass coefficient. -/
theorem xiMassCriticalPrimeConeRapidityWeight_ne_zero_of_prime
    {a : ℝ} (ha : a ≠ 0) {n : ℕ} (hn : (n + 2).Prime) :
    xiMassCriticalPrimeConeRapidityWeight a n ≠ 0 := by
  unfold xiMassCriticalPrimeConeRapidityWeight
  apply mul_ne_zero
  · apply mul_ne_zero
    · rw [ArithmeticFunction.vonMangoldt_apply_prime hn]
      exact_mod_cast (Real.log_pos (by exact_mod_cast hn.one_lt)).ne'
    · exact_mod_cast Real.exp_ne_zero _
  · exact_mod_cast ha

/-- The positive two-rapidity damping factor never vanishes. -/
theorem xiMassTwoRapidityCorrelationAmplitude_ne_zero
    (a sigma t s : ℝ) : xiMassTwoRapidityCorrelationAmplitude a sigma t s ≠ 0 := by
  unfold xiMassTwoRapidityCorrelationAmplitude
  norm_cast
  exact ne_of_gt (by positivity)

/-- A prime-pair labelled term is pointwise nonzero, independently of its phase. -/
theorem xiMassCriticalPrimeConeTwoRapidityTerm_ne_zero
    {a : ℝ} (ha : a ≠ 0) {i j : ℕ} (hi : (i + 2).Prime) (hj : (j + 2).Prime)
    (sigma u t s : ℝ) :
    xiMassCriticalPrimeConeTwoRapidityTerm a sigma u i j t s ≠ 0 := by
  unfold xiMassCriticalPrimeConeTwoRapidityTerm
  apply mul_ne_zero
  · apply mul_ne_zero
    · apply mul_ne_zero
      · exact xiMassCriticalPrimeConeRapidityWeight_ne_zero_of_prime ha hi
      · simpa using xiMassCriticalPrimeConeRapidityWeight_ne_zero_of_prime ha hj
    · exact xiMassTwoRapidityCorrelationAmplitude_ne_zero a sigma t s
  · exact Complex.exp_ne_zero _

/-- Index carrier of the literal moving prime cone. -/
def xiMassCriticalPrimeConeIndexSet (d u : ℝ) : Finset ℕ :=
  Finset.range (⌊Real.exp (d * u / (d - 1 / 2))⌋₊ - 1)

/-- The literal covariance is exactly the sum of its labelled pair terms. -/
theorem xiMassCriticalPrimeConeTwoRapidityCovariance_eq_sum_term
    (a sigma d u t s : ℝ) :
    xiMassCriticalPrimeConeTwoRapidityCovariance a sigma d u t s =
      ∑ i ∈ xiMassCriticalPrimeConeIndexSet d u,
        ∑ j ∈ xiMassCriticalPrimeConeIndexSet d u,
          xiMassCriticalPrimeConeTwoRapidityTerm a sigma u i j t s := by
  rfl

/-- A termwise source-order rule would confine every nonzero labelled covariance term to the
same-order rapidity cone. -/
def XiMassCriticalPrimeConeTermwiseSameOrderSupported (a sigma d u : ℝ) : Prop :=
  ∀ i ∈ xiMassCriticalPrimeConeIndexSet d u, ∀ j ∈ xiMassCriticalPrimeConeIndexSet d u,
    ∀ t s : ℝ, xiMassCriticalPrimeConeTwoRapidityTerm a sigma u i j t s ≠ 0 →
      0 ≤ (Real.log ((i : ℝ) + 2) - Real.log ((j : ℝ) + 2)) * (t - s)

/-- Once the literal `2` and `3` legs enter the cone, termwise same-order support is impossible.
The excluded point is their actual antiordered timelike stationary pair. -/
theorem not_xiMassCriticalPrimeConeTermwiseSameOrderSupported_of_two_three_mem
    {a sigma d u : ℝ} (ha : a ≠ 0) (hu : 0 < u)
    (hlog2 : 0 ≤ Real.log 2) (hlog3 : 0 ≤ Real.log 3)
    (h23 : Real.log 2 < Real.log 3) (h3u : Real.log 3 < u)
    (hzero : 0 ∈ xiMassCriticalPrimeConeIndexSet d u)
    (hone : 1 ∈ xiMassCriticalPrimeConeIndexSet d u) :
    ¬ XiMassCriticalPrimeConeTermwiseSameOrderSupported a sigma d u := by
  intro hsupp
  obtain ⟨t, s, hstat⟩ := exists_xiMassTwoRapidityCorrelationStationary hu hlog2 hlog3
    (h23.trans h3u) h3u
  have hanti : (Real.log 2 - Real.log 3) * (t - s) < 0 :=
    hstat.frequency_rapidity_orientation_neg hu h23.ne
  have hsame := hsupp 0 hzero 1 hone t s
    (xiMassCriticalPrimeConeTwoRapidityTerm_ne_zero ha (by norm_num) (by norm_num) sigma u t s)
  norm_num at hsame
  exact (not_le_of_gt hanti) hsame

/-- Every physical cone with `d > 1/2` eventually contains both literal prime legs. -/
theorem eventually_zero_one_mem_xiMassCriticalPrimeConeIndexSet
    {d : ℝ} (hd : 1 / 2 < d) :
    ∀ᶠ u : ℝ in Filter.atTop,
      0 ∈ xiMassCriticalPrimeConeIndexSet d u ∧
        1 ∈ xiMassCriticalPrimeConeIndexSet d u := by
  have hcoef : 0 < d / (d - 1 / 2) := by
    apply div_pos <;> linarith
  have harg : Filter.Tendsto (fun u : ℝ => d * u / (d - 1 / 2)) Filter.atTop Filter.atTop := by
    simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, id_eq] using
      Filter.tendsto_id.const_mul_atTop hcoef
  have hexp : Filter.Tendsto (fun u : ℝ => Real.exp (d * u / (d - 1 / 2)))
      Filter.atTop Filter.atTop := Real.tendsto_exp_atTop.comp harg
  filter_upwards [hexp.eventually (Filter.eventually_ge_atTop (5 : ℝ))] with u hu
  have hfloor : 5 ≤ ⌊Real.exp (d * u / (d - 1 / 2))⌋₊ := Nat.le_floor hu
  constructor <;> rw [xiMassCriticalPrimeConeIndexSet, Finset.mem_range] <;> omega

/-- **Cofinal source-order no-go.**  For every physical cone exponent `d > 1/2` and nonzero
mass coefficient, the literal moving prime cone is eventually not termwise same-order supported.
Thus T1 cannot remove its antiordered saddle by source support; only nonlocal signed cancellation
of the full covariance remains. -/
theorem eventually_not_xiMassCriticalPrimeConeTermwiseSameOrderSupported
    {a sigma d : ℝ} (ha : a ≠ 0) (hd : 1 / 2 < d) :
    ∀ᶠ u : ℝ in Filter.atTop,
      ¬ XiMassCriticalPrimeConeTermwiseSameOrderSupported a sigma d u := by
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hlog3pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h23 : Real.log 2 < Real.log 3 :=
    Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
  filter_upwards [eventually_zero_one_mem_xiMassCriticalPrimeConeIndexSet hd,
    Filter.eventually_gt_atTop (Real.log 3)] with u hmem h3u
  exact not_xiMassCriticalPrimeConeTermwiseSameOrderSupported_of_two_three_mem ha
    (lt_trans hlog3pos h3u) hlog2 hlog3 h23 h3u hmem.1 hmem.2

end

end RHTower
