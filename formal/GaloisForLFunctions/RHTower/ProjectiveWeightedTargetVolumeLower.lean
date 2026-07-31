import GaloisForLFunctions.RHTower.ProjectiveWeightedHaarQuantileActiveSupport

/-!
# Lower volume law for projective weighted coherence targets

Every feasible projective water allocation defines an explicit Haar-positive
box contained in the true coherence target.  Its exact product volume gives
the lower half of the canonical target-information sandwich.
-/

open MeasureTheory Set Metric
open scoped BigOperators

noncomputable section

namespace RHTower

theorem norm_fourier_one_sub_one_le_two_pi_mul_norm
    (y : UnitAddCircle) :
    ‖fourier 1 y - 1‖ ≤ 2 * Real.pi * ‖y‖ := by
  refine Quotient.inductionOn y ?_
  intro x
  change
    ‖fourier 1 (x : UnitAddCircle) - 1‖ ≤
      2 * Real.pi * ‖(x : UnitAddCircle)‖
  rw [fourier_coe_apply]
  have harg :
      2 * (Real.pi : ℂ) * Complex.I * (1 : ℤ) * (x : ℂ) / (1 : ℝ) =
        Complex.I * (((2 * Real.pi * x : ℝ) : ℂ)) := by
    push_cast
    ring_nf
  rw [harg]
  have hchord :=
    norm_exp_I_mul_real_sub_one_le_mod_two_pi
      (2 * Real.pi * x) (round x)
  calc
    ‖Complex.exp (Complex.I * (((2 * Real.pi * x : ℝ) : ℂ))) - 1‖
        ≤ |2 * Real.pi * x - 2 * Real.pi * (round x : ℝ)| := hchord
    _ = 2 * Real.pi * ‖(x : UnitAddCircle)‖ := by
      rw [show
        2 * Real.pi * x - 2 * Real.pi * (round x : ℝ) =
          (2 * Real.pi) * (x - (round x : ℝ)) by ring]
      rw [abs_mul, abs_of_pos (mul_pos two_pos Real.pi_pos)]
      rw [AddCircle.norm_eq]
      rw [show (1 : ℝ)⁻¹ * x = x by norm_num]
      congr 1
      ring_nf

def projectiveWaterBoxRadius {d : ℕ}
    (k : Fin d) (x : Fin d → ℝ) (j : Fin d) : ℝ :=
  if j = k then 1 / 2 else
    Real.sqrt (2 / x j) / (2 * Real.pi)

def projectiveWaterBox {d : ℕ}
    (k : Fin d) (x : Fin d → ℝ) :
    Set (Fin d → UnitAddCircle) :=
  Set.pi Set.univ (fun j =>
    Metric.closedBall 0 (projectiveWaterBoxRadius k x j))

theorem measurableSet_projectiveWaterBox {d : ℕ}
    (k : Fin d) (x : Fin d → ℝ) :
    MeasurableSet (projectiveWaterBox k x) := by
  exact MeasurableSet.univ_pi fun _ => measurableSet_closedBall

theorem projectiveWaterBoxRadius_nonneg {d : ℕ}
    (k : Fin d) (x : Fin d → ℝ) (j : Fin d) :
    0 ≤ projectiveWaterBoxRadius k x j := by
  unfold projectiveWaterBoxRadius
  split_ifs <;> positivity

theorem projectiveWaterBoxRadius_le_half {d : ℕ}
    (k : Fin d) (x : Fin d → ℝ)
    (hx : ∀ j, 1 ≤ x j) (j : Fin d) :
    projectiveWaterBoxRadius k x j ≤ 1 / 2 := by
  rw [projectiveWaterBoxRadius]
  by_cases hj : j = k
  · simp [hj]
  rw [if_neg hj]
  have hxpos : 0 < x j := zero_lt_one.trans_le (hx j)
  have hdiv : 2 / x j ≤ 2 := by
    apply (div_le_iff₀ hxpos).2
    have hxj := hx j
    nlinarith
  have hsqrt : Real.sqrt (2 / x j) ≤ Real.sqrt 2 :=
    Real.sqrt_le_sqrt hdiv
  have hsqrtTwo : Real.sqrt 2 < Real.pi := by
    have hsqrt2 : Real.sqrt 2 < 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
        Real.sqrt_nonneg 2]
    exact hsqrt2.trans (by nlinarith [Real.pi_gt_three])
  apply (div_le_iff₀ (mul_pos two_pos Real.pi_pos)).2
  nlinarith

theorem projectiveWeightedPairwiseEnergy_le_four_mul_pivotEnergy
    {d : ℕ} (w : Fin d → ℝ) (phase : Fin d → ℂ) (k : Fin d)
    (hw : ∀ j, 0 ≤ w j) (hmass : ∑ j, w j = 1) :
    projectiveWeightedPairwiseEnergy w phase ≤
      4 * projectiveWeightedPivotEnergy w phase k := by
  rw [projectiveWeightedPairwiseEnergy, projectiveWeightedPivotEnergy]
  have htriangle (i j : Fin d) :
      ‖phase i - phase j‖ ≤
        ‖phase i - phase k‖ + ‖phase j - phase k‖ := by
    calc
      ‖phase i - phase j‖ =
          ‖(phase i - phase k) - (phase j - phase k)‖ := by ring_nf
      _ ≤ ‖phase i - phase k‖ + ‖phase j - phase k‖ := norm_sub_le _ _
  have hsquare (i j : Fin d) :
      ‖phase i - phase j‖ ^ 2 ≤
        2 * ‖phase i - phase k‖ ^ 2 +
          2 * ‖phase j - phase k‖ ^ 2 := by
    have hnonneg_i : 0 ≤ ‖phase i - phase k‖ := norm_nonneg _
    have hnonneg_j : 0 ≤ ‖phase j - phase k‖ := norm_nonneg _
    have hsq := sq_le_sq₀ (norm_nonneg _) (add_nonneg hnonneg_i hnonneg_j)
      |>.2 (htriangle i j)
    nlinarith [sq_nonneg
      (‖phase i - phase k‖ - ‖phase j - phase k‖)]
  calc
    (∑ i, ∑ j, w i * w j * ‖phase i - phase j‖ ^ 2) ≤
        ∑ i, ∑ j, w i * w j *
          (2 * ‖phase i - phase k‖ ^ 2 +
            2 * ‖phase j - phase k‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro i _hi
      apply Finset.sum_le_sum
      intro j _hj
      exact mul_le_mul_of_nonneg_left (hsquare i j)
        (mul_nonneg (hw i) (hw j))
    _ = 4 * ∑ j, w j * ‖phase j - phase k‖ ^ 2 := by
      have hfirst :
          (∑ i, ∑ j, w i * w j *
            (2 * ‖phase i - phase k‖ ^ 2)) =
            2 * ∑ i, w i * ‖phase i - phase k‖ ^ 2 := by
        calc
          (∑ i, ∑ j, w i * w j *
              (2 * ‖phase i - phase k‖ ^ 2)) =
              ∑ i, (2 * w i * ‖phase i - phase k‖ ^ 2) *
                (∑ j, w j) := by
            apply Finset.sum_congr rfl
            intro i _hi
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _hj
            ring
          _ = 2 * ∑ i, w i * ‖phase i - phase k‖ ^ 2 := by
            rw [hmass]
            simp_rw [mul_one]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _hi
            ring
      have hsecond :
          (∑ i, ∑ j, w i * w j *
            (2 * ‖phase j - phase k‖ ^ 2)) =
            2 * ∑ j, w j * ‖phase j - phase k‖ ^ 2 := by
        calc
          (∑ i, ∑ j, w i * w j *
              (2 * ‖phase j - phase k‖ ^ 2)) =
              (∑ i, w i) *
                (2 * ∑ j, w j * ‖phase j - phase k‖ ^ 2) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i _hi
            simp only [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _hj
            ring
          _ = 2 * ∑ j, w j * ‖phase j - phase k‖ ^ 2 := by
            rw [hmass, one_mul]
      simp_rw [mul_add, Finset.sum_add_distrib]
      rw [hfirst, hsecond]
      ring

theorem one_sub_half_projectiveWeightedPivotEnergy_le_amplitudeNorm
    {d : ℕ} (w : Fin d → ℝ) (phase : Fin d → ℂ) (k : Fin d)
    (hmass : ∑ j, w j = 1) (hphase : ∀ j, ‖phase j‖ = 1) :
    1 - (1 / 2 : ℝ) * projectiveWeightedPivotEnergy w phase k ≤
      ‖projectiveWeightedPhaseAmplitude w phase‖ := by
  have hterm (j : Fin d) :
      ‖phase j - phase k‖ ^ 2 =
        2 - 2 * (phase j * star (phase k)).re := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub,
      Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
      hphase j, hphase k]
    norm_num
  have henergy :
      projectiveWeightedPivotEnergy w phase k =
        2 - 2 *
          (projectiveWeightedPhaseAmplitude w phase *
            star (phase k)).re := by
    rw [projectiveWeightedPivotEnergy]
    simp_rw [hterm, mul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_mul]
    rw [hmass]
    unfold projectiveWeightedPhaseAmplitude
    have hreSum :
        (∑ j, (w j : ℂ) * phase j).re =
          ∑ j, w j * (phase j).re := by
      simp
    have himSum :
        (∑ j, (w j : ℂ) * phase j).im =
          ∑ j, w j * (phase j).im := by
      simp
    rw [Complex.mul_re, hreSum, himSum]
    simp only [Complex.mul_re]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.mul_sum, Finset.sum_mul]
    norm_num
    congr 1
    all_goals
      apply Finset.sum_congr rfl
      intro j _hj
      ring
  rw [henergy]
  have hre :
      (projectiveWeightedPhaseAmplitude w phase *
          star (phase k)).re ≤
        ‖projectiveWeightedPhaseAmplitude w phase *
          star (phase k)‖ :=
    Complex.re_le_norm _
  have hnormStar : ‖star (phase k)‖ = 1 := by
    rw [norm_star, hphase k]
  rw [norm_mul, hnormStar, mul_one] at hre
  nlinarith

theorem torusIndependentProjectiveWeightedPivotEnergy_le_of_mem_waterBox
    {d : ℕ} (w : Fin d → ℝ) (k : Fin d)
    {eta : ℝ} (x : Fin d → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hx : ∀ j, 1 ≤ x j)
    (hfeasible :
      (∑ j, if j = k then 0 else w j / x j) ≤ eta)
    {y : Fin d → UnitAddCircle}
    (hy : y ∈ projectiveWaterBox k x) :
    torusIndependentProjectiveWeightedPivotEnergy w k y ≤ 2 * eta := by
  have hchord (j : Fin d) (hjk : j ≠ k) :
      ‖fourier 1 (y j) - 1‖ ^ 2 ≤ 2 / x j := by
    have hyj := hy j (Set.mem_univ j)
    rw [Metric.mem_closedBall, dist_zero_right] at hyj
    rw [projectiveWaterBoxRadius, if_neg hjk] at hyj
    have hnorm :=
      norm_fourier_one_sub_one_le_two_pi_mul_norm (y j)
    have hpi : 0 ≤ 2 * Real.pi := (mul_pos two_pos Real.pi_pos).le
    have hscaled :
        2 * Real.pi * ‖y j‖ ≤ Real.sqrt (2 / x j) := by
      calc
        2 * Real.pi * ‖y j‖ ≤
            2 * Real.pi *
              (Real.sqrt (2 / x j) / (2 * Real.pi)) :=
          mul_le_mul_of_nonneg_left hyj hpi
        _ = Real.sqrt (2 / x j) := by
          field_simp [Real.pi_ne_zero]
    have hchordSqrt :
        ‖fourier 1 (y j) - 1‖ ≤ Real.sqrt (2 / x j) :=
      hnorm.trans hscaled
    have hxpos : 0 < x j := zero_lt_one.trans_le (hx j)
    have hdivnonneg : 0 ≤ 2 / x j := div_nonneg (by norm_num) hxpos.le
    have hsquare :=
      (sq_le_sq₀ (norm_nonneg _)
        (Real.sqrt_nonneg _)).2 hchordSqrt
    rw [Real.sq_sqrt hdivnonneg] at hsquare
    exact hsquare
  rw [torusIndependentProjectiveWeightedPivotEnergy]
  calc
    (∑ j, if j = k then 0 else
        w j * ‖fourier 1 (y j) - 1‖ ^ 2) ≤
        ∑ j, if j = k then 0 else w j * (2 / x j) := by
      apply Finset.sum_le_sum
      intro j _hj
      by_cases hjk : j = k
      · simp [hjk]
      · simp only [hjk, ↓reduceIte]
        exact mul_le_mul_of_nonneg_left (hchord j hjk) (hw j)
    _ = 2 * ∑ j, if j = k then 0 else w j / x j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      by_cases hjk : j = k <;> simp [hjk]
      ring
    _ ≤ 2 * eta := mul_le_mul_of_nonneg_left hfeasible (by norm_num)

theorem preimage_projectiveWaterBox_subset_coherenceTarget
    {d : ℕ} (w : Fin d → ℝ) (k : Fin d)
    {eta : ℝ} (x : Fin d → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hmass : ∑ j, w j = 1)
    (hx : ∀ j, 1 ≤ x j)
    (hfeasible :
      (∑ j, if j = k then 0 else w j / x j) ≤ eta) :
    pivotDifferenceEquiv k ⁻¹' projectiveWaterBox k x ⊆
      torusProjectiveWeightedCoherenceTarget w eta := by
  intro z hz
  have hindependent :
      torusIndependentProjectiveWeightedPivotEnergy w k
          (pivotDifferenceEquiv k z) ≤ 2 * eta :=
    torusIndependentProjectiveWeightedPivotEnergy_le_of_mem_waterBox
      w k x hw hx hfeasible hz
  have hpivot :
      projectiveWeightedPivotEnergy w
          (fun j => fourier 1 (z j)) k ≤ 2 * eta := by
    change torusProjectiveWeightedPivotEnergy w k z ≤ 2 * eta
    rw [←
      torusIndependentProjectiveWeightedPivotEnergy_pivotDifferenceEquiv]
    exact hindependent
  rw [torusProjectiveWeightedCoherenceTarget, Set.mem_setOf_eq]
  have hlower :=
    one_sub_half_projectiveWeightedPivotEnergy_le_amplitudeNorm
      w (fun j => fourier 1 (z j)) k hmass (fun j => by
        rw [fourier_apply, Circle.norm_coe])
  exact (by nlinarith : 1 - eta ≤
    1 - (1 / 2 : ℝ) *
      projectiveWeightedPivotEnergy w (fun j => fourier 1 (z j)) k).trans
        hlower

theorem volumeReal_projectiveWaterBox
    {d : ℕ} (k : Fin d) (x : Fin d → ℝ)
    (hx : ∀ j, 1 ≤ x j) :
    volume.real (projectiveWaterBox k x) =
      ∏ j, if j = k then 1 else
        Real.sqrt (2 / x j) / Real.pi := by
  rw [measureReal_def, projectiveWaterBox, volume_pi_pi,
    ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro j _hj
  rw [AddCircle.volume_closedBall]
  have hrnonneg := projectiveWaterBoxRadius_nonneg k x j
  have hrhalf := projectiveWaterBoxRadius_le_half k x hx j
  have hmin :
      min (1 : ℝ) (2 * projectiveWaterBoxRadius k x j) =
        2 * projectiveWaterBoxRadius k x j := by
    rw [min_eq_right]
    linarith
  rw [hmin, ENNReal.toReal_ofReal (mul_nonneg (by norm_num) hrnonneg)]
  rw [projectiveWaterBoxRadius]
  by_cases hjk : j = k
  · simp [hjk]
  · simp only [hjk, ↓reduceIte]
    field_simp [Real.pi_ne_zero]

theorem projectiveWaterProduct_le_volumeReal_coherenceTarget
    {d : ℕ} (w : Fin d → ℝ) (k : Fin d)
    {eta : ℝ} (x : Fin d → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hmass : ∑ j, w j = 1)
    (hx : ∀ j, 1 ≤ x j)
    (hfeasible :
      (∑ j, if j = k then 0 else w j / x j) ≤ eta) :
    (∏ j, if j = k then 1 else
        Real.sqrt (2 / x j) / Real.pi) ≤
      volume.real (torusProjectiveWeightedCoherenceTarget w eta) := by
  have hsubset :=
    preimage_projectiveWaterBox_subset_coherenceTarget
      w k x hw hmass hx hfeasible
  have hmono :
      volume.real
          (pivotDifferenceEquiv k ⁻¹' projectiveWaterBox k x) ≤
        volume.real
          (torusProjectiveWeightedCoherenceTarget w eta) :=
    measureReal_mono hsubset
  have hmeasure :
      volume.real
          (pivotDifferenceEquiv k ⁻¹' projectiveWaterBox k x) =
        volume.real (projectiveWaterBox k x) := by
    rw [measureReal_def, measureReal_def]
    congr 1
    exact (measurePreserving_pivotDifferenceEquiv k).measure_preimage
      (measurableSet_projectiveWaterBox k x).nullMeasurableSet
  rw [hmeasure, volumeReal_projectiveWaterBox k x hx] at hmono
  exact hmono

theorem prod_one_except_eq_pow_card_sub_one
    {d : ℕ} (k : Fin d) (c : ℝ) :
    (∏ j : Fin d, if j = k then 1 else c) = c ^ (d - 1) := by
  rw [Finset.prod_ite]
  simp only [Finset.prod_const, one_pow]
  have hfilter :
      Finset.filter (fun j : Fin d => ¬j = k) Finset.univ =
        Finset.univ.erase k := by
    ext j
    simp [eq_comm]
  rw [hfilter, Finset.card_erase_of_mem (Finset.mem_univ k)]
  simp

theorem sqrt_two_div_div_pi_eq_entropyFactor
    {x : ℝ} (hx : 1 ≤ x) :
    Real.sqrt (2 / x) / Real.pi =
      (Real.sqrt 2 / Real.pi) *
        Real.exp (-(1 / 2 : ℝ) * Real.log x) := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hsqrtpos : 0 < Real.sqrt x := Real.sqrt_pos.2 hxpos
  have hexp :
      Real.exp ((1 / 2 : ℝ) * Real.log x) = Real.sqrt x := by
    rw [show (1 / 2 : ℝ) * Real.log x = Real.log x / 2 by ring,
      ← Real.log_sqrt hxpos.le, Real.exp_log hsqrtpos]
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2)]
  rw [show -(1 / 2 : ℝ) * Real.log x =
      -((1 / 2 : ℝ) * Real.log x) by ring,
    Real.exp_neg, hexp]
  field_simp [Real.pi_ne_zero, hsqrtpos.ne']

theorem projectiveWaterProduct_eq_entropy
    {d : ℕ} (k : Fin d) (x : Fin d → ℝ)
    (hx : ∀ j, 1 ≤ x j) :
    (∏ j, if j = k then 1 else
        Real.sqrt (2 / x j) / Real.pi) =
      (Real.sqrt 2 / Real.pi) ^ (d - 1) *
        Real.exp (-projectiveCoordinateEntropy k x) := by
  let c : ℝ := Real.sqrt 2 / Real.pi
  have hterm (j : Fin d) :
      (if j = k then 1 else Real.sqrt (2 / x j) / Real.pi) =
        (if j = k then 1 else c) *
          (if j = k then 1 else
            Real.exp (-(1 / 2 : ℝ) * Real.log (x j))) := by
    by_cases hjk : j = k
    · simp [hjk]
    · simp only [hjk, ↓reduceIte, c]
      exact sqrt_two_div_div_pi_eq_entropyFactor (hx j)
  calc
    (∏ j, if j = k then 1 else
        Real.sqrt (2 / x j) / Real.pi) =
        ∏ j, (if j = k then 1 else c) *
          (if j = k then 1 else
            Real.exp (-(1 / 2 : ℝ) * Real.log (x j))) := by
      apply Finset.prod_congr rfl
      intro j _hj
      exact hterm j
    _ = (∏ j, if j = k then 1 else c) *
        ∏ j, if j = k then 1 else
          Real.exp (-(1 / 2 : ℝ) * Real.log (x j)) := by
      rw [Finset.prod_mul_distrib]
    _ = c ^ (d - 1) *
        Real.exp (-projectiveCoordinateEntropy k x) := by
      rw [prod_one_except_eq_pow_card_sub_one k c]
      congr 1
      rw [show
        (∏ j, if j = k then 1 else
          Real.exp (-(1 / 2 : ℝ) * Real.log (x j))) =
            ∏ j, Real.exp
              (if j = k then 0 else
                -(1 / 2 : ℝ) * Real.log (x j)) by
          apply Finset.prod_congr rfl
          intro j _hj
          by_cases hjk : j = k <;> simp [hjk]]
      rw [← Real.exp_sum]
      congr 1
      rw [projectiveCoordinateEntropy]
      rw [show
        -((1 / 2 : ℝ) *
          ∑ j, if j = k then 0 else Real.log (x j)) =
            (-1 / 2 : ℝ) *
              ∑ j, if j = k then 0 else Real.log (x j) by ring,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      by_cases hjk : j = k <;> simp [hjk]
      ring
    _ = (Real.sqrt 2 / Real.pi) ^ (d - 1) *
        Real.exp (-projectiveCoordinateEntropy k x) := rfl

theorem entropyFactor_le_volumeReal_coherenceTarget_of_feasible
    {d : ℕ} (w : Fin d → ℝ) (k : Fin d)
    {eta : ℝ} (x : Fin d → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hmass : ∑ j, w j = 1)
    (hx : ProjectiveWaterFeasible w k eta x) :
    (Real.sqrt 2 / Real.pi) ^ (d - 1) *
        Real.exp (-projectiveCoordinateEntropy k x) ≤
      volume.real (torusProjectiveWeightedCoherenceTarget w eta) := by
  rw [← projectiveWaterProduct_eq_entropy k x hx.1]
  exact projectiveWaterProduct_le_volumeReal_coherenceTarget
    w k x hw hmass hx.1 hx.2

theorem canonicalEntropyFactor_le_volumeReal_coherenceTarget
    {d : ℕ} (hd : 0 < d) (w : Fin d → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hmass : ∑ j, w j = 1)
    {eta : ℝ} (heta : 0 < eta) :
    (Real.sqrt 2 / Real.pi) ^ (d - 1) *
        Real.exp
          (-projectiveCanonicalWaterEntropyMinimum hd w eta) ≤
      volume.real (torusProjectiveWeightedCoherenceTarget w eta) := by
  obtain ⟨k, hk⟩ :=
    exists_projectiveCanonicalWaterEntropy_minimizingPivot hd w eta
  let x : Fin d → ℝ :=
    projectiveWaterScale w k
      (projectiveCanonicalWaterLevel w k eta)
  have hx : ProjectiveWaterFeasible w k eta x :=
    projectiveCanonicalWaterScale_feasible hd w k hw hmass heta
  have hlower :=
    entropyFactor_le_volumeReal_coherenceTarget_of_feasible
      w k x hw hmass hx
  have hentropy :
      projectiveCoordinateEntropy k x =
        projectiveCanonicalWaterEntropyMinimum hd w eta := by
    calc
      projectiveCoordinateEntropy k x =
          projectiveCanonicalWaterEntropy w eta k := by
        dsimp only [x]
        rw [projectiveCanonicalWaterEntropy,
          projectiveCoordinateEntropy_waterScale]
      _ = projectiveCanonicalWaterEntropyMinimum hd w eta := hk
  rw [hentropy] at hlower
  exact hlower

/-- Canonical upper target-volume envelope, expressed with the same minimum
water entropy as the lower box law. -/
theorem volumeReal_coherenceTarget_le_canonicalEntropyFactor
    {d : ℕ} (hd : 2 ≤ d) (w : Fin d → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hmass : ∑ j, w j = 1)
    {eta : ℝ} (heta : eta ≤ 1) :
    volume.real (torusProjectiveWeightedCoherenceTarget w eta) ≤
      (d : ℝ) * Real.exp (
        (Real.pi / 4) * (d - 1 : ℕ) -
          projectiveCanonicalWaterEntropyMinimum (by omega) w eta) := by
  let hd0 : 0 < d := by omega
  let lam : Fin d → ℝ :=
    fun k => projectiveCanonicalWaterLevel w k eta
  exact
    measureReal_torusProjectiveWeightedCoherenceTarget_waterEntropy_le
      w hw hmass heta lam
      (fun k => projectiveCanonicalWaterLevel_pos w k eta)
      (fun k =>
        projectiveCanonicalWaterLevel_mul_eta_le_card_sub_one
          hd w k heta)
      (fun k =>
        projectiveCanonicalWaterEntropyMinimum_le hd0 w eta k)

/-- Negative log Haar volume of the true weighted coherence target. -/
def projectiveWeightedCoherenceTargetInformation
    {d : ℕ} (w : Fin d → ℝ) (eta : ℝ) : ℝ :=
  -Real.log
    (volume.real (torusProjectiveWeightedCoherenceTarget w eta))

/-- The canonical box law makes every positive-defect coherence target
Haar-positive; target information is therefore finite. -/
theorem volumeReal_coherenceTarget_pos
    {d : ℕ} (hd : 0 < d) (w : Fin d → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hmass : ∑ j, w j = 1)
    {eta : ℝ} (heta : 0 < eta) :
    0 < volume.real (torusProjectiveWeightedCoherenceTarget w eta) := by
  have hlower :=
    canonicalEntropyFactor_le_volumeReal_coherenceTarget
      hd w hw hmass heta
  exact (mul_pos
    (pow_pos (div_pos (Real.sqrt_pos.2 (by norm_num)) Real.pi_pos) _)
    (Real.exp_pos _)).trans_le hlower

/-- **Two-sided target-information law.**  Canonical reverse water filling
determines the negative log volume of the true coherence target up to explicit
dimension-only terms. -/
theorem canonicalWaterEntropy_targetInformation_sandwich
    {d : ℕ} (hd : 2 ≤ d) (w : Fin d → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hmass : ∑ j, w j = 1)
    {eta : ℝ} (heta0 : 0 < eta) (heta1 : eta ≤ 1) :
    projectiveCanonicalWaterEntropyMinimum (by omega) w eta -
          (Real.pi / 4) * (d - 1 : ℕ) - Real.log (d : ℝ) ≤
        projectiveWeightedCoherenceTargetInformation w eta ∧
      projectiveWeightedCoherenceTargetInformation w eta ≤
        projectiveCanonicalWaterEntropyMinimum (by omega) w eta -
          (d - 1 : ℕ) * Real.log (Real.sqrt 2 / Real.pi) := by
  let hd0 : 0 < d := by omega
  let H := projectiveCanonicalWaterEntropyMinimum hd0 w eta
  let mu :=
    volume.real (torusProjectiveWeightedCoherenceTarget w eta)
  let c := Real.sqrt 2 / Real.pi
  have hc : 0 < c := div_pos (Real.sqrt_pos.2 (by norm_num)) Real.pi_pos
  have hmu : 0 < mu :=
    volumeReal_coherenceTarget_pos hd0 w hw hmass heta0
  have hlower :
      c ^ (d - 1) * Real.exp (-H) ≤ mu := by
    simpa only [c, H, mu] using
      canonicalEntropyFactor_le_volumeReal_coherenceTarget
        hd0 w hw hmass heta0
  have hupper :
      mu ≤ (d : ℝ) *
        Real.exp ((Real.pi / 4) * (d - 1 : ℕ) - H) := by
    simpa only [H, mu] using
      volumeReal_coherenceTarget_le_canonicalEntropyFactor
        hd w hw hmass heta1
  have hlogLower :
      Real.log (c ^ (d - 1) * Real.exp (-H)) ≤ Real.log mu :=
    Real.log_le_log
      (mul_pos (pow_pos hc _) (Real.exp_pos _)) hlower
  have hlogUpper :
      Real.log mu ≤
        Real.log ((d : ℝ) *
          Real.exp ((Real.pi / 4) * (d - 1 : ℕ) - H)) :=
    Real.log_le_log hmu hupper
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hd0
  have hlogLowerEq :
      Real.log (c ^ (d - 1) * Real.exp (-H)) =
        (d - 1 : ℕ) * Real.log c - H := by
    rw [Real.log_mul (pow_ne_zero _ hc.ne') (Real.exp_ne_zero _),
      Real.log_pow, Real.log_exp]
    ring
  have hlogUpperEq :
      Real.log ((d : ℝ) *
          Real.exp ((Real.pi / 4) * (d - 1 : ℕ) - H)) =
        Real.log (d : ℝ) +
          (Real.pi / 4) * (d - 1 : ℕ) - H := by
    rw [Real.log_mul hdreal.ne' (Real.exp_ne_zero _), Real.log_exp]
    ring
  constructor
  · rw [projectiveWeightedCoherenceTargetInformation]
    change H - (Real.pi / 4) * (d - 1 : ℕ) -
        Real.log (d : ℝ) ≤ -Real.log mu
    rw [hlogUpperEq] at hlogUpper
    linarith
  · rw [projectiveWeightedCoherenceTargetInformation]
    change -Real.log mu ≤ H -
        (d - 1 : ℕ) * Real.log c
    rw [hlogLowerEq] at hlogLower
    linarith

/-- Explicit dimension-only absolute error in the canonical target-information
law. -/
def canonicalTargetInformationRemainder (d : ℕ) : ℝ :=
  max
    ((Real.pi / 4) * (d - 1 : ℕ) + Real.log (d : ℝ))
    (-((d - 1 : ℕ) * Real.log (Real.sqrt 2 / Real.pi)))

theorem abs_targetInformation_sub_canonicalWaterEntropy_le
    {d : ℕ} (hd : 2 ≤ d) (w : Fin d → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hmass : ∑ j, w j = 1)
    {eta : ℝ} (heta0 : 0 < eta) (heta1 : eta ≤ 1) :
    |projectiveWeightedCoherenceTargetInformation w eta -
        projectiveCanonicalWaterEntropyMinimum (by omega) w eta| ≤
      canonicalTargetInformationRemainder d := by
  obtain ⟨hlower, hupper⟩ :=
    canonicalWaterEntropy_targetInformation_sandwich
      hd w hw hmass heta0 heta1
  rw [abs_le]
  constructor
  · have hmax :=
      le_max_left
        ((Real.pi / 4) * (d - 1 : ℕ) + Real.log (d : ℝ))
        (-((d - 1 : ℕ) *
          Real.log (Real.sqrt 2 / Real.pi)))
    rw [canonicalTargetInformationRemainder]
    linarith
  · have hmax :=
      le_max_right
        ((Real.pi / 4) * (d - 1 : ℕ) + Real.log (d : ℝ))
        (-((d - 1 : ℕ) *
          Real.log (Real.sqrt 2 / Real.pi)))
    rw [canonicalTargetInformationRemainder]
    linarith

/-- Relative-error form: once canonical information dominates the explicit
dimension cost, the dimension-linear absolute remainder is quantitatively
negligible. -/
theorem abs_targetInformation_div_canonicalWaterEntropy_sub_one_le
    {d : ℕ} (hd : 2 ≤ d) (w : Fin d → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hmass : ∑ j, w j = 1)
    {eta : ℝ} (heta0 : 0 < eta) (heta1 : eta ≤ 1)
    (hH : 0 <
      projectiveCanonicalWaterEntropyMinimum (by omega) w eta) :
    |projectiveWeightedCoherenceTargetInformation w eta /
          projectiveCanonicalWaterEntropyMinimum (by omega) w eta - 1| ≤
      canonicalTargetInformationRemainder d /
        projectiveCanonicalWaterEntropyMinimum (by omega) w eta := by
  let I := projectiveWeightedCoherenceTargetInformation w eta
  let H := projectiveCanonicalWaterEntropyMinimum (by omega) w eta
  have hHlocal : 0 < H := by simpa only [H] using hH
  have habs : |I - H| ≤ canonicalTargetInformationRemainder d := by
    simpa only [I, H] using
      abs_targetInformation_sub_canonicalWaterEntropy_le
        hd w hw hmass heta0 heta1
  have hrewrite : I / H - 1 = (I - H) / H := by
    field_simp [hHlocal.ne']
  rw [hrewrite, abs_div, abs_of_pos hHlocal]
  exact div_le_div_of_nonneg_right habs hHlocal.le

end RHTower
