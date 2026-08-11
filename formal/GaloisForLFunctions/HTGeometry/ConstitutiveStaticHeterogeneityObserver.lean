import GaloisForLFunctions.HTGeometry.FiniteGibbsDifferentialBoundary

/-!
# Static-heterogeneity observer mechanics

A finite positive rate packet generates a posterior exponential tilt.  This module proves the exact
mechanism linking its partition derivatives, posterior rate variance, local apparent exponent, and
finite-window properness:

* posterior mean rate dissipates by the negative posterior variance;
* the local apparent exponent has an exact curvature balance;
* the first moment determinant is the partition square times variance;
* zero variance is equivalent to collapse of all active rates;
* a positive rate floor bounds every apparent-exponent sublevel in clock time.

These are finite universal-law-field mechanics.  They do not classify general first-passage laws or
assert an arithmetic/RH selection consequence.
-/

open scoped BigOperators

namespace HTGeometry

noncomputable section

/-- Unnormalized weight of one static rate after elapsed-time tilting. -/
def staticHeterogeneityWeight {ι : Type*} [Fintype ι]
    (weight rate : ι → ℝ) (i : ι) (t : ℝ) : ℝ :=
  weight i * Real.exp (-(rate i * t))

/-- Partition function of a finite static rate packet. -/
def staticHeterogeneityPartition {ι : Type*} [Fintype ι]
    (weight rate : ι → ℝ) : ℝ → ℝ :=
  ∑ i, staticHeterogeneityWeight weight rate i

/-- Unnormalized `k`-th rate moment after elapsed-time tilting. -/
def staticHeterogeneityMoment {ι : Type*} [Fintype ι]
    (weight rate : ι → ℝ) (k : ℕ) : ℝ → ℝ :=
  ∑ i, fun t => staticHeterogeneityWeight weight rate i t * rate i ^ k

/-- Nonnegative amplitudes with one active component give positive partition mass. -/
theorem staticHeterogeneityPartition_pos
    {ι : Type*} [Fintype ι]
    (weight rate : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hwpos : ∃ i, 0 < weight i) (t : ℝ) :
    0 < staticHeterogeneityPartition weight rate t := by
  rcases hwpos with ⟨i, hi⟩
  rw [staticHeterogeneityPartition]
  simp only [Finset.sum_apply]
  apply Finset.sum_pos'
  · intro j _
    exact mul_nonneg (hw j) (Real.exp_pos _).le
  · refine ⟨i, Finset.mem_univ i, ?_⟩
    exact mul_pos hi (Real.exp_pos _)

/-- Each tilted component differentiates by multiplication with its negative rate. -/
theorem hasDerivAt_staticHeterogeneityWeight
    {ι : Type*} [Fintype ι]
    (weight rate : ι → ℝ) (t : ℝ) (i : ι) :
    HasDerivAt (staticHeterogeneityWeight weight rate i)
      (staticHeterogeneityWeight weight rate i t * (-rate i)) t := by
  change HasDerivAt (fun s : ℝ => weight i * Real.exp (-(rate i * s)))
    (weight i * Real.exp (-(rate i * t)) * (-rate i)) t
  have hinner : HasDerivAt (fun s : ℝ => -(rate i * s)) (-rate i) t := by
    simpa only [neg_mul] using (hasDerivAt_const_mul (-(rate i)) :
      HasDerivAt (fun s : ℝ => (-(rate i)) * s) (-(rate i)) t)
  have hexp := (Real.hasDerivAt_exp (-(rate i * t))).comp t hinner
  simpa only [Function.comp_apply, mul_assoc] using
    hexp.const_mul (weight i)

/-- Partition derivative is the negative first tilted moment. -/
theorem hasDerivAt_staticHeterogeneityPartition
    {ι : Type*} [Fintype ι]
    (weight rate : ι → ℝ) (t : ℝ) :
    HasDerivAt (staticHeterogeneityPartition weight rate)
      (-staticHeterogeneityMoment weight rate 1 t) t := by
  classical
  have hsum := HasDerivAt.sum
      (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
        hasDerivAt_staticHeterogeneityWeight weight rate t i)
  have heq :
      (∑ i, staticHeterogeneityWeight weight rate i t * (-rate i)) =
        -(∑ i, staticHeterogeneityWeight weight rate i t * rate i) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simpa only [staticHeterogeneityPartition, staticHeterogeneityMoment,
    Finset.sum_apply, pow_one] using hsum.congr_deriv heq

/-- First tilted-moment derivative is the negative second tilted moment. -/
theorem hasDerivAt_staticHeterogeneityMoment_one
    {ι : Type*} [Fintype ι]
    (weight rate : ι → ℝ) (t : ℝ) :
    HasDerivAt (staticHeterogeneityMoment weight rate 1)
      (-staticHeterogeneityMoment weight rate 2 t) t := by
  classical
  have hsum := HasDerivAt.sum
      (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
        (hasDerivAt_staticHeterogeneityWeight weight rate t i).mul_const
          (rate i ^ 1))
  have heq :
      (∑ i, staticHeterogeneityWeight weight rate i t * (-rate i) * rate i ^ 1) =
        -(∑ i, staticHeterogeneityWeight weight rate i t * rate i ^ 2) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simpa only [staticHeterogeneityMoment, Finset.sum_apply] using
    hsum.congr_deriv heq

/-- Normalized posterior rate weight selected by elapsed time. -/
def staticHeterogeneityPosterior {ι : Type*} [Fintype ι]
    (weight rate : ι → ℝ) (t : ℝ) (i : ι) : ℝ :=
  staticHeterogeneityWeight weight rate i t /
    staticHeterogeneityPartition weight rate t

/-- Posterior mean rate. -/
def staticHeterogeneityMean {ι : Type*} [Fintype ι]
    (weight rate : ι → ℝ) : ℝ → ℝ :=
  staticHeterogeneityMoment weight rate 1 /
    staticHeterogeneityPartition weight rate

/-- Posterior rate variance. -/
def staticHeterogeneityVariance {ι : Type*} [Fintype ι]
    (weight rate : ι → ℝ) : ℝ → ℝ := fun t =>
  staticHeterogeneityMoment weight rate 2 t /
      staticHeterogeneityPartition weight rate t -
    staticHeterogeneityMean weight rate t ^ 2

/-- Local apparent exponent `t * posteriorMean(t)`. -/
def staticHeterogeneityExponent {ι : Type*} [Fintype ι]
    (weight rate : ι → ℝ) : ℝ → ℝ :=
  id * staticHeterogeneityMean weight rate

/-- Posterior weights have total mass one. -/
theorem sum_staticHeterogeneityPosterior_eq_one
    {ι : Type*} [Fintype ι]
    (weight rate : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hwpos : ∃ i, 0 < weight i) (t : ℝ) :
    ∑ i, staticHeterogeneityPosterior weight rate t i = 1 := by
  simp only [staticHeterogeneityPosterior]
  rw [← Finset.sum_div]
  simp only [staticHeterogeneityPartition, Finset.sum_apply]
  exact div_self (by
    simpa only [staticHeterogeneityPartition, Finset.sum_apply] using
      ne_of_gt (staticHeterogeneityPartition_pos weight rate hw hwpos t))

/-- Every posterior weight is nonnegative. -/
theorem staticHeterogeneityPosterior_nonneg
    {ι : Type*} [Fintype ι]
    (weight rate : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hwpos : ∃ i, 0 < weight i) (t : ℝ) (i : ι) :
    0 ≤ staticHeterogeneityPosterior weight rate t i := by
  exact div_nonneg
    (mul_nonneg (hw i) (Real.exp_pos _).le)
    (staticHeterogeneityPartition_pos weight rate hw hwpos t).le

/-- Every active source weight remains strictly positive after posterior tilting. -/
theorem staticHeterogeneityPosterior_pos_of_weight_pos
    {ι : Type*} [Fintype ι]
    (weight rate : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hwpos : ∃ i, 0 < weight i) (t : ℝ) (i : ι)
    (hi : 0 < weight i) :
    0 < staticHeterogeneityPosterior weight rate t i := by
  exact div_pos (mul_pos hi (Real.exp_pos _))
    (staticHeterogeneityPartition_pos weight rate hw hwpos t)

/-- Posterior rate moments are normalized tilted moments. -/
theorem sum_staticHeterogeneityPosterior_mul_rate_pow
    {ι : Type*} [Fintype ι]
    (weight rate : ι → ℝ) (k : ℕ) (t : ℝ) :
    (∑ i, staticHeterogeneityPosterior weight rate t i * rate i ^ k) =
      staticHeterogeneityMoment weight rate k t /
        staticHeterogeneityPartition weight rate t := by
  simp only [staticHeterogeneityPosterior, staticHeterogeneityMoment,
    Finset.sum_apply]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Posterior curvature is the centered weighted square sum. -/
theorem staticHeterogeneityVariance_eq_sum_sq
    {ι : Type*} [Fintype ι]
    (weight rate : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hwpos : ∃ i, 0 < weight i) (t : ℝ) :
    staticHeterogeneityVariance weight rate t =
      ∑ i, staticHeterogeneityPosterior weight rate t i *
        (rate i - staticHeterogeneityMean weight rate t) ^ 2 := by
  have hzero := sum_staticHeterogeneityPosterior_eq_one weight rate hw hwpos t
  have hone := sum_staticHeterogeneityPosterior_mul_rate_pow weight rate 1 t
  have htwo := sum_staticHeterogeneityPosterior_mul_rate_pow weight rate 2 t
  simp only [pow_one] at hone
  rw [staticHeterogeneityVariance]
  rw [← htwo]
  calc
    (∑ i, staticHeterogeneityPosterior weight rate t i * rate i ^ 2) -
        staticHeterogeneityMean weight rate t ^ 2 =
      (∑ i, staticHeterogeneityPosterior weight rate t i * rate i ^ 2) -
        2 * staticHeterogeneityMean weight rate t *
          (∑ i, staticHeterogeneityPosterior weight rate t i * rate i) +
        staticHeterogeneityMean weight rate t ^ 2 *
          (∑ i, staticHeterogeneityPosterior weight rate t i) := by
            rw [hone, hzero]
            simp only [staticHeterogeneityMean, Pi.div_apply]
            ring
    _ = ∑ i, staticHeterogeneityPosterior weight rate t i *
        (rate i - staticHeterogeneityMean weight rate t) ^ 2 := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- Static-heterogeneity posterior curvature is nonnegative. -/
theorem staticHeterogeneityVariance_nonneg
    {ι : Type*} [Fintype ι]
    (weight rate : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hwpos : ∃ i, 0 < weight i) (t : ℝ) :
    0 ≤ staticHeterogeneityVariance weight rate t := by
  rw [staticHeterogeneityVariance_eq_sum_sq weight rate hw hwpos t]
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (staticHeterogeneityPosterior_nonneg weight rate hw hwpos t i)
      (sq_nonneg _)

/-- Two posterior replicas measure exactly twice the rate variance. -/
theorem staticHeterogeneityPosterior_pairwiseSqGap
    {ι : Type*} [Fintype ι]
    (weight rate : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hwpos : ∃ i, 0 < weight i) (t : ℝ) :
    (∑ i, ∑ j,
        staticHeterogeneityPosterior weight rate t i *
          staticHeterogeneityPosterior weight rate t j *
            (rate i - rate j) ^ 2) =
      2 * staticHeterogeneityVariance weight rate t := by
  have hpair := normalizedWeight_pairwiseSqGap_eq_two_mul_variance
    (staticHeterogeneityPosterior weight rate t) rate
    (sum_staticHeterogeneityPosterior_eq_one weight rate hw hwpos t)
  have hone := sum_staticHeterogeneityPosterior_mul_rate_pow weight rate 1 t
  have htwo := sum_staticHeterogeneityPosterior_mul_rate_pow weight rate 2 t
  simp only [pow_one] at hone
  calc
    (∑ i, ∑ j,
        staticHeterogeneityPosterior weight rate t i *
          staticHeterogeneityPosterior weight rate t j *
            (rate i - rate j) ^ 2) =
      2 * ((∑ i, staticHeterogeneityPosterior weight rate t i * rate i ^ 2) -
        (∑ i, staticHeterogeneityPosterior weight rate t i * rate i) ^ 2) := hpair
    _ = 2 * staticHeterogeneityVariance weight rate t := by
      rw [hone, htwo, staticHeterogeneityVariance]
      simp only [staticHeterogeneityMean, Pi.div_apply]

/-- The first moment determinant equals partition mass squared times posterior variance. -/
theorem staticHeterogeneityDeterminant_eq_variance
    {ι : Type*} [Fintype ι]
    (weight rate : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hwpos : ∃ i, 0 < weight i) (t : ℝ) :
    staticHeterogeneityPartition weight rate t *
          staticHeterogeneityMoment weight rate 2 t -
        staticHeterogeneityMoment weight rate 1 t ^ 2 =
      staticHeterogeneityPartition weight rate t ^ 2 *
        staticHeterogeneityVariance weight rate t := by
  have hZ := ne_of_gt (staticHeterogeneityPartition_pos weight rate hw hwpos t)
  rw [staticHeterogeneityVariance]
  simp only [staticHeterogeneityMean, Pi.div_apply]
  field_simp [hZ]

/-- Posterior mean rate dissipates exactly by negative posterior variance. -/
theorem hasDerivAt_staticHeterogeneityMean
    {ι : Type*} [Fintype ι]
    (weight rate : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hwpos : ∃ i, 0 < weight i) (t : ℝ) :
    HasDerivAt (staticHeterogeneityMean weight rate)
      (-staticHeterogeneityVariance weight rate t) t := by
  have hZ := ne_of_gt (staticHeterogeneityPartition_pos weight rate hw hwpos t)
  have hquot := (hasDerivAt_staticHeterogeneityMoment_one weight rate t).div
    (hasDerivAt_staticHeterogeneityPartition weight rate t) hZ
  have heq :
      ((-staticHeterogeneityMoment weight rate 2 t) *
          staticHeterogeneityPartition weight rate t -
        staticHeterogeneityMoment weight rate 1 t *
          (-staticHeterogeneityMoment weight rate 1 t)) /
          staticHeterogeneityPartition weight rate t ^ 2 =
        -staticHeterogeneityVariance weight rate t := by
    rw [staticHeterogeneityVariance]
    simp only [staticHeterogeneityMean, Pi.div_apply]
    field_simp [hZ]
    ring
  simpa only [staticHeterogeneityMean] using hquot.congr_deriv heq

/-- Apparent-exponent response is mean rate minus clock-weighted curvature. -/
theorem hasDerivAt_staticHeterogeneityExponent
    {ι : Type*} [Fintype ι]
    (weight rate : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hwpos : ∃ i, 0 < weight i) (t : ℝ) :
    HasDerivAt (staticHeterogeneityExponent weight rate)
      (staticHeterogeneityMean weight rate t -
        t * staticHeterogeneityVariance weight rate t) t := by
  have hprod := (hasDerivAt_id t).mul
    (hasDerivAt_staticHeterogeneityMean weight rate hw hwpos t)
  rw [staticHeterogeneityExponent]
  exact hprod.congr_deriv (by simp only [id_eq, one_mul]; ring)

/-- Log-clock observer balance: `t * α' = α - t² * variance`. -/
theorem staticHeterogeneityExponent_balance
    {ι : Type*} [Fintype ι]
    (weight rate : ι → ℝ) (t : ℝ) :
    t * (staticHeterogeneityMean weight rate t -
        t * staticHeterogeneityVariance weight rate t) =
      staticHeterogeneityExponent weight rate t -
        t ^ 2 * staticHeterogeneityVariance weight rate t := by
  change t * (staticHeterogeneityMean weight rate t -
      t * staticHeterogeneityVariance weight rate t) =
    t * staticHeterogeneityMean weight rate t -
      t ^ 2 * staticHeterogeneityVariance weight rate t
  ring

/-- A common rate floor survives posterior normalization. -/
theorem staticHeterogeneityMean_ge_rateFloor
    {ι : Type*} [Fintype ι]
    (weight rate : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hwpos : ∃ i, 0 < weight i)
    (rateFloor : ℝ) (hfloor : ∀ i, rateFloor ≤ rate i) (t : ℝ) :
    rateFloor ≤ staticHeterogeneityMean weight rate t := by
  have hZpos := staticHeterogeneityPartition_pos weight rate hw hwpos t
  have hsum :
      0 ≤ ∑ i, staticHeterogeneityWeight weight rate i t *
        (rate i - rateFloor) := by
    exact Finset.sum_nonneg fun i _ => mul_nonneg
      (mul_nonneg (hw i) (Real.exp_pos _).le) (sub_nonneg.mpr (hfloor i))
  rw [staticHeterogeneityMean]
  apply (le_div_iff₀ hZpos).2
  rw [staticHeterogeneityMoment, staticHeterogeneityPartition,
    Finset.sum_apply, Finset.sum_apply]
  simp only [pow_one]
  calc
    rateFloor * ∑ i, staticHeterogeneityWeight weight rate i t ≤
        ∑ i, staticHeterogeneityWeight weight rate i t * rateFloor +
          ∑ i, staticHeterogeneityWeight weight rate i t * (rate i - rateFloor) := by
      have hcomm :
          rateFloor * ∑ i, staticHeterogeneityWeight weight rate i t =
            ∑ i, staticHeterogeneityWeight weight rate i t * rateFloor := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hcomm]
      exact le_add_of_nonneg_right hsum
    _ = ∑ i, staticHeterogeneityWeight weight rate i t * rate i := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- Apparent exponent grows at least linearly when every rate has a common floor. -/
theorem staticHeterogeneityExponent_ge_rateFloor_mul_time
    {ι : Type*} [Fintype ι]
    (weight rate : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hwpos : ∃ i, 0 < weight i)
    (rateFloor : ℝ) (hfloor : ∀ i, rateFloor ≤ rate i)
    (t : ℝ) (ht : 0 ≤ t) :
    rateFloor * t ≤ staticHeterogeneityExponent weight rate t := by
  change rateFloor * t ≤ t * staticHeterogeneityMean weight rate t
  have hmean := staticHeterogeneityMean_ge_rateFloor
    weight rate hw hwpos rateFloor hfloor t
  nlinarith

/-- Every apparent-exponent sublevel has bounded nonnegative clock projection. -/
theorem time_le_of_staticHeterogeneityExponent_le
    {ι : Type*} [Fintype ι]
    (weight rate : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hwpos : ∃ i, 0 < weight i)
    (rateFloor : ℝ) (hfloorPos : 0 < rateFloor)
    (hfloor : ∀ i, rateFloor ≤ rate i)
    (t A : ℝ) (ht : 0 ≤ t)
    (hA : staticHeterogeneityExponent weight rate t ≤ A) :
    t ≤ A / rateFloor := by
  have hlower := staticHeterogeneityExponent_ge_rateFloor_mul_time
    weight rate hw hwpos rateFloor hfloor t ht
  apply (le_div_iff₀ hfloorPos).2
  nlinarith

/-- Zero posterior curvature forces all active source rates to coincide. -/
theorem active_rates_eq_of_staticHeterogeneityVariance_eq_zero
    {ι : Type*} [Fintype ι]
    (weight rate : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hwpos : ∃ i, 0 < weight i) (t : ℝ)
    (hzero : staticHeterogeneityVariance weight rate t = 0)
    {i j : ι} (hi : 0 < weight i) (hj : 0 < weight j) :
    rate i = rate j := by
  rw [staticHeterogeneityVariance_eq_sum_sq weight rate hw hwpos t] at hzero
  have hterm : ∀ k ∈ (Finset.univ : Finset ι),
      0 ≤ staticHeterogeneityPosterior weight rate t k *
        (rate k - staticHeterogeneityMean weight rate t) ^ 2 := by
    intro k _
    exact mul_nonneg
      (staticHeterogeneityPosterior_nonneg weight rate hw hwpos t k) (sq_nonneg _)
  have hizero := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hzero i (Finset.mem_univ i)
  have hjzero := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hzero j (Finset.mem_univ j)
  have hisq : (rate i - staticHeterogeneityMean weight rate t) ^ 2 = 0 := by
    exact (mul_eq_zero.mp hizero).resolve_left
      (ne_of_gt (staticHeterogeneityPosterior_pos_of_weight_pos
        weight rate hw hwpos t i hi))
  have hjsq : (rate j - staticHeterogeneityMean weight rate t) ^ 2 = 0 := by
    exact (mul_eq_zero.mp hjzero).resolve_left
      (ne_of_gt (staticHeterogeneityPosterior_pos_of_weight_pos
        weight rate hw hwpos t j hj))
  have hiMean : rate i = staticHeterogeneityMean weight rate t := by nlinarith
  have hjMean : rate j = staticHeterogeneityMean weight rate t := by nlinarith
  exact hiMean.trans hjMean.symm

/-- Collapse of all active rates forces posterior curvature to vanish. -/
theorem staticHeterogeneityVariance_eq_zero_of_active_rates_eq
    {ι : Type*} [Fintype ι]
    (weight rate : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hwpos : ∃ i, 0 < weight i) (t : ℝ)
    (hactive : ∀ i j, 0 < weight i → 0 < weight j → rate i = rate j) :
    staticHeterogeneityVariance weight rate t = 0 := by
  have hpair := staticHeterogeneityPosterior_pairwiseSqGap
    weight rate hw hwpos t
  have hsum :
      (∑ i, ∑ j,
        staticHeterogeneityPosterior weight rate t i *
          staticHeterogeneityPosterior weight rate t j *
            (rate i - rate j) ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    by_cases hi : weight i = 0
    · simp [staticHeterogeneityPosterior, staticHeterogeneityWeight, hi]
    by_cases hj : weight j = 0
    · simp [staticHeterogeneityPosterior, staticHeterogeneityWeight, hj]
    have hipos : 0 < weight i := lt_of_le_of_ne (hw i) (Ne.symm hi)
    have hjpos : 0 < weight j := lt_of_le_of_ne (hw j) (Ne.symm hj)
    rw [hactive i j hipos hjpos]
    ring
  linarith

end
end HTGeometry
