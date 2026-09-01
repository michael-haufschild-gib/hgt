import GaloisForLFunctions.RHTower.XiWardCubicPositiveShiftDampedDiagonalSeparator

/-!
# Positive-shift scale resonance and finite-mixture no-go

The damped cubic separator is not monotone in depth-to-shift ratio.  Its full diagonal quantum is
attained exactly at the resonant scale `eps = 2a`; beyond that point the profile drops, so signed
dyadic scale differences need not be positive.

More generally, every fixed finite weighted mixture of source shifts becomes blind as horizontal
depth tends to zero.  Thus neither finitely many fixed shifts nor a nonnegative dyadic-difference
telescope can replace the missing all-scale or source-adaptive Stokes landing.  The positive
survivor is the exact resonance law: a displacement-matched shift pays the full quantum.
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

/-- Signed dyadic increment of the positive-shift diagonal profile. -/
def xiWardCubicPositiveShiftDyadicShellProfile (x : ℝ) : ℝ :=
  xiWardCubicPositiveShiftDiagonalSeparatorProfile (2 * x) -
    xiWardCubicPositiveShiftDiagonalSeparatorProfile x

/-- At depth-to-shift ratio `1/2`, the damped anomaly vanishes exactly. -/
theorem xiWardCubicPositiveShiftDiagonalAnomalyProfile_half :
    xiWardCubicPositiveShiftDiagonalAnomalyProfile (1 / 2) = 0 := by
  norm_num [xiWardCubicPositiveShiftDiagonalAnomalyProfile]

/-- The resonant ratio `1/2` receives the complete cubic Hellinger quantum. -/
theorem xiWardCubicPositiveShiftDiagonalSeparatorProfile_half :
    xiWardCubicPositiveShiftDiagonalSeparatorProfile (1 / 2) = 115 / 108 := by
  rw [xiWardCubicPositiveShiftDiagonalSeparatorProfile,
    xiWardCubicPositiveShiftDiagonalAnomalyProfile_half]
  ring

/-- The profile has already fallen strictly below its resonant value at ratio one. -/
theorem xiWardCubicPositiveShiftDiagonalSeparatorProfile_one_lt_half :
    xiWardCubicPositiveShiftDiagonalSeparatorProfile 1 <
      xiWardCubicPositiveShiftDiagonalSeparatorProfile (1 / 2) := by
  norm_num [xiWardCubicPositiveShiftDiagonalSeparatorProfile,
    xiWardCubicPositiveShiftDiagonalAnomalyProfile]

/-- Dyadic shell differences are not positive: the shell starting at the resonant ratio is
strictly negative. -/
theorem xiWardCubicPositiveShiftDyadicShellProfile_half_neg :
    xiWardCubicPositiveShiftDyadicShellProfile (1 / 2) < 0 := by
  rw [xiWardCubicPositiveShiftDyadicShellProfile]
  norm_num
  exact xiWardCubicPositiveShiftDiagonalSeparatorProfile_one_lt_half

/-- The separator profile is not monotone on the nonnegative depth ray. -/
theorem not_monotoneOn_xiWardCubicPositiveShiftDiagonalSeparatorProfile :
    ¬ MonotoneOn xiWardCubicPositiveShiftDiagonalSeparatorProfile (Ici 0) := by
  intro hmono
  have hle := hmono (by norm_num) (by norm_num) (by norm_num : (1 / 2 : ℝ) ≤ 1)
  exact (not_le_of_gt
    xiWardCubicPositiveShiftDiagonalSeparatorProfile_one_lt_half) hle

/-- A displacement-matched source shift `eps = 2a` pays the complete quantum. -/
theorem xiWardCubicPositiveShiftDiagonalSeparatorProfile_resonant
    {a : ℝ} (ha : a ≠ 0) :
    xiWardCubicPositiveShiftDiagonalSeparatorProfile (a / (2 * a)) = 115 / 108 := by
  rw [show a / (2 * a) = (1 / 2 : ℝ) by field_simp]
  exact xiWardCubicPositiveShiftDiagonalSeparatorProfile_half

theorem continuousAt_xiWardCubicPositiveShiftDiagonalSeparatorProfile_zero :
    ContinuousAt xiWardCubicPositiveShiftDiagonalSeparatorProfile 0 := by
  unfold xiWardCubicPositiveShiftDiagonalSeparatorProfile
    xiWardCubicPositiveShiftDiagonalAnomalyProfile
  fun_prop (disch := norm_num)

/-- **Finite-mixture shallow-collar no-go.**  Any fixed finite collection of source shifts, with
arbitrary real weights, loses all diagonal charge as displacement approaches the critical line.
Hence a uniform all-depth quantum requires an unbounded scale family or source-adaptive scale. -/
theorem tendsto_finset_weighted_xiWardCubicPositiveShiftDiagonalSeparatorProfile_zero
    {ι : Type*} (S : Finset ι) (eps w : ι → ℝ) :
    Tendsto
      (fun a : ℝ => ∑ i ∈ S,
        w i * xiWardCubicPositiveShiftDiagonalSeparatorProfile (a / eps i))
      (nhds 0) (nhds 0) := by
  have hterm (i : ι) : Tendsto
      (fun a : ℝ => w i *
        xiWardCubicPositiveShiftDiagonalSeparatorProfile (a / eps i))
      (nhds 0) (nhds 0) := by
    have hratio : Tendsto (fun a : ℝ => a / eps i) (nhds 0) (nhds 0) := by
      by_cases heps : eps i = 0
      · simp [heps]
      · simpa [heps] using
          (show ContinuousAt (fun a : ℝ => a / eps i) 0 by fun_prop).tendsto
    have hprofile :=
      continuousAt_xiWardCubicPositiveShiftDiagonalSeparatorProfile_zero.tendsto.comp hratio
    have hmul := (tendsto_const_nhds (x := w i)).mul hprofile
    simpa only [Function.comp_apply,
      xiWardCubicPositiveShiftDiagonalSeparatorProfile_zero, mul_zero] using hmul
  simpa only [Finset.sum_const_zero] using
    tendsto_finsetSum S (fun i _hi => hterm i)

/-- **Finite scale-mass no-go.**  The same blindness holds for every fixed finite measure on
positive source scales, not only for a finite combination.  Dominated convergence applies because
the separator lies between zero and `115/108` on the positive depth ray.  Therefore uniform
all-depth charge requires infinite scale mass or a scale law that moves with the tested depth. -/
theorem tendsto_integral_xiWardCubicPositiveShiftDiagonalSeparatorProfile_zero
    (μ : MeasureTheory.Measure (Ioi (0 : ℝ))) [MeasureTheory.IsFiniteMeasure μ]
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (ha0 : Tendsto a atTop (nhds 0)) :
    Tendsto
      (fun n => ∫ eps : Ioi (0 : ℝ),
        xiWardCubicPositiveShiftDiagonalSeparatorProfile (a n / (eps : ℝ)) ∂μ)
      atTop (nhds 0) := by
  have hmeas (n : ℕ) : MeasureTheory.AEStronglyMeasurable
      (fun eps : Ioi (0 : ℝ) =>
        xiWardCubicPositiveShiftDiagonalSeparatorProfile (a n / (eps : ℝ))) μ := by
    apply Continuous.aestronglyMeasurable
    unfold xiWardCubicPositiveShiftDiagonalSeparatorProfile
      xiWardCubicPositiveShiftDiagonalAnomalyProfile
    fun_prop (disch := exact ne_of_gt eps.property)
  have hbound (n : ℕ) : ∀ᵐ eps : Ioi (0 : ℝ) ∂μ,
      ‖xiWardCubicPositiveShiftDiagonalSeparatorProfile (a n / (eps : ℝ))‖ ≤
        (115 / 108 : ℝ) := by
    filter_upwards with eps
    have hratio : 0 ≤ a n / (eps : ℝ) := div_nonneg (ha n) eps.property.le
    rw [Real.norm_eq_abs, abs_of_nonneg
      (xiWardCubicPositiveShiftDiagonalSeparatorProfile_nonneg hratio)]
    exact xiWardCubicPositiveShiftDiagonalSeparatorProfile_le_quantum hratio
  have hlim : ∀ᵐ eps : Ioi (0 : ℝ) ∂μ, Tendsto
      (fun n => xiWardCubicPositiveShiftDiagonalSeparatorProfile (a n / (eps : ℝ)))
      atTop (nhds 0) := by
    filter_upwards with eps
    have hratio : Tendsto (fun n => a n / (eps : ℝ)) atTop (nhds 0) := by
      simpa [eps.property.ne'] using ha0.div_const (eps : ℝ)
    simpa only [xiWardCubicPositiveShiftDiagonalSeparatorProfile_zero] using
      continuousAt_xiWardCubicPositiveShiftDiagonalSeparatorProfile_zero.tendsto.comp hratio
  simpa using MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun _ : Ioi (0 : ℝ) => (115 / 108 : ℝ)) hmeas
    (MeasureTheory.integrable_const _) (fun n => hbound n) hlim

end

end RHTower
