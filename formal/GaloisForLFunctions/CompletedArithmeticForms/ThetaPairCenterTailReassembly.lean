import GaloisForLFunctions.CompletedArithmeticForms.ThetaPairCenterTailSeries
import GaloisForLFunctions.RHTower.ThetaEulerTwoPortJetPole

/-!
# Reassembly of ordinary theta-atom center tails

An exponentially tilted absolute atom mass scales as the inverse square
of its integer label. Its summability justifies the ordinary-pair
sum/integral exchange on every upper center half-plane.
-/

open MeasureTheory Set Filter Topology Complex
open scoped BigOperators
namespace GaloisForLFunctions.CompletedArithmeticForms
open _root_.RHTower
noncomputable section

private def tiltedAbsAtom (n : ℕ) (x : ℝ) : ℝ :=
  Real.exp ((3 / 2 : ℝ) * x) * |thetaCuspSourceTerm x (n + 1)|

private theorem tiltedAbsAtom_nonneg (n : ℕ) (x : ℝ) : 0 ≤ tiltedAbsAtom n x :=
  mul_nonneg (Real.exp_pos _).le (abs_nonneg _)

private theorem integrable_tiltedAbsAtom (n : ℕ) : Integrable (tiltedAbsAtom n) := by
  change Integrable (fun x : ℝ => Real.exp ((3 / 2 : ℝ) * x) *
    |thetaCuspSourceTerm x (n + 1)|)
  have h := (integrable_cexp_mul_thetaCuspSourceTerm (3 / 2 : ℂ)
    (by norm_num) (n + 1) (Nat.succ_pos n)).norm
  simpa [norm_mul, Complex.norm_exp, Complex.norm_real,
    Real.norm_eq_abs, Complex.mul_re] using h

private theorem summable_tiltedAbsAtom (x : ℝ) :
    Summable (fun n => tiltedAbsAtom n x) := by
  have h := ((summable_nat_add_iff 1).mpr (summable_thetaCuspSourceTerm x)).norm
  simpa only [tiltedAbsAtom, Real.norm_eq_abs] using h.mul_left (Real.exp ((3 / 2 : ℝ) * x))

private def tiltedAbsSource (x : ℝ) : ℝ := ∑' n, tiltedAbsAtom n x

private theorem tiltedAbsSource_nonneg (x : ℝ) : 0 ≤ tiltedAbsSource x :=
  tsum_nonneg (fun n => tiltedAbsAtom_nonneg n x)

private theorem integrable_tiltedAbsSource : Integrable tiltedAbsSource := by
  -- Translation of each atom makes its tilted absolute mass proportional to the inverse square label.
  apply HTGeometry.integrable_tsum_of_summable_integral_norm integrable_tiltedAbsAtom
  have hmass (n : ℕ) : (∫ x : ℝ, ‖tiltedAbsAtom n x‖) =
      ((n + 1 : ℕ) : ℝ) ^ (-2 : ℝ) * ∫ x : ℝ, tiltedAbsAtom 0 x := by
    simp_rw [Real.norm_of_nonneg (tiltedAbsAtom_nonneg n _)]
    simpa only [tiltedAbsAtom, show -(3 / 2 + 1 / 2 : ℝ) = -2 by norm_num,
      Nat.zero_add] using integral_exp_mul_abs_thetaCuspSourceTerm (3 / 2) (Nat.succ_pos n)
  simp_rw [hmass]
  exact ((summable_nat_add_iff 1).mpr
    (Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1))).mul_right _

private theorem centerDifference_measurePreserving :
    MeasurePreserving (fun p : ℝ × ℝ => (p.1 / 2 + p.2, p.1 / 2 - p.2))
      (volume.prod volume) (volume.prod volume) := by
  -- A shear, a subtraction, and a swap give the center/difference change of coordinates.
  have hshear : MeasurePreserving (fun p : ℝ × ℝ => (p.1, p.2 + p.1 / 2))
      (volume.prod volume) (volume.prod volume) :=
    (MeasurePreserving.id (volume : Measure ℝ)).skew_product (by fun_prop)
      (Filter.Eventually.of_forall fun s => (measurePreserving_add_right volume (s / 2)).map_eq)
  have h := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := volume)).comp
    ((measurePreserving_sub_prod (volume : Measure ℝ) volume).comp hshear)
  convert h using 1
  funext p
  apply Prod.ext <;> dsimp <;> ring

private theorem integrable_tiltedAbsSource_product :
    Integrable (fun p : ℝ × ℝ =>
      tiltedAbsSource (p.1 / 2 + p.2) * tiltedAbsSource (p.1 / 2 - p.2))
      (volume.prod volume) :=
  centerDifference_measurePreserving.integrable_comp_of_integrable
    (integrable_tiltedAbsSource.mul_prod integrable_tiltedAbsSource)

private def ordinaryPairKernel (b : ℝ) (q : ℕ × ℕ) (p : ℝ × ℝ) : ℂ :=
  (thetaCuspSourceTerm (p.1 / 2 + p.2) (q.1 + 1) *
    thetaCuspSourceTerm (p.1 / 2 - p.2) (q.2 + 1) : ℂ) * thetaWignerDifferencePhase b p.2

private def fullCenterKernel (b : ℝ) (p : ℝ × ℝ) : ℂ :=
  (thetaCuspFullSource (p.1 / 2 + p.2) *
    thetaCuspFullSource (p.1 / 2 - p.2) : ℂ) * thetaWignerDifferencePhase b p.2

private theorem continuous_ordinaryPairKernel (b : ℝ) (q : ℕ × ℕ) :
    Continuous (ordinaryPairKernel b q) := by
  unfold ordinaryPairKernel thetaCuspSourceTerm thetaCuspSeed thetaWignerDifferencePhase
  fun_prop

private theorem norm_ordinaryPairKernel (b : ℝ) (q : ℕ × ℕ) (p : ℝ × ℝ) :
    ‖ordinaryPairKernel b q p‖ = Real.exp (-(3 / 2 : ℝ) * p.1) *
      (tiltedAbsAtom q.1 (p.1 / 2 + p.2) * tiltedAbsAtom q.2 (p.1 / 2 - p.2)) := by
  have he : Real.exp (-(3 / 2 : ℝ) * p.1) *
      (Real.exp ((3 / 2 : ℝ) * (p.1 / 2 + p.2)) *
        Real.exp ((3 / 2 : ℝ) * (p.1 / 2 - p.2))) = 1 := by
    rw [← Real.exp_add, ← Real.exp_add]
    convert Real.exp_zero using 1
    congr 1
    ring
  unfold ordinaryPairKernel
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    thetaWignerDifferencePhase, Complex.norm_exp, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, sub_self, Real.exp_zero, mul_one]
  unfold tiltedAbsAtom
  calc
    _ = 1 * (|thetaCuspSourceTerm (p.1 / 2 + p.2) (q.1 + 1)| *
        |thetaCuspSourceTerm (p.1 / 2 - p.2) (q.2 + 1)|) := by rw [one_mul]
    _ = _ := by rw [← he]; ring

private theorem summable_norm_ordinaryPairKernel (b : ℝ) (p : ℝ × ℝ) :
    Summable (fun q => ‖ordinaryPairKernel b q p‖) := by
  simp_rw [norm_ordinaryPairKernel]
  exact (summable_mul_of_summable_norm (summable_tiltedAbsAtom _).norm
    (summable_tiltedAbsAtom _).norm).mul_left _

private theorem tsum_norm_ordinaryPairKernel (b : ℝ) (p : ℝ × ℝ) :
    (∑' q, ‖ordinaryPairKernel b q p‖) = Real.exp (-(3 / 2 : ℝ) * p.1) *
      (tiltedAbsSource (p.1 / 2 + p.2) * tiltedAbsSource (p.1 / 2 - p.2)) := by
  simp_rw [norm_ordinaryPairKernel]
  rw [tsum_mul_left, ← tsum_mul_tsum_of_summable_norm
    (summable_tiltedAbsAtom _).norm (summable_tiltedAbsAtom _).norm]
  rfl

private theorem hasSum_ordinaryPairKernel (b : ℝ) (p : ℝ × ℝ) :
    HasSum (fun q => ordinaryPairKernel b q p) (fullCenterKernel b p) := by
  have hsource (x : ℝ) : HasSum (fun n : ℕ => (thetaCuspSourceTerm x (n + 1) : ℂ))
      (thetaCuspFullSource x : ℂ) := by
    have hzero : thetaCuspSourceTerm x 0 = 0 := by
      simp [thetaCuspSourceTerm, thetaCuspSeed]
    have hbase : HasSum (thetaCuspSourceTerm x) (thetaCuspFullSource x) :=
      (summable_thetaCuspSourceTerm x).hasSum
    have hshift : HasSum (fun n : ℕ => thetaCuspSourceTerm x (n + 1))
        (thetaCuspFullSource x) := by
      refine (hasSum_nat_add_iff (f := thetaCuspSourceTerm x) 1).mpr ?_
      simpa [Finset.sum_range_one, hzero] using hbase
    exact Complex.ofRealCLM.hasSum hshift
  have hA := hsource (p.1 / 2 + p.2)
  have hB := hsource (p.1 / 2 - p.2)
  have hpair := summable_mul_of_summable_norm hA.summable.norm hB.summable.norm
  have h : HasSum (fun q : ℕ × ℕ =>
      (thetaCuspSourceTerm (p.1 / 2 + p.2) (q.1 + 1) : ℂ) *
        (thetaCuspSourceTerm (p.1 / 2 - p.2) (q.2 + 1) : ℂ))
      ((thetaCuspFullSource (p.1 / 2 + p.2) : ℂ) *
        (thetaCuspFullSource (p.1 / 2 - p.2) : ℂ)) := by
    rw [← hA.tsum_eq, ← hB.tsum_eq,
      tsum_mul_tsum_of_summable_norm hA.summable.norm hB.summable.norm]
    exact hpair.hasSum
  simpa only [ordinaryPairKernel, fullCenterKernel, Complex.ofReal_mul] using
    h.mul_right (thetaWignerDifferencePhase b p.2)

private theorem integrable_tsum_norm_ordinaryPairKernel (r b : ℝ) :
    Integrable (fun p : ℝ × ℝ => ∑' q, ‖ordinaryPairKernel b q p‖)
      ((volume.restrict (Ioi r)).prod volume) := by
  -- On an upper center half-plane, the exponential untilting factor has a constant upper bound.
  rw [Measure.restrict_prod_eq_prod_univ]
  have hmajor := (integrable_tiltedAbsSource_product.const_mul
    (Real.exp (-(3 / 2 : ℝ) * r))).integrableOn (s := Ioi r ×ˢ (univ : Set ℝ))
  apply hmajor.mono'
    (AEStronglyMeasurable.tsum (fun q =>
      (continuous_ordinaryPairKernel b q).norm.aestronglyMeasurable))
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod MeasurableSet.univ)] with p hp
  have hp1 : r < p.1 := hp.1
  rw [Real.norm_of_nonneg (tsum_nonneg (fun q => norm_nonneg _)),
    tsum_norm_ordinaryPairKernel]
  apply mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (by linarith only [hp1]))
    (mul_nonneg (tiltedAbsSource_nonneg _) (tiltedAbsSource_nonneg _))

private theorem integrable_ordinaryPairKernel (r b : ℝ) (q : ℕ × ℕ) :
    Integrable (ordinaryPairKernel b q) ((volume.restrict (Ioi r)).prod volume) := by
  apply (integrable_tsum_norm_ordinaryPairKernel r b).mono'
    (continuous_ordinaryPairKernel b q).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun p =>
    (summable_norm_ordinaryPairKernel b p).le_tsum q (fun _ _ => norm_nonneg _)

private theorem integrable_fullCenterKernel (r b : ℝ) :
    Integrable (fullCenterKernel b) ((volume.restrict (Ioi r)).prod volume) := by
  have he : fullCenterKernel b = fun p => ∑' q, ordinaryPairKernel b q p :=
    funext fun p => (hasSum_ordinaryPairKernel b p).tsum_eq.symm
  apply (integrable_tsum_norm_ordinaryPairKernel r b).mono'
  · rw [he]
    exact AEStronglyMeasurable.tsum fun q =>
      (continuous_ordinaryPairKernel b q).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun p => by
      rw [← (hasSum_ordinaryPairKernel b p).tsum_eq]
      exact norm_tsum_le_tsum_norm (summable_norm_ordinaryPairKernel b p)

private theorem hasSum_integral_ordinaryPairKernel (r b : ℝ) :
    HasSum (fun q => ∫ p : ℝ × ℝ, ordinaryPairKernel b q p
      ∂((volume.restrict (Ioi r)).prod volume))
      (∫ p : ℝ × ℝ, fullCenterKernel b p
        ∂((volume.restrict (Ioi r)).prod volume)) := by
  exact hasSum_integral_of_dominated_convergence
    (fun q p => ‖ordinaryPairKernel b q p‖)
    (fun q => (continuous_ordinaryPairKernel b q).aestronglyMeasurable)
    (fun q => Filter.Eventually.of_forall fun p => le_rfl)
    (Filter.Eventually.of_forall (summable_norm_ordinaryPairKernel b))
    (integrable_tsum_norm_ordinaryPairKernel r b)
    (Filter.Eventually.of_forall (hasSum_ordinaryPairKernel b))

private theorem re_integral_ordinaryPairKernel (r b : ℝ) (q : ℕ × ℕ) :
    (∫ p : ℝ × ℝ, ordinaryPairKernel b q p
      ∂((volume.restrict (Ioi r)).prod volume)).re =
        thetaPairCenterTailSpectrum (q.1 + 1) (q.2 + 1) r b := by
  have hi := integrable_ordinaryPairKernel r b q
  rw [MeasureTheory.integral_prod _ hi]
  have hre := Complex.reCLM.integral_comp_comm hi.integral_prod_left
  change (∫ s in Ioi r, (∫ t : ℝ, ordinaryPairKernel b q (s, t)).re) =
    (∫ s in Ioi r, ∫ t : ℝ, ordinaryPairKernel b q (s, t)).re at hre
  change (∫ s in Ioi r, ∫ t : ℝ, ordinaryPairKernel b q (s, t)).re = _
  rw [← hre]
  rfl

private theorem re_integral_fullCenterKernel (r b : ℝ) :
    (∫ p : ℝ × ℝ, fullCenterKernel b p
      ∂((volume.restrict (Ioi r)).prod volume)).re =
        ∫ s in Ioi r, (thetaWignerDistribution thetaCuspComplexSource (s / 2) b).re := by
  have hi := integrable_fullCenterKernel r b
  rw [MeasureTheory.integral_prod _ hi]
  have hre := Complex.reCLM.integral_comp_comm hi.integral_prod_left
  change (∫ s in Ioi r, (∫ t : ℝ, fullCenterKernel b (s, t)).re) =
    (∫ s in Ioi r, ∫ t : ℝ, fullCenterKernel b (s, t)).re at hre
  change (∫ s in Ioi r, ∫ t : ℝ, fullCenterKernel b (s, t)).re = _
  rw [← hre]
  apply integral_congr_ae
  filter_upwards with s
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  simp only [fullCenterKernel, thetaCuspComplexSource, Complex.conj_ofReal]

/-- The ordinary-pair tail series equals the literal complete-source Fourier tail. -/
theorem thetaPairCenterTailSum_eq_fullSource (r b : ℝ) :
    thetaPairCenterTailSum r b =
      ∫ s in Ioi r, (thetaWignerDistribution thetaCuspComplexSource (s / 2) b).re := by
  have h := Complex.reCLM.hasSum (hasSum_integral_ordinaryPairKernel r b)
  change HasSum (fun q => (∫ p : ℝ × ℝ, ordinaryPairKernel b q p
    ∂((volume.restrict (Ioi r)).prod volume)).re)
    (∫ p : ℝ × ℝ, fullCenterKernel b p
      ∂((volume.restrict (Ioi r)).prod volume)).re at h
  simp_rw [re_integral_ordinaryPairKernel, re_integral_fullCenterKernel] at h
  exact h.tsum_eq

/-- The complete theta-source tail has a frequency-uniform rectangular atom truncation error. -/
theorem thetaFullCenterTail_remainder_le {r : ℝ} (hr : 0 ≤ r) (b : ℝ) (M : ℕ) :
    |(∫ s in Ioi r, (thetaWignerDistribution thetaCuspComplexSource (s / 2) b).re) -
      ∑ p ∈ (Finset.range M ×ˢ Finset.range M),
        thetaPairCenterTailSpectrum (p.1 + 1) (p.2 + 1) r b| ≤
      8 * besselFirstAtomTailCost 0 *
        Real.exp (-(Real.pi * Real.exp r) * ((M : ℝ) + 1)) /
          (1 - Real.exp (-(Real.pi * Real.exp r))) ^ 2 := by
  rw [← thetaPairCenterTailSum_eq_fullSource]
  exact thetaPairCenterTailSum_remainder_le hr b M

end
end GaloisForLFunctions.CompletedArithmeticForms
