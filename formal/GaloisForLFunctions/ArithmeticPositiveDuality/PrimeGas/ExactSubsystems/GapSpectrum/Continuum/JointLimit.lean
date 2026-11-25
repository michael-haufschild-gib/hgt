import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.Continuum.GapLimit

/-! # The joint discrete and continuous limit of two prime-gas samples -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems

open Filter Topology MeasureTheory

private theorem test_scaleLaw {x : ℝ} (hx : 1/4 < x) (f : BoundedContinuousFunction ℕ+ ℝ) :
    ∫ k, f k ∂(scaleLaw x hx : Measure ℕ+) = ∑' k, (commonScaleWeight x k).re * f k := by
  rw [integral_countable (f.integrable (scaleLaw x hx : Measure ℕ+))]
  apply tsum_congr
  intro k
  obtain ⟨r,hr,he⟩ := commonScaleWeight_positive hx k
  rw [measureReal_def,scaleLaw_atom,← he,Complex.ofReal_re,ENNReal.toReal_ofReal hr.le,smul_eq_mul]

private theorem scale_open (h : Set.Ioi (0:ℝ)) : 1/4 < excessDamping h :=
  (by norm_num : (1/4:ℝ) < 1/2).trans (excessDamping_gt h)

/-- Weak convergence on the discrete divisor space, tested against every bounded observable. -/
theorem critical_scale_weak_limit :
    Tendsto (fun h => scaleLaw (excessDamping h) (scale_open h)) criticalApproach
      (𝓝 (scaleLaw (1/2) (by norm_num))) := by
  have htemp : Tendsto excessDamping criticalApproach (𝓝 (1/2)) := by
    have hv : Tendsto (fun h : Set.Ioi (0:ℝ) => h.val/2) criticalApproach (𝓝 0) :=
      half_excess_tendsto.mono_right nhdsWithin_le_nhds
    have hs := (tendsto_const_nhds (x := (1/2:ℝ))).add hv
    rw [add_zero] at hs
    exact hs.congr (fun _ => rfl)
  rw [tendsto_iff_seq_tendsto]
  intro u hu
  apply (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℝ).mpr
  intro f
  let clip := fun t : ℝ => max (-‖f‖) (min ‖f‖ t)
  have hb (t : ℝ) : |clip t| ≤ ‖f‖ :=
    abs_le.mpr ⟨le_max_left _ _,max_le (by linarith [norm_nonneg f]) (min_le_left _ _)⟩
  have hclip (k : ℕ+) : clip (f k) = f k := by
    have ha : |f k| ≤ ‖f‖ := f.norm_coe_le_norm k
    simp only [clip,min_eq_right (abs_le.mp ha).2,max_eq_right (abs_le.mp ha).1]
  let p := fun n k => (commonScaleWeight (excessDamping (u n)) k).re
  have hpos (n : ℕ) (k : ℕ+) : 0 ≤ p n k := by
    obtain ⟨r,hr,he⟩ := commonScaleWeight_positive (scale_open (u n)) k
    exact hr.le.trans_eq (congrArg Complex.re he)
  have hpt (k : ℕ+) : Tendsto (fun n => p n k) atTop (𝓝 (commonScaleWeight (1/2) k).re) := by
    have ht := commonScaleWeight_tendsto_critical k
    rw [← commonScaleWeight_critical k] at ht
    exact (Complex.continuous_re.tendsto _).comp (ht.comp (htemp.comp hu))
  have hl := HTGeometry.tendsto_tsum_mul_comp_of_tendsto
    (x := fun (_ : ℕ) (k : ℕ+) => f k) (xlim := fun k => f k) (f := clip) hpos
    (fun n => commonScaleReal_hasSum (scale_open (u n))) (commonScaleReal_hasSum (by norm_num : (1/4:ℝ) < 1/2))
    hpt (fun _ => tendsto_const_nhds) (by unfold clip; fun_prop) hb
  simpa only [Function.comp_apply,test_scaleLaw,hclip,p] using hl

/-- The literal gcd and h log(m/n) of the two independent Gibbs labels. -/
def criticalJointLaw (h : Set.Ioi (0:ℝ)) : ProbabilityMeasure (ℕ+ × ℝ) :=
  sampledJointLaw (excessDamping h) (h.val/2) (excessDamping_gt h)

/-- The surviving divisor has inverse-square mass. The independent scaled signed gap has Laplace density. -/
theorem critical_joint_weak_limit :
    Tendsto criticalJointLaw criticalApproach
      (𝓝 ((scaleLaw (1/2) (by norm_num)).prod _root_.RHTower.mobiusCriticalLaplaceGapProbabilityMeasure)) := by
  have hp := ProbabilityMeasure.continuous_prod.continuousAt.tendsto.comp
    (critical_scale_weak_limit.prodMk_nhds critical_gap_weak_limit)
  apply hp.congr
  intro h
  exact (sampled_joint_eq_product (excessDamping_gt h) (h.val/2)).symm

#print axioms critical_scale_weak_limit
#print axioms critical_joint_weak_limit

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems
