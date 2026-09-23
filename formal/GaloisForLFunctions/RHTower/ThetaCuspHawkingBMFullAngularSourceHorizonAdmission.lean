import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFutureSeedHorizonCap
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularGoursat
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularSourceHorizonTrace

/-!
# Literal full-angular source-horizon admission

This proves the uniform physical-clock envelope for the actual full
direct-minus-image kernel at a negative source horizon.  It is the missing
dominated-convergence input for passing the full causal cap integral to the
literal `seedCapField` boundary kernel.

Proof-chain role:
`full causal-horizon admission -> causal cap integral limit -> strong cap
weak equation -> QNM-cutoff/contact identity -> HB B2`.
-/

open MeasureTheory Set Filter Topology

namespace RHTower.D4BMFullAngularSourceHorizonAdmission

open D4BMHorizon D4BMModularCore D4BMJointSource D4BMCausalKernel
open D4BMFullAngularCircle D4BMFullAngularReconstruction D4BMFullAngularGrowth
open D4BMFullAngularSourceHorizonTrace D4BMFutureSeedHorizon D4BMFullSourceAdvanced

noncomputable section
set_option autoImplicit false

private theorem fullMean_source_horizon_majorant (q : XiZeroCopy) (branch : Bool)
    (tau X k : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧
      IntegrableOn (fun v : ℝ => B * Real.exp
        ((2 * (physicalRate q branch).re + decayExponent q) * v)) (Ioi 0) ∧
      ∀ v x y : ℝ, 0 ≤ v → y ≤ 0 →
        ‖angularMean q branch
          (Real.arcosh (max 1 (invariant (v - tau - y) x y))) X k‖ ≤
          B * Real.exp (decayExponent q * v) := by
  obtain ⟨B, hB, hI, h⟩ := angularMean_source_horizon_majorant q branch tau X k
  refine ⟨B, hB, hI, ?_⟩
  intro v x y hv hy
  have hmajor := h v x y hv hy
  dsimp only at hmajor
  rw [show v - y - tau = v - tau - y from by ring] at hmajor
  have hE : 0 < Real.exp (2 * (physicalRate q branch).re * v) := Real.exp_pos _
  have hterm : Real.exp (2 * (physicalRate q branch).re * v) *
      ‖angularMean q branch
        (Real.arcosh (max 1 (invariant (v - tau - y) x y))) X k‖ ≤
      B * Real.exp ((2 * (physicalRate q branch).re + decayExponent q) * v) := by
    refine le_trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right
      (norm_nonneg (deriv (fun r => angularMean q branch r X k)
        (Real.arcosh (max 1 (invariant (v - tau - y) x y)))))) hE.le) hmajor
  calc
    ‖angularMean q branch
        (Real.arcosh (max 1 (invariant (v - tau - y) x y))) X k‖ =
        (Real.exp (2 * (physicalRate q branch).re * v) *
          ‖angularMean q branch
            (Real.arcosh (max 1 (invariant (v - tau - y) x y))) X k‖) /
          Real.exp (2 * (physicalRate q branch).re * v) := by
      field_simp [hE.ne']
    _ ≤ (B * Real.exp ((2 * (physicalRate q branch).re + decayExponent q) * v)) /
          Real.exp (2 * (physicalRate q branch).re * v) :=
      div_le_div_of_nonneg_right hterm hE.le
    _ = B * Real.exp (decayExponent q * v) := by
      rw [show (2 * (physicalRate q branch).re + decayExponent q) * v =
        2 * (physicalRate q branch).re * v + decayExponent q * v by ring, Real.exp_add]
      field_simp [hE.ne']

private theorem onsetFirst_majorant (q : XiZeroCopy) (branch : Bool) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ v : ℝ,
      ‖timeOnsetFirst (2 * physicalRate q branch) v‖ ≤
        A * Real.exp (2 * (physicalRate q branch).re * v) := by
  obtain ⟨A, hA, h⟩ := timeOnset_pair_bound (2 * physicalRate q branch)
    (-(2 * physicalRate q branch).re) (by simp)
  have hre : - -(2 * physicalRate q branch).re = 2 * (physicalRate q branch).re := by
    simp
  refine ⟨A, hA, ?_⟩
  intro v
  calc
    ‖timeOnsetFirst (2 * physicalRate q branch) v‖ ≤
        ‖timeOnset (2 * physicalRate q branch) v‖ +
          ‖timeOnsetFirst (2 * physicalRate q branch) v‖ :=
      le_add_of_nonneg_left (norm_nonneg _)
    _ ≤ A * Real.exp (2 * (physicalRate q branch).re * v) := by
      simpa only [hre] using h v

private def closedSourceFace (q : XiZeroCopy) (branch : Bool)
    (tau target source X k : ℝ) (v : ℝ) : ℂ :=
  angularMean q branch
    (Real.arcosh (max 1 (invariant (v - tau - source) target source))) X k

private theorem closedSourceFace_continuous (q : XiZeroCopy) (branch : Bool)
    (tau target source X k : ℝ) :
    Continuous (closedSourceFace q branch tau target source X k) := by
  apply (angularMean_smooth q branch X k).continuous.comp
  apply Real.continuousOn_arcosh.comp_continuous
  · apply continuous_const.max
    unfold invariant
    apply Continuous.div <;> try fun_prop
    intro v
    exact mul_ne_zero (Real.cosh_pos target).ne' (Real.cosh_pos source).ne'
  · intro v
    exact Set.mem_Ici.mpr (le_max_left 1 _)

private theorem sourceFace_indicator (q : XiZeroCopy) (branch : Bool)
    (tau target source X k : ℝ) :
    (fun v => if |target - source| ≤ v - tau - source then
      angularMean q branch
        (Real.arcosh (invariant (v - tau - source) target source)) X k else 0) =
      (Ici (tau + source + |target - source|)).indicator
        (closedSourceFace q branch tau target source X k) := by
  funext v
  by_cases hv : tau + source + |target - source| ≤ v
  · rw [Set.indicator_of_mem (Set.mem_Ici.mpr hv)]
    have hcone : |target - source| ≤ v - tau - source := by linarith
    have hz := invariant_causal
      (⟨v - tau - source, target, source, hcone⟩ : CausalPoint)
    simp only [if_pos hcone, closedSourceFace, max_eq_right hz]
  · rw [Set.indicator_of_notMem (fun hmem => hv (Set.mem_Ici.mp hmem))]
    have hcone : ¬|target - source| ≤ v - tau - source := by
      intro h
      apply hv
      linarith
    simp only [if_neg hcone]

private theorem fullDirichlet_source_horizon_aestronglyMeasurable
    (q : XiZeroCopy) (branch : Bool) (tau x y X k : ℝ) :
    AEStronglyMeasurable (fun v =>
      angularDirichletKernel q branch (v - tau - y) x y X k)
      (volume.restrict (Ioi 0)) := by
  have hd : AEStronglyMeasurable
      ((Ici (tau + y + |x - y|)).indicator (closedSourceFace q branch tau x y X k))
      (volume : Measure ℝ) :=
    ((closedSourceFace_continuous q branch tau x y X k).aestronglyMeasurable).indicator
      measurableSet_Ici
  have hi : AEStronglyMeasurable
      ((Ici (tau + y + |(-x) - y|)).indicator (closedSourceFace q branch tau (-x) y X k))
      (volume : Measure ℝ) :=
    ((closedSourceFace_continuous q branch tau (-x) y X k).aestronglyMeasurable).indicator
      measurableSet_Ici
  have he : (fun v => angularDirichletKernel q branch (v - tau - y) x y X k) =
      fun v =>
        ((Ici (tau + y + |x - y|)).indicator
          (closedSourceFace q branch tau x y X k) v -
        (Ici (tau + y + |(-x) - y|)).indicator
          (closedSourceFace q branch tau (-x) y X k) v) / 2 := by
    funext v
    unfold angularDirichletKernel
    have heq : invariant (v - tau - y) (-x) y = invariant (v - tau - y) x (-y) := by
      simp [invariant, Real.sinh_neg, Real.cosh_neg]
    have habs : |(-x) - y| = |x + y| := by
      rw [show -x - y = -(x + y) by ring, abs_neg]
    rw [congrFun (sourceFace_indicator q branch tau x y X k) v, ← habs, ← heq,
      congrFun (sourceFace_indicator q branch tau (-x) y X k) v]
  rw [he]
  simp only [div_eq_mul_inv]
  exact ((hd.sub hi).mul_const (2 : ℂ)⁻¹).restrict

private theorem fullDirichlet_source_horizon_majorant (q : XiZeroCopy) (branch : Bool)
    (tau X k : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧
      IntegrableOn (fun v : ℝ => B * Real.exp
        ((2 * (physicalRate q branch).re + decayExponent q) * v)) (Ioi 0) ∧
      ∀ v x y : ℝ, 0 ≤ v → y ≤ 0 →
        ‖angularDirichletKernel q branch (v - tau - y) x y X k‖ ≤
          B * Real.exp (decayExponent q * v) := by
  obtain ⟨B, hB, hI, hmean⟩ := fullMean_source_horizon_majorant q branch tau X k
  refine ⟨B, hB, hI, ?_⟩
  intro v x y hv hy
  have hface (r : ℝ) :
      ‖if |r - y| ≤ v - tau - y then
        angularMean q branch
          (Real.arcosh (invariant (v - tau - y) r y)) X k else 0‖ ≤
        B * Real.exp (decayExponent q * v) := by
    split_ifs with hcone
    · have hz := invariant_causal
        (⟨v - tau - y, r, y, hcone⟩ : CausalPoint)
      rw [← max_eq_right hz]
      exact hmean v r y hv hy
    · simp only [norm_zero]
      positivity
  have hdirect := hface x
  have himage :
      ‖if |x + y| ≤ v - tau - y then
        angularMean q branch
          (Real.arcosh (invariant (v - tau - y) x (-y))) X k else 0‖ ≤
        B * Real.exp (decayExponent q * v) := by
    have he : invariant (v - tau - y) (-x) y = invariant (v - tau - y) x (-y) := by
      simp [invariant, Real.sinh_neg, Real.cosh_neg]
    have ha : |(-x) - y| = |x + y| := by
      rw [show -x - y = -(x + y) by ring, abs_neg]
    rw [← ha, ← he]
    exact hface (-x)
  unfold angularDirichletKernel
  rw [norm_div, Complex.norm_ofNat]
  calc
    ‖(if |x - y| ≤ v - tau - y then
        angularMean q branch (Real.arcosh (invariant (v - tau - y) x y)) X k else 0) -
        (if |x + y| ≤ v - tau - y then
          angularMean q branch (Real.arcosh (invariant (v - tau - y) x (-y))) X k else 0)‖ / 2 ≤
        (‖if |x - y| ≤ v - tau - y then
          angularMean q branch (Real.arcosh (invariant (v - tau - y) x y)) X k else 0‖ +
          ‖if |x + y| ≤ v - tau - y then
            angularMean q branch (Real.arcosh (invariant (v - tau - y) x (-y))) X k else 0‖) / 2 :=
      div_le_div_of_nonneg_right (norm_sub_le _ _) (by norm_num)
    _ ≤ B * Real.exp (decayExponent q * v) := by
      nlinarith

/-- Uniform absolute admission of the actual full direct-minus-image kernel
against the original onset derivative on every negative source horizon. -/
theorem fullAngularDirichlet_source_horizon_admission (q : XiZeroCopy) (branch : Bool)
    (tau X k : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      IntegrableOn (fun v : ℝ => C * Real.exp
        ((2 * (physicalRate q branch).re + decayExponent q) * v)) (Ioi 0) ∧
      ∀ v x y : ℝ, 0 ≤ v → y ≤ 0 →
        ‖timeOnsetFirst (2 * physicalRate q branch) v *
          angularDirichletKernel q branch (v - tau - y) x y X k‖ ≤
          C * Real.exp ((2 * (physicalRate q branch).re + decayExponent q) * v) := by
  obtain ⟨A, hA, honset⟩ := onsetFirst_majorant q branch
  obtain ⟨B, hB, hI, hkernel⟩ := fullDirichlet_source_horizon_majorant q branch tau X k
  refine ⟨A * B, mul_nonneg hA hB, ?_, ?_⟩
  · exact (hI.const_mul A).congr (Filter.Eventually.of_forall fun v => by ring)
  intro v x y hv hy
  rw [norm_mul]
  calc
    ‖timeOnsetFirst (2 * physicalRate q branch) v‖ *
        ‖angularDirichletKernel q branch (v - tau - y) x y X k‖ ≤
        (A * Real.exp (2 * (physicalRate q branch).re * v)) *
          (B * Real.exp (decayExponent q * v)) :=
      mul_le_mul (honset v) (hkernel v x y hv hy) (norm_nonneg _) (mul_nonneg hA (Real.exp_pos _).le)
    _ = A * B * Real.exp ((2 * (physicalRate q branch).re + decayExponent q) * v) := by
      rw [show (2 * (physicalRate q branch).re + decayExponent q) * v =
        2 * (physicalRate q branch).re * v + decayExponent q * v by ring, Real.exp_add]
      ring

/-- The unmodified full causal kernel before its source-horizon limit is
taken.  This is the literal cap integral whose limit must be `seedCapField`. -/
def fullCausalCapField (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (tau x X k y : ℝ) : ℂ :=
  -2 * seedTraceCoefficient q branch amp *
    ∫ v in Ioi (0 : ℝ), timeOnsetFirst (2 * physicalRate q branch) v *
      angularDirichletKernel q branch (v - tau - y) x y X k

private theorem fullCausalCap_density_measurable (q : XiZeroCopy) (branch : Bool)
    (tau x y X k : ℝ) :
    AEStronglyMeasurable (fun v => timeOnsetFirst (2 * physicalRate q branch) v *
      angularDirichletKernel q branch (v - tau - y) x y X k)
      (volume.restrict (Ioi 0)) := by
  have ho : Continuous (timeOnsetFirst (2 * physicalRate q branch)) :=
    continuous_iff_continuousAt.mpr
      (fun v => (timeOnsetFirst_hasDerivAt _ v).continuousAt)
  exact (ho.aestronglyMeasurable.restrict.mul
    (fullDirichlet_source_horizon_aestronglyMeasurable q branch tau x y X k))

/-- Literal causal-cap realization: integrating the actual full
direct-minus-image kernel and sending its source to the horizon gives exactly
the independently specified `seedCapField`.  This discharges the cap-value
limit; strong weak-wave transport and the QNM contact comparison remain. -/
theorem fullCausalCapField_source_horizon_tendsto (q : XiZeroCopy) (branch : Bool)
    (amp : ℂ) (tau x X k : ℝ) :
    Tendsto (fun y => fullCausalCapField q branch amp tau x X k y) atBot
      (𝓝 (seedCapField q branch amp tau x X k)) := by
  obtain ⟨C, hC, hI, hbound⟩ :=
    fullAngularDirichlet_source_horizon_admission q branch tau X k
  have hdom : ∀ᶠ y : ℝ in atBot, ∀ᵐ v : ℝ ∂(volume.restrict (Ioi 0)),
      ‖timeOnsetFirst (2 * physicalRate q branch) v *
        angularDirichletKernel q branch (v - tau - y) x y X k‖ ≤
        C * Real.exp ((2 * (physicalRate q branch).re + decayExponent q) * v) :=
    (eventually_le_atBot 0).mono fun y hy =>
      (ae_restrict_mem measurableSet_Ioi).mono fun v hv => hbound v x y hv.le hy
  have hpoint (v : ℝ) :
      Tendsto (fun y => timeOnsetFirst (2 * physicalRate q branch) v *
        angularDirichletKernel q branch (v - tau - y) x y X k) atBot
        (𝓝 (timeOnsetFirst (2 * physicalRate q branch) v *
          horizonKernel q branch tau x v X k)) :=
    (tendsto_const_nhds.mul
      (fullAngularDirichletKernel_source_horizon q branch tau x v X k))
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (fun v => C * Real.exp ((2 * (physicalRate q branch).re + decayExponent q) * v))
    (Filter.Eventually.of_forall
      (fun y => fullCausalCap_density_measurable q branch tau x y X k))
    hdom hI (Filter.Eventually.of_forall hpoint)
  change Tendsto (fun y => -2 * seedTraceCoefficient q branch amp *
      ∫ v in Ioi (0 : ℝ), timeOnsetFirst (2 * physicalRate q branch) v *
        angularDirichletKernel q branch (v - tau - y) x y X k) atBot _
  simpa only [seedCapField] using h.const_mul (-2 * seedTraceCoefficient q branch amp)

end

end RHTower.D4BMFullAngularSourceHorizonAdmission
