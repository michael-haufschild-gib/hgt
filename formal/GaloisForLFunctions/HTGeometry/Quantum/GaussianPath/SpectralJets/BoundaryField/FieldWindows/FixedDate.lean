import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.FieldWindows.CharacterEstimate
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.ProjectiveSlopes
import GaloisForLFunctions.HTGeometry.OneSidedCaptureDensity

/-! # Phase distribution at a fixed laboratory date under shrinking field uncertainty -/
open Filter Topology MeasureTheory Set
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.FieldWindows
noncomputable section
variable {I : Type} [Fintype I]

private def fieldPoint (f : ℝ→I→ℝ) (b w T s : ℝ) :=
  finiteClockPhasePoint (f (b+w*s)) T

private theorem continuous_fieldPoint (f : ℝ→I→ℝ) (hf : ∀ i, Continuous (fun z => f z i))
    (b w T : ℝ) : Continuous (fieldPoint f b w T) := by
  apply continuous_pi
  intro i
  apply (AddCircle.continuous_mk' (1:ℝ)).comp
  exact ((continuous_const.mul ((hf i).comp (continuous_const.add (continuous_const.mul continuous_id)))).div_const _)

/-- Sample the field uniformly in [b,b+w] and observe every sample at the same time T. -/
def fieldWindowLaw (f : ℝ→I→ℝ) (hf : ∀ i, Continuous (fun z => f z i)) (b w T : ℝ) :
    ProbabilityMeasure (UnitAddTorus I) :=
  unitIntervalProbabilityMeasure.map (continuous_fieldPoint f hf b w T).aemeasurable

/-- Probability of a target written in the original uniform field coordinate. -/
theorem fieldWindowLaw_real (f : ℝ→I→ℝ) (hf : ∀ i, Continuous (fun z => f z i))
    (b w T : ℝ) {A : Set (UnitAddTorus I)} (hA : MeasurableSet A) :
    (fieldWindowLaw f hf b w T : Measure _).real A =
      (unitIntervalProbabilityMeasure : Measure ℝ).real
        {s | finiteClockPhasePoint (f (b+w*s)) T∈A} := by
  rw [fieldWindowLaw,Measure.real,ProbabilityMeasure.toMeasure_map,
    Measure.map_apply (continuous_fieldPoint f hf b w T).measurable hA]
  rfl

private theorem field_character (f : ℝ→I→ℝ) (hf : ∀ i, Continuous (fun z => f z i))
    (b w T : ℝ) (m : I→ℤ) :
    (∫ x, UnitAddTorus.mFourier m x ∂(fieldWindowLaw f hf b w T : Measure _)) =
      ∫ s in (0:ℝ)..1, Complex.exp (Complex.I*((T*finiteTorusCharacterDetuning m (f (b+w*s)):ℝ):ℂ)) := by
  rw [fieldWindowLaw,ProbabilityMeasure.toMeasure_map,integral_map (continuous_fieldPoint f hf b w T).aemeasurable
    (UnitAddTorus.mFourier m).continuous.aestronglyMeasurable]
  change (∫ s in Ioc (0:ℝ) 1, UnitAddTorus.mFourier m (finiteClockPhasePoint (f (b+w*s)) T))=_
  rw [←intervalIntegral.integral_of_le zero_le_one]
  apply intervalIntegral.integral_congr
  intro s _
  change UnitAddTorus.mFourier m (finiteClockPhasePoint (f (b+w*s)) T)=_
  rw [mFourier_finiteClockPhasePoint,mul_comm _ Complex.I]

/-- The width of the uncertainty may vanish. Only its product with the
laboratory date needs to diverge when every character has nonzero slope. -/
private theorem fixed_date_law (f : ℝ→I→ℝ) (hf : ∀ i, Continuous (fun z => f z i)) {b : ℝ}
    (ha : ∀ i, AnalyticAt ℝ (fun z => f z i) b)
    (hv : RationallyIndependentFrequency (fun i => deriv (fun z => f z i) b))
    {w T : ℕ→ℝ} (hw : Tendsto w atTop (𝓝 0)) (hp : ∀ᶠ n in atTop, 0<w n)
    (hTw : Tendsto (fun n => T n*w n) atTop atTop) :
    Tendsto (fun n => fieldWindowLaw f hf b (w n) (T n)) atTop (𝓝 (finiteTorusHaarProbabilityMeasure I)) := by
  classical
  apply probabilityMeasure_tendsto_of_mFourier_integral_tendsto
  intro m
  rw [finiteTorusHaarProbabilityMeasure_mFourier_integral]
  by_cases hm : m=0
  · subst m
    simp [UnitAddTorus.mFourier_zero]
  rw [if_neg hm]
  simp_rw [field_character]
  let a (z : ℝ) := finiteTorusCharacterDetuning m (f z)
  have haa : AnalyticAt ℝ a b := Finset.analyticAt_fun_sum _ fun i _ => analyticAt_const.mul (ha i)
  have hd : HasDerivAt a (finiteTorusCharacterDetuning m (fun i => deriv (fun z => f z i) b)) b :=
    HasDerivAt.fun_sum fun i _ => (ha i).differentiableAt.hasDerivAt.const_mul (m i:ℝ)
  exact shrinking_field_character haa (fun h => hm (hv m (hd.deriv.symm.trans h))) hw hp hTw

/-- For almost every background, at all but countably many terminal baselines
on every prefix, the fixed-date phase law becomes Haar even when the width of
the single uncertain coefficient tends to zero, provided Tw tends to infinity. -/
theorem gaussian_boundary_fixed_date_haar :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, ∃ B : Set ℝ, B.Countable ∧ ∀ b ∉ B,
      let E := orderedBoundaryEnergy ω k
      ∀ r : Fin (k+3)→Bool, let f := fun z => projectiveFrequency (fun i => -E z i) r
      ∃ hf : ∀ i, Continuous (fun z => f z i), ∀ w T : ℕ→ℝ, Tendsto w atTop (𝓝 0) →
        (∀ᶠ n in atTop, 0<w n) → Tendsto (fun n => T n*w n) atTop atTop →
        Tendsto (fun n => fieldWindowLaw f hf b (w n) (T n)) atTop (𝓝 (finiteTorusHaarProbabilityMeasure _)) := by
  filter_upwards [gaussian_boundary_projective_slopes] with ω hω
  intro k
  obtain ⟨B,hB,h⟩ := hω k
  refine ⟨B,hB,?_⟩
  intro b hb E r f
  obtain ⟨_,ha,hv⟩ := h b hb
  have hf (i : {i // i≠r}) : Continuous (fun z => f z i) :=
    (continuous_orderedBoundaryEnergy ω k i.val).neg.sub (continuous_orderedBoundaryEnergy ω k r).neg
  refine ⟨hf,fun w T hw hp hT => fixed_date_law f hf
    (fun i => (ha i.val).neg.sub (ha r).neg) ?_ hw hp hT⟩
  let v := fun i => deriv (fun z => E z i) b
  have he (i : {i // i≠r}) : deriv (fun z => f z i) b=projectiveFrequency (fun i => -v i) r i :=
    ((ha i.val).differentiableAt.hasDerivAt.neg.sub (ha r).differentiableAt.hasDerivAt.neg).deriv
  rw [funext he]
  exact maximallyProjectiveEnergy_projectiveFrequency_independent _ (maximallyProjectiveEnergy_neg hv) r

#print axioms gaussian_boundary_fixed_date_haar
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.FieldWindows
