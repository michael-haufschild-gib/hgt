import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.PhysicalTimes.Eigenphases
import GaloisForLFunctions.HTGeometry.HaarRankEntropyFormation
import Mathlib.MeasureTheory.Measure.Portmanteau

/-! # Eigenphase counts at fixed angular thresholds -/
open MeasureTheory Set Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.PhysicalTimes
noncomputable section

private abbrev period := 2*Real.pi
private abbrev Angles := AddCircle period

/-- Choose the positive angular representative, measured in turns. -/
def turns (z : Angles) := ((AddCircle.equivIoc period 0 z):ℝ)/period

theorem turns_mem (z : Angles) : turns z∈Ioc (0:ℝ) 1 := by
  have h := (AddCircle.equivIoc period 0 z).property
  exact ⟨div_pos h.1 (by positivity), (div_le_one (by positivity)).mpr (by simpa only [zero_add] using h.2)⟩

private theorem measurable_turns : Measurable turns :=
  (measurable_subtype_coe.comp (AddCircle.measurableEquivIoc period 0).measurable).div_const _

private def below (a : ℝ) := {z : Angles | turns z<a}

/-- Positive representative of the eigenphase attached to one physical eigenline. -/
def physicalTurns {n : ℕ} (u : PathShell n) (t : ℝ) (j : Fin (n+2)→Bool) :=
  turns (_root_.RHTower.PrimeCirclePeriodization.phase (-t) ((isSelfAdjoint_pathHamiltonian u).isHermitian.eigenvalues j))

theorem angular_fraction {n : ℕ} (u : PathShell n) (t b : ℝ) :
    (eigenphaseLaw u t : Measure Angles).real {z | turns z<b} =
      ((Finset.univ.filter (fun j => physicalTurns u t j<b)).card:ℝ)/(2:ℝ)^(n+2) := by
  classical
  let f (j : Fin (n+2)→Bool) := _root_.RHTower.PrimeCirclePeriodization.phase (-t)
    ((isSelfAdjoint_pathHamiltonian u).isHermitian.eigenvalues j)
  let S := f ⁻¹' {z | turns z<b}
  have hs : MeasurableSet S := (measurable_of_finite f) (measurableSet_lt measurable_turns measurable_const)
  rw [measureReal_def,eigenphaseLaw,ProbabilityMeasure.toMeasure_map,
    Measure.map_apply_of_aemeasurable (measurable_of_finite _).aemeasurable (measurableSet_lt measurable_turns measurable_const)]
  change ((PMF.uniformOfFintype _).toMeasure S).toReal=_
  rw [PMF.toMeasure_uniformOfFintype_apply _ hs,ENNReal.toReal_div,ENNReal.toReal_natCast,ENNReal.toReal_natCast]
  simp [Fintype.card_subtype,S,f,physicalTurns]

private theorem null_frontier_below (a : ℝ) :
    (uniformAngles : Measure Angles) (frontier (below a))=0 := by
  let p := period
  have hp : 0<p := by dsimp only [p,period]; positivity
  have hs : frontier (below a) ⊆ ({(0:Angles),((a*p:ℝ):Angles)} : Set Angles) := by
    intro z hz
    by_contra h
    have hz₀ : z≠0 := fun h₀ => h (Or.inl h₀)
    have hza : turns z≠a := by
      intro he
      have hval := (div_eq_iff hp.ne').mp he
      apply h (Or.inr ?_)
      exact (AddCircle.coe_equivIoc (p:=period) (a:=0) (y:=z)).symm.trans (congrArg (fun x : ℝ => (x:Angles)) hval)
    have hc : ContinuousAt turns z := (continuous_subtype_val.continuousAt.comp
      (AddCircle.continuousAt_equivIoc period 0 (by simpa using hz₀))).div_const _
    rcases lt_or_gt_of_ne hza with hlt|hgt
    · exact hz.2 (mem_interior_iff_mem_nhds.mpr (hc.tendsto.eventually_lt_const hlt))
    · have hneg : (below a)ᶜ∈𝓝 z := (hc.tendsto.eventually_const_lt hgt).mono fun _ h => h.not_gt
      exact (mem_closure_iff_nhds.mp hz.1 _ hneg).ne_empty (by simp)
  letI : NullSingletonClass (uniformAngles : Measure Angles) := ⟨fun z => haarAddCircle_singleton z⟩
  exact measure_mono_null hs (((finite_singleton _).insert _).measure_zero _)

private theorem uniform_below {a : ℝ} (ha : a∈Icc (0:ℝ) 1) :
    (uniformAngles : Measure Angles).real (below a)=a := by
  let p := period
  have hp : 0<p := by dsimp only [p,period]; positivity
  have hval := (measurePreserving_subtype_coe (μa:=(volume : Measure ℝ))
    (measurableSet_Ioc (a:=(0:ℝ)) (b:=0+p))).comp (AddCircle.measurePreserving_equivIoc p (a:=0))
  have he : Iio (a*p) ∩ Ioc 0 (0+p)=Ioo 0 (a*p) := by
    ext x
    constructor
    · rintro ⟨h₁,h₂,h₃⟩; exact ⟨h₂,h₁⟩
    · rintro ⟨h₁,h₂⟩
      exact ⟨h₂,h₁,by rw [zero_add]; exact h₂.le.trans ((mul_le_mul_of_nonneg_right ha.2 hp.le).trans_eq (one_mul p))⟩
  have hpre : below a=(fun z : Angles => ((AddCircle.equivIoc p 0 z):ℝ)) ⁻¹' Iio (a*p) := by
    ext z
    exact div_lt_iff₀ hp
  have hv : (volume : Measure Angles) (below a)=ENNReal.ofReal (a*p) := by
    rw [hpre]
    calc _ = (volume.restrict (Ioc 0 (0+p))) (Iio (a*p)) :=
           hval.measure_preimage measurableSet_Iio.nullMeasurableSet
         _ = _ := by rw [Measure.restrict_apply measurableSet_Iio,he,Real.volume_Ioo,sub_zero]
  rw [AddCircle.volume_eq_smul_haarAddCircle,Measure.smul_apply,smul_eq_mul] at hv
  have hreal := congrArg ENNReal.toReal hv
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal hp.le,ENNReal.toReal_ofReal (mul_nonneg ha.1 hp.le)] at hreal
  change (AddCircle.haarAddCircle (T:=p) (below a)).toReal=a
  exact mul_left_cancel₀ hp.ne' (hreal.trans (mul_comm a p))

/-- Each angular threshold is a continuity set of circle Haar probability. -/
theorem angular_count_of_haar (μ : ℕ → ProbabilityMeasure Angles)
    (hμ : Tendsto μ atTop (𝓝 uniformAngles)) {b : ℝ} (hb : b∈Icc (0:ℝ) 1) :
    Tendsto (fun n => (μ n : Measure Angles).real {z | turns z<b}) atTop (𝓝 b) := by
  have h := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hμ (null_frontier_below b)
  have hfin : (uniformAngles : Measure Angles) (below b)≠⊤ := measure_ne_top _ _
  have hr := (ENNReal.continuousAt_toReal hfin).tendsto.comp h
  change Tendsto (fun n => (μ n : Measure Angles).real
    (below b)) atTop (𝓝 ((uniformAngles : Measure Angles).real (below b))) at hr
  rw [uniform_below hb] at hr
  exact hr

/-- For every observation sequence in a compact positive interval, the
fraction of eigenphases strictly below a turns tends to a. All thresholds
and all draw-dependent observation sequences share the same event. -/
theorem gaussian_angular_counts :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ a T : ℝ, 0<a → ∀ t : ℕ→ℝ,
      (∀ᶠ n in atTop, t n∈Icc a T) → ∀ b∈Icc (0:ℝ) 1,
      Tendsto (fun n => (eigenphaseLaw (pathPauliDisorderShell ω n) (t n) : Measure Angles).real
        {z | turns z<b}) atTop (𝓝 b) := by
  filter_upwards [gaussian_eigenphase_haar] with ω hω
  intro a T ha t ht b hb
  exact angular_count_of_haar _ (hω a T ha t ht) hb

#print axioms gaussian_angular_counts
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.PhysicalTimes
