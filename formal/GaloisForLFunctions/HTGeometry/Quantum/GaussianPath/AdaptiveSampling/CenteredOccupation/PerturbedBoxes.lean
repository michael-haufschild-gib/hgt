import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.CenteredOccupation.TransverseSegment
import Mathlib.MeasureTheory.Group.AddCircle

/-! # Haar box volume retained after a bounded transverse perturbation -/

open Filter Set Metric MeasureTheory Real Topology
namespace GaloisForLFunctions.HTGeometry.AdaptiveSampling.CenteredOccupation
noncomputable section
variable {I : Type} [Fintype I]

/-- Open coordinate box with specified centers and side lengths in turns. -/
def arcBox (c : UnitAddTorus I) (y : I → ℝ) : Set (UnitAddTorus I) :=
  Set.univ.pi fun i => ball (c i) (y i/2)

theorem isOpen_arcBox (c : UnitAddTorus I) (y : I → ℝ) : IsOpen (arcBox c y) :=
  isOpen_set_pi finite_univ fun _ _ => isOpen_ball

theorem volume_arcBox (c : UnitAddTorus I) (y : I → ℝ) (hy : ∀ i, y i≤1) :
    volume (arcBox c y)=∏ i, ENNReal.ofReal (y i) := by
  rw [arcBox,volume_pi_pi]
  apply Finset.prod_congr rfl
  intro i _
  rw [←measure_congr AddCircle.closedBall_ae_eq_ball,AddCircle.volume_closedBall,
    show 2*(y i/2)=y i by ring,min_eq_right (hy i)]

private theorem clock_supported {A : ℝ} (hA : 0≤A) :
    ∀ᵐ t ∂(centeredUniformClockProbabilityMeasure A : Measure ℝ), |t|≤A := by
  rw [centeredUniformClockProbabilityMeasure,ProbabilityMeasure.toMeasure_map]
  apply (ae_map_iff (by fun_prop) (measurableSet_le measurable_id.abs measurable_const)).mpr
  change ∀ᵐ u ∂volume.restrict (Ioc (0:ℝ) 1), |A*(2*u-1)|≤A
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  rw [abs_mul,abs_of_nonneg hA]
  have hu' : |2*u-1|≤1 := abs_le.mpr ⟨by linarith only [hu.1],by linarith only [hu.2]⟩
  exact (mul_le_mul_of_nonneg_left hu' hA).trans_eq (mul_one A)

theorem transverse_supported (v : I → ℝ) {B : ℝ} (hB : 0<B) :
    ∀ᵐ z ∂(transverseLaw v B : Measure _), ∀ i, ‖z i‖≤|v i|/(2*B) := by
  rw [transverseLaw,finiteClockSampledPhaseProbabilityMeasure,ProbabilityMeasure.toMeasure_map]
  have hm : MeasurableSet {z : UnitAddTorus I | ∀ i, ‖z i‖≤|v i|/(2*B)} :=
    measurableSet_setOf_forall fun i => measurableSet_le (measurable_pi_apply i).norm measurable_const
  apply (ae_map_iff (finiteClockPhasePoint_continuous v).aemeasurable hm).mpr
  filter_upwards [clock_supported (div_nonneg pi_pos.le hB.le)] with t ht i
  apply (show ‖finiteClockPhasePoint v t i‖≤‖t*v i/(2*π)‖ from QuotientAddGroup.norm_mk_le_norm).trans
  rw [Real.norm_eq_abs,abs_div,abs_mul,abs_of_pos (by positivity : 0<2*π)]
  calc
    _ ≤ (π/B*|v i|)/(2*π) := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ht (abs_nonneg _)) (by positivity)
    _ = _ := by field_simp [pi_ne_zero,hB.ne']

/-- If the perturbed box has a narrower side on each displaced axis,
its Haar volume bounds the lower occupation of the original box. -/
theorem box_liminf (ω : I → ℝ) (a τ : ℝ) (v : I → ℝ) {B : ℝ} (hB : 0<B)
    (hc : Tendsto (perturbedLaw ω a τ v B) atTop (𝓝 (finiteTorusHaarProbabilityMeasure I)))
    (c : UnitAddTorus I) (y w : I → ℝ) (hw : ∀ i, w i≤1) (hs : ∀ i, w i+|v i|/B≤y i) :
    ∏ i, ENNReal.ofReal (w i) ≤ atTop.liminf (fun N =>
      (integerClockPrefixLaw (fun n => finiteClockPhasePoint ω (a+(n:ℝ)*τ)) N : Measure _) (arcBox c y)) := by
  let ν N := integerClockPrefixLaw (fun n => finiteClockPhasePoint ω (a+(n:ℝ)*τ)) N
  have hl := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hc (isOpen_arcBox c w)
  rw [finiteTorusHaarProbabilityMeasure_toMeasure_eq_volume,volume_arcBox c w hw] at hl
  apply hl.trans (Filter.liminf_le_liminf (Eventually.of_forall fun N => ?_))
  let λ' : Measure (UnitAddTorus I) := transverseLaw v B
  let μ : Measure (UnitAddTorus I) := ν N
  change (μ ∗ λ') (arcBox c w)≤μ (arcBox c y)
  rw [Measure.conv,Measure.map_apply measurable_add (isOpen_arcBox c w).measurableSet]
  have hsub : (fun p : UnitAddTorus I × UnitAddTorus I => p.1+p.2) ⁻¹' arcBox c w
      ≤ᵐ[μ.prod λ'] (arcBox c y) ×ˢ Set.univ := by
    filter_upwards [(Measure.quasiMeasurePreserving_snd (μ:=μ) (ν:=λ')).ae (transverse_supported v hB)] with p hp
    intro he
    refine ⟨fun i _ => ?_,mem_univ _⟩
    have hi : dist (p.1 i+p.2 i) (c i)<w i/2 := he i (mem_univ i)
    change dist (p.1 i) (c i)<y i/2
    have hd := dist_triangle (p.1 i) (p.1 i+p.2 i) (c i)
    have hstep : dist (p.1 i) (p.1 i+p.2 i)=‖p.2 i‖ := by
      rw [dist_eq_norm,show p.1 i-(p.1 i+p.2 i)= -p.2 i by abel,norm_neg]
    rw [hstep] at hd
    have hw' : |v i|/(2*B)=|v i|/B/2 := by ring
    have hnorm := hp i
    rw [hw'] at hnorm
    linarith only [hd,hi,hnorm,hs i]
  exact (measure_mono_ae hsub).trans_eq (by rw [Measure.prod_prod,measure_univ,mul_one])

end
end GaloisForLFunctions.HTGeometry.AdaptiveSampling.CenteredOccupation
