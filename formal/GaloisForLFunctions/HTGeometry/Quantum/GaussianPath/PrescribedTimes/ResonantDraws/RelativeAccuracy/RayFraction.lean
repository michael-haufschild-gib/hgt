import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.LateScalarProbability
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.FiniteRecords.ScalarError

/-! # Exact finite-window formula for a probability along a coupling ray -/
open Set MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.RelativeAccuracy
noncomputable section
open SharpOccupation

/-- A normalized dilation interval is exactly one finite physical record.
The origin may be any clock homogeneous of degree minus one. -/
theorem ray_fraction (k s : ℕ) (ω : PathPauliDisorder) (ε : ℝ) {b t : ℝ} (hb : 1<b) (ht : 0<t)
    (o : (PrefixIndex (k+1) → ℝ) → ℝ) (hcov : ∀ a > (0:ℝ), ∀ x, a*o (a • x)=o x) :
    let N := k+3
    let u := pathPauliDisorderShell ω (k+1)
    let x := fun i => u (pathCoeffEquiv (k+1) i)
    let H : selfAdjoint (Register N) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
    rayMass b {y | pathGateDistance (k+1) s y (o y+t)≤ε} x/(b-1) =
      visitFraction H s ε (o x+t) (o x+t+(b-1)*t) := by
  intro N u x H
  let V := visitSet H s ε
  let J := Icc (o x+t) (o x+t+(b-1)*t)
  have hgen : numberedGenerator (k+1) x=H.val := numberedGenerator_shell u
  have hM : MeasurableSet V := by
    have he : V=(orbitCircuitDistance H s) ⁻¹' Iic ε := Set.ext fun _ => hasProjectiveCircuitApproximation_iff_infDist ..
    rw [he]
    exact measurableSet_Iic.preimage (orbitCircuitDistance_lipschitz H s).continuous.measurable
  have he : {v | pathGateDistance (k+1) s x (o x+v)≤ε} ∩ Icc t (b*t) =
      (fun v => v+o x) ⁻¹' (V ∩ J) := by
    ext v
    change (pathGateDistance (k+1) s x (o x+v)≤ε ∧ t≤v ∧ v≤b*t) ↔
      (HasProjectiveCircuitApproximation N ε s (unitaryEvolution H.val (v+o x)) ∧
      o x+t≤v+o x ∧ v+o x≤o x+t+(b-1)*t)
    rw [hasProjectiveCircuitApproximation_iff_infDist,pathGateDistance,hgen,add_comm v]
    exact and_congr_right' (and_congr (by constructor <;> intro h <;> linarith only [h])
      (by constructor <;> intro h <;> linarith only [h]))
  have hv : volume ((fun v : ℝ => v+o x) ⁻¹' (V ∩ J)) = volume (V ∩ J) :=
    (measurePreserving_add_right volume (o x)).measure_preimage (hM.inter measurableSet_Icc).nullMeasurableSet
  rw [rayMass_of_covariant_origin _ _ _ hcov,dilation_interval_volume _ _ _ ht,one_mul,he,
    Measure.real,hv,visitFraction,add_sub_cancel_left]
  change t⁻¹*volume.real (V ∩ J)/(b-1) = volume.real (V ∩ J)/((b-1)*t)
  field_simp [(sub_pos.mpr hb).ne',ht.ne']

#print axioms ray_fraction
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.RelativeAccuracy
