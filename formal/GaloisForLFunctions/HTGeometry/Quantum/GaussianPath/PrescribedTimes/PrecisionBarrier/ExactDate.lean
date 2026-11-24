import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.LateScalarProbability
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.FirstWaitLaw
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ExactContacts.PhysicalOrbit

/-! # Exponential exact circuit cost at a prescribed nonzero delay -/
open Set Filter MeasureTheory ProbabilityTheory
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.PrecisionBarrier
open ResonantDraws
noncomputable section

private theorem finite_window_preimage {A : Set ℝ} (h : ∀ a b, (Icc a b ∩ A).Finite)
    (o : ℝ) {t : ℝ} (ht : t≠0) :
    (((fun a : ℝ => o+a*t) ⁻¹' A) ∩ Icc 1 2).Finite := by
  let f (a : ℝ) := o+a*t
  have hi : Function.Injective f := fun a b he =>
    mul_right_cancel₀ ht (add_left_cancel (show o+a*t=o+b*t from he))
  apply ((h (o-2*|t|) (o+2*|t|)).preimage hi.injOn).subset
  rintro a ⟨ha,hw⟩
  have hh : |a*t|≤2*|t| := by
    rw [abs_mul,abs_of_nonneg (zero_le_one.trans hw.1)]
    exact mul_le_mul_of_nonneg_right hw.2 (abs_nonneg t)
  exact ⟨⟨by dsimp [f]; linarith only [(abs_le.mp hh).1],
    by dsimp [f]; linarith only [(abs_le.mp hh).2]⟩,ha⟩

/-- Along a covariantly chosen origin, every prescribed nonzero delay
has zero disorder probability of an exact circuit below the dimension
threshold. A locally finite set of time contacts has zero ray mass. -/
theorem exact_delay_null (k s : ℕ) (hs : 16*s<2^(k+3)-1) {t : ℝ} (ht : t≠0)
    (o : (PrefixIndex (k+1) → ℝ) → ℝ) (ho : Measurable o)
    (hc : ∀ a > (0:ℝ), ∀ x, a*o (a • x)=o x) :
    let μ := Measure.pi fun _ : PrefixIndex (k+1) => gaussianReal 0 1
    μ.real {x | pathGateDistance (k+1) s x (o x+t)≤0}=0 := by
  intro μ
  let n := k+1
  let X := fun ω i => pathPauliDisorderShell ω n (pathCoeffEquiv n i)
  let E := {x | pathGateDistance n s x (o x+t)≤0}
  have hm : MeasurableSet E := measurable_origin_event n s 0 t o ho
  have hh : ∀ᵐ ω ∂pathPauliDisorderLaw, rayMass 2 E (X ω)=0 := by
    filter_upwards [ExactContacts.gaussian_finite_exact_circuit_dates] with ω hω
    let u := pathPauliDisorderShell ω n
    let x := X ω
    let A := {z | HasProjectiveCircuitApproximation (k+3) 0 s (unitaryEvolution (pathHamiltonian u) z)}
    have hA (a b : ℝ) : (Icc a b ∩ A).Finite := hω k s hs a b
    have hg : numberedGenerator n x=pathHamiltonian u := numberedGenerator_shell u
    have hset : (fun a : ℝ => a*t) ⁻¹' {v | pathGateDistance n s x (o x+v)≤0}
        = (fun a : ℝ => o x+a*t) ⁻¹' A := by
      ext a
      change pathGateDistance n s x (o x+a*t)≤0 ↔
        HasProjectiveCircuitApproximation (k+3) 0 s (unitaryEvolution (pathHamiltonian u) (o x+a*t))
      rw [pathGateDistance,hg,hasProjectiveCircuitApproximation_iff_infDist]
    change rayMass 2 {y | pathGateDistance n s y (o y+t)≤0} x=0
    rw [rayMass_of_covariant_origin n s o hc x 2 t 0,hset,measureReal_restrict_apply' measurableSet_Icc]
    exact congrArg ENNReal.toReal ((finite_window_preimage hA (o x) ht).measure_zero volume)
  have hmap := gaussian_pauli_prefix_coordinates_law n
  have hi : (∫ x, rayMass 2 E x ∂μ)=0 := by
    change (∫ x, rayMass 2 E x ∂(centredProductGaussian _ 1))=0
    rw [←hmap.map_eq,integral_map hmap.measurable.aemeasurable (measurable_rayMass 2 hm).aestronglyMeasurable]
    exact integral_eq_zero_of_ae hh
  apply le_antisymm _ measureReal_nonneg
  exact (snapshot_le_dyadic_mean E hm).trans_eq (by rw [hi,mul_zero])

/-- The same exponential exact gate floor holds at the laboratory date,
at a delay from the first crossing and at a delay from its first return. -/
theorem gaussian_exact_prescribed_delays (k j r s : ℕ) (hs : 16*s<2^(k+3)-1) {t : ℝ} (ht : t≠0) :
    let n := k+1
    let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
    let σ := crossingOrigin n j (9/80)
    let Δ := crossingWait n j r
    μ.real {x | pathGateDistance n s x t≤0}=0 ∧
    μ.real {x | pathGateDistance n s x (σ x+t)≤0}=0 ∧
    μ.real {x | pathGateDistance n s x ((σ x+Δ x)+t)≤0}=0 := by
  intro n μ σ Δ
  have hσ (a : ℝ) (ha : 0<a) (x : PrefixIndex n → ℝ) : a*σ (a • x)=σ x :=
    smul_crossingOrigin n j (9/80) ha x
  constructor
  · simpa only [zero_add] using
      exact_delay_null k s hs ht (fun _ => 0) measurable_const (fun _ _ _ => mul_zero _)
  refine ⟨exact_delay_null k s hs ht σ (measurable_crossingOrigin ..) hσ,?_⟩
  exact exact_delay_null k s hs ht (fun x => σ x+Δ x)
    ((measurable_crossingOrigin ..).add (measurable_crossingWait ..))
    (fun a ha x => by rw [mul_add,hσ a ha x,smul_crossingWait n j r ha x])

#print axioms gaussian_exact_prescribed_delays
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.PrecisionBarrier
