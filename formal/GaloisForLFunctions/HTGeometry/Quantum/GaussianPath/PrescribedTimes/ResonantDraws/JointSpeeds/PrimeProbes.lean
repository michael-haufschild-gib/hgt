import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.JointSpeeds.FirstExcursionLaw
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.JointSpeeds.MaximumCDF
import GaloisForLFunctions.HTGeometry.PolynomialPhaseAperture

/-! # Recovering the actual maximum distribution from sparse late observations -/
open Set Filter MeasureTheory ProbabilityTheory Topology
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.JointSpeeds
open ResonantDraws
noncomputable section
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩

/-- Check the register at delays t log p after the original first
crossing or its first return. For q distinct primes the late probability
of q affordable observations tends to the qth Haar-fraction moment.
As q increases these moments recover the same-error orbit maximum CDF. -/
theorem prime_probes_recover_maximum (k r s : ℕ) (ε : ℝ) (afterReturn : Bool)
    (B : Set (PrefixIndex (k+1)→ℝ)) (hB : MeasurableSet B) :
    let n := k+1
    let P := nearHilbertContinuousCircuitBudget (k+3)
    let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
    let σ := crossingOrigin n P (9/80)
    let o := fun x => if afterReturn then σ x+crossingWait n P r x else σ x
    ∃ L : ℕ→ℝ, (∀ S : Finset Nat.Primes, Tendsto (fun t => μ.real
      (B ∩ {x | ∀ p : S, pathGateDistance n s x (o x+Real.log ((p.val:ℕ):ℝ)*t)≤ε}))
        atTop (𝓝 (L S.card))) ∧ Tendsto L atTop (𝓝 (μ.real (B ∩ orbitBudget n s ε))) := by
  classical
  intro n P μ σ o
  let X := fun (ω : PathPauliDisorder) i => pathPauliDisorderShell ω n (pathCoeffEquiv n i)
  let W := affordablePhaseMass k s ε
  let ν := pathPauliDisorderLaw.restrict (X ⁻¹' B)
  let D := X ⁻¹' orbitBudget n s ε
  have hX : MeasurePreserving X pathPauliDisorderLaw μ := gaussian_pauli_prefix_coordinates_law n
  letI : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
  let L (q : ℕ) := ∫ ω, W ω^q ∂ν
  refine ⟨L,?_,?_⟩
  · intro S
    let c (p : S) := Real.log ((p.val:ℕ):ℝ)
    have hc : RationallyIndependentFrequency c := rationallyIndependentFrequency_of_linearIndependent_int
      (GaloisForLFunctions.logPrime_linearIndependent_int.comp Subtype.val Subtype.val_injective)
    have h := joint_first_excursion_snapshot k P c hc (fun _ => afterReturn) (fun _ => true)
      (fun _ => r) (fun _ => s) (fun _ => ε) B hB
    simpa only [iff_true,if_true,Finset.prod_const,Finset.card_univ,Fintype.card_coe] using h
  have hD := (isClosed_orbitBudget n s ε).measurableSet.preimage hX.measurable
  have hw := (integrable_affordablePhaseMass k s ε).integrableOn (s:=X ⁻¹' B)
  have hbd (ω) : 0≤W ω ∧ W ω≤1 := ⟨measureReal_nonneg,measureReal_le_one⟩
  let f := D.indicator (fun _ => (1:ℝ))
  have hlim : ∀ᵐ ω ∂ν, Tendsto (fun q : ℕ => W ω^q) atTop (𝓝 (f ω)) := by
    filter_upwards [ae_restrict_of_ae (s:=X ⁻¹' B) (unit_fraction_iff_orbitBudget k s ε)] with ω hh
    by_cases hω : ω∈D
    · rw [show f ω=1 from indicator_of_mem hω _,show W ω=1 from hh.mpr hω]
      simp
    · rw [show f ω=0 from indicator_of_notMem hω _]
      exact tendsto_pow_atTop_nhds_zero_of_lt_one (hbd ω).1 (lt_of_le_of_ne (hbd ω).2 (fun he => hω (hh.mp he)))
  have ht := tendsto_integral_filter_of_dominated_convergence (μ:=ν)
    (F:=fun (q : ℕ) ω => W ω^q) (f:=f) (fun _ => (1:ℝ))
    (Eventually.of_forall fun q => hw.aestronglyMeasurable.pow q)
    (Eventually.of_forall fun q => ae_of_all _ fun ω =>
      (by rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (hbd ω).1 q)]; exact pow_le_one₀ (hbd ω).1 (hbd ω).2))
    (integrable_const _) hlim
  have hev : (∫ ω, f ω ∂ν)=μ.real (B ∩ orbitBudget n s ε) := by
    rw [show (∫ ω, f ω ∂ν)=ν.real D from integral_indicator_one hD,
      show ν.real D=pathPauliDisorderLaw.real (D ∩ X ⁻¹' B) from measureReal_restrict_apply hD]
    rw [inter_comm D,←preimage_inter,hX.measureReal_preimage (hB.inter (isClosed_orbitBudget n s ε).measurableSet).nullMeasurableSet]
  rwa [hev] at ht

#print axioms prime_probes_recover_maximum
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.JointSpeeds
