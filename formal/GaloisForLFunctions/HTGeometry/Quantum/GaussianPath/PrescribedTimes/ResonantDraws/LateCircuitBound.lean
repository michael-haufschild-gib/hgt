import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.LateScalarProbability
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.CircuitVolume
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.Probability.PhaseClock

/-! # Prescribed-delay probabilities beyond a deterministic phase horizon -/
open Set Filter MeasureTheory ProbabilityTheory Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws
noncomputable section
open SharpOccupation

private theorem snapshot_ray_bound (k s : ℕ) (ω : PathPauliDisorder) (t G : ℝ)
    (hG : 0<G) (ht : G≤t) (o : (PrefixIndex (k+1) → ℝ) → ℝ)
    (hcov : ∀ a > (0:ℝ), ∀ x, a*o (a • x)=o x) :
    let N := k+3
    let D : ℕ := 2^N
    let u := pathPauliDisorderShell ω (k+1)
    let x := fun i => u (pathCoeffEquiv (k+1) i)
    let H : selfAdjoint (Register N) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
    (∃ e : (Fin N → Bool) ≃ Fin ((D-1)+1), ∀ z : Fin (D-1) → ℝ, ∃ v ∈ Icc 0 G, ∀ j,
      turnDist (v*RHTower.zeroProjectiveFrequency (H.2.isHermitian.eigenvalues ∘ e.symm) j-z j)<1/80) →
    rayMass 2 {y | pathGateDistance (k+1) s y (o y+t)≤1/10} x ≤
      2*((atMostQuarterCircuitNet N s).card:ℝ)/(2:ℝ)^(D-1) := by
  intro N D u x H ⟨e,he⟩
  let C := {v : ℝ | HasProjectiveCircuitApproximation N (1/10) s (unitaryEvolution H.val (o x+v))}
  let Q : ℝ := (atMostQuarterCircuitNet N s).card
  have hgen : numberedGenerator (k+1) x=H.val := numberedGenerator_shell u
  have hset : {v | pathGateDistance (k+1) s x (o x+v)≤1/10}=C := by
    ext v
    simp only [C,mem_setOf_eq,hasProjectiveCircuitApproximation_iff_infDist,pathGateDistance,hgen]
  have ht₀ := hG.trans_le ht
  rw [rayMass_of_covariant_origin (k+1) s o hcov x 2 t (1/10),hset,
    dilation_interval_volume C 1 2 ht₀,one_mul,←div_eq_inv_mul]
  have hv := cheap_snapshot_volume H e hG.le he s (o x) t ht₀.le
  apply (div_le_div_iff₀ ht₀ (by positivity)).mpr
  change volume.real (C ∩ Icc t (2*t))*(2:ℝ)^(D-1) ≤ 2*Q*t
  rw [mul_comm (volume.real _)]
  apply hv.trans
  change Q*(t+G) ≤ 2*Q*t
  have hh := mul_le_mul_of_nonneg_left (add_le_add_left ht t) (show 0≤Q from Nat.cast_nonneg _)
  linarith only [hh]

private theorem covariant_snapshot_price (k s : ℕ) (t G : ℝ) (hG : 0<G) (ht : G≤t)
    (o : (PrefixIndex (k+1) → ℝ) → ℝ) (ho : Measurable o)
    (hcov : ∀ a > (0:ℝ), ∀ x, a*o (a • x)=o x) :
    let N := k+3
    let D : ℕ := 2^N
    let μ := Measure.pi fun _ : PrefixIndex (k+1) => gaussianReal 0 1
    (∃ B : Set PathPauliDisorder, pathPauliDisorderLaw B ≤ ENNReal.ofReal (3*(1/2:ℝ)^D) ∧
      ∀ᵐ ω ∂pathPauliDisorderLaw, ω ∉ B →
        let E := (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))).isHermitian.eigenvalues
        ∃ e : (Fin N → Bool) ≃ Fin ((D-1)+1), ∀ z : Fin (D-1) → ℝ, ∃ v ∈ Icc 0 G, ∀ j,
          turnDist (v*RHTower.zeroProjectiveFrequency (E ∘ e.symm) j-z j)<1/80) →
    μ.real {x | pathGateDistance (k+1) s x (o x+t)≤1/10} ≤
      (2:ℝ)^Fintype.card (PrefixIndex (k+1))*
        (2*((atMostQuarterCircuitNet N s).card:ℝ)/(2:ℝ)^(D-1)+3*(1/2:ℝ)^D) := by
  intro N D μ ⟨B,hB,hgood⟩
  letI : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
  let X := fun ω i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
  let E := {x | pathGateDistance (k+1) s x (o x+t)≤1/10}
  have hm : MeasurableSet E := measurable_origin_event (k+1) s (1/10) t o ho
  have hX := gaussian_pauli_prefix_coordinates_law (k+1)
  let f := fun ω => rayMass 2 E (X ω)
  have hf : Measurable f := (measurable_rayMass 2 hm).comp hX.measurable
  have h₁ (ω) : f ω≤1 := by
    apply (measureReal_mono (subset_univ _)).trans_eq
    rw [measureReal_restrict_apply_univ,Real.volume_real_Icc_of_le (by norm_num)]; norm_num
  have h := mean_of_exception pathPauliDisorderLaw f hf (fun _ => measureReal_nonneg) h₁ B
    (q:=2*((atMostQuarterCircuitNet N s).card:ℝ)/(2:ℝ)^(D-1)) (by positivity) hB (by positivity)
    (hgood.mono fun ω hw hω => snapshot_ray_bound k s ω t G hG ht o hcov (hw hω))
  have he : (∫ x, rayMass 2 E x ∂μ)=∫ ω, f ω ∂pathPauliDisorderLaw := by
    change (∫ x, rayMass 2 E x ∂(centredProductGaussian _ 1))=_
    rw [←hX.map_eq,integral_map hX.measurable.aemeasurable (measurable_rayMass 2 hm).aestronglyMeasurable]
  exact (snapshot_le_dyadic_mean E hm).trans (mul_le_mul_of_nonneg_left (he.le.trans h) (by positivity))

/-- At every sufficiently late prescribed date the empty circuit and
every larger budget obey an explicit disorder probability bound. The
same bound holds for a prescribed delay from the actual first robust
crossing, uniformly in the crossing budget and tested budget. -/
theorem gaussian_late_circuit_bound :
    ∃ c : ℕ, ∀ k j s : ℕ,
      let n := k+1
      let N := k+3
      let D : ℕ := 2^N
      let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
      let σ := crossingOrigin n j (9/80)
      let price := (2:ℝ)^Fintype.card (PrefixIndex n)*
        (2*((atMostQuarterCircuitNet N s).card:ℝ)/(2:ℝ)^(D-1)+3*(1/2:ℝ)^D)
      ∀ t : ℝ, (2:ℝ)^(D^c) ≤ t →
        μ.real {x | pathGateDistance n s x t ≤ 1/10} ≤ price ∧
        μ.real {x | pathGateDistance n s x (σ x+t) ≤ 1/10} ≤ price := by
  obtain ⟨c,hc⟩ := SpectralJets.gaussian_exponential_confidence_clock
  refine ⟨c,fun k j s => ?_⟩
  intro n N D μ σ price t ht
  let G := (2:ℝ)^(D^c)
  have hG : 0<G := by dsimp only [G]; positivity
  obtain ⟨B,hB,hh⟩ := hc k
  have hg : ∀ᵐ ω ∂pathPauliDisorderLaw, ω ∉ B →
      let E := (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω n)).isHermitian.eigenvalues
      ∃ e : (Fin N → Bool) ≃ Fin ((D-1)+1), ∀ z : Fin (D-1) → ℝ, ∃ v ∈ Icc 0 G, ∀ j,
        turnDist (v*RHTower.zeroProjectiveFrequency (E ∘ e.symm) j-z j)<1/80 := by
    filter_upwards [hh] with ω hω hx
    obtain ⟨e,he⟩ := hω hx
    exact ⟨e,by simpa only [zero_add] using he 0⟩
  constructor
  · simpa only [zero_add] using covariant_snapshot_price k s t G hG ht (fun _ => 0)
      measurable_const (fun _ _ _ => mul_zero _) ⟨B,hB,hg⟩
  · exact covariant_snapshot_price k s t G hG ht σ (measurable_crossingOrigin ..)
      (fun _ ha => smul_crossingOrigin n j (9/80) ha) ⟨B,hB,hg⟩

#print axioms gaussian_late_circuit_bound
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws
