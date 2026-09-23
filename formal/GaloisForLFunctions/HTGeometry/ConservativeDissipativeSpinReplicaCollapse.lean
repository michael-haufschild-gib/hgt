import GaloisForLFunctions.HTGeometry.ConservativeDissipativeSpinFidelity
import GaloisForLFunctions.HTGeometry.ConservativeDissipativeSpinEnergy

/-!
# Replica distinguishability and frame collapse under positive spin damping

Application of Schaffer–Exl, arXiv:2609.04530, to the corpus's pure-state replica
projectors and finite preparation frame energy. Every fixed finite replica count
has pairwise fidelity tending to one and projector separation tending to zero.
The whole nonempty finite chart ensemble has frame energy tending to one. A global
Bernoulli bound quantifies how copy count offsets the exponential damping factor;
initial coordinates and time are unrestricted, and positive damping is constructed.
-/

set_option autoImplicit false
open scoped Matrix ComplexConjugate
open Filter
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section

/-- Any two chart states have asymptotically unit fidelity under constructed positive damping. -/
theorem spinSpinorFlow_fidelity_tendsto_one (s : ℝ) (z w : ℂ) :
    Tendsto (fun t => finitePureStateFidelity
      (spinSpinorFlow (Real.exp s) z t) (spinSpinorFlow (Real.exp s) w t))
        atTop (nhds 1) := by
  have hz := spinPlaneFlow_positive_tendsto_zero s z
  have hw := spinPlaneFlow_positive_tendsto_zero s w
  have hn : Tendsto (fun t => ‖spinPlaneFlow (Real.exp s) z t -
      spinPlaneFlow (Real.exp s) w t‖ ^ (2 : ℕ)) atTop (nhds 0) := by
    simpa using ((hz.sub hw).norm.pow 2)
  have hdz : Tendsto (fun t => 1 + ‖spinPlaneFlow (Real.exp s) z t‖ ^ (2 : ℕ))
      atTop (nhds 1) := by simpa using (hz.norm.pow 2).const_add 1
  have hdw : Tendsto (fun t => 1 + ‖spinPlaneFlow (Real.exp s) w t‖ ^ (2 : ℕ))
      atTop (nhds 1) := by simpa using (hw.norm.pow 2).const_add 1
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub (hn.div (hdz.mul hdw) (by simp : (1 : ℝ) * 1 ≠ 0))
  convert h using 1
  · funext t
    rw [spinSpinorFlow, spinSpinorFlow, spinChartSpinor_fidelity, Bottcher.chordalDist_sq]
    rfl
  · simp

/-- Every fixed finite replica count eventually loses pairwise distinguishability. -/
theorem spinSpinorFlow_replica_fidelity_tendsto_one (r : ℕ) (s : ℝ) (z w : ℂ) :
    Tendsto (fun t => finitePureStateFidelity
      (finitePureTensorPower r (spinSpinorFlow (Real.exp s) z t))
      (finitePureTensorPower r (spinSpinorFlow (Real.exp s) w t))) atTop (nhds 1) := by
  simpa only [finitePureStateFidelity_tensorPower, one_pow] using
    (spinSpinorFlow_fidelity_tendsto_one s z w).pow r

/-- The actual replica-projector squared distance tends to zero. -/
theorem spinSpinorFlow_replica_projector_distance_tendsto_zero
    (r : ℕ) (s : ℝ) (z w : ℂ) :
    Tendsto (fun t => ‖finitePureProjectorEuclidean
      (finitePureTensorPower r (spinSpinorFlow (Real.exp s) z t)) -
        finitePureProjectorEuclidean
          (finitePureTensorPower r (spinSpinorFlow (Real.exp s) w t))‖ ^ (2 : ℕ)) atTop (nhds 0) := by
  have h := (tendsto_const_nhds (x := (2 : ℝ))).sub ((spinSpinorFlow_replica_fidelity_tendsto_one r s z w).const_mul 2)
  convert h using 1
  · funext t
    exact norm_finitePureProjectorEuclidean_sub_sq
      (spinChartSpinor_replica_normalized r (spinPlaneFlow (Real.exp s) z t))
      (spinChartSpinor_replica_normalized r (spinPlaneFlow (Real.exp s) w t))
  · ring

/-- A nonempty finite ensemble of replicated actual spin projectors. -/
def spinReplicaFrameEnergy (n r : ℕ) (a : ℝ) (z : Fin (n + 1) → ℂ) (t : ℝ) : ℝ :=
  finitePreparationFrameEnergy (fun i => finitePureProjectorEuclidean
    (finitePureTensorPower r (spinSpinorFlow a (z i) t)))

/-- Exact average-fidelity formula retains every pair in the whole finite ensemble. -/
theorem spinReplicaFrameEnergy_eq (n r : ℕ) (a : ℝ) (z : Fin (n + 1) → ℂ) (t : ℝ) :
    spinReplicaFrameEnergy n r a z t =
      ∑ i, ∑ j, ((n + 1 : ℕ) : ℝ)⁻¹ * ((n + 1 : ℕ) : ℝ)⁻¹ *
        (1 - Bottcher.chordalDist (spinPlaneFlow a (z i) t) (spinPlaneFlow a (z j) t) ^ (2 : ℕ)) ^ r := by
  unfold spinReplicaFrameEnergy
  rw [finitePreparationFrameEnergy_replicaProjector_eq_averageFidelity]
  simp only [Fintype.card_fin, spinSpinorFlow, spinChartSpinor_fidelity]

/-- Every finite replica ensemble reaches the maximal coincident-state frame-energy limit. -/
theorem spinReplicaFrameEnergy_tendsto_one (n r : ℕ) (s : ℝ) (z : Fin (n + 1) → ℂ) :
    Tendsto (spinReplicaFrameEnergy n r (Real.exp s) z) atTop (nhds 1) := by
  have hpair : ∀ i j : Fin (n + 1), Tendsto
      (fun t => ((n + 1 : ℕ) : ℝ)⁻¹ * ((n + 1 : ℕ) : ℝ)⁻¹ *
        finitePureStateFidelity (spinSpinorFlow (Real.exp s) (z i) t)
          (spinSpinorFlow (Real.exp s) (z j) t) ^ r)
      atTop (nhds (((n + 1 : ℕ) : ℝ)⁻¹ * ((n + 1 : ℕ) : ℝ)⁻¹)) := by
    intro i j
    simpa only [one_pow, mul_one] using
      ((spinSpinorFlow_fidelity_tendsto_one s (z i) (z j)).pow r).const_mul
        (((n + 1 : ℕ) : ℝ)⁻¹ * ((n + 1 : ℕ) : ℝ)⁻¹)
  have hsum := tendsto_finsetSum Finset.univ (fun i _ =>
    tendsto_finsetSum Finset.univ (fun j _ => hpair i j))
  convert hsum using 1
  · funext t
    simpa only [spinReplicaFrameEnergy, Fintype.card_fin] using
      finitePreparationFrameEnergy_replicaProjector_eq_averageFidelity r
        (fun i : Fin (n + 1) => spinSpinorFlow (Real.exp s) (z i) t)
  · have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp

/-- Bernoulli's inequality bounds every actual replicated projector separation by its copy count. -/
theorem spinChartSpinor_replica_projector_distance_le (r : ℕ) (z w : ℂ) :
    ‖finitePureProjectorEuclidean (finitePureTensorPower r (spinChartSpinor z)) -
      finitePureProjectorEuclidean (finitePureTensorPower r (spinChartSpinor w))‖ ^ (2 : ℕ) ≤
        2 * (r : ℝ) * (1 - finitePureStateFidelity (spinChartSpinor z) (spinChartSpinor w)) := by
  have hf : -1 ≤ finitePureStateFidelity (spinChartSpinor z) (spinChartSpinor w) := by
    unfold finitePureStateFidelity
    exact le_trans (by linarith : (-1 : ℝ) ≤ 0) (sq_nonneg _)
  have hb := one_add_mul_sub_le_pow hf r
  rw [norm_finitePureProjectorEuclidean_sub_sq (spinChartSpinor_replica_normalized r z)
    (spinChartSpinor_replica_normalized r w), finitePureStateFidelity_tensorPower]
  linarith

/-- Global explicit resource bound: copy count must compensate exponential damping to retain separation. -/
theorem spinSpinorFlow_replica_projector_exponential_bound
    (r : ℕ) (a : ℝ) (z w : ℂ) (t : ℝ) :
    ‖finitePureProjectorEuclidean (finitePureTensorPower r (spinSpinorFlow a z t)) -
      finitePureProjectorEuclidean (finitePureTensorPower r (spinSpinorFlow a w t))‖ ^ (2 : ℕ) ≤
        2 * (r : ℝ) * Real.exp (-2 * a ^ (2 : ℕ) * t) * ‖z - w‖ ^ (2 : ℕ) := by
  have hE : 0 ≤ Real.exp (-2 * a ^ (2 : ℕ) * t) := (Real.exp_pos _).le
  have hz := mul_nonneg hE (sq_nonneg ‖z‖)
  have hw := mul_nonneg hE (sq_nonneg ‖w‖)
  have hd : 1 ≤ (1 + Real.exp (-2 * a ^ (2 : ℕ) * t) * ‖z‖ ^ (2 : ℕ)) *
      (1 + Real.exp (-2 * a ^ (2 : ℕ) * t) * ‖w‖ ^ (2 : ℕ)) := by nlinarith [mul_nonneg hz hw]
  have hn := mul_nonneg hE (sq_nonneg ‖z - w‖)
  have hq : 1 - finitePureStateFidelity (spinSpinorFlow a z t) (spinSpinorFlow a w t) ≤
      Real.exp (-2 * a ^ (2 : ℕ) * t) * ‖z - w‖ ^ (2 : ℕ) := by
    rw [spinSpinorFlow_fidelity]
    have hv : Real.exp (-2 * a ^ (2 : ℕ) * t) * ‖z - w‖ ^ (2 : ℕ) /
        ((1 + Real.exp (-2 * a ^ (2 : ℕ) * t) * ‖z‖ ^ (2 : ℕ)) *
          (1 + Real.exp (-2 * a ^ (2 : ℕ) * t) * ‖w‖ ^ (2 : ℕ))) ≤
        Real.exp (-2 * a ^ (2 : ℕ) * t) * ‖z - w‖ ^ (2 : ℕ) := by
      apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hd)).mpr
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hd hn
    linarith
  calc
    _ ≤ 2 * (r : ℝ) * (1 - finitePureStateFidelity
        (spinSpinorFlow a z t) (spinSpinorFlow a w t)) :=
      spinChartSpinor_replica_projector_distance_le r _ _
    _ ≤ 2 * (r : ℝ) * (Real.exp (-2 * a ^ (2 : ℕ) * t) * ‖z - w‖ ^ (2 : ℕ)) :=
      mul_le_mul_of_nonneg_left hq (by positivity)
    _ = _ := by ring

end
end GaloisForLFunctions.HTGeometry.SchafferExl
