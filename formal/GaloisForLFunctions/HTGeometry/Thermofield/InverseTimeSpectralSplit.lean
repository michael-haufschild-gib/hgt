import GaloisForLFunctions.HTGeometry.Thermofield.ThermalReturnPlateau

/-!
# Inverse-time splitting of thermofield collisions

In the finite spectral counterpart of scale separation in arXiv:2611.25720,
fixed nonzero replica gaps dephase. A splitting proportional to the inverse
observation time keeps a finite phase within each resonant block. The limit
retains the Gibbs weights of the unsplit spectrum and resolves the internal
gaps by the symmetric-window sinc kernel.
-/

open Filter Topology
open _root_.HTGeometry

namespace GaloisForLFunctions.HTGeometry.Thermofield

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

/-- A coarse Hamiltonian with an inverse-time diagonal perturbation. -/
def inverseTimeSpectrum (E F : α → ℝ) (τ T : ℝ) (i : α) : ℝ :=
  E i + (τ / T) * F i

omit [DecidableEq α] [Nonempty α] in
private theorem replicaMultiplicityEnergy_inverseTimeSpectrum
    (E F : α → ℝ) (τ T : ℝ) (p : α → ℕ) :
    replicaMultiplicityEnergy (inverseTimeSpectrum E F τ T) p =
      replicaMultiplicityEnergy E p + (τ / T) * replicaMultiplicityEnergy F p := by
  unfold replicaMultiplicityEnergy
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by
    unfold inverseTimeSpectrum
    ring

private theorem tendsto_sinc_affine_nonzero (a b : ℝ) (ha : a ≠ 0) :
    Tendsto (fun T : ℝ => Real.sinc (T * a + b)) atTop (𝓝 0) := by
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · have h := tendsto_real_sinc_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop (-b) (tendsto_id.atTop_mul_const (neg_pos.mpr hneg)))
    refine h.congr' (Eventually.of_forall fun T => ?_)
    change Real.sinc (T * -a + -b) = Real.sinc (T * a + b)
    rw [show T * -a + -b = -(T * a + b) by ring, Real.sinc_neg]
  · exact tendsto_real_sinc_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop b (tendsto_id.atTop_mul_const hpos))

private theorem tendsto_symmetricPhaseAverage_inverseTime (a b τ : ℝ) :
    Tendsto (fun T : ℝ => symmetricPhaseAverage T (a + τ / T * b)) atTop
      (𝓝 (if a = 0 then (Real.sinc (τ * b) : ℂ) else 0)) := by
  have hrepr : (fun T : ℝ => symmetricPhaseAverage T (a + τ / T * b)) =ᶠ[atTop]
      fun T => (Real.sinc (T * a + τ * b) : ℂ) := by
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with T hT
    rw [symmetricPhaseAverage_eq_sinc _ _ hT]
    congr 2
    field_simp
  refine (tendsto_congr' hrepr).mpr ?_
  by_cases ha : a = 0
  · subst a
    simpa only [mul_zero, zero_add, if_pos rfl, if_true] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (Real.sinc (τ * b) : ℂ)) atTop
        (𝓝 (Real.sinc (τ * b) : ℂ)))
  · simp only [if_neg ha]
    have h := Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_sinc_affine_nonzero a (τ * b) ha)
    simpa only [Function.comp_def, Complex.ofReal_zero] using h

omit [Fintype α] [DecidableEq α] [Nonempty α] in
private theorem tendsto_inverseTimeSpectrum (E F : α → ℝ) (τ : ℝ) :
    Tendsto (inverseTimeSpectrum E F τ) atTop (𝓝 E) := by
  refine tendsto_pi_nhds.mpr fun i => ?_
  have h := (tendsto_inv_atTop_zero.const_mul τ).mul_const (F i)
  have h' : Tendsto (fun T : ℝ => E i + τ * T⁻¹ * F i) atTop
      (𝓝 (E i + τ * 0 * F i)) := tendsto_const_nhds.add h
  simpa only [inverseTimeSpectrum, div_eq_mul_inv, mul_zero, zero_mul, add_zero] using h'

omit [DecidableEq α] [Nonempty α] in
private theorem continuous_replicaMultiplicityWeight (p q : α → ℕ) :
    Continuous (fun w : α → ℝ => fidelityReplicaMultiplicityWeight w p q) := by
  unfold fidelityReplicaMultiplicityWeight
  fun_prop

omit [DecidableEq α] in
private theorem tendsto_GibbsWeight_inverseTime (β τ : ℝ) (E F : α → ℝ) :
    Tendsto (fun T => finiteGibbsStateWeight β (inverseTimeSpectrum E F τ T))
      atTop (𝓝 (finiteGibbsStateWeight β E)) := by
  refine tendsto_pi_nhds.mpr fun i => ?_
  have hterm (j : α) : Continuous (fun e : α → ℝ => Real.exp (-β * e j)) := by fun_prop
  have hpart : Continuous (finiteGibbsPartition (α := α) β) := by
    unfold finiteGibbsPartition
    exact continuous_finsetSum _ fun j _ => hterm j
  have hquot : ContinuousAt (fun e : α → ℝ => finiteGibbsStateWeight β e i) E := by
    unfold finiteGibbsStateWeight
    exact (hterm i).continuousAt.div hpart.continuousAt (finiteGibbsPartition_pos β E).ne'
  exact hquot.tendsto.comp (tendsto_inverseTimeSpectrum E F τ)

/-- Finite crossover mass. Only exactly resonant coarse replica pairs contribute,
with their fine gaps resolved at the scaled window size. -/
def thermalReplicaCrossover (β : ℝ) (E F : α → ℝ) (n : ℕ) (τ : ℝ) : ℂ :=
  ∑ p ∈ Finset.univ.piAntidiag n,
    ∑ q ∈ Finset.univ.piAntidiag n,
      if replicaMultiplicityEnergy E p = replicaMultiplicityEnergy E q then
        (fidelityReplicaMultiplicityWeight (finiteGibbsStateWeight β E) p q : ℂ) *
          (Real.sinc (τ * (replicaMultiplicityEnergy F p - replicaMultiplicityEnergy F q)) : ℂ)
      else 0

/-- The actual finite-window Gibbs return moments retain precisely the coarse
resonant pairs at an inverse-time splitting. -/
theorem thermalReplicaMean_tendsto_inverseTimeSpectrum
    (β τ : ℝ) (E F : α → ℝ) (n : ℕ) :
    Tendsto (fun T =>
      finiteSpectralSurvivalFidelityMean
        (finiteGibbsStateWeight β (inverseTimeSpectrum E F τ T))
        (inverseTimeSpectrum E F τ T) n T)
      atTop (𝓝 (thermalReplicaCrossover β E F n τ)) := by
  simp only [finiteSpectralSurvivalFidelityMean_eq_replicaPhaseAverage, thermalReplicaCrossover]
  refine tendsto_finsetSum _ fun p _ => tendsto_finsetSum _ fun q _ => ?_
  have hw := Complex.continuous_ofReal.continuousAt.tendsto.comp
    ((continuous_replicaMultiplicityWeight p q).continuousAt.tendsto.comp
      (tendsto_GibbsWeight_inverseTime β τ E F))
  have hphase := tendsto_symmetricPhaseAverage_inverseTime
    (replicaMultiplicityEnergy E p - replicaMultiplicityEnergy E q)
    (replicaMultiplicityEnergy F p - replicaMultiplicityEnergy F q) τ
  have h := hw.mul hphase
  simpa only [Function.comp_apply, sub_eq_zero, mul_ite, mul_zero,
    replicaMultiplicityEnergy_inverseTimeSpectrum,
    show ∀ a b c d e : ℝ, a + e * b - (c + e * d) = (a - c) + e * (b - d)
      by intros; ring] using h

omit [Nonempty α] in
/-- At zero splitting, the crossover is the original Gibbs collision mass. -/
theorem thermalReplicaCrossover_zero (β : ℝ) (E F : α → ℝ) (n : ℕ) :
    thermalReplicaCrossover β E F n 0 =
      (fidelityReplicaCollisionMass (finiteGibbsStateWeight β E) E n : ℂ) := by
  rw [← fidelityReplicaResonantMass_eq_collisionMass]
  simp only [thermalReplicaCrossover, fidelityReplicaResonantMass, zero_mul, Real.sinc_zero,
    Complex.ofReal_one, mul_one, Complex.ofReal_sum, apply_ite, Complex.ofReal_zero]

omit [Nonempty α] in
/-- A flat coarse spectrum leaves the entire fine-spectrum return at the
scaled window size, with the Gibbs weights of the flat state. -/
theorem thermalReplicaCrossover_flat (β e : ℝ) (F : α → ℝ) (n : ℕ) (τ : Set.Ioi (0 : ℝ)) :
    thermalReplicaCrossover β (fun _ => e) F n τ =
      finiteSpectralSurvivalFidelityMean (finiteGibbsStateWeight β (fun _ => e)) F n τ := by
  have hτ : 0 < (τ : ℝ) := τ.2
  rw [finiteSpectralSurvivalFidelityMean_eq_replicaPhaseAverage, thermalReplicaCrossover]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  have henergy (m : α → ℕ) (hm : m ∈ Finset.univ.piAntidiag n) :
      replicaMultiplicityEnergy (fun _ => e) m = (n : ℝ) * e := by
    rw [replicaMultiplicityEnergy, ← Finset.sum_mul]
    congr 1
    exact_mod_cast (Finset.mem_piAntidiag.mp hm).1
  rw [henergy p hp, henergy q hq, if_pos rfl, symmetricPhaseAverage_eq_sinc _ _ hτ.ne']

omit [Nonempty α] in
/-- Further dephasing of the resolved profile retains precisely the replica
pairs resonant at both scales. -/
theorem thermalReplicaCrossover_tendsto_jointCollision (β : ℝ) (E F : α → ℝ) (n : ℕ) :
    Tendsto (thermalReplicaCrossover β E F n) atTop (𝓝
      (∑ p ∈ Finset.univ.piAntidiag n,
        ∑ q ∈ Finset.univ.piAntidiag n,
          if replicaMultiplicityEnergy E p = replicaMultiplicityEnergy E q ∧
              replicaMultiplicityEnergy F p = replicaMultiplicityEnergy F q
          then (fidelityReplicaMultiplicityWeight (finiteGibbsStateWeight β E) p q : ℂ)
          else 0)) := by
  unfold thermalReplicaCrossover
  refine tendsto_finsetSum _ fun p _ => tendsto_finsetSum _ fun q _ => ?_
  by_cases hE : replicaMultiplicityEnergy E p = replicaMultiplicityEnergy E q
  · simp only [hE, if_true, true_and]
    by_cases hF : replicaMultiplicityEnergy F p = replicaMultiplicityEnergy F q
    · simp [hF]
    · simp only [hF, if_false]
      have h := tendsto_sinc_affine_nonzero
        (replicaMultiplicityEnergy F p - replicaMultiplicityEnergy F q) 0 (sub_ne_zero.mpr hF)
      have h' := Complex.continuous_ofReal.continuousAt.tendsto.comp h
      simpa only [Function.comp_apply, add_zero, Complex.ofReal_zero, mul_zero] using
        h'.const_mul (fidelityReplicaMultiplicityWeight (finiteGibbsStateWeight β E) p q : ℂ)
  · simp [hE]

/-- The two-copy partition return itself has the order-one crossover profile. -/
theorem partitionReturnMean_tendsto_inverseTimeSpectrum (β τ : ℝ) (E F : α → ℝ) :
    Tendsto (fun T => partitionReturnMean β (inverseTimeSpectrum E F τ T) T)
      atTop (𝓝 (thermalReplicaCrossover β E F 1 τ)) := by
  simpa only [partitionReturnMean, finiteSpectralSurvivalFidelityMean,
    finiteSpectralSurvivalFidelity, survival_eq_partition_ratio, pow_one] using
    thermalReplicaMean_tendsto_inverseTimeSpectrum β τ E F 1

#print axioms thermalReplicaMean_tendsto_inverseTimeSpectrum
#print axioms thermalReplicaCrossover_tendsto_jointCollision
#print axioms partitionReturnMean_tendsto_inverseTimeSpectrum

end

end GaloisForLFunctions.HTGeometry.Thermofield
