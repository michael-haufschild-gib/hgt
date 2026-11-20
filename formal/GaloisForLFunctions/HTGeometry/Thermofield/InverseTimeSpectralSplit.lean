import GaloisForLFunctions.HTGeometry.Thermofield.ThermalReturnPlateau
import GaloisForLFunctions.HTGeometry.FiniteWindowOneKnobUniformity

/-!
# Inverse-time splitting of thermofield collisions

In the finite spectral counterpart of scale separation in arXiv:2611.25720,
fixed nonzero replica gaps dephase. A splitting proportional to the inverse
observation time keeps a finite phase within each resonant block. The limit
retains the Gibbs weights of the unsplit spectrum and resolves the internal
gaps by the symmetric-window sinc kernel. The affine exceptional set identifies
the same joint collision mass in the limit of fixed nonzero perturbations.
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
private theorem continuousAt_gibbsWeight (β : ℝ) (E : α → ℝ) :
    ContinuousAt (finiteGibbsStateWeight β) E := by
  refine tendsto_pi_nhds.mpr fun i => ?_
  have hterm (j : α) : Continuous (fun e : α → ℝ => Real.exp (-β * e j)) := by fun_prop
  have hpart : Continuous (finiteGibbsPartition (α := α) β) := by
    unfold finiteGibbsPartition
    exact continuous_finsetSum _ fun j _ => hterm j
  have hquot : ContinuousAt (fun e : α → ℝ => finiteGibbsStateWeight β e i) E := by
    unfold finiteGibbsStateWeight
    exact (hterm i).continuousAt.div hpart.continuousAt (finiteGibbsPartition_pos β E).ne'
  exact hquot.tendsto

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
      ((continuousAt_gibbsWeight β E).tendsto.comp (tendsto_inverseTimeSpectrum E F τ)))
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

omit [DecidableEq α] [Nonempty α] in
private theorem affine_gap (E F : α → ℝ) (s : ℝ) (p q : α → ℕ) :
    oneKnobDetuning (affineSpectrum E F) s p q =
      (replicaMultiplicityEnergy E p - replicaMultiplicityEnergy E q) +
        s * (replicaMultiplicityEnergy F p - replicaMultiplicityEnergy F q) := by
  simpa only [replicaMultiplicityEnergy, sub_mul, Finset.sum_sub_distrib] using
    oneKnobDetuning_affineSpectrum E F s p q

private def affineExceptions (E F : α → ℝ) (M : ℕ) : Set ℝ :=
  exceptionalKnobSet (affineReplicaRelationDetection E F Set.univ M)

omit [Nonempty α] in
private theorem affine_joint_resonance_iff (E F : α → ℝ) {M n : ℕ} (hn : n ≤ M)
    {s : ℝ} (hs : s ∉ affineExceptions E F M)
    {p q : α → ℕ} (hp : p ∈ Finset.univ.piAntidiag n)
    (hq : q ∈ Finset.univ.piAntidiag n) :
    replicaMultiplicityEnergy (affineSpectrum E F s) p =
        replicaMultiplicityEnergy (affineSpectrum E F s) q ↔
      replicaMultiplicityEnergy E p = replicaMultiplicityEnergy E q ∧
        replicaMultiplicityEnergy F p = replicaMultiplicityEnergy F q := by
  constructor
  · intro hzero
    have hzero' : oneKnobDetuning (affineSpectrum E F) s p q = 0 :=
      sub_eq_zero.mpr hzero
    have hident (a : ℝ) : oneKnobDetuning (affineSpectrum E F) a p q = 0 := by
      by_contra ha
      apply hs
      rw [affineExceptions, exceptionalKnobSet, Set.mem_iUnion₂]
      refine ⟨(n, p, q), mem_replicaPairIndex hn hp hq, ?_, ?_⟩
      · change |(affineRelationPolynomial E F (n, p, q)).eval s| = 0
        rw [eval_affineRelationPolynomial, hzero', abs_zero]
      · exact fun h => ha (h a (Set.mem_univ a))
    have hE := hident 0
    rw [affine_gap, zero_mul, add_zero, sub_eq_zero] at hE
    have hF := hident 1
    rw [affine_gap, hE, sub_self, zero_add, one_mul, sub_eq_zero] at hF
    exact ⟨hE, hF⟩
  · rintro ⟨hE, hF⟩
    apply sub_eq_zero.mp
    change oneKnobDetuning (affineSpectrum E F) s p q = 0
    simp only [affine_gap, hE, hF, sub_self, mul_zero, add_zero]

omit [Nonempty α] in
/-- One punctured neighborhood of zero stabilizes the exact resonance pattern
at every replica order up to the chosen finite order. -/
theorem exists_affine_resonance_neighborhood (E F : α → ℝ) (M : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, s ≠ 0 → |s| < δ →
      ∀ n ≤ M, ∀ p ∈ Finset.univ.piAntidiag n, ∀ q ∈ Finset.univ.piAntidiag n,
        (replicaMultiplicityEnergy (affineSpectrum E F s) p =
            replicaMultiplicityEnergy (affineSpectrum E F s) q ↔
          replicaMultiplicityEnergy E p = replicaMultiplicityEnergy E q ∧
            replicaMultiplicityEnergy F p = replicaMultiplicityEnergy F q) := by
  let Z := affineExceptions E F M
  have hfinite : Z.Finite := finite_exceptionalKnobSet _
  have hclosed : IsClosed (Z \ {0}) := (hfinite.subset Set.sdiff_subset).isClosed
  have hzero : (0 : ℝ) ∈ (Z \ {0})ᶜ := by simp
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hclosed.isOpen_compl.mem_nhds hzero)
  refine ⟨δ, hδ, fun s hne hlt n hn p hp q hq =>
    affine_joint_resonance_iff E F hn ?_ hp hq⟩
  intro hs
  have hsb : s ∈ Metric.ball (0 : ℝ) δ := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hlt
  exact hball hsb ⟨hs, hne⟩

/-- Collision weight of the ordered pairs resonant at both scales. -/
def jointReplicaCollisionMass (w E F : α → ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ Finset.univ.piAntidiag n,
    ∑ q ∈ Finset.univ.piAntidiag n,
      if replicaMultiplicityEnergy E p = replicaMultiplicityEnergy E q ∧
          replicaMultiplicityEnergy F p = replicaMultiplicityEnergy F q
      then fidelityReplicaMultiplicityWeight w p q else 0

omit [Nonempty α] in
private theorem continuous_jointReplicaCollisionMass (E F : α → ℝ) (n : ℕ) :
    Continuous (fun w => jointReplicaCollisionMass w E F n) := by
  unfold jointReplicaCollisionMass
  refine continuous_finsetSum _ fun p _ => continuous_finsetSum _ fun q _ => ?_
  split_ifs
  · exact continuous_replicaMultiplicityWeight p q
  · exact continuous_const

omit [Nonempty α] in
/-- On a punctured neighborhood, the completed replica collision mass is
exactly the joint mass for every choice of weights and every order through M. -/
theorem eventually_affine_collisionMass_eq_joint (E F : α → ℝ) (M : ℕ) :
    ∀ᶠ s in 𝓝[≠] (0 : ℝ), ∀ w : α → ℝ, ∀ n ≤ M,
      fidelityReplicaCollisionMass w (affineSpectrum E F s) n =
        jointReplicaCollisionMass w E F n := by
  obtain ⟨δ, hδ, h⟩ := exists_affine_resonance_neighborhood E F M
  have hm : ∀ᶠ s in 𝓝 (0 : ℝ), s ∈ Metric.ball (0 : ℝ) δ :=
    Metric.ball_mem_nhds _ hδ
  have hsmall : ∀ᶠ s in 𝓝 (0 : ℝ), |s| < δ :=
    hm.mono fun _ hs => by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hs
  have hne : ∀ᶠ s in 𝓝[≠] (0 : ℝ), s ≠ 0 := self_mem_nhdsWithin
  filter_upwards [hsmall.filter_mono nhdsWithin_le_nhds, hne] with s hs hsne w n hn
  rw [← fidelityReplicaResonantMass_eq_collisionMass, fidelityReplicaResonantMass,
    jointReplicaCollisionMass]
  refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => ?_
  simp only [h s hsne hs n hn p hp q hq]

/-- First taking the long-time plateau of a fixed perturbed Gibbs spectrum,
then sending the splitting to zero, gives the joint collision mass. -/
theorem gibbsAffinePlateau_tendsto_joint (β : ℝ) (E F : α → ℝ) (n : ℕ) :
    Tendsto (fun s => fidelityReplicaCollisionMass
      (finiteGibbsStateWeight β (affineSpectrum E F s)) (affineSpectrum E F s) n)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (jointReplicaCollisionMass (finiteGibbsStateWeight β E) E F n)) := by
  have hcont : Continuous (affineSpectrum E F) := by
    unfold affineSpectrum
    fun_prop
  have hE : Tendsto (affineSpectrum E F) (𝓝 (0 : ℝ)) (𝓝 E) := by
    have hzero : affineSpectrum E F 0 = E := by
      funext i
      simp only [affineSpectrum, zero_mul, add_zero]
    have ht := hcont.tendsto 0
    rwa [hzero] at ht
  have hw := (continuousAt_gibbsWeight β E).tendsto.comp hE
  have hmass := (continuous_jointReplicaCollisionMass E F n).continuousAt.tendsto.comp hw
  apply (hmass.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [eventually_affine_collisionMass_eq_joint E F n] with s hs
  exact (hs (finiteGibbsStateWeight β (affineSpectrum E F s)) n le_rfl).symm

/-- The actual two-copy return plateau has the same punctured splitting limit. -/
theorem affinePartitionReturnPlateau_tendsto_joint (β : ℝ) (E F : α → ℝ) :
    Tendsto (fun s => returnPlateau β (affineSpectrum E F s)) (𝓝[≠] (0 : ℝ))
      (𝓝 (jointReplicaCollisionMass (finiteGibbsStateWeight β E) E F 1)) :=
  gibbsAffinePlateau_tendsto_joint β E F 1

omit [Nonempty α] in
/-- The resolved crossover and the fixed-splitting plateau have the same
joint collision limit. -/
theorem thermalReplicaCrossover_tendsto_affinePlateau (β : ℝ) (E F : α → ℝ) (n : ℕ) :
    Tendsto (thermalReplicaCrossover β E F n) atTop
      (𝓝 (jointReplicaCollisionMass (finiteGibbsStateWeight β E) E F n : ℂ)) := by
  simpa only [jointReplicaCollisionMass, Complex.ofReal_sum, apply_ite, Complex.ofReal_zero]
    using thermalReplicaCrossover_tendsto_jointCollision β E F n

#print axioms thermalReplicaMean_tendsto_inverseTimeSpectrum
#print axioms thermalReplicaCrossover_tendsto_jointCollision
#print axioms partitionReturnMean_tendsto_inverseTimeSpectrum
#print axioms exists_affine_resonance_neighborhood
#print axioms gibbsAffinePlateau_tendsto_joint
#print axioms affinePartitionReturnPlateau_tendsto_joint

end

end GaloisForLFunctions.HTGeometry.Thermofield
