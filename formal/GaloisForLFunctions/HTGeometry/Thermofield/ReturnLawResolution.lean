import GaloisForLFunctions.HTGeometry.Thermofield.PowerTimeReturnDistribution
import GaloisForLFunctions.HTGeometry.ResolvedRecurrenceRelationCompletenessLaw

/-!
# Resolution of thermofield return laws by replica order

Resolving a fine spectrum lowers a moment precisely when it breaks a
coarse integral relation visible at that order. For three energy levels,
the first change in the return distribution can occur at any replica order.
-/

open Filter MeasureTheory Set Topology
open _root_.HTGeometry
open RHTower (SpectralReturnFidelityInterval)

namespace GaloisForLFunctions.HTGeometry.Thermofield

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

/-- The `n`th moment of a law on the survival-fidelity interval. -/
def returnFidelityMoment (law : ProbabilityMeasure SpectralReturnFidelityInterval) (n : ℕ) : ℝ :=
  ∫ x : SpectralReturnFidelityInterval, (x : ℝ) ^ n ∂(law : Measure SpectralReturnFidelityInterval)

/-- The weak limit of the power-law Gibbs return distributions. -/
def gibbsPowerTimeReturnLimit (β τ : ℝ) (E F : α → ℝ) (γ : Ioi (0 : ℝ)) :
    ProbabilityMeasure SpectralReturnFidelityInterval :=
  (existsUnique_gibbsPowerTimeReturnDistribution β τ E F γ).exists.choose

theorem gibbsWindowReturnDistribution_tendsto_powerTimeReturnLimit (β τ : ℝ) (E F : α → ℝ)
    (γ : Ioi (0 : ℝ)) :
    Tendsto (fun T => gibbsWindowReturnDistribution β (powerTimeSpectrum E F τ γ T) T)
      atTop (𝓝 (gibbsPowerTimeReturnLimit β τ E F γ)) :=
  (existsUnique_gibbsPowerTimeReturnDistribution β τ E F γ).exists.choose_spec.1

theorem returnFidelityMoment_powerTimeReturnLimit (β τ : ℝ) (E F : α → ℝ)
    (γ : Ioi (0 : ℝ)) (n : ℕ) :
    returnFidelityMoment (gibbsPowerTimeReturnLimit β τ E F γ) n =
      (powerTimeReplicaLimit β τ E F γ n).re :=
  (existsUnique_gibbsPowerTimeReturnDistribution β τ E F γ).exists.choose_spec.2 n

/-- The return law that retains all coarse resonances. -/
def gibbsUnresolvedReturnLaw (β : ℝ) (E : α → ℝ) :
    ProbabilityMeasure SpectralReturnFidelityInterval :=
  gibbsPowerTimeReturnLimit β 1 E E ⟨2, mem_Ioi.mpr (zero_lt_two : (0 : ℝ) < 2)⟩

/-- The return law that retains precisely the common coarse and fine resonances. -/
def gibbsResolvedReturnLaw (β : ℝ) (E F : α → ℝ) :
    ProbabilityMeasure SpectralReturnFidelityInterval :=
  gibbsPowerTimeReturnLimit β 1 E F ⟨1 / 2, mem_Ioi.mpr (half_pos (zero_lt_one : (0 : ℝ) < 1))⟩

theorem returnFidelityMoment_unresolved (β : ℝ) (E : α → ℝ) (n : ℕ) :
    returnFidelityMoment (gibbsUnresolvedReturnLaw β E) n =
      fidelityReplicaCollisionMass (finiteGibbsStateWeight β E) E n := by
  rw [gibbsUnresolvedReturnLaw, returnFidelityMoment_powerTimeReturnLimit]
  norm_num [powerTimeReplicaLimit]

theorem returnFidelityMoment_resolved (β : ℝ) (E F : α → ℝ) (n : ℕ) :
    returnFidelityMoment (gibbsResolvedReturnLaw β E F) n =
      jointReplicaCollisionMass (finiteGibbsStateWeight β E) E F n := by
  rw [gibbsResolvedReturnLaw, returnFidelityMoment_powerTimeReturnLimit]
  norm_num [powerTimeReplicaLimit]

/-- Every decay exponent above one has the unresolved return law. -/
theorem gibbsPowerTimeReturnLimit_eq_unresolved (β τ : ℝ) (E F : α → ℝ) (γ : Ioi (1 : ℝ)) :
    gibbsPowerTimeReturnLimit β τ E F ⟨γ, mem_Ioi.mpr ((zero_lt_one : (0 : ℝ) < 1).trans γ.2)⟩ =
      gibbsUnresolvedReturnLaw β E := by
  apply probabilityMeasure_ext_of_integral_pow_eq
  intro n
  change returnFidelityMoment (gibbsPowerTimeReturnLimit β τ E F
      ⟨γ, mem_Ioi.mpr ((zero_lt_one : (0 : ℝ) < 1).trans γ.2)⟩) n =
    returnFidelityMoment (gibbsUnresolvedReturnLaw β E) n
  have hγ : 1 < (γ : ℝ) := γ.2
  rw [returnFidelityMoment_powerTimeReturnLimit, returnFidelityMoment_unresolved]
  simp only [powerTimeReplicaLimit, hγ.ne', not_lt_of_ge hγ.le, false_and, if_false, Complex.ofReal_re]

/-- Every decay exponent below one with nonzero amplitude has the resolved return law. -/
theorem gibbsPowerTimeReturnLimit_eq_resolved (β : ℝ) (τ : {s : ℝ // s ≠ 0}) (E F : α → ℝ)
    (γ : Ioo (0 : ℝ) 1) :
    gibbsPowerTimeReturnLimit β τ E F ⟨γ, γ.2.1⟩ = gibbsResolvedReturnLaw β E F := by
  apply probabilityMeasure_ext_of_integral_pow_eq
  intro n
  change returnFidelityMoment (gibbsPowerTimeReturnLimit β τ E F ⟨γ, γ.2.1⟩) n =
    returnFidelityMoment (gibbsResolvedReturnLaw β E F) n
  have hγ : (γ : ℝ) < 1 := γ.2.2
  have hslow : (γ : ℝ) < 1 ∧ (τ : ℝ) ≠ 0 := ⟨hγ, τ.2⟩
  rw [returnFidelityMoment_powerTimeReturnLimit, returnFidelityMoment_resolved]
  simp only [powerTimeReplicaLimit, hγ.ne, if_false, if_pos hslow, Complex.ofReal_re]

theorem returnFidelityMoment_resolved_le_unresolved (β : ℝ) (E F : α → ℝ) (n : ℕ) :
    returnFidelityMoment (gibbsResolvedReturnLaw β E F) n ≤
      returnFidelityMoment (gibbsUnresolvedReturnLaw β E) n := by
  rw [returnFidelityMoment_resolved, returnFidelityMoment_unresolved]
  exact (gibbsJointCollision_le_and_lt_iff β E F n).1

/-- A moment decreases exactly when a broken integral relation is visible at that order. -/
theorem returnFidelityMoment_resolved_lt_iff (β : ℝ) (E F : α → ℝ) (n : ℕ) :
    returnFidelityMoment (gibbsResolvedReturnLaw β E F) n <
        returnFidelityMoment (gibbsUnresolvedReturnLaw β E) n ↔
      ∃ k ∈ projectiveSpectralRelationLattice E, k ∉ projectiveSpectralRelationLattice F ∧
        spectralCharacterPositiveMass k ≤ n := by
  rw [returnFidelityMoment_resolved, returnFidelityMoment_unresolved,
    (gibbsJointCollision_le_and_lt_iff β E F n).2]
  constructor
  · rintro ⟨p, hp, q, hq, hE, hF⟩
    let k := replicaMultiplicityCharacter p q
    have hreal : SpectralCharacterReplicaRealizes n k :=
      ⟨p, q, (Finset.mem_piAntidiag.mp hp).1, (Finset.mem_piAntidiag.mp hq).1, fun _ => rfl⟩
    have hdet : finiteTorusCharacterDetuning k E = 0 := by
      rw [finiteTorusCharacterDetuning_replicaMultiplicityCharacter, sub_eq_zero]
      exact hE
    have hc := (resolvedReplicaDetects_iff_relation_and_height_le E n k).mp ⟨hreal, hdet⟩
    refine ⟨k, hc.1, ?_, hc.2⟩
    intro hk
    apply hF
    have h := ((mem_projectiveSpectralRelationLattice_iff F k).mp hk).2
    rwa [finiteTorusCharacterDetuning_replicaMultiplicityCharacter, sub_eq_zero] at h
  · rintro ⟨k, hkE, hkF, hheight⟩
    have hdet := (resolvedReplicaDetects_iff_relation_and_height_le E n k).mpr ⟨hkE, hheight⟩
    obtain ⟨p, q, hp, hq, hchar⟩ := hdet.1
    have heq : replicaMultiplicityCharacter p q = k := funext fun i => (hchar i).symm
    refine ⟨p, Finset.mem_piAntidiag.mpr ⟨hp, fun _ _ => Finset.mem_univ _⟩,
      q, Finset.mem_piAntidiag.mpr ⟨hq, fun _ _ => Finset.mem_univ _⟩, ?_, ?_⟩
    · have hzero := hdet.2
      rwa [← heq, finiteTorusCharacterDetuning_replicaMultiplicityCharacter, sub_eq_zero] at hzero
    · intro hF
      apply hkF
      refine (mem_projectiveSpectralRelationLattice_iff F k).mpr
        ⟨((mem_projectiveSpectralRelationLattice_iff E k).mp hkE).1, ?_⟩
      rw [← heq, finiteTorusCharacterDetuning_replicaMultiplicityCharacter, sub_eq_zero]
      exact hF

/-- Equality of the two laws holds exactly when the fine spectrum preserves
every balanced integral relation of the coarse spectrum. -/
theorem gibbsResolvedReturnLaw_eq_iff_relationLattice_le (β : ℝ) (E F : α → ℝ) :
    gibbsResolvedReturnLaw β E F = gibbsUnresolvedReturnLaw β E ↔
      projectiveSpectralRelationLattice E ≤ projectiveSpectralRelationLattice F := by
  constructor
  · intro heq k hk
    by_contra hnot
    have hlt := (returnFidelityMoment_resolved_lt_iff β E F (spectralCharacterPositiveMass k)).mpr
      ⟨k, hk, hnot, le_rfl⟩
    rw [heq] at hlt
    exact lt_irrefl _ hlt
  · intro hle
    apply probabilityMeasure_ext_of_integral_pow_eq
    intro n
    change returnFidelityMoment (gibbsResolvedReturnLaw β E F) n =
      returnFidelityMoment (gibbsUnresolvedReturnLaw β E) n
    apply le_antisymm (returnFidelityMoment_resolved_le_unresolved β E F n)
    apply le_of_not_gt
    intro hlt
    obtain ⟨k, hk, hnot, _⟩ := (returnFidelityMoment_resolved_lt_iff β E F n).mp hlt
    exact hnot (hle hk)

/-- The weak law of the unsplit Hamiltonian is the unresolved law. -/
theorem gibbsWindowReturnDistribution_tendsto_unresolved (β : ℝ) (E : α → ℝ) :
    Tendsto (gibbsWindowReturnDistribution β E) atTop (𝓝 (gibbsUnresolvedReturnLaw β E)) := by
  let γ : Ioi (0 : ℝ) := ⟨2, mem_Ioi.mpr (zero_lt_two : (0 : ℝ) < 2)⟩
  have h := gibbsWindowReturnDistribution_tendsto_powerTimeReturnLimit β 0 E E γ
  have hlimit : gibbsPowerTimeReturnLimit β 0 E E γ = gibbsUnresolvedReturnLaw β E :=
    gibbsPowerTimeReturnLimit_eq_unresolved β 0 E E ⟨2, mem_Ioi.mpr (one_lt_two : (1 : ℝ) < 2)⟩
  rw [hlimit] at h
  refine h.congr' (Eventually.of_forall fun T => ?_)
  have he : powerTimeSpectrum E E 0 γ T = E := by
    funext i
    simp only [powerTimeSpectrum, affineSpectrum, zero_mul, add_zero]
  rw [he]

/-- Taking the long-time law first and then removing a nonzero splitting
gives the same resolved law as the slow-decay regime. -/
theorem gibbsAffineReturnLaw_tendsto_resolved (β : ℝ) (E F : α → ℝ) :
    Tendsto (fun s => gibbsUnresolvedReturnLaw β (affineSpectrum E F s)) (𝓝[≠] (0 : ℝ))
      (𝓝 (gibbsResolvedReturnLaw β E F)) := by
  apply probabilityMeasure_tendsto_of_integral_pow_tendsto
  intro n
  change Tendsto (fun s => returnFidelityMoment (gibbsUnresolvedReturnLaw β (affineSpectrum E F s)) n)
    (𝓝[≠] (0 : ℝ)) (𝓝 (returnFidelityMoment (gibbsResolvedReturnLaw β E F) n))
  simpa only [returnFidelityMoment_unresolved, returnFidelityMoment_resolved] using
    gibbsAffinePlateau_tendsto_joint β E F n

/-- The stationary return law is continuous at zero splitting precisely
when the fine spectrum preserves the coarse relation lattice. -/
theorem gibbsAffineReturnLaw_continuousAt_iff (β : ℝ) (E F : α → ℝ) :
    ContinuousAt (fun s => gibbsUnresolvedReturnLaw β (affineSpectrum E F s)) (0 : ℝ) ↔
      projectiveSpectralRelationLattice E ≤ projectiveSpectralRelationLattice F := by
  have hz : affineSpectrum E F 0 = E := by
    funext i
    simp only [affineSpectrum, zero_mul, add_zero]
  rw [continuousAt_iff_punctured_nhds, ← gibbsResolvedReturnLaw_eq_iff_relationLattice_le β E F]
  simp only [hz]
  have h := gibbsAffineReturnLaw_tendsto_resolved β E F
  exact ⟨fun ht => tendsto_nhds_unique h ht, fun he => he ▸ h⟩

/-- Continuity of a single stationary moment detects only the relations
visible at its own replica order. -/
theorem gibbsAffineReturnMoment_continuousAt_iff (β : ℝ) (E F : α → ℝ) (n : ℕ) :
    ContinuousAt (fun s => returnFidelityMoment (gibbsUnresolvedReturnLaw β (affineSpectrum E F s)) n)
        (0 : ℝ) ↔
      returnFidelityMoment (gibbsResolvedReturnLaw β E F) n =
        returnFidelityMoment (gibbsUnresolvedReturnLaw β E) n := by
  have hz : affineSpectrum E F 0 = E := by
    funext i
    simp only [affineSpectrum, zero_mul, add_zero]
  rw [continuousAt_iff_punctured_nhds]
  simp only [returnFidelityMoment_unresolved, returnFidelityMoment_resolved, hz]
  have h := gibbsAffinePlateau_tendsto_joint β E F n
  exact ⟨fun ht => tendsto_nhds_unique h ht, fun he => he ▸ h⟩

/-- Three levels suffice for the first decrease in the law's moments to
occur at any prescribed positive order. -/
theorem delayedThreeLevelReturnMoment_lt_iff (β : ℝ) (r n : ℕ) :
    returnFidelityMoment (gibbsResolvedReturnLaw β
          (delayedThreeLevelSpectrum (r + 1)) independentThreeLevelSpectrum) n <
        returnFidelityMoment (gibbsUnresolvedReturnLaw β (delayedThreeLevelSpectrum (r + 1))) n ↔
      r + 1 ≤ n := by
  rw [returnFidelityMoment_resolved_lt_iff]
  constructor
  · rintro ⟨k, hk, hkF, hh⟩
    have hk0 : k ≠ 0 := fun h => hkF (h.symm ▸ (projectiveSpectralRelationLattice _).zero_mem)
    exact (delayedThreeLevelRelation_height_lower_bound (r + 1) (Nat.succ_pos r) hk hk0).trans hh
  · intro hn
    refine ⟨delayedThreeLevelRelation (r + 1), delayedThreeLevelRelation_mem_relationLattice _, ?_, ?_⟩
    · rw [independentThreeLevel_projectiveRelationLattice_eq_bot, AddSubgroup.mem_bot]
      exact delayedThreeLevelRelation_ne_zero _
    · rwa [delayedThreeLevelRelation_positiveMass (r + 1) (Nat.succ_pos r)]

/-- No finite list of initial moments determines the effect of a splitting,
even with three levels and fixed temperature. -/
theorem threeLevelReturnLaws_agree_through_every_cutoff (β : ℝ) (r : ℕ) :
    let E := delayedThreeLevelSpectrum (r + 1)
    let L := gibbsResolvedReturnLaw β E independentThreeLevelSpectrum
    let U := gibbsUnresolvedReturnLaw β E
    (∀ n ≤ r, returnFidelityMoment L n = returnFidelityMoment U n) ∧ L ≠ U := by
  dsimp only
  constructor
  · intro n hn
    apply le_antisymm (returnFidelityMoment_resolved_le_unresolved _ _ _ _)
    apply le_of_not_gt
    intro hlt
    have hh := (delayedThreeLevelReturnMoment_lt_iff β r n).mp hlt
    exact (Nat.not_succ_le_self r) (hh.trans hn)
  · intro h
    have hlt := (delayedThreeLevelReturnMoment_lt_iff β r (r + 1)).mpr le_rfl
    rw [h] at hlt
    exact lt_irrefl _ hlt

/-- The first discontinuous observable moment can be delayed past any finite
cutoff even though the stationary return law already jumps. -/
theorem threeLevelAffineReturnLaw_moments_continuous_through_cutoff (β : ℝ) (r : ℕ) :
    let E := delayedThreeLevelSpectrum (r + 1)
    let F := independentThreeLevelSpectrum
    (∀ n ≤ r, ContinuousAt (fun s =>
      returnFidelityMoment (gibbsUnresolvedReturnLaw β (affineSpectrum E F s)) n) (0 : ℝ)) ∧
    ¬ ContinuousAt (fun s => gibbsUnresolvedReturnLaw β (affineSpectrum E F s)) (0 : ℝ) := by
  obtain ⟨hmom, hne⟩ := threeLevelReturnLaws_agree_through_every_cutoff β r
  exact ⟨fun n hn => (gibbsAffineReturnMoment_continuousAt_iff β _ _ n).mpr (hmom n hn),
    fun h => hne ((gibbsResolvedReturnLaw_eq_iff_relationLattice_le β _ _).mpr
      ((gibbsAffineReturnLaw_continuousAt_iff β _ _).mp h))⟩

#print axioms gibbsWindowReturnDistribution_tendsto_powerTimeReturnLimit
#print axioms gibbsPowerTimeReturnLimit_eq_unresolved
#print axioms gibbsPowerTimeReturnLimit_eq_resolved
#print axioms returnFidelityMoment_resolved_lt_iff
#print axioms gibbsResolvedReturnLaw_eq_iff_relationLattice_le
#print axioms gibbsWindowReturnDistribution_tendsto_unresolved
#print axioms gibbsAffineReturnLaw_tendsto_resolved
#print axioms gibbsAffineReturnLaw_continuousAt_iff
#print axioms threeLevelReturnLaws_agree_through_every_cutoff
#print axioms threeLevelAffineReturnLaw_moments_continuous_through_cutoff

end

end GaloisForLFunctions.HTGeometry.Thermofield
