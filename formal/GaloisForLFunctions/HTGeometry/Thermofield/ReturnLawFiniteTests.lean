import GaloisForLFunctions.HTGeometry.Thermofield.ReturnLawResolution
import GaloisForLFunctions.HTGeometry.ReplicaOperatorCovarianceCrowdingLaw
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Finite tests of thermofield return-law stability

The balanced integer relation lattice of a finite spectrum is finitely
generated. A single replica moment at or above the heights of its generators
tests preservation of the full stationary return law.
-/

open Filter MeasureTheory Set Topology _root_.HTGeometry

namespace GaloisForLFunctions.HTGeometry.Thermofield

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

omit [DecidableEq α] [Nonempty α] in
/-- A finite list of integral relations tests preservation of every coarse relation. -/
theorem exists_gibbsReturnRelationTests (E : α → ℝ) :
    ∃ S : Finset (α → ℤ), (∀ k ∈ S, k ∈ projectiveSpectralRelationLattice E) ∧
      ∀ F : α → ℝ, (projectiveSpectralRelationLattice E ≤ projectiveSpectralRelationLattice F) ↔
        ∀ k ∈ S, finiteTorusCharacterDetuning k F = 0 := by
  classical
  let L := projectiveSpectralRelationLattice E
  obtain ⟨S, hS⟩ := IsNoetherian.noetherian L.toIntSubmodule
  have hmem (k : α → ℤ) (hk : k ∈ S) : k ∈ L := by
    change k ∈ L.toIntSubmodule
    rw [← hS]
    exact Submodule.subset_span hk
  refine ⟨S, hmem, fun F => ⟨?_, ?_⟩⟩
  · intro h k hk
    exact ((mem_projectiveSpectralRelationLattice_iff F k).mp (h (hmem k hk))).2
  · intro h
    change L.toIntSubmodule ≤ (projectiveSpectralRelationLattice F).toIntSubmodule
    rw [← hS]
    apply Submodule.span_le.mpr
    intro k hk
    exact (mem_projectiveSpectralRelationLattice_iff F k).mpr
      ⟨((mem_projectiveSpectralRelationLattice_iff E k).mp (hmem k hk)).1, h k hk⟩

/-- At any order above a spectrum-dependent cutoff, equality of that single
moment is equivalent to preservation of the entire return law. -/
theorem exists_gibbsReturnLaw_moment_cutoff (E : α → ℝ) :
    ∃ N : ℕ, ∀ (β : ℝ) (F : α → ℝ) (n : ℕ), N ≤ n →
      (returnFidelityMoment (gibbsResolvedReturnLaw β E F) n =
        returnFidelityMoment (gibbsUnresolvedReturnLaw β E) n ↔
        gibbsResolvedReturnLaw β E F = gibbsUnresolvedReturnLaw β E) := by
  classical
  obtain ⟨S, hmem, htests⟩ := exists_gibbsReturnRelationTests E
  refine ⟨S.sup spectralCharacterPositiveMass, fun β F n hn => ⟨?_, ?_⟩⟩
  · intro heq
    apply (gibbsResolvedReturnLaw_eq_iff_relationLattice_le β E F).mpr
    apply (htests F).mpr
    intro k hk
    by_contra hdet
    have hkF : k ∉ projectiveSpectralRelationLattice F :=
      fun h => hdet ((mem_projectiveSpectralRelationLattice_iff F k).mp h).2
    have hheight : spectralCharacterPositiveMass k ≤ n :=
      (Finset.le_sup (f := spectralCharacterPositiveMass) hk).trans hn
    have hlt := (returnFidelityMoment_resolved_lt_iff β E F n).mpr ⟨k, hmem k hk, hkF, hheight⟩
    rw [heq] at hlt
    exact lt_irrefl _ hlt
  · intro heq
    rw [heq]

/-- One sufficiently high stationary moment tests continuity of the full
law at zero splitting. The order is independent of temperature and fine spectrum. -/
theorem exists_gibbsAffineReturnLaw_continuity_cutoff (E : α → ℝ) :
    ∃ N : ℕ, ∀ (β : ℝ) (F : α → ℝ) (n : ℕ), N ≤ n →
      (ContinuousAt (fun s => returnFidelityMoment (gibbsUnresolvedReturnLaw β (affineSpectrum E F s)) n)
          (0 : ℝ) ↔
        ContinuousAt (fun s => gibbsUnresolvedReturnLaw β (affineSpectrum E F s)) (0 : ℝ)) := by
  obtain ⟨N, hN⟩ := exists_gibbsReturnLaw_moment_cutoff E
  refine ⟨N, fun β F n hn => ?_⟩
  rw [gibbsAffineReturnMoment_continuousAt_iff, hN β F n hn,
    gibbsResolvedReturnLaw_eq_iff_relationLattice_le, gibbsAffineReturnLaw_continuousAt_iff]

private def relationDetuning (k : α → ℤ) : (α → ℝ) →ₗ[ℝ] ℝ where
  toFun := finiteTorusCharacterDetuning k
  map_add' F G := by
    simp only [finiteTorusCharacterDetuning, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c F := by
    simp only [RingHom.id_apply, finiteTorusCharacterDetuning, Pi.smul_apply,
      smul_eq_mul, Finset.mul_sum, mul_left_comm]

/-- Perturbations that preserve every relation form a real linear subspace. -/
def returnLawStablePerturbations (E : α → ℝ) : Submodule ℝ (α → ℝ) :=
  ⨅ k : projectiveSpectralRelationLattice E, (relationDetuning k.val).ker

omit [DecidableEq α] [Nonempty α] in
theorem mem_returnLawStablePerturbations_iff (E F : α → ℝ) :
    F ∈ returnLawStablePerturbations E ↔
      projectiveSpectralRelationLattice E ≤ projectiveSpectralRelationLattice F := by
  rw [returnLawStablePerturbations, Submodule.mem_iInf]
  constructor
  · intro h k hk
    exact (mem_projectiveSpectralRelationLattice_iff F k).mpr
      ⟨((mem_projectiveSpectralRelationLattice_iff E k).mp hk).1, LinearMap.mem_ker.mp (h ⟨k, hk⟩)⟩
  · intro h k
    exact LinearMap.mem_ker.mpr (((mem_projectiveSpectralRelationLattice_iff F k.val).mp (h k.property)).2)

theorem gibbsAffineReturnLaw_continuousAt_iff_mem_stablePerturbations (β : ℝ) (E F : α → ℝ) :
    ContinuousAt (fun s => gibbsUnresolvedReturnLaw β (affineSpectrum E F s)) (0 : ℝ) ↔
      F ∈ returnLawStablePerturbations E :=
  (gibbsAffineReturnLaw_continuousAt_iff β E F).trans (mem_returnLawStablePerturbations_iff E F).symm

omit [DecidableEq α] [Nonempty α] in
theorem isClosed_returnLawStablePerturbations (E : α → ℝ) :
    IsClosed (returnLawStablePerturbations E : Set (α → ℝ)) := by
  rw [returnLawStablePerturbations, Submodule.coe_iInf]
  apply isClosed_iInter
  intro k
  change IsClosed {F : α → ℝ | finiteTorusCharacterDetuning k.val F = 0}
  apply isClosed_eq _ continuous_const
  unfold finiteTorusCharacterDetuning
  exact continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i)

omit [DecidableEq α] [Nonempty α] in
/-- The whole perturbation space is stable exactly when there is no nonzero coarse relation. -/
theorem returnLawStablePerturbations_eq_top_iff (E : α → ℝ) :
    returnLawStablePerturbations E = ⊤ ↔ projectiveSpectralRelationLattice E = ⊥ := by
  classical
  constructor
  · intro htop
    apply le_antisymm _ bot_le
    intro k hk
    rw [AddSubgroup.mem_bot]
    funext i
    let F (j : α) : ℝ := if j = i then 1 else 0
    have hF : F ∈ returnLawStablePerturbations E := by rw [htop]; exact Submodule.mem_top
    have h := (mem_returnLawStablePerturbations_iff E F).mp hF hk
    have hdet := ((mem_projectiveSpectralRelationLattice_iff F k).mp h).2
    have hz : (k i : ℝ) = 0 := by
      simpa only [finiteTorusCharacterDetuning, F, mul_ite, mul_zero, mul_one,
        Finset.sum_ite_eq', Finset.mem_univ, if_true] using hdet
    exact_mod_cast hz
  · intro hbot
    apply Submodule.eq_top_iff'.mpr
    intro F
    exact (mem_returnLawStablePerturbations_iff E F).mpr (by rw [hbot]; exact bot_le)

/-- A nontrivial coarse relation makes stability exceptional. The preserving
perturbations have measure zero, and the law-changing perturbations are open and dense. -/
theorem gibbsAffineReturnLaw_generic_instability (β : ℝ) (E : α → ℝ) :
    projectiveSpectralRelationLattice E ≠ ⊥ →
      let S := {F : α → ℝ |
        ContinuousAt (fun s => gibbsUnresolvedReturnLaw β (affineSpectrum E F s)) (0 : ℝ)}
      volume S = 0 ∧ IsOpen Sᶜ ∧ Dense Sᶜ := by
  intro h
  dsimp only
  have hset : {F : α → ℝ |
      ContinuousAt (fun s => gibbsUnresolvedReturnLaw β (affineSpectrum E F s)) (0 : ℝ)} =
        (returnLawStablePerturbations E : Set (α → ℝ)) :=
    Set.ext fun F => gibbsAffineReturnLaw_continuousAt_iff_mem_stablePerturbations β E F
  rw [hset]
  have hproper : returnLawStablePerturbations E ≠ ⊤ :=
    fun ht => h ((returnLawStablePerturbations_eq_top_iff E).mp ht)
  have hzero := addHaar_submodule (volume : Measure (α → ℝ)) (returnLawStablePerturbations E) hproper
  refine ⟨hzero, (isClosed_returnLawStablePerturbations E).isOpen_compl, ?_⟩
  apply interior_eq_empty_iff_dense_compl.mp
  by_contra hne
  have hpos := isOpen_interior.measure_pos (μ := (volume : Measure (α → ℝ))) (Set.nonempty_iff_ne_empty.mpr hne)
  exact (ne_of_gt hpos) (measure_mono_null interior_subset hzero)

/-- Equality of an individual moment is equivalent to preserving all
coarse replica collisions at that order. -/
theorem returnFidelityMoment_eq_iff_preserves_replicas (β : ℝ) (E F : α → ℝ) (n : ℕ) :
    returnFidelityMoment (gibbsResolvedReturnLaw β E F) n =
        returnFidelityMoment (gibbsUnresolvedReturnLaw β E) n ↔
      ∀ p ∈ Finset.univ.piAntidiag n, ∀ q ∈ Finset.univ.piAntidiag n,
        replicaMultiplicityEnergy E p = replicaMultiplicityEnergy E q →
          replicaMultiplicityEnergy F p = replicaMultiplicityEnergy F q := by
  rw [returnFidelityMoment_resolved, returnFidelityMoment_unresolved]
  obtain ⟨hle, hlt⟩ := gibbsJointCollision_le_and_lt_iff β E F n
  constructor
  · intro heq p hp q hq hE
    by_contra hF
    have hs := hlt.mpr ⟨p, hp, q, hq, hE, hF⟩
    rw [heq] at hs
    exact lt_irrefl _ hs
  · intro hp
    apply le_antisymm hle
    apply le_of_not_gt
    intro hs
    obtain ⟨p, hp', q, hq, hE, hF⟩ := hlt.mp hs
    exact hF (hp p hp' q hq hE)

/-- An affine function of the coarse energies preserves the full return law. -/
theorem gibbsResolvedReturnLaw_affine_equivalent (β : ℝ) (E : α → ℝ) (a b : ℝ) :
    gibbsResolvedReturnLaw β E (fun i => a + b * E i) = gibbsUnresolvedReturnLaw β E := by
  apply (gibbsResolvedReturnLaw_eq_iff_relationLattice_le β E _).mpr
  intro k hk
  obtain ⟨hbal, hE⟩ := (mem_projectiveSpectralRelationLattice_iff E k).mp hk
  have hbal' : ∑ i, (k i : ℝ) = 0 := by
    change (∑ i, k i) = 0 at hbal
    exact_mod_cast hbal
  apply (mem_projectiveSpectralRelationLattice_iff _ k).mpr
  refine ⟨hbal, ?_⟩
  calc
    _ = a * (∑ i, (k i : ℝ)) + b * finiteTorusCharacterDetuning k E := by
      unfold finiteTorusCharacterDetuning
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    _ = 0 := by rw [hbal', hE, mul_zero, mul_zero, add_zero]

omit [Nonempty α] in
private theorem twoReplica_mem (i j : α) :
    replicaOneHot i + replicaOneHot j ∈ Finset.univ.piAntidiag 2 := by
  refine Finset.mem_piAntidiag.mpr ⟨?_, fun _ _ => Finset.mem_univ _⟩
  simp [replicaOneHot, Pi.add_apply, Finset.sum_add_distrib]

omit [Nonempty α] in
private theorem twoReplica_energy (E : α → ℝ) (i j : α) :
    replicaMultiplicityEnergy E (replicaOneHot i + replicaOneHot j) = E i + E j := by
  have h : replicaMultiplicityEnergy E (replicaOneHot i + replicaOneHot j) =
      replicaMultiplicityEnergy E (replicaOneHot i) + replicaMultiplicityEnergy E (replicaOneHot j) := by
    simp only [replicaMultiplicityEnergy, Pi.add_apply, Nat.cast_add, add_mul, Finset.sum_add_distrib]
  rw [h, replicaMultiplicityEnergy_oneHot, replicaMultiplicityEnergy_oneHot]

/-- On an arithmetic progression of levels the second moment decides the
whole law. The preserving perturbations are exactly affine functions of the levels. -/
theorem equispacedReturnSecondMoment_eq_iff_affine (β e ω : ℝ) (d : ℕ) (F : Fin (d + 2) → ℝ) :
    let E := fun i : Fin (d + 2) => e + ω * (i.val : ℝ)
    returnFidelityMoment (gibbsResolvedReturnLaw β E F) 2 =
      returnFidelityMoment (gibbsUnresolvedReturnLaw β E) 2 ↔
      ∃ a b : ℝ, ∀ i, F i = a + b * E i := by
  let E := fun i : Fin (d + 2) => e + ω * (i.val : ℝ)
  change returnFidelityMoment (gibbsResolvedReturnLaw β E F) 2 =
      returnFidelityMoment (gibbsUnresolvedReturnLaw β E) 2 ↔
      ∃ a b : ℝ, ∀ i, F i = a + b * E i
  constructor
  · intro h
    have hpres := (returnFidelityMoment_eq_iff_preserves_replicas β E F 2).mp h
    have hpair (i j k l : Fin (d + 2)) (he : E i + E j = E k + E l) : F i + F j = F k + F l := by
      have he' : replicaMultiplicityEnergy E (replicaOneHot i + replicaOneHot j) =
          replicaMultiplicityEnergy E (replicaOneHot k + replicaOneHot l) := by
        simpa only [twoReplica_energy] using he
      simpa only [twoReplica_energy] using hpres _ (twoReplica_mem i j) _ (twoReplica_mem k l) he'
    by_cases hω : ω = 0
    · refine ⟨F 0, 0, fun i => ?_⟩
      have hf := hpair i 0 0 0 (by simp [E, hω])
      simp only [zero_mul, add_zero]
      linarith only [hf]
    · let m := F 1 - F 0
      have hrec (i : Fin (d + 1)) : F 0 + F i.succ = F 1 + F i.castSucc := by
        apply hpair
        simp only [E, Fin.val_zero, Fin.val_one, Fin.val_succ, Fin.val_castSucc,
          Nat.cast_zero, Nat.cast_one, Nat.cast_add]
        ring
      have hf (i : Fin (d + 2)) : F i = F 0 + m * (i.val : ℝ) := by
        refine Fin.induction ?_ ?_ i
        · simp
        · intro i ih
          dsimp only [m] at ih ⊢
          simp only [Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one] at ih ⊢
          linear_combination ih + hrec i
      refine ⟨F 0 - m / ω * e, m / ω, fun i => ?_⟩
      rw [hf i]
      dsimp only [E]
      field_simp
      ring
  · rintro ⟨a, b, h⟩
    have he : F = fun i => a + b * E i := funext h
    rw [he, gibbsResolvedReturnLaw_affine_equivalent]

/-- On equally spaced coarse levels, a second-moment test decides continuity
of the full weak return law at zero splitting. -/
theorem equispacedAffineReturnLaw_continuousAt_iff_affine (β e ω : ℝ) (d : ℕ) (F : Fin (d + 2) → ℝ) :
    let E := fun i : Fin (d + 2) => e + ω * (i.val : ℝ)
    ContinuousAt (fun s => gibbsUnresolvedReturnLaw β (affineSpectrum E F s)) (0 : ℝ) ↔
      ∃ a b : ℝ, ∀ i, F i = a + b * E i := by
  dsimp only
  rw [gibbsAffineReturnLaw_continuousAt_iff, ← gibbsResolvedReturnLaw_eq_iff_relationLattice_le]
  constructor
  · intro h
    apply (equispacedReturnSecondMoment_eq_iff_affine β e ω d F).mp
    exact congrArg (fun law => returnFidelityMoment law 2) h
  · rintro ⟨a, b, h⟩
    rw [funext h, gibbsResolvedReturnLaw_affine_equivalent]

#print axioms exists_gibbsReturnRelationTests
#print axioms exists_gibbsReturnLaw_moment_cutoff
#print axioms exists_gibbsAffineReturnLaw_continuity_cutoff
#print axioms gibbsAffineReturnLaw_generic_instability
#print axioms equispacedReturnSecondMoment_eq_iff_affine
#print axioms equispacedAffineReturnLaw_continuousAt_iff_affine

end

end GaloisForLFunctions.HTGeometry.Thermofield
