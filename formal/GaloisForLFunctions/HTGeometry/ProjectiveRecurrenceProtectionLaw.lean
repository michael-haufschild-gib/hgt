import GaloisForLFunctions.HTGeometry.CountableSeparableInteractionOperatorLaw

/-!
# Exact protection law for projective recurrence

An exact projective recurrence relation is robust under a declared family of
spectral perturbations precisely when two independent conditions hold: it is
a relation of the unperturbed spectrum, and it annihilates every allowed
perturbation direction.

For perturbations constant on declared sectors, the annihilator has an exact
classification.  Push the integer character to the sector label space by
summing its coefficients inside each sector.  The recurrence relation is
protected exactly when this sector-charge profile vanishes.  Unrestricted
diagonal perturbations therefore protect no nonzero relation, whereas a
restricted symmetry sector protects exactly its invisible contrasts.
-/

open Set
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Detuning selected by one finitely supported projective character. -/
def projectiveCharacterDetuning
    {I : Type*} (k : ProjectiveCharacter I) (energy : I → ℝ) : ℝ :=
  ∑ i ∈ k.1.support, (k.1 i : ℝ) * energy i

/-- A character remains an exact relation after every allowed spectral
perturbation. -/
def RobustProjectiveRelation
    {I : Type*} (energy : I → ℝ) (allowed : Set (I → ℝ))
    (k : ProjectiveCharacter I) : Prop :=
  ∀ w ∈ allowed,
    projectiveCharacterDetuning k (fun i => energy i + w i) = 0

/-- Every allowed perturbation lies in the character's annihilating
hyperplane. -/
def PerturbationAnnihilatesProjectiveRelation
    {I : Type*} (allowed : Set (I → ℝ))
    (k : ProjectiveCharacter I) : Prop :=
  ∀ w ∈ allowed, projectiveCharacterDetuning k w = 0

theorem projectiveCharacterDetuning_add
    {I : Type*} (k : ProjectiveCharacter I)
    (left right : I → ℝ) :
    projectiveCharacterDetuning k (fun i => left i + right i) =
      projectiveCharacterDetuning k left +
        projectiveCharacterDetuning k right := by
  unfold projectiveCharacterDetuning
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- **Robustness factorization.**  When the allowed family contains the zero
perturbation, robust recurrence is exactly the intersection of the original
relation lattice with the annihilator of the perturbation family. -/
theorem robustProjectiveRelation_iff
    {I : Type*} (energy : I → ℝ) (allowed : Set (I → ℝ))
    (hzero : (0 : I → ℝ) ∈ allowed)
    (k : ProjectiveCharacter I) :
    RobustProjectiveRelation energy allowed k ↔
      projectiveCharacterDetuning k energy = 0 ∧
        PerturbationAnnihilatesProjectiveRelation allowed k := by
  constructor
  · intro h
    have hbase := h 0 hzero
    rw [projectiveCharacterDetuning_add] at hbase
    have hzeroDetuning :
        projectiveCharacterDetuning k (0 : I → ℝ) = 0 := by
      simp [projectiveCharacterDetuning]
    rw [hzeroDetuning, add_zero] at hbase
    refine ⟨hbase, ?_⟩
    intro w hw
    have htotal := h w hw
    rw [projectiveCharacterDetuning_add, hbase, zero_add] at htotal
    exact htotal
  · rintro ⟨hbase, hann⟩ w hw
    rw [projectiveCharacterDetuning_add, hbase, hann w hw, add_zero]

/-- **Unrestricted no-protection law.**  No nonzero exact projective
recurrence relation is robust under all diagonal spectral perturbations. -/
theorem no_nonzero_robustProjectiveRelation_under_unrestrictedPerturbations
    {I : Type*} (energy : I → ℝ) (k : ProjectiveCharacter I)
    (hrobust : RobustProjectiveRelation energy Set.univ k) :
    k = 0 := by
  classical
  have hann : PerturbationAnnihilatesProjectiveRelation Set.univ k :=
    ((robustProjectiveRelation_iff energy Set.univ (by simp) k).1 hrobust).2
  let coefficient : I → ℝ := fun i => (k.1 i : ℝ)
  have hsquares := hann coefficient (by simp)
  change ∑ i ∈ k.1.support, coefficient i * coefficient i = 0 at hsquares
  have hcoeff :=
    (Finset.sum_mul_self_eq_zero_iff k.1.support coefficient).1 hsquares
  apply Subtype.ext
  apply Finsupp.ext
  intro i
  by_cases hi : i ∈ k.1.support
  · have hi0 := hcoeff i hi
    have hi0' : (k.1 i : ℝ) = 0 := by
      simpa [coefficient] using hi0
    change k.1 i = 0
    exact_mod_cast hi0'
  · change k.1 i = 0
    simpa [Finsupp.mem_support_iff] using hi

/-- Perturbations that can shift each declared sector independently but are
constant inside every sector. -/
def sectorSymmetricPerturbations
    {I S : Type*} (sector : I → S) : Set (I → ℝ) :=
  {w | ∃ v : S → ℝ, w = v ∘ sector}

theorem zero_mem_sectorSymmetricPerturbations
    {I S : Type*} (sector : I → S) :
    (0 : I → ℝ) ∈ sectorSymmetricPerturbations sector := by
  refine ⟨0, ?_⟩
  rfl

/-- Detuning by a sector-symmetric perturbation is evaluation of the
character pushed to sector space. -/
theorem projectiveCharacterDetuning_comp_sector
    {I S : Type*} (sector : I → S)
    (k : ProjectiveCharacter I) (v : S → ℝ) :
    projectiveCharacterDetuning k (v ∘ sector) =
      (k.1.mapDomain sector).sum fun s q => (q : ℝ) * v s := by
  unfold projectiveCharacterDetuning
  rw [Finsupp.sum_mapDomain_index]
  · rfl
  · intro s
    simp
  · intro s a b
    push_cast
    ring

/-- A projective character annihilates every sector-symmetric perturbation
exactly when its total integer charge vanishes separately in every sector. -/
theorem sectorSymmetricPerturbations_annihilate_iff
    {I S : Type*} (sector : I → S)
    (k : ProjectiveCharacter I) :
    PerturbationAnnihilatesProjectiveRelation
        (sectorSymmetricPerturbations sector) k ↔
      k.1.mapDomain sector = 0 := by
  classical
  constructor
  · intro hann
    let charge : S → ℝ := fun s => ((k.1.mapDomain sector) s : ℝ)
    have hcharge := hann (charge ∘ sector) ⟨charge, rfl⟩
    rw [projectiveCharacterDetuning_comp_sector] at hcharge
    change (k.1.mapDomain sector).sum
      (fun s q => (q : ℝ) * charge s) = 0 at hcharge
    change ∑ s ∈ (k.1.mapDomain sector).support,
      charge s * charge s = 0 at hcharge
    have hz := (Finset.sum_mul_self_eq_zero_iff
      (k.1.mapDomain sector).support charge).1 hcharge
    apply Finsupp.ext
    intro s
    by_cases hs : s ∈ (k.1.mapDomain sector).support
    · have hs0 := hz s hs
      have hs0' : ((k.1.mapDomain sector) s : ℝ) = 0 := by
        simpa [charge] using hs0
      change (k.1.mapDomain sector) s = 0
      exact_mod_cast hs0'
    · change (k.1.mapDomain sector) s = 0
      simpa [Finsupp.mem_support_iff] using hs
  · intro hzero w hw
    obtain ⟨v, rfl⟩ := hw
    rw [projectiveCharacterDetuning_comp_sector, hzero]
    simp

/-- **Sector protection law.**  Under every perturbation respecting the
declared sector partition, the robust recurrence relations are exactly the
original spectral relations whose integer charge cancels inside every
sector. -/
theorem robustProjectiveRelation_sectorSymmetric_iff
    {I S : Type*} (energy : I → ℝ) (sector : I → S)
    (k : ProjectiveCharacter I) :
    RobustProjectiveRelation energy
        (sectorSymmetricPerturbations sector) k ↔
      projectiveCharacterDetuning k energy = 0 ∧
        k.1.mapDomain sector = 0 := by
  rw [robustProjectiveRelation_iff energy
    (sectorSymmetricPerturbations sector)
    (zero_mem_sectorSymmetricPerturbations sector),
    sectorSymmetricPerturbations_annihilate_iff]

end

end GaloisForLFunctions.HTGeometry
