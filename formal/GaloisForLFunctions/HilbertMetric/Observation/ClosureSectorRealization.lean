import GaloisForLFunctions.HilbertMetric.Observation.JointCommutantRecovery

/-!
# Canonical self-adjoint realization of observation dependencies

The Armstrong construction of Lemma 4.5 in arXiv:2610.33092 replaces any
finite observation family by natural-valued diagonal observations, with
one coordinate per dependency-closed label set. Every recovery statement
is preserved exactly. Thus complex observation values introduce no extra
finite dependency patterns beyond commuting self-adjoint matrices.
-/

namespace GaloisForLFunctions.HilbertMetric.Observation
open HTGeometry Matrix
noncomputable section

/-- Label sets already containing every observation they determine. -/
def ClosedObservationSets {m n : ℕ} (E : Fin m → Fin n → ℂ) :=
  {S : Set (Fin m) // determinedLabels E S = S}

instance {m n : ℕ} (E : Fin m → Fin n → ℂ) : Finite (ClosedObservationSets E) :=
  inferInstanceAs (Finite {S : Set (Fin m) // determinedLabels E S = S})

noncomputable instance {m n : ℕ} (E : Fin m → Fin n → ℂ) : Fintype (ClosedObservationSets E) :=
  Fintype.ofFinite _

private theorem determined_mono {m n : ℕ} (E : Fin m → Fin n → ℂ)
    {S T : Set (Fin m)} (h : S ⊆ T) : determinedLabels E S ⊆ determinedLabels E T :=
  fun _ hb i j hij => hb i j (fun a ha => hij a (h ha))

private def fullSector {m n : ℕ} (E : Fin m → Fin n → ℂ) : ClosedObservationSets E :=
  ⟨Set.univ, Set.Subset.antisymm (Set.subset_univ _) (subset_determinedLabels E _)⟩

private def closureSector {m n : ℕ} (E : Fin m → Fin n → ℂ)
    (S : Set (Fin m)) : ClosedObservationSets E :=
  ⟨determinedLabels E S, determinedLabels_idempotent E S⟩

/-- The closed label set assigned to a canonical coordinate. -/
def sectorLabels {m n : ℕ} (E : Fin m → Fin n → ℂ)
    (i : Fin (Fintype.card (ClosedObservationSets E))) : Set (Fin m) :=
  ((Fintype.equivFin (ClosedObservationSets E)).symm i).val

/-- Zero records membership; a distinct positive integer records each other sector. -/
def sectorObservation {m n : ℕ} (E : Fin m → Fin n → ℂ)
    (b : Fin m) (i : Fin (Fintype.card (ClosedObservationSets E))) : ℂ := by
  classical
  exact if b ∈ sectorLabels E i then 0 else ((i.val + 1 : ℕ) : ℂ)

private theorem sector_code_ne_zero {r : ℕ} (i : Fin r) : ((i.val + 1 : ℕ) : ℂ) ≠ 0 := by
  exact_mod_cast Nat.succ_ne_zero i.val

/-- Two distinct canonical sectors agree exactly on the intersection of their closed sets. -/
theorem sectorObservation_agreement_iff {m n : ℕ} (E : Fin m → Fin n → ℂ)
    (b : Fin m) (i j : Fin (Fintype.card (ClosedObservationSets E))) :
    sectorObservation E b i = sectorObservation E b j ↔
      i = j ∨ (b ∈ sectorLabels E i ∧ b ∈ sectorLabels E j) := by
  classical
  constructor
  · intro h
    by_cases hi : b ∈ sectorLabels E i
    · by_cases hj : b ∈ sectorLabels E j
      · exact Or.inr ⟨hi, hj⟩
      · simp only [sectorObservation, if_pos hi, if_neg hj] at h
        exact False.elim (sector_code_ne_zero j h.symm)
    · by_cases hj : b ∈ sectorLabels E j
      · simp only [sectorObservation, if_neg hi, if_pos hj] at h
        exact False.elim (sector_code_ne_zero i h)
      · simp only [sectorObservation, if_neg hi, if_neg hj] at h
        have hn : i.val + 1 = j.val + 1 := by exact_mod_cast h
        exact Or.inl (Fin.ext (Nat.add_right_cancel hn))
  · rintro (rfl | ⟨hi, hj⟩)
    · rfl
    · simp only [sectorObservation, if_pos hi, if_pos hj]

/-- No two canonical coordinates represent the same full observation row. -/
theorem sectorRows_injective {m n : ℕ} (E : Fin m → Fin n → ℂ) :
    Function.Injective (fun i => fun b => sectorObservation E b i) := by
  intro i j he
  by_contra hij
  have hm (b : Fin m) : b ∈ sectorLabels E i ∧ b ∈ sectorLabels E j :=
    ((sectorObservation_agreement_iff E b i j).mp (congrFun he b)).resolve_left hij
  have hs : sectorLabels E i = sectorLabels E j :=
    Set.ext fun b => ⟨fun _ => (hm b).2, fun _ => (hm b).1⟩
  have hc : (Fintype.equivFin (ClosedObservationSets E)).symm i =
      (Fintype.equivFin (ClosedObservationSets E)).symm j := Subtype.ext hs
  exact hij ((Fintype.equivFin (ClosedObservationSets E)).symm.injective hc)

/-- The canonical dimension is positive and at most exponential in the number of labels. -/
theorem sector_dimension_bounds {m n : ℕ} (E : Fin m → Fin n → ℂ) :
    0 < Fintype.card (ClosedObservationSets E) ∧
      Fintype.card (ClosedObservationSets E) ≤ 2 ^ m := by
  constructor
  · exact Nat.lt_of_le_of_lt (Nat.zero_le _)
      (Fintype.equivFin (ClosedObservationSets E) (fullSector E)).isLt
  · calc
      Fintype.card (ClosedObservationSets E) ≤ Fintype.card (Set (Fin m)) :=
        Fintype.card_le_of_injective (fun s : ClosedObservationSets E => s.val)
          Subtype.val_injective
      _ = 2 ^ m := by simp

/-- Canonical natural-valued observations preserve the whole dependency closure. -/
theorem sectorObservation_realizes {m n : ℕ} (E : Fin m → Fin n → ℂ)
    (S : Set (Fin m)) :
    determinedLabels (sectorObservation E) S = determinedLabels E S := by
  classical
  ext b
  constructor
  · intro hb
    let i := Fintype.equivFin (ClosedObservationSets E) (fullSector E)
    let j := Fintype.equivFin (ClosedObservationSets E) (closureSector E S)
    have hi : sectorLabels E i = Set.univ := by
      simp only [sectorLabels, i, Equiv.symm_apply_apply, fullSector]
    have hj : sectorLabels E j = determinedLabels E S := by
      simp only [sectorLabels, j, Equiv.symm_apply_apply, closureSector]
    have hagree (a : Fin m) (ha : a ∈ S) :
        sectorObservation E a i = sectorObservation E a j := by
      apply (sectorObservation_agreement_iff E a i j).mpr
      exact Or.inr ⟨by rw [hi]; trivial, by rw [hj]; exact subset_determinedLabels E S ha⟩
    have h := hb i j hagree
    by_contra hne
    have hbi : b ∈ sectorLabels E i := by rw [hi]; trivial
    have hbj : b ∉ sectorLabels E j := by rwa [hj]
    simp only [sectorObservation, if_pos hbi, if_neg hbj] at h
    exact sector_code_ne_zero j h.symm
  · intro hb i j hij
    by_cases he : i = j
    · rw [he]
    have hmem (a : Fin m) (ha : a ∈ S) :
        a ∈ sectorLabels E i ∧ a ∈ sectorLabels E j :=
      ((sectorObservation_agreement_iff E a i j).mp (hij a ha)).resolve_left he
    have hbi : b ∈ sectorLabels E i := by
      have h := determined_mono E (fun a ha => (hmem a ha).1) hb
      have hc : determinedLabels E (sectorLabels E i) = sectorLabels E i :=
        ((Fintype.equivFin (ClosedObservationSets E)).symm i).property
      rwa [hc] at h
    have hbj : b ∈ sectorLabels E j := by
      have h := determined_mono E (fun a ha => (hmem a ha).2) hb
      have hc : determinedLabels E (sectorLabels E j) = sectorLabels E j :=
        ((Fintype.equivFin (ClosedObservationSets E)).symm j).property
      rwa [hc] at h
    exact (sectorObservation_agreement_iff E b i j).mpr (Or.inr ⟨hbi, hbj⟩)

/-- The canonical realization is self-adjoint, with natural-number spectra. -/
theorem sectorObservation_isHermitian {m n : ℕ} (E : Fin m → Fin n → ℂ) (b : Fin m) :
    (diagonal (sectorObservation E b)).IsHermitian := by
  classical
  rw [Matrix.isHermitian_diagonal_iff]
  intro i
  unfold sectorObservation
  split_ifs <;> simp [IsSelfAdjoint]

/-- Every pair of canonical matrices commutes literally. -/
theorem sectorObservation_commute {m n : ℕ} (E : Fin m → Fin n → ℂ) (a b : Fin m) :
    diagonal (sectorObservation E a) * diagonal (sectorObservation E b) =
      diagonal (sectorObservation E b) * diagonal (sectorObservation E a) := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

/-- The original recovery question is an exact inclusion of canonical self-adjoint commutants. -/
theorem canonical_commutant_recovery {m n : ℕ} (E : Fin m → Fin n → ℂ)
    (S : Set (Fin m)) (b : Fin m) :
    jointCommutant (sectorObservation E) S ≤
      commutantSubmodule (diagonal (sectorObservation E b)) ↔ b ∈ determinedLabels E S := by
  rw [jointCommutant_le_iff, sectorObservation_realizes]

#print axioms sectorObservation_agreement_iff
#print axioms sectorRows_injective
#print axioms sector_dimension_bounds
#print axioms sectorObservation_realizes
#print axioms sectorObservation_isHermitian
#print axioms canonical_commutant_recovery
end
end GaloisForLFunctions.HilbertMetric.Observation
