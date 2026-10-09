import GaloisForLFunctions.HTGeometry.PaperDiscriminantRootUnits
import GaloisForLFunctions.HTGeometry.PaperLocallyNilpotentMultipliers

/-!
# All locally nilpotent derivations of the ordered discriminant complement

Every such derivation is a unique invariant multiple of common root
translation. Hence all nonzero terminating derivations have the same
kernel, all pairs commute, and sums remain locally nilpotent. These are
statements about all derivations of the localized ring, including ones
whose coefficients already have discriminant denominators.
-/

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
/-- The root-free coefficient algebra admits no nonzero relative derivation. -/
theorem paperDiscriminantZero_derivation_eq_zero
    (D : Derivation K (PaperRootDiscriminantOpen K 0) (PaperRootDiscriminantOpen K 0)) :
    D = 0 := by
  apply paperDiscriminantRoot_derivation_ext
  intro i
  exact Fin.elim0 i

/-- An arbitrary coefficient preserves termination exactly when common translation fixes it. -/
theorem paperDiscriminantTranslation_smul_locallyNilpotent_iff
    (n : ℕ) (q : PaperRootDiscriminantOpen K n) :
    IsLocallyNilpotent (q • paperDiscriminantTranslation K n) ↔
      paperDiscriminantTranslation K n q = 0 :=
  paperLND_smul_iff _ (paperDiscriminantTranslation_locallyNilpotent n) q

/-- Every locally nilpotent derivation is a unique invariant multiple of common translation. -/
theorem paperDiscriminantLND_classification (n : ℕ)
    (D : Derivation K (PaperRootDiscriminantOpen K (n + 1))
      (PaperRootDiscriminantOpen K (n + 1))) :
    IsLocallyNilpotent D ↔
      ∃! q : PaperRootDiscriminantOpen K (n + 1),
        paperDiscriminantTranslation K (n + 1) q = 0 ∧
          D = q • paperDiscriminantTranslation K (n + 1) := by
  constructor
  · intro hD
    let q := D (paperDiscriminantRoot (0 : Fin (n + 1)))
    have he : D = q • paperDiscriminantTranslation K (n + 1) := by
      apply paperDiscriminantRoot_derivation_ext
      intro i
      rw [Derivation.smul_apply, paperDiscriminantTranslation_root, smul_eq_mul, mul_one]
      exact paperDiscriminantRoot_lnd_values_eq D hD i 0
    have hq : paperDiscriminantTranslation K (n + 1) q = 0 := by
      apply (paperDiscriminantTranslation_smul_locallyNilpotent_iff (n + 1) q).mp
      rw [← he]
      exact hD
    refine ⟨q, ⟨hq, he⟩, ?_⟩
    intro r hr
    have hv := congrArg
      (fun E : Derivation K (PaperRootDiscriminantOpen K (n + 1))
        (PaperRootDiscriminantOpen K (n + 1)) => E (paperDiscriminantRoot 0)) hr.2
    simpa only [Derivation.smul_apply, paperDiscriminantTranslation_root,
      smul_eq_mul, mul_one] using hv.symm
  · rintro ⟨q, ⟨hq, rfl⟩, _⟩
    exact paperLND_invariant_smul _ (paperDiscriminantTranslation_locallyNilpotent _) q hq

/-- Every pair of locally nilpotent derivations on this root space commutes. -/
theorem paperDiscriminantLND_commute (n : ℕ)
    (D E : Derivation K (PaperRootDiscriminantOpen K (n + 1))
      (PaperRootDiscriminantOpen K (n + 1)))
    (hD : IsLocallyNilpotent D) (hE : IsLocallyNilpotent E) :
    Function.Commute (D : _ → _) (E : _ → _) := by
  obtain ⟨q, ⟨hq, rfl⟩, _⟩ := (paperDiscriminantLND_classification n D).mp hD
  obtain ⟨r, ⟨hr, rfl⟩, _⟩ := (paperDiscriminantLND_classification n E).mp hE
  intro a
  simp only [Derivation.smul_apply, smul_eq_mul, Derivation.leibniz, hq, hr,
    mul_zero, add_zero]
  ring

/-- The sum of any two locally nilpotent derivations on this root space is locally nilpotent. -/
theorem paperDiscriminantLND_add (n : ℕ)
    (D E : Derivation K (PaperRootDiscriminantOpen K (n + 1))
      (PaperRootDiscriminantOpen K (n + 1)))
    (hD : IsLocallyNilpotent D) (hE : IsLocallyNilpotent E) :
    IsLocallyNilpotent (D + E) := by
  obtain ⟨q, ⟨hq, rfl⟩, _⟩ := (paperDiscriminantLND_classification n D).mp hD
  obtain ⟨r, ⟨hr, rfl⟩, _⟩ := (paperDiscriminantLND_classification n E).mp hE
  rw [← add_smul]
  apply paperLND_invariant_smul _ (paperDiscriminantTranslation_locallyNilpotent _)
  rw [map_add, hq, hr, add_zero]

/-- All nonzero locally nilpotent derivations have precisely the common-translation kernel. -/
theorem paperDiscriminantLND_kernel_rigidity (n : ℕ)
    (D : Derivation K (PaperRootDiscriminantOpen K (n + 1))
      (PaperRootDiscriminantOpen K (n + 1))) (hD : IsLocallyNilpotent D) :
    D = 0 ∨ ∀ a, D a = 0 ↔ paperDiscriminantTranslation K (n + 1) a = 0 := by
  obtain ⟨q, ⟨_, rfl⟩, _⟩ := (paperDiscriminantLND_classification n D).mp hD
  by_cases hq : q = 0
  · left
    simp [hq]
  · right
    intro a
    simp only [Derivation.smul_apply, smul_eq_mul, mul_eq_zero, hq, false_or]

/-- Universal invariants of all terminating derivations are exactly translation constants. -/
theorem paperDiscriminantLND_universal_invariants_iff (n : ℕ)
    (a : PaperRootDiscriminantOpen K (n + 1)) :
    (∀ D : Derivation K (PaperRootDiscriminantOpen K (n + 1))
      (PaperRootDiscriminantOpen K (n + 1)), IsLocallyNilpotent D → D a = 0) ↔
        paperDiscriminantTranslation K (n + 1) a = 0 := by
  constructor
  · intro h
    exact h _ (paperDiscriminantTranslation_locallyNilpotent (n + 1))
  · intro ha D hD
    obtain ⟨q, ⟨_, rfl⟩, _⟩ := (paperDiscriminantLND_classification n D).mp hD
    rw [Derivation.smul_apply, ha, smul_zero]

end

end GaloisForLFunctions.HTGeometry
