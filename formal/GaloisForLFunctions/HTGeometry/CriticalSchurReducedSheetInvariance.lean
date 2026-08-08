import GaloisForLFunctions.HTGeometry.CriticalSchurIntegralInertia

/-!
# Actual reduced Schur sheet labels are inertia invariant

Coefficientwise residue invariance upgrades to equality of the two polynomial blocks and hence to
equality in the actual reduced critical fibre.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

/-- Raw low polynomial underlying the actual reduced Schur sheet label. -/
theorem criticalGeometricSheetToSchurReducedFibre_raw
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 1 < m) (hn : 1 < n)
    (σ : criticalGeometricSheet K m n) :
    (criticalGeometricSheetToSchurReducedFibre K hm hn σ).1.1 =
      (criticalGeometricSheetToSchurFibre K hm hn σ).1.1.map
        (IsLocalRing.residue
          (criticalNormalClosureSchurValuationSubring K
            (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn))) := rfl

/-- Reciprocal low polynomial underlying the actual reduced Schur sheet label. -/
theorem criticalGeometricSheetToSchurReducedFibre_recip
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 1 < m) (hn : 1 < n)
    (σ : criticalGeometricSheet K m n) :
    (criticalGeometricSheetToSchurReducedFibre K hm hn σ).1.2 =
      (criticalGeometricSheetToSchurFibre K hm hn σ).1.2.map
        (IsLocalRing.residue
          (criticalNormalClosureSchurValuationSubring K
            (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn))) := rfl

/-- The residue-mapped raw low polynomial is fixed by actual Schur inertia. -/
theorem criticalGeometricSheetToSchurFibre_raw_map_residue_inertia
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 1 < m) (hn : 1 < n)
    (g : criticalSchurInertiaGroup K
      (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn))
    (σ : criticalGeometricSheet K m n) :
    (criticalGeometricSheetToSchurFibre K hm hn
        (criticalSchurInertiaAction K
          (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) g σ)).1.1.map
        (IsLocalRing.residue
          (criticalNormalClosureSchurValuationSubring K
            (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn))) =
      (criticalGeometricSheetToSchurFibre K hm hn σ).1.1.map
        (IsLocalRing.residue
          (criticalNormalClosureSchurValuationSubring K
            (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn))) := by
  let ε := IsLocalRing.residue
    (criticalNormalClosureSchurValuationSubring K
      (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn))
  apply Polynomial.ext
  intro k
  calc
    _ = ε ((criticalGeometricSheetToSchurFibre K hm hn
        (criticalSchurInertiaAction K
          (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) g σ)).1.1.coeff k) :=
      Polynomial.coeff_map ε k
    _ = ε ((criticalGeometricSheetToSchurFibre K hm hn σ).1.1.coeff k) := by
      by_cases hk : k < m
      · exact criticalGeometricSheetToSchurFibre_rawCoeff_residue_inertia
          K hm hn g σ ⟨k, hk⟩
      · have hmk : m ≤ k := Nat.le_of_not_gt hk
        have hleft : (criticalGeometricSheetToSchurFibre K hm hn
            (criticalSchurInertiaAction K
              (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) g σ)).1.1.coeff k = 0 :=
          Polynomial.coeff_eq_zero_of_degree_lt
            (lt_of_lt_of_le
              (criticalGeometricSheetToSchurFibre K hm hn
                (criticalSchurInertiaAction K
                  (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) g σ)).2.1
              (by exact_mod_cast hmk))
        have hright :
            (criticalGeometricSheetToSchurFibre K hm hn σ).1.1.coeff k = 0 :=
          Polynomial.coeff_eq_zero_of_degree_lt
            (lt_of_lt_of_le
              (criticalGeometricSheetToSchurFibre K hm hn σ).2.1
              (by exact_mod_cast hmk))
        exact congrArg (fun a => ε a) (hleft.trans hright.symm)
    _ = _ := (Polynomial.coeff_map ε k).symm

/-- The residue-mapped reciprocal low polynomial is fixed by actual Schur inertia. -/
theorem criticalGeometricSheetToSchurFibre_recip_map_residue_inertia
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 1 < m) (hn : 1 < n)
    (g : criticalSchurInertiaGroup K
      (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn))
    (σ : criticalGeometricSheet K m n) :
    (criticalGeometricSheetToSchurFibre K hm hn
        (criticalSchurInertiaAction K
          (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) g σ)).1.2.map
        (IsLocalRing.residue
          (criticalNormalClosureSchurValuationSubring K
            (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn))) =
      (criticalGeometricSheetToSchurFibre K hm hn σ).1.2.map
        (IsLocalRing.residue
          (criticalNormalClosureSchurValuationSubring K
            (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn))) := by
  let ε := IsLocalRing.residue
    (criticalNormalClosureSchurValuationSubring K
      (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn))
  apply Polynomial.ext
  intro k
  calc
    _ = ε ((criticalGeometricSheetToSchurFibre K hm hn
        (criticalSchurInertiaAction K
          (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) g σ)).1.2.coeff k) :=
      Polynomial.coeff_map ε k
    _ = ε ((criticalGeometricSheetToSchurFibre K hm hn σ).1.2.coeff k) := by
      by_cases hk : k < n
      · exact criticalGeometricSheetToSchurFibre_recipCoeff_residue_inertia
          K hm hn g σ ⟨k, hk⟩
      · have hnk : n ≤ k := Nat.le_of_not_gt hk
        have hleft : (criticalGeometricSheetToSchurFibre K hm hn
            (criticalSchurInertiaAction K
              (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) g σ)).1.2.coeff k = 0 :=
          Polynomial.coeff_eq_zero_of_degree_lt
            (lt_of_lt_of_le
              (criticalGeometricSheetToSchurFibre K hm hn
                (criticalSchurInertiaAction K
                  (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) g σ)).2.2.1
              (by exact_mod_cast hnk))
        have hright :
            (criticalGeometricSheetToSchurFibre K hm hn σ).1.2.coeff k = 0 :=
          Polynomial.coeff_eq_zero_of_degree_lt
            (lt_of_lt_of_le
              (criticalGeometricSheetToSchurFibre K hm hn σ).2.2.1
              (by exact_mod_cast hnk))
        exact congrArg (fun a => ε a) (hleft.trans hright.symm)
    _ = _ := (Polynomial.coeff_map ε k).symm

/-- Every actual Schur inertia element fixes the actual reduced residue-fibre sheet label. -/
theorem criticalGeometricSheetToSchurReducedFibre_inertia_invariant
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 1 < m) (hn : 1 < n)
    (g : criticalSchurInertiaGroup K
      (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn))
    (σ : criticalGeometricSheet K m n) :
    criticalGeometricSheetToSchurReducedFibre K hm hn
        (criticalSchurInertiaAction K
          (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) g σ) =
      criticalGeometricSheetToSchurReducedFibre K hm hn σ := by
  apply Subtype.ext
  exact Prod.ext
    ((criticalGeometricSheetToSchurReducedFibre_raw K hm hn
        (criticalSchurInertiaAction K
          (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) g σ)).trans
      ((criticalGeometricSheetToSchurFibre_raw_map_residue_inertia
        K hm hn g σ).trans
        (criticalGeometricSheetToSchurReducedFibre_raw K hm hn σ).symm))
    ((criticalGeometricSheetToSchurReducedFibre_recip K hm hn
        (criticalSchurInertiaAction K
          (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) g σ)).trans
      ((criticalGeometricSheetToSchurFibre_recip_map_residue_inertia
        K hm hn g σ).trans
        (criticalGeometricSheetToSchurReducedFibre_recip K hm hn σ).symm))

end

end GaloisForLFunctions.HTGeometry
