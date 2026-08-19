import GaloisForLFunctions.HTGeometry.CriticalFibreCollisionTangent
import GaloisForLFunctions.HTGeometry.CriticalSchurReducedSheetInvariance
import GaloisForLFunctions.HTGeometry.CriticalSchurValuationDVR

/-!
# Colliding sheets are singular points of the reduced fibre

Two distinct geometric sheets with the same reduced Schur fibre label have distinct integral fibre
points whose difference is divisible by a uniformizer, so the collision tangent construction
applies:

```text
C_uniformizer_dvd_of_map_residue_eq_zero
criticalSchur_exists_reduced_tangent_of_collision
    ** two colliding sheets produce a NONZERO low tangent at their common reduced state **
```

This is the bridge from the collision support to the singular locus of the reduced fibre: every
sheet involved in a collision reduces to a point where the critical Jacobian degenerates.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Polynomial IsLocalRing

set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 400000

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}
variable (hm : 1 < m) (hn : 1 < n)

/-- A polynomial over a discrete valuation ring whose reduction vanishes is divisible by a
uniformizer. -/
theorem C_uniformizer_dvd_of_map_residue_eq_zero {W : Type*} [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] {π : W} (hπ : Irreducible π) {p : W[X]}
    (hp : p.map (IsLocalRing.residue W) = 0) :
    Polynomial.C π ∣ p := by
  rw [Polynomial.C_dvd_iff_dvd_coeff]
  intro i
  have hcoeff : IsLocalRing.residue W (p.coeff i) = 0 := by
    have := congrArg (fun q : (IsLocalRing.ResidueField W)[X] => q.coeff i) hp
    simpa [Polynomial.coeff_map] using this
  have hmem : p.coeff i ∈ IsLocalRing.maximalIdeal W :=
    (IsLocalRing.residue_eq_zero_iff _).mp hcoeff
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ,
    Ideal.mem_span_singleton] at hmem
  exact hmem

/-- **Two colliding sheets produce a nonzero low tangent at their common reduced state.** -/
theorem criticalSchur_exists_reduced_tangent_of_collision
    (σ τ : criticalGeometricSheet K m n) (hne : σ ≠ τ)
    (hr : criticalGeometricSheetToSchurReducedFibre K hm hn σ
        = criticalGeometricSheetToSchurReducedFibre K hm hn τ) :
    ∃ U V : (IsLocalRing.ResidueField
        (criticalNormalClosureSchurValuationSubring K (Nat.lt_of_succ_lt hm) (Nat.lt_of_succ_lt hn)))[X],
      (U ≠ 0 ∨ V ≠ 0) ∧ U.degree < (m : ℕ) ∧ V.degree < (n : ℕ) ∧
      (X : (IsLocalRing.ResidueField
          (criticalNormalClosureSchurValuationSubring K (Nat.lt_of_succ_lt hm) (Nat.lt_of_succ_lt hn)))[X]) ^ (m + n) ∣
        U * ((criticalGeometricSheetToSchurFibre K hm hn σ).1.2.map
              (IsLocalRing.residue (criticalNormalClosureSchurValuationSubring K (Nat.lt_of_succ_lt hm) (Nat.lt_of_succ_lt hn)))
            + (criticalNormalClosureSchurReciprocalTailIntegral K (Nat.lt_of_succ_lt hm) (Nat.lt_of_succ_lt hn)).map
              (IsLocalRing.residue (criticalNormalClosureSchurValuationSubring K (Nat.lt_of_succ_lt hm) (Nat.lt_of_succ_lt hn))))
          + ((criticalGeometricSheetToSchurFibre K hm hn σ).1.1.map
              (IsLocalRing.residue (criticalNormalClosureSchurValuationSubring K (Nat.lt_of_succ_lt hm) (Nat.lt_of_succ_lt hn)))
            + (criticalNormalClosureSchurRawTailIntegral K (Nat.lt_of_succ_lt hm) (Nat.lt_of_succ_lt hn)).map
              (IsLocalRing.residue (criticalNormalClosureSchurValuationSubring K (Nat.lt_of_succ_lt hm) (Nat.lt_of_succ_lt hn)))) * V := by
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible
    (criticalNormalClosureSchurValuationSubring K (Nat.lt_of_succ_lt hm) (Nat.lt_of_succ_lt hn))
  have hcomp : ∀ (a b : criticalGeometricSheet K m n),
      criticalGeometricSheetToSchurReducedFibre K hm hn a
        = criticalGeometricSheetToSchurReducedFibre K hm hn b →
      (criticalGeometricSheetToSchurFibre K hm hn a).1.1.map
          (IsLocalRing.residue (criticalNormalClosureSchurValuationSubring K (Nat.lt_of_succ_lt hm) (Nat.lt_of_succ_lt hn)))
        = (criticalGeometricSheetToSchurFibre K hm hn b).1.1.map
          (IsLocalRing.residue (criticalNormalClosureSchurValuationSubring K (Nat.lt_of_succ_lt hm) (Nat.lt_of_succ_lt hn)))
      ∧ (criticalGeometricSheetToSchurFibre K hm hn a).1.2.map
          (IsLocalRing.residue (criticalNormalClosureSchurValuationSubring K (Nat.lt_of_succ_lt hm) (Nat.lt_of_succ_lt hn)))
        = (criticalGeometricSheetToSchurFibre K hm hn b).1.2.map
          (IsLocalRing.residue (criticalNormalClosureSchurValuationSubring K (Nat.lt_of_succ_lt hm) (Nat.lt_of_succ_lt hn))) := by
    intro a b hab
    have h := congrArg (fun z => z.1) hab
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  obtain ⟨h1, h2⟩ := hcomp σ τ hr
  refine exists_reduced_tangent_of_congruent hπ
    (criticalGeometricSheetToSchurFibre K hm hn σ)
    (criticalGeometricSheetToSchurFibre K hm hn τ) ?_ ?_ ?_
  · intro hpq
    exact hne (criticalGeometricSheetToSchurFibre_injective K hm hn hpq)
  · refine C_uniformizer_dvd_of_map_residue_eq_zero hπ ?_
    rw [Polynomial.map_sub, h1, sub_self]
  · refine C_uniformizer_dvd_of_map_residue_eq_zero hπ ?_
    rw [Polynomial.map_sub, h2, sub_self]

end

end GaloisForLFunctions.HTGeometry
