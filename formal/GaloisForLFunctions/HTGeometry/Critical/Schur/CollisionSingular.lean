import GaloisForLFunctions.HTGeometry.CriticalFibreCollisionTangent
import GaloisForLFunctions.HTGeometry.Critical.Schur.ReducedSheetInvariance
import GaloisForLFunctions.HTGeometry.Critical.Schur.ValuationDVR

/-!
# Colliding sheets are singular points of the reduced fibre

Two distinct geometric sheets with the same reduced Schur fibre label have distinct integral fibre
points whose difference is divisible by a uniformizer, so the collision tangent construction
applies:

```text
C_uniformizer_dvd_of_map_residue_eq_zero
exists_reduced_tangent_of_reduction_eq
criticalSchur_exists_reduced_tangent_of_collision
    ** two colliding sheets produce a NONZERO low tangent at their common reduced state **
```

This is the bridge from the collision support to the singular locus of the reduced fibre: every
sheet involved in a collision reduces to a point where the critical Jacobian degenerates.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Polynomial IsLocalRing

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

/-- Collision tangent in residue form: over a discrete valuation ring, two distinct fibre points
with equal reductions produce a nonzero low tangent at the common reduced point. -/
theorem exists_reduced_tangent_of_reduction_eq {W : Type*} [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] {m n : ℕ} {P Q : W[X]}
    (p q : criticalFibre W m n P Q) (hne : p ≠ q)
    (hD : p.1.1.map (IsLocalRing.residue W) = q.1.1.map (IsLocalRing.residue W))
    (hE : p.1.2.map (IsLocalRing.residue W) = q.1.2.map (IsLocalRing.residue W)) :
    ∃ U V : (IsLocalRing.ResidueField W)[X],
      (U ≠ 0 ∨ V ≠ 0) ∧ U.degree < (m : ℕ) ∧ V.degree < (n : ℕ) ∧
      (X : (IsLocalRing.ResidueField W)[X]) ^ (m + n) ∣
        U * (p.1.2.map (IsLocalRing.residue W) + Q.map (IsLocalRing.residue W))
          + (p.1.1.map (IsLocalRing.residue W) + P.map (IsLocalRing.residue W)) * V := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W
  exact exists_reduced_tangent_of_congruent hπ p q hne
    (C_uniformizer_dvd_of_map_residue_eq_zero hπ (by rw [Polynomial.map_sub, hD, sub_self]))
    (C_uniformizer_dvd_of_map_residue_eq_zero hπ (by rw [Polynomial.map_sub, hE, sub_self]))

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
  -- the reduced label is the componentwise reduction of the integral fibre point, so equal labels
  -- are exactly two residue equalities
  have h := congrArg (fun z => z.1) hr
  exact exists_reduced_tangent_of_reduction_eq _ _
    (fun hpq => hne (criticalGeometricSheetToSchurFibre_injective K hm hn hpq))
    (congrArg Prod.fst h) (congrArg Prod.snd h)

end

end GaloisForLFunctions.HTGeometry
