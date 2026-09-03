import GaloisForLFunctions.HTGeometry.IdealInertiaConjugation
import GaloisForLFunctions.HTGeometry.ValuationSubringCentreTransport
import GaloisForLFunctions.HTGeometry.CriticalBlockConjugateInertia

/-!
# Block fields are unramified at every Schur valuation

Galois transitivity carries the chosen Schur valuation to every valuation above the same base
place.  Centre-prime transport and ideal-inertia conjugation then identify every local inertia
group with a conjugate of chosen inertia.  Since all those conjugates preserve a non-singleton
monodromy block, its fixed field has ramification index one at every such valuation.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Pointwise

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 2000000

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}
variable [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]

noncomputable local instance : DecidableEq (criticalGeometricSheet K m n) :=
  Classical.decEq _

/-- Inertia at every valuation above the Schur place lies in a non-singleton block stabilizer. -/
theorem criticalAllSchur_inertia_le_blockStabilizer [DecidableEq K]
    (hm : 1 < m) (hn : 1 < n)
    {B : Set (criticalGeometricSheet K m n)}
    (hB : MulAction.IsBlock (criticalGeometricMonodromy K m n) B)
    (hB2 : ∃ x ∈ B, ∃ y ∈ B, x ≠ y)
    (W : ValuationSubring (criticalNormalClosure K m n))
    (hW : W ≠ ⊤)
    (hRW : ∀ r : CriticalSchurNormalBaseRing K (Nat.zero_lt_of_lt hm)
      (Nat.zero_lt_of_lt hn),
      algebraMap (CriticalSchurNormalBaseRing K (Nat.zero_lt_of_lt hm)
        (Nat.zero_lt_of_lt hn)) (criticalNormalClosure K m n) r ∈ W)
    (hcent : ∀ r : CriticalSchurNormalBaseRing K (Nat.zero_lt_of_lt hm)
      (Nat.zero_lt_of_lt hn),
      (¬ IsUnit (⟨algebraMap (CriticalSchurNormalBaseRing K (Nat.zero_lt_of_lt hm)
        (Nat.zero_lt_of_lt hn)) (criticalNormalClosure K m n) r, hRW r⟩ : W)) ↔
        r ∈ IsLocalRing.maximalIdeal
          (CriticalSchurNormalBaseRing K (Nat.zero_lt_of_lt hm)
            (Nat.zero_lt_of_lt hn))) :
    ∀ g : W.inertiaSubgroup (criticalObservationField K m n),
      (g : criticalNormalClosure K m n ≃ₐ[criticalObservationField K m n]
        criticalNormalClosure K m n) ∈ criticalBlockStabilizer K B := by
  let hm0 := Nat.zero_lt_of_lt hm
  let hn0 := Nat.zero_lt_of_lt hn
  let R := CriticalSchurNormalBaseRing K hm0 hn0
  let T := CriticalSchurNormalIntegralClosure K hm0 hn0
  let L := criticalNormalClosure K m n
  let F := criticalObservationField K m n
  let W₀ := criticalNormalClosureSchurValuationSubring K hm0 hn0
  haveI : FiniteDimensional F L := criticalNormalClosure_finiteDimensional K hm0 hn0
  haveI : IsGalois F L := criticalNormalClosure_isGalois K hm0 hn0
  have hW₀ : W₀ ≠ ⊤ := ValuationSubring.ne_top_of_isDiscreteValuationRing W₀
  have hRW₀ : ∀ r : R, algebraMap R L r ∈ W₀ :=
    criticalSchurNormalBase_algebraMap_mem K hm0 hn0
  have hcent₀ : ∀ r : R,
      (¬ IsUnit (⟨algebraMap R L r, hRW₀ r⟩ : W₀)) ↔
        r ∈ IsLocalRing.maximalIdeal R :=
    criticalSchurNormalBase_centre K hm0 hn0
  have hTW₀ : ∀ x : T, algebraMap T L x ∈ W₀ :=
    criticalSchurNormalIntegralClosure_mem_upper K hm0 hn0
  have hTW : ∀ x : T, algebraMap T L x ∈ W := by
    intro x
    exact ValuationInertia.mem_of_isIntegral W hRW x.property
  have hact : ∀ (g : L ≃ₐ[F] L) (x : T),
      algebraMap T L (g • x) = g • algebraMap T L x := by
    intro g x
    exact algebraMap_galRestrict_apply R g x
  obtain ⟨σ, hσ⟩ := ValuationInertia.exists_smul_valuationSubring_eq
    (R := R) (T := T) F (IsLocalRing.maximalIdeal R)
    hW₀ hW hRW₀ hRW hcent₀ hcent
  have hQ : σ • ValuationInertia.centerPrime W₀ hTW₀ =
      ValuationInertia.centerPrime W hTW :=
    ValuationInertia.smul_centerPrime_eq_of_smul_valuationSubring_eq
      hact hTW₀ hTW σ hσ
  intro g
  have hgI : (g : L ≃ₐ[F] L) ∈
      (ValuationInertia.centerPrime W hTW).inertia (L ≃ₐ[F] L) :=
    ValuationInertia.coe_mem_inertia_of_mem_inertiaSubgroup W hTW hact g.2
  rw [← hQ, ← GaloisForLFunctions.inertia_map_conj] at hgI
  obtain ⟨j, hj, hjg⟩ := hgI
  let jd : W₀.decompositionSubgroup F :=
    ValuationInertia.toDecomposition W₀ hTW₀ hact hW₀ hj
  let i : W₀.inertiaSubgroup F :=
    ⟨jd, ValuationInertia.toDecomposition_mem_inertiaSubgroup W₀ hTW₀ hact hW₀ hj⟩
  have hi := criticalSchurInertia_conjugate_mem_blockStabilizer K hm hn hB hB2 σ i
  rw [← hjg]
  exact hi

/-- The block fixed field has ramification index one at every valuation over the Schur place. -/
theorem criticalAllSchur_ramificationIdx_blockField_eq_one [DecidableEq K]
    (hm : 1 < m) (hn : 1 < n)
    {B : Set (criticalGeometricSheet K m n)}
    (hB : MulAction.IsBlock (criticalGeometricMonodromy K m n) B)
    (hB2 : ∃ x ∈ B, ∃ y ∈ B, x ≠ y)
    (W : ValuationSubring (criticalNormalClosure K m n))
    (hW : W ≠ ⊤)
    (hRW : ∀ r : CriticalSchurNormalBaseRing K (Nat.zero_lt_of_lt hm)
      (Nat.zero_lt_of_lt hn),
      algebraMap (CriticalSchurNormalBaseRing K (Nat.zero_lt_of_lt hm)
        (Nat.zero_lt_of_lt hn)) (criticalNormalClosure K m n) r ∈ W)
    (hcent : ∀ r : CriticalSchurNormalBaseRing K (Nat.zero_lt_of_lt hm)
      (Nat.zero_lt_of_lt hn),
      (¬ IsUnit (⟨algebraMap (CriticalSchurNormalBaseRing K (Nat.zero_lt_of_lt hm)
        (Nat.zero_lt_of_lt hn)) (criticalNormalClosure K m n) r, hRW r⟩ : W)) ↔
        r ∈ IsLocalRing.maximalIdeal
          (CriticalSchurNormalBaseRing K (Nat.zero_lt_of_lt hm)
            (Nat.zero_lt_of_lt hn))) :
    (ValuationInertia.intermediateCentre
        (IntermediateField.fixedField (criticalBlockStabilizer K B)) W hRW).ramificationIdx
      (CriticalSchurNormalBaseRing K (Nat.zero_lt_of_lt hm)
        (Nat.zero_lt_of_lt hn)) = 1 := by
  let hm0 := Nat.zero_lt_of_lt hm
  let hn0 := Nat.zero_lt_of_lt hn
  haveI : FiniteDimensional (criticalObservationField K m n) (criticalNormalClosure K m n) :=
    criticalNormalClosure_finiteDimensional K hm0 hn0
  haveI : IsGalois (criticalObservationField K m n) (criticalNormalClosure K m n) :=
    criticalNormalClosure_isGalois K hm0 hn0
  haveI := criticalIntermediateCentre_charZero K hm0 hn0
    (IntermediateField.fixedField (criticalBlockStabilizer K B))
    (ValuationInertia.intermediateCentre
      (IntermediateField.fixedField (criticalBlockStabilizer K B)) W hRW)
  exact ValuationInertia.ramificationIdx_fixedField_eq_one_of_inertia_le
    W (criticalBlockStabilizer K B) hRW hW
    (IsLocalRing.maximalIdeal (CriticalSchurNormalBaseRing K hm0 hn0))
    (IsDiscreteValuationRing.not_a_field _)
    hcent
    (criticalAllSchur_inertia_le_blockStabilizer K hm hn hB hB2 W hW hRW hcent)

end
end GaloisForLFunctions.HTGeometry
