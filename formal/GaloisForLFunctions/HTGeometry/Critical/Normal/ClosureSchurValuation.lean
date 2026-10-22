import GaloisForLFunctions.HTGeometry.Critical.Geometric.Monodromy
import GaloisForLFunctions.HTGeometry.Critical.Schur.SourceValuation
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Extending the actual Schur valuation to the critical normal closure

The canonical source embedding into the normal closure is obtained from the defining universal
property of `normalClosure`.  Krull's domination theorem then extends the actual Schur valuation
ring to a valuation ring of the normal closure.  The chosen extension contracts exactly to the
source Schur valuation, because the induced local-ring map is local.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option synthInstance.maxHeartbeats 200000

/-- Canonical actual source sheet inside the chosen normal closure. -/
noncomputable def criticalSourceNormalClosureEmbedding
    (K : Type*) [Field K] (m n : ℕ) : criticalGeometricSheet K m n := by
  let j : criticalSourceField K m n →ₐ[criticalObservationField K m n]
      criticalSourceAlgebraicClosure K m n :=
    { toRingHom := algebraMap (criticalSourceField K m n)
        (criticalSourceAlgebraicClosure K m n)
      commutes' := fun _ => rfl }
  exact (normalClosure.algHomEquiv (criticalObservationField K m n)
    (criticalSourceField K m n) (criticalSourceAlgebraicClosure K m n)).symm j

/-- Inclusion of the source Schur valuation ring into the normal closure. -/
noncomputable def criticalSchurSourceValuationToNormalClosure
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    criticalSchurSourceValuationSubring K hm hn →+* criticalNormalClosure K m n :=
  (criticalSourceNormalClosureEmbedding K m n).toRingHom.comp
    (criticalSchurSourceValuationSubring K hm hn).subtype

/-- Krull domination produces a valuation ring of the normal closure extending the actual source
Schur local valuation. -/
theorem exists_criticalNormalClosureSchurValuationSubring
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    ∃ (A : ValuationSubring (criticalNormalClosure K m n))
      (hmem : ∀ x : criticalSchurSourceValuationSubring K hm hn,
        criticalSchurSourceValuationToNormalClosure K hm hn x ∈ A),
      IsLocalHom ((criticalSchurSourceValuationToNormalClosure K hm hn).codRestrict
        A.toSubring hmem) :=
  IsLocalRing.exists_factor_valuationRing
    (criticalSchurSourceValuationToNormalClosure K hm hn)

/-- Chosen extension of the actual Schur valuation to the normal closure. -/
noncomputable def criticalNormalClosureSchurValuationSubring
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    ValuationSubring (criticalNormalClosure K m n) :=
  (exists_criticalNormalClosureSchurValuationSubring K hm hn).choose

theorem criticalNormalClosureSchurValuationSubring_source_mem
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (x : criticalSchurSourceValuationSubring K hm hn) :
    criticalSchurSourceValuationToNormalClosure K hm hn x ∈
      criticalNormalClosureSchurValuationSubring K hm hn :=
  (exists_criticalNormalClosureSchurValuationSubring K hm hn).choose_spec.choose x

noncomputable instance criticalSchurSourceValuationToNormalClosure_isLocalHom
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    IsLocalHom ((criticalSchurSourceValuationToNormalClosure K hm hn).codRestrict
      (criticalNormalClosureSchurValuationSubring K hm hn).toSubring
      (criticalNormalClosureSchurValuationSubring_source_mem K hm hn)) :=
  (exists_criticalNormalClosureSchurValuationSubring K hm hn).choose_spec.choose_spec

/-- A local embedding between valuation rings forces exact contraction of the upper valuation
ring. -/
theorem ValuationSubring.comap_eq_of_local_codRestrict
    {E N : Type*} [Field E] [Field N]
    (O : ValuationSubring E) (A : ValuationSubring N) (f : E →+* N)
    (hmem : ∀ x : O, f x ∈ A)
    [IsLocalHom ((f.comp O.subtype).codRestrict A.toSubring hmem)] :
    A.comap f = O := by
  ext x
  rw [ValuationSubring.mem_comap]
  constructor
  · intro hxA
    by_contra hxO
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hxO O.zero_mem
    have hxinvO : x⁻¹ ∈ O := (O.mem_or_inv_mem x).resolve_left hxO
    let y : O := ⟨x⁻¹, hxinvO⟩
    have hy_nonunit : ¬ IsUnit y := by
      intro hyunit
      have hyval : O.valuation (y : E) = 1 :=
        (O.valuation_eq_one_iff y).mp hyunit
      have hylt : O.valuation (x⁻¹) < 1 :=
        O.mem_nonunits_iff.mp (O.inv_mem_nonunits_iff.mpr (Or.inr hxO))
      exact (ne_of_lt hylt) hyval
    have hfy_unit : IsUnit
        ((f.comp O.subtype).codRestrict A.toSubring hmem y) := by
      let z : A := ⟨f x, hxA⟩
      rw [isUnit_iff_exists_inv]
      refine ⟨z, Subtype.ext ?_⟩
      change f (x⁻¹) * f x = 1
      rw [← map_mul, inv_mul_cancel₀ hx0, map_one]
    exact hy_nonunit (IsLocalHom.map_nonunit y hfy_unit)
  · intro hxO
    exact hmem ⟨x, hxO⟩

/-- The chosen normal-closure valuation lies over exactly the actual source Schur valuation. -/
theorem criticalNormalClosureSchurValuationSubring_comap_source
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (criticalNormalClosureSchurValuationSubring K hm hn).comap
        (criticalSourceNormalClosureEmbedding K m n).toRingHom =
      criticalSchurSourceValuationSubring K hm hn := by
  let O := criticalSchurSourceValuationSubring K hm hn
  let A := criticalNormalClosureSchurValuationSubring K hm hn
  let f := (criticalSourceNormalClosureEmbedding K m n).toRingHom
  let hmem : ∀ x : O, f x ∈ A :=
    criticalNormalClosureSchurValuationSubring_source_mem K hm hn
  letI : IsLocalHom ((f.comp O.subtype).codRestrict A.toSubring hmem) :=
    criticalSchurSourceValuationToNormalClosure_isLocalHom K hm hn
  exact ValuationSubring.comap_eq_of_local_codRestrict O A f hmem

/-- Decomposition group of the chosen Schur place in the actual critical normal closure. -/
abbrev criticalSchurDecompositionGroup
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :=
  (criticalNormalClosureSchurValuationSubring K hm hn).decompositionSubgroup
    (criticalObservationField K m n)

/-- Inertia group of the chosen Schur place in the actual critical normal closure. -/
noncomputable def criticalSchurInertiaGroup
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Subgroup (criticalSchurDecompositionGroup K hm hn) :=
  (criticalNormalClosureSchurValuationSubring K hm hn).inertiaSubgroup
    (criticalObservationField K m n)

end

end GaloisForLFunctions.HTGeometry
