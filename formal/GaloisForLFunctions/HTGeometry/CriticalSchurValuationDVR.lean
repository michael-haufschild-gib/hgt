import GaloisForLFunctions.HTGeometry.CriticalNormalClosureSchurValuation
import GaloisForLFunctions.HTGeometry.ValuationSubringComapDVR
import GaloisForLFunctions.HTGeometry.ValuationSubringFiniteExtensionDVR
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.RingTheory.Valuation.IsTrivialOn

/-!
# Discrete valuation structure at the actual Schur divisor

The source Schur valuation was transported from the height-one localization of a polynomial ring.
This module makes that transport literal at ring level and installs the resulting DVR structures.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

/-- The coordinate Schur valuation ring is the valuation presentation of its height-one DVR. -/
noncomputable instance criticalSchurCoordinateValuationSubring_isDiscreteValuationRing
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    IsDiscreteValuationRing (criticalSchurCoordinateValuationSubring K hm hn) := by
  unfold criticalSchurCoordinateValuationSubring
  infer_instance

/-- Ring equivalence implementing transport from the coordinate Schur DVR to the actual source
Schur valuation ring. -/
noncomputable def criticalSchurSourceValuationRingEquiv
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    criticalSchurSourceValuationSubring K hm hn ≃+*
      criticalSchurCoordinateValuationSubring K hm hn where
  toFun x := ⟨(criticalSourceSchurFieldEquiv K hm hn).symm x, x.property⟩
  invFun x := ⟨criticalSourceSchurFieldEquiv K hm hn x, by
    rw [mem_criticalSchurSourceValuationSubring_iff]
    rw [(criticalSourceSchurFieldEquiv K hm hn).symm_apply_apply]
    exact x.property⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_add' x y := by ext; simp
  map_mul' x y := by ext; simp

/-- The actual source Schur valuation ring is a DVR. -/
noncomputable instance criticalSchurSourceValuationSubring_isDiscreteValuationRing
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    IsDiscreteValuationRing (criticalSchurSourceValuationSubring K hm hn) :=
  IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (criticalSchurSourceValuationRingEquiv K hm hn).symm

/-- Restriction of the nontrivial source Schur valuation to the algebraic observation subfield is
still nontrivial.  Equivalently, its observation valuation ring is not the whole field. -/
theorem criticalSchurObservationValuationSubring_ne_top
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    criticalSchurObservationValuationSubring K hm hn ≠ ⊤ := by
  intro htop
  let O := criticalSchurSourceValuationSubring K hm hn
  let v := O.valuation
  letI : v.IsTrivialOn (criticalObservationField K m n) := {
    eq_one := fun a ha => by
      have haO : a ∈ criticalSchurObservationValuationSubring K hm hn := by
        rw [htop]
        trivial
      have hainvO : a⁻¹ ∈ criticalSchurObservationValuationSubring K hm hn := by
        rw [htop]
        trivial
      let x : O := ⟨algebraMap (criticalObservationField K m n)
        (criticalSourceField K m n) a,
        (mem_criticalSchurObservationValuationSubring_iff K hm hn a).mp haO⟩
      have hxunit : IsUnit x := by
        rw [isUnit_iff_exists_inv]
        refine ⟨⟨algebraMap (criticalObservationField K m n)
          (criticalSourceField K m n) a⁻¹,
          (mem_criticalSchurObservationValuationSubring_iff K hm hn a⁻¹).mp hainvO⟩,
          Subtype.ext ?_⟩
        change algebraMap (criticalObservationField K m n)
            (criticalSourceField K m n) a *
          algebraMap (criticalObservationField K m n)
            (criticalSourceField K m n) a⁻¹ = 1
        rw [← map_mul, mul_inv_cancel₀ ha, map_one]
      exact (O.valuation_eq_one_iff x).mp hxunit }
  letI : Algebra.IsAlgebraic (criticalObservationField K m n)
      (criticalSourceField K m n) :=
    criticalSourceField_isAlgebraic_criticalObservationField K hm hn
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hπ0 : (π : criticalSourceField K m n) ≠ 0 := by
    exact Subtype.coe_injective.ne hπ.ne_zero
  have hπval : v (π : criticalSourceField K m n) ≠ 1 := by
    intro hval
    exact hπ.not_isUnit ((O.valuation_eq_one_iff π).mpr hval)
  exact (v.transcendental_of_ne_one (criticalObservationField K m n)
    (π : criticalSourceField K m n) hπ0 hπval)
      (Algebra.IsAlgebraic.isAlgebraic (π : criticalSourceField K m n))

/-- The actual observation-field Schur valuation ring is a DVR. -/
noncomputable instance criticalSchurObservationValuationSubring_isDiscreteValuationRing
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    IsDiscreteValuationRing (criticalSchurObservationValuationSubring K hm hn) := by
  unfold criticalSchurObservationValuationSubring
  exact valuationSubringComap_isDiscreteValuationRing
    (algebraMap (criticalObservationField K m n) (criticalSourceField K m n))
    (criticalSchurSourceValuationSubring K hm hn)
    (criticalSchurObservationValuationSubring_ne_top K hm hn)

/-- The chosen normal-closure Schur valuation contracts exactly to the observation-field Schur
valuation. -/
theorem criticalNormalClosureSchurValuationSubring_comap_observation
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (criticalNormalClosureSchurValuationSubring K hm hn).comap
        (algebraMap (criticalObservationField K m n) (criticalNormalClosure K m n)) =
      criticalSchurObservationValuationSubring K hm hn := by
  calc
    (criticalNormalClosureSchurValuationSubring K hm hn).comap
        (algebraMap (criticalObservationField K m n) (criticalNormalClosure K m n)) =
      (criticalNormalClosureSchurValuationSubring K hm hn).comap
        ((criticalSourceNormalClosureEmbedding K m n).toRingHom.comp
          (algebraMap (criticalObservationField K m n) (criticalSourceField K m n))) := by
            congr 1
    _ = ((criticalNormalClosureSchurValuationSubring K hm hn).comap
          (criticalSourceNormalClosureEmbedding K m n).toRingHom).comap
          (algebraMap (criticalObservationField K m n) (criticalSourceField K m n)) :=
      (ValuationSubring.comap_comap _ _ _).symm
    _ = (criticalSchurSourceValuationSubring K hm hn).comap
          (algebraMap (criticalObservationField K m n) (criticalSourceField K m n)) := by
      rw [criticalNormalClosureSchurValuationSubring_comap_source K hm hn]
    _ = criticalSchurObservationValuationSubring K hm hn := rfl

/-- The chosen valuation ring in the actual critical normal closure is a DVR. -/
noncomputable instance criticalNormalClosureSchurValuationSubring_isDiscreteValuationRing
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    IsDiscreteValuationRing (criticalNormalClosureSchurValuationSubring K hm hn) := by
  letI : FiniteDimensional (criticalObservationField K m n)
      (criticalNormalClosure K m n) :=
    criticalNormalClosure_finiteDimensional K hm hn
  exact valuationSubring_isDiscreteValuationRing_of_finiteExtension
    (criticalSchurObservationValuationSubring K hm hn)
    (criticalNormalClosureSchurValuationSubring K hm hn)
    (criticalNormalClosureSchurValuationSubring_comap_observation K hm hn)

end

end GaloisForLFunctions.HTGeometry
