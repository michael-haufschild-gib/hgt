import GaloisForLFunctions.HTGeometry.TopDegreeValuationRing
import GaloisForLFunctions.HTGeometry.AlgebraicCascadeModel
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
# A place of the algebraic model above the degree at infinity

The degree in the coordinate `m` is the valuation whose ring is `topInt m`, a discrete valuation
ring with fraction field the coordinate field.  On a simple algebraic extension of the coordinate
field the degree becomes a place above it: the integral closure of `topInt m` in the extension is a
Dedekind domain with the extension as fraction field, and lying over supplies a maximal ideal above
the maximal ideal of `topInt m`.  That maximal ideal is a height-one prime, so it carries an adic
valuation of the extension, and its restriction to the coordinate field is the degree.

This is what a branch of the algebraic curve at infinity is, algebraically.  Which of the finitely
many places the cascade actually follows is an analytic question and is not decided here.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

attribute [instance] algCascadeField_finiteDimensional

/-- The integral closure of the valuation ring of the degree at infinity in the algebraic model. -/
noncomputable abbrev algCascadeInt (m : ℕ) (p : Polynomial CascadeField) : Type :=
  integralClosure (topInt m) (AlgCascadeField p)

instance algCascade_isScalarTower (m : ℕ) (p : Polynomial CascadeField) :
    IsScalarTower (topInt m) CascadeField (AlgCascadeField p) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

set_option synthInstance.maxHeartbeats 1000000 in
instance algCascadeInt_isDomain (m : ℕ) (p : Polynomial CascadeField) [Fact (Irreducible p)] :
    IsDomain (algCascadeInt m p) :=
  letI : IsDomain (AlgCascadeField p) := inferInstanceAs (IsDomain (AdjoinRoot p))
  Subalgebra.isDomain (integralClosure (topInt m) (AlgCascadeField p))

instance algCascadeInt_isDedekindDomain (m : ℕ) (p : Polynomial CascadeField)
    [Fact (Irreducible p)] : IsDedekindDomain (algCascadeInt m p) :=
  IsIntegralClosure.isDedekindDomain (topInt m) CascadeField (AlgCascadeField p)
    (algCascadeInt m p)

instance algCascadeInt_isFractionRing (m : ℕ) (p : Polynomial CascadeField)
    [Fact (Irreducible p)] : IsFractionRing (algCascadeInt m p) (AlgCascadeField p) :=
  IsIntegralClosure.isFractionRing_of_finite_extension (topInt m) CascadeField
    (AlgCascadeField p) (algCascadeInt m p)

/-- **A place of the algebraic model above the degree at infinity.**  Lying over the maximal ideal
of the valuation ring produces a height-one prime of the integral closure. -/
theorem exists_heightOneSpectrum_over_topInt (m : ℕ) (p : Polynomial CascadeField)
    [Fact (Irreducible p)] :
    ∃ Q : IsDedekindDomain.HeightOneSpectrum (algCascadeInt m p),
      Ideal.comap (algebraMap (topInt m) (algCascadeInt m p)) Q.asIdeal
        = IsLocalRing.maximalIdeal (topInt m) := by
  have hker : RingHom.ker (algebraMap (topInt m) (algCascadeInt m p))
      ≤ IsLocalRing.maximalIdeal (topInt m) := by
    have hinj : Function.Injective (algebraMap (topInt m) (algCascadeInt m p)) := by
      refine fun x y hxy => ?_
      have h : algebraMap (topInt m) (AlgCascadeField p) x
          = algebraMap (topInt m) (AlgCascadeField p) y := by
        rw [IsScalarTower.algebraMap_apply (topInt m) (algCascadeInt m p) (AlgCascadeField p),
          IsScalarTower.algebraMap_apply (topInt m) (algCascadeInt m p) (AlgCascadeField p), hxy]
      have h2 : algebraMap CascadeField (AlgCascadeField p) (algebraMap (topInt m) CascadeField x)
          = algebraMap CascadeField (AlgCascadeField p)
            (algebraMap (topInt m) CascadeField y) := by
        rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
        exact h
      have h3 := (algebraMap CascadeField (AlgCascadeField p)).injective h2
      exact Subtype.ext h3
    intro x hx
    rw [RingHom.mem_ker] at hx
    have : x = 0 := hinj (by rw [hx, map_zero])
    rw [this]
    exact Submodule.zero_mem _
  obtain ⟨Q, hQmax, hQcomap⟩ :=
    Ideal.exists_ideal_over_maximal_of_isIntegral (S := algCascadeInt m p)
      (IsLocalRing.maximalIdeal (topInt m)) hker
  have hQne : Q ≠ ⊥ := by
    intro hQ0
    rw [hQ0] at hQcomap
    have hbot : Ideal.comap (algebraMap (topInt m) (algCascadeInt m p)) (⊥ : Ideal _) = ⊥ := by
      refine le_antisymm ?_ bot_le
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_bot] at hx
      rw [Ideal.mem_bot]
      have hinj : Function.Injective (algebraMap (topInt m) (algCascadeInt m p)) := by
        refine fun a b hab => ?_
        have h : algebraMap (topInt m) (AlgCascadeField p) a
            = algebraMap (topInt m) (AlgCascadeField p) b := by
          rw [IsScalarTower.algebraMap_apply (topInt m) (algCascadeInt m p) (AlgCascadeField p),
            IsScalarTower.algebraMap_apply (topInt m) (algCascadeInt m p) (AlgCascadeField p), hab]
        have h2 : algebraMap CascadeField (AlgCascadeField p) (algebraMap (topInt m) CascadeField a)
            = algebraMap CascadeField (AlgCascadeField p)
              (algebraMap (topInt m) CascadeField b) := by
          rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
          exact h
        exact Subtype.ext ((algebraMap CascadeField (AlgCascadeField p)).injective h2)
      exact hinj (by rw [hx, map_zero])
    rw [hbot] at hQcomap
    exact topInt_maximalIdeal_ne_bot m hQcomap.symm
  exact ⟨⟨Q, hQmax.isPrime, hQne⟩, hQcomap⟩

end GaloisForLFunctions.HTGeometry
