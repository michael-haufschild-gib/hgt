import GaloisForLFunctions.HTGeometry.HahnLeadingCoefficient
import GaloisForLFunctions.HTGeometry.FractionRingDerivation
import GaloisForLFunctions.HTGeometry.MultiGradedNewtonModel
import Mathlib.RingTheory.HahnSeries.Valuation
import Mathlib.RingTheory.Valuation.ExtendToLocalization
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Fraction fields of multigraded Hahn series

The logarithmic states in a cascade use division, while mathlib's Hahn-series implementation is an
integral domain rather than a field. This module equips its fraction field with the extended Hahn
valuation and extends every multigraded coordinate derivation to that field.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open HahnSeries

variable {Γ R : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Field R]

/-- Fraction field of a Hahn-series domain. -/
abbrev HahnFraction (Γ R : Type*) [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] [Field R] := FractionRing (HahnSeries Γ R)

theorem hahnVal_nonZeroDivisors_le_primeCompl :
    nonZeroDivisors (HahnSeries Γ R) ≤
      (HahnSeries.addVal Γ R).toValuation.supp.primeCompl := by
  intro x hx
  change x ∉ (HahnSeries.addVal Γ R).toValuation.supp
  rw [Valuation.mem_supp_iff, AddValuation.toValuation_apply]
  have hx0 : x ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hx
  rw [HahnSeries.addVal_apply_of_ne hx0]
  intro h
  have h' := congrArg Multiplicative.toAdd h
  change OrderDual.toDual (↑x.order : WithTop Γ) = OrderDual.toDual ⊤ at h'
  exact WithTop.coe_ne_top (OrderDual.toDual.injective h')

/-- Multiplicative Hahn valuation extended to the fraction field. -/
noncomputable def hahnFractionValuation :
    Valuation (HahnFraction Γ R) (Multiplicative (WithTop Γ)ᵒᵈ) :=
  (HahnSeries.addVal Γ R).toValuation.extendToLocalization
    hahnVal_nonZeroDivisors_le_primeCompl (HahnFraction Γ R)

/-- Additive form of the extended Hahn valuation. -/
noncomputable def hahnFractionAddValuation :
    AddValuation (HahnFraction Γ R) (WithTop Γ) :=
  AddValuation.toValuation.symm hahnFractionValuation

theorem hahnFractionAddValuation_algebraMap (f : HahnSeries Γ R) :
    hahnFractionAddValuation (algebraMap (HahnSeries Γ R) (HahnFraction Γ R) f) =
      HahnSeries.addVal Γ R f := by
  change OrderDual.ofDual (Multiplicative.toAdd
      (hahnFractionValuation (algebraMap (HahnSeries Γ R) (HahnFraction Γ R) f))) = _
  rw [hahnFractionValuation,
    Valuation.extendToLocalization_apply_map_apply, AddValuation.toValuation_apply]
  rfl

/-- Coefficient-linear Hahn derivation. Unlike `hahnDerivation`, this records the coefficient field
`ℂ`, rather than `ℤ`, as the scalar ring. -/
noncomputable def hahnDerivationComplex {Δ : Type*} [AddCommMonoid Δ]
    [PartialOrder Δ] [IsOrderedCancelAddMonoid Δ]
    (μ : Δ →+ ℂ) : Derivation ℂ (HahnSeries Δ ℂ) (HahnSeries Δ ℂ) :=
  Derivation.mk'
    { toFun := hahnGrade μ
      map_add' := hahnGrade_add μ
      map_smul' := by
        intro c f
        ext d
        simp [mul_left_comm] }
    (by
      intro a b
      change hahnGrade μ (a * b) = a * hahnGrade μ b + b * hahnGrade μ a
      rw [hahnGrade_mul]
      ring)

/-- Complex-linear coordinate derivation on the multigraded Hahn domain. -/
noncomputable def mgPartialComplex (N : ℕ) (j : Fin N) :
    Derivation ℂ (HahnSeries (mgDeg N) ℂ) (HahnSeries (mgDeg N) ℂ) :=
  (mgShift N j) • hahnDerivationComplex (mgComp N j)

@[simp] theorem mgPartialComplex_apply (N : ℕ) (j : Fin N)
    (f : HahnSeries (mgDeg N) ℂ) : mgPartialComplex N j f = mgPartial N j f := by
  rfl

/-- Coordinate derivation extended to the Hahn fraction field. -/
noncomputable def hahnFractionPartial (N : ℕ) (j : Fin N) :
    Derivation ℂ (HahnFraction (mgDeg N) ℂ) (HahnFraction (mgDeg N) ℂ) :=
  GaloisForLFunctions.fractionRingDerivation
    ((Algebra.linearMap (HahnSeries (mgDeg N) ℂ) (HahnFraction (mgDeg N) ℂ)).compDer
      (mgPartialComplex N j))

@[simp] theorem hahnFractionPartial_algebraMap (N : ℕ) (j : Fin N)
    (f : HahnSeries (mgDeg N) ℂ) :
    hahnFractionPartial N j
        (algebraMap (HahnSeries (mgDeg N) ℂ) (HahnFraction (mgDeg N) ℂ) f) =
      algebraMap (HahnSeries (mgDeg N) ℂ) (HahnFraction (mgDeg N) ℂ) (mgPartial N j f) := by
  exact GaloisForLFunctions.fractionRingDerivation_algebraMap
    ((Algebra.linearMap (HahnSeries (mgDeg N) ℂ) (HahnFraction (mgDeg N) ℂ)).compDer
      (mgPartialComplex N j)) f

end GaloisForLFunctions.HTGeometry
