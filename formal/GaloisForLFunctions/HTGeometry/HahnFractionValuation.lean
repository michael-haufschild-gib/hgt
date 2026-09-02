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

/-! ## Coordinate derivations over an arbitrary characteristic-zero coefficient field -/

/-- Coefficient-linear Hahn derivation over an arbitrary characteristic-zero field. -/
noncomputable def hahnDerivationBase {Δ K : Type*} [AddCommMonoid Δ]
    [PartialOrder Δ] [IsOrderedCancelAddMonoid Δ] [Field K]
    (μ : Δ →+ K) : Derivation K (HahnSeries Δ K) (HahnSeries Δ K) :=
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

/-- A derivation viewed only as its zero-preserving coefficient map. -/
def derivationZeroHom {C K : Type*} [CommSemiring C] [CommSemiring K] [Algebra C K]
    (D : Derivation C K K) : ZeroHom K K where
  toFun := D
  map_zero' := D.map_zero

@[simp] theorem derivationZeroHom_apply
    {C K : Type*} [CommSemiring C] [CommSemiring K] [Algebra C K]
    (D : Derivation C K K) (x : K) : derivationZeroHom D x = D x := rfl

/-- Coefficientwise action of a coefficient-field derivation on Hahn series. -/
noncomputable def hahnCoefficientLinearMap
    {C K Δ : Type*} [Field C] [Field K] [Algebra C K]
    [AddCommGroup Δ] [LinearOrder Δ] [IsOrderedAddMonoid Δ]
    (D : Derivation C K K) : HahnSeries Δ K →ₗ[C] HahnSeries Δ K where
  toFun := fun f ↦ f.map (derivationZeroHom D)
  map_add' := by
    intro f g
    ext d
    simp [derivationZeroHom]
  map_smul' := by
    intro c f
    ext d
    simp [derivationZeroHom]

/-- Coefficientwise Hahn derivation extending a derivation of the coefficient field. -/
noncomputable def hahnCoefficientDerivation
    {C K Δ : Type*} [Field C] [Field K] [Algebra C K]
    [AddCommGroup Δ] [LinearOrder Δ] [IsOrderedAddMonoid Δ]
    (D : Derivation C K K) :
    Derivation C (HahnSeries Δ K) (HahnSeries Δ K) :=
  Derivation.mk' (hahnCoefficientLinearMap D)
    (by
      intro f g
      ext d
      classical
      simp only [smul_eq_mul]
      change ((f * g).map (derivationZeroHom D)).coeff d =
        (f * g.map (derivationZeroHom D) +
          g * f.map (derivationZeroHom D)).coeff d
      rw [mul_comm g (f.map (derivationZeroHom D)), HahnSeries.map_coeff]
      change D ((f * g).coeff d) = _
      rw [HahnSeries.coeff_mul, map_sum, HahnSeries.coeff_add,
        HahnSeries.coeff_mul_right' g.isPWO_support
          (HahnSeries.support_map_subset g (derivationZeroHom D)),
        HahnSeries.coeff_mul_left' f.isPWO_support
          (HahnSeries.support_map_subset f (derivationZeroHom D))]
      simp only [HahnSeries.map_coeff, derivationZeroHom]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro ij hij
      change D (f.coeff ij.1 * g.coeff ij.2) =
        f.coeff ij.1 * D (g.coeff ij.2) + D (f.coeff ij.1) * g.coeff ij.2
      simpa only [smul_eq_mul, mul_comm] using
        D.leibniz (f.coeff ij.1) (g.coeff ij.2))

@[simp] theorem coeff_hahnCoefficientDerivation
    {C K Δ : Type*} [Field C] [Field K] [Algebra C K]
    [AddCommGroup Δ] [LinearOrder Δ] [IsOrderedAddMonoid Δ]
    (D : Derivation C K K) (f : HahnSeries Δ K) (d : Δ) :
    (hahnCoefficientDerivation D f).coeff d = D (f.coeff d) := by
  rfl

/-- Coefficientwise derivation extended to the Hahn fraction field. -/
noncomputable def hahnFractionCoefficientDerivation
    {C K Δ : Type*} [Field C] [Field K] [Algebra C K]
    [AddCommGroup Δ] [LinearOrder Δ] [IsOrderedAddMonoid Δ]
    (D : Derivation C K K) :
    Derivation C (HahnFraction Δ K) (HahnFraction Δ K) :=
  GaloisForLFunctions.fractionRingDerivation
    ((Algebra.linearMap (HahnSeries Δ K) (HahnFraction Δ K)).compDer
      (hahnCoefficientDerivation D))

@[simp] theorem hahnFractionCoefficientDerivation_algebraMap
    {C K Δ : Type*} [Field C] [Field K] [Algebra C K]
    [AddCommGroup Δ] [LinearOrder Δ] [IsOrderedAddMonoid Δ]
    (D : Derivation C K K) (f : HahnSeries Δ K) :
    hahnFractionCoefficientDerivation D
        (algebraMap (HahnSeries Δ K) (HahnFraction Δ K) f) =
      algebraMap (HahnSeries Δ K) (HahnFraction Δ K)
        (hahnCoefficientDerivation D f) := by
  exact GaloisForLFunctions.fractionRingDerivation_algebraMap
    ((Algebra.linearMap (HahnSeries Δ K) (HahnFraction Δ K)).compDer
      (hahnCoefficientDerivation D)) f

@[simp] theorem hahnFractionCoefficientDerivation_coeffAlgebraMap
    {C K Δ : Type*} [Field C] [Field K] [Algebra C K]
    [AddCommGroup Δ] [LinearOrder Δ] [IsOrderedAddMonoid Δ]
    (D : Derivation C K K) (c : K) :
    hahnFractionCoefficientDerivation D (algebraMap K (HahnFraction Δ K) c) =
      algebraMap K (HahnFraction Δ K) (D c) := by
  change hahnFractionCoefficientDerivation D
      (algebraMap (HahnSeries Δ K) (HahnFraction Δ K) (HahnSeries.C c)) =
    algebraMap (HahnSeries Δ K) (HahnFraction Δ K) (HahnSeries.C (D c))
  rw [hahnFractionCoefficientDerivation_algebraMap]
  congr 1
  ext d
  by_cases hd : d = 0
  · subst d
    simp
  · simp [hd]

/-- The `j`-th exponent character with values in coefficient field `K`. -/
def mgCompBase (K : Type*) [Field K] [CharZero K] (N : ℕ) (j : Fin N) : mgDeg N →+ K where
  toFun γ := ((ofLex γ j : ℤ) : K)
  map_zero' := by
    show (((0 : Fin N → ℤ) j : ℤ) : K) = 0
    rw [Pi.zero_apply]
    norm_num
  map_add' a b := by
    change (((ofLex a j + ofLex b j : ℤ) : K)) = _
    push_cast
    ring

/-- Degree-shifting monomial for the `j`-th coordinate derivative over `K`. -/
noncomputable def mgShiftBase (K : Type*) [Field K] (N : ℕ) (j : Fin N) :
    HahnSeries (mgDeg N) K :=
  HahnSeries.single (mgStep N j) 1

/-- Coefficient-linear coordinate derivative on a multigraded Hahn domain over `K`. -/
noncomputable def mgPartialBase (K : Type*) [Field K] [CharZero K] (N : ℕ) (j : Fin N) :
    Derivation K (HahnSeries (mgDeg N) K) (HahnSeries (mgDeg N) K) :=
  (mgShiftBase K N j) • hahnDerivationBase (mgCompBase K N j)

theorem coeff_mgPartialBase {K : Type*} [Field K] [CharZero K]
    (N : ℕ) (j : Fin N) (f : HahnSeries (mgDeg N) K) (γ : mgDeg N) :
    (mgPartialBase K N j f).coeff (γ + mgStep N j) =
      ((ofLex γ j : ℤ) : K) * f.coeff γ := by
  have hd : mgPartialBase K N j f =
      mgShiftBase K N j * hahnGrade (mgCompBase K N j) f := by
    show ((mgShiftBase K N j) • hahnDerivationBase (mgCompBase K N j)) f = _
    simp only [Derivation.coe_smul, Pi.smul_apply, smul_eq_mul]
    rfl
  rw [hd, mgShiftBase, HahnSeries.coeff_single_mul, coeff_hahnGrade]
  have hidx : γ + mgStep N j - mgStep N j = γ := by abel
  rw [hidx]
  change 1 * (((ofLex γ j : ℤ) : K) * f.coeff γ) = _
  ring

/-- Coordinate derivative over `K`, extended to the multigraded Hahn fraction field. -/
noncomputable def hahnFractionPartialBase (K : Type*) [Field K] [CharZero K]
    (N : ℕ) (j : Fin N) :
    Derivation K (HahnFraction (mgDeg N) K) (HahnFraction (mgDeg N) K) :=
  GaloisForLFunctions.fractionRingDerivation
    ((Algebra.linearMap (HahnSeries (mgDeg N) K) (HahnFraction (mgDeg N) K)).compDer
      (mgPartialBase K N j))

@[simp] theorem hahnFractionPartialBase_algebraMap
    (K : Type*) [Field K] [CharZero K] (N : ℕ) (j : Fin N)
    (f : HahnSeries (mgDeg N) K) :
    hahnFractionPartialBase K N j
        (algebraMap (HahnSeries (mgDeg N) K) (HahnFraction (mgDeg N) K) f) =
      algebraMap (HahnSeries (mgDeg N) K) (HahnFraction (mgDeg N) K)
        (mgPartialBase K N j f) := by
  exact GaloisForLFunctions.fractionRingDerivation_algebraMap
    ((Algebra.linearMap (HahnSeries (mgDeg N) K) (HahnFraction (mgDeg N) K)).compDer
      (mgPartialBase K N j)) f

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
