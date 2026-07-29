import GaloisForLFunctions.HTGeometry.UpperEndPrimeLogCarrier
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Two-ended reflection geometry

Complex translations preserve the upper end and commute with differentiation.  The critical
reflection `z ↦ 1-z` has a different geometry: it exchanges the upper and lower ends, and ordinary
differentiation changes sign under that exchange.

This produces a signed two-ended differential carrier.  The formal law on meromorphic fraction
fields is `R(Df) = -D(Rf)`, the differential-geometric signature of the functional-equation
reflection.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Set
open scoped Differential

/-- The horizontal lower half-plane below height `H`. -/
def lowerTail (H : ℝ) : Set ℂ := {z | z.im < H}

/-- The filter of sets containing some sufficiently low lower half-plane. -/
def lowerEndFilter : Filter ℂ := Filter.comap Complex.im Filter.atBot

theorem lowerEndFilter_basis :
    lowerEndFilter.HasBasis (fun _ : ℝ ↦ True) lowerTail := by
  change (Filter.comap Complex.im Filter.atBot).HasBasis
    (fun _ : ℝ ↦ True) (fun H => Complex.im ⁻¹' Set.Iio H)
  exact Filter.atBot_basis_Iio.comap Complex.im

theorem lowerTail_nonempty (H : ℝ) : (lowerTail H).Nonempty := by
  refine ⟨(H - 1 : ℂ) * Complex.I, ?_⟩
  simp [lowerTail]

instance lowerEndFilter_neBot : NeBot lowerEndFilter := by
  rw [lowerEndFilter_basis.neBot_iff]
  intro H hH
  exact lowerTail_nonempty H

/-- The affine reflection occurring in the zeta functional equation. -/
def criticalReflection (z : ℂ) : ℂ := 1 - z

/-- Reflection sends a lower tail exactly to an upper tail with negated height. -/
theorem criticalReflection_preimage_lowerTail (H : ℝ) :
    criticalReflection ⁻¹' lowerTail H = upperTail (-H) := by
  ext z
  simp only [criticalReflection, lowerTail, upperTail, mem_preimage, mem_setOf_eq,
    Complex.sub_im, Complex.one_im]
  constructor <;> intro hz <;> linarith

/-- Reflection sends an upper tail exactly to a lower tail with negated height. -/
theorem criticalReflection_preimage_upperTail (H : ℝ) :
    criticalReflection ⁻¹' upperTail H = lowerTail (-H) := by
  ext z
  simp only [criticalReflection, lowerTail, upperTail, mem_preimage, mem_setOf_eq,
    Complex.sub_im, Complex.one_im]
  constructor <;> intro hz <;> linarith

/-- The critical reflection maps the upper end to the lower end. -/
theorem tendsto_criticalReflection_upper_lower :
    Tendsto criticalReflection upperEndFilter lowerEndFilter := by
  rw [upperEndFilter_basis.tendsto_iff lowerEndFilter_basis]
  intro H hH
  refine ⟨-H, trivial, ?_⟩
  intro z hz
  simp only [upperTail, lowerTail, criticalReflection, mem_setOf_eq,
    Complex.sub_im, Complex.one_im] at hz ⊢
  linarith

/-- The same involution maps the lower end back to the upper end. -/
theorem tendsto_criticalReflection_lower_upper :
    Tendsto criticalReflection lowerEndFilter upperEndFilter := by
  rw [lowerEndFilter_basis.tendsto_iff upperEndFilter_basis]
  intro H hH
  refine ⟨-H, trivial, ?_⟩
  intro z hz
  simp only [upperTail, lowerTail, criticalReflection, mem_setOf_eq,
    Complex.sub_im, Complex.one_im] at hz ⊢
  linarith

theorem criticalReflection_involutive : Function.Involutive criticalReflection := by
  intro z
  simp [criticalReflection]

/-- Reflection identifies unrestricted lower-end and upper-end germ rings. -/
noncomputable def criticalReflectionGermRingEquiv :
    Filter.Germ lowerEndFilter ℂ ≃+* Filter.Germ upperEndFilter ℂ where
  toFun f := f.compTendsto criticalReflection tendsto_criticalReflection_upper_lower
  invFun f := f.compTendsto criticalReflection tendsto_criticalReflection_lower_upper
  left_inv f := by
    induction f using Quotient.inductionOn with
    | _ f =>
      apply Filter.Germ.coe_eq.mpr
      exact Filter.Eventually.of_forall fun z ↦ by simp [criticalReflection]
  right_inv f := by
    induction f using Quotient.inductionOn with
    | _ f =>
      apply Filter.Germ.coe_eq.mpr
      exact Filter.Eventually.of_forall fun z ↦ by simp [criticalReflection]
  map_mul' f g := by
    induction f using Quotient.inductionOn with
    | _ f =>
      induction g using Quotient.inductionOn with
      | _ g => rfl
  map_add' f g := by
    induction f using Quotient.inductionOn with
    | _ f =>
      induction g using Quotient.inductionOn with
      | _ g => rfl

/-- The lower-end analytic domain, transported from the upper-end analytic domain by reflection. -/
noncomputable def lowerEndAnalyticSubring : Subring (Filter.Germ lowerEndFilter ℂ) :=
  upperEndAnalyticSubring.comap criticalReflectionGermRingEquiv.toRingHom

/-- Reflection identifies the lower- and upper-end analytic domains. -/
noncomputable def criticalReflectionAnalyticEquiv :
    lowerEndAnalyticSubring ≃+* upperEndAnalyticSubring where
  toFun a := ⟨criticalReflectionGermRingEquiv a, a.2⟩
  invFun a := ⟨criticalReflectionGermRingEquiv.symm a, by
    change criticalReflectionGermRingEquiv (criticalReflectionGermRingEquiv.symm a) ∈
      upperEndAnalyticSubring
    rw [criticalReflectionGermRingEquiv.apply_symm_apply]
    exact a.2⟩
  left_inv a := by
    apply Subtype.ext
    exact criticalReflectionGermRingEquiv.symm_apply_apply a
  right_inv a := by
    apply Subtype.ext
    exact criticalReflectionGermRingEquiv.apply_symm_apply a
  map_mul' a b := by
    apply Subtype.ext
    exact criticalReflectionGermRingEquiv.map_mul a b
  map_add' a b := by
    apply Subtype.ext
    exact criticalReflectionGermRingEquiv.map_add a b

theorem isDomain_lowerEndAnalyticSubring : IsDomain lowerEndAnalyticSubring := by
  exact criticalReflectionAnalyticEquiv.toMulEquiv.isDomain_iff.mpr
    isDomain_upperEndAnalyticSubring

/-- The lower-end meromorphic fraction field. -/
abbrev lowerEndMeroField : Type := FractionRing lowerEndAnalyticSubring

/-- Reflection identifies the lower- and upper-end meromorphic fields. -/
noncomputable def criticalReflectionMeroEquiv :
    lowerEndMeroField ≃+* upperEndMeroField := by
  letI := isDomain_lowerEndAnalyticSubring
  letI := isDomain_upperEndAnalyticSubring
  exact IsFractionRing.ringEquivOfRingEquiv criticalReflectionAnalyticEquiv

theorem criticalReflectionMeroEquiv_algebraMap (a : lowerEndAnalyticSubring) :
    letI := isDomain_lowerEndAnalyticSubring
    letI := isDomain_upperEndAnalyticSubring
    criticalReflectionMeroEquiv
        (algebraMap lowerEndAnalyticSubring lowerEndMeroField a) =
      algebraMap upperEndAnalyticSubring upperEndMeroField
        (criticalReflectionAnalyticEquiv a) := by
  letI := isDomain_lowerEndAnalyticSubring
  letI := isDomain_upperEndAnalyticSubring
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap _ a

/-- Ordinary lower-end differentiation, characterized by signed transport through reflection. -/
noncomputable def lowerEndAnalyticDeriv (a : lowerEndAnalyticSubring) :
    lowerEndAnalyticSubring :=
  criticalReflectionAnalyticEquiv.symm
    (-upperEndAnalyticDeriv (criticalReflectionAnalyticEquiv a))

/-- **Signed reflection law on analytic germs:** `R D = -D R`. -/
theorem criticalReflectionAnalyticEquiv_deriv (a : lowerEndAnalyticSubring) :
    criticalReflectionAnalyticEquiv (lowerEndAnalyticDeriv a) =
      -upperEndAnalyticDeriv (criticalReflectionAnalyticEquiv a) := by
  simp [lowerEndAnalyticDeriv]

theorem lowerEndAnalyticDeriv_zero :
    lowerEndAnalyticDeriv (0 : lowerEndAnalyticSubring) = 0 := by
  apply criticalReflectionAnalyticEquiv.injective
  rw [criticalReflectionAnalyticEquiv_deriv, map_zero, upperEndAnalyticDeriv_zero, neg_zero]

theorem lowerEndAnalyticDeriv_add (a b : lowerEndAnalyticSubring) :
    lowerEndAnalyticDeriv (a + b) =
      lowerEndAnalyticDeriv a + lowerEndAnalyticDeriv b := by
  apply criticalReflectionAnalyticEquiv.injective
  rw [criticalReflectionAnalyticEquiv_deriv, map_add, upperEndAnalyticDeriv_add,
    neg_add, map_add, criticalReflectionAnalyticEquiv_deriv,
    criticalReflectionAnalyticEquiv_deriv]

theorem lowerEndAnalyticDeriv_mul (a b : lowerEndAnalyticSubring) :
    lowerEndAnalyticDeriv (a * b) =
      a * lowerEndAnalyticDeriv b + b * lowerEndAnalyticDeriv a := by
  apply criticalReflectionAnalyticEquiv.injective
  rw [criticalReflectionAnalyticEquiv_deriv, map_mul, upperEndAnalyticDeriv_mul,
    map_add, map_mul, map_mul, criticalReflectionAnalyticEquiv_deriv,
    criticalReflectionAnalyticEquiv_deriv]
  ring

noncomputable def lowerEndAnalyticDerivation :
    Derivation ℤ lowerEndAnalyticSubring lowerEndAnalyticSubring := by
  let D : lowerEndAnalyticSubring →+ lowerEndAnalyticSubring :=
    { toFun := lowerEndAnalyticDeriv
      map_zero' := lowerEndAnalyticDeriv_zero
      map_add' := lowerEndAnalyticDeriv_add }
  exact Derivation.mk' D.toIntLinearMap lowerEndAnalyticDeriv_mul

/-- Quotient-rule differentiation on the lower-end meromorphic field. -/
@[reducible]
noncomputable def lowerEndMeroFieldDifferential : Differential lowerEndMeroField := by
  letI := isDomain_lowerEndAnalyticSubring
  letI : Algebra ℤ lowerEndAnalyticSubring := Ring.toIntAlgebra _
  letI : Algebra ℤ lowerEndMeroField := Ring.toIntAlgebra _
  exact ⟨fractionRingDerivation (K := ℤ)
    ((Algebra.linearMap lowerEndAnalyticSubring lowerEndMeroField).compDer
      lowerEndAnalyticDerivation)⟩

theorem lowerEndMeroFieldDifferential_algebraMap
    (a : lowerEndAnalyticSubring) :
    letI := isDomain_lowerEndAnalyticSubring
    letI := lowerEndMeroFieldDifferential
    (algebraMap lowerEndAnalyticSubring lowerEndMeroField a)′ =
      algebraMap lowerEndAnalyticSubring lowerEndMeroField
        (lowerEndAnalyticDeriv a) := by
  letI := isDomain_lowerEndAnalyticSubring
  letI : Algebra ℤ lowerEndAnalyticSubring := Ring.toIntAlgebra _
  letI : Algebra ℤ lowerEndMeroField := Ring.toIntAlgebra _
  letI := lowerEndMeroFieldDifferential
  change fractionRingDerivation _
    (algebraMap lowerEndAnalyticSubring lowerEndMeroField a) = _
  rw [fractionRingDerivation_algebraMap]
  rfl

/-- **Signed reflection law on meromorphic fields:** critical reflection anti-commutes with the
ordinary differential derivation. -/
theorem criticalReflectionMeroEquiv_deriv (z : lowerEndMeroField) :
    letI := isDomain_lowerEndAnalyticSubring
    letI := isDomain_upperEndAnalyticSubring
    letI := lowerEndMeroFieldDifferential
    letI := upperEndMeroFieldDifferential
    criticalReflectionMeroEquiv z′ =
      -(criticalReflectionMeroEquiv z)′ := by
  letI := isDomain_lowerEndAnalyticSubring
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℤ lowerEndAnalyticSubring := Ring.toIntAlgebra _
  letI : Algebra ℤ lowerEndMeroField := Ring.toIntAlgebra _
  letI : Algebra ℤ upperEndAnalyticSubring := Ring.toIntAlgebra _
  letI : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _
  letI := lowerEndMeroFieldDifferential
  letI := upperEndMeroFieldDifferential
  obtain ⟨a, b, hb, rfl⟩ :=
    IsFractionRing.div_surjective lowerEndAnalyticSubring z
  rw [Derivation.leibniz_div, lowerEndMeroFieldDifferential_algebraMap,
    lowerEndMeroFieldDifferential_algebraMap]
  simp only [smul_eq_mul, map_div₀, map_sub, map_mul, map_inv₀, map_pow,
    criticalReflectionMeroEquiv_algebraMap]
  rw [Derivation.leibniz_div, upperEndMeroFieldDifferential_algebraMap,
    upperEndMeroFieldDifferential_algebraMap]
  simp only [smul_eq_mul, map_neg, criticalReflectionAnalyticEquiv_deriv]
  ring

end GaloisForLFunctions.HTGeometry
