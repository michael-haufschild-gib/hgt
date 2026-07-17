import GaloisForLFunctions.HTGeometry.NormalCrossingCriticalDerivedPhase
import GaloisForLFunctions.HTGeometry.RelativeLogCharacteristicArrangement
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic

/-!
# Physical characteristic incidence

This module compares three levels of the multiple-Gamma source constraint without using any
special-function identity:

* a coface sequence whose physical factors are one parameter times units generates exactly the
  `r`-fold principal fat-point ideal;
* actual source translation defects diagonalize on exponential modes with the same coface symbols
  as the DA logarithmic characteristic arrangement;
* for a rationally independent source frame, the common physical degeneracy spectrum is exactly
  the central character.

The unit-scaled ideal theorem also isolates an orientation no-go: the unframed fat point forgets
all unit phases.  Orientation therefore has to live in a source-labelled framing or polarization,
not in the underlying ideal.
-/

open Complex
open PowerSeries
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

def unitScaledCofaceGenerator
    {R : Type*} [CommRing R] (r : ℕ) (a : R)
    (u : Fin (r + 1) → Rˣ) (i : Fin (r + 1)) : R :=
  ∏ j ∈ Finset.univ.erase i, a * (u j : R)

theorem unitScaledCofaceGenerator_eq_pow_mul_unit
    {R : Type*} [CommRing R] (r : ℕ) (a : R)
    (u : Fin (r + 1) → Rˣ) (i : Fin (r + 1)) :
    unitScaledCofaceGenerator r a u i =
      a ^ r * (∏ j ∈ Finset.univ.erase i, (u j : R)) := by
  rw [unitScaledCofaceGenerator, Finset.prod_mul_distrib]
  have hcard : (Finset.univ.erase i).card = r := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin]
    omega
  rw [Finset.prod_const, hcard]

def unitScaledCofaceIdeal
    {R : Type*} [CommRing R] (r : ℕ) (a : R)
    (u : Fin (r + 1) → Rˣ) : Ideal R :=
  Ideal.span (Set.range (unitScaledCofaceGenerator r a u))

/-- A one-parameter pullback whose source factors are the parameter times units has exactly the
principal `r`-fold fat-point ideal. -/
theorem unitScaledCofaceIdeal_eq_span_pow
    {R : Type*} [CommRing R] (r : ℕ) (a : R)
    (u : Fin (r + 1) → Rˣ) :
    unitScaledCofaceIdeal r a u = Ideal.span ({a ^ r} : Set R) := by
  apply le_antisymm
  · rw [unitScaledCofaceIdeal, Ideal.span_le]
    rintro x ⟨i, rfl⟩
    rw [unitScaledCofaceGenerator_eq_pow_mul_unit]
    exact Ideal.mem_span_singleton.mpr ⟨_, rfl⟩
  · rw [Ideal.span_singleton_le_iff_mem]
    let i : Fin (r + 1) := ⟨0, Nat.succ_pos r⟩
    let U : Rˣ := ∏ j ∈ Finset.univ.erase i, u j
    have hgen : unitScaledCofaceGenerator r a u i ∈
        unitScaledCofaceIdeal r a u :=
      Ideal.subset_span (Set.mem_range_self i)
    rw [unitScaledCofaceGenerator_eq_pow_mul_unit] at hgen
    have hcoe : (U : R) = ∏ j ∈ Finset.univ.erase i, (u j : R) := by
      exact Units.coe_prod u (Finset.univ.erase i)
    rw [← hcoe] at hgen
    have hcancel := (unitScaledCofaceIdeal r a u).mul_mem_left (↑(U⁻¹)) hgen
    simpa [U, mul_assoc, mul_comm, mul_left_comm] using hcancel

/-!
## The formal exponential physical arc

The abstract unit-scaled theorem has an actual formal exponential instantiation. For a nonzero
period `tau`, `exp(tau * X) - 1` is `X` times a unit whose constant coefficient is `tau`. Thus the
physical coface ideal is the principal fat-point ideal `(X^r)`.
-/

/-- The formal series `exp(tau * X)`, expressed by rescaling the universal exponential series. -/
def physicalFormalExponential (tau : ℂ) : ℂ⟦X⟧ :=
  PowerSeries.rescale tau (PowerSeries.exp ℂ)

/-- The shifted coefficient series `(exp(tau * X) - 1) / X`. -/
def physicalFormalExponentialQuotient (tau : ℂ) : ℂ⟦X⟧ :=
  PowerSeries.mk fun n ↦
    PowerSeries.coeff (n + 1) (physicalFormalExponential tau)

theorem physicalFormalExponential_constantCoeff (tau : ℂ) :
    PowerSeries.constantCoeff (physicalFormalExponential tau) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    physicalFormalExponential, PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
  norm_num

theorem physicalFormalExponential_sub_one_eq_X_mul_quotient (tau : ℂ) :
    physicalFormalExponential tau - 1 =
      PowerSeries.X * physicalFormalExponentialQuotient tau := by
  have h := PowerSeries.sub_const_eq_X_mul_shift (physicalFormalExponential tau)
  rw [physicalFormalExponential_constantCoeff] at h
  simpa [physicalFormalExponentialQuotient] using h

theorem physicalFormalExponentialQuotient_constantCoeff (tau : ℂ) :
    PowerSeries.constantCoeff (physicalFormalExponentialQuotient tau) = tau := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    physicalFormalExponentialQuotient, PowerSeries.coeff_mk, physicalFormalExponential,
    PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
  norm_num

theorem isUnit_physicalFormalExponentialQuotient {tau : ℂ} (htau : tau ≠ 0) :
    IsUnit (physicalFormalExponentialQuotient tau) := by
  rw [PowerSeries.isUnit_iff_constantCoeff,
    physicalFormalExponentialQuotient_constantCoeff]
  exact isUnit_iff_ne_zero.mpr htau

/-- The quotient `(exp(tau * X) - 1) / X` as a unit when `tau` is nonzero. -/
noncomputable def physicalFormalExponentialQuotientUnit
    (tau : ℂ) (htau : tau ≠ 0) : ℂ⟦X⟧ˣ :=
  (isUnit_physicalFormalExponentialQuotient htau).unit

theorem coe_physicalFormalExponentialQuotientUnit (tau : ℂ) (htau : tau ≠ 0) :
    (physicalFormalExponentialQuotientUnit tau htau : ℂ⟦X⟧) =
      physicalFormalExponentialQuotient tau :=
  (isUnit_physicalFormalExponentialQuotient htau).unit_spec

/-- The physical coface product obtained from the formal exponential arc. -/
def physicalFormalCofaceGenerator (r : ℕ) (tau : Fin (r + 1) → ℂ)
    (i : Fin (r + 1)) : ℂ⟦X⟧ :=
  ∏ j ∈ Finset.univ.erase i, (physicalFormalExponential (tau j) - 1)

/-- The family of units appearing in the physical exponential factors. -/
noncomputable def physicalFormalExponentialQuotientUnits
    (r : ℕ) (tau : Fin (r + 1) → ℂ) (htau : ∀ j, tau j ≠ 0) :
    Fin (r + 1) → ℂ⟦X⟧ˣ :=
  fun j ↦ physicalFormalExponentialQuotientUnit (tau j) (htau j)

theorem physicalFormalExponential_sub_one_eq_X_mul_unit
    (tau : ℂ) (htau : tau ≠ 0) :
    physicalFormalExponential tau - 1 =
      PowerSeries.X * (physicalFormalExponentialQuotientUnit tau htau : ℂ⟦X⟧) := by
  rw [coe_physicalFormalExponentialQuotientUnit]
  exact physicalFormalExponential_sub_one_eq_X_mul_quotient tau

theorem physicalFormalCofaceGenerator_eq_unitScaled
    (r : ℕ) (tau : Fin (r + 1) → ℂ) (htau : ∀ j, tau j ≠ 0) :
    physicalFormalCofaceGenerator r tau =
      unitScaledCofaceGenerator r PowerSeries.X
        (physicalFormalExponentialQuotientUnits r tau htau) := by
  funext i
  unfold physicalFormalCofaceGenerator
  rw [unitScaledCofaceGenerator]
  change (Finset.univ.erase i).prod
      (fun j ↦ physicalFormalExponential (tau j) - 1) =
    (Finset.univ.erase i).prod
      (fun j ↦ PowerSeries.X *
        (physicalFormalExponentialQuotientUnits r tau htau j : ℂ⟦X⟧))
  apply Finset.prod_congr rfl
  intro j hj
  simpa [physicalFormalExponentialQuotientUnits] using
    physicalFormalExponential_sub_one_eq_X_mul_unit (tau j) (htau j)

/-- The ideal generated by all physical formal-exponential cofaces. -/
def physicalFormalCofaceIdeal (r : ℕ) (tau : Fin (r + 1) → ℂ) : Ideal ℂ⟦X⟧ :=
  Ideal.span (Set.range (physicalFormalCofaceGenerator r tau))

/-- Nonzero periods make the physical formal coface ideal exactly `(X^r)`. -/
theorem physicalFormalCofaceIdeal_eq_span_X_pow
    (r : ℕ) (tau : Fin (r + 1) → ℂ) (htau : ∀ j, tau j ≠ 0) :
    physicalFormalCofaceIdeal r tau =
      Ideal.span ({PowerSeries.X ^ r} : Set ℂ⟦X⟧) := by
  rw [physicalFormalCofaceIdeal, physicalFormalCofaceGenerator_eq_unitScaled r tau htau]
  exact unitScaledCofaceIdeal_eq_span_pow r PowerSeries.X
    (physicalFormalExponentialQuotientUnits r tau htau)

theorem physicalFormalCofaceIdeal_eq_span_X_pow_of_linearIndependent
    (r : ℕ) (tau : Fin (r + 1) → ℂ) (htau : LinearIndependent ℚ tau) :
    physicalFormalCofaceIdeal r tau =
      Ideal.span ({PowerSeries.X ^ r} : Set ℂ⟦X⟧) :=
  physicalFormalCofaceIdeal_eq_span_X_pow r tau (fun j ↦ htau.ne_zero j)

/-- The physical formal fat point has module length `r`. -/
theorem physicalFormalCofaceIdeal_quotient_length
    (r : ℕ) (tau : Fin (r + 1) → ℂ) (htau : ∀ j, tau j ≠ 0) :
    Module.length ℂ⟦X⟧ (ℂ⟦X⟧ ⧸ physicalFormalCofaceIdeal r tau) = r := by
  rw [physicalFormalCofaceIdeal_eq_span_X_pow r tau htau]
  rw [← Ideal.span_singleton_pow, ← PowerSeries.maximalIdeal_eq_span_X]
  exact IsDiscreteValuationRing.length_quotient_pow_maximalIdeal ℂ⟦X⟧ r

/-- The unit multiplying `a^r` in one pulled-back coface generator. -/
def unitScaledCofaceUnit
    {R : Type*} [CommRing R] (r : ℕ)
    (u : Fin (r + 1) → Rˣ) (i : Fin (r + 1)) : Rˣ :=
  ∏ j ∈ Finset.univ.erase i, u j

theorem unitScaledCofaceGenerator_eq_pow_mul_cofaceUnit
    {R : Type*} [CommRing R] (r : ℕ) (a : R)
    (u : Fin (r + 1) → Rˣ) (i : Fin (r + 1)) :
    unitScaledCofaceGenerator r a u i =
      a ^ r * (unitScaledCofaceUnit r u i : R) := by
  rw [unitScaledCofaceGenerator_eq_pow_mul_unit]
  congr 1
  exact (Units.coe_prod u (Finset.univ.erase i)).symm

/-- Scale every coface by its unit inverse and subtract the zeroth row from the others. -/
def unitScaledCofaceRowReduce
    {R : Type*} [CommRing R] (r : ℕ) (u : Fin (r + 1) → Rˣ)
    (v : Fin (r + 1) → R) : Fin (r + 1) → R :=
  fun i ↦ if i = 0 then
      (↑((unitScaledCofaceUnit r u 0)⁻¹) : R) * v 0
    else
      (↑((unitScaledCofaceUnit r u i)⁻¹) : R) * v i -
        (↑((unitScaledCofaceUnit r u 0)⁻¹) : R) * v 0

/-- The explicit inverse row operation. -/
def unitScaledCofaceRowRestore
    {R : Type*} [CommRing R] (r : ℕ) (u : Fin (r + 1) → Rˣ)
    (v : Fin (r + 1) → R) : Fin (r + 1) → R :=
  fun i ↦ (unitScaledCofaceUnit r u i : R) *
    (if i = 0 then v 0 else v i + v 0)

/-- The pulled-back coface row operations form an invertible linear change of generators. -/
def unitScaledCofaceRowEquiv
    {R : Type*} [CommRing R] (r : ℕ) (u : Fin (r + 1) → Rˣ) :
    (Fin (r + 1) → R) ≃ₗ[R] (Fin (r + 1) → R) where
  toFun := unitScaledCofaceRowReduce r u
  invFun := unitScaledCofaceRowRestore r u
  map_add' v w := by
    funext i
    by_cases hi : i = 0 <;>
      simp [unitScaledCofaceRowReduce, hi] <;> ring
  map_smul' c v := by
    funext i
    by_cases hi : i = 0 <;>
      simp [unitScaledCofaceRowReduce, hi, smul_eq_mul] <;> ring
  left_inv v := by
    funext i
    by_cases hi : i = 0 <;>
      simp [unitScaledCofaceRowReduce, unitScaledCofaceRowRestore, hi]
  right_inv v := by
    funext i
    by_cases hi : i = 0 <;>
      simp [unitScaledCofaceRowReduce, unitScaledCofaceRowRestore, hi]

/-- Explicit row reduction of the physical coface sequence to `(a^r, 0, ..., 0)`. -/
theorem unitScaledCofaceRowEquiv_generators
    {R : Type*} [CommRing R] (r : ℕ) (a : R)
    (u : Fin (r + 1) → Rˣ) :
    unitScaledCofaceRowEquiv r u (unitScaledCofaceGenerator r a u) =
      fun i ↦ if i = 0 then a ^ r else 0 := by
  funext i
  by_cases hi : i = 0
  · subst i
    simp [unitScaledCofaceRowEquiv, unitScaledCofaceRowReduce,
      unitScaledCofaceGenerator_eq_pow_mul_cofaceUnit,
      mul_assoc, mul_comm]
  · simp [unitScaledCofaceRowEquiv, unitScaledCofaceRowReduce, hi,
      unitScaledCofaceGenerator_eq_pow_mul_cofaceUnit,
      mul_assoc, mul_comm]

def physicalKoszulUncurry
    {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (k : ℕ) (phi : V →ₗ[R] R) :
    V →ₗ[R] V [⋀^Fin k]→ₗ[R] (⋀[R]^k V) where
  toFun v := phi v • exteriorPower.ιMulti R k
  map_add' v w := by
    ext x
    simp [add_smul]
  map_smul' a v := by
    ext x
    simp [smul_smul]

def physicalKoszulDifferential
    {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (k : ℕ) (phi : V →ₗ[R] R) :
    (⋀[R]^(k + 1) V) →ₗ[R] (⋀[R]^k V) :=
  exteriorPower.alternatingMapLinearEquiv
    (AlternatingMap.alternatizeUncurryFin (physicalKoszulUncurry k phi))

theorem physicalKoszulDifferential_ιMulti
    {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (k : ℕ) (phi : V →ₗ[R] R) (v : Fin (k + 1) → V) :
    physicalKoszulDifferential k phi (exteriorPower.ιMulti R (k + 1) v) =
      ∑ i : Fin (k + 1),
        ((-1 : ℤ) ^ (i : ℕ)) •
          (phi (v i) • exteriorPower.ιMulti R k (i.removeNth v)) := by
  rw [physicalKoszulDifferential, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    AlternatingMap.alternatizeUncurryFin_apply]
  simp only [physicalKoszulUncurry, LinearMap.coe_mk, AddHom.coe_mk,
    AlternatingMap.smul_apply]

theorem physicalKoszulDifferential_natural
    {R V W : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (k : ℕ) (T : V →ₗ[R] W) (phi : W →ₗ[R] R) (psi : V →ₗ[R] R)
    (h : phi.comp T = psi) :
    (physicalKoszulDifferential k phi).comp (exteriorPower.map (k + 1) T) =
      (exteriorPower.map k T).comp (physicalKoszulDifferential k psi) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    exteriorPower.map_apply_ιMulti, physicalKoszulDifferential_ιMulti]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_zsmul, map_smul, exteriorPower.map_apply_ιMulti]
  have hphi : phi (T (v i)) = psi (v i) := by
    exact LinearMap.congr_fun h (v i)
  rw [show (T ∘ v) i = T (v i) by rfl, hphi]
  rfl

def physicalKoszulDoubleUncurry
    {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (k : ℕ) (phi : V →ₗ[R] R) :
    V →ₗ[R] V →ₗ[R] V [⋀^Fin k]→ₗ[R] (⋀[R]^k V) where
  toFun v := phi v • physicalKoszulUncurry k phi
  map_add' v w := by
    ext x y
    simp [add_smul]
  map_smul' a v := by
    ext x y
    simp [smul_smul]

theorem physicalKoszulDoubleUncurry_symmetric
    {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (k : ℕ) (phi : V →ₗ[R] R) (v w : V) :
    physicalKoszulDoubleUncurry k phi v w = physicalKoszulDoubleUncurry k phi w v := by
  ext x
  simp [physicalKoszulDoubleUncurry, physicalKoszulUncurry, mul_comm, smul_smul]

theorem physicalKoszulDifferential_sq
    {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (k : ℕ) (phi : V →ₗ[R] R) :
    (physicalKoszulDifferential k phi).comp (physicalKoszulDifferential (k + 1) phi) = 0 := by
  apply exteriorPower.linearMap_ext
  have hcomp :
      ((physicalKoszulDifferential k phi).comp (physicalKoszulDifferential (k + 1) phi)).compAlternatingMap
          (exteriorPower.ιMulti R (k + 2)) =
        AlternatingMap.alternatizeUncurryFin
          (AlternatingMap.alternatizeUncurryFinLM ∘ₗ physicalKoszulDoubleUncurry k phi) := by
    apply AlternatingMap.ext
    intro v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      physicalKoszulDifferential_ιMulti, AlternatingMap.alternatizeUncurryFin_apply,
      AlternatingMap.alternatizeUncurryFinLM_apply, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_zsmul, map_smul, physicalKoszulDifferential_ιMulti]
    simp only [physicalKoszulDoubleUncurry, LinearMap.coe_mk, AddHom.coe_mk,
      Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [physicalKoszulUncurry]
    rw [smul_comm (phi (v i)) ((-1 : ℤ) ^ (j : ℕ)), ← mul_smul]
    simp [smul_smul]
  rw [hcomp]
  rw [AlternatingMap.alternatizeUncurryFin_alternatizeUncurryFinLM_comp_of_symmetric
    (physicalKoszulDoubleUncurry_symmetric k phi)]
  rfl

def physicalCofaceFunctional
    {R ι : Type*} [CommRing R] [Fintype ι]
    (g : ι → R) : (ι → R) →ₗ[R] R where
  toFun v := ∑ i, v i * g i
  map_add' v w := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a v := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc,
      Finset.mul_sum]

def unitScaledCofaceKoszulRowReduce
    {R : Type*} [CommRing R] (r : ℕ) (u : Fin (r + 1) → Rˣ)
    (v : Fin (r + 1) → R) : Fin (r + 1) → R :=
  fun i ↦ if i = 0 then
      (↑((unitScaledCofaceUnit r u 0)⁻¹) : R) *
        (v 0 - ∑ j ∈ Finset.univ.erase (0 : Fin (r + 1)), v j)
    else
      (↑((unitScaledCofaceUnit r u i)⁻¹) : R) * v i

def unitScaledCofaceKoszulRowRestore
    {R : Type*} [CommRing R] (r : ℕ) (u : Fin (r + 1) → Rˣ)
    (v : Fin (r + 1) → R) : Fin (r + 1) → R :=
  fun i ↦ if i = 0 then
      (unitScaledCofaceUnit r u 0 : R) * v 0 +
        ∑ j ∈ Finset.univ.erase (0 : Fin (r + 1)),
          (unitScaledCofaceUnit r u j : R) * v j
    else
      (unitScaledCofaceUnit r u i : R) * v i

def unitScaledCofaceKoszulRowEquiv
    {R : Type*} [CommRing R] (r : ℕ) (u : Fin (r + 1) → Rˣ) :
    (Fin (r + 1) → R) ≃ₗ[R] (Fin (r + 1) → R) where
  toFun := unitScaledCofaceKoszulRowReduce r u
  invFun := unitScaledCofaceKoszulRowRestore r u
  map_add' v w := by
    funext i
    by_cases hi : i = 0
    · subst i
      simp only [unitScaledCofaceKoszulRowReduce, ↓reduceIte, Pi.add_apply,
        Finset.sum_add_distrib]
      ring
    · simp only [unitScaledCofaceKoszulRowReduce, hi, ↓reduceIte, Pi.add_apply]
      ring
  map_smul' a v := by
    funext i
    by_cases hi : i = 0
    · subst i
      simp only [unitScaledCofaceKoszulRowReduce, ↓reduceIte, Pi.smul_apply,
        smul_eq_mul, RingHom.id_apply]
      rw [← Finset.mul_sum]
      ring
    · simp only [unitScaledCofaceKoszulRowReduce, hi, ↓reduceIte, Pi.smul_apply,
        smul_eq_mul, RingHom.id_apply]
      ring
  left_inv v := by
    funext i
    by_cases hi : i = 0
    · subst i
      have hsum :
          (∑ j ∈ Finset.univ.erase (0 : Fin (r + 1)),
            (unitScaledCofaceUnit r u j : R) *
              unitScaledCofaceKoszulRowReduce r u v j) =
            ∑ j ∈ Finset.univ.erase (0 : Fin (r + 1)), v j := by
        apply Finset.sum_congr rfl
        intro j hj
        have hj0 : j ≠ 0 := (Finset.mem_erase.mp hj).1
        simp [unitScaledCofaceKoszulRowReduce, hj0]
      have hzero : unitScaledCofaceKoszulRowReduce r u v 0 =
          (↑((unitScaledCofaceUnit r u 0)⁻¹) : R) *
            (v 0 - ∑ j ∈ Finset.univ.erase (0 : Fin (r + 1)), v j) := by
        simp [unitScaledCofaceKoszulRowReduce]
      simp only [unitScaledCofaceKoszulRowRestore, ↓reduceIte]
      rw [hzero, hsum]
      have hunit :
          (unitScaledCofaceUnit r u 0 : R) *
              (↑((unitScaledCofaceUnit r u 0)⁻¹) : R) = 1 := by
        exact Units.mul_inv (unitScaledCofaceUnit r u 0)
      calc
        _ = ((unitScaledCofaceUnit r u 0 : R) *
              (↑((unitScaledCofaceUnit r u 0)⁻¹) : R)) *
              (v 0 - ∑ j ∈ Finset.univ.erase (0 : Fin (r + 1)), v j) +
            ∑ j ∈ Finset.univ.erase (0 : Fin (r + 1)), v j := by ring
        _ = v 0 := by rw [hunit]; ring
    · simp [unitScaledCofaceKoszulRowReduce,
        unitScaledCofaceKoszulRowRestore, hi]
  right_inv v := by
    funext i
    by_cases hi : i = 0
    · subst i
      have hsum :
          (∑ j ∈ Finset.univ.erase (0 : Fin (r + 1)),
            unitScaledCofaceKoszulRowRestore r u v j) =
            ∑ j ∈ Finset.univ.erase (0 : Fin (r + 1)),
              (unitScaledCofaceUnit r u j : R) * v j := by
        apply Finset.sum_congr rfl
        intro j hj
        have hj0 : j ≠ 0 := (Finset.mem_erase.mp hj).1
        simp [unitScaledCofaceKoszulRowRestore, hj0]
      have hzero : unitScaledCofaceKoszulRowRestore r u v 0 =
          (unitScaledCofaceUnit r u 0 : R) * v 0 +
            ∑ j ∈ Finset.univ.erase (0 : Fin (r + 1)),
              (unitScaledCofaceUnit r u j : R) * v j := by
        simp [unitScaledCofaceKoszulRowRestore]
      simp only [unitScaledCofaceKoszulRowReduce, ↓reduceIte]
      rw [hzero, hsum]
      have hunit :
          (↑((unitScaledCofaceUnit r u 0)⁻¹) : R) *
              (unitScaledCofaceUnit r u 0 : R) = 1 := by
        exact Units.inv_mul (unitScaledCofaceUnit r u 0)
      calc
        _ = ((↑((unitScaledCofaceUnit r u 0)⁻¹) : R) *
              (unitScaledCofaceUnit r u 0 : R)) * v 0 := by ring
        _ = v 0 := by rw [hunit, one_mul]
    · simp [unitScaledCofaceKoszulRowReduce,
        unitScaledCofaceKoszulRowRestore, hi]

theorem unitScaledCofaceKoszulRowEquiv_functional
    {R : Type*} [CommRing R] (r : ℕ) (a : R)
    (u : Fin (r + 1) → Rˣ) :
    (physicalCofaceFunctional
      (unitScaledCofaceGenerator r a u)).comp
        (unitScaledCofaceKoszulRowEquiv r u).toLinearMap =
      physicalCofaceFunctional (fun i ↦ if i = 0 then a ^ r else 0) := by
  apply LinearMap.ext
  intro v
  change (∑ i, unitScaledCofaceKoszulRowReduce r u v i *
      unitScaledCofaceGenerator r a u i) =
    ∑ i, v i * (if i = 0 then a ^ r else 0)
  have hrhs : (∑ i, v i * (if i = 0 then a ^ r else 0)) = v 0 * a ^ r := by
    simp
  rw [hrhs]
  have hsplit := Finset.sum_eq_add_sum_diff_singleton
    (s := (Finset.univ : Finset (Fin (r + 1)))) (0 : Fin (r + 1))
    (fun i ↦ unitScaledCofaceKoszulRowReduce r u v i *
      unitScaledCofaceGenerator r a u i)
    (by simp)
  rw [hsplit]
  simp only [Finset.sdiff_singleton_eq_erase]
  have htail :
      (∑ i ∈ Finset.univ.erase (0 : Fin (r + 1)),
        unitScaledCofaceKoszulRowReduce r u v i *
          unitScaledCofaceGenerator r a u i) =
        a ^ r * ∑ i ∈ Finset.univ.erase (0 : Fin (r + 1)), v i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hi0 : i ≠ 0 := (Finset.mem_erase.mp hi).1
    rw [unitScaledCofaceGenerator_eq_pow_mul_cofaceUnit]
    simp [unitScaledCofaceKoszulRowReduce, hi0]
    have hunit :
        (↑((unitScaledCofaceUnit r u i)⁻¹) : R) *
            (unitScaledCofaceUnit r u i : R) = 1 := by
      exact Units.inv_mul (unitScaledCofaceUnit r u i)
    calc
      _ = ((↑((unitScaledCofaceUnit r u i)⁻¹) : R) *
            (unitScaledCofaceUnit r u i : R)) *
          (v i * a ^ r) := by ring
      _ = a ^ r * v i := by rw [hunit, one_mul]; ring
  rw [htail,
    unitScaledCofaceGenerator_eq_pow_mul_cofaceUnit]
  simp only [unitScaledCofaceKoszulRowReduce, ↓reduceIte]
  have hunit0 :
      (↑((unitScaledCofaceUnit r u 0)⁻¹) : R) *
          (unitScaledCofaceUnit r u 0 : R) = 1 := by
    exact Units.inv_mul (unitScaledCofaceUnit r u 0)
  calc
    _ = ((↑((unitScaledCofaceUnit r u 0)⁻¹) : R) *
          (unitScaledCofaceUnit r u 0 : R)) *
          ((v 0 - ∑ i ∈ Finset.univ.erase (0 : Fin (r + 1)), v i) * a ^ r) +
        a ^ r * ∑ i ∈ Finset.univ.erase (0 : Fin (r + 1)), v i := by ring
    _ = v 0 * a ^ r := by rw [hunit0]; ring

noncomputable def physicalKoszulExteriorEquiv
    {R V W : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (k : ℕ) (e : V ≃ₗ[R] W) : (⋀[R]^k V) ≃ₗ[R] (⋀[R]^k W) :=
  LinearEquiv.ofBijective (exteriorPower.map k e.toLinearMap)
    ⟨exteriorPower.map_injective (n := k) e.symm.toLinearMap (by
        ext v
        simp),
      exteriorPower.map_surjective (n := k) e.surjective⟩

/-- The exterior-power chain equivalence induced by the transpose of the physical coface row
reduction. -/
noncomputable def unitScaledCofaceKoszulChainEquiv
    {R : Type*} [CommRing R] (r k : ℕ) (u : Fin (r + 1) → Rˣ) :
    (⋀[R]^k (Fin (r + 1) → R)) ≃ₗ[R]
      (⋀[R]^k (Fin (r + 1) → R)) :=
  physicalKoszulExteriorEquiv k (unitScaledCofaceKoszulRowEquiv r u)

/-- **Koszul-chain transport for the physical coface row.**

The exterior-power equivalences induced by the invertible coface row reduction intertwine the
standard Koszul differentials of the original unit-scaled row and `(a^r,0,...,0)` in every
degree. -/
theorem unitScaledCofaceKoszulChainEquiv_commutes
    {R : Type*} [CommRing R] (r k : ℕ) (a : R)
    (u : Fin (r + 1) → Rˣ) :
    (physicalKoszulDifferential k
        (physicalCofaceFunctional
          (unitScaledCofaceGenerator r a u))).comp
        (unitScaledCofaceKoszulChainEquiv r (k + 1) u).toLinearMap =
      (unitScaledCofaceKoszulChainEquiv r k u).toLinearMap.comp
        (physicalKoszulDifferential k
          (physicalCofaceFunctional (fun i ↦ if i = 0 then a ^ r else 0))) := by
  change (physicalKoszulDifferential k
      (physicalCofaceFunctional
        (unitScaledCofaceGenerator r a u))).comp
      (exteriorPower.map (k + 1) (unitScaledCofaceKoszulRowEquiv r u).toLinearMap) =
    (exteriorPower.map k (unitScaledCofaceKoszulRowEquiv r u).toLinearMap).comp
      (physicalKoszulDifferential k
        (physicalCofaceFunctional (fun i ↦ if i = 0 then a ^ r else 0)))
  exact physicalKoszulDifferential_natural k
    (unitScaledCofaceKoszulRowEquiv r u).toLinearMap
    (physicalCofaceFunctional
      (unitScaledCofaceGenerator r a u))
    (physicalCofaceFunctional (fun i ↦ if i = 0 then a ^ r else 0))
    (unitScaledCofaceKoszulRowEquiv_functional r a u)

/-- The actual formal-exponential coface Koszul complex is chain-equivalent to the one-row
complex `(X^r, 0, ..., 0)`. -/
theorem physicalFormalCofaceKoszulChainEquiv_commutes
    (r k : ℕ) (tau : Fin (r + 1) → ℂ) (htau : ∀ j, tau j ≠ 0) :
    (physicalKoszulDifferential k
        (physicalCofaceFunctional (physicalFormalCofaceGenerator r tau))).comp
        (unitScaledCofaceKoszulChainEquiv r (k + 1)
          (physicalFormalExponentialQuotientUnits r tau htau)).toLinearMap =
      (unitScaledCofaceKoszulChainEquiv r k
        (physicalFormalExponentialQuotientUnits r tau htau)).toLinearMap.comp
        (physicalKoszulDifferential k
          (physicalCofaceFunctional
            (fun i ↦ if i = 0 then PowerSeries.X ^ r else 0))) := by
  rw [physicalFormalCofaceGenerator_eq_unitScaled r tau htau]
  exact unitScaledCofaceKoszulChainEquiv_commutes r k PowerSeries.X
    (physicalFormalExponentialQuotientUnits r tau htau)


/-!
## The row-reduced physical Koszul complex

The preceding invertible row operation reduces the pulled-back coface sequence to
`(a ^ r, 0, ..., 0)`.  The following finite model computes its differential, cycles, boundaries,
and surviving basis packets without introducing an abstract Koszul-complex placeholder.
-/

/-- Exterior basis packets for the Koszul complex on `r + 1` generators. -/
def physicalKoszulBasis (r k : ℕ) :=
  {S : Finset (Fin (r + 1)) // S.card = k}

/-- Insert the distinguished nonzero row into a Koszul basis packet. -/
def physicalKoszulInsertZero {r k : ℕ} (S : physicalKoszulBasis r k)
    (hS : (0 : Fin (r + 1)) ∉ S.1) : physicalKoszulBasis r (k + 1) :=
  ⟨insert 0 S.1, by simp [Finset.card_insert_of_notMem hS, S.2]⟩

/-- The degree `k+1 -> k` Koszul differential of the row-reduced sequence `(a,0,...,0)`. -/
def rowReducedPhysicalKoszulDifferential
    {R : Type*} [CommRing R] (r k : ℕ) (a : R) :
    (physicalKoszulBasis r (k + 1) → R) →ₗ[R]
      (physicalKoszulBasis r k → R) where
  toFun c S := if hS : (0 : Fin (r + 1)) ∈ S.1 then 0
    else a * c (physicalKoszulInsertZero S hS)
  map_add' c d := by
    funext S
    by_cases hS : (0 : Fin (r + 1)) ∈ S.1 <;>
      simp [hS, mul_add]
  map_smul' b c := by
    funext S
    by_cases hS : (0 : Fin (r + 1)) ∈ S.1 <;>
      simp [hS, mul_left_comm]

/-- The row-reduced Koszul differential squares to zero. -/
theorem rowReducedPhysicalKoszulDifferential_sq
    {R : Type*} [CommRing R] (r k : ℕ) (a : R)
    (c : physicalKoszulBasis r (k + 2) → R) :
    rowReducedPhysicalKoszulDifferential r k a
        (rowReducedPhysicalKoszulDifferential r (k + 1) a c) = 0 := by
  funext S
  by_cases hS : (0 : Fin (r + 1)) ∈ S.1
  · simp [rowReducedPhysicalKoszulDifferential, hS]
  · simp [rowReducedPhysicalKoszulDifferential, hS,
      physicalKoszulInsertZero]

/-- With `a` a non-zero-divisor, a positive-degree chain is a cycle exactly when all coefficients
on packets containing the distinguished row vanish. -/
theorem rowReducedPhysicalKoszulDifferential_eq_zero_iff
    {R : Type*} [CommRing R] (r k : ℕ) (a : R)
    (ha : ∀ b : R, a * b = 0 → b = 0)
    (c : physicalKoszulBasis r (k + 1) → R) :
    rowReducedPhysicalKoszulDifferential r k a c = 0 ↔
      ∀ S, (0 : Fin (r + 1)) ∈ S.1 → c S = 0 := by
  constructor
  · intro hc S hS
    let T : physicalKoszulBasis r k :=
      ⟨S.1.erase 0, by
        rw [Finset.card_erase_of_mem hS, S.2]
        omega⟩
    have hT : (0 : Fin (r + 1)) ∉ T.1 := Finset.notMem_erase _ _
    have hvalue := congrFun hc T
    have hins : physicalKoszulInsertZero T hT = S := by
      apply Subtype.ext
      simp [physicalKoszulInsertZero, T, hS]
    simp [rowReducedPhysicalKoszulDifferential, hT, hins] at hvalue
    exact ha _ hvalue
  · intro hc
    funext S
    by_cases hS : (0 : Fin (r + 1)) ∈ S.1
    · simp [rowReducedPhysicalKoszulDifferential, hS]
    · change (if h : (0 : Fin (r + 1)) ∈ S.1 then 0
        else a * c (physicalKoszulInsertZero S h)) = 0
      rw [dif_neg hS]
      rw [hc (physicalKoszulInsertZero S hS) (by
        simp [physicalKoszulInsertZero]), mul_zero]

/-- Coefficient normal form for a boundary in the row-reduced Koszul complex. -/
def IsRowReducedPhysicalKoszulBoundary
    {R : Type*} [CommRing R] (r k : ℕ) (a : R)
    (c : physicalKoszulBasis r k → R) : Prop :=
  (∀ S, (0 : Fin (r + 1)) ∈ S.1 → c S = 0) ∧
    ∀ S, (0 : Fin (r + 1)) ∉ S.1 → ∃ b, c S = a * b

/-- The range of the row-reduced differential is exactly the coefficient normal form: zero on
packets containing row zero and coefficientwise divisible by `a` on the remaining packets. -/
theorem mem_range_rowReducedPhysicalKoszulDifferential_iff
    {R : Type*} [CommRing R] (r k : ℕ) (a : R)
    (c : physicalKoszulBasis r k → R) :
    c ∈ LinearMap.range (rowReducedPhysicalKoszulDifferential r k a) ↔
      IsRowReducedPhysicalKoszulBoundary r k a c := by
  constructor
  · rintro ⟨b, rfl⟩
    constructor
    · intro S hS
      simp [rowReducedPhysicalKoszulDifferential, hS]
    · intro S hS
      exact ⟨b (physicalKoszulInsertZero S hS), by
        simp [rowReducedPhysicalKoszulDifferential, hS]⟩
  · rintro ⟨hzero, hdiv⟩
    classical
    let b : physicalKoszulBasis r (k + 1) → R := fun U ↦
      if hU : (0 : Fin (r + 1)) ∈ U.1 then
        Classical.choose (hdiv
          ⟨U.1.erase 0, by
            rw [Finset.card_erase_of_mem hU, U.2]
            omega⟩
          (Finset.notMem_erase _ _))
      else 0
    refine ⟨b, ?_⟩
    funext S
    by_cases hS : (0 : Fin (r + 1)) ∈ S.1
    · simp [rowReducedPhysicalKoszulDifferential, hS, hzero S hS]
    · let U := physicalKoszulInsertZero S hS
      have hU : (0 : Fin (r + 1)) ∈ U.1 := by
        simp [U, physicalKoszulInsertZero]
      have herase : U.1.erase 0 = S.1 := by
        simp [U, physicalKoszulInsertZero, hS]
      have hchoose := Classical.choose_spec (hdiv S hS)
      change (if h : (0 : Fin (r + 1)) ∈ S.1 then 0
        else a * b (physicalKoszulInsertZero S h)) = c S
      rw [dif_neg hS]
      change a * b U = c S
      have hbU : b U = Classical.choose (hdiv S hS) := by
        simp [b, U, physicalKoszulInsertZero, hS]
      rw [hbU]
      exact hchoose.symm

/-- Basis packets surviving row reduction: the `k`-subsets which avoid the distinguished row. -/
def physicalKoszulSurvivingBasis (r k : ℕ) :=
  {S : physicalKoszulBasis r k // (0 : Fin (r + 1)) ∉ S.1.1}

noncomputable instance physicalKoszulSurvivingBasis_finite (r k : ℕ) :
    Finite (physicalKoszulSurvivingBasis r k) :=
  Finite.of_injective (fun S : physicalKoszulSurvivingBasis r k ↦ S.1.1) (by
    intro S T h
    exact Subtype.ext (Subtype.ext h))

/-- The surviving degree-`k` multiplicity is exactly `choose(r,k)`. -/
theorem card_physicalKoszulSurvivingBasis (r k : ℕ) :
    Nat.card (physicalKoszulSurvivingBasis r k) = Nat.choose r k := by
  let P := (Finset.univ.erase (0 : Fin (r + 1))).powersetCard k
  let e : physicalKoszulSurvivingBasis r k ≃
      {S : Finset (Fin (r + 1)) // S ∈ P} :=
    { toFun := fun (S : physicalKoszulSurvivingBasis r k) =>
        (⟨S.1.1, Finset.mem_powersetCard.mpr
          ⟨by
            intro i hi
            simp only [Finset.mem_erase, Finset.mem_univ, and_true]
            exact fun hi0 ↦ S.2 (hi0 ▸ hi),
           S.1.2⟩⟩ : {T : Finset (Fin (r + 1)) // T ∈ P})
      invFun := fun (S : {T : Finset (Fin (r + 1)) // T ∈ P}) =>
        (⟨⟨S.1, (Finset.mem_powersetCard.mp S.2).2⟩, by
          intro h0
          have hmem := (Finset.mem_powersetCard.mp S.2).1 h0
          exact (Finset.mem_erase.mp hmem).1 rfl⟩ : physicalKoszulSurvivingBasis r k)
      left_inv := fun S => rfl
      right_inv := fun S => rfl }
  letI : Fintype (physicalKoszulSurvivingBasis r k) :=
    Fintype.ofEquiv {S : Finset (Fin (r + 1)) // S ∈ P} e.symm
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.card_congr e, Fintype.card_coe, Finset.card_powersetCard]
  simp

/-- The coefficient normal form of row-reduced cycles in degree `k`. -/
def rowReducedPhysicalKoszulCycleSubmodule
    {R : Type*} [CommRing R] (r k : ℕ) :
    Submodule R (physicalKoszulBasis r k → R) where
  carrier := {c | ∀ S, (0 : Fin (r + 1)) ∈ S.1 → c S = 0}
  zero_mem' := by simp
  add_mem' := by
    intro c d hc hd S hS
    simp [hc S hS, hd S hS]
  smul_mem' := by
    intro b c hc S hS
    simp [hc S hS]

/-- Reduce every surviving cycle coefficient modulo the principal ideal `(a)`. -/
def rowReducedPhysicalKoszulReduction
    {R : Type*} [CommRing R] (r k : ℕ) (a : R) :
    rowReducedPhysicalKoszulCycleSubmodule (R := R) r k →ₗ[R]
      (physicalKoszulSurvivingBasis r k →
        R ⧸ Ideal.span ({a} : Set R)) where
  toFun c S := Ideal.Quotient.mk (Ideal.span ({a} : Set R)) (c.1 S.1)
  map_add' c d := by
    funext S
    exact map_add _ _ _
  map_smul' b c := by
    funext S
    change (Ideal.Quotient.mk (Ideal.span ({a} : Set R))) b *
      (Ideal.Quotient.mk (Ideal.span ({a} : Set R))) (c.1 S.1) =
        b • (Ideal.Quotient.mk (Ideal.span ({a} : Set R))) (c.1 S.1)
    rw [Algebra.smul_def]
    rfl

/-- The kernel of coefficient reduction is exactly the actual boundary range. -/
theorem mem_ker_rowReducedPhysicalKoszulReduction_iff
    {R : Type*} [CommRing R] (r k : ℕ) (a : R)
    (c : rowReducedPhysicalKoszulCycleSubmodule (R := R) r k) :
    c ∈ LinearMap.ker (rowReducedPhysicalKoszulReduction r k a) ↔
      c.1 ∈ LinearMap.range (rowReducedPhysicalKoszulDifferential r k a) := by
  rw [mem_range_rowReducedPhysicalKoszulDifferential_iff]
  constructor
  · intro hc
    constructor
    · exact c.2
    · intro S hS
      have hfun := LinearMap.mem_ker.mp hc
      have hcoord := congrFun hfun
        (⟨S, hS⟩ : physicalKoszulSurvivingBasis r k)
      simp only [rowReducedPhysicalKoszulReduction, LinearMap.coe_mk,
        AddHom.coe_mk] at hcoord
      have hmem : c.1 S ∈ Ideal.span ({a} : Set R) :=
        Ideal.Quotient.eq_zero_iff_mem.mp hcoord
      exact Ideal.mem_span_singleton.mp hmem
  · rintro ⟨hzero, hdiv⟩
    apply LinearMap.mem_ker.mpr
    funext S
    obtain ⟨b, hb⟩ := hdiv S.1 S.2
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.mem_span_singleton.mpr ⟨b, hb⟩

/-- Coefficient reduction from cycles onto the surviving quotient packets is surjective. -/
theorem rowReducedPhysicalKoszulReduction_surjective
    {R : Type*} [CommRing R] (r k : ℕ) (a : R) :
    Function.Surjective (rowReducedPhysicalKoszulReduction r k a) := by
  classical
  intro y
  choose b hb using fun S : physicalKoszulSurvivingBasis r k ↦
    Ideal.Quotient.mk_surjective (y S)
  let c0 : physicalKoszulBasis r k → R := fun S ↦
    if hS : (0 : Fin (r + 1)) ∈ S.1 then 0 else b ⟨S, hS⟩
  let c : rowReducedPhysicalKoszulCycleSubmodule (R := R) r k :=
    ⟨c0, by
      intro S hS
      simp [c0, hS]⟩
  refine ⟨c, ?_⟩
  funext S
  change Ideal.Quotient.mk (Ideal.span ({a} : Set R)) (c.1 S.1) = y S
  have hc : c.1 S.1 = b S := by
    change (if h : (0 : Fin (r + 1)) ∈ S.1.1 then 0 else b ⟨S.1, h⟩) = b S
    split
    · rename_i h
      exact False.elim (S.2 h)
    · congr 1
  rw [hc]
  exact hb S

/-- **Complete row-reduced physical Koszul homology.**

Cycles modulo actual boundaries are the `choose(r,k)` surviving packets, with each coefficient
reduced modulo `(a)`. -/
noncomputable def rowReducedPhysicalKoszulHomologyEquiv
    {R : Type*} [CommRing R] (r k : ℕ) (a : R) :
    (rowReducedPhysicalKoszulCycleSubmodule (R := R) r k ⧸
        LinearMap.ker (rowReducedPhysicalKoszulReduction r k a)) ≃ₗ[R]
      (physicalKoszulSurvivingBasis r k →
        R ⧸ Ideal.span ({a} : Set R)) :=
  (rowReducedPhysicalKoszulReduction r k a).quotKerEquivOfSurjective
    (rowReducedPhysicalKoszulReduction_surjective r k a)

/-- Above degree `r`, there are no surviving exterior packets. -/
theorem isEmpty_physicalKoszulSurvivingBasis_of_lt
    {r k : ℕ} (h : r < k) : IsEmpty (physicalKoszulSurvivingBasis r k) := by
  constructor
  intro S
  have hsub : S.1.1 ⊆ Finset.univ.erase (0 : Fin (r + 1)) := by
    intro i hi
    exact Finset.mem_erase.mpr ⟨fun hi0 ↦ S.2 (hi0 ▸ hi), Finset.mem_univ i⟩
  have hcard := Finset.card_le_card hsub
  rw [S.1.2] at hcard
  have hbase : (Finset.univ.erase (0 : Fin (r + 1))).card = r := by simp
  rw [hbase] at hcard
  omega

/-- Consequently the row-reduced homology quotient vanishes above degree `r`. -/
theorem rowReducedPhysicalKoszulHomology_subsingleton_of_lt
    {R : Type*} [CommRing R] {r k : ℕ} (a : R) (h : r < k) :
    Subsingleton
      (rowReducedPhysicalKoszulCycleSubmodule (R := R) r k ⧸
        LinearMap.ker (rowReducedPhysicalKoszulReduction r k a)) := by
  letI := isEmpty_physicalKoszulSurvivingBasis_of_lt h
  constructor
  intro x y
  apply (rowReducedPhysicalKoszulHomologyEquiv r k a).injective
  funext S
  exact isEmptyElim S

open PowerSeries

/-- In the complex formal power-series local ring, the row-reduced degree-`k` homology has length
`r * choose(r,k)`. -/
theorem complexPowerSeries_rowReducedPhysicalKoszulHomology_length (r k : ℕ) :
    Module.length ℂ⟦X⟧
        (physicalKoszulSurvivingBasis r k →
          ℂ⟦X⟧ ⧸ Ideal.span ({(X : ℂ⟦X⟧) ^ r} : Set ℂ⟦X⟧)) =
      (r * Nat.choose r k : ℕ) := by
  rw [Module.length_pi, ENat.card_eq_coe_natCard,
    card_physicalKoszulSurvivingBasis]
  rw [← Ideal.span_singleton_pow, ← PowerSeries.maximalIdeal_eq_span_X]
  rw [IsDiscreteValuationRing.length_quotient_pow_maximalIdeal ℂ⟦X⟧ r]
  rw [mul_comm]
  norm_cast

/-- The total row-reduced homology length is `r * 2^r`. -/
theorem complexPowerSeries_rowReducedPhysicalKoszulHomology_totalLength (r : ℕ) :
    (∑ k ∈ Finset.range (r + 1),
      Module.length ℂ⟦X⟧
        (physicalKoszulSurvivingBasis r k →
          ℂ⟦X⟧ ⧸ Ideal.span ({(X : ℂ⟦X⟧) ^ r} : Set ℂ⟦X⟧))) =
      (r * 2 ^ r : ℕ) := by
  simp_rw [complexPowerSeries_rowReducedPhysicalKoszulHomology_length]
  norm_cast
  rw [← Finset.mul_sum, Nat.sum_range_choose]

/-- Translation defect on a complex-valued mode. -/
def physicalTranslationDefect (tau : ℂ) (f : ℂ → ℂ) : ℂ → ℂ :=
  fun z ↦ f (z + tau) - f z

/-- The exponential mode on which translation defects diagonalize. -/
def physicalExponentialMode (lambda : ℂ) : ℂ → ℂ :=
  fun z ↦ Complex.exp (lambda * z)

theorem physicalExponentialMode_add (lambda tau z : ℂ) :
    physicalExponentialMode lambda (z + tau) =
      Complex.exp (lambda * tau) * physicalExponentialMode lambda z := by
  rw [physicalExponentialMode]
  rw [show lambda * (z + tau) = lambda * tau + lambda * z by ring]
  exact Complex.exp_add _ _

/-- Exponential modes diagonalize each physical source defect. -/
theorem physicalTranslationDefect_exponentialMode
    (lambda tau z : ℂ) :
    physicalTranslationDefect tau (physicalExponentialMode lambda) z =
      (Complex.exp (lambda * tau) - 1) * physicalExponentialMode lambda z := by
  rw [physicalTranslationDefect, physicalExponentialMode_add]
  ring

/-- An ordered product of source defects.  The order is immaterial on translations, but retaining
it makes the principal-symbol computation independent of a separate operator algebra. -/
def iteratedPhysicalTranslationDefect
    {ι : Type*} (tau : ι → ℂ) : List ι → (ℂ → ℂ) → (ℂ → ℂ)
  | [], f => f
  | i :: indices, f =>
      physicalTranslationDefect (tau i)
        (iteratedPhysicalTranslationDefect tau indices f)

/-- The complete iterated boundary diagonalizes with the product of its source characters. -/
theorem iteratedPhysicalTranslationDefect_exponentialMode
    {ι : Type*} (tau : ι → ℂ) (indices : List ι) (lambda z : ℂ) :
    iteratedPhysicalTranslationDefect tau indices
        (physicalExponentialMode lambda) z =
      (indices.map (fun i ↦ Complex.exp (lambda * tau i) - 1)).prod *
        physicalExponentialMode lambda z := by
  induction indices generalizing z with
  | nil => simp [iteratedPhysicalTranslationDefect]
  | cons i indices ih =>
      simp only [iteratedPhysicalTranslationDefect, physicalTranslationDefect, ih,
        List.map_cons, List.prod_cons]
      rw [physicalExponentialMode_add]
      ring

/-- The scalar physical symbol of one coface of the DA-relative source ideal. -/
def physicalCofaceSymbol
    (r : ℕ) (tau : Fin (r + 1) → ℂ) (lambda : ℂ)
    (i : Fin (r + 1)) : ℂ :=
  ∏ j ∈ Finset.univ.erase i, (Complex.exp (lambda * tau j) - 1)

/-- The corresponding coface product of actual source translation defects on an exponential
mode. -/
def physicalCofaceBoundary
    (r : ℕ) (tau : Fin (r + 1) → ℂ) (lambda : ℂ)
    (i : Fin (r + 1)) : ℂ → ℂ :=
  iteratedPhysicalTranslationDefect tau (Finset.univ.erase i).toList
    (physicalExponentialMode lambda)

/-- The physical one-parameter logarithmic clock cut out by the structural periods. -/
def physicalLogarithmicClock
    {r : ℕ} (tau : Fin (r + 1) → ℂ) (lambda : ℂ) :
    Fin (r + 1) → ℂ :=
  fun j ↦ lambda * tau j

theorem physicalCofaceBoundary_apply
    (r : ℕ) (tau : Fin (r + 1) → ℂ) (lambda z : ℂ)
    (i : Fin (r + 1)) :
    physicalCofaceBoundary r tau lambda i z =
      physicalCofaceSymbol r tau lambda i * physicalExponentialMode lambda z := by
  simpa [physicalCofaceBoundary, physicalCofaceSymbol] using
    iteratedPhysicalTranslationDefect_exponentialMode tau
      (Finset.univ.erase i).toList lambda z

/-- A coface boundary kills the exponential mode exactly when its scalar source symbol vanishes. -/
theorem physicalCofaceBoundary_eq_zero_iff_symbol_eq_zero
    (r : ℕ) (tau : Fin (r + 1) → ℂ) (lambda : ℂ)
    (i : Fin (r + 1)) :
    physicalCofaceBoundary r tau lambda i = 0 ↔
      physicalCofaceSymbol r tau lambda i = 0 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    rw [physicalCofaceBoundary_apply] at h0
    simpa [physicalExponentialMode] using h0
  · intro h
    funext z
    rw [physicalCofaceBoundary_apply, h, zero_mul]
    rfl

/-- The DA logarithmic characteristic boundary and the actual source-translation boundary have
the same restriction to the physical exponential family. -/
theorem multipleGammaPhysicalLogCharacteristicBoundary_iff_sourceBoundary
    (r : ℕ) (tau : Fin (r + 1) → ℂ) (lambda : ℂ) :
    MultipleGammaLogCharacteristicBoundary r
        (physicalLogarithmicClock tau lambda) ↔
      ∀ i : Fin (r + 1), physicalCofaceBoundary r tau lambda i = 0 := by
  change (∀ i : Fin (r + 1), physicalCofaceSymbol r tau lambda i = 0) ↔ _
  constructor
  · intro h i
    exact (physicalCofaceBoundary_eq_zero_iff_symbol_eq_zero r tau lambda i).2 (h i)
  · intro h i
    exact (physicalCofaceBoundary_eq_zero_iff_symbol_eq_zero r tau lambda i).1 (h i)

/-- Two rationally independent periods have no common nonzero holomorphic exponential
resonance. -/
theorem exp_mul_pair_eq_one_eq_one_iff_of_linearIndependent
    (v : Fin 2 → ℂ) (hv : LinearIndependent ℚ v) (lambda : ℂ) :
    (Complex.exp (lambda * v 0) = 1 ∧
      Complex.exp (lambda * v 1) = 1) ↔ lambda = 0 := by
  constructor
  · rintro ⟨h0, h1⟩
    obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp h0
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
    by_cases hlambda : lambda = 0
    · exact hlambda
    have hcross : (n : ℂ) * v 0 = (m : ℂ) * v 1 := by
      apply mul_left_cancel₀ hlambda
      calc
        lambda * ((n : ℂ) * v 0) = (n : ℂ) * (lambda * v 0) := by ring
        _ = (n : ℂ) * ((m : ℂ) * (2 * Real.pi * I)) := by rw [hm]
        _ = (m : ℂ) * ((n : ℂ) * (2 * Real.pi * I)) := by ring
        _ = (m : ℂ) * (lambda * v 1) := by rw [hn]
        _ = lambda * ((m : ℂ) * v 1) := by ring
    have hcomb : ∑ i,
        (![((n : ℤ) : ℚ), -((m : ℤ) : ℚ)] : Fin 2 → ℚ) i • v i = 0 := by
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Rat.smul_def]
      push_cast
      simpa [sub_eq_add_neg] using sub_eq_zero.mpr hcross
    have hz := Fintype.linearIndependent_iff.mp hv _ hcomb
    have hnQ : ((n : ℤ) : ℚ) = 0 := hz 0
    have hnZ : n = 0 := by exact_mod_cast hnQ
    have hnzero : lambda * v 1 = 0 := by simpa [hnZ] using hn
    exact (mul_eq_zero.mp hnzero).resolve_right
      ((linearIndependent_fin2.mp hv).1)
  · rintro rfl
    simp

/-- For a generic multiple-Gamma period family, the physical holomorphic clock meets the full
DA-relative pair arrangement only at the central character. -/
theorem multipleGammaPhysicalLogCharacteristicBoundary_iff_zero
    {r : ℕ} (hr : 1 ≤ r) (tau : Fin (r + 1) → ℂ)
    (htau : LinearIndependent ℚ tau) (lambda : ℂ) :
    MultipleGammaLogCharacteristicBoundary r
        (physicalLogarithmicClock tau lambda) ↔
      lambda = 0 := by
  rw [multipleGammaLogCharacteristicBoundary_iff_exists_resonantPair]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    let pair : Fin 2 → Fin (r + 1) := ![a, b]
    have hpair : Function.Injective pair := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [pair]
    have hLI : LinearIndependent ℚ (fun i ↦ tau (pair i)) :=
      htau.comp pair hpair
    apply (exp_mul_pair_eq_one_eq_one_iff_of_linearIndependent
      (fun i ↦ tau (pair i)) hLI lambda).mp
    simpa [physicalLogarithmicClock, pair] using And.intro ha hb
  · rintro rfl
    refine ⟨⟨0, Nat.succ_pos r⟩, ⟨1, by omega⟩, ?_,
      by simp [physicalLogarithmicClock], by simp [physicalLogarithmicClock]⟩
    simp

/-- The common physical degeneracy spectrum of the DA-relative characteristic ideal and the
actual source-translation boundary is the single central character. -/
theorem multipleGammaPhysicalSourceBoundary_iff_zero
    {r : ℕ} (hr : 1 ≤ r) (tau : Fin (r + 1) → ℂ)
    (htau : LinearIndependent ℚ tau) (lambda : ℂ) :
    (∀ i : Fin (r + 1), physicalCofaceBoundary r tau lambda i = 0) ↔
      lambda = 0 := by
  rw [← multipleGammaPhysicalLogCharacteristicBoundary_iff_sourceBoundary,
    multipleGammaPhysicalLogCharacteristicBoundary_iff_zero hr tau htau]

end

end GaloisForLFunctions.HTGeometry
