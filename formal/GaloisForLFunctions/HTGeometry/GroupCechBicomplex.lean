import GaloisForLFunctions.HTGeometry.CechLowDegreeComplex
import GaloisForLFunctions.HTGeometry.AnomalyCoefficientSectors

/-!
# The group--Čech bicomplex of a shift quotient

The anomaly of a two-shift boundary lives in a bicomplex with two directions: a Čech direction
along a cover and a group direction along the translation, with multiplicative coefficients.  With
a single translation the group direction has two rows, so the total complex in low degrees is the
mapping cone of the coefficient map, and the total differential squares to one exactly when the
mixed square commutes and the two rows are given opposite signs.

The concrete instance is the ambient meromorphic field: the coefficient map is the shift quotient
acting on units, and the coefficient sector is the holomorphic nowhere-vanishing differentially
algebraic one.  The total complex therefore restricts to that sector, which is the bicomplex form of
the coefficient layer.
-/

open Filter Topology Set Function
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

section Abstract

variable {ι G H : Type*} [CommGroup G] [CommGroup H]

/-- The Čech differential is natural in the coefficient group. -/
theorem cechD0_comp (φ : G →* H) (f : ι → G) :
    cechD0 (fun a => φ (f a)) = fun a b => φ (cechD0 f a b) := by
  funext a b
  simp [cechD0, map_div]

/-- The Čech differential is natural in the coefficient group. -/
theorem cechD1_comp (φ : G →* H) (g : ι → ι → G) :
    cechD1 (fun a b => φ (g a b)) = fun a b c => φ (cechD1 g a b c) := by
  funext a b c
  simp [cechD1, map_div, map_mul]

/-- The Čech differential is a homomorphism in the cochain. -/
theorem cechD1_div (u v : ι → ι → G) :
    cechD1 (fun a b => u a b / v a b) = fun a b c => cechD1 u a b c / cechD1 v a b c := by
  funext a b c
  simp only [cechD1, div_eq_mul_inv, mul_inv_rev, inv_inv]
  simp [mul_comm, mul_left_comm, mul_assoc]

/-- The total differential out of total degree zero. -/
def totalD1 (φ : G →* H) (f : ι → G) : (ι → ι → G) × (ι → H) :=
  (cechD0 f, fun a => φ (f a))

/-- The total differential out of total degree one.  The mixed entry carries the sign that makes
the square anticommute. -/
def totalD2 (φ : G →* H) (p : (ι → ι → G) × (ι → H)) : (ι → ι → ι → G) × (ι → ι → H) :=
  (cechD1 p.1, fun a b => cechD0 p.2 a b / φ (p.1 a b))

/-- The total differential out of total degree two, with the opposite sign in the mixed entry. -/
def totalD3 (φ : G →* H) (p : (ι → ι → ι → G) × (ι → ι → H)) :
    (ι → ι → ι → ι → G) × (ι → ι → ι → H) :=
  (cechD2 p.1, fun a b c => cechD1 p.2 a b c * φ (p.1 a b c))

/-- **The total differential squares to one out of degree zero.** -/
theorem totalD2_totalD1 (φ : G →* H) (f : ι → G) :
    totalD2 φ (totalD1 φ f) = (fun _ _ _ => (1 : G), fun _ _ => (1 : H)) := by
  refine Prod.ext ?_ ?_
  · exact cechD1_cechD0 f
  · funext a b
    show cechD0 (fun a => φ (f a)) a b / φ (cechD0 f a b) = 1
    rw [cechD0_comp]
    simp

/-- **The total differential squares to one out of degree one.** -/
theorem totalD3_totalD2 (φ : G →* H) (p : (ι → ι → G) × (ι → H)) :
    totalD3 φ (totalD2 φ p) = (fun _ _ _ _ => (1 : G), fun _ _ _ => (1 : H)) := by
  refine Prod.ext ?_ ?_
  · exact cechD2_cechD1 p.1
  · funext a b c
    have hdiv : (fun a b => cechD0 p.2 a b / φ (p.1 a b))
        = fun a b => cechD0 p.2 a b / (fun x y => φ (p.1 x y)) a b := rfl
    simp only [totalD2, totalD3]
    rw [hdiv, cechD1_div, cechD1_comp, cechD1_cechD0]
    simp

/-- **The total complex restricts to a pair of coefficient sectors.** -/
theorem totalD1_mem (S : Sector G) (T : Sector H) (φ : G →* H)
    (hφ : ∀ {x : G}, x ∈ S.carrier → φ x ∈ T.carrier) {f : ι → G} (hf : ∀ a, f a ∈ S.carrier) :
    (∀ a b, (totalD1 φ f).1 a b ∈ S.carrier) ∧ ∀ a, (totalD1 φ f).2 a ∈ T.carrier :=
  ⟨fun a b => cechD0_mem S hf a b, fun a => hφ (hf a)⟩

/-- **The total complex restricts to a pair of coefficient sectors, one degree up.** -/
theorem totalD2_mem (S : Sector G) (T : Sector H) (φ : G →* H)
    (hφ : ∀ {x : G}, x ∈ S.carrier → φ x ∈ T.carrier) {p : (ι → ι → G) × (ι → H)}
    (h1 : ∀ a b, p.1 a b ∈ S.carrier) (h2 : ∀ a, p.2 a ∈ T.carrier) :
    (∀ a b c, (totalD2 φ p).1 a b c ∈ S.carrier) ∧ ∀ a b, (totalD2 φ p).2 a b ∈ T.carrier :=
  ⟨fun a b c => cechD1_mem S h1 a b c,
    fun a b => T.div_mem (cechD0_mem T h2 a b) (hφ (h1 a b))⟩

end Abstract

noncomputable section Meromorphic

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

/-- The units of the ambient meromorphic field: its nonzero elements, as a multiplicative group. -/
abbrev MeroUnits : Type := (meroField (Set.univ : Set ℂ))ˣ

/-- Translation as a unit automorphism. -/
def translationUnitHom (q : ℂ) : MeroUnits →* MeroUnits :=
  Units.map (addTranslationMeroEquiv q).toRingHom.toMonoidHom

theorem translationUnitHom_val (q : ℂ) (u : MeroUnits) :
    ((translationUnitHom q u : MeroUnits) : meroField (Set.univ : Set ℂ))
      = addTranslationMeroEquiv q (u : meroField (Set.univ : Set ℂ)) := rfl

/-- The group differential of the translation, acting on units. -/
def shiftUnitHom (q : ℂ) : MeroUnits →* MeroUnits where
  toFun u := translationUnitHom q u * u⁻¹
  map_one' := by simp
  map_mul' u v := by
    simp only [map_mul, mul_inv_rev]
    simp [mul_comm, mul_left_comm, mul_assoc]

/-- The unit-level group differential is the shift quotient. -/
theorem shiftUnitHom_val (q : ℂ) (u : MeroUnits) :
    ((shiftUnitHom q u : MeroUnits) : meroField (Set.univ : Set ℂ))
      = shiftQuotient q (u : meroField (Set.univ : Set ℂ)) := by
  show ((translationUnitHom q u * u⁻¹ : MeroUnits) : meroField (Set.univ : Set ℂ)) = _
  rw [Units.val_mul, translationUnitHom_val, shiftQuotient, div_eq_mul_inv]
  congr 1
  exact Units.val_inv_eq_inv_val u

theorem one_mem_aSector : (1 : meroField (Set.univ : Set ℂ)) ∈ aSector := by
  refine ⟨oSector_one, ?_⟩
  have h := differentialAlgebraicOver_algebraMap (F := RatFunc ℂ)
    (E := meroField (Set.univ : Set ℂ)) 1
  rwa [map_one] at h

/-- The coefficient sector of the bicomplex: holomorphic, nowhere vanishing, differentially
algebraic units. -/
def aSectorUnits : Sector MeroUnits where
  carrier := {u : MeroUnits | (u : meroField (Set.univ : Set ℂ)) ∈ aSector}
  one_mem := by
    show ((1 : MeroUnits) : meroField (Set.univ : Set ℂ)) ∈ aSector
    rw [Units.val_one]
    exact one_mem_aSector
  mul_mem := by
    intro x y hx hy
    show ((x * y : MeroUnits) : meroField (Set.univ : Set ℂ)) ∈ aSector
    rw [Units.val_mul]
    exact aSector_mul hx hy
  inv_mem := by
    intro x hx
    show ((x⁻¹ : MeroUnits) : meroField (Set.univ : Set ℂ)) ∈ aSector
    rw [Units.val_inv_eq_inv_val]
    exact aSector_inv hx

/-- **The group differential preserves the coefficient sector.** -/
theorem shiftUnitHom_mem_aSectorUnits (q : ℂ) {u : MeroUnits} (hu : u ∈ aSectorUnits.carrier) :
    shiftUnitHom q u ∈ aSectorUnits.carrier := by
  show ((shiftUnitHom q u : MeroUnits) : meroField (Set.univ : Set ℂ)) ∈ aSector
  rw [shiftUnitHom_val]
  exact aSector_shiftQuotient q hu

variable {ι : Type*}

/-- **The group--Čech bicomplex of the ambient field, with coefficients in the anomaly sector.**
The total differential squares to one and every entry it produces from a sector cochain stays in the
sector, in both the Čech and the group direction. -/
theorem totalD_aSector (q : ℂ) {f : ι → MeroUnits}
    (hf : ∀ a, f a ∈ aSectorUnits.carrier) :
    totalD2 (shiftUnitHom q) (totalD1 (shiftUnitHom q) f)
        = (fun _ _ _ => (1 : MeroUnits), fun _ _ => (1 : MeroUnits))
      ∧ (∀ a b, (totalD1 (shiftUnitHom q) f).1 a b ∈ aSectorUnits.carrier)
      ∧ (∀ a, (totalD1 (shiftUnitHom q) f).2 a ∈ aSectorUnits.carrier)
      ∧ (∀ a b c, (totalD2 (shiftUnitHom q) (totalD1 (shiftUnitHom q) f)).1 a b c
          ∈ aSectorUnits.carrier)
      ∧ ∀ a b, (totalD2 (shiftUnitHom q) (totalD1 (shiftUnitHom q) f)).2 a b
          ∈ aSectorUnits.carrier := by
  have hφ : ∀ {x : MeroUnits}, x ∈ aSectorUnits.carrier →
      shiftUnitHom q x ∈ aSectorUnits.carrier := fun hx => shiftUnitHom_mem_aSectorUnits q hx
  obtain ⟨h1, h2⟩ := totalD1_mem aSectorUnits aSectorUnits (shiftUnitHom q) hφ hf
  obtain ⟨h3, h4⟩ := totalD2_mem aSectorUnits aSectorUnits (shiftUnitHom q) hφ h1 h2
  exact ⟨totalD2_totalD1 (shiftUnitHom q) f, h1, h2, h3, h4⟩

/-- **The two-shift bicomplex.**  Both translations act on the same coefficient sector, and the
mixed square of the two group differentials commutes, so the anomaly of a pair of shifts is a class
in the total complex of the bicomplex. -/
theorem shiftUnitHom_comm (sigma tau : ℂ) (u : MeroUnits) :
    shiftUnitHom sigma (shiftUnitHom tau u) = shiftUnitHom tau (shiftUnitHom sigma u) := by
  have hmix : ∀ v : MeroUnits, translationUnitHom sigma (translationUnitHom tau v)
      = translationUnitHom tau (translationUnitHom sigma v) := by
    intro v
    refine Units.ext ?_
    show addTranslationMeroEquiv sigma (addTranslationMeroEquiv tau
        (v : meroField (Set.univ : Set ℂ)))
        = addTranslationMeroEquiv tau (addTranslationMeroEquiv sigma
          (v : meroField (Set.univ : Set ℂ)))
    rw [addTranslationMeroEquiv_add, addTranslationMeroEquiv_add, add_comm]
  show translationUnitHom sigma (shiftUnitHom tau u) * (shiftUnitHom tau u)⁻¹
      = translationUnitHom tau (shiftUnitHom sigma u) * (shiftUnitHom sigma u)⁻¹
  show translationUnitHom sigma (translationUnitHom tau u * u⁻¹)
      * (translationUnitHom tau u * u⁻¹)⁻¹
      = translationUnitHom tau (translationUnitHom sigma u * u⁻¹)
      * (translationUnitHom sigma u * u⁻¹)⁻¹
  rw [map_mul, map_mul, hmix, map_inv, map_inv]
  simp only [mul_inv_rev, inv_inv]
  simp [mul_comm, mul_left_comm, mul_assoc]

end Meromorphic

end GaloisForLFunctions.HTGeometry
