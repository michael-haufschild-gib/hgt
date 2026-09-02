import GaloisForLFunctions.HTGeometry.ConstraintRelativity.FactorFramedTensorGradient
import GaloisForLFunctions.HTGeometry.ConstraintRelativity.SimpleHorizonTransmutation
import GaloisForLFunctions.HTGeometry.ConstraintRelativity.FactorFramedTensorClosedFibre

namespace HTGeometry.ConstraintRelativity

open scoped BigOperators KaehlerDifferential

noncomputable section

def factorKaehlerRelationElement
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) (i : Fin d) : FactorTensorOrder a r :=
  (2 : FactorTensorOrder a r) * factorTensorGenerator a r i

def factorKaehlerCoordinateIdeal
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) (i : Fin d) : Ideal (FactorTensorOrder a r) :=
  Ideal.span {factorKaehlerRelationElement a r i}

abbrev FactorKaehlerPresentation
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) :=
  ∀ i : Fin d, FactorTensorOrder a r ⧸ factorKaehlerCoordinateIdeal a r i

noncomputable instance factorKaehlerPresentationModuleOrder
    {R : Type*} [CommRing R] {d : ℕ} (a : R) (r : Fin d → ℕ) :
    Module (FactorTensorOrder a r) (FactorKaehlerPresentation a r) :=
  Pi.module (Fin d)
    (fun i => FactorTensorOrder a r ⧸ factorKaehlerCoordinateIdeal a r i)
    (FactorTensorOrder a r)

noncomputable instance factorKaehlerPresentationModuleBase
    {R : Type*} [CommRing R] {d : ℕ} (a : R) (r : Fin d → ℕ) :
    Module R (FactorKaehlerPresentation a r) :=
  Pi.module (Fin d)
    (fun i => FactorTensorOrder a r ⧸ factorKaehlerCoordinateIdeal a r i) R

instance factorKaehlerPresentationIsScalarTower
    {R : Type*} [CommRing R] {d : ℕ} (a : R) (r : Fin d → ℕ) :
    IsScalarTower R (FactorTensorOrder a r) (FactorKaehlerPresentation a r) := by
  constructor
  intro c x y
  funext i
  exact IsScalarTower.smul_assoc c x (y i)

def factorKaehlerCoordinateVector
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) (i : Fin d) : FactorKaehlerPresentation a r :=
  Pi.single i (Ideal.Quotient.mk _ 1 :
    FactorTensorOrder a r ⧸ factorKaehlerCoordinateIdeal a r i)

@[simp] theorem factorKaehlerCoordinateVector_same
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) (i : Fin d) :
  factorKaehlerCoordinateVector a r i i =
      (Ideal.Quotient.mk _ 1 :
        FactorTensorOrder a r ⧸ factorKaehlerCoordinateIdeal a r i) := by
  simp [factorKaehlerCoordinateVector]

theorem factorKaehlerCoordinateVector_ne
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) {i j : Fin d} (h : j ≠ i) :
    factorKaehlerCoordinateVector a r i j = 0 := by
  simp [factorKaehlerCoordinateVector, h]

noncomputable def factorKaehlerPolynomialDerivation
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) :
    Derivation R (FactorTensorPolynomial R d) (FactorKaehlerPresentation a r) :=
  MvPolynomial.mkDerivation R (factorKaehlerCoordinateVector a r)

@[simp] theorem factorKaehlerPolynomialDerivation_X
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) (i : Fin d) :
    factorKaehlerPolynomialDerivation a r (MvPolynomial.X i) =
      factorKaehlerCoordinateVector a r i := by
  rw [factorKaehlerPolynomialDerivation, MvPolynomial.mkDerivation_X]

theorem factorKaehlerPolynomialDerivation_relation_eq_zero
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) (i : Fin d) :
    factorKaehlerPolynomialDerivation a r (factorTensorRelation a r i) = 0 := by
  rw [factorTensorRelation, map_sub, pow_two, Derivation.leibniz]
  rw [show MvPolynomial.C (a ^ (2 * r i)) =
      algebraMap R (FactorTensorPolynomial R d) (a ^ (2 * r i)) by rfl,
    (factorKaehlerPolynomialDerivation a r).map_algebraMap]
  simp only [factorKaehlerPolynomialDerivation_X]
  funext j
  simp only [Pi.sub_apply, Pi.zero_apply, sub_zero, Pi.add_apply, Pi.smul_apply]
  by_cases hji : j = i
  · subst j
    rw [factorKaehlerCoordinateVector_same]
    have hterm :
        (MvPolynomial.X i : FactorTensorPolynomial R d) •
            (Ideal.Quotient.mk _ 1 :
              FactorTensorOrder a r ⧸ factorKaehlerCoordinateIdeal a r i) =
          Ideal.Quotient.mk _ (factorTensorGenerator a r i) := by
      calc
        (MvPolynomial.X i : FactorTensorPolynomial R d) •
            (Ideal.Quotient.mk _ 1 :
              FactorTensorOrder a r ⧸ factorKaehlerCoordinateIdeal a r i) =
            (algebraMap (FactorTensorPolynomial R d) (FactorTensorOrder a r)
              (MvPolynomial.X i)) • Ideal.Quotient.mk _ 1 :=
          (IsScalarTower.algebraMap_smul
            (R := FactorTensorPolynomial R d) (FactorTensorOrder a r)
            (MvPolynomial.X i)
            (Ideal.Quotient.mk _ 1 :
              FactorTensorOrder a r ⧸ factorKaehlerCoordinateIdeal a r i)).symm
        _ = factorTensorGenerator a r i • Ideal.Quotient.mk _ 1 := by
          rfl
        _ = Ideal.Quotient.mk _ (factorTensorGenerator a r i) := by
          change Ideal.Quotient.mk _ (factorTensorGenerator a r i * 1) = _
          rw [mul_one]
    rw [hterm]
    change
      (Ideal.Quotient.mk _ (factorTensorGenerator a r i) :
          FactorTensorOrder a r ⧸ factorKaehlerCoordinateIdeal a r i) +
        Ideal.Quotient.mk _ (factorTensorGenerator a r i) = 0
    rw [← map_add]
    rw [Ideal.Quotient.eq_zero_iff_mem]
    rw [factorKaehlerCoordinateIdeal, factorKaehlerRelationElement,
      Ideal.mem_span_singleton]
    exact ⟨1, by rw [mul_one, two_mul]⟩
  · rw [factorKaehlerCoordinateVector_ne a r hji]
    change ((MvPolynomial.X i : FactorTensorPolynomial R d) •
      (0 : FactorTensorOrder a r ⧸ factorKaehlerCoordinateIdeal a r j)) +
      (MvPolynomial.X i : FactorTensorPolynomial R d) • 0 = 0
    have hz : (MvPolynomial.X i : FactorTensorPolynomial R d) •
        (0 : FactorTensorOrder a r ⧸ factorKaehlerCoordinateIdeal a r j) = 0 := by
      calc
        (MvPolynomial.X i : FactorTensorPolynomial R d) •
            (0 : FactorTensorOrder a r ⧸ factorKaehlerCoordinateIdeal a r j) =
            algebraMap (FactorTensorPolynomial R d) (FactorTensorOrder a r)
              (MvPolynomial.X i) • 0 :=
          (IsScalarTower.algebraMap_smul
            (R := FactorTensorPolynomial R d) (FactorTensorOrder a r)
            (MvPolynomial.X i)
            (0 : FactorTensorOrder a r ⧸ factorKaehlerCoordinateIdeal a r j)).symm
        _ = 0 := smul_zero _
    rw [hz, add_zero]

theorem factorKaehlerPolynomialDerivation_eq_zero_of_mem_relationIdeal
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) {p : FactorTensorPolynomial R d}
    (hp : p ∈ factorTensorRelationIdeal a r) :
    factorKaehlerPolynomialDerivation a r p = 0 := by
  let D := factorKaehlerPolynomialDerivation a r
  refine Submodule.span_induction
    (p := fun q _ => D q = 0) ?_ ?_ ?_ ?_ hp
  · intro q hq
    obtain ⟨i, rfl⟩ := hq
    exact factorKaehlerPolynomialDerivation_relation_eq_zero a r i
  · exact map_zero D
  · intro x y _ _ hx hy
    rw [map_add, hx, hy]
    exact add_zero (0 : FactorKaehlerPresentation a r)
  · intro c x hxI hx
    change D (c * x) = 0
    rw [Derivation.leibniz, hx]
    simp only [smul_zero]
    have hxm : (Ideal.Quotient.mk _ x : FactorTensorOrder a r) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact hxI
    have hscalar : x • D c =
        (Ideal.Quotient.mk (factorTensorRelationIdeal a r) x :
          FactorTensorOrder a r) • D c := rfl
    rw [hscalar]
    rw [hxm]
    change (0 : FactorKaehlerPresentation a r) +
      (0 : FactorTensorOrder a r) • D c = 0
    have hz : (0 : FactorTensorOrder a r) • D c = 0 := by
      funext j
      change (0 : FactorTensorOrder a r) • (D c j) = 0
      exact zero_smul (FactorTensorOrder a r) (D c j)
    rw [hz]
    exact add_zero (0 : FactorKaehlerPresentation a r)

def factorOrderKaehlerCoordinateAddHom
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) :
    FactorTensorOrder a r →+ FactorKaehlerPresentation a r :=
  QuotientAddGroup.lift (factorTensorRelationIdeal a r).toAddSubgroup
    (factorKaehlerPolynomialDerivation a r).toLinearMap.toAddMonoidHom
    (fun _p hp => factorKaehlerPolynomialDerivation_eq_zero_of_mem_relationIdeal a r hp)

def factorOrderKaehlerCoordinateLinearMap
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) :
    FactorTensorOrder a r →ₗ[R] FactorKaehlerPresentation a r where
  toFun := factorOrderKaehlerCoordinateAddHom a r
  map_add' := map_add _
  map_smul' c x := by
    induction x using Quotient.inductionOn' with
    | _ p => exact (factorKaehlerPolynomialDerivation a r).toLinearMap.map_smul c p

noncomputable def factorOrderKaehlerCoordinateDerivation
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) :
    Derivation R (FactorTensorOrder a r) (FactorKaehlerPresentation a r) := by
  let D := factorKaehlerPolynomialDerivation a r
  let L := factorOrderKaehlerCoordinateLinearMap a r
  exact Derivation.mk' (A := FactorTensorOrder a r)
    (M := FactorKaehlerPresentation a r) L (by
    intro x y
    induction x using Quotient.inductionOn' with
    | _ x =>
      induction y using Quotient.inductionOn' with
      | _ y =>
        change D (x * y) =
          Ideal.Quotient.mk _ x • D y + Ideal.Quotient.mk _ y • D x
        rw [Derivation.leibniz]
        rfl)

@[simp] theorem factorOrderKaehlerCoordinateDerivation_generator
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) (i : Fin d) :
    factorOrderKaehlerCoordinateDerivation a r (factorTensorGenerator a r i) =
      factorKaehlerCoordinateVector a r i := by
  rw [factorOrderKaehlerCoordinateDerivation, factorTensorGenerator]
  change factorKaehlerPolynomialDerivation a r (MvPolynomial.X i) = _
  rw [factorKaehlerPolynomialDerivation_X]

theorem factorTensorRelation_class_eq_zero
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) (i : Fin d) :
    (Ideal.Quotient.mk _ (factorTensorRelation a r i) :
      FactorTensorOrder a r) = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_range_self i)

theorem factorKaehlerRelationElement_smul_D_generator_eq_zero
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) (i : Fin d) :
    factorKaehlerRelationElement a r i •
        KaehlerDifferential.D R (FactorTensorOrder a r)
          (factorTensorGenerator a r i) = 0 := by
  let A := FactorTensorOrder a r
  let f := factorTensorGenerator a r i
  let D := KaehlerDifferential.D R A
  have hsq : f ^ 2 = algebraMap R A (a ^ (2 * r i)) := by
    apply sub_eq_zero.mp
    change (Ideal.Quotient.mk _ (factorTensorRelation a r i) : A) = 0
    exact factorTensorRelation_class_eq_zero a r i
  have hz := congrArg D hsq
  have hder : f • D f + f • D f = 0 := by
    simpa [pow_two, Derivation.leibniz] using hz
  change ((2 : A) * f) • D f = 0
  rw [two_mul, add_smul]
  exact hder

def factorKaehlerGeneratorLine
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) (i : Fin d) :
    FactorTensorOrder a r →ₗ[FactorTensorOrder a r]
      Ω[FactorTensorOrder a r⁄R] where
  toFun c := c • KaehlerDifferential.D R (FactorTensorOrder a r)
    (factorTensorGenerator a r i)
  map_add' x y := add_smul x y _
  map_smul' c x := by
    change (c * x) • _ = c • x • _
    rw [mul_smul]

def factorKaehlerCoordinateToDifferential
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) (i : Fin d) :
    (FactorTensorOrder a r ⧸ factorKaehlerCoordinateIdeal a r i) →ₗ[
      FactorTensorOrder a r] Ω[FactorTensorOrder a r⁄R] :=
  (factorKaehlerCoordinateIdeal a r i).liftQ
    (factorKaehlerGeneratorLine a r i) (by
      intro x hx
      rw [LinearMap.mem_ker]
      rw [factorKaehlerCoordinateIdeal, Ideal.mem_span_singleton] at hx
      obtain ⟨c, rfl⟩ := hx
      change (factorKaehlerRelationElement a r i * c) •
        KaehlerDifferential.D R (FactorTensorOrder a r)
          (factorTensorGenerator a r i) =
        (0 : Ω[FactorTensorOrder a r⁄R])
      rw [mul_comm, mul_smul,
        factorKaehlerRelationElement_smul_D_generator_eq_zero, smul_zero])

@[simp] theorem factorKaehlerCoordinateToDifferential_mk
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) (i : Fin d) (c : FactorTensorOrder a r) :
    factorKaehlerCoordinateToDifferential a r i (Ideal.Quotient.mk _ c) =
      c • KaehlerDifferential.D R (FactorTensorOrder a r)
        (factorTensorGenerator a r i) := rfl

def factorKaehlerPresentationToDifferential
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) :
    FactorKaehlerPresentation a r →ₗ[FactorTensorOrder a r]
      Ω[FactorTensorOrder a r⁄R] :=
  ∑ i : Fin d, (factorKaehlerCoordinateToDifferential a r i).comp
    (LinearMap.proj i)

theorem factorKaehlerPresentationToDifferential_apply
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) (x : FactorKaehlerPresentation a r) :
    factorKaehlerPresentationToDifferential a r x =
      ∑ i : Fin d, factorKaehlerCoordinateToDifferential a r i (x i) := by
  rw [factorKaehlerPresentationToDifferential, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rfl

noncomputable def factorKaehlerDifferentialToPresentation
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) :
    Ω[FactorTensorOrder a r⁄R] →ₗ[FactorTensorOrder a r]
      FactorKaehlerPresentation a r := by
  exact Derivation.liftKaehlerDifferential
    (R := R) (S := FactorTensorOrder a r)
    (M := FactorKaehlerPresentation a r)
    (factorOrderKaehlerCoordinateDerivation a r)

@[simp] theorem factorKaehlerDifferentialToPresentation_D_generator
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) (i : Fin d) :
    factorKaehlerDifferentialToPresentation a r
        (KaehlerDifferential.D R (FactorTensorOrder a r)
          (factorTensorGenerator a r i)) =
      factorKaehlerCoordinateVector a r i := by
  rw [factorKaehlerDifferentialToPresentation,
    Derivation.liftKaehlerDifferential_comp_D,
    factorOrderKaehlerCoordinateDerivation_generator]

theorem factorKaehlerDifferentialToPresentation_coordinate
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) (i : Fin d)
    (x : FactorTensorOrder a r ⧸ factorKaehlerCoordinateIdeal a r i) :
    factorKaehlerDifferentialToPresentation a r
        (factorKaehlerCoordinateToDifferential a r i x) =
      Pi.single i x := by
  induction x using Quotient.inductionOn' with
  | _ c =>
    change factorKaehlerDifferentialToPresentation a r
        (factorKaehlerCoordinateToDifferential a r i (Ideal.Quotient.mk _ c)) =
      Pi.single i (Ideal.Quotient.mk _ c)
    rw [factorKaehlerCoordinateToDifferential_mk, map_smul,
      factorKaehlerDifferentialToPresentation_D_generator]
    funext j
    by_cases hji : j = i
    · subst j
      rw [Pi.smul_apply, factorKaehlerCoordinateVector_same, Pi.single_eq_same]
      change Ideal.Quotient.mk _ (c * 1) = Ideal.Quotient.mk _ c
      rw [mul_one]
    · simp [factorKaehlerCoordinateVector_ne a r hji, hji]

theorem factorKaehlerDifferentialToPresentation_comp_presentation
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) (x : FactorKaehlerPresentation a r) :
    factorKaehlerDifferentialToPresentation a r
        (factorKaehlerPresentationToDifferential a r x) = x := by
  rw [factorKaehlerPresentationToDifferential_apply, map_sum]
  simp_rw [factorKaehlerDifferentialToPresentation_coordinate]
  funext j
  classical
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    exact Pi.single_eq_of_ne
      (M := fun k => FactorTensorOrder a r ⧸ factorKaehlerCoordinateIdeal a r k)
      (Ne.symm hij) (x i)
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

theorem factorTensorOrder_derivation_ext
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ)
    {M : Type*} [AddCommGroup M] [Module R M]
    [Module (FactorTensorOrder a r) M]
    (D₁ D₂ : Derivation R (FactorTensorOrder a r) M)
    (h : ∀ i, D₁ (factorTensorGenerator a r i) =
      D₂ (factorTensorGenerator a r i)) : D₁ = D₂ := by
  ext x
  induction x using Quotient.inductionOn' with
  | _ p =>
    induction p using MvPolynomial.induction_on with
    | C c =>
      change D₁ (algebraMap R (FactorTensorOrder a r) c) =
        D₂ (algebraMap R (FactorTensorOrder a r) c)
      rw [D₁.map_algebraMap, D₂.map_algebraMap]
    | add p q hp hq =>
      have hmk (z : FactorTensorPolynomial R d) :
          (Quotient.mk'' z : FactorTensorOrder a r) = Ideal.Quotient.mk _ z := rfl
      have hp' : D₁ (Ideal.Quotient.mk _ p) = D₂ (Ideal.Quotient.mk _ p) := by
        rw [← hmk]
        exact hp
      have hq' : D₁ (Ideal.Quotient.mk _ q) = D₂ (Ideal.Quotient.mk _ q) := by
        rw [← hmk]
        exact hq
      change D₁ (Ideal.Quotient.mk _ p + Ideal.Quotient.mk _ q) =
        D₂ (Ideal.Quotient.mk _ p + Ideal.Quotient.mk _ q)
      rw [map_add, map_add, hp', hq']
    | mul_X p i hp =>
      have hmk (z : FactorTensorPolynomial R d) :
          (Quotient.mk'' z : FactorTensorOrder a r) = Ideal.Quotient.mk _ z := rfl
      have hp' : D₁ (Ideal.Quotient.mk _ p) = D₂ (Ideal.Quotient.mk _ p) := by
        rw [← hmk]
        exact hp
      change D₁ (Ideal.Quotient.mk _ p * factorTensorGenerator a r i) =
        D₂ (Ideal.Quotient.mk _ p * factorTensorGenerator a r i)
      rw [D₁.leibniz, D₂.leibniz, hp', h i]

theorem factorKaehlerPresentationToDifferential_coordinateVector
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) (i : Fin d) :
    factorKaehlerPresentationToDifferential a r
        (factorKaehlerCoordinateVector a r i) =
      KaehlerDifferential.D R (FactorTensorOrder a r)
        (factorTensorGenerator a r i) := by
  classical
  rw [factorKaehlerPresentationToDifferential_apply]
  rw [Finset.sum_eq_single i]
  · rw [factorKaehlerCoordinateVector_same,
      factorKaehlerCoordinateToDifferential_mk, one_smul]
  · intro j _ hji
    have hj : j ≠ i := hji
    rw [factorKaehlerCoordinateVector_ne a r hj, map_zero]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

theorem factorKaehlerPresentationToDifferential_comp_differential
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) (x : Ω[FactorTensorOrder a r⁄R]) :
    factorKaehlerPresentationToDifferential a r
        (factorKaehlerDifferentialToPresentation a r x) = x := by
  let f := (factorKaehlerPresentationToDifferential a r).comp
    (factorKaehlerDifferentialToPresentation a r)
  have hf : f = LinearMap.id := by
    apply Derivation.liftKaehlerDifferential_unique
    apply factorTensorOrder_derivation_ext a r
    intro i
    change factorKaehlerPresentationToDifferential a r
      (factorKaehlerDifferentialToPresentation a r
        (KaehlerDifferential.D R (FactorTensorOrder a r)
          (factorTensorGenerator a r i))) = _
    rw [factorKaehlerDifferentialToPresentation_D_generator,
      factorKaehlerPresentationToDifferential_coordinateVector]
    rfl
  exact LinearMap.congr_fun hf x

/-- Card `(5)`: exact Kähler presentation for the literal factor tensor order. -/
noncomputable def factorKaehlerEquivPresentation
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) :
    Ω[FactorTensorOrder a r⁄R] ≃ₗ[FactorTensorOrder a r]
      FactorKaehlerPresentation a r where
  toLinearMap := factorKaehlerDifferentialToPresentation a r
  invFun := factorKaehlerPresentationToDifferential a r
  left_inv := factorKaehlerPresentationToDifferential_comp_differential a r
  right_inv := factorKaehlerDifferentialToPresentation_comp_presentation a r

def factorGeneratorIdeal
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) (i : Fin d) : Ideal (FactorTensorOrder a r) :=
  Ideal.span {factorTensorGenerator a r i}

abbrev FactorCotangentQuotient
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) :=
  ∀ i : Fin d, FactorTensorOrder a r ⧸ factorGeneratorIdeal a r i

theorem factorKaehlerCoordinateIdeal_eq_generatorIdeal_of_isUnit_two
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) (h2 : IsUnit (2 : R)) (i : Fin d) :
    factorKaehlerCoordinateIdeal a r i = factorGeneratorIdeal a r i := by
  obtain ⟨u, hu⟩ := h2
  let v : (FactorTensorOrder a r)ˣ :=
    Units.map (algebraMap R (FactorTensorOrder a r)) u
  have hv : (v : FactorTensorOrder a r) = 2 := by
    change algebraMap R (FactorTensorOrder a r) (u : R) = 2
    rw [hu]
    exact map_ofNat (algebraMap R (FactorTensorOrder a r)) 2
  rw [factorKaehlerCoordinateIdeal, factorKaehlerRelationElement,
    factorGeneratorIdeal, ← hv]
  exact span_singleton_unit_mul v (factorTensorGenerator a r i)

private def factorQuotientLinearEquivOfEq
    {A : Type*} [CommRing A] {I J : Ideal A} (h : I = J) :
    (A ⧸ I) ≃ₗ[A] (A ⧸ J) := by
  subst J
  exact LinearEquiv.refl A (A ⧸ I)

noncomputable def factorKaehlerPresentationEquivCotangentQuotient
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) (h2 : IsUnit (2 : R)) :
    FactorKaehlerPresentation a r ≃ₗ[FactorTensorOrder a r]
      FactorCotangentQuotient a r where
  toFun x i := factorQuotientLinearEquivOfEq
    (factorKaehlerCoordinateIdeal_eq_generatorIdeal_of_isUnit_two a r h2 i) (x i)
  invFun x i := (factorQuotientLinearEquivOfEq
    (factorKaehlerCoordinateIdeal_eq_generatorIdeal_of_isUnit_two a r h2 i)).symm (x i)
  left_inv x := by
    funext i
    exact (factorQuotientLinearEquivOfEq
      (factorKaehlerCoordinateIdeal_eq_generatorIdeal_of_isUnit_two a r h2 i)).symm_apply_apply (x i)
  right_inv x := by
    funext i
    exact (factorQuotientLinearEquivOfEq
      (factorKaehlerCoordinateIdeal_eq_generatorIdeal_of_isUnit_two a r h2 i)).apply_symm_apply (x i)
  map_add' x y := by
    funext i
    exact (factorQuotientLinearEquivOfEq
      (factorKaehlerCoordinateIdeal_eq_generatorIdeal_of_isUnit_two a r h2 i)).map_add (x i) (y i)
  map_smul' c x := by
    funext i
    exact (factorQuotientLinearEquivOfEq
      (factorKaehlerCoordinateIdeal_eq_generatorIdeal_of_isUnit_two a r h2 i)).map_smul c (x i)

/-- Card `(5)`, unit-normalized form: if `2` is a base unit then
`Ω[A_r/R] ≅ ⊕_i A_r/(f_i) df_i`. -/
noncomputable def factorKaehlerEquivCotangentQuotient
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) (h2 : IsUnit (2 : R)) :
    Ω[FactorTensorOrder a r⁄R] ≃ₗ[FactorTensorOrder a r]
      FactorCotangentQuotient a r :=
  (factorKaehlerEquivPresentation a r).trans
    (factorKaehlerPresentationEquivCotangentQuotient a r h2)

theorem factorOrderToGradientTarget_surjective
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) :
    Function.Surjective (factorOrderToGradientTarget a r) := by
  intro y
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨Ideal.Quotient.mk _ p, rfl⟩

/-- The literal range of the Kähler soldering is an ideal because `A_r → A_r/(F)` is
surjective. -/
def factorKaehlerSolderingRangeIdeal
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) : Ideal (FactorGradientTarget a r) where
  carrier := LinearMap.range (factorKaehlerSoldering a r)
  zero_mem' := ⟨0, map_zero _⟩
  add_mem' := by
    rintro x y ⟨u, rfl⟩ ⟨v, rfl⟩
    exact ⟨u + v, map_add _ _ _⟩
  smul_mem' := by
    intro c y hy
    obtain ⟨x, rfl⟩ := factorOrderToGradientTarget_surjective a r c
    obtain ⟨u, rfl⟩ := hy
    refine ⟨x • u, ?_⟩
    exact (factorKaehlerSoldering a r).map_smul x u

theorem factorKaehlerSolderingRangeIdeal_mem_iff
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) (x : FactorGradientTarget a r) :
    x ∈ factorKaehlerSolderingRangeIdeal a r ↔
      x ∈ LinearMap.range (factorKaehlerSoldering a r) := Iff.rfl

def factorGradientTargetComplementIdeal
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) : Ideal (FactorGradientTarget a r) :=
  Ideal.map (Ideal.Quotient.mk (factorGradientPolynomialIdeal a r))
    factorComplementIdeal

theorem factorGradientTarget_complement_mem
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) (i : Fin d) :
    (Ideal.Quotient.mk _ (factorTensorComplement (R := R) i) :
      FactorGradientTarget a r) ∈ factorGradientTargetComplementIdeal a r := by
  rw [factorGradientTargetComplementIdeal, factorComplementIdeal, Ideal.map_span]
  apply Ideal.subset_span
  exact ⟨factorTensorComplement (R := R) i,
    Set.mem_range_self i, rfl⟩

theorem factorKaehlerSoldering_coordinate_mem_complementIdeal
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) (i : Fin d)
    (x : FactorTensorOrder a r ⧸ factorKaehlerCoordinateIdeal a r i) :
    factorKaehlerSoldering a r
        (factorKaehlerCoordinateToDifferential a r i x) ∈
      factorGradientTargetComplementIdeal a r := by
  induction x using Quotient.inductionOn' with
  | _ c =>
    change factorKaehlerSoldering a r
        (factorKaehlerCoordinateToDifferential a r i (Ideal.Quotient.mk _ c)) ∈ _
    rw [factorKaehlerCoordinateToDifferential_mk, map_smul,
      factorKaehlerSoldering_D_generator]
    change factorOrderToGradientTarget a r c *
        (Ideal.Quotient.mk _ (factorTensorComplement (R := R) i) :
          FactorGradientTarget a r) ∈ factorGradientTargetComplementIdeal a r
    exact Ideal.mul_mem_left _ _ (factorGradientTarget_complement_mem a r i)

theorem factorKaehlerSolderingRangeIdeal_eq_complementIdeal
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) :
    factorKaehlerSolderingRangeIdeal a r =
      factorGradientTargetComplementIdeal a r := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    rw [← factorKaehlerPresentationToDifferential_comp_differential a r x,
      factorKaehlerPresentationToDifferential_apply, map_sum]
    exact Ideal.sum_mem _ fun i _ =>
      factorKaehlerSoldering_coordinate_mem_complementIdeal a r i
        (factorKaehlerDifferentialToPresentation a r x i)
  · rw [factorGradientTargetComplementIdeal, factorComplementIdeal, Ideal.map_span]
    apply Ideal.span_le.mpr
    rintro y ⟨q, ⟨i, rfl⟩, rfl⟩
    change (Ideal.Quotient.mk _ (factorTensorComplement (R := R) i) :
      FactorGradientTarget a r) ∈ factorKaehlerSolderingRangeIdeal a r
    exact ⟨KaehlerDifferential.D R (FactorTensorOrder a r)
      (factorTensorGenerator a r i), factorKaehlerSoldering_D_generator a r i⟩

abbrev FactorKaehlerSolderingCokernel
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) :=
  FactorGradientTarget a r ⧸ factorKaehlerSolderingRangeIdeal a r

theorem factorTensorPotential_mem_complementIdeal
    {R : Type*} [CommRing R] {d : ℕ} [NeZero d] :
    factorTensorPotential (R := R) d ∈
      (factorComplementIdeal : Ideal (FactorTensorPolynomial R d)) := by
  let i : Fin d := Classical.choice (inferInstance : Nonempty (Fin d))
  rw [← factorTensorGenerator_mul_complement (R := R) i]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self i))

theorem factorGradientPolynomialIdeal_le_jacobianPolynomialIdeal
    {R : Type*} [CommRing R] {d : ℕ} [NeZero d]
    (a : R) (r : Fin d → ℕ) :
    factorGradientPolynomialIdeal a r ≤ factorJacobianPolynomialIdeal a r := by
  rw [factorGradientPolynomialIdeal, factorJacobianPolynomialIdeal]
  apply sup_le
  · exact le_sup_left
  · apply Ideal.span_le.mpr
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact (show (factorComplementIdeal :
      Ideal (FactorTensorPolynomial R d)) ≤
        factorTensorRelationIdeal a r ⊔ factorComplementIdeal from le_sup_right)
      (factorTensorPotential_mem_complementIdeal (R := R) (d := d))

noncomputable def factorGradientToJacobian
    {R : Type*} [CommRing R] {d : ℕ} [NeZero d]
    (a : R) (r : Fin d → ℕ) :
    FactorGradientTarget a r →+* FactorJacobianAlgebra a r :=
  Ideal.Quotient.lift (factorGradientPolynomialIdeal a r)
    (Ideal.Quotient.mk (factorJacobianPolynomialIdeal a r)) (by
      intro p hp
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact factorGradientPolynomialIdeal_le_jacobianPolynomialIdeal a r hp)

theorem factorGradientToJacobian_surjective
    {R : Type*} [CommRing R] {d : ℕ} [NeZero d]
    (a : R) (r : Fin d → ℕ) :
    Function.Surjective (factorGradientToJacobian a r) := by
  intro y
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨Ideal.Quotient.mk _ p, rfl⟩

theorem factorGradientTargetComplementIdeal_comap
    {R : Type*} [CommRing R] {d : ℕ} [NeZero d]
    (a : R) (r : Fin d → ℕ) :
    Ideal.comap (Ideal.Quotient.mk (factorGradientPolynomialIdeal a r))
        (factorGradientTargetComplementIdeal a r) =
      factorJacobianPolynomialIdeal a r := by
  rw [factorGradientTargetComplementIdeal,
    Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
  have hker : Ideal.comap (Ideal.Quotient.mk (factorGradientPolynomialIdeal a r)) ⊥ =
      factorGradientPolynomialIdeal a r := by
    ext p
    rw [Ideal.mem_comap, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
  rw [hker]
  apply le_antisymm
  · apply sup_le
    · rw [factorJacobianPolynomialIdeal]
      exact le_sup_right
    · rw [factorGradientPolynomialIdeal]
      apply sup_le
      · rw [factorJacobianPolynomialIdeal]
        exact le_sup_left
      · exact (Ideal.span_le.mpr fun x hx => by
          rw [Set.mem_singleton_iff] at hx
          subst x
          exact (show (factorComplementIdeal :
            Ideal (FactorTensorPolynomial R d)) ≤
              factorJacobianPolynomialIdeal a r by
                rw [factorJacobianPolynomialIdeal]
                exact le_sup_right)
            (factorTensorPotential_mem_complementIdeal (R := R) (d := d)))
  · rw [factorJacobianPolynomialIdeal]
    apply sup_le
    · exact le_trans
        (show factorTensorRelationIdeal a r ≤
          factorGradientPolynomialIdeal a r by
            rw [factorGradientPolynomialIdeal]
            exact le_sup_left)
        le_sup_right
    · exact le_sup_left

theorem factorGradientToJacobian_ker
    {R : Type*} [CommRing R] {d : ℕ} [NeZero d]
    (a : R) (r : Fin d → ℕ) :
    RingHom.ker (factorGradientToJacobian a r) =
      factorGradientTargetComplementIdeal a r := by
  ext x
  induction x using Quotient.inductionOn' with
  | _ p =>
    change factorGradientToJacobian a r (Ideal.Quotient.mk _ p) = 0 ↔
      Ideal.Quotient.mk _ p ∈ factorGradientTargetComplementIdeal a r
    rw [show factorGradientToJacobian a r (Ideal.Quotient.mk _ p) =
        (Ideal.Quotient.mk _ p : FactorJacobianAlgebra a r) by rfl,
      Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap,
      factorGradientTargetComplementIdeal_comap]

private def factorIdealQuotientRingEquivOfEq
    {A : Type*} [CommRing A] {I J : Ideal A} (h : I = J) :
    A ⧸ I ≃+* A ⧸ J := by
  subst J
  exact RingEquiv.refl _

/-- Cards `(7)` and `(10c)`: cokernel of literal universal Kähler soldering is the literal
factor Jacobian/critical algebra. -/
noncomputable def factorKaehlerSolderingCokernelEquivJacobian
    {R : Type*} [CommRing R] {d : ℕ} [NeZero d]
    (a : R) (r : Fin d → ℕ) :
    FactorKaehlerSolderingCokernel a r ≃+* FactorJacobianAlgebra a r :=
  (factorIdealQuotientRingEquivOfEq
    ((factorKaehlerSolderingRangeIdeal_eq_complementIdeal a r).trans
      (factorGradientToJacobian_ker a r).symm)).trans
    (RingHom.quotientKerEquivOfSurjective
      (factorGradientToJacobian_surjective a r))

end

end HTGeometry.ConstraintRelativity
