import GaloisForLFunctions.HTGeometry.ConstraintRelativity.FactorFramedTensorJacobian
import Mathlib.Algebra.MvPolynomial.Derivation

/-!
# Literal polynomial tensor-order and source-framed gradient
-/

namespace HTGeometry.ConstraintRelativity

open scoped BigOperators KaehlerDifferential

noncomputable section

abbrev FactorTensorPolynomial (R : Type*) [CommSemiring R] (d : ℕ) :=
  MvPolynomial (Fin d) R

def factorTensorRelation
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) (i : Fin d) : FactorTensorPolynomial R d :=
  MvPolynomial.X i ^ 2 - MvPolynomial.C (a ^ (2 * r i))

def factorTensorRelationIdeal
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) : Ideal (FactorTensorPolynomial R d) :=
  Ideal.span (Set.range (factorTensorRelation a r))

/-- Literal tensor order presentation `R[f_i]/(f_i²-a^(2r_i))`. -/
abbrev FactorTensorOrder
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) :=
  FactorTensorPolynomial R d ⧸ factorTensorRelationIdeal a r

def factorTensorGenerator
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) (i : Fin d) : FactorTensorOrder a r :=
  Ideal.Quotient.mk _ (MvPolynomial.X i)

def factorTensorPotential
    {R : Type*} [CommRing R] (d : ℕ) : FactorTensorPolynomial R d :=
  ∏ i : Fin d, MvPolynomial.X i

def factorTensorComplement
    {R : Type*} [CommRing R] {d : ℕ} (i : Fin d) : FactorTensorPolynomial R d :=
  ∏ j ∈ (Finset.univ.erase i), MvPolynomial.X j

theorem factorTensorGenerator_mul_complement
    {R : Type*} [CommRing R] {d : ℕ} (i : Fin d) :
    MvPolynomial.X i * factorTensorComplement (R := R) i =
      factorTensorPotential (R := R) d := by
  rw [factorTensorComplement, factorTensorPotential,
    Finset.mul_prod_erase _ _ (Finset.mem_univ i)]

def factorGradientPolynomialIdeal
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) : Ideal (FactorTensorPolynomial R d) :=
  factorTensorRelationIdeal a r ⊔ Ideal.span {factorTensorPotential (R := R) d}

/-- Exact `A_r/(F)` target presentation. -/
abbrev FactorGradientTarget
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) :=
  FactorTensorPolynomial R d ⧸ factorGradientPolynomialIdeal a r

def factorPolynomialGradient
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) :
    Derivation R (FactorTensorPolynomial R d) (FactorGradientTarget a r) :=
  MvPolynomial.mkDerivation R fun i =>
    Ideal.Quotient.mk _ (factorTensorComplement (R := R) i)

@[simp] theorem factorPolynomialGradient_X
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) (i : Fin d) :
    factorPolynomialGradient a r (MvPolynomial.X i) =
      Ideal.Quotient.mk _ (factorTensorComplement (R := R) i) := by
  rw [factorPolynomialGradient, MvPolynomial.mkDerivation_X]

theorem factorTensorRelation_mem_gradientIdeal
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) (i : Fin d) :
    factorTensorRelation a r i ∈ factorGradientPolynomialIdeal a r := by
  apply (show factorTensorRelationIdeal a r ≤ factorGradientPolynomialIdeal a r from le_sup_left)
  exact Ideal.subset_span (Set.mem_range_self i)

theorem factorTensorPotential_mem_gradientIdeal
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) :
    factorTensorPotential (R := R) d ∈ factorGradientPolynomialIdeal a r := by
  apply (show Ideal.span {factorTensorPotential (R := R) d} ≤
    factorGradientPolynomialIdeal a r from le_sup_right)
  exact Ideal.subset_span rfl

/-- Card `(10b)`: every quadratic tensor relation is killed exactly because its gradient is
`2F = 0` in `A_r/(F)`. -/
theorem factorPolynomialGradient_relation_eq_zero
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) (i : Fin d) :
    factorPolynomialGradient a r (factorTensorRelation a r i) = 0 := by
  rw [factorTensorRelation, map_sub, pow_two, Derivation.leibniz]
  rw [show MvPolynomial.C (a ^ (2 * r i)) =
      algebraMap R (FactorTensorPolynomial R d) (a ^ (2 * r i)) by rfl,
    (factorPolynomialGradient a r).map_algebraMap, sub_zero]
  simp only [factorPolynomialGradient_X]
  change (Ideal.Quotient.mk _
      (MvPolynomial.X i * factorTensorComplement (R := R) i) :
        FactorGradientTarget a r) +
    Ideal.Quotient.mk _
      (MvPolynomial.X i * factorTensorComplement (R := R) i) = 0
  rw [factorTensorGenerator_mul_complement]
  have hF : (Ideal.Quotient.mk _ (factorTensorPotential (R := R) d) :
      FactorGradientTarget a r) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact factorTensorPotential_mem_gradientIdeal a r
  rw [hF, zero_add]

theorem factorTensorRelationIdeal_le_gradientIdeal
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) :
    factorTensorRelationIdeal a r ≤ factorGradientPolynomialIdeal a r :=
  le_sup_left

theorem factorPolynomialGradient_eq_zero_of_mem_relationIdeal
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) {p : FactorTensorPolynomial R d}
    (hp : p ∈ factorTensorRelationIdeal a r) :
    factorPolynomialGradient a r p = 0 := by
  let D := factorPolynomialGradient a r
  refine Submodule.span_induction
    (p := fun q _ => D q = 0) ?_ ?_ ?_ ?_ hp
  · intro q hq
    obtain ⟨i, rfl⟩ := hq
    exact factorPolynomialGradient_relation_eq_zero a r i
  · exact map_zero D
  · intro x y _ _ hx hy
    rw [map_add, hx, hy, add_zero]
  · intro c x hxI hx
    change D (c * x) = 0
    rw [Derivation.leibniz, hx]
    simp only [smul_zero, zero_add]
    have hxJ : x ∈ factorGradientPolynomialIdeal a r :=
      factorTensorRelationIdeal_le_gradientIdeal a r hxI
    have hxm : (Ideal.Quotient.mk _ x : FactorGradientTarget a r) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact hxJ
    change (Ideal.Quotient.mk _ x : FactorGradientTarget a r) * D c = 0
    rw [hxm, zero_mul]

noncomputable def factorOrderToGradientTarget
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) :
    FactorTensorOrder a r →ₐ[R] FactorGradientTarget a r :=
  Ideal.Quotient.liftₐ (factorTensorRelationIdeal a r)
    (Ideal.Quotient.mkₐ R (factorGradientPolynomialIdeal a r)) (by
      intro p hp
      change (Ideal.Quotient.mk _ p : FactorGradientTarget a r) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact factorTensorRelationIdeal_le_gradientIdeal a r hp)

noncomputable instance factorGradientTargetAlgebraFactorOrder
    {R : Type*} [CommRing R] {d : ℕ} (a : R) (r : Fin d → ℕ) :
    Algebra (FactorTensorOrder a r) (FactorGradientTarget a r) :=
  (factorOrderToGradientTarget a r).toAlgebra

def factorOrderGradientAddHom
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) :
    FactorTensorOrder a r →+ FactorGradientTarget a r :=
  QuotientAddGroup.lift (factorTensorRelationIdeal a r).toAddSubgroup
    (factorPolynomialGradient a r).toLinearMap.toAddMonoidHom
    (fun p hp => factorPolynomialGradient_eq_zero_of_mem_relationIdeal a r hp)

@[simp] theorem factorOrderGradientAddHom_mk
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) (p : FactorTensorPolynomial R d) :
    factorOrderGradientAddHom a r (Ideal.Quotient.mk _ p) =
      factorPolynomialGradient a r p := rfl

def factorOrderGradientLinearMap
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) :
    FactorTensorOrder a r →ₗ[R] FactorGradientTarget a r where
  toFun := factorOrderGradientAddHom a r
  map_add' := map_add _
  map_smul' c x := by
    induction x using Quotient.inductionOn' with
    | _ p => exact (factorPolynomialGradient a r).toLinearMap.map_smul c p

/-- Card `(10a)`: literal `R`-derivation `∇_F : A_r → A_r/(F)`. -/
noncomputable def factorOrderGradient
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) :
    Derivation R (FactorTensorOrder a r) (FactorGradientTarget a r) := by
  let D := factorPolynomialGradient a r
  let L := factorOrderGradientLinearMap a r
  exact Derivation.mk' L (by
    intro x y
    induction x using Quotient.inductionOn' with
    | _ x =>
      induction y using Quotient.inductionOn' with
      | _ y =>
        change D (x * y) =
          Ideal.Quotient.mk _ x • D y + Ideal.Quotient.mk _ y • D x
        rw [Derivation.leibniz]
        rfl)

@[simp] theorem factorOrderGradient_generator
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) (i : Fin d) :
    factorOrderGradient a r (factorTensorGenerator a r i) =
      Ideal.Quotient.mk _ (factorTensorComplement (R := R) i) := by
  rw [factorOrderGradient, factorTensorGenerator]
  change factorPolynomialGradient a r (MvPolynomial.X i) = _
  rw [factorPolynomialGradient_X]

/-- Universal Kähler map induced by the source-framed potential gradient. -/
noncomputable def factorKaehlerSoldering
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) :
    Ω[FactorTensorOrder a r⁄R] →ₗ[FactorTensorOrder a r] FactorGradientTarget a r :=
  (factorOrderGradient a r).liftKaehlerDifferential

/-- Card `(10c)`, universal-map clause: the induced Kähler map sends `df_i` to the literal
complementary product `F/f_i`. -/
theorem factorKaehlerSoldering_D_generator
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) (i : Fin d) :
    factorKaehlerSoldering a r
        (KaehlerDifferential.D R (FactorTensorOrder a r)
          (factorTensorGenerator a r i)) =
      Ideal.Quotient.mk _ (factorTensorComplement (R := R) i) := by
  rw [factorKaehlerSoldering,
    Derivation.liftKaehlerDifferential_comp_D,
    factorOrderGradient_generator]

end

end HTGeometry.ConstraintRelativity
