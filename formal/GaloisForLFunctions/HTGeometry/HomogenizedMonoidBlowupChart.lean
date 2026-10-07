import GaloisForLFunctions.HTGeometry.HomogenizedMonoidPinching
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Polynomial.Quotient

/-!
# The affine blowup chart of a pinched monoid algebra

Write `A = R + T*(R[M])[T]` using the verified quadratic quotient. The localization of
`(R[M])[T]` at `T` is also the localization of `A` at its homogenizer. Inside this common
overring, adjoining all vertex-ideal elements divided by the homogenizer gives exactly
`(R[M])[T]`. The extended vertex ideal is `(T)`, and its quotient is `R[M]`.

All constructions allow arbitrary commutative `R` and additive commutative `M`. No finite-type,
Noetherian, properness, or domain premise is used. This file verifies the affine blowup algebra;
the identification of the full scheme Proj with this chart is a separate obligation.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.HomogenizedMonoidAlgebra
variable (R M : Type*) [CommRing R] [AddCommMonoid M]

/-- A common localization in which both the source and its dehomogenized chart embed. -/
abbrev Overring := Localization.Away (Polynomial.X : Polynomial (AddMonoidAlgebra R M))

/-- The canonical map from the polynomial ring into its localization. -/
def overringMap : Polynomial (AddMonoidAlgebra R M) →ₐ[R] Overring R M :=
  IsScalarTower.toAlgHom R (Polynomial (AddMonoidAlgebra R M)) (Overring R M)

/-- The polynomial localization is faithful, since every power of `T` is regular. -/
theorem overringMap_injective : Function.Injective (overringMap R M) := by
  apply (IsLocalization.injective_iff_isRegular
    (Submonoid.powers (Polynomial.X : Polynomial (AddMonoidAlgebra R M)))).2
  rintro ⟨_,n,rfl⟩
  exact Polynomial.isRegular_X_pow n

/-- Embed the quadratic source quotient in the common localization. -/
def sourceToOverring : Q R M →ₐ[R] Overring R M :=
  (overringMap R M).comp (quotientPolynomial R M)

/-- The source embedding in the common localization is faithful. -/
theorem sourceToOverring_injective : Function.Injective (sourceToOverring R M) :=
  (overringMap_injective R M).comp (quotientPolynomial_injective R M)

/-- The source homogenizer maps to the polynomial variable. -/
@[simp] theorem sourceToOverring_qVar_zero :
    sourceToOverring R M (qVar R M 0) = overringMap R M Polynomial.X := by
  change overringMap R M (quotientPolynomial R M (qVar R M 0)) = _
  rw [quotientPolynomial_qVar_zero]

/-- The common overring as an algebra over the source quotient. -/
instance overringSourceAlgebra : Algebra (Q R M) (Overring R M) :=
  (sourceToOverring R M).toAlgebra

/-- The reverse normal-form map has the prescribed polynomial realization. -/
theorem quotientPolynomial_reverseMap (f : MonoidAlgebra R (Tag M)) :
    quotientPolynomial R M (reverseMap R M f) = polynomialRealization R M f := by
  change polynomialRealization R M (quotientEvaluation R M (reverseMap R M f)) = _
  have h := AlgHom.congr_fun (quotientEvaluation_reverseMap R M) f
  change quotientEvaluation R M (reverseMap R M f) = f at h
  rw [h]

/-- The common overring is also the localization of the source at its homogenizer. -/
instance overring_isLocalization : IsLocalization.Away (qVar R M 0) (Overring R M) := by
  apply IsLocalization.Away.mk
  · change IsUnit (sourceToOverring R M (qVar R M 0))
    rw [sourceToOverring_qVar_zero]
    exact IsLocalization.Away.algebraMap_isUnit Polynomial.X
  · intro z
    obtain ⟨n,p,hp⟩ := IsLocalization.Away.surj
      (Polynomial.X : Polynomial (AddMonoidAlgebra R M)) z
    obtain ⟨f,hf⟩ := X_mul_mem_range R M p
    change polynomialRealization R M f = Polynomial.X * p at hf
    refine ⟨n+1,reverseMap R M f,?_⟩
    change z * (sourceToOverring R M (qVar R M 0)) ^ (n+1) =
      overringMap R M (quotientPolynomial R M (reverseMap R M f))
    rw [sourceToOverring_qVar_zero,pow_succ,← mul_assoc]
    change (z * algebraMap _ (Overring R M) Polynomial.X ^ n) *
      overringMap R M Polynomial.X = _
    rw [hp,quotientPolynomial_reverseMap,hf]
    change overringMap R M p * overringMap R M Polynomial.X = _
    rw [← map_mul,mul_comm]
  · intro a b h
    have hab : a = b := sourceToOverring_injective R M h
    exact ⟨0,by rw [hab]⟩

/-- A marked source generator divided by the homogenizer in the common localization. -/
def chartRatio (a : M) : Overring R M :=
  sourceToOverring R M (qVar R M a) *
    IsLocalization.Away.invSelf (Polynomial.X : Polynomial (AddMonoidAlgebra R M))

/-- Dividing a marked generator by the homogenizer recovers its constant monoid mark. -/
theorem chartRatio_eq (a : M) : chartRatio R M a =
    overringMap R M (Polynomial.C (AddMonoidAlgebra.single a 1)) := by
  unfold chartRatio sourceToOverring
  rw [AlgHom.comp_apply,quotientPolynomial_qVar,← Polynomial.C_mul_X_eq_monomial,map_mul,mul_assoc]
  change _ * (algebraMap _ (Overring R M) Polynomial.X * _) = _
  rw [IsLocalization.Away.mul_invSelf,mul_one]

/-- The source subalgebra with all generator ratios adjoined. -/
def affineChart : Subalgebra R (Overring R M) :=
  Algebra.adjoin R (Set.range (sourceToOverring R M) ∪ Set.range (chartRatio R M))

/-- Every source element belongs to the affine chart. -/
theorem source_mem_affineChart (a : Q R M) : sourceToOverring R M a ∈ affineChart R M :=
  Algebra.subset_adjoin (Or.inl ⟨a,rfl⟩)

/-- Every marked generator ratio belongs to the affine chart. -/
theorem ratio_mem_affineChart (a : M) : chartRatio R M a ∈ affineChart R M :=
  Algebra.subset_adjoin (Or.inr ⟨a,rfl⟩)

/-- Ratios of all vertex-ideal elements belong to the same chart. -/
theorem idealRatio_mem_affineChart {a : Q R M} (ha : a ∈ vertexIdeal R M) :
    sourceToOverring R M a *
      IsLocalization.Away.invSelf (Polynomial.X : Polynomial (AddMonoidAlgebra R M)) ∈
        affineChart R M := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    rcases ha with ⟨b,rfl⟩
    exact ratio_mem_affineChart R M b
  | zero => simp
  | add a b ha hb ia ib =>
    simpa only [map_add,add_mul] using (affineChart R M).add_mem ia ib
  | smul c a ha ih =>
    change sourceToOverring R M (c*a) * _ ∈ _
    rw [map_mul,mul_assoc]
    exact (affineChart R M).mul_mem (source_mem_affineChart R M c) ih

/-- The generators can equivalently be all elements of the vertex ideal divided by the homogenizer. -/
theorem affineChart_all_ideal : affineChart R M = Algebra.adjoin R
    (Set.range (sourceToOverring R M) ∪ Set.range (fun a : vertexIdeal R M =>
      sourceToOverring R M a * IsLocalization.Away.invSelf
        (Polynomial.X : Polynomial (AddMonoidAlgebra R M)))) := by
  apply le_antisymm
  · apply Algebra.adjoin_le
    rintro x (⟨a,rfl⟩ | ⟨a,rfl⟩)
    · exact Algebra.subset_adjoin (Or.inl ⟨a,rfl⟩)
    · exact Algebra.subset_adjoin (Or.inr ⟨⟨qVar R M a,qVar_mem_vertexIdeal R M a⟩,rfl⟩)
  · apply Algebra.adjoin_le
    rintro x (⟨a,rfl⟩ | ⟨a,rfl⟩)
    · exact source_mem_affineChart R M a
    · exact idealRatio_mem_affineChart R M a.property

/-- The homogenizer remains a coordinate on the affine chart. -/
theorem X_mem_affineChart : overringMap R M Polynomial.X ∈ affineChart R M := by
  have h := source_mem_affineChart R M (qVar R M 0)
  change overringMap R M (quotientPolynomial R M (qVar R M 0)) ∈ _ at h
  rwa [quotientPolynomial_qVar_zero] at h

/-- Every coefficient in the monoid algebra belongs to the affine chart. -/
theorem C_mem_affineChart (b : AddMonoidAlgebra R M) :
    overringMap R M (Polynomial.C b) ∈ affineChart R M := by
  induction b using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add b c hb hc => simpa using (affineChart R M).add_mem hb hc
  | single a r =>
    have h := (affineChart R M).smul_mem
      (show overringMap R M (Polynomial.C (AddMonoidAlgebra.single a 1)) ∈ affineChart R M by
        rw [← chartRatio_eq]; exact ratio_mem_affineChart R M a) r
    simpa only [← map_smul, Polynomial.smul_C, AddMonoidAlgebra.smul_single,
      smul_eq_mul,mul_one] using h

/-- The chart is precisely the polynomial ring embedded in the common localization. -/
theorem affineChart_eq_range : affineChart R M = (overringMap R M).range := by
  apply le_antisymm
  · apply Algebra.adjoin_le
    rintro x (⟨a,rfl⟩ | ⟨a,rfl⟩)
    · exact ⟨quotientPolynomial R M a,rfl⟩
    · exact ⟨Polynomial.C (AddMonoidAlgebra.single a 1),(chartRatio_eq R M a).symm⟩
  · rintro x ⟨p,rfl⟩
    induction p using Polynomial.induction_on with
    | C b => exact C_mem_affineChart R M b
    | add p q hp hq => simpa using (affineChart R M).add_mem hp hq
    | monomial n b hb =>
      rw [pow_succ,← mul_assoc,map_mul]
      exact (affineChart R M).mul_mem hb (X_mem_affineChart R M)

/-- The affine blowup chart is the full polynomial ring over the monoid algebra. -/
def affineChartEquiv : affineChart R M ≃ₐ[R] Polynomial (AddMonoidAlgebra R M) :=
  (Subalgebra.equivOfEq _ _ (affineChart_eq_range R M)).trans
    (AlgEquiv.ofInjective (overringMap R M) (overringMap_injective R M)).symm


/-- The vertex ideal becomes the principal homogenizer ideal on the chart. -/
theorem vertexIdeal_extension : Ideal.map (quotientPolynomial R M).toRingHom (vertexIdeal R M) =
    Ideal.span {Polynomial.X} := by
  apply le_antisymm
  · rw [vertexIdeal,Ideal.map_span]
    apply Ideal.span_le.2
    rintro _ ⟨x,⟨a,rfl⟩,rfl⟩
    change quotientPolynomial R M (qVar R M a) ∈ _
    rw [quotientPolynomial_qVar,← Polynomial.C_mul_X_eq_monomial]
    exact (Ideal.span {Polynomial.X}).mul_mem_left _ (Ideal.subset_span (Set.mem_singleton _))
  · apply Ideal.span_le.2
    intro x hx
    rcases Set.mem_singleton_iff.1 hx with rfl
    rw [← quotientPolynomial_qVar_zero R M]
    exact Ideal.mem_map_of_mem _ (qVar_mem_vertexIdeal R M 0)

/-- The exceptional quotient of the affine chart is the monoid algebra. -/
def exceptionalFiberEquiv :
    (Polynomial (AddMonoidAlgebra R M) ⧸
      Ideal.map (quotientPolynomial R M).toRingHom (vertexIdeal R M)) ≃ₐ[R]
        AddMonoidAlgebra R M :=
  (Ideal.quotientEquivAlgOfEq R (by
    rw [vertexIdeal_extension]
    simp only [map_zero,sub_zero])).trans
      ((Polynomial.quotientSpanXSubCAlgEquiv (0 : AddMonoidAlgebra R M)).restrictScalars R)

end GaloisForLFunctions.HTGeometry.HomogenizedMonoidAlgebra
