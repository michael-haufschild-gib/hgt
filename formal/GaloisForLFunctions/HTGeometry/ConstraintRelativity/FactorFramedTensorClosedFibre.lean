import GaloisForLFunctions.HTGeometry.ConstraintRelativity.FactorFramedTensorGradient
import GaloisForLFunctions.RHTower.DeningerHazewinkelBoundaryKernel

/-!
# Literal closed fibres of factor tensor and Jacobian algebras

This file proves coefficient reduction, rather than postulating a squarefree coordinate model.
For an arbitrary ideal in the factor polynomial ring, its literal quotient followed by quotienting
by the base parameter is identified with the corresponding quotient after coefficient reduction
to `R/(a)`.  The exact kernel calculation then gives the tensor-order presentation `(10z)` and
the Jacobian face-algebra presentation `(10f)`.
-/

namespace HTGeometry.ConstraintRelativity

open scoped BigOperators

noncomputable section

def factorCoefficientIdeal
    {R : Type*} [CommRing R] {d : ℕ} (a : R) :
    Ideal (FactorTensorPolynomial R d) :=
  Ideal.span {MvPolynomial.C a}

abbrev FactorResidueRing {R : Type*} [CommRing R] (a : R) :=
  R ⧸ Ideal.span {a}

def factorCoefficientReduction
    {R : Type*} [CommRing R] {d : ℕ} (a : R) :
    FactorTensorPolynomial R d →+*
      FactorTensorPolynomial (FactorResidueRing a) d :=
  MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {a}))

theorem factorCoefficientReduction_surjective
    {R : Type*} [CommRing R] {d : ℕ} (a : R) :
    Function.Surjective (factorCoefficientReduction (d := d) a) :=
  MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective

theorem factorCoefficientReduction_ker
    {R : Type*} [CommRing R] {d : ℕ} (a : R) :
    RingHom.ker (factorCoefficientReduction (d := d) a) = factorCoefficientIdeal a := by
  ext p
  constructor
  · intro hp
    rw [RingHom.mem_ker] at hp
    obtain ⟨q, hq⟩ := RHTower.mvPolynomial_C_dvd_of_map_quotient_eq_zero a p hp
    rw [factorCoefficientIdeal, Ideal.mem_span_singleton]
    exact ⟨q, hq⟩
  · intro hp
    rw [factorCoefficientIdeal, Ideal.mem_span_singleton] at hp
    obtain ⟨q, rfl⟩ := hp
    rw [RingHom.mem_ker, map_mul, factorCoefficientReduction, MvPolynomial.map_C]
    have ha : (Ideal.Quotient.mk (Ideal.span {a}) a : FactorResidueRing a) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span (Set.mem_singleton a)
    rw [ha, MvPolynomial.C_0, zero_mul]

private def idealQuotientRingEquivOfEq {A : Type*} [CommRing A]
    {I J : Ideal A} (h : I = J) : A ⧸ I ≃+* A ⧸ J := by
  subst J
  exact RingEquiv.refl _

/-- Literal quotient of `P/E` by the image of the base ideal `(a)`. -/
abbrev FactorClosedFibreOfIdeal
    {R : Type*} [CommRing R] {d : ℕ} (a : R)
    (E : Ideal (FactorTensorPolynomial R d)) :=
  let q : FactorTensorPolynomial R d →+* FactorTensorPolynomial R d ⧸ E :=
    Ideal.Quotient.mk E
  (FactorTensorPolynomial R d ⧸ E) ⧸ Ideal.map q (factorCoefficientIdeal a)

def factorRawToClosedFibreMap
    {R : Type*} [CommRing R] {d : ℕ} (a : R)
    (E : Ideal (FactorTensorPolynomial R d)) :
    FactorTensorPolynomial R d →+* FactorClosedFibreOfIdeal a E :=
  let q : FactorTensorPolynomial R d →+* FactorTensorPolynomial R d ⧸ E :=
    Ideal.Quotient.mk E
  (Ideal.Quotient.mk (Ideal.map q (factorCoefficientIdeal a))).comp q

theorem factorRawToClosedFibreMap_surjective
    {R : Type*} [CommRing R] {d : ℕ} (a : R)
    (E : Ideal (FactorTensorPolynomial R d)) :
    Function.Surjective (factorRawToClosedFibreMap a E) := by
  intro y
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact ⟨p, rfl⟩

theorem factorQuotientMap_ker_eq
    {A : Type*} [CommRing A] (I : Ideal A) :
    RingHom.ker (Ideal.Quotient.mk I) = I := by
  ext x
  rw [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]

theorem factorRawToClosedFibreMap_ker
    {R : Type*} [CommRing R] {d : ℕ} (a : R)
    (E : Ideal (FactorTensorPolynomial R d)) :
    RingHom.ker (factorRawToClosedFibreMap a E) = E ⊔ factorCoefficientIdeal a := by
  let q : FactorTensorPolynomial R d →+* FactorTensorPolynomial R d ⧸ E :=
    Ideal.Quotient.mk E
  have hq : Function.Surjective q := Ideal.Quotient.mk_surjective
  have hker : Ideal.comap q ⊥ = E := by
    ext p
    rw [Ideal.mem_comap, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
  have hcomap : Ideal.comap q (Ideal.map q (factorCoefficientIdeal a)) =
      factorCoefficientIdeal a ⊔ E := by
    rw [Ideal.comap_map_of_surjective q hq, hker]
  ext p
  rw [RingHom.mem_ker]
  change Ideal.Quotient.mk (Ideal.map q (factorCoefficientIdeal a)) (q p) = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap, hcomap]
  simpa [sup_comm]

def factorRawClosedFibreEquiv
    {R : Type*} [CommRing R] {d : ℕ} (a : R)
    (E : Ideal (FactorTensorPolynomial R d)) :
    FactorTensorPolynomial R d ⧸ (E ⊔ factorCoefficientIdeal a) ≃+*
      FactorClosedFibreOfIdeal a E :=
  (idealQuotientRingEquivOfEq (factorRawToClosedFibreMap_ker a E).symm).trans
    (RingHom.quotientKerEquivOfSurjective (factorRawToClosedFibreMap_surjective a E))

abbrev FactorResidueQuotient
    {R : Type*} [CommRing R] {d : ℕ} (a : R)
    (Ek : Ideal (FactorTensorPolynomial (FactorResidueRing a) d)) :=
  FactorTensorPolynomial (FactorResidueRing a) d ⧸ Ek

def factorRawToResidueQuotientMap
    {R : Type*} [CommRing R] {d : ℕ} (a : R)
    (Ek : Ideal (FactorTensorPolynomial (FactorResidueRing a) d)) :
    FactorTensorPolynomial R d →+* FactorResidueQuotient a Ek :=
  (Ideal.Quotient.mk Ek).comp (factorCoefficientReduction (d := d) a)

theorem factorRawToResidueQuotientMap_surjective
    {R : Type*} [CommRing R] {d : ℕ} (a : R)
    (Ek : Ideal (FactorTensorPolynomial (FactorResidueRing a) d)) :
    Function.Surjective (factorRawToResidueQuotientMap a Ek) := by
  intro y
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨p, rfl⟩ := factorCoefficientReduction_surjective (d := d) a q
  exact ⟨p, rfl⟩

theorem factorRawToResidueQuotientMap_ker
    {R : Type*} [CommRing R] {d : ℕ} (a : R)
    (E : Ideal (FactorTensorPolynomial R d))
    (Ek : Ideal (FactorTensorPolynomial (FactorResidueRing a) d))
    (hmap : Ideal.map (factorCoefficientReduction (d := d) a) E = Ek) :
    RingHom.ker (factorRawToResidueQuotientMap a Ek) =
      E ⊔ factorCoefficientIdeal a := by
  let red := factorCoefficientReduction (d := d) a
  have hsurj : Function.Surjective red := factorCoefficientReduction_surjective a
  have hcomap : Ideal.comap red Ek = E ⊔ factorCoefficientIdeal a := by
    rw [← hmap, Ideal.comap_map_of_surjective red hsurj,
      show Ideal.comap red ⊥ = RingHom.ker red by
        ext p
        rw [Ideal.mem_comap, Ideal.mem_bot, RingHom.mem_ker],
      factorCoefficientReduction_ker]
  ext p
  rw [RingHom.mem_ker]
  change Ideal.Quotient.mk Ek (red p) = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap, hcomap]

def factorClosedFibreResidueEquiv
    {R : Type*} [CommRing R] {d : ℕ} (a : R)
    (E : Ideal (FactorTensorPolynomial R d))
    (Ek : Ideal (FactorTensorPolynomial (FactorResidueRing a) d))
    (hmap : Ideal.map (factorCoefficientReduction (d := d) a) E = Ek) :
    FactorClosedFibreOfIdeal a E ≃+* FactorResidueQuotient a Ek :=
  (factorRawClosedFibreEquiv a E).symm.trans
    ((idealQuotientRingEquivOfEq
      (factorRawToResidueQuotientMap_ker a E Ek hmap).symm).trans
      (RingHom.quotientKerEquivOfSurjective
        (factorRawToResidueQuotientMap_surjective a Ek)))

/-! ## Tensor-order closed fibre `(10z)` -/

def factorSquareRelation
    {k : Type*} [CommRing k] {d : ℕ} (i : Fin d) :
    FactorTensorPolynomial k d :=
  MvPolynomial.X i ^ 2

def factorSquareRelationIdeal
    {k : Type*} [CommRing k] {d : ℕ} : Ideal (FactorTensorPolynomial k d) :=
  Ideal.span (Set.range factorSquareRelation)

theorem factorCoefficientReduction_map_relationIdeal
    {R : Type*} [CommRing R] {d : ℕ} (a : R) (r : Fin d → ℕ)
    (hr : ∀ i, 0 < r i) :
    Ideal.map (factorCoefficientReduction (d := d) a) (factorTensorRelationIdeal a r) =
      (factorSquareRelationIdeal :
        Ideal (FactorTensorPolynomial (FactorResidueRing a) d)) := by
  rw [factorTensorRelationIdeal, factorSquareRelationIdeal, Ideal.map_span]
  apply congrArg Ideal.span
  ext p
  constructor
  · rintro ⟨q, ⟨i, rfl⟩, rfl⟩
    refine ⟨i, ?_⟩
    have ha : (Ideal.Quotient.mk (Ideal.span {a}) a : FactorResidueRing a) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span (Set.mem_singleton a)
    have hexp : 2 * r i ≠ 0 := mul_ne_zero (by norm_num) (Nat.ne_of_gt (hr i))
    simp [factorCoefficientReduction, factorTensorRelation, factorSquareRelation, ha, hexp]
  · rintro ⟨i, rfl⟩
    refine ⟨factorTensorRelation a r i, ⟨i, rfl⟩, ?_⟩
    have ha : (Ideal.Quotient.mk (Ideal.span {a}) a : FactorResidueRing a) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span (Set.mem_singleton a)
    have hexp : 2 * r i ≠ 0 := mul_ne_zero (by norm_num) (Nat.ne_of_gt (hr i))
    simp [factorCoefficientReduction, factorTensorRelation, factorSquareRelation, ha, hexp]

/-- The literal quotient `(A_r)/(a)`; its defining ideal is the image of `(a)` in `A_r`. -/
abbrev FactorTensorClosedFibre
    {R : Type*} [CommRing R] {d : ℕ} (a : R) (r : Fin d → ℕ) :=
  FactorClosedFibreOfIdeal a (factorTensorRelationIdeal a r)

abbrev FactorSquarefreeTensorAlgebra
    {R : Type*} [CommRing R] {d : ℕ} (a : R) :=
  FactorResidueQuotient a
    (factorSquareRelationIdeal :
      Ideal (FactorTensorPolynomial (FactorResidueRing a) d))

/-- **Card `(10z)`.** The actual closed fibre of the tensor order is the squarefree local algebra
over `R/(a)`. -/
def factorTensorClosedFibreEquivSquarefree
    {R : Type*} [CommRing R] {d : ℕ} (a : R) (r : Fin d → ℕ)
    (hr : ∀ i, 0 < r i) :
    FactorTensorClosedFibre a r ≃+* FactorSquarefreeTensorAlgebra (d := d) a :=
  factorClosedFibreResidueEquiv a (factorTensorRelationIdeal a r)
    factorSquareRelationIdeal (factorCoefficientReduction_map_relationIdeal a r hr)

/-! ## Jacobian closed fibre `(10f)` -/

def factorComplementIdeal
    {R : Type*} [CommRing R] {d : ℕ} : Ideal (FactorTensorPolynomial R d) :=
  Ideal.span (Set.range factorTensorComplement)

def factorJacobianPolynomialIdeal
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) : Ideal (FactorTensorPolynomial R d) :=
  factorTensorRelationIdeal a r ⊔ factorComplementIdeal

/-- Literal critical/Jacobian algebra `A_r/(F/f_i)_i`; `F` is already in this ideal. -/
abbrev FactorJacobianAlgebra
    {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) :=
  FactorTensorPolynomial R d ⧸ factorJacobianPolynomialIdeal a r

theorem factorCoefficientReduction_map_complementIdeal
    {R : Type*} [CommRing R] {d : ℕ} (a : R) :
    Ideal.map (factorCoefficientReduction (d := d) a)
        (factorComplementIdeal : Ideal (FactorTensorPolynomial R d)) =
      (factorComplementIdeal :
        Ideal (FactorTensorPolynomial (FactorResidueRing a) d)) := by
  rw [factorComplementIdeal, Ideal.map_span]
  apply congrArg Ideal.span
  ext p
  constructor
  · rintro ⟨q, ⟨i, rfl⟩, rfl⟩
    refine ⟨i, ?_⟩
    simp [factorCoefficientReduction, factorTensorComplement]
  · rintro ⟨i, rfl⟩
    refine ⟨factorTensorComplement (R := R) i, ⟨i, rfl⟩, ?_⟩
    simp [factorCoefficientReduction, factorTensorComplement]

theorem factorCoefficientReduction_map_jacobianIdeal
    {R : Type*} [CommRing R] {d : ℕ} (a : R) (r : Fin d → ℕ)
    (hr : ∀ i, 0 < r i) :
    Ideal.map (factorCoefficientReduction (d := d) a)
        (factorJacobianPolynomialIdeal a r) =
      ((factorSquareRelationIdeal :
          Ideal (FactorTensorPolynomial (FactorResidueRing a) d)) ⊔
        factorComplementIdeal) := by
  rw [factorJacobianPolynomialIdeal, Ideal.map_sup,
    factorCoefficientReduction_map_relationIdeal a r hr,
    factorCoefficientReduction_map_complementIdeal a]

abbrev FactorJacobianClosedFibre
    {R : Type*} [CommRing R] {d : ℕ} (a : R) (r : Fin d → ℕ) :=
  FactorClosedFibreOfIdeal a (factorJacobianPolynomialIdeal a r)

abbrev FactorSquarefreeFaceAlgebra
    {R : Type*} [CommRing R] {d : ℕ} (a : R) :=
  FactorResidueQuotient a
    ((factorSquareRelationIdeal :
        Ideal (FactorTensorPolynomial (FactorResidueRing a) d)) ⊔
      factorComplementIdeal)

/-- **Card `(10f)`.** The actual closed fibre of the factor Jacobian algebra has precisely the
relations `f_i² = 0` and `∏_{j ≠ i} f_j = 0`. -/
def factorJacobianClosedFibreEquivSquarefreeFace
    {R : Type*} [CommRing R] {d : ℕ} (a : R) (r : Fin d → ℕ)
    (hr : ∀ i, 0 < r i) :
    FactorJacobianClosedFibre a r ≃+* FactorSquarefreeFaceAlgebra (d := d) a :=
  factorClosedFibreResidueEquiv a (factorJacobianPolynomialIdeal a r)
    (factorSquareRelationIdeal ⊔ factorComplementIdeal)
    (factorCoefficientReduction_map_jacobianIdeal a r hr)

end

end HTGeometry.ConstraintRelativity
