import GaloisForLFunctions.HTGeometry.ExponentialObservationHypertranscendence
import GaloisForLFunctions.HTGeometry.ProjectiveHorizonComplementarity

/-!
# Projective immittance charts and reciprocal HT horizons

For a nondegenerate projective chart

`M(x) = (a*x+b)/(c*x+d)`,

this module classifies exactly when the positive-order jet horizons of `M(x)` and `M(x⁻¹)`
coincide.  The answer is the coefficient locus `d²=c²`.  Equivalently, the pole of the chart is
one of the two fixed points of inversion.  The ordinary normalized Smith chart is the specialization
`(a,b,c,d)=(1,-1,1,1)`.

The result is static differential-field geometry.  It neither assumes nor produces passivity.
-/

open scoped Differential

namespace GaloisForLFunctions

noncomputable section

/-- A scalar projective chart, used for normalized impedance, admittance, and reflection
coordinates. -/
def projectiveImmittanceChart
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (a b c d : F) (x : E) : E :=
  (algebraMap F E a * x + algebraMap F E b) /
    (algebraMap F E c * x + algebraMap F E d)

/-- Conjugating inversion by a projective chart has the displayed coefficient matrix. -/
theorem projectiveImmittanceConjugateInversion_det
    {F : Type*} [CommRing F] (a b c d : F) :
    (b * d - a * c) * (a * c - b * d) -
        (a ^ 2 - b ^ 2) * (d ^ 2 - c ^ 2) =
      -(a * d - b * c) ^ 2 := by
  ring

/-- A nondegenerate projective observation of an HT scalar is HT.  The source is recovered by
the inverse projective chart, so no observation-side HT premise is exposed. -/
theorem hypertranscendentalOver_projectiveImmittanceChart
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    (x : E) (hx : HypertranscendentalOver F x)
    (a b c d : F) (hdet : a * d - b * c ≠ 0) :
    HypertranscendentalOver F (projectiveImmittanceChart a b c d x) := by
  let y : E := projectiveImmittanceChart a b c d x
  have hden : algebraMap F E c * x + algebraMap F E d ≠ 0 :=
    mobiusDenominator_ne_zero_of_hypertranscendentalOver x hx a b c d hdet
  have hdetE : algebraMap F E (a * d - b * c) ≠ 0 :=
    by simpa using (algebraMap F E).injective.ne hdet
  have hrecoverDenEq :
      algebraMap F E (-c) * y + algebraMap F E a =
        algebraMap F E (a * d - b * c) /
          (algebraMap F E c * x + algebraMap F E d) := by
    dsimp only [y, projectiveImmittanceChart]
    rw [map_neg, map_sub, map_mul, map_mul]
    field_simp [hden]
    ring
  have hrecoverDen : algebraMap F E (-c) * y + algebraMap F E a ≠ 0 := by
    rw [hrecoverDenEq]
    exact div_ne_zero hdetE hden
  apply HTGeometry.hypertranscendentalOver_fractionalLinearObservable_of_recovery
    (source := x) (observed := y) (a := d) (b := -b) (c := -c) (d := a) hx
  apply (eq_div_iff hrecoverDen).2
  dsimp only [y, projectiveImmittanceChart]
  simp only [map_neg]
  field_simp [hden]
  ring

/-- Exact chart identity for impedance/admittance inversion.  The right side is `M I M⁻¹`
applied to `M(x)`. -/
theorem projectiveImmittanceChart_inv_eq_conjugate
    {F E : Type*} [Field F] [CharZero F] [Field E] [CharZero E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E]
    (x : E) (hx : HypertranscendentalOver F x)
    (a b c d : F) (hdet : a * d - b * c ≠ 0) :
    projectiveImmittanceChart a b c d x⁻¹ =
      projectiveImmittanceChart
        (b * d - a * c) (a ^ 2 - b ^ 2)
        (d ^ 2 - c ^ 2) (a * c - b * d)
        (projectiveImmittanceChart a b c d x) := by
  let y : E := projectiveImmittanceChart a b c d x
  let A : F := b * d - a * c
  let B : F := a ^ 2 - b ^ 2
  let C : F := d ^ 2 - c ^ 2
  let D : F := a * c - b * d
  have hxInv : HypertranscendentalOver F x⁻¹ :=
    HTGeometry.hypertranscendentalOver_inv_iff.mpr hx
  have hy : HypertranscendentalOver F y := by
    exact hypertranscendentalOver_projectiveImmittanceChart x hx a b c d hdet
  have hdetQ : A * D - B * C ≠ 0 := by
    have hEq : A * D - B * C = -(a * d - b * c) ^ 2 := by
      exact projectiveImmittanceConjugateInversion_det a b c d
    rw [hEq]
    exact neg_ne_zero.mpr (pow_ne_zero 2 hdet)
  have hdenX : algebraMap F E c * x + algebraMap F E d ≠ 0 :=
    mobiusDenominator_ne_zero_of_hypertranscendentalOver x hx a b c d hdet
  have hdenInv : algebraMap F E c * x⁻¹ + algebraMap F E d ≠ 0 :=
    mobiusDenominator_ne_zero_of_hypertranscendentalOver x⁻¹ hxInv a b c d hdet
  have hdenQ : algebraMap F E C * y + algebraMap F E D ≠ 0 :=
    mobiusDenominator_ne_zero_of_hypertranscendentalOver y hy A B C D hdetQ
  change projectiveImmittanceChart a b c d x⁻¹ =
    projectiveImmittanceChart A B C D y
  apply (eq_div_iff hdenQ).2
  dsimp only [projectiveImmittanceChart]
  field_simp [hdenX, hdenInv]
  ring

private theorem projectiveImmittanceConjugate_stabilizer_iff
    {F : Type*} [Field F] [Differential F]
    (a b c d : F) (hdet : a * d - b * c ≠ 0) :
    d ^ 2 - c ^ 2 = 0 ∧
        (((b * d - a * c) / (a * c - b * d))′) = 0 ↔
      d ^ 2 = c ^ 2 := by
  let A : F := b * d - a * c
  let B : F := a ^ 2 - b ^ 2
  let C : F := d ^ 2 - c ^ 2
  let D : F := a * c - b * d
  have hdetQ : A * D - B * C ≠ 0 := by
    have hEq : A * D - B * C = -(a * d - b * c) ^ 2 := by
      exact projectiveImmittanceConjugateInversion_det a b c d
    rw [hEq]
    exact neg_ne_zero.mpr (pow_ne_zero 2 hdet)
  constructor
  · rintro ⟨hC, -⟩
    exact sub_eq_zero.mp hC
  · intro hdc
    have hC : C = 0 := sub_eq_zero.mpr hdc
    have hAD : A * D ≠ 0 := by
      simpa [hC] using hdetQ
    have hA : A ≠ 0 := (mul_ne_zero_iff.mp hAD).1
    have hDneg : D = -A := by
      dsimp only [A, D]
      ring
    have hratio : A / D = -1 := by
      rw [hDneg]
      field_simp [hA]
    constructor
    · exact hC
    · change (A / D)′ = 0
      rw [hratio]
      simp

/-- **Projective immittance inversion-horizon folding law.**  For an HT scalar, the first
positive-order jet horizons reported by one nondegenerate projective chart on `x` and `x⁻¹`
coincide exactly when the chart pole is an inversion fixed point. -/
theorem projectiveImmittanceChart_inv_jetTailField_one_eq_iff
    {F E : Type*} [Field F] [CharZero F] [Field E] [CharZero E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E]
    (x : E) (hx : HypertranscendentalOver F x)
    (a b c d : F) (hdet : a * d - b * c ≠ 0) :
    jetTailField F (projectiveImmittanceChart a b c d x⁻¹) 1 =
        jetTailField F (projectiveImmittanceChart a b c d x) 1 ↔
      d ^ 2 = c ^ 2 := by
  let y : E := projectiveImmittanceChart a b c d x
  let A : F := b * d - a * c
  let B : F := a ^ 2 - b ^ 2
  let C : F := d ^ 2 - c ^ 2
  let D : F := a * c - b * d
  have hy : HypertranscendentalOver F y :=
    hypertranscendentalOver_projectiveImmittanceChart x hx a b c d hdet
  have hdetQ : A * D - B * C ≠ 0 := by
    have hEq : A * D - B * C = -(a * d - b * c) ^ 2 := by
      exact projectiveImmittanceConjugateInversion_det a b c d
    rw [hEq]
    exact neg_ne_zero.mpr (pow_ne_zero 2 hdet)
  rw [projectiveImmittanceChart_inv_eq_conjugate x hx a b c d hdet]
  change (jetTailField F
      ((algebraMap F E A * y + algebraMap F E B) /
        (algebraMap F E C * y + algebraMap F E D)) 1 =
      jetTailField F y 1) ↔ d ^ 2 = c ^ 2
  rw [mobius_jetTailField_one_eq_iff y hy A B C D hdetQ]
  exact projectiveImmittanceConjugate_stabilizer_iff a b c d hdet

/-- The same coefficient locus classifies equality of the complete jet-tail flags. -/
theorem projectiveImmittanceChart_inv_all_jetTailField_eq_iff
    {F E : Type*} [Field F] [CharZero F] [Field E] [CharZero E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E]
    (x : E) (hx : HypertranscendentalOver F x)
    (a b c d : F) (hdet : a * d - b * c ≠ 0) :
    (∀ n : ℕ,
      jetTailField F (projectiveImmittanceChart a b c d x⁻¹) n =
        jetTailField F (projectiveImmittanceChart a b c d x) n) ↔
      d ^ 2 = c ^ 2 := by
  let y : E := projectiveImmittanceChart a b c d x
  let A : F := b * d - a * c
  let B : F := a ^ 2 - b ^ 2
  let C : F := d ^ 2 - c ^ 2
  let D : F := a * c - b * d
  have hy : HypertranscendentalOver F y :=
    hypertranscendentalOver_projectiveImmittanceChart x hx a b c d hdet
  have hdetQ : A * D - B * C ≠ 0 := by
    have hEq : A * D - B * C = -(a * d - b * c) ^ 2 := by
      exact projectiveImmittanceConjugateInversion_det a b c d
    rw [hEq]
    exact neg_ne_zero.mpr (pow_ne_zero 2 hdet)
  simp only [projectiveImmittanceChart_inv_eq_conjugate x hx a b c d hdet]
  change (∀ n : ℕ,
      jetTailField F
          ((algebraMap F E A * y + algebraMap F E B) /
            (algebraMap F E C * y + algebraMap F E D)) n =
        jetTailField F y n) ↔ d ^ 2 = c ^ 2
  rw [mobius_all_jetTailField_eq_iff y hy A B C D hdetQ]
  exact projectiveImmittanceConjugate_stabilizer_iff a b c d hdet

/-- The normalized Smith reflection coordinate. -/
def smithReflectionChart {E : Type*} [Field E] (x : E) : E :=
  (x - 1) / (x + 1)

/-- The practical Smith-chart impedance/admittance rule: reciprocal immittances have antipodal
reflection coordinates. -/
theorem smithReflectionChart_inv_eq_neg_of_hypertranscendentalOver
    {F E : Type*} [Field F] [CharZero F] [Field E] [CharZero E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E]
    (x : E) (hx : HypertranscendentalOver F x) :
    smithReflectionChart x⁻¹ = -smithReflectionChart x := by
  have hconj := projectiveImmittanceChart_inv_eq_conjugate
    x hx (1 : F) (-1) 1 1 (by norm_num)
  simpa [smithReflectionChart, projectiveImmittanceChart, sub_eq_add_neg] using hconj

/-- The Smith chart folds the complete reciprocal pair of HT jet-tail flags. -/
theorem smithReflectionChart_inv_all_jetTailField_eq
    {F E : Type*} [Field F] [CharZero F] [Field E] [CharZero E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E]
    (x : E) (hx : HypertranscendentalOver F x) (n : ℕ) :
    jetTailField F (smithReflectionChart x⁻¹) n =
      jetTailField F (smithReflectionChart x) n := by
  have hfold := (projectiveImmittanceChart_inv_all_jetTailField_eq_iff
    x hx (1 : F) (-1) 1 1 (by norm_num)).2 (by norm_num)
  simpa [smithReflectionChart, projectiveImmittanceChart, sub_eq_add_neg] using hfold n

/-- **Smith complementarity collapse.**  If the raw HT scalar generates the ambient differential
field, its impedance/admittance first horizons have full join, while their Smith reports have
already folded to one horizon. -/
theorem smithReflectionChart_reciprocalHorizon_complementarity_collapse
    {F E : Type*} [Field F] [CharZero F] [Field E] [CharZero E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E]
    (x : E) (hx : HypertranscendentalOver F x)
    (hgen : jetTailField F x 0 = ⊤) :
    jetTailField F x 1 ⊔ jetTailField F x⁻¹ 1 = ⊤ ∧
      jetTailField F (smithReflectionChart x) 1 ⊔
          jetTailField F (smithReflectionChart x⁻¹) 1 =
        jetTailField F (smithReflectionChart x) 1 := by
  constructor
  · exact hypertranscendentalOver_sup_firstJetTail_inv_eq_top x hx hgen
  · rw [smithReflectionChart_inv_all_jetTailField_eq x hx 1]
    simp

end

end GaloisForLFunctions
