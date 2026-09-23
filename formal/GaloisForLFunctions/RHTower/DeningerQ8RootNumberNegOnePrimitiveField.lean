import GaloisForLFunctions.RHTower.DeningerQ8RootNumberNegOneTopRadicand

/-!
# Primitive-element recovery for the explicit Q8 witness

The literature writes the witness as `ℚ(z)`, where
`z² = (5 + √5) * (41 + 6 * √41)`.  The preceding construction first forms the
three-step radical tower.  This module proves the missing equality: its top
radical alone generates that entire tower over `ℚ`.

The recovery is explicit.  With `u = z²` and `r = 5 + √5`, the defining
relations force
`r * (2050 - 82*u) = 4100 - u²`; the denominator cannot vanish.  Hence `r`,
then `√5`, `41 + 6√41`, and finally `√41` are all rational functions of `z`.
-/

open Polynomial

namespace RHTower

noncomputable section

local notation "K1" => deningerQ8RootNumberNegOneFirstQuadraticField
local notation "K2" => deningerQ8RootNumberNegOneSecondQuadraticField
local notation "K3" => deningerQ8RootNumberNegOneTopField

/-- The image of `√5` in the literal top field. -/
def deningerQ8RootNumberNegOneTopX : K3 :=
  (deningerQ8RootNumberNegOneFirstQuadraticRoot : K2)

/-- The image of `√41` in the literal top field. -/
def deningerQ8RootNumberNegOneTopY : K3 :=
  deningerQ8RootNumberNegOneSecondQuadraticRoot

def deningerQ8RootNumberNegOneTopRInField : K3 :=
  5 + deningerQ8RootNumberNegOneTopX

def deningerQ8RootNumberNegOneTopSInField : K3 :=
  41 + 6 * deningerQ8RootNumberNegOneTopY

def deningerQ8RootNumberNegOneTopU : K3 :=
  deningerQ8RootNumberNegOneTopRoot ^ (2 : ℕ)

theorem deningerQ8RootNumberNegOne_second_five :
    AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial (5 : K1) =
      (5 : K2) := by
  change AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial
    ((5 : ℕ) : K1) = (5 : K2)
  exact (map_natCast (AdjoinRoot.of
    deningerQ8RootNumberNegOneSecondQuadraticPolynomial) 5).symm

theorem deningerQ8RootNumberNegOne_top_five :
    AdjoinRoot.of deningerQ8RootNumberNegOneThirdQuadraticPolynomial (5 : K2) =
      (5 : K3) := by
  change AdjoinRoot.of deningerQ8RootNumberNegOneThirdQuadraticPolynomial
    ((5 : ℕ) : K2) = (5 : K3)
  exact (map_natCast (AdjoinRoot.of
    deningerQ8RootNumberNegOneThirdQuadraticPolynomial) 5).symm

theorem deningerQ8RootNumberNegOne_second_fortyOne :
    AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial (41 : K1) =
      (41 : K2) := by
  change AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial
    ((41 : ℕ) : K1) = (41 : K2)
  exact (map_natCast (AdjoinRoot.of
    deningerQ8RootNumberNegOneSecondQuadraticPolynomial) 41).symm

theorem deningerQ8RootNumberNegOne_top_fortyOne :
    AdjoinRoot.of deningerQ8RootNumberNegOneThirdQuadraticPolynomial (41 : K2) =
      (41 : K3) := by
  change AdjoinRoot.of deningerQ8RootNumberNegOneThirdQuadraticPolynomial
    ((41 : ℕ) : K2) = (41 : K3)
  exact (map_natCast (AdjoinRoot.of
    deningerQ8RootNumberNegOneThirdQuadraticPolynomial) 41).symm

theorem deningerQ8RootNumberNegOne_second_six :
    AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial (6 : K1) =
      (6 : K2) := by
  change AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial
    ((6 : ℕ) : K1) = (6 : K2)
  exact (map_natCast (AdjoinRoot.of
    deningerQ8RootNumberNegOneSecondQuadraticPolynomial) 6).symm

theorem deningerQ8RootNumberNegOne_top_six :
    AdjoinRoot.of deningerQ8RootNumberNegOneThirdQuadraticPolynomial (6 : K2) =
      (6 : K3) := by
  change AdjoinRoot.of deningerQ8RootNumberNegOneThirdQuadraticPolynomial
    ((6 : ℕ) : K2) = (6 : K3)
  exact (map_natCast (AdjoinRoot.of
    deningerQ8RootNumberNegOneThirdQuadraticPolynomial) 6).symm

theorem deningerQ8RootNumberNegOne_topX_sq :
    deningerQ8RootNumberNegOneTopX ^ (2 : ℕ) = 5 := by
  unfold deningerQ8RootNumberNegOneTopX
  change (AdjoinRoot.of deningerQ8RootNumberNegOneThirdQuadraticPolynomial
      (AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial
        deningerQ8RootNumberNegOneFirstQuadraticRoot)) ^ (2 : ℕ) = 5
  rw [← map_pow, ← map_pow, deningerQ8RootNumberNegOneFirstQuadraticRoot_sq]
  rw [deningerQ8RootNumberNegOne_second_five, deningerQ8RootNumberNegOne_top_five]

theorem deningerQ8RootNumberNegOne_topY_sq :
    deningerQ8RootNumberNegOneTopY ^ (2 : ℕ) = 41 := by
  unfold deningerQ8RootNumberNegOneTopY
  change (AdjoinRoot.of deningerQ8RootNumberNegOneThirdQuadraticPolynomial
    deningerQ8RootNumberNegOneSecondQuadraticRoot) ^ (2 : ℕ) = 41
  rw [← map_pow, deningerQ8RootNumberNegOneSecondQuadraticRoot_sq]
  rw [deningerQ8RootNumberNegOne_top_fortyOne]

theorem deningerQ8RootNumberNegOne_topU_eq_topR_mul_topS :
    deningerQ8RootNumberNegOneTopU =
      deningerQ8RootNumberNegOneTopRInField * deningerQ8RootNumberNegOneTopSInField := by
  have hR : AdjoinRoot.of deningerQ8RootNumberNegOneThirdQuadraticPolynomial
      ((deningerQ8RootNumberNegOneTopR : K1) : K2) =
        deningerQ8RootNumberNegOneTopRInField := by
    unfold deningerQ8RootNumberNegOneTopRInField deningerQ8RootNumberNegOneTopX
      deningerQ8RootNumberNegOneTopR
    rw [map_add, map_add, deningerQ8RootNumberNegOne_second_five,
      deningerQ8RootNumberNegOne_top_five]
  have hS : AdjoinRoot.of deningerQ8RootNumberNegOneThirdQuadraticPolynomial
      deningerQ8RootNumberNegOneTopS = deningerQ8RootNumberNegOneTopSInField := by
    unfold deningerQ8RootNumberNegOneTopSInField deningerQ8RootNumberNegOneTopY
      deningerQ8RootNumberNegOneTopS
    rw [map_add, map_mul, deningerQ8RootNumberNegOne_second_fortyOne,
      deningerQ8RootNumberNegOne_top_fortyOne,
      deningerQ8RootNumberNegOne_second_six, deningerQ8RootNumberNegOne_top_six]
  unfold deningerQ8RootNumberNegOneTopU
  rw [deningerQ8RootNumberNegOneTopRoot_sq]
  unfold deningerQ8RootNumberNegOneTopRadicand
  rw [map_mul, hR, hS]

theorem deningerQ8RootNumberNegOne_topRInField_quadratic_relation :
    deningerQ8RootNumberNegOneTopRInField ^ (2 : ℕ) -
      10 * deningerQ8RootNumberNegOneTopRInField + 20 = 0 := by
  calc
    deningerQ8RootNumberNegOneTopRInField ^ (2 : ℕ) -
        10 * deningerQ8RootNumberNegOneTopRInField + 20 =
        deningerQ8RootNumberNegOneTopX ^ (2 : ℕ) - 5 := by
      unfold deningerQ8RootNumberNegOneTopRInField
      ring
    _ = 0 := by rw [deningerQ8RootNumberNegOne_topX_sq]; norm_num

theorem deningerQ8RootNumberNegOne_topSInField_quadratic_relation :
    deningerQ8RootNumberNegOneTopSInField ^ (2 : ℕ) -
      82 * deningerQ8RootNumberNegOneTopSInField + 205 = 0 := by
  calc
    deningerQ8RootNumberNegOneTopSInField ^ (2 : ℕ) -
        82 * deningerQ8RootNumberNegOneTopSInField + 205 =
        36 * (deningerQ8RootNumberNegOneTopY ^ (2 : ℕ) - 41) := by
      unfold deningerQ8RootNumberNegOneTopSInField
      ring
    _ = 0 := by rw [deningerQ8RootNumberNegOne_topY_sq]; ring

theorem deningerQ8RootNumberNegOne_topU_quadratic_relation :
    deningerQ8RootNumberNegOneTopU ^ (2 : ℕ) -
      82 * deningerQ8RootNumberNegOneTopRInField * deningerQ8RootNumberNegOneTopU +
        205 * deningerQ8RootNumberNegOneTopRInField ^ (2 : ℕ) = 0 := by
  rw [deningerQ8RootNumberNegOne_topU_eq_topR_mul_topS]
  calc
    (deningerQ8RootNumberNegOneTopRInField * deningerQ8RootNumberNegOneTopSInField) ^ (2 : ℕ) -
        82 * deningerQ8RootNumberNegOneTopRInField *
          (deningerQ8RootNumberNegOneTopRInField *
            deningerQ8RootNumberNegOneTopSInField) +
          205 * deningerQ8RootNumberNegOneTopRInField ^ (2 : ℕ) =
        deningerQ8RootNumberNegOneTopRInField ^ (2 : ℕ) *
          (deningerQ8RootNumberNegOneTopSInField ^ (2 : ℕ) -
            82 * deningerQ8RootNumberNegOneTopSInField + 205) := by
      ring
    _ = 0 := by
      rw [deningerQ8RootNumberNegOne_topSInField_quadratic_relation, mul_zero]

theorem deningerQ8RootNumberNegOne_topU_linear_relation :
    deningerQ8RootNumberNegOneTopU ^ (2 : ℕ) -
      82 * deningerQ8RootNumberNegOneTopRInField * deningerQ8RootNumberNegOneTopU +
        2050 * deningerQ8RootNumberNegOneTopRInField - 4100 = 0 := by
  calc
    deningerQ8RootNumberNegOneTopU ^ (2 : ℕ) -
        82 * deningerQ8RootNumberNegOneTopRInField * deningerQ8RootNumberNegOneTopU +
          2050 * deningerQ8RootNumberNegOneTopRInField - 4100 =
        (deningerQ8RootNumberNegOneTopU ^ (2 : ℕ) -
          82 * deningerQ8RootNumberNegOneTopRInField * deningerQ8RootNumberNegOneTopU +
          205 * deningerQ8RootNumberNegOneTopRInField ^ (2 : ℕ)) -
            205 * (deningerQ8RootNumberNegOneTopRInField ^ (2 : ℕ) -
              10 * deningerQ8RootNumberNegOneTopRInField + 20) := by
      ring
    _ = 0 := by
      rw [deningerQ8RootNumberNegOne_topU_quadratic_relation,
        deningerQ8RootNumberNegOne_topRInField_quadratic_relation]
      ring

theorem deningerQ8RootNumberNegOne_topR_mul_recoveryDenominator :
    deningerQ8RootNumberNegOneTopRInField *
      (2050 - 82 * deningerQ8RootNumberNegOneTopU) =
        4100 - deningerQ8RootNumberNegOneTopU ^ (2 : ℕ) := by
  linear_combination deningerQ8RootNumberNegOne_topU_linear_relation

theorem deningerQ8RootNumberNegOne_recoveryDenominator_ne_zero :
    2050 - 82 * deningerQ8RootNumberNegOneTopU ≠ 0 := by
  intro h
  letI : CharZero K3 :=
    charZero_of_injective_algebraMap (algebraMap ℚ K3).injective
  have h82 : (82 : K3) ≠ 0 := by norm_num
  have hu : deningerQ8RootNumberNegOneTopU = 25 := by
    apply (mul_left_cancel₀ h82)
    calc
      (82 : K3) * deningerQ8RootNumberNegOneTopU =
          2050 - (2050 - 82 * deningerQ8RootNumberNegOneTopU) := by ring
      _ = 2050 := by rw [h]; ring
      _ = 82 * 25 := by norm_num
  have hmul := deningerQ8RootNumberNegOne_topR_mul_recoveryDenominator
  rw [hu] at hmul
  norm_num at hmul

/-- First explicit recovery formula: `5 + √5` is rational in the top radical. -/
theorem deningerQ8RootNumberNegOne_topR_recovery_formula :
    deningerQ8RootNumberNegOneTopRInField =
      (4100 - deningerQ8RootNumberNegOneTopU ^ (2 : ℕ)) /
        (2050 - 82 * deningerQ8RootNumberNegOneTopU) := by
  apply (eq_div_iff deningerQ8RootNumberNegOne_recoveryDenominator_ne_zero).2
  exact deningerQ8RootNumberNegOne_topR_mul_recoveryDenominator

theorem deningerQ8RootNumberNegOne_topRInField_ne_zero :
    deningerQ8RootNumberNegOneTopRInField ≠ 0 := by
  intro h
  apply deningerQ8RootNumberNegOne_topR_ne_zero
  apply (algebraMap K1 K2).injective
  apply (algebraMap K2 K3).injective
  rw [map_zero, map_zero]
  change AdjoinRoot.of deningerQ8RootNumberNegOneThirdQuadraticPolynomial
      (AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial
        (5 + deningerQ8RootNumberNegOneFirstQuadraticRoot)) = 0
  rw [map_add, map_add, deningerQ8RootNumberNegOne_second_five,
    deningerQ8RootNumberNegOne_top_five]
  exact h

theorem deningerQ8RootNumberNegOne_topS_recovery_formula :
    deningerQ8RootNumberNegOneTopSInField =
      deningerQ8RootNumberNegOneTopU /
        deningerQ8RootNumberNegOneTopRInField := by
  apply (eq_div_iff deningerQ8RootNumberNegOne_topRInField_ne_zero).2
  rw [deningerQ8RootNumberNegOne_topU_eq_topR_mul_topS]
  ring

/-- Second explicit recovery formula: `√41` is rational in the top radical. -/
theorem deningerQ8RootNumberNegOne_topY_recovery_formula :
    deningerQ8RootNumberNegOneTopY =
      (deningerQ8RootNumberNegOneTopU /
        deningerQ8RootNumberNegOneTopRInField - 41) / 6 := by
  letI : CharZero K3 :=
    charZero_of_injective_algebraMap (algebraMap ℚ K3).injective
  have h6 : (6 : K3) ≠ 0 := by norm_num
  apply (eq_div_iff h6).2
  rw [← deningerQ8RootNumberNegOne_topS_recovery_formula]
  unfold deningerQ8RootNumberNegOneTopSInField
  ring

/-- The literal field written `ℚ(z)` for the top radical. -/
def deningerQ8RootNumberNegOnePrimitiveField : IntermediateField ℚ K3 :=
  IntermediateField.adjoin ℚ {deningerQ8RootNumberNegOneTopRoot}

theorem deningerQ8RootNumberNegOne_topRoot_mem_primitiveField :
    deningerQ8RootNumberNegOneTopRoot ∈ deningerQ8RootNumberNegOnePrimitiveField := by
  exact IntermediateField.mem_adjoin_simple_self ℚ deningerQ8RootNumberNegOneTopRoot

theorem deningerQ8RootNumberNegOne_topU_mem_primitiveField :
    deningerQ8RootNumberNegOneTopU ∈ deningerQ8RootNumberNegOnePrimitiveField := by
  unfold deningerQ8RootNumberNegOneTopU
  exact deningerQ8RootNumberNegOnePrimitiveField.pow_mem
    deningerQ8RootNumberNegOne_topRoot_mem_primitiveField 2

theorem deningerQ8RootNumberNegOne_topR_mem_primitiveField :
    deningerQ8RootNumberNegOneTopRInField ∈ deningerQ8RootNumberNegOnePrimitiveField := by
  rw [deningerQ8RootNumberNegOne_topR_recovery_formula]
  apply deningerQ8RootNumberNegOnePrimitiveField.div_mem
  · exact deningerQ8RootNumberNegOnePrimitiveField.sub_mem
      (deningerQ8RootNumberNegOnePrimitiveField.algebraMap_mem 4100)
      (deningerQ8RootNumberNegOnePrimitiveField.pow_mem
        deningerQ8RootNumberNegOne_topU_mem_primitiveField 2)
  · exact deningerQ8RootNumberNegOnePrimitiveField.sub_mem
      (deningerQ8RootNumberNegOnePrimitiveField.algebraMap_mem 2050)
      (deningerQ8RootNumberNegOnePrimitiveField.mul_mem
        (deningerQ8RootNumberNegOnePrimitiveField.algebraMap_mem 82)
        deningerQ8RootNumberNegOne_topU_mem_primitiveField)

theorem deningerQ8RootNumberNegOne_topX_mem_primitiveField :
    deningerQ8RootNumberNegOneTopX ∈ deningerQ8RootNumberNegOnePrimitiveField := by
  have hr : 5 + deningerQ8RootNumberNegOneTopX ∈
      deningerQ8RootNumberNegOnePrimitiveField := by
    simpa [deningerQ8RootNumberNegOneTopRInField] using
      deningerQ8RootNumberNegOne_topR_mem_primitiveField
  have h5 : (5 : K3) ∈ deningerQ8RootNumberNegOnePrimitiveField :=
    deningerQ8RootNumberNegOnePrimitiveField.algebraMap_mem 5
  simpa using deningerQ8RootNumberNegOnePrimitiveField.sub_mem hr h5

theorem deningerQ8RootNumberNegOne_topS_mem_primitiveField :
    deningerQ8RootNumberNegOneTopSInField ∈ deningerQ8RootNumberNegOnePrimitiveField := by
  rw [deningerQ8RootNumberNegOne_topS_recovery_formula]
  exact deningerQ8RootNumberNegOnePrimitiveField.div_mem
    deningerQ8RootNumberNegOne_topU_mem_primitiveField
    deningerQ8RootNumberNegOne_topR_mem_primitiveField

theorem deningerQ8RootNumberNegOne_topY_mem_primitiveField :
    deningerQ8RootNumberNegOneTopY ∈ deningerQ8RootNumberNegOnePrimitiveField := by
  rw [deningerQ8RootNumberNegOne_topY_recovery_formula]
  have hus : deningerQ8RootNumberNegOneTopU /
      deningerQ8RootNumberNegOneTopRInField ∈
        deningerQ8RootNumberNegOnePrimitiveField := by
    rw [← deningerQ8RootNumberNegOne_topS_recovery_formula]
    exact deningerQ8RootNumberNegOne_topS_mem_primitiveField
  apply deningerQ8RootNumberNegOnePrimitiveField.div_mem
  · exact deningerQ8RootNumberNegOnePrimitiveField.sub_mem hus
      (deningerQ8RootNumberNegOnePrimitiveField.algebraMap_mem 41)
  · exact deningerQ8RootNumberNegOnePrimitiveField.algebraMap_mem 6

theorem deningerQ8RootNumberNegOne_top_normal_form (w : K3) :
    ∃ a b : K2, w = a + b * deningerQ8RootNumberNegOneTopRoot := by
  let f := deningerQ8RootNumberNegOneThirdQuadraticPolynomial
  have hf : f.Monic := by
    dsimp [f, deningerQ8RootNumberNegOneThirdQuadraticPolynomial]
    exact monic_X_pow_sub_C deningerQ8RootNumberNegOneTopRadicand (by norm_num)
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective w
  let p : K2[X] := q %ₘ f
  have hpdeg : p.degree ≤ 1 := by
    have hlt : p.degree < (2 : WithBot ℕ) := by
      calc
        p.degree < f.degree := Polynomial.degree_modByMonic_lt q hf
        _ = 2 := by
          simp [f, deningerQ8RootNumberNegOneThirdQuadraticPolynomial,
            Polynomial.degree_X_pow_sub_C]
    by_cases hp : p = 0
    · simp [hp]
    rw [Polynomial.degree_eq_natDegree hp] at hlt ⊢
    have hlt' : p.natDegree < 2 := by exact_mod_cast hlt
    exact_mod_cast Nat.le_of_lt_succ hlt'
  refine ⟨p.coeff 0, p.coeff 1, ?_⟩
  rw [← AdjoinRoot.mk_leftInverse hf (AdjoinRoot.mk f q)]
  rw [AdjoinRoot.modByMonicHom_mk]
  change AdjoinRoot.mk f p = _
  rw [Polynomial.eq_X_add_C_of_degree_le_one hpdeg]
  simp [p, f, deningerQ8RootNumberNegOneTopRoot]
  ring

theorem deningerQ8RootNumberNegOne_firstEmbedded_mem_primitiveField (a : K1) :
    AdjoinRoot.of deningerQ8RootNumberNegOneThirdQuadraticPolynomial
      (AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial a) ∈
        deningerQ8RootNumberNegOnePrimitiveField := by
  obtain ⟨q, t, h⟩ := deningerQ8RootNumberNegOneFirstQuadratic_normal_form a
  rw [h, map_add, map_add, map_mul, map_mul]
  have hq : AdjoinRoot.of deningerQ8RootNumberNegOneThirdQuadraticPolynomial
      (AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial q) ∈
        deningerQ8RootNumberNegOnePrimitiveField := by
    exact deningerQ8RootNumberNegOnePrimitiveField.algebraMap_mem q
  have ht : AdjoinRoot.of deningerQ8RootNumberNegOneThirdQuadraticPolynomial
      (AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial t) ∈
        deningerQ8RootNumberNegOnePrimitiveField := by
    exact deningerQ8RootNumberNegOnePrimitiveField.algebraMap_mem t
  have hx : AdjoinRoot.of deningerQ8RootNumberNegOneThirdQuadraticPolynomial
      (AdjoinRoot.of deningerQ8RootNumberNegOneSecondQuadraticPolynomial
        deningerQ8RootNumberNegOneFirstQuadraticRoot) ∈
          deningerQ8RootNumberNegOnePrimitiveField := by
    simpa [deningerQ8RootNumberNegOneTopX] using
      deningerQ8RootNumberNegOne_topX_mem_primitiveField
  exact deningerQ8RootNumberNegOnePrimitiveField.add_mem hq
    (deningerQ8RootNumberNegOnePrimitiveField.mul_mem ht hx)

theorem deningerQ8RootNumberNegOne_secondEmbedded_mem_primitiveField (a : K2) :
    AdjoinRoot.of deningerQ8RootNumberNegOneThirdQuadraticPolynomial a ∈
      deningerQ8RootNumberNegOnePrimitiveField := by
  obtain ⟨c, d, h⟩ := deningerQ8RootNumberNegOneSecondQuadratic_normal_form a
  rw [h, map_add, map_mul]
  have hc := deningerQ8RootNumberNegOne_firstEmbedded_mem_primitiveField c
  have hd := deningerQ8RootNumberNegOne_firstEmbedded_mem_primitiveField d
  have hy : AdjoinRoot.of deningerQ8RootNumberNegOneThirdQuadraticPolynomial
      deningerQ8RootNumberNegOneSecondQuadraticRoot ∈
        deningerQ8RootNumberNegOnePrimitiveField := by
    simpa [deningerQ8RootNumberNegOneTopY] using
      deningerQ8RootNumberNegOne_topY_mem_primitiveField
  exact deningerQ8RootNumberNegOnePrimitiveField.add_mem hc
    (deningerQ8RootNumberNegOnePrimitiveField.mul_mem hd hy)

/-- The documented primitive radical generates the complete degree-eight tower. -/
theorem deningerQ8RootNumberNegOne_primitiveField_eq_top :
    deningerQ8RootNumberNegOnePrimitiveField = ⊤ := by
  apply top_unique
  intro w _
  obtain ⟨a, b, h⟩ := deningerQ8RootNumberNegOne_top_normal_form w
  rw [h]
  exact deningerQ8RootNumberNegOnePrimitiveField.add_mem
    (deningerQ8RootNumberNegOne_secondEmbedded_mem_primitiveField a)
    (deningerQ8RootNumberNegOnePrimitiveField.mul_mem
      (deningerQ8RootNumberNegOne_secondEmbedded_mem_primitiveField b)
      deningerQ8RootNumberNegOne_topRoot_mem_primitiveField)

end

end RHTower
