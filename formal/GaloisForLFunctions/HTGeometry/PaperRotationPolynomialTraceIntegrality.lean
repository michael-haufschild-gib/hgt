import GaloisForLFunctions.HTGeometry.PaperRotationCanonicalTrace
import GaloisForLFunctions.HTGeometry.QuantumLaurentScalarAlgebra

/-!
# Integer canonical trace of finite Weyl idempotents

For an infinite-order clock, the concrete Weyl words are a linear basis of
the finite rotation algebra. Their coordinates define a faithful algebra
map into the explicitly constructed quantum Laurent division ring at
`exp(-it)`. The exact multiplication laws and traces agree.

Actual finite-Weyl matrix idempotents therefore have natural-number
canonical trace. This closes the formal-series to bounded-operator trace
comparison. It does not assert that arbitrary projections in the completed
rotation algebra admit finite-Weyl representatives, or construct such a
representative from the arithmetic Xi source.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open scoped Classical
local notation "RotOp" => PaperRotationHilbert →L[ℂ] PaperRotationHilbert

/-- Quantum parameter matching the ordered concrete Weyl cocycle. -/
def paperRotationQuantumUnit (t : ℝ) : ℂˣ :=
  Units.mk0 (paperRotationPhase (-t)) (by
    intro h
    have := paperRotationPhase_norm (-t)
    rw [h, norm_zero] at this
    exact zero_ne_one this)

theorem paperRotationQuantumUnit_zpow (t : ℝ) (n : ℤ) :
    (↑(paperRotationQuantumUnit t ^ n) : ℂ) = paperRotationPhase (-(n : ℝ) * t) := by
  simp only [Units.val_zpow_eq_zpow_val, paperRotationQuantumUnit, Units.val_mk0]
  rw [show -(n : ℝ) * t = (n : ℝ) * (-t) by ring]
  simp only [paperRotationPhase, Circle.exp_intCast_mul, Circle.coe_zpow]

/-- A word as an element of the finite operator algebra. -/
def paperRotationPolynomialWord (t : ℝ) (a b : ℤ) : paperRotationPolynomialAlgebra t :=
  ⟨paperRotationWord a ((b : ℝ) * t), paperRotationWord_mem_span t a b⟩

@[simp] theorem paperRotationPolynomialWord_zero (t : ℝ) :
    paperRotationPolynomialWord t 0 0 = 1 := by
  apply Subtype.ext
  change paperRotationWord 0 ((0 : ℤ) * t) = (1 : RotOp)
  simp only [Int.cast_zero, zero_mul, paperRotationWord, paperRotationModulation_zero,
    paperRotationShift_zero, ContinuousLinearMap.id_comp]
  rfl

theorem paperRotationPolynomialWord_mul (t : ℝ) (a b d e : ℤ) :
    paperRotationPolynomialWord t a b * paperRotationPolynomialWord t d e =
      (↑(paperRotationQuantumUnit t ^ (a * e)) : ℂ) •
        paperRotationPolynomialWord t (a + d) (b + e) := by
  apply Subtype.ext
  change paperRotationWord a ((b : ℝ) * t) ∘L paperRotationWord d ((e : ℝ) * t) =
    (↑(paperRotationQuantumUnit t ^ (a * e)) : ℂ) • paperRotationWord (a + d) (((b + e : ℤ) : ℝ) * t)
  rw [paperRotationWord_comp, paperRotationQuantumUnit_zpow]
  simp only [Int.cast_add,
    Int.cast_mul, add_mul, neg_mul, mul_assoc]

/-- Linear induction on finite Weyl operators. -/
theorem paperRotationPolynomial_induction (t : ℝ)
    (P : paperRotationPolynomialAlgebra t → Prop)
    (hword : ∀ a b, P (paperRotationPolynomialWord t a b))
    (hzero : P 0) (hadd : ∀ A B, P A → P B → P (A + B))
    (hsmul : ∀ z : ℂ, ∀ A, P A → P (z • A))
    (A : paperRotationPolynomialAlgebra t) : P A := by
  obtain ⟨A, hA⟩ := A
  induction hA using Submodule.span_induction with
  | mem A hA => obtain ⟨⟨a, b⟩, rfl⟩ := hA; exact hword a b
  | zero => exact hzero
  | add A B hA hB ihA ihB => exact hadd ⟨A, hA⟩ ⟨B, hB⟩ ihA ihB
  | smul z A hA ih => exact hsmul z ⟨A, hA⟩ ih

variable (t : ℝ) (ht : ∀ b : ℤ, paperRotationPhase ((b : ℝ) * t) = 1 ↔ b = 0)

private def polynomialLiftLinear : paperRotationPolynomialAlgebra t →ₗ[ℂ]
    QuantumLaurentDivisionRing (paperRotationQuantumUnit t) :=
  (Finsupp.linearCombination ℂ (fun ab : ℤ × ℤ =>
    quantumLaurentWord (paperRotationQuantumUnit t) ab.1 ab.2)).comp
      (paperRotationWords_linearIndependent t ht).repr

private theorem polynomialLift_word (a b : ℤ) :
    polynomialLiftLinear t ht (paperRotationPolynomialWord t a b) =
      quantumLaurentWord (paperRotationQuantumUnit t) a b := by
  change Finsupp.linearCombination ℂ _
    ((paperRotationWords_linearIndependent t ht).repr (paperRotationPolynomialWord t a b)) = _
  rw [(paperRotationWords_linearIndependent t ht).repr_eq_single (a, b) _ rfl,
    Finsupp.linearCombination_single, one_smul]

private theorem polynomialLift_one : polynomialLiftLinear t ht 1 = 1 := by
  rw [← paperRotationPolynomialWord_zero t, polynomialLift_word, quantumLaurentWord_zero]

private theorem polynomialLift_mul (A B : paperRotationPolynomialAlgebra t) :
    polynomialLiftLinear t ht (A * B) =
      polynomialLiftLinear t ht A * polynomialLiftLinear t ht B := by
  induction A using paperRotationPolynomial_induction t with
  | hword a b =>
    induction B using paperRotationPolynomial_induction t with
    | hword d e =>
      rw [paperRotationPolynomialWord_mul, map_smul, polynomialLift_word,
        polynomialLift_word, polynomialLift_word, quantumLaurentWord_mul]
    | hzero => simp
    | hadd B C hB hC => simp only [mul_add, map_add, hB, hC]
    | hsmul z B hB => simp only [mul_smul_comm, map_smul, hB]
  | hzero => simp
  | hadd A C hA hC => simp only [add_mul, map_add, hA, hC]
  | hsmul z A hA => simp only [smul_mul_assoc, map_smul, hA]

/-- The actual finite Weyl algebra maps to the constructed quantum Laurent division ring. -/
def paperRotationPolynomialLift : paperRotationPolynomialAlgebra t →ₐ[ℂ]
    QuantumLaurentDivisionRing (paperRotationQuantumUnit t) :=
  AlgHom.ofLinearMap (polynomialLiftLinear t ht) (polynomialLift_one t ht)
    (polynomialLift_mul t ht)

theorem paperRotationPolynomialLift_word (a b : ℤ) :
    paperRotationPolynomialLift t ht (paperRotationPolynomialWord t a b) =
      quantumLaurentWord (paperRotationQuantumUnit t) a b := polynomialLift_word t ht a b

/-- Exact comparison of the concrete canonical trace with the formal coefficient trace. -/
theorem paperRotationPolynomialLift_trace (A : paperRotationPolynomialAlgebra t) :
    quantumLaurentTrace (paperRotationQuantumUnit t) (paperRotationPolynomialLift t ht A) =
      paperRotationTrace A.val := by
  induction A using paperRotationPolynomial_induction t with
  | hword a b =>
    rw [paperRotationPolynomialLift_word, quantumLaurentTrace_word]
    exact (paperRotationTrace_integer_word t ht a b).symm
  | hzero => simp
  | hadd A B hA hB =>
    change quantumLaurentTrace _ (paperRotationPolynomialLift t ht (A + B)) =
      paperRotationTrace (A.val + B.val)
    rw [map_add, map_add, map_add, hA, hB]
  | hsmul z A hA =>
    change quantumLaurentTrace _ (paperRotationPolynomialLift t ht (z • A)) =
      paperRotationTrace (z • A.val)
    rw [map_smul, quantumLaurentTrace_smul, map_smul, hA]

include ht in
/-- Integer canonical trace of actual finite-Weyl matrix idempotents, with no lift or trace
existence premise. -/
theorem paperRotationPolynomial_idempotent_trace_eq_nat {n : ℕ}
    (E : Matrix (Fin n) (Fin n) (paperRotationPolynomialAlgebra t)) (hE : E * E = E) :
    ∃ r : ℕ, (∑ i, paperRotationTrace (E i i).val) = (r : ℂ) := by
  let L := paperRotationPolynomialLift t ht
  have hL : E.map L * E.map L = E.map L := by rw [← Matrix.map_mul, hE]
  obtain ⟨r, hr⟩ := quantumLaurentTrace_idempotent_eq_nat (paperRotationQuantumUnit t) (E.map L) hL
  refine ⟨r, ?_⟩
  simpa only [Matrix.map_apply, L, paperRotationPolynomialLift_trace] using hr

/-- The formal realization loses no finite operator: the canonical trace extracts every
coefficient in its Weyl basis. -/
theorem paperRotationPolynomialLift_injective :
    Function.Injective (paperRotationPolynomialLift t ht) := by
  have hzero (A : paperRotationPolynomialAlgebra t)
      (hA : paperRotationPolynomialLift t ht A = 0) : A = 0 := by
    let u := (paperRotationWords_linearIndependent t ht).repr A
    have hu : u = 0 := by
      ext k
      by_cases hk : k ∈ u.support
      · have hc : paperRotationTrace
            (star (paperRotationWord k.1 ((k.2 : ℝ) * t)) * A.val) = 0 := by
          calc
            _ = quantumLaurentTrace (paperRotationQuantumUnit t)
                (paperRotationPolynomialLift t ht
                  (star (paperRotationPolynomialWord t k.1 k.2) * A)) :=
              (paperRotationPolynomialLift_trace t ht _).symm
            _ = 0 := by rw [map_mul, hA, mul_zero, map_zero]
        have hr := (paperRotationWords_linearIndependent t ht).linearCombination_repr A
        change (∑ j ∈ u.support, u j • paperRotationWord j.1 ((j.2 : ℝ) * t)) = A.val at hr
        rw [← hr] at hc
        simp only [Finset.mul_sum, map_sum, mul_smul_comm, map_smul,
          paperRotationTrace_word_pair t ht] at hc
        have hi (j : ℤ × ℤ) : (k.1 = j.1 ∧ k.2 = j.2) ↔ k = j := Prod.ext_iff.symm
        simpa only [hi, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
          if_pos hk, Finsupp.zero_apply] using hc
      · simpa only [Finsupp.zero_apply] using Finsupp.notMem_support_iff.mp hk
    have hr := (paperRotationWords_linearIndependent t ht).linearCombination_repr A
    change Finsupp.linearCombination ℂ _ u = A.val at hr
    rw [hu, map_zero] at hr
    exact Subtype.ext hr.symm
  intro A B h
  exact sub_eq_zero.mp (hzero (A - B) (by rw [map_sub, h, sub_self]))

end
end GaloisForLFunctions.HTGeometry
