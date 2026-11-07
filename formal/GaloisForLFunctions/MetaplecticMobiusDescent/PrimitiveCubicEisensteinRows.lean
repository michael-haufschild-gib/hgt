/-
Primitive cubic cusp rows adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.TheCubicEisensteinSeries

/-!
# Primitive row coordinates of the actual cubic Eisenstein series

Bezout completion identifies cusp cosets with coprime rows `(c,d)` satisfying
`c=0` and `d=1` modulo three. Cubic reciprocity and denominator congruence
identify the inverse Kubota character with the row symbol `(c/d)₃`.
Reindexing preserves the actual absolutely convergent Eisenstein series.
-/
noncomputable section
open scoped BigOperators Classical MatrixGroups Matrix
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicKubota CubicJacobi

lemma levelThree_of_entries (M : SL(2,O))
    (h : ∀ i j : Fin 2, (3 : O) ∣ M i j - (if i=j then 1 else 0)) :
    M ∈ levelThree := by
  change Matrix.SpecialLinearGroup.map (n := Fin 2)
    (Ideal.Quotient.mk (Ideal.span {(3 : O)})) M = 1
  apply Subtype.ext
  funext i j
  change Ideal.Quotient.mk (Ideal.span {(3 : O)}) (M i j) =
    (1 : Matrix (Fin 2) (Fin 2) (O ⧸ Ideal.span {(3 : O)})) i j
  have hh : Ideal.Quotient.mk (Ideal.span {(3 : O)}) (M i j) =
      Ideal.Quotient.mk (Ideal.span {(3 : O)}) (if i=j then 1 else 0) :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
      (Ideal.mem_span_singleton.mpr (h i j))
  simpa only [Matrix.one_apply, apply_ite, map_one, map_zero] using hh

lemma row_coprime (M : levelThree) : IsCoprime (row M 0) (row M 1) := by
  have h : (M : SL(2,O)) 0 0*(M : SL(2,O)) 1 1 -
      (M : SL(2,O)) 0 1*(M : SL(2,O)) 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using (M : SL(2,O)).property
  refine ⟨-(M : SL(2,O)) 0 1, (M : SL(2,O)) 0 0, ?_⟩
  change -(M : SL(2,O)) 0 1*(M : SL(2,O)) 1 0 +
    (M : SL(2,O)) 0 0*(M : SL(2,O)) 1 1 = 1
  linear_combination h

lemma exists_matrix_of_primitive_row (c d : O) (hcop : IsCoprime c d)
    (hc : (3 : O) ∣ c) (hd : (3 : O) ∣ d-1) :
    ∃ M : levelThree, row M = ![c,d] := by
  obtain ⟨r,s,hrs⟩ := hcop
  let M : SL(2,O) := ⟨!![s+r*c,r*(d-1); c,d], by
    rw [Matrix.det_fin_two]
    change (s+r*c)*d-(r*(d-1))*c=1
    linear_combination hrs⟩
  have hA : s+r*c-1 = -s*(d-1) := by linear_combination hrs
  have hM : M ∈ levelThree := by
    apply levelThree_of_entries
    intro i j
    fin_cases i <;> fin_cases j
    · change (3 : O) ∣ s+r*c-1
      rw [hA]
      exact hd.mul_left (-s)
    · change (3 : O) ∣ r*(d-1)-0
      simpa only [sub_zero] using hd.mul_left r
    · change (3 : O) ∣ c-(if (1 : Fin 2)=0 then 1 else 0)
      simpa only [show (1 : Fin 2) ≠ 0 by decide, ite_false, sub_zero] using hc
    · change (3 : O) ∣ d-1
      exact hd
  exact ⟨⟨M,hM⟩, rfl⟩

def PrimitiveRow := {v : Fin 2 → O //
  IsCoprime (v 0) (v 1) ∧ (3 : O) ∣ v 0 ∧ (3 : O) ∣ v 1-1}

def cosetPrimitiveRow (x : CuspCosets) : PrimitiveRow :=
  ⟨cosetRow x, by
    induction x using Quotient.inductionOn with | _ M =>
      change IsCoprime (row M 0) (row M 1) ∧ (3 : O) ∣ row M 0 ∧ (3 : O) ∣ row M 1-1
      exact ⟨row_coprime M, levelThree_lower M, by simpa [row] using levelThree_entry M 1 1⟩⟩

lemma cosetPrimitiveRow_bijective : Function.Bijective cosetPrimitiveRow := by
  constructor
  · intro x y hxy
    exact cosetRow_injective (congrArg Subtype.val hxy)
  · intro v
    obtain ⟨M,hM⟩ := exists_matrix_of_primitive_row (v.1 0) (v.1 1)
      v.2.1 v.2.2.1 v.2.2.2
    refine ⟨cosetOf M, ?_⟩
    apply Subtype.ext
    change row M = v.1
    rw [hM]
    funext i
    fin_cases i <;> rfl

def primitiveRowEquiv : CuspCosets ≃ PrimitiveRow := Equiv.ofBijective _ cosetPrimitiveRow_bijective

open Eisenstein CubicKubota CubicJacobi

lemma inverse_character_eq_row_symbol (M : levelThree) :
    (complexCharacter M)⁻¹ = ringComplex (symbol (row M 0) (row M 1)) := by
  let a := (M : SL(2,O)) 0 0
  let b := (M : SL(2,O)) 0 1
  let c := (M : SL(2,O)) 1 0
  let d := (M : SL(2,O)) 1 1
  have hdet : a*d-b*c=1 := by
    simpa only [a,b,c,d,Matrix.det_fin_two] using (M : SL(2,O)).property
  have had : a*d-1=b*c := by linear_combination hdet
  have ha : lambda^2 ∣ a-1 := levelThree_primary M
  have hd3 : (3 : O) ∣ d-1 := by simpa [d] using levelThree_entry M 1 1
  have hd : lambda^2 ∣ d-1 := lambda_sq_dvd_three.trans hd3
  obtain ⟨b0,hb⟩ := levelThree_upper M
  obtain ⟨c0,hc⟩ := levelThree_lower M
  change b=3*b0 at hb
  change c=3*c0 at hc
  have h9 : (9 : O) ∣ a*d-1 := by
    refine ⟨b0*c0, ?_⟩
    rw [had,hb,hc]
    ring
  have hcd : c ∣ a*d-1 := by rw [had]; exact dvd_mul_left c b
  have hs := symbol_denominator_congr c (a*d) 1 (primary_mul a d ha hd) (by simp) h9 hcd
  rw [symbol_mul_denominator, symbol_one] at hs
  have hm : ringComplex (symbol c a)*ringComplex (symbol c d)=1 := by
    simpa only [map_mul, map_one] using congrArg ringComplex hs
  change (ringComplex (symbol c a))⁻¹ = ringComplex (symbol c d)
  exact inv_eq_of_mul_eq_one_right hm

lemma inverse_cosetCharacter_eq_row_symbol (x : CuspCosets) :
    (cosetCharacter x)⁻¹ = ringComplex (symbol (cosetRow x 0) (cosetRow x 1)) := by
  induction x using Quotient.inductionOn with | _ M => exact inverse_character_eq_row_symbol M

def primitiveRowPhase (v : PrimitiveRow) : ℂ :=
  ringComplex (symbol (v.1 0) (v.1 1))

lemma primitiveRowEquiv_val (x : CuspCosets) : (primitiveRowEquiv x).1 = cosetRow x := rfl

lemma primitiveRowEquiv_symm_row (v : PrimitiveRow) :
    cosetRow (primitiveRowEquiv.symm v) = v.1 := by
  exact congrArg Subtype.val (primitiveRowEquiv.apply_symm_apply v)

theorem upperEisenstein_eq_primitive_rows (z : ℂ) (v : ℝ) (hv : 0 < v) (s : ℂ) :
    upperEisenstein z v hv s = ∑' row : PrimitiveRow,
      primitiveRowPhase row *
        ((v / (‖ringComplex (row.1 0)*z+ringComplex (row.1 1)‖^2 +
          ‖ringComplex (row.1 0)‖^2*v^2) : ℝ) : ℂ)^s := by
  rw [upperEisenstein_eq_source_series]
  rw [← primitiveRowEquiv.symm.tsum_eq]
  apply tsum_congr
  intro r
  rw [inverse_cosetCharacter_eq_row_symbol, primitiveRowEquiv_symm_row]
  simp only [primitiveRowPhase, transformedHeight, heightDenominator, embeddedRow,
    Function.comp_apply, primitiveRowEquiv_symm_row]

theorem primitive_rows_summable_norm (z : ℂ) (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 2 < s.re) :
    Summable (fun row : PrimitiveRow => ‖primitiveRowPhase row *
      ((v / (‖ringComplex (row.1 0)*z+ringComplex (row.1 1)‖^2 +
        ‖ringComplex (row.1 0)‖^2*v^2) : ℝ) : ℂ)^s‖) := by
  apply primitiveRowEquiv.summable_iff.mp
  apply (summable_norm_summand (upperSection z v hv) s hs).congr
  intro x
  rw [summand_upperSection, inverse_cosetCharacter_eq_row_symbol]
  rfl

lemma primitiveRow_zero_left (row : PrimitiveRow) (hc : row.1 0 = 0) : row.1 1 = 1 := by
  have hu : IsUnit (row.1 1) := by simpa only [hc, isCoprime_zero_left] using row.2.1
  exact CubicJacobi.primary_isUnit_eq_one _ hu (lambda_sq_dvd_three.trans row.2.2.2)

#print axioms primitiveRowEquiv
#print axioms inverse_character_eq_row_symbol
#print axioms upperEisenstein_eq_primitive_rows
#print axioms primitive_rows_summable_norm
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
