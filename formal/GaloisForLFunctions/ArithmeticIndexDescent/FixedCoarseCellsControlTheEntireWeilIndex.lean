import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.HaarCellEffectivity
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.CompleteCellVariancePayment
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteConfigurationPontryaginLaw

/-!
# Finite coarse cells and the entire original Weil source

A fixed coarse cutoff costs its number of coefficient readouts. A universal
finite detail head pays the remaining pure Haar form. The resulting index
bound retains all prime powers, Gamma terms and original polar interactions.
-/

noncomputable section
open Finset
open RHTower
namespace GaloisForLFunctions.ArithmeticIndexDescent
open ArithmeticCastelnuovoSeveri.LogCells HTGeometry

/-- Extend a finite coarse coefficient vector by zero. -/
def fixedCoarseCoeffs (R : ℕ) (q : Fin R → ℝ) (a : ℕ) : ℝ :=
  if ha : a < R then q ⟨a, ha⟩ else 0

/-- The literal full Weil form on finite coarse cells and arbitrary balanced details. -/
def fixedCoarseFullWeilProfileForm {n R : ℕ}
    (q : Fin n → Fin R → ℝ) (d : Fin n → ℕ → ℝ) (X : ℕ) (x : Fin n → ℝ) : ℝ :=
  roughWeil (completePairProfile (fixedCoarseCoeffs R (fun a => ∑ i, x i * q i a))
    (fun a => ∑ i, x i * d i a) X)

private def coarseAndDetailHead {n R : ℕ}
    (q : Fin n → Fin R → ℝ) (d : Fin n → ℕ → ℝ) (A : ℕ) :
    (Fin n → ℝ) →ₗ[ℝ] (Fin (R + A) → ℝ) where
  toFun x a := if ha : (a : ℕ) < R then ∑ i, x i * q i ⟨a, ha⟩ else
    ∑ i, x i * d i ((a : ℕ) - R)
  map_add' x y := by
    funext a
    simp only [Pi.add_apply]
    split_ifs <;> simp only [add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    funext a
    simp only [Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp only [mul_assoc, Finset.mul_sum]
    all_goals rfl

/-- One universal detail head bounds the full negative dimension by the coarse size plus that head. -/
theorem exists_uniform_fixedCoarse_fullWeil_negative_dimension :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (R n : ℕ) (q : Fin n → Fin R → ℝ)
      (d : Fin n → ℕ → ℝ) (X : ℕ) (W : Submodule ℝ (Fin n → ℝ)),
      (∀ x ∈ W, x ≠ 0 → fixedCoarseFullWeilProfileForm q d X x < 0) →
        Module.finrank ℝ W ≤ R + A := by
  obtain ⟨A, hA, hpay⟩ := exists_haarTail_roughWeil_floor
  refine ⟨A, hA, ?_⟩
  intro R n q d X W hW
  let T := coarseAndDetailHead q d A
  have hnonneg (x : Fin n → ℝ) (hx : T x = 0) :
      0 ≤ fixedCoarseFullWeilProfileForm q d X x := by
    have hq (a : Fin R) : (∑ i, x i * q i a) = 0 := by
      have h : (if ha : (a : ℕ) < R then ∑ i, x i * q i ⟨a, ha⟩ else
          ∑ i, x i * d i ((a : ℕ) - R)) = 0 :=
        congrFun hx (⟨a, by omega⟩ : Fin (R + A))
      simpa only [dif_pos a.isLt] using h
    have hd (a : ℕ) (ha : a < A) : (∑ i, x i * d i a) = 0 := by
      have h : (if hb : R + a < R then ∑ i, x i * q i ⟨R + a, hb⟩ else
          ∑ i, x i * d i (R + a - R)) = 0 :=
        congrFun hx (⟨R + a, by omega⟩ : Fin (R + A))
      simpa only [dif_neg (by omega : ¬R + a < R), Nat.add_sub_cancel_left] using h
    have hqzero : fixedCoarseCoeffs R (fun a => ∑ i, x i * q i a) = 0 := by
      funext a
      unfold fixedCoarseCoeffs
      split_ifs <;> simp only [hq, Pi.zero_apply]
    have htail : haarTailCoeffs A (fun a => ∑ i, x i * d i a) =
        (fun a => ∑ i, x i * d i a) := by
      funext a
      by_cases ha : A ≤ a
      · exact if_pos ha
      · rw [haarTailCoeffs, if_neg ha, hd a (by omega)]
    have hp := hpay (fun a => ∑ i, x i * d i a) X
    rw [htail] at hp
    have hm : 0 ≤ ∑ a ∈ Icc 1 X, haarMass a * (∑ i, x i * d i a) ^ 2 :=
      sum_nonneg fun a ha => mul_nonneg (haarMass_pos (mem_Icc.mp ha).1).le (sq_nonneg _)
    have he : completePairProfile (fixedCoarseCoeffs R (fun a => ∑ i, x i * q i a))
        (fun a => ∑ i, x i * d i a) X = haarSectionProfile (fun a => ∑ i, x i * d i a) X := by
      rw [hqzero]
      funext u
      simp only [completePairProfile, averageSectionProfile, Pi.zero_apply, zero_mul,
        Finset.sum_const_zero, zero_add]
    change 0 ≤ roughWeil _
    rw [he]
    exact hm.trans hp
  have hker : LinearMap.ker (T.domRestrict W) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker, LinearMap.domRestrict_apply] at hx
    by_contra hx0
    have hv : (x : Fin n → ℝ) ≠ 0 := fun h0 => hx0 (Subtype.ext h0)
    exact (not_lt_of_ge (hnonneg x hx)) (hW x x.property hv)
  have hd := LinearMap.finrank_le_finrank_of_injective (LinearMap.ker_eq_bot.mp hker)
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using hd

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_uniform_fixedCoarse_fullWeil_negative_dimension
