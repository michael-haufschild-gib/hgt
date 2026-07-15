import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Linearity

/-!
# L-series of finite arithmetic-function determinants

This module packages the finite algebra needed to pass from Dirichlet-convolution determinants
of arithmetic functions to determinants of their absolutely convergent L-series.
-/

open scoped BigOperators

namespace GaloisForLFunctions

open LSeries ArithmeticFunction

noncomputable section

theorem coe_zsmul_arithmeticFunction (z : ℤ) (f : ArithmeticFunction ℂ) :
    ⇑(z • f) = (z : ℂ) • ⇑f := by
  funext n
  let ev : ArithmeticFunction ℂ →+ ℂ :=
    { toFun := fun g => g n
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change ev (z • f) = _
  rw [ev.map_zsmul]
  change z • f n = (z : ℂ) * f n
  rw [← Int.cast_smul_eq_zsmul ℂ]
  rfl

theorem coe_finsetSum_arithmeticFunction {ι : Type*} (s : Finset ι)
    (f : ι → ArithmeticFunction ℂ) :
    ⇑(∑ i ∈ s, f i) = ∑ i ∈ s, ⇑(f i) := by
  classical
  funext n
  let ev : ArithmeticFunction ℂ →+ ℂ :=
    { toFun := fun g => g n
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change ev (∑ i ∈ s, f i) = _
  rw [map_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rfl

theorem arithmeticFunction_one_LSeries (z : ℂ) :
    LSeriesSummable (⇑(1 : ArithmeticFunction ℂ)) z ∧
      LSeries (⇑(1 : ArithmeticFunction ℂ)) z = 1 := by
  have hterm : ∀ m : ℕ, m ≠ 1 →
      LSeries.term (⇑(1 : ArithmeticFunction ℂ)) z m = 0 := by
    intro m hm
    rcases Nat.eq_zero_or_pos m with rfl | hm1
    · exact LSeries.term_zero _ _
    · rw [LSeries.term_def, if_neg (by omega : m ≠ 0),
        ArithmeticFunction.one_apply, if_neg hm, zero_div]
  have hsumm : LSeriesSummable (⇑(1 : ArithmeticFunction ℂ)) z := by
    apply summable_of_ne_finset_zero (s := {1})
    intro m hm
    rw [Finset.mem_singleton] at hm
    exact hterm m hm
  refine ⟨hsumm, ?_⟩
  rw [LSeries, tsum_eq_single 1 hterm]
  rw [LSeries.term_def, if_neg one_ne_zero, ArithmeticFunction.one_apply, if_pos rfl]
  simp

theorem arithmeticFunction_finprod_LSeriesSummable {ι : Type*}
    (s : Finset ι) (f : ι → ArithmeticFunction ℂ) (z : ℂ)
    (hf : ∀ i ∈ s, LSeriesSummable (⇑(f i)) z) :
    LSeriesSummable (⇑(∏ i ∈ s, f i)) z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using (arithmeticFunction_one_LSeries z).1
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact ArithmeticFunction.LSeriesSummable_mul (hf i (Finset.mem_insert_self i s))
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem arithmeticFunction_finprod_LSeries {ι : Type*}
    (s : Finset ι) (f : ι → ArithmeticFunction ℂ) (z : ℂ)
    (hf : ∀ i ∈ s, LSeriesSummable (⇑(f i)) z) :
    LSeries (⇑(∏ i ∈ s, f i)) z =
      ∏ i ∈ s, LSeries (⇑(f i)) z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using (arithmeticFunction_one_LSeries z).2
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi]
      rw [ArithmeticFunction.LSeries_mul'
        (hf i (Finset.mem_insert_self i s))
        (arithmeticFunction_finprod_LSeriesSummable s f z
          (fun j hj => hf j (Finset.mem_insert_of_mem hj)))]
      rw [ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

set_option maxHeartbeats 500000 in
theorem arithmeticFunction_det_LSeriesSummable {q : ℕ}
    (M : Matrix (Fin q) (Fin q) (ArithmeticFunction ℂ)) (z : ℂ)
    (hM : ∀ i j, LSeriesSummable (⇑(M i j)) z) :
    LSeriesSummable (⇑M.det) z := by
  classical
  rw [Matrix.det_apply]
  let g : Equiv.Perm (Fin q) → ℕ → ℂ := fun σ =>
    ⇑(Equiv.Perm.sign σ • ∏ i, M (σ i) i)
  rw [coe_finsetSum_arithmeticFunction]
  change LSeriesSummable (∑ σ ∈ Finset.univ, g σ) z
  apply LSeriesSummable.sum
  intro σ hσ
  dsimp only [g]
  rw [show ⇑(Equiv.Perm.sign σ • ∏ i, M (σ i) i) =
      ((Equiv.Perm.sign σ : ℤ) : ℂ) • ⇑(∏ i, M (σ i) i) by
    exact coe_zsmul_arithmeticFunction _ _]
  exact (arithmeticFunction_finprod_LSeriesSummable Finset.univ
    (fun i => M (σ i) i) z (fun i hi => hM (σ i) i)).smul _

theorem arithmeticFunction_det_LSeries {q : ℕ}
    (M : Matrix (Fin q) (Fin q) (ArithmeticFunction ℂ)) (z : ℂ)
    (hM : ∀ i j, LSeriesSummable (⇑(M i j)) z) :
    LSeries (⇑M.det) z = Matrix.det (fun i j => LSeries (⇑(M i j)) z) := by
  classical
  rw [Matrix.det_apply, Matrix.det_apply]
  let g : Equiv.Perm (Fin q) → ℕ → ℂ := fun σ =>
    ⇑(Equiv.Perm.sign σ • ∏ i, M (σ i) i)
  have hg : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin q))),
      LSeriesSummable (g σ) z := by
    intro σ hσ
    dsimp only [g]
    rw [show ⇑(Equiv.Perm.sign σ • ∏ i, M (σ i) i) =
        ((Equiv.Perm.sign σ : ℤ) : ℂ) • ⇑(∏ i, M (σ i) i) by
      exact coe_zsmul_arithmeticFunction _ _]
    exact (arithmeticFunction_finprod_LSeriesSummable Finset.univ
      (fun i => M (σ i) i) z (fun i hi => hM (σ i) i)).smul _
  rw [coe_finsetSum_arithmeticFunction]
  change LSeries (∑ σ ∈ Finset.univ, g σ) z = _
  rw [LSeries_sum hg]
  apply Finset.sum_congr rfl
  intro σ hσ
  dsimp only [g]
  rw [show ⇑(Equiv.Perm.sign σ • ∏ i, M (σ i) i) =
      ((Equiv.Perm.sign σ : ℤ) : ℂ) • ⇑(∏ i, M (σ i) i) by
    exact coe_zsmul_arithmeticFunction _ _, LSeries_smul]
  rw [arithmeticFunction_finprod_LSeries Finset.univ (fun i => M (σ i) i) z
    (fun i hi => hM (σ i) i)]
  rw [Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ]
  rfl

end
end GaloisForLFunctions
