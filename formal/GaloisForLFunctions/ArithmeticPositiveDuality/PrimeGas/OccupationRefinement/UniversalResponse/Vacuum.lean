import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.UniversalResponse.Isometry
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.ModeCapacities.Partition

/-! # The vacuum output for a general conserving sequential response -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.UniversalResponse

open ModeCapacities CoassociativeSplitting

abbrev Response := {A : ℝ → ℂ // sequential A ∧ born A}

theorem response_iff (A : ℝ → ℂ) :
    sequential A ∧ born A ↔ sequential A ∧ conserving A :=
  and_congr_right fun h => (conserving_iff_born A h).symm

theorem response_at_one (A : Response) : A.val 1 = 1 := by
  have one : (1 : ℝ) ∈ Shares := ⟨zero_lt_one, le_rfl⟩
  have nz : A.val 1 ≠ 0 := by
    intro h
    have B := A.property.2 1 one
    rw [h, norm_zero, zero_pow two_ne_zero] at B
    exact zero_ne_one B
  have prod := A.property.1 1 one 1 one
  rw [one_mul] at prod
  exact mul_right_cancel₀ nz (prod.symm.trans (one_mul _).symm)

theorem response_contracts (A : Response) {x : ℝ} (hx : x ∈ Shares) : ‖A.val x‖ ≤ 1 := by
  have h := (A.property.2 x hx).trans_le hx.2
  nlinarith only [h, sq_nonneg (‖A.val x‖ - 1)]

private theorem realizes (A : Response) (t : Duration) :
    isometric (routing A.val (emit t.val) (survive t.val)) :=
  conserving_of_born A.property.2 _ _ (emit_pos t.property) (survive_pos t.val)

def apparatus (A : Response) (t : Duration) : Gas →ₗᵢ[ℂ] PairGas :=
  Classical.choose (realizes A t)

def vacuum (A : Response) (t : Duration) : Gas →L[ℂ] Gas :=
  vacuumSlice ∘L (apparatus A t).toContinuousLinearMap

theorem vacuum_apply (A : Response) (t : Duration) (f : Gas) (n : ℕ+) :
    vacuum A t f n = A.val (Real.exp (-t.val * energy n)) * f n := by
  change apparatus A t f (1,n) = _
  rw [show apparatus A t f (1,n) = wave (routing A.val (emit t.val) (survive t.val)) f (1,n) from
    Classical.choose_spec (realizes A t) f (1,n), wave, one_mul, routing]
  change A.val (branch (emit t.val) (survive t.val) 1 n.val) * f n = _
  rw [vacuum_probability]

theorem survival_share {t : ℝ} (ht : 0 ≤ t) (n : ℕ+) : Real.exp (-t * energy n) ∈ Shares :=
  ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) (Real.log_nonneg (by exact_mod_cast n.pos)))⟩

theorem vacuum_mass (A : Response) (t : Duration) (f : Gas) (n : ℕ+) :
    ‖vacuum A t f n‖ ^ 2 = Real.exp (-t.val * energy n) * ‖f n‖ ^ 2 := by
  rw [vacuum_apply, norm_mul, mul_pow, A.property.2 _ (survival_share t.property.le n)]

#print axioms response_iff
#print axioms vacuum_apply
#print axioms vacuum_mass

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.UniversalResponse
