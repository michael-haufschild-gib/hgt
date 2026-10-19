import GaloisForLFunctions.RHTower.Sieve.FiniteAdditiveLargeSieve
import GaloisForLFunctions.HTGeometry.FiniteRowRecombination

/-!
Weighted finite Fourier energy with colliding frequencies. Grouping equal
frequencies before Parseval preserves all signed cancellation within each
fibre. No injectivity assumption on the original frequency map is needed.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

variable {ι : Type*} [Fintype ι] {q : ℕ} [NeZero q]

def finiteWeightedFiber (f : ι → ZMod q) (a : ι → ℂ) (y : ZMod q) : ℂ :=
  ∑ i : {i // f i = y}, a i

theorem finiteWeightedFiber_character_sum (f : ι → ZMod q) (a : ι → ℂ) (n : ZMod q) :
    (∑ y : ZMod q, finiteWeightedFiber f a y * ZMod.stdAddChar (n * y)) =
      ∑ i, a i * ZMod.stdAddChar (n * f i) := by
  rw [← Fintype.sum_fiberwise f (fun i => a i * ZMod.stdAddChar (n * f i))]
  apply Finset.sum_congr rfl
  intro y _
  rw [finiteWeightedFiber, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [i.property]

/-- Exact Parseval with frequency collisions and arbitrary complex coefficients. -/
theorem sum_norm_sq_additive_phase_eq_fiber_energy (f : ι → ZMod q) (a : ι → ℂ) :
    (∑ n : ZMod q, ‖∑ i, a i * ZMod.stdAddChar (n * f i)‖ ^ 2) =
      (q : ℝ) * ∑ y : ZMod q, ‖finiteWeightedFiber f a y‖ ^ 2 := by
  simp_rw [← finiteWeightedFiber_character_sum f a]
  simpa only [Complex.normSq_eq_norm_sq] using
    _root_.RHTower.Sieve.sum_normSq_weighted_stdAddChar_mul_of_injective q
      (fun y : ZMod q => y) Function.injective_id (finiteWeightedFiber f a)

/-- All Fourier observations vanish exactly when each signed fibre total vanishes. -/
theorem additive_phase_vanishes_iff_fibers
    (f : ι → ZMod q) (a : ι → ℂ) :
    (∀ n : ZMod q, ∑ i, a i * ZMod.stdAddChar (n * f i) = 0) ↔
      ∀ y, finiteWeightedFiber f a y = 0 := by
  constructor
  · intro h
    have he := sum_norm_sq_additive_phase_eq_fiber_energy f a
    simp only [h, norm_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero] at he
    have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
    have hs : (∑ y : ZMod q, ‖finiteWeightedFiber f a y‖ ^ 2) = 0 :=
      (mul_eq_zero.mp he.symm).resolve_left hq
    intro y
    have hy := Finset.single_le_sum (fun z _ => sq_nonneg ‖finiteWeightedFiber f a z‖)
      (Finset.mem_univ y)
    rw [hs] at hy
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (finiteWeightedFiber f a y)])
  · intro h n
    rw [← finiteWeightedFiber_character_sum]
    simp [h]

/-- A fibre-size bound gives the exact collision loss in the finite large sieve. -/
theorem sum_norm_sq_additive_phase_le_fiber_card
    (f : ι → ZMod q) (a : ι → ℂ) (N : ℕ)
    (hN : ∀ y, Fintype.card {i // f i = y} ≤ N) :
    (∑ n : ZMod q, ‖∑ i, a i * ZMod.stdAddChar (n * f i)‖ ^ 2) ≤
      (q : ℝ) * N * ∑ i, ‖a i‖ ^ 2 := by
  rw [sum_norm_sq_additive_phase_eq_fiber_energy, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg q)
  calc
    _ ≤ ∑ y : ZMod q, (N : ℝ) * ∑ i : {i // f i = y}, ‖a i‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro y _
      have hc := norm_sum_smul_sq_le_mass (𝕜 := ℂ) Finset.univ
        (fun _ : {i // f i = y} => (1 : ℂ)) (fun i => a i)
      simp only [one_smul, norm_one, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one, one_mul] at hc
      exact hc.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hN y)
        (Finset.sum_nonneg fun i _ => sq_nonneg ‖a i‖))
    _ = _ := by
      rw [← Finset.mul_sum, Fintype.sum_fiberwise f (fun i => ‖a i‖ ^ 2)]

end GaloisForLFunctions.HTGeometry
