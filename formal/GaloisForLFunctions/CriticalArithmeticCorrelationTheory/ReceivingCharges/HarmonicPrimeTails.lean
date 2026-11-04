import GaloisForLFunctions.RHTower.WeilFullConeThreeHalvesLacunaryRigidity
import GaloisForLFunctions.RHTower.Sieve.HarmonicDyadicBlock

/-!
# Reciprocal source tails and terminal harmonic width

A finite band above a positive endpoint has inverse-square mass at most
the inverse endpoint. Terminal receiving rows cost their logarithmic width.
-/

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open Finset

/-- A finite source band above `R` has reciprocal-square mass at most `1/R`. -/
theorem finite_reciprocal_square_tail_le {P : Finset ℕ} {R : ℕ}
    (hR : 1 ≤ R) (hRP : ∀ p ∈ P, R < p) :
    (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ≤ 1 / (R : ℝ) := by
  classical
  have hinj : Set.InjOn (fun p : ℕ => p - (R + 1)) (↑P : Set ℕ) := by
    intro p hp q hq he
    have hpR := hRP p hp
    have hqR := hRP q hq
    change p - (R + 1) = q - (R + 1) at he
    omega
  have he :
      (∑ p ∈ P, 1 / (p : ℝ) ^ 2) =
      ∑ i ∈ P.image (fun p => p - (R + 1)), 1 / ((i + (R + 1) : ℕ) : ℝ) ^ 2 := by
    rw [sum_image hinj]
    apply sum_congr rfl
    intro p hp
    rw [Nat.sub_add_cancel (by have := hRP p hp; omega)]
  obtain ⟨hsum, hbound⟩ := _root_.RHTower.tsum_inv_nat_add_sq_le (R + 1) (by omega)
  rw [he]
  refine (hsum.sum_le_tsum _ (fun _ _ => by positivity)).trans (hbound.trans_eq ?_)
  push_cast
  ring

/-- The harmonic mass of a terminal interval is its logarithmic multiplicative width. -/
theorem terminal_harmonic_mass_le {J N : ℕ} {D : ℝ}
    (hJ : 1 ≤ J) (hJN : J ≤ N) (hDJ : (N : ℝ) ≤ D * J) :
    (∑ n ∈ Icc (J + 1) N, 1 / (n : ℝ)) ≤ Real.log D := by
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast hJ
  have hN0 : (0 : ℝ) < N := hJ0.trans_le (by exact_mod_cast hJN)
  have h := _root_.RHTower.Sieve.sum_Icc_one_div_le_log_sub
    (m := J + 1) (n := N) (by omega) (by omega)
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at h
  refine h.trans ?_
  rw [← Real.log_div hN0.ne' hJ0.ne']
  exact Real.log_le_log (div_pos hN0 hJ0) ((div_le_iff₀ hJ0).mpr hDJ)

#print axioms finite_reciprocal_square_tail_le
#print axioms terminal_harmonic_mass_le

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
