import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedLinearMollifier
import GaloisForLFunctions.RHTower.Sieve.DirichletConvolutionDivisorReindex
import GaloisForLFunctions.RHTower.Sieve.LevinsonLinearMollifiedCriticalCoefficient

/-!
# Finite convolution bridge for the critical linear mollifier

On a product index still inside the zeta head, the zero-based `dirConv` coefficient is exactly the
positive-natural Barban--Vehov coefficient constructed for the critical mollified zeta head.
-/

open Finset Complex

noncomputable section

namespace RHTower.Sieve

/-- Zero-based finite coefficient vector of the unsmoothed critical zeta head. -/
def levinsonCriticalHeadFinCoeff (L : ℕ) : Fin L → ℂ :=
  fun n => (((1 : ℝ) / Real.sqrt ((n : ℕ) + 1) : ℝ) : ℂ)

/-- Positive-natural extension of the finite critical zeta head. -/
theorem finCoeffNat_levinsonCriticalHeadFinCoeff (L n : ℕ) :
    finCoeffNat L (levinsonCriticalHeadFinCoeff L) n =
      if 1 ≤ n ∧ n ≤ L then (((1 : ℝ) / Real.sqrt n : ℝ) : ℂ) else 0 := by
  rw [finCoeffNat]
  split_ifs with h
  · change (((1 : ℝ) / Real.sqrt ((n - 1 : ℕ) + 1) : ℝ) : ℂ) = _
    norm_cast
    rw [Nat.cast_add, Nat.cast_sub h.1]
    norm_num
  · rfl

/-- The literal linear mollifier coefficient vanishes beyond its length. -/
theorem levinsonLinearMollifierCoeff_eq_zero_of_lt
    {M n : ℕ} (hMn : M < n) :
    levinsonLinearMollifierCoeff M n = 0 := by
  rw [levinsonLinearMollifierCoeff, barbanVehovWeight,
    if_neg (Nat.not_le_of_lt hMn)]
  simp

/-- At every positive index, the finite-vector extension equals the literal coefficient;
the coefficient itself supplies the upper support cutoff. -/
theorem finCoeffNat_levinsonLinearMollifierFinCoeff_of_pos
    (M : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    finCoeffNat M (RHTower.levinsonLinearMollifierFinCoeff M) n =
      levinsonLinearMollifierCoeff M n := by
  rw [finCoeffNat]
  split_ifs with h
  · change levinsonLinearMollifierCoeff M (n - 1 + 1) = _
    rw [Nat.sub_add_cancel h.1]
  · rw [levinsonLinearMollifierCoeff_eq_zero_of_lt (by omega)]

/-- On every product index inside the unsmoothed zeta head, the finite `dirConv` coefficient is
exactly the normalized Barban--Vehov critical product coefficient. -/
theorem dirConv_levinsonCriticalHead_eq_levinsonLinearMollifiedCriticalCoeff
    (L M : ℕ) (r : Fin (L * M)) (hrL : (r : ℕ) + 1 ≤ L) :
    dirConv L M (levinsonCriticalHeadFinCoeff L)
        (RHTower.levinsonLinearMollifierFinCoeff M) r =
      levinsonLinearMollifiedCriticalCoeff M ((r : ℕ) + 1) := by
  classical
  let K : ℕ := (r : ℕ) + 1
  have hK : 0 < K := by dsimp only [K]; omega
  rw [dirConv_eq_sum_divisors_finCoeffNat]
  have hterm : ∀ d ∈ K.divisors,
      finCoeffNat L (levinsonCriticalHeadFinCoeff L) d *
          finCoeffNat M (RHTower.levinsonLinearMollifierFinCoeff M) (K / d) =
        (((1 : ℝ) / Real.sqrt d : ℝ) : ℂ) *
          levinsonLinearMollifierCoeff M (K / d) := by
    intro d hdmem
    have hdvd : d ∣ K := Nat.dvd_of_mem_divisors hdmem
    have hdpos : 1 ≤ d := Nat.pos_of_mem_divisors hdmem
    have hdK : d ≤ K := Nat.le_of_dvd hK hdvd
    have hqpos : 1 ≤ K / d :=
      Nat.one_le_div_iff (by omega) |>.2 (Nat.le_of_dvd hK hdvd)
    rw [finCoeffNat_levinsonCriticalHeadFinCoeff,
      if_pos ⟨hdpos, le_trans hdK hrL⟩,
      finCoeffNat_levinsonLinearMollifierFinCoeff_of_pos M hqpos]
  rw [show ((r : ℕ) + 1) = K by rfl, Finset.sum_congr rfl hterm,
    levinsonLinearMollifiedCriticalCoeff]
  rw [← Nat.sum_divisorsAntidiagonal
      (fun d q => (((1 : ℝ) / Real.sqrt d : ℝ) : ℂ) *
        levinsonLinearMollifierCoeff M q)]
  exact Nat.sum_divisorsAntidiagonal'
    (fun d q => (((1 : ℝ) / Real.sqrt d : ℝ) : ℂ) *
      levinsonLinearMollifierCoeff M q)

end RHTower.Sieve
