import GaloisForLFunctions.RHTower.Sieve.RouteTHybridZetaAssembly
import GaloisForLFunctions.RHTower.Sieve.ZetaPartialSumTruncation

/-!
# Near-one zeta growth from Route T

The hybrid partial-sum estimate is attached to the exact Euler--Maclaurin truncation.  No
cancellation is discarded: only the two explicit continuation tails remain.
-/

namespace RHTower.Sieve

open Finset Complex

noncomputable section

/-- **Parameterized Route-T zeta growth theorem.**  Any global shell certificate satisfying the
degree-nine start threshold gives an actual zeta bound on the hybrid strip. -/
theorem norm_riemannZeta_le_routeT_uniform
    {A V R : ℕ} {σ t : ℝ}
    (hA : 2 ≤ A) (hσ0 : 0 < σ) (hσ1 : σ < 1) (ht : 1 < t)
    (hsize : 2 ^ (routeTLogCentreExponent *
      (routeTLogReceiverDegreeNineConstant * (V + 1) ^ 9 + 1)) ≤ A)
    (htop : t ≤ (((routeTLogRootBase A ^ routeTLogCentreExponent) ^
      (4 * V) : ℕ) : ℝ))
    (hfac : Nat.factorial 565 ≤ A + 1)
    (hlow : 8 * Real.pi *
      (((A * 2 ^ (R - 1) + 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3) ≤ t)
    (hroute : 2 * (1 - σ) ≤
      1 / (5000000000000000 * (V : ℝ) ^ 4))
    (hderivative : 1 - σ ≤ 1 / (3 * (2 : ℝ) ^ (566 : ℕ))) :
    ‖riemannZeta ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤
      (1 + ((A : ℝ) ^ (1 - σ) - 1) / (1 - σ) + (A : ℝ) ^ (-σ)) +
        (R : ℝ) * 6912 +
      ((A * 2 ^ R : ℕ) : ℝ) ^ (1 - σ) /
        ‖(σ : ℂ) + Complex.I * (t : ℂ) - 1‖ +
      ‖(σ : ℂ) + Complex.I * (t : ℂ)‖ *
        (((A * 2 ^ R : ℕ) : ℝ) ^ (-σ) / σ) := by
  let w : ℂ := (σ : ℂ) + Complex.I * (t : ℂ)
  let N : ℕ := A * 2 ^ R
  have hwre : w.re = σ := by simp [w]
  have hw0 : 0 < w.re := by simpa only [hwre] using hσ0
  have hwne : w ≠ 1 := by
    intro heq
    have him : w.im = t := by simp [w]
    rw [heq] at him
    simp at him
    linarith
  have hN : 1 ≤ N := by
    dsimp only [N]
    calc
      1 = 1 * 1 := (Nat.one_mul 1).symm
      _ ≤ A * 2 ^ R := Nat.mul_le_mul (by omega) Nat.one_le_two_pow
  have htrunc := norm_riemannZeta_le_partialSum hw0 hwne hN
  have hpartial := norm_routeTZeta_partialSum_le_uniform hA hσ0 hσ1 ht
    hsize htop hfac hlow hroute hderivative
  have hsum :
      (∑ k ∈ Finset.Icc 1 N, ((k : ℝ) : ℂ) ^ (-w)) =
        ∑ n ∈ Finset.Icc 1 (A * 2 ^ R),
          (n : ℂ) ^ (-((σ : ℂ) + Complex.I * (t : ℂ))) := by
    dsimp only [N, w]
    apply Finset.sum_congr rfl
    intro n _hn
    congr 1
  rw [hsum, hwre] at htrunc
  dsimp only [w, N] at htrunc ⊢
  exact htrunc.trans (by gcongr)

end

end RHTower.Sieve
