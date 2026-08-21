import GaloisForLFunctions.RHTower.Sieve.JutilaDirichletCoefficientRemoval
import GaloisForLFunctions.RHTower.Sieve.PowerFibreDivisorBound
import GaloisForLFunctions.RHTower.Sieve.MaynardRaisedDyadic

namespace RHTower.Sieve

open Finset Complex

noncomputable section

def jutilaCriticalPolynomial (L : ℕ) (t : ℝ) : ℂ :=
  jutilaCriticalDifferenceKernel L (fun _ => 1) t 0

def jutilaPowerCoefficient (L k : ℕ) : Fin (L ^ k) → ℂ :=
  convPow L k (fun _ => 1)

theorem jutilaCriticalDifferenceKernel_eq_dirPoly
    (L : ℕ) (a : Fin L → ℂ) (t u : ℝ) :
    jutilaCriticalDifferenceKernel L a t u =
      dirPoly L (sigmaWeightedCoeff L a ((1 : ℝ) / 2)) (t - u) := by
  rw [jutilaCriticalDifferenceKernel, dirPoly]
  apply Finset.sum_congr rfl
  intro n _
  rw [sigmaWeightedCoeff]
  congr 1
  push_cast
  ring_nf

theorem jutilaCriticalPolynomial_pow_eq
    (L k : ℕ) (t u : ℝ) :
    (jutilaCriticalPolynomial L (t - u)) ^ k =
      jutilaCriticalDifferenceKernel (L ^ k) (jutilaPowerCoefficient L k) t u := by
  rw [jutilaCriticalPolynomial, jutilaCriticalDifferenceKernel_eq_dirPoly,
    jutilaCriticalDifferenceKernel_eq_dirPoly]
  simp only [sub_zero]
  rw [← dirPoly_convPow]
  congr 2
  funext j
  exact convPow_sigmaWeightedCoeff L k (fun _ => 1) ((1 : ℝ) / 2) j

theorem norm_jutilaPowerCoefficient_le {eps : ℝ} (heps : 0 < eps)
    (L k : ℕ) (j : Fin (L ^ k)) :
    ‖jutilaPowerCoefficient L k j‖ ≤
      (divisorBoundConst eps * (((L ^ k : ℕ) : ℝ)) ^ eps) ^ k := by
  have hcard : ((powFibreOn L k Finset.univ j).card : ℝ) ≤
      (divisorBoundConst eps * (((L ^ k : ℕ) : ℝ)) ^ eps) ^ k :=
    powFibreOn_univ_card_le_rpow heps L k j
  have heq : ‖jutilaPowerCoefficient L k j‖ =
      ((powFibreOn L k Finset.univ j).card : ℝ) := by
    simp [jutilaPowerCoefficient, convPow, powFibreOn]
  rw [heq]
  exact hcard

theorem jutila_power_coefficient_removal {rho : Type*} [Fintype rho]
    {eps : ℝ} (heps : 0 < eps) (L k : ℕ) (tau : rho → ℝ) :
    ∑ r, ∑ s, ‖(jutilaCriticalPolynomial L (tau r - tau s)) ^ k‖ ^ 2 ≤
      (divisorBoundConst eps * (((L ^ k : ℕ) : ℝ)) ^ eps) ^ (2 * k) *
        ∑ r, ∑ s,
          ‖jutilaCriticalDifferenceKernel (L ^ k) (fun _ => 1) (tau r) (tau s)‖ ^ 2 := by
  let A : ℝ := (divisorBoundConst eps * (((L ^ k : ℕ) : ℝ)) ^ eps) ^ k
  have hA : 0 ≤ A := by
    dsimp [A]
    exact pow_nonneg (mul_nonneg (divisorBoundConst_pos heps).le (Real.rpow_nonneg (by positivity) _)) _
  have hbase := jutila_dirichlet_coefficient_removal (L ^ k) tau
    (jutilaPowerCoefficient L k) hA (norm_jutilaPowerCoefficient_le heps L k)
  have hpow : A ^ 2 =
      (divisorBoundConst eps * (((L ^ k : ℕ) : ℝ)) ^ eps) ^ (2 * k) := by
    dsimp [A]
    rw [← pow_mul]
    congr 1
    omega
  rw [hpow] at hbase
  simpa only [jutilaCriticalPolynomial_pow_eq] using hbase

end

end RHTower.Sieve
