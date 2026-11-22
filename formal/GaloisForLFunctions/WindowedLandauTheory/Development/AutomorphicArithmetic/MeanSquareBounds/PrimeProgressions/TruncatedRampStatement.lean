import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.SmoothedIdentity
import GaloisForLFunctions.WindowedLandauTheory.LandauZeroFreeBounds.Statement

/-! A normalized ramp formula with a finite zero sum and its analytic multiplicities. -/

open Complex Finset WindowedLandauTheory.HC WindowedLandauTheory.ZeroFreeDirichlet

noncomputable section

namespace QH.PrimeProgressions

def rampMain {N : ℕ} (χ : DirichletCharacter ℂ N) (y : ℝ) : ℂ := by
  classical
  exact if χ = 1 then ((Real.log y - 1 : ℝ) : ℂ) else 0

def Cutoff (κ T : ℝ) (ρ : ℂ) : Prop := 1 - κ < ρ.re ∧ |ρ.im| ≤ T

instance (κ T : ℝ) : DecidablePred (Cutoff κ T) := fun ρ =>
  inferInstanceAs (Decidable (1 - κ < ρ.re ∧ |ρ.im| ≤ T))

def TruncatedRamp {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (κ T C : ℝ) : Prop :=
  ∃ (Z : Finset ℂ) (K : ℂ),
    (∀ ρ, ρ ∈ Z ↔ IsLZero χ ρ ∧ Cutoff κ T ρ) ∧
    (∀ ρ ∈ Z, 1 ≤ analyticOrderNatAt χ.LFunction ρ) ∧
    (∀ t : ℝ, (∑ ρ ∈ Z.filter (fun ρ => |ρ.im - t| ≤ 1), (analyticOrderNatAt χ.LFunction ρ : ℝ)) ≤
      C * Real.log ((N : ℝ) * (|t| + 2))) ∧
    ∀ y : ℝ, 2 ≤ y →
      ‖An.sumLamChi χ y / (y : ℂ) - K - rampMain χ y +
        ∑ ρ ∈ Z, (analyticOrderNatAt χ.LFunction ρ : ℂ) * QH.zeroKernel y ρ‖ ≤
          C * ((N : ℝ) ^ 3 * y ^ (-(κ / 2)) + Real.log ((N : ℝ) * T) ^ 2 / T)

theorem inverse_log_error {y κ : ℝ} (hy : 2 ≤ y) (hκ : κ ≤ 1) :
    (1 + Real.log y) / y ≤ 3 * y ^ (-(κ / 2)) := by
  have hy₁ : 1 ≤ y := by linarith
  have hy₀ : 0 < y := by linarith
  have hs : 1 ≤ Real.sqrt y := Real.one_le_sqrt.mpr hy₁
  have hs₀ : 0 < Real.sqrt y := zero_lt_one.trans_le hs
  have hlog := Real.log_le_sub_one_of_pos hs₀
  rw [Real.log_sqrt hy₀.le] at hlog
  have hpow : Real.sqrt y / y = y ^ (-(1 / 2) : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub_one hy₀.ne']
    congr 1
    ring
  calc (1 + Real.log y) / y ≤ 3 * Real.sqrt y / y :=
        div_le_div_of_nonneg_right (by linarith only [hs, hlog]) hy₀.le
    _ = 3 * y ^ (-(1 / 2) : ℝ) := by rw [mul_div_assoc, hpow]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hy₁ (by linarith)) (by norm_num)

end QH.PrimeProgressions
