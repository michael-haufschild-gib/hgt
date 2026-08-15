import GaloisForLFunctions.RHTower.RoutePPrimitiveBaseCauchyCapacityReduction
import GaloisForLFunctions.RHTower.XiWardCubicLogMomentEulerSource

/-!
# Route P primitive base balanced-reflection codiagonal

The unregularized biorthogonal source/co-source pairing is exact but nonsummable on the balanced
reflection wall. This module proves that inserting the undifferenced cubic Cauchy self-kernel
before summation produces exactly the complete P-G181 primitive base budget. The identity holds
cellwise, is independent of balanced displacement, and identifies every finite base Gram trace
with a finite source-native codiagonal before any Xi-zero or divisor expansion.

Thus the strict `< 2` side of the raw modular-conormal comparison is already a literal two-sided
Euler source trace. The remaining Route P obstruction is continuation of this regularized
codiagonal to the completed Xi conormal, not construction or estimation of its source budget.
-/

open Complex Matrix
open scoped BigOperators ComplexOrder

namespace RHTower

noncomputable section

/-- Cubically regularized balanced source/co-source codiagonal on one primitive Euler cell. -/
def routePPrimitiveBaseBalancedReflectionCodiagonal
    (a : ℝ) (pe : Nat.Primes × ℕ) : ℂ :=
  routePBaseCauchyCubicKernel 1
      (xiGammaEulerPrimitiveLogFrequency pe)
      (xiGammaEulerPrimitiveLogFrequency pe) 0 *
    (xiGammaEulerPrimitiveCommonTestSourceCoeff (a : ℂ) pe *
      star (xiGammaEulerPrimitiveCommonTestCoSourceCoeff (-a : ℂ) pe))

/-- The undifferenced base Cauchy cube is exactly `216/115` times the dyadic collision cubic
moment on every positive frequency. -/
theorem routePBaseCauchyCubicKernel_self_eq_collision_rescale
    {u : ℝ} (hu : 0 < u) :
    routePBaseCauchyCubicKernel 1 u u 0 =
      (216 / 115 : ℂ) * (cubicLogMomentHellingerHorizontalKernel u u : ℂ) := by
  rw [routePBaseCauchyCubicKernel_diagonal (by norm_num) hu,
    cubicLogMomentHellingerHorizontalKernel_self hu]
  push_cast
  field_simp [hu.ne']
  ring

/-- Exact source identity: balanced reflection plus cubic regularization is the literal P-G181
primitive base weight, independently of displacement. -/
theorem routePPrimitiveBaseBalancedReflectionCodiagonal_eq_weight
    (a : ℝ) (pe : Nat.Primes × ℕ) :
    routePPrimitiveBaseBalancedReflectionCodiagonal a pe =
      (routePPrimitiveBaseCauchyCubicWeight pe : ℂ) := by
  rw [routePPrimitiveBaseBalancedReflectionCodiagonal,
    routePBaseCauchyCubicKernel_self_eq_collision_rescale
      (xiGammaEulerPrimitiveLogFrequency_pos pe)]
  rw [routePPrimitiveBaseCauchyCubicWeight]
  push_cast
  rw [← xiGammaEulerPrimitiveCubicLogMomentDiagonal_eq_weight a pe,
    xiGammaEulerPrimitiveCubicLogMomentDiagonal]
  ring

/-- The regularized balanced source codiagonal is independent of the reflection displacement
before summation. -/
theorem routePPrimitiveBaseBalancedReflectionCodiagonal_independent
    (a b : ℝ) (pe : Nat.Primes × ℕ) :
    routePPrimitiveBaseBalancedReflectionCodiagonal a pe =
      routePPrimitiveBaseBalancedReflectionCodiagonal b pe := by
  rw [routePPrimitiveBaseBalancedReflectionCodiagonal_eq_weight,
    routePPrimitiveBaseBalancedReflectionCodiagonal_eq_weight]

theorem summable_routePPrimitiveBaseBalancedReflectionCodiagonal
    (a : ℝ) :
    Summable (routePPrimitiveBaseBalancedReflectionCodiagonal a) := by
  have hcomplex : Summable (fun pe : Nat.Primes × ℕ =>
      (routePPrimitiveBaseCauchyCubicWeight pe : ℂ)) :=
    summable_routePPrimitiveBaseCauchyCubicWeight.map
      Complex.ofRealCLM Complex.ofRealCLM.continuous
  exact hcomplex.congr fun pe =>
    (routePPrimitiveBaseBalancedReflectionCodiagonal_eq_weight a pe).symm

/-- The entire source-native balanced codiagonal is exactly the `< 2` P-G181 budget. -/
theorem tsum_routePPrimitiveBaseBalancedReflectionCodiagonal_eq_budget
    (a : ℝ) :
    ∑' pe : Nat.Primes × ℕ,
        routePPrimitiveBaseBalancedReflectionCodiagonal a pe =
      (routePPrimitiveBaseCauchyCubicTraceBudget : ℂ) := by
  calc
    ∑' pe : Nat.Primes × ℕ,
        routePPrimitiveBaseBalancedReflectionCodiagonal a pe =
        ∑' pe : Nat.Primes × ℕ,
          (routePPrimitiveBaseCauchyCubicWeight pe : ℂ) := by
      apply tsum_congr
      exact routePPrimitiveBaseBalancedReflectionCodiagonal_eq_weight a
    _ = ((∑' pe : Nat.Primes × ℕ,
          routePPrimitiveBaseCauchyCubicWeight pe : ℝ) : ℂ) := by
      rw [← Complex.ofReal_tsum]
    _ = (routePPrimitiveBaseCauchyCubicTraceBudget : ℂ) := rfl

/-- Every finite base Gram trace is the corresponding finite balanced source codiagonal, before
any zero/divisor expansion. -/
theorem trace_routePPrimitiveBaseCauchyCubicKernelMatrix_eq_balanced_source
    {N : ℕ} (a : ℝ) (pe : Fin N → Nat.Primes × ℕ) (kappa : Fin N → ℝ) :
    (routePPrimitiveBaseCauchyCubicKernelMatrix 1 pe kappa).trace =
      ∑ i : Fin N,
        routePPrimitiveBaseBalancedReflectionCodiagonal a (pe i) := by
  rw [trace_routePPrimitiveBaseCauchyCubicKernelMatrix (by norm_num)]
  apply Finset.sum_congr rfl
  intro i _hi
  exact (routePPrimitiveBaseBalancedReflectionCodiagonal_eq_weight a (pe i)).symm

/-- The completed source-side codiagonal has strict subquantum mass. -/
theorem re_tsum_routePPrimitiveBaseBalancedReflectionCodiagonal_lt_two
    (a : ℝ) :
    (∑' pe : Nat.Primes × ℕ,
      routePPrimitiveBaseBalancedReflectionCodiagonal a pe).re < 2 := by
  rw [tsum_routePPrimitiveBaseBalancedReflectionCodiagonal_eq_budget]
  simpa using routePPrimitiveBaseCauchyCubicTraceBudget_lt_quantum

end

end RHTower
