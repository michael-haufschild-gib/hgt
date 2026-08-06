import Mathlib

/-!
# Krylov moment cancellation is amplified by replicas

If a finite spectral amplitude annihilates moments of orders `0, ..., K`,
then it has an analytic zero of order at least `K + 1`.  Consequently, the
product of the `r`th powers of two such amplitudes has a zero of order at
least `2 * r * (K + 1)`.  Equivalently, all lower replica-product moments
vanish.  This is the exact cancellation retained by a Krylov-orthogonal
observable and amplified by growing replica order.
-/

open scoped BigOperators Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Finite complex exponential amplitude with arbitrary coefficients and
frequencies. -/
def finiteComplexExponentialAmplitude
    {I : Type*} [Fintype I]
    (coefficient frequency : I → ℂ) (z : ℂ) : ℂ :=
  ∑ i, coefficient i * Complex.exp (frequency i * z)

theorem finiteComplexExponentialAmplitude_analyticAt
    {I : Type*} [Fintype I]
    (coefficient frequency : I → ℂ) (z : ℂ) :
    AnalyticAt ℂ (finiteComplexExponentialAmplitude coefficient frequency) z := by
  unfold finiteComplexExponentialAmplitude
  fun_prop

/-- Derivatives at the origin are the corresponding spectral moments. -/
theorem iteratedDeriv_finiteComplexExponentialAmplitude_zero
    {I : Type*} [Fintype I]
    (coefficient frequency : I → ℂ) (k : ℕ) :
    iteratedDeriv k (finiteComplexExponentialAmplitude coefficient frequency) 0 =
      ∑ i, coefficient i * frequency i ^ k := by
  classical
  unfold finiteComplexExponentialAmplitude
  rw [iteratedDeriv_fun_sum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [iteratedDeriv_const_mul_field]
    rw [congrFun (iteratedDeriv_cexp_const_mul k (frequency i)) 0]
    simp
  · intro i hi
    fun_prop

/-- Vanishing moments through order `K` force an analytic zero of order at
least `K + 1`. -/
theorem analyticOrderAt_finiteComplexExponentialAmplitude_ge
    {I : Type*} [Fintype I]
    {coefficient frequency : I → ℂ} {K : ℕ}
    (hmoment : ∀ k ≤ K, ∑ i, coefficient i * frequency i ^ k = 0) :
    (K + 1 : ℕ) ≤ analyticOrderAt
      (finiteComplexExponentialAmplitude coefficient frequency) 0 := by
  let F := finiteComplexExponentialAmplitude coefficient frequency
  have hF : AnalyticAt ℂ F 0 :=
    finiteComplexExponentialAmplitude_analyticAt coefficient frequency 0
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hF]
  intro k hk
  rw [iteratedDeriv_finiteComplexExponentialAmplitude_zero]
  exact hmoment k (by omega)

/-- Replica amplification law.  If both one-copy factors annihilate moments
through order `K`, their paired `r`-replica product annihilates every moment
strictly below `2 * r * (K + 1)`. -/
theorem iteratedDeriv_replicaProduct_zero_of_moment_null
    {I J : Type*} [Fintype I] [Fintype J]
    {leftCoefficient leftFrequency : I → ℂ}
    {rightCoefficient rightFrequency : J → ℂ}
    {K r ell : ℕ}
    (hleft : ∀ k ≤ K,
      ∑ i, leftCoefficient i * leftFrequency i ^ k = 0)
    (hright : ∀ k ≤ K,
      ∑ j, rightCoefficient j * rightFrequency j ^ k = 0)
    (hell : ell < 2 * r * (K + 1)) :
    iteratedDeriv ell
      ((finiteComplexExponentialAmplitude leftCoefficient leftFrequency) ^ r *
        (finiteComplexExponentialAmplitude rightCoefficient rightFrequency) ^ r) 0 = 0 := by
  let F := finiteComplexExponentialAmplitude leftCoefficient leftFrequency
  let G := finiteComplexExponentialAmplitude rightCoefficient rightFrequency
  have hF : AnalyticAt ℂ F 0 :=
    finiteComplexExponentialAmplitude_analyticAt leftCoefficient leftFrequency 0
  have hG : AnalyticAt ℂ G 0 :=
    finiteComplexExponentialAmplitude_analyticAt rightCoefficient rightFrequency 0
  have horderF : (K + 1 : ℕ) ≤ analyticOrderAt F 0 :=
    analyticOrderAt_finiteComplexExponentialAmplitude_ge hleft
  have horderG : (K + 1 : ℕ) ≤ analyticOrderAt G 0 :=
    analyticOrderAt_finiteComplexExponentialAmplitude_ge hright
  have horder : (2 * r * (K + 1) : ℕ) ≤
      analyticOrderAt (F ^ r * G ^ r) 0 := by
    rw [analyticOrderAt_mul (hF.pow r) (hG.pow r),
      analyticOrderAt_pow hF, analyticOrderAt_pow hG]
    have hFr := nsmul_le_nsmul_right horderF r
    have hGr := nsmul_le_nsmul_right horderG r
    have hnat : 2 * r * (K + 1) = r * (K + 1) + r * (K + 1) := by
      simp [two_mul, add_mul]
    rw [hnat, Nat.cast_add]
    exact add_le_add hFr hGr
  exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
    ((hF.pow r).mul (hG.pow r))).mp horder ell hell

end GaloisForLFunctions.HTGeometry
