import GaloisForLFunctions.RHTower.XiPhysicalPrimeLogApertureFusion
import GaloisForLFunctions.RHTower.XiPhysicalPrimeLogApertureHilbertMetric
import GaloisForLFunctions.HTGeometry.LogSquaredTailIntegral

/-!
# Unconditional diagonal budget of the physical prime-log aperture fusion energy

The prime-diagonal contribution `D_diag = ∑_p w_p² κ(p,p)` to the coherent fusion energy is bounded
by the elementary decreasing-tail estimate.  Since each diagonal kernel value satisfies
`0 ≤ κ(p,p) = ℓ_p(1 - ℓ_p/A) ≤ A`, the diagonal energy is at most `A · ∑_p (log p / p)²`, and the
weight-square prime sub-sum is dominated by the natural-number tail
`∑_{n > N₀} (log n/n)² ≤ (log²N₀ + 2 log N₀ + 2)/N₀`.  Hence, when every active prime exceeds a
threshold `N₀ ≥ 3`,
`D_diag ≤ A · (log²N₀ + 2 log N₀ + 2)/N₀`,
placing the entire diagonal contribution inside the allowed error budget.
-/

open Real Filter
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- Each diagonal fusion-kernel value is at most the physical aperture width `A`:
`κ(p,p) = ℓ_p - ℓ_p²/A ≤ ℓ_p ≤ A`. -/
theorem xiPhysicalPrimeLogApertureFusionKernel_diagonal_le
    {A : ℝ} (hA : 0 < A) (m k : ℝ) (p : Nat.Primes) :
    xiPhysicalPrimeLogApertureFusionKernel A m k p p ≤ A := by
  rw [xiPhysicalPrimeLogApertureFusionKernel_diagonal]
  have hL0 : 0 ≤ xiPhysicalPrimeLogApertureLength A m k p :=
    xiPhysicalPrimeLogApertureLength_nonneg A m k p
  have hLA : xiPhysicalPrimeLogApertureLength A m k p ≤ A :=
    xiPhysicalPrimeLogApertureLength_le hA.le m k p
  have hsq : 0 ≤ xiPhysicalPrimeLogApertureLength A m k p ^ (2 : ℕ) / A := by positivity
  linarith

/-- Diagonal-budget inequality: the prime-diagonal fusion energy is at most `A` times the sum of
squared endpoint weights, since `0 ≤ κ(p,p) ≤ A` and `w_p² ≥ 0`. -/
theorem xiPhysicalPrimeLogApertureDiagonalEnergy_le_weightSq_mul
    {A : ℝ} (hA : 0 < A) (m k : ℝ) (P : Finset Nat.Primes) :
    xiPhysicalPrimeLogApertureDiagonalEnergy P A m k ≤
      A * ∑ p ∈ P, physicalPrimeEndpointWeight (p : ℕ) ^ (2 : ℕ) := by
  rw [xiPhysicalPrimeLogApertureDiagonalEnergy, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hkappa := xiPhysicalPrimeLogApertureFusionKernel_diagonal_le hA m k p
  have hw2 : 0 ≤ physicalPrimeEndpointWeight (p : ℕ) ^ (2 : ℕ) := sq_nonneg _
  calc physicalPrimeEndpointWeight (p : ℕ) ^ (2 : ℕ) *
        xiPhysicalPrimeLogApertureFusionKernel A m k p p
      ≤ physicalPrimeEndpointWeight (p : ℕ) ^ (2 : ℕ) * A :=
        mul_le_mul_of_nonneg_left hkappa hw2
    _ = A * physicalPrimeEndpointWeight (p : ℕ) ^ (2 : ℕ) := by ring

/-- `e ≤ N₀` for every natural `N₀ ≥ 3`, since `e < 2.7182818286 < 3`. -/
theorem exp_one_le_of_three_le {N₀ : ℕ} (hN₀ : 3 ≤ N₀) : Real.exp 1 ≤ (N₀ : ℝ) := by
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h2 : (3 : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast hN₀
  linarith

/-- Weight-square prime sub-sum bound: for `N₀ ≥ 3` and a finite set of primes all exceeding `N₀`,
`∑_p (log p / p)² ≤ (log²N₀ + 2 log N₀ + 2)/N₀`.  The primes inject into the shifted tail index, and
`Summable.sum_le_tsum` bounds the finite sub-sum by the tail series controlled by
`tsum_logSq_div_sq_le`. -/
theorem sum_primes_weightSq_le_tail
    {N₀ : ℕ} (hN₀ : 3 ≤ N₀) (P : Finset Nat.Primes)
    (hP : ∀ p ∈ P, N₀ < (p : ℕ)) :
    ∑ p ∈ P, physicalPrimeEndpointWeight (p : ℕ) ^ (2 : ℕ) ≤
      (Real.log (N₀ : ℝ) ^ (2 : ℕ) + 2 * Real.log (N₀ : ℝ) + 2) / (N₀ : ℝ) := by
  set g : ℕ → ℝ := fun i => (Real.log ((N₀ : ℝ) + ((i : ℝ) + 1)) / ((N₀ : ℝ) + ((i : ℝ) + 1))) ^ (2 : ℕ)
    with hg_def
  set φ : Nat.Primes → ℕ := fun p => (p : ℕ) - (N₀ + 1) with hφ_def
  have hgsum : Summable g := by
    have hbase := (summable_nat_add_iff (f := fun n => (Real.log (n : ℝ) / (n : ℝ)) ^ (2 : ℕ))
      (N₀ + 1)).mpr summable_logSq_div_sq
    refine hbase.congr ?_
    intro i
    have : (((i + (N₀ + 1) : ℕ)) : ℝ) = (N₀ : ℝ) + ((i : ℝ) + 1) := by push_cast; ring
    rw [hg_def]
    simp only
    rw [this]
  have hinj : Set.InjOn φ ↑P := by
    intro p hp q hq h
    have hpp := hP p (Finset.mem_coe.mp hp)
    have hqq := hP q (Finset.mem_coe.mp hq)
    have : (p : ℕ) = (q : ℕ) := by rw [hφ_def] at h; simp only at h; omega
    exact Subtype.ext this
  have hpoint : ∀ p ∈ P, physicalPrimeEndpointWeight (p : ℕ) ^ (2 : ℕ) = g (φ p) := by
    intro p hp
    have hp_ge : N₀ + 1 ≤ (p : ℕ) := hP p hp
    have harg : (N₀ : ℝ) + ((((p : ℕ) - (N₀ + 1) : ℕ) : ℝ) + 1) = ((p : ℕ) : ℝ) := by
      rw [Nat.cast_sub hp_ge]; push_cast; ring
    rw [physicalPrimeEndpointWeight, hg_def, hφ_def]
    simp only
    rw [harg]
  calc ∑ p ∈ P, physicalPrimeEndpointWeight (p : ℕ) ^ (2 : ℕ)
      = ∑ p ∈ P, g (φ p) := Finset.sum_congr rfl hpoint
    _ = ∑ i ∈ P.image φ, g i := (Finset.sum_image hinj).symm
    _ ≤ ∑' i, g i := hgsum.sum_le_tsum _ (fun i _ => by rw [hg_def]; exact sq_nonneg _)
    _ ≤ (Real.log (N₀ : ℝ) ^ (2 : ℕ) + 2 * Real.log (N₀ : ℝ) + 2) / (N₀ : ℝ) :=
        tsum_logSq_div_sq_le (exp_one_le_of_three_le hN₀)

/-- Unconditional PFK11 diagonal budget: when every active prime exceeds `N₀ ≥ 3`, the prime-diagonal
fusion energy obeys `D_diag ≤ A · (log²N₀ + 2 log N₀ + 2)/N₀`.  Combines the diagonal-budget
inequality with the weight-square tail bound. -/
theorem xiPhysicalPrimeLogApertureDiagonalEnergy_le_tail
    {A : ℝ} (hA : 0 < A) (m k : ℝ) {N₀ : ℕ} (hN₀ : 3 ≤ N₀)
    (P : Finset Nat.Primes) (hP : ∀ p ∈ P, N₀ < (p : ℕ)) :
    xiPhysicalPrimeLogApertureDiagonalEnergy P A m k ≤
      A * ((Real.log (N₀ : ℝ) ^ (2 : ℕ) + 2 * Real.log (N₀ : ℝ) + 2) / (N₀ : ℝ)) := by
  calc xiPhysicalPrimeLogApertureDiagonalEnergy P A m k
      ≤ A * ∑ p ∈ P, physicalPrimeEndpointWeight (p : ℕ) ^ (2 : ℕ) :=
        xiPhysicalPrimeLogApertureDiagonalEnergy_le_weightSq_mul hA m k P
    _ ≤ A * ((Real.log (N₀ : ℝ) ^ (2 : ℕ) + 2 * Real.log (N₀ : ℝ) + 2) / (N₀ : ℝ)) :=
        mul_le_mul_of_nonneg_left (sum_primes_weightSq_le_tail hN₀ P hP) hA.le

/-- Explicit `(PFK10)`+`(PFK11)` lower bound on the off-diagonal cross defect: the automatic bound
`C_cross ≥ -D_diag` becomes quantitative, `C_cross ≥ -A·(log²N₀ + 2 log N₀ + 2)/N₀`, whenever every
active prime exceeds `N₀ ≥ 3`.  Chains the Hilbert-norm lower bound
`neg_xiPhysicalPrimeLogApertureDiagonalEnergy_le_crossDefect` with the diagonal budget. -/
theorem xiPhysicalPrimeLogApertureCrossDefect_ge_neg_tail
    {A : ℝ} (hA : 0 < A) (m k : ℝ) {N₀ : ℕ} (hN₀ : 3 ≤ N₀)
    (P : Finset Nat.Primes) (hP : ∀ p ∈ P, N₀ < (p : ℕ)) :
    -(A * ((Real.log (N₀ : ℝ) ^ (2 : ℕ) + 2 * Real.log (N₀ : ℝ) + 2) / (N₀ : ℝ))) ≤
      xiPhysicalPrimeLogApertureCrossDefect P A m k := by
  have h1 := neg_xiPhysicalPrimeLogApertureDiagonalEnergy_le_crossDefect P hA m k
  have h2 := xiPhysicalPrimeLogApertureDiagonalEnergy_le_tail hA m k hN₀ P hP
  linarith

/-- Each centered aperture carrier has norm at most `√A`, since `‖φ_p‖² = κ(p,p) ≤ A`. -/
theorem norm_centeredCarrier_le {A : ℝ} (hA : 0 < A) (m k : ℝ) (p : Nat.Primes) :
    ‖xiPhysicalPrimeLogCenteredApertureCarrier A m k p‖ ≤ Real.sqrt A := by
  have hsq : ‖xiPhysicalPrimeLogCenteredApertureCarrier A m k p‖ ^ (2 : ℕ) ≤ A := by
    rw [← real_inner_self_eq_norm_sq, real_inner_xiPhysicalPrimeLogCenteredApertureCarrier hA]
    exact xiPhysicalPrimeLogApertureFusionKernel_diagonal_le hA m k p
  rw [← Real.sqrt_sq (norm_nonneg _)]
  exact Real.sqrt_le_sqrt hsq

/-- **`(PFK16)` Hilbert norm mechanism.**  The aggregate carrier norm is controlled by the weight
sum: `‖∑_p w_p φ_p‖ ≤ √A · ∑_p w_p`, by the triangle inequality and `‖φ_p‖ ≤ √A`.  Instantiated on the
prime-power completion weights (summing to the `(PFK14)` tail) this is the critical-norm stability. -/
theorem norm_aggregateCarrier_le {A : ℝ} (hA : 0 < A) (m k : ℝ) (P : Finset Nat.Primes) :
    ‖xiPhysicalPrimeLogAggregateApertureCarrier P A m k‖
      ≤ Real.sqrt A * ∑ p ∈ P, physicalPrimeEndpointWeight (p : ℕ) := by
  rw [xiPhysicalPrimeLogAggregateApertureCarrier]
  calc ‖∑ p ∈ P, physicalPrimeEndpointWeight (p : ℕ) •
          xiPhysicalPrimeLogCenteredApertureCarrier A m k p‖
      ≤ ∑ p ∈ P, ‖physicalPrimeEndpointWeight (p : ℕ) •
          xiPhysicalPrimeLogCenteredApertureCarrier A m k p‖ := norm_sum_le _ _
    _ = ∑ p ∈ P, physicalPrimeEndpointWeight (p : ℕ) *
          ‖xiPhysicalPrimeLogCenteredApertureCarrier A m k p‖ := by
        apply Finset.sum_congr rfl; intro p _
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (physicalPrimeEndpointWeight_pos p).le]
    _ ≤ ∑ p ∈ P, physicalPrimeEndpointWeight (p : ℕ) * Real.sqrt A := by
        apply Finset.sum_le_sum; intro p _
        exact mul_le_mul_of_nonneg_left (norm_centeredCarrier_le hA m k p)
          (physicalPrimeEndpointWeight_pos p).le
    _ = Real.sqrt A * ∑ p ∈ P, physicalPrimeEndpointWeight (p : ℕ) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring

end RHTower
