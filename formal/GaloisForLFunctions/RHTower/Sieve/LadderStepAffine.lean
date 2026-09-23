import GaloisForLFunctions.RHTower.Sieve.LadderPrimeMajorant

/-!
# The ladder step majorant at an arbitrary height

Gallagher's dyadic tail consumes an affine majorant for the mean square at *every* height above the
cut, so the ladder's step estimate has to be available at every height, not only below `B₀/Q_j`.
Splitting the mean value factor into its height part and its diagonal part and using
`a² + b² ≤ (a+b)²` keeps the majorant a product, hence the Cauchy--Schwarz weight explicit, and makes
the resulting bound affine in the height.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The step majorant at height `T`. -/
def stepAffineMajorant (B₀ : ℕ) (Q η ρ T : ℝ) (j : ℕ) : ℝ :=
  ρ * (Q * (1 + η) ^ j)
    * (Real.sqrt (5 * Real.pi / 2 * T * ((B₀ : ℝ) / (Q * (1 + η) ^ j) + 1))
      + Real.sqrt (5 * Real.exp 1 / 2 * ((B₀ : ℝ) / (Q * (1 + η) ^ j))
          * ((B₀ : ℝ) / (Q * (1 + η) ^ j) + 1)))

theorem stepAffineMajorant_pos {B₀ : ℕ} {Q η ρ T : ℝ} (hQ : 0 < Q) (hη : 0 ≤ η) (hρ : 0 < ρ)
    (hB : 0 < (B₀ : ℝ)) (j : ℕ) : 0 < stepAffineMajorant B₀ Q η ρ T j := by
  have hbase : (0 : ℝ) < Q * (1 + η) ^ j := by positivity
  have hN : (0 : ℝ) < (B₀ : ℝ) / (Q * (1 + η) ^ j) := by positivity
  have hs1 : (0 : ℝ) ≤ Real.sqrt (5 * Real.pi / 2 * T * ((B₀ : ℝ) / (Q * (1 + η) ^ j) + 1)) :=
    Real.sqrt_nonneg _
  have hs2 : (0 : ℝ) < Real.sqrt (5 * Real.exp 1 / 2 * ((B₀ : ℝ) / (Q * (1 + η) ^ j))
      * ((B₀ : ℝ) / (Q * (1 + η) ^ j) + 1)) := by
    refine Real.sqrt_pos.2 ?_
    positivity
  rw [stepAffineMajorant]
  have : (0 : ℝ) < ρ * (Q * (1 + η) ^ j) := mul_pos hρ hbase
  nlinarith [hs1, hs2, this]

/-- **The step majorant dominates the step at every height.** -/
theorem stepAffineMajorant_sq_ge {B₀ : ℕ} {Q η ρ T : ℝ} (hQ : 0 < Q) (hη : 0 ≤ η) (hρ : 0 ≤ ρ)
    (hT : 0 ≤ T) (j : ℕ) {V : ℕ → ℝ} (hV0 : 0 ≤ V j) (hVj : V j ≤ ρ * (Q * (1 + η) ^ j)) :
    V j ^ (2 : ℕ) * ladderStepMVT B₀ Q η T j ≤ (stepAffineMajorant B₀ Q η ρ T j) ^ (2 : ℕ) := by
  have hbase : (0 : ℝ) < Q * (1 + η) ^ j := by positivity
  set N : ℝ := (B₀ : ℝ) / (Q * (1 + η) ^ j) with hN
  have hN0 : (0 : ℝ) ≤ N := div_nonneg (Nat.cast_nonneg _) hbase.le
  have hfl : ((⌊N⌋₊ : ℕ) : ℝ) ≤ N := Nat.floor_le hN0
  set a : ℝ := Real.sqrt (5 * Real.pi / 2 * T * (N + 1)) with ha
  set b : ℝ := Real.sqrt (5 * Real.exp 1 / 2 * N * (N + 1)) with hb
  have ha0 : (0 : ℝ) ≤ a := Real.sqrt_nonneg _
  have hb0 : (0 : ℝ) ≤ b := Real.sqrt_nonneg _
  have hasq : a ^ (2 : ℕ) = 5 * Real.pi / 2 * T * (N + 1) := by
    rw [ha, Real.sq_sqrt (by positivity)]
  have hbsq : b ^ (2 : ℕ) = 5 * Real.exp 1 / 2 * N * (N + 1) := by
    rw [hb, Real.sq_sqrt (by positivity)]
  have hmvt : ladderStepMVT B₀ Q η T j ≤ a ^ (2 : ℕ) + b ^ (2 : ℕ) := by
    rw [ladderStepMVT, ← hN, hasq, hbsq]
    have hstep : 5 * Real.pi / 2 * T + 5 * Real.exp 1 / 2 * ((⌊N⌋₊ : ℕ) : ℝ)
        ≤ 5 * Real.pi / 2 * T + 5 * Real.exp 1 / 2 * N := by
      have := mul_le_mul_of_nonneg_left hfl (by positivity : (0:ℝ) ≤ 5 * Real.exp 1 / 2)
      linarith
    have hN1 : (0 : ℝ) ≤ N + 1 := by linarith
    nlinarith [hstep, hN1]
  have hmvt0 : (0 : ℝ) ≤ ladderStepMVT B₀ Q η T j := by
    rw [ladderStepMVT, ← hN]
    have h1 : (0 : ℝ) ≤ 5 * Real.pi / 2 * T
        + 5 * Real.exp 1 / 2 * ((⌊N⌋₊ : ℕ) : ℝ) := by positivity
    have h2 : (0 : ℝ) ≤ N + 1 := by linarith
    exact mul_nonneg h1 h2
  have hVsq : V j ^ (2 : ℕ) ≤ (ρ * (Q * (1 + η) ^ j)) ^ (2 : ℕ) := by nlinarith [hVj, hV0]
  have hsum : a ^ (2 : ℕ) + b ^ (2 : ℕ) ≤ (a + b) ^ (2 : ℕ) := by nlinarith [ha0, hb0]
  have hchain : V j ^ (2 : ℕ) * ladderStepMVT B₀ Q η T j
      ≤ (ρ * (Q * (1 + η) ^ j)) ^ (2 : ℕ) * (a + b) ^ (2 : ℕ) :=
    mul_le_mul hVsq (le_trans hmvt hsum) hmvt0 (by positivity)
  refine hchain.trans (le_of_eq ?_)
  rw [stepAffineMajorant, ← hN, ← ha, ← hb, mul_pow]
  ring

/-- **The single sum of the step majorants is affine in the height.** -/
theorem sum_stepAffineMajorant_sq_le {B₀ : ℕ} {Q η ρ T : ℝ} (hQ : 0 < Q) (hη : 0 ≤ η)
    (hT : 0 ≤ T) (L : ℕ) :
    (∑ j ∈ Finset.range L, stepAffineMajorant B₀ Q η ρ T j) ^ (2 : ℕ)
      ≤ 2 * (5 * Real.pi / 2 * T) * ρ ^ (2 : ℕ)
          * (∑ j ∈ Finset.range L, (Q * (1 + η) ^ j)
              * Real.sqrt ((B₀ : ℝ) / (Q * (1 + η) ^ j) + 1)) ^ (2 : ℕ)
        + 2 * (5 * Real.exp 1 / 2) * ρ ^ (2 : ℕ)
          * (∑ j ∈ Finset.range L, (Q * (1 + η) ^ j)
              * Real.sqrt (((B₀ : ℝ) / (Q * (1 + η) ^ j))
                  * ((B₀ : ℝ) / (Q * (1 + η) ^ j) + 1))) ^ (2 : ℕ) := by
  classical
  set S₁ : ℝ := ∑ j ∈ Finset.range L, (Q * (1 + η) ^ j)
      * Real.sqrt ((B₀ : ℝ) / (Q * (1 + η) ^ j) + 1) with hS₁
  set S₂ : ℝ := ∑ j ∈ Finset.range L, (Q * (1 + η) ^ j)
      * Real.sqrt (((B₀ : ℝ) / (Q * (1 + η) ^ j)) * ((B₀ : ℝ) / (Q * (1 + η) ^ j) + 1))
    with hS₂
  have hsplit : (∑ j ∈ Finset.range L, stepAffineMajorant B₀ Q η ρ T j)
      = ρ * Real.sqrt (5 * Real.pi / 2 * T) * S₁ + ρ * Real.sqrt (5 * Real.exp 1 / 2) * S₂ := by
    rw [hS₁, hS₂, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hbase : (0 : ℝ) < Q * (1 + η) ^ j := by positivity
    have hN0 : (0 : ℝ) ≤ (B₀ : ℝ) / (Q * (1 + η) ^ j) := div_nonneg (Nat.cast_nonneg _) hbase.le
    have h1 : Real.sqrt (5 * Real.pi / 2 * T * ((B₀ : ℝ) / (Q * (1 + η) ^ j) + 1))
        = Real.sqrt (5 * Real.pi / 2 * T) * Real.sqrt ((B₀ : ℝ) / (Q * (1 + η) ^ j) + 1) :=
      Real.sqrt_mul (by positivity) _
    have h2 : Real.sqrt (5 * Real.exp 1 / 2 * ((B₀ : ℝ) / (Q * (1 + η) ^ j))
          * ((B₀ : ℝ) / (Q * (1 + η) ^ j) + 1))
        = Real.sqrt (5 * Real.exp 1 / 2)
          * Real.sqrt (((B₀ : ℝ) / (Q * (1 + η) ^ j))
              * ((B₀ : ℝ) / (Q * (1 + η) ^ j) + 1)) := by
      rw [mul_assoc, Real.sqrt_mul (by positivity)]
    rw [stepAffineMajorant, h1, h2]
    ring
  rw [hsplit]
  have hsq1 : (ρ * Real.sqrt (5 * Real.pi / 2 * T)) ^ (2 : ℕ) = ρ ^ (2 : ℕ) * (5 * Real.pi / 2 * T) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hsq2 : (ρ * Real.sqrt (5 * Real.exp 1 / 2)) ^ (2 : ℕ) = ρ ^ (2 : ℕ) * (5 * Real.exp 1 / 2) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  nlinarith [sq_nonneg (ρ * Real.sqrt (5 * Real.pi / 2 * T) * S₁
      - ρ * Real.sqrt (5 * Real.exp 1 / 2) * S₂), hsq1, hsq2, sq_nonneg S₁, sq_nonneg S₂]

end

end RHTower.Sieve
