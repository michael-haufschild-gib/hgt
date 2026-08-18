import GaloisForLFunctions.RHTower.Sieve.LadderStepMajorant

/-!
# The annulus majorant from a relative bound on the prime polynomial

Away from zero frequency the twisted prime sum over a ladder step is a small multiple of the step's
right endpoint.  That relative bound — and not a comparison with the number of primes of the step,
which would need a short-interval prime count — is what the annulus contribution consumes, and it
turns the optimal Cauchy--Schwarz weight into an explicit geometric sum.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The explicit annulus majorant of one ladder step. -/
def primeStepMajorant (B₀ : ℕ) (Q η ρ : ℝ) (j : ℕ) : ℝ :=
  ρ * Real.sqrt (5 * Real.pi / 2 + 5 * Real.exp 1 / 2) * ((B₀ : ℝ) + Q * (1 + η) ^ j)

theorem primeStepMajorant_pos {B₀ : ℕ} {Q η ρ : ℝ} (hQ : 0 < Q) (hη : 0 ≤ η) (hρ : 0 < ρ)
    (j : ℕ) : 0 < primeStepMajorant B₀ Q η ρ j := by
  have hbase : (0 : ℝ) < Q * (1 + η) ^ j := by positivity
  have hs : (0 : ℝ) < Real.sqrt (5 * Real.pi / 2 + 5 * Real.exp 1 / 2) :=
    Real.sqrt_pos.2 (by positivity)
  have hB : (0 : ℝ) ≤ (B₀ : ℝ) := Nat.cast_nonneg _
  have : (0 : ℝ) < (B₀ : ℝ) + Q * (1 + η) ^ j := by linarith
  exact mul_pos (mul_pos hρ hs) this

/-- **The annulus majorant dominates the annulus contribution of a step.** -/
theorem primeStepMajorant_sq_ge {B₀ : ℕ} {Q η G ρ : ℝ} (hQ : 0 < Q) (hη : 0 ≤ η)
    (hG0 : 0 ≤ G) (j : ℕ) (hG : G ≤ (B₀ : ℝ) / (Q * (1 + η) ^ j)) {V : ℕ → ℝ} (hV0 : 0 ≤ V j)
    (hVj : V j ≤ ρ * (Q * (1 + η) ^ j)) :
    V j ^ 2 * ladderStepMVT B₀ Q η G j ≤ (primeStepMajorant B₀ Q η ρ j) ^ 2 := by
  have hbase : (0 : ℝ) < Q * (1 + η) ^ j := by positivity
  have hmvt := ladderStepMVT_le_sq (B₀ := B₀) (Q := Q) (η := η) (G := G) hQ hη j hG
  have hmaj0 : (0 : ℝ) ≤ stepMVTMajorant B₀ Q η j := (stepMVTMajorant_pos hQ hη j).le
  have hVsq : V j ^ 2 ≤ (ρ * (Q * (1 + η) ^ j)) ^ 2 := by nlinarith [hVj, hV0]
  have hprod : V j ^ 2 * ladderStepMVT B₀ Q η G j
      ≤ (ρ * (Q * (1 + η) ^ j)) ^ 2 * (stepMVTMajorant B₀ Q η j) ^ 2 := by
    have hT0 : (0 : ℝ) ≤ ladderStepMVT B₀ Q η G j := by
      rw [ladderStepMVT]
      have h1 : (0 : ℝ) ≤ 5 * Real.pi / 2 * G
          + 5 * Real.exp 1 / 2 * ((⌊(B₀ : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ) := by
        have ha : (0 : ℝ) ≤ 5 * Real.pi / 2 * G := mul_nonneg (by positivity) hG0
        have hb : (0 : ℝ) ≤ 5 * Real.exp 1 / 2
            * ((⌊(B₀ : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ) :=
          mul_nonneg (by positivity) (Nat.cast_nonneg _)
        linarith
      have h2 : (0 : ℝ) ≤ (B₀ : ℝ) / (Q * (1 + η) ^ j) + 1 := by
        have : (0 : ℝ) ≤ (B₀ : ℝ) / (Q * (1 + η) ^ j) :=
          div_nonneg (Nat.cast_nonneg _) hbase.le
        linarith
      exact mul_nonneg h1 h2
    exact mul_le_mul hVsq hmvt hT0 (by positivity)
  refine hprod.trans (le_of_eq ?_)
  rw [primeStepMajorant, stepMVTMajorant, ← mul_pow]
  congr 1
  field_simp

/-- The geometric evaluation of the annulus majorant's sum. -/
theorem sum_primeStepMajorant_eq {B₀ : ℕ} {Q η ρ : ℝ} (hη : 0 < η) (L : ℕ) :
    (∑ j ∈ Finset.range L, primeStepMajorant B₀ Q η ρ j)
      = ρ * Real.sqrt (5 * Real.pi / 2 + 5 * Real.exp 1 / 2)
        * ((L : ℝ) * (B₀ : ℝ) + Q * (((1 + η) ^ L - 1) / η)) := by
  have hne : (1 : ℝ) + η ≠ 1 := by linarith
  have hgeom : (∑ j ∈ Finset.range L, ((1 : ℝ) + η) ^ j) = ((1 + η) ^ L - 1) / ((1 + η) - 1) :=
    geom_sum_eq hne L
  have hsimp : ((1 : ℝ) + η) - 1 = η := by ring
  rw [hsimp] at hgeom
  simp only [primeStepMajorant]
  rw [show (∑ j ∈ Finset.range L,
      ρ * Real.sqrt (5 * Real.pi / 2 + 5 * Real.exp 1 / 2) * ((B₀ : ℝ) + Q * (1 + η) ^ j))
      = ρ * Real.sqrt (5 * Real.pi / 2 + 5 * Real.exp 1 / 2)
        * ∑ j ∈ Finset.range L, ((B₀ : ℝ) + Q * (1 + η) ^ j) from by
    rw [Finset.mul_sum]]
  congr 1
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_range, ← Finset.mul_sum,
    hgeom]

end

end RHTower.Sieve
