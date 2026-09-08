import GaloisForLFunctions.HTGeometry.FeedForwardFisherRetention
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Reachable projectors for feed-forward Fisher retention

Equations (21), (S85), and (S86) of arXiv:2609.04996 realized as explicit
orthogonal projection matrices. Arbitrary interval lengths and real hopping
amplitudes are allowed, including the zero-hopping limit.
-/

open scoped BigOperators Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry


/-- The normalized field generated on one port interval after removing propagation phases. -/
def feedForwardUnitField (r : ℝ) (n : ℕ) (i : Fin (n + 1)) : ℝ :=
  r ^ i.val / Real.sqrt (feedForwardBuildup r n)

theorem feedForwardUnitField_sq (r : ℝ) (n : ℕ) (i : Fin (n + 1)) :
    feedForwardUnitField r n i ^ 2 = feedForwardRetention r n i := by
  rw [feedForwardUnitField, div_pow, Real.sq_sqrt (feedForwardBuildup_pos r n).le,
    ← pow_mul, Nat.mul_comm i.val 2, pow_mul]
  rfl

theorem sum_sq_feedForwardUnitField (r : ℝ) (n : ℕ) :
    ∑ i, feedForwardUnitField r n i ^ 2 = 1 := by
  simp only [feedForwardUnitField_sq, sum_feedForwardRetention]

/-- Orthogonal rank-one projector onto the field prepared by a single port. -/
def feedForwardProjector (r : ℝ) (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j => feedForwardUnitField r n i * feedForwardUnitField r n j

theorem feedForwardProjector_transpose (r : ℝ) (n : ℕ) :
    (feedForwardProjector r n)ᵀ = feedForwardProjector r n := by
  ext i j
  exact mul_comm _ _

theorem feedForwardProjector_idempotent (r : ℝ) (n : ℕ) :
    feedForwardProjector r n * feedForwardProjector r n = feedForwardProjector r n := by
  ext i j
  simp only [Matrix.mul_apply, feedForwardProjector]
  calc
    (∑ k, (feedForwardUnitField r n i * feedForwardUnitField r n k) *
        (feedForwardUnitField r n k * feedForwardUnitField r n j)) =
      (feedForwardUnitField r n i * feedForwardUnitField r n j) *
        ∑ k, feedForwardUnitField r n k ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by rw [sum_sq_feedForwardUnitField, mul_one]

theorem feedForwardProjector_diag (r : ℝ) (n : ℕ) (i : Fin (n + 1)) :
    feedForwardProjector r n i i = feedForwardRetention r n i := by
  rw [feedForwardProjector, ← sq, feedForwardUnitField_sq]

theorem trace_feedForwardProjector (r : ℝ) (n : ℕ) :
    Matrix.trace (feedForwardProjector r n) = 1 := by
  simp only [Matrix.trace, Matrix.diag, feedForwardProjector_diag, sum_feedForwardRetention]

/-- Projection reads exactly one coefficient of an arbitrary input field. -/
theorem feedForwardProjector_mulVec (r : ℝ) (n : ℕ) (x : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) :
    (feedForwardProjector r n *ᵥ x) i =
      feedForwardUnitField r n i * ∑ j, feedForwardUnitField r n j * x j := by
  simp only [Matrix.mulVec, dotProduct, feedForwardProjector, Finset.mul_sum, mul_assoc]

theorem feedForwardProjector_fixes_unitField (r : ℝ) (n : ℕ) :
    feedForwardProjector r n *ᵥ feedForwardUnitField r n = feedForwardUnitField r n := by
  funext i
  rw [feedForwardProjector_mulVec]
  simp only [← sq, sum_sq_feedForwardUnitField, mul_one]

/-- Cauchy--Schwarz gives the fixed-internal-resource response bound for every input. -/
theorem feedForwardProjector_energy_le (r : ℝ) (n : ℕ) (x : Fin (n + 1) → ℝ) :
    ∑ i, (feedForwardProjector r n *ᵥ x) i ^ 2 ≤ ∑ i, x i ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (feedForwardUnitField r n) x
  rw [sum_sq_feedForwardUnitField, one_mul] at h
  simpa only [feedForwardProjector_mulVec, mul_pow, ← Finset.sum_mul,
    sum_sq_feedForwardUnitField, one_mul] using h

/-- Attainable response intensities for one selected task in the reachable unit ball. -/
def feedForwardSiteResponseSet (r : ℝ) (n : ℕ) (i : Fin (n + 1)) : Set ℝ :=
  {t | ∃ c : ℝ, c ^ 2 ≤ 1 ∧ t = (c * feedForwardUnitField r n i) ^ 2}

/-- The projector diagonal is the attained optimum over the reachable unit ball. -/
theorem feedForwardSiteResponse_isGreatest (r : ℝ) (n : ℕ) (i : Fin (n + 1)) :
    IsGreatest (feedForwardSiteResponseSet r n i) (feedForwardRetention r n i) := by
  constructor
  · refine ⟨1, by simp, ?_⟩
    simp only [one_mul, feedForwardUnitField_sq]
  · rintro t ⟨c, hc, rfl⟩
    rw [mul_pow, feedForwardUnitField_sq]
    exact mul_le_of_le_one_left (feedForwardRetention_nonneg r n i) hc

/-- The reachable projector for disjoint intervals of arbitrary nonzero lengths. -/
def feedForwardIntervalProjector {m : ℕ} (r : Fin m → ℝ) (n : Fin m → ℕ) :
    Matrix (Σ j, Fin (n j + 1)) (Σ j, Fin (n j + 1)) ℝ :=
  Matrix.blockDiagonal' (fun j => feedForwardProjector (r j) (n j))

theorem feedForwardIntervalProjector_idempotent {m : ℕ}
    (r : Fin m → ℝ) (n : Fin m → ℕ) :
    feedForwardIntervalProjector r n * feedForwardIntervalProjector r n =
      feedForwardIntervalProjector r n := by
  rw [feedForwardIntervalProjector, ← Matrix.blockDiagonal'_mul]
  simp only [feedForwardProjector_idempotent]

theorem feedForwardIntervalProjector_transpose {m : ℕ}
    (r : Fin m → ℝ) (n : Fin m → ℕ) :
    (feedForwardIntervalProjector r n)ᵀ = feedForwardIntervalProjector r n := by
  rw [feedForwardIntervalProjector, Matrix.blockDiagonal'_transpose]
  simp only [feedForwardProjector_transpose]

/-- Equation (21) as a matrix trace law, allowing different couplings on each interval. -/
theorem trace_feedForwardIntervalProjector {m : ℕ}
    (r : Fin m → ℝ) (n : Fin m → ℕ) :
    Matrix.trace (feedForwardIntervalProjector r n) = (m : ℝ) := by
  rw [feedForwardIntervalProjector, Matrix.trace_blockDiagonal']
  simp only [trace_feedForwardProjector, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

end GaloisForLFunctions.HTGeometry
