import GaloisForLFunctions.HTGeometry.LongRangeNonHermitianSpectra
import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# SSH bands and exact half-line edge states

The effective dimerized hopping structure of arXiv:2503.11928 has a two-band
Bloch factor and a geometric half-line zero mode. The latter is realized as an
actual square-summable vector. Its finite truncation exposes the far-edge residual.
-/

open scoped BigOperators Matrix
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- Off-diagonal Bloch entry of a dimerized chain. -/
def coppoSSHOffDiagonal (u v theta : ℝ) : ℂ := u + v * unitBlochFactor theta

/-- The Hermitian two-sublattice Bloch matrix. -/
def coppoSSHBloch (u v theta : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of ![![0, coppoSSHOffDiagonal u v theta], ![star (coppoSSHOffDiagonal u v theta), 0]]

/-- The Bloch gap polynomial, before taking the square root. -/
def coppoSSHGapSq (u v theta : ℝ) : ℝ := u ^ 2 + v ^ 2 + 2 * u * v * Real.cos theta

theorem coppoSSHOffDiagonal_re (u v theta : ℝ) :
    (coppoSSHOffDiagonal u v theta).re = u + v * Real.cos theta := by
  simp [coppoSSHOffDiagonal, unitBlochFactor, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem coppoSSHOffDiagonal_im (u v theta : ℝ) :
    (coppoSSHOffDiagonal u v theta).im = v * Real.sin theta := by
  simp [coppoSSHOffDiagonal, unitBlochFactor, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- The band polynomial is the exact squared norm of the hopping symbol. -/
theorem coppoSSHOffDiagonal_normSq (u v theta : ℝ) :
    Complex.normSq (coppoSSHOffDiagonal u v theta) = coppoSSHGapSq u v theta := by
  rw [Complex.normSq_apply, coppoSSHOffDiagonal_re, coppoSSHOffDiagonal_im]
  have hs := Real.sin_sq_add_cos_sq theta
  dsimp [coppoSSHGapSq]
  nlinarith [mul_nonneg (sq_nonneg v) (sq_nonneg (Real.sin theta))]

/-- The Bloch matrix squares to the scalar band polynomial. -/
theorem coppoSSHBloch_sq (u v theta : ℝ) :
    coppoSSHBloch u v theta ^ 2 = (coppoSSHGapSq u v theta : ℂ) • 1 := by
  have hz : coppoSSHOffDiagonal u v theta * star (coppoSSHOffDiagonal u v theta) =
      (coppoSSHGapSq u v theta : ℂ) := by
    change coppoSSHOffDiagonal u v theta * (starRingEnd ℂ) (coppoSSHOffDiagonal u v theta) = _
    rw [Complex.mul_conj, coppoSSHOffDiagonal_normSq]
  change coppoSSHOffDiagonal u v theta * (starRingEnd ℂ) (coppoSSHOffDiagonal u v theta) = _ at hz
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coppoSSHBloch, pow_two, Matrix.mul_apply, Fin.sum_univ_two, hz, mul_comm]

/-- The squared Bloch bands have their exact zone-boundary gap. -/
theorem coppoSSHGapSq_sub_boundary (u v theta : ℝ) :
    coppoSSHGapSq u v theta - (u - v) ^ 2 = 2 * u * v * (1 + Real.cos theta) := by
  dsimp [coppoSSHGapSq]; ring

/-- Positive hopping has a global squared-band lower bound. -/
theorem coppoSSHGapSq_lower_bound (a b theta : ℝ) :
    (Real.exp a - Real.exp b) ^ 2 ≤ coppoSSHGapSq (Real.exp a) (Real.exp b) theta := by
  have h := coppoSSHGapSq_sub_boundary (Real.exp a) (Real.exp b) theta
  have hc : 0 ≤ 1 + Real.cos theta := by linarith [Real.neg_one_le_cos theta]
  have hp : 0 ≤ 2 * Real.exp a * Real.exp b * (1 + Real.cos theta) := by positivity
  linarith

/-- The paper's nested-root radicand is exactly a normalized SSH band polynomial. -/
theorem coppoSSHGapSq_paper_radical (delta theta : ℝ) :
    coppoSSHGapSq ((1 - delta) / 2) ((1 + delta) / 2) theta =
      (1 + delta ^ 2) / 2 + (1 - delta ^ 2) / 2 * Real.cos theta := by
  dsimp [coppoSSHGapSq]; ring

/-- At the zone boundary the normalized squared gap is precisely the dimerization square. -/
theorem coppoSSHGapSq_paper_boundary (delta : ℝ) :
    coppoSSHGapSq ((1 - delta) / 2) ((1 + delta) / 2) Real.pi = delta ^ 2 := by
  simp [coppoSSHGapSq, Real.cos_pi]
  ring

/-- The paper's normalized radicand is nonnegative for every real dimerization. -/
theorem coppoSSHGapSq_paper_nonneg (delta theta : ℝ) :
    0 ≤ (1 + delta ^ 2) / 2 + (1 - delta ^ 2) / 2 * Real.cos theta := by
  rw [← coppoSSHGapSq_paper_radical, ← coppoSSHOffDiagonal_normSq]
  exact Complex.normSq_nonneg _

/-- A premise-free family covering positive hopping ratios strictly below one. -/
def coppoSSHRatio (a : ℝ) : ℝ := Real.exp (-Real.exp a)

theorem coppoSSHRatio_pos (a : ℝ) : 0 < coppoSSHRatio a := Real.exp_pos _

theorem coppoSSHRatio_lt_one (a : ℝ) : coppoSSHRatio a < 1 := by
  rw [coppoSSHRatio, Real.exp_lt_one_iff]
  exact neg_neg_of_pos (Real.exp_pos a)

/-- The unnormalized half-line edge profile occupies one sublattice. -/
def coppoSSHEdgeProfile (a : ℝ) (n : ℕ) : ℝ := (-coppoSSHRatio a) ^ n

/-- The boundary profile is nonzero at the exposed site. -/
theorem coppoSSHEdgeProfile_zero (a : ℝ) : coppoSSHEdgeProfile a 0 = 1 := by
  simp [coppoSSHEdgeProfile]

/-- The profile satisfies the zero-energy dimer recurrence at every site. -/
theorem coppoSSHEdgeProfile_recurrence (a : ℝ) (n : ℕ) :
    coppoSSHRatio a * coppoSSHEdgeProfile a n + coppoSSHEdgeProfile a (n + 1) = 0 := by
  dsimp [coppoSSHEdgeProfile]
  rw [pow_succ]
  ring

/-- The exact edge profile is square summable. -/
theorem coppoSSHEdgeProfile_square_summable (a : ℝ) :
    Summable (fun n => coppoSSHEdgeProfile a n ^ 2) := by
  have hq : coppoSSHRatio a ^ 2 < 1 := by
    nlinarith [coppoSSHRatio_pos a, coppoSSHRatio_lt_one a]
  have h := summable_geometric_of_lt_one (sq_nonneg (coppoSSHRatio a)) hq
  have heq (n : ℕ) : coppoSSHEdgeProfile a n ^ 2 = (coppoSSHRatio a ^ 2) ^ n := by
    dsimp [coppoSSHEdgeProfile]
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul, neg_sq]
  simp_rw [heq]
  exact h

/-- The profile lies in the actual Hilbert sequence carrier. -/
theorem coppoSSHEdgeProfile_memlp (a : ℝ) : Memℓp (coppoSSHEdgeProfile a) 2 := by
  apply memℓp_gen
  simpa using coppoSSHEdgeProfile_square_summable a

/-- The constructed edge vector in `ℓ²`. -/
def coppoSSHEdgeVector (a : ℝ) : lp (fun _ : ℕ => ℝ) 2 :=
  ⟨coppoSSHEdgeProfile a, coppoSSHEdgeProfile_memlp a⟩

/-- The Hilbert-space edge vector is nonzero. -/
theorem coppoSSHEdgeVector_ne_zero (a : ℝ) : coppoSSHEdgeVector a ≠ 0 := by
  intro h
  have hz := congrArg (fun f : lp (fun _ : ℕ => ℝ) 2 => f 0) h
  change coppoSSHEdgeProfile a 0 = 0 at hz
  rw [coppoSSHEdgeProfile_zero] at hz
  exact one_ne_zero hz

/-- Truncating after `N+1` cells leaves exactly a far-boundary residual. -/
theorem coppoSSHEdgeProfile_terminal_residual (a : ℝ) (N : ℕ) :
    coppoSSHRatio a * coppoSSHEdgeProfile a N = -coppoSSHEdgeProfile a (N + 1) := by
  linarith [coppoSSHEdgeProfile_recurrence a N]

/-- The existing strict long-range hopping family is an SSH edge-decay subfamily. -/
theorem coppoSSHRatio_longRange (a : ℝ) :
    coppoSSHRatio (Real.log (|a| + 1)) = strictLongRangeRatio a := by
  rw [coppoSSHRatio, Real.exp_log (by positivity)]
  rfl

end GaloisForLFunctions.HTGeometry
