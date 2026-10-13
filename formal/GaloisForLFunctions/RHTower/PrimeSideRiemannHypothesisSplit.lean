import GaloisForLFunctions.RHTower.ZerosApproachLineLowerSideLag
import GaloisForLFunctions.RHTower.GaussianCentralGapLargeHeightFiniteOffLine

/-!
# RH as two prime-side statements: a height-local growth bound and one sampled one-sided bound

* The Gaussian-filtered central prime gap `F(ε, τ)` (`gaussianFilteredCentralGap`) is a
  Gaussian-weighted sum over prime powers.  It grows slower than every exponential `e^{sε}` at all
  large heights iff the zeros approach the critical line
  (`eventualFilteredCentralGapSubexponential_iff_zerosApproachLine`).
* The lag values `Φ(m log b)` along one geometric progression are smoothed Chebyshev errors at
  `x = b^m`.  Their upper boundedness plus zeros approaching the line is RH
  (`riemannHypothesis_iff_zerosApproachLine_and_pow_integerLag_bddAbove`).

**Theorem** (`riemannHypothesis_iff_filteredCentralGapSubexponential_and_pow_integerLag_bddAbove`).
For every base `b ≥ 2`, RH holds iff the filtered central prime gap grows subexponentially at all
large heights and the lag values `Φ(m log b)` are bounded above.  The lower-side version holds with
lower lag bounds along `p^m` for all `p` in an infinite set of primes
(`riemannHypothesis_iff_filteredCentralGapSubexponential_and_primePow_integerLag_bddBelow`).

**Three pillars** (`riemannHypothesis_iff_lindelof_and_cosine_finite_and_pow_integerLag_bddAbove`).
RH holds iff the Lindelöf hypothesis holds, every cosine level `cos(hD)Ξ`, `h > 0`, has only
finitely many non-real zeros, and the lags `Φ(m log b)` are bounded above: an analytic growth
statement, a deformation statement and a sampled arithmetic statement.

So RH splits into two statements about prime powers alone: a height-local asymptotic growth bound,
which sees only the limit superior of `Re ρ − ½`, and a one-sided bound sampled along a single
geometric progression, which excludes an attained top level.
-/

namespace RHTower

open BacklundConverse

/-- **RH as a height-local prime growth bound and one sampled one-sided prime bound.** -/
theorem riemannHypothesis_iff_filteredCentralGapSubexponential_and_pow_integerLag_bddAbove
    {b : ℕ} (hb : 2 ≤ b) :
    RiemannHypothesis ↔ EventualFilteredCentralGapSubexponential ∧
      ∃ M : ℝ, ∀ m : ℕ, integerLag (b ^ m) ≤ M := by
  rw [eventualFilteredCentralGapSubexponential_iff_zerosApproachLine]
  exact riemannHypothesis_iff_zerosApproachLine_and_pow_integerLag_bddAbove hb

/-- **The lower-side version, along infinitely many prime bases.** -/
theorem riemannHypothesis_iff_filteredCentralGapSubexponential_and_primePow_integerLag_bddBelow
    {P : Set ℕ} (hP : P.Infinite) (hPp : ∀ p ∈ P, p.Prime) :
    RiemannHypothesis ↔ EventualFilteredCentralGapSubexponential ∧
      ∀ p ∈ P, ∃ M : ℝ, ∀ m : ℕ, 1 ≤ m → M ≤ integerLag (p ^ m) := by
  rw [eventualFilteredCentralGapSubexponential_iff_zerosApproachLine]
  exact riemannHypothesis_iff_zerosApproachLine_and_primePow_integerLag_bddBelow hP hPp

/-- **RH as Lindelöf, cosine finiteness and one sampled one-sided prime bound.** -/
theorem riemannHypothesis_iff_lindelof_and_cosine_finite_and_pow_integerLag_bddAbove {b : ℕ}
    (hb : 2 ≤ b) :
    RiemannHypothesis ↔ LindelofSparse.LindelofCriticalLine ∧
      (∀ h : ℝ, 0 < h → {z : ℂ | CosineDefectBudget.cosShiftXi h z = 0 ∧ z.im ≠ 0}.Finite) ∧
      ∃ M : ℝ, ∀ m : ℕ, integerLag (b ^ m) ≤ M := by
  rw [riemannHypothesis_iff_zerosApproachLine_and_pow_integerLag_bddAbove hb,
    zerosApproachLine_iff_lindelof_and_cosShiftXi_finite_nonreal, and_assoc]


end RHTower
