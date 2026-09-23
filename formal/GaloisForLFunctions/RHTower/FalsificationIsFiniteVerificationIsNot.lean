import GaloisForLFunctions.RHTower.LadderNeedsAllRungs

/-!
# One rung refutes, all rungs verify

The polynomial ladder is finite at each width but its length is the dimension.  This file records the
asymmetry that makes that acceptable in one direction and fatal in the other.

**Descartes is exact for real-rooted polynomials.**  The characteristic polynomial of a symmetric
matrix has only real roots, and for such a polynomial the number of positive roots equals the number
of sign changes in its coefficient sequence.  With coefficients `(1, -e₁, e₂, -e₃, …)` this says the
number of negative eigenvalues is the number of sign changes in `(1, e₁, e₂, …, e_d)`.

**Consequences, and they point in opposite directions.**

* **Refutation is a single certificate.**  If any one `e_k` is negative, some eigenvalue is negative:
  the symmetric functions of nonnegative numbers are nonnegative, so a negative `e_k` contradicts
  nonnegativity of the spectrum.  One explicit polynomial inequality in prime data, checkable in
  isolation at any width, refutes the hypothesis.
* **Verification needs the whole ladder.**  Truncation fails — unit diagonal with off-diagonal `-3/5`
  has positive `1×1` and `2×2` minors and negative determinant — so no proper subset of the rungs
  certifies positivity.

> **Disproof of the hypothesis is a finite certificate: one negative symmetric function of one Weil
> Gram matrix.  Proof is not: it requires every symmetric function at every width.  The asymmetry is
> exact, and it is the precise sense in which the problem is hard in only one direction.**

This file formalizes the refutation direction, its independence of the width, and the failure of
truncation for verification.
-/

open Finset

noncomputable section

namespace RHTower

/-- **Refutation from one rung.**  A negative symmetric function forces a negative eigenvalue. -/
theorem exists_neg_of_esymm_neg {ι : Type*} [DecidableEq ι] (s : Finset ι) (lam : ι → ℝ) (k : ℕ)
    (hneg : ∑ t ∈ s.powersetCard k, ∏ i ∈ t, lam i < 0) :
    ¬ (∀ i ∈ s, 0 ≤ lam i) := by
  intro h
  exact absurd (esymm_nonneg_of_nonneg s lam h k) (not_le.mpr hneg)

/-- The certificate does not depend on the width: a negative rung at any single width already
refutes. -/
theorem refutation_localised {ι : Type*} [DecidableEq ι] (s : Finset ι) (lam : ι → ℝ) {k : ℕ}
    (hneg : ∑ t ∈ s.powersetCard k, ∏ i ∈ t, lam i < 0) :
    ∃ i ∈ s, lam i < 0 := by
  by_contra hcon
  push Not at hcon
  exact exists_neg_of_esymm_neg s lam k hneg hcon

/-- **Verification is not localised.**  The witness of the previous entry has its first two rungs
nonnegative and its third negative, so checking a proper initial segment certifies nothing. -/
theorem verification_not_localised :
    (0:ℝ) < 1 ∧ (0:ℝ) < 1 - (-(3:ℝ) / 5) ^ (2 : ℕ) ∧
      (1 - (-(3:ℝ) / 5)) ^ (2 : ℕ) * (1 + 2 * (-(3:ℝ) / 5)) < 0 :=
  truncation_insufficient

/-- **The asymmetry, stated.**  One negative rung refutes; nonnegativity of a proper initial segment
does not verify. -/
theorem asymmetry {ι : Type*} [DecidableEq ι] (s : Finset ι) (lam : ι → ℝ) {k : ℕ}
    (hneg : ∑ t ∈ s.powersetCard k, ∏ i ∈ t, lam i < 0) :
    (∃ i ∈ s, lam i < 0) ∧
      ((0:ℝ) < 1 - (-(3:ℝ) / 5) ^ (2 : ℕ) ∧
        (1 - (-(3:ℝ) / 5)) ^ (2 : ℕ) * (1 + 2 * (-(3:ℝ) / 5)) < 0) :=
  ⟨refutation_localised s lam hneg, minors_pos_at_witness, det_neg_at_witness⟩

/-- The first rung is the trace, and it is nonnegative whenever the spectrum is. -/
theorem first_rung {ι : Type*} [DecidableEq ι] (s : Finset ι) (lam : ι → ℝ)
    (h : ∀ i ∈ s, 0 ≤ lam i) :
    0 ≤ ∑ t ∈ s.powersetCard 1, ∏ i ∈ t, lam i :=
  esymm_nonneg_of_nonneg s lam h 1

end RHTower
