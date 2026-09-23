import GaloisForLFunctions.RHTower.RouteEDegreeNormalizedGibbsBoundaryVariation
import GaloisForLFunctions.RHTower.Sieve.MoebiusSignCount

/-!
# Sign-complete physical degree decomposition

Join every finite-shell endpoint carrying the opposite nonzero Möbius sign.  This gives a symmetric
sign-reversing physical incidence.  Its row degree has an exact decomposition into squarefree shell
mass and the shell Möbius sum.  Consequently ordinary degree variance is bounded pointwise by the
squarefree-density variance plus Möbius shell energy, the two arithmetic inputs naturally exposed
by short-interval theory.

This file proves only finite identities.  It assumes no short-interval estimate, degree lower
bound, column-load estimate, Möbius cancellation estimate, or RH premise.
-/

namespace RHTower

open scoped BigOperators ArithmeticFunction.Moebius
open Finset ArithmeticFunction

noncomputable section

/-- Möbius sum on a finite source-declared physical shell. -/
def routeEMoebiusShellSum
    (S : Finset ℕ) (shell : ℕ → ℕ → Prop) (n : ℕ) : ℝ := by
  classical
  exact ∑ q ∈ S, if shell n q then ((μ q : ℤ) : ℝ) else 0

/-- Squarefree mass on the same shell, written as `μ²`. -/
def routeESquarefreeShellMass
    (S : Finset ℕ) (shell : ℕ → ℕ → Prop) (n : ℕ) : ℝ := by
  classical
  exact ∑ q ∈ S, if shell n q then ((μ q : ℤ) : ℝ) ^ (2 : ℕ) else 0

/-- Number of shell endpoints whose nonzero Möbius sign is opposite to the source sign. -/
def routeEOppositeSignShellMass
    (S : Finset ℕ) (shell : ℕ → ℕ → Prop) (n : ℕ) : ℝ := by
  classical
  exact ∑ q ∈ S, if shell n q ∧ μ q = -(μ n) then 1 else 0

private theorem two_mul_oppositeSignIndicator_eq
    {n q : ℕ} (hn : μ n = 1 ∨ μ n = -1) :
    2 * (if μ q = -(μ n) then (1 : ℝ) else 0) =
      ((μ q : ℤ) : ℝ) ^ (2 : ℕ) - ((μ n : ℤ) : ℝ) * ((μ q : ℤ) : ℝ) := by
  rcases RHTower.Sieve.moebius_trichotomy q with hq | hq | hq <;>
    rcases hn with hn | hn <;> simp [hq, hn] <;> norm_num

/-- Exact local sign split: twice opposite-sign row mass equals squarefree shell mass minus source
sign times the shell Möbius sum. -/
theorem routeE_two_mul_oppositeSignShellMass_eq
    (S : Finset ℕ) (shell : ℕ → ℕ → Prop) {n : ℕ}
    (hn : μ n = 1 ∨ μ n = -1) :
    2 * routeEOppositeSignShellMass S shell n =
      routeESquarefreeShellMass S shell n -
        ((μ n : ℤ) : ℝ) * routeEMoebiusShellSum S shell n := by
  unfold routeEOppositeSignShellMass routeESquarefreeShellMass routeEMoebiusShellSum
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q _hq
  by_cases hs : shell n q
  · simp only [hs, true_and, if_true]
    exact two_mul_oppositeSignIndicator_eq hn
  · simp [hs]

/-- Unit raw incidence joining every shell endpoint of opposite nonzero Möbius sign. -/
noncomputable def routeESignCompleteRawIncidence
    (shell : ℕ → ℕ → Prop) (n q : ℕ) : ℝ := by
  classical
  exact if μ n ≠ 0 ∧ shell n q ∧ μ q = -(μ n) then 1 else 0

theorem routeESignCompleteRawIncidence_nonneg
    (shell : ℕ → ℕ → Prop) (n q : ℕ) :
    0 ≤ routeESignCompleteRawIncidence shell n q := by
  classical
  simp only [routeESignCompleteRawIncidence]
  split_ifs <;> norm_num

theorem routeESignCompleteRawIncidence_comm
    (shell : ℕ → ℕ → Prop) (hshell : ∀ a b, shell a b ↔ shell b a) (n q : ℕ) :
    routeESignCompleteRawIncidence shell n q =
      routeESignCompleteRawIncidence shell q n := by
  classical
  unfold routeESignCompleteRawIncidence
  by_cases h : μ n ≠ 0 ∧ shell n q ∧ μ q = -(μ n)
  · rw [if_pos h]
    have hq0 : μ q ≠ 0 := by rw [h.2.2]; simpa using h.1
    have hrev : μ n = -(μ q) := by rw [h.2.2]; ring
    rw [if_pos ⟨hq0, (hshell n q).mp h.2.1, hrev⟩]
  · rw [if_neg h]
    symm
    apply if_neg
    rintro ⟨hq0, hqs, hrev⟩
    have hn0 : μ n ≠ 0 := by rw [hrev]; simpa using hq0
    have hforward : μ q = -(μ n) := by rw [hrev]; ring
    exact h ⟨hn0, (hshell n q).mpr hqs, hforward⟩

theorem routeESignCompleteRawIncidence_diag
    (shell : ℕ → ℕ → Prop) (n : ℕ) :
    routeESignCompleteRawIncidence shell n n = 0 := by
  classical
  unfold routeESignCompleteRawIncidence
  apply if_neg
  rintro ⟨hn0, _hs, hneg⟩
  have : μ n = 0 := by omega
  exact hn0 this

theorem routeESignCompleteRawIncidence_support_reverses_moebius
    (shell : ℕ → ℕ → Prop) {n q : ℕ}
    (h : routeESignCompleteRawIncidence shell n q ≠ 0) :
    (μ q : ℤ) = -(μ n : ℤ) := by
  classical
  unfold routeESignCompleteRawIncidence at h
  by_cases hrel : μ n ≠ 0 ∧ shell n q ∧ μ q = -(μ n)
  · exact hrel.2.2
  · simp [hrel] at h

/-- Finite row mass of the sign-complete physical incidence. -/
def routeESignCompleteRowMass
    (S : Finset ℕ) (shell : ℕ → ℕ → Prop) (n : ℕ) : ℝ :=
  ∑ q ∈ S, routeESignCompleteRawIncidence shell n q

theorem routeESignCompleteRowMass_eq_oppositeSignShellMass
    (S : Finset ℕ) (shell : ℕ → ℕ → Prop) {n : ℕ} (hn : μ n ≠ 0) :
    routeESignCompleteRowMass S shell n = routeEOppositeSignShellMass S shell n := by
  unfold routeESignCompleteRowMass routeEOppositeSignShellMass
  apply Finset.sum_congr rfl
  intro q _hq
  by_cases hrel : shell n q ∧ μ q = -(μ n)
  · simp [routeESignCompleteRawIncidence, hn, hrel]
  · simp [routeESignCompleteRawIncidence, hn, hrel]

/-- Exact degree identity for the sign-complete incidence. -/
theorem routeE_two_mul_signCompleteRowMass_eq
    (S : Finset ℕ) (shell : ℕ → ℕ → Prop) {n : ℕ}
    (hn : μ n = 1 ∨ μ n = -1) :
    2 * routeESignCompleteRowMass S shell n =
      routeESquarefreeShellMass S shell n -
        ((μ n : ℤ) : ℝ) * routeEMoebiusShellSum S shell n := by
  rw [routeESignCompleteRowMass_eq_oppositeSignShellMass S shell
    (by rcases hn with h | h <;> simp [h])]
  exact routeE_two_mul_oppositeSignShellMass_eq S shell hn

/-- Degree variance reduces pointwise to squarefree-density variance plus Möbius shell energy. -/
theorem routeE_signCompleteRowMass_deviation_sq_le
    (S : Finset ℕ) (shell : ℕ → ℕ → Prop) {n : ℕ}
    (hn : μ n = 1 ∨ μ n = -1) (Q : ℝ) :
    (routeESignCompleteRowMass S shell n - Q / 2) ^ (2 : ℕ) ≤
      (1 / 2 : ℝ) * (routeESquarefreeShellMass S shell n - Q) ^ (2 : ℕ) +
        (1 / 2 : ℝ) * routeEMoebiusShellSum S shell n ^ (2 : ℕ) := by
  have hid := routeE_two_mul_signCompleteRowMass_eq S shell hn
  have hsignSq : ((μ n : ℤ) : ℝ) ^ (2 : ℕ) = 1 := by
    rcases hn with hn | hn <;> simp [hn]
  have hrewrite :
      2 * (routeESignCompleteRowMass S shell n - Q / 2) =
        (routeESquarefreeShellMass S shell n - Q) -
          ((μ n : ℤ) : ℝ) * routeEMoebiusShellSum S shell n := by
    linarith
  calc
    (routeESignCompleteRowMass S shell n - Q / 2) ^ (2 : ℕ) =
        (1 / 4 : ℝ) *
          ((routeESquarefreeShellMass S shell n - Q) -
            ((μ n : ℤ) : ℝ) * routeEMoebiusShellSum S shell n) ^ (2 : ℕ) := by
      rw [← hrewrite]
      ring
    _ ≤ (1 / 2 : ℝ) * (routeESquarefreeShellMass S shell n - Q) ^ (2 : ℕ) +
          (1 / 2 : ℝ) * routeEMoebiusShellSum S shell n ^ (2 : ℕ) := by
      nlinarith [sq_nonneg
        ((routeESquarefreeShellMass S shell n - Q) +
          ((μ n : ℤ) : ℝ) * routeEMoebiusShellSum S shell n)]

end

end RHTower
