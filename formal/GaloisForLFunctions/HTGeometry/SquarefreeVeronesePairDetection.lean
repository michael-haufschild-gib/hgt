import GaloisForLFunctions.HTGeometry.SquarefreeVeroneseIdeal

/-!
# Pair detection for the squarefree Veronese ideal

When the variable set has cardinality `r + 1`, a monomial has support width at least `r`
exactly when its support meets every two-element coordinate set.  Consequently the squarefree
degree-`r` Veronese ideal is detected by the pair faces: outside the ideal, some nonzero monomial
coefficient survives after a pair of variables is removed.

This is the finite combinatorial specialization step in the reverse inclusion for the multiple
elliptic-gamma transverse-constraint theorem.  It is independent of the remaining analytic
order-one orbit input.
-/

namespace GaloisForLFunctions.VeroneseIdeal

open MvPolynomial Finset

variable {R σ : Type*} [CommRing R] [Fintype σ] [DecidableEq σ]

/-- **Pair-face detection of the squarefree Veronese ideal.**  On `r + 1` variables, a polynomial
belongs to the squarefree degree-`r` ideal exactly when the support of every nonzero monomial
coefficient meets every pair of variables.  Negating the right side gives the explicit pair and
monomial that survive the corresponding coordinate specialization. -/
theorem mem_veroneseIdeal_iff_every_pair_meets_support
    {r : ℕ} (hcard : Fintype.card σ = r + 1) (P : MvPolynomial σ R) :
    P ∈ veroneseIdeal R σ r ↔
      ∀ d : σ →₀ ℕ, coeff d P ≠ 0 →
        ∀ L : Finset σ, L.card = 2 → ¬ Disjoint d.support L := by
  rw [mem_veroneseIdeal_iff]
  constructor
  · intro hwide d hd L hL hdisj
    have hr : r ≤ d.support.card := hwide d hd
    have hLsub : L ⊆ Finset.univ \ d.support := by
      intro i hiL
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
      exact fun hiSupport => Finset.disjoint_left.mp hdisj hiSupport hiL
    have hLcardle : L.card ≤ (Finset.univ \ d.support).card :=
      Finset.card_le_card hLsub
    have hcomplement : (Finset.univ \ d.support).card ≤ 1 := by
      rw [Finset.card_sdiff]
      simp only [Finset.inter_univ, Finset.card_univ, hcard]
      omega
    omega
  · intro hpairs d hd
    by_contra hr
    have hsupport : d.support.card < r := Nat.lt_of_not_ge hr
    have hcomplement : 2 ≤ (Finset.univ \ d.support).card := by
      rw [Finset.card_sdiff]
      simp only [Finset.inter_univ, Finset.card_univ, hcard]
      omega
    obtain ⟨L, hLsub, hLcard⟩ := Finset.exists_subset_card_eq hcomplement
    apply hpairs d hd L hLcard
    rw [Finset.disjoint_left]
    intro i hiSupport hiL
    exact (Finset.mem_sdiff.mp (hLsub hiL)).2 hiSupport

/-- Outside the squarefree degree-`r` ideal on `r + 1` variables, one can exhibit a nonzero
monomial coefficient and a two-element coordinate set disjoint from its support. -/
theorem exists_pair_disjoint_support_of_not_mem_veroneseIdeal
    {r : ℕ} (hcard : Fintype.card σ = r + 1) (P : MvPolynomial σ R)
    (hP : P ∉ veroneseIdeal R σ r) :
    ∃ d : σ →₀ ℕ, ∃ L : Finset σ,
      coeff d P ≠ 0 ∧ L.card = 2 ∧ Disjoint d.support L := by
  rw [mem_veroneseIdeal_iff_every_pair_meets_support hcard P] at hP
  push Not at hP
  obtain ⟨d, hd, L, hL, hdisj⟩ := hP
  exact ⟨d, L, hd, hL, hdisj⟩

omit [Fintype σ] in
/-- **Exact transverse-support threshold for one monomial.**  A nonzero monomial belongs to the
squarefree degree-`r` ideal exactly when its exponent uses at least `r` distinct variables.  This
is the algebraic rank law behind the transverse-depth corollary: repeated use of one direction
does not compensate for a missing independent direction. -/
theorem monomial_mem_veroneseIdeal_iff
    {r : ℕ} {d : σ →₀ ℕ} {c : R} (hc : c ≠ 0) :
    monomial d c ∈ veroneseIdeal R σ r ↔ r ≤ d.support.card := by
  constructor
  · intro hmem
    exact (mem_veroneseIdeal_iff (R := R) (r := r) (monomial d c)).mp hmem d (by simp [hc])
  · exact monomial_mem_ideal c

end GaloisForLFunctions.VeroneseIdeal
