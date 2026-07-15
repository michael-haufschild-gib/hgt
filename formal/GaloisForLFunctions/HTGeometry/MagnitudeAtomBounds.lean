import GaloisForLFunctions.HTGeometry.MagnitudeWeightMassPolynomial
import GaloisForLFunctions.HTGeometry.MagnitudeNonzeroWeightMinimum

/-!
# Uniform bounds for inhomogeneous magnitude atoms

Every appearing grouped atom inherits its count and index mass from a support monomial of the
fixed differential polynomial.  This packages the uniform bounds needed to localize a selected
valuation minimizer.
-/

open PowerSeries MvPolynomial Finset

namespace GaloisForLFunctions

noncomputable section

/-- Largest ordinary `X`-degree among support monomials. -/
def magnitudeMaxXDegree (Q : MvPolynomial (Fin (n + 2)) ℂ) : ℕ :=
  Q.support.sup fun m => m 0

theorem xDegree_le_magnitudeMaxXDegree {n : ℕ}
    (Q : MvPolynomial (Fin (n + 2)) ℂ) {m : Fin (n + 2) →₀ ℕ}
    (hm : m ∈ Q.support) : m 0 ≤ magnitudeMaxXDegree Q :=
  Finset.le_sup (f := fun m => m 0) hm

/-- Each coordinate of a natural-valued `Finsupp` is bounded by its total count. -/
theorem finsupp_apply_le_count (ν : ℕ →₀ ℕ) (i : ℕ) :
    ν i ≤ ν.sum (fun _ k => k) := by
  rw [Finsupp.sum]
  by_cases hi : ν i = 0
  · simp [hi]
  · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finsupp.mem_support_iff.mpr hi)

/-- An appearing grouped key is realized by a sigma atom whose support monomial records its exact
count and index-weighted sum. -/
theorem atom_grading_witness_of_mem {n N : ℕ}
    (Q : MvPolynomial (Fin (n + 2)) ℂ) {ν : ℕ →₀ ℕ}
    (hν : ν ∈ (sigmaIdx n N Q).image (atomKeyOf n)) :
    ∃ x : Σ m : Fin (n + 2) →₀ ℕ,
        Fin (∑ j : Fin (n + 1), m j.succ) →₀ ℕ,
      x ∈ sigmaIdx n N Q ∧ ν = atomKeyOf n x ∧
      ν.sum (fun _ k => k) = jetMonomialDegree n x.1 ∧
      ν.sum (fun i k => i * k) = N - x.1 0 + jetMonomialOrder n x.1 := by
  classical
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hν
  refine ⟨x, hx, rfl, ?_, ?_⟩
  · exact atomKeyOf_count n x
  · rw [atomKeyOf_weighted_sum n x, sigmaIdx_antidiag_sum hx]
    rfl

/-- Every appearing atom has total count at most the maximal jet degree of `Q`. -/
theorem appearing_atom_count_le {n N : ℕ}
    (Q : MvPolynomial (Fin (n + 2)) ℂ) {ν : ℕ →₀ ℕ}
    (hν : ν ∈ (sigmaIdx n N Q).image (atomKeyOf n)) :
    ν.sum (fun _ k => k) ≤ magnitudeMaxJetDegree n Q := by
  obtain ⟨x, hx, _, hcount, _⟩ := atom_grading_witness_of_mem Q hν
  have hm : x.1 ∈ Q.support := by
    rw [sigmaIdx, Finset.mem_sigma] at hx
    exact (Finset.mem_filter.mp hx.1).1
  rw [hcount]
  exact jetDegree_le_magnitudeMaxJetDegree Q hm

/-- Every coordinate multiplicity of an appearing atom is bounded by the maximal jet degree. -/
theorem appearing_atom_apply_le {n N : ℕ}
    (Q : MvPolynomial (Fin (n + 2)) ℂ) {ν : ℕ →₀ ℕ}
    (hν : ν ∈ (sigmaIdx n N Q).image (atomKeyOf n)) :
    ∀ i, ν i ≤ magnitudeMaxJetDegree n Q := by
  intro i
  exact (finsupp_apply_le_count ν i).trans (appearing_atom_count_le Q hν)

/-- The index mass of every appearing atom lies in the fixed-width interval
`[N - maxXDegree, N + maxJetOrder]`. -/
theorem appearing_atom_weighted_sum_bounds {n N : ℕ}
    (Q : MvPolynomial (Fin (n + 2)) ℂ) {ν : ℕ →₀ ℕ}
    (hν : ν ∈ (sigmaIdx n N Q).image (atomKeyOf n)) :
    N - magnitudeMaxXDegree Q ≤ ν.sum (fun i k => i * k) ∧
      ν.sum (fun i k => i * k) ≤ N + magnitudeMaxJetOrder n Q := by
  obtain ⟨x, hx, _, _, hweight⟩ := atom_grading_witness_of_mem Q hν
  have hm : x.1 ∈ Q.support := by
    rw [sigmaIdx, Finset.mem_sigma] at hx
    exact (Finset.mem_filter.mp hx.1).1
  have hxdeg := xDegree_le_magnitudeMaxXDegree Q hm
  have hjord : jetMonomialOrder n x.1 ≤ magnitudeMaxJetOrder n Q := by
    exact jetOrder_le_magnitudeMaxJetOrder Q hm
  rw [hweight]
  constructor
  · exact (Nat.sub_le_sub_left hxdeg N).trans (Nat.le_add_right _ _)
  · omega

/-- Above the maximal ordinary `X`-degree, every appearing atom has nonempty source support. -/
theorem appearing_atom_support_nonempty_of_maxX_lt_level {n N : ℕ}
    (Q : MvPolynomial (Fin (n + 2)) ℂ) {ν : ℕ →₀ ℕ}
    (hν : ν ∈ (sigmaIdx n N Q).image (atomKeyOf n))
    (hN : magnitudeMaxXDegree Q < N) : ν.support.Nonempty := by
  apply Finsupp.support_nonempty_iff.mpr
  intro hzero
  have hlower := (appearing_atom_weighted_sum_bounds Q hν).1
  rw [hzero] at hlower
  simp at hlower
  omega

/-- A valuation upper bound controls the largest source index once `b` is strictly increasing on
the relevant tail. -/
theorem support_max_le_of_valuation_le {ν : ℕ →₀ ℕ} {b : ℕ → ℝ}
    (hbnn : ∀ n, 0 ≤ b n) {T K : ℕ}
    (hbstrict : ∀ p q, T ≤ p → p < q → b p < b q)
    (hne : ν.support.Nonempty) (hTK : T ≤ K)
    (hV : ν.sum (fun n k => (k : ℝ) * b n) ≤ b K) :
    ν.support.max' hne ≤ K := by
  by_contra hnot
  have hlt : K < ν.support.max' hne := Nat.lt_of_not_ge hnot
  have hb_lt : b K < b (ν.support.max' hne) := hbstrict K _ hTK hlt
  have hb_le := valuation_ge_b_max hbnn hne
  linarith

/-- Count, index mass, and a maximum-index bound force one-sided tail support. -/
theorem finsupp_tailSupport_of_count_weight_max {ν : ℕ →₀ ℕ} {D W K T : ℕ}
    (hcount : ν.sum (fun _ k => k) = D)
    (hweight : W ≤ ν.sum (fun n k => n * k))
    (hne : ν.support.Nonempty) (hmax : ν.support.max' hne ≤ K)
    (hT : T + (D - 1) * K ≤ W) :
    ∀ n, ν n ≠ 0 → T ≤ n := by
  have hcount' : (∑ n ∈ ν.support, ν n) = D := by
    simpa [Finsupp.sum] using hcount
  have hweight' : (∑ n ∈ ν.support, n * ν n) = ν.sum (fun n k => n * k) := by
    rfl
  have hgeom := weight_le_min_add_max hcount' hweight' hne
  have hmin : T ≤ ν.support.min' hne := by
    have hmaxmul : (D - 1) * ν.support.max' hne ≤ (D - 1) * K :=
      Nat.mul_le_mul_left _ hmax
    omega
  intro n hn
  exact hmin.trans (Finset.min'_le _ _ (Finsupp.mem_support_iff.mpr hn))

end

end GaloisForLFunctions
