import Mathlib

/-!
# Confluent vanishing forces a polynomial to be zero

A polynomial whose degree is below the total prescribed vanishing order at finitely many distinct
points, and which vanishes to that order at each of them, is zero.  The count is the ordinary
root-multiplicity count: each point contributes its multiplicity, the multiplicities of distinct
points add inside the root multiset, and the multiset is no larger than the degree.
-/

namespace GaloisForLFunctions.HTGeometry

theorem sum_count_le_card {α : Type*} [DecidableEq α] (m : Multiset α) (T : Finset α) :
    ∑ a ∈ T, m.count a ≤ Multiset.card m := by
  have h1 : ∑ a ∈ T, m.count a = ∑ a ∈ T ∩ m.toFinset, m.count a := by
    refine (Finset.sum_subset Finset.inter_subset_left ?_).symm
    intro x hx hnx
    rw [Multiset.count_eq_zero]
    intro hmem
    exact hnx (Finset.mem_inter.2 ⟨hx, Multiset.mem_toFinset.2 hmem⟩)
  rw [h1, ← Multiset.toFinset_sum_count_eq m]
  exact Finset.sum_le_sum_of_subset Finset.inter_subset_right

/-- **Confluent vanishing.**  A polynomial of degree below the total vanishing order that vanishes
to the prescribed order at each of finitely many distinct points is zero. -/
theorem polynomial_eq_zero_of_jets_vanish {ι : Type*} [Fintype ι]
    (q : ι → ℂ) (hq : Function.Injective q) (ord : ι → ℕ)
    {P : Polynomial ℂ} (hdeg : P.natDegree < ∑ i, ord i)
    (hvan : ∀ i, ∀ j, j < ord i → ((⇑Polynomial.derivative)^[j] P).eval (q i) = 0) :
    P = 0 := by
  classical
  by_contra hP
  have hmult : ∀ i, ord i ≤ P.rootMultiplicity (q i) := by
    intro i
    rcases Nat.eq_zero_or_pos (ord i) with h0 | hpos
    · rw [h0]
      exact Nat.zero_le _
    · have hlt := Polynomial.lt_rootMultiplicity_of_isRoot_iterate_derivative
        (p := P) (t := q i) (n := ord i - 1) hP (fun m hm => hvan i m (by omega))
      omega
  have hsum : ∑ i, ord i ≤ ∑ i, P.rootMultiplicity (q i) :=
    Finset.sum_le_sum fun i _ => hmult i
  have hcount : ∑ i, P.rootMultiplicity (q i)
      = ∑ a ∈ Finset.univ.image q, Multiset.count a P.roots := by
    rw [Finset.sum_image (fun x _ y _ h => hq h)]
    exact Finset.sum_congr rfl fun i _ => (Polynomial.count_roots P).symm
  have hle : ∑ a ∈ Finset.univ.image q, Multiset.count a P.roots ≤ Multiset.card P.roots :=
    sum_count_le_card _ _
  have hdegle : Multiset.card P.roots ≤ P.natDegree := Polynomial.card_roots' P
  omega

/-- **Confluent vanishing of a monomial-shifted polynomial.**  If `X^L · Q` vanishes to the
prescribed orders at finitely many distinct nonzero points and `Q` has degree below the total
order, then `Q = 0`: the monomial factor is a unit at every nonzero node, so it contributes no
multiplicity. -/
theorem polynomial_eq_zero_of_shifted_jets_vanish {ι : Type*} [Fintype ι]
    (q : ι → ℂ) (hq : Function.Injective q) (hq0 : ∀ i, q i ≠ 0) (ord : ι → ℕ) (L : ℕ)
    {Q : Polynomial ℂ} (hdeg : Q.natDegree < ∑ i, ord i)
    (hvan : ∀ i, ∀ j, j < ord i →
      ((⇑Polynomial.derivative)^[j] ((Polynomial.X ^ L) * Q)).eval (q i) = 0) :
    Q = 0 := by
  classical
  by_contra hQ
  have hP : (Polynomial.X ^ L * Q : Polynomial ℂ) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) hQ
  have hmultX : ∀ i, Polynomial.rootMultiplicity (q i) (Polynomial.X ^ L : Polynomial ℂ) = 0 := by
    intro i
    refine Polynomial.rootMultiplicity_eq_zero ?_
    simp [Polynomial.IsRoot, hq0 i]
  have hmult : ∀ i, ord i ≤ Q.rootMultiplicity (q i) := by
    intro i
    rcases Nat.eq_zero_or_pos (ord i) with h0 | hpos
    · rw [h0]
      exact Nat.zero_le _
    · have hlt := Polynomial.lt_rootMultiplicity_of_isRoot_iterate_derivative
        (p := (Polynomial.X ^ L * Q : Polynomial ℂ)) (t := q i) (n := ord i - 1) hP
        (fun m hm => hvan i m (by omega))
      rw [Polynomial.rootMultiplicity_mul hP, hmultX i, Nat.zero_add] at hlt
      omega
  have hsum : ∑ i, ord i ≤ ∑ i, Q.rootMultiplicity (q i) :=
    Finset.sum_le_sum fun i _ => hmult i
  have hcount : ∑ i, Q.rootMultiplicity (q i)
      = ∑ a ∈ Finset.univ.image q, Multiset.count a Q.roots := by
    rw [Finset.sum_image (fun x _ y _ h => hq h)]
    exact Finset.sum_congr rfl fun i _ => (Polynomial.count_roots Q).symm
  have hle : ∑ a ∈ Finset.univ.image q, Multiset.count a Q.roots ≤ Multiset.card Q.roots :=
    sum_count_le_card _ _
  have hdegle : Multiset.card Q.roots ≤ Q.natDegree := Polynomial.card_roots' Q
  omega

end GaloisForLFunctions.HTGeometry
