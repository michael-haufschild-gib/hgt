import GaloisForLFunctions.HTGeometry.LaguerreRule

/-!
# Real-exponent Vandermonde nondegeneracy

The moment argument in Lemma A.1 of the Navier–Stokes paper uses that
`exp (αⱼ yᵢ)` has nonzero determinant at strictly ordered real exponents and
nodes.  Unlike the ordinary Vandermonde theorem, the exponents here are real.
The corpus's Laguerre zero-count theorem for exponential sums supplies the
missing Chebyshev-system argument.
-/

namespace GaloisForLFunctions.HTGeometry.NavierStokesRealExponentialVandermonde

open Finset

/-- Real-exponent evaluation matrix, with nodes in rows and exponents in columns. -/
noncomputable def realExponentialVandermonde {n : ℕ} (α y : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => Real.exp (α j * y i)

private theorem signChanges_le_length_pred :
    ∀ (m : ℕ) (c : Fin (m + 1) → ℝ), signChanges c ≤ m := by
  intro m
  induction m with
  | zero => intro c; simp
  | succ m ih =>
      intro c
      rw [signChanges_succ]
      by_cases h : c 0 * c 1 < 0
      · rw [if_pos h]
        simpa [Nat.add_comm] using Nat.add_le_add_left (ih fun i => c i.succ) 1
      · rw [if_neg h]
        simpa using (ih fun i => c i.succ).trans (Nat.le_succ m)

private theorem vanishesTo_of_le_one {f : ℝ → ℝ} {k : ℕ} {x : ℝ}
    (hk : k ≤ 1) (hzero : f x = 0) : VanishesTo f k x := by
  intro j hj
  have hjzero : j = 0 := by omega
  subst j
  simpa using hzero

/-- Restrict a finite exponential sum to its nonzero coefficient support. -/
private theorem sum_orderedSupport_eq {n m : ℕ} (c α : Fin n → ℝ)
    (support : Finset (Fin n)) (hsupport : support = univ.filter fun i => c i ≠ 0)
    (hcard : support.card = m + 1) (t : ℝ) :
    (∑ r : Fin (m + 1),
      c (support.orderIsoOfFin hcard r) *
        Real.exp (α (support.orderIsoOfFin hcard r) * t)) =
      ∑ i : Fin n, c i * Real.exp (α i * t) := by
  let e := support.orderIsoOfFin hcard
  calc
    (∑ r : Fin (m + 1), c (e r) * Real.exp (α (e r) * t)) =
        ∑ z : support, c z * Real.exp (α z * t) := by
      change (∑ r : Fin (m + 1),
        c (e.toEquiv r) * Real.exp (α (e.toEquiv r) * t)) = _
      exact Equiv.sum_comp e.toEquiv (fun z : support => c z * Real.exp (α z * t))
    _ = ∑ i ∈ support, c i * Real.exp (α i * t) := by
      rw [← support.sum_attach]
      rfl
    _ = ∑ i : Fin n, c i * Real.exp (α i * t) := by
      rw [hsupport, sum_filter]
      refine (sum_congr rfl fun i _ => ?_).symm
      by_cases hi : c i ≠ 0
      · rw [if_pos hi]
      · rw [if_neg hi, not_ne_iff.mp hi, zero_mul]

/--
Generalized Vandermonde theorem for arbitrary real exponents.  Strict ordering
of exponents and nodes makes the exponential evaluation matrix nonsingular.
-/
theorem det_realExponentialVandermonde_ne_zero {n : ℕ} (α y : Fin n → ℝ)
    (hα : StrictMono α) (hy : StrictMono y) :
    (realExponentialVandermonde α y).det ≠ 0 := by
  classical
  intro hdet
  obtain ⟨c, hcne, hmul⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  let support : Finset (Fin n) := univ.filter fun i => c i ≠ 0
  have hsupport_ne : support.Nonempty := by
    by_contra hempty
    have hempty' : support = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    apply hcne
    funext i
    have hi : i ∉ support := by simp [hempty']
    simpa [support] using hi
  obtain ⟨m, hcard⟩ : ∃ m, support.card = m + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Finset.card_ne_zero.mpr hsupport_ne)
  let e := support.orderIsoOfFin hcard
  let c' : Fin (m + 1) → ℝ := fun r => c (e r)
  let α' : Fin (m + 1) → ℝ := fun r => α (e r)
  have hc' : ∀ r, c' r ≠ 0 := by
    intro r
    exact (Finset.mem_filter.mp (e r).property).2
  have hα' : StrictMono α' := by
    intro i j hij
    exact hα (e.lt_iff_lt.mpr hij)
  have hzero : ∀ i : Fin n, expSum c' α' (y i) = 0 := by
    intro i
    rw [expSum]
    change (∑ r : Fin (m + 1),
      c (e r) * Real.exp (α (e r) * y i)) = 0
    rw [sum_orderedSupport_eq c α support rfl hcard]
    have hi := congrFun hmul i
    simpa [Matrix.mulVec, dotProduct, realExponentialVandermonde, mul_comm] using hi
  have hyinj : Function.Injective y := hy.injective
  have hzeros : IsZeroList (expSum c' α') (List.ofFn y) := by
    refine ⟨List.pairwise_ofFn.mpr fun i j hij => (hy hij).le, ?_⟩
    intro x
    by_cases hx : x ∈ List.ofFn y
    · obtain ⟨i, hi⟩ := List.mem_ofFn.mp hx
      refine vanishesTo_of_le_one ?_ ?_
      · exact List.nodup_iff_count_le_one.mp (List.nodup_ofFn.mpr hyinj) x
      · rw [← hi]
        exact hzero i
    · rw [List.count_eq_zero.mpr hx]
      exact vanishesTo_zero _ _
  have hlaguerre := laguerre_zeroList_length_le m c' α' hα' hc' (List.ofFn y) hzeros
  have hsupport_card_le : support.card ≤ n := by simpa using support.card_le_univ
  have hsign := signChanges_le_length_pred m c'
  simp only [List.length_ofFn] at hlaguerre
  omega

/-- The real-exponent evaluation matrix is a unit over `ℝ`. -/
theorem isUnit_realExponentialVandermonde {n : ℕ} (α y : Fin n → ℝ)
    (hα : StrictMono α) (hy : StrictMono y) :
    IsUnit (realExponentialVandermonde α y) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  exact det_realExponentialVandermonde_ne_zero α y hα hy

/-- Exponential moments of point masses at the ordered nodes. -/
noncomputable def weightedExponentialMomentMatrix {n : ℕ}
    (α y weight : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (realExponentialVandermonde α y).transpose * Matrix.diagonal weight

@[simp]
theorem weightedExponentialMomentMatrix_apply {n : ℕ}
    (α y weight : Fin n → ℝ) (i j : Fin n) :
    weightedExponentialMomentMatrix α y weight i j =
      Real.exp (α i * y j) * weight j := by
  classical
  simp [weightedExponentialMomentMatrix, Matrix.mul_apply,
    realExponentialVandermonde, Matrix.diagonal_apply]

/-- Determinant factors into the real-exponent Vandermonde determinant and point masses. -/
theorem det_weightedExponentialMomentMatrix {n : ℕ}
    (α y weight : Fin n → ℝ) :
    (weightedExponentialMomentMatrix α y weight).det =
      (realExponentialVandermonde α y).det * ∏ j, weight j := by
  classical
  rw [weightedExponentialMomentMatrix, Matrix.det_mul, Matrix.det_transpose,
    Matrix.det_diagonal]

/-- Nonzero point masses preserve moment-map invertibility. -/
theorem isUnit_weightedExponentialMomentMatrix {n : ℕ}
    (α y weight : Fin n → ℝ) (hα : StrictMono α) (hy : StrictMono y)
    (hweight : ∀ j, weight j ≠ 0) :
    IsUnit (weightedExponentialMomentMatrix α y weight) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero,
    det_weightedExponentialMomentMatrix]
  exact mul_ne_zero (det_realExponentialVandermonde_ne_zero α y hα hy)
    (Finset.prod_ne_zero_iff.mpr fun j _ => hweight j)

end GaloisForLFunctions.HTGeometry.NavierStokesRealExponentialVandermonde
