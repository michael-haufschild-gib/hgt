import GaloisForLFunctions.HTGeometry.SturmReduction

/-!
# From zero sets to zero configurations

Laguerre's rule bounds the length of a zero *configuration* — a sorted list with multiplicity.  A
finite zero *set* becomes such a configuration by sorting: each zero appears once, so the counts are
at most one and only the vanishing of the function itself is needed.

Together with the elementary bound `signChanges c + 1 ≤ m` this turns Laguerre's rule into the
statement the descent's base case needs: a real exponential sum with `m` nonzero terms and strictly
increasing exponents has at most `m - 1` zeros.
-/

open Set Filter Real

namespace GaloisForLFunctions.HTGeometry

/-! ## Sign changes are at most one fewer than the number of terms -/

theorem signChangesList_add_one_le : ∀ l : List ℝ, l ≠ [] → signChangesList l + 1 ≤ l.length := by
  intro l
  induction l with
  | nil => intro h; exact absurd rfl h
  | cons x u ih =>
    intro _
    cases u with
    | nil => simp [signChangesList]
    | cons y v =>
      have hih := ih (by simp)
      rw [signChangesList]
      simp only [List.length_cons] at hih ⊢
      split <;> omega

theorem signChanges_add_one_le {m : ℕ} (hm : 0 < m) (c : Fin m → ℝ) :
    signChanges c + 1 ≤ m := by
  have hne : (List.ofFn c) ≠ [] := by
    intro hcon
    have hz : (List.ofFn c).length = 0 := by rw [hcon]; rfl
    rw [List.length_ofFn] at hz
    omega
  have hb := signChangesList_add_one_le (List.ofFn c) hne
  rw [List.length_ofFn] at hb
  exact hb

/-! ## A finite zero set is a zero configuration -/

theorem exists_isZeroList_of_finset {f : ℝ → ℝ} (Z : Finset ℝ) (hZ : ∀ x ∈ Z, f x = 0) :
    ∃ l : List ℝ, IsZeroList f l ∧ l.length = Z.card := by
  classical
  refine ⟨Z.sort (· ≤ ·), ⟨Finset.pairwise_sort Z (· ≤ ·), ?_⟩, Finset.length_sort (· ≤ ·)⟩
  intro x
  by_cases hx : x ∈ Z.sort (· ≤ ·)
  · have hcount : (Z.sort (· ≤ ·)).count x ≤ 1 :=
      List.nodup_iff_count_le_one.mp (Z.sort_nodup (· ≤ ·)) x
    intro j hj
    have hj0 : j = 0 := by omega
    subst hj0
    rw [iteratedDeriv_zero]
    exact hZ x ((Finset.mem_sort (· ≤ ·)).mp hx)
  · rw [List.count_eq_zero.mpr hx]
    exact vanishesTo_zero _ _

/-! ## The base case of the descent -/

/-- **A real exponential sum has at most `m - 1` zeros.**  Laguerre's rule, applied to the sorted
zero set. -/
theorem card_zeros_le_expSum {m : ℕ} (hm : 0 < m) (c a : Fin m → ℝ)
    (hstrict : StrictMono a) (hc : ∀ i, c i ≠ 0)
    (Z : Finset ℝ) (hZ : ∀ x ∈ Z, expSum c a x = 0) :
    Z.card + 1 ≤ m := by
  obtain ⟨l, hl, hlen⟩ := exists_isZeroList_of_finset (f := expSum c a) Z hZ
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hlag := laguerre_zeroList_length_le n c a hstrict hc l hl
  have hsc := signChanges_add_one_le (m := n + 1) hm c
  omega

end GaloisForLFunctions.HTGeometry
