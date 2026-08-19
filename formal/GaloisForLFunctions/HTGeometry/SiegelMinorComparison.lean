import GaloisForLFunctions.HTGeometry.SiegelTruncation

/-!
# Comparable minors give comparable diagonals

Each Jacobi diagonal entry is the ratio of two consecutive leading minors, so a two-sided comparison
of the minors of two forms transfers, with the constant squared, to a two-sided comparison of their
diagonals.

This reduces the entry bounds of Siegel's finiteness to a statement about minors: the leading minors
of two *reduced* bases of the same lattice are comparable, because reduction makes each of them
comparable to the minimum over sublattices of that rank.

* `d_le_of_det_le` : **comparable minors give comparable diagonals.**
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n : ℕ}

/-- **A two-sided comparison of leading minors gives a two-sided comparison of diagonals.** -/
theorem d_le_of_det_le {J J' : JacobiData n} {C : ℝ} (hC : 0 < C)
    (hle : ∀ (k : ℕ) (hk : k ≤ n),
      (leadingBlock hk J.form).det ≤ C * (leadingBlock hk J'.form).det)
    (hge : ∀ (k : ℕ) (hk : k ≤ n),
      (leadingBlock hk J'.form).det ≤ C * (leadingBlock hk J.form).det)
    (l : Fin n) : J.d l ≤ C ^ 2 * J'.d l := by
  have hk1 : (l : ℕ) + 1 ≤ n := l.isLt
  have hk0 : (l : ℕ) ≤ n := Nat.le_of_succ_le hk1
  have hll : (⟨(l : ℕ), hk1⟩ : Fin n) = l := Fin.ext rfl
  have hJ := det_leadingBlock_succ J hk1
  have hJ' := det_leadingBlock_succ J' hk1
  rw [hll] at hJ hJ'
  have hposJ : (0 : ℝ) < (leadingBlock hk0 J.form).det := by
    rw [det_leadingBlock_form hk0 J]
    exact Finset.prod_pos fun m _ => J.pos _
  have hposJ' : (0 : ℝ) < (leadingBlock hk0 J'.form).det := by
    rw [det_leadingBlock_form hk0 J']
    exact Finset.prod_pos fun m _ => J'.pos _
  have h1 : (leadingBlock hk0 J.form).det * J.d l ≤ C * ((leadingBlock hk0 J'.form).det * J'.d l) :=
    by rw [← hJ, ← hJ']; exact hle ((l : ℕ) + 1) hk1
  have h2 : (leadingBlock hk0 J'.form).det ≤ C * (leadingBlock hk0 J.form).det := hge (l : ℕ) hk0
  have hdJ' : (0 : ℝ) ≤ J'.d l := (J'.pos l).le
  have h3 : C * (leadingBlock hk0 J'.form).det * J'.d l
      ≤ C * (C * (leadingBlock hk0 J.form).det) * J'.d l :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hC.le) hdJ'
  have h4 : (leadingBlock hk0 J.form).det * J.d l
      ≤ (leadingBlock hk0 J.form).det * (C ^ 2 * J'.d l) := by nlinarith [h1, h3]
  exact le_of_mul_le_mul_left h4 hposJ

end GaloisForLFunctions.HTGeometry
