/-
The seam crossing operators `B_{p,r}` as concrete matrices, and their crossing-energy law as a trace.

The seam construction's foundational object (§1) is the crossing tower `B_{p,r} = (1 − Q_p)S_p^r Q_p`
with the Hilbert–Schmidt energy law `⟨B_{p,r}, B_{p,s}⟩_HS = r·δ_{r,s}`.  `SeamCrossingTower` proves the
law at the combinatorial level (the count of shared matrix positions).  Here the crossing operator is a
genuine finite matrix and the energy law is its actual Hilbert–Schmidt inner product
`tr(B_rᴴ B_s)` — grounding the tower as operators, not supports.

`crossOp M r` is the `r`-step crossing on the `M`-shell space: column `j < r` carries a single unit
entry in row `j + r` (it lifts the lowest `r` shells up by `r` steps — a clean model of `(1−Q)S^rQ`,
where `Q` projects onto the low block and `S^r` shifts up by `r`).  Its Hilbert–Schmidt inner product
is read off the trace identity `tr(Aᴴ B) = Σ_{i,k} conj(A_{ki}) B_{ki}`:

* `crossOp_orthogonal` — `tr(B_rᴴ B_s) = 0` for `r ≠ s`: a shared diagonal entry would force
  `i + r = i + s`.  Distinct crossing lengths are Hilbert–Schmidt orthogonal.
* `crossOp_self_energy` — `tr(B_rᴴ B_r) = r` (for `2r ≤ M`, so the crossing fits): the crossing has
  exactly `r` unit entries, so `‖B_r‖²_HS = r`.  The crossing self-energy is the crossing length — the
  `1/r` Euler weight is its reciprocal.

Together `tr(B_rᴴ B_s) = if r = s then r else 0` — the crossing-energy law of the moonshot §1, realized
at the operator level.
-/
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.RCLike.Basic

noncomputable section

namespace RHTower

open Matrix Finset

/-- The `r`-step seam crossing operator on the `M`-shell space: column `j < r` carries a unit entry in
row `j + r`.  A finite model of `(1 − Q)S^r Q` — project onto the low `r` shells, shift up by `r`. -/
def crossOp (M r : ℕ) : Matrix (Fin M) (Fin M) ℂ :=
  fun i j => if (j : ℕ) < r ∧ (i : ℕ) = (j : ℕ) + r then 1 else 0

/-- The Hilbert–Schmidt inner product of two crossing operators, expanded:
`tr(B_rᴴ B_s) = Σ_{i,k} conj((B_r)_{ki}) (B_s)_{ki}`. -/
theorem crossOp_hs_trace (M r s : ℕ) :
    ((crossOp M r)ᴴ * (crossOp M s)).trace
      = ∑ i : Fin M, ∑ k : Fin M,
          star (crossOp M r k i) * (crossOp M s k i) := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- **Distinct crossing lengths are Hilbert–Schmidt orthogonal.**  `tr(B_rᴴ B_s) = 0` for `r ≠ s`: a
nonzero diagonal term needs `(k) = (i) + r` and `(k) = (i) + s`, forcing `r = s`. -/
theorem crossOp_orthogonal (M : ℕ) {r s : ℕ} (h : r ≠ s) :
    ((crossOp M r)ᴴ * (crossOp M s)).trace = 0 := by
  rw [crossOp_hs_trace]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun k _ => ?_
  simp only [crossOp]
  by_cases hr : (i : ℕ) < r ∧ (k : ℕ) = (i : ℕ) + r
  · by_cases hs : (i : ℕ) < s ∧ (k : ℕ) = (i : ℕ) + s
    · exact absurd (by omega : r = s) h
    · simp [hs]
  · simp [hr]

/-- **The crossing self-energy is the crossing length.**  `tr(B_rᴴ B_r) = r` when the crossing fits
(`2r ≤ M`): `B_r` has exactly `r` unit entries (one per low shell `j < r`), so `‖B_r‖²_HS = r`.  The
reciprocal `1/r` is the Euler weight of `SeamCrossingTower.expKernel_eq_eulerFactor`. -/
theorem crossOp_self_energy (M r : ℕ) (hM : 2 * r ≤ M) :
    ((crossOp M r)ᴴ * (crossOp M r)).trace = (r : ℂ) := by
  rw [crossOp_hs_trace]
  have hinner : ∀ i : Fin M,
      (∑ k : Fin M, star (crossOp M r k i) * (crossOp M r k i))
        = if (i : ℕ) < r then (1 : ℂ) else 0 := by
    intro i
    simp only [crossOp]
    by_cases hi : (i : ℕ) < r
    · have hlt : (i : ℕ) + r < M := by omega
      rw [Finset.sum_eq_single (⟨(i : ℕ) + r, hlt⟩ : Fin M)]
      · simp [hi]
      · intro k _ hk
        have hne : (k : ℕ) ≠ (i : ℕ) + r := fun hc => hk (Fin.ext hc)
        simp [hi, hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · simp [hi]
  rw [Finset.sum_congr rfl (fun i _ => hinner i),
    Fin.sum_univ_eq_sum_range (fun j => if j < r then (1 : ℂ) else 0) M, Finset.sum_boole]
  have hfilter : (Finset.range M).filter (fun x => x < r) = Finset.range r := by
    ext x; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [hfilter, Finset.card_range]

/-- **The crossing-energy law at the operator level.**  `tr(B_rᴴ B_s) = r·δ_{r,s}` (for `2r ≤ M`): the
Hilbert–Schmidt inner product of the crossing operators is the crossing length on the diagonal and `0`
off it — the moonshot §1 energy law realized as an actual matrix trace. -/
theorem crossOp_energy_law (M r s : ℕ) (hM : 2 * r ≤ M) :
    ((crossOp M r)ᴴ * (crossOp M s)).trace = if r = s then (r : ℂ) else 0 := by
  by_cases h : r = s
  · subst h; rw [if_pos rfl]; exact crossOp_self_energy M r hM
  · rw [if_neg h]; exact crossOp_orthogonal M h

/-! ### The crossing operators are odd square-zero differentials -/

/-- **A crossing operator is square-zero.**  `B_r · B_r = 0`: a composed nonzero entry would need
`(k) = (j) + r` (first factor) and `(k) < r` (second), so `(j) + r < r`, impossible.  So each crossing
is a legitimate seam differential `d` — the object the McKean–Singer compression acts on
(`SeamHodgeCompression`, `SeamFiniteHodge`), connecting the §1 tower to the §6–§8 Hodge step. -/
theorem crossOp_sq_zero (M r : ℕ) : crossOp M r * crossOp M r = 0 := by
  ext i j
  simp only [Matrix.mul_apply, crossOp, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases h1 : (k : ℕ) < r ∧ (i : ℕ) = (k : ℕ) + r
  · by_cases h2 : (j : ℕ) < r ∧ (k : ℕ) = (j : ℕ) + r
    · omega
    · simp [h2]
  · simp [h1]

/-- The seam grading involution for the `r`-crossing: `+1` on the low `r` shells, `−1` above.  Its
square is `1` (`gradeOp_sq`), and it makes the crossing odd (`grade_crossOp_odd`). -/
def gradeOp (M r : ℕ) : Matrix (Fin M) (Fin M) ℂ :=
  Matrix.diagonal (fun k => if (k : ℕ) < r then 1 else -1)

/-- The seam grading is an involution: `Γ² = 1`. -/
theorem gradeOp_sq (M r : ℕ) : gradeOp M r * gradeOp M r = 1 := by
  rw [gradeOp, Matrix.diagonal_mul_diagonal]
  have h : (fun k : Fin M => (if (k : ℕ) < r then (1 : ℂ) else -1) * (if (k : ℕ) < r then 1 else -1))
      = (fun _ => (1 : ℂ)) := by funext k; by_cases hk : (k : ℕ) < r <;> simp [hk]
  rw [h, Matrix.diagonal_one]

/-- **The crossing is odd for the grading.**  `Γ · B_r = −(B_r · Γ)`: the crossing sends the low block
(`+1`) to the high block (`−1`), reversing the grading sign.  So `(Γ, B_r)` is an odd square-zero
differential — exactly the input `seam_hodge_compression_finite` requires, realized by a concrete
crossing operator. -/
theorem grade_crossOp_odd (M r : ℕ) :
    gradeOp M r * crossOp M r = -(crossOp M r * gradeOp M r) := by
  ext i j
  simp only [gradeOp, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.neg_apply, crossOp]
  by_cases h : (j : ℕ) < r ∧ (i : ℕ) = (j : ℕ) + r
  · simp [h]
  · simp [h]

end RHTower
