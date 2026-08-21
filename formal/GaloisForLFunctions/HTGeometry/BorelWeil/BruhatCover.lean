import GaloisForLFunctions.HTGeometry.BorelWeil.LUDecomposition
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# The Bruhat covering of the flag variety

The flag variety `G/B` is covered by the `|W|` translates of the big cell, one for each element of
the Weyl group.  In matrix terms this is the statement proved here: for every invertible `g` there
is a permutation `σ` of the rows such that **all** leading principal minors of the row-permuted
matrix `g.submatrix σ id` are nonzero — equivalently `g = P_σ · L · B` with `L` lower unitriangular
and `B` invertible upper triangular, by the LU theorem of `LUDecomposition`.

The proof is Gaussian elimination with pivoting, run as a greedy induction: having chosen `j` rows
whose `j × j` leading minor is nonzero, one more row can always be adjoined, since otherwise the
cofactor vector of the enlarged minor would be a nonzero kernel vector of `g`.

## Main results

* `det_eq_det_of_rows_id` — determinants agree when the trailing rows are identity rows and the
  leading blocks agree.
* `exists_extend_minor` — the greedy step.
-/

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix

variable {N : ℕ} {k : Type*} [Field k]

/-- A leading minor depends only on the row selection below its size. -/
theorem leadingMinorMat_congr_of_eq_below (g : Matrix (Fin N) (Fin N) k) {m : ℕ}
    {f f' : Fin N → Fin N} (h : ∀ i : Fin N, (i : ℕ) < m → f i = f' i) :
    leadingMinorMat m (g.submatrix f id) = leadingMinorMat m (g.submatrix f' id) := by
  have hmat : truncate m (g.submatrix f id) = truncate m (g.submatrix f' id) := by
    ext i l
    by_cases hi : (i : ℕ) < m
    · by_cases hl : (l : ℕ) < m
      · rw [truncate_apply_of_both hi hl, truncate_apply_of_both hi hl]
        simp only [Matrix.submatrix_apply, id_eq, h i hi]
      · rw [truncate_apply_of_not_right hl, truncate_apply_of_not_right hl]
    · rw [truncate_apply_of_not_left hi, truncate_apply_of_not_left hi]
  rw [leadingMinorMat, leadingMinorMat, hmat]

/-- Two matrices whose rows from `j` on are the identity rows and whose leading `j × j` blocks
agree have the same determinant. -/
theorem det_eq_det_of_rows_id {j : ℕ} {A B : Matrix (Fin N) (Fin N) k}
    (hA : ∀ i l : Fin N, ¬ (i : ℕ) < j → A i l = if i = l then 1 else 0)
    (hB : ∀ i l : Fin N, ¬ (i : ℕ) < j → B i l = if i = l then 1 else 0)
    (hblock : ∀ i l : Fin N, (i : ℕ) < j → (l : ℕ) < j → A i l = B i l) :
    A.det = B.det := by
  classical
  set b : Fin N → ℕ := fun i => if (i : ℕ) < j then 0 else 1 with hb
  have hb0 : ∀ i : Fin N, (i : ℕ) < j → b i = 0 := by
    intro i hi; simp only [hb]; rw [if_pos hi]
  have hb1 : ∀ i : Fin N, ¬ (i : ℕ) < j → b i = 1 := by
    intro i hi; simp only [hb]; rw [if_neg hi]
  have htri : ∀ (M : Matrix (Fin N) (Fin N) k),
      (∀ i l : Fin N, ¬ (i : ℕ) < j → M i l = if i = l then 1 else 0) →
      M.BlockTriangular b := by
    intro M hM i l hil
    have hi : ¬ (i : ℕ) < j := by
      intro hc
      rw [hb0 i hc] at hil
      omega
    have hne : i ≠ l := by
      rintro rfl
      exact absurd hil (lt_irrefl _)
    rw [hM i l hi, if_neg hne]
  have hblocks : ∀ a : ℕ, A.toSquareBlock b a = B.toSquareBlock b a := by
    intro a
    ext x y
    have hax : b (x : Fin N) = a := x.2
    have hay : b (y : Fin N) = a := y.2
    by_cases hx : ((x : Fin N) : ℕ) < j
    · have hbx : b (x : Fin N) = 0 := hb0 _ hx
      have hby : b (y : Fin N) = 0 := by rw [hay, ← hax]; exact hbx
      have hy : ((y : Fin N) : ℕ) < j := by
        by_contra hc
        rw [hb1 _ hc] at hby
        omega
      exact hblock _ _ hx hy
    · show A _ _ = B _ _
      rw [hA _ _ hx, hB _ _ hx]
  rw [(htri A hA).det, (htri B hB).det]
  exact Finset.prod_congr rfl fun a _ => by rw [hblocks a]

end GaloisForLFunctions.HTGeometry.BorelWeil

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix

variable {N : ℕ} {k : Type*} [Field k]

/-- The truncated row-permuted matrix used in the greedy step. -/
def bruhatStepMat (g : Matrix (Fin N) (Fin N) k) (j : ℕ) (hj : j < N)
    (f : Fin N → Fin N) (r : Fin N) : Matrix (Fin N) (Fin N) k :=
  truncate (j + 1) (g.submatrix (Function.update f ⟨j, hj⟩ r) id)

theorem det_bruhatStepMat (g : Matrix (Fin N) (Fin N) k) (j : ℕ) (hj : j < N)
    (f : Fin N → Fin N) (r : Fin N) :
    (bruhatStepMat g j hj f r).det
      = leadingMinorMat (j + 1) (g.submatrix (Function.update f ⟨j, hj⟩ r) id) := rfl

theorem bruhatStepMat_off_row (g : Matrix (Fin N) (Fin N) k) (j : ℕ) (hj : j < N)
    (f : Fin N → Fin N) (r r' : Fin N) {i : Fin N} (hi : i ≠ ⟨j, hj⟩) (l : Fin N) :
    bruhatStepMat g j hj f r i l = bruhatStepMat g j hj f r' i l := by
  have hupd : Function.update f ⟨j, hj⟩ r i = Function.update f ⟨j, hj⟩ r' i := by
    rw [Function.update_of_ne hi, Function.update_of_ne hi]
  rw [bruhatStepMat, bruhatStepMat]
  by_cases h1 : (i : ℕ) < j + 1
  · by_cases h2 : (l : ℕ) < j + 1
    · rw [truncate_apply_of_both h1 h2, truncate_apply_of_both h1 h2]
      simp only [Matrix.submatrix_apply, id_eq, hupd]
    · rw [truncate_apply_of_not_right h2, truncate_apply_of_not_right h2]
  · rw [truncate_apply_of_not_left h1, truncate_apply_of_not_left h1]

theorem bruhatStepMat_row (g : Matrix (Fin N) (Fin N) k) (j : ℕ) (hj : j < N)
    (f : Fin N → Fin N) (r : Fin N) (l : Fin N) :
    bruhatStepMat g j hj f r ⟨j, hj⟩ l = if (l : ℕ) < j + 1 then g r l else 0 := by
  have hjlt : ((⟨j, hj⟩ : Fin N) : ℕ) < j + 1 := by simp
  rw [bruhatStepMat]
  by_cases h2 : (l : ℕ) < j + 1
  · rw [truncate_apply_of_both hjlt h2, if_pos h2]
    simp only [Matrix.submatrix_apply, id_eq, Function.update_self]
  · rw [truncate_apply_of_not_right h2, if_neg h2, if_neg]
    rintro rfl
    exact h2 hjlt

theorem bruhatStepMat_block (g : Matrix (Fin N) (Fin N) k) (j : ℕ) (hj : j < N)
    (f : Fin N → Fin N) (r : Fin N) {i l : Fin N} (hi : (i : ℕ) < j) (hl : (l : ℕ) < j) :
    bruhatStepMat g j hj f r i l = g (f i) l := by
  have hine : i ≠ ⟨j, hj⟩ := by
    intro hc
    rw [hc] at hi
    simp at hi
  rw [bruhatStepMat, truncate_apply_of_both (by omega) (by omega)]
  simp only [Matrix.submatrix_apply, id_eq, Function.update_of_ne hine]

theorem bruhatStepMat_row_id (g : Matrix (Fin N) (Fin N) k) (j : ℕ) (hj : j < N)
    (f : Fin N → Fin N) (r : Fin N) {i : Fin N} (hi : ¬ (i : ℕ) < j) (hine : i ≠ ⟨j, hj⟩)
    (l : Fin N) : bruhatStepMat g j hj f r i l = if i = l then 1 else 0 := by
  have h1 : ¬ (i : ℕ) < j + 1 := by
    intro hc
    apply hine
    apply Fin.ext
    show (i : ℕ) = j
    omega
  rw [bruhatStepMat, truncate_apply_of_not_left h1]

end GaloisForLFunctions.HTGeometry.BorelWeil

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix

variable {N : ℕ} {k : Type*} [Field k]

theorem adjugate_bruhatStepMat_diag (g : Matrix (Fin N) (Fin N) k) (j : ℕ) (hj : j < N)
    (f : Fin N → Fin N) (r : Fin N) :
    (bruhatStepMat g j hj f r).adjugate ⟨j, hj⟩ ⟨j, hj⟩
      = leadingMinorMat j (g.submatrix f id) := by
  classical
  rw [Matrix.adjugate_apply, leadingMinorMat]
  refine det_eq_det_of_rows_id (j := j) ?_ ?_ ?_
  · intro i l hi
    by_cases hine : i = ⟨j, hj⟩
    · rw [hine, Matrix.updateRow_self, Pi.single_apply]
      by_cases h : l = (⟨j, hj⟩ : Fin N)
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg fun hc => h hc.symm]
    · rw [Matrix.updateRow_ne hine]
      exact bruhatStepMat_row_id g j hj f r hi hine l
  · intro i l hi
    exact truncate_apply_of_not_left hi
  · intro i l hi hl
    have hine : i ≠ ⟨j, hj⟩ := by
      intro hc
      rw [hc] at hi
      simp at hi
    rw [Matrix.updateRow_ne hine, bruhatStepMat_block g j hj f r hi hl,
      truncate_apply_of_both hi hl]
    simp

/-- **The greedy step of the Bruhat covering.**  A nonvanishing leading minor of size `j` extends
to one of size `j + 1` by adjoining a suitable row. -/
theorem exists_extend_minor {g : Matrix (Fin N) (Fin N) k} (hg : g.det ≠ 0) {j : ℕ} (hj : j < N)
    (f : Fin N → Fin N) (hf : leadingMinorMat j (g.submatrix f id) ≠ 0) :
    ∃ r : Fin N, leadingMinorMat (j + 1) (g.submatrix (Function.update f ⟨j, hj⟩ r) id) ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  set jF : Fin N := ⟨j, hj⟩ with hjF
  set c : Fin N → k := fun l => (bruhatStepMat g j hj f (f jF)).adjugate l jF with hc
  have hadj : ∀ (r : Fin N) (l : Fin N), (bruhatStepMat g j hj f r).adjugate l jF = c l := by
    intro r l
    simp only [hc]
    rw [Matrix.adjugate_apply, Matrix.adjugate_apply]
    congr 1
    ext i m
    by_cases hi : i = jF
    · subst hi
      rw [Matrix.updateRow_self, Matrix.updateRow_self]
    · rw [Matrix.updateRow_ne hi, Matrix.updateRow_ne hi]
      exact bruhatStepMat_off_row g j hj f r (f jF) hi m
  set v : Fin N → k := fun l => if (l : ℕ) < j + 1 then c l else 0 with hv
  have hker : g *ᵥ v = 0 := by
    funext r
    have hzero : (bruhatStepMat g j hj f r).det = 0 := hcon r
    have hmul : ∑ l, (bruhatStepMat g j hj f r) jF l * c l = 0 := by
      have h := congrFun (congrFun (Matrix.mul_adjugate (bruhatStepMat g j hj f r)) jF) jF
      rw [Matrix.mul_apply] at h
      have h2 : ∑ l, (bruhatStepMat g j hj f r) jF l
          * (bruhatStepMat g j hj f r).adjugate l jF = 0 := by
        rw [h, hzero]
        simp
      rw [← h2]
      exact Finset.sum_congr rfl fun l _ => by rw [hadj r l]
    show (∑ l, g r l * v l) = 0
    rw [← hmul]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [hv]
    rw [bruhatStepMat_row]
    by_cases h : (l : ℕ) < j + 1 <;> simp [h]
  have hvne : v ≠ 0 := by
    intro h0
    apply hf
    have hvj : v jF = leadingMinorMat j (g.submatrix f id) := by
      simp only [hv, hc]
      rw [if_pos (by simp [hjF]), adjugate_bruhatStepMat_diag]
    rw [← hvj, h0]
    rfl
  exact hg ((Matrix.exists_mulVec_eq_zero_iff (M := g)).mp ⟨v, hvne, hker⟩)

end GaloisForLFunctions.HTGeometry.BorelWeil

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix

variable {N : ℕ} {k : Type*} [Field k]

theorem leadingMinorMat_eq_zero_of_row_eq (g : Matrix (Fin N) (Fin N) k) {m : ℕ}
    {f : Fin N → Fin N} {t s : Fin N} (hts : t ≠ s) (ht : (t : ℕ) < m) (hs : (s : ℕ) < m)
    (heq : f t = f s) : leadingMinorMat m (g.submatrix f id) = 0 := by
  refine Matrix.det_zero_of_row_eq hts ?_
  funext l
  by_cases hl : (l : ℕ) < m
  · rw [truncate_apply_of_both ht hl, truncate_apply_of_both hs hl]
    simp only [Matrix.submatrix_apply, id_eq, heq]
  · rw [truncate_apply_of_not_right hl, truncate_apply_of_not_right hl,
      if_neg (by rintro rfl; exact hl ht), if_neg (by rintro rfl; exact hl hs)]

/-- **The Bruhat covering of the flag variety.**  Every invertible matrix admits a permutation of
its rows after which all leading principal minors are nonzero.  Together with
`exists_lu_of_leadingMinor_ne_zero` this says `g = P_σ · L · B`: the `|W|` translates of the big
cell cover `G/B`. -/
theorem exists_perm_leadingMinor_ne_zero {g : Matrix (Fin N) (Fin N) k} (hg : g.det ≠ 0) :
    ∃ σ : Equiv.Perm (Fin N),
      ∀ i : Fin N, leadingMinorMat ((i : ℕ) + 1) (g.submatrix σ id) ≠ 0 := by
  classical
  have key : ∀ j : ℕ, j ≤ N → ∃ σ : Equiv.Perm (Fin N),
      ∀ i : Fin N, (i : ℕ) < j → leadingMinorMat ((i : ℕ) + 1) (g.submatrix σ id) ≠ 0 := by
    intro j
    induction j with
    | zero => intro _; exact ⟨1, by intro i hi; omega⟩
    | succ j ih =>
      intro hjN
      obtain ⟨σ, hσ⟩ := ih (by omega)
      have hj : j < N := by omega
      set jF : Fin N := ⟨j, hj⟩ with hjF
      have hminj : leadingMinorMat j (g.submatrix σ id) ≠ 0 := by
        rcases Nat.eq_zero_or_pos j with hj0 | hj0
        · subst hj0
          have h0 : truncate 0 (g.submatrix (⇑σ) id) = 1 := by
            ext i l
            rw [truncate_apply_of_not_left (by omega), Matrix.one_apply]
          rw [leadingMinorMat, h0, Matrix.det_one]
          exact one_ne_zero
        · have := hσ ⟨j - 1, by omega⟩ (by simp; omega)
          have hcast : ((⟨j - 1, by omega⟩ : Fin N) : ℕ) + 1 = j := by simp; omega
          rwa [hcast] at this
      obtain ⟨r, hr⟩ := exists_extend_minor hg hj (⇑σ) hminj
      obtain ⟨t, rfl⟩ : ∃ t, σ t = r := ⟨σ.symm r, σ.apply_symm_apply r⟩
      have htj : j ≤ (t : ℕ) := by
        by_contra hlt
        push Not at hlt
        have htne : t ≠ jF := by
          intro hc
          have hval : ((⟨j, hj⟩ : Fin N) : ℕ) = j := rfl
          rw [hc] at hlt
          omega
        refine hr (leadingMinorMat_eq_zero_of_row_eq g htne (by omega) (by simp [hjF]) ?_)
        rw [Function.update_of_ne htne, Function.update_self]
      refine ⟨(Equiv.swap jF t).trans σ, ?_⟩
      have hagree : ∀ i : Fin N, (i : ℕ) < j + 1 →
          ((Equiv.swap jF t).trans σ) i = Function.update (⇑σ) jF (σ t) i := by
        intro i hi
        by_cases hij : i = jF
        · rw [hij, Equiv.trans_apply, Equiv.swap_apply_left, Function.update_self]
        · have hit : i ≠ t := by
            intro hc
            have ht1 : (t : ℕ) < j + 1 := by rw [← hc]; exact hi
            have ht2 : (t : ℕ) = j := by omega
            exact hij (by rw [hc]; exact Fin.ext ht2)
          rw [Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne hij hit,
            Function.update_of_ne hij]
      intro i hi
      rcases Nat.lt_or_ge (i : ℕ) j with hij | hij
      · rw [leadingMinorMat_congr_of_eq_below g (f' := ⇑σ) ?_]
        · exact hσ i hij
        · intro m hm
          rw [hagree m (by omega)]
          refine Function.update_of_ne ?_ _ _
          intro hc
          have hval : ((⟨j, hj⟩ : Fin N) : ℕ) = j := rfl
          rw [hc] at hm
          omega
      · have hij' : (i : ℕ) = j := by omega
        rw [leadingMinorMat_congr_of_eq_below g (f' := Function.update (⇑σ) jF (σ t))
          (fun m hm => hagree m (by omega)), hij']
        exact hr
  obtain ⟨σ, hσ⟩ := key N le_rfl
  exact ⟨σ, fun i => hσ i i.isLt⟩

end GaloisForLFunctions.HTGeometry.BorelWeil

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix

variable {N : ℕ} {k : Type*} [Field k]

/-- **The Bruhat factorization.**  Every invertible matrix becomes a product of a lower
unitriangular matrix and a Borel element after permuting its rows: this is the statement that the
`|W|` translates of the big cell cover the flag variety. -/
theorem exists_bruhat_factorization {g : Matrix (Fin N) (Fin N) k} (hg : g.det ≠ 0) :
    ∃ (σ : Equiv.Perm (Fin N)) (L B : Matrix (Fin N) (Fin N) k),
      IsLowerUni L ∧ IsBorelMat B ∧ g.submatrix σ id = L * B := by
  obtain ⟨σ, hσ⟩ := exists_perm_leadingMinor_ne_zero hg
  obtain ⟨L, B, hL, hB, hfac⟩ := exists_lu_of_leadingMinor_ne_zero (g.submatrix (⇑σ) id) hσ
  exact ⟨σ, L, B, hL, hB, hfac⟩

end GaloisForLFunctions.HTGeometry.BorelWeil
