import GaloisForLFunctions.HTGeometry.DeterminantalJacobi

/-!
# The generic determinantal stratification is singular exactly on the deeper stratum

For a square matrix of independent variables, differentiating a `(t+1)`-minor in the entry at its
last chosen row and column returns exactly the `t`-minor obtained by deleting them.  Hence at a
point where some `t`-minor is nonzero, some partial derivative of some `(t+1)`-minor is nonzero:
the singular locus of the rank-`t` locus is contained in the rank-`(t−1)` locus.

Together with `DeterminantalJacobi.pderiv_det_submatrix_eval_eq_zero`, which gives the reverse
containment, this is the classical statement `Sing(C_k) = C_{k+1}` for generic determinantal
varieties.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset

variable {K : Type*} [CommRing K] {N : ℕ}

/-- The generic square matrix of independent variables. -/
noncomputable def genericVarMatrix (K : Type*) [CommRing K] (N : ℕ) :
    Matrix (Fin N) (Fin N) (MvPolynomial (Fin N × Fin N) K) :=
  Matrix.of fun i j => MvPolynomial.X (i, j)

theorem genericVarMatrix_apply (K : Type*) [CommRing K] (N : ℕ) (i j : Fin N) :
    genericVarMatrix K N i j = MvPolynomial.X (i, j) := rfl

/-- Differentiating a generic `(t+1)`-minor in the entry at the last chosen row and column returns
the `t`-minor obtained by deleting them. -/
theorem pderiv_det_genericVarMatrix_snoc {t : ℕ}
    (I₀ m₀ : Fin t → Fin N) {a b : Fin N}
    (hI : ∀ k, I₀ k ≠ a) (hm : ∀ l, m₀ l ≠ b) :
    MvPolynomial.pderiv (a, b)
        ((genericVarMatrix K N).submatrix (Fin.snoc I₀ a) (Fin.snoc m₀ b)).det
      = ((genericVarMatrix K N).submatrix I₀ m₀).det := by
  classical
  set A := (genericVarMatrix K N).submatrix (Fin.snoc I₀ a) (Fin.snoc m₀ b) with hA
  have hIsnoc : ∀ k : Fin (t + 1), (Fin.snoc I₀ a : Fin (t + 1) → Fin N) k = a ↔ k = Fin.last t := by
    intro k
    refine Fin.lastCases ?_ ?_ k
    · simp
    · intro l
      rw [Fin.snoc_castSucc]
      constructor
      · intro h; exact absurd h (hI l)
      · intro h; exact absurd h (by exact Fin.castSucc_ne_last l)
  have hmsnoc : ∀ l : Fin (t + 1), (Fin.snoc m₀ b : Fin (t + 1) → Fin N) l = b ↔ l = Fin.last t := by
    intro l
    refine Fin.lastCases ?_ ?_ l
    · simp
    · intro j
      rw [Fin.snoc_castSucc]
      constructor
      · intro h; exact absurd h (hm j)
      · intro h; exact absurd h (by exact Fin.castSucc_ne_last j)
  have hrow_last : (fun l => (MvPolynomial.pderiv (a, b)) (A (Fin.last t) l))
      = (Pi.single (Fin.last t) 1 : Fin (t + 1) → MvPolynomial (Fin N × Fin N) K) := by
    funext l
    have hIk : (Fin.snoc I₀ a : Fin (t + 1) → Fin N) (Fin.last t) = a := by simp
    rw [hA, Matrix.submatrix_apply, genericVarMatrix_apply, MvPolynomial.pderiv_X,
      Pi.single_apply, Pi.single_apply, hIk]
    by_cases hl : l = Fin.last t
    · subst hl
      have hml : (Fin.snoc m₀ b : Fin (t + 1) → Fin N) (Fin.last t) = b := by simp
      rw [if_pos (by rw [hml]), if_pos rfl]
    · have hml : (Fin.snoc m₀ b : Fin (t + 1) → Fin N) l ≠ b := fun h => hl ((hmsnoc l).mp h)
      rw [if_neg (by intro h; exact hml (congrArg Prod.snd h)), if_neg hl]
  have hrow_other : ∀ k : Fin (t + 1), k ≠ Fin.last t →
      (fun l => (MvPolynomial.pderiv (a, b)) (A k l))
        = (0 : Fin (t + 1) → MvPolynomial (Fin N × Fin N) K) := by
    intro k hk
    funext l
    have hIk : (Fin.snoc I₀ a : Fin (t + 1) → Fin N) k ≠ a := fun h => hk ((hIsnoc k).mp h)
    rw [hA, Matrix.submatrix_apply, genericVarMatrix_apply, MvPolynomial.pderiv_X,
      Pi.single_apply]
    rw [if_neg (by intro h; exact hIk (congrArg Prod.fst h))]
    rfl
  rw [derivation_det]
  rw [Finset.sum_eq_single (Fin.last t)]
  · rw [hrow_last]
    have hexp := Matrix.det_succ_row (A.updateRow (Fin.last t) (Pi.single (Fin.last t) 1))
      (Fin.last t)
    rw [hexp, Finset.sum_eq_single (Fin.last t)]
    · have hone : (A.updateRow (Fin.last t) (Pi.single (Fin.last t) 1)) (Fin.last t)
          (Fin.last t) = 1 := by
        rw [Matrix.updateRow_apply, if_pos rfl, Pi.single_apply, if_pos rfl]
      rw [hone, mul_one]
      have hsub : (A.updateRow (Fin.last t) (Pi.single (Fin.last t) 1)).submatrix
          (Fin.last t).succAbove (Fin.last t).succAbove
          = (genericVarMatrix K N).submatrix I₀ m₀ := by
        funext p q
        have hne : (Fin.last t).succAbove p ≠ Fin.last t := Fin.succAbove_ne _ p
        rw [Matrix.submatrix_apply, Matrix.updateRow_apply, if_neg hne, hA,
          Matrix.submatrix_apply]
        simp [Fin.succAbove_last, Fin.snoc_castSucc, Matrix.submatrix_apply]
      rw [hsub]
      simp
    · intro j _ hj
      have hz : (A.updateRow (Fin.last t) (Pi.single (Fin.last t) 1)) (Fin.last t) j = 0 := by
        rw [Matrix.updateRow_apply, if_pos rfl, Pi.single_apply, if_neg hj]
      rw [hz]
      ring
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro k _ hk
    rw [hrow_other k hk]
    refine Matrix.det_eq_zero_of_row_eq_zero k fun j => ?_
    rw [Matrix.updateRow_self]
    rfl
  · intro h; exact absurd (Finset.mem_univ _) h

theorem exists_notMem_range {t : ℕ} (hN : t < N) (f : Fin t → Fin N) :
    ∃ a : Fin N, ∀ k, f k ≠ a := by
  classical
  have hcard : (Finset.image f (Finset.univ : Finset (Fin t))).card
      < (Finset.univ : Finset (Fin N)).card := by
    calc (Finset.image f (Finset.univ : Finset (Fin t))).card
        ≤ (Finset.univ : Finset (Fin t)).card := Finset.card_image_le
      _ = t := by simp
      _ < N := hN
      _ = (Finset.univ : Finset (Fin N)).card := by simp
  have hne : Finset.image f (Finset.univ : Finset (Fin t)) ≠ Finset.univ := fun h => by
    rw [h] at hcard; omega
  rw [Ne, Finset.eq_univ_iff_forall] at hne
  push Not at hne
  obtain ⟨a, ha⟩ := hne
  refine ⟨a, fun k hk => ha ?_⟩
  exact Finset.mem_image.mpr ⟨k, Finset.mem_univ k, hk⟩

/-- **The generic determinantal stratum is smooth off the deeper stratum.**  If some `t`-minor is
nonzero at a point, then some partial derivative of some `(t+1)`-minor is nonzero there: the
singular locus of the rank-`t` locus is contained in the rank-`(t−1)` locus. -/
theorem exists_pderiv_det_ne_zero_of_minor_ne_zero {t : ℕ} (hN : t < N)
    (x : Fin N × Fin N → K) (I₀ m₀ : Fin t → Fin N)
    (h : MvPolynomial.eval x (((genericVarMatrix K N).submatrix I₀ m₀).det) ≠ 0) :
    ∃ (I m : Fin (t + 1) → Fin N) (i : Fin N × Fin N),
      MvPolynomial.eval x
        (MvPolynomial.pderiv i (((genericVarMatrix K N).submatrix I m).det)) ≠ 0 := by
  obtain ⟨a, ha⟩ := exists_notMem_range hN I₀
  obtain ⟨b, hb⟩ := exists_notMem_range hN m₀
  refine ⟨Fin.snoc I₀ a, Fin.snoc m₀ b, (a, b), ?_⟩
  rw [pderiv_det_genericVarMatrix_snoc I₀ m₀ ha hb]
  exact h


end GaloisForLFunctions.HTGeometry
