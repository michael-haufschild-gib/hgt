import Mathlib

/-!
# The Leibniz jet matrix of multiplication by a fixed function

Multiplying by a fixed smooth function acts on finite jets by a lower triangular matrix whose
diagonal is the value of that function.  At a point where the fixed function does not vanish, the
action on jets is therefore a linear isomorphism.

This is the derivative of the gauge-to-jet map of a divisor-fixed family `W · exp(g)`: perturbing
`g` in a direction `q` multiplies the source by `q`, so the derivative of the jet map is
multiplication by the source followed by the jet isomorphism of the perturbation.  Only the Leibniz
rule is involved; no Bell polynomial expansion of `(exp g)` is needed.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The coefficient of the `j`-th jet in the `l`-th jet of a product with a fixed factor. -/
def leibnizJetCoeff (Fj : ℕ → ℂ) (l j : ℕ) : ℂ :=
  if j ≤ l then (Nat.choose l j : ℂ) * Fj (l - j) else 0

/-- The matrix by which multiplication by a fixed function acts on jets of order below `m`. -/
def leibnizJetMatrix (m : ℕ) (Fj : ℕ → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  fun l j => leibnizJetCoeff Fj (l : ℕ) (j : ℕ)

theorem leibnizJetMatrix_blockTriangular (m : ℕ) (Fj : ℕ → ℂ) :
    (leibnizJetMatrix m Fj).BlockTriangular (⇑OrderDual.toDual) := by
  intro i j hij
  have hlt : (i : Fin m) < j := by simpa using hij
  have hnot : ¬ ((j : ℕ) ≤ (i : ℕ)) := by
    intro h
    exact absurd (Fin.le_def.mpr h) (not_le.mpr hlt)
  rw [leibnizJetMatrix, leibnizJetCoeff, if_neg hnot]

/-- **The Leibniz jet matrix is lower triangular with constant diagonal the function value.** -/
theorem det_leibnizJetMatrix (m : ℕ) (Fj : ℕ → ℂ) :
    (leibnizJetMatrix m Fj).det = (Fj 0) ^ m := by
  rw [Matrix.det_of_lowerTriangular _ (leibnizJetMatrix_blockTriangular m Fj)]
  have hdiag : ∀ l : Fin m, leibnizJetMatrix m Fj l l = Fj 0 := by
    intro l
    rw [leibnizJetMatrix, leibnizJetCoeff, if_pos (le_refl (l : ℕ)), Nat.choose_self,
      Nat.sub_self]
    norm_num
  rw [Finset.prod_congr rfl fun l _ => hdiag l, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- **Multiplication by a nonvanishing function is an isomorphism on jets.** -/
theorem det_leibnizJetMatrix_ne_zero (m : ℕ) {Fj : ℕ → ℂ} (h : Fj 0 ≠ 0) :
    (leibnizJetMatrix m Fj).det ≠ 0 := by
  rw [det_leibnizJetMatrix]
  exact pow_ne_zero m h

/-- **The jets of a product are the Leibniz matrix applied to the jets of the second factor.** -/
theorem iteratedDeriv_mul_eq_leibnizJetMatrix {F q : ℂ → ℂ} {x : ℂ} (m : ℕ)
    (hF : ContDiffAt ℂ (m : ℕ) F x) (hq : ContDiffAt ℂ (m : ℕ) q x) (l : Fin m) :
    iteratedDeriv (l : ℕ) (fun z => F z * q z) x
      = ∑ j : Fin m, leibnizJetMatrix m (fun r => iteratedDeriv r F x) l j
          * iteratedDeriv (j : ℕ) q x := by
  classical
  have hle : ((l : ℕ) : WithTop ℕ∞) ≤ (m : ℕ) := by
    exact_mod_cast (Nat.cast_le.mpr (le_of_lt l.2) : ((l : ℕ) : ℕ∞) ≤ (m : ℕ∞))
  have hFl : ContDiffAt ℂ ((l : ℕ) : ℕ) F x := hF.of_le hle
  have hql : ContDiffAt ℂ ((l : ℕ) : ℕ) q x := hq.of_le hle
  have hmul : (fun z => F z * q z) = F * q := rfl
  rw [hmul, iteratedDeriv_mul hFl hql]
  set Fj : ℕ → ℂ := fun r => iteratedDeriv r F x with hFj
  set qj : ℕ → ℂ := fun r => iteratedDeriv r q x with hqj
  have hRHS : (∑ j : Fin m, leibnizJetMatrix m Fj l j * qj (j : ℕ))
      = ∑ j ∈ Finset.range m, leibnizJetCoeff Fj (l : ℕ) j * qj j :=
    Fin.sum_univ_eq_sum_range (fun j => leibnizJetCoeff Fj (l : ℕ) j * qj j) m
  rw [hRHS]
  have hsub : Finset.range ((l : ℕ) + 1) ⊆ Finset.range m := by
    intro j hj
    rw [Finset.mem_range] at hj ⊢
    omega
  rw [← Finset.sum_subset hsub (fun j _ hj => by
    rw [Finset.mem_range] at hj
    rw [leibnizJetCoeff, if_neg (by omega), zero_mul])]
  refine Finset.sum_nbij' (fun i => (l : ℕ) - i) (fun j => (l : ℕ) - j) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_range] at hi ⊢
    omega
  · intro j hj
    rw [Finset.mem_range] at hj ⊢
    omega
  · intro i hi
    rw [Finset.mem_range] at hi
    omega
  · intro j hj
    rw [Finset.mem_range] at hj
    omega
  · intro i hi
    rw [Finset.mem_range] at hi
    have hsub2 : (l : ℕ) - ((l : ℕ) - i) = i := by omega
    rw [leibnizJetCoeff, if_pos (by omega), hsub2, Nat.choose_symm (by omega)]

end

end GaloisForLFunctions.HTGeometry
