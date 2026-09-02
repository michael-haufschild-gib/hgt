import GaloisForLFunctions.HTGeometry.MultiGradedNewtonModel
import GaloisForLFunctions.HTGeometry.JacobianDomainCriterion

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open HahnSeries

/-- Multidegree of the product of the first `k` Newton coordinates. -/
def mgPrefixDegree (N k : ℕ) : mgDeg N :=
  toLex fun j => if (j : ℕ) < k then (-1 : ℤ) else 0

@[simp] theorem ofLex_mgPrefixDegree (N k : ℕ) (j : Fin N) :
    ofLex (mgPrefixDegree N k) j = if (j : ℕ) < k then (-1 : ℤ) else 0 := rfl

/-- Gradient matrix of a family of Hahn-series observables. -/
def hahnGradientMatrix {N : ℕ} (f : Fin N → HahnSeries (mgDeg N) ℂ) :
    Matrix (Fin N) (Fin N) (HahnSeries (mgDeg N) ℂ) :=
  fun i j => mgPartial N j (f i)

/-- Boundary matrix of descending prefix monomials. -/
def hahnPrefixGradientLeadMatrix {N : ℕ} (c : Fin N → ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j => if (j : ℕ) < N - (i : ℕ) then -c i else 0

/-- Reversing rows turns the prefix boundary matrix into a lower triangle. -/
def hahnPrefixGradientLeadRowReversed {N : ℕ} (c : Fin N → ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j => hahnPrefixGradientLeadMatrix c i.rev j

def hahnFinRevPerm (N : ℕ) : Equiv.Perm (Fin N) :=
  Function.Involutive.toPerm (fun i => i.rev) (fun i => Fin.rev_rev i)

theorem hahnPrefixGradientLeadRowReversed_lower {N : ℕ} (c : Fin N → ℂ)
    (i j : Fin N) (hij : i < j) : hahnPrefixGradientLeadRowReversed c i j = 0 := by
  rw [hahnPrefixGradientLeadRowReversed, hahnPrefixGradientLeadMatrix]
  simp only [Fin.val_rev]
  rw [if_neg]
  omega

theorem hahnPrefixGradientLeadRowReversed_diag {N : ℕ} (c : Fin N → ℂ)
    (i : Fin N) : hahnPrefixGradientLeadRowReversed c i i = -c i.rev := by
  rw [hahnPrefixGradientLeadRowReversed, hahnPrefixGradientLeadMatrix]
  simp only [Fin.val_rev]
  rw [if_pos]
  omega

theorem hahnPrefixGradientLeadRowReversed_det_ne_zero {N : ℕ} (c : Fin N → ℂ)
    (hc : ∀ i, c i ≠ 0) : (hahnPrefixGradientLeadRowReversed c).det ≠ 0 := by
  rw [Matrix.det_of_lowerTriangular _
    (hahnPrefixGradientLeadRowReversed_lower c)]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => by
    rw [hahnPrefixGradientLeadRowReversed_diag]
    exact neg_ne_zero.mpr (hc i.rev)

theorem hahnPrefixGradientLeadMatrix_det_ne_zero {N : ℕ} (c : Fin N → ℂ)
    (hc : ∀ i, c i ≠ 0) : (hahnPrefixGradientLeadMatrix c).det ≠ 0 := by
  intro hzero
  apply hahnPrefixGradientLeadRowReversed_det_ne_zero c hc
  have hrev : hahnPrefixGradientLeadRowReversed c =
      (hahnPrefixGradientLeadMatrix c).submatrix (hahnFinRevPerm N) id := by
    funext i j
    rfl
  rw [hrev, Matrix.det_permute, hzero, mul_zero]

/-- **Puiseux/Hahn prefix-gradient staircase.**

If row `i` has a nonzero leading term equal to the product of the first `N-i` independent
coordinates, then the matrix of all coordinate derivatives is nonsingular. Lower Hahn terms are
allowed without restriction. -/
theorem hahnGradientMatrix_det_ne_zero_of_prefix_leads {N : ℕ}
    (f : Fin N → HahnSeries (mgDeg N) ℂ) (c : Fin N → ℂ)
    (hc : ∀ i, c i ≠ 0)
    (hf : ∀ i, HasLeadAt (f i) (mgPrefixDegree N (N - (i : ℕ))) (c i)) :
    (hahnGradientMatrix f).det ≠ 0 := by
  refine det_ne_zero_of_hasLeadAt (hahnGradientMatrix f)
    (fun i => mgPrefixDegree N (N - (i : ℕ))) (fun j => mgStep N j)
    (hahnPrefixGradientLeadMatrix c) ?_
    (hahnPrefixGradientLeadMatrix_det_ne_zero c hc)
  intro i j
  have h := hasLeadAt_mgPartial (j := j) (hf i)
  rw [ofLex_mgPrefixDegree] at h
  by_cases hj : (j : ℕ) < N - (i : ℕ)
  · simpa [hahnGradientMatrix, hahnPrefixGradientLeadMatrix, hj] using h
  · simpa [hahnGradientMatrix, hahnPrefixGradientLeadMatrix, hj] using h

/-! ## Cascade output followed by logarithmic derivatives -/

/-- Degrees of the terminal output followed by the descending-prefix logarithmic derivatives in a
product cascade. -/
def mgCascadeObservableDegree (n : ℕ) (i : Fin (n + 1)) : mgDeg (n + 1) :=
  if i = 0 then mgUnit (n + 1) (Fin.last n)
  else mgPrefixDegree (n + 1) (n + 1 - (i : ℕ))

@[simp] theorem mgCascadeObservableDegree_zero (n : ℕ) :
    mgCascadeObservableDegree n 0 = mgUnit (n + 1) (Fin.last n) := by
  simp [mgCascadeObservableDegree]

@[simp] theorem mgCascadeObservableDegree_succ (n : ℕ) (i : Fin n) :
    mgCascadeObservableDegree n i.succ = mgPrefixDegree (n + 1) (n - (i : ℕ)) := by
  simp only [mgCascadeObservableDegree, Fin.succ_ne_zero, ↓reduceIte, Fin.val_succ]
  congr 1
  omega

/-- Boundary matrix for the terminal output followed by descending-prefix logarithmic
derivatives. -/
def hahnCascadeGradientLeadMatrix {n : ℕ} (c : Fin (n + 1) → ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  fun i j => if i = 0 then (if j = Fin.last n then -c i else 0)
    else if (j : ℕ) < n + 1 - (i : ℕ) then -c i else 0

/-- Reversing columns makes the cascade boundary matrix upper triangular. -/
def hahnCascadeGradientLeadColumnReversed {n : ℕ} (c : Fin (n + 1) → ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  fun i j => hahnCascadeGradientLeadMatrix c i j.rev

theorem hahnCascadeGradientLeadColumnReversed_upper {n : ℕ}
    (c : Fin (n + 1) → ℂ) (i j : Fin (n + 1)) (hji : j < i) :
    hahnCascadeGradientLeadColumnReversed c i j = 0 := by
  by_cases hi : i = 0
  · subst i
    exact (Fin.not_lt_zero j hji).elim
  · rw [hahnCascadeGradientLeadColumnReversed, hahnCascadeGradientLeadMatrix, if_neg hi,
      if_neg]
    simp only [Fin.val_rev]
    omega

theorem hahnCascadeGradientLeadColumnReversed_diag {n : ℕ}
    (c : Fin (n + 1) → ℂ) (i : Fin (n + 1)) :
    hahnCascadeGradientLeadColumnReversed c i i = -c i := by
  by_cases hi : i = 0
  · subst i
    simp [hahnCascadeGradientLeadColumnReversed, hahnCascadeGradientLeadMatrix]
  · rw [hahnCascadeGradientLeadColumnReversed, hahnCascadeGradientLeadMatrix, if_neg hi,
      if_pos]
    simp only [Fin.val_rev]
    omega

theorem hahnCascadeGradientLeadColumnReversed_det_ne_zero {n : ℕ}
    (c : Fin (n + 1) → ℂ) (hc : ∀ i, c i ≠ 0) :
    (hahnCascadeGradientLeadColumnReversed c).det ≠ 0 := by
  rw [Matrix.det_of_upperTriangular
    (hahnCascadeGradientLeadColumnReversed_upper c)]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => by
    rw [hahnCascadeGradientLeadColumnReversed_diag]
    exact neg_ne_zero.mpr (hc i)

theorem hahnCascadeGradientLeadMatrix_det_ne_zero {n : ℕ}
    (c : Fin (n + 1) → ℂ) (hc : ∀ i, c i ≠ 0) :
    (hahnCascadeGradientLeadMatrix c).det ≠ 0 := by
  intro hzero
  apply hahnCascadeGradientLeadColumnReversed_det_ne_zero c hc
  have hrev : hahnCascadeGradientLeadColumnReversed c =
      (hahnCascadeGradientLeadMatrix c).submatrix id (hahnFinRevPerm (n + 1)) := by
    funext i j
    rfl
  rw [hrev, Matrix.det_permute', hzero, mul_zero]

/-- **Hahn cascade-gradient staircase.** If `f 0` is terminal-coordinate shaped and each following
row has a nonzero leading term equal to the successively shorter prefix product, then the matrix of
all coordinate derivatives is nonsingular. Arbitrary strictly higher Hahn terms are retained. -/
theorem hahnGradientMatrix_det_ne_zero_of_cascade_leads {n : ℕ}
    (f : Fin (n + 1) → HahnSeries (mgDeg (n + 1)) ℂ)
    (c : Fin (n + 1) → ℂ) (hc : ∀ i, c i ≠ 0)
    (hf : ∀ i, HasLeadAt (f i) (mgCascadeObservableDegree n i) (c i)) :
    (hahnGradientMatrix f).det ≠ 0 := by
  refine det_ne_zero_of_hasLeadAt (hahnGradientMatrix f)
    (mgCascadeObservableDegree n) (fun j => mgStep (n + 1) j)
    (hahnCascadeGradientLeadMatrix c) ?_
    (hahnCascadeGradientLeadMatrix_det_ne_zero c hc)
  intro i j
  have h := hasLeadAt_mgPartial (j := j) (hf i)
  by_cases hi : i = 0
  · subst i
    rw [mgCascadeObservableDegree_zero] at h
    by_cases hj : j = Fin.last n
    · subst j
      simpa [hahnGradientMatrix, hahnCascadeGradientLeadMatrix, mgUnit] using h
    · simpa [hahnGradientMatrix, hahnCascadeGradientLeadMatrix, mgUnit, hj] using h
  · rw [mgCascadeObservableDegree, if_neg hi, ofLex_mgPrefixDegree] at h
    rw [mgCascadeObservableDegree, if_neg hi]
    by_cases hj : (j : ℕ) < n + 1 - (i : ℕ)
    · simpa [hahnGradientMatrix, hahnCascadeGradientLeadMatrix, hi, hj] using h
    · simpa [hahnGradientMatrix, hahnCascadeGradientLeadMatrix, hi, hj] using h

/-! ## Algebraic-independence conclusion -/

theorem hahnGrade_algebraMap_complex {N : ℕ} (j : Fin N) (c : ℂ) :
    hahnGrade (mgComp N j) (algebraMap ℂ (HahnSeries (mgDeg N) ℂ) c) = 0 := by
  ext d
  by_cases hd : d = 0
  · subst d
    simp [HahnSeries.algebraMap_apply]
  · simp [HahnSeries.algebraMap_apply, HahnSeries.C_apply,
      HahnSeries.coeff_single_of_ne hd]

theorem mgPartial_algebraMap_complex {N : ℕ} (j : Fin N) (c : ℂ) :
    mgPartial N j (algebraMap ℂ (HahnSeries (mgDeg N) ℂ) c) = 0 := by
  change mgShift N j *
      hahnGrade (mgComp N j) (algebraMap ℂ (HahnSeries (mgDeg N) ℂ) c) = 0
  rw [hahnGrade_algebraMap_complex, mul_zero]

/-- A nonzero Hahn gradient determinant gives algebraic independence over the coefficient field. -/
theorem algebraicIndependent_of_hahnGradientMatrix_det_ne_zero {N : ℕ}
    (f : Fin N → HahnSeries (mgDeg N) ℂ)
    (hdet : (hahnGradientMatrix f).det ≠ 0) :
    AlgebraicIndependent ℂ f := by
  let M : Matrix (Fin N) (Fin N) (HahnSeries (mgDeg N) ℂ) :=
    Matrix.transpose (hahnGradientMatrix f)
  have hM : M.det ≠ 0 := by
    simpa [M, Matrix.det_transpose] using hdet
  refine algebraicIndependent_of_domain_jacobian f
    (fun i => mgPartial N i) ?_ ?_ ?_ M hM ?_
  · intro i a b
    exact map_add (mgPartial N i) a b
  · intro i a b
    simpa only [smul_eq_mul, add_comm, mul_comm] using (mgPartial N i).leibniz a b
  · intro i c
    exact mgPartial_algebraMap_complex i c
  · intro i j
    rfl

/-- **Algebraic independence of a Hahn cascade observable chain.** Terminal-coordinate leading
output and the successive nonzero prefix-product leads force algebraic independence over `ℂ`. -/
theorem algebraicIndependent_hahnCascade_of_leads {n : ℕ}
    (f : Fin (n + 1) → HahnSeries (mgDeg (n + 1)) ℂ)
    (c : Fin (n + 1) → ℂ) (hc : ∀ i, c i ≠ 0)
    (hf : ∀ i, HasLeadAt (f i) (mgCascadeObservableDegree n i) (c i)) :
    AlgebraicIndependent ℂ f :=
  algebraicIndependent_of_hahnGradientMatrix_det_ne_zero f
    (hahnGradientMatrix_det_ne_zero_of_cascade_leads f c hc hf)

end GaloisForLFunctions.HTGeometry
