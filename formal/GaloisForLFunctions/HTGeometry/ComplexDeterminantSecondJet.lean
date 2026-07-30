import GaloisForLFunctions.HTGeometry.ParametricSpectralBranch
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Complex determinant second jets

This module differentiates a finite complex determinant through its Leibniz
expansion.  The local theorem is stated with neighbourhood hypotheses so it
can be applied directly to analytic eigenvalue branches, which are only
specified as germs.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- First derivative of a complex determinant as a polynomial in its value
and entrywise first derivative. -/
def complexDetFirstJet {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A A₁ : Matrix ι ι ℂ) : ℂ :=
  ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) *
    ∑ i : ι, (∏ j ∈ Finset.univ.erase i, A (σ j) j) * A₁ (σ i) i

private def complexDetFirstJetDerivative
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A dA B dB : Matrix ι ι ℂ) : ℂ :=
  ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) *
    ∑ i : ι,
      ((∑ j ∈ Finset.univ.erase i,
          (∏ k ∈ (Finset.univ.erase i).erase j, A (σ k) k) *
            dA (σ j) j) *
        B (σ i) i +
        (∏ j ∈ Finset.univ.erase i, A (σ j) j) * dB (σ i) i)

/-- Second derivative of a complex determinant as a polynomial in its
entrywise matrix two-jet. -/
def complexDetSecondJet {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A A₁ A₂ : Matrix ι ι ℂ) : ℂ :=
  complexDetFirstJetDerivative A A₁ A₁ A₂

/-- Entrywise complex derivatives determine the derivative of a matrix
determinant. -/
theorem hasDerivAt_complexMatrixDet
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ℂ → Matrix ι ι ℂ) (A₁ : Matrix ι ι ℂ) (x : ℂ)
    (hA : ∀ i j, HasDerivAt (fun t => A t i j) (A₁ i j) x) :
    HasDerivAt (fun t => (A t).det) (complexDetFirstJet (A x) A₁) x := by
  rw [show (fun t => (A t).det) = fun t =>
      ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∏ i, A t (σ i) i by
    funext t
    exact Matrix.det_apply' (A t)]
  unfold complexDetFirstJet
  apply HasDerivAt.fun_sum
  intro σ hσ
  convert! ((HasDerivAt.fun_finsetProd fun i hi => hA (σ i) i).const_mul
    (((Equiv.Perm.sign σ : ℤ) : ℂ))) using 1

/-- The cofactor column used to expand along a row is independent of that
row. -/
private theorem adjugate_updateRow_same_col_complex
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (i j : ι) (v : ι → ℂ) :
    (A.updateRow i v).adjugate j i = A.adjugate j i := by
  rw [Matrix.adjugate_apply, Matrix.adjugate_apply]
  congr 1
  ext r c
  by_cases hr : r = i
  · subst r
    simp [Matrix.updateRow]
  · simp [Matrix.updateRow, hr]

/-- The cofactor row used to expand along a column is independent of that
column. -/
private theorem adjugate_updateCol_same_row_complex
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (i j : ι) (v : ι → ℂ) :
    (A.updateCol i v).adjugate i j = A.adjugate i j := by
  calc
    (A.updateCol i v).adjugate i j =
        ((A.updateCol i v).adjugate.transpose) j i := rfl
    _ = ((A.updateCol i v).transpose.adjugate) j i := by
      rw [Matrix.adjugate_transpose]
    _ = (A.transpose.updateRow i v).adjugate j i := by
      rw [← Matrix.updateRow_transpose]
    _ = A.transpose.adjugate j i :=
      adjugate_updateRow_same_col_complex A.transpose i j v
    _ = A.adjugate i j := by
      rw [← Matrix.adjugate_transpose]
      rfl

/-- Expanding after replacing column `i` uses the corresponding row of the
original adjugate. -/
private theorem det_updateCol_eq_sum_mul_adjugate_complex
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (i : ι) (v : ι → ℂ) :
    (A.updateCol i v).det = ∑ j, v j * A.adjugate i j := by
  rw [Matrix.det_eq_sum_mul_adjugate_col (A.updateCol i v) i]
  congr 1
  ext j
  rw [adjugate_updateCol_same_row_complex A i j v]
  simp [Matrix.updateCol]

/-- Jacobi's first-variation formula in adjugate form, including singular
matrices. -/
theorem complexDetFirstJet_eq_adjugate_trace
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) :
    complexDetFirstJet A B = (A.adjugate * B).trace := by
  have hcolumns :
      complexDetFirstJet A B =
        ∑ i, (A.updateCol i (fun j => B j i)).det := by
    unfold complexDetFirstJet
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Matrix.det_apply']
    apply Finset.sum_congr rfl
    intro σ hσ
    congr 1
    rw [← Finset.mul_prod_erase Finset.univ
      (fun j => (A.updateCol i (fun r => B r i)) (σ j) j)
      (Finset.mem_univ i)]
    rw [Matrix.updateCol_self]
    rw [mul_comm]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    rw [Matrix.updateCol_ne (Finset.ne_of_mem_erase hj)]
  rw [hcolumns, Matrix.trace]
  apply Finset.sum_congr rfl
  intro i hi
  rw [det_updateCol_eq_sum_mul_adjugate_complex]
  simp only [Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- At a diagonal matrix with one prescribed zero, only that diagonal entry
of the perturbation contributes to the first determinant jet. -/
theorem complexDetFirstJet_diagonal_single_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℂ) (B : Matrix ι ι ℂ) (x : ι)
    (hdx : d x = 0) :
    complexDetFirstJet (Matrix.diagonal d) B =
      (∏ j ∈ Finset.univ.erase x, d j) * B x x := by
  rw [complexDetFirstJet_eq_adjugate_trace,
    Matrix.adjugate_diagonal, Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply]
  rw [Finset.sum_eq_single x]
  · rw [Finset.sum_eq_single x]
    · rw [Matrix.diagonal_apply_eq]
    · intro j hj hjx
      rw [Matrix.diagonal_apply_ne _ hjx.symm]
      simp
    · intro hx'
      exact absurd (Finset.mem_univ x) hx'
  · intro i hi hix
    rw [Finset.sum_eq_single i]
    · rw [Matrix.diagonal_apply_eq]
      apply mul_eq_zero_of_left
      apply Finset.prod_eq_zero
        (Finset.mem_erase.mpr
          ⟨fun h => hix h.symm, Finset.mem_univ x⟩)
      exact hdx
    · intro j hj hji
      rw [Matrix.diagonal_apply_ne _ hji.symm]
      simp
    · intro hi'
      exact absurd (Finset.mem_univ i) hi'
  · intro hx
    exact absurd (Finset.mem_univ x) hx

/-- Differentiating the first determinant jet produces the second determinant
jet. -/
theorem hasDerivAt_complexDetFirstJet
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A A₁ : ℂ → Matrix ι ι ℂ) (A₂ : Matrix ι ι ℂ) (x : ℂ)
    (hA : ∀ i j, HasDerivAt (fun t => A t i j) (A₁ x i j) x)
    (hA₁ : ∀ i j, HasDerivAt (fun t => A₁ t i j) (A₂ i j) x) :
    HasDerivAt (fun t => complexDetFirstJet (A t) (A₁ t))
      (complexDetSecondJet (A x) (A₁ x) A₂) x := by
  unfold complexDetFirstJet complexDetSecondJet
    complexDetFirstJetDerivative
  apply HasDerivAt.fun_sum
  intro σ hσ
  apply HasDerivAt.const_mul
  apply HasDerivAt.fun_sum
  intro i hi
  exact (HasDerivAt.fun_finsetProd fun j hj => hA (σ j) j).mul
    (hA₁ (σ i) i)

/-- The literal second derivative of a complex determinant is its algebraic
second jet.  Only a neighbourhood two-jet is needed. -/
theorem complexDet_secondDerivative_eq_jet
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A A₁ : ℂ → Matrix ι ι ℂ) (A₂ : Matrix ι ι ℂ) (x : ℂ)
    (hA :
      ∀ᶠ t in 𝓝 x,
        ∀ i j, HasDerivAt (fun s => A s i j) (A₁ t i j) t)
    (hA₁ : ∀ i j, HasDerivAt (fun t => A₁ t i j) (A₂ i j) x) :
    deriv (deriv (fun t => (A t).det)) x =
      complexDetSecondJet (A x) (A₁ x) A₂ := by
  have hderiv :
      (fun t => deriv (fun s => (A s).det) t) =ᶠ[𝓝 x]
        fun t => complexDetFirstJet (A t) (A₁ t) := by
    filter_upwards [hA] with t ht
    exact (hasDerivAt_complexMatrixDet A (A₁ t) t ht).deriv
  have hsecond :=
    hasDerivAt_complexDetFirstJet A A₁ A₂ x
      (mem_of_mem_nhds hA)
      hA₁
  exact (hsecond.congr_of_eventuallyEq hderiv).deriv

/-! ## Characteristic branches -/

/-- Characteristic matrix along an affine spectral branch. -/
def affineBranchCharacteristicMatrix
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (energy : ι → ℂ) (V : Matrix ι ι ℂ) (branch : ℂ → ℂ)
    (g : ℂ) : Matrix ι ι ℂ :=
  Matrix.scalar ι (branch g) - Matrix.diagonal energy - g • V

/-- Entrywise first derivative of the affine branch characteristic matrix. -/
def affineBranchCharacteristicMatrixFirstJet
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : Matrix ι ι ℂ) (branch : ℂ → ℂ)
    (g : ℂ) : Matrix ι ι ℂ :=
  Matrix.scalar ι (deriv branch g) - V

/-- Entrywise second derivative of the affine branch characteristic matrix. -/
def affineBranchCharacteristicMatrixSecondJet
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (branch : ℂ → ℂ) (g : ℂ) : Matrix ι ι ℂ :=
  Matrix.scalar ι (deriv (deriv branch) g)

@[simp] theorem affineBranchCharacteristicMatrix_apply_same
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (energy : ι → ℂ) (V : Matrix ι ι ℂ) (branch : ℂ → ℂ)
    (g : ℂ) (i : ι) :
    affineBranchCharacteristicMatrix energy V branch g i i =
      branch g - energy i - g * V i i := by
  simp [affineBranchCharacteristicMatrix, Matrix.scalar_apply]

@[simp] theorem affineBranchCharacteristicMatrix_apply_ne
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (energy : ι → ℂ) (V : Matrix ι ι ℂ) (branch : ℂ → ℂ)
    (g : ℂ) {i j : ι} (hij : i ≠ j) :
    affineBranchCharacteristicMatrix energy V branch g i j =
      -(g * V i j) := by
  simp [affineBranchCharacteristicMatrix, Matrix.scalar_apply, hij]

@[simp] theorem affineBranchCharacteristicMatrixFirstJet_apply_same
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : Matrix ι ι ℂ) (branch : ℂ → ℂ) (g : ℂ) (i : ι) :
    affineBranchCharacteristicMatrixFirstJet V branch g i i =
      deriv branch g - V i i := by
  simp [affineBranchCharacteristicMatrixFirstJet, Matrix.scalar_apply]

@[simp] theorem affineBranchCharacteristicMatrixFirstJet_apply_ne
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : Matrix ι ι ℂ) (branch : ℂ → ℂ) (g : ℂ)
    {i j : ι} (hij : i ≠ j) :
    affineBranchCharacteristicMatrixFirstJet V branch g i j =
      -V i j := by
  simp [affineBranchCharacteristicMatrixFirstJet, Matrix.scalar_apply, hij]

/-- An actual analytic characteristic-root branch has zero determinant
second jet.  This is the assumption-free analytic-to-algebraic bridge used by
second-order spectral perturbation. -/
theorem affineEigenbranch_complexDetSecondJet_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (energy : ι → ℂ) (V : Matrix ι ι ℂ) (branch : ℂ → ℂ)
    (hbranch : AnalyticAt ℂ branch 0)
    (hroot :
      ∀ᶠ g in 𝓝 0,
        matrixCharpolyRelation
          (Matrix.diagonal energy + g • V, branch g) = 0) :
    complexDetSecondJet
        (affineBranchCharacteristicMatrix energy V branch 0)
        (affineBranchCharacteristicMatrixFirstJet V branch 0)
        (affineBranchCharacteristicMatrixSecondJet branch 0) = 0 := by
  let A := affineBranchCharacteristicMatrix energy V branch
  let A₁ := affineBranchCharacteristicMatrixFirstJet V branch
  let A₂ : Matrix ι ι ℂ :=
    affineBranchCharacteristicMatrixSecondJet branch 0
  have hA :
      ∀ᶠ t in 𝓝 (0 : ℂ),
        ∀ i j, HasDerivAt (fun s => A s i j) (A₁ t i j) t := by
    filter_upwards [hbranch.eventually_analyticAt] with t ht
    intro i j
    by_cases hij : i = j
    · subst j
      simp only [A, A₁,
        affineBranchCharacteristicMatrix_apply_same,
        affineBranchCharacteristicMatrixFirstJet_apply_same]
      simpa only [Pi.sub_apply, id_eq, one_mul] using!
        ((ht.differentiableAt.hasDerivAt.sub_const (energy i)).sub
          ((hasDerivAt_id t).mul_const (V i i)))
    · simp only [A, A₁,
        affineBranchCharacteristicMatrix_apply_ne _ _ _ _ hij,
        affineBranchCharacteristicMatrixFirstJet_apply_ne _ _ _ hij]
      simpa only [Pi.neg_apply, id_eq, one_mul] using!
        ((hasDerivAt_id t).mul_const (V i j)).neg
  have hA₁ :
      ∀ i j, HasDerivAt (fun t => A₁ t i j) (A₂ i j) 0 := by
    intro i j
    by_cases hij : i = j
    · subst j
      simpa [A₁, A₂, affineBranchCharacteristicMatrixFirstJet,
        affineBranchCharacteristicMatrixSecondJet] using
        hbranch.deriv.differentiableAt.hasDerivAt.sub_const (V i i)
    · simpa [A₁, A₂, affineBranchCharacteristicMatrixFirstJet,
        affineBranchCharacteristicMatrixSecondJet, hij] using
        hasDerivAt_const (x := (0 : ℂ)) (-V i j)
  have hdetJet :=
    complexDet_secondDerivative_eq_jet A A₁ A₂ 0 hA hA₁
  have hdetZero :
      (fun g => (A g).det) =ᶠ[𝓝 (0 : ℂ)] fun _ => 0 := by
    filter_upwards [hroot] with g hg
    simpa [A, affineBranchCharacteristicMatrix,
      matrixCharpolyRelation, sub_add_eq_sub_sub] using hg
  have hsecondZero :
      deriv (deriv (fun g => (A g).det)) 0 = 0 := by
    simpa using hdetZero.deriv.deriv_eq
  exact hdetJet ▸ hsecondZero

/-- For a simple diagonal spectrum, an affine perturbation with zero diagonal
has no first-order eigenvalue motion.  This is the exact first half of the
Rayleigh--Schrödinger law, derived from the characteristic equation. -/
theorem affineEigenbranch_firstDerivative_eq_zero_of_diagonal_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (energy : ι → ℂ) (hinj : Function.Injective energy)
    (V : Matrix ι ι ℂ) (hVdiag : ∀ i, V i i = 0)
    (x : ι) (branch : ℂ → ℂ)
    (hbranch : AnalyticAt ℂ branch 0)
    (hbase : branch 0 = energy x)
    (hroot :
      ∀ᶠ g in 𝓝 0,
        matrixCharpolyRelation
          (Matrix.diagonal energy + g • V, branch g) = 0) :
    deriv branch 0 = 0 := by
  let A := affineBranchCharacteristicMatrix energy V branch
  let B := affineBranchCharacteristicMatrixFirstJet V branch 0
  have hAentry :
      ∀ i j, HasDerivAt (fun g => A g i j) (B i j) 0 := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp only [A, B, affineBranchCharacteristicMatrix_apply_same,
        affineBranchCharacteristicMatrixFirstJet_apply_same]
      simpa only [Pi.sub_apply, id_eq, one_mul] using!
        ((hbranch.differentiableAt.hasDerivAt.sub_const (energy i)).sub
          ((hasDerivAt_id (0 : ℂ)).mul_const (V i i)))
    · simp only [A, B,
        affineBranchCharacteristicMatrix_apply_ne _ _ _ _ hij,
        affineBranchCharacteristicMatrixFirstJet_apply_ne _ _ _ hij]
      simpa only [Pi.neg_apply, id_eq, one_mul] using!
        ((hasDerivAt_id (0 : ℂ)).mul_const (V i j)).neg
  have hdetDeriv :=
    hasDerivAt_complexMatrixDet A B 0 hAentry
  have hdetZero :
      (fun g => (A g).det) =ᶠ[𝓝 (0 : ℂ)] fun _ => 0 := by
    filter_upwards [hroot] with g hg
    simpa [A, affineBranchCharacteristicMatrix,
      matrixCharpolyRelation, sub_add_eq_sub_sub] using hg
  have hjetZero : complexDetFirstJet (A 0) B = 0 := by
    rw [← hdetDeriv.deriv]
    simpa using hdetZero.deriv_eq
  have hA0 :
      A 0 = Matrix.diagonal (fun i => energy x - energy i) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [A, hbase]
    · simp [A, affineBranchCharacteristicMatrix_apply_ne _ _ _ _ hij,
        Matrix.diagonal_apply_ne _ hij]
  have hBxx : B x x = deriv branch 0 := by
    simp [B, hVdiag]
  rw [hA0,
    complexDetFirstJet_diagonal_single_zero
      (fun i => energy x - energy i) B x (sub_self _),
    hBxx] at hjetZero
  have hprod :
      ∏ i ∈ Finset.univ.erase x, (energy x - energy i) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    apply sub_ne_zero.mpr
    intro heq
    exact (Finset.mem_erase.mp hi).1 (hinj heq.symm)
  exact (mul_eq_zero.mp hjetZero).resolve_left hprod

end

end GaloisForLFunctions.HTGeometry
