import GaloisForLFunctions.HTGeometry.LocalExtensionSliceProjectiveGenericity
import GaloisForLFunctions.HTGeometry.RealAffineHermitianFamilyProjectiveGenericity
import GaloisForLFunctions.HTGeometry.WeakInteractionRecurrenceSingularityLaw

/-!
# Generic projective spectra for finite Anderson families

For every fixed finite Hermitian hopping matrix, arbitrary real diagonal
onsite controls contain a maximally projective spectral witness. Consequently,
the onsite potentials with maximal projective spectral rank are dense,
residual, and of full Lebesgue measure.

The witness transfer is nonperturbative. It first uses the joint family
`t • T + diagonal p`, whose zero-hopping slice contains a maximally projective
diagonal packet, and then rescales one generic point with `t ≠ 0` back to the
fixed-hopping slice.
-/

open Set Topology MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Maximal projective energy is invariant under nonzero real scaling. -/
theorem MaximallyProjectiveEnergy.const_mul
    {I : Type*} [Fintype I]
    {energy : I → ℝ}
    (hmax : MaximallyProjectiveEnergy energy)
    {c : ℝ} (hc : c ≠ 0) :
    MaximallyProjectiveEnergy (fun i => c * energy i) := by
  intro k hbalanced hzero
  apply hmax k hbalanced
  have hscaled :
      c * (∑ i, (k i : ℝ) * energy i) = 0 := by
    calc
      c * (∑ i, (k i : ℝ) * energy i) =
          ∑ i, (k i : ℝ) * (c * energy i) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = 0 := hzero
  exact (mul_eq_zero.mp hscaled).resolve_left hc

/-- Nonzero real scaling of a Hermitian matrix preserves maximal projective
rank of its canonical eigenvalue packet. -/
theorem maximallyProjectiveEnergy_eigenvalues_real_smul
    {I : Type*} [Fintype I] [DecidableEq I]
    (H : Matrix I I ℂ) (hH : H.IsHermitian)
    {c : ℝ} (hc : c ≠ 0)
    (hscaled : ((c : ℂ) • H).IsHermitian)
    (hmax : MaximallyProjectiveEnergy hH.eigenvalues) :
    MaximallyProjectiveEnergy hscaled.eigenvalues := by
  apply maximallyProjectiveEnergy_hermitianEigenvalues_of_rootPacket
    ((c : ℂ) • H) hscaled
    (fun i => c * hH.eigenvalues i)
    (hmax.const_mul hc)
  intro i
  have hroot :=
    hermitianEigenvalue_matrixCharpolyRelation H hH i
  unfold matrixCharpolyRelation at hroot ⊢
  push_cast
  have hmatrix :
      Matrix.scalar I
          (((c : ℂ) * (hH.eigenvalues i : ℂ))) -
          (c : ℂ) • H =
        (c : ℂ) •
          (Matrix.scalar I (hH.eigenvalues i : ℂ) - H) := by
    ext a b
    by_cases hab : a = b
    · subst b
      simp [Matrix.scalar_apply]
      ring
    · simp [Matrix.scalar_apply, hab]
  rw [hmatrix, Matrix.det_smul, hroot, mul_zero]

/-- The rank-one diagonal generator attached to one Anderson site. -/
def finiteAndersonOnsiteGenerator
    {n : ℕ} (i : Fin n) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun j => if j = i then 1 else 0)

theorem finiteAndersonOnsiteGenerator_isHermitian
    {n : ℕ} (i : Fin n) :
    (finiteAndersonOnsiteGenerator i).IsHermitian := by
  unfold finiteAndersonOnsiteGenerator
  rw [Matrix.isHermitian_diagonal_iff]
  intro j
  rw [isSelfAdjoint_iff]
  simp

/-- Fixed hopping plus arbitrary real onsite potential. -/
def finiteAndersonHamiltonian
    {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (onsite : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  T + Matrix.diagonal (fun i => (onsite i : ℂ))

theorem finiteAndersonHamiltonian_isHermitian
    {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : T.IsHermitian) (onsite : Fin n → ℝ) :
    (finiteAndersonHamiltonian T onsite).IsHermitian := by
  apply hT.add
  rw [Matrix.isHermitian_diagonal_iff]
  intro i
  rw [isSelfAdjoint_iff]
  simp

theorem realAffineMatrix_finiteAndersonOnsiteGenerator
    {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (onsite : Fin n → ℝ) :
    realAffineMatrix T finiteAndersonOnsiteGenerator onsite =
      finiteAndersonHamiltonian T onsite := by
  ext a b
  by_cases hab : a = b
  · subst b
    simp [realAffineMatrix, finiteAndersonOnsiteGenerator,
      finiteAndersonHamiltonian]
  · simp [realAffineMatrix, finiteAndersonOnsiteGenerator,
      finiteAndersonHamiltonian, hab]

/-- Joint hopping-strength/onsite generator family. -/
def finiteAndersonJointGenerator
    {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ) :
    Fin (n + 1) → Matrix (Fin n) (Fin n) ℂ :=
  Fin.cases T finiteAndersonOnsiteGenerator

theorem finiteAndersonJointGenerator_isHermitian
    {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : T.IsHermitian) :
    ∀ j, (finiteAndersonJointGenerator T j).IsHermitian := by
  intro j
  refine Fin.cases hT (fun i => ?_) j
  exact finiteAndersonOnsiteGenerator_isHermitian i

theorem realAffineMatrix_finiteAndersonJointGenerator
    {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (p : Fin (n + 1) → ℝ) :
    realAffineMatrix 0 (finiteAndersonJointGenerator T) p =
      (p 0 : ℂ) • T +
        Matrix.diagonal (fun i => (p i.succ : ℂ)) := by
  ext a b
  by_cases hab : a = b
  · subst b
    simp [realAffineMatrix, finiteAndersonJointGenerator,
      finiteAndersonOnsiteGenerator, Fin.sum_univ_succ]
  · simp [realAffineMatrix, finiteAndersonJointGenerator,
      finiteAndersonOnsiteGenerator, Fin.sum_univ_succ, hab]

/-- Every fixed finite Hermitian hopping matrix admits a real onsite
potential with maximally projective canonical spectrum. -/
theorem finiteAnderson_exists_maximallyProjective
    {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : T.IsHermitian) :
    ∃ onsite : Fin n → ℝ,
      MaximallyProjectiveEnergy
        (finiteAndersonHamiltonian_isHermitian
          T hT onsite).eigenvalues := by
  obtain ⟨energy, henergy, hclose⟩ :=
    exists_maximallyProjectiveEnergy_close_fintype
      (fun _ : Fin n => 0) 1 zero_lt_one
  let p₀ : Fin (n + 1) → ℝ :=
    Fin.cases 0 energy
  have hzero : (0 : Matrix (Fin n) (Fin n) ℂ).IsHermitian :=
    Matrix.isHermitian_zero
  have hjointHermitian :
      ∀ p : Fin (n + 1) → ℝ,
        (realAffineMatrix 0
          (finiteAndersonJointGenerator T) p).IsHermitian :=
    realAffineMatrix_isHermitian 0
      (finiteAndersonJointGenerator T) hzero
      (finiteAndersonJointGenerator_isHermitian T hT)
  have hp₀matrix :
      realAffineMatrix 0
          (finiteAndersonJointGenerator T) p₀ =
        Matrix.diagonal (fun i => (energy i : ℂ)) := by
    rw [realAffineMatrix_finiteAndersonJointGenerator]
    simp [p₀]
  have hdiag :
      (Matrix.diagonal (fun i => (energy i : ℂ)) :
        Matrix (Fin n) (Fin n) ℂ).IsHermitian := by
    rw [Matrix.isHermitian_diagonal_iff]
    intro i
    rw [isSelfAdjoint_iff]
    simp
  have hdiagMax :
      MaximallyProjectiveEnergy hdiag.eigenvalues := by
    apply maximallyProjectiveEnergy_hermitianEigenvalues_of_rootPacket
      (Matrix.diagonal (fun i => (energy i : ℂ))) hdiag
      energy henergy
    intro i
    exact matrixCharpolyRelation_diagonal_root
      (fun i => (energy i : ℂ)) i
  have hp₀Max :
      MaximallyProjectiveEnergy
        (hjointHermitian p₀).eigenvalues := by
    have heigen :
        (hjointHermitian p₀).eigenvalues =
          hdiag.eigenvalues := by
      apply
        (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff
          (hjointHermitian p₀) hdiag).2
      exact congrArg Matrix.charpoly hp₀matrix
    rw [heigen]
    exact hdiagMax
  obtain ⟨hdense, hresidual, hnull⟩ :=
    realAffineHermitianMaximalSet_dense_residual_fullMeasure
      0 (finiteAndersonJointGenerator T) hzero
      (finiteAndersonJointGenerator_isHermitian T hT)
      p₀ hp₀Max
  let U : Set (Fin (n + 1) → ℝ) :=
    {p | 0 < p 0}
  have hUopen : IsOpen U := by
    exact isOpen_lt continuous_const (continuous_apply 0)
  have hUnonempty : U.Nonempty := by
    refine ⟨Fin.cases 1 (fun _ => 0), ?_⟩
    simp [U]
  obtain ⟨p, hp, hpU⟩ :=
    hdense.exists_mem_open hUopen hUnonempty
  let c : ℝ := p 0
  have hc : c ≠ 0 := ne_of_gt hpU
  let onsite : Fin n → ℝ :=
    fun i => c⁻¹ * p i.succ
  let Hjoint : Matrix (Fin n) (Fin n) ℂ :=
    realAffineMatrix 0 (finiteAndersonJointGenerator T) p
  let hHjoint : Hjoint.IsHermitian :=
    hjointHermitian p
  have hHjointMax :
      MaximallyProjectiveEnergy hHjoint.eigenvalues := by
    unfold realAffineHermitianMaximalSet
      polynomialHermitianMatrixMaximalSet at hp
    let hpoly :
        ((realAffineMatrixPolynomial 0
          (finiteAndersonJointGenerator T)).map
            (MvPolynomial.eval₂Hom (RingHom.id ℂ)
              (fun t => (p t : ℂ)))).IsHermitian := by
      rw [eval_realAffineMatrixPolynomial]
      exact hjointHermitian p
    change MaximallyProjectiveEnergy hpoly.eigenvalues at hp
    have heigen :
        hpoly.eigenvalues = hHjoint.eigenvalues := by
      apply
        (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff
          hpoly hHjoint).2
      rw [eval_realAffineMatrixPolynomial]
    rw [← heigen]
    exact hp
  let hscaled :
      (((c⁻¹ : ℝ) : ℂ) • Hjoint).IsHermitian :=
    hHjoint.smul (by
      rw [isSelfAdjoint_iff]
      simp)
  have hscaledMax :=
    maximallyProjectiveEnergy_eigenvalues_real_smul
      Hjoint hHjoint (inv_ne_zero hc) hscaled hHjointMax
  have hscaledMatrix :
      ((c⁻¹ : ℝ) : ℂ) • Hjoint =
        finiteAndersonHamiltonian T onsite := by
    rw [show Hjoint =
      (c : ℂ) • T +
        Matrix.diagonal (fun i => (p i.succ : ℂ)) by
      exact realAffineMatrix_finiteAndersonJointGenerator T p]
    ext a b
    have hcC : (c : ℂ) ≠ 0 := by
      exact_mod_cast hc
    by_cases hab : a = b
    · subst b
      simp [finiteAndersonHamiltonian, onsite]
      field_simp [hcC]
    · simp [finiteAndersonHamiltonian, onsite, hab]
      field_simp [hcC]
  let hfixed :=
    finiteAndersonHamiltonian_isHermitian T hT onsite
  have heigen :
      hscaled.eigenvalues = hfixed.eigenvalues := by
    apply
      (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff
        hscaled hfixed).2
    exact congrArg Matrix.charpoly hscaledMatrix
  refine ⟨onsite, ?_⟩
  rw [← heigen]
  exact hscaledMax

/-- Onsite parameters with maximal projective spectrum for fixed hopping. -/
def finiteAndersonProjectiveMaximalSet
    {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : T.IsHermitian) :
    Set (Fin n → ℝ) :=
  {onsite |
    MaximallyProjectiveEnergy
      (finiteAndersonHamiltonian_isHermitian
        T hT onsite).eigenvalues}

/-- The physical fixed-hopping definition agrees with the real-affine
genericity engine's parameter set. -/
theorem finiteAndersonProjectiveMaximalSet_eq_realAffine
    {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : T.IsHermitian) :
    finiteAndersonProjectiveMaximalSet T hT =
      realAffineHermitianMaximalSet T
        finiteAndersonOnsiteGenerator hT
        finiteAndersonOnsiteGenerator_isHermitian := by
  ext onsite
  let hA :=
    realAffineMatrix_isHermitian T
      finiteAndersonOnsiteGenerator hT
      finiteAndersonOnsiteGenerator_isHermitian onsite
  let hH :=
    finiteAndersonHamiltonian_isHermitian T hT onsite
  let hpoly :
      ((realAffineMatrixPolynomial T
        finiteAndersonOnsiteGenerator).map
          (MvPolynomial.eval₂Hom (RingHom.id ℂ)
            (fun t => (onsite t : ℂ)))).IsHermitian := by
    rw [eval_realAffineMatrixPolynomial]
    exact hA
  change MaximallyProjectiveEnergy hH.eigenvalues ↔
    MaximallyProjectiveEnergy hpoly.eigenvalues
  have hpolyA : hpoly.eigenvalues = hA.eigenvalues := by
    apply
      (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff
        hpoly hA).2
    rw [eval_realAffineMatrixPolynomial]
  have hAH : hA.eigenvalues = hH.eigenvalues := by
    apply
      (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff
        hA hH).2
    exact congrArg Matrix.charpoly
      (realAffineMatrix_finiteAndersonOnsiteGenerator T onsite)
  rw [hpolyA, hAH]

/-- **Finite Anderson projective genericity law.** For arbitrary fixed
finite Hermitian hopping, the real onsite potentials whose canonical
eigenvalue packet has maximal projective rational rank form a dense,
residual, full-Lebesgue-measure set. -/
theorem finiteAndersonProjectiveMaximalSet_dense_residual_fullMeasure
    {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : T.IsHermitian) :
    Dense (finiteAndersonProjectiveMaximalSet T hT) ∧
      finiteAndersonProjectiveMaximalSet T hT ∈
        residual (Fin n → ℝ) ∧
      volume (finiteAndersonProjectiveMaximalSet T hT)ᶜ = 0 := by
  rw [finiteAndersonProjectiveMaximalSet_eq_realAffine T hT]
  obtain ⟨onsite, hmax⟩ :=
    finiteAnderson_exists_maximallyProjective T hT
  have haffineMax :
      MaximallyProjectiveEnergy
        (realAffineMatrix_isHermitian T
          finiteAndersonOnsiteGenerator hT
          finiteAndersonOnsiteGenerator_isHermitian
          onsite).eigenvalues := by
    let hA :=
      realAffineMatrix_isHermitian T
        finiteAndersonOnsiteGenerator hT
        finiteAndersonOnsiteGenerator_isHermitian onsite
    let hH :=
      finiteAndersonHamiltonian_isHermitian T hT onsite
    have heigen : hA.eigenvalues = hH.eigenvalues := by
      apply
        (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff
          hA hH).2
      exact congrArg Matrix.charpoly
        (realAffineMatrix_finiteAndersonOnsiteGenerator T onsite)
    rw [heigen]
    exact hmax
  exact
    realAffineHermitianMaximalSet_dense_residual_fullMeasure
      T finiteAndersonOnsiteGenerator hT
      finiteAndersonOnsiteGenerator_isHermitian
      onsite haffineMax

end

end GaloisForLFunctions.HTGeometry
