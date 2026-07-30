import GaloisForLFunctions.HTGeometry.PolynomialHermitianSpectrumGenericity

/-!
# Generic projective spectra in real-affine Hermitian families

Physical finite-dimensional Hamiltonian models are real affine spans of
Hermitian generators.  This file instantiates polynomial-family genericity
for that exact class.
-/

open Set Topology MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Polynomial matrix representing a real-affine matrix family. -/
def realAffineMatrixPolynomial
    {θ I : Type*} [Fintype θ]
    (base : Matrix I I ℂ)
    (generator : θ → Matrix I I ℂ) :
    Matrix I I (MvPolynomial θ ℂ) :=
  fun a b =>
    MvPolynomial.C (base a b) +
      ∑ t,
        MvPolynomial.X t *
          MvPolynomial.C (generator t a b)

/-- Evaluation of the same real-affine matrix family. -/
def realAffineMatrix
    {θ I : Type*} [Fintype θ]
    (base : Matrix I I ℂ)
    (generator : θ → Matrix I I ℂ)
    (p : θ → ℝ) :
    Matrix I I ℂ :=
  fun a b =>
    base a b + ∑ t, (p t : ℂ) * generator t a b

theorem eval_realAffineMatrixPolynomial
    {θ I : Type*} [Fintype θ]
    (base : Matrix I I ℂ)
    (generator : θ → Matrix I I ℂ)
    (p : θ → ℝ) :
    (realAffineMatrixPolynomial base generator).map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ)
          (fun t => (p t : ℂ))) =
      realAffineMatrix base generator p := by
  ext a b
  simp [realAffineMatrixPolynomial,
    realAffineMatrix]

/-- Real coefficients preserve Hermiticity of an affine generator
family. -/
theorem realAffineMatrix_isHermitian
    {θ I : Type*} [Fintype θ]
    (base : Matrix I I ℂ)
    (generator : θ → Matrix I I ℂ)
    (hbase : base.IsHermitian)
    (hgenerator : ∀ t, (generator t).IsHermitian)
    (p : θ → ℝ) :
    (realAffineMatrix base generator p).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro a b
  simp only [realAffineMatrix]
  change
    (starRingEnd ℂ)
        (base b a + ∑ t, (p t : ℂ) * generator t b a) =
      base a b + ∑ t, (p t : ℂ) * generator t a b
  rw [map_add, map_sum]
  congr 1
  · exact hbase.apply a b
  · apply Finset.sum_congr rfl
    intro t ht
    rw [map_mul]
    have htgen :
        (starRingEnd ℂ) (generator t b a) =
          generator t a b := by
      exact hgenerator t |>.apply a b
    rw [htgen]
    simp

/-- Parameters whose real-affine Hermitian spectrum has maximal
projective rational rank. -/
def realAffineHermitianMaximalSet
    {m : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (base : Matrix I I ℂ)
    (generator : Fin m → Matrix I I ℂ)
    (hbase : base.IsHermitian)
    (hgenerator : ∀ t, (generator t).IsHermitian) :
    Set (Fin m → ℝ) :=
  polynomialHermitianMatrixMaximalSet
    (realAffineMatrixPolynomial base generator)
    (fun p => by
      rw [eval_realAffineMatrixPolynomial]
      exact realAffineMatrix_isHermitian
        base generator hbase hgenerator p)

/-- **Real-affine Hermitian one-witness theorem.** If one Hamiltonian in
a finite real-affine Hermitian family has maximal projective spectral
rank, then almost every Hamiltonian in that family does; the set is also
dense and residual. -/
theorem
    realAffineHermitianMaximalSet_dense_residual_fullMeasure
    {m : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (base : Matrix I I ℂ)
    (generator : Fin m → Matrix I I ℂ)
    (hbase : base.IsHermitian)
    (hgenerator : ∀ t, (generator t).IsHermitian)
    (p₀ : Fin m → ℝ)
    (hmax :
      MaximallyProjectiveEnergy
        (realAffineMatrix_isHermitian
          base generator hbase hgenerator p₀).eigenvalues) :
    Dense
        (realAffineHermitianMaximalSet
          base generator hbase hgenerator) ∧
      realAffineHermitianMaximalSet
          base generator hbase hgenerator ∈
        residual (Fin m → ℝ) ∧
      volume
        (realAffineHermitianMaximalSet
          base generator hbase hgenerator)ᶜ = 0 := by
  unfold realAffineHermitianMaximalSet
  apply
    polynomialHermitianMatrixMaximalSet_dense_residual_fullMeasure
      (realAffineMatrixPolynomial base generator)
      (fun p => by
        rw [eval_realAffineMatrixPolynomial]
        exact realAffineMatrix_isHermitian
          base generator hbase hgenerator p)
      p₀
  let hpoly :
      ((realAffineMatrixPolynomial base generator).map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ)
          (fun t => (p₀ t : ℂ)))).IsHermitian := by
    rw [eval_realAffineMatrixPolynomial]
    exact realAffineMatrix_isHermitian
      base generator hbase hgenerator p₀
  let hreal :
      (realAffineMatrix base generator p₀).IsHermitian :=
    realAffineMatrix_isHermitian
      base generator hbase hgenerator p₀
  change MaximallyProjectiveEnergy hpoly.eigenvalues
  have heigenvalues :
      hpoly.eigenvalues = hreal.eigenvalues := by
    apply
      (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff
        hpoly hreal).2
    rw [eval_realAffineMatrixPolynomial]
  rw [heigenvalues]
  exact hmax

end

end GaloisForLFunctions.HTGeometry
