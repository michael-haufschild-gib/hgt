import GaloisForLFunctions.QuantumAlg.Util.QuantumFisher

/-!
# Collective quantum Fisher information and connected correlations

For a finite family of observables, covariance of their sum is the sum of all pairwise
covariances.  Consequently pure-state quantum Fisher information of the half-sum observable is
the full connected-correlation sum.  Dividing by the number of sites gives the normalization used
for collective spin magnetization in finite chains.

These identities are the algebraic content of equation (14) in Formicola--Di Bello--de Candia--
De Filippis--Perroni, *Discrete time crystals in disordered anisotropic Heisenberg chains*,
arXiv:2609.04037.  They do not use the paper's numerical phase classification.
-/

open scoped BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Sum of a finite family of observables. -/
def finiteCollectiveObservable
    {n ι : Type*} [Fintype n] [Fintype ι]
    (A : ι → Matrix n n ℂ) : Matrix n n ℂ :=
  ∑ i, A i

/-- Pure-state generator quantum Fisher value in covariance form. -/
def pureGeneratorQuantumFisher
    {n : Type*} [Fintype n]
    (ψ : n → ℂ) (A : Matrix n n ℂ) : ℝ :=
  4 * QuantumAlg.qCov ψ A A

/-- Covariance of a collective observable is the complete pair-correlation sum. -/
theorem qCov_finiteCollectiveObservable_eq_sum
    {n ι : Type*} [Fintype n] [Fintype ι]
    (ψ : n → ℂ) (A : ι → Matrix n n ℂ) :
    QuantumAlg.qCov ψ (finiteCollectiveObservable A)
        (finiteCollectiveObservable A) =
      ∑ i, ∑ j, QuantumAlg.qCov ψ (A i) (A j) := by
  classical
  unfold finiteCollectiveObservable
  rw [show (∑ i, A i) = ∑ i ∈ Finset.univ, ((1 : ℝ) : ℂ) • A i by simp]
  rw [QuantumAlg.qCov_sum_ofReal_smul_left]
  simp_rw [QuantumAlg.qCov_sum_ofReal_smul_right]
  simp

/-- Quantum Fisher information of a collective generator is four times the complete covariance
matrix sum. -/
theorem pureGeneratorQuantumFisher_collective_eq_four_mul_sum
    {n ι : Type*} [Fintype n] [Fintype ι]
    (ψ : n → ℂ) (A : ι → Matrix n n ℂ) :
    pureGeneratorQuantumFisher ψ (finiteCollectiveObservable A) =
      4 * ∑ i, ∑ j, QuantumAlg.qCov ψ (A i) (A j) := by
  rw [pureGeneratorQuantumFisher,
    qCov_finiteCollectiveObservable_eq_sum]

/-- Half-sum collective observable, including the spin convention
`M_z = (1/2) ∑ᵢ σᶻᵢ`. -/
def finiteHalfCollectiveObservable
    {n ι : Type*} [Fintype n] [Fintype ι]
    (A : ι → Matrix n n ℂ) : Matrix n n ℂ :=
  ((1 / 2 : ℝ) : ℂ) • finiteCollectiveObservable A

/-- The factor four in pure-state QFI cancels the two factors of one half in the collective
spin generator, leaving exactly the complete connected-correlation sum. -/
theorem pureGeneratorQuantumFisher_halfCollective_eq_sum
    {n ι : Type*} [Fintype n] [Fintype ι]
    (ψ : n → ℂ) (A : ι → Matrix n n ℂ) :
    pureGeneratorQuantumFisher ψ (finiteHalfCollectiveObservable A) =
      ∑ i, ∑ j, QuantumAlg.qCov ψ (A i) (A j) := by
  classical
  unfold pureGeneratorQuantumFisher finiteHalfCollectiveObservable
  rw [QuantumAlg.qCov_ofReal_smul_left,
    QuantumAlg.qCov_ofReal_smul_right,
    qCov_finiteCollectiveObservable_eq_sum]
  ring

/-- Per-site QFI of a half-sum collective observable.  Division is total, so the empty family has
value zero. -/
def finiteHalfCollectiveQuantumFisherPerSite
    {n ι : Type*} [Fintype n] [Fintype ι]
    (ψ : n → ℂ) (A : ι → Matrix n n ℂ) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ *
    pureGeneratorQuantumFisher ψ (finiteHalfCollectiveObservable A)

/-- Paper-style normalized QFI/susceptibility identity: QFI per site is the normalized sum of all
connected two-point correlations. -/
theorem finiteHalfCollectiveQuantumFisherPerSite_eq_correlationSum
    {n ι : Type*} [Fintype n] [Fintype ι]
    (ψ : n → ℂ) (A : ι → Matrix n n ℂ) :
    finiteHalfCollectiveQuantumFisherPerSite ψ A =
      (Fintype.card ι : ℝ)⁻¹ *
        ∑ i, ∑ j, QuantumAlg.qCov ψ (A i) (A j) := by
  rw [finiteHalfCollectiveQuantumFisherPerSite,
    pureGeneratorQuantumFisher_halfCollective_eq_sum]

/-- The same collective QFI is the sum of every entry of the covariance-form QFIM. -/
theorem pureGeneratorQuantumFisher_collective_eq_sum_qfim
    {n : Type*} [Fintype n] {M : ℕ}
    (ψ : n → ℂ) (A : Fin M → Matrix n n ℂ) :
    pureGeneratorQuantumFisher ψ (finiteCollectiveObservable A) =
      ∑ i, ∑ j, QuantumAlg.qfim ψ A i j := by
  rw [pureGeneratorQuantumFisher_collective_eq_four_mul_sum]
  simp only [QuantumAlg.qfim_apply, Finset.mul_sum]

end

end GaloisForLFunctions.HTGeometry
