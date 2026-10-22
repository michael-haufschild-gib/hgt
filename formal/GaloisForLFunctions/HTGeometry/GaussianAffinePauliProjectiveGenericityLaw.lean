import GaloisForLFunctions.HTGeometry.GenericLocalCollisionExtremality
import GaloisForLFunctions.HTGeometry.PiMeasureAbsoluteContinuity
import GaloisForLFunctions.HTGeometry.RootPacketRelabelling
import GaloisForLFunctions.HTGeometry.TwoLocalHardWindowLaw
import GaloisForLFunctions.HTGeometry.ActivePauliShellSpectralLaw
import GaloisForLFunctions.HTGeometry.PauliBoundedHamiltonianLocalityLaw
import GaloisForLFunctions.HTGeometry.TwoLocalPauliGaussianEnergyCap

/-!
# Gaussian two-local Pauli perturbations preserve maximally projective spectra

A Hermitian spectrum `E` is maximally projective when no nonzero integer vector `k` with
`Σ k_i = 0` satisfies `Σ k_i E_i = 0`. This module proves a one-witness genericity law for
Gaussian Pauli perturbations on `n` qubits: if a Hermitian base Hamiltonian `H₀` has maximally
projective spectrum, then for every real scale `s`, almost surely with respect to the standard
Gaussian on the coefficients `x` of the nonidentity Pauli strings of weight at most two,
`H₀ + Σ_P s x_P P` also has maximally projective spectrum. It is obtained by viewing
`H₀ + s Σ x_P P` as a real-affine Hermitian family, whose maximal set has Lebesgue-null complement
once it contains one point, and transferring null sets through the absolute continuity of the
Gaussian.

## Main results

- `Matrix.IsHermitian.maximallyProjective_reindexAlgEquiv`: maximal projectivity of the spectrum
  is invariant under reindexing the basis.
- `stdGaussian_absolutelyContinuous_volume_finEuclidean`: the standard Gaussian on
  `EuclideanSpace ℝ (Fin m)` is absolutely continuous with respect to Lebesgue measure.
- `realAffineMatrix_scaledActivePauli_eq`: the real-affine family with generators `s · P` is
  `H₀ + s · Σ_t p_t P_t`.
- `maximallyProjective_scaledAffine_activePauli_ae`: if `H₀` has maximally projective spectrum,
  then for every real `s` and almost every Gaussian two-local Pauli coefficient vector `x`, the
  spectrum of `H₀ + H(s x)` is maximally projective.

## Hypotheses

The main theorem is conditional on `hmax`: the Hermitian base matrix `H₀` itself has maximally
projective spectrum (`MaximallyProjectiveEnergy hH₀.eigenvalues`). No other substantive input is
assumed; the scale `s` is arbitrary.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator
open Matrix MeasureTheory ProbabilityTheory Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Reindexing a Hermitian matrix along `e : I ≃ J` preserves maximal projectivity of its spectrum
(no nonzero balanced integer relation among the eigenvalues). -/
theorem Matrix.IsHermitian.maximallyProjective_reindexAlgEquiv
    {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J]
    (e : I ≃ J) {H : Matrix I I ℂ} (hH : H.IsHermitian)
    (hmax : MaximallyProjectiveEnergy hH.eigenvalues) :
    MaximallyProjectiveEnergy
      ((hH.reindex e).eigenvalues) := by
  let hHr : (Matrix.reindexAlgEquiv ℂ ℂ e H).IsHermitian := hH.reindex e
  let energy : I → ℝ := fun i => hHr.eigenvalues (e i)
  have hroots : Finset.univ.val.map (fun i => ((energy i : ℝ) : ℂ)) =
      H.charpoly.roots := by
    change Multiset.map
      ((fun j : J => ((hHr.eigenvalues j : ℝ) : ℂ)) ∘ e) Finset.univ.val = _
    rw [← Multiset.map_map, Multiset.map_univ_val_equiv e]
    rw [hermitianEigenvalues_rootMultiset hHr]
    congr 1
    exact Matrix.charpoly_reindex e H
  have henergy : MaximallyProjectiveEnergy energy :=
    maximallyProjectiveEnergy_of_rootMultiset hH hmax energy hroots
  simpa [energy, hHr] using henergy.comp_equiv e.symm

/-- The standard Gaussian measure on `EuclideanSpace ℝ (Fin m)` is absolutely continuous with
respect to Lebesgue measure. -/
theorem stdGaussian_absolutelyContinuous_volume_finEuclidean (m : ℕ) :
    stdGaussian (EuclideanSpace ℝ (Fin m)) ≪ volume := by
  rw [← map_pi_eq_stdGaussian]
  have hprod :
      Measure.pi (fun _ : Fin m => gaussianReal 0 1) ≪
        (volume : Measure (Fin m → ℝ)) :=
    productGaussian_absolutelyContinuous m (by norm_num) (fun _ => 0)
  have hmap := hprod.map (MeasurableEquiv.toLp 2 (Fin m → ℝ)).measurable
  simpa only [MeasurableEquiv.coe_toLp,
    (PiLp.volume_preserving_toLp (Fin m)).map_eq] using hmap

/-- The linear isometry relabelling Euclidean coefficient vectors indexed by nonidentity Pauli
strings of weight at most `q` into numbered coordinates. -/
def pauliTracelessEuclideanReindex (n q : ℕ) :
    EuclideanSpace ℝ (PauliTracelessLabel n q) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (ActivePauliCoordinate n q) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (pauliTracelessLabelEquivFin n q)

theorem activePauliFinHamiltonian_pauliTracelessEuclideanReindex
    {n q : ℕ} (x : EuclideanSpace ℝ (PauliTracelessLabel n q)) :
    activePauliFinHamiltonian
        (WithLp.ofLp (pauliTracelessEuclideanReindex n q x)) =
      activePauliHamiltonian
        (fun Q => ((WithLp.ofLp x Q : ℝ) : ℂ)) := by
  ext i j
  simp [pauliTracelessEuclideanReindex, activePauliFinHamiltonian,
    activePauliHamiltonian, LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft']

/-- Coefficient vectors `p` for which `H₀ + s · Σ_t p_t P_t` (sum over the nonidentity Pauli
strings of weight at most `q`) has maximally projective spectrum. -/
def scaledAffineActivePauliMaximalSet
    {n q : ℕ} (H₀ : Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ) (hH₀ : H₀.IsHermitian)
      (scale : ℝ) :
    Set (ActivePauliCoordinate n q → ℝ) :=
  realAffineHermitianMaximalSet H₀
    (fun t => (scale : ℂ) •
      finitePauliMatrix ((pauliTracelessLabelEquivFin n q).symm t).1)
    hH₀
    (fun t => by
      rw [Matrix.isHermitian_iff_isSelfAdjoint, IsSelfAdjoint, star_smul,
        (Matrix.isHermitian_iff_isSelfAdjoint.mp
          (finitePauliMatrix_isHermitian
            ((pauliTracelessLabelEquivFin n q).symm t).1)).star_eq]
      simp)

/-- The real-affine matrix with base `H₀` and generators `s · P_t` at parameter `p` equals
`H₀ + s · Σ_t p_t P_t`. -/
theorem realAffineMatrix_scaledActivePauli_eq
    {n q : ℕ} (H₀ : Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ) (scale : ℝ)
      (p : ActivePauliCoordinate n q → ℝ) :
    realAffineMatrix H₀
        (fun t => (scale : ℂ) •
          finitePauliMatrix ((pauliTracelessLabelEquivFin n q).symm t).1) p =
      H₀ + (scale : ℂ) • activePauliFinHamiltonian p := by
  ext i j
  simp [realAffineMatrix, activePauliFinHamiltonian,
    activePauliHamiltonian, Matrix.sum_apply, Matrix.smul_apply]
  calc
    (∑ x, (p x : ℂ) * ((scale : ℂ) *
        finitePauliMatrix ((pauliTracelessLabelEquivFin n q).symm x).1 i j)) =
        ∑ x, (scale : ℂ) * ((p x : ℂ) *
          finitePauliMatrix ((pauliTracelessLabelEquivFin n q).symm x).1 i j) := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = (scale : ℂ) * ∑ x, (p x : ℂ) *
          finitePauliMatrix ((pauliTracelessLabelEquivFin n q).symm x).1 i j := by
      rw [Finset.mul_sum]
    _ = (scale : ℂ) * ∑ Q, (p (pauliTracelessLabelEquivFin n q Q) : ℂ) *
          finitePauliMatrix Q.1 i j := by
      congr 1
      symm
      apply Fintype.sum_equiv (pauliTracelessLabelEquivFin n q)
      intro Q
      simp

/-- Assuming `hmax`: the Hermitian `H₀` has maximally projective spectrum. Then for every real
`scale`, for almost every standard Gaussian two-local Pauli coefficient vector `x`, the spectrum of
`H₀ + H(scale • x)` is again maximally projective. -/
theorem maximallyProjective_scaledAffine_activePauli_ae
    {n : ℕ} (H₀ : Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ) (hH₀ : H₀.IsHermitian)
    (hmax : MaximallyProjectiveEnergy hH₀.eigenvalues)
    (scale : ℝ) :
    ∀ᵐ x ∂(stdGaussian (TwoLocalPauliCoefficientSpace n)),
      MaximallyProjectiveEnergy
        ((hH₀.add (Matrix.isHermitian_iff_isSelfAdjoint.mpr
          (isSelfAdjoint_realActivePauliHamiltonian (scale • x)))).eigenvalues) := by
  let m := Fintype.card (PauliTracelessLabel n 2)
  let generator : Fin m → Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ :=
    fun t => (scale : ℂ) •
      finitePauliMatrix ((pauliTracelessLabelEquivFin n 2).symm t).1
  have hgenerator : ∀ t, (generator t).IsHermitian := by
    intro t
    dsimp only [generator]
    rw [Matrix.isHermitian_iff_isSelfAdjoint, IsSelfAdjoint, star_smul,
      (Matrix.isHermitian_iff_isSelfAdjoint.mp
        (finitePauliMatrix_isHermitian
          ((pauliTracelessLabelEquivFin n 2).symm t).1)).star_eq]
    simp
  let hfamily := realAffineMatrix_isHermitian H₀ generator hH₀ hgenerator
  have hzero : realAffineMatrix H₀ generator (0 : Fin m → ℝ) = H₀ := by
    ext i j
    simp [realAffineMatrix]
  have hmaxzero : MaximallyProjectiveEnergy (hfamily 0).eigenvalues := by
    have heig := isHermitian_eigenvalues_congr (hfamily 0) hH₀ hzero
    rw [heig]
    exact hmax
  obtain ⟨_, _, hnull⟩ :=
    realAffineHermitianMaximalSet_dense_residual_fullMeasure
      H₀ generator hH₀ hgenerator 0 hmaxzero
  let S := realAffineHermitianMaximalSet H₀ generator hH₀ hgenerator
  let μ : Measure (Fin m → ℝ) := Measure.pi fun _ => gaussianReal 0 1
  have hAC : μ ≪ (volume : Measure (Fin m → ℝ)) := by
    exact productGaussian_absolutelyContinuous m (by norm_num) (fun _ => 0)
  have hμnull : μ Sᶜ = 0 := hAC hnull
  have hraw : ∀ᵐ p ∂μ,
      MaximallyProjectiveEnergy (hfamily p).eigenvalues := by
    filter_upwards [compl_mem_ae_iff.mpr hμnull] with p hp
    exact maximallyProjective_of_mem_realAffineHermitianMaximalSet
      H₀ generator hH₀ hgenerator (by simpa [S] using hp)
  have hmapOfLp :
      (stdGaussian (EuclideanSpace ℝ (Fin m))).map WithLp.ofLp = μ := by
    rw [← map_pi_eq_stdGaussian, Measure.map_map]
    · have hcomp :
          (WithLp.ofLp : EuclideanSpace ℝ (Fin m) → (Fin m → ℝ)) ∘
              (WithLp.toLp 2) = id := by
          funext p
          rfl
      rw [hcomp, Measure.map_id]
    · exact (MeasurableEquiv.toLp 2 (Fin m → ℝ)).symm.measurable
    · exact (MeasurableEquiv.toLp 2 (Fin m → ℝ)).measurable
  have hqmpOfLp : Measure.QuasiMeasurePreserving
      (WithLp.ofLp : EuclideanSpace ℝ (Fin m) → (Fin m → ℝ))
      (stdGaussian (EuclideanSpace ℝ (Fin m))) μ := by
    refine ⟨(MeasurableEquiv.toLp 2 (Fin m → ℝ)).symm.measurable, ?_⟩
    rw [hmapOfLp]
  have heuclidean : ∀ᵐ y ∂(stdGaussian (EuclideanSpace ℝ (Fin m))),
      MaximallyProjectiveEnergy (hfamily (WithLp.ofLp y)).eigenvalues :=
    hqmpOfLp.ae hraw
  let f := pauliTracelessEuclideanReindex n 2
  have hmapf : (stdGaussian (TwoLocalPauliCoefficientSpace n)).map f =
      stdGaussian (EuclideanSpace ℝ (Fin m)) := by
    simpa [f, m, ActivePauliCoordinate] using
      (stdGaussian_map f)
  have hqmpf : Measure.QuasiMeasurePreserving f
      (stdGaussian (TwoLocalPauliCoefficientSpace n))
      (stdGaussian (EuclideanSpace ℝ (Fin m))) := by
    refine ⟨f.continuous.measurable, ?_⟩
    rw [hmapf]
  filter_upwards [hqmpf.ae heuclidean] with x hx
  have hmatrix : realAffineMatrix H₀ generator (WithLp.ofLp (f x)) =
      H₀ + realActivePauliHamiltonian (scale • x) := by
    calc
      realAffineMatrix H₀ generator (WithLp.ofLp (f x)) =
          H₀ + (scale : ℂ) •
            activePauliFinHamiltonian (WithLp.ofLp (f x)) := by
        exact realAffineMatrix_scaledActivePauli_eq H₀ scale _
      _ = H₀ + (scale : ℂ) • realActivePauliHamiltonian x := by
        rw [activePauliFinHamiltonian_pauliTracelessEuclideanReindex]
        rfl
      _ = H₀ + realActivePauliHamiltonian (scale • x) := by
        rw [realActivePauliHamiltonian_smul]
  have heig := isHermitian_eigenvalues_congr
    (hfamily (WithLp.ofLp (f x)))
    (hH₀.add (Matrix.isHermitian_iff_isSelfAdjoint.mpr
      (isSelfAdjoint_realActivePauliHamiltonian (scale • x)))) hmatrix
  rw [← heig]
  exact hx

end

end GaloisForLFunctions.HTGeometry
