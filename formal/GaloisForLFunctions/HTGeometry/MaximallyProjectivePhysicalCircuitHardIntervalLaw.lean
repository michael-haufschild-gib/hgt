import GaloisForLFunctions.HTGeometry.ProjectiveSpectralCircuitHardIntervalLaw
import GaloisForLFunctions.HTGeometry.SpectralObservedOrbitDimension
import GaloisForLFunctions.RHTower.StaticChoiQuantitativeHardGapLaw

/-!
# Physical continuous-circuit-hard intervals from maximal spectral rank

The zero-anchored projective spectral flow is the actual Schrödinger evolution
up to its explicit anchor phase in the canonical Hermitian eigenbasis.  Since
the projective circuit-hard law already excludes every global-phase circuit
representative, it transfers without loss to physical operator norm.

Thus every finite Hermitian Hamiltonian with maximally projective spectrum has
syndetic positive-width intervals on which its exact evolution needs at least
`(D - 1) / 16` continuous two-qubit gates at one fixed positive error.
-/

open Matrix Set Topology
open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Canonical unitary eigenbasis of a finite Hermitian matrix, packaged in the
matrix-unitary group used by the circuit model. -/
def hermitianEigenbasisUnitary
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian) :
    Matrix.unitaryGroup ι ℂ :=
  ⟨(hH.eigenvectorUnitary : Matrix ι ι ℂ), hH.eigenvectorUnitary.2⟩

/-- Exact physical/projective bridge: the Schrödinger evolution is the
zero-anchored spectral matrix times the phase of the anchor eigenvalue. -/
theorem unitaryEvolution_eq_anchorPhase_smul_projectiveSpectralMatrix
    {n d : ℕ} (e : (Fin n → Bool) ≃ Fin (d + 1))
    {H : Matrix (Fin n → Bool) (Fin n → Bool) ℂ}
    (hH : H.IsHermitian) (t : ℝ) :
    unitaryEvolution H t =
      Complex.exp (-(Complex.I * (t * hH.eigenvalues (e.symm 0)))) •
        projectiveSpectralMatrix e (hermitianEigenbasisUnitary hH)
          (RHTower.projectivePhysicalPhaseFlow
            (fun i => hH.eigenvalues (e.symm i)) t) := by
  rw [unitaryEvolution_spectral hH]
  let anchor : ℂ :=
    Complex.exp (-(Complex.I * (t * hH.eigenvalues (e.symm 0))))
  have hdiag : Matrix.diagonal (fun i : Fin n → Bool =>
      Complex.exp (-(Complex.I * (t * hH.eigenvalues i)))) =
      anchor • Matrix.diagonal (fun q : Fin n → Bool =>
        fourier 1 (RHTower.zeroAnchoredPhase d
          (RHTower.projectivePhysicalPhaseFlow
            (fun i => hH.eigenvalues (e.symm i)) t) (e q))) := by
    ext i j
    by_cases hij : i = j
    · subst j
      rw [Matrix.diagonal_apply_eq, Matrix.smul_apply,
        Matrix.diagonal_apply_eq]
      simp only [smul_eq_mul]
      generalize hr : e i = r
      change Complex.exp (-(Complex.I * (t * hH.eigenvalues i))) =
        anchor * fourier 1 (RHTower.zeroAnchoredPhase d
          (RHTower.projectivePhysicalPhaseFlow
            (fun k => hH.eigenvalues (e.symm k)) t) r)
      rcases Fin.eq_zero_or_eq_succ r with hzero | ⟨k, hsucc⟩
      · rw [hzero] at hr ⊢
        have hi : i = e.symm 0 := by
          apply e.injective
          simpa using hr
        simp [RHTower.zeroAnchoredPhase, anchor, hi]
      · rw [hsucc] at hr ⊢
        rw [RHTower.fourier_projectiveChoiPhase_eq_exp]
        have hi : i = e.symm k.succ := by
          apply e.injective
          simpa using hr
        rw [hi]
        unfold anchor
        rw [← Complex.exp_add]
        congr 1
        unfold RHTower.zeroProjectiveFrequency
        simp
        ring
    · rw [Matrix.diagonal_apply_ne _ hij, Matrix.smul_apply,
        Matrix.diagonal_apply_ne _ hij]
      simp
  let D : Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
    Matrix.diagonal (fun q =>
      fourier 1 (RHTower.zeroAnchoredPhase d
        (RHTower.projectivePhysicalPhaseFlow
          (fun i => hH.eigenvalues (e.symm i)) t) (e q)))
  calc
    ((hH.eigenvectorUnitary : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) *
        Matrix.diagonal (fun i =>
          Complex.exp (-(Complex.I * (t * hH.eigenvalues i))))) *
        star (hH.eigenvectorUnitary :
          Matrix (Fin n → Bool) (Fin n → Bool) ℂ) =
      ((hH.eigenvectorUnitary : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) *
        (anchor • D)) * star (hH.eigenvectorUnitary :
          Matrix (Fin n → Bool) (Fin n → Bool) ℂ) := by rw [hdiag]
    _ = anchor • (((hH.eigenvectorUnitary :
          Matrix (Fin n → Bool) (Fin n → Bool) ℂ) * D) *
        star (hH.eigenvectorUnitary :
          Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) := by
      simp only [Matrix.mul_smul, Matrix.smul_mul]
    _ = anchor • projectiveSpectralMatrix e
        (hermitianEigenbasisUnitary hH)
          (RHTower.projectivePhysicalPhaseFlow
            (fun i => hH.eigenvalues (e.symm i)) t) := by
      congr 1

/-- **Universal physical hard-interval law.**  Every finite Hermitian
Hamiltonian with maximally projective spectrum has one fixed positive operator
error, one fixed positive plateau width, and one finite recurrence gap such
that every gap window contains a full plateau interval excluding every
continuous two-qubit circuit with `16s < D - 1`. -/
theorem maximallyProjective_unitaryEvolution_continuousCircuitHardIntervals_syndetic
    {n d s : ℕ} (e : (Fin n → Bool) ≃ Fin (d + 1))
    {H : Matrix (Fin n → Bool) (Fin n → Bool) ℂ}
    (hH : H.IsHermitian)
    (hmax : MaximallyProjectiveEnergy (fun i => hH.eigenvalues (e.symm i)))
    (hs : s * 16 < d) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ W : ℝ, 0 < W ∧ ∃ L : ℝ, 0 ≤ L ∧
      ∀ a : ℝ, ∃ u ∈ Set.Icc a (a + L),
        ∀ t ∈ Set.Icc u (u + W),
          ∀ C : TwoQubitCircuit n, C.gateCount ≤ s →
            ε ≤ ‖unitaryEvolution H t -
              (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)‖ := by
  obtain ⟨ε, hε, W, hW, L, hL, hhard⟩ :=
    maximallyProjective_projectiveSpectralCircuitHardIntervals_syndetic
      (fun i => hH.eigenvalues (e.symm i)) hmax e
      (hermitianEigenbasisUnitary hH) hs
  refine ⟨ε, hε, W, hW, L, hL, ?_⟩
  intro a
  obtain ⟨u, hu, huHard⟩ := hhard a
  refine ⟨u, hu, ?_⟩
  intro t ht C hCs
  let anchor : ℂ :=
    Complex.exp (-(Complex.I * (t * hH.eigenvalues (e.symm 0))))
  have hanchor : ‖anchor‖ = 1 := by
    unfold anchor
    rw [Complex.norm_exp]
    simp
  have hproj := huHard t ht anchor⁻¹ (by rw [norm_inv, hanchor, inv_one]) C hCs
  rw [unitaryEvolution_eq_anchorPhase_smul_projectiveSpectralMatrix]
  change ε ≤ ‖anchor • projectiveSpectralMatrix e
      (hermitianEigenbasisUnitary hH)
        (RHTower.projectivePhysicalPhaseFlow
          (fun i => hH.eigenvalues (e.symm i)) t) -
      (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)‖
  have hfactor : anchor • projectiveSpectralMatrix e
        (hermitianEigenbasisUnitary hH)
          (RHTower.projectivePhysicalPhaseFlow
            (fun i => hH.eigenvalues (e.symm i)) t) -
        (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) =
      anchor • (projectiveSpectralMatrix e
        (hermitianEigenbasisUnitary hH)
          (RHTower.projectivePhysicalPhaseFlow
            (fun i => hH.eigenvalues (e.symm i)) t) -
        anchor⁻¹ • (C.eval : Matrix (Fin n → Bool) (Fin n → Bool) ℂ)) := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ (Complex.exp_ne_zero _), one_smul]
  rw [hfactor, norm_smul, hanchor, one_mul]
  exact hproj

end
end GaloisForLFunctions.HTGeometry
