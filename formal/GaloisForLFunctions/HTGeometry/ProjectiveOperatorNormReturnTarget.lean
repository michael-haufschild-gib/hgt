import GaloisForLFunctions.HTGeometry.SpectralObservedOrbitDimension
import GaloisForLFunctions.HTGeometry.AnchoredProjectiveReturnDensityLaw
import GaloisForLFunctions.HTGeometry.UnitaryL2OperatorNorm

/-!
# The projective return target in operator norm

The local return law is proved for the anchored chord target on the relative-phase torus.  The
object it models is the projective operator-norm return target of the evolution: the times at which
the evolution is within `ε` of a scalar multiple of the identity, the scalar being the phase of the
reference level.

This file identifies the two.  Conjugation by the eigenvector unitary is an isometry, so the
operator-norm distance from the evolution to its anchoring phase is the largest chord among the
relative phases, and the anchored chord target is exactly the operator-norm target.
-/

open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]

omit [Fintype d] [Nonempty d] in
/-- A scalar multiple of the identity is the constant diagonal matrix. -/
theorem smul_one_eq_diagonal_const (c : ℂ) :
    c • (1 : Matrix d d ℂ) = Matrix.diagonal (fun _ : d => c) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp
  · simp [Matrix.one_apply_ne h, Matrix.diagonal_apply_ne _ h]

/-- The anchoring phase of a Hermitian generator at a reference level. -/
def anchorPhase (E : d → ℝ) (a : d) (t : ℝ) : ℂ := Complex.exp (-(Complex.I * (t * E a)))

/-- **The projective operator-norm return distance is the largest relative-phase chord.**  The
distance from the evolution to its anchoring phase is the supremum over levels of the chord of the
relative phase. -/
theorem l2_opNorm_unitaryEvolution_sub_anchorPhase {H : Matrix d d ℂ} (hH : H.IsHermitian)
    (a : d) (t : ℝ) :
    ‖unitaryEvolution H t - anchorPhase hH.eigenvalues a t • (1 : Matrix d d ℂ)‖
      = ‖fun i : d =>
          Complex.exp (-(Complex.I * (t * (hH.eigenvalues i - hH.eigenvalues a)))) - 1‖ := by
  set V : Matrix d d ℂ := (hH.eigenvectorUnitary : Matrix d d ℂ) with hVdef
  have hV : V ∈ unitary (Matrix d d ℂ) := hH.eigenvectorUnitary.2
  have hVstar : V * star V = 1 := (Unitary.mem_iff.mp hV).2
  set c : ℂ := anchorPhase hH.eigenvalues a t with hc
  have hone : c • (1 : Matrix d d ℂ) = V * Matrix.diagonal (fun _ : d => c) * star V := by
    rw [← smul_one_eq_diagonal_const c, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hVstar]
  have hdiff : unitaryEvolution H t - c • (1 : Matrix d d ℂ)
      = V * Matrix.diagonal
          (fun i : d => Complex.exp (-(Complex.I * (t * hH.eigenvalues i))) - c) * star V := by
    rw [unitaryEvolution_spectral hH t, hone, ← Matrix.sub_mul, ← Matrix.mul_sub,
      ← Matrix.diagonal_sub]
  rw [hdiff, l2_opNorm_unitary_conj_eq hV, Matrix.l2_opNorm_diagonal]
  have hentry : ∀ i : d,
      ‖Complex.exp (-(Complex.I * (t * hH.eigenvalues i))) - c‖
        = ‖Complex.exp (-(Complex.I * (t * (hH.eigenvalues i - hH.eigenvalues a)))) - 1‖ := by
    intro i
    have hfactor : Complex.exp (-(Complex.I * (t * hH.eigenvalues i))) - c
        = c * (Complex.exp (-(Complex.I * (t * (hH.eigenvalues i - hH.eigenvalues a)))) - 1) := by
      rw [hc, anchorPhase, mul_sub, mul_one, ← Complex.exp_add]
      congr 2
      ring
    rw [hfactor, norm_mul, hc, anchorPhase]
    have hnorm : ‖Complex.exp (-(Complex.I * (t * hH.eigenvalues a)))‖ = 1 := by
      rw [Complex.norm_exp]
      have hre : (-(Complex.I * ((t : ℂ) * (hH.eigenvalues a : ℂ)))).re = 0 := by
        simp [Complex.mul_re]
      rw [hre, Real.exp_zero]
    rw [hnorm, one_mul]
  simp only [Pi.norm_def]
  congr 1
  refine Finset.sup_congr rfl fun i _ => ?_
  rw [show ‖Complex.exp (-(Complex.I * (t * hH.eigenvalues i))) - c‖₊
      = ‖Complex.exp (-(Complex.I * (t * (hH.eigenvalues i - hH.eigenvalues a)))) - 1‖₊ from
    NNReal.coe_injective (by simpa using hentry i)]

/-- Conjugate phases have the same chord to one. -/
theorem norm_exp_neg_I_mul_sub_one (θ : ℝ) :
    ‖Complex.exp (-(Complex.I * (θ : ℂ))) - 1‖ = ‖Complex.exp (Complex.I * (θ : ℂ)) - 1‖ := by
  have hconj : Complex.exp (-(Complex.I * (θ : ℂ))) - 1
      = (starRingEnd ℂ) (Complex.exp (Complex.I * (θ : ℂ)) - 1) := by
    rw [map_sub, ← Complex.exp_conj]
    simp
  rw [hconj, RCLike.norm_conj]

omit [Nonempty d] in
/-- The chord of a relative phase read on the phase torus. -/
theorem norm_fourier_one_finiteClockPhasePoint_sub_one (E : d → ℝ) (a : d) (t : ℝ)
    (i : {i : d // i ≠ a}) :
    ‖fourier 1 (finiteClockPhasePoint (projectiveFrequency E a) t i) - 1‖
      = ‖Complex.exp (-(Complex.I * ((t : ℂ) * ((E i : ℂ) - (E a : ℂ))))) - 1‖ := by
  have hpoint : finiteClockPhasePoint (projectiveFrequency E a) t i
      = ((t * (E i - E a) / (2 * Real.pi) : ℝ) : UnitAddCircle) := rfl
  rw [hpoint, fourier_coe_apply]
  have harg : 2 * (Real.pi : ℂ) * Complex.I * (1 : ℤ)
        * ((t * (E i - E a) / (2 * Real.pi) : ℝ) : ℂ) / (1 : ℝ)
      = Complex.I * ((t * (E i - E a) : ℝ) : ℂ) := by
    have hpi : (Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast Real.pi_ne_zero
    push_cast
    field_simp
  rw [harg, ← norm_exp_neg_I_mul_sub_one (t * (E i - E a))]
  congr 3
  push_cast
  ring

/-- **The anchored chord target is the projective operator-norm return target.**  A time lies in the
anchored chord target of the relative-phase torus exactly when the evolution is within `ε` of its
anchoring phase in operator norm. -/
theorem mem_anchoredProjectiveReturnTarget_iff_l2_opNorm {H : Matrix d d ℂ} (hH : H.IsHermitian)
    (a : d) (t : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    finiteClockPhasePoint (projectiveFrequency hH.eigenvalues a) t
        ∈ anchoredProjectiveReturnTarget ε
      ↔ ‖unitaryEvolution H t - anchorPhase hH.eigenvalues a t • (1 : Matrix d d ℂ)‖ ≤ ε := by
  rw [l2_opNorm_unitaryEvolution_sub_anchorPhase hH a t, pi_norm_le_iff_of_nonneg hε]
  constructor
  · intro hmem i
    by_cases hia : i = a
    · subst hia
      have hzero : Complex.exp (-(Complex.I * ((t : ℂ)
          * ((hH.eigenvalues i : ℂ) - (hH.eigenvalues i : ℂ))))) - 1 = 0 := by
        norm_num
      rw [hzero, norm_zero]
      exact hε
    · have h := hmem ⟨i, hia⟩
      rw [norm_fourier_one_finiteClockPhasePoint_sub_one hH.eigenvalues a t ⟨i, hia⟩] at h
      exact h
  · intro hall i
    rw [norm_fourier_one_finiteClockPhasePoint_sub_one hH.eigenvalues a t i]
    exact hall i

/-- **The projective operator-norm return set.**  The times at which the evolution is within `ε` of
its anchoring phase. -/
def projectiveReturnTimes (H : Matrix d d ℂ) (hH : H.IsHermitian) (a : d) (ε : ℝ) : Set ℝ :=
  {t | ‖unitaryEvolution H t - anchorPhase hH.eigenvalues a t • (1 : Matrix d d ℂ)‖ ≤ ε}

/-- **The return set is the pullback of the anchored chord target.**  Every measure statement about
the chord target on the relative-phase torus is a statement about the operator-norm return set. -/
theorem projectiveReturnTimes_eq_preimage {H : Matrix d d ℂ} (hH : H.IsHermitian) (a : d)
    {ε : ℝ} (hε : 0 ≤ ε) :
    projectiveReturnTimes H hH a ε
      = (fun t : ℝ => finiteClockPhasePoint (projectiveFrequency hH.eigenvalues a) t) ⁻¹'
          anchoredProjectiveReturnTarget ε := by
  ext t
  exact (mem_anchoredProjectiveReturnTarget_iff_l2_opNorm hH a t hε).symm

/-- **Exact projective return in operator norm is the `ε = 0` target.**  The evolution equals a
scalar multiple of the identity exactly when its relative-phase point lies in the degenerate chord
target. -/
theorem unitaryEvolution_eq_anchorPhase_smul_one_iff {H : Matrix d d ℂ} (hH : H.IsHermitian)
    (a : d) (t : ℝ) :
    unitaryEvolution H t = anchorPhase hH.eigenvalues a t • (1 : Matrix d d ℂ)
      ↔ finiteClockPhasePoint (projectiveFrequency hH.eigenvalues a) t
          ∈ anchoredProjectiveReturnTarget 0 := by
  rw [mem_anchoredProjectiveReturnTarget_iff_l2_opNorm hH a t (le_refl 0)]
  constructor
  · intro h
    rw [h, sub_self, norm_zero]
  · intro h
    have hzero : unitaryEvolution H t - anchorPhase hH.eigenvalues a t • (1 : Matrix d d ℂ) = 0 :=
      norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
    exact sub_eq_zero.mp hzero

end

end GaloisForLFunctions.HTGeometry
