import GaloisForLFunctions.HTGeometry.FiniteUnitaryAdjointAutocorrelationLaw

/-!
# Energy-defect law for finite unitary dynamics

For a Hermitian source `H`, loss of adjoint autocorrelation under a unitary `U` is exactly half
the squared Hilbert--Schmidt energy of the commutator `[H,U]`.  Thus full source memory is
equivalent to exact commutation.  Combining this identity with the exact Haar second moment gives
a gap-free tail bound for an approximate-centralizer tube.
-/

open scoped ComplexConjugate
open MeasureTheory MeasureTheory.Measure TopologicalSpace
open scoped BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Squared Hilbert--Schmidt energy of a finite complex matrix. -/
def finiteMatrixHilbertSchmidtEnergy
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) : ℝ :=
  (Matrix.trace (star A * A)).re

theorem finiteMatrixHilbertSchmidtEnergy_eq_sum_normSq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) :
    finiteMatrixHilbertSchmidtEnergy A =
      ∑ i, ∑ j, Complex.normSq (A j i) := by
  simp [finiteMatrixHilbertSchmidtEnergy, Matrix.trace, Matrix.mul_apply,
    star, Matrix.conjTranspose_apply, Complex.normSq_apply]

theorem finiteMatrixHilbertSchmidtEnergy_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) :
    0 ≤ finiteMatrixHilbertSchmidtEnergy A := by
  rw [finiteMatrixHilbertSchmidtEnergy_eq_sum_normSq]
  exact Finset.sum_nonneg fun i _hi =>
    Finset.sum_nonneg fun j _hj => Complex.normSq_nonneg (A j i)

theorem finiteMatrixHilbertSchmidtEnergy_eq_zero_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) :
    finiteMatrixHilbertSchmidtEnergy A = 0 ↔ A = 0 := by
  rw [finiteMatrixHilbertSchmidtEnergy_eq_sum_normSq]
  constructor
  · intro h
    ext i j
    have houter :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _hi =>
        Finset.sum_nonneg fun j _hj => Complex.normSq_nonneg (A j i))).mp h
        j (Finset.mem_univ j)
    have hinner :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _hi =>
        Complex.normSq_nonneg (A i j))).mp houter i (Finset.mem_univ i)
    exact Complex.normSq_eq_zero.mp hinner
  · rintro rfl
    simp

/-- **Energy-defect identity.** The loss of a Hermitian source's adjoint autocorrelation is
exactly half the squared Hilbert--Schmidt commutator energy. -/
theorem finiteUnitary_commutator_hilbertSchmidtEnergy_eq_autocorrelationDefect
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (U : Matrix.unitaryGroup ι ℂ) :
    finiteMatrixHilbertSchmidtEnergy
        (H * (U : Matrix ι ι ℂ) - (U : Matrix ι ι ℂ) * H) =
      2 * ((Matrix.trace (H * H)).re -
        (Matrix.trace
          (H * star (U : Matrix ι ι ℂ) * H * (U : Matrix ι ι ℂ))).re) := by
  have hstarH : star H = H := hH
  have hunit : star (U : Matrix ι ι ℂ) * (U : Matrix ι ι ℂ) = 1 :=
    Unitary.coe_star_mul_self U
  have htrace1 :
      Matrix.trace
          (star (U : Matrix ι ι ℂ) * H * H * (U : Matrix ι ι ℂ)) =
        Matrix.trace (H * H) := by
    calc
      _ = Matrix.trace
          ((U : Matrix ι ι ℂ) *
            (star (U : Matrix ι ι ℂ) * H * H)) := by
            simpa only [Matrix.mul_assoc] using
              (Matrix.trace_mul_comm
                (star (U : Matrix ι ι ℂ) * H * H) (U : Matrix ι ι ℂ))
      _ = Matrix.trace
          (((U : Matrix ι ι ℂ) * star (U : Matrix ι ι ℂ)) * H * H) := by
            congr 1
            noncomm_ring
      _ = Matrix.trace (H * H) := by
        rw [show (U : Matrix ι ι ℂ) * star (U : Matrix ι ι ℂ) = 1 from
          Unitary.coe_mul_star_self U]
        simp
  have htrace2 :
      Matrix.trace
          (star (U : Matrix ι ι ℂ) * H * (U : Matrix ι ι ℂ) * H) =
        Matrix.trace
          (H * star (U : Matrix ι ι ℂ) * H * (U : Matrix ι ι ℂ)) := by
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_comm
        (star (U : Matrix ι ι ℂ) * H * (U : Matrix ι ι ℂ)) H)
  unfold finiteMatrixHilbertSchmidtEnergy
  rw [star_sub, star_mul, star_mul, hstarH]
  have hexpand :
      (star (U : Matrix ι ι ℂ) * H - H * star (U : Matrix ι ι ℂ)) *
          (H * (U : Matrix ι ι ℂ) - (U : Matrix ι ι ℂ) * H) =
        star (U : Matrix ι ι ℂ) * H * H * (U : Matrix ι ι ℂ) -
          star (U : Matrix ι ι ℂ) * H * (U : Matrix ι ι ℂ) * H -
          H * star (U : Matrix ι ι ℂ) * H * (U : Matrix ι ι ℂ) +
          H * H := by
    calc
      _ = star (U : Matrix ι ι ℂ) * H * H * (U : Matrix ι ι ℂ) -
          star (U : Matrix ι ι ℂ) * H * (U : Matrix ι ι ℂ) * H -
          H * star (U : Matrix ι ι ℂ) * H * (U : Matrix ι ι ℂ) +
          H * (star (U : Matrix ι ι ℂ) * (U : Matrix ι ι ℂ)) * H := by
            noncomm_ring
      _ = _ := by rw [hunit]; noncomm_ring
  rw [hexpand]
  simp only [Matrix.trace_add, Matrix.trace_sub, Complex.add_re, Complex.sub_re]
  rw [htrace1, htrace2]
  ring

/-- Full adjoint autocorrelation is equivalent to exact commutation with the source. -/
theorem finiteUnitary_full_adjointAutocorrelation_iff_commute
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (U : Matrix.unitaryGroup ι ℂ) :
    (Matrix.trace
        (H * star (U : Matrix ι ι ℂ) * H * (U : Matrix ι ι ℂ))).re =
        (Matrix.trace (H * H)).re ↔
      H * (U : Matrix ι ι ℂ) = (U : Matrix ι ι ℂ) * H := by
  constructor
  · intro hfull
    have hzero :
        finiteMatrixHilbertSchmidtEnergy
            (H * (U : Matrix ι ι ℂ) - (U : Matrix ι ι ℂ) * H) = 0 := by
      rw [finiteUnitary_commutator_hilbertSchmidtEnergy_eq_autocorrelationDefect
        H hH U, hfull]
      ring
    have hcomm := (finiteMatrixHilbertSchmidtEnergy_eq_zero_iff
      (H * (U : Matrix ι ι ℂ) - (U : Matrix ι ι ℂ) * H)).mp hzero
    exact sub_eq_zero.mp hcomm
  · intro hcomm
    have hzero :
        finiteMatrixHilbertSchmidtEnergy
            (H * (U : Matrix ι ι ℂ) - (U : Matrix ι ι ℂ) * H) = 0 := by
      apply (finiteMatrixHilbertSchmidtEnergy_eq_zero_iff _).2
      exact sub_eq_zero.mpr hcomm
    rw [finiteUnitary_commutator_hilbertSchmidtEnergy_eq_autocorrelationDefect
      H hH U] at hzero
    linarith

/-- **Gap-free approximate-centralizer Haar tail.** For a nonzero traceless Hermitian source,
the Haar probability that commutator energy is no larger than source energy is at most
`4 / (D^2 - 1)`. -/
theorem haar_measureReal_commutatorEnergy_le_traceEnergy_le
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (d : ℕ) (e : κ ≃ Fin 2 ⊕ Fin d)
    (H : Matrix κ κ ℂ) (hH : H.IsHermitian)
    (htrace : H.trace = 0) (hzero : H ≠ 0) :
    (finiteUnitaryHaar κ).real
        {U | finiteMatrixHilbertSchmidtEnergy
            (H * (U : Matrix κ κ ℂ) - (U : Matrix κ κ ℂ) * H) ≤
          (Matrix.trace (H * H)).re} ≤
      4 / ((((d + 2 : ℕ) : ℝ) ^ 2) - 1) := by
  apply (measureReal_mono (μ := finiteUnitaryHaar κ) ?_).trans
    (haar_measureReal_half_traceEnergy_adjointAutocorrelation_le
      d e H hH htrace hzero)
  intro U hdefect
  change finiteMatrixHilbertSchmidtEnergy
      (H * (U : Matrix κ κ ℂ) - (U : Matrix κ κ ℂ) * H) ≤
    (Matrix.trace (H * H)).re at hdefect
  let S : ℝ := (Matrix.trace (H * H)).re
  let F : ℝ := (Matrix.trace
    (H * star (U : Matrix κ κ ℂ) * H * (U : Matrix κ κ ℂ))).re
  have hS : 0 < S := by
    change 0 < (Matrix.trace (H * H)).re
    rw [trace_mul_self_re_eq_sum_sq_eigenvalues H hH]
    exact sum_sq_eigenvalues_pos_of_ne_zero H hH hzero
  have hid :
      finiteMatrixHilbertSchmidtEnergy
          (H * (U : Matrix κ κ ℂ) - (U : Matrix κ κ ℂ) * H) =
        2 * (S - F) := by
    exact finiteUnitary_commutator_hilbertSchmidtEnergy_eq_autocorrelationDefect H hH U
  have hF : S / 2 ≤ F := by linarith
  change (S / 2) ^ 2 ≤ F ^ 2
  nlinarith

end

end GaloisForLFunctions.HTGeometry
