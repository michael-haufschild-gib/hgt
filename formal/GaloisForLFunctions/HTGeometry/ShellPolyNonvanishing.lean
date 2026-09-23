/-
# Nonvanishing of the shell polynomial

The shell polynomial is nonzero as soon as it has one nonzero value, and its value at a coordinate
vector is the product over labellings of the criticality square sums; each of those is nonzero as
soon as one coordinate direction contributes.  So nonvanishing reduces to a single witness: one
coordinate vector at which no labelling of the spectrum is critical.

Main results:
* `eval_jointCriticalitySquareSum_ne_zero_of_exists` — one direction suffices.
* `eval_shellPoly_ne_zero_of_forall` — one witness vector suffices.
* `shellPoly_ne_zero_of_eval_ne_zero` — **hence the polynomial is nonzero**.
-/
import GaloisForLFunctions.HTGeometry.ShellPolyScaling

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {N D : ℕ}

theorem eval_jointCriticalitySquareSum_eq (M : ℕ) (c : ℕ → MvPolynomial (Fin N) ℝ)
    (k : Fin D → ℝ) (π : Equiv.Perm (Fin D)) (x : Fin D ⊕ Fin N → ℝ) :
    MvPolynomial.eval x (jointCriticalitySquareSum M c k π)
      = ∑ i : Fin N, (MvPolynomial.eval x (jointCriticality M c k π i)) ^ (2 : ℕ) := by
  simp only [jointCriticalitySquareSum]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_pow]

set_option maxHeartbeats 1000000 in
/-- One coordinate direction with a nonzero criticality expression makes the square sum nonzero. -/
theorem eval_jointCriticalitySquareSum_ne_zero_of_exists (M : ℕ)
    (c : ℕ → MvPolynomial (Fin N) ℝ) (k : Fin D → ℝ) (π : Equiv.Perm (Fin D))
    (x : Fin D ⊕ Fin N → ℝ) {i : Fin N}
    (h : MvPolynomial.eval x (jointCriticality M c k π i) ≠ 0) :
    MvPolynomial.eval x (jointCriticalitySquareSum M c k π) ≠ 0 := by
  rw [eval_jointCriticalitySquareSum_eq]
  intro hzero
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin N))) => sq_nonneg
      (MvPolynomial.eval x (jointCriticality M c k π j)))).mp hzero i (Finset.mem_univ i)
  exact h ((pow_eq_zero_iff two_ne_zero).mp hterm)

/-- **One witness vector at which no labelling is critical makes the shell polynomial value
nonzero.** -/
theorem eval_shellPoly_ne_zero_of_forall {P : Fin N → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a, (P a).IsHermitian) (M : ℕ) (c : ℕ → MvPolynomial (Fin N) ℝ) (k : Fin D → ℝ)
    (G : MvPolynomial (Fin N) ℝ)
    (hG : ∀ θ : Fin N → ℝ, MvPolynomial.eval θ G
      = MvPolynomial.eval
          (Sum.elim (fun i => (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues i) θ)
          (jointCriticalProduct M c k))
    (θ₀ : Fin N → ℝ)
    (h : ∀ π : Equiv.Perm (Fin D),
      MvPolynomial.eval
          (Sum.elim (fun i => (isHermitian_spectralEnsembleMatrix hP θ₀).eigenvalues i) θ₀)
          (jointCriticalitySquareSum M c k π) ≠ 0) :
    MvPolynomial.eval θ₀ G ≠ 0 := by
  classical
  rw [hG θ₀]
  simp only [jointCriticalProduct]
  rw [map_prod]
  exact Finset.prod_ne_zero_iff.mpr fun π _ => h π

/-- **A polynomial with one nonzero value is nonzero.** -/
theorem shellPoly_ne_zero_of_eval_ne_zero {G : MvPolynomial (Fin N) ℝ} {θ₀ : Fin N → ℝ}
    (h : MvPolynomial.eval θ₀ G ≠ 0) : G ≠ 0 := by
  intro hc
  rw [hc] at h
  exact h (by simp)

end

end GaloisForLFunctions.HTGeometry
