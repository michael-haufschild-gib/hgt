import GaloisForLFunctions.RHTower.StaticChoiQuantitativeRecurrenceUpperLaw
import GaloisForLFunctions.HTGeometry.SpectralObservedOrbitDimension

/-!
# Choi survival amplitude equals the normalized trace of the evolution

For a Hermitian matrix `H` on `ℂ^d` with eigenvalues `λ_i`, the trace of the unitary evolution
`U(t)` is the spectral phase sum `Σ_i e^(-i t λ_i)`. Consequently the overlap between the
spectral Choi state of `H` at time `t` and at time `0` has the same modulus as the normalized
trace `d^(-1) tr U(t)`, which links the static Choi survival amplitude to the physical
normalized trace of the evolution.

## Main results

- `trace_unitaryEvolution_eq_sum_spectralPhase`: `tr U(t) = Σ_i exp(-i t λ_i)`.
- `norm_inner_staticSpectralChoiVector_zero_eq_norm_normalizedTrace_unitaryEvolution`:
  `|⟨Choi(t), Choi(0)⟩| = |d^(-1) tr U(t)|` for `d > 0`.

## Hypotheses

Unconditional; the only assumptions are that `H` is Hermitian and, for the second result, `d > 0`.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator
open Matrix

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- For Hermitian `H` with eigenvalues `λ_i`, the trace of the unitary evolution at time `t` is
the spectral phase sum `Σ_i exp(-i t λ_i)`. -/
theorem trace_unitaryEvolution_eq_sum_spectralPhase
    {d : ℕ} {H : Matrix (Fin d) (Fin d) ℂ}
    (hH : H.IsHermitian) (t : ℝ) :
    Matrix.trace (unitaryEvolution H t) =
      ∑ i, Complex.exp (-(Complex.I * (t * hH.eigenvalues i))) := by
  let V : Matrix (Fin d) (Fin d) ℂ := hH.eigenvectorUnitary
  let D : Matrix (Fin d) (Fin d) ℂ :=
    Matrix.diagonal (fun i => Complex.exp (-(Complex.I * (t * hH.eigenvalues i))))
  have hV : star V * V = 1 := hH.eigenvectorUnitary.2.1
  rw [unitaryEvolution_spectral hH t]
  change Matrix.trace (V * D * star V) = _
  calc
    Matrix.trace (V * D * star V) = Matrix.trace (V * (D * star V)) := by
      rw [Matrix.mul_assoc]
    _ = Matrix.trace ((D * star V) * V) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace D := by rw [Matrix.mul_assoc, hV, Matrix.mul_one]
    _ = _ := by simp [D]

/-- For Hermitian `H` on `ℂ^d` with `d > 0`, the modulus of the overlap of the spectral Choi states at
times `t` and `0` equals the modulus of the normalized trace `d^(-1) tr U(t)`. -/
theorem norm_inner_staticSpectralChoiVector_zero_eq_norm_normalizedTrace_unitaryEvolution
    {d : ℕ} (hd : 0 < d) {H : Matrix (Fin d) (Fin d) ℂ}
    (hH : H.IsHermitian) (t : ℝ) :
    ‖inner ℂ
        (staticSpectralChoiVector d t hH.eigenvalues)
        (staticSpectralChoiVector d 0 hH.eigenvalues)‖ =
      ‖(d : ℂ)⁻¹ * Matrix.trace (unitaryEvolution H t)‖ := by
  rw [norm_inner_symm, inner_staticSpectralChoiVector_zero hd,
    trace_unitaryEvolution_eq_sum_spectralPhase hH t]
  let positive : Fin d → ℂ := fun i =>
    Complex.exp (Complex.I * (((t * hH.eigenvalues i : ℝ) : ℂ)))
  let negative : Fin d → ℂ := fun i =>
    Complex.exp (-(Complex.I * (((t * hH.eigenvalues i : ℝ) : ℂ))))
  have hphase : ∀ i, negative i = starRingEnd ℂ (positive i) := by
    intro i
    dsimp [negative, positive]
    rw [← Complex.exp_conj]
    congr 1
    simp
  have hsum : ∑ i, negative i = starRingEnd ℂ (∑ i, positive i) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => hphase i
  simp only [finiteSpectralSurvivalAmplitude, uniformSurvivalWeight,
    finiteObserverHamiltonianVertexPhase, Complex.ofReal_inv,
    Complex.ofReal_natCast]
  push_cast
  dsimp only [positive, negative] at hsum
  push_cast at hsum
  rw [← Finset.mul_sum, hsum]
  rw [show (d : ℂ)⁻¹ *
      starRingEnd ℂ (∑ i, Complex.exp (Complex.I * (↑t * ↑(hH.eigenvalues i)))) =
      starRingEnd ℂ ((d : ℂ)⁻¹ *
        ∑ i, Complex.exp (Complex.I * (↑t * ↑(hH.eigenvalues i)))) by simp]
  exact Complex.norm_conj _ |>.symm

end

end RHTower
