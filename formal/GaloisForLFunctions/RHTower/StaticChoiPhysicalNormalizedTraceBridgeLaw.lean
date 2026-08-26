import GaloisForLFunctions.RHTower.StaticChoiQuantitativeRecurrenceUpperLaw
import GaloisForLFunctions.HTGeometry.SpectralObservedOrbitDimension

open scoped BigOperators Matrix Matrix.Norms.L2Operator
open Matrix

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

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
