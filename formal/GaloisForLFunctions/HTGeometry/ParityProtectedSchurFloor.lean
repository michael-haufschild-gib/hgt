import GaloisForLFunctions.HTGeometry.FiniteConstraintGroupAverage

/-!
# Parity-protected Schur floors

A self-adjoint parity makes its fixed and anti-fixed sectors orthogonal.  Consequently no family
of corrections lying in the fixed sector can reduce energy carried by the anti-fixed sector.
The exact residual energy is the sum of the corrected even energy and the untouched odd energy.

The correction family is arbitrary: it need not come from a finite-rank projection, an optimal
Schur complement, or even a common finite-dimensional boundary space.  Hence the lower floor is
independent of boundary capacity.
-/

open scoped BigOperators

namespace HTGeometry

noncomputable section

section OrthogonalResidual

variable {𝕜 H ι : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [Fintype ι]

/-- **Orthogonal correction law.**  If every corrected `e`-mode is orthogonal to every `o`-mode,
then the residual energy is exactly the sum of the two sector energies. -/
theorem orthogonalBoundaryResidualEnergy_eq
    (e o b : ι → H) (c : ι → 𝕜)
    (horth : ∀ i j, inner 𝕜 (e i - b i) (o j) = 0) :
    ‖∑ i, c i • ((e i + o i) - b i)‖ ^ (2 : ℕ) =
      ‖∑ i, c i • (e i - b i)‖ ^ (2 : ℕ) +
        ‖∑ i, c i • o i‖ ^ (2 : ℕ) := by
  let E : H := ∑ i, c i • (e i - b i)
  let O : H := ∑ i, c i • o i
  have hsum : (∑ i, c i • ((e i + o i) - b i)) = E + O := by
    dsimp [E, O]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    module
  have hEO : inner 𝕜 E O = 0 := by
    dsimp [E, O]
    rw [inner_sum]
    apply Finset.sum_eq_zero
    intro j _
    rw [sum_inner]
    apply Finset.sum_eq_zero
    intro i _
    rw [inner_smul_left, inner_smul_right, horth]
    simp
  rw [hsum]
  simpa [pow_two] using
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero E O hEO

/-- Orthogonal correction can never lower energy below the protected sector. -/
theorem orthogonalBoundaryResidualEnergy_lower
    (e o b : ι → H) (c : ι → 𝕜)
    (horth : ∀ i j, inner 𝕜 (e i - b i) (o j) = 0) :
    ‖∑ i, c i • o i‖ ^ (2 : ℕ) ≤
      ‖∑ i, c i • ((e i + o i) - b i)‖ ^ (2 : ℕ) := by
  rw [orthogonalBoundaryResidualEnergy_eq e o b c horth]
  exact le_add_of_nonneg_left (sq_nonneg _)

end OrthogonalResidual

section ParityResidual

variable {𝕜 H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- Fixed and anti-fixed vectors of a self-adjoint parity are orthogonal.  Only the vectorwise
parity equations are needed; no global finite-dimensionality assumption enters. -/
theorem inner_eq_zero_of_selfAdjointParity_even_odd
    (J : H →L[𝕜] H) (hJ : IsSelfAdjoint J)
    {e o : H} (he : J e = e) (ho : J o = -o) :
    inner 𝕜 e o = 0 := by
  have hsymm := hJ.isSymmetric e o
  change inner 𝕜 (J e) o = inner 𝕜 e (J o) at hsymm
  rw [he, ho, inner_neg_right] at hsymm
  linear_combination hsymm / 2

/-- Single-vector parity decomposition behind the capacity-free floor. -/
theorem parityBoundaryResidualNormSq_eq
    (J : H →L[𝕜] H) (hJ : IsSelfAdjoint J)
    (e o b : H) (he : J e = e) (ho : J o = -o) (hb : J b = b) :
    ‖(e + o) - b‖ ^ (2 : ℕ) = ‖e - b‖ ^ (2 : ℕ) + ‖o‖ ^ (2 : ℕ) := by
  have heven : J (e - b) = e - b := by rw [map_sub, he, hb]
  have horth := inner_eq_zero_of_selfAdjointParity_even_odd J hJ heven ho
  have hsum : (e + o) - b = (e - b) + o := by module
  rw [hsum]
  simpa [pow_two] using
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (e - b) o horth

variable {ι : Type*} [Fintype ι]

/-- **Parity-protected Schur floor law.**  Arbitrary fixed-sector corrections leave the full
anti-fixed packet energy unchanged.  Boundary rank and boundary dimension do not occur. -/
theorem parityBoundaryResidualEnergy_eq
    (J : H →L[𝕜] H) (hJ : IsSelfAdjoint J)
    (e o b : ι → H) (c : ι → 𝕜)
    (he : ∀ i, J (e i) = e i)
    (ho : ∀ i, J (o i) = -o i)
    (hb : ∀ i, J (b i) = b i) :
    ‖∑ i, c i • ((e i + o i) - b i)‖ ^ (2 : ℕ) =
      ‖∑ i, c i • (e i - b i)‖ ^ (2 : ℕ) +
        ‖∑ i, c i • o i‖ ^ (2 : ℕ) := by
  apply orthogonalBoundaryResidualEnergy_eq e o b c
  intro i j
  apply inner_eq_zero_of_selfAdjointParity_even_odd J hJ
  · rw [map_sub, he, hb]
  · exact ho j

/-- No even correction family, of any capacity, can lower packet energy below its odd sector. -/
theorem parityBoundaryResidualEnergy_lower
    (J : H →L[𝕜] H) (hJ : IsSelfAdjoint J)
    (e o b : ι → H) (c : ι → 𝕜)
    (he : ∀ i, J (e i) = e i)
    (ho : ∀ i, J (o i) = -o i)
    (hb : ∀ i, J (b i) = b i) :
    ‖∑ i, c i • o i‖ ^ (2 : ℕ) ≤
      ‖∑ i, c i • ((e i + o i) - b i)‖ ^ (2 : ℕ) := by
  rw [parityBoundaryResidualEnergy_eq J hJ e o b c he ho hb]
  exact le_add_of_nonneg_left (sq_nonneg _)

end ParityResidual

end


end HTGeometry
