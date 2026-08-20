/-
# The energy form of the nonconstancy witness

The nonconstancy criterion asks for a coefficient vector at which no labelling of the spectrum
satisfies `(∑ⱼ kⱼλⱼ)² = b² ∑ₐθₐ²`, while the quadratic-rate rigidity of the extension architecture
produces one at which no labelling satisfies `(∑ⱼ kⱼλⱼ)² = κ ∑ⱼλⱼ²`.  For a family orthonormal in
the trace pairing the two energies agree up to the normalising constant, so the second witness is
the first.

Main results:
* `sum_sq_eigenvalues_of_orthonormal` — the spectral energy of an orthonormal family is the
  coefficient energy.
* `exists_witness_of_energy_witness` — **the energy-form witness is a coordinate-form witness**.
* `tendsto_integral_exp_sortedSpectralAction_zero_of_energy_witness` — **angular dephasing from an
  energy-form witness**.
-/
import GaloisForLFunctions.HTGeometry.SpectralActionWitness

open Filter Topology MeasureTheory Metric

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {N D : ℕ}

/-- **The spectral energy of a trace-orthonormal family is the coefficient energy.** -/
theorem sum_sq_eigenvalues_of_orthonormal {P : Fin N → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a, (P a).IsHermitian) {c : ℝ}
    (hON : ∀ a b, (P a * P b).trace = if a = b then ((c : ℝ) : ℂ) else 0)
    (θ : Fin N → ℝ) :
    ∑ i, ((isHermitian_spectralEnsembleMatrix hP θ).eigenvalues i) ^ 2 = c * ∑ a, (θ a) ^ 2 := by
  classical
  rw [sum_sq_eigenvalues_eq_trace_sq_re, trace_sq_spectralEnsembleMatrix]
  have hinner : ∀ a : Fin N,
      (∑ b, ((θ a : ℂ) * (θ b : ℂ)) * (P a * P b).trace)
        = ((((θ a) ^ 2 * c : ℝ)) : ℂ) := by
    intro a
    rw [Finset.sum_eq_single a]
    · rw [hON a a, if_pos rfl]
      push_cast
      ring
    · intro b _ hb
      rw [hON a b, if_neg (Ne.symm hb), mul_zero]
    · intro hc
      exact absurd (Finset.mem_univ a) hc
  rw [Finset.sum_congr rfl fun a _ => hinner a]
  rw [← Complex.ofReal_sum, Complex.ofReal_re, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- **The energy-form witness is a coordinate-form witness.** -/
theorem exists_witness_of_energy_witness {P : Fin N → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a, (P a).IsHermitian) (k : Fin D → ℝ) {c : ℝ} (hc : 0 < c)
    (hON : ∀ a b, (P a * P b).trace = if a = b then ((c : ℝ) : ℂ) else 0)
    (hwit : ∀ κ : ℝ, ∃ θ₀ : Fin N → ℝ, ∀ π : Equiv.Perm (Fin D),
      (∑ j, k j * (isHermitian_spectralEnsembleMatrix hP θ₀).eigenvalues (π j)) ^ 2
        ≠ κ * ∑ i, ((isHermitian_spectralEnsembleMatrix hP θ₀).eigenvalues i) ^ 2)
    (b : ℝ) :
    ∃ θ₀ : Fin N → ℝ, ∀ π : Equiv.Perm (Fin D),
      (∑ j, k j * (isHermitian_spectralEnsembleMatrix hP θ₀).eigenvalues (π j)) ^ 2
        ≠ b ^ 2 * (∑ a, (θ₀ a) ^ 2) := by
  obtain ⟨θ₀, hθ₀⟩ := hwit (b ^ 2 / c)
  refine ⟨θ₀, fun π hπ => hθ₀ π ?_⟩
  rw [sum_sq_eigenvalues_of_orthonormal hP hON θ₀, hπ]
  field_simp

section Dephasing

variable {m : ℕ}

/-- **Angular dephasing from an energy-form witness.** -/
theorem tendsto_integral_exp_sortedSpectralAction_zero_of_energy_witness
    {P : Fin m → Matrix (Fin D) (Fin D) ℂ} (hP : ∀ a, (P a).IsHermitian)
    (hDisc : spectralDiscriminantPoly P ≠ 0) (k : Fin D → ℝ) {c : ℝ} (hc : 0 < c)
    (hON : ∀ a b, (P a * P b).trace = if a = b then ((c : ℝ) : ℂ) else 0)
    (hwit : ∀ κ : ℝ, ∃ θ₀ : Fin m → ℝ, ∀ π : Equiv.Perm (Fin D),
      (∑ j, k j * (isHermitian_spectralEnsembleMatrix hP θ₀).eigenvalues (π j)) ^ 2
        ≠ κ * ∑ i, ((isHermitian_spectralEnsembleMatrix hP θ₀).eigenvalues i) ^ 2)
    (g : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 → ℂ) (hg : Measurable g)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x, ‖g x‖ ≤ C) :
    Filter.Tendsto (fun t : ℝ => ∫ x, g x *
        Complex.exp (-((t * sortedSpectralAction hP k
            (WithLp.ofLp (x : EuclideanSpace ℝ (Fin m))) : ℝ) : ℂ) * Complex.I)
        ∂(MeasureTheory.volume.toSphere))
      (Filter.cocompact ℝ) (nhds 0) :=
  tendsto_integral_exp_sortedSpectralAction_zero_of_witness hP hDisc k
    (exists_witness_of_energy_witness hP k hc hON hwit) g hg hC0 hC

end Dephasing

end

end GaloisForLFunctions.HTGeometry
