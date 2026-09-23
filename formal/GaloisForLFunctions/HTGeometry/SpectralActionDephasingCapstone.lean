/-
# Angular dephasing from a simple-spectrum member

The dephasing capstones ask for the spectral discriminant to be a nonzero polynomial.  That is not
an extra hypothesis: it is exactly the card's own sentence "the local family contains a
simple-spectrum member", because the discriminant evaluates to the squared Vandermonde of the
spectrum.  Restating the capstones with a simple-spectrum coefficient vector in place of the
polynomial condition puts them in the form the construction of the ensemble actually delivers.

Main results:
* `tendsto_integral_exp_sortedSpectralAction_zero_of_simple_of_disjoint` — **dephasing from a
  simple-spectrum member and a disjoint pair**.
* `tendsto_integral_exp_sortedSpectralAction_zero_of_simple_of_energy_witness` — the same from an
  energy-form witness.
-/
import GaloisForLFunctions.HTGeometry.SpectralEnergyWitnessBridge

open Filter Topology MeasureTheory Metric

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {m D : ℕ}

/-- **Angular dephasing from a simple-spectrum member and a disjoint pair.** -/
theorem tendsto_integral_exp_sortedSpectralAction_zero_of_simple_of_disjoint
    {P : Fin m → Matrix (Fin D) (Fin D) ℂ} (hP : ∀ a, (P a).IsHermitian)
    {θs : Fin m → ℝ}
    (hsimple : Function.Injective (isHermitian_spectralEnsembleMatrix hP θs).eigenvalues)
    (k : Fin D → ℝ) {θ₁ θ₂ : Fin m → ℝ}
    (hdisj : ∀ π₁ π₂ : Equiv.Perm (Fin D),
      (∑ j, k j * (isHermitian_spectralEnsembleMatrix hP θ₁).eigenvalues (π₁ j)) ^ (2 : ℕ)
          * (∑ a, (θ₂ a) ^ (2 : ℕ))
        ≠ (∑ j, k j * (isHermitian_spectralEnsembleMatrix hP θ₂).eigenvalues (π₂ j)) ^ (2 : ℕ)
          * (∑ a, (θ₁ a) ^ (2 : ℕ)))
    (g : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 → ℂ) (hg : Measurable g)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x, ‖g x‖ ≤ C) :
    Filter.Tendsto (fun t : ℝ => ∫ x, g x *
        Complex.exp (-((t * sortedSpectralAction hP k
            (WithLp.ofLp (x : EuclideanSpace ℝ (Fin m))) : ℝ) : ℂ) * Complex.I)
        ∂(MeasureTheory.volume.toSphere))
      (Filter.cocompact ℝ) (nhds 0) :=
  tendsto_integral_exp_sortedSpectralAction_zero_of_disjoint hP
    (spectralDiscriminantPoly_ne_zero hP hsimple) k hdisj g hg hC0 hC

/-- **Angular dephasing from a simple-spectrum member and an energy-form witness.** -/
theorem tendsto_integral_exp_sortedSpectralAction_zero_of_simple_of_energy_witness
    {P : Fin m → Matrix (Fin D) (Fin D) ℂ} (hP : ∀ a, (P a).IsHermitian)
    {θs : Fin m → ℝ}
    (hsimple : Function.Injective (isHermitian_spectralEnsembleMatrix hP θs).eigenvalues)
    (k : Fin D → ℝ) {c : ℝ} (hc : 0 < c)
    (hON : ∀ a b, (P a * P b).trace = if a = b then ((c : ℝ) : ℂ) else 0)
    (hwit : ∀ κ : ℝ, ∃ θ₀ : Fin m → ℝ, ∀ π : Equiv.Perm (Fin D),
      (∑ j, k j * (isHermitian_spectralEnsembleMatrix hP θ₀).eigenvalues (π j)) ^ (2 : ℕ)
        ≠ κ * ∑ i, ((isHermitian_spectralEnsembleMatrix hP θ₀).eigenvalues i) ^ (2 : ℕ))
    (g : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 → ℂ) (hg : Measurable g)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x, ‖g x‖ ≤ C) :
    Filter.Tendsto (fun t : ℝ => ∫ x, g x *
        Complex.exp (-((t * sortedSpectralAction hP k
            (WithLp.ofLp (x : EuclideanSpace ℝ (Fin m))) : ℝ) : ℂ) * Complex.I)
        ∂(MeasureTheory.volume.toSphere))
      (Filter.cocompact ℝ) (nhds 0) :=
  tendsto_integral_exp_sortedSpectralAction_zero_of_energy_witness hP
    (spectralDiscriminantPoly_ne_zero hP hsimple) k hc hON hwit g hg hC0 hC

end

end GaloisForLFunctions.HTGeometry
