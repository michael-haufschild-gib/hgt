import GaloisForLFunctions.HTGeometry.WaveEnergyFlux

/-!
# The flux identity with a source

The inhomogeneous clock equation `∂ₜ²u = Δu + Vu + f` has the same energy computation as the
homogeneous one, with one extra term: the source pairs with the time derivative. Everything else
cancels exactly as before, so

`∫ ∂ₜ(energy density) = 2∫ ((V+1)·u·∂ₜu + f·∂ₜu)`.

The extra pairing is what a Picard iteration on the Duhamel formula controls, so this identity is
the entry point to an existence proof by the energy method.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped ContDiff

section Source

variable {d : ℕ} {u V f : ℝ × (Fin d → ℝ) → ℝ} {K : Set (Fin d → ℝ)}

/-- The clock equation with a source. -/
def SolvesWaveEqSource (u V f : ℝ × (Fin d → ℝ) → ℝ) : Prop :=
  ∀ p : ℝ × (Fin d → ℝ), waveDirDeriv (timeDir d) (waveDirDeriv (timeDir d) u) p
    = (∑ i : Fin d, waveDirDeriv (spaceDir d i) (waveDirDeriv (spaceDir d i) u) p)
      + V p * u p + f p

/-- A source-free solution is the special case of a vanishing source. -/
theorem solvesWaveEqSource_zero (h : SolvesWaveEq u V) :
    SolvesWaveEqSource u V (fun _ => 0) := by
  intro p
  rw [show ((fun _ : ℝ × (Fin d → ℝ) => (0 : ℝ)) p) = 0 from rfl, add_zero]
  exact h p

/-- **A source is absorbed into the potential wherever the field does not vanish**, so the
inhomogeneous equation is the homogeneous one for a modified potential off the zero set. -/
theorem solvesWaveEq_of_solvesWaveEqSource (h : SolvesWaveEqSource u V f)
    {p : ℝ × (Fin d → ℝ)} (hp : u p ≠ 0) :
    waveDirDeriv (timeDir d) (waveDirDeriv (timeDir d) u) p
      = (∑ i : Fin d, waveDirDeriv (spaceDir d i) (waveDirDeriv (spaceDir d i) u) p)
        + (V p + f p / u p) * u p := by
  rw [h p]
  field_simp
  ring

/-- **The pointwise energy identity with a source.** -/
theorem waveDirDeriv_energyDensity_source (hu : ContDiff ℝ ∞ u)
    (hsolve : SolvesWaveEqSource u V f) (p : ℝ × (Fin d → ℝ)) :
    waveDirDeriv (timeDir d) (energyDensity u) p
      = 2 * (waveDirDeriv (timeDir d) u p
          * ((∑ i : Fin d, waveDirDeriv (spaceDir d i)
              (waveDirDeriv (spaceDir d i) u) p) + V p * u p + f p))
        + (∑ i : Fin d, 2 * (waveDirDeriv (spaceDir d i) u p
            * waveDirDeriv (timeDir d) (waveDirDeriv (spaceDir d i) u) p))
        + 2 * (u p * waveDirDeriv (timeDir d) u p) := by
  rw [waveDirDeriv_energyDensity hu p, hsolve p]

end Source

end GaloisForLFunctions.HTGeometry
