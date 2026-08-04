import GaloisForLFunctions.HTGeometry.WaveDecayingL2Sub
import GaloisForLFunctions.HTGeometry.WaveDecayingReflection

/-!
# Uniqueness for square-integrable solutions

Collecting the square-integrability conditions into one predicate makes them closed under
differences, and the difference of two solutions with the same Cauchy data has vanishing initial
energy. So two square-integrable solutions of the same clock equation with the same data agree
everywhere — the two-solution uniqueness statement in the class that a Fourier construction can
meet.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped ContDiff

section L2Uniqueness

variable {d : ℕ} {u₁ u₂ V : ℝ × (Fin d → ℝ) → ℝ}

/-- A smooth field whose slices, time derivative and first two spatial derivatives are square
integrable on every slice. -/
structure L2Solution (u : ℝ × (Fin d → ℝ) → ℝ) : Prop where
  /-- The field is smooth. -/
  smooth : ContDiff ℝ ∞ u
  /-- The slices are square integrable. -/
  sliceL2 : ∀ t : ℝ, MemLp (slice u t) 2 (volume : Measure (Fin d → ℝ))
  /-- So is the time derivative. -/
  dirL2 : ∀ t : ℝ, MemLp (slice (waveDirDeriv (timeDir d) u) t) 2
    (volume : Measure (Fin d → ℝ))
  /-- So is each spatial derivative. -/
  spaceL2 : ∀ (t : ℝ) (i : Fin d), MemLp
    (fun x : Fin d → ℝ => waveDirDeriv (spaceDir d i) u (t, x)) 2
    (volume : Measure (Fin d → ℝ))
  /-- So is each coordinate derivative of a slice. -/
  gradL2 : ∀ (t : ℝ) (i : Fin d), MemLp (coordPartial i (slice u t)) 2
    (volume : Measure (Fin d → ℝ))
  /-- So is each coordinate derivative of the time derivative. -/
  gradDirL2 : ∀ (t : ℝ) (i : Fin d),
    MemLp (coordPartial i (slice (waveDirDeriv (timeDir d) u) t)) 2
      (volume : Measure (Fin d → ℝ))
  /-- And each second coordinate derivative. -/
  lapL2 : ∀ (t : ℝ) (i : Fin d), MemLp (coordPartial i (coordPartial i (slice u t))) 2
    (volume : Measure (Fin d → ℝ))

/-- **The class is closed under differences.** -/
theorem L2Solution.sub (h₁ : L2Solution u₁) (h₂ : L2Solution u₂) :
    L2Solution (fun q => u₁ q - u₂ q) := by
  have hsl₁ : ∀ t : ℝ, ContDiff ℝ ∞ (slice u₁ t) := fun t => contDiff_slice h₁.smooth t
  have hsl₂ : ∀ t : ℝ, ContDiff ℝ ∞ (slice u₂ t) := fun t => contDiff_slice h₂.smooth t
  refine
    { smooth := h₁.smooth.sub h₂.smooth
      sliceL2 := fun t => memLp_two_slice_sub (h₁.sliceL2 t) (h₂.sliceL2 t)
      dirL2 := fun t =>
        memLp_two_slice_dirDeriv_sub h₁.smooth h₂.smooth (h₁.dirL2 t) (h₂.dirL2 t)
      spaceL2 := fun t i =>
        memLp_two_slice_dirDeriv_sub h₁.smooth h₂.smooth (h₁.spaceL2 t i) (h₂.spaceL2 t i)
      gradL2 := fun t i =>
        memLp_two_coordPartial_slice_sub h₁.smooth h₂.smooth (h₁.gradL2 t i) (h₂.gradL2 t i)
      gradDirL2 := fun t i => ?_
      lapL2 := fun t i => ?_ }
  · have heq : slice (waveDirDeriv (timeDir d) fun q => u₁ q - u₂ q) t
        = fun x : Fin d → ℝ => slice (waveDirDeriv (timeDir d) u₁) t x
          - slice (waveDirDeriv (timeDir d) u₂) t x := by
      funext x
      exact waveDirDeriv_sub h₁.smooth h₂.smooth _ (t, x)
    rw [heq, coordPartial_sub_fun (contDiff_slice (contDiff_dirDeriv h₁.smooth _) t)
      (contDiff_slice (contDiff_dirDeriv h₂.smooth _) t)]
    exact (h₁.gradDirL2 t i).sub (h₂.gradDirL2 t i)
  · rw [slice_sub, coordPartial_sub_fun (hsl₁ t) (hsl₂ t),
      coordPartial_sub_fun (contDiff_coordPartial (hsl₁ t) i)
        (contDiff_coordPartial (hsl₂ t) i)]
    exact (h₁.lapL2 t i).sub (h₂.lapL2 t i)

/-- **Uniqueness for square-integrable solutions.** -/
theorem eq_of_solvesWaveEq_of_memLp (h₁ : L2Solution u₁) (h₂ : L2Solution u₂)
    (hs₁ : SolvesWaveEq u₁ V) (hs₂ : SolvesWaveEq u₂ V) (hVcont : Continuous V)
    {M : ℝ} (hM : ∀ p, |V p| ≤ M)
    (hdom : ∀ t : ℝ, ∃ bound : (Fin d → ℝ) → ℝ,
      Integrable bound (volume : Measure (Fin d → ℝ)) ∧
        ∀ s ∈ Metric.ball t 1, ∀ x : Fin d → ℝ,
          ‖waveDirDeriv (timeDir d) (energyDensity fun q => u₁ q - u₂ q) (s, x)‖ ≤ bound x)
    (hval : ∀ x : Fin d → ℝ, u₁ ((0 : ℝ), x) = u₂ ((0 : ℝ), x))
    (hder : ∀ x : Fin d → ℝ, waveDirDeriv (timeDir d) u₁ ((0 : ℝ), x)
      = waveDirDeriv (timeDir d) u₂ ((0 : ℝ), x))
    (t : ℝ) (x : Fin d → ℝ) : u₁ (t, x) = u₂ (t, x) := by
  have hsub := h₁.sub h₂
  have hdec : DecayingSolution (fun q => u₁ q - u₂ q) V :=
    decayingSolution_of_memLp_two hsub.smooth (solvesWaveEq_sub h₁.smooth h₂.smooth hs₁ hs₂)
      hsub.sliceL2 hsub.dirL2 hsub.spaceL2 hsub.gradL2 hsub.gradDirL2 hsub.lapL2
      hVcont ⟨M, hM⟩ hdom
  have hval' : ∀ y : Fin d → ℝ, (fun q : ℝ × (Fin d → ℝ) => u₁ q - u₂ q) ((0 : ℝ), y) = 0 := by
    intro y
    show u₁ ((0 : ℝ), y) - u₂ ((0 : ℝ), y) = 0
    rw [hval y, sub_self]
  have hder' : ∀ y : Fin d → ℝ,
      waveDirDeriv (timeDir d) (fun q : ℝ × (Fin d → ℝ) => u₁ q - u₂ q) ((0 : ℝ), y) = 0 := by
    intro y
    rw [waveDirDeriv_sub h₁.smooth h₂.smooth, hder y, sub_self]
  have h0 : waveEnergy (fun q : ℝ × (Fin d → ℝ) => u₁ q - u₂ q) 0 = 0 :=
    waveEnergy_eq_zero_of_slice_zero hsub.smooth hval' hder'
  have hvan := eq_zero_of_waveEnergy_zero_of_decaying_all hdec hM h0 t x
  have : u₁ (t, x) - u₂ (t, x) = 0 := hvan
  linarith

end L2Uniqueness

end GaloisForLFunctions.HTGeometry
