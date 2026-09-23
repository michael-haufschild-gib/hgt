import GaloisForLFunctions.HTGeometry.WaveEnergyDecaying
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# A square-integrability criterion for the decay hypotheses

The bundle of hypotheses behind the decaying estimate is a list of integrability statements about
products of two functions, so square integrability of each factor implies all of them by
Cauchy–Schwarz. That is the practical criterion: a solution whose slices, their spatial derivatives
and their second spatial derivatives are square integrable, together with the time derivative and
its spatial derivatives, satisfies every field of the bundle except the local domination in time.

This is the form in which a Fourier construction can meet the hypotheses — Plancherel turns square
integrability of a synthesis into square integrability of its density.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped ContDiff

section L2

variable {d : ℕ} {u V : ℝ × (Fin d → ℝ) → ℝ}

/-- **Square integrability of the factors gives every integrability field of the bundle.** -/
theorem decayingSolution_of_memLp_two (hu : ContDiff ℝ ∞ u) (hsolve : SolvesWaveEq u V)
    (hL2u : ∀ t : ℝ, MemLp (slice u t) 2 (volume : Measure (Fin d → ℝ)))
    (hL2d : ∀ t : ℝ, MemLp (slice (waveDirDeriv (timeDir d) u) t) 2
      (volume : Measure (Fin d → ℝ)))
    (hL2s : ∀ (t : ℝ) (i : Fin d), MemLp (fun x : Fin d → ℝ =>
      waveDirDeriv (spaceDir d i) u (t, x)) 2 (volume : Measure (Fin d → ℝ)))
    (hL2g : ∀ (t : ℝ) (i : Fin d), MemLp (coordPartial i (slice u t)) 2
      (volume : Measure (Fin d → ℝ)))
    (hL2gd : ∀ (t : ℝ) (i : Fin d),
      MemLp (coordPartial i (slice (waveDirDeriv (timeDir d) u) t)) 2
        (volume : Measure (Fin d → ℝ)))
    (hL2l : ∀ (t : ℝ) (i : Fin d), MemLp (coordPartial i (coordPartial i (slice u t))) 2
      (volume : Measure (Fin d → ℝ)))
    (hVcont : Continuous V) (hVbdd : ∃ M : ℝ, ∀ p, |V p| ≤ M)
    (hdom : ∀ t : ℝ, ∃ bound : (Fin d → ℝ) → ℝ,
      Integrable bound (volume : Measure (Fin d → ℝ)) ∧
        ∀ s ∈ Metric.ball t 1, ∀ x : Fin d → ℝ,
          ‖waveDirDeriv (timeDir d) (energyDensity u) (s, x)‖ ≤ bound x) :
    DecayingSolution u V := by
  obtain ⟨M, hM⟩ := hVbdd
  refine
    { smooth := hu
      solves := hsolve
      energyInt := fun t => ?_
      greenInt₁ := fun t i => MemLp.integrable_mul (hL2l t i) (hL2d t)
      greenInt₂ := fun t i => MemLp.integrable_mul (hL2g t i) (hL2gd t i)
      greenInt₃ := fun t i => MemLp.integrable_mul (hL2g t i) (hL2d t)
      fluxInt := fun t => ?_
      dominated := hdom }
  · -- the energy density is a sum of squares
    have hd : Integrable (fun x : Fin d → ℝ => (waveDirDeriv (timeDir d) u (t, x)) ^ (2 : ℕ))
        (volume : Measure (Fin d → ℝ)) := _root_.MeasureTheory.MemLp.integrable_sq (hL2d t)
    have hu2 : Integrable (fun x : Fin d → ℝ => (u (t, x)) ^ (2 : ℕ))
        (volume : Measure (Fin d → ℝ)) := _root_.MeasureTheory.MemLp.integrable_sq (hL2u t)
    have hs : ∀ i : Fin d, Integrable
        (fun x : Fin d → ℝ => (waveDirDeriv (spaceDir d i) u (t, x)) ^ (2 : ℕ))
        (volume : Measure (Fin d → ℝ)) := fun i => _root_.MeasureTheory.MemLp.integrable_sq (hL2s t i)
    have hsum : Integrable (fun x : Fin d → ℝ =>
        ∑ i : Fin d, (waveDirDeriv (spaceDir d i) u (t, x)) ^ (2 : ℕ))
        (volume : Measure (Fin d → ℝ)) := integrable_finsetSum _ fun i _ => hs i
    exact (hd.add hsum).add hu2
  · -- the zeroth-order term is a bounded multiple of a product of two square integrable factors
    have hprod : Integrable
        (fun x : Fin d → ℝ => u (t, x) * waveDirDeriv (timeDir d) u (t, x))
        (volume : Measure (Fin d → ℝ)) := MemLp.integrable_mul (hL2u t) (hL2d t)
    refine Integrable.mono' (hprod.norm.const_mul (M + 1)) ?_ ?_
    · have hmap : Continuous fun x : Fin d → ℝ => ((t, x) : ℝ × (Fin d → ℝ)) := by fun_prop
      exact (((hVcont.comp hmap).add continuous_const).aestronglyMeasurable).mul
        hprod.aestronglyMeasurable
    · filter_upwards with x
      have h1 : |V (t, x) + 1| ≤ M + 1 := by
        have hMle := abs_le.mp (hM (t, x))
        rw [abs_le]
        constructor <;> linarith [hMle.1, hMle.2]
      rw [Real.norm_eq_abs, abs_mul]
      refine mul_le_mul h1 le_rfl (abs_nonneg _) ?_
      have := hM (t, x)
      have habs := abs_nonneg (V (t, x))
      linarith

end L2

end GaloisForLFunctions.HTGeometry
