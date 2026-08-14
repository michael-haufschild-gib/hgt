import GaloisForLFunctions.RHTower.PoissonMuntzAbelMeanDefect
import GaloisForLFunctions.HTGeometry.RadialLatticeSourceEnvelope

/-!
# The Abel boundary value of the radial sum is the full radial source

The one-sided Poisson--Muntz boundary law computes the Abel limit of the square-root normalized
positive Fourier-sample sum as

```text
f(0) / (2 √a)  +  (∑_{n ≥ 1} f (n / a)) / √a,
```

which is literally the Poisson centre plus the physical lattice charge — that is, the full radial
source `R_λ(t)` at `a = λ exp t`.  Identifying the two closes `(19a)`--`(19b)` at the level of the
object the envelope estimates speak about, so the half-density envelope, the squared mass `(4)`,
and the polar-charge estimate `(18)` all apply to the Abel-summed radial sum itself.
-/

noncomputable section

open Filter MeasureTheory Set HTGeometry
open scoped Topology

namespace RHTower

/-- A compactly supported source vanishes past a nonnegative radius. -/
theorem exists_vanishing_radius {f : ℝ → ℝ} (hcompact : HasCompactSupport f) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x : ℝ, L < x → f x = 0 := by
  obtain ⟨L, hL⟩ := hcompact.isBounded.subset_closedBall (0 : ℝ)
  refine ⟨max L 0, le_max_right _ _, fun x hx => ?_⟩
  refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
  have hball := hL hmem
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hball
  have hxL : L < x := lt_of_le_of_lt (le_max_left L 0) hx
  have hx0 : (0 : ℝ) < x := lt_of_le_of_lt (le_max_right L 0) hx
  rw [abs_of_pos hx0] at hball
  linarith

/-- **`(19a)`--`(19b)`.**  The Abel boundary value of the square-root normalized radial sum is the
full radial source: Poisson centre plus physical lattice charge. -/
theorem tendsto_sqrt_mul_poissonMuntzAbelSum_eq_radialFullLogSource
    {f : ℝ → ℝ} (hf : Integrable f) (heven : Function.Even f)
    (hcompact : HasCompactSupport f) {lam t : ℝ} (hlam : 0 < lam)
    (hmean : ∫ x : ℝ, f x = 0)
    (hleb : Tendsto
      (fun s => (∫ u in (0 : ℝ)..s,
        |poissonMuntzAngularDatum f (lam * Real.exp t) u
            - poissonMuntzAngularDatum f (lam * Real.exp t) 0| +
          |poissonMuntzAngularDatum f (lam * Real.exp t) (-u)
            - poissonMuntzAngularDatum f (lam * Real.exp t) 0|) / s)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun r : ℝ => (Real.sqrt (lam * Real.exp t) : ℂ) *
        poissonMuntzAbelSum f (lam * Real.exp t) r) (𝓝[<] 1)
      (𝓝 ((radialFullLogSource f lam t : ℝ) : ℂ)) := by
  have ha : (0 : ℝ) < lam * Real.exp t := by positivity
  obtain ⟨L, hL0, hvan⟩ := exists_vanishing_radius hcompact
  have hbase := tendsto_sqrt_mul_poissonMuntzAbelSum_physicalLattice_of_compactSupport
    hf heven hcompact ha hmean hleb
  have hval : ((radialFullLogSource f lam t : ℝ) : ℂ)
      = (f 0 : ℂ) / (2 * (Real.sqrt (lam * Real.exp t) : ℂ))
        + ((∑' n : ℕ, f (((n : ℝ) + 1) / (lam * Real.exp t))) : ℂ) /
            (Real.sqrt (lam * Real.exp t) : ℂ) := by
    rw [radialFullLogSource, radialLogSource_ofReal (L := L) hlam hvan t]
    push_cast
    ring
  rw [hval]
  exact hbase

end RHTower
