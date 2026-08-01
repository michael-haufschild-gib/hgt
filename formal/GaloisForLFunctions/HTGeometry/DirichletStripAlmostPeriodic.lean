import GaloisForLFunctions.HTGeometry.StripAlmostPeriodicUniformLimit
import GaloisForLFunctions.HTGeometry.StripAlmostPeriodicExpSum

/-!
# Dirichlet series are strip almost periodic

A partial sum of `∑ aₙ e^{−λₙ s}` is an exponential sum with real frequencies, hence almost periodic
on every vertical strip; and almost periodicity passes to uniform limits on closed substrips.  So a
Dirichlet series converging uniformly on the substrips of a half plane is almost periodic there.

This places the series (30) of the card — in particular any `L`-series in its half plane of uniform
convergence — inside the class the finite-phase law governs, so the law's contrapositive applies to
them: infinite rational Bohr rank forces hypertranscendence over `ℂ(s)⟨Γ⟩`.
-/

open Filter Topology Complex

namespace GaloisForLFunctions

open _root_.HTGeometry

/-- A partial sum of a Dirichlet series is an exponential sum. -/
theorem dirichletPartial_eq_expSum (a : ℕ → ℂ) (lam : ℕ → ℝ) (n : ℕ) (z : ℂ) :
    ∑ k ∈ Finset.range n, a k * Complex.exp (-(lam k : ℂ) * z)
      = expSum (fun i : Fin n => a (i : ℕ)) (fun i : Fin n => -(lam (i : ℕ))) z := by
  rw [expSum, Fin.sum_univ_eq_sum_range (fun i => a i * Complex.exp (((-(lam i) : ℝ) : ℂ) * z)) n]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  ring_nf

/-- **A uniformly convergent Dirichlet series is strip almost periodic.**  Its partial sums are
exponential sums with real frequencies, which are almost periodic on every vertical strip, and
almost periodicity passes to uniform limits. -/
theorem isStripAlmostPeriodic_dirichlet {σ R : ℝ} (a : ℕ → ℂ) (lam : ℕ → ℝ) (D : ℂ → ℂ)
    (hconv : ∀ r : ℝ, r < R → ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, ∀ z ∈ closedStrip σ r,
      ‖D z - ∑ k ∈ Finset.range n, a k * Complex.exp (-(lam k : ℂ) * z)‖ ≤ ε) :
    IsStripAlmostPeriodic D σ R := by
  refine isStripAlmostPeriodic_of_uniform_approx fun r hr ε hε => ?_
  obtain ⟨n, hn⟩ := hconv r hr ε hε
  refine ⟨expSum (fun i : Fin n => a (i : ℕ)) (fun i : Fin n => -(lam (i : ℕ))), ?_, ?_⟩
  · exact isStripAlmostPeriodic_expSum _ _ σ R r hr
  · intro z hz
    rw [← dirichletPartial_eq_expSum]
    exact hn z hz

end GaloisForLFunctions
