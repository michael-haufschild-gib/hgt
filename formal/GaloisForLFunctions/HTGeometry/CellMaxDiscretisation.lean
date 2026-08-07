import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Topology.Order.Compact
/-!
# Discretisation of an integral by cell maxima

Splitting `[a, a+mΔ]` into `m` closed cells of length `Δ`, a continuous integrand attains a maximum on each cell,
and the integral is at most `Δ` times the sum of those maxima.  The statement produces the maximisers, so an
estimate for sums over *well-spaced* frequencies can consume them: maximisers of cells of the same parity are at
distance at least `Δ`, so splitting the cells into even and odd families gives two well-spaced families at the cost
of a factor two.

This is the device that converts a Halász-type bound on a sum over spaced frequencies — where at most one
frequency pays the trivial size and every other is damped — into a bound on a vertical integral.  Measuring the
exceptional set instead charges the trivial size to a whole window, which is what defeats the measure-based route.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open MeasureTheory intervalIntegral

/-- **Discretisation of an integral by cell maxima.**  Splitting `[a, a+mΔ]` into `m` cells of length `Δ` and
taking the maximum of a continuous integrand on each closed cell — attained by compactness — bounds the integral
by `Δ` times the sum of the maxima.  The maximisers are produced by the statement, so a bound on sums over
well-spaced frequencies can consume them. -/
theorem exists_cell_max_integral_le {F : ℝ → ℝ} (hF : Continuous F) (a Δ : ℝ) (hΔ : 0 < Δ) (m : ℕ) :
    ∃ c : ℕ → ℝ, (∀ k, k < m → c k ∈ Set.Icc (a + (k : ℝ) * Δ) (a + ((k : ℝ) + 1) * Δ))
      ∧ (∫ t in a..(a + (m : ℝ) * Δ), F t) ≤ ∑ k ∈ Finset.range m, Δ * F (c k) := by
  classical
  -- a maximiser on each closed cell
  have hcell : ∀ k : ℕ, ∃ x ∈ Set.Icc (a + (k : ℝ) * Δ) (a + ((k : ℝ) + 1) * Δ),
      IsMaxOn F (Set.Icc (a + (k : ℝ) * Δ) (a + ((k : ℝ) + 1) * Δ)) x := by
    intro k
    refine (isCompact_Icc).exists_isMaxOn ?_ (hF.continuousOn)
    refine Set.nonempty_Icc.2 ?_
    have : (0 : ℝ) ≤ Δ := hΔ.le
    nlinarith [this]
  choose c hcmem hcmax using hcell
  refine ⟨c, fun k _ => hcmem k, ?_⟩
  -- the integral is the sum over the cells
  set g : ℕ → ℝ := fun k => a + (k : ℝ) * Δ with hg
  have hadj : ∀ k < m, IntervalIntegrable F volume (g k) (g (k + 1)) :=
    fun k _ => (hF.intervalIntegrable _ _)
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hadj
  have hg0 : g 0 = a := by rw [hg]; simp
  have hgm : g m = a + (m : ℝ) * Δ := by rw [hg]
  rw [hg0, hgm] at hsum
  rw [← hsum]
  refine Finset.sum_le_sum fun k hk => ?_
  rw [Finset.mem_range] at hk
  have hgk : g (k + 1) = a + ((k : ℝ) + 1) * Δ := by
    simp only [hg]
    push_cast
    ring
  have hle : g k ≤ g (k + 1) := by
    simp only [hg]
    push_cast
    nlinarith [hΔ.le]
  have hbound : ∀ x ∈ Set.Icc (g k) (g (k + 1)), F x ≤ F (c k) := by
    intro x hx
    rw [hgk] at hx
    exact hcmax k hx
  have hmono : (∫ t in (g k)..(g (k + 1)), F t) ≤ ∫ _t in (g k)..(g (k + 1)), F (c k) :=
    intervalIntegral.integral_mono_on hle (hF.intervalIntegrable _ _)
      (intervalIntegrable_const) hbound
  refine hmono.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_const, hgk]
  simp only [hg]
  ring

end GaloisForLFunctions.HTGeometry
end
