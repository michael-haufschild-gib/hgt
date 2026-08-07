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

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open MeasureTheory Finset

/-- Maximisers of cells of the same parity are at distance at least the cell length: distinct indices of one
parity differ by at least two, so a whole cell separates them. -/
theorem cell_points_spaced {c : ℕ → ℝ} {a Δ : ℝ} (hΔ : 0 ≤ Δ) {m : ℕ}
    (hc : ∀ k, k < m → c k ∈ Set.Icc (a + (k : ℝ) * Δ) (a + ((k : ℝ) + 1) * Δ))
    {k k' : ℕ} (hk : k < m) (hk' : k' < m) (hpar : k % 2 = k' % 2) (hne : k ≠ k') :
    Δ ≤ |c k - c k'| := by
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hstep : k + 2 ≤ k' := by omega
    have h1 := (hc k hk).2
    have h2 := (hc k' hk').1
    have hcast : (a + ((k : ℝ) + 1) * Δ) + Δ ≤ a + (k' : ℝ) * Δ := by
      have hk2 : ((k : ℝ) + 2) ≤ (k' : ℝ) := by exact_mod_cast hstep
      nlinarith [hΔ]
    rw [abs_sub_comm, abs_of_nonneg (by linarith : (0 : ℝ) ≤ c k' - c k)]
    linarith
  · have hstep : k' + 2 ≤ k := by omega
    have h1 := (hc k' hk').2
    have h2 := (hc k hk).1
    have hcast : (a + ((k' : ℝ) + 1) * Δ) + Δ ≤ a + (k : ℝ) * Δ := by
      have hk2 : ((k' : ℝ) + 2) ≤ (k : ℝ) := by exact_mod_cast hstep
      nlinarith [hΔ]
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ c k - c k')]
    linarith

/-- **An integral against two well-spaced families.**  Discretising by cell maxima and splitting the cells by
parity, a continuous integrand's integral is at most the cell length times the sum of its values over two
`Δ`-spaced finite sets of points.  This is the form a Halász-type bound on spaced frequencies consumes. -/
theorem exists_spaced_families_integral_le {F : ℝ → ℝ} (hF : Continuous F) (a Δ : ℝ) (hΔ : 0 < Δ)
    (m : ℕ) :
    ∃ S₁ S₂ : Finset ℝ,
      (∀ t ∈ S₁, ∀ u ∈ S₁, t ≠ u → Δ ≤ |t - u|)
      ∧ (∀ t ∈ S₂, ∀ u ∈ S₂, t ≠ u → Δ ≤ |t - u|)
      ∧ (∫ t in a..(a + (m : ℝ) * Δ), F t) ≤ Δ * ((∑ t ∈ S₁, F t) + ∑ t ∈ S₂, F t) := by
  classical
  obtain ⟨c, hc, hint⟩ := exists_cell_max_integral_le hF a Δ hΔ m
  set E : Finset ℕ := {k ∈ Finset.range m | k % 2 = 0} with hE
  set O : Finset ℕ := {k ∈ Finset.range m | ¬(k % 2 = 0)} with hO
  -- injectivity of `c` on each parity class
  have hinj : ∀ (P : Finset ℕ), (∀ k ∈ P, k < m) →
      (∀ k ∈ P, ∀ k' ∈ P, k % 2 = k' % 2) → Set.InjOn c P := by
    intro P hPm hPpar k hk k' hk' hval
    by_contra hne
    have hsp := cell_points_spaced hΔ.le hc (hPm k hk) (hPm k' hk') (hPpar k hk k' hk') hne
    rw [hval] at hsp
    simp at hsp
    linarith [hsp]
  have hEm : ∀ k ∈ E, k < m := by
    intro k hk
    rw [hE, Finset.mem_filter, Finset.mem_range] at hk
    exact hk.1
  have hOm : ∀ k ∈ O, k < m := by
    intro k hk
    rw [hO, Finset.mem_filter, Finset.mem_range] at hk
    exact hk.1
  have hEpar : ∀ k ∈ E, ∀ k' ∈ E, k % 2 = k' % 2 := by
    intro k hk k' hk'
    rw [hE, Finset.mem_filter] at hk hk'
    rw [hk.2, hk'.2]
  have hOpar : ∀ k ∈ O, ∀ k' ∈ O, k % 2 = k' % 2 := by
    intro k hk k' hk'
    rw [hO, Finset.mem_filter] at hk hk'
    omega
  refine ⟨E.image c, O.image c, ?_, ?_, ?_⟩
  · intro t ht u hu hne
    rw [Finset.mem_image] at ht hu
    obtain ⟨k, hk, hkt⟩ := ht
    obtain ⟨k', hk', hku⟩ := hu
    have hkk' : k ≠ k' := by
      intro h
      rw [h, hku] at hkt
      exact hne hkt.symm
    rw [← hkt, ← hku]
    exact cell_points_spaced hΔ.le hc (hEm k hk) (hEm k' hk') (hEpar k hk k' hk') hkk'
  · intro t ht u hu hne
    rw [Finset.mem_image] at ht hu
    obtain ⟨k, hk, hkt⟩ := ht
    obtain ⟨k', hk', hku⟩ := hu
    have hkk' : k ≠ k' := by
      intro h
      rw [h, hku] at hkt
      exact hne hkt.symm
    rw [← hkt, ← hku]
    exact cell_points_spaced hΔ.le hc (hOm k hk) (hOm k' hk') (hOpar k hk k' hk') hkk'
  · refine hint.trans (le_of_eq ?_)
    rw [Finset.sum_image (fun k hk k' hk' h => hinj E hEm hEpar hk hk' h),
      Finset.sum_image (fun k hk k' hk' h => hinj O hOm hOpar hk hk' h)]
    rw [hE, hO, ← Finset.mul_sum]
    congr 1
    exact (Finset.sum_filter_add_sum_filter_not (Finset.range m) (fun k => k % 2 = 0)
      (fun k => F (c k))).symm

end GaloisForLFunctions.HTGeometry
end

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open Finset

/-- **From cell maximisers to an indexed sequence with a uniform gap.**  Taking every second cell and continuing by
an arithmetic progression past the range gives a sequence whose consecutive terms differ by at least the cell
length — the form a large-values estimate consumes, which is stated for an indexed family with a gap at every
index. -/
theorem exists_gap_sequence_of_cells {c : ℕ → ℝ} {a Δ : ℝ} (hΔ : 0 < Δ) {m : ℕ}
    (hc : ∀ k, k < m → c k ∈ Set.Icc (a + (k : ℝ) * Δ) (a + ((k : ℝ) + 1) * Δ)) (r : ℕ) :
    ∃ lam : ℕ → ℝ, (∀ i, lam i + Δ ≤ lam (i + 1))
      ∧ (∀ j, 2 * j + r < m → lam j = c (2 * j + r)) := by
  classical
  refine ⟨fun j => if 2 * j + r < m then c (2 * j + r) else a + ((2 * j + r : ℕ) : ℝ) * Δ,
    fun i => ?_, fun j hj => by simp [hj]⟩
  by_cases h1 : 2 * i + r < m
  · by_cases h2 : 2 * (i + 1) + r < m
    · simp only [if_pos h1, if_pos h2]
      have hup := (hc (2 * i + r) h1).2
      have hlow := (hc (2 * (i + 1) + r) h2).1
      have hcast : ((2 * i + r : ℕ) : ℝ) + 1 + 1 ≤ ((2 * (i + 1) + r : ℕ) : ℝ) := by
        push_cast
        ring_nf
        linarith
      nlinarith [hup, hlow, hΔ.le, hcast]
    · simp only [if_pos h1, if_neg h2]
      have hup := (hc (2 * i + r) h1).2
      have hcast : ((2 * i + r : ℕ) : ℝ) + 1 + 1 ≤ ((2 * (i + 1) + r : ℕ) : ℝ) := by
        push_cast
        ring_nf
        linarith
      nlinarith [hup, hΔ.le, hcast]
  · have h2 : ¬(2 * (i + 1) + r < m) := by omega
    simp only [if_neg h1, if_neg h2]
    have hcast : ((2 * i + r : ℕ) : ℝ) + 1 ≤ ((2 * (i + 1) + r : ℕ) : ℝ) := by
      push_cast
      ring_nf
      linarith
    nlinarith [hΔ.le, hcast]

end GaloisForLFunctions.HTGeometry
end
