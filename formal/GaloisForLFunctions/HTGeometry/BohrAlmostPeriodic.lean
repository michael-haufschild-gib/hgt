import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.Order.Archimedean

/-!
# Bohr almost periodicity and the vanishing lemma

A function is Bohr almost periodic when its `ε`-almost-periods are relatively dense: every interval
of some fixed length contains a translation moving the function by at most `ε` uniformly.

The single fact proved here is the **vanishing lemma**: an almost-periodic function that tends to
zero along `atTop` is identically zero.  Almost periodicity forbids decay — the supremum is
recovered arbitrarily far out — so decay forces the function to have been zero all along.

This is the elementary core of the frequency-rank arguments used to separate vertically
almost-periodic Dirichlet series from vertically decaying archimedean factors.  It is classical
mathematics; it is recorded here because it is absent from mathlib and is a prerequisite for those
arguments.
-/

namespace HTGeometry

variable {E : Type*} [NormedAddCommGroup E]

/-- `f` is Bohr almost periodic: for every `ε > 0` the `ε`-almost-periods are relatively dense, i.e.
there is a length `L` such that every interval `[a, a + L]` contains an `ε`-almost-period. -/
def IsBohrAlmostPeriodic (f : ℝ → E) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ L : ℝ, 0 < L ∧
    ∀ a : ℝ, ∃ τ ∈ Set.Icc a (a + L), ∀ x : ℝ, ‖f (x + τ) - f x‖ ≤ ε

/-- **The vanishing lemma.**  An almost-periodic function tending to zero at `+∞` is identically
zero.  Almost periodicity transports the value at any point arbitrarily far to the right, where the
limit forces it to be small. -/
theorem eq_zero_of_isBohrAlmostPeriodic_of_tendsto_zero
    {f : ℝ → E} (hap : IsBohrAlmostPeriodic f)
    (h0 : Filter.Tendsto f Filter.atTop (nhds 0)) :
    ∀ x, f x = 0 := by
  intro x₀
  have key : ∀ ε : ℝ, 0 < ε → ‖f x₀‖ ≤ 2 * ε := by
    intro ε hε
    obtain ⟨L, hL, hdense⟩ := hap ε hε
    -- the limit gives a threshold beyond which `‖f‖ ≤ ε`
    have hev : ∀ᶠ y in Filter.atTop, ‖f y‖ ≤ ε := by
      have hnorm : Filter.Tendsto (fun y => ‖f y‖) Filter.atTop (nhds 0) := by
        rw [show (fun y => ‖f y‖) = (fun z : E => ‖z‖) ∘ f by rfl]
        simpa only [norm_zero] using
          (continuous_norm (E := E)).tendsto (0 : E) |>.comp h0
      exact Filter.Tendsto.eventually_le_const hε hnorm
    obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hev
    -- pick an almost-period far enough to the right
    obtain ⟨τ, hτmem, hτ⟩ := hdense (M + |x₀| + 1)
    have hx₀τ : M ≤ x₀ + τ := by
      have h1 : M + |x₀| + 1 ≤ τ := hτmem.1
      have h2 : -|x₀| ≤ x₀ := neg_abs_le x₀
      linarith
    have hsmall : ‖f (x₀ + τ)‖ ≤ ε := hM _ hx₀τ
    have hshift : ‖f (x₀ + τ) - f x₀‖ ≤ ε := hτ x₀
    calc ‖f x₀‖ = ‖f (x₀ + τ) - (f (x₀ + τ) - f x₀)‖ := by congr 1; abel
      _ ≤ ‖f (x₀ + τ)‖ + ‖f (x₀ + τ) - f x₀‖ := norm_sub_le _ _
      _ ≤ ε + ε := add_le_add hsmall hshift
      _ = 2 * ε := by ring
  by_contra hne
  have hpos : 0 < ‖f x₀‖ := norm_pos_iff.mpr hne
  have := key (‖f x₀‖ / 4) (by positivity)
  linarith

/-- Almost periodicity is closed under uniform limits: an `epsilon/3` argument transfers
almost-periods from an approximant to the limit. -/
theorem isBohrAlmostPeriodic_of_uniform_approx {f : ℝ → E}
    (h : ∀ ε : ℝ, 0 < ε → ∃ g : ℝ → E, IsBohrAlmostPeriodic g ∧ ∀ x, ‖f x - g x‖ ≤ ε) :
    IsBohrAlmostPeriodic f := by
  intro ε hε
  obtain ⟨g, hg, hclose⟩ := h (ε / 3) (by linarith)
  obtain ⟨L, hL, hdense⟩ := hg (ε / 3) (by linarith)
  refine ⟨L, hL, fun a => ?_⟩
  obtain ⟨τ, hτmem, hτ⟩ := hdense a
  refine ⟨τ, hτmem, fun x => ?_⟩
  have hsplit : f (x + τ) - f x
      = (f (x + τ) - g (x + τ)) + (g (x + τ) - g x) + (g x - f x) := by abel
  calc ‖f (x + τ) - f x‖
      ≤ ‖(f (x + τ) - g (x + τ)) + (g (x + τ) - g x)‖ + ‖g x - f x‖ := by
        rw [hsplit]; exact norm_add_le _ _
    _ ≤ (‖f (x + τ) - g (x + τ)‖ + ‖g (x + τ) - g x‖) + ‖g x - f x‖ := by
        gcongr
        exact norm_add_le _ _
    _ ≤ (ε / 3 + ε / 3) + ε / 3 := by
        refine add_le_add (add_le_add (hclose _) (hτ x)) ?_
        rw [← norm_neg]
        simpa using hclose x
    _ = ε := by ring

end HTGeometry
