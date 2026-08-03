import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Normed.Group.Constructions

/-!
# Avoiding finitely many hyperplanes inside an open set

A functional which is affine with nonzero slope along one coordinate direction is nonzero on a dense
set of parameters: moving that one coordinate by a small amount moves the value off zero.  Finitely
many such conditions therefore still meet every nonempty open set.

This is the selection principle behind explicit spectral base points: positivity constraints cut out
a nonempty open set of parameters, while finitely many coincidences of energies or of energy gaps
are hyperplanes, and hyperplanes cannot cover an open set.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

variable {θ : Type*} [Fintype θ] [DecidableEq θ]

/-- Moving one coordinate stays inside any ball of larger radius. -/
theorem dist_coordinateShift_lt {p : θ → ℝ} {θ₀ : θ} {δ r : ℝ} (hδ : |δ| < r) (hr : 0 < r) :
    dist (p + δ • (Pi.single θ₀ (1 : ℝ))) p < r := by
  classical
  set e₀ : θ → ℝ := Pi.single θ₀ (1 : ℝ) with he₀
  rw [dist_pi_lt_iff hr]
  intro i
  have hdiff : (p + δ • e₀) i - p i = δ * e₀ i := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [Real.dist_eq, hdiff]
  by_cases hi : i = θ₀
  · subst hi
    rw [he₀, Pi.single_eq_same, mul_one]
    exact hδ
  · rw [he₀, Pi.single_eq_of_ne hi, mul_zero, abs_zero]
    exact hr

/-- **A functional with a nonzero coordinate slope is nonzero on a dense set.** -/
theorem dense_setOf_ne_zero_of_coordinateShift {F : (θ → ℝ) → ℝ} {θ₀ : θ} {c : ℝ} (hc : c ≠ 0)
    (hshift : ∀ (p : θ → ℝ) (δ : ℝ),
      F (p + δ • (Pi.single θ₀ (1 : ℝ))) = F p + δ * c) :
    Dense {p : θ → ℝ | F p ≠ 0} := by
  classical
  refine Metric.dense_iff.2 fun p r hr => ?_
  by_cases hp : F p ≠ 0
  · exact ⟨p, Metric.mem_ball_self hr, hp⟩
  push Not at hp
  have hδ : (0 : ℝ) < r / 2 := by positivity
  refine ⟨p + (r / 2) • (Pi.single θ₀ (1 : ℝ)), Metric.mem_ball.2 ?_, ?_⟩
  · refine dist_coordinateShift_lt ?_ hr
    rw [abs_of_pos hδ]
    linarith
  · show F (p + (r / 2) • (Pi.single θ₀ (1 : ℝ))) ≠ 0
    rw [hshift, hp, zero_add]
    exact mul_ne_zero (ne_of_gt hδ) hc

/-- **Finitely many hyperplanes never cover a nonempty open set.**  If every member of a finite
family of continuous functionals has a nonzero slope along some coordinate direction, then some
parameter of a prescribed nonempty open set is off all of their zero sets. -/
theorem exists_mem_open_forall_ne_zero {R : Type*}
    {Ω : Set (θ → ℝ)} (hΩopen : IsOpen Ω) (hΩne : Ω.Nonempty)
    (F : R → (θ → ℝ) → ℝ) (s : Finset R)
    (hcont : ∀ r ∈ s, Continuous (F r))
    (hshift : ∀ r ∈ s, ∃ (θ₀ : θ) (c : ℝ), c ≠ 0 ∧
      ∀ (p : θ → ℝ) (δ : ℝ), F r (p + δ • (Pi.single θ₀ (1 : ℝ))) = F r p + δ * c) :
    ∃ p ∈ Ω, ∀ r ∈ s, F r p ≠ 0 := by
  classical
  have key : ∀ s : Finset R, (∀ r ∈ s, Continuous (F r)) →
      (∀ r ∈ s, ∃ (θ₀ : θ) (c : ℝ), c ≠ 0 ∧
        ∀ (p : θ → ℝ) (δ : ℝ), F r (p + δ • (Pi.single θ₀ (1 : ℝ))) = F r p + δ * c) →
      IsOpen (Ω ∩ {p : θ → ℝ | ∀ r ∈ s, F r p ≠ 0}) ∧
        (Ω ∩ {p : θ → ℝ | ∀ r ∈ s, F r p ≠ 0}).Nonempty := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro _ _
        refine ⟨by simpa using hΩopen, ?_⟩
        obtain ⟨p, hp⟩ := hΩne
        exact ⟨p, hp, by simp⟩
    | insert r s hr ih =>
        intro hcontIns hshiftIns
        obtain ⟨hopen, hne⟩ :=
          ih (fun t ht => hcontIns t (Finset.mem_insert_of_mem ht))
            (fun t ht => hshiftIns t (Finset.mem_insert_of_mem ht))
        obtain ⟨θ₀, c, hc, hstep⟩ := hshiftIns r (Finset.mem_insert_self r s)
        have hCopen : IsOpen {p : θ → ℝ | F r p ≠ 0} :=
          isOpen_ne.preimage (hcontIns r (Finset.mem_insert_self r s))
        have hCdense : Dense {p : θ → ℝ | F r p ≠ 0} :=
          dense_setOf_ne_zero_of_coordinateShift hc hstep
        have hsplit : Ω ∩ {p : θ → ℝ | ∀ t ∈ insert r s, F t p ≠ 0}
            = (Ω ∩ {p : θ → ℝ | ∀ t ∈ s, F t p ≠ 0}) ∩ {p : θ → ℝ | F r p ≠ 0} := by
          ext p
          simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Finset.forall_mem_insert]
          tauto
        rw [hsplit]
        exact ⟨hopen.inter hCopen, hCdense.inter_open_nonempty _ hopen hne⟩
  obtain ⟨p, hp⟩ := (key s hcont hshift).2
  exact ⟨p, hp.1, hp.2⟩

end GaloisForLFunctions.HTGeometry
