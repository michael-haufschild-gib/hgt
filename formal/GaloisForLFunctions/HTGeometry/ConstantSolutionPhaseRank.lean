import GaloisForLFunctions.HTGeometry.PhaseRankCapstone
import Mathlib.Algebra.Polynomial.Roots

/-!
# The constant case

A function satisfying a nonzero algebraic equation pointwise takes values in a finite set, so on a
connected strip it is constant.  A constant function has identically zero translation distance, so
every frequency character of its hull is constant and the frequency group is trivial: its rank is
zero.

This is the base of the descent on the order of an algebraic differential relation.
-/

open Filter Topology Metric Set

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

variable {σ R : ℝ}

/-- The translates of a constant function are itself. -/
theorem translateBC_const {f : ℝ →ᵇ ℂ} {c : ℂ} (hf : ∀ x : ℝ, f x = c) (u : ℝ) :
    translateBC u f = f := by
  ext x
  simp [translateBC, hf]

/-- **A constant function has no nonzero hull frequency.**  Its translation distance is identically
zero, so a frequency character must be constant, which forces the frequency to vanish. -/
theorem bohrHullFrequencies_eq_bot_of_const {f : ℝ →ᵇ ℂ} {c : ℂ} (hf : ∀ x : ℝ, f x = c) :
    bohrHullFrequencies f = ⊥ := by
  ext mu
  simp only [mem_bohrHullFrequencies, AddSubgroup.mem_bot]
  constructor
  · intro hmu
    by_contra hne
    obtain ⟨δ, hδ, hδlt⟩ := Metric.uniformContinuous_iff.mp hmu 1 one_pos
    have hdist : ∀ s t : BohrLine f, dist s t = 0 := by
      intro s t
      rw [BohrLine.dist_eq, translateBC_const hf, translateBC_const hf]
      simp
    have hclose : ∀ s t : ℝ, dist (expChar mu s) (expChar mu t) < 1 := by
      intro s t
      have := hδlt (a := BohrLine.of f s) (b := BohrLine.of f t)
        (by rw [hdist]; exact hδ)
      simpa using this
    have h0 : expChar mu 0 = 1 := by simp [expChar]
    have hpi : expChar mu (Real.pi / mu) = -1 := by
      have hmu' : (mu : ℝ) ≠ 0 := hne
      have : (mu * (Real.pi / mu) : ℝ) = Real.pi := by field_simp
      rw [expChar, this]
      exact Complex.exp_pi_mul_I
    have := hclose 0 (Real.pi / mu)
    rw [h0, hpi] at this
    rw [Complex.dist_eq] at this
    norm_num at this
  · intro h
    subst h
    exact isBohrHullFrequency_zero f

/-- The frequency rank of a constant function is zero. -/
theorem rank_eq_zero_of_const {f : ℝ →ᵇ ℂ} {c : ℂ} (hf : ∀ x : ℝ, f x = c) :
    Module.rank ℤ (bohrHullFrequencies f) = 0 := by
  have h := bohrHullFrequencies_eq_bot_of_const hf
  rw [h]
  exact rank_subsingleton' ℤ _

/-- **A holomorphic function satisfying a nonzero algebraic equation is constant.**  Its values lie
in the finite root set, and a connected set has subsingleton image in a finite set. -/
theorem const_of_polynomial_relation {Φ : ℂ → ℂ}
    (hΦ : ContinuousOn Φ (verticalStrip σ R)) (q : Polynomial ℂ) (hq : q ≠ 0)
    (hrel : ∀ z ∈ verticalStrip σ R, q.eval (Φ z) = 0)
    {z w : ℂ} (hz : z ∈ verticalStrip σ R) (hw : w ∈ verticalStrip σ R) : Φ z = Φ w := by
  classical
  set S : Set ℂ := {x : ℂ | q.eval x = 0} with hS
  have hSfin : S.Finite := by
    have hset : S = (q.roots.toFinset : Set ℂ) := by
      ext x
      simp [hS, Multiset.mem_toFinset, Polynomial.mem_roots hq, Polynomial.IsRoot]
    rw [hset]
    exact (q.roots.toFinset : Finset ℂ).finite_toSet
  haveI : Finite ↥S := hSfin
  have hmaps : Set.MapsTo Φ (verticalStrip σ R) S := fun x hx => hrel x hx
  have hcont : ContinuousOn (fun x => Φ x) (verticalStrip σ R) := hΦ
  have hconn : IsPreconnected (verticalStrip σ R) := (convex_verticalStrip σ R).isPreconnected
  have himg : IsPreconnected (Φ '' verticalStrip σ R) := hconn.image _ hcont
  have hsub : Φ '' verticalStrip σ R ⊆ S := Set.image_subset_iff.mpr hmaps
  have hfinimg : (Φ '' verticalStrip σ R).Finite := hSfin.subset hsub
  have hsubsing : (Φ '' verticalStrip σ R).Subsingleton := by
    haveI : Finite ↥(Φ '' verticalStrip σ R) := hfinimg
    haveI : PreconnectedSpace ↥(Φ '' verticalStrip σ R) := Subtype.preconnectedSpace himg
    intro a ha b hb
    have hid := IsPreconnected.constant (Y := ↥(Φ '' verticalStrip σ R)) isPreconnected_univ
      (f := id) continuous_id.continuousOn (Set.mem_univ (⟨a, ha⟩ : ↥(Φ '' verticalStrip σ R)))
      (Set.mem_univ (⟨b, hb⟩ : ↥(Φ '' verticalStrip σ R)))
    exact congrArg Subtype.val hid
  exact hsubsing ⟨z, hz, rfl⟩ ⟨w, hw, rfl⟩

end GaloisForLFunctions
