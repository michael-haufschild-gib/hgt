import Mathlib.Topology.Instances.Int
import Mathlib.Topology.UnitInterval

/-!
# Rigidity of continuous integer-lattice-valued functions

A continuous real-valued function on a preconnected space cannot move between distinct points of
a nonzero one-dimensional integer lattice. This elementary intermediate-value lemma avoids choosing
an integer-valued lift and is used for trace quantization of special-unitary logarithms.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

theorem continuous_eq_zero_of_eq_int_mul
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (x0 : X) (f : X → ℝ) (hf : Continuous f) (h0 : f x0 = 0)
    (c : ℝ) (hc : 0 < c) (hdisc : ∀ x, ∃ n : ℤ, f x = (n : ℝ) * c) :
    ∀ x, f x = 0 := by
  intro x
  obtain ⟨n, hn⟩ := hdisc x
  by_contra hx
  have hn0 : n ≠ 0 := by
    intro h
    subst n
    simp at hn
    exact hx hn
  rcases lt_or_gt_of_ne hn0 with hnneg | hnpos
  · have hnle : (n : ℝ) ≤ -1 := by
      have hni : n ≤ -1 := by omega
      exact_mod_cast hni
    have hfx : f x ≤ -c := by
      rw [hn]
      nlinarith
    have hmid : -c / 2 ∈ Set.Icc (f x) (f x0) := by
      rw [h0]
      constructor <;> nlinarith
    obtain ⟨y, hy⟩ := (intermediate_value_univ x x0 hf) hmid
    obtain ⟨m, hm⟩ := hdisc y
    have hmhalf : (m : ℝ) = -(1 / 2 : ℝ) := by
      have heq : (m : ℝ) * c = -c / 2 := hm ▸ hy
      nlinarith
    have hmCases : m ≤ -1 ∨ 0 ≤ m := by omega
    rcases hmCases with hmle | hmge
    · have : (m : ℝ) ≤ -1 := by exact_mod_cast hmle
      nlinarith
    · have : (0 : ℝ) ≤ m := by exact_mod_cast hmge
      nlinarith
  · have hnle : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
    have hfx : c ≤ f x := by
      rw [hn]
      nlinarith
    have hmid : c / 2 ∈ Set.Icc (f x0) (f x) := by
      rw [h0]
      constructor <;> nlinarith
    obtain ⟨y, hy⟩ := (intermediate_value_univ x0 x hf) hmid
    obtain ⟨m, hm⟩ := hdisc y
    have hmhalf : (m : ℝ) = (1 / 2 : ℝ) := by
      have heq : (m : ℝ) * c = c / 2 := hm ▸ hy
      nlinarith
    have hmCases : m ≤ 0 ∨ 1 ≤ m := by omega
    rcases hmCases with hmle | hmge
    · have : (m : ℝ) ≤ 0 := by exact_mod_cast hmle
      nlinarith
    · have : (1 : ℝ) ≤ m := by exact_mod_cast hmge
      nlinarith

end GaloisForLFunctions.HTGeometry
