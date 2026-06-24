/-
# Böttcher tower — Tier 1: the one-coordinate monodromy obstruction (abstract algebraic core)

This is the bottom-most load-bearing block of the q62 formalization
(`unbounded-one-coordinate-monodromy-obstruction.md`). It contains NO analysis:
purely the algebra that turns "one coordinate is moved by arbitrarily high-order
scalar monodromy while the other is fixed" into "no nonzero polynomial relation".

Built bottom-up; each lemma compiles against Mathlib (lean4 v4.30.0).
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.GroupTheory.OrderOfElement

open Polynomial

namespace Bottcher

/-- **T1a.** A polynomial over an integral domain that vanishes on a finite set of
strictly more than `natDegree` distinct points is the zero polynomial. -/
theorem eq_zero_of_card_roots_gt_natDegree
    {R : Type*} [CommRing R] [IsDomain R]
    (p : R[X]) (S : Finset R) (hS : ∀ x ∈ S, p.eval x = 0)
    (hcard : p.natDegree < S.card) : p = 0 := by
  classical
  by_contra hp
  have hsub : S ⊆ p.roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots']
    exact ⟨hp, hS x hx⟩
  have h1 : S.card ≤ p.roots.toFinset.card := Finset.card_le_card hsub
  have h2 : p.roots.toFinset.card ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
  have h3 : Multiset.card p.roots ≤ p.natDegree := Polynomial.card_roots' p
  omega

/-- **T1b.** With `ζ` of order `m` and `f ≠ 0` in a field, the map `k ↦ ζ^k * f` is
injective on `{k | k < m}`: the `m` rotates of `f` under the monodromy multiplier are
pairwise distinct. -/
theorem rotate_injOn {M : Type*} [Field M] {ζ : M} {m : ℕ} (hζ : orderOf ζ = m)
    {f : M} (hf : f ≠ 0) :
    Set.InjOn (fun k : ℕ => ζ ^ k * f) (Set.Iio m) := by
  intro j hj k hk hjk
  have hpow : ζ ^ j = ζ ^ k := mul_right_cancel₀ hf hjk
  have hinj := pow_injOn_Iio_orderOf (x := ζ)
  rw [hζ] at hinj
  exact hinj hj hk hpow

/-- **T1c (scalar core of the one-coordinate monodromy obstruction).**
A polynomial of degree `< m` over a field that vanishes at every rotate `ζ^k · f`
(`k < m`) of a nonzero `f`, where the monodromy multiplier `ζ` has order `m`, is the
zero polynomial. This is the finite-degree contradiction in
`unbounded-one-coordinate-monodromy-obstruction.md`: arbitrarily high-order scalar
monodromy on one coordinate cannot be absorbed by any fixed-degree relation. -/
theorem eq_zero_of_high_monodromy {M : Type*} [Field M]
    {ζ : M} {m : ℕ} (hζ : orderOf ζ = m) {f : M} (hf : f ≠ 0)
    (P : M[X]) (hP : ∀ k : ℕ, k < m → P.eval (ζ ^ k * f) = 0)
    (hdeg : P.natDegree < m) : P = 0 := by
  classical
  set S : Finset M := (Finset.range m).image (fun k => ζ ^ k * f) with hSdef
  have hinj : Set.InjOn (fun k : ℕ => ζ ^ k * f) ↑(Finset.range m) := by
    rw [Finset.coe_range]; exact rotate_injOn hζ hf
  have hcard : S.card = m := by
    rw [hSdef, Finset.card_image_of_injOn hinj, Finset.card_range]
  have hroots : ∀ x ∈ S, P.eval x = 0 := by
    intro x hx
    rw [hSdef, Finset.mem_image] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    exact hP k (Finset.mem_range.mp hk)
  exact eq_zero_of_card_roots_gt_natDegree P S hroots (by omega)

end Bottcher
