import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysPerfectionDense

/-!
# Uniqueness of the maps attached to an `𝒪`-valued point

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Supplement 14.9
(`t106`).

The diagram attached to a triple `(x, y, P̄ˣ)` is uniquely determined by the triple.  Deninger's
argument is exactly two observations.  The map `P̂_y` out of the perfection of the adic completion
is continuous and its restriction along the comparison map from the perfection of the ring is
`P_y`, which the triple already determines; since that comparison map has dense image by
Proposition 14.7(a), `P̂_y` is unique.  And `P̃_y` is determined because the map `λ` it is
prescribed on is surjective.
-/

namespace RHTower

open Perfection

/-- **Deninger, Supplement 14.9 (`t106`), uniqueness of `P̂`.**  A continuous map out of the
perfection of a topological monoid is determined by its restriction along the comparison map from
the perfection of a monoid with dense image, provided every element of the latter is a `p`-th
power. -/
theorem deningerPerfection_ext_of_dense {M N Z : Type*} [CommMonoid M] [CommMonoid N] {p : ℕ}
    [TopologicalSpace N] [ContinuousMul N] [TopologicalSpace Z] [T2Space Z]
    (hp : ∀ a : M, ∃ b : M, b ^ p = a) (φ : M →* N) (hφ : DenseRange φ)
    {F G : Perfection N p → Z} (hF : Continuous F) (hG : Continuous G)
    (h : ∀ a : Perfection M p, F (mapMonoidHom p φ a) = G (mapMonoidHom p φ a)) : F = G :=
  (deningerPerfection_denseRange_mapMonoidHom hp φ hφ).equalizer hF hG (funext h)

/-- **Deninger, Supplement 14.9 (`t106`), uniqueness of `P̃`.**  A map prescribed on a surjection
is unique. -/
theorem deningerEq_of_comp_surjective {A B Z : Type*} {l : A → B} (hl : Function.Surjective l)
    {F G : B → Z} (h : ∀ a, F (l a) = G (l a)) : F = G := by
  funext b
  obtain ⟨a, rfl⟩ := hl b
  exact h a

end RHTower
