import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysPerfectionDense
import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysPerfectionLocal

/-!
# Perfections of localizations

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 14.7(b).

Let `A` be an integral domain in which every element is a `p`-th power and let `S ⊆ A` be a
multiplicative subset with `a ∈ S ↔ a ^ p ∈ S`.  If the Tate module of roots of unity of `A`
surjects onto that of the fraction field `K`, then every element of `lim_{()^p} S⁻¹ A` is a
quotient `y z⁻¹` with `y ∈ lim_{()^p} A` and `z ∈ lim_{()^p} S`.

Written multiplicatively, so that no inverses are needed: an element `x` of `lim_{()^p} K` whose
zeroth coefficient is a nonzero fraction `a₀ / s₀` satisfies `y = x z` for such a pair.  The
mechanism is that `x z` and the perfection element built from `a₀` have the same nonzero zeroth
coefficient, so they differ by an element of the Tate module of roots of unity, which by hypothesis
comes from `A`.
-/

namespace RHTower

open Perfection

/-- A `p`-power-closed multiplicative subset supports perfection elements: any of its members is
the zeroth coefficient of an element of the perfection all of whose coefficients lie in the
subset. -/
theorem deningerPerfection_exists_submonoid_lift {A : Type*} [CommMonoid A] {p : ℕ}
    (S : Submonoid A) (hp : ∀ a : A, ∃ b : A, b ^ p = a)
    (hS : ∀ a : A, a ^ p ∈ S → a ∈ S) {s : A} (hs : s ∈ S) :
    ∃ z : Perfection A p, coeffMonoidHom A p 0 z = s ∧ ∀ n, coeffMonoidHom A p n z ∈ S := by
  classical
  choose r hr using hp
  refine ⟨⟨fun n => r^[n] s, ?_⟩, rfl, ?_⟩
  · intro n
    show r^[n + 1] s ^ p = r^[n] s
    rw [Function.iterate_succ_apply']
    exact hr _
  · intro n
    induction n with
    | zero => exact hs
    | succ n ih =>
        refine hS _ ?_
        show r^[n + 1] s ^ p ∈ S
        rw [Function.iterate_succ_apply', hr]
        exact ih

/-- **Deninger, Proposition 14.7(b).**  Every element of the perfection of a localization of `A` is
a quotient of an element of the perfection of `A` by an element of the perfection of the
multiplicative subset. -/
theorem deningerPerfection_localization_eq_quotient
    {A K : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    {p : ℕ} (hp0 : p ≠ 0) (S : Submonoid A)
    (hpow : ∀ a : A, ∃ b : A, b ^ p = a) (hS : ∀ a : A, a ^ p ∈ S → a ∈ S)
    (hmu : ∀ ζ : Perfection K p, coeffMonoidHom K p 0 ζ = 1 →
      ∃ ζ' : Perfection A p,
        mapMonoidHom p ((algebraMap A K : A →+* K) : A →* K) ζ' = ζ)
    (x : Perfection K p) {a₀ s₀ : A} (ha₀ : a₀ ≠ 0) (hs₀ : s₀ ∈ S)
    (hfrac : coeffMonoidHom K p 0 x * algebraMap A K s₀ = algebraMap A K a₀) :
    ∃ (y z : Perfection A p), (∀ n, coeffMonoidHom A p n z ∈ S) ∧
      mapMonoidHom p ((algebraMap A K : A →+* K) : A →* K) y
        = x * mapMonoidHom p ((algebraMap A K : A →+* K) : A →* K) z := by
  classical
  obtain ⟨z, hz0, hzS⟩ := deningerPerfection_exists_submonoid_lift S hpow hS hs₀
  obtain ⟨y', hy'⟩ := deningerPerfection_coeffMonoidHom_surjective (M := A) (p := p) hpow 0 a₀
  set φ : A →* K := ((algebraMap A K : A →+* K) : A →* K) with hφ
  have hcoeff : coeffMonoidHom K p 0 (x * mapMonoidHom p φ z)
      = coeffMonoidHom K p 0 (mapMonoidHom p φ y') := by
    rw [map_mul, coeffMonoidHom_mapMonoidHom, coeffMonoidHom_mapMonoidHom, hz0, hy']
    exact hfrac
  have hne : coeffMonoidHom K p 0 (mapMonoidHom p φ y') ≠ 0 := by
    rw [coeffMonoidHom_mapMonoidHom, hy']
    intro h
    exact ha₀ ((map_eq_zero_iff (algebraMap A K) (IsFractionRing.injective A K)).1 h)
  obtain ⟨ζ, hζ1, hζ⟩ :=
    deningerPerfection_exists_ratio hp0 (x * mapMonoidHom p φ z) (mapMonoidHom p φ y') hcoeff hne
  obtain ⟨ζ', hζ'⟩ := hmu ζ hζ1
  refine ⟨ζ' * y', z, hzS, ?_⟩
  rw [map_mul, hζ', hζ]

end RHTower
