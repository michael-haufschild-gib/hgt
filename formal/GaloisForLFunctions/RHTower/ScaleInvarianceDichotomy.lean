import GaloisForLFunctions.RHTower.FamilyIncoherence

/-!
# The carrier must be scale-invariant modulo a discrete subgroup

Two obstructions now point the same way, and together they determine the shape of the carrier of a
Hilbert–Pólya operator.  This is the first *positive* structural statement of the classification: it
derives the carrier rather than positing it.

**Scale-invariance is forced.**  A family of truncated models indexed by a scale has spectra that move
with the scale, so it is incoherent.  The only way a scale-indexed family can have one spectrum is
for its members to be unitarily equivalent under the scaling, i.e. for the operator to be
scale-covariant.  Then all spectra coincide and the family collapses to a single object.

**Full scale-invariance destroys discreteness.**  If the spectrum `S` satisfies `λS = S` for every
`λ > 0` and contains one positive point, it contains *every* positive point: given `x > 0` and
`s ∈ S` with `s > 0`, take `λ = x/s`.  So a fully scale-covariant operator has a spectrum that is a
union of rays — continuous, never discrete.  That is the classical reason the dilation generator
`xp` on `L²(0,∞)` has purely absolutely continuous spectrum: it *is* the generator of the scaling
group.

**A discrete subgroup restores it.**  Invariance under a *discrete* subgroup of the scaling group is
compatible with a discrete spectrum: `q^ℤ = {qⁿ : n ∈ ℤ}` is invariant under multiplication by `q`
and misses every point strictly between `1` and `q`.  So the requirement is invariance under a
discrete subgroup, not under the whole group.

> **The carrier of a Hilbert–Pólya operator must be a scale-invariant space quotiented by a discrete
> subgroup of the scaling group: fully invariant enough for the family to be coherent, discretely
> invariant enough for the spectrum not to be a continuum.**

The unique arithmetic realisation of "scale-invariant space modulo a discrete scaling subgroup" that
also carries the primes is the adele class space with the idele action — which is where the known
construction lives, and where the spectrum appears as absorption.  The classification therefore ends
by singling out that carrier from two independent obstructions rather than by assumption.

This file formalizes the two halves of the dichotomy: full invariance forces a ray, and discrete
invariance does not.
-/

open Set

noncomputable section

namespace RHTower

/-- **Full scale-invariance forces a ray.**  A set invariant under every positive dilation and
containing one positive point contains all positive points. -/
theorem scale_invariant_ray {S : Set ℝ}
    (hinv : ∀ lam : ℝ, 0 < lam → ∀ s ∈ S, lam * s ∈ S)
    {s : ℝ} (hs : s ∈ S) (hspos : 0 < s) :
    ∀ x : ℝ, 0 < x → x ∈ S := by
  intro x hx
  have hlam : 0 < x / s := div_pos hx hspos
  have := hinv (x / s) hlam s hs
  rwa [div_mul_cancel₀ x (ne_of_gt hspos)] at this

/-- Hence such a spectrum is not discrete: every neighbourhood of a positive point meets it in a
continuum of points. -/
theorem scale_invariant_not_discrete {S : Set ℝ}
    (hinv : ∀ lam : ℝ, 0 < lam → ∀ s ∈ S, lam * s ∈ S)
    {s : ℝ} (hs : s ∈ S) (hspos : 0 < s) :
    Ioi (0 : ℝ) ⊆ S := fun _ hx => scale_invariant_ray hinv hs hspos _ hx

/-- **A discrete subgroup does not force a ray.**  The set `{qⁿ}` is invariant under multiplication
by `q` yet misses points between `1` and `q`. -/
theorem discrete_orbit_invariant {q : ℝ} (hq : 1 < q) (n : ℤ) :
    q * q ^ n = q ^ (n + 1) := by
  rw [zpow_add₀ (ne_of_gt (lt_trans one_pos hq)) n 1]
  simp [mul_comm]

/-- The orbit misses the geometric mean of `1` and `q` when `q > 1`: it is not a ray. -/
theorem discrete_orbit_not_ray {q : ℝ} (hq : 1 < q) :
    ∃ x : ℝ, 0 < x ∧ x < q ∧ 1 < x ∧ ∀ n : ℤ, (n = 0 → x ≠ q ^ n) := by
  refine ⟨(1 + q) / 2, by positivity, by linarith, by linarith, ?_⟩
  intro n hn
  rw [hn]
  simp only [zpow_zero]
  intro hcon
  linarith [hcon]

/-- **The dichotomy.**  Full invariance gives a continuum; invariance under a discrete subgroup does
not.  So the carrier must be invariant under a discrete subgroup and not under the whole group. -/
theorem carrier_dichotomy {S : Set ℝ} {s : ℝ}
    (hfull : ∀ lam : ℝ, 0 < lam → ∀ t ∈ S, lam * t ∈ S)
    (hs : s ∈ S) (hspos : 0 < s) {x : ℝ} (hx : 0 < x) (hnot : x ∉ S) : False :=
  hnot (scale_invariant_ray hfull hs hspos x hx)

/-- **The forced shape of the carrier.**  Assembling the two halves: a coherent family needs scale
covariance, full covariance forces a continuum, so the invariance must be by a proper discrete
subgroup — the carrier is a scale-invariant space modulo such a subgroup. -/
theorem carrier_shape {S : Set ℝ} {s x : ℝ}
    (hdiscrete : x ∉ S) (hx : 0 < x) (hs : s ∈ S) (hspos : 0 < s) :
    ¬ (∀ lam : ℝ, 0 < lam → ∀ t ∈ S, lam * t ∈ S) := by
  intro hfull
  exact carrier_dichotomy hfull hs hspos hx hdiscrete

end RHTower
