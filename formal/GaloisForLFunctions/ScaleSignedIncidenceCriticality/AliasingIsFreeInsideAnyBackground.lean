import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheMassApertureExchangeLaw

/-!
# Aliasing is free inside any background

`TwoMechanismsOfHiding` separates the two ways a configuration can carry depth past a certificate:
aliasing, which the pure off-line lattice uses at no cost, and mass, which costs an exponential.
The pure lattice has no on-line zeros, so one might read aliasing as a property of crystals only.
It is not. Aliasing is available to *any* configuration whose off-line zeros carry a lattice
structure, however much on-line mass sits beside them.

The diluted configuration — an off-line sub-lattice of spacing `2π/ℓ` inside an on-line background
of mass `2L` — is Weil-positive at **every** aperture up to `min (ℓ/2) (L/2)`, at every depth
(`dilutedLattice_hides_below_own_nyquist`). The mechanism is exact and visible in the formula: below
its own Nyquist aperture the off-line sub-lattice contributes aliasing index one, and the lattice
ground energy at index one vanishes identically
(`SquareRootThreshold.latticeFloor_one`), so there is nothing for the background to pay for.

Beyond `ℓ/2` the index exceeds one, the ground energy becomes negative, and the exchange law of
`TheMassApertureExchangeLaw` applies: hiding then costs mass exponential in `δa`.
`theTwoRegimesOfAMixedConfiguration` states the two regimes together.

The consequence for a counterexample is a structural requirement, not a size one. Off-line zeros
hide for free up to half the spacing of their own arithmetic structure, whatever else the
configuration contains; past that point they must be paid for exponentially. A hypothetical
counterexample to RH must therefore have its off-line zeros arithmetically structured — a lattice,
not a scatter — and the aperture at which it can first be caught is half the spacing of that
structure.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

/-! ### 1. Below its own Nyquist aperture the sub-lattice aliases -/

/-- At an aperture below half the sub-lattice spacing parameter the aliasing index is one. -/
theorem ceil_two_mul_div_eq_one {ℓ a : ℝ} (hℓ : 0 < ℓ) (ha : 0 < a) (haℓ : a ≤ ℓ / 2) :
    ⌈2 * a / ℓ⌉₊ = 1 := by
  rw [Nat.ceil_eq_iff (by norm_num : (1 : ℕ) ≠ 0)]
  refine ⟨?_, ?_⟩
  · rw [show ((1 : ℕ) - 1 : ℕ) = 0 from rfl]
    push_cast
    positivity
  · push_cast
    rw [div_le_one hℓ]
    linarith

/-- **Aliasing is free inside any background.** Below the sub-lattice's own Nyquist aperture the
diluted configuration is Weil-positive at every depth, whatever the on-line mass. -/
theorem dilutedLattice_hides_below_own_nyquist {ℓ L δ a : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (ha : 0 < a) (haℓ : a ≤ ℓ / 2) (haL : a ≤ L / 2)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) :
    0 ≤ ((dilutedLatticeConfig hℓ hL hδ hδ').W f f).re := by
  refine dilutedLattice_weil_nonneg_of_floor hℓ hL hδ hδ' haL ?_ hf hfs
  rw [ceil_two_mul_div_eq_one hℓ ha haℓ, latticeFloor_one]
  simp only [mul_zero, neg_zero]
  linarith

/-! ### 2. The two regimes -/

/-- **The two regimes of a mixed configuration.** Below half the sub-lattice spacing the
configuration hides for free at every depth; above it, hiding costs on-line mass exponential in the
depth times the aperture. -/
theorem theTwoRegimesOfAMixedConfiguration {ℓ L δ : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) :
    (∀ a : ℝ, 0 < a → a ≤ ℓ / 2 → a ≤ L / 2 → ∀ f : ℝ → ℂ, ContDiff ℝ 2 f →
        tsupport f ⊆ Icc (-a) a → 0 ≤ ((dilutedLatticeConfig hℓ hL hδ hδ').W f f).re) ∧
      ∀ a : ℝ, 0 < a → a ≤ L / 2 →
        (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
          0 ≤ ((dilutedLatticeConfig hℓ hL hδ hδ').W f f).re) →
        ℓ * Real.exp (δ * (2 * a - ℓ)) ≤ 2 * L + 2 * a + ℓ :=
  ⟨fun _ ha haℓ haL _ hf hfs =>
      dilutedLattice_hides_below_own_nyquist hℓ hL hδ hδ' ha haℓ haL hf hfs,
    fun _ ha haL hpos => mass_ge_of_dilutedLattice_positive hℓ hL hδ hδ' ha haL hpos⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
