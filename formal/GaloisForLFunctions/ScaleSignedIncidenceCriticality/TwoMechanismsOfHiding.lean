import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheFloorsRequireAnOffLineCrystal
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheMassApertureExchangeLaw
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheResolutionIntervalIsTheWholeRange

/-!
# Two mechanisms of hiding

A configuration that passes a bounded-aperture certificate while carrying depth is *hiding*. The
witnesses of the field do it in two different ways, and the ways are not variants of one another:
they have different costs and different requirements.

**Aliasing.** The pure off-line lattice of spacing `2π/L` — every zero off the line, no on-line zero
at all — is Weil-positive at every aperture up to `L/2`, at every depth
(`aliasingHides`). The hiding aperture is *linear* in the scale, it costs nothing, and the depth is
irrelevant. This is the mechanism behind every floor of the programme.

**Mass.** A configuration whose off-line part is one simple pair in an on-line background, or a
diluted sub-lattice inside one, can hide only by paying on-line mass, and the payment is
exponential in the depth times the aperture: `|Q| (sinh (δ v) − 1) ≤ M`
(`massHides`, from `TheFloorsRequireAnOffLineCrystal`) and
`ℓ e^{δ(2a − ℓ)} ≤ 2L + 2a + ℓ` (`massHidesDiluted`, from `TheMassApertureExchangeLaw`). Here the
hiding aperture is *logarithmic* in the mass.

`twoMechanismsOfHiding` states the three facts together. The contrast is the content: aliasing buys
an aperture linear in the scale for free, mass buys only a logarithm of itself. So a configuration
that hides far must do it by aliasing, and aliasing requires the off-line zeros to carry the whole
Poisson structure — no on-line zeros to interfere. That is why the floors need a crystal
(`TheFloorsRequireAnOffLineCrystal`) and why a finite exceptional set is caught at an explicit
aperture (`FiniteOffLineSetsAreRefutedAtAnExplicitAperture`): both are statements that the mass
mechanism is weak, and only the aliasing mechanism is strong.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

/-! ### 1. Aliasing hides for free, to an aperture linear in the scale -/

/-- **Aliasing.** A pure off-line lattice hides every depth up to its Nyquist aperture, with no
on-line mass. -/
theorem aliasingHides {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) {a : ℝ}
    (haL : a ≤ L / 2) : aperturePositivity a (offLineLattice hL hδ hδ') :=
  (offLineLattice_weil_positive_iff hL hδ hδ' a).mpr haL

/-- And the aperture so bought is linear in the scale: every bound is reached by taking the lattice
dense enough. -/
theorem aliasingHidesArbitrarilyFar {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (a : ℝ) (ha : 0 < a) :
    ∃ (L : ℝ) (hL : 0 < L), width (offLineLattice hL hδ hδ') = δ ∧
      aperturePositivity a (offLineLattice hL hδ hδ') := by
  have hL : (0 : ℝ) < 2 * a := by linarith
  exact ⟨2 * a, hL, width_offLineLattice hL hδ hδ', aliasingHides hL hδ hδ' (by linarith)⟩

/-! ### 2. Mass hides only to a logarithm of itself -/

/-- **Mass, one pair.** Hiding a simple off-line pair of depth `δ` up to lag `v` in an on-line
background costs mass `|Q| (sinh (δ v) − 1)`. -/
theorem massHides (Z : ZeroConfig) (hZ : TemperedConfig Z) {δ γ₀ : ℝ} (hδ : 0 < δ)
    (hp : heightPoint δ γ₀ ∈ Z.carrier) (hm : heightPoint (-δ) γ₀ ∈ Z.carrier)
    (hmp : Z.mult (heightPoint δ γ₀) = 1) (hmm : Z.mult (heightPoint (-δ) γ₀) = 1)
    (hon : ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 ∨ ρ = heightPoint δ γ₀ ∨ ρ = heightPoint (-δ) γ₀)
    {β : ℝ → ℂ} (hβ : ContDiff ℝ 2 β) {w : ℝ} (hβs : ∀ u, β u ≠ 0 → |u| ≤ w) {v : ℝ}
    (hv : 0 ≤ v)
    (hpos : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-(v / 2 + w)) (v / 2 + w) →
      0 ≤ (Z.W f f).re) :
    ‖paperFT β (-(Complex.I * δ))‖ * ‖paperFT β (Complex.I * δ)‖ * (Real.sinh (δ * v) - 1) ≤
      onLineMass Z β γ₀ :=
  onLineMass_ge_of_aperturePositivity Z hZ hδ hp hm hmp hmm hon hβ hβs hv hpos

/-- **Mass, a diluted sub-lattice.** The same exponential cost, with no dependence on the
dilution. -/
theorem massHidesDiluted {ℓ L δ a : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (ha : 0 < a) (haL : a ≤ L / 2)
    (hpos : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      0 ≤ ((dilutedLatticeConfig hℓ hL hδ hδ').W f f).re) :
    ℓ * Real.exp (δ * (2 * a - ℓ)) ≤ 2 * L + 2 * a + ℓ :=
  mass_ge_of_dilutedLattice_positive hℓ hL hδ hδ' ha haL hpos

/-! ### 3. The two mechanisms -/

/-- **The classification of hiding.** Aliasing hides to an aperture linear in the scale at no cost;
mass hides only to a logarithm of itself. A configuration that hides far therefore hides by
aliasing, which requires the off-line zeros to carry the whole lattice structure. -/
theorem twoMechanismsOfHiding {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    (∀ a : ℝ, 0 < a → ∃ (L : ℝ) (hL : 0 < L), width (offLineLattice hL hδ hδ') = δ ∧
        aperturePositivity a (offLineLattice hL hδ hδ')) ∧
      ∀ (ℓ L a : ℝ) (hℓ : 0 < ℓ) (hL : 0 < L), 0 < a → a ≤ L / 2 →
        (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
          0 ≤ ((dilutedLatticeConfig hℓ hL hδ hδ').W f f).re) →
        ℓ * Real.exp (δ * (2 * a - ℓ)) ≤ 2 * L + 2 * a + ℓ :=
  ⟨fun a ha => aliasingHidesArbitrarilyFar hδ hδ' a ha,
    fun _ _ _ hℓ hL ha haL hpos => massHidesDiluted hℓ hL hδ hδ' ha haL hpos⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
