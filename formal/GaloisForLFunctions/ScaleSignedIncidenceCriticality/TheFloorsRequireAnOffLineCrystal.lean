import GaloisForLFunctions.ScaleSignedIncidenceCriticality.CoercivityAtABoundedApertureIsStillBlind
import GaloisForLFunctions.SquareRootThreshold.IsolatedPairInArbitraryBackground

/-!
# The floors require an off-line crystal

Every witness behind the programme's floors is an off-line *lattice*: a configuration all of whose
zeros are off the line. That is not an accident of convenience, and this module shows it is
unavoidable — with the consequence that a bounded aperture does certify a nontrivial depth bound as
soon as the off-line set is sparse.

Take a configuration whose zeros are all on the line except one simple reflected pair of depth `δ`
at height `γ₀`, and measure the local on-line mass `M` that a profile `β` of half-width `w` sees at
that height. Weil positivity at aperture `v/2 + w` then forces
(`onLineMass_ge_of_aperturePositivity`, the contrapositive of
`SquareRootThreshold.isolatedPair_visible`)

`|Q| (sinh (δ v) − 1) ≤ M`,   `Q = h_β(−iδ) h_β(iδ)`,

and hence a bound on the depth itself (`depth_le_of_aperturePositivity_of_mass`):

`δ ≤ arsinh (M/|Q| + 1) / v`.

So a finite aperture is *not* blind to a sparse off-line set: it bounds its depth logarithmically in
the local mass. The trivial floor `½` of `BoundedApertureReadingsHaveTheTrivialResolutionLimit`,
`CoercivityAtABoundedApertureIsStillBlind` and the seam theorems is therefore a statement about
crystals — configurations whose off-line zeros are as numerous as their on-line ones
(`theFloorsRequireACrystal`). The two together say where the difficulty actually sits: not in seeing
one off-line zero, which is cheap, but in excluding a conspiracy of infinitely many.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

/-! ### 1. Positivity forces mass -/

/-- **Positivity at a finite aperture forces local on-line mass.** For a configuration with a
single simple off-line pair, hiding depth `δ` up to lag `v` costs mass `|Q| (sinh (δ v) − 1)`. -/
theorem onLineMass_ge_of_aperturePositivity (Z : ZeroConfig) (hZ : TemperedConfig Z) {δ γ₀ : ℝ}
    (hδ : 0 < δ) (hp : heightPoint δ γ₀ ∈ Z.carrier) (hm : heightPoint (-δ) γ₀ ∈ Z.carrier)
    (hmp : Z.mult (heightPoint δ γ₀) = 1) (hmm : Z.mult (heightPoint (-δ) γ₀) = 1)
    (hon : ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 ∨ ρ = heightPoint δ γ₀ ∨ ρ = heightPoint (-δ) γ₀)
    {β : ℝ → ℂ} (hβ : ContDiff ℝ 2 β) {w : ℝ} (hβs : ∀ u, β u ≠ 0 → |u| ≤ w) {v : ℝ}
    (hv : 0 ≤ v)
    (hpos : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-(v / 2 + w)) (v / 2 + w) →
      0 ≤ (Z.W f f).re) :
    ‖paperFT β (-(Complex.I * δ))‖ * ‖paperFT β (Complex.I * δ)‖ * (Real.sinh (δ * v) - 1) ≤
      onLineMass Z β γ₀ := by
  by_contra hlt
  obtain ⟨f, hf, hfs, hneg⟩ :=
    isolatedPair_visible Z hZ hδ hp hm hmp hmm hon hβ hβs hv (not_le.mp hlt)
  exact absurd (hpos f hf hfs) (not_le.mpr hneg)

/-! ### 2. The depth bound -/

/-- **A finite aperture bounds the depth of a sparse off-line set.** The bound is logarithmic in
the local on-line mass. -/
theorem depth_le_of_aperturePositivity_of_mass (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {δ γ₀ : ℝ} (hδ : 0 < δ) (hp : heightPoint δ γ₀ ∈ Z.carrier)
    (hm : heightPoint (-δ) γ₀ ∈ Z.carrier) (hmp : Z.mult (heightPoint δ γ₀) = 1)
    (hmm : Z.mult (heightPoint (-δ) γ₀) = 1)
    (hon : ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 ∨ ρ = heightPoint δ γ₀ ∨ ρ = heightPoint (-δ) γ₀)
    {β : ℝ → ℂ} (hβ : ContDiff ℝ 2 β) {w : ℝ} (hβs : ∀ u, β u ≠ 0 → |u| ≤ w) {v : ℝ}
    (hv : 0 < v)
    (hQ : 0 < ‖paperFT β (-(Complex.I * δ))‖ * ‖paperFT β (Complex.I * δ)‖)
    (hpos : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-(v / 2 + w)) (v / 2 + w) →
      0 ≤ (Z.W f f).re) :
    δ ≤ Real.arsinh (onLineMass Z β γ₀ /
      (‖paperFT β (-(Complex.I * δ))‖ * ‖paperFT β (Complex.I * δ)‖) + 1) / v := by
  have hmass := onLineMass_ge_of_aperturePositivity Z hZ hδ hp hm hmp hmm hon hβ hβs hv.le hpos
  have h1 : Real.sinh (δ * v) - 1 ≤
      onLineMass Z β γ₀ / (‖paperFT β (-(Complex.I * δ))‖ * ‖paperFT β (Complex.I * δ)‖) := by
    rw [le_div_iff₀ hQ]
    linarith [hmass]
  have hsinh : Real.sinh (δ * v) ≤
      onLineMass Z β γ₀ / (‖paperFT β (-(Complex.I * δ))‖ * ‖paperFT β (Complex.I * δ)‖) + 1 := by
    linarith
  have hbound := (Real.sinh_le_sinh (x := δ * v)
      (y := Real.arsinh (onLineMass Z β γ₀ /
        (‖paperFT β (-(Complex.I * δ))‖ * ‖paperFT β (Complex.I * δ)‖) + 1))).mp
    (by rw [Real.sinh_arsinh]; exact hsinh)
  rw [le_div_iff₀ hv]
  linarith [hbound]

/-! ### 3. The floors are about crystals -/

/-- **The floors require a crystal.** At every aperture and every coercivity level there is a
width-`½` configuration passing the certificate — but each such witness has *all* of its zeros off
the line. For a configuration with a single off-line pair the same certificate bounds the depth by
the logarithm of the local mass, so the trivial floors are statements about off-line crystals and
not about sparse off-line sets. -/
theorem theFloorsRequireACrystal {a η : ℝ} (ha : 0 < a) :
    (∃ Z : TemperedZeroConfig, width Z = 1 / 2 ∧ apertureGain a η Z) ∧
      ∀ (Z : ZeroConfig), TemperedConfig Z → ∀ δ γ₀ : ℝ, 0 < δ →
        heightPoint δ γ₀ ∈ Z.carrier → heightPoint (-δ) γ₀ ∈ Z.carrier →
        Z.mult (heightPoint δ γ₀) = 1 → Z.mult (heightPoint (-δ) γ₀) = 1 →
        (∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 ∨ ρ = heightPoint δ γ₀ ∨ ρ = heightPoint (-δ) γ₀) →
        ∀ (β : ℝ → ℂ), ContDiff ℝ 2 β → ∀ w : ℝ, (∀ u, β u ≠ 0 → |u| ≤ w) → ∀ v : ℝ, 0 < v →
        0 < ‖paperFT β (-(Complex.I * δ))‖ * ‖paperFT β (Complex.I * δ)‖ →
        (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-(v / 2 + w)) (v / 2 + w) →
          0 ≤ (Z.W f f).re) →
        δ ≤ Real.arsinh (onLineMass Z β γ₀ /
          (‖paperFT β (-(Complex.I * δ))‖ * ‖paperFT β (Complex.I * δ)‖) + 1) / v :=
  ⟨exists_width_eq_half_apertureGain ha η,
    fun Z hZ _ _ hδ hp hm hmp hmm hon _ hβ _ hβs _ hv hQ hpos =>
      depth_le_of_aperturePositivity_of_mass Z hZ hδ hp hm hmp hmm hon hβ hβs hv hQ hpos⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
