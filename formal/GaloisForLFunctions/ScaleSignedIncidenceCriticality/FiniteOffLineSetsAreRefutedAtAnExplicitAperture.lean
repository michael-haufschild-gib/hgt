import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheRefutationCalculusIsCompleteOnBothFaces
import GaloisForLFunctions.SquareRootThreshold.FiniteOffLineSetsAreVisible

/-!
# Finite off-line sets are refuted at an explicit aperture

`TheRefutationOrderOnFaces` shows a bounded-aperture certificate cannot refute *when it holds*. The
complementary half is immediate and had not been drawn: a certificate that **fails** refutes, because
a configuration of width zero is Weil-positive at every aperture
(`refutes_of_not_aperturePositivity`). So the aperture face does refute — exactly in the regime
where its certificate is unavailable.

That regime is reached at a computable aperture as soon as the off-line set is finite. The
visibility law for finite off-line sets (`SquareRootThreshold.finiteOffLine_visible`) produces, from
a finite set `T` of off-line zeros right of the line with a depth gap `g`, an aperture bound beyond
which some test makes the Weil form negative — logarithmic in the local on-line mass and linear in
`T.card`. Hence `refutes_aperturePositivity_of_finiteOffLine`: beyond that bound the certificate
fails and therefore refutes.

Two consequences close the loop with the floors.

* `not_fullPositivity_of_finiteOffLine` — a configuration with a finite nonempty off-line set is
  never positive at every aperture: it is caught at a finite aperture, not only in the limit.
* `theFloorsNeedInfinitelyManyOffLineZeros` — therefore the witnesses behind every floor of the
  programme must carry *infinitely many* off-line zeros. The depth-`½` lattices do; a ζ-like
  configuration with finitely many exceptional zeros does not, and for it the aperture face is
  effective.

So the trans-Nyquist wall is a statement about infinite off-line conspiracies. Against a finite
exceptional set the bounded certificate is already a complete refutation device, with an explicit
aperture.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

/-! ### 1. A failing certificate refutes -/

/-- **A certificate that fails refutes the critical line.** Width zero implies positivity at every
aperture, so nothing in the shadow of a failing certificate lies on the line. -/
theorem refutes_of_not_aperturePositivity {a : ℝ} {Z : TemperedZeroConfig}
    (hZ : ¬ aperturePositivity a Z) :
    Refutes (aperturePositivity a) (fun W => width W = 0) Z := by
  intro W hW hw
  have hposW : aperturePositivity a W := fun f hf hfs =>
    (configWidth_eq_zero_iff_weil_nonneg W.2).mp hw f hf
      (HasCompactSupport.of_support_subset_isCompact isCompact_Icc
        ((subset_tsupport f).trans hfs))
  exact hZ ((mem_shadow_iff.mp hW) ▸ hposW)

/-! ### 2. Finite off-line sets fail at an explicit aperture -/

/-- **Beyond the visibility bound a finite off-line set is refuted.** -/
theorem refutes_aperturePositivity_of_finiteOffLine {T : Finset ℂ} (m : ℂ → ℕ) {t₀ : ℂ}
    (ht₀ : t₀ ∈ T) {g : ℝ} (hg : 0 < g) (hgD : g ≤ t₀.re - 1 / 2)
    (hgap : ∀ t ∈ T, t.re ≠ t₀.re → t.re ≤ t₀.re - g) {w : ℝ} (hw : 0 < w) :
    ∃ c ℓ : ℝ, 0 < c ∧ 0 < ℓ ∧ ∀ Z : ZeroConfig, ∀ hZ : TemperedConfig Z,
      (∀ z, z ∈ T ↔ z ∈ Z.carrier ∧ 1 / 2 < z.re) → (∀ t ∈ T, Z.mult t = m t) →
      ∀ a : ℝ, 1 / (2 * g) * max 0 (Real.log ((2 * onLineMassOf Z (modScaledBump w t₀.im) +
          4 * ∑ t ∈ T, ‖offLineWeight (modScaledBump w t₀.im) (m t) t‖) / c)) +
          (T.card + 2) * ℓ / 2 + w ≤ a →
        Refutes (aperturePositivity a) (fun W => width W = 0) ⟨Z, hZ⟩ := by
  obtain ⟨c, ℓ, hc, hℓ, hmain⟩ := finiteOffLine_visible m ht₀ hg hgD hgap hw
  refine ⟨c, ℓ, hc, hℓ, fun Z hZ hT hm a ha => refutes_of_not_aperturePositivity ?_⟩
  obtain ⟨f, hf, hfs, hneg⟩ := hmain Z hZ hT hm a ha
  exact fun hpos => absurd (hpos f hf hfs) (not_le.mpr hneg)

/-- **A finite nonempty off-line set is caught at a finite aperture.** -/
theorem not_fullPositivity_of_finiteOffLine {T : Finset ℂ} (m : ℂ → ℕ) {t₀ : ℂ}
    (ht₀ : t₀ ∈ T) {g : ℝ} (hg : 0 < g) (hgD : g ≤ t₀.re - 1 / 2)
    (hgap : ∀ t ∈ T, t.re ≠ t₀.re → t.re ≤ t₀.re - g) {w : ℝ} (hw : 0 < w)
    (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hT : ∀ z, z ∈ T ↔ z ∈ Z.carrier ∧ 1 / 2 < z.re) (hm : ∀ t ∈ T, Z.mult t = m t) :
    ¬ fullPositivity ⟨Z, hZ⟩ := by
  obtain ⟨c, ℓ, hc, hℓ, hmain⟩ := finiteOffLine_visible m ht₀ hg hgD hgap hw
  set A : ℝ := 1 / (2 * g) * max 0 (Real.log ((2 * onLineMassOf Z (modScaledBump w t₀.im) +
      4 * ∑ t ∈ T, ‖offLineWeight (modScaledBump w t₀.im) (m t) t‖) / c)) +
      (T.card + 2) * ℓ / 2 + w with hA
  obtain ⟨f, hf, hfs, hneg⟩ := hmain Z hZ hT hm A le_rfl
  intro hfull
  have hfc : HasCompactSupport f :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc ((subset_tsupport f).trans hfs)
  exact absurd (hfull f hf hfc) (not_le.mpr hneg)

/-! ### 3. The floors need an infinite off-line set -/

/-- **The floors need infinitely many off-line zeros.** A configuration positive at every aperture
cannot have a finite nonempty off-line set, so the witnesses behind the trivial floors — depth-`½`
lattices and their dilutions — carry infinitely many off-line zeros by necessity. Against a finite
exceptional set the bounded certificate refutes, at the explicit aperture of the visibility law. -/
theorem theFloorsNeedInfinitelyManyOffLineZeros {T : Finset ℂ} (m : ℂ → ℕ) {t₀ : ℂ}
    (ht₀ : t₀ ∈ T) {g : ℝ} (hg : 0 < g) (hgD : g ≤ t₀.re - 1 / 2)
    (hgap : ∀ t ∈ T, t.re ≠ t₀.re → t.re ≤ t₀.re - g) {w : ℝ} (hw : 0 < w)
    (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hT : ∀ z, z ∈ T ↔ z ∈ Z.carrier ∧ 1 / 2 < z.re) (hm : ∀ t ∈ T, Z.mult t = m t) :
    ¬ fullPositivity ⟨Z, hZ⟩ ∧
      ∀ {a : ℝ}, ¬ aperturePositivity a ⟨Z, hZ⟩ →
        Refutes (aperturePositivity a) (fun W => width W = 0) ⟨Z, hZ⟩ :=
  ⟨not_fullPositivity_of_finiteOffLine m ht₀ hg hgD hgap hw Z hZ hT hm,
    fun hfail => refutes_of_not_aperturePositivity hfail⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
