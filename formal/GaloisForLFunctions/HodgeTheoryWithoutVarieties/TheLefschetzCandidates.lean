import GaloisForLFunctions.HodgeTheoryWithoutVarieties.StarsOfTheCompleteWeilFamily
import GaloisForLFunctions.HodgeTheoryWithoutVarieties.TheLiouvilleProperty
import GaloisForLFunctions.ArithmeticCouplingTheory.TheCouplingHomotopyIsCrossingFree

/-!
# The three candidates for the arithmetic Lefschetz operator

In the Kähler package a Lefschetz operator is a deformation of the form along which hard Lefschetz
holds, so that the signature is transported from a base point. The review names three candidates.
Each has an exact answer.

1. **The dilation generator** (`dilation_transports_downward`). Dilation by `d` embeds the
   horizon `⌊N/d⌋` at overlap `c⌊N/d⌋/N` isometrically onto the star of `d` at `(c, N)`
   (`completeWeilEnergy_starEmbed`). Hard Lefschetz holds trivially, since the embedding is
   injective. It transports positivity **downward**, from `(c, N)` to every star, and negative
   squares upward. It creates no positivity: every deep star is positive unconditionally
   (`exists_star_positive_tiltedUnitSpline`), while without RH the whole form fails infinitely
   often (`not_rh_gluing_failure`). The missing positivity is a gluing between stars.
2. **The overlap flow** (`riemannHypothesis_iff_liouville_along_the_overlap_flow`). Hard Lefschetz
   on the Hodge–Riemann locus of `c ∈ [1, 2(log N)^β]` is exactly RH. Without RH it fails
   infinitely often: some overlap carries a primitive zero mode of a hyperplane-positive form
   (`frequently_exists_primitive_zero_mode_of_not_rh`).
3. **The coupling Laplacian** (`couplingLaplacian_transports_the_index`). Along the coupling
   homotopy `A + t(K_ζ − A)` from any coupling-free kernel `A`, the coupling form is `t L_pL_q K_ζ`.
   Hard Lefschetz therefore holds for every `t > 0`, and the index is `κ(K_ζ)` throughout. The base
   point `t = 0` is the zero form, so the path transports the index of `ζ` from a degenerate
   origin and carries no information from a base point with Hodge–Riemann.

So no candidate is a free Lefschetz operator. Dilation and the coupling Laplacian satisfy hard
Lefschetz for structural reasons, and transport only what they are given. The overlap flow would
transport positivity from the universal regime, and its hard Lefschetz property is RH.
-/

noncomputable section

open Filter Topology Finset
open GaloisForLFunctions.EdgeHodgeTheory GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.ArithmeticCouplingTheory GaloisForLFunctions.HeckeKreinToeplitz

namespace GaloisForLFunctions.HodgeTheoryWithoutVarieties

/-- **Dilation transports positivity downward.** Positivity at `(c, N)` gives positivity at the
star `(c⌊N/d⌋/N, ⌊N/d⌋)` for every `d ≤ N`, for the full form and on the primitive part. -/
theorem dilation_transports_downward {φ : ℝ → ℝ} (hφ : Admissible φ) {c : ℝ} (hc : 0 < c)
    {N : ℕ} (h : PositiveAt φ c N) {d : ℕ} (hd : 0 < d) (hdN : d ≤ N) :
    PositiveAt φ (starOverlap c N d) (N / d) :=
  positiveAt_div hφ.contDiff hφ.supp hc hd hdN h

/-- **Without RH the gluing fails while the deep stars stay positive.** For `α < α*` and
`β > 1/4`: unconditionally there is `M₀` such that every star of depth `⌊N/d⌋ ≥ M₀` at overlap
`c⌊N/d⌋/N ∈ [1, (log ⌊N/d⌋)^α)` is positive; and without RH the whole complete Weil form of the
tilted spline fails positivity at overlap `2(log N)^β` for infinitely many `N`. -/
theorem not_rh_gluing_failure (hRH : ¬ RiemannHypothesis) {α β : ℝ} (hα : 0 < α)
    (hα' : α < CriticalArithmeticCorrelationTheory.powerLogPositivityExponent) (hβ : 1 / 4 < β) :
    (∃ M₀ : ℕ, ∀ (c : ℝ) (N d : ℕ), 0 < c → 0 < d → d ≤ N → M₀ ≤ N / d →
      1 ≤ starOverlap c N d → starOverlap c N d < Real.log (N / d : ℕ) ^ α →
      ∀ y : EuclideanSpace ℝ (PrimeHorizonIndex (N / d)),
        0 ≤ completeWeilEnergy SpacingScaleHarmonicAnalysis.tiltedUnitSpline c N (starEmbed d N y)) ∧
    ∃ᶠ N : ℕ in atTop, ¬ PositiveAt SpacingScaleHarmonicAnalysis.tiltedUnitSpline (2 * Real.log N ^ β) N := by
  refine ⟨exists_star_positive_tiltedUnitSpline hα hα', fun H => hRH ?_⟩
  exact (riemannHypothesis_iff_eventually_positiveAt_log admissible_tiltedUnitSpline hβ).mpr
    (H.mono fun _ h => not_not.mp h)

/-- **Without RH the overlap flow has primitive zero modes.** For `β > 1/2`, infinitely often some
overlap `c ∈ [1, 2(log N)^β]` carries a hyperplane-positive complete Weil form of the tilted spline
that is degenerate on the primitive part. -/
theorem frequently_exists_primitive_zero_mode_of_not_rh (hRH : ¬ RiemannHypothesis) {β : ℝ}
    (hβ : 1 / 2 < β) :
    ∃ᶠ N : ℕ in atTop, ∃ c ∈ Set.Icc 1 (2 * Real.log N ^ β),
      HyperplanePositiveAt SpacingScaleHarmonicAnalysis.tiltedUnitSpline c N ∧
        ¬ HardLefschetz (completeWeilMatrix SpacingScaleHarmonicAnalysis.tiltedUnitSpline c N) (poleClass N) := by
  intro H
  refine hRH ((riemannHypothesis_iff_liouville_along_the_overlap_flow hβ).mpr ?_)
  filter_upwards [H] with N hN c hc hpos
  by_contra hL
  exact hN ⟨c, hc, hpos, hL⟩

/-- **The coupling Laplacian transports the index of `ζ`.** Along the coupling homotopy from any
kernel that is coupling-free across the towers of `p ≠ q`, the coupling form on `⟨p, q⟩` has
exactly `κ(K_ζ)` negative squares at every `t > 0`; it vanishes at `t = 0`. -/
theorem couplingLaplacian_transports_the_index {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {A : HeckeLattice → ℂ}
    (hA : ∀ u ∈ Subgroup.zpowers (primeElt hp), ∀ v ∈ Subgroup.zpowers (primeElt hq),
      coupling A u v = 0) :
    (∀ t : ℝ, 0 < t →
      negIndex (lap (primeElt hp) (lap (primeElt hq) (couplingHomotopy A zetaKernel t)) ∘
        (twoPrimeLattice hp hq).subtype) = negIndex zetaKernel) ∧
    (RiemannHypothesis ↔ negIndex zetaKernel = 0) :=
  ⟨fun _ ht => negIndex_lap_lap_couplingHomotopy_zeta hp hq hpq hA ht,
    riemannHypothesis_iff_negIndex_zetaKernel_eq_zero⟩

end GaloisForLFunctions.HodgeTheoryWithoutVarieties
