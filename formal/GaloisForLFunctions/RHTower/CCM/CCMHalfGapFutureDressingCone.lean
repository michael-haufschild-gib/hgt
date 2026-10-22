import GaloisForLFunctions.RHTower.CommonProfileBooleanAnchorCurvature
import GaloisForLFunctions.RHTower.UniversalQuadraticRootRidgeDensity

/-!
# Exact cone of phase-locked future dressing

Half-gap twisting makes each normalized quadratic-root response real.  This file classifies the
largest coordinatewise real cone on which complete signed Bernoulli future dressing is
automatically nonnegative.

For local root density `θ` and phase-locked normalized response `u`, one future coordinate acts by

`(1 - θ) - θ u = 1 - θ * (1 + u)`.

Consequently the complete Boolean packet is a product of these local factors.  If
`0 ≤ θ ≤ 1 / 2` and `-1 ≤ u ≤ 1`, every factor is nonnegative.  The density threshold is sharp:
on a singleton, `u = 1` gives `1 - 2 θ`, which is negative as soon as `θ > 1 / 2`.

This theorem does not orient the physical CCM response.  In the anchored physical formula the
Fourier profile is sampled at the changing scales `u / (c r)`, so its responses do not form the
multiplicative packet assumed here.  The result records both the exact positive survivor and the
precise connector that a source-level argument would still have to prove.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Complete signed future dressing of a multiplicative real response packet. -/
def halfGapFutureDressing
    (s : Finset ℕ) (θ u : ℕ → ℝ) : ℝ :=
  ∑ t ∈ s.powerset,
    (-1 : ℝ) ^ t.card * completeAliasWeight s t θ * ∏ p ∈ t, u p

/-- One inserted future coordinate acts by its exact phase-locked local factor. -/
theorem halfGapFutureDressing_insert
    {p : ℕ} {s : Finset ℕ} (hp : p ∉ s) (θ u : ℕ → ℝ) :
    halfGapFutureDressing (insert p s) θ u =
      (1 - θ p * (1 + u p)) * halfGapFutureDressing s θ u := by
  classical
  unfold halfGapFutureDressing
  rw [Finset.sum_powerset_insert hp, ← Finset.sum_add_distrib]
  calc
    (∑ t ∈ s.powerset,
        ((-1 : ℝ) ^ t.card * completeAliasWeight (insert p s) t θ *
              ∏ q ∈ t, u q +
          (-1 : ℝ) ^ (insert p t).card *
              completeAliasWeight (insert p s) (insert p t) θ *
                ∏ q ∈ insert p t, u q)) =
        ∑ t ∈ s.powerset,
          (1 - θ p * (1 + u p)) *
            ((-1 : ℝ) ^ t.card * completeAliasWeight s t θ *
              ∏ q ∈ t, u q) := by
      apply Finset.sum_congr rfl
      intro t ht
      have hts : t ⊆ s := Finset.mem_powerset.mp ht
      have hpt : p ∉ t := fun hmem => hp (hts hmem)
      rw [completeAliasWeight_insert_inactive hp hts,
        completeAliasWeight_insert_active hp hts,
        Finset.card_insert_of_notMem hpt, Finset.prod_insert hpt, pow_succ]
      ring
    _ = (1 - θ p * (1 + u p)) *
        ∑ t ∈ s.powerset,
          (-1 : ℝ) ^ t.card * completeAliasWeight s t θ *
            ∏ q ∈ t, u q := by
      rw [Finset.mul_sum]

/-- **Exact future-dressing product law.** Complete signed Bernoulli dressing factors into the
local half-gap multipliers `1 - θ p * (1 + u p)`. -/
theorem halfGapFutureDressing_eq_prod
    (s : Finset ℕ) (θ u : ℕ → ℝ) :
    halfGapFutureDressing s θ u =
      ∏ p ∈ s, (1 - θ p * (1 + u p)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [halfGapFutureDressing, completeAliasWeight]
  | @insert p s hp ih =>
      rw [halfGapFutureDressing_insert hp, Finset.prod_insert hp, ih]

/-- **Half-density cone preservation.** Root densities at most one half and phase-locked
normalized responses in the real unit interval force nonnegative complete future dressing. -/
theorem halfGapFutureDressing_nonneg
    (s : Finset ℕ) (θ u : ℕ → ℝ)
    (hθ0 : ∀ p ∈ s, 0 ≤ θ p)
    (hθhalf : ∀ p ∈ s, θ p ≤ 1 / 2)
    (hu : ∀ p ∈ s, -1 ≤ u p ∧ u p ≤ 1) :
    0 ≤ halfGapFutureDressing s θ u := by
  rw [halfGapFutureDressing_eq_prod]
  apply Finset.prod_nonneg
  intro p hp
  have hθ := hθhalf p hp
  have huUpper := (hu p hp).2
  have hsum : 0 ≤ 1 + u p := by linarith [(hu p hp).1]
  have hmul₁ : θ p * (1 + u p) ≤ θ p * 2 :=
    mul_le_mul_of_nonneg_left (by linarith) (hθ0 p hp)
  have hmul₂ : θ p * 2 ≤ 1 := by linarith
  norm_num at hmul₁ hmul₂ ⊢
  linarith

/-- On one future coordinate the extremal aligned response is exactly `1 - 2 θ`. -/
theorem halfGapFutureDressing_singleton_one
    (p : ℕ) (θ : ℕ → ℝ) :
    halfGapFutureDressing {p} θ (fun _ => 1) = 1 - 2 * θ p := by
  rw [halfGapFutureDressing_eq_prod]
  simp
  ring

/-- **Sharpness of the half-density threshold.** Above density one half, an admissible real
unit-disk response makes future dressing strictly negative already on a singleton. -/
theorem halfGapFutureDressing_singleton_neg_of_half_lt
    {p : ℕ} {θ : ℕ → ℝ} (hθ : 1 / 2 < θ p) :
    halfGapFutureDressing {p} θ (fun _ => 1) < 0 := by
  rw [halfGapFutureDressing_singleton_one]
  linarith

end

end RHTower
