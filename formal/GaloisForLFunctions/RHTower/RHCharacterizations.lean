/-
# The Riemann Hypothesis characterization hub

The development proves the Riemann Hypothesis equivalent to a wide array of structurally distinct
conditions, each in its own file and its own representation of `ξ`: the raw non-vanishing, the Kummer
root tower, the multiplicity/parity ladder, the off-line height locus and its atomic measure, the census
jump, the `2`-adic valuation profile, the variation filtration, the `u`-plane descent, and the modulus
holography.  This file brings them together into a single `TFAE`: the whole program's diverse handles on
`ξ` are one and the same object, RH.
-/
import GaloisForLFunctions.RHTower.RiemannTower
import GaloisForLFunctions.RHTower.ValMeasure
import GaloisForLFunctions.RHTower.ValuationProfile
import GaloisForLFunctions.RHTower.DiscJump
import GaloisForLFunctions.RHTower.WindowLadder
import GaloisForLFunctions.RHTower.Variation
import GaloisForLFunctions.RHTower.UPlaneDescent
import GaloisForLFunctions.RHTower.SquareLadder
import GaloisForLFunctions.RHTower.XiDeckCharge
import GaloisForLFunctions.RHTower.DiscExtraction
import GaloisForLFunctions.RHTower.RHLadderTheory
import GaloisForLFunctions.RHTower.DeckChargeLadder
import GaloisForLFunctions.RHTower.WeightMismatchRefutation
import GaloisForLFunctions.RHTower.ChargeTomography

open Complex

namespace RHTower

/-- **The Riemann Hypothesis characterization hub.**  The following are equivalent — RH read through
every representation the development supplies:

1. `RiemannHypothesis`;
2. `ξ` has no zero on `Re s > 1/2` (the raw analytic statement);
3. `ξ` admits a coherent Kummer root tower on `Re s > 1/2`;
4. every rung `RHLadder k` (the `2^k`-multiplicity ladder) holds;
5. the off-line height locus is empty;
6. the `2`-adic valuation profile is identically `⊤`;
7. every census jump vanishes;
8. every box has no enclosed zero;
9. every variation zero-set is empty;
10. the `u`-plane descent `ξ_↓` is zero-free on the slit plane;
11. `ξ_↓` admits a coherent Kummer tower on the slit plane. -/
theorem rh_tfae : List.TFAE
    [ RiemannHypothesis,
      ∀ s ∈ rightHalf, xi s ≠ 0,
      Nonempty (CoherentTower xi rightHalf),
      ∀ k, RHLadder k,
      offLineHeights = ∅,
      ∀ t : ℝ, valProfile t = ⊤,
      ∀ t : ℝ, discJump t = 0,
      ∀ T : ℝ, boxZeros T = ∅,
      ∀ k : ℕ, badHeightSet k = ∅,
      ∀ w ∈ slitPlane, xiDescent w ≠ 0,
      Nonempty (CoherentTower xiDescent slitPlane),
      ∀ k, ∀ ρ ∈ rightHalf, xi ρ = 0 → xiDeckCharge k ρ = 1,
      ∀ k, LineHolography k,
      ∀ (k : ℕ) (T : ℝ), WindowCertificate k T,
      ∀ ρ ∈ rightHalf, ∃ R₀ > 0, ∀ {R r₁ r₂ : ℝ}, 0 < r₁ → r₁ < r₂ → r₂ < R → R ≤ R₀ →
        modulusSlope ρ r₁ r₂ = 0 ] := by
  tfae_have 1 ↔ 2 := rh_iff_xi_ne_zero_right
  tfae_have 1 ↔ 3 := rh_iff_tower
  tfae_have 1 ↔ 4 := rh_iff_forall_ladder
  tfae_have 1 ↔ 5 := rh_iff_offLineHeights_empty
  tfae_have 1 ↔ 6 := rh_iff_forall_valProfile_eq_top
  tfae_have 1 ↔ 7 := rh_iff_forall_discJump_eq_zero
  tfae_have 1 ↔ 8 := rh_iff_forall_boxZeros_empty
  tfae_have 1 ↔ 9 := rh_iff_forall_badHeightSet_empty
  tfae_have 1 ↔ 10 := rh_iff_xiDescent_ne_zero_slitPlane
  tfae_have 1 ↔ 11 := rh_iff_xiDescent_coherentTower_slitPlane
  tfae_have 1 ↔ 12 := rh_iff_xiDeckCharge
  tfae_have 1 ↔ 13 := rh_iff_forall_lineHolography
  tfae_have 1 ↔ 14 := rh_iff_forall_windowCertificate
  tfae_have 1 ↔ 15 := rh_iff_forall_modulusSlope_eq_zero
  tfae_finish

/-- **The `RH_{2^k}` rung characterization hub.**  For each level `k`, the following are equivalent —
the rung read through every representation: the abstract `RHLadder k`; hole-order divisibility on the
right half; the additive ladder charge; the geometric deck charge; line holography; the window
certificate at level `k`; the strip and upper-half restrictions of the divisibility clause. -/
theorem rhLadder_tfae (k : ℕ) : List.TFAE
    [ RHLadder k,
      ∀ ρ ∈ rightHalf, xi ρ = 0 → 2 ^ k ∣ (analyticOrderAt xi ρ).toNat,
      ∀ ρ ∈ rightHalf, xi ρ = 0 → ladderCharge k ρ = 0,
      ∀ ρ ∈ rightHalf, xi ρ = 0 → xiDeckCharge k ρ = 1,
      LineHolography k,
      ∀ T : ℝ, WindowCertificate k T,
      ∀ ρ : ℂ, 1 / 2 < ρ.re → ρ.re < 1 → xi ρ = 0 → ((2 ^ k : ℕ) : ℕ∞) ∣ analyticOrderAt xi ρ,
      ∀ ρ ∈ rightHalf, 0 ≤ ρ.im → xi ρ = 0 → ((2 ^ k : ℕ) : ℕ∞) ∣ analyticOrderAt xi ρ ] := by
  tfae_have 1 ↔ 2 := rhLadder_iff_toNat_dvd k
  tfae_have 1 ↔ 3 := rhLadder_iff_ladderCharge_zero k
  tfae_have 1 ↔ 4 := rhLadder_iff_xiDeckCharge_one k
  tfae_have 1 ↔ 5 := rhLadder_iff_lineHolography k
  tfae_have 1 ↔ 6 := rhLadder_iff_forall_windowCertificate k
  tfae_have 1 ↔ 7 := rhLadder_iff_strip k
  tfae_have 1 ↔ 8 := rhLadder_iff_upperHalf k
  tfae_finish

/-- **The `RH₂` (base parity rung) characterization hub.**  `RH₂ = RHLadder 1` — every off-line zero has
even order — read through its distinctive parity handles: `2 ∣ ord`; even order; the existence of an
analytic **square root** of `ξ` on the right half; every window has even order throughout; the level-1
additive and geometric deck charges vanish; the level-1 window certificate.  RH₂ is the first, sharpest
rung: the single parity bit whose diverse readings coincide. -/
theorem rh2_tfae : List.TFAE
    [ RHLadder 1,
      ∀ ρ ∈ rightHalf, xi ρ = 0 → 2 ^ 1 ∣ (analyticOrderAt xi ρ).toNat,
      ∀ ρ ∈ rightHalf, xi ρ = 0 → Even (analyticOrderAt xi ρ).toNat,
      ∃ g, AnalyticOnNhd ℂ g rightHalf ∧ ∀ s ∈ rightHalf, g s ^ 2 = xi s,
      ∀ T : ℝ, ∀ ρ ∈ boxZeros T, Even (analyticOrderAt xi ρ).toNat,
      ∀ ρ ∈ rightHalf, xi ρ = 0 → ladderCharge 1 ρ = 0,
      ∀ ρ ∈ rightHalf, xi ρ = 0 → xiDeckCharge 1 ρ = 1,
      ∀ T : ℝ, WindowCertificate 1 T ] := by
  tfae_have 1 ↔ 2 := rhLadder_iff_toNat_dvd 1
  tfae_have 1 ↔ 3 := rhLadder_one_iff_even_order
  tfae_have 1 ↔ 4 := rhLadder_one_iff_sqrt_rightHalf
  tfae_have 1 ↔ 5 := rhLadder_one_iff_forall_window_even
  tfae_have 1 ↔ 6 := rhLadder_iff_ladderCharge_zero 1
  tfae_have 1 ↔ 7 := rhLadder_iff_xiDeckCharge_one 1
  tfae_have 1 ↔ 8 := rhLadder_iff_forall_windowCertificate 1
  tfae_finish

end RHTower
