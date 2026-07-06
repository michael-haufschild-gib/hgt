import GaloisForLFunctions.RHTower.DiscWindow

/-!
# The finite-side DISC census

The DISC bit of a window is the discrepancy between the loop class of its level-`2^{k+1}` roots and
the on-line prediction `exp(2πi·L/2^{k+1})`; by `deckClass_eq_line_iff_right_dvd` it vanishes iff
the enclosed right-half order sum `N` is divisible by `2^k`.  That order sum, reduced modulo `2^k`,
is the **window's DISC census** — a value in the finite decidable ring `ZMod (2^k)`.

For ξ the census is not computable (its zeros are the unknowns).  This file transports the census
to the concrete finite carrier `completedGN N`, whose zeros in any window are finite and whose
orders are decidable data:

* `windowDiscBit k t m` — the census, `∈ ZMod (2^k)`, of a reflection-closed configuration.
* `windowDiscBit_transport` — the boundary congruences (deck side at `2^{k+1}`, seam side at
  `2^{k+1}`) force the ξ census to EQUAL the finite-carrier census in `ZMod (2^k)`: the
  order-equivariance package read at the value level.
* `completedGN_deckClass_eq_line_iff_right_dvd` — the finite carrier's OWN loop class equals its
  line prediction iff its census vanishes: the DISC bit is a finite-side deck integral.
* `xi_rung_of_completedGN_deckClass_line` — the payoff: the finite carrier's loop-vs-line
  agreement, together with the boundary congruences, forces ξ's rung — ξ's per-window rung datum
  read off a decidable finite-carrier deck class.
-/

namespace RHTower

open Complex Set Metric

/-- The right-half enclosed order sum of a configuration — the quantity the loop class reads
(blind to the split `D = L + 2N`), i.e. the window's `N`. -/
noncomputable def windowRightSum (t : Finset ℂ) (m : ℂ → ℕ) : ℕ :=
  ∑ z ∈ t.filter (fun z => 1 / 2 < z.re), m z

/-- **The window DISC census**: the right-half enclosed order sum reduced modulo `2^k`, valued in
the finite decidable ring `ZMod (2^k)`.  Its vanishing is the level-`k` rung datum of the window;
its equality across carriers is the DISC bit's carrier-invariance. -/
noncomputable def windowDiscBit (k : ℕ) (t : Finset ℂ) (m : ℂ → ℕ) : ZMod (2 ^ k) :=
  (windowRightSum t m : ZMod (2 ^ k))

/-- The census vanishes iff the window's rung datum holds: `2^k` divides the right-half order
sum. -/
theorem windowDiscBit_eq_zero_iff (k : ℕ) (t : Finset ℂ) (m : ℂ → ℕ) :
    windowDiscBit k t m = 0 ↔ 2 ^ k ∣ windowRightSum t m := by
  haveI : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
  exact ZMod.natCast_eq_zero_iff _ _

/-- **The census transports across the seam.**  Under the two boundary congruences at level
`2^{k+1}` — the deck-side total-order congruence and the seam-side on-line congruence — the ξ
census and the finite-carrier census are EQUAL in `ZMod (2^k)`.  This is the order-equivariance
package (`anneal_window_parity_transport`) read as an identity of window values, not merely of
counts: the DISC bit is the same whether computed from ξ or from the finite carrier. -/
theorem windowDiscBit_transport {N : ℕ} (k : ℕ)
    {t₁ t₂ : Finset ℂ} {m₁ m₂ : ℂ → ℕ}
    (hm₁ : ∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z)
    (hcl₁ : ∀ z ∈ t₁, lineReflect z ∈ t₁)
    (hstrip : ∀ z ∈ t₂, 0 < z.re ∧ z.re < 1)
    (hm₂ : ∀ z ∈ t₂, (m₂ z : ℕ∞) = analyticOrderAt (completedGN N) z)
    (hcl₂ : ∀ z ∈ t₂, lineReflect z ∈ t₂)
    (hD : ∑ z ∈ t₁, m₁ z ≡ ∑ z ∈ t₂, m₂ z [MOD 2 ^ (k + 1)])
    (hL : ∑ z ∈ t₁.filter (fun z => z.re = 1 / 2), m₁ z
        ≡ ∑ z ∈ t₂.filter (fun z => z.re = 1 / 2), m₂ z [MOD 2 ^ (k + 1)]) :
    windowDiscBit k t₁ m₁ = windowDiscBit k t₂ m₂ := by
  have h := anneal_window_parity_transport k hm₁ hcl₁ hstrip hm₂ hcl₂ hD hL
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr h

/-- **The finite carrier's loop class reads its census.**  For a reflection-closed enclosed
presentation of the completed finite carrier on a window ball, its level-`2^{k+1}` deck class
equals the on-line prediction `exp(2πi·L/2^{k+1})` iff the census vanishes.  The reflection
invariance of the orders is supplied by `completedGN_orderAt_lineReflect` on the strip; no entire
factorization of `completedGN` is needed — the presentation is the hypothesis. -/
theorem completedGN_deckClass_eq_line_iff_right_dvd {N k : ℕ} {t : Finset ℂ} {m : ℂ → ℕ}
    {h G₁ G₂ : ℂ → ℂ} {a : ℂ} {r₀ R : ℝ} (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    (hstrip : ∀ z ∈ t, 0 < z.re ∧ z.re < 1)
    (hm : ∀ z ∈ t, (m z : ℕ∞) = analyticOrderAt (completedGN N) z)
    (hclosed : ∀ z ∈ t, lineReflect z ∈ t)
    (hρ : ∀ z ∈ t, ‖z - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hfact : ∀ z ∈ ball a R, completedGN N z = (∏ w ∈ t, (z - w) ^ m w) * h z)
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartRA a r₀ R)) (hG₂ : AnalyticOnNhd ℂ G₂ (chartLA a r₀ R))
    (hpG₁ : ∀ z ∈ chartRA a r₀ R, G₁ z ^ 2 ^ (k + 1) = completedGN N z)
    (hpG₂ : ∀ z ∈ chartLA a r₀ R, G₂ z ^ 2 ^ (k + 1) = completedGN N z) :
    (deckClass G₁ G₂ (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I) (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I)
        = Complex.exp (2 * (Real.pi : ℂ) * I *
            ((∑ z ∈ t.filter (fun z => z.re = 1 / 2), m z : ℕ) : ℂ)
            / ((2 ^ (k + 1) : ℕ) : ℂ)))
      ↔ 2 ^ k ∣ windowRightSum t m := by
  have hminv : ∀ z ∈ t, m (lineReflect z) = m z := by
    intro z hz
    obtain ⟨h0z, h1z⟩ := hstrip z hz
    have h1 := completedGN_orderAt_lineReflect (N := N) h0z h1z
    have h2 := hm _ (hclosed z hz)
    rw [h1, ← hm z hz] at h2
    exact Nat.cast_inj.mp h2
  exact deckClass_eq_line_iff_right_dvd h0 hrR hclosed hminv hρ hh hh0 hfact hG₁ hG₂ hpG₁ hpG₂

/-- **The finite carrier's census reads through its deck class.**  Equivalent to
`completedGN_deckClass_eq_line_iff_right_dvd`, phrased as census vanishing: the finite-side DISC
bit is `0` exactly when the loop class matches the line prediction. -/
theorem completedGN_deckClass_eq_line_iff_discBit {N k : ℕ} {t : Finset ℂ} {m : ℂ → ℕ}
    {h G₁ G₂ : ℂ → ℂ} {a : ℂ} {r₀ R : ℝ} (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    (hstrip : ∀ z ∈ t, 0 < z.re ∧ z.re < 1)
    (hm : ∀ z ∈ t, (m z : ℕ∞) = analyticOrderAt (completedGN N) z)
    (hclosed : ∀ z ∈ t, lineReflect z ∈ t)
    (hρ : ∀ z ∈ t, ‖z - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hfact : ∀ z ∈ ball a R, completedGN N z = (∏ w ∈ t, (z - w) ^ m w) * h z)
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartRA a r₀ R)) (hG₂ : AnalyticOnNhd ℂ G₂ (chartLA a r₀ R))
    (hpG₁ : ∀ z ∈ chartRA a r₀ R, G₁ z ^ 2 ^ (k + 1) = completedGN N z)
    (hpG₂ : ∀ z ∈ chartLA a r₀ R, G₂ z ^ 2 ^ (k + 1) = completedGN N z) :
    (deckClass G₁ G₂ (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I) (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I)
        = Complex.exp (2 * (Real.pi : ℂ) * I *
            ((∑ z ∈ t.filter (fun z => z.re = 1 / 2), m z : ℕ) : ℂ)
            / ((2 ^ (k + 1) : ℕ) : ℂ)))
      ↔ windowDiscBit k t m = 0 := by
  rw [windowDiscBit_eq_zero_iff]
  exact completedGN_deckClass_eq_line_iff_right_dvd h0 hrR hstrip hm hclosed hρ hh hh0 hfact
    hG₁ hG₂ hpG₁ hpG₂

/-- **The rung read off the finite carrier's deck class.**  If the finite carrier's loop class
agrees with its line prediction (its census vanishes) and the two boundary congruences hold, then
`2^k` divides ξ's right-half order sum: ξ's per-window rung datum is read from a decidable
finite-carrier deck integral. -/
theorem xi_rung_of_completedGN_discBit_zero {N k : ℕ}
    {t₁ t₂ : Finset ℂ} {m₁ m₂ : ℂ → ℕ}
    (hm₁ : ∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z)
    (hcl₁ : ∀ z ∈ t₁, lineReflect z ∈ t₁)
    (hstrip : ∀ z ∈ t₂, 0 < z.re ∧ z.re < 1)
    (hm₂ : ∀ z ∈ t₂, (m₂ z : ℕ∞) = analyticOrderAt (completedGN N) z)
    (hcl₂ : ∀ z ∈ t₂, lineReflect z ∈ t₂)
    (hD : ∑ z ∈ t₁, m₁ z ≡ ∑ z ∈ t₂, m₂ z [MOD 2 ^ (k + 1)])
    (hL : ∑ z ∈ t₁.filter (fun z => z.re = 1 / 2), m₁ z
        ≡ ∑ z ∈ t₂.filter (fun z => z.re = 1 / 2), m₂ z [MOD 2 ^ (k + 1)])
    (hfin : windowDiscBit k t₂ m₂ = 0) :
    windowDiscBit k t₁ m₁ = 0 := by
  rw [windowDiscBit_transport (N := N) k hm₁ hcl₁ hstrip hm₂ hcl₂ hD hL]
  exact hfin

/-- The same payoff in divisibility form: the finite-side census vanishing forces `2^k` to divide
ξ's right-half order sum. -/
theorem xi_rightSum_dvd_of_completedGN_discBit_zero {N k : ℕ}
    {t₁ t₂ : Finset ℂ} {m₁ m₂ : ℂ → ℕ}
    (hm₁ : ∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z)
    (hcl₁ : ∀ z ∈ t₁, lineReflect z ∈ t₁)
    (hstrip : ∀ z ∈ t₂, 0 < z.re ∧ z.re < 1)
    (hm₂ : ∀ z ∈ t₂, (m₂ z : ℕ∞) = analyticOrderAt (completedGN N) z)
    (hcl₂ : ∀ z ∈ t₂, lineReflect z ∈ t₂)
    (hD : ∑ z ∈ t₁, m₁ z ≡ ∑ z ∈ t₂, m₂ z [MOD 2 ^ (k + 1)])
    (hL : ∑ z ∈ t₁.filter (fun z => z.re = 1 / 2), m₁ z
        ≡ ∑ z ∈ t₂.filter (fun z => z.re = 1 / 2), m₂ z [MOD 2 ^ (k + 1)])
    (hfin : windowDiscBit k t₂ m₂ = 0) :
    2 ^ k ∣ windowRightSum t₁ m₁ :=
  (windowDiscBit_eq_zero_iff k t₁ m₁).mp
    (xi_rung_of_completedGN_discBit_zero (N := N) hm₁ hcl₁ hstrip hm₂ hcl₂ hD hL hfin)

end RHTower
