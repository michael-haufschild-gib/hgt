import GaloisForLFunctions.RHTower.DiscWindow
import GaloisForLFunctions.RHTower.SeamCongruence

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

/-- A vanishing ξ DISC bit on a reflection-closed subwindow is exactly the subwindow congruence.
This is the local, per-subconfiguration form that avoids the full-window total-sum blindness. -/
theorem subWindow_congruence_of_windowDiscBit_zero {k : ℕ} {T : ℝ} {t : Finset ℂ}
    (_hsub : ↑t ⊆ stripZeros T)
    (hclosed : ∀ z ∈ t, lineReflect z ∈ t)
    (hbit : windowDiscBit k t (fun z => (analyticOrderAt xi z).toNat) = 0) :
    ∑ ρ ∈ t, (analyticOrderAt xi ρ).toNat ≡
      ∑ ρ ∈ t.filter (fun ρ => ρ.re = 1 / 2),
        (analyticOrderAt xi ρ).toNat [MOD 2 ^ (k + 1)] := by
  have hmr : ∀ z ∈ t,
      (fun ρ => (analyticOrderAt xi ρ).toNat) (lineReflect z) =
        (fun ρ => (analyticOrderAt xi ρ).toNat) z := by
    intro z _
    exact congrArg ENat.toNat (xi_orderAt_lineReflect z)
  have hID := window_identity (m := fun ρ => (analyticOrderAt xi ρ).toNat) hclosed hmr
  rw [window_modEq_iff hID]
  exact (windowDiscBit_eq_zero_iff k t (fun z => (analyticOrderAt xi z).toNat)).mp hbit

/-- Window certificates from vanishing ξ DISC bits on every reflection-closed subwindow. -/
theorem windowCertificate_of_subWindow_discBits_zero {k : ℕ} {T : ℝ}
    (hbits : ∀ t : Finset ℂ, ↑t ⊆ stripZeros T →
      (∀ z ∈ t, lineReflect z ∈ t) →
      windowDiscBit k t (fun z => (analyticOrderAt xi z).toNat) = 0) :
    WindowCertificate k T := by
  rw [windowCertificate_iff_subWindow_congruences]
  intro t hsub hclosed
  exact subWindow_congruence_of_windowDiscBit_zero hsub hclosed (hbits t hsub hclosed)

/-- Window certificates from transported finite DISC bits on every reflection-closed subwindow.
Each subconfiguration may use its own finite completed-carrier presentation; what matters is that
the transport congruences identify its DISC bit with a finite bit that vanishes. -/
theorem windowCertificate_of_subWindow_finiteDiscBits_zero {k : ℕ} {T : ℝ}
    (hbits : ∀ t : Finset ℂ, ↑t ⊆ stripZeros T →
      (∀ z ∈ t, lineReflect z ∈ t) →
      ∃ N : ℕ, ∃ t₂ : Finset ℂ, ∃ m₂ : ℂ → ℕ,
        (∀ z ∈ t₂, 0 < z.re ∧ z.re < 1) ∧
        (∀ z ∈ t₂, (m₂ z : ℕ∞) = analyticOrderAt (completedGN N) z) ∧
        (∀ z ∈ t₂, lineReflect z ∈ t₂) ∧
        (∑ z ∈ t, (analyticOrderAt xi z).toNat ≡ ∑ z ∈ t₂, m₂ z
          [MOD 2 ^ (k + 1)]) ∧
        (∑ z ∈ t.filter (fun z => z.re = 1 / 2), (analyticOrderAt xi z).toNat
          ≡ ∑ z ∈ t₂.filter (fun z => z.re = 1 / 2), m₂ z [MOD 2 ^ (k + 1)]) ∧
        windowDiscBit k t₂ m₂ = 0) :
    WindowCertificate k T := by
  refine windowCertificate_of_subWindow_discBits_zero ?_
  intro t hsub hclosed
  rcases hbits t hsub hclosed with
    ⟨N, t₂, m₂, hstrip, hm₂, hcl₂, hD, hL, hfin⟩
  exact xi_rung_of_completedGN_discBit_zero (N := N) (k := k)
    (fun z _ => ENat.coe_toNat (xi_order_ne_top z)) hclosed hstrip hm₂ hcl₂ hD hL hfin

/-- Finite deck-line data for every reflection-closed subwindow of a height window.  Each
subwindow may choose its own completed finite carrier, zero presentation, root charts, and
transport congruences; the finite carrier's deck class is required to match its line prediction. -/
def SubWindowFiniteDeckLineData (k : ℕ) (T : ℝ) : Prop :=
  ∀ t : Finset ℂ, ↑t ⊆ stripZeros T →
    (∀ z ∈ t, lineReflect z ∈ t) →
    ∃ N : ℕ, ∃ t₂ : Finset ℂ, ∃ m₂ : ℂ → ℕ,
    ∃ h G₁ G₂ : ℂ → ℂ, ∃ a : ℂ, ∃ r₀ R : ℝ,
      0 ≤ r₀ ∧ r₀ < R ∧
      (∀ z ∈ t₂, 0 < z.re ∧ z.re < 1) ∧
      (∀ z ∈ t₂, (m₂ z : ℕ∞) = analyticOrderAt (completedGN N) z) ∧
      (∀ z ∈ t₂, lineReflect z ∈ t₂) ∧
      (∀ z ∈ t₂, ‖z - a‖ ≤ r₀) ∧
      AnalyticOnNhd ℂ h (ball a R) ∧
      (∀ z ∈ ball a R, h z ≠ 0) ∧
      (∀ z ∈ ball a R, completedGN N z = (∏ w ∈ t₂, (z - w) ^ m₂ w) * h z) ∧
      AnalyticOnNhd ℂ G₁ (chartRA a r₀ R) ∧
      AnalyticOnNhd ℂ G₂ (chartLA a r₀ R) ∧
      (∀ z ∈ chartRA a r₀ R, G₁ z ^ 2 ^ (k + 1) = completedGN N z) ∧
      (∀ z ∈ chartLA a r₀ R, G₂ z ^ 2 ^ (k + 1) = completedGN N z) ∧
      (deckClass G₁ G₂ (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I)
          (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I)
        = Complex.exp (2 * (Real.pi : ℂ) * I *
            ((∑ z ∈ t₂.filter (fun z => z.re = 1 / 2), m₂ z : ℕ) : ℂ)
            / ((2 ^ (k + 1) : ℕ) : ℂ))) ∧
      (∑ z ∈ t, (analyticOrderAt xi z).toNat ≡ ∑ z ∈ t₂, m₂ z
        [MOD 2 ^ (k + 1)]) ∧
      (∑ z ∈ t.filter (fun z => z.re = 1 / 2), (analyticOrderAt xi z).toNat
        ≡ ∑ z ∈ t₂.filter (fun z => z.re = 1 / 2), m₂ z [MOD 2 ^ (k + 1)])

/-- Window certificates from finite deck-line equality on every reflection-closed subwindow.
This discharges the finite-side `windowDiscBit = 0` premise through the completed finite carrier's
own deck class, so the subwindow bridge consumes deck data rather than a precomputed DISC bit. -/
theorem windowCertificate_of_subWindow_finiteDeckLine {k : ℕ} {T : ℝ}
    (hbits : SubWindowFiniteDeckLineData k T) :
    WindowCertificate k T := by
  refine windowCertificate_of_subWindow_finiteDiscBits_zero ?_
  intro t hsub hclosed
  rcases hbits t hsub hclosed with
    ⟨N, t₂, m₂, h, G₁, G₂, a, r₀, R, h0, hrR, hstrip, hm₂, hcl₂, hρ₂,
      hhan, hh0, hfact, hG₁, hG₂, hpG₁, hpG₂, hdeck, hD, hL⟩
  refine ⟨N, t₂, m₂, hstrip, hm₂, hcl₂, hD, hL, ?_⟩
  exact (completedGN_deckClass_eq_line_iff_discBit (N := N) (k := k)
    (t := t₂) (m := m₂) (h := h) (G₁ := G₁) (G₂ := G₂) (a := a)
    (r₀ := r₀) (R := R) h0 hrR hstrip hm₂ hcl₂ hρ₂ hhan hh0 hfact
    hG₁ hG₂ hpG₁ hpG₂).mp hdeck

/-- Cofinal supply of subwindow finite deck-line data at a fixed rung. -/
def CofinalSubWindowFiniteDeckLineData (k : ℕ) : Prop :=
  ∀ B : ℝ, ∃ T, B ≤ T ∧ SubWindowFiniteDeckLineData k T

/-- Cofinal subwindow finite deck-line data forces the fixed RH ladder rung. -/
theorem rhLadder_of_cofinal_subWindow_finiteDeckLineData {k : ℕ}
    (hbits : CofinalSubWindowFiniteDeckLineData k) :
    RHLadder k := by
  refine rhLadder_of_cofinal_windowCertificates ?_
  intro B
  obtain ⟨T, hBT, hT⟩ := hbits B
  exact ⟨T, hBT, windowCertificate_of_subWindow_finiteDeckLine hT⟩

/-- Cofinal subwindow finite deck-line data at every rung gives RH. -/
theorem rh_of_cofinal_subWindow_finiteDeckLineData
    (hbits : ∀ k : ℕ, CofinalSubWindowFiniteDeckLineData k) :
    RiemannHypothesis := by
  rw [rh_iff_forall_ladder]
  intro k
  exact rhLadder_of_cofinal_subWindow_finiteDeckLineData (hbits k)

/-- Subwindow finite deck-line data with the transport congruences discharged by the seam.
Instead of assuming the total-count congruence `hD` and the line-count congruence `hL`, this
interface supplies peeled ξ/completed-carrier presentations, EM/LOW domination data on the
annular charts, and two sign tables.  `anneal_D_transport` then gives total equality, while
`hL_exact_of_two_sign_data` gives line equality. -/
def SubWindowFiniteDeckLineTwoSignData (k : ℕ) (T : ℝ) : Prop :=
  ∀ t : Finset ℂ, ↑t ⊆ stripZeros T →
    (∀ z ∈ t, lineReflect z ∈ t) →
    ∃ N M : ℕ, ∃ t₂ : Finset ℂ, ∃ m₂ : ℂ → ℕ,
    ∃ h h' G₁ G₂ : ℂ → ℂ, ∃ a : ℂ, ∃ r₀ R ε₁ δ : ℝ,
    ∃ s₁ : ℕ, ∃ ts₁ : ℕ → ℝ, ∃ s₂ : ℕ, ∃ ts₂ : ℕ → ℝ,
      1 ≤ M ∧
      0 ≤ r₀ ∧ r₀ < R ∧
      (∀ z ∈ t₂, 0 < z.re ∧ z.re < 1) ∧
      (∀ z ∈ t₂, (m₂ z : ℕ∞) = analyticOrderAt (completedGN N) z) ∧
      (∀ z ∈ t₂, lineReflect z ∈ t₂) ∧
      (∀ z ∈ t, ‖z - a‖ ≤ r₀) ∧
      (∀ z ∈ t₂, ‖z - a‖ ≤ r₀) ∧
      AnalyticOnNhd ℂ h (ball a R) ∧
      (∀ z ∈ ball a R, h z ≠ 0) ∧
      AnalyticOnNhd ℂ h' (ball a R) ∧
      (∀ z ∈ ball a R, h' z ≠ 0) ∧
      (∀ z ∈ ball a R,
        xi z = (∏ w ∈ t, (z - w) ^ (analyticOrderAt xi w).toNat) * h z) ∧
      (∀ z ∈ ball a R, completedGN N z = (∏ w ∈ t₂, (z - w) ^ m₂ w) * h' z) ∧
      (∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, 0 < z.re ∧ z.re < 1) ∧
      (∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
        ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁) ∧
      (∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
        ‖emCarrier M z - gN N z‖ ≤ δ) ∧
      CarrierFloorOn (chartRA a r₀ R ∪ chartLA a r₀ R) N (ε₁ + δ) ∧
      AnalyticOnNhd ℂ G₁ (chartRA a r₀ R) ∧
      AnalyticOnNhd ℂ G₂ (chartLA a r₀ R) ∧
      (∀ z ∈ chartRA a r₀ R, G₁ z ^ 2 ^ (k + 1) = completedGN N z) ∧
      (∀ z ∈ chartLA a r₀ R, G₂ z ^ 2 ^ (k + 1) = completedGN N z) ∧
      (deckClass G₁ G₂ (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I)
          (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I)
        = Complex.exp (2 * (Real.pi : ℂ) * I *
            ((∑ z ∈ t₂.filter (fun z => z.re = 1 / 2), m₂ z : ℕ) : ℂ)
            / ((2 ^ (k + 1) : ℕ) : ℂ))) ∧
      (∀ i, i < s₁ → ts₁ i < ts₁ (i + 1)) ∧
      (∀ i, i < s₁ →
        (xi (linePoint (ts₁ i))).re * (xi (linePoint (ts₁ (i + 1)))).re < 0) ∧
      (∀ u : ℝ, ts₁ 0 ≤ u → u ≤ ts₁ s₁ → linePoint u ∈ ball a R) ∧
      (∑ z ∈ t₂, m₂ z ≤ s₁) ∧
      (∀ i, i < s₂ → ts₂ i < ts₂ (i + 1)) ∧
      (∀ i, i < s₂ →
        (completedGN N (linePoint (ts₂ i))).re *
          (completedGN N (linePoint (ts₂ (i + 1)))).re < 0) ∧
      (∀ u : ℝ, ts₂ 0 ≤ u → u ≤ ts₂ s₂ → linePoint u ∈ ball a R) ∧
      (∑ z ∈ t₂, m₂ z ≤ s₂)

/-- Two-sign subwindow data discharges the raw transport congruences of
`SubWindowFiniteDeckLineData`. -/
theorem subWindowFiniteDeckLineData_of_twoSignData {k : ℕ} {T : ℝ}
    (hbits : SubWindowFiniteDeckLineTwoSignData k T) :
    SubWindowFiniteDeckLineData k T := by
  intro t hsub hclosed
  rcases hbits t hsub hclosed with
    ⟨N, M, t₂, m₂, h, h', G₁, G₂, a, r₀, R, ε₁, δ, s₁, ts₁, s₂, ts₂,
      hM, h0, hrR, hstrip₂, hm₂, hcl₂, hρ₁, hρ₂, hhan, hh0, hhan', hh0',
      hfact₁, hfact₂, hchartStrip, hE, hclose, hF, hG₁, hG₂, hpG₁, hpG₂,
      hdeck, hmono₁, hsign₁, hseg₁, hcount₂₁, hmono₂, hsign₂, hseg₂, hcount₂₂⟩
  have hm₁ : ∀ z ∈ t,
      ((fun ρ => (analyticOrderAt xi ρ).toNat) z : ℕ∞) = analyticOrderAt xi z := by
    intro z _
    exact ENat.coe_toNat (xi_order_ne_top z)
  have hdom : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖xi z - completedGN N z‖ < ‖completedGN N z‖ :=
    completed_domination_of_emCarrier_close_floor hM hchartStrip hE hclose hF
  have hDeq : ∑ z ∈ t, (analyticOrderAt xi z).toNat = ∑ z ∈ t₂, m₂ z :=
    anneal_D_transport h0 hrR hρ₁ hρ₂ hhan hh0 hhan' hh0' hfact₁ hfact₂ hdom
  have hD : ∑ z ∈ t, (analyticOrderAt xi z).toNat ≡ ∑ z ∈ t₂, m₂ z
      [MOD 2 ^ (k + 1)] := by
    rw [hDeq]
  have hLeq : ∑ z ∈ t.filter (fun z => z.re = 1 / 2), (analyticOrderAt xi z).toNat =
      ∑ z ∈ t₂.filter (fun z => z.re = 1 / 2), m₂ z :=
    hL_exact_of_two_sign_data h0 hrR hm₁ hclosed hstrip₂ hm₂ hcl₂ hρ₁ hρ₂
      hhan hh0 hhan' hh0' hfact₁ hfact₂ hdom hmono₁ hsign₁ hseg₁ hcount₂₁
      hmono₂ hsign₂ hseg₂ hcount₂₂
  have hL : ∑ z ∈ t.filter (fun z => z.re = 1 / 2), (analyticOrderAt xi z).toNat
      ≡ ∑ z ∈ t₂.filter (fun z => z.re = 1 / 2), m₂ z [MOD 2 ^ (k + 1)] := by
    rw [hLeq]
  exact ⟨N, t₂, m₂, h', G₁, G₂, a, r₀, R, h0, hrR, hstrip₂, hm₂, hcl₂, hρ₂,
    hhan', hh0', hfact₂, hG₁, hG₂, hpG₁, hpG₂, hdeck, hD, hL⟩

/-- Window certificate from subwindow finite deck-line data whose transport congruences are
derived from EM/LOW domination and two sign tables. -/
theorem windowCertificate_of_subWindow_finiteDeckLine_twoSignData {k : ℕ} {T : ℝ}
    (hbits : SubWindowFiniteDeckLineTwoSignData k T) :
    WindowCertificate k T :=
  windowCertificate_of_subWindow_finiteDeckLine
    (subWindowFiniteDeckLineData_of_twoSignData hbits)

/-- Cofinal supply of two-sign subwindow finite deck-line data at a fixed rung. -/
def CofinalSubWindowFiniteDeckLineTwoSignData (k : ℕ) : Prop :=
  ∀ B : ℝ, ∃ T, B ≤ T ∧ SubWindowFiniteDeckLineTwoSignData k T

/-- Cofinal two-sign subwindow finite deck-line data forces the fixed RH ladder rung. -/
theorem rhLadder_of_cofinal_subWindow_finiteDeckLineTwoSignData {k : ℕ}
    (hbits : CofinalSubWindowFiniteDeckLineTwoSignData k) :
    RHLadder k := by
  refine rhLadder_of_cofinal_windowCertificates ?_
  intro B
  obtain ⟨T, hBT, hT⟩ := hbits B
  exact ⟨T, hBT, windowCertificate_of_subWindow_finiteDeckLine_twoSignData hT⟩

/-- Cofinal two-sign subwindow finite deck-line data at every rung gives RH. -/
theorem rh_of_cofinal_subWindow_finiteDeckLineTwoSignData
    (hbits : ∀ k : ℕ, CofinalSubWindowFiniteDeckLineTwoSignData k) :
    RiemannHypothesis := by
  rw [rh_iff_forall_ladder]
  intro k
  exact rhLadder_of_cofinal_subWindow_finiteDeckLineTwoSignData (hbits k)

end RHTower
