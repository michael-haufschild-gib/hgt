/-
Doc 22 §2 ASSEMBLED (task #165): the mod-2^k window relation transports to the
concrete finite carrier — D-transport + L-transport + (ID) on both carriers,
composed into single statements.

The reduction's endgame arithmetic, machine-checked end to end on the actual
objects (ξ and `completedGN`):

* `analyticOrderAt_conj_conj_of_analyticAt` / `analyticOrderAt_conj_of_conjEquivariant`
  — the Schwarz-reflection order equivariance LOCALIZED (entirety dropped): the
  last missing multiplicity input for the meromorphic completed carrier.
* `completedGN_analyticAt`, `completedGN_orderAt_conj`,
  `completedGN_orderAt_lineReflect` — the finite carrier now has the FULL
  line-reflection equivariance package on the strip; `xi_orderAt_lineReflect`
  names ξ's. These are exactly what `window_identity` (ID) consumes.
* `window_N_congruence` — the arithmetic core: two (ID)s + boundary congruences
  `D₁ ≡ D₂`, `L₁ ≡ L₂ (mod 2^{k+1})` ⟹ `N₁ ≡ N₂ (mod 2^k)`.
* `anneal_window_parity_transport` — the assembly on the carriers: the (ID)s are
  DERIVED from the banked equivariances (not assumed); only the two transported
  boundary congruences remain as inputs.
* `xi_rung_of_finite_side` — the reduction payoff: 2^k-divisibility of the
  truncation's right-half count forces ξ's.
* `anneal_mod_two_window_relation` — the k = 1 headline: level-4 boundary
  congruences ⟹ `N_ξ(W) ≡ N_g(W) (mod 2)`.

Where the two congruence inputs come from (the "doubly-dominated" reading):
the deck side `hD` is fed by chart-wide domination via `anneal_deck_transport`
(+ the level-2^{k+1} deck↔counting dictionary); the seam side `hL` is fed at
level 2 by `anneal_seam_L_transport` (two-point on-line domination). The
residual between the seam datum (L mod 2) and the required `hL` (L mod 2^{k+1})
is precisely the (K1)-blindness measured by `deckClass_blind_to_split` —
boundary data at level 2 cannot separate an on-line double zero from an
off-line pair. That lift is the remaining dictionary item, typed here as the
`hL` hypothesis; it is finite-side-checkable per window (the truncation's zeros
are computable), which is what the instance runs discharge.
-/
import GaloisForLFunctions.RHTower.SeamSignTransport
import GaloisForLFunctions.RHTower.CountingSubstitute
import GaloisForLFunctions.RHTower.WindowRelation

namespace RHTower

open Complex

/-! ### §1 The completed carrier: analyticity and full line-reflection equivariance -/

/-- Reality pairing of orders for the completed carrier on the strip. -/
private theorem completedGN_orderAt_conj {N : ℕ} {z : ℂ} (h0 : 0 < z.re) (h1 : z.re < 1) :
    analyticOrderAt (completedGN N) ((starRingEnd ℂ) z)
      = analyticOrderAt (completedGN N) z :=
  analyticOrderAt_conj_of_conjEquivariant (completedGN_conj N)
    (completedGN_analyticAt h0 h1)
    (completedGN_analyticAt (by rwa [Complex.conj_re]) (by rwa [Complex.conj_re]))

/-- FULL line-reflection order equivariance for the completed carrier on the strip:
the multiplicity structure the window identity (ID) consumes on the finite side. -/
theorem completedGN_orderAt_lineReflect {N : ℕ} {z : ℂ} (h0 : 0 < z.re) (h1 : z.re < 1) :
    analyticOrderAt (completedGN N) (lineReflect z)
      = analyticOrderAt (completedGN N) z := by
  have hc0 : 0 < ((starRingEnd ℂ) z).re := by rwa [Complex.conj_re]
  have hc1 : ((starRingEnd ℂ) z).re < 1 := by rwa [Complex.conj_re]
  rw [show lineReflect z = 1 - (starRingEnd ℂ) z from rfl,
    completedGN_orderAt_one_sub hc0 hc1, completedGN_orderAt_conj h0 h1]

/-! ### §3 The arithmetic core of the reduction -/

/-- **The window-parity transport, arithmetic core** (doc 22 §2's conclusion): two
(ID)s plus the two boundary congruences at level `2^(k+1)` force the right-half
counts to agree mod `2^k`. -/
theorem window_N_congruence {k D₁ L₁ N₁ D₂ L₂ N₂ : ℕ}
    (hID₁ : D₁ = L₁ + 2 * N₁) (hID₂ : D₂ = L₂ + 2 * N₂)
    (hD : D₁ ≡ D₂ [MOD 2 ^ (k + 1)]) (hL : L₁ ≡ L₂ [MOD 2 ^ (k + 1)]) :
    N₁ ≡ N₂ [MOD 2 ^ k] := by
  subst hID₁ hID₂
  have h2 : 2 * N₁ ≡ 2 * N₂ [MOD 2 ^ (k + 1)] := hL.add_left_cancel hD
  have hpow : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by
    rw [pow_succ]
    ring
  rw [hpow] at h2
  unfold Nat.ModEq at h2 ⊢
  rw [Nat.mul_mod_mul_left, Nat.mul_mod_mul_left] at h2
  exact Nat.eq_of_mul_eq_mul_left two_pos h2

/-! ### §4 The assembled window-parity transport on the actual carriers -/

/-- **The mod-2^k window-parity transport, assembled** (doc 22 §2 end to end):
for a reflection-closed ξ-configuration and a reflection-closed strip configuration
of the concrete completed truncation, the two transported boundary congruences
(deck side at level 2^{k+1}, seam side at level 2^{k+1}) force
`N_ξ(W) ≡ N_g(W) (mod 2^k)`. The (ID)s are DERIVED from the carriers' banked
equivariances, not assumed. -/
theorem anneal_window_parity_transport {N : ℕ} (k : ℕ)
    {t₁ t₂ : Finset ℂ} {m₁ m₂ : ℂ → ℕ}
    (hm₁ : ∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z)
    (hcl₁ : ∀ z ∈ t₁, lineReflect z ∈ t₁)
    (hstrip : ∀ z ∈ t₂, 0 < z.re ∧ z.re < 1)
    (hm₂ : ∀ z ∈ t₂, (m₂ z : ℕ∞) = analyticOrderAt (completedGN N) z)
    (hcl₂ : ∀ z ∈ t₂, lineReflect z ∈ t₂)
    (hD : ∑ z ∈ t₁, m₁ z ≡ ∑ z ∈ t₂, m₂ z [MOD 2 ^ (k + 1)])
    (hL : ∑ z ∈ t₁.filter (fun z => z.re = 1 / 2), m₁ z
        ≡ ∑ z ∈ t₂.filter (fun z => z.re = 1 / 2), m₂ z [MOD 2 ^ (k + 1)]) :
    ∑ z ∈ t₁.filter (fun z => 1 / 2 < z.re), m₁ z
      ≡ ∑ z ∈ t₂.filter (fun z => 1 / 2 < z.re), m₂ z [MOD 2 ^ k] := by
  classical
  have hmr₁ : ∀ z ∈ t₁, m₁ (lineReflect z) = m₁ z := by
    intro z hz
    have h1 := xi_orderAt_lineReflect z
    have h2 := hm₁ _ (hcl₁ z hz)
    rw [h1, ← hm₁ z hz] at h2
    exact Nat.cast_inj.mp h2
  have hmr₂ : ∀ z ∈ t₂, m₂ (lineReflect z) = m₂ z := by
    intro z hz
    obtain ⟨h0, h1⟩ := hstrip z hz
    have h1eq := completedGN_orderAt_lineReflect (N := N) h0 h1
    have h2 := hm₂ _ (hcl₂ z hz)
    rw [h1eq, ← hm₂ z hz] at h2
    exact Nat.cast_inj.mp h2
  exact window_N_congruence (window_identity hcl₁ hmr₁) (window_identity hcl₂ hmr₂) hD hL

/-- **The rung reads off the finite side**: under the same transported congruences,
2^k-divisibility of the truncation's right-half count forces ξ's. -/
theorem xi_rung_of_finite_side {N : ℕ} (k : ℕ)
    {t₁ t₂ : Finset ℂ} {m₁ m₂ : ℂ → ℕ}
    (hm₁ : ∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z)
    (hcl₁ : ∀ z ∈ t₁, lineReflect z ∈ t₁)
    (hstrip : ∀ z ∈ t₂, 0 < z.re ∧ z.re < 1)
    (hm₂ : ∀ z ∈ t₂, (m₂ z : ℕ∞) = analyticOrderAt (completedGN N) z)
    (hcl₂ : ∀ z ∈ t₂, lineReflect z ∈ t₂)
    (hD : ∑ z ∈ t₁, m₁ z ≡ ∑ z ∈ t₂, m₂ z [MOD 2 ^ (k + 1)])
    (hL : ∑ z ∈ t₁.filter (fun z => z.re = 1 / 2), m₁ z
        ≡ ∑ z ∈ t₂.filter (fun z => z.re = 1 / 2), m₂ z [MOD 2 ^ (k + 1)])
    (hfin : 2 ^ k ∣ ∑ z ∈ t₂.filter (fun z => 1 / 2 < z.re), m₂ z) :
    2 ^ k ∣ ∑ z ∈ t₁.filter (fun z => 1 / 2 < z.re), m₁ z := by
  have h := anneal_window_parity_transport k hm₁ hcl₁ hstrip hm₂ hcl₂ hD hL
  exact Nat.modEq_zero_iff_dvd.mp (h.trans (Nat.modEq_zero_iff_dvd.mpr hfin))

/-- **The mod-2 window relation on doubly-dominated strip windows** (k = 1
headline): boundary congruences at level 4 give `N_ξ(W) ≡ N_g(W) (mod 2)`. -/
theorem anneal_mod_two_window_relation {N : ℕ}
    {t₁ t₂ : Finset ℂ} {m₁ m₂ : ℂ → ℕ}
    (hm₁ : ∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z)
    (hcl₁ : ∀ z ∈ t₁, lineReflect z ∈ t₁)
    (hstrip : ∀ z ∈ t₂, 0 < z.re ∧ z.re < 1)
    (hm₂ : ∀ z ∈ t₂, (m₂ z : ℕ∞) = analyticOrderAt (completedGN N) z)
    (hcl₂ : ∀ z ∈ t₂, lineReflect z ∈ t₂)
    (hD : ∑ z ∈ t₁, m₁ z ≡ ∑ z ∈ t₂, m₂ z [MOD 4])
    (hL : ∑ z ∈ t₁.filter (fun z => z.re = 1 / 2), m₁ z
        ≡ ∑ z ∈ t₂.filter (fun z => z.re = 1 / 2), m₂ z [MOD 4]) :
    ∑ z ∈ t₁.filter (fun z => 1 / 2 < z.re), m₁ z
      ≡ ∑ z ∈ t₂.filter (fun z => 1 / 2 < z.re), m₂ z [MOD 2] := by
  have h4 : (4 : ℕ) = 2 ^ (1 + 1) := by norm_num
  have h2 : (2 : ℕ) = 2 ^ (1 : ℕ) := by norm_num
  rw [h4] at hD hL
  rw [h2]
  exact anneal_window_parity_transport 1 hm₁ hcl₁ hstrip hm₂ hcl₂ hD hL

end RHTower

namespace RHTower

open Metric

/-- **The D-transport, discharged at the counting level** (executable (i)): peeled
factorizations of ξ and the completed truncation on a window ball, zeros in the
hole, domination on the slit-annulus charts ⟹ the enclosed multiplicity counts are
EQUAL — not merely congruent. Instantiates `enclosed_count_eq_of_close`
(the Rouché substitute) on the concrete carriers. -/
theorem anneal_D_transport {N : ℕ} {t₁ t₂ : Finset ℂ} {m₁ m₂ : ℂ → ℕ}
    {h h' : ℂ → ℂ} {a : ℂ} {r₀ R : ℝ} (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    (hρ₁ : ∀ w ∈ t₁, ‖w - a‖ ≤ r₀) (hρ₂ : ∀ w ∈ t₂, ‖w - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hh' : AnalyticOnNhd ℂ h' (ball a R)) (hh0' : ∀ z ∈ ball a R, h' z ≠ 0)
    (hfact₁ : ∀ z ∈ ball a R, xi z = (∏ w ∈ t₁, (z - w) ^ m₁ w) * h z)
    (hfact₂ : ∀ z ∈ ball a R, completedGN N z = (∏ w ∈ t₂, (z - w) ^ m₂ w) * h' z)
    (hdom : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖xi z - completedGN N z‖ < ‖completedGN N z‖) :
    ∑ w ∈ t₁, m₁ w = ∑ w ∈ t₂, m₂ w :=
  enclosed_count_eq_of_close t₂ t₁ id m₂ id m₁ h0 hrR hρ₂ hρ₁ hh' hh0' hh hh0
    hfact₂ hfact₁ hdom

/-- **The mod-2 window relation under domination** (doc 22 §2, maximally
discharged): on a strip window with peeled factorizations of both carriers and
domination on the slit-annulus charts, the deck-side input hD is PROVED (exact
count equality); the single remaining analytic input is the seam congruence hL —
the on-line multiplicity sums mod 4, computable from the finite side's certified
zero data. Conclusion: `N_ξ(W) ≡ N_g(W) (mod 2)`. -/
theorem anneal_mod_two_window_relation_of_domination {N : ℕ}
    {t₁ t₂ : Finset ℂ} {m₁ m₂ : ℂ → ℕ} {h h' : ℂ → ℂ} {a : ℂ} {r₀ R : ℝ}
    (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    (hm₁ : ∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z)
    (hcl₁ : ∀ z ∈ t₁, lineReflect z ∈ t₁)
    (hstrip : ∀ z ∈ t₂, 0 < z.re ∧ z.re < 1)
    (hm₂ : ∀ z ∈ t₂, (m₂ z : ℕ∞) = analyticOrderAt (completedGN N) z)
    (hcl₂ : ∀ z ∈ t₂, lineReflect z ∈ t₂)
    (hρ₁ : ∀ w ∈ t₁, ‖w - a‖ ≤ r₀) (hρ₂ : ∀ w ∈ t₂, ‖w - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hh' : AnalyticOnNhd ℂ h' (ball a R)) (hh0' : ∀ z ∈ ball a R, h' z ≠ 0)
    (hfact₁ : ∀ z ∈ ball a R, xi z = (∏ w ∈ t₁, (z - w) ^ m₁ w) * h z)
    (hfact₂ : ∀ z ∈ ball a R, completedGN N z = (∏ w ∈ t₂, (z - w) ^ m₂ w) * h' z)
    (hdom : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖xi z - completedGN N z‖ < ‖completedGN N z‖)
    (hL : ∑ z ∈ t₁.filter (fun z => z.re = 1 / 2), m₁ z
        ≡ ∑ z ∈ t₂.filter (fun z => z.re = 1 / 2), m₂ z [MOD 4]) :
    ∑ z ∈ t₁.filter (fun z => 1 / 2 < z.re), m₁ z
      ≡ ∑ z ∈ t₂.filter (fun z => 1 / 2 < z.re), m₂ z [MOD 2] := by
  have hDeq : ∑ w ∈ t₁, m₁ w = ∑ w ∈ t₂, m₂ w :=
    anneal_D_transport h0 hrR hρ₁ hρ₂ hh hh0 hh' hh0' hfact₁ hfact₂ hdom
  exact anneal_mod_two_window_relation hm₁ hcl₁ hstrip hm₂ hcl₂
    (hDeq ▸ Nat.ModEq.refl _) hL

end RHTower

namespace RHTower

open Metric

/-- **General window-parity transport under domination.** The domination/counting
substitute proves the deck-side congruence exactly, so every `2^k` rung only
keeps the seam congruence as an input. -/
theorem anneal_window_parity_transport_of_domination {N : ℕ} (k : ℕ)
    {t₁ t₂ : Finset ℂ} {m₁ m₂ : ℂ → ℕ} {h h' : ℂ → ℂ} {a : ℂ} {r₀ R : ℝ}
    (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    (hm₁ : ∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z)
    (hcl₁ : ∀ z ∈ t₁, lineReflect z ∈ t₁)
    (hstrip : ∀ z ∈ t₂, 0 < z.re ∧ z.re < 1)
    (hm₂ : ∀ z ∈ t₂, (m₂ z : ℕ∞) = analyticOrderAt (completedGN N) z)
    (hcl₂ : ∀ z ∈ t₂, lineReflect z ∈ t₂)
    (hρ₁ : ∀ w ∈ t₁, ‖w - a‖ ≤ r₀) (hρ₂ : ∀ w ∈ t₂, ‖w - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hh' : AnalyticOnNhd ℂ h' (ball a R)) (hh0' : ∀ z ∈ ball a R, h' z ≠ 0)
    (hfact₁ : ∀ z ∈ ball a R, xi z = (∏ w ∈ t₁, (z - w) ^ m₁ w) * h z)
    (hfact₂ : ∀ z ∈ ball a R, completedGN N z = (∏ w ∈ t₂, (z - w) ^ m₂ w) * h' z)
    (hdom : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖xi z - completedGN N z‖ < ‖completedGN N z‖)
    (hL : ∑ z ∈ t₁.filter (fun z => z.re = 1 / 2), m₁ z
        ≡ ∑ z ∈ t₂.filter (fun z => z.re = 1 / 2), m₂ z [MOD 2 ^ (k + 1)]) :
    ∑ z ∈ t₁.filter (fun z => 1 / 2 < z.re), m₁ z
      ≡ ∑ z ∈ t₂.filter (fun z => 1 / 2 < z.re), m₂ z [MOD 2 ^ k] := by
  have hDeq : ∑ w ∈ t₁, m₁ w = ∑ w ∈ t₂, m₂ w :=
    anneal_D_transport h0 hrR hρ₁ hρ₂ hh hh0 hh' hh0' hfact₁ hfact₂ hdom
  exact anneal_window_parity_transport k hm₁ hcl₁ hstrip hm₂ hcl₂
    (hDeq ▸ Nat.ModEq.refl _) hL

end RHTower

namespace RHTower

open Metric

/-- **Finite-side rung under domination.** Domination proves the deck count transport;
combined with the seam congruence and finite-side rung, this gives the ξ rung. -/
theorem xi_rung_of_finite_side_of_domination {N : ℕ} (k : ℕ)
    {t₁ t₂ : Finset ℂ} {m₁ m₂ : ℂ → ℕ} {h h' : ℂ → ℂ} {a : ℂ} {r₀ R : ℝ}
    (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    (hm₁ : ∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z)
    (hcl₁ : ∀ z ∈ t₁, lineReflect z ∈ t₁)
    (hstrip : ∀ z ∈ t₂, 0 < z.re ∧ z.re < 1)
    (hm₂ : ∀ z ∈ t₂, (m₂ z : ℕ∞) = analyticOrderAt (completedGN N) z)
    (hcl₂ : ∀ z ∈ t₂, lineReflect z ∈ t₂)
    (hρ₁ : ∀ w ∈ t₁, ‖w - a‖ ≤ r₀) (hρ₂ : ∀ w ∈ t₂, ‖w - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hh' : AnalyticOnNhd ℂ h' (ball a R)) (hh0' : ∀ z ∈ ball a R, h' z ≠ 0)
    (hfact₁ : ∀ z ∈ ball a R, xi z = (∏ w ∈ t₁, (z - w) ^ m₁ w) * h z)
    (hfact₂ : ∀ z ∈ ball a R, completedGN N z = (∏ w ∈ t₂, (z - w) ^ m₂ w) * h' z)
    (hdom : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖xi z - completedGN N z‖ < ‖completedGN N z‖)
    (hL : ∑ z ∈ t₁.filter (fun z => z.re = 1 / 2), m₁ z
        ≡ ∑ z ∈ t₂.filter (fun z => z.re = 1 / 2), m₂ z [MOD 2 ^ (k + 1)])
    (hfin : 2 ^ k ∣ ∑ z ∈ t₂.filter (fun z => 1 / 2 < z.re), m₂ z) :
    2 ^ k ∣ ∑ z ∈ t₁.filter (fun z => 1 / 2 < z.re), m₁ z := by
  have hparity := anneal_window_parity_transport_of_domination k h0 hrR hm₁ hcl₁ hstrip hm₂ hcl₂
    hρ₁ hρ₂ hh hh0 hh' hh0' hfact₁ hfact₂ hdom hL
  exact Nat.modEq_zero_iff_dvd.mp (hparity.trans (Nat.modEq_zero_iff_dvd.mpr hfin))

end RHTower

namespace RHTower

open Metric

/-- **Window-parity transport under relative control.** Relative `η < 1` closeness
between ξ and the completed finite carrier proves the count transport used by
ANNEAL, so the right-half window counts agree mod `2^k`; the same certificate
also gives U0 principal-log control of the correction ratio on the charts. -/
theorem anneal_window_parity_transport_of_relative_close {N : ℕ} (k : ℕ)
    {t₁ t₂ : Finset ℂ} {m₁ m₂ : ℂ → ℕ} {h h' : ℂ → ℂ} {a : ℂ} {r₀ R η : ℝ}
    (h0 : 0 ≤ r₀) (hrR : r₀ < R) (hη : η < 1)
    (hm₁ : ∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z)
    (hcl₁ : ∀ z ∈ t₁, lineReflect z ∈ t₁)
    (hstrip : ∀ z ∈ t₂, 0 < z.re ∧ z.re < 1)
    (hm₂ : ∀ z ∈ t₂, (m₂ z : ℕ∞) = analyticOrderAt (completedGN N) z)
    (hcl₂ : ∀ z ∈ t₂, lineReflect z ∈ t₂)
    (hρ₁ : ∀ w ∈ t₁, ‖w - a‖ ≤ r₀) (hρ₂ : ∀ w ∈ t₂, ‖w - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hh' : AnalyticOnNhd ℂ h' (ball a R)) (hh0' : ∀ z ∈ ball a R, h' z ≠ 0)
    (hfact₁ : ∀ z ∈ ball a R, xi z = (∏ w ∈ t₁, (z - w) ^ m₁ w) * h z)
    (hfact₂ : ∀ z ∈ ball a R, completedGN N z = (∏ w ∈ t₂, (z - w) ^ m₂ w) * h' z)
    (hG0 : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, completedGN N z ≠ 0)
    (hrel : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖(xi z - completedGN N z) / completedGN N z‖ ≤ η)
    (hL : ∑ z ∈ t₁.filter (fun z => z.re = 1 / 2), m₁ z
        ≡ ∑ z ∈ t₂.filter (fun z => z.re = 1 / 2), m₂ z [MOD 2 ^ (k + 1)]) :
    (∑ z ∈ t₁.filter (fun z => 1 / 2 < z.re), m₁ z
      ≡ ∑ z ∈ t₂.filter (fun z => 1 / 2 < z.re), m₂ z [MOD 2 ^ k]) ∧
      ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
        ‖Complex.log (xi z / completedGN N z)‖ ≤
          (1 - η)⁻¹ * ‖(xi z - completedGN N z) / completedGN N z‖ := by
  obtain ⟨hDeq, hlog⟩ :=
    enclosed_count_eq_of_relative_close t₂ t₁ id m₂ id m₁ h0 hrR hη hρ₂ hρ₁
      hh' hh0' hh hh0 hfact₂ hfact₁ hG0 hrel
  have hparity := anneal_window_parity_transport k hm₁ hcl₁ hstrip hm₂ hcl₂
    (hDeq ▸ Nat.ModEq.refl _) hL
  exact ⟨hparity, hlog⟩

/-- **Finite-side rung under relative control.** Relative `η < 1` closeness between ξ
and the completed finite carrier on the annulus charts proves the count transport
used by ANNEAL, so the finite-side rung still transfers to ξ; the same certificate
also gives U0 principal-log control of the correction ratio on the charts. -/
theorem xi_rung_of_finite_side_of_relative_close {N : ℕ} (k : ℕ)
    {t₁ t₂ : Finset ℂ} {m₁ m₂ : ℂ → ℕ} {h h' : ℂ → ℂ} {a : ℂ} {r₀ R η : ℝ}
    (h0 : 0 ≤ r₀) (hrR : r₀ < R) (hη : η < 1)
    (hm₁ : ∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z)
    (hcl₁ : ∀ z ∈ t₁, lineReflect z ∈ t₁)
    (hstrip : ∀ z ∈ t₂, 0 < z.re ∧ z.re < 1)
    (hm₂ : ∀ z ∈ t₂, (m₂ z : ℕ∞) = analyticOrderAt (completedGN N) z)
    (hcl₂ : ∀ z ∈ t₂, lineReflect z ∈ t₂)
    (hρ₁ : ∀ w ∈ t₁, ‖w - a‖ ≤ r₀) (hρ₂ : ∀ w ∈ t₂, ‖w - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hh' : AnalyticOnNhd ℂ h' (ball a R)) (hh0' : ∀ z ∈ ball a R, h' z ≠ 0)
    (hfact₁ : ∀ z ∈ ball a R, xi z = (∏ w ∈ t₁, (z - w) ^ m₁ w) * h z)
    (hfact₂ : ∀ z ∈ ball a R, completedGN N z = (∏ w ∈ t₂, (z - w) ^ m₂ w) * h' z)
    (hG0 : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, completedGN N z ≠ 0)
    (hrel : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖(xi z - completedGN N z) / completedGN N z‖ ≤ η)
    (hL : ∑ z ∈ t₁.filter (fun z => z.re = 1 / 2), m₁ z
        ≡ ∑ z ∈ t₂.filter (fun z => z.re = 1 / 2), m₂ z [MOD 2 ^ (k + 1)])
    (hfin : 2 ^ k ∣ ∑ z ∈ t₂.filter (fun z => 1 / 2 < z.re), m₂ z) :
    (2 ^ k ∣ ∑ z ∈ t₁.filter (fun z => 1 / 2 < z.re), m₁ z) ∧
      ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
        ‖Complex.log (xi z / completedGN N z)‖ ≤
          (1 - η)⁻¹ * ‖(xi z - completedGN N z) / completedGN N z‖ := by
  obtain ⟨hparity, hlog⟩ :=
    anneal_window_parity_transport_of_relative_close k h0 hrR hη hm₁ hcl₁ hstrip hm₂ hcl₂
      hρ₁ hρ₂ hh hh0 hh' hh0' hfact₁ hfact₂ hG0 hrel hL
  exact ⟨Nat.modEq_zero_iff_dvd.mp (hparity.trans (Nat.modEq_zero_iff_dvd.mpr hfin)), hlog⟩

end RHTower

namespace RHTower

open Complex Metric

/-- **Window-parity transport under relative control with raw finite-carrier
nonvanishing.** On charts contained in the positive strip and away from `1`,
nonvanishing of `gN` gives nonvanishing of `completedGN`, so the relative ANNEAL
window-parity transport consumes the finite carrier's natural nonzero check. -/
theorem anneal_window_parity_transport_of_relative_close_gN_nonzero {N : ℕ} (k : ℕ)
    {t₁ t₂ : Finset ℂ} {m₁ m₂ : ℂ → ℕ} {h h' : ℂ → ℂ} {a : ℂ} {r₀ R η : ℝ}
    (h0 : 0 ≤ r₀) (hrR : r₀ < R) (hη : η < 1)
    (hchartStrip : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, 0 < z.re ∧ z ≠ 1)
    (hm₁ : ∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z)
    (hcl₁ : ∀ z ∈ t₁, lineReflect z ∈ t₁)
    (hstrip : ∀ z ∈ t₂, 0 < z.re ∧ z.re < 1)
    (hm₂ : ∀ z ∈ t₂, (m₂ z : ℕ∞) = analyticOrderAt (completedGN N) z)
    (hcl₂ : ∀ z ∈ t₂, lineReflect z ∈ t₂)
    (hρ₁ : ∀ w ∈ t₁, ‖w - a‖ ≤ r₀) (hρ₂ : ∀ w ∈ t₂, ‖w - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hh' : AnalyticOnNhd ℂ h' (ball a R)) (hh0' : ∀ z ∈ ball a R, h' z ≠ 0)
    (hfact₁ : ∀ z ∈ ball a R, xi z = (∏ w ∈ t₁, (z - w) ^ m₁ w) * h z)
    (hfact₂ : ∀ z ∈ ball a R, completedGN N z = (∏ w ∈ t₂, (z - w) ^ m₂ w) * h' z)
    (hgN0 : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, gN N z ≠ 0)
    (hrel : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖(xi z - completedGN N z) / completedGN N z‖ ≤ η)
    (hL : ∑ z ∈ t₁.filter (fun z => z.re = 1 / 2), m₁ z
        ≡ ∑ z ∈ t₂.filter (fun z => z.re = 1 / 2), m₂ z [MOD 2 ^ (k + 1)]) :
    (∑ z ∈ t₁.filter (fun z => 1 / 2 < z.re), m₁ z
      ≡ ∑ z ∈ t₂.filter (fun z => 1 / 2 < z.re), m₂ z [MOD 2 ^ k]) ∧
      ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
        ‖Complex.log (xi z / completedGN N z)‖ ≤
          (1 - η)⁻¹ * ‖(xi z - completedGN N z) / completedGN N z‖ := by
  have hG0 : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, completedGN N z ≠ 0 := by
    intro z hz
    obtain ⟨hσ, hz1⟩ := hchartStrip z hz
    exact completedGN_ne_zero_of_gN_ne_zero hσ hz1 (hgN0 z hz)
  exact anneal_window_parity_transport_of_relative_close k h0 hrR hη hm₁ hcl₁ hstrip hm₂ hcl₂
    hρ₁ hρ₂ hh hh0 hh' hh0' hfact₁ hfact₂ hG0 hrel hL

/-- **Finite-side rung under relative control with completed-carrier nonvanishing
supplied by the raw finite carrier.**  On charts contained in the positive strip and
away from `1`, nonvanishing of `gN` gives nonvanishing of `completedGN`; the relative
ANNEAL rung transfer can therefore consume raw finite-carrier nonvanishing data. -/
theorem xi_rung_of_finite_side_of_relative_close_gN_nonzero {N : ℕ} (k : ℕ)
    {t₁ t₂ : Finset ℂ} {m₁ m₂ : ℂ → ℕ} {h h' : ℂ → ℂ} {a : ℂ} {r₀ R η : ℝ}
    (h0 : 0 ≤ r₀) (hrR : r₀ < R) (hη : η < 1)
    (hchartStrip : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, 0 < z.re ∧ z ≠ 1)
    (hm₁ : ∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z)
    (hcl₁ : ∀ z ∈ t₁, lineReflect z ∈ t₁)
    (hstrip : ∀ z ∈ t₂, 0 < z.re ∧ z.re < 1)
    (hm₂ : ∀ z ∈ t₂, (m₂ z : ℕ∞) = analyticOrderAt (completedGN N) z)
    (hcl₂ : ∀ z ∈ t₂, lineReflect z ∈ t₂)
    (hρ₁ : ∀ w ∈ t₁, ‖w - a‖ ≤ r₀) (hρ₂ : ∀ w ∈ t₂, ‖w - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hh' : AnalyticOnNhd ℂ h' (ball a R)) (hh0' : ∀ z ∈ ball a R, h' z ≠ 0)
    (hfact₁ : ∀ z ∈ ball a R, xi z = (∏ w ∈ t₁, (z - w) ^ m₁ w) * h z)
    (hfact₂ : ∀ z ∈ ball a R, completedGN N z = (∏ w ∈ t₂, (z - w) ^ m₂ w) * h' z)
    (hgN0 : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, gN N z ≠ 0)
    (hrel : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖(xi z - completedGN N z) / completedGN N z‖ ≤ η)
    (hL : ∑ z ∈ t₁.filter (fun z => z.re = 1 / 2), m₁ z
        ≡ ∑ z ∈ t₂.filter (fun z => z.re = 1 / 2), m₂ z [MOD 2 ^ (k + 1)])
    (hfin : 2 ^ k ∣ ∑ z ∈ t₂.filter (fun z => 1 / 2 < z.re), m₂ z) :
    (2 ^ k ∣ ∑ z ∈ t₁.filter (fun z => 1 / 2 < z.re), m₁ z) ∧
      ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
        ‖Complex.log (xi z / completedGN N z)‖ ≤
          (1 - η)⁻¹ * ‖(xi z - completedGN N z) / completedGN N z‖ := by
  obtain ⟨hparity, hlog⟩ :=
    anneal_window_parity_transport_of_relative_close_gN_nonzero k h0 hrR hη hchartStrip
      hm₁ hcl₁ hstrip hm₂ hcl₂ hρ₁ hρ₂ hh hh0 hh' hh0' hfact₁ hfact₂ hgN0 hrel hL
  exact ⟨Nat.modEq_zero_iff_dvd.mp (hparity.trans (Nat.modEq_zero_iff_dvd.mpr hfin)), hlog⟩

/-- **Finite-side rung under relative control with LOW-floor nonvanishing.**
A nonnegative `CarrierFloorOn` certificate supplies the finite-carrier nonvanishing
needed by the relative ANNEAL rung transfer. -/
theorem xi_rung_of_finite_side_of_relative_close_carrierFloorOn {N : ℕ} (k : ℕ)
    {t₁ t₂ : Finset ℂ} {m₁ m₂ : ℂ → ℕ} {h h' : ℂ → ℂ} {a : ℂ}
    {r₀ R η ε : ℝ}
    (h0 : 0 ≤ r₀) (hrR : r₀ < R) (hη : η < 1) (hε : 0 ≤ ε)
    (hF : CarrierFloorOn (chartRA a r₀ R ∪ chartLA a r₀ R) N ε)
    (hchartStrip : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, 0 < z.re ∧ z ≠ 1)
    (hm₁ : ∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z)
    (hcl₁ : ∀ z ∈ t₁, lineReflect z ∈ t₁)
    (hstrip : ∀ z ∈ t₂, 0 < z.re ∧ z.re < 1)
    (hm₂ : ∀ z ∈ t₂, (m₂ z : ℕ∞) = analyticOrderAt (completedGN N) z)
    (hcl₂ : ∀ z ∈ t₂, lineReflect z ∈ t₂)
    (hρ₁ : ∀ w ∈ t₁, ‖w - a‖ ≤ r₀) (hρ₂ : ∀ w ∈ t₂, ‖w - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hh' : AnalyticOnNhd ℂ h' (ball a R)) (hh0' : ∀ z ∈ ball a R, h' z ≠ 0)
    (hfact₁ : ∀ z ∈ ball a R, xi z = (∏ w ∈ t₁, (z - w) ^ m₁ w) * h z)
    (hfact₂ : ∀ z ∈ ball a R, completedGN N z = (∏ w ∈ t₂, (z - w) ^ m₂ w) * h' z)
    (hrel : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖(xi z - completedGN N z) / completedGN N z‖ ≤ η)
    (hL : ∑ z ∈ t₁.filter (fun z => z.re = 1 / 2), m₁ z
        ≡ ∑ z ∈ t₂.filter (fun z => z.re = 1 / 2), m₂ z [MOD 2 ^ (k + 1)])
    (hfin : 2 ^ k ∣ ∑ z ∈ t₂.filter (fun z => 1 / 2 < z.re), m₂ z) :
    (2 ^ k ∣ ∑ z ∈ t₁.filter (fun z => 1 / 2 < z.re), m₁ z) ∧
      ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
        ‖Complex.log (xi z / completedGN N z)‖ ≤
          (1 - η)⁻¹ * ‖(xi z - completedGN N z) / completedGN N z‖ := by
  have hG0 : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, completedGN N z ≠ 0 := by
    intro z hz
    obtain ⟨hσ, hz1⟩ := hchartStrip z hz
    exact completedGN_ne_zero_of_carrierFloorOn hε hF hz hσ hz1
  exact xi_rung_of_finite_side_of_relative_close k h0 hrR hη hm₁ hcl₁ hstrip hm₂ hcl₂
    hρ₁ hρ₂ hh hh0 hh' hh0' hfact₁ hfact₂ hG0 hrel hL hfin

end RHTower

namespace RHTower

open Complex

/-- **Relative ANNEAL deck transport with raw finite-carrier nonvanishing.**
Relative `η < 1` control between `xi` and `completedGN` transports the level-`2^k`
deck reading and gives the U0 principal-log bound; nonvanishing of `completedGN` on
the charts is derived from the raw finite carrier `gN`. -/
theorem anneal_deck_transport_of_relative_close_gN_nonzero {N : ℕ}
    {F₁ F₂ G₁ G₂ : ℂ → ℂ} {a : ℂ} {R η : ℝ} (k : ℕ)
    (hR : 0 < R) (hη : η < 1)
    (hchartStrip : ∀ z ∈ chartR a R ∪ chartL a R, 0 < z.re ∧ z ≠ 1)
    (hF₁ : AnalyticOnNhd ℂ F₁ (chartR a R)) (hF₂ : AnalyticOnNhd ℂ F₂ (chartL a R))
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartR a R)) (hG₂ : AnalyticOnNhd ℂ G₂ (chartL a R))
    (hpF₁ : ∀ z ∈ chartR a R, F₁ z ^ (2 : ℕ) ^ k = xi z)
    (hpF₂ : ∀ z ∈ chartL a R, F₂ z ^ (2 : ℕ) ^ k = xi z)
    (hpG₁ : ∀ z ∈ chartR a R, G₁ z ^ (2 : ℕ) ^ k = completedGN N z)
    (hpG₂ : ∀ z ∈ chartL a R, G₂ z ^ (2 : ℕ) ^ k = completedGN N z)
    (hgN0 : ∀ z ∈ chartR a R ∪ chartL a R, gN N z ≠ 0)
    (hrel : ∀ z ∈ chartR a R ∪ chartL a R,
      ‖(xi z - completedGN N z) / completedGN N z‖ ≤ η) :
    deckClass F₁ F₂ (a + ((R / 2 : ℝ) : ℂ) * I) (a - ((R / 2 : ℝ) : ℂ) * I) =
        deckClass G₁ G₂ (a + ((R / 2 : ℝ) : ℂ) * I) (a - ((R / 2 : ℝ) : ℂ) * I) ∧
      ∀ z ∈ chartR a R ∪ chartL a R,
        ‖Complex.log (xi z / completedGN N z)‖ ≤
          (1 - η)⁻¹ * ‖(xi z - completedGN N z) / completedGN N z‖ := by
  have hG0 : ∀ z ∈ chartR a R ∪ chartL a R, completedGN N z ≠ 0 := by
    intro z hz
    obtain ⟨hσ, hz1⟩ := hchartStrip z hz
    exact completedGN_ne_zero_of_gN_ne_zero hσ hz1 (hgN0 z hz)
  exact seam_transport_of_relative_close hR (pow_pos two_pos k) hη (xi_analyticOnNhd _)
    hF₁ hF₂ hG₁ hG₂ hpF₁ hpF₂ hpG₁ hpG₂ hG0 hrel

/-- **Relative ANNEAL deck transport with LOW-floor nonvanishing.**
A nonnegative `CarrierFloorOn` certificate supplies the finite-carrier
nonvanishing needed by the relative deck transport, while preserving the
deck-class equality and U0 principal-log control conclusions. -/
theorem anneal_deck_transport_of_relative_close_carrierFloorOn {N : ℕ}
    {F₁ F₂ G₁ G₂ : ℂ → ℂ} {a : ℂ} {R η ε : ℝ} (k : ℕ)
    (hR : 0 < R) (hη : η < 1) (hε : 0 ≤ ε)
    (hF : CarrierFloorOn (chartR a R ∪ chartL a R) N ε)
    (hchartStrip : ∀ z ∈ chartR a R ∪ chartL a R, 0 < z.re ∧ z ≠ 1)
    (hF₁ : AnalyticOnNhd ℂ F₁ (chartR a R)) (hF₂ : AnalyticOnNhd ℂ F₂ (chartL a R))
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartR a R)) (hG₂ : AnalyticOnNhd ℂ G₂ (chartL a R))
    (hpF₁ : ∀ z ∈ chartR a R, F₁ z ^ (2 : ℕ) ^ k = xi z)
    (hpF₂ : ∀ z ∈ chartL a R, F₂ z ^ (2 : ℕ) ^ k = xi z)
    (hpG₁ : ∀ z ∈ chartR a R, G₁ z ^ (2 : ℕ) ^ k = completedGN N z)
    (hpG₂ : ∀ z ∈ chartL a R, G₂ z ^ (2 : ℕ) ^ k = completedGN N z)
    (hrel : ∀ z ∈ chartR a R ∪ chartL a R,
      ‖(xi z - completedGN N z) / completedGN N z‖ ≤ η) :
    deckClass F₁ F₂ (a + ((R / 2 : ℝ) : ℂ) * I) (a - ((R / 2 : ℝ) : ℂ) * I) =
        deckClass G₁ G₂ (a + ((R / 2 : ℝ) : ℂ) * I) (a - ((R / 2 : ℝ) : ℂ) * I) ∧
      ∀ z ∈ chartR a R ∪ chartL a R,
        ‖Complex.log (xi z / completedGN N z)‖ ≤
          (1 - η)⁻¹ * ‖(xi z - completedGN N z) / completedGN N z‖ := by
  have hgN0 : ∀ z ∈ chartR a R ∪ chartL a R, gN N z ≠ 0 :=
    gN_ne_zero_of_carrierFloorOn hε hF
  exact anneal_deck_transport_of_relative_close_gN_nonzero k hR hη hchartStrip
    hF₁ hF₂ hG₁ hG₂ hpF₁ hpF₂ hpG₁ hpG₂ hgN0 hrel

end RHTower

namespace RHTower

open Complex

/-- **Relative ANNEAL seam L-transport with raw finite-carrier nonvanishing.**
Relative `η < 1` control at the two on-line seam basepoints supplies the strict
pointwise domination used by the k = 1 sign dictionary, and the same data gives U0
principal-log bounds at both basepoints. -/
theorem anneal_seam_L_transport_of_relative_close_gN_nonzero {N : ℕ}
    {g₁ g₂ G₁ G₂ : ℂ → ℂ} {U : Set ℂ} {η : ℝ}
    (hη : η < 1)
    (hU : IsOpen U) (hUc : IsPreconnected U)
    (hUstrip : ∀ z ∈ U, 0 < z.re ∧ z.re < 1)
    (hg₁ : AnalyticOnNhd ℂ g₁ U) (hg₂ : AnalyticOnNhd ℂ g₂ (lineReflect ⁻¹' U))
    (hG₁ : AnalyticOnNhd ℂ G₁ U) (hG₂ : AnalyticOnNhd ℂ G₂ (lineReflect ⁻¹' U))
    (hp₁ : ∀ s ∈ U, g₁ s ^ (2 : ℕ) = xi s) (hp₂ : ∀ s ∈ lineReflect ⁻¹' U, g₂ s ^ (2 : ℕ) = xi s)
    (hP₁ : ∀ s ∈ U, G₁ s ^ (2 : ℕ) = completedGN N s)
    (hP₂ : ∀ s ∈ lineReflect ⁻¹' U, G₂ s ^ (2 : ℕ) = completedGN N s)
    {pP pM : ℂ} (hpP : pP ∈ U) (hpM : pM ∈ U)
    (hPline : pP.re = 1 / 2) (hMline : pM.re = 1 / 2)
    (hgN0P : gN N pP ≠ 0) (hgN0M : gN N pM ≠ 0)
    (hrelP : ‖(xi pP - completedGN N pP) / completedGN N pP‖ ≤ η)
    (hrelM : ‖(xi pM - completedGN N pM) / completedGN N pM‖ ≤ η) :
    deckClass g₁ g₂ pP pM = deckClass G₁ G₂ pP pM ∧
      ‖Complex.log (xi pP / completedGN N pP)‖ ≤
        (1 - η)⁻¹ * ‖(xi pP - completedGN N pP) / completedGN N pP‖ ∧
      ‖Complex.log (xi pM / completedGN N pM)‖ ≤
        (1 - η)⁻¹ * ‖(xi pM - completedGN N pM) / completedGN N pM‖ := by
  have hPσ : 0 < pP.re := by rw [hPline]; norm_num
  have hMσ : 0 < pM.re := by rw [hMline]; norm_num
  have hPne1 : pP ≠ 1 := by
    intro hp
    rw [hp] at hPline
    norm_num at hPline
  have hMne1 : pM ≠ 1 := by
    intro hp
    rw [hp] at hMline
    norm_num at hMline
  have hG0P : completedGN N pP ≠ 0 := completedGN_ne_zero_of_gN_ne_zero hPσ hPne1 hgN0P
  have hG0M : completedGN N pM ≠ 0 := completedGN_ne_zero_of_gN_ne_zero hMσ hMne1 hgN0M
  have hdomP : ‖xi pP - completedGN N pP‖ < ‖completedGN N pP‖ := by
    have hpos : 0 < ‖completedGN N pP‖ := norm_pos_iff.mpr hG0P
    have hdiv : ‖xi pP - completedGN N pP‖ / ‖completedGN N pP‖ ≤ η := by
      simpa [norm_div] using hrelP
    have hmul : ‖xi pP - completedGN N pP‖ ≤ η * ‖completedGN N pP‖ :=
      (div_le_iff₀ hpos).mp hdiv
    exact lt_of_le_of_lt hmul (by simpa using mul_lt_mul_of_pos_right hη hpos)
  have hdomM : ‖xi pM - completedGN N pM‖ < ‖completedGN N pM‖ := by
    have hpos : 0 < ‖completedGN N pM‖ := norm_pos_iff.mpr hG0M
    have hdiv : ‖xi pM - completedGN N pM‖ / ‖completedGN N pM‖ ≤ η := by
      simpa [norm_div] using hrelM
    have hmul : ‖xi pM - completedGN N pM‖ ≤ η * ‖completedGN N pM‖ :=
      (div_le_iff₀ hpos).mp hdiv
    exact lt_of_le_of_lt hmul (by simpa using mul_lt_mul_of_pos_right hη hpos)
  have hdeck := anneal_seam_L_transport hU hUc hUstrip hg₁ hg₂ hG₁ hG₂ hp₁ hp₂ hP₁ hP₂
    hpP hpM hPline hMline hdomP hdomM
  exact ⟨hdeck, ratio_log_norm_le_of_relative_close hη hG0P hrelP,
    ratio_log_norm_le_of_relative_close hη hG0M hrelM⟩

/-- **Relative ANNEAL seam L-transport with LOW-floor nonvanishing.**
A nonnegative `CarrierFloorOn` certificate supplies the two pointwise finite-carrier
nonvanishing inputs needed by the relative seam dictionary, while preserving deck
transport and both U0 principal-log bounds. -/
theorem anneal_seam_L_transport_of_relative_close_carrierFloorOn {N : ℕ}
    {g₁ g₂ G₁ G₂ : ℂ → ℂ} {U : Set ℂ} {η ε : ℝ}
    (hη : η < 1) (hε : 0 ≤ ε) (hF : CarrierFloorOn U N ε)
    (hU : IsOpen U) (hUc : IsPreconnected U)
    (hUstrip : ∀ z ∈ U, 0 < z.re ∧ z.re < 1)
    (hg₁ : AnalyticOnNhd ℂ g₁ U) (hg₂ : AnalyticOnNhd ℂ g₂ (lineReflect ⁻¹' U))
    (hG₁ : AnalyticOnNhd ℂ G₁ U) (hG₂ : AnalyticOnNhd ℂ G₂ (lineReflect ⁻¹' U))
    (hp₁ : ∀ s ∈ U, g₁ s ^ (2 : ℕ) = xi s) (hp₂ : ∀ s ∈ lineReflect ⁻¹' U, g₂ s ^ (2 : ℕ) = xi s)
    (hP₁ : ∀ s ∈ U, G₁ s ^ (2 : ℕ) = completedGN N s)
    (hP₂ : ∀ s ∈ lineReflect ⁻¹' U, G₂ s ^ (2 : ℕ) = completedGN N s)
    {pP pM : ℂ} (hpP : pP ∈ U) (hpM : pM ∈ U)
    (hPline : pP.re = 1 / 2) (hMline : pM.re = 1 / 2)
    (hrelP : ‖(xi pP - completedGN N pP) / completedGN N pP‖ ≤ η)
    (hrelM : ‖(xi pM - completedGN N pM) / completedGN N pM‖ ≤ η) :
    deckClass g₁ g₂ pP pM = deckClass G₁ G₂ pP pM ∧
      ‖Complex.log (xi pP / completedGN N pP)‖ ≤
        (1 - η)⁻¹ * ‖(xi pP - completedGN N pP) / completedGN N pP‖ ∧
      ‖Complex.log (xi pM / completedGN N pM)‖ ≤
        (1 - η)⁻¹ * ‖(xi pM - completedGN N pM) / completedGN N pM‖ := by
  have hgN0P : gN N pP ≠ 0 := gN_ne_zero_of_carrierFloorOn hε hF pP hpP
  have hgN0M : gN N pM ≠ 0 := gN_ne_zero_of_carrierFloorOn hε hF pM hpM
  exact anneal_seam_L_transport_of_relative_close_gN_nonzero hη hU hUc hUstrip
    hg₁ hg₂ hG₁ hG₂ hp₁ hp₂ hP₁ hP₂ hpP hpM hPline hMline
    hgN0P hgN0M hrelP hrelM

end RHTower
