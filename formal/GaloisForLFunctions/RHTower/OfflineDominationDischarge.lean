/-
Concrete discharge of the finite-carrier domination interfaces.

The Euler--Maclaurin remainder and finite-carrier closeness already construct the AFE side of
the comparison.  The pointwise Dirichlet or Gamma-ratio inequalities construct the LOW side.
Composing the two removes both named Prop interfaces from the raw and completed domination
statements.
-/
import GaloisForLFunctions.RHTower.EMCarrier
import GaloisForLFunctions.RHTower.GNCarrierBridge
import GaloisForLFunctions.RHTower.RouteBOfflineDomination

namespace RHTower

/-- **Raw EM domination from a concrete pointwise Dirichlet inequality.**  The AFE and carrier-floor
Prop interfaces are both constructed internally. -/
theorem raw_domination_of_emCarrier_close_pointwise_domination
    {S : Set ℂ} {N M : ℕ} {ε₁ δ : ℝ}
    (hE : ∀ z ∈ S, ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁)
    (hclose : ∀ z ∈ S, ‖emCarrier M z - gN N z‖ ≤ δ)
    (hdom : ∀ z ∈ S,
      ‖zetaChi z * dirichletPoly N (1 - z)‖ + (ε₁ + δ) < ‖dirichletPoly N z‖) :
    ∀ z ∈ S,
      ‖z‖ * (M : ℝ) ^ (-z.re) / z.re + ‖emCarrier M z - gN N z‖ < ‖gN N z‖ :=
  raw_domination_of_emCarrier_close_floor hE hclose
    (carrierFloorOn_of_pointwise_domination N hdom)

/-- **Completed-carrier domination from a concrete pointwise Dirichlet inequality.**  On a strip
set, EM error plus finite-carrier closeness is strictly dominated by the carrier using no named
analytic interface. -/
theorem completed_domination_of_emCarrier_close_pointwise_domination
    {S : Set ℂ} {N M : ℕ} (hM : 1 ≤ M) {ε₁ δ : ℝ}
    (hstrip : ∀ z ∈ S, 0 < z.re ∧ z.re < 1)
    (hE : ∀ z ∈ S, ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁)
    (hclose : ∀ z ∈ S, ‖emCarrier M z - gN N z‖ ≤ δ)
    (hdom : ∀ z ∈ S,
      ‖zetaChi z * dirichletPoly N (1 - z)‖ + (ε₁ + δ) < ‖dirichletPoly N z‖) :
    ∀ z ∈ S, ‖xi z - completedGN N z‖ < ‖completedGN N z‖ :=
  completed_domination_of_emCarrier_close_floor hM hstrip hE hclose
    (carrierFloorOn_of_pointwise_domination N hdom)

/-- **Raw EM domination from direct Dirichlet-part floor data.**  The LOW Prop is eliminated in
favor of its two quantitative inequalities. -/
theorem raw_domination_of_emCarrier_close_dirichlet_floor
    {S : Set ℂ} {N M : ℕ} {t₀ ε₁ δ : ℝ}
    (hE : ∀ z ∈ S, ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁)
    (hclose : ∀ z ∈ S, ‖emCarrier M z - gN N z‖ ≤ δ)
    (hfloor : ∀ z ∈ S, t₀ < ‖dirichletPoly N z‖)
    (hrefl : ∀ z ∈ S,
      ‖zetaChi z * dirichletPoly N (1 - z)‖ ≤ t₀ - (ε₁ + δ)) :
    ∀ z ∈ S,
      ‖z‖ * (M : ℝ) ^ (-z.re) / z.re + ‖emCarrier M z - gN N z‖ < ‖gN N z‖ :=
  raw_domination_of_emCarrier_close_floor hE hclose
    (carrierFloorOn_of_dirichletPoly_floor N hfloor hrefl)

/-- **Completed domination from direct Dirichlet-part floor data.**  The named AFE and LOW
interfaces do not occur in the conclusion's hypotheses. -/
theorem completed_domination_of_emCarrier_close_dirichlet_floor
    {S : Set ℂ} {N M : ℕ} (hM : 1 ≤ M) {t₀ ε₁ δ : ℝ}
    (hstrip : ∀ z ∈ S, 0 < z.re ∧ z.re < 1)
    (hE : ∀ z ∈ S, ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁)
    (hclose : ∀ z ∈ S, ‖emCarrier M z - gN N z‖ ≤ δ)
    (hfloor : ∀ z ∈ S, t₀ < ‖dirichletPoly N z‖)
    (hrefl : ∀ z ∈ S,
      ‖zetaChi z * dirichletPoly N (1 - z)‖ ≤ t₀ - (ε₁ + δ)) :
    ∀ z ∈ S, ‖xi z - completedGN N z‖ < ‖completedGN N z‖ :=
  completed_domination_of_emCarrier_close_floor hM hstrip hE hclose
    (carrierFloorOn_of_dirichletPoly_floor N hfloor hrefl)

/-- **Raw EM domination from the native `dpoly2` floor.**  The two-dimensional Dirichlet carrier
data feed the domination theorem without a `CarrierFloorOn` premise. -/
theorem raw_domination_of_emCarrier_close_dpoly2_floor
    {S : Set ℂ} {N M : ℕ} {t₀ ε₁ δ : ℝ}
    (hE : ∀ z ∈ S, ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁)
    (hclose : ∀ z ∈ S, ‖emCarrier M z - gN N z‖ ≤ δ)
    (hfloor : ∀ z ∈ S,
      t₀ < ‖dpoly2 (fun _ => 1) (Finset.Icc 1 N) z‖)
    (hrefl : ∀ z ∈ S,
      ‖zetaChi z * dpoly2 (fun _ => 1) (Finset.Icc 1 N) (1 - z)‖ ≤
        t₀ - (ε₁ + δ)) :
    ∀ z ∈ S,
      ‖z‖ * (M : ℝ) ^ (-z.re) / z.re + ‖emCarrier M z - gN N z‖ < ‖gN N z‖ :=
  raw_domination_of_emCarrier_close_floor hE hclose
    (carrierFloorOn_of_dpoly2_floor N hfloor hrefl)

/-- **Completed domination from the native `dpoly2` floor.**  This is the direct finite-carrier
input shape used by the off-line chart floor machinery. -/
theorem completed_domination_of_emCarrier_close_dpoly2_floor
    {S : Set ℂ} {N M : ℕ} (hM : 1 ≤ M) {t₀ ε₁ δ : ℝ}
    (hstrip : ∀ z ∈ S, 0 < z.re ∧ z.re < 1)
    (hE : ∀ z ∈ S, ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁)
    (hclose : ∀ z ∈ S, ‖emCarrier M z - gN N z‖ ≤ δ)
    (hfloor : ∀ z ∈ S,
      t₀ < ‖dpoly2 (fun _ => 1) (Finset.Icc 1 N) z‖)
    (hrefl : ∀ z ∈ S,
      ‖zetaChi z * dpoly2 (fun _ => 1) (Finset.Icc 1 N) (1 - z)‖ ≤
        t₀ - (ε₁ + δ)) :
    ∀ z ∈ S, ‖xi z - completedGN N z‖ < ‖completedGN N z‖ :=
  completed_domination_of_emCarrier_close_floor hM hstrip hE hclose
    (carrierFloorOn_of_dpoly2_floor N hfloor hrefl)

/-- **Raw EM domination from the explicit Gamma-ratio inequality.**  The exact modulus formula for
`zetaChi` turns the displayed inequality directly into the carrier floor, so no LOW Prop remains. -/
theorem raw_domination_of_emCarrier_close_gamma_ratio
    {S : Set ℂ} {N M : ℕ} {ε₁ δ : ℝ}
    (hE : ∀ z ∈ S, ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁)
    (hclose : ∀ z ∈ S, ‖emCarrier M z - gN N z‖ ≤ δ)
    (hdom : ∀ z ∈ S,
      Real.pi ^ (z.re - 1 / 2) * ‖Complex.Gamma ((1 - z) / 2)‖ /
          ‖Complex.Gamma (z / 2)‖ * ‖dirichletPoly N (1 - z)‖ + (ε₁ + δ) <
        ‖dirichletPoly N z‖) :
    ∀ z ∈ S,
      ‖z‖ * (M : ℝ) ^ (-z.re) / z.re + ‖emCarrier M z - gN N z‖ < ‖gN N z‖ :=
  raw_domination_of_emCarrier_close_floor hE hclose
    (carrierFloorOn_of_gamma_ratio_domination N hdom)

/-- **Completed-carrier domination from the explicit Gamma-ratio inequality.**  This is the
interface-free off-line comparison: only concrete pointwise estimates and the strip domain remain. -/
theorem completed_domination_of_emCarrier_close_gamma_ratio
    {S : Set ℂ} {N M : ℕ} (hM : 1 ≤ M) {ε₁ δ : ℝ}
    (hstrip : ∀ z ∈ S, 0 < z.re ∧ z.re < 1)
    (hE : ∀ z ∈ S, ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁)
    (hclose : ∀ z ∈ S, ‖emCarrier M z - gN N z‖ ≤ δ)
    (hdom : ∀ z ∈ S,
      Real.pi ^ (z.re - 1 / 2) * ‖Complex.Gamma ((1 - z) / 2)‖ /
          ‖Complex.Gamma (z / 2)‖ * ‖dirichletPoly N (1 - z)‖ + (ε₁ + δ) <
        ‖dirichletPoly N z‖) :
    ∀ z ∈ S, ‖xi z - completedGN N z‖ < ‖completedGN N z‖ :=
  completed_domination_of_emCarrier_close_floor hM hstrip hE hclose
    (carrierFloorOn_of_gamma_ratio_domination N hdom)

/-! ### Interface-free deck and seam transports -/

/-- **ANNEAL deck transport from pointwise Dirichlet domination.**  Both the AFE and LOW interfaces
are built internally from concrete finite-data inequalities. -/
theorem anneal_deck_transport_of_emCarrier_close_pointwise_domination {N M : ℕ}
    {F₁ F₂ G₁ G₂ : ℂ → ℂ} {a : ℂ} {R ε₁ δ : ℝ}
    (k : ℕ) (hM : 1 ≤ M) (hR : 0 < R)
    (hstrip : ∀ z ∈ chartR a R ∪ chartL a R, 0 < z.re ∧ z.re < 1)
    (hE : ∀ z ∈ chartR a R ∪ chartL a R,
      ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁)
    (hclose : ∀ z ∈ chartR a R ∪ chartL a R,
      ‖emCarrier M z - gN N z‖ ≤ δ)
    (hdom : ∀ z ∈ chartR a R ∪ chartL a R,
      ‖zetaChi z * dirichletPoly N (1 - z)‖ + (ε₁ + δ) < ‖dirichletPoly N z‖)
    (hF₁ : AnalyticOnNhd ℂ F₁ (chartR a R)) (hF₂ : AnalyticOnNhd ℂ F₂ (chartL a R))
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartR a R)) (hG₂ : AnalyticOnNhd ℂ G₂ (chartL a R))
    (hpF₁ : ∀ z ∈ chartR a R, F₁ z ^ 2 ^ k = xi z)
    (hpF₂ : ∀ z ∈ chartL a R, F₂ z ^ 2 ^ k = xi z)
    (hpG₁ : ∀ z ∈ chartR a R, G₁ z ^ 2 ^ k = completedGN N z)
    (hpG₂ : ∀ z ∈ chartL a R, G₂ z ^ 2 ^ k = completedGN N z) :
    deckClass F₁ F₂ (a + ((R / 2 : ℝ) : ℂ) * Complex.I)
        (a - ((R / 2 : ℝ) : ℂ) * Complex.I) =
      deckClass G₁ G₂ (a + ((R / 2 : ℝ) : ℂ) * Complex.I)
        (a - ((R / 2 : ℝ) : ℂ) * Complex.I) :=
  anneal_deck_transport_of_emCarrier_close k hM hR hstrip hE hclose
    (carrierFloorOn_of_pointwise_domination N hdom)
    hF₁ hF₂ hG₁ hG₂ hpF₁ hpF₂ hpG₁ hpG₂

/-- **ANNEAL deck transport from the explicit Gamma-ratio inequality.** -/
theorem anneal_deck_transport_of_emCarrier_close_gamma_ratio {N M : ℕ}
    {F₁ F₂ G₁ G₂ : ℂ → ℂ} {a : ℂ} {R ε₁ δ : ℝ}
    (k : ℕ) (hM : 1 ≤ M) (hR : 0 < R)
    (hstrip : ∀ z ∈ chartR a R ∪ chartL a R, 0 < z.re ∧ z.re < 1)
    (hE : ∀ z ∈ chartR a R ∪ chartL a R,
      ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁)
    (hclose : ∀ z ∈ chartR a R ∪ chartL a R,
      ‖emCarrier M z - gN N z‖ ≤ δ)
    (hdom : ∀ z ∈ chartR a R ∪ chartL a R,
      Real.pi ^ (z.re - 1 / 2) * ‖Complex.Gamma ((1 - z) / 2)‖ /
          ‖Complex.Gamma (z / 2)‖ * ‖dirichletPoly N (1 - z)‖ + (ε₁ + δ) <
        ‖dirichletPoly N z‖)
    (hF₁ : AnalyticOnNhd ℂ F₁ (chartR a R)) (hF₂ : AnalyticOnNhd ℂ F₂ (chartL a R))
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartR a R)) (hG₂ : AnalyticOnNhd ℂ G₂ (chartL a R))
    (hpF₁ : ∀ z ∈ chartR a R, F₁ z ^ 2 ^ k = xi z)
    (hpF₂ : ∀ z ∈ chartL a R, F₂ z ^ 2 ^ k = xi z)
    (hpG₁ : ∀ z ∈ chartR a R, G₁ z ^ 2 ^ k = completedGN N z)
    (hpG₂ : ∀ z ∈ chartL a R, G₂ z ^ 2 ^ k = completedGN N z) :
    deckClass F₁ F₂ (a + ((R / 2 : ℝ) : ℂ) * Complex.I)
        (a - ((R / 2 : ℝ) : ℂ) * Complex.I) =
      deckClass G₁ G₂ (a + ((R / 2 : ℝ) : ℂ) * Complex.I)
        (a - ((R / 2 : ℝ) : ℂ) * Complex.I) :=
  anneal_deck_transport_of_emCarrier_close k hM hR hstrip hE hclose
    (carrierFloorOn_of_gamma_ratio_domination N hdom)
    hF₁ hF₂ hG₁ hG₂ hpF₁ hpF₂ hpG₁ hpG₂

/-- **Seam `L`-transport from pointwise Dirichlet domination.**  The finite-data inequalities
replace the carrier-floor interface. -/
theorem anneal_seam_L_transport_of_emCarrier_close_pointwise_domination {N M : ℕ}
    {g₁ g₂ G₁ G₂ : ℂ → ℂ} {U : Set ℂ} {ε₁ δ : ℝ}
    (hMpos : 1 ≤ M) (hU : IsOpen U) (hUc : IsPreconnected U)
    (hUstrip : ∀ z ∈ U, 0 < z.re ∧ z.re < 1)
    (hE : ∀ z ∈ U, ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁)
    (hclose : ∀ z ∈ U, ‖emCarrier M z - gN N z‖ ≤ δ)
    (hdom : ∀ z ∈ U,
      ‖zetaChi z * dirichletPoly N (1 - z)‖ + (ε₁ + δ) < ‖dirichletPoly N z‖)
    (hg₁ : AnalyticOnNhd ℂ g₁ U) (hg₂ : AnalyticOnNhd ℂ g₂ (lineReflect ⁻¹' U))
    (hG₁ : AnalyticOnNhd ℂ G₁ U) (hG₂ : AnalyticOnNhd ℂ G₂ (lineReflect ⁻¹' U))
    (hp₁ : ∀ s ∈ U, g₁ s ^ 2 = xi s)
    (hp₂ : ∀ s ∈ lineReflect ⁻¹' U, g₂ s ^ 2 = xi s)
    (hP₁ : ∀ s ∈ U, G₁ s ^ 2 = completedGN N s)
    (hP₂ : ∀ s ∈ lineReflect ⁻¹' U, G₂ s ^ 2 = completedGN N s)
    {pP pM : ℂ} (hpP : pP ∈ U) (hpM : pM ∈ U)
    (hPline : pP.re = 1 / 2) (hMline : pM.re = 1 / 2) :
    deckClass g₁ g₂ pP pM = deckClass G₁ G₂ pP pM :=
  anneal_seam_L_transport_of_emCarrier_close_floor hMpos hU hUc hUstrip hE hclose
    (carrierFloorOn_of_pointwise_domination N hdom)
    hg₁ hg₂ hG₁ hG₂ hp₁ hp₂ hP₁ hP₂ hpP hpM hPline hMline

/-- **Seam `L`-transport from the explicit Gamma-ratio inequality.** -/
theorem anneal_seam_L_transport_of_emCarrier_close_gamma_ratio {N M : ℕ}
    {g₁ g₂ G₁ G₂ : ℂ → ℂ} {U : Set ℂ} {ε₁ δ : ℝ}
    (hMpos : 1 ≤ M) (hU : IsOpen U) (hUc : IsPreconnected U)
    (hUstrip : ∀ z ∈ U, 0 < z.re ∧ z.re < 1)
    (hE : ∀ z ∈ U, ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁)
    (hclose : ∀ z ∈ U, ‖emCarrier M z - gN N z‖ ≤ δ)
    (hdom : ∀ z ∈ U,
      Real.pi ^ (z.re - 1 / 2) * ‖Complex.Gamma ((1 - z) / 2)‖ /
          ‖Complex.Gamma (z / 2)‖ * ‖dirichletPoly N (1 - z)‖ + (ε₁ + δ) <
        ‖dirichletPoly N z‖)
    (hg₁ : AnalyticOnNhd ℂ g₁ U) (hg₂ : AnalyticOnNhd ℂ g₂ (lineReflect ⁻¹' U))
    (hG₁ : AnalyticOnNhd ℂ G₁ U) (hG₂ : AnalyticOnNhd ℂ G₂ (lineReflect ⁻¹' U))
    (hp₁ : ∀ s ∈ U, g₁ s ^ 2 = xi s)
    (hp₂ : ∀ s ∈ lineReflect ⁻¹' U, g₂ s ^ 2 = xi s)
    (hP₁ : ∀ s ∈ U, G₁ s ^ 2 = completedGN N s)
    (hP₂ : ∀ s ∈ lineReflect ⁻¹' U, G₂ s ^ 2 = completedGN N s)
    {pP pM : ℂ} (hpP : pP ∈ U) (hpM : pM ∈ U)
    (hPline : pP.re = 1 / 2) (hMline : pM.re = 1 / 2) :
    deckClass g₁ g₂ pP pM = deckClass G₁ G₂ pP pM :=
  anneal_seam_L_transport_of_emCarrier_close_floor hMpos hU hUc hUstrip hE hclose
    (carrierFloorOn_of_gamma_ratio_domination N hdom)
    hg₁ hg₂ hG₁ hG₂ hp₁ hp₂ hP₁ hP₂ hpP hpM hPline hMline

/-- **Finite-side rung transport from pointwise Dirichlet domination.**  The carrier-floor Prop is
replaced by its concrete pointwise inequality. -/
theorem xi_rung_of_finite_side_of_emCarrier_close_pointwise_domination {N M : ℕ} (k : ℕ)
    {t₁ t₂ : Finset ℂ} {m₁ m₂ : ℂ → ℕ} {h h' : ℂ → ℂ}
    {a : ℂ} {r₀ R ε₁ δ : ℝ}
    (hMpos : 1 ≤ M) (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    (hchartStrip : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      0 < z.re ∧ z.re < 1)
    (hE : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁)
    (hclose : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖emCarrier M z - gN N z‖ ≤ δ)
    (hdom : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖zetaChi z * dirichletPoly N (1 - z)‖ + (ε₁ + δ) < ‖dirichletPoly N z‖)
    (hm₁ : ∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z)
    (hcl₁ : ∀ z ∈ t₁, lineReflect z ∈ t₁)
    (hstrip : ∀ z ∈ t₂, 0 < z.re ∧ z.re < 1)
    (hm₂ : ∀ z ∈ t₂, (m₂ z : ℕ∞) = analyticOrderAt (completedGN N) z)
    (hcl₂ : ∀ z ∈ t₂, lineReflect z ∈ t₂)
    (hρ₁ : ∀ w ∈ t₁, ‖w - a‖ ≤ r₀) (hρ₂ : ∀ w ∈ t₂, ‖w - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (Metric.ball a R)) (hh0 : ∀ z ∈ Metric.ball a R, h z ≠ 0)
    (hh' : AnalyticOnNhd ℂ h' (Metric.ball a R)) (hh0' : ∀ z ∈ Metric.ball a R, h' z ≠ 0)
    (hfact₁ : ∀ z ∈ Metric.ball a R, xi z = (∏ w ∈ t₁, (z - w) ^ m₁ w) * h z)
    (hfact₂ : ∀ z ∈ Metric.ball a R,
      completedGN N z = (∏ w ∈ t₂, (z - w) ^ m₂ w) * h' z)
    (hL : ∑ z ∈ t₁.filter (fun z => z.re = 1 / 2), m₁ z
        ≡ ∑ z ∈ t₂.filter (fun z => z.re = 1 / 2), m₂ z [MOD 2 ^ (k + 1)])
    (hfin : 2 ^ k ∣ ∑ z ∈ t₂.filter (fun z => 1 / 2 < z.re), m₂ z) :
    2 ^ k ∣ ∑ z ∈ t₁.filter (fun z => 1 / 2 < z.re), m₁ z :=
  xi_rung_of_finite_side_of_emCarrier_close_floor k hMpos h0 hrR hchartStrip hE hclose
    (carrierFloorOn_of_pointwise_domination N hdom)
    hm₁ hcl₁ hstrip hm₂ hcl₂ hρ₁ hρ₂ hh hh0 hh' hh0' hfact₁ hfact₂ hL hfin

/-- **Finite-side rung transport from the explicit Gamma-ratio inequality.** -/
theorem xi_rung_of_finite_side_of_emCarrier_close_gamma_ratio {N M : ℕ} (k : ℕ)
    {t₁ t₂ : Finset ℂ} {m₁ m₂ : ℂ → ℕ} {h h' : ℂ → ℂ}
    {a : ℂ} {r₀ R ε₁ δ : ℝ}
    (hMpos : 1 ≤ M) (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    (hchartStrip : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      0 < z.re ∧ z.re < 1)
    (hE : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁)
    (hclose : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      ‖emCarrier M z - gN N z‖ ≤ δ)
    (hdom : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
      Real.pi ^ (z.re - 1 / 2) * ‖Complex.Gamma ((1 - z) / 2)‖ /
          ‖Complex.Gamma (z / 2)‖ * ‖dirichletPoly N (1 - z)‖ + (ε₁ + δ) <
        ‖dirichletPoly N z‖)
    (hm₁ : ∀ z ∈ t₁, (m₁ z : ℕ∞) = analyticOrderAt xi z)
    (hcl₁ : ∀ z ∈ t₁, lineReflect z ∈ t₁)
    (hstrip : ∀ z ∈ t₂, 0 < z.re ∧ z.re < 1)
    (hm₂ : ∀ z ∈ t₂, (m₂ z : ℕ∞) = analyticOrderAt (completedGN N) z)
    (hcl₂ : ∀ z ∈ t₂, lineReflect z ∈ t₂)
    (hρ₁ : ∀ w ∈ t₁, ‖w - a‖ ≤ r₀) (hρ₂ : ∀ w ∈ t₂, ‖w - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (Metric.ball a R)) (hh0 : ∀ z ∈ Metric.ball a R, h z ≠ 0)
    (hh' : AnalyticOnNhd ℂ h' (Metric.ball a R)) (hh0' : ∀ z ∈ Metric.ball a R, h' z ≠ 0)
    (hfact₁ : ∀ z ∈ Metric.ball a R, xi z = (∏ w ∈ t₁, (z - w) ^ m₁ w) * h z)
    (hfact₂ : ∀ z ∈ Metric.ball a R,
      completedGN N z = (∏ w ∈ t₂, (z - w) ^ m₂ w) * h' z)
    (hL : ∑ z ∈ t₁.filter (fun z => z.re = 1 / 2), m₁ z
        ≡ ∑ z ∈ t₂.filter (fun z => z.re = 1 / 2), m₂ z [MOD 2 ^ (k + 1)])
    (hfin : 2 ^ k ∣ ∑ z ∈ t₂.filter (fun z => 1 / 2 < z.re), m₂ z) :
    2 ^ k ∣ ∑ z ∈ t₁.filter (fun z => 1 / 2 < z.re), m₁ z :=
  xi_rung_of_finite_side_of_emCarrier_close_floor k hMpos h0 hrR hchartStrip hE hclose
    (carrierFloorOn_of_gamma_ratio_domination N hdom)
    hm₁ hcl₁ hstrip hm₂ hcl₂ hρ₁ hρ₂ hh hh0 hh' hh0' hfact₁ hfact₂ hL hfin

end RHTower
