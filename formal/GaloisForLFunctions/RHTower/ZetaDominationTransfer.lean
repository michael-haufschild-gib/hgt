/-
The base rung from the named carrier interfaces.

The completed domination premise of the carrier weld is exactly what the two named
analytic interfaces of the anneal reduction supply: on any strip subset, the (AFE)
accuracy `‖ζ − gN‖ ≤ ε` and the (LOW) floor `ε < ‖gN‖` combine to
`‖ξ − completedGN‖ < ‖completedGN‖` pointwise.  Instantiated on the two slit charts of an
isolating annulus at a hypothetical off-line zero, the weld machinery takes over: the
member splits unconditionally, the chain of exact jumps and one dominated move reaches ξ,
and the anchored event ledger follows from one parity.  The base rung of the ladder is
thereby reduced to the two named interfaces on the charts of one isolating annulus per
off-line zero plus the evenness of the completed carrier's hole-zero count there — and in
raw form, to the pointwise relative closeness of ζ to the carrier on those charts plus
the same parity.
-/
import GaloisForLFunctions.RHTower.CarrierSplit
import GaloisForLFunctions.RHTower.ZetaCarrier

namespace RHTower

open Complex Metric

/-- **The base rung from raw ζ-carrier closeness and one parity.**  If every hypothetical
off-line ξ-zero admits an isolating annulus inside the strip on whose two slit charts ζ
stays relatively close to the carrier — `‖ζ − gN‖ < ‖gN‖` pointwise — and every split of
the completed member has even count, then every off-line vanishing order is even. -/
theorem rhLadder_one_of_zeta_carrier_close
    (hsupply : ∀ ρ ∈ rightHalf, xi ρ = 0 → ∃ (r₀ R : ℝ) (N : ℕ),
      0 ≤ r₀ ∧ r₀ < R ∧
      (∀ z ∈ ball ρ R, 0 < z.re ∧ z.re < 1) ∧
      (∀ z ∈ ball ρ R, z ≠ ρ → xi z ≠ 0) ∧
      (∀ z ∈ chartRA ρ r₀ R ∪ chartLA ρ r₀ R,
        ‖riemannZeta z - gN N z‖ < ‖gN N z‖) ∧
      (∀ (zs : List ℂ) (u : ℂ → ℂ),
        (∀ w ∈ zs, ‖w - ρ‖ ≤ r₀) →
        AnalyticOnNhd ℂ u (ball ρ R) → (∀ z ∈ ball ρ R, u z ≠ 0) →
        (∀ z ∈ ball ρ R, completedGN N z = ((zs.map (fun w => z - w)).prod) * u z) →
        Even zs.length)) :
    RHLadder 1 := by
  refine rhLadder_one_of_isolating_anchoredEventLedgers ?_
  intro ρ hρ h0
  obtain ⟨r₀, R, N, h1, h2, hstrip, hiso, hclose, hpar⟩ := hsupply ρ hρ h0
  refine ⟨r₀, R, h1, h2, hiso, ?_⟩
  refine anchoredEventLedger_of_domination h1 h2 (F := completedGN N) ?_ ?_ hpar
  · intro z hz
    exact (completedGN_analyticOnNhd_strip N) z (hstrip z hz)
  · intro z hz
    have hzball : z ∈ ball ρ R := by
      rw [charts_union_eq_annulus ρ h1] at hz
      exact hz.1
    obtain ⟨h0r, h1r⟩ := hstrip z hzball
    have hz0 : z ≠ 0 := by
      rintro rfl
      simp at h0r
    have hz1 : z ≠ 1 := by
      rintro rfl
      simp at h1r
    exact (completed_domination_iff hz0 hz1 (Gammaℝ_ne_zero_of_re_pos h0r)).mpr
      (hclose z hz)

/-- **The base rung from (AFE) + (LOW) + one parity.**  If every hypothetical off-line
ξ-zero admits an isolating annulus inside the strip whose two slit charts carry the named
(AFE) accuracy and (LOW) floor interfaces of the anneal reduction, and every split of the
completed member has even count, then every off-line vanishing order is even.  The
analytic burden of the base rung is exactly the two named interfaces localized to the
charts of one isolating annulus per off-line zero, plus the parity of the carrier's
hole-zero count — the member's own mod-2 deck cocycle. -/
theorem rhLadder_one_of_interfaces_parity
    (hsupply : ∀ ρ ∈ rightHalf, xi ρ = 0 → ∃ (r₀ R : ℝ) (N : ℕ) (ε : ℝ),
      0 ≤ r₀ ∧ r₀ < R ∧
      (∀ z ∈ ball ρ R, 0 < z.re ∧ z.re < 1) ∧
      (∀ z ∈ ball ρ R, z ≠ ρ → xi z ≠ 0) ∧
      AFEAccurateOn (chartRA ρ r₀ R ∪ chartLA ρ r₀ R) N ε ∧
      CarrierFloorOn (chartRA ρ r₀ R ∪ chartLA ρ r₀ R) N ε ∧
      (∀ (zs : List ℂ) (u : ℂ → ℂ),
        (∀ w ∈ zs, ‖w - ρ‖ ≤ r₀) →
        AnalyticOnNhd ℂ u (ball ρ R) → (∀ z ∈ ball ρ R, u z ≠ 0) →
        (∀ z ∈ ball ρ R, completedGN N z = ((zs.map (fun w => z - w)).prod) * u z) →
        Even zs.length)) :
    RHLadder 1 := by
  refine rhLadder_one_of_zeta_carrier_close ?_
  intro ρ hρ h0
  obtain ⟨r₀, R, N, ε, h1, h2, hstrip, hiso, hA, hF, hpar⟩ := hsupply ρ hρ h0
  exact ⟨r₀, R, N, h1, h2, hstrip, hiso,
    raw_domination_of_interfaces hA hF, hpar⟩

end RHTower
