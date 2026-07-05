/-
# The EM-pinned window: counting certificates from finite carrier data

The relative pinning lemma turns a one-simple-zero reference plus relative
closeness `η < 1` on the annulus charts into on-line location of every counted
zero.  The seam certificate surface produces exactly that closeness for
`f = ξ`, `g = completedGN N` from finite data: Euler–Maclaurin remainder
bounds, finite `emCarrier`/`gN` closeness, and a doubled LOW floor.  Welding
the two:

* `xi_window_pinned_of_emCarrier_close_half_floor` — EM finite data + doubled
  LOW floor + a one-simple-zero factorization of the completed finite carrier
  at a critical-line center + a hole-supported factorization of ξ pin every
  ξ-zero of the window ball onto the critical line, with the U0 principal-log
  control of the correction ratio on the charts.
* `riemannHypothesis_of_emCarrier_pinned_windows` — RH from a family of such
  certificates, one around each hypothetical right-half ξ-zero.

Against the sign-table endpoints, the ξ sign-alternation data is replaced by
the carrier's local zero structure: the certificate burden is finite-carrier
arithmetic (floor, closeness, one simple zero at the center) plus the ξ
factorization, and the on-line location comes from counting, not from sign
changes.
-/
import GaloisForLFunctions.RHTower.SeamCongruence

namespace RHTower

open Complex Metric

/-- **The EM-pinned window.**  EM finite data and a doubled LOW floor on the
annulus charts, a one-simple-zero factorization `completedGN N = (z − ρ₀)·h`
of the completed finite carrier at a critical-line center, and a
hole-supported factorization of ξ force every ξ-zero of the window ball onto
the critical line, and control the principal log of the correction ratio on
the charts by the U0 bound. -/
theorem xi_window_pinned_of_emCarrier_close_half_floor
    {N M : ℕ} (hM : 1 ≤ M) {ε₁ δ : ℝ} (hεδ : 0 ≤ ε₁ + δ)
    {ρ₀ : ℂ} {r₀ R : ℝ} (h0 : 0 ≤ r₀) (hrR : r₀ < R) (hρ₀re : ρ₀.re = 1 / 2)
    (hstrip : ∀ z ∈ chartRA ρ₀ r₀ R ∪ chartLA ρ₀ r₀ R, 0 < z.re ∧ z ≠ 1)
    (hE : ∀ z ∈ chartRA ρ₀ r₀ R ∪ chartLA ρ₀ r₀ R,
      ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁)
    (hclose : ∀ z ∈ chartRA ρ₀ r₀ R ∪ chartLA ρ₀ r₀ R,
      ‖emCarrier M z - gN N z‖ ≤ δ)
    (hF : CarrierFloorOn (chartRA ρ₀ r₀ R ∪ chartLA ρ₀ r₀ R) N (2 * (ε₁ + δ)))
    {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h (ball ρ₀ R)) (hh0 : ∀ z ∈ ball ρ₀ R, h z ≠ 0)
    (hfactg : ∀ z ∈ ball ρ₀ R, completedGN N z = (z - ρ₀) * h z)
    (t : Finset ℂ) (m' : ℂ → ℕ) {h' : ℂ → ℂ}
    (hh' : AnalyticOnNhd ℂ h' (ball ρ₀ R)) (hh0' : ∀ z ∈ ball ρ₀ R, h' z ≠ 0)
    (hρ' : ∀ w ∈ t, ‖w - ρ₀‖ ≤ r₀)
    (hfactf : ∀ z ∈ ball ρ₀ R, xi z = (∏ w ∈ t, (z - w) ^ m' w) * h' z) :
    (∀ p ∈ ball ρ₀ R, xi p = 0 → p.re = 1 / 2) ∧
      ∀ z ∈ chartRA ρ₀ r₀ R ∪ chartLA ρ₀ r₀ R,
        ‖Complex.log (xi z / completedGN N z)‖ ≤
          (1 - (1 / 2 : ℝ))⁻¹ * ‖(xi z - completedGN N z) / completedGN N z‖ := by
  have hfloor_nonneg : 0 ≤ 2 * (ε₁ + δ) := mul_nonneg (by norm_num) hεδ
  have hη : (1 / 2 : ℝ) < 1 := by norm_num
  have hsym : ∀ z ∈ ball ρ₀ R,
      xi (1 - (starRingEnd ℂ) z) = (starRingEnd ℂ) (xi z) := by
    intro z _
    rw [xi_one_sub]
    exact xi_conj z
  have hg0 : ∀ z ∈ chartRA ρ₀ r₀ R ∪ chartLA ρ₀ r₀ R, completedGN N z ≠ 0 := by
    intro z hz
    obtain ⟨hσ, hz1⟩ := hstrip z hz
    exact completedGN_ne_zero_of_gN_ne_zero hσ hz1
      (gN_ne_zero_of_carrierFloorOn hfloor_nonneg hF z hz)
  have hrel : ∀ z ∈ chartRA ρ₀ r₀ R ∪ chartLA ρ₀ r₀ R,
      ‖(xi z - completedGN N z) / completedGN N z‖ ≤ (1 / 2 : ℝ) :=
    completed_relative_error_of_emCarrier_close_half_floor hM hεδ hstrip hE hclose hF
  obtain ⟨hpin, hlog⟩ := pinned_zero_re_eq_half_of_relative_close t id m' h0 hrR hη
    hρ₀re hsym hh hh0 hh' hh0' hfactg hρ' hfactf hg0 hrel
  refine ⟨?_, hlog⟩
  intro p hp hxi
  have hfa := hfactf p hp
  rw [hxi] at hfa
  have hprod : (∏ w ∈ t, (p - w) ^ m' w) = 0 := by
    rcases mul_eq_zero.mp hfa.symm with hc | hc
    · exact hc
    · exact absurd hc (hh0' p hp)
  obtain ⟨w, hwmem, hwzero⟩ := Finset.prod_eq_zero_iff.mp hprod
  have hm0 : m' w ≠ 0 := by
    intro hzero'
    rw [hzero', pow_zero] at hwzero
    exact one_ne_zero hwzero
  have hpw : p = w := sub_eq_zero.mp ((pow_eq_zero_iff hm0).mp hwzero)
  rw [hpw]
  exact hpin w hwmem hm0

/-- **The EM-pinned RH gate.**  RH from a family of EM-pinned window
certificates, one around each hypothetical right-half ξ-zero: finite EM
remainder and closeness bounds, a doubled LOW floor, the carrier's
one-simple-zero factorization at a critical-line center, and a hole-supported
ξ factorization.  The counting substitute pins each window's ξ-zeros to the
line; no sign table enters. -/
theorem riemannHypothesis_of_emCarrier_pinned_windows
    (hwin : ∀ ρ ∈ rightHalf, xi ρ = 0 →
      ∃ (N M : ℕ) (ε₁ δ : ℝ) (t : Finset ℂ) (m' : ℂ → ℕ) (h h' : ℂ → ℂ)
        (ρ₀ : ℂ) (r₀ R : ℝ),
        1 ≤ M ∧ 0 ≤ ε₁ + δ ∧ 0 ≤ r₀ ∧ r₀ < R ∧ ρ ∈ ball ρ₀ R ∧ ρ₀.re = 1 / 2
        ∧ (∀ z ∈ chartRA ρ₀ r₀ R ∪ chartLA ρ₀ r₀ R, 0 < z.re ∧ z ≠ 1)
        ∧ (∀ z ∈ chartRA ρ₀ r₀ R ∪ chartLA ρ₀ r₀ R,
            ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁)
        ∧ (∀ z ∈ chartRA ρ₀ r₀ R ∪ chartLA ρ₀ r₀ R, ‖emCarrier M z - gN N z‖ ≤ δ)
        ∧ CarrierFloorOn (chartRA ρ₀ r₀ R ∪ chartLA ρ₀ r₀ R) N (2 * (ε₁ + δ))
        ∧ AnalyticOnNhd ℂ h (ball ρ₀ R) ∧ (∀ z ∈ ball ρ₀ R, h z ≠ 0)
        ∧ (∀ z ∈ ball ρ₀ R, completedGN N z = (z - ρ₀) * h z)
        ∧ AnalyticOnNhd ℂ h' (ball ρ₀ R) ∧ (∀ z ∈ ball ρ₀ R, h' z ≠ 0)
        ∧ (∀ w ∈ t, ‖w - ρ₀‖ ≤ r₀)
        ∧ (∀ z ∈ ball ρ₀ R, xi z = (∏ w ∈ t, (z - w) ^ m' w) * h' z)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_local_online_windows
  intro ρ hρ hzero
  obtain ⟨N, M, ε₁, δ, t, m', h, h', ρ₀, r₀, R, hM, hεδ, h0, hrR, hρball, hρ₀re,
    hstrip, hE, hclose, hF, hh, hh0, hfactg, hh', hh0', hρ', hfactf⟩ :=
    hwin ρ hρ hzero
  exact ⟨ρ₀, R, hρball,
    (xi_window_pinned_of_emCarrier_close_half_floor hM hεδ h0 hrR hρ₀re hstrip hE
      hclose hF hh hh0 hfactg t m' hh' hh0' hρ' hfactf).1⟩

end RHTower
