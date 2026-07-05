/-
The center-anchored scalar certificate: window pinning and the RH gate from data at a KNOWN point.

All previous pinning gates take their circle data at the carrier zero — a point whose exact
position no finite computation can produce.  Here the certificate is anchored entirely at a known
line center `c`: two signs bracket an on-line carrier zero `ρ'` (intermediate value theorem), a
Jensen quotient below two makes it the unique, simple zero of the window (divisor count), the
minimum-modulus engine converts one anchor and one sup into the derivative floor `κ` and the
boundary-circle carrier floors, and the difference-quotient sup transfer converts one completed
sup into the slope deviation `Δ`.  Every hypothesis is a scalar inequality, a 1D sup over a
c-centered circle or region, or a sign — data a finite verification can in principle certify —
and the conclusion pins every ξ-zero of a ball around the bracketed zero to the critical line.
-/
import GaloisForLFunctions.RHTower.JensenCount

open Complex Metric

namespace RHTower

/-- **Pinned window from center-anchored scalar data.**  Signs, a Jensen pair, engine scalars,
an archimedean floor on the bracket segment, EM budgets, and the `ηC`-budget inequality — all
anchored at the known center `c` — produce an on-line point `ρ'` within `rz` of `c` such that
every ξ-zero of `ball ρ' R` lies on the critical line. -/
theorem xi_window_pinned_of_center_scalars
    {N M : ℕ} (hM : 1 ≤ M) {ε₁ δ : ℝ} (hεδ : 0 ≤ ε₁ + δ)
    {c : ℂ} {t₁ t₂ rz r₀ R P rJ RJ m_J M_J m_e M_h M_G a₀ κ : ℝ}
    (ht₁ : 0 < t₁) (h12 : t₁ ≤ t₂) (hrz0 : 0 < rz)
    (h0 : 0 < r₀) (hrR : r₀ < R) (hRP : R ≤ P)
    (hPrz : P + rz ≤ RJ) (hRrzJ : R + rz < rJ) (hrJR : rJ < RJ)
    (hstrip : ∀ z ∈ closedBall c RJ, 0 < z.re ∧ z.re < 1)
    (hbr : ∀ τ ∈ Set.Icc t₁ t₂,
      ((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I ∈ closedBall c rz)
    (hsign : (completedGN N (((1 / 2 : ℝ) : ℂ) + (t₁ : ℂ) * I)).re
      * (completedGN N (((1 / 2 : ℝ) : ℂ) + (t₂ : ℂ) * I)).re ≤ 0)
    (hmJ0 : 0 < m_J) (hmJ : m_J ≤ ‖gN N c‖) (hMJ : 1 ≤ M_J)
    (hbound : ∀ z ∈ sphere c RJ, ‖gN N z‖ ≤ M_J)
    (hjensen : Real.log (M_J / ‖gN N c‖) / Real.log (RJ / rJ) < 2)
    (hme0 : 0 < m_e) (hme : m_e ≤ m_J / rz)
    (hMh : M_J / (rJ - rz) ≤ M_h) (hmeMh : m_e < M_h)
    (ha₀ : ∀ z : ℂ, z.re = 1 / 2 → z ∈ closedBall c rz → a₀ ≤ ‖archFactor z‖)
    (hκ0 : 0 < κ)
    (hκle : κ ≤ a₀ * (m_e * Real.exp (-(2 * Real.log (M_h / m_e) * rz / (rJ - rz)))))
    (hMG : ∀ z ∈ closedBall c RJ, ‖completedGN N z‖ ≤ M_G)
    (hηC : R * (2 * (M_G / P)) / (P * κ)
      + (1 + R * (2 * (M_G / P)) / (P * κ)) / 2 < 1)
    (hE : ∀ z ∈ closedBall c RJ, ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁)
    (hclose : ∀ z ∈ closedBall c RJ, ‖emCarrier M z - gN N z‖ ≤ δ)
    (hfl : 2 * (ε₁ + δ) < r₀ * (m_e * Real.exp
      (-(2 * Real.log (M_h / m_e) * (R + rz) / (rJ - (R + rz)))))) :
    ∃ ρ' : ℂ, ρ'.re = 1 / 2 ∧ ρ' ∈ closedBall c rz ∧
      ∀ p ∈ ball ρ' R, xi p = 0 → p.re = 1 / 2 := by
  have hR0 : 0 < R := lt_trans h0 hrR
  have hP : 0 < P := lt_of_lt_of_le hR0 hRP
  have hrzJ : rz < rJ := lt_of_le_of_lt (by linarith) hRrzJ
  have hfc : gN N c ≠ 0 := by
    intro h
    rw [h, norm_zero] at hmJ
    linarith
  obtain ⟨ρ', hρre, hρrz, hczero, hgzero, hdan, hd0, hdfact, hdderiv⟩ :=
    carrier_one_zero_package_of_signs_jensen ht₁ h12 hrz0 hrzJ.le hrJR hstrip hbr
      hsign hfc hMJ hbound hjensen
  have hρrJ : ρ' ∈ closedBall c rJ := (closedBall_subset_closedBall hrzJ.le) hρrz
  have hρdist : ‖ρ' - c‖ ≤ rz := by
    rw [← dist_eq_norm]
    exact mem_closedBall.mp hρrz
  -- containments
  have hsphPsub : closedBall ρ' P ⊆ closedBall c RJ := by
    intro z hz
    rw [mem_closedBall]
    calc dist z c ≤ dist z ρ' + dist ρ' c := dist_triangle z ρ' c
      _ ≤ P + rz := add_le_add (mem_closedBall.mp hz) (mem_closedBall.mp hρrz)
      _ ≤ RJ := hPrz
  have hballP : ∀ z ∈ closedBall ρ' P, 0 < z.re ∧ z.re < 1 :=
    fun z hz => hstrip z (hsphPsub hz)
  -- carrier analyticity and ball sup on the Jensen region
  have hgan : ∀ z ∈ closedBall c RJ, AnalyticAt ℂ (gN N) z := by
    intro z hz
    exact gN_analyticAt (Gammaℝ_ne_zero_of_re_pos (by
      rw [Complex.sub_re, Complex.one_re]
      linarith [(hstrip z hz).2]))
  have hRJ0 : 0 < RJ := lt_trans (lt_of_le_of_lt hrz0.le hrzJ) hrJR
  have hgRJ : ∀ z ∈ closedBall c RJ, ‖gN N z‖ ≤ M_J :=
    norm_le_on_closedBall_of_sphere hRJ0 hgan hbound
  -- difference-quotient sup on the engine ball
  have hsupJ : ∀ z ∈ sphere c rJ, ‖gN N z‖ ≤ M_J := by
    intro z hz
    apply hgRJ
    rw [mem_closedBall]
    rw [mem_sphere] at hz
    rw [hz]
    exact hrJR.le
  have hganJ : ∀ z ∈ closedBall c rJ, AnalyticAt ℂ (gN N) z := fun z hz =>
    hgan z ((closedBall_subset_closedBall hrJR.le) hz)
  have hhsupCB := dslope_norm_le_of_boundary_sup hrz0.le hρdist hrzJ hganJ
    hgzero hsupJ
  have hhsup : ∀ z ∈ ball c rJ, ‖dslope (gN N) ρ' z‖ ≤ M_h := fun z hz =>
    le_trans (hhsupCB z (ball_subset_closedBall hz)) hMh
  -- difference-quotient anchor at the center
  have hcne : c ≠ ρ' := by
    intro h
    rw [h] at hfc
    exact hfc hgzero
  have hcd0 : (0 : ℝ) < ‖c - ρ'‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hcne)
  have hcdrz : ‖c - ρ'‖ ≤ rz := by
    rw [norm_sub_rev]
    exact hρdist
  have hanc : m_e ≤ ‖dslope (gN N) ρ' c‖ := by
    rw [dslope_of_ne _ hcne, slope_def_field, hgzero, sub_zero, norm_div]
    refine le_trans hme ?_
    exact div_le_div₀ (norm_nonneg _) hmJ hcd0 hcdrz
  -- derivative floor at the zero
  have h0re : 0 < ρ'.re := by
    rw [hρre]
    norm_num
  have hκderiv : κ ≤ ‖deriv (completedGN N) ρ'‖ := by
    refine le_trans hκle ?_
    exact deriv_completedGN_floor_of_anchor hrz0.le hrzJ hρrz h0re hdan hd0
      hdfact hhsup hme0 hmeMh hanc (ha₀ ρ' hρre hρrz)
  -- slope deviation from the completed sup
  have hcan : ∀ z ∈ closedBall ρ' P, AnalyticAt ℂ (completedGN N) z := fun z hz =>
    completedGN_analyticAt (hballP z hz).1 (hballP z hz).2
  have hMGsph : ∀ z ∈ sphere ρ' P, ‖completedGN N z‖ ≤ M_G := fun z hz =>
    hMG z (hsphPsub (sphere_subset_closedBall hz))
  have hΔgate := slope_deviation_of_boundary_sup hP hcan hczero hMGsph
  -- EM data on the certificate circles
  have hcircsub : sphere ρ' r₀ ∪ sphere ρ' R ⊆ closedBall ρ' P := by
    intro z hz
    rcases hz with h | h
    · rw [mem_sphere] at h
      rw [mem_closedBall, h]
      linarith
    · rw [mem_sphere] at h
      rw [mem_closedBall, h]
      exact hRP
  have hEr : ∀ z ∈ sphere ρ' r₀ ∪ sphere ρ' R,
      ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁ := fun z hz =>
    hE z (hsphPsub (hcircsub hz))
  have hcloser : ∀ z ∈ sphere ρ' r₀ ∪ sphere ρ' R,
      ‖emCarrier M z - gN N z‖ ≤ δ := fun z hz =>
    hclose z (hsphPsub (hcircsub hz))
  -- circle floors from the minimum-modulus engine
  have hSsub : sphere ρ' r₀ ∪ sphere ρ' R ⊆ closedBall c (R + rz) := by
    intro z hz
    have hzρ : ‖z - ρ'‖ ≤ R := by
      rcases hz with h | h
      · rw [mem_sphere] at h
        rw [← dist_eq_norm, h]
        exact hrR.le
      · rw [mem_sphere] at h
        rw [← dist_eq_norm, h]
    rw [mem_closedBall]
    calc dist z c ≤ dist z ρ' + dist ρ' c := dist_triangle z ρ' c
      _ ≤ R + rz := by
          rw [dist_eq_norm]
          exact add_le_add hzρ (mem_closedBall.mp hρrz)
  have hdcirc : ∀ z ∈ sphere ρ' r₀ ∪ sphere ρ' R, r₀ ≤ ‖z - ρ'‖ := by
    intro z hz
    rcases hz with h | h
    · rw [mem_sphere] at h
      rw [← dist_eq_norm, h]
    · rw [mem_sphere] at h
      rw [← dist_eq_norm, h]
      exact hrR.le
  have hFcirc : CarrierFloorOn (sphere ρ' r₀ ∪ sphere ρ' R) N (2 * (ε₁ + δ)) :=
    carrierFloorOn_of_single_zero_anchor (by positivity) hRrzJ hdan hd0 hdfact
      hhsup hme0 hmeMh hanc hSsub hdcirc hfl
  -- the slope gate
  refine ⟨ρ', hρre, hρrz, ?_⟩
  exact (xi_window_pinned_of_slope_circles hM hεδ h0 hrR hRP hκ0 hηC hρre
    hballP hczero hκderiv hΔgate hEr hcloser hFcirc).1

/-- **The center-scalar RH gate.**  RH follows if every hypothetical right-half ξ-zero admits a
certificate consisting entirely of data anchored at a KNOWN critical-line center: two signs, a
Jensen anchor/sup pair, engine and budget scalars, an archimedean floor on the bracket segment,
and EM sups over one known region — with the window radius `R` absorbing both the zero bracket
`rz` and the distance `R'` from the center to the hypothetical zero. -/
theorem riemannHypothesis_of_center_scalar_windows
    (hwin : ∀ ρ ∈ rightHalf, xi ρ = 0 →
      ∃ (N M : ℕ) (ε₁ δ : ℝ) (c : ℂ)
        (t₁ t₂ rz r₀ R R' P rJ RJ m_J M_J m_e M_h M_G a₀ κ : ℝ),
        1 ≤ M ∧ 0 ≤ ε₁ + δ ∧
        0 < t₁ ∧ t₁ ≤ t₂ ∧ 0 < rz ∧
        0 < r₀ ∧ r₀ < R ∧ R ≤ P ∧
        P + rz ≤ RJ ∧ R + rz < rJ ∧ rJ < RJ ∧
        ρ ∈ ball c R' ∧ R' + rz ≤ R ∧
        (∀ z ∈ closedBall c RJ, 0 < z.re ∧ z.re < 1) ∧
        (∀ τ ∈ Set.Icc t₁ t₂,
          ((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I ∈ closedBall c rz) ∧
        (completedGN N (((1 / 2 : ℝ) : ℂ) + (t₁ : ℂ) * I)).re
          * (completedGN N (((1 / 2 : ℝ) : ℂ) + (t₂ : ℂ) * I)).re ≤ 0 ∧
        0 < m_J ∧ m_J ≤ ‖gN N c‖ ∧ 1 ≤ M_J ∧
        (∀ z ∈ sphere c RJ, ‖gN N z‖ ≤ M_J) ∧
        Real.log (M_J / ‖gN N c‖) / Real.log (RJ / rJ) < 2 ∧
        0 < m_e ∧ m_e ≤ m_J / rz ∧
        M_J / (rJ - rz) ≤ M_h ∧ m_e < M_h ∧
        (∀ z : ℂ, z.re = 1 / 2 → z ∈ closedBall c rz →
          a₀ ≤ ‖archFactor z‖) ∧
        0 < κ ∧
        κ ≤ a₀ * (m_e * Real.exp (-(2 * Real.log (M_h / m_e) * rz / (rJ - rz)))) ∧
        (∀ z ∈ closedBall c RJ, ‖completedGN N z‖ ≤ M_G) ∧
        R * (2 * (M_G / P)) / (P * κ)
          + (1 + R * (2 * (M_G / P)) / (P * κ)) / 2 < 1 ∧
        (∀ z ∈ closedBall c RJ, ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁) ∧
        (∀ z ∈ closedBall c RJ, ‖emCarrier M z - gN N z‖ ≤ δ) ∧
        2 * (ε₁ + δ) < r₀ * (m_e * Real.exp
          (-(2 * Real.log (M_h / m_e) * (R + rz) / (rJ - (R + rz)))))) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_local_online_windows
  intro ρ hρ hzero
  obtain ⟨N, M, ε₁, δ, c, t₁, t₂, rz, r₀, R, R', P, rJ, RJ, m_J, M_J, m_e,
    M_h, M_G, a₀, κ, hM, hεδ, ht₁, h12, hrz0, h0, hrR, hRP, hPrz, hRrzJ,
    hrJR, hρR', hR'rz, hstrip, hbr, hsign, hmJ0, hmJ, hMJ, hbound, hjensen,
    hme0, hme, hMh, hmeMh, ha₀, hκ0, hκle, hMG, hηC, hE, hclose, hfl⟩ :=
    hwin ρ hρ hzero
  obtain ⟨ρ', hρre, hρrz, hpin⟩ := xi_window_pinned_of_center_scalars hM hεδ
    ht₁ h12 hrz0 h0 hrR hRP hPrz hRrzJ hrJR hstrip hbr hsign hmJ0 hmJ hMJ
    hbound hjensen hme0 hme hMh hmeMh ha₀ hκ0 hκle hMG hηC hE hclose hfl
  refine ⟨ρ', R, ?_, hpin⟩
  rw [mem_ball]
  calc dist ρ ρ' ≤ dist ρ c + dist c ρ' := dist_triangle ρ c ρ'
    _ < R' + rz := by
        apply add_lt_add_of_lt_of_le (mem_ball.mp hρR')
        rw [dist_comm]
        exact mem_closedBall.mp hρrz
    _ ≤ R := hR'rz

end RHTower
