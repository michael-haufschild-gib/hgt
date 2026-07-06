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

namespace RHTower

/-- **Jensen quotient monotonicity under an anchor floor.**  If `m ≤ x`, then the
Jensen quotient with the unknown anchor `x` is no larger than the quotient using
the certified lower floor `m`, provided the radius denominator has positive log. -/
theorem jensen_quotient_lt_of_anchor_floor {M m x r R B : ℝ}
    (hM : 0 < M) (hm : 0 < m) (hmx : m ≤ x) (hratio : 1 < R / r)
    (hbudget : Real.log (M / m) / Real.log (R / r) < B) :
    Real.log (M / x) / Real.log (R / r) < B := by
  have hx : 0 < x := lt_of_lt_of_le hm hmx
  have hdiv : M / x ≤ M / m := div_le_div_of_nonneg_left hM.le hm hmx
  have hMx : 0 < M / x := div_pos hM hx
  have hlog : Real.log (M / x) ≤ Real.log (M / m) := Real.log_le_log hMx hdiv
  have hden : 0 < Real.log (R / r) := Real.log_pos hratio
  exact lt_of_le_of_lt (div_le_div_of_nonneg_right hlog hden.le) hbudget

/-- **ScalarCertificate Jensen budget from the certified `gN` anchor floor.**  The
actual center anchor `‖gN N c‖` no longer has to appear in the budget estimate:
it suffices to prove the stronger scalar inequality with the floor `m_J`. -/
theorem gN_jensen_budget_of_anchor_floor {N : ℕ} {c : ℂ} {m_J M_J rJ RJ : ℝ}
    (hmJ0 : 0 < m_J) (hmJ : m_J ≤ ‖gN N c‖) (hMJ : 1 ≤ M_J)
    (hratio : 1 < RJ / rJ)
    (hbudget : Real.log (M_J / m_J) / Real.log (RJ / rJ) < 2) :
    Real.log (M_J / ‖gN N c‖) / Real.log (RJ / rJ) < 2 :=
  jensen_quotient_lt_of_anchor_floor (lt_of_lt_of_le zero_lt_one hMJ) hmJ0 hmJ hratio hbudget

end RHTower

namespace RHTower

/-- **Center-floor scalar certificate with canonical minimum-modulus inputs.**  This is the
same pinned-window gate as `xi_window_pinned_of_center_scalars`, but the minimum-modulus scalars
are no longer independent data: the difference-quotient anchor and sup are fixed to the canonical
values `m_J / rz` and `M_J / (rJ - rz)`.  The Jensen estimate is also checked against the
certified floor `m_J`, not the unknown actual anchor `‖gN N c‖`. -/
theorem xi_window_pinned_of_center_floor_scalars
    {N M : ℕ} (hM : 1 ≤ M) {ε₁ δ : ℝ} (hεδ : 0 ≤ ε₁ + δ)
    {c : ℂ} {t₁ t₂ rz r₀ R P rJ RJ m_J M_J M_G a₀ κ : ℝ}
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
    (hjensen_floor : Real.log (M_J / m_J) / Real.log (RJ / rJ) < 2)
    (hengine : m_J / rz < M_J / (rJ - rz))
    (ha₀ : ∀ z : ℂ, z.re = 1 / 2 → z ∈ closedBall c rz → a₀ ≤ ‖archFactor z‖)
    (hκ0 : 0 < κ)
    (hκle : κ ≤ a₀ * ((m_J / rz) * Real.exp
      (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * rz / (rJ - rz)))))
    (hMG : ∀ z ∈ closedBall c RJ, ‖completedGN N z‖ ≤ M_G)
    (hηC : R * (2 * (M_G / P)) / (P * κ)
      + (1 + R * (2 * (M_G / P)) / (P * κ)) / 2 < 1)
    (hE : ∀ z ∈ closedBall c RJ, ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁)
    (hclose : ∀ z ∈ closedBall c RJ, ‖emCarrier M z - gN N z‖ ≤ δ)
    (hfl : 2 * (ε₁ + δ) < r₀ * ((m_J / rz) * Real.exp
      (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * (R + rz) /
        (rJ - (R + rz)))))) :
    ∃ ρ' : ℂ, ρ'.re = 1 / 2 ∧ ρ' ∈ closedBall c rz ∧
      ∀ p ∈ ball ρ' R, xi p = 0 → p.re = 1 / 2 := by
  have hR0 : 0 < R := lt_trans h0 hrR
  have hrzJ : rz < rJ := by linarith
  have hrJ0 : 0 < rJ := by linarith
  have hratio : 1 < RJ / rJ := (one_lt_div hrJ0).mpr hrJR
  have hjensen : Real.log (M_J / ‖gN N c‖) / Real.log (RJ / rJ) < 2 :=
    gN_jensen_budget_of_anchor_floor hmJ0 hmJ hMJ hratio hjensen_floor
  exact xi_window_pinned_of_center_scalars hM hεδ ht₁ h12 hrz0 h0 hrR hRP hPrz
    hRrzJ hrJR hstrip hbr hsign hmJ0 hmJ hMJ hbound hjensen
    (div_pos hmJ0 hrz0) le_rfl le_rfl hengine ha₀ hκ0 hκle hMG hηC hE hclose hfl

end RHTower

namespace RHTower

/-- **RH gate with canonical center-floor scalar windows.**  This is the RH-level version of
`xi_window_pinned_of_center_floor_scalars`: each window supplies the certified anchor floor
`m_J`, the carrier sup `M_J`, the canonical engine separation
`m_J / rz < M_J / (rJ - rz)`, and the two explicit exponential budget inequalities.  The
auxiliary minimum-modulus scalars required by `xi_window_pinned_of_center_scalars` are inserted
internally as `m_J / rz` and `M_J / (rJ - rz)`. -/
theorem riemannHypothesis_of_center_floor_scalar_windows
    (hwin : ∀ ρ ∈ rightHalf, xi ρ = 0 →
      ∃ (N M : ℕ) (ε₁ δ : ℝ) (c : ℂ)
        (t₁ t₂ rz r₀ R R' P rJ RJ m_J M_J M_G a₀ κ : ℝ),
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
        Real.log (M_J / m_J) / Real.log (RJ / rJ) < 2 ∧
        m_J / rz < M_J / (rJ - rz) ∧
        (∀ z : ℂ, z.re = 1 / 2 → z ∈ closedBall c rz →
          a₀ ≤ ‖archFactor z‖) ∧
        0 < κ ∧
        κ ≤ a₀ * ((m_J / rz) * Real.exp
          (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * rz / (rJ - rz)))) ∧
        (∀ z ∈ closedBall c RJ, ‖completedGN N z‖ ≤ M_G) ∧
        R * (2 * (M_G / P)) / (P * κ)
          + (1 + R * (2 * (M_G / P)) / (P * κ)) / 2 < 1 ∧
        (∀ z ∈ closedBall c RJ, ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁) ∧
        (∀ z ∈ closedBall c RJ, ‖emCarrier M z - gN N z‖ ≤ δ) ∧
        2 * (ε₁ + δ) < r₀ * ((m_J / rz) * Real.exp
          (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * (R + rz) /
            (rJ - (R + rz)))))) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_center_scalar_windows
  intro ρ hρ hzero
  obtain ⟨N, M, ε₁, δ, c, t₁, t₂, rz, r₀, R, R', P, rJ, RJ, m_J, M_J,
    M_G, a₀, κ, hM, hεδ, ht₁, h12, hrz0, h0, hrR, hRP, hPrz, hRrzJ,
    hrJR, hρR', hR'rz, hstrip, hbr, hsign, hmJ0, hmJ, hMJ, hbound,
    hjensen_floor, hengine, ha₀, hκ0, hκle, hMG, hηC, hE, hclose, hfl⟩ :=
    hwin ρ hρ hzero
  have hR0 : 0 < R := lt_trans h0 hrR
  have hrzJ : rz < rJ := by linarith
  have hrJ0 : 0 < rJ := by linarith
  have hratio : 1 < RJ / rJ := (one_lt_div hrJ0).mpr hrJR
  have hjensen : Real.log (M_J / ‖gN N c‖) / Real.log (RJ / rJ) < 2 :=
    gN_jensen_budget_of_anchor_floor hmJ0 hmJ hMJ hratio hjensen_floor
  refine ⟨N, M, ε₁, δ, c, t₁, t₂, rz, r₀, R, R', P, rJ, RJ, m_J, M_J,
    m_J / rz, M_J / (rJ - rz), M_G, a₀, κ, ?_⟩
  exact ⟨hM, hεδ, ht₁, h12, hrz0, h0, hrR, hRP, hPrz, hRrzJ, hrJR,
    hρR', hR'rz, hstrip, hbr, hsign, hmJ0, hmJ, hMJ, hbound, hjensen,
    div_pos hmJ0 hrz0, le_rfl, le_rfl, hengine, ha₀, hκ0, hκle, hMG, hηC,
    hE, hclose, hfl⟩

end RHTower

namespace RHTower

/-- **Center-floor scalar certificate with canonical derivative floor.**  This sharpens
`xi_window_pinned_of_center_floor_scalars` by removing the independent derivative-floor witness
`κ`: it is fixed to the minimum-modulus value produced from the same canonical floor,
`a₀ * (m_J / rz) * exp(...)`.  The remaining slope budget is therefore a direct scalar
inequality in the anchor floor, carrier sup, radii, archimedean floor, and completed-carrier sup. -/
theorem xi_window_pinned_of_center_floor_canonical_kappa
    {N M : ℕ} (hM : 1 ≤ M) {ε₁ δ : ℝ} (hεδ : 0 ≤ ε₁ + δ)
    {c : ℂ} {t₁ t₂ rz r₀ R P rJ RJ m_J M_J M_G a₀ : ℝ}
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
    (hjensen_floor : Real.log (M_J / m_J) / Real.log (RJ / rJ) < 2)
    (hengine : m_J / rz < M_J / (rJ - rz))
    (ha₀ : ∀ z : ℂ, z.re = 1 / 2 → z ∈ closedBall c rz → a₀ ≤ ‖archFactor z‖)
    (ha₀0 : 0 < a₀)
    (hMG : ∀ z ∈ closedBall c RJ, ‖completedGN N z‖ ≤ M_G)
    (hηC : R * (2 * (M_G / P)) /
        (P * (a₀ * ((m_J / rz) * Real.exp
          (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * rz / (rJ - rz))))))
      + (1 + R * (2 * (M_G / P)) /
        (P * (a₀ * ((m_J / rz) * Real.exp
          (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * rz / (rJ - rz))))))) / 2 < 1)
    (hE : ∀ z ∈ closedBall c RJ, ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁)
    (hclose : ∀ z ∈ closedBall c RJ, ‖emCarrier M z - gN N z‖ ≤ δ)
    (hfl : 2 * (ε₁ + δ) < r₀ * ((m_J / rz) * Real.exp
      (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * (R + rz) /
        (rJ - (R + rz)))))) :
    ∃ ρ' : ℂ, ρ'.re = 1 / 2 ∧ ρ' ∈ closedBall c rz ∧
      ∀ p ∈ ball ρ' R, xi p = 0 → p.re = 1 / 2 := by
  have hengineFloor0 : 0 < (m_J / rz) * Real.exp
      (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * rz / (rJ - rz))) :=
    mul_pos (div_pos hmJ0 hrz0) (Real.exp_pos _)
  have hκ0 : 0 < a₀ * ((m_J / rz) * Real.exp
      (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * rz / (rJ - rz)))) :=
    mul_pos ha₀0 hengineFloor0
  exact xi_window_pinned_of_center_floor_scalars hM hεδ ht₁ h12 hrz0 h0 hrR hRP hPrz
    hRrzJ hrJR hstrip hbr hsign hmJ0 hmJ hMJ hbound hjensen_floor hengine ha₀
    hκ0 le_rfl hMG hηC hE hclose hfl

/-- **RH gate with canonical derivative-floor center windows.**  This removes `κ` from the
per-zero scalar witness list.  Each window now supplies only the certified `gN` anchor floor,
the carrier and completed-carrier sups, radii, the archimedean scalar floor `a₀`, and the two
explicit exponential budgets, with the derivative floor inserted canonically. -/
theorem riemannHypothesis_of_center_floor_canonical_kappa_windows
    (hwin : ∀ ρ ∈ rightHalf, xi ρ = 0 →
      ∃ (N M : ℕ) (ε₁ δ : ℝ) (c : ℂ)
        (t₁ t₂ rz r₀ R R' P rJ RJ m_J M_J M_G a₀ : ℝ),
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
        Real.log (M_J / m_J) / Real.log (RJ / rJ) < 2 ∧
        m_J / rz < M_J / (rJ - rz) ∧
        (∀ z : ℂ, z.re = 1 / 2 → z ∈ closedBall c rz →
          a₀ ≤ ‖archFactor z‖) ∧
        0 < a₀ ∧
        (∀ z ∈ closedBall c RJ, ‖completedGN N z‖ ≤ M_G) ∧
        R * (2 * (M_G / P)) /
            (P * (a₀ * ((m_J / rz) * Real.exp
              (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * rz / (rJ - rz))))))
          + (1 + R * (2 * (M_G / P)) /
            (P * (a₀ * ((m_J / rz) * Real.exp
              (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * rz / (rJ - rz))))))) / 2 < 1 ∧
        (∀ z ∈ closedBall c RJ, ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁) ∧
        (∀ z ∈ closedBall c RJ, ‖emCarrier M z - gN N z‖ ≤ δ) ∧
        2 * (ε₁ + δ) < r₀ * ((m_J / rz) * Real.exp
          (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * (R + rz) /
            (rJ - (R + rz)))))) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_center_floor_scalar_windows
  intro ρ hρ hzero
  obtain ⟨N, M, ε₁, δ, c, t₁, t₂, rz, r₀, R, R', P, rJ, RJ, m_J, M_J,
    M_G, a₀, hM, hεδ, ht₁, h12, hrz0, h0, hrR, hRP, hPrz, hRrzJ, hrJR,
    hρR', hR'rz, hstrip, hbr, hsign, hmJ0, hmJ, hMJ, hbound, hjensen_floor,
    hengine, ha₀, ha₀0, hMG, hηC, hE, hclose, hfl⟩ := hwin ρ hρ hzero
  have hengineFloor0 : 0 < (m_J / rz) * Real.exp
      (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * rz / (rJ - rz))) :=
    mul_pos (div_pos hmJ0 hrz0) (Real.exp_pos _)
  have hκ0 : 0 < a₀ * ((m_J / rz) * Real.exp
      (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * rz / (rJ - rz)))) :=
    mul_pos ha₀0 hengineFloor0
  refine ⟨N, M, ε₁, δ, c, t₁, t₂, rz, r₀, R, R', P, rJ, RJ, m_J, M_J,
    M_G, a₀, a₀ * ((m_J / rz) * Real.exp
      (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * rz / (rJ - rz)))), ?_⟩
  exact ⟨hM, hεδ, ht₁, h12, hrz0, h0, hrR, hRP, hPrz, hRrzJ, hrJR,
    hρR', hR'rz, hstrip, hbr, hsign, hmJ0, hmJ, hMJ, hbound, hjensen_floor,
    hengine, ha₀, hκ0, le_rfl, hMG, hηC, hE, hclose, hfl⟩

end RHTower

namespace RHTower

/-- **Cross-multiplied slope budget.**  The slope constraint
`η + (1 + η) / 2 < 1`, with `η = R * (2 * (M / P)) / (P * κ)`, follows from the
plain product inequality `6 * R * M < P^2 * κ` when the denominator is positive. -/
theorem slope_budget_of_cross_mul {R M P κ : ℝ} (hP : 0 < P) (hκ : 0 < κ)
    (hcross : 6 * R * M < P ^ 2 * κ) :
    R * (2 * (M / P)) / (P * κ)
      + (1 + R * (2 * (M / P)) / (P * κ)) / 2 < 1 := by
  have hden0 : 0 < P ^ 2 * κ := mul_pos (sq_pos_of_pos hP) hκ
  have hηeq : R * (2 * (M / P)) / (P * κ) = (2 * R * M) / (P ^ 2 * κ) := by
    field_simp [hP.ne', hκ.ne']
  rw [hηeq]
  have hη : (2 * R * M) / (P ^ 2 * κ) < 1 / 3 := by
    rw [div_lt_iff₀ hden0]
    nlinarith
  linarith

/-- **Center-floor scalar certificate with cross-multiplied slope budget.**  This replaces the
nested `ηC` slope inequality in `xi_window_pinned_of_center_floor_canonical_kappa` by the product
inequality `6 * R * M_G < P^2 * κ`, with `κ` fixed to the canonical minimum-modulus derivative
floor. -/
theorem xi_window_pinned_of_center_floor_cross_slope
    {N M : ℕ} (hM : 1 ≤ M) {ε₁ δ : ℝ} (hεδ : 0 ≤ ε₁ + δ)
    {c : ℂ} {t₁ t₂ rz r₀ R P rJ RJ m_J M_J M_G a₀ : ℝ}
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
    (hjensen_floor : Real.log (M_J / m_J) / Real.log (RJ / rJ) < 2)
    (hengine : m_J / rz < M_J / (rJ - rz))
    (ha₀ : ∀ z : ℂ, z.re = 1 / 2 → z ∈ closedBall c rz → a₀ ≤ ‖archFactor z‖)
    (ha₀0 : 0 < a₀)
    (hMG : ∀ z ∈ closedBall c RJ, ‖completedGN N z‖ ≤ M_G)
    (hcross : 6 * R * M_G < P ^ 2 * (a₀ * ((m_J / rz) * Real.exp
      (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * rz / (rJ - rz))))))
    (hE : ∀ z ∈ closedBall c RJ, ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁)
    (hclose : ∀ z ∈ closedBall c RJ, ‖emCarrier M z - gN N z‖ ≤ δ)
    (hfl : 2 * (ε₁ + δ) < r₀ * ((m_J / rz) * Real.exp
      (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * (R + rz) /
        (rJ - (R + rz)))))) :
    ∃ ρ' : ℂ, ρ'.re = 1 / 2 ∧ ρ' ∈ closedBall c rz ∧
      ∀ p ∈ ball ρ' R, xi p = 0 → p.re = 1 / 2 := by
  have hPpos : 0 < P := lt_of_lt_of_le (lt_trans h0 hrR) hRP
  have hengineFloor0 : 0 < (m_J / rz) * Real.exp
      (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * rz / (rJ - rz))) :=
    mul_pos (div_pos hmJ0 hrz0) (Real.exp_pos _)
  have hκ0 : 0 < a₀ * ((m_J / rz) * Real.exp
      (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * rz / (rJ - rz)))) :=
    mul_pos ha₀0 hengineFloor0
  have hηC := slope_budget_of_cross_mul (R := R) (M := M_G) (P := P)
    (κ := a₀ * ((m_J / rz) * Real.exp
      (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * rz / (rJ - rz)))))
    hPpos hκ0 hcross
  exact xi_window_pinned_of_center_floor_canonical_kappa hM hεδ ht₁ h12 hrz0 h0 hrR
    hRP hPrz hRrzJ hrJR hstrip hbr hsign hmJ0 hmJ hMJ hbound hjensen_floor
    hengine ha₀ ha₀0 hMG hηC hE hclose hfl

/-- **RH gate with cross-multiplied canonical slope budgets.**  Each window now proves the slope
face by the product inequality `6 * R * M_G < P^2 * κ`, where `κ` is the canonical derivative
floor from the same center anchor and carrier sup. -/
theorem riemannHypothesis_of_center_floor_cross_slope_windows
    (hwin : ∀ ρ ∈ rightHalf, xi ρ = 0 →
      ∃ (N M : ℕ) (ε₁ δ : ℝ) (c : ℂ)
        (t₁ t₂ rz r₀ R R' P rJ RJ m_J M_J M_G a₀ : ℝ),
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
        Real.log (M_J / m_J) / Real.log (RJ / rJ) < 2 ∧
        m_J / rz < M_J / (rJ - rz) ∧
        (∀ z : ℂ, z.re = 1 / 2 → z ∈ closedBall c rz →
          a₀ ≤ ‖archFactor z‖) ∧
        0 < a₀ ∧
        (∀ z ∈ closedBall c RJ, ‖completedGN N z‖ ≤ M_G) ∧
        6 * R * M_G < P ^ 2 * (a₀ * ((m_J / rz) * Real.exp
          (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * rz / (rJ - rz))))) ∧
        (∀ z ∈ closedBall c RJ, ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁) ∧
        (∀ z ∈ closedBall c RJ, ‖emCarrier M z - gN N z‖ ≤ δ) ∧
        2 * (ε₁ + δ) < r₀ * ((m_J / rz) * Real.exp
          (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * (R + rz) /
            (rJ - (R + rz)))))) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_center_floor_canonical_kappa_windows
  intro ρ hρ hzero
  obtain ⟨N, M, ε₁, δ, c, t₁, t₂, rz, r₀, R, R', P, rJ, RJ, m_J, M_J,
    M_G, a₀, hM, hεδ, ht₁, h12, hrz0, h0, hrR, hRP, hPrz, hRrzJ, hrJR,
    hρR', hR'rz, hstrip, hbr, hsign, hmJ0, hmJ, hMJ, hbound, hjensen_floor,
    hengine, ha₀, ha₀0, hMG, hcross, hE, hclose, hfl⟩ := hwin ρ hρ hzero
  have hPpos : 0 < P := lt_of_lt_of_le (lt_trans h0 hrR) hRP
  have hengineFloor0 : 0 < (m_J / rz) * Real.exp
      (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * rz / (rJ - rz))) :=
    mul_pos (div_pos hmJ0 hrz0) (Real.exp_pos _)
  have hκ0 : 0 < a₀ * ((m_J / rz) * Real.exp
      (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * rz / (rJ - rz)))) :=
    mul_pos ha₀0 hengineFloor0
  have hηC := slope_budget_of_cross_mul (R := R) (M := M_G) (P := P)
    (κ := a₀ * ((m_J / rz) * Real.exp
      (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * rz / (rJ - rz)))))
    hPpos hκ0 hcross
  refine ⟨N, M, ε₁, δ, c, t₁, t₂, rz, r₀, R, R', P, rJ, RJ, m_J, M_J,
    M_G, a₀, ?_⟩
  exact ⟨hM, hεδ, ht₁, h12, hrz0, h0, hrR, hRP, hPrz, hRrzJ, hrJR,
    hρR', hR'rz, hstrip, hbr, hsign, hmJ0, hmJ, hMJ, hbound, hjensen_floor,
    hengine, ha₀, ha₀0, hMG, hηC, hE, hclose, hfl⟩

end RHTower

namespace RHTower

/-- Log/exponential normalization for the minimum-modulus floor.  It rewrites the Borel-Caratheodory
loss from exponential-log form to the equivalent power law in the relative anchor height `x / A`. -/
theorem minmod_exp_ratio_eq_power {x A r L : ℝ} (hx : 0 < x) (hA : 0 < A) :
    x * Real.exp (-(2 * Real.log (A / x) * r / L)) =
      x * (x / A) ^ (2 * r / L) := by
  rw [Real.rpow_def_of_pos (div_pos hx hA)]
  congr 1
  have hlogAx : Real.log (A / x) = Real.log A - Real.log x := by
    rw [Real.log_div hA.ne' hx.ne']
  have hlogxA : Real.log (x / A) = Real.log x - Real.log A := by
    rw [Real.log_div hx.ne' hA.ne']
  rw [hlogAx, hlogxA]
  ring_nf

/-- Certificate-floor specialization of `minmod_exp_ratio_eq_power`.  The canonical cofactor anchor is
`x = m_J / rz` and the canonical cofactor ceiling is `A = M_J / (rJ - rz)`. -/
theorem canonical_minmod_exp_eq_power {m_J M_J rz rJ s : ℝ}
    (hmJ0 : 0 < m_J) (hrz0 : 0 < rz) (hMJ0 : 0 < M_J) (hrzJ : rz < rJ) :
    (m_J / rz) * Real.exp
        (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * s / (rJ - s))) =
      (m_J / rz) *
        ((m_J / rz) / (M_J / (rJ - rz))) ^ (2 * s / (rJ - s)) := by
  exact minmod_exp_ratio_eq_power
    (x := m_J / rz) (A := M_J / (rJ - rz)) (r := s) (L := rJ - s)
    (div_pos hmJ0 hrz0) (div_pos hMJ0 (sub_pos.mpr hrzJ))

/-- Cross-slope producer from the power-law form of the canonical minimum-modulus floor. -/
theorem canonical_cross_budget_of_power_floor {m_J M_J rz rJ R P M_G a₀ : ℝ}
    (hmJ0 : 0 < m_J) (hrz0 : 0 < rz) (hMJ0 : 0 < M_J) (hrzJ : rz < rJ)
    (hcross : 6 * R * M_G < P ^ 2 * (a₀ * ((m_J / rz) *
      ((m_J / rz) / (M_J / (rJ - rz))) ^ (2 * rz / (rJ - rz))))) :
    6 * R * M_G < P ^ 2 * (a₀ * ((m_J / rz) * Real.exp
      (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * rz / (rJ - rz))))) := by
  rw [canonical_minmod_exp_eq_power (m_J := m_J) (M_J := M_J) (rz := rz) (rJ := rJ)
    (s := rz) hmJ0 hrz0 hMJ0 hrzJ]
  exact hcross

/-- EM-closeness producer from the power-law form of the canonical minimum-modulus floor at radius
`R + rz`. -/
theorem canonical_em_budget_of_power_floor {m_J M_J rz rJ R r₀ ε₁ δ : ℝ}
    (hmJ0 : 0 < m_J) (hrz0 : 0 < rz) (hMJ0 : 0 < M_J) (hrzJ : rz < rJ)
    (hfl : 2 * (ε₁ + δ) < r₀ * ((m_J / rz) *
      ((m_J / rz) / (M_J / (rJ - rz))) ^ (2 * (R + rz) / (rJ - (R + rz))))) :
    2 * (ε₁ + δ) < r₀ * ((m_J / rz) * Real.exp
      (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * (R + rz) /
        (rJ - (R + rz))))) := by
  rw [canonical_minmod_exp_eq_power (m_J := m_J) (M_J := M_J) (rz := rz) (rJ := rJ)
    (s := R + rz) hmJ0 hrz0 hMJ0 hrzJ]
  exact hfl

end RHTower
namespace RHTower

/-- The canonical dimensionless anchor ratio is positive and below one exactly when the engine
separation `m_J / rz < M_J / (rJ - rz)` holds. -/
theorem canonical_anchor_ratio_pos_lt_one_of_engine {m_J M_J rz rJ : ℝ}
    (hmJ0 : 0 < m_J) (hrz0 : 0 < rz) (hMJ0 : 0 < M_J) (hrzJ : rz < rJ)
    (hengine : m_J / rz < M_J / (rJ - rz)) :
    0 < (m_J / rz) / (M_J / (rJ - rz)) ∧
      (m_J / rz) / (M_J / (rJ - rz)) < 1 := by
  have hx : 0 < m_J / rz := div_pos hmJ0 hrz0
  have hA : 0 < M_J / (rJ - rz) := div_pos hMJ0 (sub_pos.mpr hrzJ)
  exact ⟨div_pos hx hA, (div_lt_one hA).mpr hengine⟩

/-- The minimum-modulus radius exponent `2s/(rJ-s)` is monotone in the radius below `rJ`. -/
theorem minmod_radius_exponent_mono {rJ s t : ℝ}
    (hs0 : 0 ≤ s) (hst : s ≤ t) (htJ : t < rJ) :
    2 * s / (rJ - s) ≤ 2 * t / (rJ - t) := by
  have hsJ : s < rJ := lt_of_le_of_lt hst htJ
  have hden_s : 0 < rJ - s := sub_pos.mpr hsJ
  have hden_t : 0 < rJ - t := sub_pos.mpr htJ
  rw [div_le_div_iff₀ hden_s hden_t]
  nlinarith

/-- On the canonical engine range, the relative-anchor power decreases as the certificate radius grows. -/
theorem canonical_anchor_ratio_rpow_antitone_radius {m_J M_J rz rJ s t : ℝ}
    (hmJ0 : 0 < m_J) (hrz0 : 0 < rz) (hMJ0 : 0 < M_J) (hrzJ : rz < rJ)
    (hengine : m_J / rz < M_J / (rJ - rz))
    (hs0 : 0 ≤ s) (hst : s ≤ t) (htJ : t < rJ) :
    ((m_J / rz) / (M_J / (rJ - rz))) ^ (2 * t / (rJ - t)) ≤
      ((m_J / rz) / (M_J / (rJ - rz))) ^ (2 * s / (rJ - s)) := by
  obtain ⟨hq0, hq1lt⟩ := canonical_anchor_ratio_pos_lt_one_of_engine
    hmJ0 hrz0 hMJ0 hrzJ hengine
  exact Real.rpow_le_rpow_of_exponent_ge hq0 hq1lt.le
    (minmod_radius_exponent_mono hs0 hst htJ)

/-- The outer EM radius has no larger canonical power factor than the inner cross-slope radius. -/
theorem canonical_em_power_le_cross_power {m_J M_J rz rJ R : ℝ}
    (hmJ0 : 0 < m_J) (hrz0 : 0 < rz) (hMJ0 : 0 < M_J) (hrzJ : rz < rJ)
    (hengine : m_J / rz < M_J / (rJ - rz)) (hR0 : 0 ≤ R) (hRrzJ : R + rz < rJ) :
    ((m_J / rz) / (M_J / (rJ - rz))) ^ (2 * (R + rz) / (rJ - (R + rz))) ≤
      ((m_J / rz) / (M_J / (rJ - rz))) ^ (2 * rz / (rJ - rz)) := by
  exact canonical_anchor_ratio_rpow_antitone_radius hmJ0 hrz0 hMJ0 hrzJ hengine
    hrz0.le (by linarith) hRrzJ

end RHTower

namespace RHTower

/-- A single outer-radius power floor feeds both canonical certificate budgets.  The EM-radius power
factor is no larger than the cross-slope power factor, so proving the cross budget against the outer
factor is stronger than the existing inner-radius cross budget; the EM budget is exactly the outer-radius
power form. -/
theorem canonical_cross_em_budgets_of_outer_power_floor
    {m_J M_J rz rJ R P M_G a₀ r₀ ε₁ δ : ℝ}
    (hmJ0 : 0 < m_J) (hrz0 : 0 < rz) (hMJ0 : 0 < M_J) (hrzJ : rz < rJ)
    (hengine : m_J / rz < M_J / (rJ - rz)) (ha₀0 : 0 < a₀)
    (hR0 : 0 ≤ R) (hRrzJ : R + rz < rJ)
    (hcross_outer : 6 * R * M_G < P ^ 2 * (a₀ * ((m_J / rz) *
      ((m_J / rz) / (M_J / (rJ - rz))) ^ (2 * (R + rz) / (rJ - (R + rz))))))
    (hfl_outer : 2 * (ε₁ + δ) < r₀ * ((m_J / rz) *
      ((m_J / rz) / (M_J / (rJ - rz))) ^ (2 * (R + rz) / (rJ - (R + rz))))) :
    6 * R * M_G < P ^ 2 * (a₀ * ((m_J / rz) * Real.exp
        (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * rz / (rJ - rz))))) ∧
      2 * (ε₁ + δ) < r₀ * ((m_J / rz) * Real.exp
        (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * (R + rz) /
          (rJ - (R + rz))))) := by
  have hx0 : 0 ≤ m_J / rz := (div_pos hmJ0 hrz0).le
  have hpow_le := canonical_em_power_le_cross_power
    (m_J := m_J) (M_J := M_J) (rz := rz) (rJ := rJ) (R := R)
    hmJ0 hrz0 hMJ0 hrzJ hengine hR0 hRrzJ
  have hfloor_le : (m_J / rz) *
      ((m_J / rz) / (M_J / (rJ - rz))) ^ (2 * (R + rz) / (rJ - (R + rz))) ≤
      (m_J / rz) *
      ((m_J / rz) / (M_J / (rJ - rz))) ^ (2 * rz / (rJ - rz)) := by
    exact mul_le_mul_of_nonneg_left hpow_le hx0
  have ha_floor_le : a₀ * ((m_J / rz) *
      ((m_J / rz) / (M_J / (rJ - rz))) ^ (2 * (R + rz) / (rJ - (R + rz)))) ≤
      a₀ * ((m_J / rz) *
      ((m_J / rz) / (M_J / (rJ - rz))) ^ (2 * rz / (rJ - rz))) := by
    exact mul_le_mul_of_nonneg_left hfloor_le ha₀0.le
  have hright_le : P ^ 2 * (a₀ * ((m_J / rz) *
      ((m_J / rz) / (M_J / (rJ - rz))) ^ (2 * (R + rz) / (rJ - (R + rz))))) ≤
      P ^ 2 * (a₀ * ((m_J / rz) *
      ((m_J / rz) / (M_J / (rJ - rz))) ^ (2 * rz / (rJ - rz)))) := by
    exact mul_le_mul_of_nonneg_left ha_floor_le (sq_nonneg P)
  have hcross_power : 6 * R * M_G < P ^ 2 * (a₀ * ((m_J / rz) *
      ((m_J / rz) / (M_J / (rJ - rz))) ^ (2 * rz / (rJ - rz)))) :=
    lt_of_lt_of_le hcross_outer hright_le
  exact ⟨canonical_cross_budget_of_power_floor hmJ0 hrz0 hMJ0 hrzJ hcross_power,
    canonical_em_budget_of_power_floor hmJ0 hrz0 hMJ0 hrzJ hfl_outer⟩

end RHTower

namespace RHTower

/-- A single normalized max budget implies the two product budgets. -/
theorem outer_power_budget_pair_of_max_floor
    {F R M_G P a₀ r₀ ε₁ δ : ℝ}
    (hP0 : 0 < P) (ha₀0 : 0 < a₀) (hr₀0 : 0 < r₀)
    (hbudget : max ((6 * R * M_G) / (P ^ 2 * a₀)) ((2 * (ε₁ + δ)) / r₀) < F) :
    6 * R * M_G < P ^ 2 * (a₀ * F) ∧ 2 * (ε₁ + δ) < r₀ * F := by
  have hden : 0 < P ^ 2 * a₀ := mul_pos (sq_pos_of_pos hP0) ha₀0
  have hcross_norm : (6 * R * M_G) / (P ^ 2 * a₀) < F :=
    lt_of_le_of_lt (le_max_left _ _) hbudget
  have hcross_mul := mul_lt_mul_of_pos_right hcross_norm hden
  rw [div_mul_cancel₀ _ hden.ne'] at hcross_mul
  have hcross : 6 * R * M_G < P ^ 2 * (a₀ * F) := by
    nlinarith [hcross_mul]
  have hfl_norm : (2 * (ε₁ + δ)) / r₀ < F :=
    lt_of_le_of_lt (le_max_right _ _) hbudget
  have hfl_mul := mul_lt_mul_of_pos_right hfl_norm hr₀0
  rw [div_mul_cancel₀ _ hr₀0.ne'] at hfl_mul
  have hfl : 2 * (ε₁ + δ) < r₀ * F := by
    nlinarith [hfl_mul]
  exact ⟨hcross, hfl⟩

/-- A single normalized max budget feeds both canonical certificate budgets. -/
theorem canonical_cross_em_budgets_of_outer_power_floor_max
    {m_J M_J rz rJ R P M_G a₀ r₀ ε₁ δ : ℝ}
    (hmJ0 : 0 < m_J) (hrz0 : 0 < rz) (hMJ0 : 0 < M_J) (hrzJ : rz < rJ)
    (hengine : m_J / rz < M_J / (rJ - rz)) (hP0 : 0 < P) (ha₀0 : 0 < a₀)
    (hr₀0 : 0 < r₀) (hR0 : 0 ≤ R) (hRrzJ : R + rz < rJ)
    (hbudget_outer : max ((6 * R * M_G) / (P ^ 2 * a₀)) ((2 * (ε₁ + δ)) / r₀) <
      (m_J / rz) *
        ((m_J / rz) / (M_J / (rJ - rz))) ^ (2 * (R + rz) / (rJ - (R + rz)))) :
    6 * R * M_G < P ^ 2 * (a₀ * ((m_J / rz) * Real.exp
        (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * rz / (rJ - rz))))) ∧
      2 * (ε₁ + δ) < r₀ * ((m_J / rz) * Real.exp
        (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * (R + rz) /
          (rJ - (R + rz))))) := by
  obtain ⟨hcross_outer, hfl_outer⟩ :=
    outer_power_budget_pair_of_max_floor
      (F := (m_J / rz) *
        ((m_J / rz) / (M_J / (rJ - rz))) ^ (2 * (R + rz) / (rJ - (R + rz))))
      (R := R) (M_G := M_G) (P := P) (a₀ := a₀) (r₀ := r₀)
      (ε₁ := ε₁) (δ := δ) hP0 ha₀0 hr₀0 hbudget_outer
  exact canonical_cross_em_budgets_of_outer_power_floor
    (m_J := m_J) (M_J := M_J) (rz := rz) (rJ := rJ) (R := R)
    (P := P) (M_G := M_G) (a₀ := a₀) (r₀ := r₀) (ε₁ := ε₁) (δ := δ)
    hmJ0 hrz0 hMJ0 hrzJ hengine ha₀0 hR0 hRrzJ hcross_outer hfl_outer

end RHTower

namespace RHTower

/-- A completed-carrier closed-ball bound follows from an archimedean closed-ball bound and a
boundary `gN` bound. -/
theorem completedGN_bound_of_arch_gN_sphere_bound
    {N : ℕ} {c : ℂ} {RJ M_J A_G : ℝ}
    (hRJ0 : 0 < RJ)
    (hstrip : ∀ z ∈ closedBall c RJ, 0 < z.re ∧ z.re < 1)
    (harch : ∀ z ∈ closedBall c RJ, ‖archFactor z‖ ≤ A_G)
    (hbound : ∀ z ∈ sphere c RJ, ‖gN N z‖ ≤ M_J) :
    ∀ z ∈ closedBall c RJ, ‖completedGN N z‖ ≤ A_G * M_J := by
  have hAG0 : 0 ≤ A_G := by
    exact le_trans (norm_nonneg (archFactor c)) (harch c (mem_closedBall_self hRJ0.le))
  have hgan : ∀ z ∈ closedBall c RJ, AnalyticAt ℂ (gN N) z := by
    intro z hz
    exact gN_analyticAt (Gammaℝ_ne_zero_of_re_pos (by
      rw [Complex.sub_re, Complex.one_re]
      linarith [(hstrip z hz).2]))
  have hgRJ : ∀ z ∈ closedBall c RJ, ‖gN N z‖ ≤ M_J :=
    norm_le_on_closedBall_of_sphere hRJ0 hgan hbound
  intro z hz
  change ‖archFactor z * gN N z‖ ≤ A_G * M_J
  rw [norm_mul]
  exact mul_le_mul (harch z hz) (hgRJ z hz) (norm_nonneg _) hAG0

end RHTower
