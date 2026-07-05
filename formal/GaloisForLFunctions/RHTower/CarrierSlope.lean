/-
Producing the carrier-vs-linear circle domination from one-dimensional data.

On the critical line the completed carrier is real (`completedGN_im_eq_zero_on_line`), so a sign
change of its real part between two line heights forces an on-line zero `ρ'` by the intermediate
value theorem.  At a zero the difference quotient `dslope (completedGN N) ρ'` is analytic on any
strip ball, takes the value `deriv (completedGN N) ρ'` at the center, and factors the carrier
exactly as `completedGN N z = (z − ρ')·dslope z`.  The Schwarz lemma turns a sup bound `Δ` for
the slope deviation on ONE circle of radius `P` into the linear decay `(Δ/P)·‖z − ρ'‖` on the
whole ball, hence into the two-circle relative domination
`‖completedGN N z − c(z−ρ')‖ ≤ (R·Δ/(P·κ))·‖c(z−ρ')‖` consumed by the pinning gates, where
`κ ≤ ‖deriv (completedGN N) ρ'‖` is a derivative floor at the zero.  The per-window carrier
certificate thereby reduces to: two signs on the line, one derivative floor at one point, and one
sup on one circle.
-/
import GaloisForLFunctions.RHTower.AnnealWindowRelation
import GaloisForLFunctions.RHTower.SeamSignTransport
import GaloisForLFunctions.RHTower.PinnedWindow
import GaloisForLFunctions.RHTower.MinimumModulus

open Complex Metric

namespace RHTower

/-- The difference quotient `dslope f a` of an analytic function is analytic: at the base
point via the shifted power series, elsewhere as a quotient with nonvanishing denominator. -/
theorem analyticAt_dslope_of_analyticAt {f : ℂ → ℂ} {a z : ℂ}
    (ha : AnalyticAt ℂ f a) (hz : AnalyticAt ℂ f z) :
    AnalyticAt ℂ (dslope f a) z := by
  rcases eq_or_ne z a with rfl | hne
  · obtain ⟨p, hp⟩ := ha
    exact hp.has_fpower_series_dslope_fslope.analyticAt
  · have hq : AnalyticAt ℂ (fun w => (f w - f a) / (w - a)) z :=
      (hz.sub analyticAt_const).div (analyticAt_id.sub analyticAt_const)
        (sub_ne_zero.mpr hne)
    apply hq.congr
    filter_upwards [isOpen_ne.mem_nhds hne] with w hw
    rw [dslope_of_ne _ hw, slope_def_field]

/-- **Schwarz decay from one circle.**  An analytic function on a closed ball whose deviation
from its center value is at most `Δ` on the boundary circle satisfies the linear decay
`‖h z − h a‖ ≤ (Δ/P)·‖z − a‖` on the whole closed ball: the maximum principle spreads the
circle bound inward, and the Schwarz lemma converts the resulting ball bound into vanishing
proportional to the distance from the center. -/
theorem slope_deviation_ball_bound {h : ℂ → ℂ} {a : ℂ} {P Δ : ℝ}
    (hP : 0 < P)
    (hh : ∀ z ∈ closedBall a P, AnalyticAt ℂ h z)
    (hΔ : ∀ z ∈ sphere a P, ‖h z - h a‖ ≤ Δ) :
    ∀ z ∈ closedBall a P, ‖h z - h a‖ ≤ Δ / P * ‖z - a‖ := by
  have hdiffcl : DiffContOnCl ℂ (fun z => h z - h a) (ball a P) := by
    constructor
    · intro z hz
      exact ((hh z (ball_subset_closedBall hz)).sub
        analyticAt_const).differentiableAt.differentiableWithinAt
    · intro z hz
      rw [closure_ball a hP.ne'] at hz
      exact ((hh z hz).sub analyticAt_const).continuousAt.continuousWithinAt
  have hmax : ∀ z ∈ closedBall a P, ‖h z - h a‖ ≤ Δ := by
    intro z hz
    have hfr : ∀ w ∈ frontier (ball a P), ‖h w - h a‖ ≤ Δ := by
      intro w hw
      rw [frontier_ball a hP.ne'] at hw
      exact hΔ w hw
    refine Complex.norm_le_of_forall_mem_frontier_norm_le
      Metric.isBounded_ball hdiffcl hfr ?_
    rw [closure_ball a hP.ne']
    exact hz
  intro z hz
  rcases eq_or_lt_of_le (mem_closedBall.mp hz) with heq | hlt
  · have hnorm : ‖z - a‖ = P := by rw [← dist_eq_norm]; exact heq
    calc ‖h z - h a‖ ≤ Δ := hΔ z (mem_sphere.mpr heq)
      _ = Δ / P * P := (div_mul_cancel₀ Δ hP.ne').symm
      _ = Δ / P * ‖z - a‖ := by rw [hnorm]
  · have hd : DifferentiableOn ℂ h (ball a P) := fun w hw =>
      (hh w (ball_subset_closedBall hw)).differentiableAt.differentiableWithinAt
    have hmaps : Set.MapsTo h (ball a P) (closedBall (h a) Δ) := by
      intro w hw
      rw [mem_closedBall, dist_eq_norm]
      exact hmax w (ball_subset_closedBall hw)
    have := Complex.dist_le_div_mul_dist_of_mapsTo_ball hd hmaps (mem_ball.mpr hlt)
    rwa [dist_eq_norm, dist_eq_norm] at this

/-- **On-line carrier zero from a sign change.**  The completed carrier is real on the critical
line, so a sign change of its real part between two heights produces an on-line zero between
them: continuity along the line plus the intermediate value theorem.  Two signs — purely
one-dimensional data — certify a zero of the two-dimensional carrier, on the line. -/
theorem exists_online_carrier_zero_of_sign_change (N : ℕ) {t₁ t₂ : ℝ} (h12 : t₁ ≤ t₂)
    (hsign : (completedGN N (((1 / 2 : ℝ) : ℂ) + (t₁ : ℂ) * I)).re
      * (completedGN N (((1 / 2 : ℝ) : ℂ) + (t₂ : ℂ) * I)).re ≤ 0) :
    ∃ τ ∈ Set.Icc t₁ t₂, completedGN N (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) = 0 := by
  have hcontline : Continuous fun τ : ℝ =>
      completedGN N (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) := by
    rw [continuous_iff_continuousAt]
    intro τ
    have hre : ((((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)).re = 1 / 2 := by simp
    have h1 : ContinuousAt (completedGN N) (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) :=
      (completedGN_analyticAt (by rw [hre]; norm_num)
        (by rw [hre]; norm_num)).continuousAt
    have hlin : ContinuousAt (fun τ : ℝ => ((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) τ := by
      fun_prop
    show ContinuousAt
      (completedGN N ∘ fun τ : ℝ => ((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) τ
    exact ContinuousAt.comp h1 hlin
  have hφ : Continuous fun τ : ℝ =>
      (completedGN N (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)).re :=
    Complex.continuous_re.comp hcontline
  have hzero : ∃ τ ∈ Set.Icc t₁ t₂,
      (completedGN N (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)).re = 0 := by
    rcases mul_nonpos_iff.mp hsign with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨τ, hτ, hφτ⟩ := intermediate_value_Icc' h12 hφ.continuousOn ⟨h2, h1⟩
      exact ⟨τ, hτ, hφτ⟩
    · obtain ⟨τ, hτ, hφτ⟩ := intermediate_value_Icc h12 hφ.continuousOn ⟨h1, h2⟩
      exact ⟨τ, hτ, hφτ⟩
  obtain ⟨τ, hτ, hφτ⟩ := hzero
  refine ⟨τ, hτ, ?_⟩
  have hre : ((((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)).re = 1 / 2 := by simp
  have him := completedGN_im_eq_zero_on_line (N := N) hre
  exact Complex.ext (by simpa using hφτ) (by simpa using him)

/-- **Carrier-vs-linear circle domination from slope data.**  At an on-line carrier zero with
derivative floor `κ`, a sup bound `Δ` for the slope deviation on ONE circle of radius `P`
produces the relative domination of the carrier by its tangent line on BOTH certificate
circles, with ratio `ηC = R·Δ/(P·κ)`.  This is the first producer of the `hcarrier` face of
the same-circle pinning gates; its data are two reals and one circle sup. -/
theorem completedGN_linear_domination_of_slope_data
    {N : ℕ} {ρ' : ℂ} {P r₀ R Δ κ : ℝ}
    (hP : 0 < P) (h0 : 0 ≤ r₀) (hr₀R : r₀ ≤ R) (hRP : R ≤ P) (hκ : 0 < κ)
    (hball : ∀ z ∈ closedBall ρ' P, 0 < z.re ∧ z.re < 1)
    (hzero : completedGN N ρ' = 0)
    (hderiv : κ ≤ ‖deriv (completedGN N) ρ'‖)
    (hΔ : ∀ z ∈ sphere ρ' P,
      ‖dslope (completedGN N) ρ' z - deriv (completedGN N) ρ'‖ ≤ Δ) :
    ∀ z ∈ sphere ρ' r₀ ∪ sphere ρ' R,
      ‖completedGN N z - deriv (completedGN N) ρ' * (z - ρ')‖
        ≤ R * Δ / (P * κ) * ‖deriv (completedGN N) ρ' * (z - ρ')‖ := by
  set g : ℂ → ℂ := dslope (completedGN N) ρ' with hg_def
  have hρ'mem : ρ' ∈ closedBall ρ' P := mem_closedBall_self hP.le
  have hgan : ∀ z ∈ closedBall ρ' P, AnalyticAt ℂ g z := fun z hz =>
    analyticAt_dslope_of_analyticAt
      (completedGN_analyticAt (hball ρ' hρ'mem).1 (hball ρ' hρ'mem).2)
      (completedGN_analyticAt (hball z hz).1 (hball z hz).2)
  have hga : g ρ' = deriv (completedGN N) ρ' := dslope_same _ _
  have hΔ0 : 0 ≤ Δ := by
    obtain ⟨w, hw⟩ := (NormedSpace.sphere_nonempty (x := ρ')).mpr hP.le
    exact le_trans (norm_nonneg _) (hΔ w hw)
  have hΔ' : ∀ z ∈ sphere ρ' P, ‖g z - g ρ'‖ ≤ Δ := by
    intro z hz
    rw [hga]
    exact hΔ z hz
  have hdev := slope_deviation_ball_bound hP hgan hΔ'
  have hfact : ∀ z : ℂ, completedGN N z = (z - ρ') * g z := by
    intro z
    have hs := sub_smul_dslope (completedGN N) ρ' z
    rw [hzero, sub_zero, smul_eq_mul] at hs
    exact hs.symm
  intro z hz
  have hzR : ‖z - ρ'‖ ≤ R := by
    rcases hz with h | h
    · rw [mem_sphere] at h
      rw [← dist_eq_norm, h]
      exact hr₀R
    · rw [mem_sphere] at h
      rw [← dist_eq_norm, h]
  have hzP : z ∈ closedBall ρ' P := by
    rw [mem_closedBall, dist_eq_norm]
    exact le_trans hzR hRP
  have hdev' : ‖g z - deriv (completedGN N) ρ'‖ ≤ Δ / P * ‖z - ρ'‖ := by
    rw [← hga]
    exact hdev z hzP
  have hq0 : (0 : ℝ) ≤ ‖z - ρ'‖ := norm_nonneg _
  have hR0 : (0 : ℝ) ≤ R := le_trans h0 hr₀R
  have hfrac0 : (0 : ℝ) ≤ R * Δ / (P * κ) :=
    div_nonneg (mul_nonneg hR0 hΔ0) (mul_nonneg hP.le hκ.le)
  calc ‖completedGN N z - deriv (completedGN N) ρ' * (z - ρ')‖
      = ‖z - ρ'‖ * ‖g z - deriv (completedGN N) ρ'‖ := by
        rw [hfact z, show (z - ρ') * g z - deriv (completedGN N) ρ' * (z - ρ')
          = (z - ρ') * (g z - deriv (completedGN N) ρ') by ring, norm_mul]
    _ ≤ ‖z - ρ'‖ * (Δ / P * ‖z - ρ'‖) :=
        mul_le_mul_of_nonneg_left hdev' hq0
    _ = Δ / P * (‖z - ρ'‖ * ‖z - ρ'‖) := by ring
    _ ≤ Δ / P * (R * ‖z - ρ'‖) := by
        apply mul_le_mul_of_nonneg_left _ (div_nonneg hΔ0 hP.le)
        exact mul_le_mul_of_nonneg_right hzR hq0
    _ = R * Δ / (P * κ) * (κ * ‖z - ρ'‖) := by
        field_simp
    _ ≤ R * Δ / (P * κ) * (‖deriv (completedGN N) ρ'‖ * ‖z - ρ'‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hderiv hq0) hfrac0
    _ = R * Δ / (P * κ) * ‖deriv (completedGN N) ρ' * (z - ρ')‖ := by
        rw [norm_mul]

/-- **Slope-data pinned window.**  At an on-line carrier zero with derivative floor `κ` and
slope deviation `Δ` on the enclosing circle of radius `P`, the EM remainder, finite-carrier
closeness and LOW floor on the two certificate circles pin every ξ-zero of the window ball to
the critical line, provided the total budget `ηC + (1+ηC)/2 < 1` with `ηC = R·Δ/(P·κ)`.  The
carrier face of the same-circle certificate is discharged by the tangent-line domination. -/
theorem xi_window_pinned_of_slope_circles
    {N M : ℕ} (hM : 1 ≤ M) {ε₁ δ : ℝ} (hεδ : 0 ≤ ε₁ + δ)
    {ρ₀ : ℂ} {r₀ R P Δ κ : ℝ}
    (h0 : 0 < r₀) (hrR : r₀ < R) (hRP : R ≤ P) (hκ : 0 < κ)
    (hηC : R * Δ / (P * κ) + (1 + R * Δ / (P * κ)) / 2 < 1)
    (hρ₀re : ρ₀.re = 1 / 2)
    (hball : ∀ z ∈ closedBall ρ₀ P, 0 < z.re ∧ z.re < 1)
    (hzero : completedGN N ρ₀ = 0)
    (hderiv : κ ≤ ‖deriv (completedGN N) ρ₀‖)
    (hΔ : ∀ z ∈ sphere ρ₀ P,
      ‖dslope (completedGN N) ρ₀ z - deriv (completedGN N) ρ₀‖ ≤ Δ)
    (hE : ∀ z ∈ sphere ρ₀ r₀ ∪ sphere ρ₀ R,
      ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁)
    (hclose : ∀ z ∈ sphere ρ₀ r₀ ∪ sphere ρ₀ R,
      ‖emCarrier M z - gN N z‖ ≤ δ)
    (hFcirc : CarrierFloorOn (sphere ρ₀ r₀ ∪ sphere ρ₀ R) N (2 * (ε₁ + δ))) :
    (∀ p ∈ ball ρ₀ R, xi p = 0 → p.re = 1 / 2) ∧
      ∀ z ∈ chartRA ρ₀ r₀ R ∪ chartLA ρ₀ r₀ R,
        ‖Complex.log (xi z / (deriv (completedGN N) ρ₀ * (z - ρ₀)))‖ ≤
          (1 - (R * Δ / (P * κ) + (1 + R * Δ / (P * κ)) / 2))⁻¹ *
            ‖(xi z - deriv (completedGN N) ρ₀ * (z - ρ₀))
              / (deriv (completedGN N) ρ₀ * (z - ρ₀))‖ := by
  have hP : 0 < P := lt_of_lt_of_le (lt_trans h0 hrR) hRP
  have hc : deriv (completedGN N) ρ₀ ≠ 0 :=
    norm_pos_iff.mp (lt_of_lt_of_le hκ hderiv)
  have hsub : sphere ρ₀ r₀ ∪ sphere ρ₀ R ⊆ closedBall ρ₀ P := by
    intro z hz
    rcases hz with h | h
    · rw [mem_sphere] at h
      rw [mem_closedBall, h]
      linarith
    · rw [mem_sphere] at h
      rw [mem_closedBall, h]
      exact hRP
  have hstripCirc : ∀ z ∈ sphere ρ₀ r₀ ∪ sphere ρ₀ R, 0 < z.re ∧ z ≠ 1 := by
    intro z hz
    obtain ⟨h0re, h1re⟩ := hball z (hsub hz)
    refine ⟨h0re, fun h1 => ?_⟩
    rw [h1] at h1re
    simp at h1re
  have hcarrier := completedGN_linear_domination_of_slope_data
    hP h0.le hrR.le hRP hκ hball hzero hderiv hΔ
  exact xi_window_pinned_of_emCarrier_single_circle_pair hM hεδ hc h0 hrR hηC
    hρ₀re hstripCirc hcarrier hE hclose hFcirc

/-- **Slope-data RH gate.**  RH follows from per-zero certificates whose carrier face is fully
one-dimensional: an on-line carrier zero (producible from two line signs), a derivative floor at
that single point, one slope sup on one circle, and EM/closeness/floor data on the two
certificate circles. -/
theorem riemannHypothesis_of_slope_circle_windows
    (hwin : ∀ ρ ∈ rightHalf, xi ρ = 0 →
      ∃ (N M : ℕ) (ε₁ δ P Δ κ : ℝ) (ρ₀ : ℂ) (r₀ R : ℝ),
        1 ≤ M ∧ 0 ≤ ε₁ + δ ∧ 0 < r₀ ∧ r₀ < R ∧ R ≤ P ∧ 0 < κ
        ∧ R * Δ / (P * κ) + (1 + R * Δ / (P * κ)) / 2 < 1
        ∧ ρ ∈ ball ρ₀ R ∧ ρ₀.re = 1 / 2
        ∧ (∀ z ∈ closedBall ρ₀ P, 0 < z.re ∧ z.re < 1)
        ∧ completedGN N ρ₀ = 0
        ∧ κ ≤ ‖deriv (completedGN N) ρ₀‖
        ∧ (∀ z ∈ sphere ρ₀ P,
            ‖dslope (completedGN N) ρ₀ z - deriv (completedGN N) ρ₀‖ ≤ Δ)
        ∧ (∀ z ∈ sphere ρ₀ r₀ ∪ sphere ρ₀ R,
            ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁)
        ∧ (∀ z ∈ sphere ρ₀ r₀ ∪ sphere ρ₀ R,
            ‖emCarrier M z - gN N z‖ ≤ δ)
        ∧ CarrierFloorOn (sphere ρ₀ r₀ ∪ sphere ρ₀ R) N (2 * (ε₁ + δ))) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_local_online_windows
  intro ρ hρ hzero
  obtain ⟨N, M, ε₁, δ, P, Δ, κ, ρ₀, r₀, R, hM, hεδ, h0, hrR, hRP, hκ, hηC,
    hρball, hρ₀re, hball, hzeroG, hderiv, hΔ, hE, hclose, hFcirc⟩ :=
    hwin ρ hρ hzero
  exact ⟨ρ₀, R, hρball,
    (xi_window_pinned_of_slope_circles hM hεδ h0 hrR hRP hκ hηC hρ₀re hball
      hzeroG hderiv hΔ hE hclose hFcirc).1⟩

end RHTower

namespace RHTower

/-- At the zero of a one-zero factorization the derivative of the completed carrier is the
archimedean factor times the cofactor value: `completedGN′(ρ') = archFactor(ρ')·h(ρ')`.  The
`gN`-derivative at the zero is the cofactor value (product rule, vanishing factor), and the
archimedean product contributes only its own value there since `gN(ρ') = 0`. -/
theorem deriv_completedGN_of_factor {N : ℕ} {ρ' c : ℂ} {h : ℂ → ℂ} {R : ℝ}
    (hρ' : ρ' ∈ ball c R) (h0re : 0 < ρ'.re)
    (hh : AnalyticOnNhd ℂ h (ball c R))
    (hfact : ∀ z ∈ ball c R, gN N z = (z - ρ') * h z) :
    deriv (completedGN N) ρ' = archFactor ρ' * h ρ' := by
  have hg0 : gN N ρ' = 0 := by
    rw [hfact ρ' hρ']
    simp
  have hev : gN N =ᶠ[nhds ρ'] fun z => (z - ρ') * h z := by
    filter_upwards [isOpen_ball.mem_nhds hρ'] with z hz using hfact z hz
  have hhd : DifferentiableAt ℂ h ρ' := (hh ρ' hρ').differentiableAt
  have hprod : HasDerivAt (fun z => (z - ρ') * h z)
      (1 * h ρ' + (ρ' - ρ') * deriv h ρ') ρ' :=
    HasDerivAt.mul ((hasDerivAt_id ρ').sub_const ρ') hhd.hasDerivAt
  have hd1 : deriv (fun z => (z - ρ') * h z) ρ' = h ρ' := by
    simpa using hprod.deriv
  have hgderiv : deriv (gN N) ρ' = h ρ' := by
    rw [hev.deriv_eq, hd1]
  have hgdiff : DifferentiableAt ℂ (gN N) ρ' := by
    rw [hev.differentiableAt_iff]
    exact (differentiableAt_id.sub_const ρ').mul hhd
  have hGne : Gammaℝ ρ' ≠ 0 := Gammaℝ_ne_zero_of_re_pos h0re
  have harch : AnalyticAt ℂ archFactor ρ' := by
    have hpoly : AnalyticAt ℂ (fun s : ℂ => s * (s - 1) / 2) ρ' := by fun_prop
    exact hpoly.mul (Gammaℝ_analyticAt hGne)
  calc deriv (completedGN N) ρ'
      = deriv (archFactor * gN N) ρ' := rfl
    _ = deriv archFactor ρ' * gN N ρ' + archFactor ρ' * deriv (gN N) ρ' :=
        deriv_mul harch.differentiableAt hgdiff
    _ = archFactor ρ' * h ρ' := by
        rw [hg0, hgderiv]
        ring

/-- **Derivative floor at the window zero from anchor and sup.**  For a one-zero window with
zero-free cofactor, the minimum-modulus engine floors the cofactor at the zero, and the
archimedean value converts this into the derivative floor `κ` consumed by the slope-data
pinning gates: `κ = a₀·m·exp(−2·log(M/m)·r/(R−r))` from one anchor `m`, one sup `M`, and one
archimedean scalar `a₀`. -/
theorem deriv_completedGN_floor_of_anchor {N : ℕ} {ρ' c : ℂ} {h : ℂ → ℂ}
    {R r M m a₀ : ℝ}
    (hr : 0 ≤ r) (hrR : r < R)
    (hρ' : ρ' ∈ closedBall c r) (h0re : 0 < ρ'.re)
    (hh : AnalyticOnNhd ℂ h (ball c R))
    (hh0 : ∀ z ∈ ball c R, h z ≠ 0)
    (hfact : ∀ z ∈ ball c R, gN N z = (z - ρ') * h z)
    (hsup : ∀ z ∈ ball c R, ‖h z‖ ≤ M)
    (hm : 0 < m) (hmM : m < M) (hanc : m ≤ ‖h c‖)
    (ha₀ : a₀ ≤ ‖archFactor ρ'‖) :
    a₀ * (m * Real.exp (-(2 * Real.log (M / m) * r / (R - r))))
      ≤ ‖deriv (completedGN N) ρ'‖ := by
  have hρball : ρ' ∈ ball c R :=
    mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hρ') hrR)
  rw [deriv_completedGN_of_factor hρball h0re hh hfact, norm_mul]
  exact mul_le_mul ha₀
    (norm_lower_bound_of_anchor hr hrR hh hh0 hsup hm hmM hanc ρ' hρ')
    (by positivity) (norm_nonneg _)

end RHTower

namespace RHTower

/-- **Difference-quotient sup from a boundary carrier sup.**  If `G` is analytic on
`closedBall a P` and vanishes at `ρ'` (at distance at most `dρ < P` from the center), a sup
bound `M` for `G` on the boundary circle bounds the difference quotient by `M/(P − dρ)` on the
whole closed ball: on the circle the quotient is `‖G z‖/‖z − ρ'‖` with denominator at least
`P − dρ`, and the maximum principle spreads the bound inward through the removable point. -/
theorem dslope_norm_le_of_boundary_sup {G : ℂ → ℂ} {a ρ' : ℂ} {P M dρ : ℝ}
    (hdρ0 : 0 ≤ dρ) (hdρ : ‖ρ' - a‖ ≤ dρ) (hdP : dρ < P)
    (hG : ∀ z ∈ closedBall a P, AnalyticAt ℂ G z)
    (hzero : G ρ' = 0)
    (hsup : ∀ z ∈ sphere a P, ‖G z‖ ≤ M) :
    ∀ z ∈ closedBall a P, ‖dslope G ρ' z‖ ≤ M / (P - dρ) := by
  have hP : 0 < P := lt_of_le_of_lt hdρ0 hdP
  have hρ'mem : ρ' ∈ closedBall a P := by
    rw [mem_closedBall, dist_eq_norm]
    linarith
  have hhan : ∀ z ∈ closedBall a P, AnalyticAt ℂ (dslope G ρ') z := fun z hz =>
    analyticAt_dslope_of_analyticAt (hG ρ' hρ'mem) (hG z hz)
  have hfr : ∀ z ∈ sphere a P, ‖dslope G ρ' z‖ ≤ M / (P - dρ) := by
    intro z hz
    have hzdist : P - dρ ≤ ‖z - ρ'‖ := by
      have h1 : ‖z - a‖ = P := by
        rw [← dist_eq_norm]
        exact mem_sphere.mp hz
      have h2 : ‖z - a‖ - ‖ρ' - a‖ ≤ ‖z - ρ'‖ := by
        have := norm_sub_norm_le (z - a) (ρ' - a)
        simpa [sub_sub_sub_cancel_right] using this
      linarith
    have hzne : z ≠ ρ' := by
      intro hzeq
      rw [hzeq, sub_self, norm_zero] at hzdist
      linarith
    rw [dslope_of_ne _ hzne, slope_def_field, hzero, sub_zero, norm_div]
    have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hsup z hz)
    apply div_le_div₀ hM0 (hsup z hz) (by linarith)
    exact hzdist
  intro z hz
  have hdiffcl : DiffContOnCl ℂ (dslope G ρ') (ball a P) := by
    constructor
    · intro w hw
      exact (hhan w (ball_subset_closedBall hw)).differentiableAt.differentiableWithinAt
    · intro w hw
      rw [closure_ball a hP.ne'] at hw
      exact (hhan w hw).continuousAt.continuousWithinAt
  refine Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hdiffcl ?_ ?_
  · intro w hw
    rw [frontier_ball a hP.ne'] at hw
    exact hfr w hw
  · rw [closure_ball a hP.ne']
    exact hz

/-- **Slope-deviation sup from a boundary carrier sup.**  At a zero of `G`, the deviation of
the difference quotient from the derivative on the circle of radius `P` is at most `2M/P`,
where `M` bounds `G` on that circle: both the quotient and the derivative (the quotient's
center value) are bounded by `M/P`. -/
theorem slope_deviation_of_boundary_sup {G : ℂ → ℂ} {ρ' : ℂ} {P M : ℝ}
    (hP : 0 < P)
    (hG : ∀ z ∈ closedBall ρ' P, AnalyticAt ℂ G z)
    (hzero : G ρ' = 0)
    (hsup : ∀ z ∈ sphere ρ' P, ‖G z‖ ≤ M) :
    ∀ z ∈ sphere ρ' P, ‖dslope G ρ' z - deriv G ρ'‖ ≤ 2 * (M / P) := by
  have hball := dslope_norm_le_of_boundary_sup (le_refl 0)
    (by simp) hP hG hzero hsup
  simp only [sub_zero] at hball
  intro z hz
  have hzmem : z ∈ closedBall ρ' P := sphere_subset_closedBall hz
  have hcen : ‖deriv G ρ'‖ ≤ M / P := by
    rw [← dslope_same G ρ']
    exact hball ρ' (mem_closedBall_self hP.le)
  calc ‖dslope G ρ' z - deriv G ρ'‖
      ≤ ‖dslope G ρ' z‖ + ‖deriv G ρ'‖ := norm_sub_le _ _
    _ ≤ M / P + M / P := add_le_add (hball z hzmem) hcen
    _ = 2 * (M / P) := by ring

end RHTower
