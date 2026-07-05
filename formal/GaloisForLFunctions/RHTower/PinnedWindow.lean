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

/-- **The EM-pinned window from carrier data alone.**  Every ξ-side hypothesis
of `xi_window_pinned_of_emCarrier_close_half_floor` is discharged internally:
the `1/2` relative error forbids ξ-zeros on the annulus (the slit charts cover
it), and ξ multi-peels through its hole zeros by `xi_ball_factorization`.  The
whole certificate is carrier arithmetic: EM bounds, closeness, the doubled LOW
floor, and one simple carrier zero at the critical-line center. -/
theorem xi_window_pinned_of_carrier_simple_zero
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
    (hfactg : ∀ z ∈ ball ρ₀ R, completedGN N z = (z - ρ₀) * h z) :
    (∀ p ∈ ball ρ₀ R, xi p = 0 → p.re = 1 / 2) ∧
      ∀ z ∈ chartRA ρ₀ r₀ R ∪ chartLA ρ₀ r₀ R,
        ‖Complex.log (xi z / completedGN N z)‖ ≤
          (1 - (1 / 2 : ℝ))⁻¹ * ‖(xi z - completedGN N z) / completedGN N z‖ := by
  have hfloor_nonneg : 0 ≤ 2 * (ε₁ + δ) := mul_nonneg (by norm_num) hεδ
  have hg0 : ∀ z ∈ chartRA ρ₀ r₀ R ∪ chartLA ρ₀ r₀ R, completedGN N z ≠ 0 := by
    intro z hz
    obtain ⟨hσ, hz1⟩ := hstrip z hz
    exact completedGN_ne_zero_of_gN_ne_zero hσ hz1
      (gN_ne_zero_of_carrierFloorOn hfloor_nonneg hF z hz)
  have hrel : ∀ z ∈ chartRA ρ₀ r₀ R ∪ chartLA ρ₀ r₀ R,
      ‖(xi z - completedGN N z) / completedGN N z‖ ≤ (1 / 2 : ℝ) :=
    completed_relative_error_of_emCarrier_close_half_floor hM hεδ hstrip hE hclose hF
  have hhole : ∀ p ∈ ball ρ₀ R, xi p = 0 → ‖p - ρ₀‖ ≤ r₀ := by
    intro p hp hxi
    by_contra hout
    have hann : p ∈ ball ρ₀ R \ closedBall ρ₀ r₀ :=
      ⟨hp, fun hmem => hout (by rwa [mem_closedBall, Complex.dist_eq] at hmem)⟩
    have hmem := annulus_subset_charts h0 hann
    have h1 := hrel p hmem
    rw [hxi, zero_sub, norm_div, norm_neg,
      div_self (norm_ne_zero_iff.mpr (hg0 p hmem))] at h1
    norm_num at h1
  obtain ⟨t, m', h', htmem, hh'an, hh'0, hfactf⟩ := xi_ball_factorization ρ₀ R
  exact xi_window_pinned_of_emCarrier_close_half_floor hM hεδ h0 hrR hρ₀re hstrip hE
    hclose hF hh hh0 hfactg t m' hh'an hh'0
    (fun w hw => hhole w ((htmem w).mp hw).1 ((htmem w).mp hw).2) hfactf

/-- **The EM-pinned RH gate.**  RH from a family of EM-pinned window
certificates, one around each hypothetical right-half ξ-zero: finite EM
remainder and closeness bounds, a doubled LOW floor, and the carrier's
one-simple-zero factorization at a critical-line center.  The counting
substitute pins each window's ξ-zeros to the line; no sign table and no
ξ-side hypothesis enters. -/
theorem riemannHypothesis_of_emCarrier_pinned_windows
    (hwin : ∀ ρ ∈ rightHalf, xi ρ = 0 →
      ∃ (N M : ℕ) (ε₁ δ : ℝ) (h : ℂ → ℂ) (ρ₀ : ℂ) (r₀ R : ℝ),
        1 ≤ M ∧ 0 ≤ ε₁ + δ ∧ 0 ≤ r₀ ∧ r₀ < R ∧ ρ ∈ ball ρ₀ R ∧ ρ₀.re = 1 / 2
        ∧ (∀ z ∈ chartRA ρ₀ r₀ R ∪ chartLA ρ₀ r₀ R, 0 < z.re ∧ z ≠ 1)
        ∧ (∀ z ∈ chartRA ρ₀ r₀ R ∪ chartLA ρ₀ r₀ R,
            ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁)
        ∧ (∀ z ∈ chartRA ρ₀ r₀ R ∪ chartLA ρ₀ r₀ R, ‖emCarrier M z - gN N z‖ ≤ δ)
        ∧ CarrierFloorOn (chartRA ρ₀ r₀ R ∪ chartLA ρ₀ r₀ R) N (2 * (ε₁ + δ))
        ∧ AnalyticOnNhd ℂ h (ball ρ₀ R) ∧ (∀ z ∈ ball ρ₀ R, h z ≠ 0)
        ∧ (∀ z ∈ ball ρ₀ R, completedGN N z = (z - ρ₀) * h z)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_local_online_windows
  intro ρ hρ hzero
  obtain ⟨N, M, ε₁, δ, h, ρ₀, r₀, R, hM, hεδ, h0, hrR, hρball, hρ₀re,
    hstrip, hE, hclose, hF, hh, hh0, hfactg⟩ := hwin ρ hρ hzero
  exact ⟨ρ₀, R, hρball,
    (xi_window_pinned_of_carrier_simple_zero hM hεδ h0 hrR hρ₀re
      hstrip hE hclose hF hh hh0 hfactg).1⟩

end RHTower

namespace RHTower

open Complex Filter Metric

/-- **The carrier one-simple-zero criterion.**  If the completed carrier is
dominated by a linear reference `c·(z − ρ₀)` on the annulus charts of a strip
window centered on the critical line, then it has exactly one zero in the
window ball — a simple zero `ρ'` on the critical line inside the hole — and
factors as `completedGN N = (·−ρ')·h` with `h` analytic and zero-free on the
ball.  Everything is derived from the domination: no annulus zeros (chart
coverage), local finiteness and finite orders (analyticity, nonvanishing at a
chart point), enclosed count `= 1` (the Rouché substitute against the count-1
reference), on-line location (the pinning lemma, with the carrier's own real
FE `completedGN_lineReflect` as symmetry input), and the factorization
(multi-peeling through the unique zero). -/
theorem completedGN_simple_zero_factorization_of_close
    {N : ℕ} {ρ₀ c : ℂ} (hc : c ≠ 0) {r₀ R : ℝ}
    (h0 : 0 ≤ r₀) (hrR : r₀ < R) (hρ₀re : ρ₀.re = 1 / 2)
    (hball : ∀ z ∈ ball ρ₀ R, 0 < z.re ∧ z.re < 1)
    (hclose : ∀ z ∈ chartRA ρ₀ r₀ R ∪ chartLA ρ₀ r₀ R,
      ‖completedGN N z - c * (z - ρ₀)‖ < ‖c * (z - ρ₀)‖) :
    ∃ (ρ' : ℂ) (h : ℂ → ℂ), ρ'.re = 1 / 2 ∧ ‖ρ' - ρ₀‖ ≤ r₀
      ∧ AnalyticOnNhd ℂ h (ball ρ₀ R) ∧ (∀ z ∈ ball ρ₀ R, h z ≠ 0)
      ∧ ∀ z ∈ ball ρ₀ R, completedGN N z = (z - ρ') * h z := by
  classical
  have hFan : AnalyticOnNhd ℂ (completedGN N) (ball ρ₀ R) := fun z hz =>
    completedGN_analyticAt (hball z hz).1 (hball z hz).2
  -- a chart point where domination forbids vanishing
  set z₀ : ℂ := ρ₀ + (((r₀ + R) / 2 : ℝ) : ℂ) with hz₀_def
  have hRpos : 0 < R := lt_of_le_of_lt h0 hrR
  have hmid : r₀ < (r₀ + R) / 2 ∧ (r₀ + R) / 2 < R := by constructor <;> linarith
  have hz₀norm : ‖z₀ - ρ₀‖ = (r₀ + R) / 2 := by
    rw [hz₀_def, add_sub_cancel_left, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  have hz₀ball : z₀ ∈ ball ρ₀ R := by
    rw [mem_ball, Complex.dist_eq, hz₀norm]
    exact hmid.2
  have hz₀chart : z₀ ∈ chartRA ρ₀ r₀ R := by
    refine ⟨?_, hz₀ball, ?_⟩
    · show z₀ - ρ₀ ∈ slitPlane
      rw [Complex.mem_slitPlane_iff, hz₀_def, add_sub_cancel_left]
      left
      rw [Complex.ofReal_re]
      linarith
    · rw [mem_closedBall, Complex.dist_eq, hz₀norm]
      exact not_le.mpr hmid.1
  have hFz₀ : completedGN N z₀ ≠ 0 := by
    intro hzero
    have hcl := hclose z₀ (Or.inl hz₀chart)
    rw [hzero, zero_sub, norm_neg] at hcl
    exact lt_irrefl _ hcl
  -- domination confines every ball zero to the hole
  have hzero_hole : ∀ p ∈ ball ρ₀ R, completedGN N p = 0 → ‖p - ρ₀‖ ≤ r₀ := by
    intro p hp hxi
    by_contra hout
    have hann : p ∈ ball ρ₀ R \ closedBall ρ₀ r₀ :=
      ⟨hp, fun hmem => hout (by rwa [mem_closedBall, Complex.dist_eq] at hmem)⟩
    have hcl := hclose p (annulus_subset_charts h0 hann)
    rw [hxi, zero_sub, norm_neg] at hcl
    exact lt_irrefl _ hcl
  -- local finiteness of the ball zeros, and finite orders
  have hcod : {x | completedGN N x ≠ 0} ∈ codiscreteWithin (ball ρ₀ R) := by
    rcases hFan.eqOn_zero_or_eventually_ne_zero_of_preconnected
        (convex_ball ρ₀ R).isPreconnected with h | h
    · exact absurd (h hz₀ball) hFz₀
    · exact h
  have hfin : {z ∈ ball ρ₀ R | completedGN N z = 0}.Finite := by
    have hK : IsCompact (closedBall ρ₀ r₀) := isCompact_closedBall _ _
    have hmem : {x | completedGN N x ≠ 0} ∈ codiscreteWithin (closedBall ρ₀ r₀) :=
      Filter.codiscreteWithin_mono (closedBall_subset_ball hrR) hcod
    refine (hK.finite_diff_of_mem_codiscreteWithin hmem).subset ?_
    rintro x ⟨hxb, hx0⟩
    refine ⟨?_, by simpa using hx0⟩
    rw [mem_closedBall, Complex.dist_eq]
    exact hzero_hole x hxb hx0
  have hordF : ∀ w ∈ ball ρ₀ R, analyticOrderAt (completedGN N) w ≠ ⊤ := by
    intro w hw htop
    have hev0 : completedGN N =ᶠ[nhds w] (0 : ℂ → ℂ) := by
      filter_upwards [analyticOrderAt_eq_top.mp htop] with z hz
      simpa using hz
    exact hFz₀ (hFan.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball ρ₀ R).isPreconnected hw hev0 hz₀ball)
  -- multi-peel through the ball zeros
  have htmem : ∀ w, w ∈ hfin.toFinset ↔ w ∈ ball ρ₀ R ∧ completedGN N w = 0 := by
    intro w
    rw [Set.Finite.mem_toFinset]
    rfl
  obtain ⟨m, h', hh'an, hh'0, hfactf⟩ := exists_multi_peel isOpen_ball hFan
    hfin.toFinset (fun w hw => ((htmem w).mp hw).1)
    (fun z hz hz0 => (htmem z).mpr ⟨hz, hz0⟩)
    (fun w hw => hordF w ((htmem w).mp hw).1)
  have hρ't : ∀ w ∈ hfin.toFinset, ‖w - ρ₀‖ ≤ r₀ := fun w hw =>
    hzero_hole w ((htmem w).mp hw).1 ((htmem w).mp hw).2
  -- the Rouché substitute: enclosed count = 1
  have hcount := enclosed_count_eq_of_close ({ρ₀} : Finset ℂ) hfin.toFinset
    id (fun _ => 1) id m h0 hrR
    (fun i hi => by
      rw [Finset.mem_singleton] at hi
      subst hi
      simpa using h0)
    hρ't (fun z _ => analyticAt_const) (fun z _ => hc) hh'an hh'0
    (fun z _ => by rw [Finset.prod_singleton]; simp only [id_eq, pow_one]; ring)
    hfactf hclose
  rw [Finset.sum_singleton] at hcount
  -- every listed zero has multiplicity ≥ 1, so there is exactly one, simple
  have hm1 : ∀ w ∈ hfin.toFinset, 1 ≤ m w := by
    intro w hw
    rcases Nat.eq_zero_or_pos (m w) with hm0 | hm0
    · exfalso
      obtain ⟨hwball, hwz⟩ := (htmem w).mp hw
      have hfa := hfactf w hwball
      rw [hwz] at hfa
      have hprod : (∏ w' ∈ hfin.toFinset, (w - w') ^ m w') ≠ 0 := by
        rw [Finset.prod_ne_zero_iff]
        intro w' hw'
        by_cases hww' : w' = w
        · rw [hww', sub_self, hm0, pow_zero]
          exact one_ne_zero
        · exact pow_ne_zero _ (sub_ne_zero.mpr fun hh => hww' hh.symm)
      exact mul_ne_zero hprod (hh'0 w hwball) hfa.symm
    · exact hm0
  have hne : hfin.toFinset.Nonempty := by
    rcases Finset.eq_empty_or_nonempty hfin.toFinset with he | hne
    · rw [he, Finset.sum_empty] at hcount
      exact absurd hcount (by norm_num)
    · exact hne
  have hcard1 : hfin.toFinset.card = 1 := by
    have hle : hfin.toFinset.card ≤ 1 := by
      calc hfin.toFinset.card = ∑ _w ∈ hfin.toFinset, 1 :=
            (Finset.card_eq_sum_ones _)
        _ ≤ ∑ w ∈ hfin.toFinset, m w := Finset.sum_le_sum hm1
        _ = 1 := hcount
    exact le_antisymm hle (Finset.card_pos.mpr hne)
  obtain ⟨ρ', hρ'eq⟩ := Finset.card_eq_one.mp hcard1
  have hρ'mem : ρ' ∈ hfin.toFinset := by
    rw [hρ'eq]
    exact Finset.mem_singleton_self ρ'
  have hmρ' : m ρ' = 1 := by
    have h1 := hcount
    rw [hρ'eq, Finset.sum_singleton] at h1
    exact h1
  -- the pinning lemma puts the zero on the line (carrier real FE as symmetry)
  have hsym : ∀ z ∈ ball ρ₀ R,
      completedGN N (1 - (starRingEnd ℂ) z) = (starRingEnd ℂ) (completedGN N z) := by
    intro z hz
    have h1 := completedGN_lineReflect (N := N) (hball z hz).1 (hball z hz).2
    rwa [show lineReflect z = 1 - (starRingEnd ℂ) z from rfl] at h1
  have hpin := pinned_zero_re_eq_half hfin.toFinset id m h0 hrR hρ₀re hsym
    (fun z _ => analyticAt_const) (fun z _ => hc) hh'an hh'0
    (fun z _ => by ring) hρ't hfactf hclose
  have hρ're : ρ'.re = 1 / 2 := hpin ρ' hρ'mem (by rw [hmρ']; norm_num)
  refine ⟨ρ', h', hρ're, hρ't ρ' hρ'mem, hh'an, hh'0, ?_⟩
  intro z hz
  have hfa := hfactf z hz
  rwa [hρ'eq, Finset.prod_singleton, hmρ', pow_one] at hfa

end RHTower

namespace RHTower

open Complex Metric

/-- **The double-domination pinned window.**  Two dominations produce the whole
certificate: the carrier dominated by a linear reference on the outer window
yields its unique simple on-line zero `ρ'`
(`completedGN_simple_zero_factorization_of_close`), and the EM/LOW data on the
window recentered at `ρ'` pins every ξ-zero there to the critical line
(`xi_window_pinned_of_carrier_simple_zero`), with the U0 log control on the
recentered charts. -/
theorem xi_window_pinned_of_double_domination
    {N M : ℕ} (hM : 1 ≤ M) {ε₁ δ : ℝ} (hεδ : 0 ≤ ε₁ + δ)
    {ρ₀ c : ℂ} (hc : c ≠ 0) {r₀ R r₀' R' : ℝ}
    (h0 : 0 ≤ r₀) (hrR : r₀ < R) (h0' : 0 ≤ r₀') (hrR' : r₀' < R')
    (hRR' : R' + r₀ ≤ R) (hρ₀re : ρ₀.re = 1 / 2)
    (hball : ∀ z ∈ ball ρ₀ R, 0 < z.re ∧ z.re < 1)
    (hcloseC : ∀ z ∈ chartRA ρ₀ r₀ R ∪ chartLA ρ₀ r₀ R,
      ‖completedGN N z - c * (z - ρ₀)‖ < ‖c * (z - ρ₀)‖)
    (hdata : ∀ ρ' : ℂ, ρ'.re = 1 / 2 → ‖ρ' - ρ₀‖ ≤ r₀ →
      (∀ z ∈ chartRA ρ' r₀' R' ∪ chartLA ρ' r₀' R', 0 < z.re ∧ z ≠ 1)
      ∧ (∀ z ∈ chartRA ρ' r₀' R' ∪ chartLA ρ' r₀' R',
          ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁)
      ∧ (∀ z ∈ chartRA ρ' r₀' R' ∪ chartLA ρ' r₀' R',
          ‖emCarrier M z - gN N z‖ ≤ δ)
      ∧ CarrierFloorOn (chartRA ρ' r₀' R' ∪ chartLA ρ' r₀' R') N (2 * (ε₁ + δ))) :
    ∃ ρ' : ℂ, ρ'.re = 1 / 2 ∧ ‖ρ' - ρ₀‖ ≤ r₀
      ∧ (∀ p ∈ ball ρ' R', xi p = 0 → p.re = 1 / 2)
      ∧ ∀ z ∈ chartRA ρ' r₀' R' ∪ chartLA ρ' r₀' R',
          ‖Complex.log (xi z / completedGN N z)‖ ≤
            (1 - (1 / 2 : ℝ))⁻¹ * ‖(xi z - completedGN N z) / completedGN N z‖ := by
  obtain ⟨ρ', h, hρ're, hρ'hole, hhan, hh0, hfact⟩ :=
    completedGN_simple_zero_factorization_of_close hc h0 hrR hρ₀re hball hcloseC
  have hsub : ball ρ' R' ⊆ ball ρ₀ R := by
    intro z hz
    rw [mem_ball] at hz ⊢
    calc dist z ρ₀ ≤ dist z ρ' + dist ρ' ρ₀ := dist_triangle z ρ' ρ₀
      _ < R' + r₀ := by
          have h2 : dist ρ' ρ₀ ≤ r₀ := by rwa [Complex.dist_eq]
          linarith
      _ ≤ R := hRR'
  obtain ⟨hstrip', hE', hclose', hF'⟩ := hdata ρ' hρ're hρ'hole
  obtain ⟨honline, hlog⟩ := xi_window_pinned_of_carrier_simple_zero hM hεδ h0' hrR'
    hρ're hstrip' hE' hclose' hF' (hhan.mono hsub) (fun z hz => hh0 z (hsub hz))
    (fun z hz => hfact z (hsub hz))
  exact ⟨ρ', hρ're, hρ'hole, honline, hlog⟩

/-- **The double-domination RH gate.**  RH from a family of two-domination
certificates, one per hypothetical right-half ξ-zero: a linear-reference
domination of the completed carrier on the outer window (which locates the
carrier's unique simple on-line zero), and EM/closeness/LOW-floor data on the
recentered window.  Every structural clause — carrier factorization, ξ
factorization, symmetry, zero location — is internal. -/
theorem riemannHypothesis_of_double_domination_windows
    (hwin : ∀ ρ ∈ rightHalf, xi ρ = 0 →
      ∃ (N M : ℕ) (ε₁ δ : ℝ) (ρ₀ c : ℂ) (r₀ R r₀' R' : ℝ),
        1 ≤ M ∧ 0 ≤ ε₁ + δ ∧ c ≠ 0
        ∧ 0 ≤ r₀ ∧ r₀ < R ∧ 0 ≤ r₀' ∧ r₀' < R' ∧ R' + r₀ ≤ R
        ∧ ρ₀.re = 1 / 2 ∧ ρ ∈ ball ρ₀ (R' - r₀)
        ∧ (∀ z ∈ ball ρ₀ R, 0 < z.re ∧ z.re < 1)
        ∧ (∀ z ∈ chartRA ρ₀ r₀ R ∪ chartLA ρ₀ r₀ R,
            ‖completedGN N z - c * (z - ρ₀)‖ < ‖c * (z - ρ₀)‖)
        ∧ (∀ ρ' : ℂ, ρ'.re = 1 / 2 → ‖ρ' - ρ₀‖ ≤ r₀ →
            (∀ z ∈ chartRA ρ' r₀' R' ∪ chartLA ρ' r₀' R', 0 < z.re ∧ z ≠ 1)
            ∧ (∀ z ∈ chartRA ρ' r₀' R' ∪ chartLA ρ' r₀' R',
                ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁)
            ∧ (∀ z ∈ chartRA ρ' r₀' R' ∪ chartLA ρ' r₀' R',
                ‖emCarrier M z - gN N z‖ ≤ δ)
            ∧ CarrierFloorOn (chartRA ρ' r₀' R' ∪ chartLA ρ' r₀' R')
                N (2 * (ε₁ + δ)))) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_local_online_windows
  intro ρ hρ hzero
  obtain ⟨N, M, ε₁, δ, ρ₀, c, r₀, R, r₀', R', hM, hεδ, hc, h0, hrR, h0', hrR', hRR',
    hρ₀re, hρball, hball, hcloseC, hdata⟩ := hwin ρ hρ hzero
  obtain ⟨ρ', hρ're, hρ'hole, honline, -⟩ :=
    xi_window_pinned_of_double_domination hM hεδ hc h0 hrR h0' hrR' hRR' hρ₀re
      hball hcloseC hdata
  refine ⟨ρ', R', ?_, honline⟩
  rw [mem_ball] at hρball ⊢
  calc dist ρ ρ' ≤ dist ρ ρ₀ + dist ρ₀ ρ' := dist_triangle ρ ρ₀ ρ'
    _ < (R' - r₀) + r₀ := by
        have h2 : dist ρ₀ ρ' ≤ r₀ := by
          rw [Complex.dist_eq, norm_sub_rev]
          exact hρ'hole
        linarith
    _ = R' := by ring

end RHTower
