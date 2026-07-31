/-
# The u-plane winding realisation: annulus torsors, the seam-index formula, and comparison

The winding (flow) face of the deck-charge calculus, carried onto the descended function
`xiDescent` and its slit-plane geometry.  Three Phase-D deliverables live here.

* **Root-torsor classification on a slit annulus (`xiDescent_deckClass_annulus_isolating`,
  `xiDescent_deckClass_annulus_one_iff_dvd`).**  Around an isolated `u`-plane zero `w₀`, any
  two chart roots of `xiDescent` on the right/left annulus charts have deck class
  `exp(2πi · ord_{w₀} / n)`, and it is trivial — a global `n`-th root exists across the
  annulus — exactly when `n ∣ ord_{w₀}`.  The rank-one torsor is completely classified by the
  enclosed order mod `n`.

* **The seam-index formula (`windingNumber_xiDescent_disc`, `loopCharge_xiDescent_disc`).**
  The winding number of `xiDescent` around a circle is the total order of the enclosed
  `u`-plane zeros, and its rung-`k` reduction is the enclosed deck charge `wCharge (2^k)`.
  For a circle centred on the real axis the enclosed zeros are conjugation-symmetric, so an
  island of genuinely off-real zeros contributes **even** order and the rung-`1` winding
  vanishes (`loopCharge_xiDescent_disc_two_eq_zero`) — the seam sees only the parity of the
  total, blind to a single odd upper defect.

* **Comparison `s ↔ u` (`windingNumber_xiDescent_center_sq`,
  `windingNumber_xiDescent_eq_xi_of_center_sq`).**  The winding of `xiDescent` around the
  descended image `(ρ − 1/2)²` equals the winding of `ξ` around `ρ`; both read the shared
  multiplicity.  The `s`-plane quadrant winding and the `u`-plane slit winding are the same
  integer.

The single-zero peel `xiDescent_peel_ball` and the multi-zero peel `exists_multi_peel_orders`
feed the argument principle `windingNumber_argument_principle`; the annulus class uses
`deckClass_multi_zero`.  These are the ξ-templates (`WindingXi`, `IsolatingAnnulusRung`)
transported to the descended function.
-/
import GaloisForLFunctions.RHTower.UPlaneTorsor
import GaloisForLFunctions.RHTower.WindingXi
import GaloisForLFunctions.RHTower.DeckMultiZero

namespace RHTower

open Complex Set Metric Filter

/-! ### The isolating peel of the descended function -/

/-- **The peel extends to any isolating ball.**  If `xiDescent` has no zero on `ball w₀ R`
except possibly `w₀`, then `xiDescent = (z − w₀)^m · h` there with `h` analytic and nonvanishing
on the whole ball. -/
theorem xiDescent_peel_isolating_ball (w₀ : ℂ) {R : ℝ}
    (hiso : ∀ z ∈ ball w₀ R, z ≠ w₀ → xiDescent z ≠ 0) :
    ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h (ball w₀ R) ∧
      (∀ z ∈ ball w₀ R, h z ≠ 0) ∧
      ∀ z ∈ ball w₀ R, xiDescent z = (z - w₀) ^ (analyticOrderAt xiDescent w₀).toNat * h z := by
  have hm : analyticOrderAt xiDescent w₀ = ((analyticOrderAt xiDescent w₀).toNat : ℕ∞) :=
    (ENat.coe_toNat (xiDescent_orderAt_ne_top w₀)).symm
  obtain ⟨h, hhan, hh0, hfact, -⟩ :=
    exists_peel isOpen_univ xiDescent_analyticOnNhd_univ (Set.mem_univ w₀) hm
  refine ⟨h, fun z _ => hhan z (Set.mem_univ z), ?_, fun z _ => hfact z (Set.mem_univ z)⟩
  intro z hz
  by_cases hzρ : z = w₀
  · rwa [hzρ]
  · intro h0
    have hf := hfact z (Set.mem_univ z)
    rw [h0, mul_zero] at hf
    exact hiso z hz hzρ hf

/-! ### The annulus root-torsor classification -/

/-- **The deck class of the descended function on an isolating annulus.**  For annulus data
`0 ≤ r₀ < R` whose ball contains no `xiDescent`-zero besides the centre, any local analytic
`n`-th roots of `xiDescent` on the two slit annulus charts have deck class `exp(2πi·m/n)`, where
`m = ord_{w₀} xiDescent`. -/
theorem xiDescent_deckClass_annulus_isolating (w₀ : ℂ) {r₀ R : ℝ} (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    (hiso : ∀ z ∈ ball w₀ R, z ≠ w₀ → xiDescent z ≠ 0) {n : ℕ} (hn : 0 < n) {G₁ G₂ : ℂ → ℂ}
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartRA w₀ r₀ R))
    (hG₂ : AnalyticOnNhd ℂ G₂ (chartLA w₀ r₀ R))
    (hpG₁ : ∀ z ∈ chartRA w₀ r₀ R, G₁ z ^ n = xiDescent z)
    (hpG₂ : ∀ z ∈ chartLA w₀ r₀ R, G₂ z ^ n = xiDescent z) :
    deckClass G₁ G₂ (w₀ + (((r₀ + R) / 2 : ℝ) : ℂ) * I)
        (w₀ - (((r₀ + R) / 2 : ℝ) : ℂ) * I) =
      exp (2 * (Real.pi : ℂ) * I * ((analyticOrderAt xiDescent w₀).toNat : ℂ) / n) := by
  obtain ⟨h, hhan, hh0, hfact⟩ := xiDescent_peel_isolating_ball w₀ hiso
  have hmz := deckClass_multi_zero (Finset.univ : Finset Unit) (fun _ => w₀)
    (fun _ => (analyticOrderAt xiDescent w₀).toNat) h0 hrR hn
    (fun _ _ => by simpa using h0)
    hhan hh0
    (fun z hz => by
      have hprod : (∏ _i ∈ (Finset.univ : Finset Unit),
          (z - w₀) ^ (analyticOrderAt xiDescent w₀).toNat) =
          (z - w₀) ^ (analyticOrderAt xiDescent w₀).toNat := by simp
      rw [hprod]
      exact hfact z hz)
    hG₁ hG₂ hpG₁ hpG₂
  have hsum : (∑ _i ∈ (Finset.univ : Finset Unit),
      (((analyticOrderAt xiDescent w₀).toNat : ℕ) : ℂ)) =
      ((analyticOrderAt xiDescent w₀).toNat : ℂ) := by simp
  rw [hsum] at hmz
  exact hmz

/-- **Complete rank-one classification.**  On an isolating slit annulus the deck class is trivial
— a global `n`-th root of `xiDescent` exists across the annulus — exactly when `n ∣ ord_{w₀}`. -/
theorem xiDescent_deckClass_annulus_one_iff_dvd (w₀ : ℂ) {r₀ R : ℝ} (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    (hiso : ∀ z ∈ ball w₀ R, z ≠ w₀ → xiDescent z ≠ 0) {n : ℕ} (hn : 0 < n) {G₁ G₂ : ℂ → ℂ}
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartRA w₀ r₀ R))
    (hG₂ : AnalyticOnNhd ℂ G₂ (chartLA w₀ r₀ R))
    (hpG₁ : ∀ z ∈ chartRA w₀ r₀ R, G₁ z ^ n = xiDescent z)
    (hpG₂ : ∀ z ∈ chartLA w₀ r₀ R, G₂ z ^ n = xiDescent z) :
    deckClass G₁ G₂ (w₀ + (((r₀ + R) / 2 : ℝ) : ℂ) * I)
        (w₀ - (((r₀ + R) / 2 : ℝ) : ℂ) * I) = 1 ↔
      n ∣ (analyticOrderAt xiDescent w₀).toNat := by
  rw [xiDescent_deckClass_annulus_isolating w₀ h0 hrR hiso hn hG₁ hG₂ hpG₁ hpG₂]
  exact exp_two_pi_mul_div_eq_one_iff hn _

/-! ### Local finiteness and the root-existence face on slit domains -/

/-- The nonvanishing locus of `xiDescent` is codiscrete: it is entire and not identically zero
(`xiDescent (9/4) ≠ 0`), so its zeros are isolated. -/
theorem xiDescent_ne_zero_codiscrete :
    {x | xiDescent x ≠ 0} ∈ codiscreteWithin (Set.univ : Set ℂ) := by
  rcases xiDescent_analyticOnNhd_univ.eqOn_zero_or_eventually_ne_zero_of_preconnected
      isPreconnected_univ with h | h
  · exact absurd (by simpa using h (Set.mem_univ ((9 : ℂ) / 4))) xiDescent_far_anchor_ne_zero
  · exact h

/-- Local finiteness of the `xiDescent`-zeros in an arbitrary ball. -/
theorem xiDescent_zeros_finite_ball (a : ℂ) (R : ℝ) :
    {z ∈ Metric.ball a R | xiDescent z = 0}.Finite := by
  have hK : IsCompact (Metric.closedBall a R) := isCompact_closedBall _ _
  have hmem : {x | xiDescent x ≠ 0} ∈ codiscreteWithin (Metric.closedBall a R) :=
    Filter.codiscreteWithin_mono (subset_univ _) xiDescent_ne_zero_codiscrete
  refine (hK.finite_sdiff_of_mem_codiscreteWithin hmem).subset ?_
  rintro x ⟨hxb, hx0⟩
  exact ⟨ball_subset_closedBall hxb, by simpa using hx0⟩

/-- **Root existence on a slit domain.**  On a convex open slit-plane region with one nonvanishing
point, `xiDescent` admits an analytic `2^k`-th root exactly when its deck charge is trivial at every
enclosed zero.  Together with the annulus class this is the complete classification of the allowed
root torsors: a global root exists iff every local charge vanishes; a single nonzero local charge
(an off-slit zero of order not divisible by `2^k`) is the whole obstruction. -/
theorem xiDescent_root_on_slit_iff_charge {Ω : Set ℂ} {z₀ : ℂ} {k : ℕ}
    (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω) (hΩsub : Ω ⊆ slitPlane) (hz₀ : z₀ ∈ Ω)
    (hz₀0 : xiDescent z₀ ≠ 0) :
    (∃ g, AnalyticOnNhd ℂ g Ω ∧ ∀ s ∈ Ω, g s ^ (2 ^ k) = xiDescent s) ↔
      ∀ ρ ∈ Ω, xiDescent ρ = 0 → carrierCharge xiDescent k ρ = 1 := by
  refine exists_root_iff_carrierCharge_trivial hΩo hΩc hz₀
    (xiDescent_analyticOnNhd_of_subset_slitPlane hΩsub) hz₀0 ?_
  intro R
  exact (xiDescent_zeros_finite_ball z₀ ((R : ℝ) + 1)).subset (fun s hs => ⟨hs.1.2, hs.2⟩)

/-! ### The seam-index (winding) formula -/

/-- **The winding number of `xiDescent` around a zero is its order.**  There is a small disc about
`w₀` on which every positive-radius circle winds `xiDescent` exactly `ord_{w₀}` times. -/
theorem windingNumber_xiDescent_zero (w₀ : ℂ) :
    ∃ R₀ > 0, ∀ r : ℝ, 0 < r → r < R₀ →
      windingNumber (fun θ => xiDescent (w₀ + ↑r * exp (I * ↑θ))) 0 (2 * Real.pi)
        = ((analyticOrderAt xiDescent w₀).toNat : ℤ) := by
  obtain ⟨R₀, hR₀, h, hha, hh0, hfact⟩ := xiDescent_peel_ball w₀
  refine ⟨R₀, hR₀, fun r hr hrR => ?_⟩
  have hap := windingNumber_argument_principle ({()} : Finset Unit) (fun _ => w₀)
    (fun _ => (analyticOrderAt xiDescent w₀).toNat) (f := xiDescent) (g := h) (c := w₀)
    (r := r) (R := R₀) hrR hr (fun i _ => by rw [sub_self, norm_zero]; exact hr)
    hha.continuousOn hh0 (fun z hz => by rw [Finset.prod_singleton]; exact hfact z hz)
  rwa [Finset.sum_singleton] at hap

/-- The rung-`k` loop deck charge of a small circle about a `u`-plane zero is the reduction of its
order. -/
theorem loopCharge_xiDescent_zero (w₀ : ℂ) (k : ℕ) :
    ∃ R₀ > 0, ∀ r : ℝ, 0 < r → r < R₀ →
      loopCharge k (fun θ => xiDescent (w₀ + ↑r * exp (I * ↑θ))) 0 (2 * Real.pi)
        = wCharge (2 ^ k) ((analyticOrderAt xiDescent w₀).toNat : ℤ) := by
  obtain ⟨R₀, hR₀, hw⟩ := windingNumber_xiDescent_zero w₀
  exact ⟨R₀, hR₀, fun r hr hrR => by rw [loopCharge, hw r hr hrR]⟩

/-- **The seam-index formula.**  If `t` collects all `xiDescent`-zeros of `ball c R`, all strictly
inside the circle of radius `r < R`, the winding number of `xiDescent` around that circle is the
total enclosed order `Σ_{w ∈ t} ord_w` — the census of enclosed `u`-plane multiplicities. -/
theorem windingNumber_xiDescent_disc (c : ℂ) {r R : ℝ} (hrR : r < R) (hr : 0 < r)
    (t : Finset ℂ) (htU : ∀ w ∈ t, w ∈ Metric.ball c R)
    (hzeros : ∀ z ∈ Metric.ball c R, xiDescent z = 0 → z ∈ t)
    (hin : ∀ w ∈ t, ‖w - c‖ < r) :
    windingNumber (fun θ => xiDescent (c + ↑r * exp (I * ↑θ))) 0 (2 * Real.pi)
      = ∑ w ∈ t, ((analyticOrderAt xiDescent w).toNat : ℤ) := by
  obtain ⟨h, hha, hh0, hfact⟩ := exists_multi_peel_orders (f := xiDescent) isOpen_ball
    (xiDescent_analyticOnNhd_univ.mono (Set.subset_univ _)) t htU hzeros
    (fun w _ => xiDescent_orderAt_ne_top w)
  exact windingNumber_argument_principle t (fun w => w)
    (fun w => (analyticOrderAt xiDescent w).toNat) (f := xiDescent) (g := h) (c := c) (r := r) (R := R)
    hrR hr hin hha.continuousOn hh0 hfact

/-- The rung-`k` loop deck charge of a boundary circle is the reduction of the total enclosed
order — the winding realisation of the enclosed `u`-plane deck charge. -/
theorem loopCharge_xiDescent_disc (c : ℂ) {r R : ℝ} (hrR : r < R) (hr : 0 < r)
    (t : Finset ℂ) (htU : ∀ w ∈ t, w ∈ Metric.ball c R)
    (hzeros : ∀ z ∈ Metric.ball c R, xiDescent z = 0 → z ∈ t)
    (hin : ∀ w ∈ t, ‖w - c‖ < r) (k : ℕ) :
    loopCharge k (fun θ => xiDescent (c + ↑r * exp (I * ↑θ))) 0 (2 * Real.pi)
      = wCharge (2 ^ k) (∑ w ∈ t, ((analyticOrderAt xiDescent w).toNat : ℤ)) := by
  rw [loopCharge, windingNumber_xiDescent_disc c hrR hr t htU hzeros hin]

/-- **Controlled boundary winding.**  If `xiDescent` admits an analytic `2^k`-th root on the slit
disc `ball c R`, then the boundary rung-`k` winding charge vanishes: root existence forces the
enclosed order divisible, so the aggregate winding is `≡ 0`.  This is the winding-necessary condition
tying the root-torsor classification (Deliverable 1) to the seam-index formula (Deliverable 2). -/
theorem xiDescent_root_imp_loopCharge_disc_zero {c : ℂ} {r R : ℝ} {k : ℕ}
    (hrR : r < R) (hr : 0 < r) (hRsub : Metric.ball c R ⊆ slitPlane)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Metric.ball c R) (hz₀0 : xiDescent z₀ ≠ 0)
    (t : Finset ℂ) (htU : ∀ w ∈ t, w ∈ Metric.ball c R)
    (hzeros : ∀ z ∈ Metric.ball c R, xiDescent z = 0 → z ∈ t)
    (hin : ∀ w ∈ t, ‖w - c‖ < r)
    (hroot : ∃ g, AnalyticOnNhd ℂ g (Metric.ball c R) ∧
      ∀ s ∈ Metric.ball c R, g s ^ (2 ^ k) = xiDescent s) :
    loopCharge k (fun θ => xiDescent (c + ↑r * exp (I * ↑θ))) 0 (2 * Real.pi) = 0 := by
  haveI : NeZero (2 ^ k) := ⟨pow_ne_zero k (by norm_num)⟩
  have hchg := (xiDescent_root_on_slit_iff_charge isOpen_ball (convex_ball c R) hRsub hz₀ hz₀0).mp
    hroot
  have hdvd : ∀ w ∈ t, ((2 ^ k : ℕ) : ℤ) ∣ ((analyticOrderAt xiDescent w).toNat : ℤ) := by
    intro w hw
    by_cases hz : xiDescent w = 0
    · exact Int.natCast_dvd_natCast.mpr
        ((carrierCharge_eq_one_iff_dvd xiDescent k w).mp (hchg w (htU w hw) hz))
    · rw [analyticOrderAt_eq_zero.mpr (Or.inr hz)]; simp
  rw [loopCharge_xiDescent_disc c hrR hr t htU hzeros hin k, wCharge_eq_zero_iff]
  exact Finset.dvd_sum hdvd

/-- **Seam blindness at rung `1`.**  A circle centred on the real axis whose enclosed
`xiDescent`-zeros are all genuinely off-real encloses a conjugation-symmetric island, so the rung-`1`
winding charge is `0`: reality forces the total order even.  The seam cannot detect a single odd
upper defect. -/
theorem loopCharge_xiDescent_disc_two_eq_zero (c : ℂ) (hc : c.im = 0) {r R : ℝ}
    (hrR : r < R) (hr : 0 < r)
    (t : Finset ℂ) (htU : ∀ w ∈ t, w ∈ Metric.ball c R) (hto : ∀ w ∈ t, xiDescent w = 0)
    (hzeros : ∀ z ∈ Metric.ball c R, xiDescent z = 0 → z ∈ t)
    (hin : ∀ w ∈ t, ‖w - c‖ < r) (hoffreal : ∀ w ∈ t, w.im ≠ 0) :
    loopCharge 1 (fun θ => xiDescent (c + ↑r * exp (I * ↑θ))) 0 (2 * Real.pi) = 0 := by
  rw [loopCharge_xiDescent_disc c hrR hr t htU hzeros hin 1]
  have hcc : (starRingEnd ℂ) c = c := by
    apply Complex.ext
    · rw [Complex.conj_re]
    · rw [Complex.conj_im, hc, neg_zero]
  have hconjmem : ∀ w ∈ t, (starRingEnd ℂ) w ∈ t := by
    intro w hw
    refine hzeros _ ?_ ?_
    · have hnorm : ‖(starRingEnd ℂ) w - c‖ = ‖w - c‖ := by
        rw [show (starRingEnd ℂ) w - c = (starRingEnd ℂ) (w - c) from by rw [map_sub, hcc]]
        exact norm_conj _
      rw [Metric.mem_ball, Complex.dist_eq, hnorm, ← Complex.dist_eq]
      exact Metric.mem_ball.mp (htU w hw)
    · rw [xiDescent_conj, hto w hw, map_zero]
  have hnofix : ∀ w ∈ t, (starRingEnd ℂ) w ≠ w := by
    intro w hw hcw
    refine hoffreal w hw ?_
    have := congrArg Complex.im hcw
    rw [Complex.conj_im] at this
    linarith
  have hord : ∀ w ∈ t, (analyticOrderAt xiDescent ((starRingEnd ℂ) w)).toNat
      = (analyticOrderAt xiDescent w).toNat := fun w _ => by rw [xiDescent_orderAt_conj]
  have hz := seam_charge_two_eq_zero (fun w => (analyticOrderAt xiDescent w).toNat)
    hconjmem hnofix hord
  have hcast : (∑ w ∈ t, ((analyticOrderAt xiDescent w).toNat : ℤ))
      = ((∑ w ∈ t, (analyticOrderAt xiDescent w).toNat : ℕ) : ℤ) := by push_cast; ring
  rw [pow_one, hcast]
  exact hz

/-! ### The s-plane ↔ u-plane winding comparison -/

/-- **The u-plane winding around the descended zero reads the s-plane order.**  For `ρ ∈ rightHalf`,
the winding of `xiDescent` around a small circle about `(ρ − 1/2)²` equals `ord_ρ ξ`. -/
theorem windingNumber_xiDescent_center_sq {ρ : ℂ} (hρ : ρ ∈ rightHalf) :
    ∃ R₀ > 0, ∀ r : ℝ, 0 < r → r < R₀ →
      windingNumber (fun θ => xiDescent ((ρ - (1 / 2 : ℂ)) ^ 2 + ↑r * exp (I * ↑θ)))
          0 (2 * Real.pi) = ((analyticOrderAt xi ρ).toNat : ℤ) := by
  obtain ⟨R₀, hR₀, hw⟩ := windingNumber_xiDescent_zero ((ρ - (1 / 2 : ℂ)) ^ 2)
  refine ⟨R₀, hR₀, fun r hr hrR => ?_⟩
  rw [hw r hr hrR, analyticOrderAt_xiDescent_center_sq hρ]

/-- **The comparison theorem.**  Near an off-line `ξ`-zero `ρ`, the `u`-plane winding of `xiDescent`
around the descended image `(ρ − 1/2)²` equals the `s`-plane winding of `ξ` around `ρ`: the quadrant
winding and the slit winding are the same integer. -/
theorem windingNumber_xiDescent_eq_xi_of_center_sq {ρ : ℂ} (hρ : ρ ∈ rightHalf) :
    ∃ R₀ > 0, ∀ r r' : ℝ, 0 < r → r < R₀ → 0 < r' → r' < R₀ →
      windingNumber (fun θ => xiDescent ((ρ - (1 / 2 : ℂ)) ^ 2 + ↑r * exp (I * ↑θ)))
          0 (2 * Real.pi)
        = windingNumber (fun θ => xi (ρ + ↑r' * exp (I * ↑θ))) 0 (2 * Real.pi) := by
  obtain ⟨R₁, hR₁, hu⟩ := windingNumber_xiDescent_center_sq hρ
  obtain ⟨R₂, hR₂, hs⟩ := windingNumber_xi_zero ρ
  refine ⟨min R₁ R₂, lt_min hR₁ hR₂, fun r r' hr hrR hr' hr'R => ?_⟩
  rw [hu r hr (lt_of_lt_of_le hrR (min_le_left _ _)),
    hs r' hr' (lt_of_lt_of_le hr'R (min_le_right _ _))]

end RHTower
