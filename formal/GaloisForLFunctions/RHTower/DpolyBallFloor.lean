/-
Spreading a single-point floor of the finite Dirichlet carrier to a whole closed ball, and hence to
the annulus charts and boundary circles simultaneously.

The two-dimensional carrier `dpoly2 a s` is holomorphic, and on any right half-plane `Re z ≥ σ₋`
each term `n^{-z}` is Lipschitz with constant `log n · n^{-σ₋}` (mean value inequality for
`z ↦ exp(−(log n) z)` on the convex half-plane). Summing, the carrier itself is Lipschitz there with
constant `∑ |aₙ| · log n · n^{-σ₋}`. A closed ball `closedBall z₀ R` lies in the half-plane
`Re z ≥ z₀.re − R`, so a floor `t₀ < ‖F z₀‖` at the center, together with a variation budget
`(∑ |aₙ| log n · n^{-(z₀.re−R)}) · R ≤ t₀ − ε`, forces `ε < ‖F z‖` on the whole ball by the reverse
triangle inequality. The certificate charts `chartRA ∪ chartLA` and the two boundary circles
`sphere r₀ ∪ sphere R` all sit inside `closedBall ρ₀ R`, so one center floor produces the two
`CarrierFloorOn` data the circle-data pinning gate consumes at once.
-/
import GaloisForLFunctions.RHTower.GNCarrierBridge
import GaloisForLFunctions.RHTower.SecondMoment
import GaloisForLFunctions.RHTower.DeckMultiZero
import GaloisForLFunctions.RHTower.PinnedWindow
import GaloisForLFunctions.RHTower.ScalarCertificate
import GaloisForLFunctions.RHTower.HardyCarrier
import GaloisForLFunctions.RHTower.RouteBOfflineDomination
import GaloisForLFunctions.RHTower.RouteBChiDecay
import GaloisForLFunctions.RHTower.EMCarrier

open Complex Finset Metric

namespace RHTower

/-- **Per-term half-plane Lipschitz bound.** For `1 ≤ n` and two points with real part at least
`σ₋`, `‖n^{-z} − n^{-w}‖ ≤ log n · n^{-σ₋} · ‖z − w‖`. Mean value inequality for the entire function
`v ↦ exp(−(log n) v)` on the convex half-plane `{Re ≥ σ₋}`, where its derivative has norm
`log n · exp(−(log n) Re v) = log n · n^{-Re v} ≤ log n · n^{-σ₋}`. -/
theorem norm_cpow_sub_cpow_le (n : ℕ) (hn : 1 ≤ n) {sm : ℝ} {z w : ℂ}
    (hz : sm ≤ z.re) (hw : sm ≤ w.re) :
    ‖(n : ℂ) ^ (-z) - (n : ℂ) ^ (-w)‖
      ≤ Real.log n * (n : ℝ) ^ (-sm) * ‖z - w‖ := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  set c : ℂ := ((Real.log n : ℝ) : ℂ) with hc
  have hrepr : ∀ u : ℂ, (n : ℂ) ^ (-u) = Complex.exp (-(c * u)) := by
    intro u
    rw [Complex.cpow_def_of_ne_zero hn0,
      show Complex.log (n : ℂ) = c by
        rw [hc, show ((n : ℂ)) = (((n : ℝ)) : ℂ) by push_cast; ring]
        exact (Complex.ofReal_log (le_of_lt hnpos)).symm]
    ring_nf
  have hderiv : ∀ u : ℂ, HasDerivAt (fun v : ℂ => Complex.exp (-(c * v)))
      (Complex.exp (-(c * u)) * (-c)) u := by
    intro u
    have h1 : HasDerivAt (fun v : ℂ => -(c * v)) (-c) u := by
      simpa using ((hasDerivAt_id u).const_mul c).neg
    exact h1.cexp
  have hbound : ∀ u ∈ {v : ℂ | sm ≤ v.re},
      ‖Complex.exp (-(c * u)) * (-c)‖ ≤ Real.log n * (n : ℝ) ^ (-sm) := by
    intro u hu
    rw [norm_mul, norm_neg, Complex.norm_exp]
    have hre : (-(c * u)).re = -(Real.log n * u.re) := by
      rw [hc]
      simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
    rw [hre]
    have hcnorm : ‖c‖ = Real.log n := by
      rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog0]
    rw [hcnorm]
    have hexp : Real.exp (-(Real.log n * u.re)) = (n : ℝ) ^ (-u.re) := by
      rw [Real.rpow_def_of_pos hnpos]; ring_nf
    rw [hexp]
    have hmono : (n : ℝ) ^ (-u.re) ≤ (n : ℝ) ^ (-sm) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (neg_le_neg hu)
    calc (n : ℝ) ^ (-u.re) * Real.log n
        ≤ (n : ℝ) ^ (-sm) * Real.log n :=
          mul_le_mul_of_nonneg_right hmono hlog0
      _ = Real.log n * (n : ℝ) ^ (-sm) := by ring
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun v : ℂ => Complex.exp (-(c * v)))
    (f' := fun u : ℂ => Complex.exp (-(c * u)) * (-c))
    (s := {v : ℂ | sm ≤ v.re}) (C := Real.log n * (n : ℝ) ^ (-sm))
    (fun u _ => (hderiv u).hasDerivWithinAt) hbound
    (convex_halfSpace_re_ge sm) hw hz
  rw [hrepr z, hrepr w]
  exact hmv

/-- **Carrier half-plane Lipschitz bound.** On the half-plane `Re ≥ σ₋`, the finite Dirichlet
carrier changes by at most `(∑ |aₙ| · log n · n^{-σ₋}) · ‖z − w‖`. Termwise sum of the per-term
bound. -/
theorem norm_dpoly2_sub_le (a : ℕ → ℝ) (s : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n)
    {sm : ℝ} {z w : ℂ} (hz : sm ≤ z.re) (hw : sm ≤ w.re) :
    ‖dpoly2 a s z - dpoly2 a s w‖
      ≤ (∑ n ∈ s, |a n| * (Real.log n * (n : ℝ) ^ (-sm))) * ‖z - w‖ := by
  rw [dpoly2, dpoly2, ← Finset.sum_sub_distrib]
  refine le_trans (norm_sum_le _ _) ?_
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro n hn
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc |a n| * ‖(n : ℂ) ^ (-z) - (n : ℂ) ^ (-w)‖
      ≤ |a n| * (Real.log n * (n : ℝ) ^ (-sm) * ‖z - w‖) :=
        mul_le_mul_of_nonneg_left (norm_cpow_sub_cpow_le n (hs n hn) hz hw) (abs_nonneg _)
    _ = |a n| * (Real.log n * (n : ℝ) ^ (-sm)) * ‖z - w‖ := by ring

/-- A point of `closedBall z₀ R` has real part at least `z₀.re − R`, since `|Re(z − z₀)| ≤ ‖z − z₀‖ ≤ R`. -/
theorem re_ge_of_mem_closedBall {z₀ z : ℂ} {R : ℝ} (hz : z ∈ closedBall z₀ R) :
    z₀.re - R ≤ z.re := by
  have h1 : |(z - z₀).re| ≤ ‖z - z₀‖ := Complex.abs_re_le_norm _
  have h2 : ‖z - z₀‖ ≤ R := by rwa [mem_closedBall, dist_eq] at hz
  have h3 : |z.re - z₀.re| ≤ R := by
    rw [show z.re - z₀.re = (z - z₀).re by simp]
    exact le_trans h1 h2
  have := abs_le.mp h3
  linarith [this.1]

/-- **Center floor spreads to the ball.** A floor `t₀ < ‖F z₀‖` at the center of `closedBall z₀ R`,
together with the variation budget `(∑ |aₙ| log n · n^{-(z₀.re−R)}) · R ≤ t₀ − ε`, gives the floor
`ε < ‖F z‖` at every point of the ball. Reverse triangle inequality against the half-plane Lipschitz
bound, with `σ₋ = z₀.re − R` the ball's minimal real part. -/
theorem dpoly2_ball_floor (a : ℕ → ℝ) (s : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n)
    {z₀ : ℂ} {R t₀ ε : ℝ} (hR : 0 ≤ R)
    (hcenter : t₀ < ‖dpoly2 a s z₀‖)
    (hbudget : (∑ n ∈ s, |a n| * (Real.log n * (n : ℝ) ^ (-(z₀.re - R)))) * R ≤ t₀ - ε) :
    ∀ z ∈ closedBall z₀ R, ε < ‖dpoly2 a s z‖ := by
  intro z hz
  set L : ℝ := ∑ n ∈ s, |a n| * (Real.log n * (n : ℝ) ^ (-(z₀.re - R))) with hL
  have hL0 : 0 ≤ L := by
    apply Finset.sum_nonneg
    intro n hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hs n hn
    exact mul_nonneg (abs_nonneg _)
      (mul_nonneg (Real.log_nonneg hn1) (le_of_lt (Real.rpow_pos_of_pos (by linarith) _)))
  have hzre : z₀.re - R ≤ z.re := re_ge_of_mem_closedBall hz
  have hz₀re : z₀.re - R ≤ z₀.re := by linarith
  have hlip := norm_dpoly2_sub_le a s hs hzre hz₀re
  have hdist : ‖z - z₀‖ ≤ R := by rwa [mem_closedBall, dist_eq] at hz
  have hvar : ‖dpoly2 a s z - dpoly2 a s z₀‖ ≤ t₀ - ε := by
    calc ‖dpoly2 a s z - dpoly2 a s z₀‖
        ≤ L * ‖z - z₀‖ := hlip
      _ ≤ L * R := mul_le_mul_of_nonneg_left hdist hL0
      _ ≤ t₀ - ε := hbudget
  have hrev : ‖dpoly2 a s z₀‖ - ‖dpoly2 a s z‖ ≤ ‖dpoly2 a s z₀ - dpoly2 a s z‖ :=
    norm_sub_norm_le _ _
  rw [norm_sub_rev] at hrev
  linarith

/-- A carrier floor on a set restricts to any subset. -/
theorem carrierFloorOn_mono {S S' : Set ℂ} {N : ℕ} {ε : ℝ} (hsub : S' ⊆ S)
    (h : CarrierFloorOn S N ε) : CarrierFloorOn S' N ε :=
  fun z hz => h z (hsub hz)

/-- The annulus charts lie in the closed ball of the same outer radius. -/
theorem charts_subset_closedBall (a : ℂ) (r₀ R : ℝ) :
    chartRA a r₀ R ∪ chartLA a r₀ R ⊆ closedBall a R := by
  intro z hz
  rcases hz with hz | hz
  · exact ball_subset_closedBall hz.2.1
  · exact ball_subset_closedBall hz.2.1

/-- Both boundary circles lie in the closed ball of the outer radius. -/
theorem spheres_subset_closedBall (a : ℂ) {r₀ R : ℝ} (hr₀R : r₀ ≤ R) :
    Metric.sphere a r₀ ∪ Metric.sphere a R ⊆ closedBall a R := by
  intro z hz
  rcases hz with hz | hz
  · exact closedBall_subset_closedBall hr₀R (sphere_subset_closedBall hz)
  · exact sphere_subset_closedBall hz

/-- **Ball `CarrierFloorOn` from a center floor.** A Dirichlet-part floor `t₀ < ‖dirichletPoly N ρ₀‖`
at the center, the variation budget to real part `ρ₀.re − R`, and the reflected χ-term budget on the
ball together give the certificate floor `CarrierFloorOn (closedBall ρ₀ R) N ε`. Composes the ball
spreading of the Dirichlet part (unit coefficients) with the reverse-triangle split of
`gN = D + χ·D(1−·)`. -/
theorem carrierFloorOn_closedBall_of_center (N : ℕ) {ρ₀ : ℂ} {R t₀ t₁ ε : ℝ} (hR : 0 ≤ R)
    (hcenter : t₀ < ‖dirichletPoly N ρ₀‖)
    (hbudget : (∑ n ∈ Finset.Icc 1 N, Real.log n * (n : ℝ) ^ (-(ρ₀.re - R))) * R ≤ t₀ - t₁)
    (hrefl : ∀ z ∈ closedBall ρ₀ R, ‖zetaChi z * dirichletPoly N (1 - z)‖ ≤ t₁ - ε) :
    CarrierFloorOn (closedBall ρ₀ R) N ε := by
  refine carrierFloorOn_of_dirichletPoly_floor N (t₀ := t₁) ?_ hrefl
  have hsum : (∑ n ∈ Finset.Icc 1 N, |(1 : ℝ)| * (Real.log n * (n : ℝ) ^ (-(ρ₀.re - R))))
      = ∑ n ∈ Finset.Icc 1 N, Real.log n * (n : ℝ) ^ (-(ρ₀.re - R)) := by
    apply Finset.sum_congr rfl
    intro n _
    rw [abs_one, one_mul]
  intro z hz
  rw [dirichletPoly_eq_dpoly2]
  refine dpoly2_ball_floor (fun _ => 1) (Finset.Icc 1 N)
    (fun n hn => (Finset.mem_Icc.mp hn).1) (t₀ := t₀) hR ?_ ?_ z hz
  · rw [← dirichletPoly_eq_dpoly2]; exact hcenter
  · rw [hsum]; exact hbudget

/-- **Both circle-gate floor data from one center floor.** The single center floor produces
`CarrierFloorOn` on the annulus charts `chartRA ∪ chartLA` AND on the two boundary circles
`sphere r₀ ∪ sphere R` simultaneously — the exact pair the circle-data pinning gate
`riemannHypothesis_of_emCarrier_pinned_windows_of_circles` consumes — since both sets lie in
`closedBall ρ₀ R`. -/
theorem carrierFloorOn_charts_spheres_of_center (N : ℕ) {ρ₀ : ℂ} {r₀ R t₀ t₁ ε : ℝ}
    (hR : 0 ≤ R) (hr₀R : r₀ ≤ R)
    (hcenter : t₀ < ‖dirichletPoly N ρ₀‖)
    (hbudget : (∑ n ∈ Finset.Icc 1 N, Real.log n * (n : ℝ) ^ (-(ρ₀.re - R))) * R ≤ t₀ - t₁)
    (hrefl : ∀ z ∈ closedBall ρ₀ R, ‖zetaChi z * dirichletPoly N (1 - z)‖ ≤ t₁ - ε) :
    CarrierFloorOn (chartRA ρ₀ r₀ R ∪ chartLA ρ₀ r₀ R) N ε ∧
    CarrierFloorOn (Metric.sphere ρ₀ r₀ ∪ Metric.sphere ρ₀ R) N ε := by
  have hball := carrierFloorOn_closedBall_of_center N hR hcenter hbudget hrefl
  exact ⟨carrierFloorOn_mono (charts_subset_closedBall ρ₀ r₀ R) hball,
    carrierFloorOn_mono (spheres_subset_closedBall ρ₀ hr₀R) hball⟩

/-- **Both circle-gate floors from a critical-line `dpoly` center floor.**  The
native one-dimensional line carrier at height `ρ₀.im` supplies the Dirichlet
center floor whenever `ρ₀.re = 1/2`, then the closed-ball spreading lemma gives
both chart and boundary-circle `CarrierFloorOn` data. -/
theorem carrierFloorOn_charts_spheres_of_line_center (N : ℕ) {ρ₀ : ℂ}
    (hρ₀re : ρ₀.re = 1 / 2) {r₀ R t₀ t₁ ε : ℝ}
    (hR : 0 ≤ R) (hr₀R : r₀ ≤ R)
    (hcenter : t₀ < ‖dpoly (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) (Finset.Icc 1 N) ρ₀.im‖)
    (hbudget : (∑ n ∈ Finset.Icc 1 N, Real.log n * (n : ℝ) ^ (-(ρ₀.re - R))) * R ≤
      t₀ - t₁)
    (hrefl : ∀ z ∈ closedBall ρ₀ R,
      ‖zetaChi z * dirichletPoly N (1 - z)‖ ≤ t₁ - ε) :
    CarrierFloorOn (chartRA ρ₀ r₀ R ∪ chartLA ρ₀ r₀ R) N ε ∧
    CarrierFloorOn (Metric.sphere ρ₀ r₀ ∪ Metric.sphere ρ₀ R) N ε := by
  have hcenterD : t₀ < ‖dirichletPoly N ρ₀‖ := by
    rwa [dirichletPoly_criticalLine_eq N hρ₀re]
  exact carrierFloorOn_charts_spheres_of_center N hR hr₀R hcenterD hbudget hrefl

/-- **Cofinal circle-gate floors from a cofinal line floor.** If the one-dimensional
critical-line carrier exceeds `t₀` cofinally often, and the variation budget to
real part `½ − R` and reflected χ-term budget on each window ball hold, then above
every bound there is a height `τ` at which both the annulus-chart floor and the
boundary-circle floor hold at level `ε`. This is the height-level datum the
circle-data pinning gate turns into RH, once each window center is a simple
on-line carrier zero. -/
theorem window_floor_cofinal_of_line_cofinal (N : ℕ) {r₀ R t₀ t₁ ε : ℝ}
    (hR : 0 ≤ R) (hr₀R : r₀ ≤ R)
    (hbudget : (∑ n ∈ Finset.Icc 1 N, Real.log n * (n : ℝ) ^ (-(1/2 - R))) * R ≤ t₀ - t₁)
    (hline : ∀ M : ℝ, ∃ τ, M < τ ∧
      t₀ < ‖dpoly (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) (Finset.Icc 1 N) τ‖)
    (hrefl : ∀ τ : ℝ, ∀ z ∈ closedBall (((1/2 : ℝ) : ℂ) + (τ : ℂ) * I) R,
      ‖zetaChi z * dirichletPoly N (1 - z)‖ ≤ t₁ - ε) :
    ∀ M : ℝ, ∃ τ, M < τ ∧
      CarrierFloorOn (chartRA (((1/2 : ℝ) : ℂ) + (τ : ℂ) * I) r₀ R
        ∪ chartLA (((1/2 : ℝ) : ℂ) + (τ : ℂ) * I) r₀ R) N ε ∧
      CarrierFloorOn (Metric.sphere (((1/2 : ℝ) : ℂ) + (τ : ℂ) * I) r₀
        ∪ Metric.sphere (((1/2 : ℝ) : ℂ) + (τ : ℂ) * I) R) N ε := by
  intro M
  obtain ⟨τ, hτM, hτfloor⟩ := hline M
  have hre : ((((1/2 : ℝ) : ℂ) + (τ : ℂ) * I)).re = 1/2 := by simp
  refine ⟨τ, hτM, ?_⟩
  refine carrierFloorOn_charts_spheres_of_line_center N (t₀ := t₀) hre hR hr₀R ?_ ?_ (hrefl τ)
  · simpa using hτfloor
  · rw [hre]
    exact hbudget

/-- **Circle-data EM-pinned RH from one line-carrier center floor.**  The explicit
chart and circle `CarrierFloorOn` assumptions of the circle pinning gate are
discharged by one `dpoly` floor at the critical-line center height, the ball
variation budget, and the reflected χ-term budget on the closed ball. -/
theorem riemannHypothesis_of_emCarrier_center_floor_pinned_windows_of_circles
    (hwin : ∀ ρ ∈ rightHalf, xi ρ = 0 →
      ∃ (N M : ℕ) (ε₁ δ t₀ t₁ : ℝ) (h : ℂ → ℂ) (ρ₀ : ℂ) (r₀ R : ℝ),
        1 ≤ M ∧ 0 ≤ ε₁ + δ ∧ 0 ≤ r₀ ∧ r₀ < R ∧ ρ ∈ ball ρ₀ R ∧
        ρ₀.re = 1 / 2 ∧
        (∀ z ∈ closedBall ρ₀ R, 0 < z.re ∧ z.re < 1) ∧
        (∀ z ∈ sphere ρ₀ r₀ ∪ sphere ρ₀ R,
          ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁) ∧
        (∀ z ∈ sphere ρ₀ r₀ ∪ sphere ρ₀ R,
          ‖emCarrier M z - gN N z‖ ≤ δ) ∧
        t₀ < ‖dpoly (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) (Finset.Icc 1 N) ρ₀.im‖ ∧
        (∑ n ∈ Finset.Icc 1 N, Real.log n * (n : ℝ) ^ (-(ρ₀.re - R))) * R ≤
          t₀ - t₁ ∧
        (∀ z ∈ closedBall ρ₀ R,
          ‖zetaChi z * dirichletPoly N (1 - z)‖ ≤ t₁ - 2 * (ε₁ + δ)) ∧
        AnalyticOnNhd ℂ h (ball ρ₀ R) ∧ (∀ z ∈ ball ρ₀ R, h z ≠ 0) ∧
        (∀ z ∈ ball ρ₀ R, completedGN N z = (z - ρ₀) * h z)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_emCarrier_pinned_windows_of_circles
  intro ρ hρ hzero
  obtain ⟨N, M, ε₁, δ, t₀, t₁, h, ρ₀, r₀, R, hM, hεδ, h0, hrR, hρball,
    hρ₀re, hball, hE, hclose, hcenter, hbudget, hrefl, hh, hh0, hfactg⟩ :=
    hwin ρ hρ hzero
  have hR : 0 ≤ R := le_trans h0 hrR.le
  obtain ⟨hF, hFcirc⟩ :=
    carrierFloorOn_charts_spheres_of_line_center N hρ₀re hR hrR.le hcenter hbudget hrefl
  exact ⟨N, M, ε₁, δ, h, ρ₀, r₀, R, hM, hεδ, h0, hrR, hρball,
    hρ₀re, hball, hE, hclose, hF, hFcirc, hh, hh0, hfactg⟩

/-- **Exact-budget same-circle RH from one line-carrier center floor.**  The same
`dpoly` floor at the critical-line center height spreads over the closed ball and
supplies the boundary-circle floor required by the primitive same-circle EM gate,
so the remaining local data are only the carrier-vs-linear bound, the EM/closeness
bounds, and the exact linear-reference budget. -/
theorem riemannHypothesis_of_emCarrier_single_circle_pair_center_floor_windows
    (hwin : ∀ ρ ∈ rightHalf, xi ρ = 0 →
      ∃ (N M : ℕ) (ε₁ δ ηC t₀ t₁ : ℝ) (ρ₀ c : ℂ) (r₀ R : ℝ),
        1 ≤ M ∧ 0 ≤ ε₁ + δ ∧ c ≠ 0 ∧ 0 < r₀ ∧ r₀ < R ∧
        ηC + (1 + ηC) / 2 < 1 ∧ ρ ∈ ball ρ₀ R ∧ ρ₀.re = 1 / 2 ∧
        (∀ z ∈ sphere ρ₀ r₀ ∪ sphere ρ₀ R, 0 < z.re ∧ z ≠ 1) ∧
        (∀ z ∈ sphere ρ₀ r₀ ∪ sphere ρ₀ R,
          ‖completedGN N z - c * (z - ρ₀)‖ ≤ ηC * ‖c * (z - ρ₀)‖) ∧
        (∀ z ∈ sphere ρ₀ r₀ ∪ sphere ρ₀ R,
          ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁) ∧
        (∀ z ∈ sphere ρ₀ r₀ ∪ sphere ρ₀ R,
          ‖emCarrier M z - gN N z‖ ≤ δ) ∧
        t₀ < ‖dpoly (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) (Finset.Icc 1 N) ρ₀.im‖ ∧
        (∑ n ∈ Finset.Icc 1 N, Real.log n * (n : ℝ) ^ (-(ρ₀.re - R))) * R ≤
          t₀ - t₁ ∧
        (∀ z ∈ closedBall ρ₀ R,
          ‖zetaChi z * dirichletPoly N (1 - z)‖ ≤ t₁ - 2 * (ε₁ + δ))) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_emCarrier_single_circle_pair_windows
  intro ρ hρ hzero
  obtain ⟨N, M, ε₁, δ, ηC, t₀, t₁, ρ₀, c, r₀, R, hM, hεδ, hc, h0, hrR,
    hηC, hρball, hρ₀re, hstripCirc, hcarrier, hE, hclose, hcenter, hbudget, hrefl⟩ :=
    hwin ρ hρ hzero
  have hR : 0 ≤ R := le_trans h0.le hrR.le
  obtain ⟨_, hFcirc⟩ :=
    carrierFloorOn_charts_spheres_of_line_center N hρ₀re hR hrR.le hcenter hbudget hrefl
  exact ⟨N, M, ε₁, δ, ηC, ρ₀, c, r₀, R, hM, hεδ, hc, h0, hrR, hηC, hρball,
    hρ₀re, hstripCirc, hcarrier, hE, hclose, hFcirc⟩

end RHTower

namespace RHTower

/-- **Window floors inside every prescribed interval.**  Every interval
`[T, T+U]` on the critical line contains a center whose chart and
boundary-circle carrier floors hold: the second-moment every-window floor
places the center height, and the ball variation and reflected-χ budgets
spread it to the charts and circles.  Certificate windows can therefore be
anchored within `U` of ANY height — the placement the per-zero gates require —
rather than merely cofinally. -/
theorem window_floor_in_every_interval (N : ℕ) {r₀ R t₀ t₁ ε U : ℝ}
    (hR : 0 ≤ R) (hr₀R : r₀ ≤ R) (hU : 0 < U)
    (hdom : t₀ ^ 2 * U
        + ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
            2 * |(m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))|
              / |Real.log n - Real.log m|
      < U * Real.log ((N : ℝ) + 1))
    (hbudget : (∑ n ∈ Finset.Icc 1 N, Real.log n * (n : ℝ) ^ (-(1/2 - R))) * R
      ≤ t₀ - t₁)
    (hrefl : ∀ τ : ℝ, ∀ z ∈ closedBall (((1/2 : ℝ) : ℂ) + (τ : ℂ) * I) R,
      ‖zetaChi z * dirichletPoly N (1 - z)‖ ≤ t₁ - ε) :
    ∀ T : ℝ, ∃ τ ∈ Set.Icc T (T + U),
      CarrierFloorOn (chartRA (((1/2 : ℝ) : ℂ) + (τ : ℂ) * I) r₀ R
        ∪ chartLA (((1/2 : ℝ) : ℂ) + (τ : ℂ) * I) r₀ R) N ε ∧
      CarrierFloorOn (Metric.sphere (((1/2 : ℝ) : ℂ) + (τ : ℂ) * I) r₀
        ∪ Metric.sphere (((1/2 : ℝ) : ℂ) + (τ : ℂ) * I) R) N ε := by
  intro T
  obtain ⟨τ, hτmem, hτfloor⟩ :=
    exists_native_dpoly_floor_in_window N (T := T) hU hdom
  have hre : ((((1/2 : ℝ) : ℂ) + (τ : ℂ) * I)).re = 1/2 := by simp
  refine ⟨τ, hτmem, ?_⟩
  refine carrierFloorOn_charts_spheres_of_line_center N (t₀ := t₀)
    hre hR hr₀R ?_ ?_ (hrefl τ)
  · simpa using hτfloor
  · rw [hre]
    exact hbudget

end RHTower

namespace RHTower

/-- **Reflected-χ ball budget from its boundary circle.**  The reflected term
`χ(z)·D_N(1−z)` is analytic on any closed ball inside the half-plane `Re z < 1`
(the Γ-factor of the reflection stays away from its poles), so the maximum
principle transports its sup bound from the boundary circle to the whole ball. -/
theorem reflected_chi_budget_of_circle {N : ℕ} {ρ₀ : ℂ} {R b : ℝ} (hR : 0 < R)
    (hlt1 : ∀ z ∈ closedBall ρ₀ R, z.re < 1)
    (hcirc : ∀ z ∈ sphere ρ₀ R, ‖zetaChi z * dirichletPoly N (1 - z)‖ ≤ b) :
    ∀ z ∈ closedBall ρ₀ R, ‖zetaChi z * dirichletPoly N (1 - z)‖ ≤ b := by
  have hdan : ∀ z : ℂ, AnalyticAt ℂ (fun w : ℂ => dirichletPoly N (1 - w)) z := by
    intro z
    have hdiff : Differentiable ℂ (dirichletPoly N ∘ fun w : ℂ => 1 - w) :=
      (dirichletPoly_differentiable N).comp
        ((differentiable_const (1 : ℂ)).sub differentiable_id)
    exact (hdiff.differentiableOn.analyticOnNhd isOpen_univ) z (Set.mem_univ z)
  have hfan : ∀ z ∈ closedBall ρ₀ R,
      AnalyticAt ℂ (fun w => zetaChi w * dirichletPoly N (1 - w)) z := by
    intro z hz
    have hGne : Gammaℝ (1 - z) ≠ 0 := by
      apply Gammaℝ_ne_zero_of_re_pos
      rw [Complex.sub_re, Complex.one_re]
      linarith [hlt1 z hz]
    exact (zetaChi_analyticAt hGne).mul (hdan z)
  have hdiffcl : DiffContOnCl ℂ (fun w => zetaChi w * dirichletPoly N (1 - w))
      (ball ρ₀ R) := by
    constructor
    · intro z hz
      exact (hfan z (ball_subset_closedBall hz)).differentiableAt.differentiableWithinAt
    · intro z hz
      rw [closure_ball ρ₀ hR.ne'] at hz
      exact (hfan z hz).continuousAt.continuousWithinAt
  intro z hz
  refine Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball
    hdiffcl ?_ ?_
  · intro w hw
    rw [frontier_ball ρ₀ hR.ne'] at hw
    exact hcirc w hw
  · rw [closure_ball ρ₀ hR.ne']
    exact hz

/-- Points of a closed ball around an on-line center of radius `R < 1/2` stay in
the half-plane `Re z < 1`. -/
theorem re_lt_one_of_mem_closedBall_line {ρ₀ z : ℂ} {R : ℝ}
    (hρ₀re : ρ₀.re = 1 / 2) (hR12 : R < 1 / 2) (hz : z ∈ closedBall ρ₀ R) :
    z.re < 1 := by
  have h1 : |(z - ρ₀).re| ≤ ‖z - ρ₀‖ := Complex.abs_re_le_norm _
  have h2 : ‖z - ρ₀‖ ≤ R := by rwa [mem_closedBall, dist_eq] at hz
  have h3 := (abs_le.mp (le_trans h1 h2)).2
  rw [Complex.sub_re] at h3
  rw [hρ₀re] at h3
  linarith

/-- **Fully one-dimensional same-circle RH gate.**  The exact-budget same-circle
EM route with every per-zero datum one-dimensional: circle data for the
carrier-vs-linear, EM and closeness bounds, one `dpoly` center floor on the
line, the scalar variation budget, and the reflected-χ budget on the boundary
circle only — the maximum principle supplies the ball budget internally. -/
theorem riemannHypothesis_of_emCarrier_single_circle_pair_center_floor_circle_windows
    (hwin : ∀ ρ ∈ rightHalf, xi ρ = 0 →
      ∃ (N M : ℕ) (ε₁ δ ηC t₀ t₁ : ℝ) (ρ₀ c : ℂ) (r₀ R : ℝ),
        1 ≤ M ∧ 0 ≤ ε₁ + δ ∧ c ≠ 0 ∧ 0 < r₀ ∧ r₀ < R ∧ R < 1 / 2 ∧
        ηC + (1 + ηC) / 2 < 1 ∧ ρ ∈ ball ρ₀ R ∧ ρ₀.re = 1 / 2 ∧
        (∀ z ∈ sphere ρ₀ r₀ ∪ sphere ρ₀ R, 0 < z.re ∧ z ≠ 1) ∧
        (∀ z ∈ sphere ρ₀ r₀ ∪ sphere ρ₀ R,
          ‖completedGN N z - c * (z - ρ₀)‖ ≤ ηC * ‖c * (z - ρ₀)‖) ∧
        (∀ z ∈ sphere ρ₀ r₀ ∪ sphere ρ₀ R,
          ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁) ∧
        (∀ z ∈ sphere ρ₀ r₀ ∪ sphere ρ₀ R,
          ‖emCarrier M z - gN N z‖ ≤ δ) ∧
        t₀ < ‖dpoly (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) (Finset.Icc 1 N) ρ₀.im‖ ∧
        (∑ n ∈ Finset.Icc 1 N, Real.log n * (n : ℝ) ^ (-(ρ₀.re - R))) * R ≤
          t₀ - t₁ ∧
        (∀ z ∈ Metric.sphere ρ₀ R,
          ‖zetaChi z * dirichletPoly N (1 - z)‖ ≤ t₁ - 2 * (ε₁ + δ))) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_emCarrier_single_circle_pair_center_floor_windows
  intro ρ hρ hzero
  obtain ⟨N, M, ε₁, δ, ηC, t₀, t₁, ρ₀, c, r₀, R, hM, hεδ, hc, h0, hrR, hR12,
    hηC, hρball, hρ₀re, hstripCirc, hcarrier, hE, hclose, hcenter, hbudget,
    hreflcirc⟩ := hwin ρ hρ hzero
  have hR : 0 < R := lt_trans h0 hrR
  have hrefl := reflected_chi_budget_of_circle hR
    (fun z hz => re_lt_one_of_mem_closedBall_line hρ₀re hR12 hz) hreflcirc
  exact ⟨N, M, ε₁, δ, ηC, t₀, t₁, ρ₀, c, r₀, R, hM, hεδ, hc, h0, hrR, hηC,
    hρball, hρ₀re, hstripCirc, hcarrier, hE, hclose, hcenter, hbudget, hrefl⟩

end RHTower

namespace RHTower

/-- **`gN` center anchor from a critical-line `dpoly` floor.**  At a known
critical-line center, a line-Dirichlet floor and a reflected-term budget upgrade
the second-moment anchor to the exact scalar hypothesis `m_J ≤ ‖gN N c‖`
consumed by `ScalarCertificate.lean`. -/
theorem gN_line_anchor_of_dpoly_floor (N : ℕ) {τ t₀ m_J : ℝ}
    (hline : t₀ < ‖dpoly (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) (Finset.Icc 1 N) τ‖)
    (hrefl : ‖zetaChi (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) *
        dirichletPoly N (1 - (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I))‖ ≤ t₀ - m_J) :
    m_J ≤ ‖gN N (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ := by
  let c : ℂ := ((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I
  have hre : c.re = 1 / 2 := by simp [c]
  have him : c.im = τ := by simp [c]
  have hD : t₀ < ‖dirichletPoly N c‖ := by
    rw [dirichletPoly_criticalLine_eq N hre, him]
    exact hline
  have hgn : gN N c = dirichletPoly N c + zetaChi c * dirichletPoly N (1 - c) := rfl
  have key : ‖dirichletPoly N c‖ ≤ ‖gN N c‖ + ‖zetaChi c * dirichletPoly N (1 - c)‖ := by
    rw [hgn]
    exact norm_le_add_norm_add _ _
  change m_J ≤ ‖gN N c‖
  linarith

/-- **Every-window `gN` center anchor from the banked second moment.**  If the
explicit second-moment domination inequality gives a line floor in every window,
and the reflected center term is below the reserve `t₀ - m_J` at every such
center, then every interval `[T,T+U]` contains a critical-line center satisfying
the `ScalarCertificate` anchor `m_J ≤ ‖gN N c‖`. -/
theorem exists_gN_line_anchor_in_window_of_secondMoment
    (N : ℕ) {U t₀ m_J : ℝ} (hU : 0 < U)
    (hdom : t₀ ^ 2 * U
        + ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
            2 * |(m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))|
              / |Real.log n - Real.log m|
      < U * Real.log ((N : ℝ) + 1))
    (hrefl : ∀ τ : ℝ,
      ‖zetaChi (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) *
          dirichletPoly N (1 - (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I))‖ ≤ t₀ - m_J) :
    ∀ T : ℝ, ∃ τ ∈ Set.Icc T (T + U),
      m_J ≤ ‖gN N (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ := by
  intro T
  obtain ⟨τ, hτ, hfloor⟩ := exists_native_dpoly_floor_in_window N (T := T) hU hdom
  exact ⟨τ, hτ, gN_line_anchor_of_dpoly_floor N hfloor (hrefl τ)⟩

end RHTower

namespace RHTower

/-- **Cross-slope center certificate from a critical-line `dpoly` floor.**  The sharpened
center-floor scalar gate no longer needs the `gN` anchor as primitive data when the known center is
on the critical line: a one-dimensional `dpoly` floor and the reflected center reserve produce
`m_J ≤ ‖gN N c‖`, and the rest of the certificate is the cross-multiplied scalar surface. -/
theorem xi_window_pinned_of_line_floor_cross_slope
    {N M : ℕ} (hM : 1 ≤ M) {ε₁ δ : ℝ} (hεδ : 0 ≤ ε₁ + δ)
    {τ t₀ t₁ t₂ rz r₀ R P rJ RJ m_J M_J M_G a₀ : ℝ}
    (ht₁ : 0 < t₁) (h12 : t₁ ≤ t₂) (hrz0 : 0 < rz)
    (h0 : 0 < r₀) (hrR : r₀ < R) (hRP : R ≤ P)
    (hPrz : P + rz ≤ RJ) (hRrzJ : R + rz < rJ) (hrJR : rJ < RJ)
    (hstrip : ∀ z ∈ closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
      0 < z.re ∧ z.re < 1)
    (hbr : ∀ u ∈ Set.Icc t₁ t₂,
      ((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I ∈
        closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) rz)
    (hsign : (completedGN N (((1 / 2 : ℝ) : ℂ) + (t₁ : ℂ) * I)).re
      * (completedGN N (((1 / 2 : ℝ) : ℂ) + (t₂ : ℂ) * I)).re ≤ 0)
    (hmJ0 : 0 < m_J)
    (hline : t₀ < ‖dpoly (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) (Finset.Icc 1 N) τ‖)
    (hrefl : ‖zetaChi (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) *
        dirichletPoly N (1 - (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I))‖ ≤ t₀ - m_J)
    (hMJ : 1 ≤ M_J)
    (hbound : ∀ z ∈ sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
      ‖gN N z‖ ≤ M_J)
    (hjensen_floor : Real.log (M_J / m_J) / Real.log (RJ / rJ) < 2)
    (hengine : m_J / rz < M_J / (rJ - rz))
    (ha₀ : ∀ z : ℂ, z.re = 1 / 2 →
      z ∈ closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) rz → a₀ ≤ ‖archFactor z‖)
    (ha₀0 : 0 < a₀)
    (hMG : ∀ z ∈ closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
      ‖completedGN N z‖ ≤ M_G)
    (hcross : 6 * R * M_G < P ^ 2 * (a₀ * ((m_J / rz) * Real.exp
      (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * rz / (rJ - rz))))))
    (hE : ∀ z ∈ closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
      ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁)
    (hclose : ∀ z ∈ closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
      ‖emCarrier M z - gN N z‖ ≤ δ)
    (hfl : 2 * (ε₁ + δ) < r₀ * ((m_J / rz) * Real.exp
      (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * (R + rz) /
        (rJ - (R + rz)))))) :
    ∃ ρ' : ℂ, ρ'.re = 1 / 2 ∧
      ρ' ∈ closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) rz ∧
      ∀ p ∈ ball ρ' R, xi p = 0 → p.re = 1 / 2 := by
  have hmJ : m_J ≤ ‖gN N (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ :=
    gN_line_anchor_of_dpoly_floor N hline hrefl
  exact xi_window_pinned_of_center_floor_cross_slope hM hεδ ht₁ h12 hrz0 h0 hrR hRP
    hPrz hRrzJ hrJR hstrip hbr hsign hmJ0 hmJ hMJ hbound hjensen_floor hengine
    ha₀ ha₀0 hMG hcross hE hclose hfl

/-- **RH gate from line-floor cross-slope scalar windows.**  This feeds the banked
one-dimensional `dpoly` floor language into the newest center-floor scalar certificate: every
window supplies a critical-line center height `τ`, a line-carrier floor, a reflected center
reserve, known-center sups, and the cross-multiplied canonical scalar budgets. -/
theorem riemannHypothesis_of_line_floor_cross_slope_windows
    (hwin : ∀ ρ ∈ rightHalf, xi ρ = 0 →
      ∃ (N M : ℕ) (ε₁ δ : ℝ)
        (τ t₀ t₁ t₂ rz r₀ R R' P rJ RJ m_J M_J M_G a₀ : ℝ),
        1 ≤ M ∧ 0 ≤ ε₁ + δ ∧
        0 < t₁ ∧ t₁ ≤ t₂ ∧ 0 < rz ∧
        0 < r₀ ∧ r₀ < R ∧ R ≤ P ∧
        P + rz ≤ RJ ∧ R + rz < rJ ∧ rJ < RJ ∧
        ρ ∈ ball (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) R' ∧ R' + rz ≤ R ∧
        (∀ z ∈ closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          0 < z.re ∧ z.re < 1) ∧
        (∀ u ∈ Set.Icc t₁ t₂,
          ((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I ∈
            closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) rz) ∧
        (completedGN N (((1 / 2 : ℝ) : ℂ) + (t₁ : ℂ) * I)).re
          * (completedGN N (((1 / 2 : ℝ) : ℂ) + (t₂ : ℂ) * I)).re ≤ 0 ∧
        0 < m_J ∧
        t₀ < ‖dpoly (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) (Finset.Icc 1 N) τ‖ ∧
        ‖zetaChi (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) *
          dirichletPoly N (1 - (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I))‖ ≤ t₀ - m_J ∧
        1 ≤ M_J ∧
        (∀ z ∈ sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ, ‖gN N z‖ ≤ M_J) ∧
        Real.log (M_J / m_J) / Real.log (RJ / rJ) < 2 ∧
        m_J / rz < M_J / (rJ - rz) ∧
        (∀ z : ℂ, z.re = 1 / 2 →
          z ∈ closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) rz →
          a₀ ≤ ‖archFactor z‖) ∧
        0 < a₀ ∧
        (∀ z ∈ closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖completedGN N z‖ ≤ M_G) ∧
        6 * R * M_G < P ^ 2 * (a₀ * ((m_J / rz) * Real.exp
          (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * rz / (rJ - rz))))) ∧
        (∀ z ∈ closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁) ∧
        (∀ z ∈ closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖emCarrier M z - gN N z‖ ≤ δ) ∧
        2 * (ε₁ + δ) < r₀ * ((m_J / rz) * Real.exp
          (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * (R + rz) /
            (rJ - (R + rz)))))) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_center_floor_cross_slope_windows
  intro ρ hρ hzero
  obtain ⟨N, M, ε₁, δ, τ, t₀, t₁, t₂, rz, r₀, R, R', P, rJ, RJ, m_J,
    M_J, M_G, a₀, hM, hεδ, ht₁, h12, hrz0, h0, hrR, hRP, hPrz, hRrzJ,
    hrJR, hρR', hR'rz, hstrip, hbr, hsign, hmJ0, hline, hrefl, hMJ,
    hbound, hjensen_floor, hengine, ha₀, ha₀0, hMG, hcross, hE, hclose, hfl⟩ :=
    hwin ρ hρ hzero
  have hmJ : m_J ≤ ‖gN N (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ :=
    gN_line_anchor_of_dpoly_floor N hline hrefl
  refine ⟨N, M, ε₁, δ, ((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I, t₁, t₂, rz, r₀,
    R, R', P, rJ, RJ, m_J, M_J, M_G, a₀, ?_⟩
  exact ⟨hM, hεδ, ht₁, h12, hrz0, h0, hrR, hRP, hPrz, hRrzJ, hrJR,
    hρR', hR'rz, hstrip, hbr, hsign, hmJ0, hmJ, hMJ, hbound, hjensen_floor,
    hengine, ha₀, ha₀0, hMG, hcross, hE, hclose, hfl⟩

end RHTower

namespace RHTower

/-- **RH gate from second-moment-selected line-floor cross-slope windows.**  The center height is
no longer a primitive witness.  In every prescribed interval `[T,T+U]`, the banked second-moment
floor selects a height `τ`; the remaining center-scalar, circle, sign, EM, and cross-slope data are
assumed uniformly across that interval and are then evaluated at the selected center. -/
theorem riemannHypothesis_of_secondMoment_line_floor_cross_slope_windows
    (hwin : ∀ ρ ∈ rightHalf, xi ρ = 0 →
      ∃ (N M : ℕ) (ε₁ δ : ℝ)
        (T U t₀ t₁ t₂ rz r₀ R R' P rJ RJ m_J M_J M_G a₀ : ℝ),
        1 ≤ M ∧ 0 ≤ ε₁ + δ ∧
        0 < U ∧
        t₀ ^ 2 * U
          + ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
              2 * |(m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))|
                / |Real.log n - Real.log m|
        < U * Real.log ((N : ℝ) + 1) ∧
        0 < t₁ ∧ t₁ ≤ t₂ ∧ 0 < rz ∧
        0 < r₀ ∧ r₀ < R ∧ R ≤ P ∧
        P + rz ≤ RJ ∧ R + rz < rJ ∧ rJ < RJ ∧
        (∀ τ ∈ Set.Icc T (T + U),
          ρ ∈ ball (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) R') ∧
        R' + rz ≤ R ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          0 < z.re ∧ z.re < 1) ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ u ∈ Set.Icc t₁ t₂,
          ((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I ∈
            closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) rz) ∧
        (completedGN N (((1 / 2 : ℝ) : ℂ) + (t₁ : ℂ) * I)).re
          * (completedGN N (((1 / 2 : ℝ) : ℂ) + (t₂ : ℂ) * I)).re ≤ 0 ∧
        0 < m_J ∧
        (∀ τ ∈ Set.Icc T (T + U),
          ‖zetaChi (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) *
            dirichletPoly N (1 - (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I))‖ ≤ t₀ - m_J) ∧
        1 ≤ M_J ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ, ‖gN N z‖ ≤ M_J) ∧
        Real.log (M_J / m_J) / Real.log (RJ / rJ) < 2 ∧
        m_J / rz < M_J / (rJ - rz) ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z : ℂ, z.re = 1 / 2 →
          z ∈ closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) rz →
          a₀ ≤ ‖archFactor z‖) ∧
        0 < a₀ ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖completedGN N z‖ ≤ M_G) ∧
        6 * R * M_G < P ^ 2 * (a₀ * ((m_J / rz) * Real.exp
          (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * rz / (rJ - rz))))) ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁) ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖emCarrier M z - gN N z‖ ≤ δ) ∧
        2 * (ε₁ + δ) < r₀ * ((m_J / rz) * Real.exp
          (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * (R + rz) /
            (rJ - (R + rz)))))) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_line_floor_cross_slope_windows
  intro ρ hρ hzero
  obtain ⟨N, M, ε₁, δ, T, U, t₀, t₁, t₂, rz, r₀, R, R', P, rJ, RJ,
    m_J, M_J, M_G, a₀, hM, hεδ, hU, hdom, ht₁, h12, hrz0, h0, hrR, hRP,
    hPrz, hRrzJ, hrJR, hρR', hR'rz, hstrip, hbr, hsign, hmJ0, hrefl,
    hMJ, hbound, hjensen_floor, hengine, ha₀, ha₀0, hMG, hcross, hE,
    hclose, hfl⟩ := hwin ρ hρ hzero
  obtain ⟨τ, hτ, hline⟩ := exists_native_dpoly_floor_in_window N (T := T) hU hdom
  refine ⟨N, M, ε₁, δ, τ, t₀, t₁, t₂, rz, r₀, R, R', P, rJ, RJ, m_J,
    M_J, M_G, a₀, ?_⟩
  exact ⟨hM, hεδ, ht₁, h12, hrz0, h0, hrR, hRP, hPrz, hRrzJ, hrJR,
    hρR' τ hτ, hR'rz, hstrip τ hτ, hbr τ hτ, hsign, hmJ0, hline, hrefl τ hτ,
    hMJ, hbound τ hτ, hjensen_floor, hengine, ha₀ τ hτ, ha₀0, hMG τ hτ,
    hcross, hE τ hτ, hclose τ hτ, hfl⟩

end RHTower

namespace RHTower

/-- **Two-sided strip containment for critical-line center balls.**  A closed ball centered at
`1/2 + iτ` with radius `< 1/2` lies inside the strip `0 < Re z < 1`. -/
theorem line_center_closedBall_strip {τ RJ : ℝ} (hRJ : RJ < 1 / 2) :
    ∀ z ∈ closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
      0 < z.re ∧ z.re < 1 := by
  intro z hz
  have hdist : ‖z - (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ ≤ RJ := by
    rw [← dist_eq_norm]
    exact mem_closedBall.mp hz
  have hre_abs : |z.re - 1 / 2| ≤ RJ := by
    calc |z.re - 1 / 2|
        = |(z - (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)).re| := by simp [sub_re]
      _ ≤ ‖z - (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ := Complex.abs_re_le_norm _
      _ ≤ RJ := hdist
  have hle : z.re - 1 / 2 ≤ RJ := (abs_le.mp hre_abs).2
  have hge : -RJ ≤ z.re - 1 / 2 := (abs_le.mp hre_abs).1
  exact ⟨by linarith, by linarith⟩

/-- Exact norm-square formula on the critical-line parametrization. -/
theorem linePt_norm_sq (τ : ℝ) : ‖linePt τ‖ ^ 2 = (1 / 2 : ℝ) ^ 2 + τ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq]
  unfold linePt
  simp [Complex.normSq]
  ring

/-- On the critical line, the point norm is monotone in the height modulus. -/
theorem linePt_norm_mono_abs {u v : ℝ} (h : |u| ≤ |v|) : ‖linePt u‖ ≤ ‖linePt v‖ := by
  have hsq_uv : u ^ 2 ≤ v ^ 2 := sq_le_sq.mpr h
  have hsq : ‖linePt u‖ ^ 2 ≤ ‖linePt v‖ ^ 2 := by
    rw [linePt_norm_sq, linePt_norm_sq]
    nlinarith
  have habs := sq_le_sq.mp hsq
  simpa [abs_of_nonneg (norm_nonneg (linePt u)), abs_of_nonneg (norm_nonneg (linePt v))]
    using habs

/-- A height inside a real interval has modulus bounded by the larger endpoint modulus. -/
theorem abs_le_max_abs_endpoints_of_mem_Icc {A B τ : ℝ} (hτ : τ ∈ Set.Icc A B) :
    |τ| ≤ max |A| |B| := by
  apply abs_le.mpr
  constructor
  · have hA : -|A| ≤ A := neg_abs_le A
    have hmaxA : |A| ≤ max |A| |B| := le_max_left _ _
    linarith [hτ.1]
  · have hB : B ≤ |B| := le_abs_self B
    have hmaxB : |B| ≤ max |A| |B| := le_max_right _ _
    linarith [hτ.2]

/-- The critical-line point norm on a window is bounded by the larger endpoint norm. -/
theorem linePt_norm_le_endpoint_max {T U τ : ℝ} (hτ : τ ∈ Set.Icc T (T + U)) :
    ‖linePt τ‖ ≤ max ‖linePt T‖ ‖linePt (T + U)‖ := by
  have habs := abs_le_max_abs_endpoints_of_mem_Icc hτ
  by_cases hTU : |T| ≤ |T + U|
  · have hτ_abs : |τ| ≤ |T + U| := by
      simpa [max_eq_right hTU] using habs
    exact le_trans (linePt_norm_mono_abs hτ_abs) (le_max_right _ _)
  · have hUT : |T + U| ≤ |T| := le_of_not_ge hTU
    have hτ_abs : |τ| ≤ |T| := by
      simpa [max_eq_left hUT] using habs
    exact le_trans (linePt_norm_mono_abs hτ_abs) (le_max_left _ _)

/-- A concrete point on the critical-line circle of radius `RJ`. -/
theorem linePt_add_radius_mem_sphere {τ RJ : ℝ} (hRJ0 : 0 ≤ RJ) :
    linePt τ + (RJ : ℂ) ∈ sphere (linePt τ) RJ := by
  rw [mem_sphere, dist_eq_norm]
  have hsub : linePt τ + (RJ : ℂ) - linePt τ = (RJ : ℂ) := by ring
  rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hRJ0]

/-- A single endpoint-max scalar controls the Euler-Maclaurin remainder majorant on every
critical-line disk in the window. -/
theorem em_remainder_norm_le_window_closedBall_of_endpoint_bound {M : ℕ} {T U RJ ε₁ : ℝ}
    (hM : 1 ≤ M) (hRJ12 : RJ < 1 / 2)
    (hbudget : (max ‖linePt T‖ ‖linePt (T + U)‖ + RJ) *
      (M : ℝ) ^ (-(1 / 2 - RJ)) / (1 / 2 - RJ) ≤ ε₁) :
    ∀ τ ∈ Set.Icc T (T + U), ∀ z ∈ closedBall (linePt τ) RJ,
      ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁ := by
  intro τ hτ
  have hden0 : 0 < 1 / 2 - RJ := by linarith
  have hpow_nonneg : 0 ≤ (M : ℝ) ^ (-(1 / 2 - RJ)) :=
    Real.rpow_nonneg (Nat.cast_nonneg M) _
  have hcenter_le : ‖linePt τ‖ + RJ ≤ max ‖linePt T‖ ‖linePt (T + U)‖ + RJ := by
    exact add_le_add (linePt_norm_le_endpoint_max hτ) le_rfl
  have hmul : (‖linePt τ‖ + RJ) * (M : ℝ) ^ (-(1 / 2 - RJ)) ≤
      (max ‖linePt T‖ ‖linePt (T + U)‖ + RJ) *
        (M : ℝ) ^ (-(1 / 2 - RJ)) := by
    exact mul_le_mul_of_nonneg_right hcenter_le hpow_nonneg
  have hbudgetτ : (‖linePt τ‖ + RJ) * (M : ℝ) ^ (-(1 / 2 - RJ)) /
      (1 / 2 - RJ) ≤ ε₁ := by
    exact le_trans (div_le_div_of_nonneg_right hmul hden0.le) hbudget
  intro z hz
  exact em_remainder_norm_le_line_closedBall_of_center_bound
    (M := M) (τ := τ) (RJ := RJ) (ε₁ := ε₁) hM hRJ12 (by simpa [linePt] using hbudgetτ)
    z (by simpa [linePt] using hz)

/-- A point with real part `1/2` is the critical-line parametrization at its imaginary part. -/
theorem eq_linePt_of_re_eq_half {z : ℂ} (hzre : z.re = 1 / 2) :
    z = linePt z.im := by
  apply Complex.ext
  · rw [hzre, linePt_re]
  · unfold linePt
    simp

/-- If a critical-line point lies in an `rz`-ball around a center height in `[T,T+U]`, its height
lies in the expanded segment `[T-rz,T+U+rz]`. -/
theorem im_mem_expanded_window_of_mem_line_center_closedBall
    {T U τ rz : ℝ} {z : ℂ} (hτ : τ ∈ Set.Icc T (T + U))
    (hz : z ∈ closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) rz) :
    z.im ∈ Set.Icc (T - rz) (T + U + rz) := by
  have hdist : ‖z - (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ ≤ rz := by
    rw [← dist_eq_norm]
    exact mem_closedBall.mp hz
  have him_abs : |z.im - τ| ≤ rz := by
    calc |z.im - τ|
        = |(z - (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)).im| := by
            simp [sub_im]
      _ ≤ ‖z - (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ := Complex.abs_im_le_norm _
      _ ≤ rz := hdist
  have him_low : -rz ≤ z.im - τ := (abs_le.mp him_abs).1
  have him_high : z.im - τ ≤ rz := (abs_le.mp him_abs).2
  exact ⟨by linarith [hτ.1, him_low], by linarith [hτ.2, him_high]⟩

/-- **RH gate from second-moment-selected windows with automatic strip containment.**  This is
`riemannHypothesis_of_secondMoment_line_floor_cross_slope_windows` with the uniform strip hypothesis
replaced by the scalar radius condition `RJ < 1/2` for critical-line centers. -/
theorem riemannHypothesis_of_secondMoment_line_floor_cross_slope_windows_of_radius_strip
    (hwin : ∀ ρ ∈ rightHalf, xi ρ = 0 →
      ∃ (N M : ℕ) (ε₁ δ : ℝ)
        (T U t₀ t₁ t₂ rz r₀ R R' P rJ RJ m_J M_J M_G a₀ : ℝ),
        1 ≤ M ∧ 0 ≤ ε₁ + δ ∧
        0 < U ∧
        t₀ ^ 2 * U
          + ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
              2 * |(m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))|
                / |Real.log n - Real.log m|
        < U * Real.log ((N : ℝ) + 1) ∧
        0 < t₁ ∧ t₁ ≤ t₂ ∧ 0 < rz ∧
        0 < r₀ ∧ r₀ < R ∧ R ≤ P ∧
        P + rz ≤ RJ ∧ R + rz < rJ ∧ rJ < RJ ∧ RJ < 1 / 2 ∧
        (∀ τ ∈ Set.Icc T (T + U),
          ρ ∈ ball (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) R') ∧
        R' + rz ≤ R ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ u ∈ Set.Icc t₁ t₂,
          ((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I ∈
            closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) rz) ∧
        (completedGN N (((1 / 2 : ℝ) : ℂ) + (t₁ : ℂ) * I)).re
          * (completedGN N (((1 / 2 : ℝ) : ℂ) + (t₂ : ℂ) * I)).re ≤ 0 ∧
        0 < m_J ∧
        (∀ τ ∈ Set.Icc T (T + U),
          ‖zetaChi (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) *
            dirichletPoly N (1 - (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I))‖ ≤ t₀ - m_J) ∧
        1 ≤ M_J ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ, ‖gN N z‖ ≤ M_J) ∧
        Real.log (M_J / m_J) / Real.log (RJ / rJ) < 2 ∧
        m_J / rz < M_J / (rJ - rz) ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z : ℂ, z.re = 1 / 2 →
          z ∈ closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) rz →
          a₀ ≤ ‖archFactor z‖) ∧
        0 < a₀ ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖completedGN N z‖ ≤ M_G) ∧
        6 * R * M_G < P ^ 2 * (a₀ * ((m_J / rz) * Real.exp
          (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * rz / (rJ - rz))))) ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁) ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖emCarrier M z - gN N z‖ ≤ δ) ∧
        2 * (ε₁ + δ) < r₀ * ((m_J / rz) * Real.exp
          (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * (R + rz) /
            (rJ - (R + rz)))))) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_secondMoment_line_floor_cross_slope_windows
  intro ρ hρ hzero
  obtain ⟨N, M, ε₁, δ, T, U, t₀, t₁, t₂, rz, r₀, R, R', P, rJ, RJ,
    m_J, M_J, M_G, a₀, hM, hεδ, hU, hdom, ht₁, h12, hrz0, h0, hrR, hRP,
    hPrz, hRrzJ, hrJR, hRJ12, hρR', hR'rz, hbr, hsign, hmJ0, hrefl, hMJ,
    hbound, hjensen_floor, hengine, ha₀, ha₀0, hMG, hcross, hE, hclose, hfl⟩ :=
    hwin ρ hρ hzero
  refine ⟨N, M, ε₁, δ, T, U, t₀, t₁, t₂, rz, r₀, R, R', P, rJ, RJ,
    m_J, M_J, M_G, a₀, ?_⟩
  exact ⟨hM, hεδ, hU, hdom, ht₁, h12, hrz0, h0, hrR, hRP, hPrz, hRrzJ,
    hrJR, hρR', hR'rz, (fun τ _ => line_center_closedBall_strip hRJ12), hbr,
    hsign, hmJ0, hrefl, hMJ, hbound, hjensen_floor, hengine, ha₀, ha₀0, hMG,
    hcross, hE, hclose, hfl⟩

end RHTower

namespace RHTower

/-- **Critical-line height distance as a center-ball certificate.**  If two line heights differ by
at most `rz`, then the corresponding critical-line point lies in the `rz`-ball around the other. -/
theorem line_point_mem_closedBall_line_center_of_abs_sub_le {τ u rz : ℝ}
    (h : |u - τ| ≤ rz) :
    ((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I ∈
      closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) rz := by
  rw [mem_closedBall, dist_eq_norm]
  have hnorm : ‖(((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I) -
      (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ = |u - τ| := by
    rw [show (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I) -
        (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) = I * ((u - τ : ℝ) : ℂ) by
          apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]]
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  rwa [hnorm]

/-- **Uniform bracket containment from endpoint inequalities.**  If every possible selected center
height lies in `[T,T+U]` and the bracket interval `[t₁,t₂]` lies in the common overlap
`[T+U-rz, T+rz]`, then the entire bracket is inside every selected center ball. -/
theorem line_interval_mem_closedBall_line_center_of_endpoint_bounds
    {T U t₁ t₂ rz τ u : ℝ}
    (hlo : T + U - rz ≤ t₁) (hhi : t₂ ≤ T + rz)
    (hτ : τ ∈ Set.Icc T (T + U)) (hu : u ∈ Set.Icc t₁ t₂) :
    ((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I ∈
      closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) rz := by
  have habs : |u - τ| ≤ rz := by
    rw [abs_le]
    constructor <;> linarith [hτ.1, hτ.2, hu.1, hu.2]
  exact line_point_mem_closedBall_line_center_of_abs_sub_le habs

/-- **RH gate with automatic strip and bracket geometry.**  This removes the raw bracket-containment
hypothesis from the second-moment-selected scalar gate: the endpoint inequalities
`T+U-rz ≤ t₁` and `t₂ ≤ T+rz` certify that the full sign bracket lies inside every possible selected
center ball. -/
theorem riemannHypothesis_of_secondMoment_line_floor_cross_slope_windows_of_radius_strip_interval_bracket
    (hwin : ∀ ρ ∈ rightHalf, xi ρ = 0 →
      ∃ (N M : ℕ) (ε₁ δ : ℝ)
        (T U t₀ t₁ t₂ rz r₀ R R' P rJ RJ m_J M_J M_G a₀ : ℝ),
        1 ≤ M ∧ 0 ≤ ε₁ + δ ∧
        0 < U ∧
        t₀ ^ 2 * U
          + ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
              2 * |(m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))|
                / |Real.log n - Real.log m|
        < U * Real.log ((N : ℝ) + 1) ∧
        0 < t₁ ∧ t₁ ≤ t₂ ∧ 0 < rz ∧
        0 < r₀ ∧ r₀ < R ∧ R ≤ P ∧
        P + rz ≤ RJ ∧ R + rz < rJ ∧ rJ < RJ ∧ RJ < 1 / 2 ∧
        (∀ τ ∈ Set.Icc T (T + U),
          ρ ∈ ball (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) R') ∧
        R' + rz ≤ R ∧
        T + U - rz ≤ t₁ ∧ t₂ ≤ T + rz ∧
        (completedGN N (((1 / 2 : ℝ) : ℂ) + (t₁ : ℂ) * I)).re
          * (completedGN N (((1 / 2 : ℝ) : ℂ) + (t₂ : ℂ) * I)).re ≤ 0 ∧
        0 < m_J ∧
        (∀ τ ∈ Set.Icc T (T + U),
          ‖zetaChi (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) *
            dirichletPoly N (1 - (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I))‖ ≤ t₀ - m_J) ∧
        1 ≤ M_J ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ, ‖gN N z‖ ≤ M_J) ∧
        Real.log (M_J / m_J) / Real.log (RJ / rJ) < 2 ∧
        m_J / rz < M_J / (rJ - rz) ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z : ℂ, z.re = 1 / 2 →
          z ∈ closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) rz →
          a₀ ≤ ‖archFactor z‖) ∧
        0 < a₀ ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖completedGN N z‖ ≤ M_G) ∧
        6 * R * M_G < P ^ 2 * (a₀ * ((m_J / rz) * Real.exp
          (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * rz / (rJ - rz))))) ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁) ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖emCarrier M z - gN N z‖ ≤ δ) ∧
        2 * (ε₁ + δ) < r₀ * ((m_J / rz) * Real.exp
          (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * (R + rz) /
            (rJ - (R + rz)))))) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_secondMoment_line_floor_cross_slope_windows_of_radius_strip
  intro ρ hρ hzero
  obtain ⟨N, M, ε₁, δ, T, U, t₀, t₁, t₂, rz, r₀, R, R', P, rJ, RJ,
    m_J, M_J, M_G, a₀, hM, hεδ, hU, hdom, ht₁, h12, hrz0, h0, hrR, hRP,
    hPrz, hRrzJ, hrJR, hRJ12, hρR', hR'rz, hbrlo, hbrhi, hsign, hmJ0,
    hrefl, hMJ, hbound, hjensen_floor, hengine, ha₀, ha₀0, hMG, hcross,
    hE, hclose, hfl⟩ := hwin ρ hρ hzero
  refine ⟨N, M, ε₁, δ, T, U, t₀, t₁, t₂, rz, r₀, R, R', P, rJ, RJ,
    m_J, M_J, M_G, a₀, ?_⟩
  exact ⟨hM, hεδ, hU, hdom, ht₁, h12, hrz0, h0, hrR, hRP, hPrz, hRrzJ,
    hrJR, hRJ12, hρR', hR'rz,
    (fun τ hτ u hu => line_interval_mem_closedBall_line_center_of_endpoint_bounds hbrlo hbrhi hτ hu),
    hsign, hmJ0, hrefl, hMJ, hbound, hjensen_floor, hengine, ha₀, ha₀0, hMG,
    hcross, hE, hclose, hfl⟩

end RHTower

namespace RHTower

/-- **Scalar target-ball certificate.**  A quadratic bound in real and imaginary coordinates
places the target point in the open ball around the critical-line center. -/
theorem point_mem_line_center_ball_of_quadratic {ρ : ℂ} {τ R' : ℝ}
    (hR'0 : 0 < R')
    (hquad : (ρ.re - 1 / 2) ^ 2 + (ρ.im - τ) ^ 2 < R' ^ 2) :
    ρ ∈ ball (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) R' := by
  rw [mem_ball, dist_eq_norm]
  have hsq : ‖ρ - (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ ^ 2 < R' ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [Complex.sub_re, Complex.sub_im]
    ring_nf at hquad ⊢
    exact hquad
  exact lt_of_pow_lt_pow_left₀ 2 hR'0.le hsq

/-- **RH gate with scalar target containment.**  This replaces the raw target-zero ball membership
by the coordinate inequality `(ρ.re-1/2)^2 + (ρ.im-τ)^2 < R'^2` for every admissible selected center. -/
theorem riemannHypothesis_of_secondMoment_line_floor_cross_slope_windows_of_radius_strip_interval_bracket_quadratic_target
    (hwin : ∀ ρ ∈ rightHalf, xi ρ = 0 →
      ∃ (N M : ℕ) (ε₁ δ : ℝ)
        (T U t₀ t₁ t₂ rz r₀ R R' P rJ RJ m_J M_J M_G a₀ : ℝ),
        1 ≤ M ∧ 0 ≤ ε₁ + δ ∧
        0 < U ∧
        t₀ ^ 2 * U
          + ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
              2 * |(m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))|
                / |Real.log n - Real.log m|
        < U * Real.log ((N : ℝ) + 1) ∧
        0 < t₁ ∧ t₁ ≤ t₂ ∧ 0 < rz ∧
        0 < r₀ ∧ r₀ < R ∧ R ≤ P ∧
        P + rz ≤ RJ ∧ R + rz < rJ ∧ rJ < RJ ∧ RJ < 1 / 2 ∧
        0 < R' ∧
        (∀ τ ∈ Set.Icc T (T + U),
          (ρ.re - 1 / 2) ^ 2 + (ρ.im - τ) ^ 2 < R' ^ 2) ∧
        R' + rz ≤ R ∧
        T + U - rz ≤ t₁ ∧ t₂ ≤ T + rz ∧
        (completedGN N (((1 / 2 : ℝ) : ℂ) + (t₁ : ℂ) * I)).re
          * (completedGN N (((1 / 2 : ℝ) : ℂ) + (t₂ : ℂ) * I)).re ≤ 0 ∧
        0 < m_J ∧
        (∀ τ ∈ Set.Icc T (T + U),
          ‖zetaChi (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) *
            dirichletPoly N (1 - (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I))‖ ≤ t₀ - m_J) ∧
        1 ≤ M_J ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ, ‖gN N z‖ ≤ M_J) ∧
        Real.log (M_J / m_J) / Real.log (RJ / rJ) < 2 ∧
        m_J / rz < M_J / (rJ - rz) ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z : ℂ, z.re = 1 / 2 →
          z ∈ closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) rz →
          a₀ ≤ ‖archFactor z‖) ∧
        0 < a₀ ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖completedGN N z‖ ≤ M_G) ∧
        6 * R * M_G < P ^ 2 * (a₀ * ((m_J / rz) * Real.exp
          (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * rz / (rJ - rz))))) ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁) ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖emCarrier M z - gN N z‖ ≤ δ) ∧
        2 * (ε₁ + δ) < r₀ * ((m_J / rz) * Real.exp
          (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * (R + rz) /
            (rJ - (R + rz)))))) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_secondMoment_line_floor_cross_slope_windows_of_radius_strip_interval_bracket
  intro ρ hρ hzero
  obtain ⟨N, M, ε₁, δ, T, U, t₀, t₁, t₂, rz, r₀, R, R', P, rJ, RJ,
    m_J, M_J, M_G, a₀, hM, hεδ, hU, hdom, ht₁, h12, hrz0, h0, hrR, hRP,
    hPrz, hRrzJ, hrJR, hRJ12, hR'0, hρquad, hR'rz, hbrlo, hbrhi, hsign,
    hmJ0, hrefl, hMJ, hbound, hjensen_floor, hengine, ha₀, ha₀0, hMG, hcross,
    hE, hclose, hfl⟩ := hwin ρ hρ hzero
  refine ⟨N, M, ε₁, δ, T, U, t₀, t₁, t₂, rz, r₀, R, R', P, rJ, RJ,
    m_J, M_J, M_G, a₀, ?_⟩
  exact ⟨hM, hεδ, hU, hdom, ht₁, h12, hrz0, h0, hrR, hRP, hPrz, hRrzJ,
    hrJR, hRJ12,
    (fun τ hτ => point_mem_line_center_ball_of_quadratic hR'0 (hρquad τ hτ)),
    hR'rz, hbrlo, hbrhi, hsign, hmJ0, hrefl, hMJ, hbound, hjensen_floor, hengine,
    ha₀, ha₀0, hMG, hcross, hE, hclose, hfl⟩

end RHTower

namespace RHTower

/-- **Endpoint control of interval distance.**  If a real point is within `Rτ` of both endpoints
of `[T,T+U]`, it is within `Rτ` of every point of the interval. -/
theorem interval_abs_le_of_endpoint_abs_le {x T U Rτ τ : ℝ}
    (hT : |x - T| ≤ Rτ) (hTU : |x - (T + U)| ≤ Rτ)
    (hτ : τ ∈ Set.Icc T (T + U)) :
    |x - τ| ≤ Rτ := by
  rw [abs_le] at hT hTU ⊢
  constructor <;> linarith [hT.1, hT.2, hTU.1, hTU.2, hτ.1, hτ.2]

/-- **Endpoint scalar target certificate.**  Endpoint imaginary-distance bounds and one quadratic
budget imply the uniform quadratic target condition over the whole center interval. -/
theorem quadratic_target_of_endpoint_abs_im_bounds {ρ : ℂ} {T U Rτ R' : ℝ}
    (hT : |ρ.im - T| ≤ Rτ)
    (hTU : |ρ.im - (T + U)| ≤ Rτ)
    (hquad : (ρ.re - 1 / 2) ^ 2 + Rτ ^ 2 < R' ^ 2) :
    ∀ τ ∈ Set.Icc T (T + U),
      (ρ.re - 1 / 2) ^ 2 + (ρ.im - τ) ^ 2 < R' ^ 2 := by
  intro τ hτ
  have habs : |ρ.im - τ| ≤ Rτ :=
    interval_abs_le_of_endpoint_abs_le hT hTU hτ
  have hRτ0 : 0 ≤ Rτ := le_trans (abs_nonneg (ρ.im - T)) hT
  have habs' : |ρ.im - τ| ≤ |Rτ| := by
    rwa [abs_of_nonneg hRτ0]
  have hdist_sq : (ρ.im - τ) ^ 2 ≤ Rτ ^ 2 := sq_le_sq.mpr habs'
  nlinarith

/-- **RH gate with endpoint scalar target containment.**  This removes the remaining uniform
quadratic target hypothesis: endpoint bounds for the target height and one quadratic radius budget
supply the target containment over every admissible selected center. -/
theorem riemannHypothesis_of_secondMoment_line_floor_cross_slope_windows_of_radius_strip_interval_bracket_endpoint_target
    (hwin : ∀ ρ ∈ rightHalf, xi ρ = 0 →
      ∃ (N M : ℕ) (ε₁ δ : ℝ)
        (T U t₀ t₁ t₂ rz r₀ R R' Rτ P rJ RJ m_J M_J M_G a₀ : ℝ),
        1 ≤ M ∧ 0 ≤ ε₁ + δ ∧
        0 < U ∧
        t₀ ^ 2 * U
          + ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
              2 * |(m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))|
                / |Real.log n - Real.log m|
        < U * Real.log ((N : ℝ) + 1) ∧
        0 < t₁ ∧ t₁ ≤ t₂ ∧ 0 < rz ∧
        0 < r₀ ∧ r₀ < R ∧ R ≤ P ∧
        P + rz ≤ RJ ∧ R + rz < rJ ∧ rJ < RJ ∧ RJ < 1 / 2 ∧
        0 < R' ∧
        |ρ.im - T| ≤ Rτ ∧ |ρ.im - (T + U)| ≤ Rτ ∧
        (ρ.re - 1 / 2) ^ 2 + Rτ ^ 2 < R' ^ 2 ∧
        R' + rz ≤ R ∧
        T + U - rz ≤ t₁ ∧ t₂ ≤ T + rz ∧
        (completedGN N (((1 / 2 : ℝ) : ℂ) + (t₁ : ℂ) * I)).re
          * (completedGN N (((1 / 2 : ℝ) : ℂ) + (t₂ : ℂ) * I)).re ≤ 0 ∧
        0 < m_J ∧
        (∀ τ ∈ Set.Icc T (T + U),
          ‖zetaChi (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) *
            dirichletPoly N (1 - (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I))‖ ≤ t₀ - m_J) ∧
        1 ≤ M_J ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ, ‖gN N z‖ ≤ M_J) ∧
        Real.log (M_J / m_J) / Real.log (RJ / rJ) < 2 ∧
        m_J / rz < M_J / (rJ - rz) ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z : ℂ, z.re = 1 / 2 →
          z ∈ closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) rz →
          a₀ ≤ ‖archFactor z‖) ∧
        0 < a₀ ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖completedGN N z‖ ≤ M_G) ∧
        6 * R * M_G < P ^ 2 * (a₀ * ((m_J / rz) * Real.exp
          (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * rz / (rJ - rz))))) ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁) ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖emCarrier M z - gN N z‖ ≤ δ) ∧
        2 * (ε₁ + δ) < r₀ * ((m_J / rz) * Real.exp
          (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * (R + rz) /
            (rJ - (R + rz)))))) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_secondMoment_line_floor_cross_slope_windows_of_radius_strip_interval_bracket_quadratic_target
  intro ρ hρ hzero
  obtain ⟨N, M, ε₁, δ, T, U, t₀, t₁, t₂, rz, r₀, R, R', Rτ, P, rJ, RJ,
    m_J, M_J, M_G, a₀, hM, hεδ, hU, hdom, ht₁, h12, hrz0, h0, hrR, hRP,
    hPrz, hRrzJ, hrJR, hRJ12, hR'0, hρT, hρTU, hρquad, hR'rz, hbrlo, hbrhi,
    hsign, hmJ0, hrefl, hMJ, hbound, hjensen_floor, hengine, ha₀, ha₀0, hMG,
    hcross, hE, hclose, hfl⟩ := hwin ρ hρ hzero
  refine ⟨N, M, ε₁, δ, T, U, t₀, t₁, t₂, rz, r₀, R, R', P, rJ, RJ,
    m_J, M_J, M_G, a₀, ?_⟩
  exact ⟨hM, hεδ, hU, hdom, ht₁, h12, hrz0, h0, hrR, hRP, hPrz, hRrzJ,
    hrJR, hRJ12, hR'0,
    quadratic_target_of_endpoint_abs_im_bounds hρT hρTU hρquad,
    hR'rz, hbrlo, hbrhi, hsign, hmJ0, hrefl, hMJ, hbound, hjensen_floor, hengine,
    ha₀, ha₀0, hMG, hcross, hE, hclose, hfl⟩

end RHTower

namespace RHTower

/-- **Critical-line reflected-term modulus.**  At a critical-line center the reflected χ-term has
exactly the same modulus as the one-dimensional Dirichlet carrier: `χ` is unitary on the line and
`1-s` is the conjugate of `s`. -/
theorem reflected_center_norm_eq_line_dpoly (N : ℕ) (τ : ℝ) :
    ‖zetaChi (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) *
        dirichletPoly N (1 - (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I))‖ =
      ‖dpoly (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) (Finset.Icc 1 N) τ‖ := by
  let c : ℂ := ((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I
  have hc_re : c.re = 1 / 2 := by simp [c]
  have h_one_sub : 1 - c = (starRingEnd ℂ) c := by
    apply Complex.ext
    · simp [c]
      norm_num
    · simp [c]
  have hDconj : dirichletPoly N (1 - c) = (starRingEnd ℂ) (dirichletPoly N c) := by
    rw [h_one_sub, dirichletPoly_conj]
  calc
    ‖zetaChi c * dirichletPoly N (1 - c)‖
        = ‖zetaChi c‖ * ‖dirichletPoly N (1 - c)‖ := norm_mul _ _
    _ = 1 * ‖dirichletPoly N (1 - c)‖ := by rw [zetaChi_norm_on_line hc_re]
    _ = ‖dirichletPoly N (1 - c)‖ := one_mul _
    _ = ‖dirichletPoly N c‖ := by rw [hDconj, Complex.norm_conj]
    _ = ‖dpoly (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) (Finset.Icc 1 N) τ‖ := by
      rw [dirichletPoly_criticalLine_eq N hc_re]
      simp [c]

/-- **Positive reflected reserve is incompatible with a critical-line `dpoly` floor.**  Therefore
the `dpoly`-floor-to-`gN` anchor bridge cannot be discharged on the critical line by making the
reflected term smaller than the floor; the next anchor producer must use `gN`'s phase/sign structure
directly. -/
theorem not_line_dpoly_floor_and_reflected_reserve (N : ℕ) {τ t₀ m_J : ℝ}
    (hmJ0 : 0 < m_J)
    (hline : t₀ < ‖dpoly (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) (Finset.Icc 1 N) τ‖)
    (hrefl : ‖zetaChi (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) *
        dirichletPoly N (1 - (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I))‖ ≤ t₀ - m_J) :
    False := by
  rw [reflected_center_norm_eq_line_dpoly N τ] at hrefl
  linarith

end RHTower

namespace RHTower

/-- **`gN` center anchor from a Hardy-floor scalar.**  On the critical line the carrier modulus is
exactly the finite Hardy amplitude, so a lower bound for `|H_N(τ)|` is the direct anchor
`m_J ≤ ‖gN N (1/2+iτ)‖`. -/
theorem gN_line_anchor_of_hardy_floor (N : ℕ) {τ m_J : ℝ}
    (hHardy : m_J ≤ |hardyCarrier N τ|) :
    m_J ≤ ‖gN N (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ := by
  change m_J ≤ ‖gN N (linePt τ)‖
  rw [norm_gN_line_eq_abs_hardyCarrier]
  exact hHardy

/-- **Cross-slope center certificate from a Hardy floor.**  This is the direct replacement for the
void critical-line reflected-reserve producer: the center anchor is supplied by the finite Hardy
amplitude `|H_N(τ)|`, while the rest of the certificate remains the cross-multiplied scalar surface. -/
theorem xi_window_pinned_of_hardy_floor_cross_slope
    {N M : ℕ} (hM : 1 ≤ M) {ε₁ δ : ℝ} (hεδ : 0 ≤ ε₁ + δ)
    {τ t₁ t₂ rz r₀ R P rJ RJ m_J M_J M_G a₀ : ℝ}
    (ht₁ : 0 < t₁) (h12 : t₁ ≤ t₂) (hrz0 : 0 < rz)
    (h0 : 0 < r₀) (hrR : r₀ < R) (hRP : R ≤ P)
    (hPrz : P + rz ≤ RJ) (hRrzJ : R + rz < rJ) (hrJR : rJ < RJ)
    (hstrip : ∀ z ∈ closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
      0 < z.re ∧ z.re < 1)
    (hbr : ∀ u ∈ Set.Icc t₁ t₂,
      ((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I ∈
        closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) rz)
    (hsign : (completedGN N (((1 / 2 : ℝ) : ℂ) + (t₁ : ℂ) * I)).re
      * (completedGN N (((1 / 2 : ℝ) : ℂ) + (t₂ : ℂ) * I)).re ≤ 0)
    (hmJ0 : 0 < m_J)
    (hHardy : m_J ≤ |hardyCarrier N τ|)
    (hMJ : 1 ≤ M_J)
    (hbound : ∀ z ∈ sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
      ‖gN N z‖ ≤ M_J)
    (hjensen_floor : Real.log (M_J / m_J) / Real.log (RJ / rJ) < 2)
    (hengine : m_J / rz < M_J / (rJ - rz))
    (ha₀ : ∀ z : ℂ, z.re = 1 / 2 →
      z ∈ closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) rz → a₀ ≤ ‖archFactor z‖)
    (ha₀0 : 0 < a₀)
    (hMG : ∀ z ∈ closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
      ‖completedGN N z‖ ≤ M_G)
    (hcross : 6 * R * M_G < P ^ 2 * (a₀ * ((m_J / rz) * Real.exp
      (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * rz / (rJ - rz))))))
    (hE : ∀ z ∈ closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
      ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁)
    (hclose : ∀ z ∈ closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
      ‖emCarrier M z - gN N z‖ ≤ δ)
    (hfl : 2 * (ε₁ + δ) < r₀ * ((m_J / rz) * Real.exp
      (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * (R + rz) /
        (rJ - (R + rz)))))) :
    ∃ ρ' : ℂ, ρ'.re = 1 / 2 ∧
      ρ' ∈ closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) rz ∧
      ∀ p ∈ ball ρ' R, xi p = 0 → p.re = 1 / 2 := by
  have hmJ : m_J ≤ ‖gN N (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ :=
    gN_line_anchor_of_hardy_floor N hHardy
  exact xi_window_pinned_of_center_floor_cross_slope hM hεδ ht₁ h12 hrz0 h0 hrR hRP
    hPrz hRrzJ hrJR hstrip hbr hsign hmJ0 hmJ hMJ hbound hjensen_floor hengine
    ha₀ ha₀0 hMG hcross hE hclose hfl

/-- **RH gate from Hardy-floor cross-slope scalar windows.**  The center anchor is now the real
finite Hardy amplitude `|H_N(τ)|`, avoiding the impossible request that the reflected χ-half be
smaller than the line Dirichlet half. -/
theorem riemannHypothesis_of_hardy_floor_cross_slope_windows
    (hwin : ∀ ρ ∈ rightHalf, xi ρ = 0 →
      ∃ (N M : ℕ) (ε₁ δ : ℝ)
        (τ t₁ t₂ rz r₀ R R' P rJ RJ m_J M_J M_G a₀ : ℝ),
        1 ≤ M ∧ 0 ≤ ε₁ + δ ∧
        0 < t₁ ∧ t₁ ≤ t₂ ∧ 0 < rz ∧
        0 < r₀ ∧ r₀ < R ∧ R ≤ P ∧
        P + rz ≤ RJ ∧ R + rz < rJ ∧ rJ < RJ ∧
        ρ ∈ ball (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) R' ∧ R' + rz ≤ R ∧
        (∀ z ∈ closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          0 < z.re ∧ z.re < 1) ∧
        (∀ u ∈ Set.Icc t₁ t₂,
          ((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I ∈
            closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) rz) ∧
        (completedGN N (((1 / 2 : ℝ) : ℂ) + (t₁ : ℂ) * I)).re
          * (completedGN N (((1 / 2 : ℝ) : ℂ) + (t₂ : ℂ) * I)).re ≤ 0 ∧
        0 < m_J ∧
        m_J ≤ |hardyCarrier N τ| ∧
        1 ≤ M_J ∧
        (∀ z ∈ sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ, ‖gN N z‖ ≤ M_J) ∧
        Real.log (M_J / m_J) / Real.log (RJ / rJ) < 2 ∧
        m_J / rz < M_J / (rJ - rz) ∧
        (∀ z : ℂ, z.re = 1 / 2 →
          z ∈ closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) rz →
          a₀ ≤ ‖archFactor z‖) ∧
        0 < a₀ ∧
        (∀ z ∈ closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖completedGN N z‖ ≤ M_G) ∧
        6 * R * M_G < P ^ 2 * (a₀ * ((m_J / rz) * Real.exp
          (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * rz / (rJ - rz))))) ∧
        (∀ z ∈ closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁) ∧
        (∀ z ∈ closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖emCarrier M z - gN N z‖ ≤ δ) ∧
        2 * (ε₁ + δ) < r₀ * ((m_J / rz) * Real.exp
          (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * (R + rz) /
            (rJ - (R + rz)))))) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_center_floor_cross_slope_windows
  intro ρ hρ hzero
  obtain ⟨N, M, ε₁, δ, τ, t₁, t₂, rz, r₀, R, R', P, rJ, RJ, m_J,
    M_J, M_G, a₀, hM, hεδ, ht₁, h12, hrz0, h0, hrR, hRP, hPrz, hRrzJ,
    hrJR, hρR', hR'rz, hstrip, hbr, hsign, hmJ0, hHardy, hMJ,
    hbound, hjensen_floor, hengine, ha₀, ha₀0, hMG, hcross, hE, hclose, hfl⟩ :=
    hwin ρ hρ hzero
  have hmJ : m_J ≤ ‖gN N (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ :=
    gN_line_anchor_of_hardy_floor N hHardy
  refine ⟨N, M, ε₁, δ, ((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I, t₁, t₂, rz, r₀,
    R, R', P, rJ, RJ, m_J, M_J, M_G, a₀, ?_⟩
  exact ⟨hM, hεδ, ht₁, h12, hrz0, h0, hrR, hRP, hPrz, hRrzJ, hrJR,
    hρR', hR'rz, hstrip, hbr, hsign, hmJ0, hmJ, hMJ, hbound, hjensen_floor,
    hengine, ha₀, ha₀0, hMG, hcross, hE, hclose, hfl⟩

end RHTower

namespace RHTower

/-- **Window-selected Hardy-floor RH gate with endpoint scalar geometry.**  The remaining center
selection target is now explicit and non-void: every certificate window must contain a height
`τ ∈ [T,T+U]` where the finite Hardy amplitude anchors the carrier, `m_J ≤ |H_N(τ)|`.  The target
zero containment, sign bracket containment, strip control, and circle/EM budgets are all stated on
known window endpoints or uniformly over the known interval. -/
theorem riemannHypothesis_of_window_hardy_floor_cross_slope_endpoint_target
    (hwin : ∀ ρ ∈ rightHalf, xi ρ = 0 →
      ∃ (N M : ℕ) (ε₁ δ : ℝ)
        (T U t₁ t₂ rz r₀ R R' Rτ P rJ RJ m_J M_J M_G a₀ : ℝ),
        1 ≤ M ∧ 0 ≤ ε₁ + δ ∧
        0 < U ∧
        0 < t₁ ∧ t₁ ≤ t₂ ∧ 0 < rz ∧
        0 < r₀ ∧ r₀ < R ∧ R ≤ P ∧
        P + rz ≤ RJ ∧ R + rz < rJ ∧ rJ < RJ ∧ RJ < 1 / 2 ∧
        0 < R' ∧
        |ρ.im - T| ≤ Rτ ∧ |ρ.im - (T + U)| ≤ Rτ ∧
        (ρ.re - 1 / 2) ^ 2 + Rτ ^ 2 < R' ^ 2 ∧
        R' + rz ≤ R ∧
        T + U - rz ≤ t₁ ∧ t₂ ≤ T + rz ∧
        (∃ τ ∈ Set.Icc T (T + U), m_J ≤ |hardyCarrier N τ|) ∧
        (completedGN N (((1 / 2 : ℝ) : ℂ) + (t₁ : ℂ) * I)).re
          * (completedGN N (((1 / 2 : ℝ) : ℂ) + (t₂ : ℂ) * I)).re ≤ 0 ∧
        0 < m_J ∧
        1 ≤ M_J ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ, ‖gN N z‖ ≤ M_J) ∧
        Real.log (M_J / m_J) / Real.log (RJ / rJ) < 2 ∧
        m_J / rz < M_J / (rJ - rz) ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z : ℂ, z.re = 1 / 2 →
          z ∈ closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) rz →
          a₀ ≤ ‖archFactor z‖) ∧
        0 < a₀ ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖completedGN N z‖ ≤ M_G) ∧
        6 * R * M_G < P ^ 2 * (a₀ * ((m_J / rz) * Real.exp
          (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * rz / (rJ - rz))))) ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁) ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖emCarrier M z - gN N z‖ ≤ δ) ∧
        2 * (ε₁ + δ) < r₀ * ((m_J / rz) * Real.exp
          (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * (R + rz) /
            (rJ - (R + rz)))))) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_hardy_floor_cross_slope_windows
  intro ρ hρ hzero
  obtain ⟨N, M, ε₁, δ, T, U, t₁, t₂, rz, r₀, R, R', Rτ, P, rJ, RJ,
    m_J, M_J, M_G, a₀, hM, hεδ, hU, ht₁, h12, hrz0, h0, hrR, hRP,
    hPrz, hRrzJ, hrJR, hRJ12, hR'0, hρT, hρTU, hρquad, hR'rz, hbrlo, hbrhi,
    hHardyEx, hsign, hmJ0, hMJ, hbound, hjensen_floor, hengine, ha₀, ha₀0,
    hMG, hcross, hE, hclose, hfl⟩ := hwin ρ hρ hzero
  obtain ⟨τ, hτ, hHardy⟩ := hHardyEx
  refine ⟨N, M, ε₁, δ, τ, t₁, t₂, rz, r₀, R, R', P, rJ, RJ,
    m_J, M_J, M_G, a₀, ?_⟩
  exact ⟨hM, hεδ, ht₁, h12, hrz0, h0, hrR, hRP, hPrz, hRrzJ, hrJR,
    point_mem_line_center_ball_of_quadratic hR'0
      ((quadratic_target_of_endpoint_abs_im_bounds hρT hρTU hρquad) τ hτ),
    hR'rz, line_center_closedBall_strip hRJ12,
    (fun u hu => line_interval_mem_closedBall_line_center_of_endpoint_bounds hbrlo hbrhi hτ hu),
    hsign, hmJ0, hHardy, hMJ, (fun z hz => hbound τ hτ z hz), hjensen_floor,
    hengine, (fun z hzre hz => ha₀ τ hτ z hzre hz), ha₀0,
    (fun z hz => hMG τ hτ z hz), hcross, (fun z hz => hE τ hτ z hz),
    (fun z hz => hclose τ hτ z hz), hfl⟩

end RHTower

namespace RHTower

/-- **Point floor from a strict interval `L²` budget.**  If the square integral of a real
function over `[T,T+U]` is larger than the constant budget `m² U`, then some point in the
window has amplitude at least `m`. -/
theorem exists_abs_floor_in_window_of_l2
    {f : ℝ → ℝ} {T U m : ℝ}
    (hU : 0 < U) (hm0 : 0 ≤ m)
    (hfint : IntervalIntegrable (fun t : ℝ => (f t) ^ 2) MeasureTheory.volume T (T + U))
    (hL2 : m ^ 2 * U < ∫ t in T..(T + U), (f t) ^ 2) :
    ∃ τ ∈ Set.Icc T (T + U), m ≤ |f τ| := by
  by_contra hcon
  have hlt : ∀ τ ∈ Set.Icc T (T + U), |f τ| < m := by
    intro τ hτ
    exact lt_of_not_ge (fun hge => hcon ⟨τ, hτ, hge⟩)
  have hsq : ∀ τ ∈ Set.Icc T (T + U), (f τ) ^ 2 ≤ m ^ 2 := by
    intro τ hτ
    have habs : |f τ| ≤ |m| := by
      rw [abs_of_nonneg hm0]
      exact le_of_lt (hlt τ hτ)
    exact sq_le_sq.mpr habs
  have hup : (∫ t in T..(T + U), (f t) ^ 2) ≤ m ^ 2 * U := by
    have hmono := intervalIntegral.integral_mono_on
      (g := fun _ => m ^ 2) (μ := MeasureTheory.volume) (by linarith : T ≤ T + U)
      hfint intervalIntegrable_const hsq
    calc (∫ t in T..(T + U), (f t) ^ 2)
        ≤ ∫ _ in T..(T + U), m ^ 2 := hmono
      _ = m ^ 2 * U := by
          rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  linarith

/-- **Hardy point floor from a strict interval `L²` budget.**  The squared Hardy amplitude is
automatically interval-integrable, so the only analytic input is the strict `L²` lower bound. -/
theorem exists_hardy_floor_in_window_of_l2
    (N : ℕ) {T U m_J : ℝ} (hU : 0 < U) (hmJ0 : 0 ≤ m_J)
    (hL2 : m_J ^ 2 * U < ∫ τ in T..(T + U), (hardyCarrier N τ) ^ 2) :
    ∃ τ ∈ Set.Icc T (T + U), m_J ≤ |hardyCarrier N τ| := by
  exact exists_abs_floor_in_window_of_l2 hU hmJ0
    (intervalIntegrable_hardyCarrier_sq N T U) hL2

/-- **Window-selected Hardy-`L²` RH gate with endpoint scalar geometry.**  The center-selection
hypothesis is now the interval inequality
`m_J² U < ∫_T^{T+U} H_N(τ)^2 dτ`; the point anchor consumed by the existing finite
certificate is produced by `exists_hardy_floor_in_window_of_l2`. -/
theorem riemannHypothesis_of_window_hardy_l2_cross_slope_endpoint_target
    (hwin : ∀ ρ ∈ rightHalf, xi ρ = 0 →
      ∃ (N M : ℕ) (ε₁ δ : ℝ)
        (T U t₁ t₂ rz r₀ R R' Rτ P rJ RJ m_J M_J M_G a₀ : ℝ),
        1 ≤ M ∧ 0 ≤ ε₁ + δ ∧
        0 < U ∧
        0 < t₁ ∧ t₁ ≤ t₂ ∧ 0 < rz ∧
        0 < r₀ ∧ r₀ < R ∧ R ≤ P ∧
        P + rz ≤ RJ ∧ R + rz < rJ ∧ rJ < RJ ∧ RJ < 1 / 2 ∧
        0 < R' ∧
        |ρ.im - T| ≤ Rτ ∧ |ρ.im - (T + U)| ≤ Rτ ∧
        (ρ.re - 1 / 2) ^ 2 + Rτ ^ 2 < R' ^ 2 ∧
        R' + rz ≤ R ∧
        T + U - rz ≤ t₁ ∧ t₂ ≤ T + rz ∧
        0 < m_J ∧
        m_J ^ 2 * U < ∫ τ in T..(T + U), (hardyCarrier N τ) ^ 2 ∧
        (completedGN N (((1 / 2 : ℝ) : ℂ) + (t₁ : ℂ) * I)).re
          * (completedGN N (((1 / 2 : ℝ) : ℂ) + (t₂ : ℂ) * I)).re ≤ 0 ∧
        1 ≤ M_J ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ, ‖gN N z‖ ≤ M_J) ∧
        Real.log (M_J / m_J) / Real.log (RJ / rJ) < 2 ∧
        m_J / rz < M_J / (rJ - rz) ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z : ℂ, z.re = 1 / 2 →
          z ∈ closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) rz →
          a₀ ≤ ‖archFactor z‖) ∧
        0 < a₀ ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖completedGN N z‖ ≤ M_G) ∧
        6 * R * M_G < P ^ 2 * (a₀ * ((m_J / rz) * Real.exp
          (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * rz / (rJ - rz))))) ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁) ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖emCarrier M z - gN N z‖ ≤ δ) ∧
        2 * (ε₁ + δ) < r₀ * ((m_J / rz) * Real.exp
          (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * (R + rz) /
            (rJ - (R + rz)))))) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_window_hardy_floor_cross_slope_endpoint_target
  intro ρ hρ hzero
  obtain ⟨N, M, ε₁, δ, T, U, t₁, t₂, rz, r₀, R, R', Rτ, P, rJ, RJ,
    m_J, M_J, M_G, a₀, hM, hεδ, hU, ht₁, h12, hrz0, h0, hrR, hRP,
    hPrz, hRrzJ, hrJR, hRJ12, hR'0, hρT, hρTU, hρquad, hR'rz, hbrlo, hbrhi,
    hmJ0, hL2, hsign, hMJ, hbound, hjensen_floor, hengine, ha₀, ha₀0,
    hMG, hcross, hE, hclose, hfl⟩ := hwin ρ hρ hzero
  have hHardyEx : ∃ τ ∈ Set.Icc T (T + U), m_J ≤ |hardyCarrier N τ| :=
    exists_hardy_floor_in_window_of_l2 N hU hmJ0.le hL2
  refine ⟨N, M, ε₁, δ, T, U, t₁, t₂, rz, r₀, R, R', Rτ, P, rJ, RJ,
    m_J, M_J, M_G, a₀, ?_⟩
  exact ⟨hM, hεδ, hU, ht₁, h12, hrz0, h0, hrR, hRP, hPrz, hRrzJ, hrJR,
    hRJ12, hR'0, hρT, hρTU, hρquad, hR'rz, hbrlo, hbrhi, hHardyEx,
    hsign, hmJ0, hMJ, hbound, hjensen_floor, hengine, ha₀, ha₀0, hMG,
    hcross, hE, hclose, hfl⟩

end RHTower

namespace RHTower

/-- **Hardy floor from a phase-free `gN` line `L²` budget.**  Since `H_N(τ)^2` is the
squared norm of `gN` on the critical line, a strict line-norm second-moment budget supplies the
same Hardy point anchor as the Hardy-amplitude budget. -/
theorem exists_hardy_floor_in_window_of_gN_line_l2
    (N : ℕ) {T U m_J : ℝ} (hU : 0 < U) (hmJ0 : 0 ≤ m_J)
    (hL2 : m_J ^ 2 * U < ∫ τ in T..(T + U), ‖gN N (linePt τ)‖ ^ 2) :
    ∃ τ ∈ Set.Icc T (T + U), m_J ≤ |hardyCarrier N τ| := by
  apply exists_hardy_floor_in_window_of_l2 N hU hmJ0
  have heq : (fun τ : ℝ => (hardyCarrier N τ) ^ 2)
      = fun τ : ℝ => ‖gN N (linePt τ)‖ ^ 2 := by
    funext τ
    exact hardyCarrier_sq_eq_norm_gN_line_sq N τ
  rwa [heq]

/-- **Window-selected `gN` line-`L²` RH gate with endpoint scalar geometry.**  The remaining
center-selection lower bound is stated directly as a line second moment of the finite carrier,
`m_J² U < ∫ ‖gN N(1/2+iτ)‖² dτ`, and is converted internally to the Hardy-amplitude gate. -/
theorem riemannHypothesis_of_window_gN_line_l2_cross_slope_endpoint_target
    (hwin : ∀ ρ ∈ rightHalf, xi ρ = 0 →
      ∃ (N M : ℕ) (ε₁ δ : ℝ)
        (T U t₁ t₂ rz r₀ R R' Rτ P rJ RJ m_J M_J M_G a₀ : ℝ),
        1 ≤ M ∧ 0 ≤ ε₁ + δ ∧
        0 < U ∧
        0 < t₁ ∧ t₁ ≤ t₂ ∧ 0 < rz ∧
        0 < r₀ ∧ r₀ < R ∧ R ≤ P ∧
        P + rz ≤ RJ ∧ R + rz < rJ ∧ rJ < RJ ∧ RJ < 1 / 2 ∧
        0 < R' ∧
        |ρ.im - T| ≤ Rτ ∧ |ρ.im - (T + U)| ≤ Rτ ∧
        (ρ.re - 1 / 2) ^ 2 + Rτ ^ 2 < R' ^ 2 ∧
        R' + rz ≤ R ∧
        T + U - rz ≤ t₁ ∧ t₂ ≤ T + rz ∧
        0 < m_J ∧
        m_J ^ 2 * U < ∫ τ in T..(T + U), ‖gN N (linePt τ)‖ ^ 2 ∧
        (completedGN N (((1 / 2 : ℝ) : ℂ) + (t₁ : ℂ) * I)).re
          * (completedGN N (((1 / 2 : ℝ) : ℂ) + (t₂ : ℂ) * I)).re ≤ 0 ∧
        1 ≤ M_J ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ, ‖gN N z‖ ≤ M_J) ∧
        Real.log (M_J / m_J) / Real.log (RJ / rJ) < 2 ∧
        m_J / rz < M_J / (rJ - rz) ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z : ℂ, z.re = 1 / 2 →
          z ∈ closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) rz →
          a₀ ≤ ‖archFactor z‖) ∧
        0 < a₀ ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖completedGN N z‖ ≤ M_G) ∧
        6 * R * M_G < P ^ 2 * (a₀ * ((m_J / rz) * Real.exp
          (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * rz / (rJ - rz))))) ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁) ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖emCarrier M z - gN N z‖ ≤ δ) ∧
        2 * (ε₁ + δ) < r₀ * ((m_J / rz) * Real.exp
          (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * (R + rz) /
            (rJ - (R + rz)))))) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_window_hardy_l2_cross_slope_endpoint_target
  intro ρ hρ hzero
  obtain ⟨N, M, ε₁, δ, T, U, t₁, t₂, rz, r₀, R, R', Rτ, P, rJ, RJ,
    m_J, M_J, M_G, a₀, hM, hεδ, hU, ht₁, h12, hrz0, h0, hrR, hRP,
    hPrz, hRrzJ, hrJR, hRJ12, hR'0, hρT, hρTU, hρquad, hR'rz, hbrlo, hbrhi,
    hmJ0, hL2line, hsign, hMJ, hbound, hjensen_floor, hengine, ha₀, ha₀0,
    hMG, hcross, hE, hclose, hfl⟩ := hwin ρ hρ hzero
  have hL2Hardy : m_J ^ 2 * U < ∫ τ in T..(T + U), (hardyCarrier N τ) ^ 2 := by
    have heq : (fun τ : ℝ => (hardyCarrier N τ) ^ 2)
        = fun τ : ℝ => ‖gN N (linePt τ)‖ ^ 2 := by
      funext τ
      exact hardyCarrier_sq_eq_norm_gN_line_sq N τ
    rwa [heq]
  refine ⟨N, M, ε₁, δ, T, U, t₁, t₂, rz, r₀, R, R', Rτ, P, rJ, RJ,
    m_J, M_J, M_G, a₀, ?_⟩
  exact ⟨hM, hεδ, hU, ht₁, h12, hrz0, h0, hrR, hRP, hPrz, hRrzJ, hrJR,
    hRJ12, hR'0, hρT, hρTU, hρquad, hR'rz, hbrlo, hbrhi, hmJ0,
    hL2Hardy, hsign, hMJ, hbound, hjensen_floor, hengine, ha₀, ha₀0, hMG,
    hcross, hE, hclose, hfl⟩

end RHTower

namespace RHTower

/-- **Hardy floor from the explicit main-plus-interference line second moment.**  The phase-free
line norm is rewritten using `gN = D + chi * conj D` on the critical line, so the analytic input is
now the scalar second moment of the Dirichlet main term plus the functional-equation cross term. -/
theorem exists_hardy_floor_in_window_of_gN_line_l2_split
    (N : ℕ) {T U m_J : ℝ} (hU : 0 < U) (hmJ0 : 0 ≤ m_J)
    (hL2 : m_J ^ 2 * U < ∫ τ in T..(T + U),
      (2 * ‖dirichletPoly N (linePt τ)‖ ^ 2
        + 2 * (zetaChi (linePt τ)
          * ((starRingEnd ℂ) (dirichletPoly N (linePt τ))) ^ 2).re)) :
    ∃ τ ∈ Set.Icc T (T + U), m_J ≤ |hardyCarrier N τ| := by
  apply exists_hardy_floor_in_window_of_gN_line_l2 N hU hmJ0
  have heq : (fun τ : ℝ => ‖gN N (linePt τ)‖ ^ 2)
      = fun τ : ℝ =>
        2 * ‖dirichletPoly N (linePt τ)‖ ^ 2
          + 2 * (zetaChi (linePt τ)
            * ((starRingEnd ℂ) (dirichletPoly N (linePt τ))) ^ 2).re := by
    funext τ
    exact norm_gN_line_sq_eq_dirichlet_cross N τ
  rwa [heq]

/-- **Window-selected explicit split-line-`L²` RH gate with endpoint scalar geometry.**  The
remaining every-window input is the exact scalar inequality obtained from the finite functional
equation expansion of `‖gN N (1/2+iτ)‖^2`. -/
theorem riemannHypothesis_of_window_gN_line_l2_split_cross_slope_endpoint_target
    (hwin : ∀ ρ ∈ rightHalf, xi ρ = 0 →
      ∃ (N M : ℕ) (ε₁ δ : ℝ)
        (T U t₁ t₂ rz r₀ R R' Rτ P rJ RJ m_J M_J M_G a₀ : ℝ),
        1 ≤ M ∧ 0 ≤ ε₁ + δ ∧
        0 < U ∧
        0 < t₁ ∧ t₁ ≤ t₂ ∧ 0 < rz ∧
        0 < r₀ ∧ r₀ < R ∧ R ≤ P ∧
        P + rz ≤ RJ ∧ R + rz < rJ ∧ rJ < RJ ∧ RJ < 1 / 2 ∧
        0 < R' ∧
        |ρ.im - T| ≤ Rτ ∧ |ρ.im - (T + U)| ≤ Rτ ∧
        (ρ.re - 1 / 2) ^ 2 + Rτ ^ 2 < R' ^ 2 ∧
        R' + rz ≤ R ∧
        T + U - rz ≤ t₁ ∧ t₂ ≤ T + rz ∧
        0 < m_J ∧
        m_J ^ 2 * U < ∫ τ in T..(T + U),
          (2 * ‖dirichletPoly N (linePt τ)‖ ^ 2
            + 2 * (zetaChi (linePt τ)
              * ((starRingEnd ℂ) (dirichletPoly N (linePt τ))) ^ 2).re) ∧
        (completedGN N (((1 / 2 : ℝ) : ℂ) + (t₁ : ℂ) * I)).re
          * (completedGN N (((1 / 2 : ℝ) : ℂ) + (t₂ : ℂ) * I)).re ≤ 0 ∧
        1 ≤ M_J ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ, ‖gN N z‖ ≤ M_J) ∧
        Real.log (M_J / m_J) / Real.log (RJ / rJ) < 2 ∧
        m_J / rz < M_J / (rJ - rz) ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z : ℂ, z.re = 1 / 2 →
          z ∈ closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) rz →
          a₀ ≤ ‖archFactor z‖) ∧
        0 < a₀ ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖completedGN N z‖ ≤ M_G) ∧
        6 * R * M_G < P ^ 2 * (a₀ * ((m_J / rz) * Real.exp
          (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * rz / (rJ - rz))))) ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁) ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖emCarrier M z - gN N z‖ ≤ δ) ∧
        2 * (ε₁ + δ) < r₀ * ((m_J / rz) * Real.exp
          (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * (R + rz) /
            (rJ - (R + rz)))))) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_window_gN_line_l2_cross_slope_endpoint_target
  intro ρ hρ hzero
  obtain ⟨N, M, ε₁, δ, T, U, t₁, t₂, rz, r₀, R, R', Rτ, P, rJ, RJ,
    m_J, M_J, M_G, a₀, hM, hεδ, hU, ht₁, h12, hrz0, h0, hrR, hRP,
    hPrz, hRrzJ, hrJR, hRJ12, hR'0, hρT, hρTU, hρquad, hR'rz, hbrlo, hbrhi,
    hmJ0, hL2split, hsign, hMJ, hbound, hjensen_floor, hengine, ha₀, ha₀0,
    hMG, hcross, hE, hclose, hfl⟩ := hwin ρ hρ hzero
  have hL2line : m_J ^ 2 * U < ∫ τ in T..(T + U), ‖gN N (linePt τ)‖ ^ 2 := by
    have heq : (fun τ : ℝ => ‖gN N (linePt τ)‖ ^ 2)
        = fun τ : ℝ =>
          2 * ‖dirichletPoly N (linePt τ)‖ ^ 2
            + 2 * (zetaChi (linePt τ)
              * ((starRingEnd ℂ) (dirichletPoly N (linePt τ))) ^ 2).re := by
      funext τ
      exact norm_gN_line_sq_eq_dirichlet_cross N τ
    rwa [heq]
  refine ⟨N, M, ε₁, δ, T, U, t₁, t₂, rz, r₀, R, R', Rτ, P, rJ, RJ,
    m_J, M_J, M_G, a₀, ?_⟩
  exact ⟨hM, hεδ, hU, ht₁, h12, hrz0, h0, hrR, hRP, hPrz, hRrzJ, hrJR,
    hRJ12, hR'0, hρT, hρTU, hρquad, hR'rz, hbrlo, hbrhi, hmJ0,
    hL2line, hsign, hMJ, hbound, hjensen_floor, hengine, ha₀, ha₀0, hMG,
    hcross, hE, hclose, hfl⟩

end RHTower

namespace RHTower

/-- **Hardy floor from separate main and interference line-moment budgets.**  It is enough to
lower-bound the positive Dirichlet main moment and separately bound the functional-equation
interference from below: if `mainFloor` minus the allowed cross-loss beats `m_J² U`, then the split
line-`L²` floor supplies the Hardy anchor. -/
theorem exists_hardy_floor_in_window_of_gN_line_l2_split_bounds
    (N : ℕ) {T U m_J mainFloor crossLoss : ℝ} (hU : 0 < U) (hmJ0 : 0 ≤ m_J)
    (hmain : mainFloor ≤ ∫ τ in T..(T + U), 2 * ‖dirichletPoly N (linePt τ)‖ ^ 2)
    (hcross : -crossLoss ≤ ∫ τ in T..(T + U),
      2 * (zetaChi (linePt τ)
        * ((starRingEnd ℂ) (dirichletPoly N (linePt τ))) ^ 2).re)
    (hbudget : m_J ^ 2 * U < mainFloor - crossLoss) :
    ∃ τ ∈ Set.Icc T (T + U), m_J ≤ |hardyCarrier N τ| := by
  apply exists_hardy_floor_in_window_of_gN_line_l2_split N hU hmJ0
  have hline : Continuous linePt := by
    unfold linePt
    fun_prop
  have hDline : Continuous fun τ : ℝ => dirichletPoly N (linePt τ) := by
    exact (dirichletPoly_differentiable N).continuous.comp hline
  have hmainCont : Continuous fun τ : ℝ => 2 * ‖dirichletPoly N (linePt τ)‖ ^ 2 := by
    exact ((hDline.norm.pow 2).const_mul 2)
  have hmainInt : IntervalIntegrable (fun τ : ℝ => 2 * ‖dirichletPoly N (linePt τ)‖ ^ 2)
      MeasureTheory.volume T (T + U) :=
    hmainCont.intervalIntegrable T (T + U)
  have hcrossCont : Continuous fun τ : ℝ =>
      2 * (zetaChi (linePt τ)
        * ((starRingEnd ℂ) (dirichletPoly N (linePt τ))) ^ 2).re := by
    have hgnCont : Continuous fun τ : ℝ => ‖gN N (linePt τ)‖ ^ 2 :=
      (continuous_gN_line N).norm.pow 2
    have heq : (fun τ : ℝ =>
        2 * (zetaChi (linePt τ)
          * ((starRingEnd ℂ) (dirichletPoly N (linePt τ))) ^ 2).re)
        = fun τ : ℝ => ‖gN N (linePt τ)‖ ^ 2
          - 2 * ‖dirichletPoly N (linePt τ)‖ ^ 2 := by
      funext τ
      rw [norm_gN_line_sq_eq_dirichlet_cross N τ]
      ring
    rw [heq]
    exact hgnCont.sub hmainCont
  have hcrossInt : IntervalIntegrable (fun τ : ℝ =>
      2 * (zetaChi (linePt τ)
        * ((starRingEnd ℂ) (dirichletPoly N (linePt τ))) ^ 2).re)
      MeasureTheory.volume T (T + U) :=
    hcrossCont.intervalIntegrable T (T + U)
  have hadd : (∫ τ in T..(T + U),
      (2 * ‖dirichletPoly N (linePt τ)‖ ^ 2
        + 2 * (zetaChi (linePt τ)
          * ((starRingEnd ℂ) (dirichletPoly N (linePt τ))) ^ 2).re))
      = (∫ τ in T..(T + U), 2 * ‖dirichletPoly N (linePt τ)‖ ^ 2)
        + ∫ τ in T..(T + U),
          2 * (zetaChi (linePt τ)
            * ((starRingEnd ℂ) (dirichletPoly N (linePt τ))) ^ 2).re := by
    rw [intervalIntegral.integral_add hmainInt hcrossInt]
  rw [hadd]
  linarith

end RHTower

namespace RHTower

/-- **Hardy floor from a main moment and pointwise FE-interference loss.**  A uniform segment bound
`-crossDensity` for the split cross term supplies the integral loss `crossDensity * U`, so the
remaining anchor inequality is the scalar budget `m_J² U < mainFloor - crossDensity * U`. -/
theorem exists_hardy_floor_in_window_of_gN_line_l2_split_pointwise_cross
    (N : ℕ) {T U m_J mainFloor crossDensity : ℝ} (hU : 0 < U) (hmJ0 : 0 ≤ m_J)
    (hmain : mainFloor ≤ ∫ τ in T..(T + U), 2 * ‖dirichletPoly N (linePt τ)‖ ^ 2)
    (hcrossPt : ∀ τ ∈ Set.Icc T (T + U),
      -crossDensity ≤ 2 * (zetaChi (linePt τ)
        * ((starRingEnd ℂ) (dirichletPoly N (linePt τ))) ^ 2).re)
    (hbudget : m_J ^ 2 * U < mainFloor - crossDensity * U) :
    ∃ τ ∈ Set.Icc T (T + U), m_J ≤ |hardyCarrier N τ| := by
  apply exists_hardy_floor_in_window_of_gN_line_l2_split_bounds N hU hmJ0 hmain
  · have hcrossInt : IntervalIntegrable (fun τ : ℝ =>
        2 * (zetaChi (linePt τ)
          * ((starRingEnd ℂ) (dirichletPoly N (linePt τ))) ^ 2).re)
        MeasureTheory.volume T (T + U) :=
      (continuous_gN_line_crossTerm N).intervalIntegrable T (T + U)
    have hmono := intervalIntegral.integral_mono_on
      (f := fun _ : ℝ => -crossDensity)
      (g := fun τ : ℝ => 2 * (zetaChi (linePt τ)
        * ((starRingEnd ℂ) (dirichletPoly N (linePt τ))) ^ 2).re)
      (μ := MeasureTheory.volume) (by linarith : T ≤ T + U)
      intervalIntegrable_const hcrossInt hcrossPt
    calc -(crossDensity * U)
        = (-crossDensity) * U := by ring
      _ = ∫ _ in T..(T + U), (-crossDensity) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
          ring
      _ ≤ ∫ τ in T..(T + U),
          2 * (zetaChi (linePt τ)
            * ((starRingEnd ℂ) (dirichletPoly N (linePt τ))) ^ 2).re := hmono
  · exact hbudget

end RHTower

namespace RHTower

/-- **Main line moment from the banked Dirichlet second moment.**  On the critical line,
`dirichletPoly N` is the one-dimensional `dpoly` with coefficients `n^{-1/2}`, so the existing
second-moment lower bound gives the positive main contribution in the split `gN` line norm. -/
theorem dirichlet_line_main_moment_lower_bound (N : ℕ) (T U : ℝ) :
    2 * (U * (∑ m ∈ Finset.Icc 1 N, ((m : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2)
        - ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
            2 * |(m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))|
              / |Real.log n - Real.log m|)
      ≤ ∫ τ in T..(T + U), 2 * ‖dirichletPoly N (linePt τ)‖ ^ 2 := by
  let a : ℕ → ℝ := fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))
  let s : Finset ℕ := Finset.Icc 1 N
  have hs : ∀ n ∈ s, 1 ≤ n := by
    intro n hn
    exact (Finset.mem_Icc.mp hn).1
  have hline : (fun τ : ℝ => ‖dirichletPoly N (linePt τ)‖ ^ 2)
      = fun τ : ℝ => ‖dpoly a s τ‖ ^ 2 := by
    funext τ
    change ‖dirichletPoly N (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ ^ 2
      = ‖dpoly a s τ‖ ^ 2
    rw [dirichletPoly_line_eq N τ]
  have hlow := secondMoment_lower_bound a s T U hs
  dsimp only [a, s] at hlow
  rw [← hline] at hlow
  have hmul : 2 * (U * (∑ m ∈ Finset.Icc 1 N, ((m : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2)
        - ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
            2 * |(m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))|
              / |Real.log n - Real.log m|)
      ≤ 2 * (∫ τ in T..(T + U), ‖dirichletPoly N (linePt τ)‖ ^ 2) := by
    exact mul_le_mul_of_nonneg_left hlow (by norm_num)
  calc 2 * (U * (∑ m ∈ Finset.Icc 1 N, ((m : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2)
        - ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
            2 * |(m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))|
              / |Real.log n - Real.log m|)
      ≤ 2 * (∫ τ in T..(T + U), ‖dirichletPoly N (linePt τ)‖ ^ 2) := hmul
    _ = ∫ τ in T..(T + U), 2 * ‖dirichletPoly N (linePt τ)‖ ^ 2 := by
      rw [intervalIntegral.integral_const_mul]

/-- **Hardy floor from the banked main second moment and a pointwise FE-interference loss.**  The
remaining window anchor closes once the explicit Dirichlet off-diagonal budget and the segment-wise
cross-density loss leave more than `m_J² U`. -/
theorem exists_hardy_floor_in_window_of_secondMoment_pointwise_cross
    (N : ℕ) {T U m_J crossDensity : ℝ} (hU : 0 < U) (hmJ0 : 0 ≤ m_J)
    (hcrossPt : ∀ τ ∈ Set.Icc T (T + U),
      -crossDensity ≤ 2 * (zetaChi (linePt τ)
        * ((starRingEnd ℂ) (dirichletPoly N (linePt τ))) ^ 2).re)
    (hbudget : m_J ^ 2 * U <
      2 * (U * (∑ m ∈ Finset.Icc 1 N, ((m : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2)
        - ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
            2 * |(m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))|
              / |Real.log n - Real.log m|) - crossDensity * U) :
    ∃ τ ∈ Set.Icc T (T + U), m_J ≤ |hardyCarrier N τ| := by
  apply exists_hardy_floor_in_window_of_gN_line_l2_split_pointwise_cross N hU hmJ0
  · exact dirichlet_line_main_moment_lower_bound N T U
  · exact hcrossPt
  · exact hbudget

end RHTower

namespace RHTower

/-- **Hardy floor from banked second moment plus a line Dirichlet norm-square envelope.**  A uniform
bound `‖D_N(1/2+iτ)‖² ≤ Dsup` on the window gives the FE-interference loss `2 * Dsup`, so the anchor
budget is fully scalar: banked main moment minus `2 * Dsup * U` beats `m_J² U`. -/
theorem exists_hardy_floor_in_window_of_secondMoment_cross_sup
    (N : ℕ) {T U m_J Dsup : ℝ} (hU : 0 < U) (hmJ0 : 0 ≤ m_J)
    (hDsup : ∀ τ ∈ Set.Icc T (T + U), ‖dirichletPoly N (linePt τ)‖ ^ 2 ≤ Dsup)
    (hbudget : m_J ^ 2 * U <
      2 * (U * (∑ m ∈ Finset.Icc 1 N, ((m : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2)
        - ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
            2 * |(m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))|
              / |Real.log n - Real.log m|) - (2 * Dsup) * U) :
    ∃ τ ∈ Set.Icc T (T + U), m_J ≤ |hardyCarrier N τ| := by
  apply exists_hardy_floor_in_window_of_secondMoment_pointwise_cross N hU hmJ0
  · intro τ hτ
    exact gN_line_crossTerm_lower_bound_of_dirichlet_norm_sq_le N τ (hDsup τ hτ)
  · exact hbudget

end RHTower

namespace RHTower

/-- **Hardy floor from banked second moment plus a line Dirichlet norm envelope.**  A uniform scalar
bound `‖D_N(1/2+iτ)‖ ≤ Dnorm` on the window gives the FE-interference loss `2 * Dnorm²`, so the
remaining anchor check is the finite budget inequality displayed below. -/
theorem exists_hardy_floor_in_window_of_secondMoment_norm_sup
    (N : ℕ) {T U m_J Dnorm : ℝ} (hU : 0 < U) (hmJ0 : 0 ≤ m_J)
    (hDnorm : ∀ τ ∈ Set.Icc T (T + U), ‖dirichletPoly N (linePt τ)‖ ≤ Dnorm)
    (hbudget : m_J ^ 2 * U <
      2 * (U * (∑ m ∈ Finset.Icc 1 N, ((m : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2)
        - ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
            2 * |(m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))|
              / |Real.log n - Real.log m|) - (2 * Dnorm ^ 2) * U) :
    ∃ τ ∈ Set.Icc T (T + U), m_J ≤ |hardyCarrier N τ| := by
  apply exists_hardy_floor_in_window_of_secondMoment_cross_sup (N := N) (T := T)
    (U := U) (m_J := m_J) (Dsup := Dnorm ^ 2) hU hmJ0
  · intro τ hτ
    exact pow_le_pow_left₀ (norm_nonneg _) (hDnorm τ hτ) 2
  · exact hbudget

end RHTower

namespace RHTower

/-- **Full RH endpoint gate from the banked second moment plus a line norm envelope.**  The Hardy
center witness in the endpoint scalar gate is produced internally from the banked Dirichlet main
moment and the window envelope `‖D_N(1/2+iτ)‖ ≤ Dnorm`; the remaining anchor condition is the explicit
finite inequality `m_J² U < mainSecondMomentFloor - (2 * Dnorm²) * U`. -/
theorem riemannHypothesis_of_secondMoment_norm_sup_cross_slope_endpoint_target
    (hwin : ∀ ρ ∈ rightHalf, xi ρ = 0 →
      ∃ (N M : ℕ) (ε₁ δ : ℝ)
        (T U t₁ t₂ rz r₀ R R' Rτ P rJ RJ m_J Dnorm M_J M_G a₀ : ℝ),
        1 ≤ M ∧ 0 ≤ ε₁ + δ ∧
        0 < U ∧
        0 < t₁ ∧ t₁ ≤ t₂ ∧ 0 < rz ∧
        0 < r₀ ∧ r₀ < R ∧ R ≤ P ∧
        P + rz ≤ RJ ∧ R + rz < rJ ∧ rJ < RJ ∧ RJ < 1 / 2 ∧
        0 < R' ∧
        |ρ.im - T| ≤ Rτ ∧ |ρ.im - (T + U)| ≤ Rτ ∧
        (ρ.re - 1 / 2) ^ 2 + Rτ ^ 2 < R' ^ 2 ∧
        R' + rz ≤ R ∧
        T + U - rz ≤ t₁ ∧ t₂ ≤ T + rz ∧
        0 < m_J ∧
        (∀ τ ∈ Set.Icc T (T + U), ‖dirichletPoly N (linePt τ)‖ ≤ Dnorm) ∧
        m_J ^ 2 * U <
          2 * (U * (∑ m ∈ Finset.Icc 1 N, ((m : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2)
            - ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
                2 * |(m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))|
                  / |Real.log n - Real.log m|) - (2 * Dnorm ^ 2) * U ∧
        (completedGN N (((1 / 2 : ℝ) : ℂ) + (t₁ : ℂ) * I)).re
          * (completedGN N (((1 / 2 : ℝ) : ℂ) + (t₂ : ℂ) * I)).re ≤ 0 ∧
        1 ≤ M_J ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ, ‖gN N z‖ ≤ M_J) ∧
        Real.log (M_J / m_J) / Real.log (RJ / rJ) < 2 ∧
        m_J / rz < M_J / (rJ - rz) ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z : ℂ, z.re = 1 / 2 →
          z ∈ closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) rz →
          a₀ ≤ ‖archFactor z‖) ∧
        0 < a₀ ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖completedGN N z‖ ≤ M_G) ∧
        6 * R * M_G < P ^ 2 * (a₀ * ((m_J / rz) * Real.exp
          (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * rz / (rJ - rz))))) ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁) ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖emCarrier M z - gN N z‖ ≤ δ) ∧
        2 * (ε₁ + δ) < r₀ * ((m_J / rz) * Real.exp
          (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * (R + rz) /
            (rJ - (R + rz)))))) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_window_hardy_floor_cross_slope_endpoint_target
  intro ρ hρ hzero
  obtain ⟨N, M, ε₁, δ, T, U, t₁, t₂, rz, r₀, R, R', Rτ, P, rJ, RJ,
    m_J, Dnorm, M_J, M_G, a₀, hM, hεδ, hU, ht₁, h12, hrz0, h0, hrR, hRP,
    hPrz, hRrzJ, hrJR, hRJ12, hR'0, hρT, hρTU, hρquad, hR'rz, hbrlo, hbrhi,
    hmJ0, hDnorm, hbudget, hsign, hMJ, hbound, hjensen_floor, hengine, ha₀,
    ha₀0, hMG, hcross, hE, hclose, hfl⟩ := hwin ρ hρ hzero
  have hHardyEx : ∃ τ ∈ Set.Icc T (T + U), m_J ≤ |hardyCarrier N τ| :=
    exists_hardy_floor_in_window_of_secondMoment_norm_sup N hU hmJ0.le hDnorm hbudget
  refine ⟨N, M, ε₁, δ, T, U, t₁, t₂, rz, r₀, R, R', Rτ, P, rJ, RJ,
    m_J, M_J, M_G, a₀, ?_⟩
  exact ⟨hM, hεδ, hU, ht₁, h12, hrz0, h0, hrR, hRP, hPrz, hRrzJ, hrJR,
    hRJ12, hR'0, hρT, hρTU, hρquad, hR'rz, hbrlo, hbrhi, hHardyEx,
    hsign, hmJ0, hMJ, hbound, hjensen_floor, hengine, ha₀, ha₀0, hMG,
    hcross, hE, hclose, hfl⟩

end RHTower

namespace RHTower

/-- **Hardy floor from banked second moment plus a Hardy-phase quadrature envelope.**  The split
FE-interference loss is controlled by `|Im(conj(w) * D_N)| ≤ Ysup`, giving the sharper scalar loss
`2 * Ysup²` instead of the full Dirichlet-norm loss. -/
theorem exists_hardy_floor_in_window_of_secondMoment_orthogonal_sup
    (N : ℕ) {T U m_J Ysup : ℝ} (hU : 0 < U) (hmJ0 : 0 ≤ m_J)
    (hY : ∀ τ ∈ Set.Icc T (T + U), |hardyOrthogonalCarrier N τ| ≤ Ysup)
    (hbudget : m_J ^ 2 * U <
      2 * (U * (∑ m ∈ Finset.Icc 1 N, ((m : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2)
        - ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
            2 * |(m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))|
              / |Real.log n - Real.log m|) - (2 * Ysup ^ 2) * U) :
    ∃ τ ∈ Set.Icc T (T + U), m_J ≤ |hardyCarrier N τ| := by
  apply exists_hardy_floor_in_window_of_secondMoment_pointwise_cross N hU hmJ0
  · intro τ hτ
    exact gN_line_crossTerm_lower_bound_of_hardyOrthogonal_le N τ (hY τ hτ)
  · exact hbudget

/-- **Full RH endpoint gate from the banked second moment plus a Hardy-phase quadrature envelope.**
The center witness is produced internally once the banked main moment beats the explicit quadrature
loss `(2 * Ysup²) * U`; the remaining certificate data stay on the known endpoint, segment, and circle
surfaces. -/
theorem riemannHypothesis_of_secondMoment_orthogonal_sup_cross_slope_endpoint_target
    (hwin : ∀ ρ ∈ rightHalf, xi ρ = 0 →
      ∃ (N M : ℕ) (ε₁ δ : ℝ)
        (T U t₁ t₂ rz r₀ R R' Rτ P rJ RJ m_J Ysup M_J M_G a₀ : ℝ),
        1 ≤ M ∧ 0 ≤ ε₁ + δ ∧
        0 < U ∧
        0 < t₁ ∧ t₁ ≤ t₂ ∧ 0 < rz ∧
        0 < r₀ ∧ r₀ < R ∧ R ≤ P ∧
        P + rz ≤ RJ ∧ R + rz < rJ ∧ rJ < RJ ∧ RJ < 1 / 2 ∧
        0 < R' ∧
        |ρ.im - T| ≤ Rτ ∧ |ρ.im - (T + U)| ≤ Rτ ∧
        (ρ.re - 1 / 2) ^ 2 + Rτ ^ 2 < R' ^ 2 ∧
        R' + rz ≤ R ∧
        T + U - rz ≤ t₁ ∧ t₂ ≤ T + rz ∧
        0 < m_J ∧
        (∀ τ ∈ Set.Icc T (T + U), |hardyOrthogonalCarrier N τ| ≤ Ysup) ∧
        m_J ^ 2 * U <
          2 * (U * (∑ m ∈ Finset.Icc 1 N, ((m : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2)
            - ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
                2 * |(m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))|
                  / |Real.log n - Real.log m|) - (2 * Ysup ^ 2) * U ∧
        (completedGN N (((1 / 2 : ℝ) : ℂ) + (t₁ : ℂ) * I)).re
          * (completedGN N (((1 / 2 : ℝ) : ℂ) + (t₂ : ℂ) * I)).re ≤ 0 ∧
        1 ≤ M_J ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ, ‖gN N z‖ ≤ M_J) ∧
        Real.log (M_J / m_J) / Real.log (RJ / rJ) < 2 ∧
        m_J / rz < M_J / (rJ - rz) ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z : ℂ, z.re = 1 / 2 →
          z ∈ closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) rz →
          a₀ ≤ ‖archFactor z‖) ∧
        0 < a₀ ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖completedGN N z‖ ≤ M_G) ∧
        6 * R * M_G < P ^ 2 * (a₀ * ((m_J / rz) * Real.exp
          (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * rz / (rJ - rz))))) ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁) ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖emCarrier M z - gN N z‖ ≤ δ) ∧
        2 * (ε₁ + δ) < r₀ * ((m_J / rz) * Real.exp
          (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * (R + rz) /
            (rJ - (R + rz)))))) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_window_hardy_floor_cross_slope_endpoint_target
  intro ρ hρ hzero
  obtain ⟨N, M, ε₁, δ, T, U, t₁, t₂, rz, r₀, R, R', Rτ, P, rJ, RJ,
    m_J, Ysup, M_J, M_G, a₀, hM, hεδ, hU, ht₁, h12, hrz0, h0, hrR, hRP,
    hPrz, hRrzJ, hrJR, hRJ12, hR'0, hρT, hρTU, hρquad, hR'rz, hbrlo, hbrhi,
    hmJ0, hY, hbudget, hsign, hMJ, hbound, hjensen_floor, hengine, ha₀,
    ha₀0, hMG, hcross, hE, hclose, hfl⟩ := hwin ρ hρ hzero
  have hHardyEx : ∃ τ ∈ Set.Icc T (T + U), m_J ≤ |hardyCarrier N τ| :=
    exists_hardy_floor_in_window_of_secondMoment_orthogonal_sup N hU hmJ0.le hY hbudget
  refine ⟨N, M, ε₁, δ, T, U, t₁, t₂, rz, r₀, R, R', Rτ, P, rJ, RJ,
    m_J, M_J, M_G, a₀, ?_⟩
  exact ⟨hM, hεδ, hU, ht₁, h12, hrz0, h0, hrR, hRP, hPrz, hRrzJ, hrJR,
    hRJ12, hR'0, hρT, hρTU, hρquad, hR'rz, hbrlo, hbrhi, hHardyEx,
    hsign, hmJ0, hMJ, hbound, hjensen_floor, hengine, ha₀, ha₀0, hMG,
    hcross, hE, hclose, hfl⟩

end RHTower

namespace RHTower

/-- **Hardy floor from a main moment and averaged Hardy-phase quadrature energy.**  The exact
Hardy-phase split rewrites the Hardy energy as `H_N² = 2 * (2‖D_N‖²) - 4Y_N²`, so an averaged
quadrature-energy budget can replace the stronger pointwise quadrature envelope. -/
theorem exists_hardy_floor_in_window_of_main_orthogonal_energy
    (N : ℕ) {T U m_J mainFloor orthLoss : ℝ} (hU : 0 < U) (hmJ0 : 0 ≤ m_J)
    (hmain : mainFloor ≤ ∫ τ in T..(T + U), 2 * ‖dirichletPoly N (linePt τ)‖ ^ 2)
    (horth : (∫ τ in T..(T + U), 4 * (hardyOrthogonalCarrier N τ) ^ 2) ≤ orthLoss)
    (hbudget : m_J ^ 2 * U < 2 * mainFloor - orthLoss) :
    ∃ τ ∈ Set.Icc T (T + U), m_J ≤ |hardyCarrier N τ| := by
  apply exists_hardy_floor_in_window_of_l2 N hU hmJ0
  have hline : Continuous linePt := by
    unfold linePt
    fun_prop
  have hDline : Continuous fun τ : ℝ => dirichletPoly N (linePt τ) := by
    exact (dirichletPoly_differentiable N).continuous.comp hline
  have hmainCont : Continuous fun τ : ℝ => 2 * ‖dirichletPoly N (linePt τ)‖ ^ 2 := by
    exact ((hDline.norm.pow 2).const_mul 2)
  have hmainInt : IntervalIntegrable (fun τ : ℝ => 2 * ‖dirichletPoly N (linePt τ)‖ ^ 2)
      MeasureTheory.volume T (T + U) :=
    hmainCont.intervalIntegrable T (T + U)
  have hhardyInt : IntervalIntegrable (fun τ : ℝ => (hardyCarrier N τ) ^ 2)
      MeasureTheory.volume T (T + U) :=
    intervalIntegrable_hardyCarrier_sq N T U
  have horthEq : (fun τ : ℝ => 4 * (hardyOrthogonalCarrier N τ) ^ 2)
      = fun τ : ℝ => 2 * (2 * ‖dirichletPoly N (linePt τ)‖ ^ 2) - (hardyCarrier N τ) ^ 2 := by
    funext τ
    rw [dirichlet_main_eq_hardy_components N τ]
    ring
  have horthInt : IntervalIntegrable (fun τ : ℝ => 4 * (hardyOrthogonalCarrier N τ) ^ 2)
      MeasureTheory.volume T (T + U) := by
    rw [horthEq]
    exact (hmainInt.const_mul 2).sub hhardyInt
  have hHardyEq : (∫ τ in T..(T + U), (hardyCarrier N τ) ^ 2)
      = 2 * (∫ τ in T..(T + U), 2 * ‖dirichletPoly N (linePt τ)‖ ^ 2)
        - ∫ τ in T..(T + U), 4 * (hardyOrthogonalCarrier N τ) ^ 2 := by
    have hpoint : (fun τ : ℝ => (hardyCarrier N τ) ^ 2)
        = fun τ : ℝ => 2 * (2 * ‖dirichletPoly N (linePt τ)‖ ^ 2)
          - 4 * (hardyOrthogonalCarrier N τ) ^ 2 := by
      funext τ
      rw [dirichlet_main_eq_hardy_components N τ]
      ring
    rw [hpoint]
    rw [intervalIntegral.integral_sub (hmainInt.const_mul 2) horthInt]
    rw [intervalIntegral.integral_const_mul]
  rw [hHardyEq]
  linarith

/-- **Hardy floor from the banked second moment and averaged Hardy-phase quadrature energy.**  The
remaining anchor check is the additive budget saying that the anchor energy plus the actual
quadrature energy fits under the banked second-moment floor. -/
theorem exists_hardy_floor_in_window_of_secondMoment_orthogonal_energy
    (N : ℕ) {T U m_J : ℝ} (hU : 0 < U) (hmJ0 : 0 ≤ m_J)
    (hbudget :
      m_J ^ 2 * U + (∫ τ in T..(T + U), 4 * (hardyOrthogonalCarrier N τ) ^ 2) <
        4 * (U * (∑ m ∈ Finset.Icc 1 N, ((m : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2)
        - ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
            2 * |(m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))|
              / |Real.log n - Real.log m|)) :
    ∃ τ ∈ Set.Icc T (T + U), m_J ≤ |hardyCarrier N τ| := by
  apply exists_hardy_floor_in_window_of_main_orthogonal_energy N hU hmJ0
  · exact dirichlet_line_main_moment_lower_bound N T U
  · exact le_rfl
  · linarith

/-- **`gN` line anchor from the banked second moment and averaged quadrature energy.**  This is
the carrier-form version of `exists_hardy_floor_in_window_of_secondMoment_orthogonal_energy`: the
selected height is returned directly as the scalar anchor `m_J ≤ ‖gN N (1/2+iτ)‖`. -/
theorem exists_gN_line_anchor_in_window_of_secondMoment_orthogonal_energy
    (N : ℕ) {T U m_J : ℝ} (hU : 0 < U) (hmJ0 : 0 ≤ m_J)
    (hbudget :
      m_J ^ 2 * U + (∫ τ in T..(T + U), 4 * (hardyOrthogonalCarrier N τ) ^ 2) <
        4 * (U * (∑ m ∈ Finset.Icc 1 N, ((m : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2)
        - ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
            2 * |(m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))|
              / |Real.log n - Real.log m|)) :
    ∃ τ ∈ Set.Icc T (T + U),
      m_J ≤ ‖gN N (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ := by
  obtain ⟨τ, hτ, hHardy⟩ :=
    exists_hardy_floor_in_window_of_secondMoment_orthogonal_energy N hU hmJ0 hbudget
  exact ⟨τ, hτ, gN_line_anchor_of_hardy_floor N hHardy⟩

end RHTower

namespace RHTower

/-- **Critical-line `dirichletPoly` second-moment upper bound.**  This is the upper companion to
`dirichlet_line_main_moment_lower_bound`, with the same explicit off-diagonal constant. -/
theorem dirichlet_line_norm_sq_moment_upper_bound (N : ℕ) (T U : ℝ) :
    (∫ τ in T..(T + U), ‖dirichletPoly N (linePt τ)‖ ^ 2)
      ≤ U * (∑ m ∈ Finset.Icc 1 N, ((m : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2)
        + ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
            2 * |(m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))|
              / |Real.log n - Real.log m| := by
  let a : ℕ → ℝ := fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))
  let s : Finset ℕ := Finset.Icc 1 N
  have hs : ∀ n ∈ s, 1 ≤ n := by
    intro n hn
    exact (Finset.mem_Icc.mp hn).1
  have hline : (fun τ : ℝ => ‖dirichletPoly N (linePt τ)‖ ^ 2)
      = fun τ : ℝ => ‖dpoly a s τ‖ ^ 2 := by
    funext τ
    change ‖dirichletPoly N (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ ^ 2
      = ‖dpoly a s τ‖ ^ 2
    rw [dirichletPoly_line_eq N τ]
  have hup := secondMoment_upper_bound a s T U hs
  dsimp only [a, s] at hup
  rwa [hline]

/-- **Averaged quadrature energy is bounded by averaged one-sided Dirichlet energy.**  This is only the
baseline ceiling; later estimates must save against it to feed the Hardy anchor budget. -/
theorem orthogonal_energy_le_dirichlet_energy
    (N : ℕ) {T U : ℝ} (hU : 0 ≤ U) :
    (∫ τ in T..(T + U), 4 * (hardyOrthogonalCarrier N τ) ^ 2)
      ≤ ∫ τ in T..(T + U), 4 * ‖dirichletPoly N (linePt τ)‖ ^ 2 := by
  have hline : Continuous linePt := by
    unfold linePt
    fun_prop
  have hDline : Continuous fun τ : ℝ => dirichletPoly N (linePt τ) := by
    exact (dirichletPoly_differentiable N).continuous.comp hline
  have hmainCont : Continuous fun τ : ℝ => 2 * ‖dirichletPoly N (linePt τ)‖ ^ 2 := by
    exact ((hDline.norm.pow 2).const_mul 2)
  have hmainInt : IntervalIntegrable (fun τ : ℝ => 2 * ‖dirichletPoly N (linePt τ)‖ ^ 2)
      MeasureTheory.volume T (T + U) :=
    hmainCont.intervalIntegrable T (T + U)
  have hhardyInt : IntervalIntegrable (fun τ : ℝ => (hardyCarrier N τ) ^ 2)
      MeasureTheory.volume T (T + U) :=
    intervalIntegrable_hardyCarrier_sq N T U
  have horthEq : (fun τ : ℝ => 4 * (hardyOrthogonalCarrier N τ) ^ 2)
      = fun τ : ℝ => 2 * (2 * ‖dirichletPoly N (linePt τ)‖ ^ 2) - (hardyCarrier N τ) ^ 2 := by
    funext τ
    rw [dirichlet_main_eq_hardy_components N τ]
    ring
  have horthInt : IntervalIntegrable (fun τ : ℝ => 4 * (hardyOrthogonalCarrier N τ) ^ 2)
      MeasureTheory.volume T (T + U) := by
    rw [horthEq]
    exact (hmainInt.const_mul 2).sub hhardyInt
  have hDInt : IntervalIntegrable (fun τ : ℝ => 4 * ‖dirichletPoly N (linePt τ)‖ ^ 2)
      MeasureTheory.volume T (T + U) :=
    (((hDline.norm.pow 2).const_mul 4).intervalIntegrable T (T + U))
  exact intervalIntegral.integral_mono_on
    (μ := MeasureTheory.volume) (by linarith : T ≤ T + U)
    horthInt hDInt (fun τ _ => by
      have hsq := hardyOrthogonalCarrier_sq_le_dirichlet_norm_sq N τ
      nlinarith)

/-- **Explicit upper bound for the averaged Hardy-phase quadrature energy.**  It combines the
pointwise phase ceiling with the upper Montgomery-Vaughan window bound. -/
theorem orthogonal_energy_le_dirichlet_upper_bound
    (N : ℕ) {T U : ℝ} (hU : 0 ≤ U) :
    (∫ τ in T..(T + U), 4 * (hardyOrthogonalCarrier N τ) ^ 2)
      ≤ 4 * (U * (∑ m ∈ Finset.Icc 1 N, ((m : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2)
        + ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
            2 * |(m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))|
              / |Real.log n - Real.log m|) := by
  have horth := orthogonal_energy_le_dirichlet_energy N (T := T) (U := U) hU
  have hup := dirichlet_line_norm_sq_moment_upper_bound N T U
  have hscale : (∫ τ in T..(T + U), 4 * ‖dirichletPoly N (linePt τ)‖ ^ 2)
      = 4 * (∫ τ in T..(T + U), ‖dirichletPoly N (linePt τ)‖ ^ 2) := by
    rw [intervalIntegral.integral_const_mul]
  rw [hscale] at horth
  nlinarith

end RHTower

namespace RHTower

/-- **Hardy floor from a quadrature-energy saving below the crude total-energy ceiling.**  If the
quadrature energy improves on `4 * (U * diagonal + offdiag)` by `saving`, then the diagonal cancels
against the banked main floor and the remaining anchor budget is `m_J² U < saving - 8 * offdiag`. -/
theorem exists_hardy_floor_in_window_of_secondMoment_orthogonal_saving
    (N : ℕ) {T U m_J saving : ℝ} (hU : 0 < U) (hmJ0 : 0 ≤ m_J)
    (horth : (∫ τ in T..(T + U), 4 * (hardyOrthogonalCarrier N τ) ^ 2) ≤
      4 * (U * (∑ m ∈ Finset.Icc 1 N, ((m : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2)
        + ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
            2 * |(m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))|
              / |Real.log n - Real.log m|) - saving)
    (hbudget : m_J ^ 2 * U < saving - 8 *
      (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
        2 * |(m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))|
          / |Real.log n - Real.log m|)) :
    ∃ τ ∈ Set.Icc T (T + U), m_J ≤ |hardyCarrier N τ| := by
  apply exists_hardy_floor_in_window_of_secondMoment_orthogonal_energy
    (N := N) (T := T) (U := U) (m_J := m_J) hU hmJ0
  linarith

end RHTower
namespace RHTower

/-- Full RH endpoint gate from the banked second moment plus a Hardy-phase quadrature saving below
`4 * (U * diagonal + offdiag)`.  The center witness is produced internally once the saving beats the
explicit finite budget `m_J^2 * U + 8 * offdiag`; all remaining certificate data stay on known endpoint,
segment, and circle surfaces. -/
theorem riemannHypothesis_of_secondMoment_orthogonal_saving_cross_slope_endpoint_target
    (hwin : ∀ ρ ∈ rightHalf, xi ρ = 0 →
      ∃ (N M : ℕ) (ε₁ δ : ℝ)
        (T U t₁ t₂ rz r₀ R R' Rτ P rJ RJ m_J saving M_J M_G a₀ : ℝ),
        1 ≤ M ∧ 0 ≤ ε₁ + δ ∧
        0 < U ∧
        0 < t₁ ∧ t₁ ≤ t₂ ∧ 0 < rz ∧
        0 < r₀ ∧ r₀ < R ∧ R ≤ P ∧
        P + rz ≤ RJ ∧ R + rz < rJ ∧ rJ < RJ ∧ RJ < 1 / 2 ∧
        0 < R' ∧
        |ρ.im - T| ≤ Rτ ∧ |ρ.im - (T + U)| ≤ Rτ ∧
        (ρ.re - 1 / 2) ^ 2 + Rτ ^ 2 < R' ^ 2 ∧
        R' + rz ≤ R ∧
        T + U - rz ≤ t₁ ∧ t₂ ≤ T + rz ∧
        0 < m_J ∧
        (∫ τ in T..(T + U), 4 * (hardyOrthogonalCarrier N τ) ^ 2) ≤
          4 * (U * (∑ m ∈ Finset.Icc 1 N, ((m : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2)
            + ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
                2 * |(m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))|
                  / |Real.log n - Real.log m|) - saving ∧
        m_J ^ 2 * U < saving - 8 *
          (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
            2 * |(m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))|
              / |Real.log n - Real.log m|) ∧
        (completedGN N (((1 / 2 : ℝ) : ℂ) + (t₁ : ℂ) * I)).re
          * (completedGN N (((1 / 2 : ℝ) : ℂ) + (t₂ : ℂ) * I)).re ≤ 0 ∧
        1 ≤ M_J ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ, ‖gN N z‖ ≤ M_J) ∧
        Real.log (M_J / m_J) / Real.log (RJ / rJ) < 2 ∧
        m_J / rz < M_J / (rJ - rz) ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z : ℂ, z.re = 1 / 2 →
          z ∈ closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) rz →
          a₀ ≤ ‖archFactor z‖) ∧
        0 < a₀ ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖completedGN N z‖ ≤ M_G) ∧
        6 * R * M_G < P ^ 2 * (a₀ * ((m_J / rz) * Real.exp
          (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * rz / (rJ - rz))))) ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁) ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖emCarrier M z - gN N z‖ ≤ δ) ∧
        2 * (ε₁ + δ) < r₀ * ((m_J / rz) * Real.exp
          (-(2 * Real.log ((M_J / (rJ - rz)) / (m_J / rz)) * (R + rz) /
            (rJ - (R + rz)))))) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_window_hardy_floor_cross_slope_endpoint_target
  intro ρ hρ hzero
  obtain ⟨N, M, ε₁, δ, T, U, t₁, t₂, rz, r₀, R, R', Rτ, P, rJ, RJ,
    m_J, saving, M_J, M_G, a₀, hM, hεδ, hU, ht₁, h12, hrz0, h0, hrR, hRP,
    hPrz, hRrzJ, hrJR, hRJ12, hR'0, hρT, hρTU, hρquad, hR'rz, hbrlo, hbrhi,
    hmJ0, horth, hbudget, hsign, hMJ, hbound, hjensen_floor, hengine, ha₀,
    ha₀0, hMG, hcross, hE, hclose, hfl⟩ := hwin ρ hρ hzero
  have hHardyEx : ∃ τ ∈ Set.Icc T (T + U), m_J ≤ |hardyCarrier N τ| :=
    exists_hardy_floor_in_window_of_secondMoment_orthogonal_saving N hU hmJ0.le horth hbudget
  refine ⟨N, M, ε₁, δ, T, U, t₁, t₂, rz, r₀, R, R', Rτ, P, rJ, RJ,
    m_J, M_J, M_G, a₀, ?_⟩
  exact ⟨hM, hεδ, hU, ht₁, h12, hrz0, h0, hrR, hRP, hPrz, hRrzJ, hrJR,
    hRJ12, hR'0, hρT, hρTU, hρquad, hR'rz, hbrlo, hbrhi, hHardyEx,
    hsign, hmJ0, hMJ, hbound, hjensen_floor, hengine, ha₀, ha₀0, hMG,
    hcross, hE, hclose, hfl⟩

end RHTower

namespace RHTower

/-- **Hardy-floor certificate from a single outer-power scalar budget.**  The Hardy carrier supplies
the center anchor; the scalar side is reduced to one outer-radius power floor that simultaneously
feeds the cross-slope and EM budgets. -/
theorem xi_window_pinned_of_hardy_floor_outer_power
    {N M : ℕ} (hM : 1 ≤ M) {ε₁ δ : ℝ} (hεδ : 0 ≤ ε₁ + δ)
    {τ t₁ t₂ rz r₀ R P rJ RJ m_J M_J M_G a₀ : ℝ}
    (ht₁ : 0 < t₁) (h12 : t₁ ≤ t₂) (hrz0 : 0 < rz)
    (h0 : 0 < r₀) (hrR : r₀ < R) (hRP : R ≤ P)
    (hPrz : P + rz ≤ RJ) (hRrzJ : R + rz < rJ) (hrJR : rJ < RJ)
    (hstrip : ∀ z ∈ closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
      0 < z.re ∧ z.re < 1)
    (hbr : ∀ u ∈ Set.Icc t₁ t₂,
      ((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I ∈
        closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) rz)
    (hsign : (completedGN N (((1 / 2 : ℝ) : ℂ) + (t₁ : ℂ) * I)).re
      * (completedGN N (((1 / 2 : ℝ) : ℂ) + (t₂ : ℂ) * I)).re ≤ 0)
    (hmJ0 : 0 < m_J)
    (hHardy : m_J ≤ |hardyCarrier N τ|)
    (hMJ : 1 ≤ M_J)
    (hbound : ∀ z ∈ sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
      ‖gN N z‖ ≤ M_J)
    (hjensen_floor : Real.log (M_J / m_J) / Real.log (RJ / rJ) < 2)
    (hengine : m_J / rz < M_J / (rJ - rz))
    (ha₀ : ∀ z : ℂ, z.re = 1 / 2 →
      z ∈ closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) rz → a₀ ≤ ‖archFactor z‖)
    (ha₀0 : 0 < a₀)
    (hMG : ∀ z ∈ closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
      ‖completedGN N z‖ ≤ M_G)
    (hcross_outer : 6 * R * M_G < P ^ 2 * (a₀ * ((m_J / rz) *
      ((m_J / rz) / (M_J / (rJ - rz))) ^ (2 * (R + rz) / (rJ - (R + rz))))))
    (hE : ∀ z ∈ closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
      ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁)
    (hclose : ∀ z ∈ closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
      ‖emCarrier M z - gN N z‖ ≤ δ)
    (hfl_outer : 2 * (ε₁ + δ) < r₀ * ((m_J / rz) *
      ((m_J / rz) / (M_J / (rJ - rz))) ^ (2 * (R + rz) / (rJ - (R + rz))))) :
    ∃ ρ' : ℂ, ρ'.re = 1 / 2 ∧
      ρ' ∈ closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) rz ∧
      ∀ p ∈ ball ρ' R, xi p = 0 → p.re = 1 / 2 := by
  have hR0 : 0 ≤ R := (lt_trans h0 hrR).le
  have hMJ0 : 0 < M_J := lt_of_lt_of_le zero_lt_one hMJ
  have hrzJ : rz < rJ := by linarith
  obtain ⟨hcross, hfl⟩ :=
    canonical_cross_em_budgets_of_outer_power_floor
      (m_J := m_J) (M_J := M_J) (rz := rz) (rJ := rJ) (R := R)
      (P := P) (M_G := M_G) (a₀ := a₀) (r₀ := r₀) (ε₁ := ε₁) (δ := δ)
      hmJ0 hrz0 hMJ0 hrzJ hengine ha₀0 hR0 hRrzJ hcross_outer hfl_outer
  exact xi_window_pinned_of_hardy_floor_cross_slope hM hεδ ht₁ h12 hrz0 h0 hrR hRP
    hPrz hRrzJ hrJR hstrip hbr hsign hmJ0 hHardy hMJ hbound hjensen_floor hengine
    ha₀ ha₀0 hMG hcross hE hclose hfl

end RHTower

namespace RHTower

/-- Full RH endpoint gate from the banked second moment, the exact averaged quadrature-energy
budget, and one outer-radius power floor.  The Hardy anchor face is the additive scalar inequality
`m_J^2 U + orthogonalEnergy < 4 * (U * diagonal - offdiag)`. -/
theorem riemannHypothesis_of_secondMoment_orthogonal_saving_outer_power_endpoint_target
    (hwin : ∀ ρ ∈ rightHalf, xi ρ = 0 →
      ∃ (N M : ℕ) (ε₁ δ : ℝ)
        (T U t₁ t₂ rz r₀ R P rJ RJ m_J M_J M_G a₀ : ℝ),
        1 ≤ M ∧
        0 < U ∧
        0 < t₁ ∧ t₁ ≤ t₂ ∧ 0 < rz ∧
        0 < r₀ ∧ r₀ < R ∧ R ≤ P ∧
        P + rz ≤ RJ ∧ R + rz < rJ ∧ rJ < RJ ∧ RJ < 1 / 2 ∧
        rz < R ∧
        (ρ.re - 1 / 2) ^ 2 +
            (max |ρ.im - T| |ρ.im - (T + U)|) ^ 2 < (R - rz) ^ 2 ∧
        T + U - rz ≤ t₁ ∧ t₂ ≤ T + rz ∧
        0 < m_J ∧
        m_J ^ 2 * U +
          (∫ τ in T..(T + U), 4 * (hardyOrthogonalCarrier N τ) ^ 2) <
          4 * (U * (∑ m ∈ Finset.Icc 1 N, ((m : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2)
            - ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
                2 * |(m : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))|
                  / |Real.log n - Real.log m|) ∧
        (completedGN N (((1 / 2 : ℝ) : ℂ) + (t₁ : ℂ) * I)).re
          * (completedGN N (((1 / 2 : ℝ) : ℂ) + (t₂ : ℂ) * I)).re ≤ 0 ∧
        1 ≤ M_J ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ, ‖gN N z‖ ≤ M_J) ∧
        Real.log (M_J / m_J) / Real.log (RJ / rJ) < 2 ∧
        m_J / rz < M_J / (rJ - rz) ∧
        (∀ u ∈ Set.Icc (T - rz) (T + U + rz), a₀ ≤ ‖archFactor (linePt u)‖) ∧
        0 < a₀ ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖completedGN N z‖ ≤ M_G) ∧
        max ((6 * R * M_G) / (P ^ 2 * a₀))
            ((2 * (ε₁ + δ)) / r₀) <
          (m_J / rz) *
            ((m_J / rz) / (M_J / (rJ - rz))) ^
              (2 * (R + rz) / (rJ - (R + rz))) ∧
        (max ‖linePt T‖ ‖linePt (T + U)‖ + RJ) *
          (M : ℝ) ^ (-(1 / 2 - RJ)) / (1 / 2 - RJ) ≤ ε₁ ∧
        (∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
          sphere (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
          ‖emCarrier M z - gN N z‖ ≤ δ)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_center_floor_cross_slope_windows
  intro ρ hρ hzero
  obtain ⟨N, M, ε₁, δ, T, U, t₁, t₂, rz, r₀, R, P, rJ, RJ,
    m_J, M_J, M_G, a₀, hM, hU, ht₁, h12, hrz0, h0, hrR, hRP,
    hPrz, hRrzJ, hrJR, hRJ12, hrzR, hρquad, hbrlo, hbrhi,
    hmJ0, henergy, hsign, hMJ, hbound, hjensen_floor, hengine, ha₀,
    ha₀0, hMG, hbudget_outer, hE, hclose⟩ :=
    hwin ρ hρ hzero
  let Rprime : ℝ := R - rz
  let Rτ : ℝ := max |ρ.im - T| |ρ.im - (T + U)|
  have hR'0 : 0 < Rprime := by
    dsimp [Rprime]
    linarith
  have hR'rz : Rprime + rz ≤ R := by
    dsimp [Rprime]
    linarith
  have hρT : |ρ.im - T| ≤ Rτ := by
    exact le_max_left _ _
  have hρTU : |ρ.im - (T + U)| ≤ Rτ := by
    exact le_max_right _ _
  have hρquad' : (ρ.re - 1 / 2) ^ 2 + Rτ ^ 2 < Rprime ^ 2 := by
    simpa [Rτ, Rprime] using hρquad
  have hR0 : 0 ≤ R := (lt_trans h0 hrR).le
  have hP0 : 0 < P := lt_of_lt_of_le (lt_trans h0 hrR) hRP
  have hMJ0 : 0 < M_J := lt_of_lt_of_le zero_lt_one hMJ
  have hrzJ : rz < rJ := by linarith
  have hRJ0 : 0 < RJ := by linarith [h0, hrR, hRrzJ, hrJR, hrz0]
  have hε₁0 : 0 ≤ ε₁ := by
    have hden0 : 0 < 1 / 2 - RJ := by linarith
    have hpow_nonneg : 0 ≤ (M : ℝ) ^ (-(1 / 2 - RJ)) :=
      Real.rpow_nonneg (Nat.cast_nonneg M) _
    have hmax_nonneg : 0 ≤ max ‖linePt T‖ ‖linePt (T + U)‖ :=
      le_trans (norm_nonneg (linePt T)) (le_max_left _ _)
    have hlhs_nonneg : 0 ≤ (max ‖linePt T‖ ‖linePt (T + U)‖ + RJ) *
        (M : ℝ) ^ (-(1 / 2 - RJ)) / (1 / 2 - RJ) := by
      exact div_nonneg (mul_nonneg (add_nonneg hmax_nonneg hRJ0.le) hpow_nonneg) hden0.le
    exact le_trans hlhs_nonneg hE
  have hδ0 : 0 ≤ δ := by
    have hτT : T ∈ Set.Icc T (T + U) := ⟨le_rfl, by linarith [hU]⟩
    have hsample : linePt T + (RJ : ℂ) ∈
        sphere (((1 / 2 : ℝ) : ℂ) + (T : ℂ) * I) RJ := by
      simpa [linePt] using linePt_add_radius_mem_sphere (τ := T) hRJ0.le
    exact le_trans (norm_nonneg (emCarrier M (linePt T + (RJ : ℂ)) -
      gN N (linePt T + (RJ : ℂ)))) (hclose T hτT (linePt T + (RJ : ℂ)) hsample)
  have hεδ : 0 ≤ ε₁ + δ := add_nonneg hε₁0 hδ0
  obtain ⟨τ, hτ, hAnchor⟩ :=
    exists_gN_line_anchor_in_window_of_secondMoment_orthogonal_energy N hU hmJ0.le henergy
  have hMG_ball : ∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
      closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
      ‖completedGN N z‖ ≤ M_G := by
    intro τ hτ
    have hcan : ∀ z ∈ closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
        AnalyticAt ℂ (completedGN N) z := by
      intro z hz
      exact completedGN_analyticAt
        ((line_center_closedBall_strip (τ := τ) hRJ12 z hz).1)
        ((line_center_closedBall_strip (τ := τ) hRJ12 z hz).2)
    exact norm_le_on_closedBall_of_sphere hRJ0 hcan (hMG τ hτ)
  have hE_ball : ∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
      closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
      ‖z‖ * (M : ℝ) ^ (-z.re) / z.re ≤ ε₁ := by
    intro τ hτ z hz
    exact em_remainder_norm_le_window_closedBall_of_endpoint_bound
      (M := M) (T := T) (U := U) (RJ := RJ) (ε₁ := ε₁) hM hRJ12 hE
      τ hτ z (by simpa [linePt] using hz)
  have hclose_ball : ∀ τ ∈ Set.Icc T (T + U), ∀ z ∈
      closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
      ‖emCarrier M z - gN N z‖ ≤ δ := by
    intro τ hτ
    have hcan : ∀ z ∈ closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) RJ,
        AnalyticAt ℂ (fun z => emCarrier M z - gN N z) z := by
      intro z hz
      have hstripz := line_center_closedBall_strip (τ := τ) hRJ12 z hz
      have hz1 : z ≠ 1 := by
        intro hz_eq
        have hlt : (1 : ℂ).re < 1 := by simpa [hz_eq] using hstripz.2
        norm_num at hlt
      have hG1 : Gammaℝ (1 - z) ≠ 0 := by
        exact Gammaℝ_ne_zero_of_re_pos (by
          rw [Complex.sub_re, Complex.one_re]
          linarith [hstripz.2])
      exact (emCarrier_analyticAt_of_ne_one hM hz1).sub (gN_analyticAt hG1)
    exact norm_le_on_closedBall_of_sphere hRJ0 hcan (hclose τ hτ)
  have ha₀_line_ball : ∀ τ ∈ Set.Icc T (T + U), ∀ z : ℂ, z.re = 1 / 2 →
      z ∈ closedBall (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) rz →
      a₀ ≤ ‖archFactor z‖ := by
    intro τ hτ z hzre hz
    have him : z.im ∈ Set.Icc (T - rz) (T + U + rz) :=
      im_mem_expanded_window_of_mem_line_center_closedBall hτ hz
    have hzline : z = linePt z.im := eq_linePt_of_re_eq_half hzre
    rw [hzline]
    exact ha₀ z.im him
  obtain ⟨hcross, hfl⟩ :=
    canonical_cross_em_budgets_of_outer_power_floor_max
      (m_J := m_J) (M_J := M_J) (rz := rz) (rJ := rJ) (R := R)
      (P := P) (M_G := M_G) (a₀ := a₀) (r₀ := r₀) (ε₁ := ε₁) (δ := δ)
      hmJ0 hrz0 hMJ0 hrzJ hengine hP0 ha₀0 h0 hR0 hRrzJ hbudget_outer
  refine ⟨N, M, ε₁, δ, ((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I,
    t₁, t₂, rz, r₀, R, Rprime, P, rJ, RJ, m_J, M_J, M_G, a₀, ?_⟩
  exact ⟨hM, hεδ, ht₁, h12, hrz0, h0, hrR, hRP, hPrz, hRrzJ, hrJR,
    point_mem_line_center_ball_of_quadratic hR'0
      ((quadratic_target_of_endpoint_abs_im_bounds hρT hρTU hρquad') τ hτ),
    hR'rz, line_center_closedBall_strip hRJ12,
    (fun u hu => line_interval_mem_closedBall_line_center_of_endpoint_bounds hbrlo hbrhi hτ hu),
    hsign, hmJ0, hAnchor, hMJ, (fun z hz => hbound τ hτ z hz),
    hjensen_floor, hengine, (fun z hzre hz => ha₀_line_ball τ hτ z hzre hz),
    ha₀0, (fun z hz => hMG_ball τ hτ z hz), hcross,
    (fun z hz => hE_ball τ hτ z hz), (fun z hz => hclose_ball τ hτ z hz), hfl⟩

end RHTower
