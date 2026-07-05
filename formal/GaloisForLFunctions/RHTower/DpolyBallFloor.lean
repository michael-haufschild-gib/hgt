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
import GaloisForLFunctions.RHTower.DeckMultiZero

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

/-- **Cofinal circle-gate floors from a cofinal line floor.** If the Dirichlet part exceeds `t₀` at
the on-line centers `½ + iτ` for cofinally many `τ`, and the (height-independent) variation budget
to real part `½ − R` and the reflected χ-term budget on each window ball hold, then above every
bound there is a height `τ` at which BOTH the annulus-chart floor and the boundary-circle floor hold
at level `ε`. This is the height-level datum the circle-data pinning gate turns into RH, once each
window center is a simple on-line carrier zero. -/
theorem window_floor_cofinal_of_line_cofinal (N : ℕ) {r₀ R t₀ t₁ ε : ℝ}
    (hR : 0 ≤ R) (hr₀R : r₀ ≤ R)
    (hbudget : (∑ n ∈ Finset.Icc 1 N, Real.log n * (n : ℝ) ^ (-(1/2 - R))) * R ≤ t₀ - t₁)
    (hline : ∀ M : ℝ, ∃ τ, M < τ ∧
      t₀ < ‖dirichletPoly N (((1/2 : ℝ) : ℂ) + (τ : ℂ) * I)‖)
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
  refine carrierFloorOn_charts_spheres_of_center N hR hr₀R hτfloor ?_ (hrefl τ)
  rw [hre]
  exact hbudget

end RHTower
