import GaloisForLFunctions.RHTower.ZetaSelfReturnThresholdIsTheDistanceToNonvanishingTargets

/-!
# The self-return threshold reads the vanishing order

At a zero `z₀` of `ζ` in the strip, of order `D = analyticOrderNatAt ζ z₀ ≥ 1`, write
`ζ(z) = (z − z₀)^D g(z)` near `z₀` with `g` analytic and `g(z₀) ≠ 0`.  The self-return threshold
`d(z₀, r) = zetaNonvanishingDistance z₀ r` of the disc `closedBall z₀ r` then satisfies, for all
small `r`,

  `|g(z₀)|/4 · r^D ≤ d(z₀, r) ≤ 4 · 3^D · |g(z₀)| · r^D`

(`exists_vanishingOrder_bounds_zetaNonvanishingDistance`).  The lower bound is the minimum
modulus principle on the circle `|z − z₀| = r`, where `|ζ| ≥ r^D |g(z₀)|/2`
(`half_le_zetaNonvanishingDistance_of_sphere`); the upper bound is the admissible target
`(z − z₀ − 2r)^D g(z)`, nonvanishing on `ball z₀ (3r/2)` (`zetaNonvanishingDistance_le_of_target`).
So the threshold exponent `log d(z₀, r)/log r → D` as `r → 0` reads the multiplicity of the zero,
while `d(z₀, r) = 0` for small `r` exactly when `ζ(z₀) ≠ 0`.  With the self-return dichotomy: around
a zero of order `D` the `ε`-self-returns are power-saving rare for `ε < |g(z₀)| r^D/4` and have
positive lower density for `ε > 4·3^D |g(z₀)| r^D` (`zetaReturnSet_volume_dichotomy_at_zero`).
The multiplicity of a hypothetical off-line zero is therefore visible in the return statistics
of the orbit `ζ(· + iτ)` at the scale `r^D`.
-/

open Complex Filter Topology Set Metric MeasureTheory

namespace RHTower

noncomputable section

/-! ## 1. Two-sided control of the threshold -/

/-- **Lower bound from a circle.**  If `ζ(z₀) = 0` and `|ζ| ≥ m` on the circle `|z − z₀| = r`,
then `d(z₀, r) ≥ m/2`: an admissible target within `m/2` of `ζ` would vanish inside the circle by
the minimum modulus principle. -/
theorem half_le_zetaNonvanishingDistance_of_sphere {z₀ : ℂ} {r m : ℝ} (hr : 0 < r)
    (h1 : z₀.re + r < 1) (hz : riemannZeta z₀ = 0)
    (hm : ∀ z ∈ sphere z₀ r, m ≤ ‖riemannZeta z‖) :
    m / 2 ≤ zetaNonvanishingDistance z₀ r := by
  by_contra hlt
  push Not at hlt
  obtain ⟨g, ⟨η, hη, hg, hg0⟩, hclose⟩ := mem_zetaNonvanishingTolerances_of_distance_lt h1 hlt
  have hball : closedBall z₀ r ⊆ ball z₀ (r + η) := closedBall_subset_ball (by linarith)
  have hdiff : DifferentiableOn ℂ g (closedBall z₀ r) := fun z hz =>
    (hg z (hball hz)).differentiableAt.differentiableWithinAt
  have hsph : ∀ z ∈ sphere z₀ r, ‖g z₀‖ < ‖g z‖ := by
    intro z hzs
    have h1' := hclose z₀ (mem_closedBall_self hr.le)
    have h2' := hclose z (sphere_subset_closedBall hzs)
    have h3' := hm z hzs
    have h4 := norm_sub_norm_le (riemannZeta z) (g z)
    rw [hz, zero_sub, norm_neg] at h1'
    linarith
  obtain ⟨z, hz, hgz⟩ := DeBruijn.exists_zero_of_norm_lt_sphere_on hr hdiff hsph
  exact hg0 z (hball (ball_subset_closedBall hz)) hgz

/-- **Upper bound from a target.**  An admissible target within `b` of `ζ` on the closed disc
bounds the threshold by `b`. -/
theorem zetaNonvanishingDistance_le_of_target {z₀ : ℂ} {r b : ℝ} (hr : 0 ≤ r) {g : ℂ → ℂ}
    (hg : g ∈ nonvanishingDiscTargets z₀ r)
    (hclose : ∀ z ∈ closedBall z₀ r, ‖riemannZeta z - g z‖ ≤ b) :
    zetaNonvanishingDistance z₀ r ≤ b := by
  refine le_of_forall_pos_lt_add fun δ hδ => ?_
  refine lt_of_le_of_lt (csInf_le (bddBelow_zetaNonvanishingTolerances z₀ hr) ?_)
    (by linarith : b + δ / 2 < b + δ)
  exact ⟨g, hg, fun z hz => by linarith [hclose z hz]⟩

/-! ## 2. The local factorization of `ζ` at a zero -/

/-- `ζ` has finite analytic order at every point other than `1`. -/
theorem analyticOrderAt_riemannZeta_ne_top_of_ne_one' {w : ℂ} (hw : w ≠ 1) :
    analyticOrderAt riemannZeta w ≠ ⊤ := by
  intro htop
  have hlocal : riemannZeta =ᶠ[nhds w] (0 : ℂ → ℂ) := by
    filter_upwards [analyticOrderAt_eq_top.mp htop] with z hz
    simpa using hz
  have hpreconnected : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
  have hglobal : Set.EqOn riemannZeta 0 ({1}ᶜ : Set ℂ) :=
    analyticOn_riemannZeta.eqOn_of_preconnected_of_eventuallyEq
      analyticOnNhd_const hpreconnected (by simpa using hw) hlocal
  have hzetaTwo : riemannZeta (2 : ℂ) = 0 := by
    simpa using hglobal (show (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) by norm_num)
  exact riemannZeta_ne_zero_of_one_le_re (by norm_num) hzetaTwo

/-- **Local factorization at a zero.**  Near a zero `z₀ ≠ 1`, `ζ(z) = (z − z₀)^D g(z)` with
`D = analyticOrderNatAt ζ z₀ ≥ 1` and `g` analytic, nonvanishing at `z₀`. -/
theorem exists_zeta_local_factorization {z₀ : ℂ} (hz₀ : z₀ ≠ 1) (hz : riemannZeta z₀ = 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧ g z₀ ≠ 0 ∧ 1 ≤ analyticOrderNatAt riemannZeta z₀ ∧
      ∀ᶠ z in 𝓝 z₀, riemannZeta z = (z - z₀) ^ analyticOrderNatAt riemannZeta z₀ * g z := by
  have hζan : AnalyticAt ℂ riemannZeta z₀ := analyticOn_riemannZeta z₀ (by simpa using hz₀)
  obtain ⟨g, hgan, hg0, hev⟩ :=
    hζan.analyticOrderAt_ne_top.mp (analyticOrderAt_riemannZeta_ne_top_of_ne_one' hz₀)
  refine ⟨g, hgan, hg0, one_le_toNat_analyticOrderAt_riemannZeta hz₀ hz, ?_⟩
  filter_upwards [hev] with z hz
  rw [hz, smul_eq_mul]

/-! ## 3. The vanishing-order law -/

/-- **The threshold reads the vanishing order.**  At a zero `z₀` of `ζ` in the strip, with the
local factorization `ζ = (z − z₀)^D g`, `D ≥ 1`, `g(z₀) ≠ 0`: for all small `r` the disc
`closedBall z₀ r` has doubled closure in the strip and
`|g(z₀)|/4 · r^D ≤ d(z₀, r) ≤ 4 · 3^D · |g(z₀)| · r^D`. -/
theorem exists_vanishingOrder_bounds_zetaNonvanishingDistance {z₀ : ℂ} (hz : riemannZeta z₀ = 0)
    (h1 : 1 / 2 < z₀.re) (h2 : z₀.re < 1) :
    ∃ g : ℂ → ℂ, g z₀ ≠ 0 ∧ 1 ≤ analyticOrderNatAt riemannZeta z₀ ∧
      (∀ᶠ z in 𝓝 z₀, riemannZeta z = (z - z₀) ^ analyticOrderNatAt riemannZeta z₀ * g z) ∧
      ∃ r₀ > 0, ∀ r : ℝ, 0 < r → r ≤ r₀ →
        (1 / 2 < z₀.re - 2 * r ∧ z₀.re + 2 * r < 1) ∧
        ‖g z₀‖ / 4 * r ^ analyticOrderNatAt riemannZeta z₀ ≤ zetaNonvanishingDistance z₀ r ∧
        zetaNonvanishingDistance z₀ r ≤
          4 * 3 ^ analyticOrderNatAt riemannZeta z₀ * ‖g z₀‖ *
            r ^ analyticOrderNatAt riemannZeta z₀ := by
  have hz₀ : z₀ ≠ 1 := by
    intro h
    rw [h] at h2
    simp at h2
  obtain ⟨g, hgan, hg0, hD1, hev⟩ := exists_zeta_local_factorization hz₀ hz
  obtain ⟨D, hD⟩ : ∃ D : ℕ, D = analyticOrderNatAt riemannZeta z₀ := ⟨_, rfl⟩
  rw [← hD] at hev hD1 ⊢
  refine ⟨g, hg0, hD1, hev, ?_⟩
  -- the factorization, analyticity of `g` and the two-sided bound on `|g|` hold on small balls
  obtain ⟨R₁, hR₁, hfac⟩ := Metric.eventually_nhds_iff_ball.mp hev
  obtain ⟨R₂, hR₂, hgan'⟩ := Metric.eventually_nhds_iff_ball.mp hgan.eventually_analyticAt
  have hg0' : 0 < ‖g z₀‖ := norm_pos_iff.mpr hg0
  obtain ⟨R₃, hR₃, hgcont⟩ := Metric.continuousAt_iff.mp hgan.continuousAt (‖g z₀‖ / 2)
    (by positivity)
  have hglow : ∀ z ∈ ball z₀ R₃, ‖g z₀‖ / 2 < ‖g z‖ ∧ ‖g z‖ < 3 * ‖g z₀‖ / 2 := by
    intro z hz
    have h := hgcont (mem_ball.mp hz)
    rw [dist_eq_norm] at h
    have h4 := norm_sub_norm_le (g z) (g z₀)
    have h5 := norm_sub_norm_le (g z₀) (g z)
    rw [norm_sub_rev (g z₀)] at h5
    constructor <;> linarith
  obtain ⟨R, hR⟩ : ∃ R : ℝ,
      R = min (min R₁ R₂) (min R₃ (min ((z₀.re - 1 / 2) / 2) ((1 - z₀.re) / 2))) := ⟨_, rfl⟩
  have hR0 : 0 < R := by
    rw [hR]
    exact lt_min (lt_min hR₁ hR₂) (lt_min hR₃ (lt_min (by linarith) (by linarith)))
  have hRR₁ : R ≤ R₁ := by rw [hR]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hRR₂ : R ≤ R₂ := by rw [hR]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hRR₃ : R ≤ R₃ := by rw [hR]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hRa : R ≤ (z₀.re - 1 / 2) / 2 := by
    rw [hR]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hRb : R ≤ (1 - z₀.re) / 2 := by
    rw [hR]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨R / 2, by positivity, fun r hr hrR => ⟨⟨by linarith, by linarith⟩, ?_, ?_⟩⟩
  · -- lower bound: `|ζ| = r^D |g| ≥ r^D |g(z₀)|/2` on the circle of radius `r`
    have hm : ∀ z ∈ sphere z₀ r, r ^ D * (‖g z₀‖ / 2) ≤ ‖riemannZeta z‖ := by
      intro z hz
      have hzn := mem_sphere_iff_norm.mp hz
      have hzb : z ∈ ball z₀ R := by
        rw [mem_ball_iff_norm, hzn]; linarith
      rw [hfac z (ball_subset_ball hRR₁ hzb), norm_mul, norm_pow, hzn]
      exact mul_le_mul_of_nonneg_left (hglow z (ball_subset_ball hRR₃ hzb)).1.le
        (pow_nonneg hr.le D)
    have := half_le_zetaNonvanishingDistance_of_sphere hr (by linarith) hz hm
    calc ‖g z₀‖ / 4 * r ^ D = r ^ D * (‖g z₀‖ / 2) / 2 := by ring
      _ ≤ _ := this
  · -- upper bound: the admissible target `(z − z₀ − 2r)^D g(z)`
    obtain ⟨c, hc⟩ : ∃ c : ℂ, c = ((2 * r : ℝ) : ℂ) := ⟨_, rfl⟩
    have hcn : ‖c‖ = 2 * r := by rw [hc, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    have hmem : (fun z => (z - z₀ - c) ^ D * g z) ∈ nonvanishingDiscTargets z₀ r := by
      refine ⟨r / 2, by positivity, fun z hz => ?_, fun z hz hzero => ?_⟩
      · have hzR : z ∈ ball z₀ R₂ := ball_subset_ball (by linarith) hz
        exact (((analyticAt_id.sub analyticAt_const).sub analyticAt_const).pow D).mul (hgan' z hzR)
      · have hzn := mem_ball_iff_norm.mp hz
        rcases mul_eq_zero.mp hzero with h | h
        · have h' : z - z₀ = c := by
            have := pow_eq_zero_iff (n := D) (by omega) |>.mp h
            exact sub_eq_zero.mp this
          have := congrArg norm h'
          rw [hcn] at this
          linarith
        · have := (hglow z (ball_subset_ball (by linarith) hz)).1
          rw [h, norm_zero] at this
          linarith
    refine zetaNonvanishingDistance_le_of_target hr.le hmem fun z hz => ?_
    have hzn := mem_closedBall_iff_norm.mp hz
    have hzR : z ∈ ball z₀ R := by rw [mem_ball_iff_norm]; linarith
    have hgz := (hglow z (ball_subset_ball hRR₃ hzR)).2
    rw [hfac z (ball_subset_ball hRR₁ hzR), ← sub_mul, norm_mul]
    have hpoly : ‖(z - z₀) ^ D - (z - z₀ - c) ^ D‖ ≤ 2 * 3 ^ D * r ^ D := by
      have hA : ‖(z - z₀) ^ D‖ ≤ (3 * r) ^ D := by
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (by linarith) D
      have hB : ‖(z - z₀ - c) ^ D‖ ≤ (3 * r) ^ D := by
        rw [norm_pow]
        refine pow_le_pow_left₀ (norm_nonneg _) ?_ D
        calc ‖z - z₀ - c‖ ≤ ‖z - z₀‖ + ‖c‖ := norm_sub_le _ _
          _ ≤ 3 * r := by rw [hcn]; linarith
      calc ‖(z - z₀) ^ D - (z - z₀ - c) ^ D‖ ≤ ‖(z - z₀) ^ D‖ + ‖(z - z₀ - c) ^ D‖ :=
            norm_sub_le _ _
        _ ≤ (3 * r) ^ D + (3 * r) ^ D := add_le_add hA hB
        _ = 2 * 3 ^ D * r ^ D := by rw [mul_pow]; ring
    have h3D : (0 : ℝ) ≤ 3 ^ D * r ^ D := by positivity
    calc ‖(z - z₀) ^ D - (z - z₀ - c) ^ D‖ * ‖g z‖
        ≤ (2 * 3 ^ D * r ^ D) * (3 * ‖g z₀‖ / 2) :=
          mul_le_mul hpoly hgz.le (norm_nonneg _) (by positivity)
      _ = 3 * 3 ^ D * ‖g z₀‖ * r ^ D := by ring
      _ ≤ 4 * 3 ^ D * ‖g z₀‖ * r ^ D := by nlinarith

/-- **The self-return dichotomy at a zero, at the scale of its order.**  Around a zero of order
`D` with cofactor value `g(z₀)`, for all small `r`: the `ε`-self-returns on `closedBall z₀ r` are
power-saving rare for `ε < |g(z₀)| r^D/4` and have positive lower density for
`ε > 4·3^D |g(z₀)| r^D`. -/
theorem zetaReturnSet_volume_dichotomy_at_zero {z₀ : ℂ} (hz : riemannZeta z₀ = 0)
    (h1 : 1 / 2 < z₀.re) (h2 : z₀.re < 1) :
    ∃ g : ℂ → ℂ, g z₀ ≠ 0 ∧ 1 ≤ analyticOrderNatAt riemannZeta z₀ ∧
      (∀ᶠ z in 𝓝 z₀, riemannZeta z = (z - z₀) ^ analyticOrderNatAt riemannZeta z₀ * g z) ∧
      ∃ r₀ > 0, ∀ r : ℝ, 0 < r → r ≤ r₀ → ∀ ε : ℝ,
        (ε < ‖g z₀‖ / 4 * r ^ analyticOrderNatAt riemannZeta z₀ →
          ∃ θ : ℝ, θ < 1 ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
            volume (zetaReturnSet (closedBall z₀ r) ε ∩ Icc 0 T) ≤ ENNReal.ofReal (T ^ θ)) ∧
        (4 * 3 ^ analyticOrderNatAt riemannZeta z₀ * ‖g z₀‖ *
            r ^ analyticOrderNatAt riemannZeta z₀ < ε →
          ∃ c > 0, ∀ᶠ T : ℝ in atTop,
            ENNReal.ofReal (c * T) ≤ volume (zetaReturnSet (closedBall z₀ r) ε ∩ Icc 0 T)) := by
  obtain ⟨g, hg0, hD1, hev, r₀, hr₀, hbounds⟩ :=
    exists_vanishingOrder_bounds_zetaNonvanishingDistance hz h1 h2
  refine ⟨g, hg0, hD1, hev, r₀, hr₀, fun r hr hrr₀ ε => ?_⟩
  obtain ⟨⟨hm1, hm2⟩, hlow, hup⟩ := hbounds r hr hrr₀
  exact ⟨fun hε => (zetaReturnSet_volume_dichotomy hr hm1 hm2 ε).2 (hε.trans_le hlow),
    fun hε => (zetaReturnSet_volume_dichotomy hr hm1 hm2 ε).1 (hup.trans_lt hε)⟩

end

end RHTower
