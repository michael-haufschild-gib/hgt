import GaloisForLFunctions.ExclusionOfTheCriticalState.TheBeyondTheWallPrimeBalanceExcludesTheState
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheProbeSamplesHaveNoFiniteRecurrence
import GaloisForLFunctions.SignedWindowCriticality.TheCollarHankelForm
import GaloisForLFunctions.HTGeometry.SpectralHardyTraceFormation

/-!
# The archimedean wall tail is a trivial-zero sum

The Lévy density `ω(x) = Σ_k e^{−(2k+½)x}` has its modes at `2k + ½`. After the first mode, which
cancels the positive charge, the rates `r_k = 2(k+1) + ½` are the reflected centred trivial zeros
`−σ_k` of SignedWindowCriticality, and the coefficients of the archimedean wall tail
`J_{≥1}F(p) = Σ_k L F(r_k)/(r_k − p)` are the trivial-zero moments `μ_{σ_k}(F) = ∫ F e^{−σ_k u}`
of the collar Hankel calculus.

* **Trivial-zero form** (`archimedeanWallTail_eq_trivialMoments`):
  `J_{≥1}F(p) = Σ_k μ_{σ_k}(F)/(−σ_k − p)`.
* **The trivial zeros see every profile of the energy domain** (`ae_eq_of_trivialMoments_eq`).
  Two profiles with the same trivial-zero moments agree almost everywhere; this extends
  `eq_zero_of_trivialMoments_eq_zero` from continuous collar tests to the whole half line.
  Mechanism: `L F − L G` is bounded and holomorphic on `Re w > 0` and vanishes at the
  Blaschke-divergent rates `r_k`, hence identically; then the probe samples agree.
* **The wall tail determines the profile** (`ae_eq_of_archimedeanWallTail_eventuallyEq`). The
  tail is holomorphic off the ray `[5/2, ∞)` (`differentiableOn_archimedeanWallTail_compl`), the
  slit plane is connected, and the coefficient at `r_j` is read off on the vertical `r_j + iε`
  (`wallCoeff_eq_of_eqOn`). Two profiles whose archimedean wall tails agree near one point agree:
  the archimedean side of the left formula alone pins down the profile.
* **Hankel inertia on the half line** (`collarHankel_neg_of_domain`,
  `exists_collarHankel_nonpos_of_domain`). For `m > 0` the collar Hankel form
  `e^m μ_{½}(F)² − Σ_k e^{2mσ_k} μ_{σ_k}(F)²` is negative at every profile of the energy domain
  with `μ_{½}(F) = 0` that is not almost everywhere zero, and every plane of the domain contains
  a nonzero direction with nonpositive form.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex Metric

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri HTGeometry
  SignedWindowCriticality CanonicalSystemOfTheWindowTower

/-! ### Rates and moments -/

/-- The `k`-th archimedean wall rate `r_k = 2(k+1) + ½ = −σ_k`. -/
def trivialRate (k : ℕ) : ℝ := 2 * ((k : ℝ) + 1) + 1 / 2

theorem trivialRate_eq_neg_trivialExponent (k : ℕ) : trivialRate k = -trivialExponent k := by
  unfold trivialRate trivialExponent
  ring

theorem le_trivialRate (k : ℕ) : (k : ℝ) + 1 ≤ trivialRate k := by
  unfold trivialRate
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

theorem trivialRate_pos (k : ℕ) : 0 < trivialRate k :=
  lt_of_lt_of_le (by positivity) (le_trivialRate k)

theorem ofReal_trivialRate (k : ℕ) :
    ((trivialRate k : ℝ) : ℂ) = 2 * ((k : ℂ) + 1) + 1 / 2 := by
  unfold trivialRate
  push_cast
  ring

/-- The transform at a wall rate is the trivial-zero moment. -/
theorem laplace_trivialRate (F : ℝ → ℝ) (k : ℕ) :
    negativeHalfLineLaplace (cx F) (trivialRate k : ℂ) = (leftMoment F (trivialExponent k) : ℂ) := by
  rw [negativeHalfLineLaplace_ofReal]
  unfold leftMoment
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only
  rw [trivialRate_eq_neg_trivialExponent]
  congr 2
  ring

/-- The `k`-th coefficient `L F(r_k)` of the wall tail. -/
def wallCoeff (F : ℝ → ℝ) (k : ℕ) : ℂ := negativeHalfLineLaplace (cx F) (trivialRate k : ℂ)

theorem archimedeanWallTail_eq_rate (F : ℝ → ℝ) (p : ℂ) :
    archimedeanWallTail F p = ∑' k : ℕ, wallCoeff F k / ((trivialRate k : ℂ) - p) := by
  unfold archimedeanWallTail wallCoeff
  refine tsum_congr fun k => ?_
  rw [ofReal_trivialRate]

/-- **The archimedean wall tail in trivial-zero form**: `J_{≥1}F(p) = Σ_k μ_{σ_k}(F)/(−σ_k − p)`. -/
theorem archimedeanWallTail_eq_trivialMoments (F : ℝ → ℝ) (p : ℂ) :
    archimedeanWallTail F p =
      ∑' k : ℕ, (leftMoment F (trivialExponent k) : ℂ) / (((-trivialExponent k : ℝ) : ℂ) - p) := by
  rw [archimedeanWallTail_eq_rate]
  refine tsum_congr fun k => ?_
  rw [wallCoeff, laplace_trivialRate, trivialRate_eq_neg_trivialExponent]

/-! ### The trivial zeros see every profile -/

theorem not_summable_trivialRate_blaschke :
    ¬ Summable fun k : ℕ => trivialRate k / (1 + trivialRate k ^ 2) := by
  intro hs
  have hle : ∀ k : ℕ, (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ≤
      6 * (trivialRate k / (1 + trivialRate k ^ 2)) := by
    intro k
    have h1 := le_trivialRate k
    have h3 : trivialRate k ≤ 3 * ((k : ℝ) + 1) := by
      unfold trivialRate
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hr := trivialRate_pos k
    push_cast
    rw [mul_div_assoc', div_le_div_iff₀ hk (by positivity)]
    nlinarith
  have hsum : Summable fun k : ℕ => (1 : ℝ) / ((k + 1 : ℕ) : ℝ) :=
    Summable.of_nonneg_of_le (fun k => by positivity) hle (hs.mul_left 6)
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).mp hsum)

/-- **The trivial zeros see every profile of the energy domain.** -/
theorem ae_eq_of_trivialMoments_eq {F G : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hG : CriticalHalfLineEnergyDomain G)
    (h : ∀ k : ℕ, leftMoment F (trivialExponent k) = leftMoment G (trivialExponent k)) :
    F =ᵐ[volume] G := by
  set Φ : ℂ → ℂ := fun w => negativeHalfLineLaplace (cx F) w - negativeHalfLineLaplace (cx G) w
    with hΦ
  have hΦd : DifferentiableOn ℂ Φ {w : ℂ | 0 < w.re} :=
    ((differentiableOn_laplace_of_sq hF.meas hF.support hF.exponential).sub
      (differentiableOn_laplace_of_sq hG.meas hG.support hG.exponential)).mono
        fun w (hw : 0 < w.re) => show -(8 / 2) < w.re by linarith
  have hΦb : ∀ w : ℂ, 0 < w.re → ‖Φ w‖ ≤ halfPoleMass F + halfPoleMass G := fun w hw =>
    (norm_sub_le _ _).trans (add_le_add (norm_laplace_le_halfPoleMass hF (by linarith))
      (norm_laplace_le_halfPoleMass hG (by linarith)))
  have hzero := eqOn_zero_of_bounded_of_blaschke_divergent (δ := 0) le_rfl hΦd hΦb
    (Λ := trivialRate) (fun a b hab => by
      unfold trivialRate at hab
      exact_mod_cast (show (a : ℝ) = b by linarith))
    (by
      rw [Nat.cofinite_eq_atTop]
      exact tendsto_atTop_mono (fun k => (le_trivialRate k).trans' (by linarith))
        tendsto_natCast_atTop_atTop)
    trivialRate_pos (fun k => by
      simp only [hΦ]
      rw [laplace_trivialRate, laplace_trivialRate, h k, sub_self])
    not_summable_trivialRate_blaschke
  refine (criticalProbeSample_eq_iff_ae hF hG).mp (funext fun n => ?_)
  have h5 := hzero ((5 + n : ℝ) : ℂ) (by simp; positivity)
  simp only [hΦ, sub_eq_zero, negativeHalfLineLaplace_ofReal, Complex.ofReal_inj] at h5
  exact h5

/-- A profile of the energy domain with vanishing trivial-zero moments vanishes. -/
theorem ae_eq_zero_of_trivialMoments_eq_zero {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (h : ∀ k : ℕ, leftMoment F (trivialExponent k) = 0) : F =ᵐ[volume] 0 := by
  have hZ := hF.add_const_mul hF (-1)
  have hz : (fun u => F u + -1 * F u) = (0 : ℝ → ℝ) := by funext u; simp
  have h0 : ∀ k : ℕ, leftMoment (fun u => F u + -1 * F u) (trivialExponent k) = 0 := by
    intro k; rw [hz]; simp [leftMoment]
  have := ae_eq_of_trivialMoments_eq hF hZ fun k => by rw [h k, h0 k]
  rwa [hz] at this

/-! ### Holomorphy of the wall tail off the ray -/

/-- The ray `[5/2, ∞)` carrying the wall rates. -/
def wallRay : Set ℂ := {p : ℂ | p.im = 0 ∧ 5 / 2 ≤ p.re}

theorem isClosed_wallRay : IsClosed wallRay :=
  (isClosed_eq Complex.continuous_im continuous_const).inter
    (isClosed_le continuous_const Complex.continuous_re)

theorem trivialRate_mem_wallRay (k : ℕ) : ((trivialRate k : ℝ) : ℂ) ∈ wallRay := by
  refine ⟨Complex.ofReal_im _, ?_⟩
  rw [Complex.ofReal_re]
  unfold trivialRate
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

/-- The slit plane is star-convex about `0`, hence connected. -/
theorem isPreconnected_wallRay_compl : IsPreconnected wallRayᶜ := by
  have h0 : (0 : ℂ) ∈ wallRayᶜ := fun h => by have := h.2; norm_num at this
  refine (StarConvex.isPathConnected (a := (0 : ℂ)) (fun y hy a b ha hb hab => ?_)
    h0).isConnected.isPreconnected
  rintro ⟨him, hre⟩
  simp only [smul_zero, zero_add, Complex.real_smul, Complex.mul_im, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, sub_zero] at him hre
  rcases hb.lt_or_eq with hb0 | hb0
  · apply hy
    have hy0 : 0 < y.re := by
      by_contra h
      push Not at h
      nlinarith
    refine ⟨(mul_eq_zero.mp him).resolve_left hb0.ne', ?_⟩
    have hb1 : b ≤ 1 := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hb1 hy0.le]
  · rw [← hb0] at hre
    norm_num at hre

/-- A Laplace value at a positive real rate decays like the inverse square root of the rate. -/
theorem norm_laplace_ofReal_le {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {r : ℝ}
    (hr : 0 < r) :
    ‖negativeHalfLineLaplace (cx F) (r : ℂ)‖ ≤ (2 * (∫ u, F u ^ 2) + 1) / (4 * Real.sqrt r) := by
  set s := Real.sqrt r
  have hs : 0 < s := Real.sqrt_pos.mpr hr
  have hs2 : s ^ 2 = r := Real.sq_sqrt hr.le
  have hdom : Integrable fun u : ℝ => (1 / (2 * s)) * F u ^ 2 + (s / 2) * probe (2 * r) u :=
    (hF.sq.const_mul _).add ((integrable_probe (by positivity)).const_mul _)
  have hpt : ∀ u : ℝ, ‖cexp ((r : ℂ) * u) * cx F u‖ ≤
      (1 / (2 * s)) * F u ^ 2 + (s / 2) * probe (2 * r) u := by
    intro u
    rcases lt_or_ge u 0 with hu | hu
    · rw [norm_mul, norm_cexp_mul_ofReal, cx, Complex.ofReal_re, Complex.norm_real,
        Real.norm_eq_abs, probe_of_neg hu]
      set X := |F u| / Real.sqrt s
      set Y := Real.sqrt s * Real.exp (r * u)
      have hss : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.le
      have hXY : Real.exp (r * u) * |F u| = X * Y := by
        dsimp [X, Y]; field_simp [(Real.sqrt_pos.mpr hs).ne']
      have hX2 : (1 / (2 * s)) * F u ^ 2 = X ^ 2 / 2 := by
        dsimp [X]; rw [div_pow, sq_abs, hss]; ring
      have hY2 : (s / 2) * Real.exp ((2 * r) * u) = Y ^ 2 / 2 := by
        dsimp [Y]
        rw [mul_pow, hss, sq (Real.exp (r * u)), ← Real.exp_add,
          show r * u + r * u = (2 * r) * u by ring]
        ring
      rw [hXY, hX2, hY2]
      nlinarith [sq_nonneg (X - Y)]
    · simp [cx, hF.support u hu, probe_of_nonneg hu]
  refine (norm_integral_le_of_norm_le hdom (Eventually.of_forall hpt)).trans_eq ?_
  rw [integral_add (hF.sq.const_mul _) ((integrable_probe (by positivity)).const_mul _),
    integral_const_mul, integral_const_mul, integral_probe (by positivity)]
  field_simp [hs.ne', hr.ne']
  nlinarith [hs2]

theorem norm_wallCoeff_le {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) (k : ℕ) :
    ‖wallCoeff F k‖ ≤ (2 * (∫ u, F u ^ 2) + 1) / 4 * ((k : ℝ) + 1) ^ (-(1 / 2 : ℝ)) := by
  unfold wallCoeff
  have h := norm_laplace_ofReal_le hF (trivialRate_pos k)
  have hA : 0 ≤ 2 * (∫ u, F u ^ 2) + 1 := by
    have : 0 ≤ ∫ u, F u ^ 2 := integral_nonneg fun u => sq_nonneg (F u)
    linarith
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  rw [Real.rpow_neg hk.le, ← Real.sqrt_eq_rpow]
  refine h.trans ?_
  calc (2 * (∫ u, F u ^ 2) + 1) / (4 * Real.sqrt (trivialRate k))
      ≤ (2 * (∫ u, F u ^ 2) + 1) / (4 * Real.sqrt ((k : ℝ) + 1)) :=
        div_le_div_of_nonneg_left hA (by positivity)
          (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (le_trivialRate k)) (by norm_num))
    _ = (2 * (∫ u, F u ^ 2) + 1) / 4 * (Real.sqrt ((k : ℝ) + 1))⁻¹ := by ring

theorem summable_rpow_three_halves :
    Summable fun k : ℕ => ((k : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
  have hr := (summable_nat_add_iff 1).mpr
    (Real.summable_nat_rpow.mpr (by norm_num : -(3 / 2 : ℝ) < -1))
  exact hr.congr fun k => by push_cast; rfl

theorem rpow_neg_half_div (k : ℕ) :
    ((k : ℝ) + 1) ^ (-(1 / 2 : ℝ)) / ((k : ℝ) + 1) = ((k : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  rw [show (-(3 / 2 : ℝ)) = -(1 / 2) - 1 by norm_num, Real.rpow_sub_one hk.ne']

/-- **The wall tail is holomorphic off the ray `[5/2, ∞)`.** -/
theorem differentiableOn_archimedeanWallTail_compl {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) : DifferentiableOn ℂ (archimedeanWallTail F) wallRayᶜ := by
  intro p₀ hp₀
  have hne : wallRay.Nonempty := ⟨_, trivialRate_mem_wallRay 0⟩
  have hη : 0 < infDist p₀ wallRay := (isClosed_wallRay.notMem_iff_infDist_pos hne).mp hp₀
  set η := infDist p₀ wallRay with hη_def
  set M : ℝ := ‖p₀‖ + η / 2 + 1 with hM
  have hM1 : 1 ≤ M := by rw [hM]; have := norm_nonneg p₀; linarith
  set c : ℝ := min 1 (η / (2 * M)) with hc
  have hc0 : 0 < c := lt_min one_pos (by positivity)
  set K : ℝ := (2 * (∫ u, F u ^ 2) + 1) / 4 with hK
  have hK0 : 0 ≤ K := by
    have : 0 ≤ ∫ u, F u ^ 2 := integral_nonneg fun u => sq_nonneg (F u)
    rw [hK]; positivity
  -- the rates stay at distance `c (k + 1)` from the ball
  have hdist : ∀ p ∈ ball p₀ (η / 2), ∀ k : ℕ,
      c * ((k : ℝ) + 1) ≤ ‖((trivialRate k : ℝ) : ℂ) - p‖ := by
    intro p hp k
    have hpd : dist p p₀ < η / 2 := hp
    have h1 : η / 2 ≤ ‖((trivialRate k : ℝ) : ℂ) - p‖ := by
      have hinf : infDist p wallRay ≤ dist p ((trivialRate k : ℝ) : ℂ) :=
        infDist_le_dist_of_mem (trivialRate_mem_wallRay k)
      have htri : infDist p₀ wallRay ≤ infDist p wallRay + dist p₀ p :=
        infDist_le_infDist_add_dist
      rw [dist_eq_norm, norm_sub_rev] at hinf
      rw [dist_comm] at htri
      linarith
    have h2 : trivialRate k - (M - 1) ≤ ‖((trivialRate k : ℝ) : ℂ) - p‖ := by
      have hre := Complex.re_le_norm (((trivialRate k : ℝ) : ℂ) - p)
      have hpre : p.re ≤ ‖p₀‖ + η / 2 := by
        have h3 := Complex.re_le_norm p
        have h4 := norm_sub_norm_le p p₀
        rw [← dist_eq_norm] at h4
        linarith
      rw [Complex.sub_re, Complex.ofReal_re] at hre
      rw [hM]
      linarith
    have hk0 : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
    rcases le_or_gt M ((k : ℝ) + 1) with hk | hk
    · have hc1 : c ≤ 1 := min_le_left _ _
      have : c * ((k : ℝ) + 1) ≤ (k : ℝ) + 1 := by nlinarith
      have hrt : trivialRate k = 2 * ((k : ℝ) + 1) + 1 / 2 := rfl
      linarith
    · have : c * ((k : ℝ) + 1) ≤ η / 2 := by
        have hm := min_le_right 1 (η / (2 * M))
        have hMpos : 0 < M := by linarith
        calc c * ((k : ℝ) + 1) ≤ η / (2 * M) * M :=
              mul_le_mul hm hk.le hk0 (by positivity)
          _ = η / 2 := by field_simp
      linarith
  have hball : DifferentiableOn ℂ (archimedeanWallTail F) (ball p₀ (η / 2)) := by
    have hfun : archimedeanWallTail F =
        fun p => ∑' k : ℕ, wallCoeff F k / ((trivialRate k : ℂ) - p) :=
      funext (archimedeanWallTail_eq_rate F)
    rw [hfun]
    refine differentiableOn_tsum_of_summable_norm
      (summable_rpow_three_halves.mul_left (K / c)) (fun k => ?_) isOpen_ball
      (fun k p hp => ?_)
    · intro p hp
      have hpos : 0 < ‖((trivialRate k : ℝ) : ℂ) - p‖ :=
        lt_of_lt_of_le (by positivity) (hdist p hp k)
      exact ((differentiableAt_const _).div ((differentiableAt_const _).sub differentiableAt_id)
        (norm_pos_iff.mp hpos)).differentiableWithinAt
    · rw [norm_div]
      calc ‖wallCoeff F k‖ / ‖((trivialRate k : ℝ) : ℂ) - p‖
          ≤ (K * ((k : ℝ) + 1) ^ (-(1 / 2 : ℝ))) / (c * ((k : ℝ) + 1)) :=
            div_le_div₀ (by positivity) (norm_wallCoeff_le hF k) (by positivity) (hdist p hp k)
        _ = K / c * (((k : ℝ) + 1) ^ (-(1 / 2 : ℝ)) / ((k : ℝ) + 1)) := by
            field_simp
        _ = K / c * ((k : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by rw [rpow_neg_half_div]
  exact (hball.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self (by positivity)))).differentiableWithinAt

/-- Tails that agree near a point of the slit plane agree on the slit plane. -/
theorem eqOn_archimedeanWallTail_of_eventuallyEq {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G) {p₀ : ℂ}
    (hp₀ : p₀ ∉ wallRay) (h : archimedeanWallTail F =ᶠ[𝓝 p₀] archimedeanWallTail G) :
    EqOn (archimedeanWallTail F) (archimedeanWallTail G) wallRayᶜ :=
  ((differentiableOn_archimedeanWallTail_compl hF).analyticOnNhd
      isClosed_wallRay.isOpen_compl).eqOn_of_preconnected_of_eventuallyEq
    ((differentiableOn_archimedeanWallTail_compl hG).analyticOnNhd isClosed_wallRay.isOpen_compl)
    isPreconnected_wallRay_compl hp₀ h

/-! ### Reading the coefficients on verticals -/

/-- Off the diagonal the wall rates are separated proportionally to the index. -/
theorem le_norm_trivialRate_sub {j k : ℕ} (hjk : k ≠ j) (ε : ℝ) :
    ((k : ℝ) + 1) / ((j : ℝ) + 1) ≤
      ‖((trivialRate k : ℝ) : ℂ) - (((trivialRate j : ℝ) : ℂ) + ε * I)‖ := by
  have hre := Complex.abs_re_le_norm (((trivialRate k : ℝ) : ℂ) - (((trivialRate j : ℝ) : ℂ) + ε * I))
  have he : (((trivialRate k : ℝ) : ℂ) - (((trivialRate j : ℝ) : ℂ) + ε * I)).re =
      2 * ((k : ℝ) - j) := by
    simp [trivialRate]
    ring
  rw [he] at hre
  refine le_trans ?_ hre
  have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  rw [div_le_iff₀ hj]
  rcases Nat.lt_or_gt_of_ne hjk with h | h
  · have h' : (k : ℝ) + 1 ≤ j := by exact_mod_cast h
    rw [abs_of_neg (by linarith)]
    nlinarith [show (0 : ℝ) ≤ k by positivity]
  · have h' : (j : ℝ) + 1 ≤ k := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]
    nlinarith [show (0 : ℝ) ≤ j by positivity]

/-- At `r_j + iε` the wall tail is the `j`-th pole plus a rest bounded uniformly in `ε`. -/
theorem exists_bound_wallTail_vertical {H : ℝ → ℝ} (hH : CriticalHalfLineEnergyDomain H)
    (j : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ ε : ℝ, 0 < ε →
      ‖((ε : ℂ) * I) * archimedeanWallTail H (((trivialRate j : ℝ) : ℂ) + ε * I) +
        wallCoeff H j‖ ≤ ε * B := by
  set K : ℝ := (2 * (∫ u, H u ^ 2) + 1) / 4 with hK
  have hK0 : 0 ≤ K := by
    have : 0 ≤ ∫ u, H u ^ 2 := integral_nonneg fun u => sq_nonneg (H u)
    rw [hK]; positivity
  set b : ℕ → ℝ := fun k => K * ((j : ℝ) + 1) * ((k : ℝ) + 1) ^ (-(3 / 2 : ℝ)) with hb
  have hb_sum : Summable b := summable_rpow_three_halves.mul_left _
  have hb0 : ∀ k, 0 ≤ b k := fun k => by rw [hb]; positivity
  refine ⟨∑' k, b k, tsum_nonneg hb0, fun ε hε => ?_⟩
  set p : ℂ := ((trivialRate j : ℝ) : ℂ) + ε * I with hp
  set f : ℕ → ℂ := fun k => wallCoeff H k / (((trivialRate k : ℝ) : ℂ) - p) with hf
  set g : ℕ → ℂ := fun k => if k = j then 0 else f k with hg
  have hgb : ∀ k, ‖g k‖ ≤ b k := by
    intro k
    by_cases hk : k = j
    · rw [show g k = 0 by simp [hg, hk], norm_zero]
      exact hb0 k
    · rw [show g k = f k by simp [hg, hk]]
      have hd := le_norm_trivialRate_sub hk ε
      have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have hjpos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
      simp only [hf, norm_div]
      calc ‖wallCoeff H k‖ / ‖((trivialRate k : ℝ) : ℂ) - p‖
          ≤ (K * ((k : ℝ) + 1) ^ (-(1 / 2 : ℝ))) / (((k : ℝ) + 1) / ((j : ℝ) + 1)) :=
            div_le_div₀ (by positivity) (norm_wallCoeff_le hH k) (by positivity) hd
        _ = K * ((j : ℝ) + 1) * (((k : ℝ) + 1) ^ (-(1 / 2 : ℝ)) / ((k : ℝ) + 1)) := by
            field_simp
        _ = b k := by rw [rpow_neg_half_div]
  have hgs : Summable g := Summable.of_norm_bounded hb_sum hgb
  have hfs : Summable f := by
    have hs : Summable fun k => if k = j then f j else 0 :=
      summable_of_ne_finset_zero (s := {j}) fun k hk => by
        rw [Finset.mem_singleton] at hk
        simp [hk]
    refine (hgs.add hs).congr fun k => ?_
    by_cases hk : k = j
    · rw [hk]; simp [hg]
    · simp [hg, hk]
  have htail : archimedeanWallTail H p = f j + ∑' k, g k := by
    rw [archimedeanWallTail_eq_rate]
    exact hfs.tsum_eq_add_tsum_ite j
  have hεI : ((ε : ℂ) * I) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hε.ne') Complex.I_ne_zero
  have hfj : ((ε : ℂ) * I) * f j = -wallCoeff H j := by
    simp only [hf]
    rw [hp, show ((trivialRate j : ℝ) : ℂ) - (((trivialRate j : ℝ) : ℂ) + ε * I) = -((ε : ℂ) * I)
      by ring, div_neg, mul_neg]
    congr 1
    have hε0 : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hε.ne'
    field_simp
  rw [htail, mul_add, hfj, show -wallCoeff H j + (ε : ℂ) * I * ∑' k, g k + wallCoeff H j =
    (ε : ℂ) * I * ∑' k, g k by ring, norm_mul, norm_mul, Complex.norm_real, Complex.norm_I,
    mul_one, Real.norm_of_nonneg hε.le]
  refine mul_le_mul_of_nonneg_left ?_ hε.le
  exact (norm_tsum_le_tsum_norm hgs.norm).trans (hgs.norm.tsum_le_tsum hgb hb_sum)

/-- **Equal tails have equal coefficients.** -/
theorem wallCoeff_eq_of_eqOn {F G : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hG : CriticalHalfLineEnergyDomain G)
    (h : EqOn (archimedeanWallTail F) (archimedeanWallTail G) wallRayᶜ) (j : ℕ) :
    wallCoeff F j = wallCoeff G j := by
  obtain ⟨BF, hBF, hF'⟩ := exists_bound_wallTail_vertical hF j
  obtain ⟨BG, hBG, hG'⟩ := exists_bound_wallTail_vertical hG j
  have hle : ∀ ε : ℝ, 0 < ε → ‖wallCoeff F j - wallCoeff G j‖ ≤ ε * (BF + BG) := by
    intro ε hε
    have hmem : ((trivialRate j : ℝ) : ℂ) + ε * I ∈ wallRayᶜ := fun hm => by
      have := hm.1
      simp at this
      exact hε.ne' this
    have he := h hmem
    have hd : wallCoeff F j - wallCoeff G j =
        (((ε : ℂ) * I) * archimedeanWallTail F (((trivialRate j : ℝ) : ℂ) + ε * I) +
          wallCoeff F j) -
        (((ε : ℂ) * I) * archimedeanWallTail G (((trivialRate j : ℝ) : ℂ) + ε * I) +
          wallCoeff G j) := by
      rw [he]; ring
    rw [hd]
    calc _ ≤ _ := norm_sub_le _ _
      _ ≤ ε * BF + ε * BG := add_le_add (hF' ε hε) (hG' ε hε)
      _ = ε * (BF + BG) := by ring
  by_contra hne
  have hpos : 0 < ‖wallCoeff F j - wallCoeff G j‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have := hle (‖wallCoeff F j - wallCoeff G j‖ / (2 * (BF + BG + 1))) (by positivity)
  have hB : 0 < BF + BG + 1 := by linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at this
  nlinarith

/-- **The archimedean wall tail determines the profile.** Two profiles of the energy domain whose
tails agree near one point off the ray `[5/2, ∞)` agree almost everywhere. -/
theorem ae_eq_of_archimedeanWallTail_eventuallyEq {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G) {p₀ : ℂ}
    (hp₀ : p₀ ∉ wallRay) (h : archimedeanWallTail F =ᶠ[𝓝 p₀] archimedeanWallTail G) :
    F =ᵐ[volume] G := by
  have hEq := eqOn_archimedeanWallTail_of_eventuallyEq hF hG hp₀ h
  refine ae_eq_of_trivialMoments_eq hF hG fun k => ?_
  have hc := wallCoeff_eq_of_eqOn hF hG hEq k
  unfold wallCoeff at hc
  rw [laplace_trivialRate, laplace_trivialRate] at hc
  exact_mod_cast hc

/-! ### Hankel inertia on the half line -/

theorem abs_leftMoment_trivial_le_halfPoleMass {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (k : ℕ) : |leftMoment F (trivialExponent k)| ≤ halfPoleMass F := by
  have h := norm_laplace_le_halfPoleMass hF (p := ((trivialRate k : ℝ) : ℂ))
    (by rw [Complex.ofReal_re]; linarith [trivialRate_pos k])
  rwa [laplace_trivialRate, Complex.norm_real, Real.norm_eq_abs] at h

/-- The trivial-zero squares of a profile are summable at every positive Hankel distance. -/
theorem summable_trivialSquares_of_domain {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {m : ℝ} (hm : 0 < m) :
    Summable fun k : ℕ =>
      Real.exp (2 * m * trivialExponent k) * leftMoment F (trivialExponent k) ^ 2 := by
  have hgeo : Summable fun k : ℕ => halfPoleMass F ^ 2 * Real.exp (k * (-(4 * m))) :=
    (Real.summable_exp_nat_mul_iff.mpr (by linarith)).mul_left _
  refine hgeo.of_nonneg_of_le (fun k => by positivity) fun k => ?_
  have hsq : leftMoment F (trivialExponent k) ^ 2 ≤ halfPoleMass F ^ 2 := by
    have h := abs_leftMoment_trivial_le_halfPoleMass hF k
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have hexp : Real.exp (2 * m * trivialExponent k) ≤ Real.exp (k * (-(4 * m))) := by
    refine Real.exp_le_exp.mpr ?_
    unfold trivialExponent
    nlinarith
  calc Real.exp (2 * m * trivialExponent k) * leftMoment F (trivialExponent k) ^ 2
      ≤ Real.exp (k * (-(4 * m))) * halfPoleMass F ^ 2 :=
        mul_le_mul hexp hsq (sq_nonneg _) (Real.exp_pos _).le
    _ = _ := by ring

/-- **The collar Hankel form is negative on the pole hyperplane of the energy domain.** -/
theorem collarHankel_neg_of_domain {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {m : ℝ}
    (hm : 0 < m) (hpole : leftMoment F (1 / 2) = 0) (hne : ¬ F =ᵐ[volume] 0) :
    collarHankel m F < 0 := by
  obtain ⟨k, hk⟩ : ∃ k, leftMoment F (trivialExponent k) ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hne (ae_eq_zero_of_trivialMoments_eq_zero hF hall)
  have hpos := (summable_trivialSquares_of_domain hF hm).tsum_pos (fun k => by positivity) k
    (mul_pos (Real.exp_pos _) (by positivity))
  unfold collarHankel
  rw [hpole]
  linarith

/-- The pole moment `μ_{½}(G) = ∫ G e^{−u/2}` of a profile is an absolutely convergent integral. -/
theorem integrable_mul_exp_neg_half {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G) :
    Integrable fun u => G u * Real.exp (-(1 / 2 * u)) := by
  refine (integrable_abs_mul_exp_of_domain hG (c := -(1 / 2)) (by norm_num)).mono'
    (hG.meas.mul (by fun_prop)).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), neg_mul]

/-- **Every plane of the energy domain carries a nonpositive Hankel direction**: the collar Hankel
form has at most one positive square on the half line. -/
theorem exists_collarHankel_nonpos_of_domain {G₁ G₂ : ℝ → ℝ}
    (h₁ : CriticalHalfLineEnergyDomain G₁) (h₂ : CriticalHalfLineEnergyDomain G₂) (m : ℝ) :
    ∃ s t : ℝ, (s, t) ≠ (0, 0) ∧ collarHankel m (fun u => s * G₁ u + t * G₂ u) ≤ 0 := by
  have hlin : ∀ s t : ℝ, leftMoment (fun u => s * G₁ u + t * G₂ u) (1 / 2) =
      s * leftMoment G₁ (1 / 2) + t * leftMoment G₂ (1 / 2) := by
    intro s t
    unfold leftMoment
    simp_rw [add_mul, mul_assoc]
    rw [integral_add ((integrable_mul_exp_neg_half h₁).const_mul s)
      ((integrable_mul_exp_neg_half h₂).const_mul t), integral_const_mul, integral_const_mul]
  have hnonpos : ∀ s t : ℝ, leftMoment (fun u => s * G₁ u + t * G₂ u) (1 / 2) = 0 →
      collarHankel m (fun u => s * G₁ u + t * G₂ u) ≤ 0 := by
    intro s t h0
    unfold collarHankel
    rw [h0]
    have : 0 ≤ ∑' k : ℕ, Real.exp (2 * m * trivialExponent k) *
        leftMoment (fun u => s * G₁ u + t * G₂ u) (trivialExponent k) ^ 2 :=
      tsum_nonneg fun k => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_sub]
    linarith
  by_cases h0 : leftMoment G₁ (1 / 2) = 0 ∧ leftMoment G₂ (1 / 2) = 0
  · exact ⟨1, 0, by simp, hnonpos 1 0 (by rw [hlin, h0.1, h0.2]; ring)⟩
  · refine ⟨leftMoment G₂ (1 / 2), -leftMoment G₁ (1 / 2), fun he => h0 ?_,
      hnonpos _ _ (by rw [hlin]; ring)⟩
    simp only [Prod.mk.injEq, neg_eq_zero] at he
    exact ⟨he.2, he.1⟩

#print axioms ae_eq_of_archimedeanWallTail_eventuallyEq
#print axioms collarHankel_neg_of_domain
#print axioms exists_collarHankel_nonpos_of_domain

end GaloisForLFunctions.ExclusionOfTheCriticalState
