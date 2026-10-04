import GaloisForLFunctions.RHTower.ThetaMovingCuspTotientReconstruction
import GaloisForLFunctions.RHTower.ThetaCriticalBoundaryMellinCharge
import GaloisForLFunctions.RHTower.ThetaCofinalCurrentSignChanges
import GaloisForLFunctions.HTGeometry.ZetaJetFreeness

/-!
# Moving-cusp reflection: the negative cusp and the one-unit spectral shear

The cofinal dual source `R_∞` has Mellin transform `F(w)/ζ(w − 1/2)` on `Re w > 3/2`.  Its
meromorphic continuation has, at every nontrivial zeta zero `ρ` of multiplicity `m`, a zero of
order `m` at `ρ − 1/2` and a pole of order `m` at `ρ + 1/2` (the one-unit spectral shear).

Landau's abscissa theorem then shows that `R_∞` takes both signs arbitrarily far into the negative
cusp: the tail transform would have to be singular at its real abscissa, yet `F(w)/ζ(w − 1/2)` is
holomorphic at every real `w > 1/2`, while the pole at `ρ + 1/2` puts the abscissa above `1/2`.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-! ## Gaussian decay on the positive ray -/

theorem exists_abs_movingCuspDualLimit_le_gaussian :
    ∃ B : ℝ, ∃ D : ℕ, 0 ≤ B ∧ ∀ u : ℝ, 0 ≤ u →
      |movingCuspDualLimit u| ≤ B * Real.exp (D * u) * Real.exp (-Real.pi * Real.exp (2 * u)) := by
  obtain ⟨C, D, hC, hk⟩ := gaussianLogTail_thetaCuspFullSource.tail
  set Z : ℝ := ∑' n : ℕ, (n : ℝ) ^ (D + 1) * Real.exp (-Real.pi * (n : ℝ) ^ 2)
  have hZs : Summable fun n : ℕ => (n : ℝ) ^ (D + 1) * Real.exp (-Real.pi * (n : ℝ) ^ 2) :=
    summable_pow_mul_exp_neg_nat_sq (D + 1) Real.pi_pos
  have hZ : 0 ≤ Z := tsum_nonneg fun n => by positivity
  refine ⟨C * Real.exp Real.pi * Z, D, by positivity, fun u hu => ?_⟩
  have hterm : ∀ n : ℕ, |movingCuspLimitWeight n * thetaCuspFullSource (u + Real.log n)| ≤
      C * Real.exp (D * u) * Real.exp (-Real.pi * Real.exp (2 * u)) *
        (Real.exp Real.pi * ((n : ℝ) ^ (D + 1) * Real.exp (-Real.pi * (n : ℝ) ^ 2))) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [movingCuspLimitWeight]
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < n := by linarith
    have hx : 0 ≤ u + Real.log n := by linarith [Real.log_nonneg hnR]
    have hkx := hk _ hx
    rw [abs_mul]
    have hw : |movingCuspLimitWeight n| ≤ (n : ℝ) ^ 1 := polyBoundedWeight_movingCuspLimitWeight n
    have hexpD : Real.exp (D * (u + Real.log n)) = Real.exp (D * u) * (n : ℝ) ^ D := by
      rw [mul_add, Real.exp_add, ← Real.rpow_natCast, Real.rpow_def_of_pos hnpos, mul_comm (Real.log n)]
    have hexp2 : Real.exp (-Real.pi * Real.exp (2 * (u + Real.log n))) ≤
        Real.exp (-Real.pi * Real.exp (2 * u)) * (Real.exp Real.pi * Real.exp (-Real.pi * (n : ℝ) ^ 2)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have hl : Real.exp (2 * Real.log n) = (n : ℝ) ^ 2 := by
        rw [← Real.exp_log (pow_pos hnpos 2), Real.log_pow]; norm_num
      rw [mul_add, Real.exp_add, hl]
      have h1 : 1 ≤ Real.exp (2 * u) := Real.one_le_exp (by linarith)
      have hn2 : 1 ≤ (n : ℝ) ^ 2 := by nlinarith
      nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_left (sub_nonneg.2 hn2) (sub_nonneg.2 h1)]
    calc |movingCuspLimitWeight n| * |thetaCuspFullSource (u + Real.log n)|
        ≤ (n : ℝ) ^ 1 * (C * (Real.exp (D * u) * (n : ℝ) ^ D) *
            (Real.exp (-Real.pi * Real.exp (2 * u)) * (Real.exp Real.pi * Real.exp (-Real.pi * (n : ℝ) ^ 2)))) := by
          refine mul_le_mul hw (hkx.trans ?_) (abs_nonneg _) (by positivity)
          rw [hexpD]
          exact mul_le_mul_of_nonneg_left hexp2 (by positivity)
      _ = _ := by ring
  have hsum : Summable fun n : ℕ => C * Real.exp (D * u) * Real.exp (-Real.pi * Real.exp (2 * u)) *
      (Real.exp Real.pi * ((n : ℝ) ^ (D + 1) * Real.exp (-Real.pi * (n : ℝ) ^ 2))) :=
    (hZs.mul_left _).mul_left _
  calc |movingCuspDualLimit u|
      ≤ ∑' n : ℕ, |movingCuspLimitWeight n * thetaCuspFullSource (u + Real.log n)| := by
        rw [movingCuspDualLimit, logShiftSeries, ← Real.norm_eq_abs]
        exact (norm_tsum_le_tsum_norm (summable_movingCuspDualLimit u).norm).trans_eq
          (tsum_congr fun n => Real.norm_eq_abs _)
    _ ≤ ∑' n : ℕ, C * Real.exp (D * u) * Real.exp (-Real.pi * Real.exp (2 * u)) *
          (Real.exp Real.pi * ((n : ℝ) ^ (D + 1) * Real.exp (-Real.pi * (n : ℝ) ^ 2))) :=
        Summable.tsum_le_tsum hterm (summable_movingCuspDualLimit u).abs hsum
    _ = C * Real.exp Real.pi * Z * Real.exp (D * u) * Real.exp (-Real.pi * Real.exp (2 * u)) := by
        rw [tsum_mul_left, tsum_mul_left]; ring

/-! ## The positive-ray transform is entire -/

/-- `P(w) = ∫_0^∞ e^{wu} R_∞(u) du`. -/
def movingCuspHeadTransform (w : ℂ) : ℂ :=
  ∫ y in Ioi (0 : ℝ), Complex.exp (w * y) * (movingCuspDualLimit y : ℂ)

theorem differentiable_movingCuspHeadTransform : Differentiable ℂ movingCuspHeadTransform := by
  intro w₀
  obtain ⟨B, D, hB, hR⟩ := exists_abs_movingCuspDualLimit_le_gaussian
  set b : ℝ := max (w₀.re + D + 2) 1
  have hb : 0 < b := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hmaj : IntegrableOn (fun y : ℝ => B * (Real.exp (b * y) *
      Real.exp (-(Real.pi * Real.exp (2 * y))))) (Ioi 0) :=
    ((integrable_exp_mul_exp_neg_mul_exp_two_mul hb Real.pi_pos).const_mul B).integrableOn
  have hC : ∀ y : ℝ, 0 < y → ∀ w : ℂ, w.re ≤ w₀.re + 1 →
      (1 + y) * Real.exp (w.re * y) * |movingCuspDualLimit y| ≤
        B * (Real.exp (b * y) * Real.exp (-(Real.pi * Real.exp (2 * y)))) := fun y hy w hw => by
    have hg := hR y hy.le
    have h1 : 1 + y ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
    have h2 : Real.exp y * Real.exp (w.re * y) * Real.exp (D * y) ≤ Real.exp (b * y) := by
      rw [← Real.exp_add, ← Real.exp_add]
      exact Real.exp_le_exp.2 (by nlinarith [le_max_left (w₀.re + D + 2) 1])
    calc (1 + y) * Real.exp (w.re * y) * |movingCuspDualLimit y|
        ≤ Real.exp y * Real.exp (w.re * y) * (B * Real.exp (D * y) *
            Real.exp (-Real.pi * Real.exp (2 * y))) := by gcongr
      _ = B * ((Real.exp y * Real.exp (w.re * y) * Real.exp (D * y)) *
            Real.exp (-(Real.pi * Real.exp (2 * y)))) := by ring_nf
      _ ≤ _ := by gcongr
  have hcont : ∀ w : ℂ, Continuous fun y : ℝ => Complex.exp (w * y) * (movingCuspDualLimit y : ℂ) :=
    fun w => (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul
      (Complex.continuous_ofReal.comp continuous_movingCuspDualLimit)
  have hball : ∀ w ∈ Metric.ball w₀ 1, w.re ≤ w₀.re + 1 := fun w hw => by
    have := (Complex.abs_re_le_norm (w - w₀)).trans (le_of_lt (by rwa [← dist_eq_norm]))
    rw [Complex.sub_re] at this
    linarith [le_abs_self (w.re - w₀.re)]
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun w y => Complex.exp (w * y) * (movingCuspDualLimit y : ℂ))
    (F' := fun w y => (y : ℂ) * (Complex.exp (w * y) * (movingCuspDualLimit y : ℂ)))
    (bound := fun y => B * (Real.exp (b * y) * Real.exp (-(Real.pi * Real.exp (2 * y)))))
    (Metric.ball_mem_nhds w₀ one_pos) (Eventually.of_forall fun w => (hcont w).aestronglyMeasurable)
    (hmaj.mono' (hcont w₀).aestronglyMeasurable ((ae_restrict_iff' measurableSet_Ioi).2
      (ae_of_all _ fun y hy => by
        rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
        have := hC y hy w₀ (by linarith)
        have hy0 : (0 : ℝ) < y := hy
        have hp := mul_nonneg (Real.exp_pos (w₀.re * y)).le (abs_nonneg (movingCuspDualLimit y))
        calc Real.exp (w₀.re * y) * |movingCuspDualLimit y|
            ≤ (1 + y) * (Real.exp (w₀.re * y) * |movingCuspDualLimit y|) :=
              le_mul_of_one_le_left hp (by linarith)
          _ ≤ _ := by rw [← mul_assoc]; exact this)))
    ((Complex.continuous_ofReal.mul (hcont w₀)).aestronglyMeasurable)
    ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun y hy w hw => by
      rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (show (0:ℝ) < y from hy)]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      have := hC y hy w (hball w hw)
      have hp := mul_nonneg (Real.exp_pos (w.re * y)).le (abs_nonneg (movingCuspDualLimit y))
      calc y * (Real.exp (w.re * y) * |movingCuspDualLimit y|)
          ≤ (1 + y) * (Real.exp (w.re * y) * |movingCuspDualLimit y|) :=
            mul_le_mul_of_nonneg_right (by linarith) hp
        _ ≤ _ := by rw [← mul_assoc]; exact this))
    hmaj (ae_of_all _ fun y w _ => by
      have := ((hasDerivAt_id w).mul_const (y : ℂ)).cexp.mul_const (movingCuspDualLimit y : ℂ)
      refine this.congr_deriv ?_
      simp only [id, one_mul]
      ring)
  exact h.2.differentiableAt

/-! ## The negative-cusp transform and its continuation -/

/-- The continuation `Gc(s) = F(s + 1/4)/ζ(s − 1/4) − P(s + 1/4)` of the negative-cusp transform
`∫_0^∞ R_∞(−L) e^{−(s+1/4)L} dL`. -/
def movingCuspNegativeTransform (s : ℂ) : ℂ :=
  XiC (Complex.I * (s + 1 / 4)) * zetaInvShift (s + 1 / 4 - 3 / 2) - movingCuspHeadTransform (s + 1 / 4)

theorem movingCuspNegativeTransform_eq {σ : ℝ} (hσ : 3 / 2 < σ) :
    IntegrableOn (fun L : ℝ => movingCuspDualLimit (-L) * Real.exp (-(L / 4)) * Real.exp (-σ * L))
      (Ioi 0) ∧
    ((∫ L in Ioi (0 : ℝ), movingCuspDualLimit (-L) * Real.exp (-(L / 4)) * Real.exp (-σ * L) : ℝ) : ℂ) =
      movingCuspNegativeTransform σ := by
  set w : ℝ := σ + 1 / 4
  have hw : 3 / 2 < w := by simp only [w]; linarith
  have hfun : ∀ L : ℝ, movingCuspDualLimit (-L) * Real.exp (-(L / 4)) * Real.exp (-σ * L) =
      movingCuspDualLimit (-L) * Real.exp (-w * L) := fun L => by
    rw [mul_assoc, ← Real.exp_add]; congr 2; simp only [w]; ring
  simp_rw [hfun]
  obtain ⟨hint, hval⟩ := integral_cexp_mul_movingCuspDualLimit (w := (w : ℂ)) (by simpa using hw)
  have hnorm : Integrable (fun L : ℝ => movingCuspDualLimit (-L) * Real.exp (-w * L)) := by
    have h := hint.norm.comp_neg
    refine h.mono' ((continuous_movingCuspDualLimit.comp continuous_neg).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
      (ae_of_all _ fun L => ?_)
    simp only [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    rw [show w * -L = -w * L by ring, mul_comm]
  refine ⟨hnorm.integrableOn, ?_⟩
  have hsplit := integral_add_compl (measurableSet_Ioi (a := (0 : ℝ))) hint
  rw [compl_Ioi, hval] at hsplit
  have hneg := integral_comp_neg_Iic (0 : ℝ)
    (fun x : ℝ => Complex.exp ((w : ℂ) * (-x : ℝ)) * (movingCuspDualLimit (-x) : ℂ))
  simp only [neg_neg, neg_zero] at hneg
  rw [← integral_complex_ofReal]
  have hcast : (fun L : ℝ => ((movingCuspDualLimit (-L) * Real.exp (-w * L) : ℝ) : ℂ)) =
      fun x : ℝ => Complex.exp ((w : ℂ) * (-x : ℝ)) * (movingCuspDualLimit (-x) : ℂ) := by
    funext x; push_cast; ring_nf
  rw [hcast, ← hneg, movingCuspNegativeTransform,
    show (σ : ℂ) + 1 / 4 = (w : ℂ) by simp [w],
    show (w : ℂ) - 3 / 2 = ((w : ℂ) - 1 / 2) - 1 by ring,
    zetaInvShift_eq (by simp; linarith), show (1 : ℂ) + ((w : ℂ) - 1 / 2 - 1) = (w : ℂ) - 1 / 2 by ring,
    movingCuspHeadTransform]
  linear_combination hsplit

theorem analyticAt_movingCuspNegativeTransform {s : ℂ} (hs : 1 / 4 < s.re) (hxi : xi (s - 1 / 4) ≠ 0) :
    AnalyticAt ℂ movingCuspNegativeTransform s := by
  have h1 : AnalyticAt ℂ (fun s : ℂ => XiC (Complex.I * (s + 1 / 4))) s :=
    (XiC_differentiable.analyticAt _).comp (analyticAt_const.mul (analyticAt_id.add analyticAt_const))
  have h2 : AnalyticAt ℂ (fun s : ℂ => zetaInvShift (s + 1 / 4 - 3 / 2)) s :=
    (analyticAt_zetaInvShift (by simp; linarith)
      (by rwa [show (1 : ℂ) + (s + 1 / 4 - 3 / 2) = s - 1 / 4 by ring])).comp
      ((analyticAt_id.add analyticAt_const).sub analyticAt_const)
  have h3 : AnalyticAt ℂ (fun s : ℂ => movingCuspHeadTransform (s + 1 / 4)) s :=
    (differentiable_movingCuspHeadTransform.analyticAt _).comp (analyticAt_id.add analyticAt_const)
  exact (h1.mul h2).sub h3

theorem XiC_I_mul_eq_xi_half_add (w : ℂ) : XiC (Complex.I * w) = xi (1 / 2 + w) := by
  rw [XiC, show 1 / 2 + Complex.I * w * Complex.I = 1 - (1 / 2 + w) by
    rw [mul_comm Complex.I w, mul_assoc, Complex.I_mul_I]; ring, xi_one_sub]

theorem not_meromorphicOrderAt_nonneg_movingCuspNegativeTransform {ε : ℂ} (hε : ε ≠ 0) {ρ : ℂ}
    (hρ : xi ρ = 0) (hρre : 0 < ρ.re) :
    ¬ 0 ≤ meromorphicOrderAt (fun s => ε * movingCuspNegativeTransform s) (ρ + 1 / 4) := by
  intro ho
  have hρ1 : ρ ≠ 1 := fun h => xi_ne_zero_of_real 1 (by rw [h] at hρ; simpa using hρ)
  have hρ0 : ρ ≠ 0 := fun h => xi_ne_zero_of_real 0 (by rw [h] at hρ; simpa using hρ)
  set t : ℂ → ℂ := fun s => s + 1 / 4 - 3 / 2
  have htan : AnalyticAt ℂ t (ρ + 1 / 4) := (analyticAt_id.add analyticAt_const).sub analyticAt_const
  have ht : t (ρ + 1 / 4) = ρ - 1 := by simp only [t]; ring
  set N : ℂ → ℂ := fun s => (1 + t s) * t s * Complex.Gammaℝ (1 + t s)
  have hNan : AnalyticAt ℂ N (ρ + 1 / 4) := by
    have hsh : AnalyticAt ℂ (fun s : ℂ => 1 + t s) (ρ + 1 / 4) := analyticAt_const.add htan
    have hval : 0 < (1 + t (ρ + 1 / 4)).re := by rw [ht]; simpa using hρre
    exact (hsh.mul htan).mul ((GaloisForLFunctions.HTGeometry.analyticAt_Gammaℝ hval).comp_of_eq hsh rfl)
  have hN0 : N (ρ + 1 / 4) ≠ 0 := by
    simp only [N, ht, show (1 : ℂ) + (ρ - 1) = ρ by ring]
    exact mul_ne_zero (mul_ne_zero hρ0 (sub_ne_zero.2 hρ1)) (Complex.Gammaℝ_ne_zero_of_re_pos hρre)
  have hxian : AnalyticAt ℂ (fun s => 2 * xi (1 + t s)) (ρ + 1 / 4) :=
    analyticAt_const.mul ((xi_differentiable.analyticAt _).comp (analyticAt_const.add htan))
  have hXan : AnalyticAt ℂ (fun s : ℂ => XiC (Complex.I * (s + 1 / 4))) (ρ + 1 / 4) :=
    (XiC_differentiable.analyticAt _).comp (analyticAt_const.mul (analyticAt_id.add analyticAt_const))
  have hXne : XiC (Complex.I * (ρ + 1 / 4 + 1 / 4)) ≠ 0 := by
    rw [XiC_I_mul_eq_xi_half_add, show (1 / 2 : ℂ) + (ρ + 1 / 4 + 1 / 4) = 1 - (-ρ) by ring, xi_one_sub]
    rw [show -ρ = 1 - (1 + ρ) by ring, xi_one_sub]
    exact xi_ne_zero_of_one_lt_re (by simp; linarith)
  have hPan : AnalyticAt ℂ (fun s => movingCuspHeadTransform (s + 1 / 4)) (ρ + 1 / 4) :=
    (differentiable_movingCuspHeadTransform.analyticAt _).comp (analyticAt_id.add analyticAt_const)
  have hZfun : (fun s => zetaInvShift (t s)) = fun s => N s / (2 * xi (1 + t s)) := rfl
  have hmero : MeromorphicAt (fun s => ε * movingCuspNegativeTransform s) (ρ + 1 / 4) := by
    have hZ : MeromorphicAt (fun s => zetaInvShift (t s)) (ρ + 1 / 4) := by
      rw [hZfun]; exact hNan.meromorphicAt.div hxian.meromorphicAt
    exact analyticAt_const.meromorphicAt.mul ((hXan.meromorphicAt.mul hZ).sub hPan.meromorphicAt)
  obtain ⟨c, hc⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hmero ho
  have hXnear : ∀ᶠ s in 𝓝[≠] (ρ + 1 / 4), XiC (Complex.I * (s + 1 / 4)) ≠ 0 :=
    nhdsWithin_le_nhds (hXan.continuousAt.eventually_ne hXne)
  have hZlim : Tendsto (fun s => zetaInvShift (t s)) (𝓝[≠] (ρ + 1 / 4))
      (𝓝 ((ε⁻¹ * c + movingCuspHeadTransform (ρ + 1 / 4 + 1 / 4)) /
        XiC (Complex.I * (ρ + 1 / 4 + 1 / 4)))) := by
    have h1 := ((hc.const_mul ε⁻¹).add (hPan.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)).div
      (hXan.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hXne
    refine h1.congr' ?_
    filter_upwards [hXnear] with s hs
    show (ε⁻¹ * (ε * movingCuspNegativeTransform s) + movingCuspHeadTransform (s + 1 / 4)) /
      XiC (Complex.I * (s + 1 / 4)) = zetaInvShift (t s)
    rw [movingCuspNegativeTransform, inv_mul_cancel_left₀ hε, div_eq_iff hs]
    ring
  have hxi_near : ∀ᶠ s in 𝓝[≠] (ρ + 1 / 4), xi (1 + t s) ≠ 0 := by
    have hmap : Tendsto (fun s => 1 + t s) (𝓝[≠] (ρ + 1 / 4)) (𝓝[≠] ρ) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have hcont : Continuous fun s => (1 : ℂ) + t s := by simp only [t]; fun_prop
        have h1 := hcont.tendsto (ρ + 1 / 4)
        rw [ht, show (1 : ℂ) + (ρ - 1) = ρ by ring] at h1
        exact h1.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        intro h
        apply hs
        simp only [Set.mem_singleton_iff, t] at h ⊢
        linear_combination h
    exact hmap.eventually (eventually_xi_ne_zero ρ)
  have hprod : ∀ᶠ s in 𝓝[≠] (ρ + 1 / 4), 2 * xi (1 + t s) * zetaInvShift (t s) = N s := by
    filter_upwards [hxi_near] with s hs
    have : 2 * xi (1 + t s) ≠ 0 := mul_ne_zero two_ne_zero hs
    show 2 * xi (1 + t s) * (N s / (2 * xi (1 + t s))) = N s
    rw [mul_div_cancel₀ _ this]
  have hL := ((hxian.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul hZlim).congr' hprod
  have hN := hNan.continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds (a := ρ + 1 / 4) (s := {ρ + 1 / 4}ᶜ))
  have huniq := tendsto_nhds_unique hL hN
  simp only [ht, show (1 : ℂ) + (ρ - 1) = ρ by ring, hρ, mul_zero, zero_mul] at huniq
  exact hN0 huniq.symm

/-- **Both signs at the negative cusp.**  For `ε = ±1` there is no `T` with `ε R_∞(u) ≥ 0` for all
`u ≤ −T`. -/
theorem movingCuspDualLimit_not_eventually_signed {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    ¬ ∃ T : ℝ, ∀ u ≤ -T, 0 ≤ ε * movingCuspDualLimit u := by
  rintro ⟨T, hT⟩
  have hε0 : (ε : ℂ) ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  obtain ⟨ρ, hρ, hρre⟩ := exists_xi_zero_re_ge_half
  set g : ℝ → ℝ := fun L => ε * movingCuspDualLimit (-L) * Real.exp (-(L / 4))
  have hgc : Continuous g := (continuous_const.mul (continuous_movingCuspDualLimit.comp
    continuous_neg)).mul (Real.continuous_exp.comp (continuous_id.div_const 4).neg)
  set S : Set ℂ := {s : ℂ | xi (s - 1 / 4) = 0}
  have hSeq : S = (fun z => z + 1 / 4) '' {s : ℂ | xi s = 0} := by
    ext s
    simp only [S, Set.mem_setOf_eq, Set.mem_image]
    exact ⟨fun h => ⟨s - 1 / 4, h, by ring⟩, fun ⟨z, hz, hzs⟩ => by rw [← hzs]; simpa using hz⟩
  have hS : S.Countable := by rw [hSeq]; exact xi_zeroSet_countable.image _
  have hScl : IsClosed S :=
    isClosed_eq (xi_differentiable.continuous.comp (continuous_id.sub continuous_const)) continuous_const
  have hSre : ∀ z ∈ S, z.im ≠ 0 := fun z hz him => by
    have : z - 1 / 4 = (((z.re - 1 / 4 : ℝ)) : ℂ) := Complex.ext (by simp) (by simp [him])
    exact xi_ne_zero_of_real (z.re - 1 / 4) (this ▸ hz)
  have hgi : ∀ σ : ℝ, 3 / 2 < σ → IntegrableOn (fun L : ℝ => g L * Real.exp (-σ * L)) (Ioi 0) :=
    fun σ hσ => IntegrableOn.congr_fun ((movingCuspNegativeTransform_eq hσ).1.const_mul ε)
      (fun L _ => by simp only [g]; ring) measurableSet_Ioi
  have htrans : ∀ σ : ℝ, 3 / 2 < σ →
      ((∫ L in Ioi (0 : ℝ), g L * Real.exp (-σ * L) : ℝ) : ℂ) =
        (fun s => (ε : ℂ) * movingCuspNegativeTransform s) (σ : ℂ) := fun σ hσ => by
    show _ = (ε : ℂ) * movingCuspNegativeTransform (σ : ℂ)
    rw [← (movingCuspNegativeTransform_eq hσ).2, ← Complex.ofReal_mul, ← integral_const_mul]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun L _ => ?_
    simp only [g]; ring
  have hGan : ∀ z : ℂ, 1 / 4 < z.re → z ∉ S →
      AnalyticAt ℂ (fun s => (ε : ℂ) * movingCuspNegativeTransform s) z := fun z hz hzS =>
    analyticAt_const.mul (analyticAt_movingCuspNegativeTransform hz hzS)
  have hpiso : ∀ᶠ s in 𝓝[≠] (ρ + 1 / 4), s ∉ S := by
    have hmap : Tendsto (fun s => s - 1 / 4) (𝓝[≠] (ρ + 1 / 4)) (𝓝[≠] ρ) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have hcont : Continuous fun s : ℂ => s - 1 / 4 := by fun_prop
        have h1 := hcont.tendsto (ρ + 1 / 4)
        rw [add_sub_cancel_right] at h1
        exact h1.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        intro h
        apply hs
        simp only [Set.mem_singleton_iff] at h ⊢
        linear_combination h
    exact hmap.eventually (eventually_xi_ne_zero ρ)
  refine not_eventually_nonneg_of_pole_of_countable hgc hS hScl hSre hgi htrans hGan
    (p := ρ + 1 / 4) (by simp; linarith)
    (not_meromorphicOrderAt_nonneg_movingCuspNegativeTransform hε0 hρ (by linarith)) hpiso
    ⟨max T 0, le_max_right _ _, fun L hL => ?_⟩
  have hy : -L ≤ -T := by linarith [le_max_left T 0]
  have := hT (-L) hy
  simp only [g]
  exact mul_nonneg this (Real.exp_pos _).le

/-- **Infinitely many sign changes at the negative cusp.**  `R_∞` takes both signs for
arbitrarily negative `u`. -/
theorem movingCuspDualLimit_takes_both_signs (T : ℝ) :
    (∃ u ≤ -T, movingCuspDualLimit u < 0) ∧ ∃ u ≤ -T, 0 < movingCuspDualLimit u := by
  constructor
  · by_contra h
    push Not at h
    exact movingCuspDualLimit_not_eventually_signed (Or.inl rfl) ⟨T, fun u hu => by
      simpa using h u hu⟩
  · by_contra h
    push Not at h
    exact movingCuspDualLimit_not_eventually_signed (Or.inr rfl) ⟨T, fun u hu => by
      simpa using h u hu⟩

/-! ## The one-unit spectral shear -/

theorem meromorphicAt_riemannZeta_any (s : ℂ) : MeromorphicAt riemannZeta s :=
  GaloisForLFunctions.HTGeometry.meromorphicOn_riemannZeta s (Set.mem_univ s)

theorem meromorphicAt_riemannZeta_add (a x : ℂ) : MeromorphicAt (fun w => riemannZeta (w + a)) x :=
  MeromorphicAt.comp_analyticAt (g := fun w : ℂ => w + a) (x := x) (meromorphicAt_riemannZeta_any (x + a))
    (analyticAt_id.add analyticAt_const)

theorem meromorphicOrderAt_riemannZeta_comp_add (a x : ℂ) :
    meromorphicOrderAt (fun w => riemannZeta (w + a)) x = meromorphicOrderAt riemannZeta (x + a) := by
  have h := meromorphicOrderAt_comp_of_deriv_ne_zero (f := riemannZeta) (g := fun w : ℂ => w + a)
    (x := x) (analyticAt_id.add analyticAt_const) (by simp)
  exact h

theorem meromorphicOrderAt_eq_zero_of_analyticAt {f : ℂ → ℂ} {x : ℂ} (hf : AnalyticAt ℂ f x)
    (hx : f x ≠ 0) : meromorphicOrderAt f x = 0 := by
  rw [hf.meromorphicOrderAt_eq, hf.analyticOrderAt_eq_zero.2 hx]
  rfl

theorem riemannZeta_ne_zero_of_neg_one_lt_re_neg {s : ℂ} (h1 : -1 < s.re) (h0 : s.re < 0) :
    riemannZeta s ≠ 0 := by
  refine riemannZeta_ne_zero_of_re_le_zero h0.le fun n hn => ?_
  have := congrArg Complex.re hn
  simp at this
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-- The order of `ξ` at a point of the open strip is the order of `ζ`. -/
theorem meromorphicOrderAt_xi_eq_riemannZeta {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ ≠ 1) :
    meromorphicOrderAt xi ρ = meromorphicOrderAt riemannZeta ρ := by
  have hρ0 : ρ ≠ 0 := fun h => by rw [h] at h0; simp at h0
  set g : ℂ → ℂ := fun s => s * (s - 1) / 2 * Complex.Gammaℝ s
  have hΓ := GaloisForLFunctions.HTGeometry.analyticAt_Gammaℝ h0
  have hg : AnalyticAt ℂ g ρ := by simp only [g]; fun_prop
  have hg0 : g ρ ≠ 0 := mul_ne_zero (div_ne_zero (mul_ne_zero hρ0 (sub_ne_zero.2 h1)) two_ne_zero)
    (Complex.Gammaℝ_ne_zero_of_re_pos h0)
  rw [← meromorphicOrderAt_mul_of_ne_zero (f := riemannZeta) hg hg0]
  refine meromorphicOrderAt_congr ?_
  have hopen : IsOpen {s : ℂ | 0 < s.re ∧ s ≠ 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ne
  filter_upwards [nhdsWithin_le_nhds (hopen.mem_nhds ⟨h0, h1⟩)] with s hs
  have hs0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs
  rw [xi_eq_mul_completedRiemannZeta hs0 hs.2, Pi.mul_apply,
    riemannZeta_def_of_ne_zero hs0]
  simp only [g]
  field_simp [Complex.Gammaℝ_ne_zero_of_re_pos hs.1]

/-- The continued dual transform `F(w)/ζ(w − 1/2)`. -/
def movingCuspDualTransform (w : ℂ) : ℂ := XiC (Complex.I * w) * (riemannZeta (w - 1 / 2))⁻¹

/-- The totient reconstruction multiplier `ζ(w − 1/2)/ζ(w + 1/2)`. -/
def totientReconstructionMultiplier (w : ℂ) : ℂ := riemannZeta (w - 1 / 2) * (riemannZeta (w + 1 / 2))⁻¹

theorem meromorphicAt_XiC_I_mul (w : ℂ) : AnalyticAt ℂ (fun w => XiC (Complex.I * w)) w :=
  (XiC_differentiable.analyticAt _).comp (analyticAt_const.mul analyticAt_id)

/-- **Spectral shear, upper copy.**  At `ρ + 1/2` the dual transform has a pole of order `m`. -/
theorem meromorphicOrderAt_movingCuspDualTransform_add_half {ρ : ℂ} (h0 : 0 < ρ.re) :
    meromorphicOrderAt movingCuspDualTransform (ρ + 1 / 2) = -meromorphicOrderAt riemannZeta ρ := by
  have hX := meromorphicAt_XiC_I_mul (ρ + 1 / 2)
  have hXne : XiC (Complex.I * (ρ + 1 / 2)) ≠ 0 := by
    rw [XiC_I_mul_eq_xi_half_add, show (1 / 2 : ℂ) + (ρ + 1 / 2) = 1 + ρ by ring]
    exact xi_ne_zero_of_one_lt_re (by simp; linarith)
  have hZ : MeromorphicAt (fun w => riemannZeta (w - 1 / 2)) (ρ + 1 / 2) := by
    simpa [sub_eq_add_neg] using meromorphicAt_riemannZeta_add (-(1 / 2)) (ρ + 1 / 2)
  rw [show movingCuspDualTransform =
      (fun w => XiC (Complex.I * w)) * (fun w => riemannZeta (w - 1 / 2))⁻¹ from rfl,
    meromorphicOrderAt_mul hX.meromorphicAt hZ.inv, meromorphicOrderAt_inv,
    meromorphicOrderAt_eq_zero_of_analyticAt hX hXne, zero_add]
  have := meromorphicOrderAt_riemannZeta_comp_add (-(1 / 2)) (ρ + 1 / 2)
  simp only [← sub_eq_add_neg, add_sub_cancel_right] at this
  rw [this]

/-- **Spectral shear, lower copy.**  At `ρ − 1/2` the dual transform has a zero of order `m`. -/
theorem meromorphicOrderAt_movingCuspDualTransform_sub_half {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    meromorphicOrderAt movingCuspDualTransform (ρ - 1 / 2) = meromorphicOrderAt riemannZeta ρ := by
  have hρ1 : ρ ≠ 1 := fun h => by rw [h] at h1; simp at h1
  have hX := meromorphicAt_XiC_I_mul (ρ - 1 / 2)
  have hζan : AnalyticAt ℂ (fun w => riemannZeta (w - 1 / 2)) (ρ - 1 / 2) :=
    (GaloisForLFunctions.HTGeometry.analyticAt_riemannZeta (by
      intro h; have := congrArg Complex.re h; simp at this; linarith)).comp
      (analyticAt_id.sub analyticAt_const)
  have hζne : riemannZeta (ρ - 1 / 2 - 1 / 2) ≠ 0 := by
    rw [show ρ - 1 / 2 - 1 / 2 = ρ - 1 by ring]
    exact riemannZeta_ne_zero_of_neg_one_lt_re_neg (by simp; linarith) (by simp; linarith)
  rw [show movingCuspDualTransform =
      (fun w => XiC (Complex.I * w)) * (fun w => riemannZeta (w - 1 / 2))⁻¹ from rfl,
    meromorphicOrderAt_mul hX.meromorphicAt hζan.meromorphicAt.inv, meromorphicOrderAt_inv,
    meromorphicOrderAt_eq_zero_of_analyticAt hζan hζne, neg_zero, add_zero]
  have hfun : (fun w => XiC (Complex.I * w)) = fun w => xi (w + 1 / 2) := by
    funext w; rw [XiC_I_mul_eq_xi_half_add, add_comm]
  rw [hfun]
  have h := meromorphicOrderAt_comp_of_deriv_ne_zero (f := xi) (g := fun w : ℂ => w + 1 / 2)
    (x := ρ - 1 / 2) (analyticAt_id.add analyticAt_const) (by simp)
  simp only [sub_add_cancel] at h
  rw [show (fun w => xi (w + 1 / 2)) = xi ∘ fun w => w + 1 / 2 from rfl, h,
    meromorphicOrderAt_xi_eq_riemannZeta h0 hρ1]

/-- **The reconstruction multiplier carries the opposite shear.** -/
theorem meromorphicOrderAt_totientReconstructionMultiplier {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    meromorphicOrderAt totientReconstructionMultiplier (ρ - 1 / 2) = -meromorphicOrderAt riemannZeta ρ ∧
      meromorphicOrderAt totientReconstructionMultiplier (ρ + 1 / 2) = meromorphicOrderAt riemannZeta ρ := by
  have hm : ∀ a x : ℂ, MeromorphicAt (fun w => riemannZeta (w + a)) x := meromorphicAt_riemannZeta_add
  have hsplit : totientReconstructionMultiplier =
      (fun w => riemannZeta (w + -(1 / 2))) * (fun w => riemannZeta (w + 1 / 2))⁻¹ := by
    funext w; simp [totientReconstructionMultiplier, sub_eq_add_neg]
  have hord : ∀ x, meromorphicOrderAt totientReconstructionMultiplier x =
      meromorphicOrderAt riemannZeta (x + -(1 / 2)) - meromorphicOrderAt riemannZeta (x + 1 / 2) := by
    intro x
    rw [hsplit, meromorphicOrderAt_mul (hm _ x) (hm _ x).inv, meromorphicOrderAt_inv,
      meromorphicOrderAt_riemannZeta_comp_add, meromorphicOrderAt_riemannZeta_comp_add, sub_eq_add_neg]
  have hρ1 : ρ ≠ 1 := fun h => by rw [h] at h1; simp at h1
  constructor
  · rw [hord, show ρ - 1 / 2 + -(1 / 2) = ρ - 1 by ring, show ρ - 1 / 2 + 1 / 2 = ρ by ring,
      meromorphicOrderAt_eq_zero_of_analyticAt (GaloisForLFunctions.HTGeometry.analyticAt_riemannZeta (by
        intro h; have := congrArg Complex.re h; simp at this; linarith))
        (riemannZeta_ne_zero_of_neg_one_lt_re_neg (by simp; linarith) (by simp; linarith)), zero_sub]
  · have hz1 : riemannZeta (ρ + 1) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simp; linarith)
    have ha1 : AnalyticAt ℂ riemannZeta (ρ + 1) :=
      GaloisForLFunctions.HTGeometry.analyticAt_riemannZeta (by
        intro h; have := congrArg Complex.re h; simp at this; linarith)
    rw [hord, show ρ + 1 / 2 + -(1 / 2) = ρ by ring, show ρ + 1 / 2 + 1 / 2 = ρ + 1 by ring,
      meromorphicOrderAt_eq_zero_of_analyticAt ha1 hz1, sub_zero]

/-- **The real convergence wall.**  At `w = 3/2`, `1/ζ(w − 1/2)` has a simple zero and the
reconstruction multiplier has a simple pole. -/
theorem meromorphicOrderAt_wall :
    meromorphicOrderAt (fun w => (riemannZeta (w - 1 / 2))⁻¹) (3 / 2) = 1 ∧
      meromorphicOrderAt totientReconstructionMultiplier (3 / 2) = -1 := by
  have h1 : meromorphicOrderAt (fun w => riemannZeta (w - 1 / 2)) (3 / 2) = -1 := by
    have := meromorphicOrderAt_riemannZeta_comp_add (-(1 / 2)) (3 / 2)
    simp only [← sub_eq_add_neg] at this
    rw [this, show (3 / 2 : ℂ) - 1 / 2 = 1 by norm_num,
      GaloisForLFunctions.meromorphicOrderAt_riemannZeta_one]
    rfl
  have hm : ∀ a x : ℂ, MeromorphicAt (fun w => riemannZeta (w + a)) x := meromorphicAt_riemannZeta_add
  constructor
  · rw [show (fun w => (riemannZeta (w - 1 / 2))⁻¹) = (fun w => riemannZeta (w - 1 / 2))⁻¹ from rfl,
      meromorphicOrderAt_inv, h1]
    rfl
  · have hsplit : totientReconstructionMultiplier =
        (fun w => riemannZeta (w - 1 / 2)) * (fun w => riemannZeta (w + 1 / 2))⁻¹ := rfl
    rw [hsplit, meromorphicOrderAt_mul (by simpa [sub_eq_add_neg] using hm (-(1 / 2)) (3 / 2))
      (hm _ _).inv, meromorphicOrderAt_inv, h1, meromorphicOrderAt_riemannZeta_comp_add,
      meromorphicOrderAt_eq_zero_of_analyticAt (GaloisForLFunctions.HTGeometry.analyticAt_riemannZeta
        (by norm_num)) (riemannZeta_ne_zero_of_one_le_re (by norm_num)), neg_zero, add_zero]

/-- **The shear cancels in the product.**  Away from the zeros of `ζ(w ± 1/2)`, the product of
the dual transform and the reconstruction multiplier is `F(w)/ζ(w + 1/2)`. -/
theorem movingCuspDualTransform_mul_multiplier {w : ℂ} (hw : riemannZeta (w - 1 / 2) ≠ 0) :
    movingCuspDualTransform w * totientReconstructionMultiplier w =
      XiC (Complex.I * w) * (riemannZeta (w + 1 / 2))⁻¹ := by
  rw [movingCuspDualTransform, totientReconstructionMultiplier, mul_assoc,
    ← mul_assoc (riemannZeta (w - 1 / 2))⁻¹, inv_mul_cancel₀ hw, one_mul]

/-- **The shear cancels into the seed transform.**  In the open Xi strip `|Re w| < 1/2`, off the
zeros of `ζ(w + 1/2)`, the product of the dual transform and the reconstruction multiplier is the
seed transform `ℒ_w h = G(w)`, which has no zero in the strip. -/
theorem movingCuspDualTransform_mul_multiplier_eq_seed {w : ℂ} (hw : |w.re| < 1 / 2)
    (hz2 : riemannZeta (w + 1 / 2) ≠ 0) :
    movingCuspDualTransform w * totientReconstructionMultiplier w = thetaAtomMellinFactor w ∧
      thetaAtomMellinFactor w ≠ 0 := by
  have h1 := abs_lt.1 hw
  have hz : riemannZeta (w - 1 / 2) ≠ 0 :=
    riemannZeta_ne_zero_of_neg_one_lt_re_neg (by simp; linarith) (by simp; linarith)
  have hw1 : w ≠ 1 / 2 := fun h => by rw [h] at h1; norm_num at h1
  refine ⟨?_, thetaAtomMellinFactor_ne_zero (by linarith) hw1⟩
  rw [movingCuspDualTransform_mul_multiplier hz, XiC_I_mul_eq_thetaAtomMellinFactor_mul_zeta
    (by linarith) hw1, mul_assoc, mul_inv_cancel₀ hz2, mul_one]

/-- **The product is zero-free and pole-free in the open Xi strip:** its meromorphic order vanishes
at every point of `|Re w| < 1/2`, zeta zeros included. -/
theorem meromorphicOrderAt_movingCuspDualTransform_mul_multiplier {w₀ : ℂ} (hw₀ : |w₀.re| < 1 / 2) :
    meromorphicOrderAt (movingCuspDualTransform * totientReconstructionMultiplier) w₀ = 0 := by
  have hopen : IsOpen {w : ℂ | |w.re| < 1 / 2} :=
    isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const
  have hxi : ∀ᶠ w in 𝓝[≠] w₀, xi (w + 1 / 2) ≠ 0 := by
    have hmap : Tendsto (fun w => w + 1 / 2) (𝓝[≠] w₀) (𝓝[≠] (w₀ + 1 / 2)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · exact ((continuous_id.add continuous_const).tendsto w₀).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with w hw h
        exact hw (by simpa using h)
    exact hmap.eventually (eventually_xi_ne_zero _)
  have heq : movingCuspDualTransform * totientReconstructionMultiplier =ᶠ[𝓝[≠] w₀]
      thetaAtomMellinFactor := by
    filter_upwards [hxi, nhdsWithin_le_nhds (hopen.mem_nhds hw₀)] with w hw hstrip
    have h1 := abs_lt.1 (show |w.re| < 1 / 2 from hstrip)
    have hw1 : w ≠ 1 / 2 := fun h => by rw [h] at h1; norm_num at h1
    have hz2 : riemannZeta (w + 1 / 2) ≠ 0 := fun h0 => by
      have hX := XiC_I_mul_eq_thetaAtomMellinFactor_mul_zeta (w := w) (by linarith) hw1
      rw [h0, mul_zero, XiC_I_mul_eq_xi_half_add, add_comm] at hX
      exact hw hX
    exact (movingCuspDualTransform_mul_multiplier_eq_seed hstrip hz2).1
  rw [meromorphicOrderAt_congr heq]
  have h1 := abs_lt.1 hw₀
  exact meromorphicOrderAt_eq_zero_of_analyticAt (analyticAt_thetaAtomMellinFactor (by linarith))
    (thetaAtomMellinFactor_ne_zero (by linarith) fun h => by rw [h] at h1; norm_num at h1)

/-- **The reconstruction multiplier.**  For `Re w > 3/2`, `ℒh(w) = M(w) ℒR_∞(w)` with
`M(w) = ζ(w − 1/2)/ζ(w + 1/2)`. -/
theorem integral_seed_eq_multiplier_mul_dual {w : ℂ} (hw : 3 / 2 < w.re) :
    (∫ u : ℝ, Complex.exp (w * u) * (thetaSeedAtom u : ℂ)) =
      totientReconstructionMultiplier w * ∫ u : ℝ, Complex.exp (w * u) * (movingCuspDualLimit u : ℂ) := by
  rw [(integral_cexp_mul_movingCuspDualLimit hw).2]
  have hseed : (∫ u : ℝ, Complex.exp (w * u) * (thetaSeedAtom u : ℂ)) = thetaAtomMellinFactor w := by
    have := integral_cexp_mul_thetaCuspSourceTerm w (by linarith) 1 one_pos
    simpa [thetaSeedAtom] using this
  have hz1 : riemannZeta (w - 1 / 2) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simp; linarith)
  have hz2 : riemannZeta (w + 1 / 2) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simp; linarith)
  rw [hseed, XiC_I_mul_eq_thetaAtomMellinFactor_mul_zeta (by linarith)
    (fun h => by rw [h] at hw; norm_num at hw), totientReconstructionMultiplier]
  calc thetaAtomMellinFactor w = thetaAtomMellinFactor w *
        (riemannZeta (w - 1 / 2) * (riemannZeta (w - 1 / 2))⁻¹) *
        (riemannZeta (w + 1 / 2) * (riemannZeta (w + 1 / 2))⁻¹) := by
        rw [mul_inv_cancel₀ hz1, mul_inv_cancel₀ hz2]; ring
    _ = _ := by ring

end

end RHTower
