import GaloisForLFunctions.HTGeometry.ArithmeticTaylorCoefficientFloor
import GaloisForLFunctions.HTGeometry.PowerSeriesDiscBridge
import GaloisForLFunctions.HTGeometry.RGTowerCoherence
import GaloisForLFunctions.HTGeometry.TaylorFormalBridge
import GaloisForLFunctions.HTGeometry.DifferentialAlgebraicOnSum
import GaloisForLFunctions.HTGeometry.SqrtStretchedGrowth
import GaloisForLFunctions.HTGeometry.CompositionJetTranscendence

/-!
# Algebraic entire-heat differentially algebraic fibres have finite spectrum

A one-sided periodic heat orbit with algebraic Fourier coefficients that is jointly entire has
super-Gaussian coefficient decay, because the backward-time fibre is again a convergent series.
If its spatial fibre at time zero is differentially algebraic, the ordinary generating function of
the coefficients is differentially algebraic on a logarithm chart, so Popken's floor applies to its
Taylor coefficients.  The two scales are incompatible, so only finitely many coefficients survive.
-/

open PowerSeries MvPolynomial Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### Super-Gaussian decay from entire backward time -/

theorem exists_gaussian_bound {a : ℕ → ℂ} {u : ℂ → ℂ → ℂ}
    (hu : ∀ t z : ℂ, HasSum (fun n : ℕ => a n *
      Complex.exp (-4 * (Real.pi : ℂ) ^ 2 * (n : ℂ) ^ 2 * t) *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z)) (u t z)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, ‖a n‖ * Real.exp ((n : ℝ) ^ 2) ≤ M := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero]
  set t₀ : ℂ := -(1 / (4 * (Real.pi : ℂ) ^ 2)) with ht₀
  have hterm : ∀ n : ℕ, a n * Complex.exp (-4 * (Real.pi : ℂ) ^ 2 * (n : ℂ) ^ 2 * t₀) *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * 0)
      = a n * Complex.exp (((n : ℝ) ^ 2 : ℝ)) := by
    intro n
    rw [ht₀]
    have harg : -4 * (Real.pi : ℂ) ^ 2 * (n : ℂ) ^ 2 * (-(1 / (4 * (Real.pi : ℂ) ^ 2)))
        = (((n : ℝ) ^ 2 : ℝ) : ℂ) := by
      field_simp
      push_cast
      ring
    rw [harg]
    simp
  have hsum := hu t₀ 0
  rw [show (fun n : ℕ => a n * Complex.exp (-4 * (Real.pi : ℂ) ^ 2 * (n : ℂ) ^ 2 * t₀) *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * 0))
      = fun n : ℕ => a n * Complex.exp (((n : ℝ) ^ 2 : ℝ)) from funext hterm] at hsum
  have hsummable : Summable fun n : ℕ => ‖a n * Complex.exp (((n : ℝ) ^ 2 : ℝ))‖ :=
    summable_norm_iff.mpr hsum.summable
  refine ⟨∑' n : ℕ, ‖a n * Complex.exp (((n : ℝ) ^ 2 : ℝ))‖, ?_, ?_⟩
  · exact tsum_nonneg fun n => norm_nonneg _
  · intro n
    have hnorm : ‖a n * Complex.exp (((n : ℝ) ^ 2 : ℝ))‖ = ‖a n‖ * Real.exp ((n : ℝ) ^ 2) := by
      rw [norm_mul, Complex.norm_exp, Complex.ofReal_re]
    rw [← hnorm]
    exact hsummable.le_tsum n fun i _ => norm_nonneg _

/-! ### The generating function is entire -/

theorem radius_eq_top_of_gaussian {a : ℕ → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ n : ℕ, ‖a n‖ * Real.exp ((n : ℝ) ^ 2) ≤ M) :
    (FormalMultilinearSeries.ofScalars ℂ a).radius = ⊤ := by
  refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
  rcases eq_or_ne r 0 with rfl | hr0
  · simp
  have hrpos : (0 : ℝ) < (r : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hr0)
  refine FormalMultilinearSeries.le_radius_of_bound _
    (M * Real.exp ((Real.log r) ^ 2 / 4)) fun n => ?_
  have hnorm : ‖FormalMultilinearSeries.ofScalars ℂ a n‖ = ‖a n‖ :=
    FormalMultilinearSeries.ofScalars_norm ℂ a n
  rw [hnorm]
  have hexp : (r : ℝ) ^ n = Real.exp ((n : ℝ) * Real.log r) := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  have ha : ‖a n‖ ≤ M * Real.exp (-((n : ℝ) ^ 2)) := by
    have h2 : (0 : ℝ) < Real.exp ((n : ℝ) ^ 2) := Real.exp_pos _
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ h2]
    exact h n
  calc ‖a n‖ * (r : ℝ) ^ n ≤ (M * Real.exp (-((n : ℝ) ^ 2))) * Real.exp ((n : ℝ) * Real.log r) := by
        rw [hexp]
        exact mul_le_mul_of_nonneg_right ha (le_of_lt (Real.exp_pos _))
    _ = M * Real.exp ((n : ℝ) * Real.log r - (n : ℝ) ^ 2) := by
        rw [mul_assoc, ← Real.exp_add]
        ring_nf
    _ ≤ M * Real.exp ((Real.log r) ^ 2 / 4) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hM
        nlinarith [sq_nonneg ((n : ℝ) - Real.log r / 2)]

/-! ### The logarithm chart -/

/-- The principal logarithm chart inverting `z ↦ exp(2πiz)`. -/
private def logChart : ℂ → ℂ := fun w => Complex.log w / (2 * (Real.pi : ℂ) * Complex.I)

theorem twoPiI_ne_zero : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  simp [hπ, Complex.I_ne_zero]

theorem mem_slitPlane_of_mem_ball {w : ℂ} (hw : w ∈ Metric.ball (1 : ℂ) (1 / 2)) :
    w ∈ Complex.slitPlane := by
  have hdist : ‖w - 1‖ < 1 / 2 := by
    simpa [Complex.dist_eq] using hw
  have hre : |w.re - 1| ≤ ‖w - 1‖ := by
    simpa using Complex.abs_re_le_norm (w - 1)
  have : 0 < w.re := by
    have := abs_lt.mp (lt_of_le_of_lt hre hdist)
    linarith [this.1]
  exact Complex.mem_slitPlane_iff.mpr (Or.inl this)

private theorem hasDerivAt_logChart {w : ℂ} (hw : w ∈ Metric.ball (1 : ℂ) (1 / 2)) :
    HasDerivAt logChart (w⁻¹ / (2 * (Real.pi : ℂ) * Complex.I)) w := by
  have hlog : HasDerivAt Complex.log w⁻¹ w :=
    Complex.hasDerivAt_log (mem_slitPlane_of_mem_ball hw)
  exact hlog.div_const _

theorem analyticOnNhd_logChart :
    AnalyticOnNhd ℂ logChart (Metric.ball (1 : ℂ) (1 / 2)) := by
  intro w hw
  have hball : Metric.ball (1 : ℂ) (1 / 2) ∈ nhds w := Metric.isOpen_ball.mem_nhds hw
  have hdiff : ∀ᶠ v in nhds w, DifferentiableAt ℂ logChart v := by
    filter_upwards [hball] with v hv using (hasDerivAt_logChart hv).differentiableAt
  exact (Complex.analyticAt_iff_eventually_differentiableAt).mpr hdiff

theorem deriv_logChart {w : ℂ} (hw : w ∈ Metric.ball (1 : ℂ) (1 / 2)) :
    deriv logChart w = w⁻¹ / (2 * (Real.pi : ℂ) * Complex.I) :=
  (hasDerivAt_logChart hw).deriv

theorem exp_twoPiI_logChart {w : ℂ} (hw : w ∈ Metric.ball (1 : ℂ) (1 / 2)) :
    Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * logChart w) = w := by
  have hne : w ≠ 0 := by
    intro h
    have := mem_slitPlane_of_mem_ball hw
    rw [h] at this
    simp [Complex.mem_slitPlane_iff] at this
  rw [logChart, mul_div_cancel₀ _ twoPiI_ne_zero, Complex.exp_log hne]

/-- **The logarithm chart is differentially algebraic**: `2πi w g'(w) = 1`. -/
theorem differentiallyAlgebraicOn_logChart :
    DifferentiallyAlgebraicOn logChart (Metric.ball (1 : ℂ) (1 / 2)) := by
  classical
  refine ⟨1, MvPolynomial.C (2 * (Real.pi : ℂ) * Complex.I) * MvPolynomial.X 0 *
    MvPolynomial.X 2 - 1, ?_, ?_⟩
  · intro hzero
    have hev := congrArg (MvPolynomial.eval (fun _ : Fin 3 => (0 : ℂ))) hzero
    simp only [map_sub, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, map_one,
      mul_zero, zero_sub] at hev
    exact absurd hev (by norm_num)
  · intro z hz
    have hzne : z ≠ 0 := by
      intro h
      have hmem := mem_slitPlane_of_mem_ball hz
      rw [h] at hmem
      simp [Complex.mem_slitPlane_iff] at hmem
    have hjet0 : (Fin.cons z (fun j : Fin 2 => iteratedDeriv (j : ℕ) logChart z) :
        Fin 3 → ℂ) 0 = z := by
      simp
    have hjet2 : (Fin.cons z (fun j : Fin 2 => iteratedDeriv (j : ℕ) logChart z) :
        Fin 3 → ℂ) 2 = deriv logChart z := by
      have : (2 : Fin 3) = Fin.succ 1 := rfl
      rw [this, Fin.cons_succ]
      simp [iteratedDeriv_one]
    simp only [map_sub, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, map_one]
    rw [hjet0, hjet2, deriv_logChart hz]
    field_simp
    norm_num

/-- **The logarithm chart is a faithful substitution.** -/
theorem substitutionFaithful_logChart :
    SubstitutionFaithful (Metric.ball (1 : ℂ) (1 / 2)) Set.univ logChart := by
  intro f hf hvan z _
  set E : ℂ → ℂ := fun v => Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * v) with hEdef
  have hEcont : ContinuousAt E 0 := by
    refine Complex.continuous_exp.continuousAt.comp ?_
    exact (continuous_const.mul continuous_id).continuousAt
  have hE0 : E 0 = 1 := by simp [hEdef]
  have hball : ∀ᶠ v in nhds (0 : ℂ), E v ∈ Metric.ball (1 : ℂ) (1 / 2) := by
    have hmem : Metric.ball (1 : ℂ) (1 / 2) ∈ nhds (E 0) := by
      rw [hE0]
      exact Metric.ball_mem_nhds _ (by norm_num)
    exact hEcont.preimage_mem_nhds hmem
  have hsmall : ∀ᶠ v in nhds (0 : ℂ), ‖v‖ < 1 / 2 := by
    have : Metric.ball (0 : ℂ) (1 / 2) ∈ nhds (0 : ℂ) := Metric.ball_mem_nhds _ (by norm_num)
    filter_upwards [this] with v hv
    simpa [Complex.dist_eq] using hv
  have hzero : ∀ᶠ v in nhds (0 : ℂ), f v = 0 := by
    filter_upwards [hball, hsmall] with v hv hvsmall
    have him : ((2 * (Real.pi : ℂ) * Complex.I) * v).im = 2 * Real.pi * v.re := by
      simp [Complex.mul_im, Complex.mul_re]
    have hre : |v.re| < 1 / 2 := lt_of_le_of_lt (Complex.abs_re_le_norm v) hvsmall
    have hlog : Complex.log (E v) = (2 * (Real.pi : ℂ) * Complex.I) * v := by
      rw [hEdef]
      refine Complex.log_exp ?_ ?_
      · rw [him]
        have := abs_lt.mp hre
        nlinarith [Real.pi_pos, this.1]
      · rw [him]
        have := abs_lt.mp hre
        nlinarith [Real.pi_pos, this.2]
    have hchart : logChart (E v) = v := by
      rw [logChart, hlog, mul_comm, mul_div_assoc, div_self twoPiI_ne_zero, mul_one]
    have hfv := hvan (E v) hv
    rwa [hchart] at hfv
  have hEqOn := hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ (0 : ℂ)) hzero
  exact hEqOn (Set.mem_univ z)

/-! ### The generating function -/

theorem analyticOnNhd_seriesSum_of_radius_top {a : ℕ → ℂ}
    (hr : (FormalMultilinearSeries.ofScalars ℂ a).radius = ⊤) :
    AnalyticOnNhd ℂ (seriesSum a) Set.univ := by
  set p := FormalMultilinearSeries.ofScalars ℂ a with hp
  have hball : HasFPowerSeriesOnBall p.sum p 0 p.radius :=
    p.hasFPowerSeriesOnBall (by rw [hr]; simp)
  have ha : AnalyticOnNhd ℂ p.sum Set.univ := by
    simpa [hr] using hball.analyticOnNhd
  rw [seriesSum_eq_ofScalarsSum a, ← hp]
  exact ha

theorem differentiable_jetFun {f : ℂ → ℂ} (hf : Differentiable ℂ f) (r : ℕ)
    (P : MvPolynomial (Fin (r + 2)) ℂ) :
    Differentiable ℂ (GaloisForLFunctions.jetFun f r P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      rw [GaloisForLFunctions.jetFun_C]
      exact differentiable_const c
  | add p q hp hq =>
      rw [GaloisForLFunctions.jetFun_add]
      exact hp.add hq
  | mul_X p i hp =>
      rw [GaloisForLFunctions.jetFun_mul]
      refine hp.mul ?_
      induction i using Fin.cases with
      | zero =>
          rw [GaloisForLFunctions.jetFun_X_zero]
          exact differentiable_id
      | succ j =>
          rw [GaloisForLFunctions.jetFun_X_succ]
          exact differentiable_iteratedDeriv_entire hf (j : ℕ)

/-! ### The chart domain -/

theorem isPreconnected_chartBall : IsPreconnected (Metric.ball (1 : ℂ) (1 / 2)) :=
  (convex_ball (1 : ℂ) (1 / 2)).isPreconnected

theorem nonempty_chartBall : (Metric.ball (1 : ℂ) (1 / 2)).Nonempty :=
  Metric.nonempty_ball.mpr (by norm_num)

theorem infinite_chartBall : (Metric.ball (1 : ℂ) (1 / 2)).Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun k : ℕ => (1 : ℂ) + (1 / ((k : ℂ) + 3))) ?_ ?_
  · intro k l hkl
    have h1 : ((k : ℂ) + 3) ≠ 0 := by
      intro hc
      have := congrArg Complex.re hc
      simp at this
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have h2 : ((l : ℂ) + 3) ≠ 0 := by
      intro hc
      have := congrArg Complex.re hc
      simp at this
      have : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
      linarith
    have heq : ((k : ℂ) + 3) = ((l : ℂ) + 3) := by
      field_simp at hkl
      linear_combination -hkl
    have : (k : ℂ) = (l : ℂ) := by linear_combination heq
    exact_mod_cast this
  · intro k
    have hk3 : (0 : ℝ) < (k : ℝ) + 3 := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have hnorm : ‖(1 : ℂ) + (1 / ((k : ℂ) + 3)) - 1‖ = 1 / ((k : ℝ) + 3) := by
      have hcast : ((k : ℂ) + 3) = (((k : ℝ) + 3 : ℝ) : ℂ) := by push_cast; ring
      rw [add_sub_cancel_left, hcast, one_div, norm_inv, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hk3, one_div]
    rw [Metric.mem_ball, Complex.dist_eq, hnorm]
    rw [div_lt_iff₀ hk3]
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith

/-! ### The finite-spectrum theorem -/

/-- **Algebraic entire-heat differentially algebraic fibres have finite spectrum.**  A one-sided
periodic heat orbit with algebraic Fourier amplitudes that converges for every complex time and
place has only finitely many nonzero amplitudes as soon as its spatial fibre at time zero is
differentially algebraic. -/
theorem arithmetic_heat_finite_spectrum
    {a : ℕ → ℂ} (halg : ∀ n, IsAlgebraic ℚ (a n)) {u : ℂ → ℂ → ℂ}
    (hu : ∀ t z : ℂ, HasSum (fun n : ℕ => a n *
      Complex.exp (-4 * (Real.pi : ℂ) ^ 2 * (n : ℂ) ^ 2 * t) *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z)) (u t z))
    (hDA : DifferentiallyAlgebraicOn (u 0) Set.univ) :
    ∀ᶠ n in atTop, a n = 0 := by
  classical
  obtain ⟨M, hM0, hM⟩ := exists_gaussian_bound hu
  have hrad := radius_eq_top_of_gaussian hM0 hM
  set h : ℂ → ℂ := seriesSum a with hhdef
  have hana : AnalyticOnNhd ℂ h Set.univ := analyticOnNhd_seriesSum_of_radius_top hrad
  have hdiff : Differentiable ℂ h := fun z => (hana z (Set.mem_univ z)).differentiableAt
  have hcontDiff : ContDiff ℂ (⊤ : ℕ∞) h := hana.contDiff
  -- the spatial fibre is the generating function read on the exponential chart
  have hfibre : ∀ z : ℂ, u 0 z = h (Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * z)) := by
    intro z
    have hsum := hu 0 z
    have hterm : (fun n : ℕ => a n * Complex.exp (-4 * (Real.pi : ℂ) ^ 2 * (n : ℂ) ^ 2 * 0) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z))
        = fun n : ℕ => a n * (Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * z)) ^ n := by
      funext n
      rw [mul_zero, Complex.exp_zero, mul_one, ← Complex.exp_nat_mul]
      ring_nf
    rw [hterm] at hsum
    rw [hhdef, seriesSum]
    exact hsum.tsum_eq.symm
  have hanaΦ : AnalyticOnNhd ℂ (u 0) Set.univ := by
    have hfun : u 0 = fun z => h (Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * z)) :=
      funext hfibre
    have hdiffΦ : Differentiable ℂ (u 0) := by
      rw [hfun]
      intro z
      refine DifferentiableAt.comp z (hdiff _) ?_
      exact (Complex.differentiable_exp _).comp z
        ((differentiable_const _).mul differentiable_id z)
    exact hdiffΦ.differentiableOn.analyticOnNhd isOpen_univ
  -- the generating function is differentially algebraic on the chart
  have hDAcomp := differentiallyAlgebraicOn_comp Metric.isOpen_ball isPreconnected_chartBall
    nonempty_chartBall infinite_chartBall isOpen_univ isPreconnected_univ Set.univ_nonempty
    (Set.infinite_univ) hanaΦ analyticOnNhd_logChart (Set.mapsTo_univ _ _)
    substitutionFaithful_logChart hDA differentiallyAlgebraicOn_logChart
  have hDAh : DifferentiallyAlgebraicOn h (Metric.ball (1 : ℂ) (1 / 2)) := by
    refine differentiallyAlgebraicOn_of_eqOn Metric.isOpen_ball (fun w hw => ?_) hDAcomp
    rw [hfibre (logChart w), exp_twoPiI_logChart hw]
  -- the relation extends to the whole plane and passes to the Taylor series
  obtain ⟨r, P, hP0, hPvan⟩ := hDAh
  have hjetdiff : Differentiable ℂ (GaloisForLFunctions.jetFun h r P) :=
    differentiable_jetFun hdiff r P
  have hjetana : AnalyticOnNhd ℂ (GaloisForLFunctions.jetFun h r P) Set.univ :=
    hjetdiff.differentiableOn.analyticOnNhd isOpen_univ
  have hjetzero : GaloisForLFunctions.jetFun h r P = 0 := by
    funext z
    have hnb : ∀ᶠ w in nhds (1 : ℂ), GaloisForLFunctions.jetFun h r P w = 0 := by
      filter_upwards [Metric.isOpen_ball.mem_nhds
        (Metric.mem_ball_self (show (0 : ℝ) < 1 / 2 by norm_num))] with w hw using hPvan w hw
    have := hjetana.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (Set.mem_univ (1 : ℂ)) hnb
    exact this (Set.mem_univ z)
  have hh : h = FormalMultilinearSeries.ofScalarsSum a := by
    rw [hhdef, seriesSum_eq_ofScalarsSum]
    rfl
  have htaylor : GaloisForLFunctions.taylorPS h = PowerSeries.mk a := by
    ext n
    rw [PowerSeries.coeff_mk, hh]
    exact taylorPS_ofScalarsSum_of_radius_eq_top a hrad n
  have hformal : MvPolynomial.aeval
      (GaloisForLFunctions.formalJets r (PowerSeries.mk a)) P = 0 := by
    rw [← htaylor, ← GaloisForLFunctions.taylorPS_jetFun h r hcontDiff P, hjetzero]
    rw [show (0 : ℂ → ℂ) = fun _ => (0 : ℂ) from rfl, GaloisForLFunctions.taylorPS_const,
      map_zero]
  -- Popken's floor
  have halgF : ∀ n, IsAlgebraic ℚ (PowerSeries.coeff n (PowerSeries.mk a)) := by
    intro n
    rw [PowerSeries.coeff_mk]
    exact halg n
  obtain ⟨Kp, hKp, hfloor⟩ := exists_popken_floor_of_formalRelation halgF hP0 hformal
  -- the two scales are incompatible
  have hMpos : (0 : ℝ) < M + 1 := by linarith
  have hMbound : ∀ n : ℕ, ‖a n‖ ≤ (M + 1) * Real.exp (-((n : ℝ) ^ 2)) := by
    intro n
    have h2 : (0 : ℝ) < Real.exp ((n : ℝ) ^ 2) := Real.exp_pos _
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ h2]
    have := hM n
    linarith
  have hsmall : ∀ᶠ n : ℕ in atTop,
      (M + 1) * Real.exp (-((n : ℝ) ^ 2)) < Real.exp (-(Kp * ((n : ℝ) * (Real.log n) ^ 2))) := by
    have hlittle : ∀ᶠ x : ℝ in atTop, ‖Real.log x ^ 2‖ ≤ (1 / (2 * Kp)) * ‖x‖ :=
      isLittleO_log_sq_id.bound (by positivity)
    have hnat : ∀ᶠ n : ℕ in atTop, ‖Real.log (n : ℝ) ^ 2‖ ≤ (1 / (2 * Kp)) * ‖(n : ℝ)‖ :=
      hlittle.natCast_atTop
    filter_upwards [hnat, eventually_ge_atTop (2 : ℕ),
      eventually_gt_atTop (Nat.ceil (2 * Real.log (M + 1) + 2))] with n hn hn2 hnbig
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
      linarith
    have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn1
    have hnorm1 : ‖Real.log (n : ℝ) ^ 2‖ = Real.log (n : ℝ) ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hnorm2 : ‖(n : ℝ)‖ = (n : ℝ) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [hnorm1, hnorm2] at hn
    have hkey : Kp * ((n : ℝ) * Real.log n ^ 2) ≤ (n : ℝ) ^ 2 / 2 := by
      have h1 : Kp * Real.log (n : ℝ) ^ 2 ≤ (n : ℝ) / 2 := by
        have := mul_le_mul_of_nonneg_left hn (le_of_lt hKp)
        rw [← mul_assoc] at this
        have hKpne : Kp * (1 / (2 * Kp)) = 1 / 2 := by
          field_simp
        rw [hKpne] at this
        linarith [this]
      nlinarith [h1, hn1]
    have hbig : Real.log (M + 1) < (n : ℝ) ^ 2 / 2 := by
      have hlt : (2 * Real.log (M + 1) + 2) < (n : ℝ) := by
        have h1 : (Nat.ceil (2 * Real.log (M + 1) + 2) : ℝ) < (n : ℝ) := by
          exact_mod_cast hnbig
        exact lt_of_le_of_lt (Nat.le_ceil _) h1
      nlinarith [hn1, hlt]
    have hlogM : Real.log ((M + 1) * Real.exp (-((n : ℝ) ^ 2)))
        = Real.log (M + 1) - (n : ℝ) ^ 2 := by
      rw [Real.log_mul (ne_of_gt hMpos) (ne_of_gt (Real.exp_pos _)), Real.log_exp]
      ring
    have hlt : Real.log ((M + 1) * Real.exp (-((n : ℝ) ^ 2)))
        < -(Kp * ((n : ℝ) * Real.log n ^ 2)) := by
      rw [hlogM]
      linarith [hkey, hbig]
    have hposl : (0 : ℝ) < (M + 1) * Real.exp (-((n : ℝ) ^ 2)) := by positivity
    calc (M + 1) * Real.exp (-((n : ℝ) ^ 2))
        = Real.exp (Real.log ((M + 1) * Real.exp (-((n : ℝ) ^ 2)))) := (Real.exp_log hposl).symm
      _ < Real.exp (-(Kp * ((n : ℝ) * Real.log n ^ 2))) := Real.exp_lt_exp.mpr hlt
  filter_upwards [hsmall, eventually_ge_atTop 2] with n hn hn2
  by_contra hane
  have hcoeff : PowerSeries.coeff n (PowerSeries.mk a) ≠ 0 := by
    rw [PowerSeries.coeff_mk]
    exact hane
  have h1 := hfloor n hn2 hcoeff
  rw [PowerSeries.coeff_mk] at h1
  have h2 := hMbound n
  linarith [h1, h2, hn]

end

end GaloisForLFunctions.HTGeometry
