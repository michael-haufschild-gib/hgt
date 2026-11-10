import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.IsozericTangentFlow
import GaloisForLFunctions.HTGeometry.PolydiscWeierstrass
import GaloisForLFunctions.HTGeometry.NormalSeriesStrictFDeriv

/-!
# Exact realization of admissible prime tangents

A bounded real prime velocity occurs in an actual bounded holomorphic gauge
family with a joint regularization at the zeta pole exactly when its absolute
prime series converges at an exponent below one.

The realizing family has prime phases `exp(i a_p z)`. Its regularization is
the zeta residue factor times the exponential of the normally convergent
Euler logarithm difference. A uniform logarithm bound gives joint analyticity,
and the Euler identity identifies the constructed function with the actual
fibres. Every real fibre of the linear flow preserves zeta zero multiplicities
on a common half-plane extending left of one.
-/

open Complex Filter Topology Metric Set
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticCorrelationGeometry
open GaloisForLFunctions.PrimeTorusTheory
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations

/-- The logarithm has a uniform derivative bound on every closed disk about one avoiding zero. -/
private theorem norm_log_sub_log_of_norm_sub_one_le {z w : ℂ} {ρ : ℝ}
    (hρ : ρ < 1) (hz : ‖z - 1‖ ≤ ρ) (hw : ‖w - 1‖ ≤ ρ) :
    ‖Complex.log z - Complex.log w‖ ≤ (1 / (1 - ρ)) * ‖z - w‖ := by
  have hsl (v : ℂ) (hv : v ∈ closedBall 1 ρ) : v ∈ Complex.slitPlane := by
    have hnorm : ‖v - 1‖ ≤ ρ := by simpa only [mem_closedBall, dist_eq_norm] using hv
    have hre := (neg_le_abs (v - 1).re).trans ((Complex.abs_re_le_norm _).trans hnorm)
    simp only [Complex.sub_re, Complex.one_re] at hre
    exact Or.inl (by linarith only [hre, hρ])
  have hd : ∀ v ∈ closedBall (1 : ℂ) ρ,
      HasDerivWithinAt Complex.log v⁻¹ (closedBall 1 ρ) v :=
    fun v hv => (Complex.hasDerivAt_log (hsl v hv)).hasDerivWithinAt
  have hb : ∀ v ∈ closedBall (1 : ℂ) ρ, ‖v⁻¹‖ ≤ 1 / (1 - ρ) := by
    intro v hv
    have hv' : ‖v - 1‖ ≤ ρ := by simpa only [mem_closedBall, dist_eq_norm] using hv
    have ht := norm_add_le (1 - v) v
    rw [sub_add_cancel, norm_one, norm_sub_rev] at ht
    have hl : 1 - ρ ≤ ‖v‖ := by linarith only [ht, hv']
    rw [norm_inv, ← one_div]
    exact div_le_div₀ (by norm_num) le_rfl (sub_pos.mpr hρ) hl
  exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (convex_closedBall 1 ρ)
    (by simpa only [mem_closedBall, dist_eq_norm] using hw)
    (by simpa only [mem_closedBall, dist_eq_norm] using hz)

/-- Local normal convergence supplies the joint analytic Euler logarithm. -/
private theorem analyticAt_tsum_fin2_ball {ι : Type*}
    {f : ι → (Fin 2 → ℂ) → ℂ} {c : Fin 2 → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : ∀ i, AnalyticOnNhd ℂ (f i) (ball c (2 * r)))
    {u : ι → ℝ} (hu : Summable u)
    (hb : ∀ i v, v ∈ ball c (2 * r) → ‖f i v‖ ≤ u i) :
    AnalyticAt ℂ (fun v => ∑' i, f i v) c := by
  have hsub : ball c r ⊆ ball c (2 * r) := ball_subset_ball (by linarith only [hr])
  have hlocal : ∀ v ∈ ball c r, ball v r ⊆ ball c (2 * r) := by
    intro v hv w hw
    exact lt_of_le_of_lt (dist_triangle w v c) (by
      have hv' := mem_ball.mp hv
      have hw' := mem_ball.mp hw
      linarith only [hv', hw'])
  have hb' : ∀ i v, v ∈ ball c r → ‖fderiv ℂ (f i) v‖ ≤ (2 / r) * u i := by
    intro i v hv
    have hd : DifferentiableOn ℂ (f i) (ball v r) :=
      (hf i).differentiableOn.mono (hlocal v hv)
    have hm : MapsTo (f i) (ball v r) (closedBall (f i v) (2 * u i)) := by
      intro w hw
      rw [mem_closedBall, dist_eq_norm]
      exact (norm_sub_le _ _).trans (by
        linarith only [hb i w (hlocal v hv hw), hb i v (hsub hv)])
    have h := Complex.norm_fderiv_le_div_of_mapsTo_ball hd hm hr
    convert h using 1
    ring
  have hu' : Summable (fun i => (2 / r) * u i) := hu.mul_left _
  have hsum : Summable (fun i => f i c) :=
    hu.of_norm_bounded (fun i => hb i c (mem_ball_self (by positivity)))
  have hd : DifferentiableOn ℂ (fun v => ∑' i, f i v) (ball c r) := by
    intro v hv
    exact (hasFDerivAt_tsum_of_isPreconnected hu' isOpen_ball
      (convex_ball c r).isPreconnected
      (fun i w hw => (hf i w (hsub hw)).differentiableAt.hasFDerivAt)
      hb' (mem_ball_self hr) hsum hv).differentiableAt.differentiableWithinAt
  exact HTGeometry.analyticAt_of_differentiableOn isOpen_ball hd (mem_ball_self hr)


/-- Normal convergence in two complex variables, transported through the standard coordinate map. -/
theorem analyticAt_tsum_prod_ball {ι : Type*}
    {f : ι → (ℂ × ℂ) → ℂ} {c : ℂ × ℂ} {r : ℝ} (hr : 0 < r)
    (hf : ∀ i, AnalyticOnNhd ℂ (f i) (ball c r))
    {u : ι → ℝ} (hu : Summable u)
    (hb : ∀ i q, q ∈ ball c r → ‖f i q‖ ≤ u i) :
    AnalyticAt ℂ (fun q => ∑' i, f i q) c := by
  let e := ContinuousLinearEquiv.finTwoArrow ℂ ℂ
  have hn : e ⁻¹' ball c r ∈ 𝓝 (e.symm c) :=
    e.continuous.continuousAt.preimage_mem_nhds
      (by simpa only [e.apply_symm_apply] using ball_mem_nhds c hr)
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hn
  have hf' (i : ι) : AnalyticOnNhd ℂ (fun v => f i (e v)) (ball (e.symm c) ε) := by
    intro v hv
    exact (hf i (e v) (hsub hv)).comp (e.toContinuousLinearMap.analyticAt v)
  have h2 : 2 * (ε / 2) = ε := by ring
  have h := analyticAt_tsum_fin2_ball (r := ε / 2) (by positivity)
    (by simpa only [h2] using hf') hu
    (by
      intro i v hv
      apply hb i (e v)
      apply hsub
      simpa only [h2] using hv)
  have hc := h.comp (e.symm.toContinuousLinearMap.analyticAt c)
  change AnalyticAt ℂ (fun q : ℂ × ℂ => ∑' i, f i (e (e.symm q))) c at hc
  simpa only [e.apply_symm_apply] using hc

/-- The exact change in one Euler logarithm along the linear phase flow. -/
def linearEulerChange (a : Nat.Primes → ℝ) (p : Nat.Primes) (q : ℂ × ℂ) : ℂ :=
  Complex.log (1 - Complex.exp (-(q.2 * (primeFrequency p : ℂ)))) -
    Complex.log (1 - linearPrimePhase a p q.1 * Complex.exp (-(q.2 * (primeFrequency p : ℂ))))

/-- The residue factor times the normally convergent Euler logarithm change. -/
def linearFlowRegularization (a : Nat.Primes → ℝ) (q : ℂ × ℂ) : ℂ :=
  _root_.RHTower.zetaResidueFactor q.2 * Complex.exp (∑' p, linearEulerChange a p q)


theorem norm_prime_decay_le {c : ℝ} {s : ℂ} (hc : c ≤ s.re) (p : Nat.Primes) :
    ‖Complex.exp (-(s * (primeFrequency p : ℂ)))‖ ≤ primeDamping c p := by
  rw [Complex.norm_exp, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, primeDamping, ← prime_exp_decay]
  exact Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right hc (primeFrequency_nonneg p)))

private theorem primeDamping_le_exp_log_two {c : ℝ} (hc : 0 ≤ c) (p : Nat.Primes) :
    primeDamping c p ≤ Real.exp (-(c * Real.log 2)) := by
  rw [primeDamping, ← prime_exp_decay]
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  exact mul_le_mul_of_nonneg_left
    (Real.log_le_log (by norm_num) (by exact_mod_cast p.2.two_le)) hc

private theorem norm_linearPrimePhase_sub_one_le {a : Nat.Primes → ℝ} {K r : ℝ}
    (ha : ∀ p, |a p| ≤ K) (p : Nat.Primes) {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖linearPrimePhase a p z - 1‖ ≤ (r * Real.exp (K * r)) * |a p| := by
  have hK : 0 ≤ K := (abs_nonneg _).trans (ha p)
  have hTaylor := Complex.norm_exp_sub_sum_le_norm_mul_exp ((a p : ℂ) * I * z) 1
  have ht : ‖linearPrimePhase a p z - 1‖ ≤
      ‖(a p : ℂ) * I * z‖ * Real.exp ‖(a p : ℂ) * I * z‖ := by
    simpa [linearPrimePhase, Finset.sum_range_succ, Nat.factorial] using hTaylor
  have hn : ‖(a p : ℂ) * I * z‖ = |a p| * ‖z‖ := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
  rw [hn] at ht
  calc _ ≤ (|a p| * ‖z‖) * Real.exp (|a p| * ‖z‖) := ht
       _ ≤ (|a p| * r) * Real.exp (K * r) :=
         mul_le_mul (mul_le_mul_of_nonneg_left hz (abs_nonneg _))
           (Real.exp_le_exp.mpr (mul_le_mul (ha p) hz (norm_nonneg _) hK))
           (Real.exp_pos _).le (mul_nonneg (abs_nonneg _) ((norm_nonneg _).trans hz))
       _ = _ := by ring

theorem norm_log_euler_change_le {u d : ℂ} {M q : ℝ}
    (hM : 1 ≤ M) (hu : ‖u‖ ≤ M) (hd : ‖d‖ ≤ q) (hMq : M * q < 1) :
    ‖Complex.log (1 - d) - Complex.log (1 - u * d)‖ ≤
      (1 / (1 - M * q)) * ‖u - 1‖ * ‖d‖ := by
  have hq : 0 ≤ q := (norm_nonneg _).trans hd
  have hρd : ‖(1 - d) - 1‖ ≤ M * q := by
    simpa only [sub_sub_cancel_left, norm_neg] using
      hd.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hM hq)
  have hρu : ‖(1 - u * d) - 1‖ ≤ M * q := by
    simpa only [sub_sub_cancel_left, norm_neg, norm_mul] using
      mul_le_mul hu hd (norm_nonneg _) (zero_le_one.trans hM)
  have h := norm_log_sub_log_of_norm_sub_one_le hMq hρd hρu
  have he : (1 - d) - (1 - u * d) = (u - 1) * d := by ring
  rw [he, norm_mul] at h
  simpa only [mul_assoc] using h

theorem one_sub_mem_slitPlane {w : ℂ} (hw : ‖w‖ < 1) :
    1 - w ∈ Complex.slitPlane := by
  apply Or.inl
  simp only [Complex.sub_re, Complex.one_re]
  linarith only [Complex.re_le_norm w, hw]

private theorem analyticAt_linearEulerChange {a : Nat.Primes → ℝ} (p : Nat.Primes)
    {q : ℂ × ℂ}
    (hd : ‖Complex.exp (-(q.2 * (primeFrequency p : ℂ)))‖ < 1)
    (hu : ‖linearPrimePhase a p q.1 * Complex.exp (-(q.2 * (primeFrequency p : ℂ)))‖ < 1) :
    AnalyticAt ℂ (linearEulerChange a p) q := by
  have hda : AnalyticAt ℂ (fun v : ℂ × ℂ =>
      Complex.exp (-(v.2 * (primeFrequency p : ℂ)))) q :=
    (((ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt q).mul analyticAt_const).neg.cexp
  have hua : AnalyticAt ℂ (fun v : ℂ × ℂ => linearPrimePhase a p v.1) q :=
    (analyticAt_const.mul ((ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt q)).cexp
  exact ((analyticAt_const.sub hda).clog (one_sub_mem_slitPlane hd)).sub
    ((analyticAt_const.sub (hua.mul hda)).clog (one_sub_mem_slitPlane hu))


private theorem summable_gaugePhaseEulerLog (x : GaugeTorus) {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun p : Nat.Primes =>
      phaseEulerLog (primeDamping σ p) (fun _ => twist x p) 0) := by
  refine ((summable_primeDamping hσ).mul_left 6).of_norm_bounded ?_
  intro p
  exact phaseEulerLog_bound (primeDamping_pos σ p).le (primeDamping_le_half hσ.le p)
    (by rw [norm_twist]; norm_num)

/-- The constructed regularization is the actual Euler fibre throughout the real Euler region. -/
theorem linearFlowRegularization_eq_gaugeFibre (a : Nat.Primes → ℝ) (t : ℝ)
    {σ : ℝ} (hσ : 1 < σ) :
    linearFlowRegularization a ((t : ℂ), (σ : ℂ)) =
      ((σ : ℂ) - 1) * gaugeFibre (linearPhaseGauge a t) (σ : ℂ) := by
  let A : Nat.Primes → ℂ := fun p =>
    phaseEulerLog (primeDamping σ p) (fun _ => twist (linearPhaseGauge a t) p) 0
  let B : Nat.Primes → ℂ := fun p =>
    phaseEulerLog (primeDamping σ p) (fun _ => twist (0 : GaugeTorus) p) 0
  have hA : Summable A := summable_gaugePhaseEulerLog _ hσ
  have hB : Summable B := summable_gaugePhaseEulerLog _ hσ
  have he (p : Nat.Primes) : linearEulerChange a p ((t : ℂ), (σ : ℂ)) = A p - B p := by
    dsimp [linearEulerChange, A, B, phaseEulerLog]
    rw [prime_cexp_decay, ← ofReal_primeDamping]
    rw [twist_linearPhaseGauge_prime, twist_trivial]
    simp only [one_mul, mul_comm]
    ring
  have hsum : (∑' p, linearEulerChange a p ((t : ℂ), (σ : ℂ))) =
      (∑' p, A p) - ∑' p, B p := by
    rw [tsum_congr he, hA.tsum_sub hB]
  have hAe : Complex.exp (∑' p, A p) = gaugeFibre (linearPhaseGauge a t) (σ : ℂ) :=
    exp_phaseEulerLog_eq_gaugeFibre hσ (fun _ => rfl)
  have hBe : Complex.exp (∑' p, B p) = riemannZeta (σ : ℂ) := by
    rw [exp_phaseEulerLog_eq_gaugeFibre hσ (fun _ => rfl), gaugeFibre_trivial (s := (σ : ℂ)) hσ]
  have hF : riemannZeta (σ : ℂ) * Complex.exp
      (∑' p, linearEulerChange a p ((t : ℂ), (σ : ℂ))) =
      gaugeFibre (linearPhaseGauge a t) (σ : ℂ) := by
    rw [← hBe, hsum, ← Complex.exp_add]
    convert hAe using 1
    congr 1
    ring
  have hσne : (σ : ℂ) ≠ 1 := by exact_mod_cast (ne_of_gt hσ : σ ≠ 1)
  rw [linearFlowRegularization,
    _root_.RHTower.zetaResidueFactor_of_ne (s := (σ : ℂ)) hσne, mul_assoc, hF]


/-- Absolute prime summability controls the joint Euler change on a neighborhood of the pole. -/
private theorem exists_linearEulerChange_normal_bound {a : Nat.Primes → ℝ} {K σ : ℝ}
    (ha : ∀ p, |a p| ≤ K) (hσ0 : 1 / 2 < σ) (hσ1 : σ < 1) :
    ∃ R : ℝ, 0 < R ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ p : Nat.Primes,
      ∀ v ∈ ball ((0 : ℂ), (1 : ℂ)) R,
        AnalyticAt ℂ (linearEulerChange a p) v ∧
          ‖linearEulerChange a p v‖ ≤ C * (|a p| * (p : ℝ) ^ (-σ)) := by
  have hK : 0 ≤ K := (abs_nonneg _).trans (ha (⟨2, Nat.prime_two⟩ : Nat.Primes))
  let c : ℝ := (1 + σ) / 2
  have hσc : σ < c := by dsimp [c]; linarith only [hσ1]
  have hc0 : 0 < c := by dsimp [c]; linarith only [hσ0]
  have hc1 : c < 1 := by dsimp [c]; linarith only [hσ1]
  let q : ℝ := Real.exp (-(c * Real.log 2))
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by
    dsimp [q]
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (neg_lt_zero.mpr (mul_pos hc0 (Real.log_pos (by norm_num))))
  have he : ContinuousAt (fun r : ℝ => Real.exp (K * r) * q) 0 :=
    (Real.continuous_exp.continuousAt.comp (continuousAt_const.mul continuousAt_id)).mul
      continuousAt_const
  have hnear : {r : ℝ | Real.exp (K * r) * q < 1} ∈ 𝓝 0 :=
    he.preimage_mem_nhds (Iio_mem_nhds (by simpa only [mul_zero, Real.exp_zero, one_mul] using hq1))
  obtain ⟨ε, hε, hεsmall⟩ := Metric.mem_nhds_iff.mp hnear
  let r : ℝ := ε / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrε : r < ε := by dsimp [r]; linarith only [hε]
  let M : ℝ := Real.exp (K * r)
  have hMq : M * q < 1 := hεsmall (by
    simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hr] using hrε)
  have hM : 1 ≤ M := by
    change 1 ≤ Real.exp (K * r)
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (mul_nonneg hK hr.le)
  let V : Set (ℂ × ℂ) := {v | ‖v.1‖ < r ∧ c < v.2.re}
  have hV : IsOpen V :=
    (isOpen_lt (continuous_norm.comp continuous_fst) continuous_const).inter
      (isOpen_lt continuous_const (Complex.continuous_re.comp continuous_snd))
  have hv0 : ((0 : ℂ), (1 : ℂ)) ∈ V := by
    exact ⟨by simpa only [norm_zero] using hr, by simpa only [Complex.one_re] using hc1⟩
  obtain ⟨R, hR, hRV⟩ := Metric.isOpen_iff.mp hV (0, 1) hv0
  let D : ℝ := 1 / (1 - M * q)
  have hD : 0 ≤ D := (div_pos one_pos (sub_pos.mpr hMq)).le
  let C : ℝ := D * (r * M)
  have hC : 0 ≤ C := mul_nonneg hD (mul_nonneg hr.le (zero_le_one.trans hM))
  refine ⟨R, hR, C, hC, ?_⟩
  intro p v hv
  have hv' : ‖v.1‖ < r ∧ c < v.2.re := hRV hv
  have hu : ‖linearPrimePhase a p v.1‖ ≤ M :=
    linearPrimePhase_bound ha p (by simpa only [mem_ball, dist_zero_right] using hv'.1)
  have hdq : ‖Complex.exp (-(v.2 * (primeFrequency p : ℂ)))‖ ≤ q :=
    (norm_prime_decay_le hv'.2.le p).trans (primeDamping_le_exp_log_two hc0.le p)
  have hdu : ‖linearPrimePhase a p v.1 * Complex.exp (-(v.2 * (primeFrequency p : ℂ)))‖ ≤ M * q := by
    rw [norm_mul]
    exact mul_le_mul hu hdq (norm_nonneg _) (zero_le_one.trans hM)
  refine ⟨analyticAt_linearEulerChange p (hdq.trans_lt hq1) (hdu.trans_lt hMq), ?_⟩
  have hl := norm_log_euler_change_le hM hu hdq hMq
  have hp := norm_linearPrimePhase_sub_one_le ha p hv'.1.le
  have hdσ := norm_prime_decay_le (hσc.le.trans hv'.2.le) p
  change ‖linearEulerChange a p v‖ ≤ D * ‖linearPrimePhase a p v.1 - 1‖ *
    ‖Complex.exp (-(v.2 * (primeFrequency p : ℂ)))‖ at hl
  calc ‖linearEulerChange a p v‖ ≤ D * ‖linearPrimePhase a p v.1 - 1‖ *
      ‖Complex.exp (-(v.2 * (primeFrequency p : ℂ)))‖ := hl
       _ ≤ (D * ((r * M) * |a p|)) * primeDamping σ p :=
         mul_le_mul (mul_le_mul_of_nonneg_left hp hD) hdσ (norm_nonneg _)
           (mul_nonneg hD (mul_nonneg (mul_nonneg hr.le (zero_le_one.trans hM)) (abs_nonneg _)))
       _ = C * (|a p| * (p : ℝ) ^ (-σ)) := by dsimp [C, primeDamping]; ring

/-- The explicit linear Euler flow admits an actual jointly holomorphic pole regularization. -/
theorem analyticAt_linearFlowRegularization {a : Nat.Primes → ℝ} {K σ : ℝ}
    (ha : ∀ p, |a p| ≤ K) (hσ0 : 1 / 2 < σ) (hσ1 : σ < 1)
    (hs : Summable (fun p : Nat.Primes => |a p| * (p : ℝ) ^ (-σ))) :
    AnalyticAt ℂ (linearFlowRegularization a) (0, 1) := by
  obtain ⟨R, hR, C, _, hb⟩ := exists_linearEulerChange_normal_bound ha hσ0 hσ1
  have hL : AnalyticAt ℂ (fun v => ∑' p, linearEulerChange a p v) (0, 1) :=
    analyticAt_tsum_prod_ball hR (fun p v hv => (hb p v hv).1) (hs.mul_left C)
      (fun p v hv => (hb p v hv).2)
  have hZ : AnalyticAt ℂ _root_.RHTower.zetaResidueFactor 1 :=
    _root_.RHTower.differentiable_zetaResidueFactor.differentiableOn.analyticAt
      (show Set.univ ∈ 𝓝 (1 : ℂ) from Filter.univ_mem)
  exact (hZ.comp (f := fun v : ℂ × ℂ => v.2)
    ((ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt (0, 1))).mul hL.cexp


/-- Bounded prime velocities occur in actual jointly regularized families exactly when
    their absolute prime series converges at an exponent below one. -/
theorem bounded_prime_tangent_admissible_iff {a : Nat.Primes → ℝ} {K : ℝ}
    (ha : ∀ p, |a p| ≤ K) :
    (∃ (x : ℝ → GaugeTorus) (u : Nat.Primes → ℂ → ℂ) (U : ℂ × ℂ → ℂ) (R M : ℝ),
      0 < R ∧ x 0 = 0 ∧
      (∀ p, DifferentiableOn ℂ (u p) (ball 0 R)) ∧
      (∀ p z, z ∈ ball 0 R → ‖u p z‖ ≤ M) ∧
      (∀ t : ℝ, |t| < R → ∀ p, u p (t : ℂ) = twist (x t) p) ∧
      AnalyticAt ℂ U (0, 1) ∧
      (∀ σ : ℝ, 1 < σ → σ < 1 + R → ∀ t : ℝ, |t| < R →
        U ((t : ℂ), (σ : ℂ)) = ((σ : ℂ) - 1) * gaugeFibre (x t) (σ : ℂ)) ∧
      ∀ p, deriv (u p) 0 = (a p : ℂ) * Complex.I) ↔
    ∃ σ : ℝ, 1 / 2 < σ ∧ σ < 1 ∧
      Summable (fun p : Nat.Primes => |a p| * (p : ℝ) ^ (-σ)) := by
  constructor
  · rintro ⟨x, u, U, R, M, hR, hx, hu, hb, hphase, hU, hagree, hder⟩
    obtain ⟨σ, hσ0, hσ1, hs⟩ :=
      gauge_tangent_absolute_power_saving hR hx hu hb hphase hU hagree
    have he (p : Nat.Primes) : (deriv (u p) 0).im = a p := by rw [hder p]; simp
    exact ⟨σ, hσ0, hσ1, by simpa only [he] using hs⟩
  · rintro ⟨σ, hσ0, hσ1, hs⟩
    refine ⟨linearPhaseGauge a, linearPrimePhase a, linearFlowRegularization a,
      1, Real.exp K, one_pos, linearPhaseGauge_zero a,
      (fun p => (differentiable_linearPrimePhase a p).differentiableOn), ?_, ?_,
      analyticAt_linearFlowRegularization ha hσ0 hσ1 hs, ?_, deriv_linearPrimePhase_zero a⟩
    · intro p z hz
      simpa only [mul_one] using linearPrimePhase_bound ha p hz
    · intro t _ p
      exact (twist_linearPhaseGauge_prime a t p).symm
    · intro s hs _ t _
      exact linearFlowRegularization_eq_gaugeFibre a t hs

/-- The integrating linear flow preserves each zero multiplicity on its common half-plane. -/
theorem linearPhaseGauge_zero_order {a : Nat.Primes → ℝ} {K σ : ℝ}
    (ha : ∀ p, |a p| ≤ K) (hσ : 1 / 2 ≤ σ)
    (hs : Summable (fun p : Nat.Primes => |a p| * (p : ℝ) ^ (-σ)))
    (t : ℝ) {s : ℂ} (hs₀ : σ < s.re) (hs₁ : s ≠ 1) :
    analyticOrderAt (fun z => riemannZeta z *
      Complex.exp (deformationExponent (linearPhaseGauge a t) z)) s =
      analyticOrderAt riemannZeta s :=
  analyticOrderAt_isozeric hσ (linearPhaseGauge_mem_isozericClass ha hs t) hs₀ hs₁

#print axioms linearFlowRegularization_eq_gaugeFibre
#print axioms analyticAt_linearFlowRegularization
#print axioms bounded_prime_tangent_admissible_iff
#print axioms linearPhaseGauge_zero_order
end GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations
