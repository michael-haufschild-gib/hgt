import GaloisForLFunctions.RHTower.OddSectorWeightAbsoluteConvergence
import GaloisForLFunctions.RHTower.WeilPoleWeightAtMostOne
import GaloisForLFunctions.RHTower.WeilOddBlindPoleWeightWindow
import GaloisForLFunctions.HTGeometry.L1PeriodizationFourier

/-!
# Odd Weil positivity caps the pole weight at one

**Theorem** (`le_one_of_weilPositiveOddAt`).  If real weights `lam` are Weil-positive at pole
weight `β` on every autocorrelation of an odd compactly supported `C²` test, then `β ≤ 1`.

**Corollaries.**  The prime-blind odd window lies in `(−∞, 1]`
(`le_one_of_primeBlindPositiveOddAt`); under RH it is exactly `(−∞, 1]`
(`riemannHypothesis_imp_primeBlindPositiveOddAt_iff`).

Proof.  Let `φ` be an even bump, `k = φ ⋆ φ̃` its autocorrelation and `J = ∫ φ(x) e^{−x/2} dx`.
The odd far bumps `φ(x − a) − φ(x + a)` give, for `a ≥ 0`, the lower bound
`S(a) ≥ β(e^a − 2)J² − A₀` for the window sums `S(a) = Σ_{n ≥ 2} lam(n) n^{−1/2} k(log n − 2a)`.
By absolute convergence of `Σ lam(n) n^{−s}` on `Re s > 1` and Fubini, the Laplace transform is
`∫ S(a) e^{−(1+2σ)a} da = ½ K(σ) F(σ)` with `F(σ) = Σ lam(n) n^{−1−σ}` and
`K(σ) = ∫ k(u) e^{(1/2+σ)u} du`, so `σ K(σ) F(σ) ≥ βJ² + O(σ)`.  The odd log-density ceiling and
Abel summation give `σF(σ) · Re σζ(1+σ) ≤ 1 + ε + O(σ²)`.  Since `0 ≤ K(σ) ≤ e^{σ/6} K(0)`,
`K(0) = J² > 0` and `σζ(1+σ) → 1`, letting `σ → 0⁺` gives `βJ² ≤ (1 + ε)J²` for every `ε > 0`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate
open Zeta23

noncomputable section

namespace RHTower.OddSector

open ResonatorProfile EvenSector WeilOneSided WeilMeanSquare WeilSpectral WeilPoleWeight

/-! ## The window kernel -/

theorem continuous_farKernel : Continuous farKernel := by
  have hc : Continuous fun u => (farBump u : ℂ) :=
    Complex.continuous_ofReal.comp continuous_farBump
  have hcs : HasCompactSupport fun u => (farBump u : ℂ) :=
    hasCompactSupport_farBump.comp_left Complex.ofReal_zero
  have h2 : ContDiff ℝ 2 fun u => (farBump u : ℂ) := contDiff_ofReal_comp (contDiff_farBump 2)
  have hw := (EF.weilTest_contDiff h2 hc hcs).continuous
  have e : farKernel = fun u => (EF.weilTest (fun u => (farBump u : ℂ))
      (fun u => (farBump u : ℂ)) u).re := by
    funext u; rw [weilTest_ofReal_eq, Complex.ofReal_re]; rfl
  rw [e]
  exact Complex.continuous_re.comp hw

theorem hasCompactSupport_farKernel : HasCompactSupport farKernel :=
  HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) (2 * (nodeBump 2).rOut)) fun x hx => by
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, not_le] at hx
    exact farKernel_eq_zero hx.le

theorem integrable_farKernel_mul_exp (c : ℝ) :
    Integrable fun u => farKernel u * Real.exp (c * u) :=
  (continuous_farKernel.mul (by fun_prop)).integrable_of_hasCompactSupport
    hasCompactSupport_farKernel.mul_right

/-- `K(σ) = ∫ k(u) e^{(1/2+σ)u} du`. -/
def farLaplace (σ : ℝ) : ℝ := ∫ u, farKernel u * Real.exp ((1 / 2 + σ) * u)

theorem farJ_pos : 0 < farJ := by
  unfold farJ
  refine (continuous_farBump.mul (by fun_prop)).integral_pos_of_hasCompactSupport_nonneg_nonzero
    hasCompactSupport_farBump.mul_right
    (fun x => mul_nonneg (farBump_nonneg x) (Real.exp_pos _).le) (x := 0) ?_
  rw [farBump_eq_one (by rw [abs_zero]; exact (nodeBump 2).rIn_pos.le)]
  simp

/-- `K(0) = J²`: the transform of an autocorrelation at `−i/2` is `φ̂(−i/2) φ̂(i/2)`. -/
theorem farLaplace_zero : farLaplace 0 = farJ ^ 2 := by
  have hc : Continuous fun u => (farBump u : ℂ) :=
    Complex.continuous_ofReal.comp continuous_farBump
  have hcs : HasCompactSupport fun u => (farBump u : ℂ) :=
    hasCompactSupport_farBump.comp_left Complex.ofReal_zero
  have hk : EF.weilTest (fun u => (farBump u : ℂ)) (fun u => (farBump u : ℂ)) =
      fun u => (farKernel u : ℂ) := by
    funext u; rw [weilTest_ofReal_eq]; rfl
  have h1 := EF.paperFT_weilTest hc hc hcs hcs (-I / 2)
  rw [hk, conj_neg_I_div_two, paperFT_ofRealFun_neg_I_div_two, paperFT_ofRealFun_neg_I_div_two,
    paperFT_ofRealFun_I_div_two, Complex.conj_ofReal] at h1
  have hJ' : ∫ u, farBump u * Real.exp (u / 2) = farJ := by
    unfold farJ
    rw [← integral_neg_eq_self (fun u => farBump u * Real.exp (u / 2))]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    show farBump (-u) * Real.exp (-u / 2) = farBump u * Real.exp (-u / 2)
    rw [farBump_neg]
  rw [hJ'] at h1
  have h3 : ∫ u, farKernel u * Real.exp (u / 2) = farJ * farJ := by exact_mod_cast h1
  unfold farLaplace
  rw [sq, ← h3]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  show farKernel u * Real.exp ((1 / 2 + 0) * u) = farKernel u * Real.exp (u / 2)
  rw [show (1 / 2 + 0 : ℝ) * u = u / 2 by ring]

/-- `K(σ) ≤ e^{σ/6} K(0)`, since `k` is nonnegative and supported in `[−1/6, 1/6]`. -/
theorem farLaplace_le {σ : ℝ} (hσ : 0 ≤ σ) : farLaplace σ ≤ Real.exp (σ / 6) * farLaplace 0 := by
  unfold farLaplace
  rw [← integral_const_mul]
  refine integral_mono (integrable_farKernel_mul_exp _)
    ((integrable_farKernel_mul_exp _).const_mul _) fun u => ?_
  show farKernel u * Real.exp ((1 / 2 + σ) * u) ≤
    Real.exp (σ / 6) * (farKernel u * Real.exp ((1 / 2 + 0) * u))
  have hk := farKernel_nonneg u
  rcases le_or_gt (2 * (nodeBump 2).rOut) |u| with hu | hu
  · rw [farKernel_eq_zero hu]; simp
  · have hr := nodeBump_rOut_le 2
    have hu6 : u ≤ 1 / 6 := by have := le_abs_self u; linarith
    have he : Real.exp ((1 / 2 + σ) * u) ≤ Real.exp (σ / 6) * Real.exp ((1 / 2 + 0) * u) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith)
    calc farKernel u * Real.exp ((1 / 2 + σ) * u)
        ≤ farKernel u * (Real.exp (σ / 6) * Real.exp ((1 / 2 + 0) * u)) :=
          mul_le_mul_of_nonneg_left he hk
      _ = Real.exp (σ / 6) * (farKernel u * Real.exp ((1 / 2 + 0) * u)) := by ring

theorem integrable_farKernel_log_sub (σ L : ℝ) :
    Integrable fun a => farKernel (L - 2 * a) * Real.exp (-(1 + 2 * σ) * a) := by
  have h := (((integrable_farKernel_mul_exp (1 / 2 + σ)).comp_sub_left L).comp_mul_left'
    (R := 2) two_ne_zero).const_mul (Real.exp (-(1 / 2 + σ) * L))
  refine h.congr (Eventually.of_forall fun a => ?_)
  show Real.exp (-(1 / 2 + σ) * L) * (farKernel (L - 2 * a) *
      Real.exp ((1 / 2 + σ) * (L - 2 * a))) =
    farKernel (L - 2 * a) * Real.exp (-(1 + 2 * σ) * a)
  rw [mul_left_comm, ← Real.exp_add]
  congr 2; ring

/-- `∫ k(L − 2a) e^{−(1+2σ)a} da = ½ e^{−(1/2+σ)L} K(σ)`. -/
theorem integral_farKernel_log_sub (σ L : ℝ) :
    ∫ a, farKernel (L - 2 * a) * Real.exp (-(1 + 2 * σ) * a) =
      Real.exp (-(1 / 2 + σ) * L) / 2 * farLaplace σ := by
  have hpt : (fun a => farKernel (L - 2 * a) * Real.exp (-(1 + 2 * σ) * a)) = fun a =>
      Real.exp (-(1 / 2 + σ) * L) * (farKernel (L - 2 * a) *
        Real.exp ((1 / 2 + σ) * (L - 2 * a))) := by
    funext a
    rw [mul_left_comm, ← Real.exp_add]
    congr 2; ring
  rw [hpt, integral_const_mul]
  have h2 : ∫ a, farKernel (L - 2 * a) * Real.exp ((1 / 2 + σ) * (L - 2 * a)) =
      1 / 2 * farLaplace σ := by
    calc ∫ a, farKernel (L - 2 * a) * Real.exp ((1 / 2 + σ) * (L - 2 * a))
        = |(2 : ℝ)⁻¹| • ∫ y, farKernel (L - y) * Real.exp ((1 / 2 + σ) * (L - y)) :=
          Measure.integral_comp_mul_left
            (fun y => farKernel (L - y) * Real.exp ((1 / 2 + σ) * (L - y))) 2
      _ = |(2 : ℝ)⁻¹| • ∫ y, farKernel y * Real.exp ((1 / 2 + σ) * y) := by
          rw [integral_sub_left_eq_self (fun y => farKernel y * Real.exp ((1 / 2 + σ) * y))
            volume L]
      _ = 1 / 2 * farLaplace σ := by
          rw [smul_eq_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]; unfold farLaplace; ring
  rw [h2]
  ring

/-! ## The Laplace transform of the window sums -/

/-- The real Dirichlet series `F(σ) = Σ_{n ≥ 2} lam(n) n^{−1−σ}`. -/
def oddDirichlet (lam : ℕ → ℝ) (σ : ℝ) : ℝ :=
  ∑' n : ℕ, (if 2 ≤ n then lam n else 0) / (n : ℝ) ^ (1 + σ)

theorem LSeries_lamC_eq_oddDirichlet (lam : ℕ → ℝ) (σ : ℝ) :
    LSeries (WeilHerglotz.lamC lam) (1 + σ) = (oddDirichlet lam σ : ℂ) := by
  unfold LSeries oddDirichlet
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [LSeries.term_of_ne_zero hn, WeilHerglotz.lamC, Complex.ofReal_div,
    Complex.ofReal_cpow (Nat.cast_nonneg _)]
  push_cast
  rfl

theorem farSum_eq_zero_of_nonpos (lam : ℕ → ℝ) {a : ℝ} (ha : a ≤ 0) : farSum lam a = 0 := by
  unfold farSum
  refine (tsum_congr fun n => ?_).trans tsum_zero
  split_ifs with hn
  · have hn0 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hl : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn0
    have := Real.log_two_gt_d9
    have hr := nodeBump_rOut_le 2
    rw [farKernel_eq_zero (by rw [abs_of_nonneg (by linarith)]; linarith), mul_zero]
  · rw [zero_mul]

/-- **Fubini for the window sums.**  For `σ > 0`,
`∫ S(a) e^{−(1+2σ)a} da = ½ K(σ) F(σ)`, the integrand being integrable. -/
theorem integral_farSum_mul_exp {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) {σ : ℝ} (hσ : 0 < σ) :
    Integrable (fun a => farSum lam a * Real.exp (-(1 + 2 * σ) * a)) ∧
      ∫ a, farSum lam a * Real.exp (-(1 + 2 * σ) * a) = farLaplace σ / 2 * oddDirichlet lam σ := by
  set c : ℕ → ℝ := fun n => if 2 ≤ n then lam n / Real.sqrt n else 0 with hc
  set f : ℕ → ℝ → ℝ := fun n a => c n * (farKernel (Real.log n - 2 * a) *
    Real.exp (-(1 + 2 * σ) * a)) with hf
  have hfi : ∀ n, Integrable (f n) := fun n =>
    (integrable_farKernel_log_sub σ (Real.log n)).const_mul (c n)
  have hfint : ∀ n, ∫ a, f n a =
      c n * (Real.exp (-(1 / 2 + σ) * Real.log n) / 2 * farLaplace σ) := by
    intro n
    simp only [hf]
    rw [integral_const_mul, integral_farKernel_log_sub]
  have hfn : ∀ n, ∫ a, ‖f n a‖ =
      |c n| * (Real.exp (-(1 / 2 + σ) * Real.log n) / 2 * farLaplace σ) := by
    intro n
    have e : (fun a => ‖f n a‖) = fun a => |c n| * (farKernel (Real.log n - 2 * a) *
        Real.exp (-(1 + 2 * σ) * a)) := by
      funext a
      simp only [hf, Real.norm_eq_abs, abs_mul, abs_of_nonneg (farKernel_nonneg _),
        abs_of_pos (Real.exp_pos _)]
    rw [e, integral_const_mul, integral_farKernel_log_sub]
  have hterm : ∀ n : ℕ, c n * Real.exp (-(1 / 2 + σ) * Real.log n) =
      (if 2 ≤ n then lam n else 0) / (n : ℝ) ^ (1 + σ) := by
    intro n
    simp only [hc]
    split_ifs with hn
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have e : -(1 / 2 + σ) * Real.log n + Real.log n * (1 + σ) = Real.log n * (1 / 2) := by
        ring
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn0, Real.rpow_def_of_pos hn0,
        div_mul_eq_mul_div, div_eq_div_iff (Real.exp_pos _).ne' (Real.exp_pos _).ne', mul_assoc,
        ← Real.exp_add, e]
    · simp
  have hsum0 : Summable fun n : ℕ => |c n| * Real.exp (-(1 / 2 + σ) * Real.log n) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      (hsl (1 + σ) (by linarith))
    have h1 : |c n| * Real.exp (-(1 / 2 + σ) * Real.log n) =
        |c n * Real.exp (-(1 / 2 + σ) * Real.log n)| := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    rw [h1, hterm n]
    have hp : 0 ≤ (n : ℝ) ^ (1 + σ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    split_ifs
    · rw [abs_div, abs_of_nonneg hp]
    · rw [zero_div, abs_zero]; positivity
  have hsum : Summable fun n => ∫ a, ‖f n a‖ :=
    (hsum0.mul_right (farLaplace σ / 2)).congr fun n => by rw [hfn n]; ring
  have hint := GaloisForLFunctions.HTGeometry.integrable_tsum_of_summable_integral_norm hfi hsum
  have hS : (fun a => farSum lam a * Real.exp (-(1 + 2 * σ) * a)) = fun a => ∑' n, f n a := by
    funext a
    unfold farSum
    rw [← tsum_mul_right]
    refine tsum_congr fun n => ?_
    simp only [hf, hc]
    ring
  refine ⟨by rw [hS]; exact hint, ?_⟩
  rw [hS, ← integral_tsum_of_summable_integral_norm hfi hsum]
  calc ∑' n, ∫ a, f n a
      = ∑' n : ℕ, (if 2 ≤ n then lam n else 0) / (n : ℝ) ^ (1 + σ) * (farLaplace σ / 2) :=
        tsum_congr fun n => by rw [hfint n, ← hterm n]; ring
    _ = farLaplace σ / 2 * oddDirichlet lam σ := by
        rw [tsum_mul_right]; unfold oddDirichlet; exact mul_comm _ _

/-- **The Laplace lower bound.**  Odd positivity at pole weight `β ≥ 0` gives, for `σ > 0`,
`½ K(σ) F(σ) ≥ βJ²/(2σ) − (2βJ² + A₀)/(1 + 2σ)`. -/
theorem farLaplace_lower {β : ℝ} {lam : ℕ → ℝ} (h : WeilPositiveOddAt β lam) (hβ : 0 ≤ β)
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) {σ : ℝ} (hσ : 0 < σ) :
    β * farJ ^ 2 / (2 * σ) - (2 * β * farJ ^ 2 + farArchConst) / (1 + 2 * σ) ≤
      farLaplace σ / 2 * oddDirichlet lam σ := by
  obtain ⟨hint, heq⟩ := integral_farSum_mul_exp hsl hσ
  have hzero : ∫ a in Ioi 0, farSum lam a * Real.exp (-(1 + 2 * σ) * a) =
      ∫ a, farSum lam a * Real.exp (-(1 + 2 * σ) * a) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun a ha => by
      simp only [mem_Ioi, not_lt] at ha
      rw [farSum_eq_zero_of_nonpos lam ha, zero_mul]
  rw [← heq, ← hzero]
  have h1 : IntegrableOn (fun a : ℝ => Real.exp (-(2 * σ) * a)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  have h2 : IntegrableOn (fun a : ℝ => Real.exp (-(1 + 2 * σ) * a)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  have hval : ∫ a in Ioi 0, (β * farJ ^ 2 * Real.exp (-(2 * σ) * a) -
      (2 * β * farJ ^ 2 + farArchConst) * Real.exp (-(1 + 2 * σ) * a)) =
      β * farJ ^ 2 / (2 * σ) - (2 * β * farJ ^ 2 + farArchConst) / (1 + 2 * σ) := by
    rw [integral_sub (h1.const_mul _) (h2.const_mul _), integral_const_mul, integral_const_mul,
      integral_exp_mul_Ioi (by linarith), integral_exp_mul_Ioi (by linarith)]
    simp only [mul_zero, Real.exp_zero, neg_div_neg_eq]
    ring
  rw [← hval]
  refine setIntegral_mono_on ((h1.const_mul _).sub (h2.const_mul _)) hint.integrableOn
    measurableSet_Ioi fun a ha => ?_
  have hge := farSum_ge h hβ (le_of_lt (mem_Ioi.mp ha))
  have hw := Real.exp_pos (-(1 + 2 * σ) * a)
  have he : Real.exp (-(2 * σ) * a) = Real.exp a * Real.exp (-(1 + 2 * σ) * a) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [he]
  calc β * farJ ^ 2 * (Real.exp a * Real.exp (-(1 + 2 * σ) * a)) -
        (2 * β * farJ ^ 2 + farArchConst) * Real.exp (-(1 + 2 * σ) * a)
      = (β * (Real.exp a - 2) * farJ ^ 2 - farArchConst) * Real.exp (-(1 + 2 * σ) * a) := by
        ring
    _ ≤ farSum lam a * Real.exp (-(1 + 2 * σ) * a) := mul_le_mul_of_nonneg_right hge hw.le

/-! ## The ceiling -/

/-- **Odd Weil positivity caps the pole weight at one.** -/
theorem le_one_of_weilPositiveOddAt {β : ℝ} {lam : ℕ → ℝ} (h : WeilPositiveOddAt β lam) :
    β ≤ 1 := by
  rcases le_or_gt β 0 with hβ0 | hβ0
  · linarith
  have hβ := hβ0.le
  have hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ := fun σ hσ =>
    summable_abs_div_rpow_of_weilPositiveOddAt h hβ hσ
  have hJ : 0 < farJ ^ 2 := pow_pos farJ_pos 2
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨N₀, hN₀⟩ := odd_log_density_le h (ε := ε / 4) (by positivity)
  set K : ℝ := ∑ N ∈ Finset.range N₀, |logDensitySum lam N| with hKdef
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hK : ∀ N : ℕ, N < N₀ → logDensitySum lam N ≤ K := fun N hN =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun N => |logDensitySum lam N|)
      (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr hN))
  -- the Abelian upper bound
  have hU : ∀ σ : ℝ, 0 < σ → σ * oddDirichlet lam σ * ((σ : ℂ) * riemannZeta (1 + σ)).re ≤
      σ ^ 2 * K + (1 + ε / 2) := by
    intro σ hσ
    have hc := re_LSeries_lamConv_le hsl (c := 1 / 2 + ε / 4) (by positivity)
      (fun N hN => hN₀ N hN) hK hK0 hσ
    rw [LSeries_lamConv hsl hσ, LSeries_lamC_eq_oddDirichlet, Complex.re_ofReal_mul] at hc
    rw [Complex.re_ofReal_mul]
    calc σ * oddDirichlet lam σ * (σ * (riemannZeta (1 + σ)).re)
        = σ ^ 2 * (oddDirichlet lam σ * (riemannZeta (1 + σ)).re) := by ring
      _ ≤ σ ^ 2 * (K + 2 * (1 / 2 + ε / 4) / σ ^ 2) :=
          mul_le_mul_of_nonneg_left hc (by positivity)
      _ = σ ^ 2 * K + (1 + ε / 2) := by field_simp; ring
  -- the Laplace lower bound
  have hL : ∀ σ : ℝ, 0 < σ →
      β * farJ ^ 2 - 2 * σ * (2 * β * farJ ^ 2 + farArchConst) / (1 + 2 * σ) ≤
        farLaplace σ * (σ * oddDirichlet lam σ) := by
    intro σ hσ
    have h2 := mul_le_mul_of_nonneg_left (farLaplace_lower h hβ hsl hσ)
      (by positivity : (0 : ℝ) ≤ 2 * σ)
    have e1 : 2 * σ * (β * farJ ^ 2 / (2 * σ)) = β * farJ ^ 2 := by
      rw [mul_div_assoc']; exact mul_div_cancel_left₀ _ (by positivity)
    have e2 : 2 * σ * (β * farJ ^ 2 / (2 * σ) -
        (2 * β * farJ ^ 2 + farArchConst) / (1 + 2 * σ)) =
        β * farJ ^ 2 - 2 * σ * (2 * β * farJ ^ 2 + farArchConst) / (1 + 2 * σ) := by
      rw [mul_sub, e1, mul_div_assoc]
    rw [e2] at h2
    calc _ ≤ 2 * σ * (farLaplace σ / 2 * oddDirichlet lam σ) := h2
      _ = farLaplace σ * (σ * oddDirichlet lam σ) := by ring
  have hKb : ∀ σ : ℝ, 0 < σ → 0 ≤ farLaplace σ ∧ farLaplace σ ≤ Real.exp (σ / 6) * farJ ^ 2 :=
    fun σ hσ => ⟨integral_nonneg fun u => mul_nonneg (farKernel_nonneg u) (Real.exp_pos _).le,
      (farLaplace_le hσ.le).trans_eq (by rw [farLaplace_zero])⟩
  -- the limits
  have hg : Tendsto (fun σ : ℝ => ((σ : ℂ) * riemannZeta (1 + σ)).re) (𝓝[>] 0) (𝓝 1) := by
    have h1 := (Complex.continuous_re.tendsto (1 : ℂ)).comp tendsto_mul_riemannZeta_one_add
    rw [Complex.one_re] at h1
    exact h1
  have hN : Tendsto (fun σ : ℝ => β * farJ ^ 2 - 2 * σ * (2 * β * farJ ^ 2 + farArchConst) /
      (1 + 2 * σ)) (𝓝[>] 0) (𝓝 (β * farJ ^ 2)) := by
    have hd : ContinuousAt (fun σ : ℝ => β * farJ ^ 2 -
        2 * σ * (2 * β * farJ ^ 2 + farArchConst) / (1 + 2 * σ)) 0 :=
      continuousAt_const.sub (ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num))
    have h1 := hd.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using h1
  have hR : Tendsto (fun σ : ℝ => (σ ^ 2 * K + (1 + ε / 2)) * (Real.exp (σ / 6) * farJ ^ 2))
      (𝓝[>] 0) (𝓝 ((1 + ε / 2) * farJ ^ 2)) := by
    have hc : Continuous fun σ : ℝ =>
        (σ ^ 2 * K + (1 + ε / 2)) * (Real.exp (σ / 6) * farJ ^ 2) := by fun_prop
    exact (hc.tendsto' 0 _ (by simp)).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ σ : ℝ in 𝓝[>] 0, (β * farJ ^ 2 - 2 * σ * (2 * β * farJ ^ 2 + farArchConst) /
      (1 + 2 * σ)) * ((σ : ℂ) * riemannZeta (1 + σ)).re ≤
      (σ ^ 2 * K + (1 + ε / 2)) * (Real.exp (σ / 6) * farJ ^ 2) := by
    have hpos : ∀ᶠ σ in 𝓝[>] (0 : ℝ), 0 < σ := self_mem_nhdsWithin
    have hgpos : ∀ᶠ σ : ℝ in 𝓝[>] 0, 0 < ((σ : ℂ) * riemannZeta (1 + σ)).re :=
      hg.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [hpos, hgpos] with σ hσ' hgσ
    obtain ⟨hK1, hK2⟩ := hKb σ hσ'
    have hU0 : 0 ≤ σ ^ 2 * K + (1 + ε / 2) := by positivity
    calc (β * farJ ^ 2 - 2 * σ * (2 * β * farJ ^ 2 + farArchConst) / (1 + 2 * σ)) *
          ((σ : ℂ) * riemannZeta (1 + σ)).re
        ≤ farLaplace σ * (σ * oddDirichlet lam σ) * ((σ : ℂ) * riemannZeta (1 + σ)).re :=
          mul_le_mul_of_nonneg_right (hL σ hσ') hgσ.le
      _ = farLaplace σ * (σ * oddDirichlet lam σ * ((σ : ℂ) * riemannZeta (1 + σ)).re) := by
          ring
      _ ≤ farLaplace σ * (σ ^ 2 * K + (1 + ε / 2)) := mul_le_mul_of_nonneg_left (hU σ hσ') hK1
      _ ≤ Real.exp (σ / 6) * farJ ^ 2 * (σ ^ 2 * K + (1 + ε / 2)) :=
          mul_le_mul_of_nonneg_right hK2 hU0
      _ = (σ ^ 2 * K + (1 + ε / 2)) * (Real.exp (σ / 6) * farJ ^ 2) := by ring
  have hle := le_of_tendsto_of_tendsto (hN.mul hg) hR hev
  rw [mul_one] at hle
  have hβε : β ≤ 1 + ε / 2 := le_of_mul_le_mul_right hle hJ
  linarith

/-- **The prime-blind odd window lies in `(−∞, 1]`.** -/
theorem le_one_of_primeBlindPositiveOddAt {β : ℝ} (h : PrimeBlindPositiveOddAt β) : β ≤ 1 := by
  obtain ⟨lam, hlam⟩ := (exists_weilPositiveOddAt_iff β).mpr h
  exact le_one_of_weilPositiveOddAt hlam

theorem not_primeBlindPositiveOddAt_of_one_lt {β : ℝ} (hβ : 1 < β) :
    ¬ PrimeBlindPositiveOddAt β := fun h =>
  absurd (le_one_of_primeBlindPositiveOddAt h) (not_le.mpr hβ)

theorem not_weilPositiveOddAt_of_one_lt {β : ℝ} (hβ : 1 < β) (lam : ℕ → ℝ) :
    ¬ WeilPositiveOddAt β lam := fun h =>
  absurd (le_one_of_weilPositiveOddAt h) (not_le.mpr hβ)

/-- **Under RH the prime-blind odd window is exactly `(−∞, 1]`.** -/
theorem riemannHypothesis_imp_primeBlindPositiveOddAt_iff (hRH : RiemannHypothesis) (β : ℝ) :
    PrimeBlindPositiveOddAt β ↔ β ≤ 1 :=
  ⟨le_one_of_primeBlindPositiveOddAt, primeBlindPositiveOddAt_of_riemannHypothesis hRH⟩

end RHTower.OddSector

end
