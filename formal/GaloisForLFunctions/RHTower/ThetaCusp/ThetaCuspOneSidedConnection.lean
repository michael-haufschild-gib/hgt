import GaloisForLFunctions.RHTower.ThetaRationalCuspBoundary
import GaloisForLFunctions.RHTower.ThetaZeroDivisionSource
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailFiniteTranslationBounds

/-!
# The one-sided theta connection: Ward reduction and contour rotation

For `H(z) = ∫₀^∞ k(x) e^{izx} dx`, two integrations by parts on the raw theta tail
`T₀(x) = e^{x/2}(ϑ(e^{2x}) - 1)/2` (with `k = T₀'' - T₀/4`, `T₀'(0) = -1/4`) and the clock
substitution `y = e^{2x}` give, for every complex `z`,

`H(z) = 1/4 + (iz/2)(ϑ(1) - 1) - ((z² + 1/4)/4) M_z`,   `M_z = ∫₁^∞ y^{iz/2 - 3/4}(ϑ(y) - 1) dy`,

hence `XiC(z) = 1/2 - ((z² + 1/4)/4)(M_z + M_{-z})`, with `M` entire.

In the logarithmic clock `y = e^w` the integrand `e^{izw/2} κ(e^w)` is holomorphic on
`|Im w| < π/2` and decays doubly exponentially on half-strips (sector bound for `κ`).  Cauchy's
theorem on rectangles `[0, L] × [0, φ]` gives the exact rotated branch
`H(z) = ½ (i ∫₀^φ e^{iθ} F_z(e^{iθ}) dθ + e^{iφ} ∫₁^∞ F_z(r e^{iφ}) dr)`, `F_z(y) = y^{iz/2-1} κ(y)`,
for every `0 < φ < π/2`.
-/
open Complex Filter Topology Set MeasureTheory

noncomputable section

namespace RHTower

/-! ## Theta tail bounds -/

theorem hasSum_jacobiThetaSum_sub_one {y : ℂ} (hy : 0 < y.re) :
    HasSum (fun n : ℕ => 2 * cexp (-(Real.pi : ℂ) * ((n + 1 : ℕ) : ℂ) ^ 2 * y))
      (jacobiThetaSum y - 1) := by
  have hs : Summable (fun n : ℤ => cexp (-(Real.pi : ℂ) * (n : ℂ) ^ 2 * y)) := by
    simpa using summable_theta_series 0 hy
  have h := hs.hasSum.nat_add_neg
  have hfun : (fun n : ℕ => cexp (-(Real.pi : ℂ) * ((n : ℤ) : ℂ) ^ 2 * y) +
      cexp (-(Real.pi : ℂ) * ((-(n : ℤ) : ℤ) : ℂ) ^ 2 * y)) =
      fun n : ℕ => 2 * cexp (-(Real.pi : ℂ) * (n : ℂ) ^ 2 * y) := by
    funext n; simp only [Int.cast_natCast, Int.cast_neg, neg_sq]; ring
  have hval : (∑' b : ℤ, cexp (-(Real.pi : ℂ) * (b : ℂ) ^ 2 * y)) +
      cexp (-(Real.pi : ℂ) * ((0 : ℤ) : ℂ) ^ 2 * y) = jacobiThetaSum y + 1 := by
    simp [jacobiThetaSum]
  rw [hfun, hval] at h
  have h3 := (hasSum_nat_add_iff' 1).mpr h
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_pow two_ne_zero,
    mul_zero, zero_mul, Complex.exp_zero, mul_one] at h3
  have e : jacobiThetaSum y + 1 - 2 = jacobiThetaSum y - 1 := by ring
  rw [e] at h3
  refine h3.congr_fun fun n => ?_
  push_cast; ring

theorem norm_cexp_neg_pi_natSq (m : ℕ) (y : ℂ) :
    ‖cexp (-(Real.pi : ℂ) * (m : ℂ) ^ 2 * y)‖ = Real.exp (-(Real.pi * (m : ℝ) ^ 2 * y.re)) := by
  have := norm_cexp_neg_pi_sq (m : ℤ) y
  simpa using this

theorem norm_jacobiThetaSum_sub_one_le {y : ℂ} (hy : 0 < y.re) :
    ‖jacobiThetaSum y - 1‖ ≤ 2 * (Real.exp (-(Real.pi * y.re)) /
      (1 - Real.exp (-(Real.pi * y.re)))) := by
  set r := Real.exp (-(Real.pi * y.re))
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hgeom : HasSum (fun n : ℕ => 2 * r ^ (n + 1)) (2 * (r / (1 - r))) := by
    have := ((hasSum_geometric_of_lt_one hr0 hr1).mul_left r).mul_left 2
    rw [show r * (1 - r)⁻¹ = r / (1 - r) by ring] at this
    exact this.congr_fun fun n => by ring
  have hbound : ∀ n : ℕ, ‖2 * cexp (-(Real.pi : ℂ) * ((n + 1 : ℕ) : ℂ) ^ 2 * y)‖ ≤
      2 * r ^ (n + 1) := by
    intro n
    rw [norm_mul, Complex.norm_ofNat, norm_cexp_neg_pi_natSq (n + 1) y]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    rw [← Real.exp_nat_mul]
    refine Real.exp_le_exp.mpr ?_
    have h1 : ((n + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
      nlinarith
    have hpy : 0 ≤ Real.pi * y.re := by positivity
    nlinarith
  rw [← (hasSum_jacobiThetaSum_sub_one hy).tsum_eq]
  exact tsum_of_norm_bounded hgeom hbound

/-! ## The one-sided connection and its Ward reduction -/

/-- The one-sided connection `H(z) = ∫₀^∞ k(x) e^{izx} dx`. -/
def thetaOneSidedConnection (z : ℂ) : ℂ :=
  ∫ x in Ioi (0 : ℝ), (thetaCuspFullSource x : ℂ) * cexp (I * z * x)

/-- The Ward exponent `α_z = iz/2 - 3/4`. -/
def wardExponent (z : ℂ) : ℂ := I * z / 2 - 3 / 4

/-- The Ward Mellin integral `M_z = ∫₁^∞ y^{α_z} (ϑ(y) - 1) dy`. -/
def wardMellin (z : ℂ) : ℂ :=
  ∫ y in Ioi (1 : ℝ), (y : ℂ) ^ wardExponent z * (jacobiThetaSum y - 1)

theorem jacobiThetaSum_ofReal_eq_evenKernel (t : ℝ) :
    jacobiThetaSum t = (HurwitzZeta.evenKernel 0 t : ℂ) := by
  have h := HurwitzZeta.evenKernel_def 0 t
  simp only [QuotientAddGroup.mk_zero, Complex.ofReal_zero, zero_pow two_ne_zero, mul_zero,
    zero_mul, Complex.exp_zero, one_mul] at h
  rw [h]
  unfold jacobiThetaSum jacobiTheta₂
  refine tsum_congr fun n => ?_
  unfold jacobiTheta₂_term
  congr 1
  ring_nf
  rw [I_sq]
  ring_nf

/-- The raw theta tail in the clock variable: `T₀(x) = e^{x/2} (ϑ(e^{2x}) - 1)/2`. -/
theorem thetaCuspTailDerivative_zero_eq_jacobiThetaSum (x : ℝ) :
    ((thetaCuspTailDerivative 0 x : ℝ) : ℂ) =
      (Real.exp (x / 2) : ℂ) * (jacobiThetaSum (Real.exp (2 * x)) - 1) / 2 := by
  rw [thetaCuspTailDerivative_zero_eq_evenKernel,
    jacobiThetaSum_ofReal_eq_evenKernel]
  push_cast; ring

theorem norm_cexp_I_mul_ofReal (z : ℂ) (x : ℝ) : ‖cexp (I * z * x)‖ = Real.exp (-(z.im * x)) := by
  rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re]

/-- `e^{izx} T_m(x)` is integrable on `(0, ∞)` for every complex `z`. -/
theorem integrableOn_cexp_mul_thetaCuspTailDerivative (m : ℕ) (z : ℂ) :
    IntegrableOn (fun x : ℝ => cexp (I * z * x) * (thetaCuspTailDerivative m x : ℂ)) (Ioi 0) := by
  obtain ⟨p, hp⟩ := exists_nat_gt (|z.im| + 1)
  have hint : IntegrableOn (fun x : ℝ => thetaCuspTailDerivativeNatExpConstant m p *
      Real.exp ((|z.im| - p) * x)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul _
  refine hint.mono' ?_ ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_))
  · exact (Continuous.aestronglyMeasurable (by
      have := (differentiable_thetaCuspTailDerivative m).continuous
      fun_prop))
  · have hx0 : (0 : ℝ) < x := hx
    rw [norm_mul, norm_cexp_I_mul_ofReal, Complex.norm_real, Real.norm_eq_abs]
    have hb := abs_thetaCuspTailDerivative_le_nat_exp_neg m p hx0.le
    calc Real.exp (-(z.im * x)) * |thetaCuspTailDerivative m x|
        ≤ Real.exp (|z.im| * x) * (thetaCuspTailDerivativeNatExpConstant m p *
            Real.exp (-(p : ℝ) * x)) := by
          refine mul_le_mul (Real.exp_le_exp.mpr ?_) hb (abs_nonneg _) (Real.exp_pos _).le
          have := neg_abs_le z.im; nlinarith
      _ = thetaCuspTailDerivativeNatExpConstant m p * Real.exp ((|z.im| - p) * x) := by
          rw [mul_comm, mul_assoc, ← Real.exp_add]; ring_nf

theorem tendsto_cexp_mul_thetaCuspTailDerivative (m : ℕ) (z : ℂ) :
    Tendsto (fun x : ℝ => cexp (I * z * x) * (thetaCuspTailDerivative m x : ℂ)) atTop (𝓝 0) := by
  obtain ⟨p, hp⟩ := exists_nat_gt (|z.im| + 1)
  have hlim : Tendsto (fun x : ℝ => thetaCuspTailDerivativeNatExpConstant m p *
      Real.exp ((|z.im| - p) * x)) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg
      (by linarith : |z.im| - (p : ℝ) < 0))
    simpa using h.const_mul (thetaCuspTailDerivativeNatExpConstant m p)
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 0] with x hx
  rw [norm_mul, norm_cexp_I_mul_ofReal, Complex.norm_real, Real.norm_eq_abs]
  have hb := abs_thetaCuspTailDerivative_le_nat_exp_neg m p hx
  calc Real.exp (-(z.im * x)) * |thetaCuspTailDerivative m x|
      ≤ Real.exp (|z.im| * x) * (thetaCuspTailDerivativeNatExpConstant m p *
          Real.exp (-(p : ℝ) * x)) := by
        refine mul_le_mul (Real.exp_le_exp.mpr ?_) hb (abs_nonneg _) (Real.exp_pos _).le
        have := neg_abs_le z.im; nlinarith
    _ = thetaCuspTailDerivativeNatExpConstant m p * Real.exp ((|z.im| - p) * x) := by
        rw [mul_comm, mul_assoc, ← Real.exp_add]; ring_nf

/-- One integration by parts: `∫₀^∞ e^{izx} T_{m+1} = -T_m(0) - iz ∫₀^∞ e^{izx} T_m`. -/
theorem integral_cexp_mul_thetaCuspTailDerivative_succ (m : ℕ) (z : ℂ) :
    (∫ x in Ioi (0 : ℝ), cexp (I * z * x) * (thetaCuspTailDerivative (m + 1) x : ℂ)) =
      -(thetaCuspTailDerivative m 0 : ℂ) -
        I * z * ∫ x in Ioi (0 : ℝ), cexp (I * z * x) * (thetaCuspTailDerivative m x : ℂ) := by
  have hu : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun x : ℝ => cexp (I * z * x)) (I * z * cexp (I * z * x)) x := by
    intro x _
    have h := ((Complex.hasDerivAt_exp _).comp (x : ℂ) ((hasDerivAt_id (x : ℂ)).const_mul (I * z))).comp_ofReal
    exact h.congr_deriv (by simp only [mul_one, id]; ring)
  have hv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun x : ℝ => (thetaCuspTailDerivative m x : ℂ))
      (thetaCuspTailDerivative (m + 1) x : ℂ) x :=
    fun x _ => (hasDerivAt_thetaCuspTailDerivative m x).ofReal_comp
  have hcont : Continuous (fun x : ℝ => cexp (I * z * x) * (thetaCuspTailDerivative m x : ℂ)) := by
    have := (differentiable_thetaCuspTailDerivative m).continuous; fun_prop
  have hzero : Tendsto ((fun x : ℝ => cexp (I * z * x)) * fun x : ℝ => (thetaCuspTailDerivative m x : ℂ))
      (𝓝[>] 0) (𝓝 (thetaCuspTailDerivative m 0 : ℂ)) := by
    have := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] at this
    exact this
  have h := integral_Ioi_mul_deriv_eq_deriv_mul hu hv
    (integrableOn_cexp_mul_thetaCuspTailDerivative (m + 1) z)
    (IntegrableOn.congr_fun ((integrableOn_cexp_mul_thetaCuspTailDerivative m z).const_mul (I * z))
      (fun x _ => by simp only [Pi.mul_apply]; ring) measurableSet_Ioi)
    hzero (tendsto_cexp_mul_thetaCuspTailDerivative m z)
  rw [h, zero_sub, ← integral_const_mul]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => by ring

theorem norm_jacobiThetaSum_sub_one_le_of_one_le {u : ℝ} (hu : 1 ≤ u) :
    ‖jacobiThetaSum u - 1‖ ≤ 4 * Real.exp (-(Real.pi * u)) := by
  have hre : (0 : ℝ) < (u : ℂ).re := by simp; linarith
  have h := norm_jacobiThetaSum_sub_one_le hre
  simp only [Complex.ofReal_re] at h
  set r := Real.exp (-(Real.pi * u))
  have hr : r ≤ Real.exp (-Real.pi) := Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  have hπ : Real.exp (-Real.pi) < 1 / 2 := by
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
    have := Real.add_one_lt_exp (show Real.pi ≠ 0 from Real.pi_ne_zero)
    linarith [Real.pi_gt_three]
  have hr0 : 0 < r := Real.exp_pos _
  have h1 : 1 / 2 < 1 - r := by linarith
  calc ‖jacobiThetaSum u - 1‖ ≤ 2 * (r / (1 - r)) := h
    _ ≤ 2 * (r / (1 / 2)) := by gcongr
    _ = 4 * r := by ring

theorem integrableOn_wardMellin_integrand (z : ℂ) :
    IntegrableOn (fun u : ℝ => (u : ℂ) ^ wardExponent z * (jacobiThetaSum u - 1)) (Ici 1) := by
  set N := ⌈|(wardExponent z).re|⌉₊
  have hint : IntegrableOn (fun u : ℝ => 4 * N.factorial * Real.exp ((1 - Real.pi) * u)) (Ici 1) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact (integrableOn_exp_mul_Ioi (by linarith [Real.pi_gt_three]) 1).const_mul _
  refine hint.mono' ?_ ((ae_restrict_iff' measurableSet_Ici).mpr (Eventually.of_forall fun u hu => ?_))
  · refine ContinuousOn.aestronglyMeasurable (fun u hu => ?_) measurableSet_Ici
    have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu
    have hslit : (u : ℂ) ∈ Complex.slitPlane := Or.inl (by simpa using hu0)
    have h1 : ContinuousAt (fun u : ℝ => (u : ℂ) ^ wardExponent z) u :=
      (continuousAt_cpow_const hslit).comp Complex.continuous_ofReal.continuousAt
    have h2 : ContinuousAt (fun u : ℝ => jacobiThetaSum u) u :=
      (hasDerivAt_jacobiThetaSum (by simpa using hu0)).continuousAt.comp
        Complex.continuous_ofReal.continuousAt
    exact (h1.mul (h2.sub continuousAt_const)).continuousWithinAt
  · have hu1 : (1 : ℝ) ≤ u := hu
    have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu1
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0]
    have hpow : u ^ (wardExponent z).re ≤ N.factorial * Real.exp u := by
      calc u ^ (wardExponent z).re ≤ u ^ (N : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hu1 ((le_abs_self _).trans (Nat.le_ceil _))
        _ = u ^ N := Real.rpow_natCast u N
        _ ≤ N.factorial * Real.exp u := by
            have := Real.pow_div_factorial_le_exp u hu0.le N
            rwa [div_le_iff₀ (by positivity), mul_comm] at this
    have hθ := norm_jacobiThetaSum_sub_one_le_of_one_le hu1
    calc u ^ (wardExponent z).re * ‖jacobiThetaSum u - 1‖
        ≤ (N.factorial * Real.exp u) * (4 * Real.exp (-(Real.pi * u))) :=
          mul_le_mul hpow hθ (norm_nonneg _) (by positivity)
      _ = 4 * N.factorial * Real.exp ((1 - Real.pi) * u) := by
          rw [mul_mul_mul_comm, ← Real.exp_add]; ring_nf

/-- The clock substitution `y = e^{2x}`: `∫₀^∞ e^{izx} T₀(x) dx = M_z / 4`. -/
theorem integral_cexp_mul_thetaCuspTailDerivative_zero (z : ℂ) :
    (∫ x in Ioi (0 : ℝ), cexp (I * z * x) * (thetaCuspTailDerivative 0 x : ℂ)) =
      wardMellin z / 4 := by
  set α := wardExponent z
  have hid : ∀ x : ℝ, (2 * Real.exp (2 * x)) • ((Real.exp (2 * x) : ℂ) ^ α *
      (jacobiThetaSum (Real.exp (2 * x)) - 1)) =
      4 * (cexp (I * z * x) * (thetaCuspTailDerivative 0 x : ℂ)) := by
    intro x
    rw [thetaCuspTailDerivative_zero_eq_jacobiThetaSum, Complex.real_smul,
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'),
      ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp]
    push_cast
    have e : cexp (2 * (x : ℂ)) * cexp (2 * (x : ℂ) * α) = cexp (I * z * x) * cexp ((x : ℂ) / 2) := by
      rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; simp only [α, wardExponent]; ring
    linear_combination (2 * (jacobiThetaSum (cexp (2 * (x : ℂ))) - 1)) * e
  have hsub := integral_deriv_smul_comp_Ioi (a := 0) (f := fun x => Real.exp (2 * x))
    (f' := fun x => 2 * Real.exp (2 * x))
    (g := fun u : ℝ => (u : ℂ) ^ α * (jacobiThetaSum u - 1))
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn)
    (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)))
    (fun x _ => by
      have := ((Real.hasDerivAt_exp (2 * x)).comp x ((hasDerivAt_id x).const_mul 2))
      exact (this.congr_deriv (by simp only [mul_one]; ring)).hasDerivWithinAt)
    (fun u hu => by
      obtain ⟨x, _, rfl⟩ := hu
      have hu0 : (0 : ℝ) < Real.exp (2 * x) := Real.exp_pos _
      have hslit : ((Real.exp (2 * x) : ℝ) : ℂ) ∈ Complex.slitPlane :=
        Or.inl (by rw [Complex.ofReal_re]; exact hu0)
      have h1 : ContinuousAt (fun u : ℝ => (u : ℂ) ^ α) (Real.exp (2 * x)) :=
        (continuousAt_cpow_const hslit).comp Complex.continuous_ofReal.continuousAt
      have h2 : ContinuousAt (fun u : ℝ => jacobiThetaSum u) (Real.exp (2 * x)) :=
        (hasDerivAt_jacobiThetaSum (show (0 : ℝ) < ((Real.exp (2 * x) : ℝ) : ℂ).re by
          rw [Complex.ofReal_re]; exact hu0)).continuousAt.comp
          Complex.continuous_ofReal.continuousAt
      exact (h1.mul (h2.sub continuousAt_const)).continuousWithinAt)
    ((integrableOn_wardMellin_integrand z).mono_set (by
      rintro u ⟨x, hx, rfl⟩
      exact Real.one_le_exp (by have : (0 : ℝ) ≤ x := hx; linarith)))
    (by
      rw [integrableOn_Ici_iff_integrableOn_Ioi]
      refine IntegrableOn.congr_fun
        ((integrableOn_cexp_mul_thetaCuspTailDerivative 0 z).const_mul 4) (fun x _ => ?_)
        measurableSet_Ioi
      exact (hid x).symm)
  simp only [Real.exp_zero, mul_zero] at hsub
  rw [show (∫ x in Ioi (0 : ℝ), (2 * Real.exp (2 * x)) • (((fun u : ℝ =>
      (u : ℂ) ^ α * (jacobiThetaSum u - 1)) ∘ fun x => Real.exp (2 * x)) x)) =
      ∫ x in Ioi (0 : ℝ), 4 * (cexp (I * z * x) * (thetaCuspTailDerivative 0 x : ℂ)) from
      setIntegral_congr_fun measurableSet_Ioi fun x _ => hid x, integral_const_mul] at hsub
  unfold wardMellin
  rw [← hsub]
  ring

/-- **Ward reduction.** `H(z) = 1/4 + (iz/2)(ϑ(1) - 1) - ((z² + 1/4)/4) M_z` for every complex `z`. -/
theorem thetaOneSidedConnection_eq_ward (z : ℂ) :
    thetaOneSidedConnection z =
      1 / 4 + I * z / 2 * (jacobiThetaSum 1 - 1) - (z ^ 2 + 1 / 4) / 4 * wardMellin z := by
  have hk : ∀ x : ℝ, (thetaCuspFullSource x : ℂ) * cexp (I * z * x) =
      cexp (I * z * x) * (thetaCuspTailDerivative 2 x : ℂ) -
        (1 / 4) * (cexp (I * z * x) * (thetaCuspTailDerivative 0 x : ℂ)) := by
    intro x; rw [thetaCuspFullSource_eq_tail_second_sub]; push_cast; ring
  unfold thetaOneSidedConnection
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x _ => hk x), integral_sub
    (integrableOn_cexp_mul_thetaCuspTailDerivative 2 z)
    ((integrableOn_cexp_mul_thetaCuspTailDerivative 0 z).const_mul _), integral_const_mul,
    integral_cexp_mul_thetaCuspTailDerivative_succ 1 z,
    integral_cexp_mul_thetaCuspTailDerivative_succ 0 z,
    integral_cexp_mul_thetaCuspTailDerivative_zero, thetaCuspTailDerivative_one_zero]
  have h0 : (thetaCuspTailDerivative 0 0 : ℂ) = (jacobiThetaSum 1 - 1) / 2 := by
    rw [thetaCuspTailDerivative_zero_eq_jacobiThetaSum]; simp
  rw [h0]
  push_cast
  ring_nf
  rw [I_sq]
  ring

/-- `XiC z = H(z) + H(-z)`. -/
theorem XiC_eq_thetaOneSidedConnection_add (z : ℂ) :
    XiC z = thetaOneSidedConnection z + thetaOneSidedConnection (-z) := by
  rw [← sourceTransform_thetaSourceC,
    expMomentSource_thetaSourceC.sourceTransform_eq_integral_cos thetaSourceC_neg z]
  unfold thetaOneSidedConnection
  rw [← integral_add, ← integral_const_mul]
  · refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    have hcos : Complex.cos (z * x) = (cexp (z * x * I) + cexp (-(z * x) * I)) / 2 := rfl
    simp only [thetaSourceC, hcos]
    rw [show z * x * I = I * z * x by ring, show -(z * x) * I = I * -z * x by ring]
    ring
  · exact (expMomentSource_thetaSourceC.integrable_cexp (-z)).integrableOn.congr_fun
      (fun x _ => by simp only [thetaSourceC]; ring_nf) measurableSet_Ioi
  · exact (expMomentSource_thetaSourceC.integrable_cexp z).integrableOn.congr_fun
      (fun x _ => by simp only [thetaSourceC]; ring_nf) measurableSet_Ioi

/-- **Two-sided reduction.** `XiC z = 1/2 - ((z² + 1/4)/4)(M_z + M_{-z})`. -/
theorem XiC_eq_wardMellin (z : ℂ) :
    XiC z = 1 / 2 - (z ^ 2 + 1 / 4) / 4 * (wardMellin z + wardMellin (-z)) := by
  rw [XiC_eq_thetaOneSidedConnection_add, thetaOneSidedConnection_eq_ward,
    thetaOneSidedConnection_eq_ward]
  ring

/-- `M_z` is entire. -/
theorem differentiable_wardMellin : Differentiable ℂ wardMellin := by
  intro z₀
  have hrep : wardMellin = fun z => 4 * ∫ x in Ioi (0 : ℝ),
      cexp (I * z * x) * (thetaCuspTailDerivative 0 x : ℂ) := by
    funext z; rw [integral_cexp_mul_thetaCuspTailDerivative_zero]; ring
  rw [hrep]
  refine DifferentiableAt.const_mul ?_ 4
  obtain ⟨p, hp⟩ := exists_nat_gt (|z₀.im| + 2)
  set C := thetaCuspTailDerivativeNatExpConstant 0 p
  set bound : ℝ → ℝ := fun x => C * Real.exp ((|z₀.im| + 2 - p) * x)
  have hbound : IntegrableOn bound (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul _
  have hmeas : ∀ z : ℂ, AEStronglyMeasurable (fun x : ℝ => cexp (I * z * x) *
      (thetaCuspTailDerivative 0 x : ℂ)) (volume.restrict (Ioi 0)) := fun z =>
    (by have := (differentiable_thetaCuspTailDerivative 0).continuous; fun_prop :
      Continuous fun x : ℝ => cexp (I * z * x) * (thetaCuspTailDerivative 0 x : ℂ)).aestronglyMeasurable
  have hdom : ∀ᵐ x : ℝ ∂(volume.restrict (Ioi (0 : ℝ))), ∀ z ∈ Metric.ball z₀ 1,
      ‖(I * x) * cexp (I * z * x) * (thetaCuspTailDerivative 0 x : ℂ)‖ ≤ bound x := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx z hz => ?_)
    have hx0 : (0 : ℝ) < x := hx
    have hd : ‖z - z₀‖ < 1 := by rw [← dist_eq_norm]; exact hz
    have him : |z.im| ≤ |z₀.im| + 1 := by
      have h1 : |z.im - z₀.im| ≤ ‖z - z₀‖ := by
        simpa only [Complex.sub_im] using Complex.abs_im_le_norm (z - z₀)
      have := abs_sub_abs_le_abs_sub z.im z₀.im; linarith
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hx0, norm_cexp_I_mul_ofReal, Complex.norm_real, Real.norm_eq_abs]
    have hb := abs_thetaCuspTailDerivative_le_nat_exp_neg 0 p hx0.le
    have hxe : x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
    calc x * Real.exp (-(z.im * x)) * |thetaCuspTailDerivative 0 x|
        ≤ Real.exp x * Real.exp ((|z₀.im| + 1) * x) * (C * Real.exp (-(p : ℝ) * x)) := by
          refine mul_le_mul (mul_le_mul hxe (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le
            (Real.exp_pos _).le) hb (abs_nonneg _) (by positivity)
          have := neg_abs_le z.im; nlinarith
      _ = bound x := by
          simp only [bound]; rw [mul_comm, mul_assoc, ← Real.exp_add, ← Real.exp_add]; ring_nf
  have hderiv : ∀ᵐ x : ℝ ∂(volume.restrict (Ioi (0 : ℝ))), ∀ z ∈ Metric.ball z₀ 1,
      HasDerivAt (fun z => cexp (I * z * x) * (thetaCuspTailDerivative 0 x : ℂ))
        ((I * x) * cexp (I * z * x) * (thetaCuspTailDerivative 0 x : ℂ)) z := by
    refine Eventually.of_forall fun x z _ => ?_
    have h := ((Complex.hasDerivAt_exp _).comp z
      (((hasDerivAt_id z).const_mul I).mul_const (x : ℂ))).mul_const (thetaCuspTailDerivative 0 x : ℂ)
    exact h.congr_deriv (by simp only [mul_one, id]; ring)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds z₀ one_pos)
    (Eventually.of_forall hmeas) (integrableOn_cexp_mul_thetaCuspTailDerivative 0 z₀)
    ((by have := (differentiable_thetaCuspTailDerivative 0).continuous; fun_prop :
      Continuous fun x : ℝ => (I * x) * cexp (I * z₀ * x) *
        (thetaCuspTailDerivative 0 x : ℂ)).aestronglyMeasurable) hdom hbound hderiv).2.differentiableAt

/-! ## Sector decay of the boundary source -/

/-- The Gaussian weight constant `S_δ = Σ_n (2π² n⁴ + 3π n²) e^{-(πδ/2) n²}`. -/
def boundarySourceSectorConstant (δ : ℝ) : ℝ :=
  ∑' n : ℤ, (2 * Real.pi ^ 2 * |(n : ℝ)| ^ 4 + 3 * Real.pi * |(n : ℝ)| ^ 2) *
    Real.exp (-((Real.pi * δ / 2) * (n : ℝ) ^ 2))

theorem summable_boundarySourceSector {δ : ℝ} (hδ : 0 < δ) :
    Summable (fun n : ℤ => (2 * Real.pi ^ 2 * |(n : ℝ)| ^ 4 + 3 * Real.pi * |(n : ℝ)| ^ 2) *
      Real.exp (-((Real.pi * δ / 2) * (n : ℝ) ^ 2))) := by
  have h4 := summable_int_pow_mul_exp_neg_sq 4 (by positivity : 0 < Real.pi * δ / 2)
  have h2 := summable_int_pow_mul_exp_neg_sq 2 (by positivity : 0 < Real.pi * δ / 2)
  exact ((h4.mul_left (2 * Real.pi ^ 2)).add (h2.mul_left (3 * Real.pi))).congr fun n => by ring

/-- **Sector decay.** For `Re y ≥ δ > 0`,
`‖κ(y)‖ ≤ S_δ ‖y‖^{5/4} (‖y‖ + 1) e^{-(π/2) Re y}`. -/
theorem norm_thetaBoundarySource_le {δ : ℝ} (hδ : 0 < δ) {y : ℂ} (hy : δ ≤ y.re) :
    ‖thetaBoundarySource y‖ ≤ boundarySourceSectorConstant δ * ‖y‖ ^ (5 / 4 : ℝ) *
      (‖y‖ + 1) * Real.exp (-(Real.pi / 2 * y.re)) := by
  have hy0 : 0 < y.re := lt_of_lt_of_le hδ hy
  rw [thetaBoundarySource_eq_tsum hy0, norm_mul,
    show (5 / 4 : ℂ) = ((5 / 4 : ℝ) : ℂ) by push_cast; ring, Complex.norm_cpow_real]
  have hterm : ∀ n : ℤ, ‖thetaBoundaryTerm y n‖ ≤
      ((2 * Real.pi ^ 2 * |(n : ℝ)| ^ 4 + 3 * Real.pi * |(n : ℝ)| ^ 2) *
        Real.exp (-((Real.pi * δ / 2) * (n : ℝ) ^ 2))) * ((‖y‖ + 1) * Real.exp (-(Real.pi / 2 * y.re))) := by
    intro n
    by_cases hn : n = 0
    · subst hn; simp [thetaBoundaryTerm]
    have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
      have : (1 : ℤ) ≤ n ^ 2 := by
        rcases lt_trichotomy n 0 with h | h | h
        · nlinarith
        · exact absurd h hn
        · nlinarith
      exact_mod_cast this
    unfold thetaBoundaryTerm
    rw [norm_mul, norm_cexp_neg_pi_sq]
    have hpoly : ‖2 * (Real.pi : ℂ) ^ 2 * (n : ℂ) ^ 4 * y - 3 * Real.pi * (n : ℂ) ^ 2‖ ≤
        (2 * Real.pi ^ 2 * |(n : ℝ)| ^ 4 + 3 * Real.pi * |(n : ℝ)| ^ 2) * (‖y‖ + 1) := by
      refine (norm_sub_le _ _).trans ?_
      simp only [norm_mul, norm_pow, Complex.norm_real, Complex.norm_intCast, Complex.norm_ofNat,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      have h1 : 0 ≤ 2 * Real.pi ^ 2 * |(n : ℝ)| ^ 4 := by positivity
      have h2 : 0 ≤ 3 * Real.pi * |(n : ℝ)| ^ 2 * ‖y‖ := by positivity
      nlinarith
    have hexp : Real.exp (-(Real.pi * (n : ℝ) ^ 2 * y.re)) ≤
        Real.exp (-((Real.pi * δ / 2) * (n : ℝ) ^ 2)) * Real.exp (-(Real.pi / 2 * y.re)) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have h1 : (n : ℝ) ^ 2 * y.re ≥ (n : ℝ) ^ 2 * δ / 2 + y.re / 2 := by nlinarith
      nlinarith [Real.pi_pos]
    calc ‖2 * (Real.pi : ℂ) ^ 2 * (n : ℂ) ^ 4 * y - 3 * Real.pi * (n : ℂ) ^ 2‖ *
          Real.exp (-(Real.pi * (n : ℝ) ^ 2 * y.re))
        ≤ ((2 * Real.pi ^ 2 * |(n : ℝ)| ^ 4 + 3 * Real.pi * |(n : ℝ)| ^ 2) * (‖y‖ + 1)) *
          (Real.exp (-((Real.pi * δ / 2) * (n : ℝ) ^ 2)) * Real.exp (-(Real.pi / 2 * y.re))) :=
          mul_le_mul hpoly hexp (Real.exp_pos _).le (by positivity)
      _ = _ := by ring
  have hsum := (summable_boundarySourceSector hδ).mul_right ((‖y‖ + 1) * Real.exp (-(Real.pi / 2 * y.re)))
  have hS := tsum_of_norm_bounded hsum.hasSum hterm
  rw [tsum_mul_right] at hS
  calc ‖y‖ ^ (5 / 4 : ℝ) * ‖∑' n : ℤ, thetaBoundaryTerm y n‖
      ≤ ‖y‖ ^ (5 / 4 : ℝ) * (boundarySourceSectorConstant δ *
          ((‖y‖ + 1) * Real.exp (-(Real.pi / 2 * y.re)))) :=
        mul_le_mul_of_nonneg_left hS (by positivity)
    _ = _ := by ring

/-- `u^m e^{-bu} ≤ m!/b^m` for `u ≥ 0`, `b > 0`. -/
theorem pow_mul_exp_neg_mul_le_factorial {b u : ℝ} (hb : 0 < b) (hu : 0 ≤ u) (m : ℕ) :
    u ^ m * Real.exp (-(b * u)) ≤ m.factorial / b ^ m := by
  have h := Real.pow_div_factorial_le_exp (b * u) (by positivity) m
  rw [div_le_iff₀ (by positivity)] at h
  rw [le_div_iff₀ (by positivity), Real.exp_neg]
  have hexp := Real.exp_pos (b * u)
  calc u ^ m * (Real.exp (b * u))⁻¹ * b ^ m = (b * u) ^ m * (Real.exp (b * u))⁻¹ := by ring
    _ ≤ Real.exp (b * u) * m.factorial * (Real.exp (b * u))⁻¹ :=
        mul_le_mul_of_nonneg_right h (inv_nonneg.mpr hexp.le)
    _ = m.factorial := by field_simp

/-- A doubly exponential factor beats every exponential: `e^{ax} e^{-b e^x} ≤ C e^{-x}` on `x ≥ 0`. -/
theorem exists_exp_mul_exp_neg_exp_le (a : ℝ) {b : ℝ} (hb : 0 < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 ≤ x →
      Real.exp (a * x) * Real.exp (-(b * Real.exp x)) ≤ C * Real.exp (-x) := by
  set m := ⌈|a| + 1⌉₊
  refine ⟨m.factorial / b ^ m, by positivity, fun x hx => ?_⟩
  have hu : 1 ≤ Real.exp x := Real.one_le_exp hx
  have h1 : Real.exp ((a + 1) * x) ≤ Real.exp x ^ m := by
    rw [← Real.exp_nat_mul]
    refine Real.exp_le_exp.mpr ?_
    have : a + 1 ≤ (m : ℝ) := by
      have := Nat.le_ceil (|a| + 1); have := le_abs_self a; linarith
    nlinarith
  have h2 := pow_mul_exp_neg_mul_le_factorial hb (Real.exp_pos x).le m
  calc Real.exp (a * x) * Real.exp (-(b * Real.exp x))
      = Real.exp ((a + 1) * x) * Real.exp (-(b * Real.exp x)) * Real.exp (-x) := by
        rw [mul_right_comm, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; ring_nf
    _ ≤ Real.exp x ^ m * Real.exp (-(b * Real.exp x)) * Real.exp (-x) := by gcongr
    _ ≤ m.factorial / b ^ m * Real.exp (-x) := by gcongr

/-! ## Contour rotation in the logarithmic clock -/

/-- **Rotation of a half-line integral** through the rectangle `[0, L] × [0, φ]`. -/
theorem integral_Ioi_eq_rotated {f : ℂ → ℂ} {φ : ℝ} (hφ : 0 ≤ φ)
    (hd : ∀ w : ℂ, 0 ≤ w.re → 0 ≤ w.im → w.im ≤ φ → DifferentiableAt ℂ f w)
    (hi0 : IntegrableOn (fun t : ℝ => f t) (Ioi 0))
    (hiφ : IntegrableOn (fun t : ℝ => f (t + φ * I)) (Ioi 0))
    (hdecay : Tendsto (fun L : ℝ => ∫ s in (0 : ℝ)..φ, f (L + s * I)) atTop (𝓝 0)) :
    (∫ t in Ioi (0 : ℝ), f t) =
      (∫ t in Ioi (0 : ℝ), f (t + φ * I)) + I * ∫ s in (0 : ℝ)..φ, f (s * I) := by
  have hrect : ∀ L : ℝ, 0 ≤ L → (∫ x in (0 : ℝ)..L, f x) - (∫ x in (0 : ℝ)..L, f (x + φ * I)) +
      I * (∫ y in (0 : ℝ)..φ, f (L + y * I)) - I * (∫ y in (0 : ℝ)..φ, f (y * I)) = 0 := by
    intro L hL
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f 0 (L + φ * I) (by
      intro w hw
      obtain ⟨hre, him⟩ := hw
      simp only [Complex.zero_re, Complex.add_re, Complex.ofReal_re, Complex.mul_I_re,
        Complex.mul_I_im, Complex.ofReal_im, neg_zero, add_zero,
        Complex.zero_im, Complex.add_im, zero_add] at hre him
      rw [Set.mem_preimage, Set.uIcc_of_le hL] at hre
      rw [Set.mem_preimage, Set.uIcc_of_le hφ] at him
      exact (hd w hre.1 him.1 him.2).differentiableWithinAt)
    simp only [Complex.zero_re, Complex.add_re, Complex.ofReal_re, Complex.mul_I_re,
      Complex.mul_I_im, Complex.ofReal_im, neg_zero, add_zero,
      Complex.zero_im, Complex.add_im, zero_add, zero_mul, smul_eq_mul, Complex.ofReal_zero] at h
    exact h
  have hB := intervalIntegral_tendsto_integral_Ioi 0 hi0 tendsto_id
  have hT := intervalIntegral_tendsto_integral_Ioi 0 hiφ tendsto_id
  have hlim := ((hB.sub hT).add (hdecay.const_mul I)).sub
    (tendsto_const_nhds (x := I * ∫ y in (0 : ℝ)..φ, f (y * I)))
  have hzero : Tendsto (fun L : ℝ => (∫ x in (0 : ℝ)..L, f x) - (∫ x in (0 : ℝ)..L, f (x + φ * I)) +
      I * (∫ y in (0 : ℝ)..φ, f (L + y * I)) - I * (∫ y in (0 : ℝ)..φ, f (y * I))) atTop (𝓝 0) :=
    tendsto_const_nhds.congr' (eventually_ge_atTop 0 |>.mono fun L hL => (hrect L hL).symm)
  have := tendsto_nhds_unique hlim hzero
  rw [mul_zero, add_zero] at this
  linear_combination this

theorem cpow_cexp {w : ℂ} (h1 : -Real.pi < w.im) (h2 : w.im ≤ Real.pi) (c : ℂ) :
    cexp w ^ c = cexp (w * c) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero w), Complex.log_exp h1 h2]

theorem analyticOnNhd_jacobiThetaSum : AnalyticOnNhd ℂ jacobiThetaSum {y : ℂ | 0 < y.re} :=
  DifferentiableOn.analyticOnNhd (fun _ hy => (hasDerivAt_jacobiThetaSum hy).differentiableAt
    |>.differentiableWithinAt) (isOpen_lt continuous_const Complex.continuous_re)

theorem differentiableAt_thetaBoundarySource {y : ℂ} (hy : 0 < y.re) :
    DifferentiableAt ℂ thetaBoundarySource y := by
  have h1 := (analyticOnNhd_jacobiThetaSum.deriv y hy).differentiableAt
  have h2 := (analyticOnNhd_jacobiThetaSum.deriv.deriv y hy).differentiableAt
  have h3 : DifferentiableAt ℂ (fun y : ℂ => y ^ (5 / 4 : ℂ)) y :=
    (Complex.hasStrictDerivAt_cpow_const (Or.inl hy)).hasDerivAt.differentiableAt
  unfold thetaBoundarySource
  exact h3.mul (((differentiableAt_const _).mul differentiableAt_id).mul h2 |>.add
    ((differentiableAt_const _).mul h1))

/-- The log-clock integrand `G_z(w) = e^{izw/2} κ(e^w)`. -/
def connectionLogIntegrand (z w : ℂ) : ℂ := cexp (I * z * w / 2) * thetaBoundarySource (cexp w)

/-- The rotated connection integrand `F_z(y) = y^{iz/2 - 1} κ(y)`. -/
def rotatedConnectionIntegrand (z y : ℂ) : ℂ := y ^ (I * z / 2 - 1) * thetaBoundarySource y

theorem cexp_mul_rotatedConnectionIntegrand (z : ℂ) {w : ℂ} (h1 : -Real.pi < w.im)
    (h2 : w.im ≤ Real.pi) :
    cexp w * rotatedConnectionIntegrand z (cexp w) = connectionLogIntegrand z w := by
  unfold rotatedConnectionIntegrand connectionLogIntegrand
  rw [cpow_cexp h1 h2, ← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

theorem re_cexp_ge {φ : ℝ} (hφ : φ < Real.pi / 2) {w : ℂ} (hre : 0 ≤ w.re) (him0 : 0 ≤ w.im)
    (him : w.im ≤ φ) : Real.cos φ ≤ (cexp w).re ∧ Real.cos φ * Real.exp w.re ≤ (cexp w).re := by
  have hc : Real.cos φ ≤ Real.cos w.im :=
    Real.cos_le_cos_of_nonneg_of_le_pi him0 (by linarith [Real.pi_pos]) him
  have hcpos : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hφ⟩
  have he : 1 ≤ Real.exp w.re := Real.one_le_exp hre
  rw [Complex.exp_re]
  constructor <;> nlinarith [Real.exp_pos w.re]

/-- Uniform decay of the log-clock integrand on the half-strip `Re w ≥ 0`, `0 ≤ Im w ≤ φ`. -/
theorem exists_norm_connectionLogIntegrand_le (z : ℂ) {φ : ℝ} (hφ0 : 0 ≤ φ) (hφ : φ < Real.pi / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, 0 ≤ w.re → 0 ≤ w.im → w.im ≤ φ →
      ‖connectionLogIntegrand z w‖ ≤ C * Real.exp (-w.re) := by
  have hcpos : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hφ⟩
  obtain ⟨C₁, hC₁, hb⟩ := exists_exp_mul_exp_neg_exp_le (|z.im| / 2 + 9 / 4)
    (by positivity : 0 < Real.pi / 2 * Real.cos φ)
  set S := boundarySourceSectorConstant (Real.cos φ)
  have hS : 0 ≤ S := tsum_nonneg fun n => by positivity
  refine ⟨2 * S * Real.exp (|z.re| * φ / 2) * C₁, by positivity, fun w hre him0 him => ?_⟩
  obtain ⟨hδ, hδ'⟩ := re_cexp_ge hφ hre him0 him
  have hκ := norm_thetaBoundarySource_le hcpos hδ
  rw [Complex.norm_exp] at hκ
  have hpow : Real.exp w.re ^ (5 / 4 : ℝ) = Real.exp (5 / 4 * w.re) := by
    rw [← Real.exp_mul]; ring_nf
  rw [hpow] at hκ
  have hphase : ‖cexp (I * z * w / 2)‖ ≤ Real.exp (|z.re| * φ / 2) * Real.exp (|z.im| / 2 * w.re) := by
    rw [Complex.norm_exp, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have : (I * z * w / 2).re = -(z.re * w.im + z.im * w.re) / 2 := by
      simp [Complex.mul_re, Complex.mul_im]; ring
    rw [this]
    have h1 : -(z.re * w.im) ≤ |z.re| * φ := by
      have := neg_abs_le z.re; nlinarith [abs_nonneg z.re]
    have h2 : -(z.im * w.re) ≤ |z.im| * w.re := by
      have := neg_abs_le z.im; nlinarith
    linarith
  have hexp1 : Real.exp w.re + 1 ≤ 2 * Real.exp w.re := by linarith [Real.one_le_exp hre]
  have hdecay : Real.exp (-(Real.pi / 2 * (cexp w).re)) ≤
      Real.exp (-(Real.pi / 2 * Real.cos φ * Real.exp w.re)) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  have hkey := hb w.re hre
  unfold connectionLogIntegrand
  rw [norm_mul]
  calc ‖cexp (I * z * w / 2)‖ * ‖thetaBoundarySource (cexp w)‖
      ≤ (Real.exp (|z.re| * φ / 2) * Real.exp (|z.im| / 2 * w.re)) *
          (S * Real.exp (5 / 4 * w.re) * (2 * Real.exp w.re) *
            Real.exp (-(Real.pi / 2 * Real.cos φ * Real.exp w.re))) := by
        refine mul_le_mul hphase (hκ.trans ?_) (norm_nonneg _) (by positivity)
        gcongr
    _ = 2 * S * Real.exp (|z.re| * φ / 2) * (Real.exp ((|z.im| / 2 + 9 / 4) * w.re) *
          Real.exp (-(Real.pi / 2 * Real.cos φ * Real.exp w.re))) := by
        rw [show (|z.im| / 2 + 9 / 4) * w.re = |z.im| / 2 * w.re + 5 / 4 * w.re + w.re by ring,
          Real.exp_add, Real.exp_add]
        ring
    _ ≤ 2 * S * Real.exp (|z.re| * φ / 2) * (C₁ * Real.exp (-w.re)) := by gcongr
    _ = 2 * S * Real.exp (|z.re| * φ / 2) * C₁ * Real.exp (-w.re) := by ring

theorem differentiableAt_connectionLogIntegrand (z : ℂ) {φ : ℝ} (hφ : φ < Real.pi / 2) {w : ℂ}
    (hre : 0 ≤ w.re) (him0 : 0 ≤ w.im) (him : w.im ≤ φ) :
    DifferentiableAt ℂ (connectionLogIntegrand z) w := by
  have hcpos : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hφ⟩
  have hpos : 0 < (cexp w).re := lt_of_lt_of_le hcpos (re_cexp_ge hφ hre him0 him).1
  have h := (differentiableAt_thetaBoundarySource hpos).comp w Complex.differentiableAt_exp
  unfold connectionLogIntegrand
  exact (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => cexp (I * z * w / 2)) w).mul h

theorem integrableOn_connectionLogIntegrand (z : ℂ) {φ : ℝ} (hφ0 : 0 ≤ φ) (hφ : φ < Real.pi / 2)
    {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ φ) :
    IntegrableOn (fun t : ℝ => connectionLogIntegrand z (t + s * I)) (Ioi 0) := by
  obtain ⟨C, hC, hb⟩ := exists_norm_connectionLogIntegrand_le z hφ0 hφ
  refine ((integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 0).const_mul C).mono' ?_
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_))
  · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
    have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
    have hw : 0 ≤ ((t : ℂ) + s * I).re := by simp [ht0]
    have hd := differentiableAt_connectionLogIntegrand z hφ hw (by simp [hs0]) (by simp [hs])
    exact (ContinuousAt.comp (g := connectionLogIntegrand z) (f := fun t : ℝ => (t : ℂ) + s * I)
      hd.continuousAt (by fun_prop)).continuousWithinAt
  · have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
    have := hb ((t : ℂ) + s * I) (by simp [ht0]) (by simp [hs0]) (by simp [hs])
    simpa [neg_mul, one_mul] using this

theorem image_exp_Ioi_zero : Real.exp '' Ioi 0 = Ioi 1 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩; exact Real.one_lt_exp_iff.mpr hx
  · intro hy
    have hy0 : (0 : ℝ) < y := lt_trans one_pos hy
    exact ⟨Real.log y, Real.log_pos hy, Real.exp_log hy0⟩

/-- Exponential substitution on the half-line: `∫₀^∞ e^t g(e^t) dt = ∫₁^∞ g(r) dr`. -/
theorem integral_Ioi_exp_smul_comp (g : ℝ → ℂ) :
    (∫ t in Ioi (0 : ℝ), Real.exp t • g (Real.exp t)) = ∫ r in Ioi (1 : ℝ), g r := by
  have h := integral_image_eq_integral_abs_deriv_smul (f := Real.exp) (f' := Real.exp)
    (s := Ioi 0) measurableSet_Ioi (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_injective.injOn g
  rw [image_exp_Ioi_zero] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [abs_of_pos (Real.exp_pos t)]

/-- **Rotated connection branch.** For `0 < φ < π/2`,
`H(z) = ½ (i ∫₀^φ e^{iθ} F_z(e^{iθ}) dθ + e^{iφ} ∫₁^∞ F_z(r e^{iφ}) dr)`,
`F_z(y) = y^{iz/2-1} κ(y)`. -/
theorem thetaOneSidedConnection_eq_rotated (z : ℂ) {φ : ℝ} (hφ0 : 0 < φ) (hφ : φ < Real.pi / 2) :
    thetaOneSidedConnection z = (1 / 2) *
      (I * (∫ θ in (0 : ℝ)..φ, cexp (θ * I) * rotatedConnectionIntegrand z (cexp (θ * I))) +
        cexp (φ * I) * ∫ r in Ioi (1 : ℝ), rotatedConnectionIntegrand z (r * cexp (φ * I))) := by
  obtain ⟨C, hC, hb⟩ := exists_norm_connectionLogIntegrand_le z hφ0.le hφ
  have hi0 : IntegrableOn (fun t : ℝ => connectionLogIntegrand z t) (Ioi 0) := by
    have := integrableOn_connectionLogIntegrand z hφ0.le hφ le_rfl hφ0.le (s := 0)
    simpa using this
  have hiφ := integrableOn_connectionLogIntegrand z hφ0.le hφ hφ0.le le_rfl
  have hdecay : Tendsto (fun L : ℝ => ∫ s in (0 : ℝ)..φ, connectionLogIntegrand z (L + s * I))
      atTop (𝓝 0) := by
    have hlim : Tendsto (fun L : ℝ => C * Real.exp (-L) * |φ - 0|) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul C).mul_const |φ - 0|
      simpa using this
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop 0] with L hL
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun s hs => ?_
    rw [Set.uIoc_of_le hφ0.le] at hs
    have := hb ((L : ℂ) + s * I) (by simp [hL]) (by simp [hs.1.le]) (by simp [hs.2])
    simpa using this
  have hrot := integral_Ioi_eq_rotated (f := connectionLogIntegrand z) hφ0.le
    (fun w hre him0 him => differentiableAt_connectionLogIntegrand z hφ hre him0 him) hi0 hiφ hdecay
  -- the real axis gives `2 H(z)`
  have hreal : (∫ t in Ioi (0 : ℝ), connectionLogIntegrand z t) = 2 * thetaOneSidedConnection z := by
    have hpt : ∀ t : ℝ, connectionLogIntegrand z t =
        (thetaCuspFullSource ((1 / 2) * t) : ℂ) * cexp (I * z * ((1 / 2 * t : ℝ) : ℂ)) := by
      intro t
      have hs : (((1 / 2) * t : ℝ) : ℂ) ∈ thetaCuspStrip := by
        show |(((1 / 2) * t : ℝ) : ℂ).im| < Real.pi / 4
        simp [Real.pi_pos]
      have hk := thetaCuspStripSource_eq_boundarySource hs
      rw [thetaCuspStripSource_ofReal] at hk
      unfold connectionLogIntegrand
      rw [show cexp (t : ℂ) = cexp (2 * (((1 / 2) * t : ℝ) : ℂ)) by push_cast; ring_nf, ← hk]
      push_cast; ring_nf
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => hpt t)]
    have h := integral_comp_mul_left_Ioi (fun u : ℝ => (thetaCuspFullSource u : ℂ) *
      cexp (I * z * u)) 0 (by norm_num : (0 : ℝ) < 1 / 2)
    simp only [mul_zero] at h
    rw [h, thetaOneSidedConnection]
    norm_num
  -- the rotated ray
  have hray : (∫ t in Ioi (0 : ℝ), connectionLogIntegrand z (t + φ * I)) =
      cexp (φ * I) * ∫ r in Ioi (1 : ℝ), rotatedConnectionIntegrand z (r * cexp (φ * I)) := by
    have hpt : ∀ t : ℝ, connectionLogIntegrand z (t + φ * I) =
        cexp (φ * I) * (Real.exp t • rotatedConnectionIntegrand z (Real.exp t * cexp (φ * I))) := by
      intro t
      have him : ((t : ℂ) + φ * I).im = φ := by simp
      rw [← cexp_mul_rotatedConnectionIntegrand z (by rw [him]; linarith [Real.pi_pos])
        (by rw [him]; linarith [Real.pi_pos]), Complex.exp_add, Complex.real_smul,
        Complex.ofReal_exp]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => hpt t), integral_const_mul,
      integral_Ioi_exp_smul_comp (fun r => rotatedConnectionIntegrand z (r * cexp (φ * I)))]
  -- the arc
  have harc : (∫ s in (0 : ℝ)..φ, connectionLogIntegrand z (s * I)) =
      ∫ θ in (0 : ℝ)..φ, cexp (θ * I) * rotatedConnectionIntegrand z (cexp (θ * I)) := by
    refine intervalIntegral.integral_congr fun θ hθ => ?_
    rw [Set.uIcc_of_le hφ0.le] at hθ
    have him : ((θ : ℂ) * I).im = θ := by simp
    exact (cexp_mul_rotatedConnectionIntegrand z (by rw [him]; linarith [hθ.1, Real.pi_pos])
      (by rw [him]; linarith [hθ.2, Real.pi_pos])).symm
  rw [hreal, hray, harc] at hrot
  linear_combination hrot / 2

end RHTower
