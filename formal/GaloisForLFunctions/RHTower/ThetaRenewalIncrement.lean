import GaloisForLFunctions.RHTower.ThetaQuadratureDefectSpectralKernel

/-!
# The positive renewal increment of the theta profile

With `a = 1/4`, `c = Θ(1)` and `P(t) = e^{t/4} Θ(e^t)`, the renewal increment
`ν(t) = aP(t) - P'(t) = 2π Σ_{n≥1} n² e^{5t/4 - πn² e^t}` is positive, `ν(0) = ac` (the seam slope
`P'(0)` vanishes because `P` is even), and it decays faster than every exponential.  Its Laplace
transform `N(s) = ∫₀^∞ e^{-st} ν(t) dt` is entire, `N(s) = (a - s) M_{2is} + c - 1` (integration by
parts against `R = P - e^{at}`, `ν = aR - R'`), and the renewal denominator `D = c - N` equals
`(s - a) L(s)` off the pole and satisfies the two-ended identity
`(a - iz) D(-iz) + (a + iz) D(iz) = Ξ(2z)` for all complex `z`.

The weighted density `v = e^{at} ν/c` satisfies `v(0) = a` and `v(t) ≤ a e^{-βt}` for `t ≥ 0`
(`β = π - 3/2`, termwise logarithmic derivatives), so the renewal mass `q = ∫₀^∞ v` obeys
`0 < q ≤ a/β < 1/6`; hence `|N(s)| ≤ cq` and `Re D(s) ≥ c(1 - q) > 0` on `Re s ≥ -a`.
-/
open Complex Filter Topology Set MeasureTheory HurwitzZeta

noncomputable section

namespace RHTower

local notation "Θ" => evenKernel (0 : UnitAddCircle)

/-! ## Superexponential decay of the theta moments -/

theorem thetaMoment_le_exp_neg (k : ℕ) {y : ℝ} (hy : 1 ≤ y) :
    thetaMoment k y ≤ thetaMoment k 1 * Real.exp Real.pi * Real.exp (-(Real.pi * y)) := by
  have hs1 := summable_thetaMoment_terms k (show (0 : ℝ) < 1 by norm_num)
  have hsy := summable_thetaMoment_terms k (show (0 : ℝ) < y by linarith)
  calc thetaMoment k y = ∑' n : ℕ, ((n : ℝ) + 1) ^ (2 * k) *
        Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 * y)) := rfl
    _ ≤ ∑' n : ℕ, ((n : ℝ) + 1) ^ (2 * k) * Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 * 1)) *
        (Real.exp Real.pi * Real.exp (-(Real.pi * y))) :=
        hsy.tsum_le_tsum (fun n => ?_) (hs1.mul_right (Real.exp Real.pi * Real.exp (-(Real.pi * y))))
    _ = thetaMoment k 1 * Real.exp Real.pi * Real.exp (-(Real.pi * y)) := by
        rw [tsum_mul_right, mul_assoc]; rfl
  have hn : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have key : Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 * y)) ≤
      Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 * 1)) *
        (Real.exp Real.pi * Real.exp (-(Real.pi * y))) := by
    rw [← Real.exp_add, ← Real.exp_add]
    have hprod : 0 ≤ Real.pi * ((((n : ℝ) + 1) ^ 2 - 1) * (y - 1)) :=
      mul_nonneg Real.pi_pos.le (mul_nonneg (sub_nonneg.2 hn) (sub_nonneg.2 hy))
    exact Real.exp_le_exp.mpr (by nlinarith)
  calc ((n : ℝ) + 1) ^ (2 * k) * Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 * y))
      ≤ ((n : ℝ) + 1) ^ (2 * k) * (Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 * 1)) *
        (Real.exp Real.pi * Real.exp (-(Real.pi * y)))) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = _ := by ring

/-- `α t - π t²/2 ≤ α²/(2π)`. -/
theorem mul_sub_sq_le (α t : ℝ) : α * t - Real.pi * t ^ 2 / 2 ≤ α ^ 2 / (2 * Real.pi) := by
  have hpi := Real.pi_pos
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (Real.pi * t - α)]

/-- `e^{κ t - π e^t} ≤ C e^{-t}` on `t ≥ 0` for every `κ`. -/
theorem exists_exp_sub_pi_exp_le (κ : ℝ) :
    ∃ C, 0 < C ∧ ∀ t, 0 ≤ t → Real.exp (κ * t - Real.pi * Real.exp t) ≤ C * Real.exp (-t) := by
  refine ⟨Real.exp (-Real.pi + (κ + 1 - Real.pi) ^ 2 / (2 * Real.pi)), Real.exp_pos _, fun t ht => ?_⟩
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have h1 := Real.quadratic_le_exp_of_nonneg ht
  have h2 := mul_sub_sq_le (κ + 1 - Real.pi) t
  have hpi := Real.pi_pos
  nlinarith

/-! ## The renewal increment -/

/-- The renewal increment `ν(t) = aP(t) - P'(t) = 2π Σ_{n≥1} n² e^{5t/4 - πn²e^t}` (`a = 1/4`). -/
def thetaRenewalIncrement (t : ℝ) : ℝ := 2 * Real.pi * Real.exp (5 / 4 * t) * thetaMoment 1 (Real.exp t)

theorem thetaRenewalIncrement_pos (t : ℝ) : 0 < thetaRenewalIncrement t :=
  mul_pos (by positivity) (thetaMoment_pos 1 (Real.exp_pos t))

theorem continuous_thetaMoment_comp_exp (k : ℕ) : Continuous fun t => thetaMoment k (Real.exp t) :=
  continuous_iff_continuousAt.2 fun t =>
    ((hasDerivAt_thetaMoment k (Real.exp_pos t)).continuousAt).comp Real.continuous_exp.continuousAt

theorem continuous_thetaRenewalIncrement : Continuous thetaRenewalIncrement := by
  have := continuous_thetaMoment_comp_exp 1
  unfold thetaRenewalIncrement
  fun_prop

/-- `P'(t) = P(t)/4 - ν(t)`. -/
theorem hasDerivAt_thetaLogProfile (t : ℝ) :
    HasDerivAt thetaLogProfile (thetaLogProfile t / 4 - thetaRenewalIncrement t) t := by
  have h1 : HasDerivAt (fun t => Real.exp (t / 4)) (Real.exp (t / 4) * (1 / 4)) t :=
    ((hasDerivAt_id t).div_const 4).exp.congr_deriv (by simp [id])
  have h2 : HasDerivAt (fun t => Θ (Real.exp t))
      (-(2 * Real.pi * thetaMoment 1 (Real.exp t)) * Real.exp t) t :=
    (hasDerivAt_evenKernel_zero (Real.exp_pos t)).comp t (Real.hasDerivAt_exp t)
  refine (h1.mul h2).congr_deriv ?_
  rw [thetaLogProfile, thetaRenewalIncrement,
    show Real.exp (5 / 4 * t) = Real.exp (t / 4) * Real.exp t by rw [← Real.exp_add]; ring_nf]
  ring

/-- `R'(t) = R(t)/4 - ν(t)`, so `ν = aR - R'`. -/
theorem hasDerivAt_thetaLogTail (t : ℝ) :
    HasDerivAt thetaLogTail (thetaLogTail t / 4 - thetaRenewalIncrement t) t := by
  have h1 : HasDerivAt (fun t => Real.exp (t / 4)) (Real.exp (t / 4) * (1 / 4)) t :=
    ((hasDerivAt_id t).div_const 4).exp.congr_deriv (by simp [id])
  have h := (hasDerivAt_thetaLogProfile t).sub h1
  have hfun : thetaLogTail = thetaLogProfile - fun t => Real.exp (t / 4) := by
    funext s; simp only [Pi.sub_apply]; rw [thetaLogProfile_eq_add]; ring
  have h2 : HasDerivAt (thetaLogProfile - fun t => Real.exp (t / 4))
      (thetaLogTail t / 4 - thetaRenewalIncrement t) t :=
    h.congr_deriv (by rw [thetaLogProfile_eq_add]; ring)
  rwa [← hfun] at h2

/-- The seam slope vanishes: `P'(0) = 0`, hence `ν(0) = a c`. -/
theorem thetaRenewalIncrement_zero : thetaRenewalIncrement 0 = Θ 1 / 4 := by
  have hd := hasDerivAt_thetaLogProfile 0
  have hdn := (hasDerivAt_thetaLogProfile (-0)).comp 0 (hasDerivAt_neg 0)
  have heq : thetaLogProfile ∘ Neg.neg = thetaLogProfile := funext fun t => thetaLogProfile_neg t
  rw [heq, neg_zero] at hdn
  have h0 := hd.unique hdn
  have hP0 : thetaLogProfile 0 = Θ 1 := by simp [thetaLogProfile]
  rw [hP0] at h0
  linarith

/-- `ν(t) ≤ C e^{5t/4 - π e^t}` on `t ≥ 0`. -/
theorem thetaRenewalIncrement_le {t : ℝ} (ht : 0 ≤ t) :
    thetaRenewalIncrement t ≤ 2 * Real.pi * thetaMoment 1 1 * Real.exp Real.pi *
      Real.exp (5 / 4 * t - Real.pi * Real.exp t) := by
  rw [thetaRenewalIncrement]
  have h := thetaMoment_le_exp_neg 1 (Real.one_le_exp ht)
  calc 2 * Real.pi * Real.exp (5 / 4 * t) * thetaMoment 1 (Real.exp t)
      ≤ 2 * Real.pi * Real.exp (5 / 4 * t) *
        (thetaMoment 1 1 * Real.exp Real.pi * Real.exp (-(Real.pi * Real.exp t))) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by rw [show 5 / 4 * t - Real.pi * Real.exp t = 5 / 4 * t + -(Real.pi * Real.exp t) by
          ring, Real.exp_add]; ring

/-- Every exponential moment of `ν` on `t ≥ 0` is finite: `e^{Kt} ν(t) ≤ C e^{-t}`. -/
theorem exists_exp_mul_thetaRenewalIncrement_le (K : ℝ) :
    ∃ C, 0 < C ∧ ∀ t, 0 ≤ t → Real.exp (K * t) * thetaRenewalIncrement t ≤ C * Real.exp (-t) := by
  obtain ⟨C, hC, hle⟩ := exists_exp_sub_pi_exp_le (K + 5 / 4)
  have hM := thetaMoment_pos 1 (show (0 : ℝ) < 1 by norm_num)
  refine ⟨2 * Real.pi * thetaMoment 1 1 * Real.exp Real.pi * C, by positivity, fun t ht => ?_⟩
  calc Real.exp (K * t) * thetaRenewalIncrement t ≤ Real.exp (K * t) *
        (2 * Real.pi * thetaMoment 1 1 * Real.exp Real.pi *
          Real.exp (5 / 4 * t - Real.pi * Real.exp t)) :=
        mul_le_mul_of_nonneg_left (thetaRenewalIncrement_le ht) (Real.exp_pos _).le
    _ = 2 * Real.pi * thetaMoment 1 1 * Real.exp Real.pi *
          Real.exp ((K + 5 / 4) * t - Real.pi * Real.exp t) := by
        rw [mul_left_comm, ← Real.exp_add]; ring_nf
    _ ≤ 2 * Real.pi * thetaMoment 1 1 * Real.exp Real.pi * (C * Real.exp (-t)) :=
        mul_le_mul_of_nonneg_left (hle t ht) (by positivity)
    _ = _ := by ring

theorem thetaLogTail_le_exp_sub {t : ℝ} (ht : 0 ≤ t) :
    thetaLogTail t ≤ 2 * thetaMoment 0 1 * Real.exp Real.pi *
      Real.exp (1 / 4 * t - Real.pi * Real.exp t) := by
  rw [thetaLogTail, evenKernel_zero_eq_thetaMoment (Real.exp_pos t)]
  have h := thetaMoment_le_exp_neg 0 (Real.one_le_exp ht)
  calc Real.exp (t / 4) * (1 + 2 * thetaMoment 0 (Real.exp t) - 1)
      = 2 * Real.exp (t / 4) * thetaMoment 0 (Real.exp t) := by ring
    _ ≤ 2 * Real.exp (t / 4) * (thetaMoment 0 1 * Real.exp Real.pi *
          Real.exp (-(Real.pi * Real.exp t))) := mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by rw [show 1 / 4 * t - Real.pi * Real.exp t = t / 4 + -(Real.pi * Real.exp t) by
          ring, Real.exp_add]; ring

theorem exists_exp_mul_thetaLogTail_le (K : ℝ) :
    ∃ C, 0 < C ∧ ∀ t, 0 ≤ t → Real.exp (K * t) * thetaLogTail t ≤ C * Real.exp (-t) := by
  obtain ⟨C, hC, hle⟩ := exists_exp_sub_pi_exp_le (K + 1 / 4)
  have hM := thetaMoment_pos 0 (show (0 : ℝ) < 1 by norm_num)
  refine ⟨2 * thetaMoment 0 1 * Real.exp Real.pi * C, by positivity, fun t ht => ?_⟩
  calc Real.exp (K * t) * thetaLogTail t ≤ Real.exp (K * t) *
        (2 * thetaMoment 0 1 * Real.exp Real.pi * Real.exp (1 / 4 * t - Real.pi * Real.exp t)) :=
        mul_le_mul_of_nonneg_left (thetaLogTail_le_exp_sub ht) (Real.exp_pos _).le
    _ = 2 * thetaMoment 0 1 * Real.exp Real.pi *
          Real.exp ((K + 1 / 4) * t - Real.pi * Real.exp t) := by
        rw [mul_left_comm, ← Real.exp_add]; ring_nf
    _ ≤ 2 * thetaMoment 0 1 * Real.exp Real.pi * (C * Real.exp (-t)) :=
        mul_le_mul_of_nonneg_left (hle t ht) (by positivity)
    _ = _ := by ring

/-! ## The entire Laplace transform of the increment and the renewal denominator -/

theorem integrableOn_cexp_mul_of_superexp {f : ℝ → ℝ} (hf : Continuous f)
    (hbound : ∀ K : ℝ, ∃ C, 0 < C ∧ ∀ t, 0 ≤ t → Real.exp (K * t) * |f t| ≤ C * Real.exp (-t))
    (s : ℂ) : IntegrableOn (fun t : ℝ => cexp (-(s * t)) * (f t : ℂ)) (Ioi 0) := by
  obtain ⟨C, hC, hle⟩ := hbound (-s.re)
  have hdom : IntegrableOn (fun t : ℝ => C * Real.exp ((-1) * t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by norm_num) 0).const_mul C
  refine hdom.mono' ((by fun_prop : Continuous fun t : ℝ => cexp (-(s * t)) * (f t : ℂ))
    |>.aestronglyMeasurable) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
  have hre : (-(s * (t : ℂ))).re = -s.re * t := by simp
  rw [hre, neg_one_mul]
  exact hle t (le_of_lt ht)

theorem thetaRenewalIncrement_superexp (K : ℝ) :
    ∃ C, 0 < C ∧ ∀ t, 0 ≤ t → Real.exp (K * t) * |thetaRenewalIncrement t| ≤ C * Real.exp (-t) := by
  obtain ⟨C, hC, h⟩ := exists_exp_mul_thetaRenewalIncrement_le K
  exact ⟨C, hC, fun t ht => by rw [abs_of_pos (thetaRenewalIncrement_pos t)]; exact h t ht⟩

theorem thetaLogTail_superexp (K : ℝ) :
    ∃ C, 0 < C ∧ ∀ t, 0 ≤ t → Real.exp (K * t) * |thetaLogTail t| ≤ C * Real.exp (-t) := by
  obtain ⟨C, hC, h⟩ := exists_exp_mul_thetaLogTail_le K
  exact ⟨C, hC, fun t ht => by rw [abs_of_pos (thetaLogTail_pos t)]; exact h t ht⟩

/-- The Laplace transform `N(s) = ∫₀^∞ e^{-st} ν(t) dt`, entire in `s`. -/
def thetaRenewalLaplace (s : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), cexp (-(s * t)) * (thetaRenewalIncrement t : ℂ)

/-- `N(s) = (1/4 - s) M_{2is} + c - 1` for every complex `s`. -/
theorem thetaRenewalLaplace_eq (s : ℂ) :
    thetaRenewalLaplace s = (1 / 4 - s) * wardMellin (2 * I * s) + ((Θ 1 : ℝ) - 1 : ℂ) := by
  have hR := integrableOn_cexp_mul_of_superexp continuous_thetaLogTail thetaLogTail_superexp s
  have hν := integrableOn_cexp_mul_of_superexp continuous_thetaRenewalIncrement
    thetaRenewalIncrement_superexp s
  -- integration by parts against `R`
  have hu : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun t : ℝ => cexp (-(s * t))) (-s * cexp (-(s * x))) x := by
    intro x _
    have := ((hasDerivAt_id (x : ℂ)).const_mul s).neg.cexp.comp_ofReal
    refine this.congr_deriv ?_
    simp only [id, Pi.neg_apply]; ring
  have hv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun t : ℝ => (thetaLogTail t : ℂ))
      ((thetaLogTail x / 4 - thetaRenewalIncrement x : ℝ) : ℂ) x :=
    fun x _ => (hasDerivAt_thetaLogTail x).ofReal_comp
  have huvL : IntegrableOn (fun t : ℝ => cexp (-(s * t)) *
      ((thetaLogTail t / 4 - thetaRenewalIncrement t : ℝ) : ℂ)) (Ioi 0) := by
    refine IntegrableOn.congr_fun ((hR.const_mul (1 / 4)).sub hν) (fun t _ => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply]; push_cast; ring
  have huv' : IntegrableOn ((fun t : ℝ => cexp (-(s * t))) *
      fun t => ((thetaLogTail t / 4 - thetaRenewalIncrement t : ℝ) : ℂ)) (Ioi 0) := huvL
  have hu'v : IntegrableOn ((fun t : ℝ => -s * cexp (-(s * t))) *
      fun t => (thetaLogTail t : ℂ)) (Ioi 0) := by
    refine IntegrableOn.congr_fun (hR.const_mul (-s)) (fun t _ => ?_) measurableSet_Ioi
    simp only [Pi.mul_apply]; ring
  have hzero : Tendsto ((fun t : ℝ => cexp (-(s * t))) * fun t => (thetaLogTail t : ℂ))
      (𝓝[>] 0) (𝓝 ((thetaLogTail 0 : ℝ) : ℂ)) := by
    have hc : Continuous ((fun t : ℝ => cexp (-(s * t))) * fun t => (thetaLogTail t : ℂ)) := by
      have := continuous_thetaLogTail
      exact (by fun_prop : Continuous fun t : ℝ => cexp (-(s * t))).mul (by fun_prop)
    have := hc.tendsto 0
    simp only [Pi.mul_apply, Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero,
      one_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hinf : Tendsto ((fun t : ℝ => cexp (-(s * t))) * fun t => (thetaLogTail t : ℂ))
      atTop (𝓝 0) := by
    obtain ⟨C, hC, hle⟩ := thetaLogTail_superexp (-s.re)
    refine squeeze_zero_norm' ?_ ((Real.tendsto_exp_neg_atTop_nhds_zero).const_mul C |>.congr
      (fun t => rfl) |> fun h => by simpa using h)
    filter_upwards [eventually_ge_atTop 0] with t ht
    rw [Pi.mul_apply, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
    have hre : (-(s * (t : ℂ))).re = -s.re * t := by simp
    rw [hre]
    exact hle t ht
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v hzero hinf
  have hM := integral_cexp_mul_thetaLogTail s
  have hsplit : thetaRenewalLaplace s = (1 / 4 : ℂ) * (∫ t in Ioi (0 : ℝ),
      cexp (-(s * t)) * (thetaLogTail t : ℂ)) - ∫ t in Ioi (0 : ℝ), cexp (-(s * t)) *
        ((thetaLogTail t / 4 - thetaRenewalIncrement t : ℝ) : ℂ) := by
    rw [thetaRenewalLaplace, ← integral_const_mul, ← integral_sub (hR.const_mul _) huvL]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    push_cast; ring
  rw [hsplit, hibp, hM]
  have hR0 : thetaLogTail 0 = Θ 1 - 1 := by simp [thetaLogTail]
  have hint : (∫ t in Ioi (0 : ℝ), -s * cexp (-(s * t)) * (thetaLogTail t : ℂ)) =
      -s * wardMellin (2 * I * s) := by
    rw [← hM, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    ring
  rw [hint, hR0]
  push_cast
  ring

/-- The renewal denominator `D(s) = c - N(s)`. -/
def thetaRenewalDenominator (s : ℂ) : ℂ := ((Θ 1 : ℝ) : ℂ) - thetaRenewalLaplace s

theorem thetaRenewalDenominator_eq (s : ℂ) :
    thetaRenewalDenominator s = 1 + (s - 1 / 4) * wardMellin (2 * I * s) := by
  rw [thetaRenewalDenominator, thetaRenewalLaplace_eq]; ring

/-- `D(s) = (s - 1/4) L(s)` off the pole. -/
theorem thetaRenewalDenominator_eq_laplace {s : ℂ} (hs : s ≠ 1 / 4) :
    thetaRenewalDenominator s = (s - 1 / 4) * thetaLogLaplaceC s := by
  have hne : s - 1 / 4 ≠ 0 := sub_ne_zero.mpr hs
  rw [thetaRenewalDenominator_eq, thetaLogLaplaceC, mul_add, mul_one_div_cancel hne]

/-- **The two-ended renewal identity.** `(a - iz) D(-iz) + (a + iz) D(iz) = Ξ(2z)` for all `z`. -/
theorem thetaRenewal_two_ended (z : ℂ) :
    (1 / 4 - I * z) * thetaRenewalDenominator (-(I * z)) +
      (1 / 4 + I * z) * thetaRenewalDenominator (I * z) = XiC (2 * z) := by
  rw [thetaRenewalDenominator_eq, thetaRenewalDenominator_eq, XiC_eq_wardMellin,
    show 2 * I * -(I * z) = 2 * z by linear_combination (-2 * z) * I_sq,
    show 2 * I * (I * z) = -(2 * z) by linear_combination (2 * z) * I_sq]
  linear_combination (z ^ 2 * wardMellin (2 * z) + z ^ 2 * wardMellin (-(2 * z))) * I_sq

/-! ## The subcritical renewal mass -/

/-- The weighted increment `v(t) = e^{t/4} ν(t)/c`. -/
def thetaRenewalDensity (t : ℝ) : ℝ := Real.exp (t / 4) * thetaRenewalIncrement t / Θ 1

theorem thetaRenewalDensity_zero : thetaRenewalDensity 0 = 1 / 4 := by
  have hc : 0 < Θ 1 := lt_trans one_pos (one_lt_evenKernel_zero one_pos)
  rw [thetaRenewalDensity, thetaRenewalIncrement_zero]; simp; field_simp

theorem thetaRenewalDensity_pos (t : ℝ) : 0 < thetaRenewalDensity t := by
  have hc : 0 < Θ 1 := lt_trans one_pos (one_lt_evenKernel_zero one_pos)
  exact div_pos (mul_pos (Real.exp_pos _) (thetaRenewalIncrement_pos t)) hc

/-- `v(t) ≤ (1/4) e^{-βt}` on `t ≥ 0`, with `β = π - 3/2`. -/
theorem thetaRenewalDensity_le {t : ℝ} (ht : 0 ≤ t) :
    thetaRenewalDensity t ≤ 1 / 4 * Real.exp (-((Real.pi - 3 / 2) * t)) := by
  have hc : 0 < Θ 1 := lt_trans one_pos (one_lt_evenKernel_zero one_pos)
  have hs1 := summable_thetaMoment_terms 1 (show (0 : ℝ) < 1 by norm_num)
  have hst := summable_thetaMoment_terms 1 (Real.exp_pos t)
  have hkey : Real.exp (3 / 2 * t) * thetaMoment 1 (Real.exp t) ≤
      thetaMoment 1 1 * Real.exp (-((Real.pi - 3 / 2) * t)) := by
    rw [thetaMoment, thetaMoment, ← tsum_mul_left, ← tsum_mul_right]
    refine (hst.mul_left _).tsum_le_tsum (fun n => ?_) (hs1.mul_right _)
    have hn : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    have hexp := Real.add_one_le_exp t
    have key : Real.exp (3 / 2 * t) * Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp t)) ≤
        Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 * 1)) * Real.exp (-((Real.pi - 3 / 2) * t)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have hprod : 0 ≤ Real.pi * ((((n : ℝ) + 1) ^ 2 - 1) * (Real.exp t - 1 - t) +
          (((n : ℝ) + 1) ^ 2 - 1) * t) :=
        mul_nonneg Real.pi_pos.le (add_nonneg (mul_nonneg (sub_nonneg.2 hn) (by linarith))
          (mul_nonneg (sub_nonneg.2 hn) ht))
      nlinarith [Real.pi_pos]
    calc Real.exp (3 / 2 * t) * (((n : ℝ) + 1) ^ (2 * 1) *
          Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp t)))
        = ((n : ℝ) + 1) ^ (2 * 1) * (Real.exp (3 / 2 * t) *
          Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp t))) := by ring
      _ ≤ ((n : ℝ) + 1) ^ (2 * 1) * (Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 * 1)) *
          Real.exp (-((Real.pi - 3 / 2) * t))) := mul_le_mul_of_nonneg_left key (by positivity)
      _ = _ := by ring
  have hv0 : thetaRenewalDensity 0 = 2 * Real.pi * thetaMoment 1 1 / Θ 1 := by
    simp [thetaRenewalDensity, thetaRenewalIncrement]
  rw [thetaRenewalDensity_zero] at hv0
  calc thetaRenewalDensity t = 2 * Real.pi / Θ 1 * (Real.exp (3 / 2 * t) *
        thetaMoment 1 (Real.exp t)) := by
        rw [thetaRenewalDensity, thetaRenewalIncrement,
          show Real.exp (3 / 2 * t) = Real.exp (t / 4) * Real.exp (5 / 4 * t) by
            rw [← Real.exp_add]; ring_nf]
        field_simp
    _ ≤ 2 * Real.pi / Θ 1 * (thetaMoment 1 1 * Real.exp (-((Real.pi - 3 / 2) * t))) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = 2 * Real.pi * thetaMoment 1 1 / Θ 1 * Real.exp (-((Real.pi - 3 / 2) * t)) := by ring
    _ = _ := by rw [← hv0]

/-- The weighted renewal mass `q = ∫₀^∞ v`. -/
def thetaRenewalMass : ℝ := ∫ t in Ioi (0 : ℝ), thetaRenewalDensity t

theorem continuous_thetaRenewalDensity : Continuous thetaRenewalDensity := by
  have := continuous_thetaRenewalIncrement
  unfold thetaRenewalDensity
  fun_prop

theorem integrableOn_thetaRenewalDensity : IntegrableOn thetaRenewalDensity (Ioi 0) := by
  have hdom : IntegrableOn (fun t : ℝ => 1 / 4 * Real.exp ((-(Real.pi - 3 / 2)) * t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith [Real.pi_gt_three]) 0).const_mul _
  refine hdom.mono' continuous_thetaRenewalDensity.aestronglyMeasurable.restrict ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (thetaRenewalDensity_pos t), neg_mul]
  exact thetaRenewalDensity_le (le_of_lt ht)

theorem thetaRenewalMass_pos : 0 < thetaRenewalMass :=
  setIntegral_Ioi_pos integrableOn_thetaRenewalDensity fun t _ => thetaRenewalDensity_pos t

/-- **Subcritical mass.** `q ≤ a/β < 1/6`. -/
theorem thetaRenewalMass_lt : thetaRenewalMass < 1 / 6 := by
  have hβ : 0 < Real.pi - 3 / 2 := by linarith [Real.pi_gt_three]
  have hle : thetaRenewalMass ≤ ∫ t in Ioi (0 : ℝ), 1 / 4 * Real.exp ((-(Real.pi - 3 / 2)) * t) :=
    setIntegral_mono_on integrableOn_thetaRenewalDensity
      ((integrableOn_exp_mul_Ioi (by linarith) 0).const_mul _) measurableSet_Ioi fun t ht => by
        rw [neg_mul]; exact thetaRenewalDensity_le (le_of_lt ht)
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) 0] at hle
  simp only [mul_zero, Real.exp_zero] at hle
  have : 1 / 4 * (-1 / -(Real.pi - 3 / 2)) < 1 / 6 := by
    rw [neg_div_neg_eq, mul_one_div, div_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [Real.pi_gt_three]
  linarith

theorem thetaSeam_pos : 0 < Θ 1 := lt_trans one_pos (one_lt_evenKernel_zero one_pos)

/-- `|N(s)| ≤ c q` on `Re s ≥ -1/4`. -/
theorem norm_thetaRenewalLaplace_le {s : ℂ} (hs : -(1 / 4) ≤ s.re) :
    ‖thetaRenewalLaplace s‖ ≤ Θ 1 * thetaRenewalMass := by
  rw [thetaRenewalLaplace]
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [thetaRenewalMass, ← integral_const_mul]
  refine setIntegral_mono_on (integrableOn_cexp_mul_of_superexp continuous_thetaRenewalIncrement
    thetaRenewalIncrement_superexp s).norm (integrableOn_thetaRenewalDensity.const_mul _)
    measurableSet_Ioi fun t ht => ?_
  have ht0 : (0 : ℝ) < t := ht
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (thetaRenewalIncrement_pos t), thetaRenewalDensity]
  have hre : (-(s * (t : ℂ))).re = -s.re * t := by simp
  rw [hre, mul_div_assoc', mul_div_cancel_left₀ _ thetaSeam_pos.ne']
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith))
    (thetaRenewalIncrement_pos t).le

/-- The denominator has real part at least `c(1 - q) > 0`, hence no zeros, on `Re s ≥ -1/4`. -/
theorem re_thetaRenewalDenominator_ge {s : ℂ} (hs : -(1 / 4) ≤ s.re) :
    Θ 1 * (1 - thetaRenewalMass) ≤ (thetaRenewalDenominator s).re := by
  have h := norm_thetaRenewalLaplace_le hs
  have hre := Complex.re_le_norm (thetaRenewalLaplace s)
  rw [thetaRenewalDenominator, Complex.sub_re, Complex.ofReal_re]
  nlinarith

theorem thetaRenewalDenominator_ne_zero {s : ℂ} (hs : -(1 / 4) ≤ s.re) :
    thetaRenewalDenominator s ≠ 0 := by
  intro h0
  have := re_thetaRenewalDenominator_ge hs
  rw [h0, Complex.zero_re] at this
  have := mul_pos thetaSeam_pos (sub_pos.2 (thetaRenewalMass_lt.trans (by norm_num : (1 : ℝ) / 6 < 1)))
  linarith

end RHTower
