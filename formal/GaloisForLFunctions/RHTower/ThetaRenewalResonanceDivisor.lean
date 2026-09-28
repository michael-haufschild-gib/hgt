import GaloisForLFunctions.RHTower.ThetaRenewalDenominatorOrder
import GaloisForLFunctions.RHTower.OrderOneHadamardFactorization
import GaloisForLFunctions.RHTower.CanonicalProductE1LogDeriv

/-!
# The resonance divisor of the renewal denominator

`D(z) = c - N(z)` is entire of order one with `D(0) > 0`.

* **Uniform decay.** Integrating by parts, `z N(z) = ν(0) + ∫₀^∞ e^{-zt} ν'(t) dt`, so on
  `Re z ≥ -B`: `‖z‖ ‖N(z)‖ ≤ ν(0) + ∫₀^∞ e^{Bt} |ν'(t)| dt`.  Hence every zero with `Re ζ ≥ -B`
  lies in a fixed disc: only finitely many zeros satisfy `Re ζ ≥ -B`, and every enumeration of the
  divisor has `Re ζ → -∞`.  All zeros satisfy `Re ζ < -1/4`.
* **(5d).** The genus-one Hadamard theorem gives `D(z) = D(0) e^{βz} ∏ (1 - z/ζ) e^{z/ζ}` with
  `β = D'(0)/D(0) = ∫ tν / (c - N(0)) > 0` and `∑ |ζ|⁻² < ∞`; the product has vanishing derivative
  at `0`, which fixes `β`.  Off the zeros, `D'/D = β + ∑ ((z - ζ)⁻¹ + ζ⁻¹)`.
* **Infinitely many resonances.** A finite divisor would make the product, hence `D`, of finite
  exponential type, contradicting `log M_D(R) ≥ R log R - O(R)`.  Exactly one zero is real, so
  infinitely many zeros are nonreal.
-/

open Complex Filter Topology Set MeasureTheory HurwitzZeta
open GaloisForLFunctions.EntireZeroDivisor

namespace RHTower

noncomputable section

local notation "Θ" => evenKernel (0 : UnitAddCircle)

/-! ## The derivative of the increment -/

/-- `ν'(t) = 2π (5/4 e^{5t/4} M₁(e^t) - π e^{9t/4} M₂(e^t))`. -/
def thetaRenewalIncrementDeriv (t : ℝ) : ℝ :=
  2 * Real.pi * (5 / 4 * Real.exp (5 / 4 * t) * thetaMoment 1 (Real.exp t) -
    Real.pi * Real.exp (9 / 4 * t) * thetaMoment 2 (Real.exp t))

theorem hasDerivAt_thetaRenewalIncrement (t : ℝ) :
    HasDerivAt thetaRenewalIncrement (thetaRenewalIncrementDeriv t) t := by
  have h1 : HasDerivAt (fun t : ℝ => Real.exp (5 / 4 * t)) (Real.exp (5 / 4 * t) * (5 / 4)) t :=
    (hasDerivAt_id t |>.const_mul (5 / 4) |>.exp).congr_deriv (by simp)
  have h2 : HasDerivAt (fun t : ℝ => thetaMoment 1 (Real.exp t))
      (-(Real.pi * thetaMoment 2 (Real.exp t)) * Real.exp t) t :=
    (hasDerivAt_thetaMoment 1 (Real.exp_pos t)).comp t (Real.hasDerivAt_exp t)
  have h := (h1.mul h2).const_mul (2 * Real.pi)
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  · rw [thetaRenewalIncrementDeriv, show 9 / 4 * t = 5 / 4 * t + t by ring, Real.exp_add]; ring
  · simp only [thetaRenewalIncrement, Pi.mul_apply]; ring

theorem continuous_thetaRenewalIncrementDeriv : Continuous thetaRenewalIncrementDeriv := by
  have h1 := continuous_thetaMoment_comp_exp 1
  have h2 := continuous_thetaMoment_comp_exp 2
  unfold thetaRenewalIncrementDeriv; fun_prop

/-- Every exponential moment of `|ν'|` is finite: `e^{Kt} |ν'(t)| ≤ C e^{-t}` on `t ≥ 0`. -/
theorem exists_exp_mul_abs_thetaRenewalIncrementDeriv_le (K : ℝ) :
    ∃ C, 0 < C ∧ ∀ t, 0 ≤ t → Real.exp (K * t) * |thetaRenewalIncrementDeriv t| ≤
      C * Real.exp (-t) := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_exp_sub_pi_exp_le (K + 5 / 4)
  obtain ⟨C₂, hC₂, h₂⟩ := exists_exp_sub_pi_exp_le (K + 9 / 4)
  have hM1 := thetaMoment_pos 1 (show (0 : ℝ) < 1 by norm_num)
  have hM2 := thetaMoment_pos 2 (show (0 : ℝ) < 1 by norm_num)
  refine ⟨2 * Real.pi * (5 / 4 * thetaMoment 1 1 * Real.exp Real.pi * C₁ +
    Real.pi * thetaMoment 2 1 * Real.exp Real.pi * C₂), by positivity, fun t ht => ?_⟩
  have hm1 := thetaMoment_le_exp_neg 1 (Real.one_le_exp ht)
  have hm2 := thetaMoment_le_exp_neg 2 (Real.one_le_exp ht)
  have hp1 := (thetaMoment_pos 1 (Real.exp_pos t)).le
  have hp2 := (thetaMoment_pos 2 (Real.exp_pos t)).le
  have habs : |thetaRenewalIncrementDeriv t| ≤ 2 * Real.pi *
      (5 / 4 * Real.exp (5 / 4 * t) * thetaMoment 1 (Real.exp t) +
        Real.pi * Real.exp (9 / 4 * t) * thetaMoment 2 (Real.exp t)) := by
    rw [thetaRenewalIncrementDeriv, abs_mul, abs_of_pos (by positivity)]
    gcongr
    refine (abs_sub _ _).trans (le_of_eq ?_)
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  have e1 : Real.exp (K * t) * Real.exp (5 / 4 * t) * Real.exp (-(Real.pi * Real.exp t)) =
      Real.exp ((K + 5 / 4) * t - Real.pi * Real.exp t) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have e2 : Real.exp (K * t) * Real.exp (9 / 4 * t) * Real.exp (-(Real.pi * Real.exp t)) =
      Real.exp ((K + 9 / 4) * t - Real.pi * Real.exp t) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have hk1 := h₁ t ht
  have hk2 := h₂ t ht
  calc Real.exp (K * t) * |thetaRenewalIncrementDeriv t|
      ≤ Real.exp (K * t) * (2 * Real.pi *
          (5 / 4 * Real.exp (5 / 4 * t) * thetaMoment 1 (Real.exp t) +
            Real.pi * Real.exp (9 / 4 * t) * thetaMoment 2 (Real.exp t))) :=
        mul_le_mul_of_nonneg_left habs (Real.exp_pos _).le
    _ ≤ Real.exp (K * t) * (2 * Real.pi *
          (5 / 4 * Real.exp (5 / 4 * t) * (thetaMoment 1 1 * Real.exp Real.pi *
              Real.exp (-(Real.pi * Real.exp t))) +
            Real.pi * Real.exp (9 / 4 * t) * (thetaMoment 2 1 * Real.exp Real.pi *
              Real.exp (-(Real.pi * Real.exp t))))) := by gcongr
    _ = 2 * Real.pi * (5 / 4 * thetaMoment 1 1 * Real.exp Real.pi *
          (Real.exp (K * t) * Real.exp (5 / 4 * t) * Real.exp (-(Real.pi * Real.exp t))) +
        Real.pi * thetaMoment 2 1 * Real.exp Real.pi *
          (Real.exp (K * t) * Real.exp (9 / 4 * t) * Real.exp (-(Real.pi * Real.exp t)))) := by
        ring
    _ ≤ 2 * Real.pi * (5 / 4 * thetaMoment 1 1 * Real.exp Real.pi * (C₁ * Real.exp (-t)) +
        Real.pi * thetaMoment 2 1 * Real.exp Real.pi * (C₂ * Real.exp (-t))) := by
        rw [e1, e2]; gcongr
    _ = _ := by ring

theorem integrableOn_exp_mul_abs_thetaRenewalIncrementDeriv (K : ℝ) :
    IntegrableOn (fun t => Real.exp (K * t) * |thetaRenewalIncrementDeriv t|) (Ioi 0) := by
  obtain ⟨C, hC, hle⟩ := exists_exp_mul_abs_thetaRenewalIncrementDeriv_le K
  refine ((integrableOn_exp_mul_Ioi (a := -1) (by norm_num) 0).const_mul C).mono'
    (by have := continuous_thetaRenewalIncrementDeriv; fun_prop) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  rw [Real.norm_of_nonneg (by positivity), neg_one_mul]
  exact hle t (le_of_lt ht)

/-! ## Uniform decay of `N` on right half-planes -/

theorem integrableOn_cexp_mul_thetaRenewalIncrementDeriv (z : ℂ) :
    IntegrableOn (fun t : ℝ => cexp (-(z * t)) * (thetaRenewalIncrementDeriv t : ℂ)) (Ioi 0) := by
  refine (integrableOn_exp_mul_abs_thetaRenewalIncrementDeriv (-z.re)).mono'
    (by have := continuous_thetaRenewalIncrementDeriv; fun_prop) ?_
  refine Eventually.of_forall fun t => ?_
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
  simp

/-- **Integration by parts.** `z N(z) = ν(0) + ∫₀^∞ e^{-zt} ν'(t) dt`. -/
theorem mul_thetaRenewalLaplace_eq (z : ℂ) :
    z * thetaRenewalLaplace z = (thetaRenewalIncrement 0 : ℂ) +
      ∫ t in Ioi (0 : ℝ), cexp (-(z * t)) * (thetaRenewalIncrementDeriv t : ℂ) := by
  have hν := continuous_thetaRenewalIncrement
  set u : ℝ → ℂ := fun t => (thetaRenewalIncrement t : ℂ)
  set u' : ℝ → ℂ := fun t => (thetaRenewalIncrementDeriv t : ℂ)
  set v : ℝ → ℂ := fun t => -cexp (-(z * t))
  set v' : ℝ → ℂ := fun t => z * cexp (-(z * t))
  have hu : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt u (u' x) x := fun x _ =>
    (hasDerivAt_thetaRenewalIncrement x).ofReal_comp
  have hv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt v (v' x) x := by
    intro x _
    have h := (((hasDerivAt_id (x : ℂ)).const_mul z).neg.cexp.comp_ofReal).neg
    simp only [Pi.neg_apply, id] at h
    refine h.congr_deriv ?_
    simp only [v']; ring
  have huv' : IntegrableOn (u * v') (Ioi 0) := by
    refine IntegrableOn.congr_fun ((integrableOn_cexp_mul_of_superexp
      continuous_thetaRenewalIncrement thetaRenewalIncrement_superexp z).const_mul z)
      (fun t _ => ?_) measurableSet_Ioi
    simp only [Pi.mul_apply, u, v']; ring
  have hu'v : IntegrableOn (u' * v) (Ioi 0) := by
    refine IntegrableOn.congr_fun (integrableOn_cexp_mul_thetaRenewalIncrementDeriv z).neg
      (fun t _ => ?_) measurableSet_Ioi
    simp only [Pi.mul_apply, Pi.neg_apply, u', v]; ring
  have hcont : Continuous (u * v) := by simp only [u, v]; fun_prop
  have h0 : Tendsto (u * v) (𝓝[>] 0) (𝓝 (-(thetaRenewalIncrement 0 : ℂ))) := by
    have h := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa [u, v] using h
  have htop : Tendsto (u * v) atTop (𝓝 0) := by
    obtain ⟨C, hC, hle⟩ := thetaRenewalIncrement_superexp (-z.re)
    refine squeeze_zero_norm' (a := fun t => C * Real.exp (-t)) ?_ ?_
    · refine eventually_atTop.mpr ⟨0, fun t ht => ?_⟩
      have hn : ‖(u * v) t‖ = Real.exp (-z.re * t) * |thetaRenewalIncrement t| := by
        simp only [Pi.mul_apply, u, v, norm_mul, norm_neg, Complex.norm_real, Complex.norm_exp,
          Real.norm_eq_abs, neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
        ring_nf
      rw [hn]
      exact hle t ht
    · simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul C
  have h := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v h0 htop
  have hL : ∫ x in Ioi (0 : ℝ), u x * v' x = z * thetaRenewalLaplace z := by
    rw [thetaRenewalLaplace, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [u, v']; ring
  have hR : ∫ x in Ioi (0 : ℝ), u' x * v x =
      -∫ t in Ioi (0 : ℝ), cexp (-(z * t)) * (thetaRenewalIncrementDeriv t : ℂ) := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [u', v]; ring
  rw [hL, hR] at h
  rw [h]; ring

/-- **Uniform decay.** On `Re z ≥ -B`, `‖z‖ ‖N(z)‖ ≤ ν(0) + ∫₀^∞ e^{Bt} |ν'(t)| dt`. -/
theorem norm_mul_thetaRenewalLaplace_le {B : ℝ} {z : ℂ} (hz : -B ≤ z.re) :
    ‖z‖ * ‖thetaRenewalLaplace z‖ ≤ thetaRenewalIncrement 0 +
      ∫ t in Ioi (0 : ℝ), Real.exp (B * t) * |thetaRenewalIncrementDeriv t| := by
  rw [← norm_mul, mul_thetaRenewalLaplace_eq]
  refine (norm_add_le _ _).trans ?_
  rw [Complex.norm_real, Real.norm_of_nonneg (thetaRenewalIncrement_pos 0).le]
  gcongr
  refine (norm_integral_le_integral_norm _).trans (setIntegral_mono_on
    (integrableOn_cexp_mul_thetaRenewalIncrementDeriv z).norm
    (integrableOn_exp_mul_abs_thetaRenewalIncrementDeriv B) measurableSet_Ioi fun t ht => ?_)
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
  gcongr
  simp only [neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  nlinarith [mem_Ioi.mp ht]

/-! ## The resonance divisor -/

/-- The decay constant `M_B = ν(0) + ∫₀^∞ e^{Bt} |ν'(t)| dt`. -/
def thetaRenewalDecayConst (B : ℝ) : ℝ :=
  thetaRenewalIncrement 0 + ∫ t in Ioi (0 : ℝ), Real.exp (B * t) * |thetaRenewalIncrementDeriv t|

theorem analyticOnNhd_thetaRenewalDenominator : AnalyticOnNhd ℂ thetaRenewalDenominator univ :=
  differentiable_thetaRenewalDenominator.differentiableOn.analyticOnNhd isOpen_univ

theorem thetaRenewalDenominator_zero_ne : thetaRenewalDenominator 0 ≠ 0 := by
  rw [thetaRenewalDenominator_zero_eq, Complex.ofReal_ne_zero]
  linarith [thetaRenewalLaplaceReal_zero_lt]

theorem analyticOrderAt_thetaRenewalDenominator_ne_top (z : ℂ) :
    analyticOrderAt thetaRenewalDenominator z ≠ ⊤ :=
  analyticOnNhd_thetaRenewalDenominator.analyticOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (mem_univ 0) (mem_univ z)
    (by rw [((analyticOnNhd_thetaRenewalDenominator 0 (mem_univ 0)).analyticOrderAt_eq_zero).mpr
      thetaRenewalDenominator_zero_ne]; exact ENat.zero_ne_top)

/-- A zero of `D` lies in the divisor support. -/
theorem mem_support_divisor_of_thetaRenewalDenominator_eq_zero {ζ : ℂ}
    (hζ : thetaRenewalDenominator ζ = 0) :
    ζ ∈ (MeromorphicOn.divisor thetaRenewalDenominator univ).support := by
  rw [Function.mem_support, divisor_univ_eq_analyticOrder analyticOnNhd_thetaRenewalDenominator]
  have hne := analyticOrderAt_thetaRenewalDenominator_ne_top ζ
  have h0 : analyticOrderAt thetaRenewalDenominator ζ ≠ 0 := fun h =>
    ((analyticOnNhd_thetaRenewalDenominator ζ (mem_univ ζ)).analyticOrderAt_eq_zero.mp h) hζ
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne
  rw [← hn] at h0 ⊢
  simp only [ENat.map_coe, WithTop.untop₀_coe, ne_eq, Nat.cast_eq_zero]
  exact_mod_cast h0

/-- A divisor point of `D` is a zero of `D`. -/
theorem thetaRenewalDenominator_zeroCopyPoint (q : ZeroCopy thetaRenewalDenominator) :
    thetaRenewalDenominator (zeroCopyPoint thetaRenewalDenominator q) = 0 := by
  have h : (MeromorphicOn.divisor thetaRenewalDenominator univ) (q.1 : ℂ) ≠ 0 := q.1.2
  by_contra hne
  apply h
  change ¬thetaRenewalDenominator (q.1 : ℂ) = 0 at hne
  rw [divisor_univ_eq_analyticOrder analyticOnNhd_thetaRenewalDenominator,
    ((analyticOnNhd_thetaRenewalDenominator _ (mem_univ _)).analyticOrderAt_eq_zero).mpr hne]
  simp

/-- **Resonances escape left.** Zeros of `D` with `Re ζ ≥ -B` satisfy `‖ζ‖ ≤ M_B / c`. -/
theorem norm_le_of_thetaRenewalDenominator_eq_zero {B : ℝ} {ζ : ℂ}
    (hζ : thetaRenewalDenominator ζ = 0) (hB : -B ≤ ζ.re) :
    ‖ζ‖ ≤ thetaRenewalDecayConst B / Θ 1 := by
  have hc := thetaSeam_pos
  have hN : thetaRenewalLaplace ζ = ((Θ 1 : ℝ) : ℂ) := by
    rw [thetaRenewalLaplace_eq_sub, hζ, sub_zero]
  have h := norm_mul_thetaRenewalLaplace_le hB
  rw [hN, Complex.norm_real, Real.norm_of_nonneg hc.le] at h
  rw [le_div_iff₀ hc]
  exact h

/-- **(5), divisor escape.** For every `B`, only finitely many zeros satisfy `Re ζ ≥ -B`. -/
theorem finite_thetaRenewalDenominator_zeros_re_ge (B : ℝ) :
    {ζ : ℂ | thetaRenewalDenominator ζ = 0 ∧ -B ≤ ζ.re}.Finite := by
  have hfin := finite_zeroSupport_ball analyticOnNhd_thetaRenewalDenominator
    (thetaRenewalDecayConst B / Θ 1)
  refine (hfin.image (fun w : ZeroSupport thetaRenewalDenominator => (w : ℂ))).subset ?_
  rintro ζ ⟨hζ, hB⟩
  exact ⟨⟨ζ, mem_support_divisor_of_thetaRenewalDenominator_eq_zero hζ⟩,
    norm_le_of_thetaRenewalDenominator_eq_zero hζ hB, rfl⟩

theorem finite_zeroCopy_re_ge (B : ℝ) :
    {q : ZeroCopy thetaRenewalDenominator |
      -B ≤ (zeroCopyPoint thetaRenewalDenominator q).re}.Finite := by
  refine (locallyFinite_zeroCopyPoint analyticOnNhd_thetaRenewalDenominator
    (thetaRenewalDecayConst B / Θ 1)).subset fun q hq => ?_
  exact norm_le_of_thetaRenewalDenominator_eq_zero (thetaRenewalDenominator_zeroCopyPoint q) hq

/-- Every enumeration of the resonance divisor, with multiplicity, has `Re ζ → -∞`. -/
theorem tendsto_re_zeroCopyPoint_cofinite :
    Tendsto (fun q => (zeroCopyPoint thetaRenewalDenominator q).re) cofinite atBot := by
  rw [Filter.tendsto_atBot]
  intro b
  refine (finite_zeroCopy_re_ge (-b)).subset fun q hq => ?_
  simp only [mem_compl_iff, mem_setOf_eq, not_le] at hq ⊢
  linarith

/-- Every zero of `D` lies in `Re z < -1/4`. -/
theorem re_lt_of_thetaRenewalDenominator_eq_zero {ζ : ℂ} (hζ : thetaRenewalDenominator ζ = 0) :
    ζ.re < -(1 / 4) := by
  by_contra h
  rw [not_lt] at h
  exact thetaRenewalDenominator_ne_zero h hζ

/-! ## The normalized Hadamard product (5d) -/

open OrderOneHadamard in
theorem exists_expAffine_mul_hadamardProduct_thetaRenewalDenominator :
    ∃ a b : ℂ, ∀ z, thetaRenewalDenominator z =
      cexp (a * z + b) * hadamardProduct thetaRenewalDenominator z := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_thetaRenewalDenominator_le
  exact exists_expAffine_mul_hadamardProduct hC analyticOnNhd_thetaRenewalDenominator
    thetaRenewalDenominator_zero_ne analyticOrderAt_thetaRenewalDenominator_ne_top hbound

open OrderOneHadamard in
theorem summable_inv_sq_thetaRenewalZeros :
    Summable fun q : ZeroCopy thetaRenewalDenominator =>
      1 / ‖zeroCopyPoint thetaRenewalDenominator q‖ ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_thetaRenewalDenominator_le
  exact summable_inv_sq_zeroCopyPoint hC analyticOnNhd_thetaRenewalDenominator
    thetaRenewalDenominator_zero_ne hbound

theorem zeroCopyPoint_thetaRenewal_ne_zero (q : ZeroCopy thetaRenewalDenominator) :
    zeroCopyPoint thetaRenewalDenominator q ≠ 0 :=
  zeroCopyPoint_ne_zero analyticOnNhd_thetaRenewalDenominator thetaRenewalDenominator_zero_ne q

open OrderOneHadamard in
theorem differentiable_hadamardProduct_thetaRenewal :
    Differentiable ℂ (hadamardProduct thetaRenewalDenominator) := fun z =>
  (hadamardProduct_analytic analyticOnNhd_thetaRenewalDenominator thetaRenewalDenominator_zero_ne
    summable_inv_sq_thetaRenewalZeros z (mem_univ z)).differentiableAt

/-- The logarithmic derivative of the canonical product. -/
theorem logDeriv_hadamardProduct_thetaRenewal {z : ℂ}
    (hz : ∀ q, z ≠ zeroCopyPoint thetaRenewalDenominator q) :
    logDeriv (OrderOneHadamard.hadamardProduct thetaRenewalDenominator) z =
      ∑' q, ((z - zeroCopyPoint thetaRenewalDenominator q)⁻¹ +
        (zeroCopyPoint thetaRenewalDenominator q)⁻¹) :=
  logDeriv_canonicalProductE1Indexed zeroCopyPoint_thetaRenewal_ne_zero
    summable_inv_sq_thetaRenewalZeros hz

theorem deriv_hadamardProduct_thetaRenewal_zero :
    deriv (OrderOneHadamard.hadamardProduct thetaRenewalDenominator) 0 = 0 := by
  have h := logDeriv_hadamardProduct_thetaRenewal (z := 0)
    (fun q h => zeroCopyPoint_thetaRenewal_ne_zero q h.symm)
  rw [logDeriv_apply, OrderOneHadamard.hadamardProduct_zero, div_one] at h
  rw [h]
  simp

/-- The exponential drift `β = D'(0)/D(0) = ∫ tν / (c - N(0))`. -/
def thetaRenewalDrift : ℝ :=
  (∫ t in Ioi (0 : ℝ), t * thetaRenewalIncrement t) / (Θ 1 - thetaRenewalLaplaceReal 0)

theorem thetaRenewalDrift_pos : 0 < thetaRenewalDrift :=
  div_pos integral_mul_thetaRenewalIncrement_pos (by linarith [thetaRenewalLaplaceReal_zero_lt])

theorem deriv_thetaRenewalDenominator_zero :
    deriv thetaRenewalDenominator 0 = thetaRenewalDrift * thetaRenewalDenominator 0 := by
  have h := deriv_thetaRenewalDenominator_ofReal 0
  simp only [Complex.ofReal_zero, neg_zero, zero_mul, Real.exp_zero, mul_one] at h
  rw [h, thetaRenewalDenominator_zero_eq, thetaRenewalDrift]
  have hne : Θ 1 - thetaRenewalLaplaceReal 0 ≠ 0 := by
    linarith [thetaRenewalLaplaceReal_zero_lt]
  have hne' : ((Θ 1 : ℝ) : ℂ) - (thetaRenewalLaplaceReal 0 : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_sub]; exact_mod_cast hne
  push_cast
  field_simp

/-- **(5d).** `D(z) = D(0) e^{βz} ∏ (1 - z/ζ) e^{z/ζ}`, with `β = D'(0)/D(0) > 0` and
`∑ |ζ|⁻² < ∞`, the product running over the zeros with multiplicity. -/
theorem thetaRenewalDenominator_eq_hadamard (z : ℂ) :
    thetaRenewalDenominator z = thetaRenewalDenominator 0 * cexp (thetaRenewalDrift * z) *
      OrderOneHadamard.hadamardProduct thetaRenewalDenominator z := by
  obtain ⟨a, b, hab⟩ := exists_expAffine_mul_hadamardProduct_thetaRenewalDenominator
  have hD0 : thetaRenewalDenominator 0 = cexp b := by
    rw [hab 0]; simp
  have hderiv : HasDerivAt thetaRenewalDenominator (a * cexp b) 0 := by
    have h1 : HasDerivAt (fun w => cexp (a * w + b)) (cexp (a * 0 + b) * a) 0 :=
      (((hasDerivAt_id (0 : ℂ)).const_mul a).add_const b).cexp.congr_deriv (by simp)
    have h2 := (differentiable_hadamardProduct_thetaRenewal 0).hasDerivAt
    rw [deriv_hadamardProduct_thetaRenewal_zero] at h2
    have h := h1.mul h2
    rw [OrderOneHadamard.hadamardProduct_zero] at h
    refine (h.congr_deriv (by simp; ring)).congr_of_eventuallyEq
      (Eventually.of_forall fun w => hab w)
  have ha : a = thetaRenewalDrift := by
    have h1 := hderiv.deriv
    rw [deriv_thetaRenewalDenominator_zero, hD0] at h1
    exact (mul_right_cancel₀ (Complex.exp_ne_zero b) h1).symm
  rw [hab z, hD0, ha, Complex.exp_add]
  ring

/-- **The resonance-phase sum.** Off the zeros,
`D'(z)/D(z) = β + ∑_ζ ((z - ζ)⁻¹ + ζ⁻¹)`. -/
theorem logDeriv_thetaRenewalDenominator {z : ℂ} (hz : thetaRenewalDenominator z ≠ 0) :
    logDeriv thetaRenewalDenominator z = thetaRenewalDrift +
      ∑' q, ((z - zeroCopyPoint thetaRenewalDenominator q)⁻¹ +
        (zeroCopyPoint thetaRenewalDenominator q)⁻¹) := by
  have hzq : ∀ q, z ≠ zeroCopyPoint thetaRenewalDenominator q := fun q h =>
    hz (h ▸ thetaRenewalDenominator_zeroCopyPoint q)
  have hP : OrderOneHadamard.hadamardProduct thetaRenewalDenominator z ≠ 0 := by
    intro h0; apply hz; rw [thetaRenewalDenominator_eq_hadamard z, h0, mul_zero]
  have hfun : thetaRenewalDenominator = fun w => (thetaRenewalDenominator 0 *
      cexp (thetaRenewalDrift * w)) * OrderOneHadamard.hadamardProduct thetaRenewalDenominator w :=
    funext thetaRenewalDenominator_eq_hadamard
  have hE : thetaRenewalDenominator 0 * cexp (thetaRenewalDrift * z) ≠ 0 :=
    mul_ne_zero thetaRenewalDenominator_zero_ne (Complex.exp_ne_zero _)
  have hD0 := thetaRenewalDenominator_zero_ne
  conv_lhs => rw [hfun]
  rw [logDeriv_mul z hE hP (by fun_prop) (differentiable_hadamardProduct_thetaRenewal z),
    logDeriv_hadamardProduct_thetaRenewal hzq]
  congr 1
  rw [logDeriv_apply]
  have hd : HasDerivAt (fun w => thetaRenewalDenominator 0 * cexp (thetaRenewalDrift * w))
      (thetaRenewalDenominator 0 * (cexp (thetaRenewalDrift * z) * thetaRenewalDrift)) z :=
    (((hasDerivAt_id z).const_mul (thetaRenewalDrift : ℂ)).cexp.const_mul _).congr_deriv
      (by simp)
  rw [hd.deriv]
  field_simp

/-! ## Infinitely many resonances -/

theorem norm_weierstrassE1_le (w : ℂ) : ‖weierstrassE1 w‖ ≤ Real.exp (2 * ‖w‖) := by
  rw [weierstrassE1, norm_mul, Complex.norm_exp, show 2 * ‖w‖ = ‖w‖ + ‖w‖ by ring, Real.exp_add]
  refine mul_le_mul ?_ (Real.exp_le_exp.mpr (Complex.re_le_norm w)) (Real.exp_pos _).le
    (Real.exp_pos _).le
  calc ‖1 - w‖ ≤ ‖(1 : ℂ)‖ + ‖w‖ := norm_sub_le _ _
    _ = ‖w‖ + 1 := by rw [norm_one]; ring
    _ ≤ Real.exp ‖w‖ := Real.add_one_le_exp _

theorem mem_zeroSet_of_mem_support {w : ℂ}
    (hw : w ∈ (MeromorphicOn.divisor thetaRenewalDenominator univ).support) :
    thetaRenewalDenominator w = 0 := by
  by_contra hne
  apply hw
  rw [divisor_univ_eq_analyticOrder analyticOnNhd_thetaRenewalDenominator,
    ((analyticOnNhd_thetaRenewalDenominator _ (mem_univ _)).analyticOrderAt_eq_zero).mpr hne]
  simp

/-- **`D` has infinitely many zeros.** Otherwise its genus-one product is finite, `D` would have
finite exponential type, contradicting `log M_D(R) ≥ R log R - O(R)`. -/
theorem infinite_thetaRenewalDenominator_zeros :
    {ζ : ℂ | thetaRenewalDenominator ζ = 0}.Infinite := by
  intro hfin
  have hsupp : (MeromorphicOn.divisor thetaRenewalDenominator univ).support.Finite :=
    hfin.subset fun w hw => mem_zeroSet_of_mem_support hw
  haveI : Finite (ZeroSupport thetaRenewalDenominator) := hsupp.to_subtype
  haveI : Fintype (ZeroCopy thetaRenewalDenominator) := Fintype.ofFinite _
  set K : ℝ := ∑ q, 2 / ‖zeroCopyPoint thetaRenewalDenominator q‖
  have hP : ∀ z, ‖OrderOneHadamard.hadamardProduct thetaRenewalDenominator z‖ ≤
      Real.exp (K * ‖z‖) := by
    intro z
    rw [OrderOneHadamard.hadamardProduct, canonicalProductE1Indexed, tprod_fintype, norm_prod]
    calc ∏ q, ‖weierstrassE1 (z / zeroCopyPoint thetaRenewalDenominator q)‖
        ≤ ∏ q, Real.exp (2 * ‖z / zeroCopyPoint thetaRenewalDenominator q‖) :=
          Finset.prod_le_prod (fun q _ => norm_nonneg _) (fun q _ => norm_weierstrassE1_le _)
      _ = Real.exp (K * ‖z‖) := by
          rw [← Real.exp_sum, Finset.sum_mul]
          congr 1
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [norm_div]; ring
  obtain ⟨z, -, hz⟩ := thetaRenewalDenominator_infinite_type ‖thetaRenewalDenominator 0‖
    (thetaRenewalDrift + K) 0
  refine absurd hz (not_lt.mpr ?_)
  rw [thetaRenewalDenominator_eq_hadamard z, norm_mul, norm_mul, Complex.norm_exp, add_mul,
    Real.exp_add, ← mul_assoc]
  refine mul_le_mul (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)) (hP z)
    (norm_nonneg _) (by positivity)
  have h1 := Complex.re_le_norm z
  simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
  exact mul_le_mul_of_nonneg_left h1 thetaRenewalDrift_pos.le

/-- **Infinitely many nonreal resonances.** Exactly one zero of `D` is real, so infinitely many
are nonreal; all lie in `Re ζ < -1/4`. -/
theorem infinite_nonreal_thetaRenewalDenominator_zeros :
    {ζ : ℂ | thetaRenewalDenominator ζ = 0 ∧ ζ.im ≠ 0}.Infinite := by
  obtain ⟨x, hx, huniq⟩ := existsUnique_real_thetaRenewalDenominator_eq_zero
  refine (infinite_thetaRenewalDenominator_zeros.sdiff (Set.finite_singleton (x : ℂ))).mono ?_
  rintro ζ ⟨hζ, hne⟩
  refine ⟨hζ, fun him => hne ?_⟩
  have hre : ζ = (ζ.re : ℂ) := Complex.ext (by simp) (by simp [him])
  have hlt := re_lt_of_thetaRenewalDenominator_eq_zero hζ
  have := huniq ζ.re ⟨by rw [← hre]; exact hζ, hlt⟩
  rw [hre, this]; rfl

/-- **(5).** `N` is entire of finite order: `‖N(z)‖ ≤ exp(C (1 + ‖z‖)²)`. -/
theorem exists_norm_thetaRenewalLaplace_le_sq :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖thetaRenewalLaplace z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ 2) := by
  obtain ⟨C, hC, h⟩ := exists_norm_thetaRenewalDenominator_le_sq
  have hc := thetaSeam_pos
  refine ⟨C + Θ 1 + 1, by positivity, fun z => ?_⟩
  have h1 : 1 ≤ (1 + ‖z‖) ^ 2 := by nlinarith [norm_nonneg z]
  calc ‖thetaRenewalLaplace z‖ ≤ ‖((Θ 1 : ℝ) : ℂ)‖ + ‖thetaRenewalDenominator z‖ := by
        rw [thetaRenewalLaplace_eq_sub]; exact norm_sub_le _ _
    _ ≤ Real.exp (Θ 1 * (1 + ‖z‖) ^ 2) + Real.exp (C * (1 + ‖z‖) ^ 2) := by
        rw [Complex.norm_real, Real.norm_of_nonneg hc.le]
        gcongr
        · calc Θ 1 ≤ Θ 1 * (1 + ‖z‖) ^ 2 := le_mul_of_one_le_right hc.le h1
            _ ≤ Real.exp (Θ 1 * (1 + ‖z‖) ^ 2) := by linarith [Real.add_one_le_exp (Θ 1 * (1 + ‖z‖) ^ 2)]
        · exact h z
    _ ≤ Real.exp ((C + Θ 1 + 1) * (1 + ‖z‖) ^ 2) := by
        rw [add_mul, add_mul, Real.exp_add, Real.exp_add, one_mul]
        have e1 : 1 ≤ Real.exp (C * (1 + ‖z‖) ^ 2) := Real.one_le_exp (by positivity)
        have e2 : 1 ≤ Real.exp (Θ 1 * (1 + ‖z‖) ^ 2) := Real.one_le_exp (by positivity)
        have e3 : 2 ≤ Real.exp ((1 + ‖z‖) ^ 2) := by
          linarith [Real.add_one_le_exp ((1 + ‖z‖) ^ 2)]
        have hab1 : Real.exp (Θ 1 * (1 + ‖z‖) ^ 2) ≤
            Real.exp (C * (1 + ‖z‖) ^ 2) * Real.exp (Θ 1 * (1 + ‖z‖) ^ 2) :=
          le_mul_of_one_le_left (by positivity) e1
        have hab2 : Real.exp (C * (1 + ‖z‖) ^ 2) ≤
            Real.exp (C * (1 + ‖z‖) ^ 2) * Real.exp (Θ 1 * (1 + ‖z‖) ^ 2) :=
          le_mul_of_one_le_right (by positivity) e2
        have h3 : Real.exp (C * (1 + ‖z‖) ^ 2) * Real.exp (Θ 1 * (1 + ‖z‖) ^ 2) * 2 ≤
            Real.exp (C * (1 + ‖z‖) ^ 2) * Real.exp (Θ 1 * (1 + ‖z‖) ^ 2) *
              Real.exp ((1 + ‖z‖) ^ 2) := mul_le_mul_of_nonneg_left e3 (by positivity)
        linarith

end

end RHTower
