import GaloisForLFunctions.RHTower.ThetaSieveBidirectionalCuspVariation
import GaloisForLFunctions.RHTower.ThetaZeroDivisionSource
import GaloisForLFunctions.HTGeometry.TwoSidedExponentialMoments

/-!
# Causal modes of the prime-deleted theta sources and the Gaussian boundary trace

For a real source `f` and `ω ∈ ℂ` the right-anchored causal response is
`U_{f,ω}(x) = e^{-ωx} ∫_x^∞ e^{ωt} f(t) dt`; it solves `(∂_x + ω) U = -f`, and its negative-cusp
boundary trace `lim_{x→-∞} e^{ωx} U_{f,ω}(x)` is the full transform `∫ e^{ωt} f`.

Let `k_S` be a finite literal prime deletion of the completed theta source and `h` its first
Gaussian atom.

* At every zero `ω` of `w ↦ XiC(iw)` the transform of `k_S` vanishes, so `U_{k_S,ω}` equals the
  left-anchored response `-e^{-ωx} ∫_{-∞}^x e^{ωt} k_S`, decays faster than every exponential at
  both ends and lies in `L²(ℝ)`.
* Along every exhaustion of the primes `U_{k_{S_j},ω} → U_{h,ω}` uniformly on every right ray.
* The boundary trace of every `U_{k_S,ω}` is `0`, that of `U_{h,ω}` is
  `H(ω) = (ω - 1/2) Γ(ω/2 + 5/4) π^{-(ω/2+1/4)} ≠ 0`: cofinal deletion and the boundary trace do
  not commute.
* For `Re ω ≥ 0`, `|U_{h,ω}(x)| e^{Re ω · x} → |H(ω)|` at the negative cusp, `U_{h,ω} ∉ L²(-∞,0)`
  and `‖U_{k_{S_j},ω}‖²_{L²} → ∞`.
-/

open MeasureTheory Set Filter Topology

noncomputable section

set_option autoImplicit false

namespace RHTower

/-! ## The right-anchored causal response -/

/-- The right-anchored causal response `U_{f,ω}(x) = e^{-ωx} ∫_x^∞ e^{ωt} f(t) dt`. -/
def rightCausalResponse (f : ℝ → ℝ) (ω : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (-(ω * x)) * ∫ t in Ioi x, Complex.exp (ω * t) * (f t : ℂ)

theorem norm_cexp_mul_ofReal (ω : ℂ) (t : ℝ) :
    ‖Complex.exp (ω * t)‖ = Real.exp (ω.re * t) := by
  rw [Complex.norm_exp, Complex.re_mul_ofReal]

/-- The boundary weight `e^{ωx} U_{f,ω}(x)` is the right tail of the transform. -/
theorem cexp_mul_rightCausalResponse (f : ℝ → ℝ) (ω : ℂ) (x : ℝ) :
    Complex.exp (ω * x) * rightCausalResponse f ω x =
      ∫ t in Ioi x, Complex.exp (ω * t) * (f t : ℂ) := by
  rw [rightCausalResponse, ← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero,
    one_mul]

/-- **Causal equation.**  `(∂_x + ω) U_{f,ω} = -f`. -/
theorem hasDerivAt_rightCausalResponse {f : ℝ → ℝ} (hf : Continuous f) {ω : ℂ}
    (hint : Integrable (fun t : ℝ => Complex.exp (ω * t) * (f t : ℂ))) (x : ℝ) :
    HasDerivAt (rightCausalResponse f ω) (-(ω * rightCausalResponse f ω x) - f x) x := by
  have hI := hasDerivAt_setIntegral_Ioi hint (by fun_prop) x
  have hlin : HasDerivAt (fun y : ℝ => -(ω * (y : ℂ))) (-ω) x := by
    have h := ((hasDerivAt_id' x).ofReal_comp).const_mul (-ω)
    simpa using h
  refine (hlin.cexp.mul hI).congr_deriv ?_
  rw [rightCausalResponse]
  have hx : Complex.exp (-(ω * x)) * Complex.exp (ω * x) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  linear_combination (-(f x : ℂ)) * hx

theorem continuous_rightCausalResponse {f : ℝ → ℝ} (hf : Continuous f) {ω : ℂ}
    (hint : Integrable (fun t : ℝ => Complex.exp (ω * t) * (f t : ℂ))) :
    Continuous (rightCausalResponse f ω) :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_rightCausalResponse hf hint x).continuousAt

/-- **Left-anchored form.**  If the full transform vanishes,
`U_{f,ω}(x) = -e^{-ωx} ∫_{-∞}^x e^{ωt} f(t) dt`. -/
theorem rightCausalResponse_eq_neg_left {f : ℝ → ℝ} {ω : ℂ}
    (hint : Integrable (fun t : ℝ => Complex.exp (ω * t) * (f t : ℂ)))
    (hzero : ∫ t : ℝ, Complex.exp (ω * t) * (f t : ℂ) = 0) (x : ℝ) :
    rightCausalResponse f ω x =
      -(Complex.exp (-(ω * x)) * ∫ t in Iic x, Complex.exp (ω * t) * (f t : ℂ)) := by
  have h := integral_add_compl (measurableSet_Iic (a := x)) hint
  rw [compl_Iic, hzero] at h
  rw [rightCausalResponse]
  linear_combination Complex.exp (-(ω * x)) * h

theorem rightCausalResponse_sub {f g : ℝ → ℝ} {ω : ℂ}
    (hf : Integrable (fun t : ℝ => Complex.exp (ω * t) * (f t : ℂ)))
    (hg : Integrable (fun t : ℝ => Complex.exp (ω * t) * (g t : ℂ))) (x : ℝ) :
    rightCausalResponse (fun t => f t - g t) ω x =
      rightCausalResponse f ω x - rightCausalResponse g ω x := by
  simp only [rightCausalResponse, Complex.ofReal_sub, mul_sub]
  rw [integral_sub hf.integrableOn hg.integrableOn, mul_sub]

/-! ## Exponential bounds at the two ends -/

/-- Right bound: for `Re ω ≤ a`, `‖U_{f,ω}(x)‖ ≤ ∫_x^∞ e^{-ax} |e^{at} f(t)| dt`. -/
theorem norm_rightCausalResponse_le {f : ℝ → ℝ} {ω : ℂ} {a : ℝ} (ha : ω.re ≤ a) {x : ℝ}
    (hint : IntegrableOn (fun t : ℝ => Real.exp (a * t) * f t) (Ioi x)) :
    ‖rightCausalResponse f ω x‖ ≤
      ∫ t in Ioi x, Real.exp (-(a * x)) * |Real.exp (a * t) * f t| := by
  rw [rightCausalResponse, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hint.abs.const_mul _) ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards with t ht
  have ht' : 0 ≤ t - x := sub_nonneg.mpr (le_of_lt ht)
  rw [← mul_assoc, ← Complex.exp_add, norm_mul, Complex.norm_exp, Complex.norm_real,
    Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos (a * t)), ← mul_assoc, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (abs_nonneg _)
  have hre : (-(ω * (x : ℂ)) + ω * t).re = ω.re * (t - x) := by
    simp only [Complex.add_re, Complex.neg_re, Complex.re_mul_ofReal]
    ring
  rw [hre]
  nlinarith

/-- Left bound: for `b ≤ Re ω`,
`‖e^{-ωx} ∫_{-∞}^x e^{ωt} f(t) dt‖ ≤ ∫_{-∞}^x e^{-bx} |e^{bt} f(t)| dt`. -/
theorem norm_cexp_mul_setIntegral_Iic_le {f : ℝ → ℝ} {ω : ℂ} {b : ℝ} (hb : b ≤ ω.re) {x : ℝ}
    (hint : IntegrableOn (fun t : ℝ => Real.exp (b * t) * f t) (Iic x)) :
    ‖Complex.exp (-(ω * x)) * ∫ t in Iic x, Complex.exp (ω * t) * (f t : ℂ)‖ ≤
      ∫ t in Iic x, Real.exp (-(b * x)) * |Real.exp (b * t) * f t| := by
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le (hint.abs.const_mul _) ?_
  rw [ae_restrict_iff' measurableSet_Iic]
  filter_upwards with t ht
  have ht' : t - x ≤ 0 := sub_nonpos.mpr ht
  rw [← mul_assoc, ← Complex.exp_add, norm_mul, Complex.norm_exp, Complex.norm_real,
    Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos (b * t)), ← mul_assoc, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (abs_nonneg _)
  have hre : (-(ω * (x : ℂ)) + ω * t).re = ω.re * (t - x) := by
    simp only [Complex.add_re, Complex.neg_re, Complex.re_mul_ofReal]
    ring
  rw [hre]
  nlinarith

private theorem setIntegral_const_mul_abs_le {f : ℝ → ℝ} {c : ℝ} {s : Set ℝ} (hc : 0 ≤ c)
    (hf : Integrable f) :
    (∫ t in s, c * |f t|) ≤ c * ∫ t, |f t| := by
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left
    (setIntegral_le_integral hf.abs (Eventually.of_forall fun _ => abs_nonneg _)) hc

/-- **Two-ended decay.**  If `e^{at} f` is integrable for every real `a` and the transform at `ω`
vanishes, then `U_{f,ω}` decays faster than every exponential at both ends. -/
theorem exists_norm_rightCausalResponse_le {f : ℝ → ℝ} {ω : ℂ}
    (hmom : ∀ a : ℝ, Integrable (fun t : ℝ => Real.exp (a * t) * f t))
    (hint : Integrable (fun t : ℝ => Complex.exp (ω * t) * (f t : ℂ)))
    (hzero : ∫ t : ℝ, Complex.exp (ω * t) * (f t : ℂ) = 0) (N : ℝ) :
    ∃ C, ∀ x, ‖rightCausalResponse f ω x‖ ≤ C * Real.exp (-(N * |x|)) := by
  set M := |ω.re| + |N| with hM
  set Ca := ∫ t, |Real.exp (M * t) * f t|
  set Cb := ∫ t, |Real.exp (-M * t) * f t|
  have hCa : 0 ≤ Ca := integral_nonneg fun _ => abs_nonneg _
  have hCb : 0 ≤ Cb := integral_nonneg fun _ => abs_nonneg _
  have hωM : ω.re ≤ M := by rw [hM]; linarith [le_abs_self ω.re, abs_nonneg N]
  have hωM' : -M ≤ ω.re := by rw [hM]; linarith [neg_abs_le ω.re, abs_nonneg N]
  have hNM : N ≤ M := by rw [hM]; linarith [le_abs_self N, abs_nonneg ω.re]
  refine ⟨Ca + Cb, fun x => ?_⟩
  have hE := (Real.exp_pos (-(N * |x|))).le
  rcases le_total 0 x with hx | hx
  · have h1 := norm_rightCausalResponse_le hωM (hmom M).integrableOn (x := x)
    have h2 := setIntegral_const_mul_abs_le (s := Ioi x) (Real.exp_pos (-(M * x))).le (hmom M)
    have h3 : Real.exp (-(M * x)) ≤ Real.exp (-(N * |x|)) := by
      rw [abs_of_nonneg hx]
      exact Real.exp_le_exp.mpr (by nlinarith)
    calc ‖rightCausalResponse f ω x‖ ≤ Real.exp (-(M * x)) * Ca := h1.trans h2
      _ ≤ Real.exp (-(N * |x|)) * Ca := mul_le_mul_of_nonneg_right h3 hCa
      _ ≤ (Ca + Cb) * Real.exp (-(N * |x|)) := by nlinarith
  · rw [rightCausalResponse_eq_neg_left hint hzero, norm_neg]
    have h1 := norm_cexp_mul_setIntegral_Iic_le hωM' (hmom (-M)).integrableOn (x := x)
    have h2 := setIntegral_const_mul_abs_le (s := Iic x) (Real.exp_pos (-(-M * x))).le
      (hmom (-M))
    have h3 : Real.exp (-(-M * x)) ≤ Real.exp (-(N * |x|)) := by
      rw [abs_of_nonpos hx]
      exact Real.exp_le_exp.mpr (by nlinarith)
    calc ‖Complex.exp (-(ω * x)) * ∫ t in Iic x, Complex.exp (ω * t) * (f t : ℂ)‖ ≤
          Real.exp (-(-M * x)) * Cb := h1.trans h2
      _ ≤ Real.exp (-(N * |x|)) * Cb := mul_le_mul_of_nonneg_right h3 hCb
      _ ≤ (Ca + Cb) * Real.exp (-(N * |x|)) := by nlinarith

/-- A two-ended rapidly decreasing causal response is square integrable. -/
theorem memLp_two_rightCausalResponse {f : ℝ → ℝ} (hf : Continuous f) {ω : ℂ}
    (hmom : ∀ a : ℝ, Integrable (fun t : ℝ => Real.exp (a * t) * f t))
    (hint : Integrable (fun t : ℝ => Complex.exp (ω * t) * (f t : ℂ)))
    (hzero : ∫ t : ℝ, Complex.exp (ω * t) * (f t : ℂ) = 0) :
    MemLp (rightCausalResponse f ω) 2 := by
  have hcont := continuous_rightCausalResponse hf hint
  obtain ⟨C, hC⟩ := exists_norm_rightCausalResponse_le hmom hint hzero 1
  rw [memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable]
  refine ((_root_.HTGeometry.integrable_abs_pow_mul_exp_neg_abs 0 two_pos).const_mul
    (C ^ 2)).mono' (hcont.norm.pow 2).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h := pow_le_pow_left₀ (norm_nonneg _) (hC x) 2
  refine h.trans (le_of_eq ?_)
  rw [mul_pow, sq (Real.exp _), ← Real.exp_add]
  congr 1
  simp only [pow_zero, one_mul]
  rw [Real.exp_eq_exp]
  ring

/-! ## The negative-cusp boundary trace -/

theorem tendsto_setIntegral_Ioi_atBot {g : ℝ → ℂ} (hg : Integrable g) :
    Tendsto (fun x : ℝ => ∫ t in Ioi x, g t) atBot (𝓝 (∫ t, g t)) := by
  have h := intervalIntegral_tendsto_integral_Iic (μ := volume) (l := atBot) (a := fun x => x)
    (0 : ℝ) hg.integrableOn tendsto_id
  have htot := integral_add_compl (measurableSet_Iic (a := (0 : ℝ))) hg
  rw [compl_Iic] at htot
  rw [← htot]
  refine (h.add_const (∫ t in Ioi (0 : ℝ), g t)).congr fun x => ?_
  rw [setIntegral_Ioi_eq_sub hg x, intervalIntegral.integral_symm x 0]
  ring

/-- **Boundary trace.**  `lim_{x→-∞} e^{ωx} U_{f,ω}(x) = ∫ e^{ωt} f(t) dt`. -/
theorem tendsto_cexp_mul_rightCausalResponse_atBot {f : ℝ → ℝ} {ω : ℂ}
    (hint : Integrable (fun t : ℝ => Complex.exp (ω * t) * (f t : ℂ))) :
    Tendsto (fun x : ℝ => Complex.exp (ω * x) * rightCausalResponse f ω x) atBot
      (𝓝 (∫ t : ℝ, Complex.exp (ω * t) * (f t : ℂ))) := by
  simp_rw [cexp_mul_rightCausalResponse]
  exact tendsto_setIntegral_Ioi_atBot hint

/-! ## Causal modes of the finite deletions -/

/-- **Two-ended causal mode of a finite deletion.**  At every zero `ω` of `w ↦ XiC(iw)` the causal
response of `k_S` solves `(∂_x + ω) U = -k_S`, equals the left-anchored response, decays faster
than every exponential at both ends, lies in `L²(ℝ)` and has boundary trace `0`. -/
theorem thetaPrimeDeletion_causalMode (S : Finset ℕ) (hS : ∀ p ∈ S, 0 < p) {ω : ℂ}
    (hzero : XiC (Complex.I * ω) = 0) :
    (∀ x, HasDerivAt (rightCausalResponse (thetaPrimeDeletion S thetaCuspFullSource) ω)
        (-(ω * rightCausalResponse (thetaPrimeDeletion S thetaCuspFullSource) ω x) -
          thetaPrimeDeletion S thetaCuspFullSource x) x) ∧
      (∀ x, rightCausalResponse (thetaPrimeDeletion S thetaCuspFullSource) ω x =
        -(Complex.exp (-(ω * x)) * ∫ t in Iic x, Complex.exp (ω * t) *
          (thetaPrimeDeletion S thetaCuspFullSource t : ℂ))) ∧
      (∀ N : ℝ, ∃ C, ∀ x,
        ‖rightCausalResponse (thetaPrimeDeletion S thetaCuspFullSource) ω x‖ ≤
          C * Real.exp (-(N * |x|))) ∧
      MemLp (rightCausalResponse (thetaPrimeDeletion S thetaCuspFullSource) ω) 2 ∧
      Tendsto (fun x : ℝ => Complex.exp (ω * x) *
        rightCausalResponse (thetaPrimeDeletion S thetaCuspFullSource) ω x) atBot (𝓝 0) := by
  have hf := continuous_thetaPrimeDeletion S continuous_thetaCuspFullSource
  have hint := integrable_cexp_mul_thetaPrimeDeletion_thetaCuspFullSource S hS ω
  have hmom : ∀ a : ℝ, Integrable (fun t : ℝ =>
      Real.exp (a * t) * thetaPrimeDeletion S thetaCuspFullSource t) :=
    fun a => integrable_exp_mul_thetaPrimeDeletion S hS a
  have hz : ∫ t : ℝ, Complex.exp (ω * t) * (thetaPrimeDeletion S thetaCuspFullSource t : ℂ) = 0 := by
    rw [integral_cexp_mul_thetaPrimeDeletion_thetaCuspFullSource S hS, hzero, zero_mul]
  refine ⟨hasDerivAt_rightCausalResponse hf hint, rightCausalResponse_eq_neg_left hint hz,
    exists_norm_rightCausalResponse_le hmom hint hz, memLp_two_rightCausalResponse hf hmom hint hz,
    ?_⟩
  simpa [hz] using tendsto_cexp_mul_rightCausalResponse_atBot hint

/-! ## The Gaussian seed mode -/

theorem integrable_cexp_mul_thetaSeedAtom {ω : ℂ} (hω : -(5 / 2) < ω.re) :
    Integrable (fun t : ℝ => Complex.exp (ω * t) * (thetaCuspSourceTerm t 1 : ℂ)) :=
  integrable_cexp_mul_thetaCuspSourceTerm ω hω 1 one_pos

/-- **Seed boundary trace (3).**  `lim_{x→-∞} e^{ωx} U_{h,ω}(x) = H(ω)`. -/
theorem tendsto_cexp_mul_rightCausalResponse_seed {ω : ℂ} (hω : -(5 / 2) < ω.re) :
    Tendsto (fun x : ℝ => Complex.exp (ω * x) *
        rightCausalResponse (fun t => thetaCuspSourceTerm t 1) ω x) atBot
      (𝓝 (thetaAtomMellinFactor ω)) := by
  rw [← integral_cexp_mul_thetaSeedAtom ω hω]
  exact tendsto_cexp_mul_rightCausalResponse_atBot (integrable_cexp_mul_thetaSeedAtom hω)

theorem thetaAtomMellinFactor_ne_zero_of_abs_re_lt {ω : ℂ} (hω : |ω.re| < 1 / 2) :
    thetaAtomMellinFactor ω ≠ 0 := by
  have hre := abs_lt.mp hω
  refine thetaAtomMellinFactor_ne_zero (by linarith) fun h => ?_
  have := congrArg Complex.re h
  norm_num at this
  linarith

/-- **Negative-cusp asymptotics of the seed mode.**  `|U_{h,ω}(x)| e^{Re ω · x} → |H(ω)|`. -/
theorem tendsto_norm_rightCausalResponse_seed_mul_exp {ω : ℂ} (hω : -(5 / 2) < ω.re) :
    Tendsto (fun x : ℝ => ‖rightCausalResponse (fun t => thetaCuspSourceTerm t 1) ω x‖ *
        Real.exp (ω.re * x)) atBot (𝓝 ‖thetaAtomMellinFactor ω‖) := by
  refine (tendsto_cexp_mul_rightCausalResponse_seed hω).norm.congr fun x => ?_
  rw [norm_mul, norm_cexp_mul_ofReal, mul_comm]

/-- For `Re ω ≥ 0` the seed mode stays above `|H(ω)|/2` on a whole negative ray. -/
theorem exists_half_le_norm_rightCausalResponse_seed {ω : ℂ} (hω0 : 0 ≤ ω.re) :
    ∃ x₀ ≤ (0 : ℝ), ∀ x ≤ x₀, ‖thetaAtomMellinFactor ω‖ / 2 ≤
      ‖rightCausalResponse (fun t => thetaCuspSourceTerm t 1) ω x‖ := by
  have hω : -(5 / 2) < ω.re := by linarith
  by_cases hH : thetaAtomMellinFactor ω = 0
  · exact ⟨0, le_rfl, fun x _ => by rw [hH, norm_zero, zero_div]; exact norm_nonneg _⟩
  have hpos : ‖thetaAtomMellinFactor ω‖ / 2 < ‖thetaAtomMellinFactor ω‖ := by
    have := norm_pos_iff.mpr hH
    linarith
  obtain ⟨x₁, hx₁⟩ := eventually_atBot.mp
    ((tendsto_cexp_mul_rightCausalResponse_seed hω).norm.eventually (lt_mem_nhds hpos))
  refine ⟨min x₁ 0, min_le_right _ _, fun x hx => ?_⟩
  have h := hx₁ x (hx.trans (min_le_left _ _))
  have hx0 : x ≤ 0 := hx.trans (min_le_right _ _)
  rw [norm_mul, norm_cexp_mul_ofReal] at h
  have hexp : Real.exp (ω.re * x) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hU := norm_nonneg (rightCausalResponse (fun t => thetaCuspSourceTerm t 1) ω x)
  nlinarith

/-- **The seed mode is not square integrable at the negative cusp** when `Re ω ≥ 0` and
`H(ω) ≠ 0`. -/
theorem not_integrableOn_sq_norm_rightCausalResponse_seed {ω : ℂ} (hω0 : 0 ≤ ω.re)
    (hH : thetaAtomMellinFactor ω ≠ 0) :
    ¬ IntegrableOn (fun x => ‖rightCausalResponse (fun t => thetaCuspSourceTerm t 1) ω x‖ ^ 2)
      (Iic 0) := by
  intro hI
  obtain ⟨x₀, hx₀, hlow⟩ := exists_half_le_norm_rightCausalResponse_seed hω0
  set c := (‖thetaAtomMellinFactor ω‖ / 2) ^ 2 with hc
  have hcpos : 0 < c := by have := norm_pos_iff.mpr hH; positivity
  set I := ∫ x in Iic (0 : ℝ),
    ‖rightCausalResponse (fun t => thetaCuspSourceTerm t 1) ω x‖ ^ 2
  set L := |I| / c + 1 with hL
  have hL0 : 0 ≤ L := by positivity
  have hsub : Icc (x₀ - L) x₀ ⊆ Iic 0 := fun x hx => hx.2.trans hx₀
  have h1 : (∫ x in Icc (x₀ - L) x₀,
      ‖rightCausalResponse (fun t => thetaCuspSourceTerm t 1) ω x‖ ^ 2) ≤ I :=
    setIntegral_mono_set hI (Eventually.of_forall fun _ => by positivity) hsub.eventuallyLE
  have h2 : (∫ _x in Icc (x₀ - L) x₀, c) ≤ ∫ x in Icc (x₀ - L) x₀,
      ‖rightCausalResponse (fun t => thetaCuspSourceTerm t 1) ω x‖ ^ 2 := by
    refine setIntegral_mono_on (continuous_const.integrableOn_Icc) (hI.mono_set hsub)
      measurableSet_Icc fun x hx => ?_
    exact pow_le_pow_left₀ (by positivity) (hlow x hx.2) 2
  rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul] at h2
  have h3 : (x₀ - (x₀ - L)) * c = |I| + c := by
    rw [hL]
    field_simp
    ring
  have := le_abs_self I
  linarith

/-! ## Cofinal deletion: local convergence, noncommutation and escape -/

/-- **Weighted absolute residual on right rays.**  For `w > -5/2` and every `x₀`,
`∫_{x₀}^∞ |e^{wt} (k_{S_j} - h)(t)| dt → 0`. -/
theorem PrimeExhaustion.tendsto_setIntegral_Ioi_abs_exp_mul_thetaSieveResidual
    {S : ℕ → Finset ℕ} (hS : PrimeExhaustion S) {w : ℝ} (hw : -(5 / 2) < w) (x₀ : ℝ) :
    Tendsto (fun j => ∫ x in Ioi x₀, |Real.exp (w * x) * thetaSieveResidual (S j) x|)
      atTop (𝓝 0) := by
  set R' := |x₀|
  set C := ∑' m, thetaCuspSourceMajorant R' m
  let bound : ℝ → ℝ := fun x =>
    (Set.Icc (-R') 0).indicator (fun _ => Real.exp (|w| * R') * C) x +
      (Real.exp (w * x) * thetaCuspFullSource x + |Real.exp (w * x) * thetaCuspSourceTerm x 1|)
  have hbound : Integrable bound (volume.restrict (Set.Ioi x₀)) := by
    apply Integrable.integrableOn
    apply Integrable.add
    · exact (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
    · exact (HedenmalmThetaSource.integrable_exp_mul_thetaCuspFullSource w).add
        (integrable_exp_mul_thetaSeedAtom hw).abs
  have hlim : (∫ _x in Set.Ioi x₀, (0 : ℝ)) = 0 := integral_zero _ _
  rw [← hlim]
  apply tendsto_integral_of_dominated_convergence bound
  · intro j
    exact (((by fun_prop : Continuous fun x : ℝ => Real.exp (w * x)).mul
      (continuous_thetaSieveResidual (S j))).abs).aestronglyMeasurable
  · exact hbound
  · intro j
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with x hx
    rw [Real.norm_eq_abs, abs_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    by_cases hx0 : x ≤ 0
    · have hmem : x ∈ Set.Icc (-R') 0 :=
        ⟨by linarith [neg_abs_le x₀, Set.mem_Ioi.mp hx], hx0⟩
      have hmem' : x ∈ Set.Icc (-R') R' := ⟨hmem.1, hx0.trans (abs_nonneg x₀)⟩
      simp only [bound, Set.indicator_of_mem hmem]
      have hres := abs_thetaPrimeDeletion_sub_seed_le (S j) (hS.prime j) hmem'
      have hexp : Real.exp (w * x) ≤ Real.exp (|w| * R') := by
        apply Real.exp_le_exp.mpr
        have : |x| ≤ R' := abs_le.mpr ⟨hmem.1, hx0.trans (abs_nonneg x₀)⟩
        calc w * x ≤ |w * x| := le_abs_self _
          _ = |w| * |x| := abs_mul _ _
          _ ≤ |w| * R' := mul_le_mul_of_nonneg_left this (abs_nonneg w)
      have h1 : Real.exp (w * x) * |thetaSieveResidual (S j) x| ≤ Real.exp (|w| * R') * C :=
        mul_le_mul hexp hres (abs_nonneg _) (Real.exp_pos _).le
      have h2 : 0 ≤ Real.exp (w * x) * thetaCuspFullSource x :=
        mul_nonneg (Real.exp_pos _).le (thetaCuspFullSource_pos_all x).le
      have h3 := abs_nonneg (Real.exp (w * x) * thetaCuspSourceTerm x 1)
      linarith
    · have hx0' : 0 ≤ x := le_of_lt (not_le.mp hx0)
      have hmem : x ∉ Set.Icc (-R') 0 := fun h => hx0 h.2
      simp only [bound, Set.indicator_of_notMem hmem, zero_add]
      obtain ⟨_, h2⟩ := thetaCuspSourceTerm_one_le_thetaPrimeDeletion (S j) (hS.prime j) hx0'
      have hD := (thetaPrimeDeletion_pos_of_nonneg (S j) (hS.prime j) hx0').le
      have habs : |thetaSieveResidual (S j) x| ≤
          thetaCuspFullSource x + |thetaCuspSourceTerm x 1| := by
        unfold thetaSieveResidual
        calc
          |thetaPrimeDeletion (S j) thetaCuspFullSource x - thetaCuspSourceTerm x 1| ≤
              |thetaPrimeDeletion (S j) thetaCuspFullSource x| + |thetaCuspSourceTerm x 1| :=
            abs_sub _ _
          _ ≤ thetaCuspFullSource x + |thetaCuspSourceTerm x 1| := by
            rw [abs_of_nonneg hD]
            linarith
      rw [abs_mul, abs_of_pos (Real.exp_pos (w * x))]
      nlinarith [Real.exp_pos (w * x)]
  · filter_upwards with x
    have h := ((hS.tendsto_thetaPrimeDeletion x).sub_const (thetaCuspSourceTerm x 1)).const_mul
      (Real.exp (w * x))
    rw [sub_self, mul_zero] at h
    have h' := h.abs
    rw [abs_zero] at h'
    exact h'

theorem rightCausalResponse_thetaSieveResidual (S : Finset ℕ) (hS : ∀ p ∈ S, 0 < p) {ω : ℂ}
    (hω : -(5 / 2) < ω.re) (x : ℝ) :
    rightCausalResponse (thetaSieveResidual S) ω x =
      rightCausalResponse (thetaPrimeDeletion S thetaCuspFullSource) ω x -
        rightCausalResponse (fun t => thetaCuspSourceTerm t 1) ω x :=
  rightCausalResponse_sub (integrable_cexp_mul_thetaPrimeDeletion_thetaCuspFullSource S hS ω)
    (integrable_cexp_mul_thetaSeedAtom hω) x

/-- **Local mode convergence (2).**  Along every exhaustion of the primes, the causal responses of
the deleted sources converge to the seed response uniformly on every right ray `[x₀, ∞)`. -/
theorem PrimeExhaustion.tendstoUniformlyOn_rightCausalResponse {S : ℕ → Finset ℕ}
    (hS : PrimeExhaustion S) {ω : ℂ} (hω : -(5 / 2) < ω.re) (x₀ : ℝ) :
    TendstoUniformlyOn
      (fun j => rightCausalResponse (thetaPrimeDeletion (S j) thetaCuspFullSource) ω)
      (rightCausalResponse (fun t => thetaCuspSourceTerm t 1) ω) atTop (Ici x₀) := by
  set a := max ω.re 0 with ha
  have ha0 : 0 ≤ a := le_max_right _ _
  have hωa : ω.re ≤ a := le_max_left _ _
  have hlim := (hS.tendsto_setIntegral_Ioi_abs_exp_mul_thetaSieveResidual
    (w := a) (by linarith) x₀).const_mul (Real.exp (-(a * x₀)))
  rw [mul_zero] at hlim
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with j hj x hx
  have hSpos : ∀ p ∈ S j, 0 < p := fun p hp => (hS.prime j p hp).pos
  have hres := integrable_exp_mul_thetaSieveResidual (S j) hSpos (w := a) (by linarith)
  rw [dist_eq_norm, ← norm_neg, neg_sub, ← rightCausalResponse_thetaSieveResidual (S j) hSpos hω]
  have hx' : x₀ ≤ x := hx
  calc ‖rightCausalResponse (thetaSieveResidual (S j)) ω x‖ ≤
        ∫ t in Ioi x, Real.exp (-(a * x)) * |Real.exp (a * t) * thetaSieveResidual (S j) t| :=
      norm_rightCausalResponse_le hωa hres.integrableOn
    _ = Real.exp (-(a * x)) * ∫ t in Ioi x, |Real.exp (a * t) * thetaSieveResidual (S j) t| :=
      integral_const_mul _ _
    _ ≤ Real.exp (-(a * x₀)) *
        ∫ t in Ioi x₀, |Real.exp (a * t) * thetaSieveResidual (S j) t| := by
      apply mul_le_mul (Real.exp_le_exp.mpr (by nlinarith)) _ (integral_nonneg fun _ => abs_nonneg _)
        (Real.exp_pos _).le
      exact setIntegral_mono_set hres.abs.integrableOn
        (Eventually.of_forall fun _ => abs_nonneg _)
        (Ioi_subset_Ioi hx').eventuallyLE
    _ < ε := hj

/-- **Noncommutation of cofinal deletion and the boundary trace (4).**  At every Xi zero `ω` of the
open strip: for every finite deletion the boundary trace vanishes, pointwise in `x` the weighted
modes converge to the seed mode, and the seed mode has boundary trace `H(ω) ≠ 0`. -/
theorem PrimeExhaustion.boundaryTrace_tendsto {S : ℕ → Finset ℕ} (hS : PrimeExhaustion S)
    {ω : ℂ} (hω : |ω.re| < 1 / 2) (hzero : XiC (Complex.I * ω) = 0) :
    (∀ j, Tendsto (fun x : ℝ => Complex.exp (ω * x) *
        rightCausalResponse (thetaPrimeDeletion (S j) thetaCuspFullSource) ω x) atBot (𝓝 0)) ∧
      (∀ x : ℝ, Tendsto (fun j => Complex.exp (ω * x) *
        rightCausalResponse (thetaPrimeDeletion (S j) thetaCuspFullSource) ω x) atTop
          (𝓝 (Complex.exp (ω * x) * rightCausalResponse (fun t => thetaCuspSourceTerm t 1) ω x))) ∧
      Tendsto (fun x : ℝ => Complex.exp (ω * x) *
        rightCausalResponse (fun t => thetaCuspSourceTerm t 1) ω x) atBot
          (𝓝 (thetaAtomMellinFactor ω)) ∧
      thetaAtomMellinFactor ω ≠ 0 := by
  have hre := abs_lt.mp hω
  have hω' : -(5 / 2) < ω.re := by linarith
  refine ⟨fun j => (thetaPrimeDeletion_causalMode (S j)
      (fun p hp => (hS.prime j p hp).pos) hzero).2.2.2.2, fun x => ?_,
    tendsto_cexp_mul_rightCausalResponse_seed hω', thetaAtomMellinFactor_ne_zero_of_abs_re_lt hω⟩
  exact ((hS.tendstoUniformlyOn_rightCausalResponse hω' x).tendsto_at
    (self_mem_Ici)).const_mul _

/-- **The two iterated limits (4).**
`lim_j lim_{x→-∞} e^{ωx} U_{k_{S_j},ω}(x) = 0` while
`lim_{x→-∞} lim_j e^{ωx} U_{k_{S_j},ω}(x) = H(ω) ≠ 0`. -/
theorem PrimeExhaustion.boundaryTrace_noncommute {S : ℕ → Finset ℕ} (hS : PrimeExhaustion S)
    {ω : ℂ} (hω : |ω.re| < 1 / 2) (hzero : XiC (Complex.I * ω) = 0) :
    limUnder atTop (fun j => limUnder atBot (fun x : ℝ => Complex.exp (ω * x) *
        rightCausalResponse (thetaPrimeDeletion (S j) thetaCuspFullSource) ω x)) = 0 ∧
      limUnder atBot (fun x : ℝ => limUnder atTop (fun j => Complex.exp (ω * x) *
        rightCausalResponse (thetaPrimeDeletion (S j) thetaCuspFullSource) ω x)) =
        thetaAtomMellinFactor ω ∧
      thetaAtomMellinFactor ω ≠ 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := hS.boundaryTrace_tendsto hω hzero
  refine ⟨?_, ?_, h4⟩
  · have hfun : (fun j => limUnder atBot (fun x : ℝ => Complex.exp (ω * x) *
        rightCausalResponse (thetaPrimeDeletion (S j) thetaCuspFullSource) ω x)) =
        fun _ => (0 : ℂ) := funext fun j => (h1 j).limUnder_eq
    rw [hfun]
    exact tendsto_const_nhds.limUnder_eq
  · have hfun : (fun x : ℝ => limUnder atTop (fun j => Complex.exp (ω * x) *
        rightCausalResponse (thetaPrimeDeletion (S j) thetaCuspFullSource) ω x)) =
        fun x : ℝ => Complex.exp (ω * x) *
          rightCausalResponse (fun t => thetaCuspSourceTerm t 1) ω x :=
      funext fun x => (h2 x).limUnder_eq
    rw [hfun]
    exact h3.limUnder_eq

/-- **Escape of the finite modes (5).**  At an Xi zero with `0 ≤ Re ω < 1/2`, every
`U_{k_{S_j},ω}` lies in `L²(ℝ)`, but `‖U_{k_{S_j},ω}‖²_{L²} → ∞`. -/
theorem PrimeExhaustion.tendsto_integral_sq_norm_rightCausalResponse {S : ℕ → Finset ℕ}
    (hS : PrimeExhaustion S) {ω : ℂ} (hω0 : 0 ≤ ω.re) (hω1 : ω.re < 1 / 2)
    (hzero : XiC (Complex.I * ω) = 0) :
    Tendsto (fun j => ∫ x : ℝ,
      ‖rightCausalResponse (thetaPrimeDeletion (S j) thetaCuspFullSource) ω x‖ ^ 2)
      atTop atTop := by
  have hω : |ω.re| < 1 / 2 := abs_lt.mpr ⟨by linarith, hω1⟩
  have hω' : -(5 / 2) < ω.re := by linarith
  have hH := thetaAtomMellinFactor_ne_zero_of_abs_re_lt hω
  set H := ‖thetaAtomMellinFactor ω‖ with hHdef
  have hHpos : 0 < H := norm_pos_iff.mpr hH
  obtain ⟨x₀, _, hlow⟩ := exists_half_le_norm_rightCausalResponse_seed hω0
  set c := (H / 4) ^ 2 with hc
  have hcpos : 0 < c := by positivity
  rw [tendsto_atTop]
  intro M
  set L := |M| / c with hL
  have hL0 : 0 ≤ L := by positivity
  have hunif := hS.tendstoUniformlyOn_rightCausalResponse hω' (x₀ - L)
  rw [Metric.tendstoUniformlyOn_iff] at hunif
  filter_upwards [hunif (H / 4) (by positivity)] with j hj
  have hSpos : ∀ p ∈ S j, 0 < p := fun p hp => (hS.prime j p hp).pos
  obtain ⟨_, _, _, hmem, _⟩ := thetaPrimeDeletion_causalMode (S j) hSpos hzero
  have hcont := continuous_rightCausalResponse
    (continuous_thetaPrimeDeletion (S j) continuous_thetaCuspFullSource)
    (integrable_cexp_mul_thetaPrimeDeletion_thetaCuspFullSource (S j) hSpos ω)
  have hI := (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).1 hmem
  have hK : ∀ x ∈ Icc (x₀ - L) x₀, c ≤
      ‖rightCausalResponse (thetaPrimeDeletion (S j) thetaCuspFullSource) ω x‖ ^ 2 := by
    intro x hx
    have h1 := hlow x hx.2
    have h2 := hj x hx.1
    rw [dist_eq_norm] at h2
    have h3 := norm_sub_norm_le (rightCausalResponse (fun t => thetaCuspSourceTerm t 1) ω x)
      (rightCausalResponse (thetaPrimeDeletion (S j) thetaCuspFullSource) ω x)
    exact pow_le_pow_left₀ (by positivity) (by linarith) 2
  have h1 : (∫ _x in Icc (x₀ - L) x₀, c) ≤ ∫ x in Icc (x₀ - L) x₀,
      ‖rightCausalResponse (thetaPrimeDeletion (S j) thetaCuspFullSource) ω x‖ ^ 2 :=
    setIntegral_mono_on (continuous_const.integrableOn_Icc) hI.integrableOn measurableSet_Icc hK
  have h2 := setIntegral_le_integral (s := Icc (x₀ - L) x₀) hI
    (Eventually.of_forall fun x => by positivity)
  rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul] at h1
  have h3 : (x₀ - (x₀ - L)) * c = |M| := by
    rw [hL]
    field_simp
    ring
  have := le_abs_self M
  linarith

/-- For `Re ω ≥ 0` in the strip the seed mode is not in `L²(-∞, 0)`. -/
theorem not_memLp_two_rightCausalResponse_seed {ω : ℂ} (hω0 : 0 ≤ ω.re) (hω1 : ω.re < 1 / 2) :
    ¬ MemLp (rightCausalResponse (fun t => thetaCuspSourceTerm t 1) ω) 2
      (volume.restrict (Iic 0)) := by
  have hω : |ω.re| < 1 / 2 := abs_lt.mpr ⟨by linarith, hω1⟩
  have hcont := continuous_rightCausalResponse (continuous_thetaCuspSourceTerm 1)
    (integrable_cexp_mul_thetaSeedAtom (ω := ω) (by linarith))
  rw [memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable]
  exact not_integrableOn_sq_norm_rightCausalResponse_seed hω0
    (thetaAtomMellinFactor_ne_zero_of_abs_re_lt hω)

end RHTower
