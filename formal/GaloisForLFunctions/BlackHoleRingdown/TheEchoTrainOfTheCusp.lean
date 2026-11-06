import GaloisForLFunctions.RHTower.TotientMulLSeries
import GaloisForLFunctions.HTGeometry.CoshFourierTransform

/-!
# The echo train of the cusp

The scattering coefficient of the modular surface is the Laplace transform of a causal echo train. A
wave reflected at the cusp returns as echoes with delay `2 log c` and weight `ϕ(c)/c`, each carrying the
same bounce profile `(1 - e^{-v})^{-1/2}`:

`K(τ) = ∑_{2 log c < τ} (ϕ(c)/c) (1 - e^{-(τ - 2 log c)})^{-1/2}`.

For `Re w > 1/2`,

`∫ e^{-wτ} K(τ) dτ = B(w, 1/2) ζ(2w)/ζ(2w+1) = Λ(2w)/Λ(2w+1)`,

which at `s = w + 1/2` is the classical `Λ(2s-1)/Λ(2s)`. The bounce profile transforms to the Beta
factor, its translates give the Dirichlet series of the totient, and `K` vanishes for `τ ≤ 0`.
-/

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

/-- The bounce profile `(1 - e^{-v})^{-1/2}`. -/
def bounceKernel (v : ℝ) : ℝ := (1 - Real.exp (-v)) ^ (-(1 / 2) : ℝ)

/-- The delay of the echo of denominator `c`. -/
def echoDelay (c : ℕ) : ℝ := 2 * Real.log c

/-- The weight of the echo of denominator `c`. -/
def echoWeight (c : ℕ) : ℝ := (Nat.totient c : ℝ) / c

/-- The echo of denominator `c`, switched on at its delay. -/
def echoTerm (c : ℕ) (τ : ℝ) : ℝ :=
  if echoDelay c < τ then echoWeight c * bounceKernel (τ - echoDelay c) else 0

/-- The echo train. -/
def echoKernel (τ : ℝ) : ℝ := ∑' c : ℕ, echoTerm c τ

theorem echoDelay_nonneg (c : ℕ) : 0 ≤ echoDelay c := by
  rw [echoDelay]
  exact mul_nonneg (by norm_num) (Real.log_natCast_nonneg c)

/-- **Causality.**  The echo train vanishes before time zero. -/
theorem echoKernel_eq_zero_of_nonpos {τ : ℝ} (hτ : τ ≤ 0) : echoKernel τ = 0 := by
  have h : ∀ c : ℕ, echoTerm c τ = 0 := fun c => by
    rw [echoTerm, if_neg (not_lt.mpr (hτ.trans (echoDelay_nonneg c)))]
  simp [echoKernel, h]

/-! ### The bounce -/

/-- The damped bounce, supported on `v > 0`. -/
def bounceWave (w : ℂ) (v : ℝ) : ℂ :=
  if 0 < v then Complex.exp (-w * (v : ℂ)) * ((bounceKernel v : ℝ) : ℂ) else 0

/-- The substitution `x = e^{-v}` carries the positive half-line onto the unit interval. -/
theorem image_exp_neg_Ioi : (fun v : ℝ => Real.exp (-v)) '' Ioi (0 : ℝ) = Ioo (0 : ℝ) 1 := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨Real.exp_pos _, ?_⟩
    rw [Real.exp_lt_one_iff]
    simpa using (mem_Ioi.mp hv)
  · rintro ⟨h0, h1⟩
    refine ⟨-Real.log x, ?_, ?_⟩
    · simpa using (Real.log_neg h0 h1)
    · simp only [neg_neg]
      exact Real.exp_log h0

/-- The Beta integrand in the variable `v`. -/
theorem abs_smul_betaIntegrand_exp_neg (w : ℂ) {v : ℝ} (hv : 0 < v) :
    |-Real.exp (-v)| • (((Real.exp (-v) : ℝ) : ℂ) ^ (w - 1) *
        ((1 : ℂ) - ((Real.exp (-v) : ℝ) : ℂ)) ^ ((1 / 2 : ℂ) - 1))
      = Complex.exp (-w * (v : ℂ)) * ((bounceKernel v : ℝ) : ℂ) := by
  have hpos : 0 < 1 - Real.exp (-v) := by
    have : Real.exp (-v) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith
    linarith
  have hbase : ((1 : ℂ) - ((Real.exp (-v) : ℝ) : ℂ)) = ((1 - Real.exp (-v) : ℝ) : ℂ) := by
    push_cast
    ring
  have hexpo : ((1 / 2 : ℂ) - 1) = ((-(1 / 2) : ℝ) : ℂ) := by
    push_cast
    ring
  have hbounce : ((1 : ℂ) - ((Real.exp (-v) : ℝ) : ℂ)) ^ ((1 / 2 : ℂ) - 1)
      = ((bounceKernel v : ℝ) : ℂ) := by
    rw [hbase, hexpo, bounceKernel, Complex.ofReal_cpow hpos.le]
  have hcpow : ((Real.exp (-v) : ℝ) : ℂ) ^ (w - 1) = Complex.exp ((w - 1) * ((-v : ℝ) : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos (-v)).ne'),
      ← Complex.ofReal_log (Real.exp_pos (-v)).le, Real.log_exp, mul_comm]
  rw [abs_neg, abs_of_pos (Real.exp_pos (-v)), Complex.real_smul, hbounce, hcpow, ← mul_assoc,
    Complex.ofReal_exp, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- **The bounce is integrable and transforms to the Beta function.** -/
theorem integrableOn_and_integral_bounce {w : ℂ} (hw : 0 < w.re) :
    IntegrableOn (fun v : ℝ => Complex.exp (-w * (v : ℂ)) * ((bounceKernel v : ℝ) : ℂ)) (Ioi 0) ∧
      (∫ v in Ioi (0 : ℝ), Complex.exp (-w * (v : ℂ)) * ((bounceKernel v : ℝ) : ℂ))
        = Complex.betaIntegral w (1 / 2) := by
  set g : ℝ → ℂ := fun x => ((x : ℝ) : ℂ) ^ (w - 1) * ((1 : ℂ) - ((x : ℝ) : ℂ)) ^ ((1 / 2 : ℂ) - 1)
    with hg
  have hderiv : ∀ v ∈ Ioi (0 : ℝ),
      HasDerivWithinAt (fun v : ℝ => Real.exp (-v)) (-Real.exp (-v)) (Ioi 0) v := by
    intro v _
    have h := (hasDerivAt_neg v).exp
    rw [mul_neg_one] at h
    exact h.hasDerivWithinAt
  have hinj : InjOn (fun v : ℝ => Real.exp (-v)) (Ioi 0) := by
    intro x _ y _ hxy
    simpa using Real.exp_injective hxy
  have hconv : IntegrableOn g (Ioo (0 : ℝ) 1) := by
    have h := Complex.betaIntegral_convergent (u := w) (v := 1 / 2) hw (by norm_num)
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).mp h
  have hpt : EqOn (fun v : ℝ => |-Real.exp (-v)| • g (Real.exp (-v)))
      (fun v : ℝ => Complex.exp (-w * (v : ℂ)) * ((bounceKernel v : ℝ) : ℂ)) (Ioi 0) :=
    fun v hv => abs_smul_betaIntegrand_exp_neg w (mem_Ioi.mp hv)
  constructor
  · have himage := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hderiv
      hinj g).mp (by rw [image_exp_neg_Ioi]; exact hconv)
    exact himage.congr_fun hpt measurableSet_Ioi
  · have hchange := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj g
    rw [image_exp_neg_Ioi] at hchange
    rw [← setIntegral_congr_fun measurableSet_Ioi hpt, ← hchange,
      HTGeometry.betaIntegral_eq_setIntegral]

theorem bounceWave_eq_indicator (w : ℂ) :
    bounceWave w = (Ioi (0 : ℝ)).indicator
      (fun v : ℝ => Complex.exp (-w * (v : ℂ)) * ((bounceKernel v : ℝ) : ℂ)) := by
  funext v
  by_cases hv : 0 < v
  · simp [bounceWave, hv]
  · simp [bounceWave, hv]

theorem integrable_bounceWave {w : ℂ} (hw : 0 < w.re) : Integrable (bounceWave w) := by
  rw [bounceWave_eq_indicator, integrable_indicator_iff measurableSet_Ioi]
  exact (integrableOn_and_integral_bounce hw).1

theorem integral_bounceWave {w : ℂ} (hw : 0 < w.re) :
    (∫ v, bounceWave w v) = Complex.betaIntegral w (1 / 2) := by
  rw [bounceWave_eq_indicator, integral_indicator measurableSet_Ioi]
  exact (integrableOn_and_integral_bounce hw).2

/-! ### The echoes -/

/-- An echo is the bounce translated by its delay, with a constant coefficient. -/
theorem cexp_mul_echoTerm (w : ℂ) (c : ℕ) (τ : ℝ) :
    Complex.exp (-w * (τ : ℂ)) * ((echoTerm c τ : ℝ) : ℂ)
      = ((echoWeight c : ℝ) : ℂ) * Complex.exp (-w * ((echoDelay c : ℝ) : ℂ))
        * bounceWave w (τ - echoDelay c) := by
  by_cases h : echoDelay c < τ
  · have h' : 0 < τ - echoDelay c := by linarith
    rw [echoTerm, if_pos h, bounceWave, if_pos h']
    have hexp : Complex.exp (-w * (τ : ℂ))
        = Complex.exp (-w * ((echoDelay c : ℝ) : ℂ))
          * Complex.exp (-w * ((τ - echoDelay c : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hexp]
    push_cast
    ring
  · have h' : ¬ 0 < τ - echoDelay c := by linarith
    rw [echoTerm, if_neg h, bounceWave, if_neg h']
    simp

/-- The coefficient of the echo of denominator `c`. -/
def echoCoefficient (w : ℂ) (c : ℕ) : ℂ :=
  ((echoWeight c : ℝ) : ℂ) * Complex.exp (-w * ((echoDelay c : ℝ) : ℂ))

/-- The echo coefficients are the terms of the totient Dirichlet series. -/
theorem echoCoefficient_eq_term (w : ℂ) (c : ℕ) :
    echoCoefficient w c = LSeries.term (fun n : ℕ => (Nat.totient n : ℂ)) (2 * w + 1) c := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · simp [echoCoefficient, echoWeight]
  · have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    rw [LSeries.term_of_ne_zero hc.ne', echoCoefficient, echoWeight, echoDelay,
      Complex.cpow_add _ _ hcC, Complex.cpow_one, Complex.cpow_def_of_ne_zero hcC,
      ← Complex.natCast_log]
    have hexp : Complex.exp (-w * ((2 * Real.log c : ℝ) : ℂ))
        = (Complex.exp (((Real.log c : ℝ) : ℂ) * (2 * w)))⁻¹ := by
      rw [← Complex.exp_neg]
      congr 1
      push_cast
      ring
    rw [hexp]
    push_cast
    field_simp

theorem norm_echoCoefficient_le {w : ℂ} (c : ℕ) :
    ‖echoCoefficient w c‖ ≤ 1 / (c : ℝ) ^ (2 * w.re) := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · simp [echoCoefficient, echoWeight]
    positivity
  · have hc0 : (0 : ℝ) < c := by exact_mod_cast hc
    have hweight : 0 ≤ echoWeight c ∧ echoWeight c ≤ 1 := by
      constructor
      · rw [echoWeight]
        positivity
      · rw [echoWeight, div_le_one hc0]
        exact_mod_cast Nat.totient_le c
    rw [echoCoefficient, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hweight.1, Complex.norm_exp]
    have hre : (-w * ((echoDelay c : ℝ) : ℂ)).re = -(2 * w.re) * Real.log c := by
      rw [Complex.re_mul_ofReal, Complex.neg_re, echoDelay]
      ring
    rw [hre]
    have hrpow : 1 / (c : ℝ) ^ (2 * w.re) = Real.exp (-(2 * w.re) * Real.log c) := by
      rw [Real.rpow_def_of_pos hc0, one_div, ← Real.exp_neg]
      congr 1
      ring
    rw [hrpow]
    exact mul_le_of_le_one_left (Real.exp_pos _).le hweight.2

/-- The Dirichlet series of the totient. -/
theorem lseries_totient {u : ℂ} (hu : 2 < u.re) :
    LSeries (fun n : ℕ => (Nat.totient n : ℂ)) u = riemannZeta (u - 1) / riemannZeta u := by
  have ht := RHTower.TotientMulLSeries.LSeries_totient_mul 1 (by omega) hu
  have hmu : RHTower.TotientMulLSeries.muChi 1 = fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ) := by
    funext n
    by_cases hn : n = 0
    · subst n
      simp [RHTower.TotientMulLSeries.muChi, RHTower.TotientMulMoebius.chi]
    · simp [RHTower.TotientMulLSeries.muChi, RHTower.TotientMulMoebius.chi, hn]
  simp only [one_mul, Nat.totient_one, Nat.cast_one, hmu] at ht
  have hm : LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) u * riemannZeta u = 1 := by
    rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta (by linarith only [hu]), mul_comm]
    exact ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius (by linarith only [hu])
  have hz : riemannZeta u ≠ 0 := by
    intro he
    rw [he, mul_zero] at hm
    exact zero_ne_one hm
  apply (eq_div_iff hz).mpr
  rw [ht]
  linear_combination (riemannZeta (u - 1)) * hm

/-! ### The train -/

/-- **The Laplace transform of the echo train.** -/
theorem integral_cexp_mul_echoKernel {w : ℂ} (hw : 1 / 2 < w.re) :
    (∫ τ : ℝ, Complex.exp (-w * (τ : ℂ)) * ((echoKernel τ : ℝ) : ℂ))
      = Complex.betaIntegral w (1 / 2) * (riemannZeta (2 * w) / riemannZeta (2 * w + 1)) := by
  have hw0 : 0 < w.re := by linarith
  set F : ℕ → ℝ → ℂ := fun c τ => echoCoefficient w c * bounceWave w (τ - echoDelay c) with hF
  have hFeq : ∀ c τ, F c τ = Complex.exp (-w * (τ : ℂ)) * ((echoTerm c τ : ℝ) : ℂ) := by
    intro c τ
    rw [cexp_mul_echoTerm, hF]
    rfl
  have hint : ∀ c, Integrable (F c) := fun c =>
    ((integrable_bounceWave hw0).comp_sub_right (echoDelay c)).const_mul _
  have hnorm : ∀ c, (∫ τ, ‖F c τ‖) = ‖echoCoefficient w c‖ * ∫ v, ‖bounceWave w v‖ := by
    intro c
    have hpt : ∀ τ, ‖F c τ‖ = ‖echoCoefficient w c‖ * ‖bounceWave w (τ - echoDelay c)‖ :=
      fun τ => norm_mul _ _
    simp_rw [hpt]
    rw [integral_const_mul,
      integral_sub_right_eq_self (fun v => ‖bounceWave w v‖) (echoDelay c)]
  have hbase : Summable fun c : ℕ => 1 / (c : ℝ) ^ (2 * w.re) :=
    Real.summable_one_div_nat_rpow.mpr (by linarith)
  have hsum : Summable fun c => ∫ τ, ‖F c τ‖ := by
    simp_rw [hnorm]
    refine Summable.mul_right _ (Summable.of_norm_bounded hbase fun c => ?_)
    rw [norm_norm]
    exact norm_echoCoefficient_le c
  have hHS := hasSum_integral_of_summable_integral_norm hint hsum
  have hval : ∀ c, (∫ τ, F c τ) = echoCoefficient w c * Complex.betaIntegral w (1 / 2) := by
    intro c
    rw [hF]
    simp only
    rw [integral_const_mul, integral_sub_right_eq_self (bounceWave w) (echoDelay c),
      integral_bounceWave hw0]
  have hpoint : ∀ τ : ℝ, Complex.exp (-w * (τ : ℂ)) * ((echoKernel τ : ℝ) : ℂ) = ∑' c, F c τ := by
    intro τ
    rw [echoKernel, Complex.ofReal_tsum, ← tsum_mul_left]
    exact tsum_congr fun c => (hFeq c τ).symm
  have hre : 2 < (2 * w + 1).re := by
    simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, Complex.one_re,
      zero_mul, sub_zero]
    linarith
  simp_rw [hpoint]
  rw [← hHS.tsum_eq]
  simp_rw [hval, echoCoefficient_eq_term]
  rw [tsum_mul_right, mul_comm]
  congr 1
  have hL := lseries_totient hre
  rw [LSeries] at hL
  rw [hL]
  congr 2
  ring

/-- `Γ_ℝ(2w)/Γ_ℝ(2w+1)` is the Beta factor `B(w, 1/2)`. -/
theorem gammaR_div_eq_betaIntegral {w : ℂ} (hw : 0 < w.re) :
    Complex.Gammaℝ (2 * w) / Complex.Gammaℝ (2 * w + 1) = Complex.betaIntegral w (1 / 2) := by
  have hbeta := Complex.Gamma_mul_Gamma_eq_betaIntegral hw (by norm_num : (0 : ℝ) < (1 / 2 : ℂ).re)
  have hhalf : (0 : ℝ) < (w + 1 / 2).re := by
    simp only [Complex.add_re]
    norm_num
    linarith
  have hG : Complex.Gamma (w + 1 / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hhalf
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hsq : (Real.pi : ℂ) ^ (1 / 2 : ℂ) = Complex.Gamma (1 / 2) := by
    rw [Complex.Gamma_one_half_eq]
  have harg1 : 2 * w / 2 = w := by ring
  have harg2 : (2 * w + 1) / 2 = w + 1 / 2 := by ring
  have hexpo : (Real.pi : ℂ) ^ (-(2 * w) / 2) / (Real.pi : ℂ) ^ (-(2 * w + 1) / 2)
      = (Real.pi : ℂ) ^ (1 / 2 : ℂ) := by
    rw [← Complex.cpow_sub _ _ hpi]
    congr 1
    ring
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, harg1, harg2]
  have hbeta' : Complex.betaIntegral w (1 / 2)
      = Complex.Gamma w * Complex.Gamma (1 / 2) / Complex.Gamma (w + 1 / 2) :=
    (eq_div_iff hG).mpr (by rw [hbeta]; ring)
  rw [hbeta', ← hsq, ← hexpo]
  ring

/-- **The echo train transforms to the scattering coefficient.**  For `Re w > 1/2`, the Laplace
transform of the echo train is `Λ(2w)/Λ(2w+1)`, that is `Λ(2s-1)/Λ(2s)` at `s = w + 1/2`. -/
theorem integral_cexp_mul_echoKernel_eq_completed {w : ℂ} (hw : 1 / 2 < w.re) :
    (∫ τ : ℝ, Complex.exp (-w * (τ : ℂ)) * ((echoKernel τ : ℝ) : ℂ))
      = completedRiemannZeta (2 * w) / completedRiemannZeta (2 * w + 1) := by
  have hw0 : 0 < w.re := by linarith
  have hre1 : 0 < (2 * w).re := by
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    linarith
  have hre2 : 0 < (2 * w + 1).re := by
    simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, Complex.one_re,
      zero_mul, sub_zero]
    linarith
  have hne1 : (2 * w) ≠ 0 := fun h => by simp [h] at hre1
  have hne2 : (2 * w + 1) ≠ 0 := fun h => by simp [h] at hre2
  have hG1 : Complex.Gammaℝ (2 * w) ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hre1
  have hG2 : Complex.Gammaℝ (2 * w + 1) ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hre2
  have hz2 : riemannZeta (2 * w + 1) ≠ 0 := by
    refine riemannZeta_ne_zero_of_one_le_re ?_
    simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, Complex.one_re,
      zero_mul, sub_zero]
    linarith
  rw [integral_cexp_mul_echoKernel hw, ← gammaR_div_eq_betaIntegral hw0,
    riemannZeta_def_of_ne_zero hne1, riemannZeta_def_of_ne_zero hne2]
  have hΛ2 : completedRiemannZeta (2 * w + 1) ≠ 0 := by
    intro h
    apply hz2
    rw [riemannZeta_def_of_ne_zero hne2, h, zero_div]
  field_simp

end GaloisForLFunctions.BlackHoleRingdown

end
