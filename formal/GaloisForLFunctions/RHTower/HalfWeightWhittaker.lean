import GaloisForLFunctions.HTGeometry.BesselArgumentDerivative
import GaloisForLFunctions.HTGeometry.BesselOrderRecurrence
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinTwoKBesselMellinProduct

/-!
# The modified Bessel equation and the Mellin transform of `K_ν(t) e^{-t}`

For the Schläfli function `K_ν(s) = ∫_0^∞ e^{-s cosh t} cosh(νt) dt` (`Kb ν s`):

* `hasDerivAt_Kb`, `hasDerivAt_Kb'`: `K_ν' = -K_{ν-1} - (ν/s)K_ν = -K_{ν+1} + (ν/s)K_ν` (argument
  derivative `-(K_{ν+1}+K_{ν-1})/2` and the order recurrence);
* `hasDerivAt_dKb`: the modified Bessel equation `K'' = K - K'/s + (ν²/s²) K`;
* `Wh ν t = √t K_ν(t)`: `hasDerivAt_Wh`, `hasDerivAt_dWh`: the Whittaker equation
  `W'' = (1 + (ν² - 1/4)/t²) W`, i.e. the Maass modal equation with `λ = 1/4 - ν²`.

**`integral_Kb_exp_cpow`**: for `|Re ν| < Re μ`,
`∫_0^∞ K_ν(t) e^{-t} t^{μ-1} dt = 2^{μ-1} Γ(μ) Γ(μ+ν) Γ(μ-ν) / Γ(2μ)`,
by the whole-line Schläfli representation, Fubini (`integrable_mkern`), the Gamma integral
`∫_0^∞ t^{μ-1} e^{-(1+cosh u)t} dt = Γ(μ)(1+cosh u)^{-μ}`, `1 + cosh u = 2cosh²(u/2)`, and the
hyperbolic Beta transform `∫ cosh(v)^{-2μ} e^{2νv} dv = 2^{2μ-1} Γ(μ+ν)Γ(μ-ν)/Γ(2μ)`.
This is the archimedean factor of Shimura's integral: its pole at `μ = ν` is the forced zero.
-/

open Real Complex Filter Topology MeasureTheory Set

namespace GaloisForLFunctions.RHTower.HalfWeight

open GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### The modified Bessel equation for the Schläfli `K` -/

/-- `K_ν(s)` as a function of the argument. -/
def Kb (ν : ℂ) (s : ℝ) : ℂ := modifiedBesselKOrder s ν

/-- `K_ν' = -K_{ν-1} - (ν/s) K_ν`. -/
theorem hasDerivAt_Kb {s : ℝ} (hs : 0 < s) (ν : ℂ) :
    HasDerivAt (Kb ν) (-Kb (ν - 1) s - ν / s * Kb ν s) s := by
  have h := RHTower.d4BM_hasDerivAt_modifiedBesselKOrder_argument hs ν
  refine h.congr_deriv ?_
  have hr := modifiedBesselKOrder_add_one hs ν
  simp only [Kb]
  rw [hr]
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  field_simp
  ring

/-- `K_ν' = -K_{ν+1} + (ν/s) K_ν`. -/
theorem hasDerivAt_Kb' {s : ℝ} (hs : 0 < s) (ν : ℂ) :
    HasDerivAt (Kb ν) (-Kb (ν + 1) s + ν / s * Kb ν s) s := by
  refine (hasDerivAt_Kb hs ν).congr_deriv ?_
  have hr := modifiedBesselKOrder_add_one hs ν
  simp only [Kb]
  rw [hr]
  ring

/-- The first argument derivative as a function. -/
def dKb (ν : ℂ) (s : ℝ) : ℂ := -Kb (ν - 1) s - ν / s * Kb ν s

/-- **The modified Bessel equation**: `K'' = K - K'/s + (ν²/s²) K`. -/
theorem hasDerivAt_dKb {s : ℝ} (hs : 0 < s) (ν : ℂ) :
    HasDerivAt (dKb ν) (Kb ν s - dKb ν s / s + ν ^ 2 / (s : ℂ) ^ 2 * Kb ν s) s := by
  have h1 := hasDerivAt_Kb' hs (ν - 1)
  have h2 := hasDerivAt_Kb hs ν
  have hinv : HasDerivAt (fun q : ℝ => ν / (q : ℂ)) (-(ν / (s : ℂ) ^ 2)) s := by
    have := ((hasDerivAt_id s).ofReal_comp).inv (by exact_mod_cast hs.ne' : ((id s : ℝ) : ℂ) ≠ 0)
    have := this.const_mul ν
    refine this.congr_deriv ?_
    simp only [id, Complex.ofReal_one]
    field_simp
  have h := (h1.neg).sub (hinv.mul h2)
  refine h.congr_deriv ?_
  simp only [dKb, sub_add_cancel]
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  field_simp
  ring

/-! ### The Whittaker function `W(t) = √t K_ν(t)` -/

/-- `W_ν(t) = √t K_ν(t)`. -/
def Wh (ν : ℂ) (t : ℝ) : ℂ := (Real.sqrt t : ℂ) * Kb ν t

/-- `W' = (1/(2t)) W + √t K'`. -/
def dWh (ν : ℂ) (t : ℝ) : ℂ := (Real.sqrt t : ℂ) * (Kb ν t / (2 * t) + dKb ν t)

theorem hasDerivAt_sqrt_ofReal {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun q : ℝ => (Real.sqrt q : ℂ)) ((Real.sqrt t : ℂ) / (2 * t)) t := by
  have h := (Real.hasDerivAt_sqrt ht.ne').ofReal_comp
  refine h.congr_deriv ?_
  have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.2 ht).ne'
  have hst : (Real.sqrt t : ℂ) * Real.sqrt t = t := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt ht.le]
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hs0 : (Real.sqrt t : ℂ) ≠ 0 := by exact_mod_cast hs
  push_cast
  field_simp
  rw [← hst]
  ring

theorem hasDerivAt_Wh {t : ℝ} (ht : 0 < t) (ν : ℂ) : HasDerivAt (Wh ν) (dWh ν t) t := by
  have h := (hasDerivAt_sqrt_ofReal ht).mul (hasDerivAt_Kb ht ν)
  refine h.congr_deriv ?_
  simp only [dWh, dKb]
  ring

/-- **The Whittaker equation**: `W'' = (1 + (ν² - 1/4)/t²) W`. -/
theorem hasDerivAt_dWh {t : ℝ} (ht : 0 < t) (ν : ℂ) :
    HasDerivAt (dWh ν) ((1 + (ν ^ 2 - 1 / 4) / (t : ℂ) ^ 2) * Wh ν t) t := by
  have hK := hasDerivAt_Kb ht ν
  have hdK := hasDerivAt_dKb ht ν
  have hq : HasDerivAt (fun q : ℝ => Kb ν q / (2 * q)) (((-Kb (ν - 1) t - ν / t * Kb ν t) * (2 * t) -
      Kb ν t * 2) / (2 * t) ^ 2) t := by
    have h2 : HasDerivAt (fun q : ℝ => (2 * (q : ℂ))) 2 t := by
      simpa using ((hasDerivAt_id t).ofReal_comp).const_mul (2 : ℂ)
    exact hK.div h2 (by have : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
                        exact mul_ne_zero two_ne_zero this)
  have h := (hasDerivAt_sqrt_ofReal ht).mul (hq.add hdK)
  refine h.congr_deriv ?_
  simp only [Pi.add_apply, dKb, Wh]
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  field_simp
  ring


/-! ### The Mellin transform of `K_ν(t) e^{-t}` -/

/-- `1 + cosh u = 2 cosh²(u/2)`. -/
theorem one_add_cosh_eq (u : ℝ) : 1 + Real.cosh u = 2 * Real.cosh (u / 2) ^ 2 := by
  have h := Real.cosh_two_mul (u / 2)
  rw [show 2 * (u / 2) = u by ring, Real.cosh_sq] at h
  rw [h, Real.cosh_sq]; ring

/-- `(1/(1 + cosh u))^μ = 2^{-μ} cosh(u/2)^{-2μ}`. -/
theorem one_div_one_add_cosh_cpow (u : ℝ) (μ : ℂ) :
    ((1 / (1 + Real.cosh u) : ℝ) : ℂ) ^ μ = (2 : ℂ) ^ (-μ) * ((Real.cosh (u / 2) : ℝ) : ℂ) ^ (-(2 * μ)) := by
  have hc : 0 < Real.cosh (u / 2) := Real.cosh_pos _
  have hp : 0 < 1 / (1 + Real.cosh u) := by have := Real.cosh_pos u; positivity
  have e1 : 1 / (1 + Real.cosh u) = (2 * Real.cosh (u / 2) ^ 2)⁻¹ := by rw [one_add_cosh_eq, one_div]
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hp.ne'),
    Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hc.ne'), ← Complex.exp_add]
  congr 1
  rw [← Complex.ofReal_log hp.le, ← Complex.ofReal_log hc.le,
    show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_log (by norm_num), e1,
    Real.log_inv, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  push_cast
  ring

/-- The Mellin–Schläfli integrand `exp(-t cosh u + νu) e^{-t} t^{μ-1}`. -/
def mkern (μ ν : ℂ) (t u : ℝ) : ℂ :=
  RHTower.besselOrderExpKernel t ν u * ((Real.exp (-t) : ℝ) : ℂ) * (t : ℂ) ^ (μ - 1)

theorem mkern_eq (μ ν : ℂ) (t u : ℝ) :
    mkern μ ν t u = Complex.exp (ν * u) * ((t : ℂ) ^ (μ - 1) *
      Complex.exp (-(((1 + Real.cosh u : ℝ) : ℂ) * t))) := by
  unfold mkern RHTower.besselOrderExpKernel
  rw [Complex.ofReal_exp, ← Complex.ofReal_cosh]
  rw [show (((1 + Real.cosh u : ℝ)) : ℂ) = 1 + (Real.cosh u : ℂ) by push_cast; ring]
  rw [show Complex.exp (-(t : ℂ) * (Real.cosh u : ℂ) + ν * u) * Complex.exp ((-t : ℝ) : ℂ) =
      Complex.exp (ν * u) * Complex.exp (-((1 + (Real.cosh u : ℂ)) * t)) by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring]
  ring

theorem norm_mkern {μ ν : ℂ} {t : ℝ} (ht : 0 < t) (u : ℝ) :
    ‖mkern μ ν t u‖ = Real.exp (ν.re * u) * (t ^ (μ.re - 1) * Real.exp (-((1 + Real.cosh u) * t))) := by
  rw [mkern_eq, norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp,
    Complex.norm_cpow_eq_rpow_re_of_pos ht]
  simp

/-- The `t`-integral: `∫_0^∞ exp(-t cosh u + νu) e^{-t} t^{μ-1} dt = e^{νu} Γ(μ) (1 + cosh u)^{-μ}`. -/
theorem integral_mkern_t {μ : ℂ} (hμ : 0 < μ.re) (ν : ℂ) (u : ℝ) :
    ∫ t in Ioi (0 : ℝ), mkern μ ν t u =
      Complex.exp (ν * u) * (((1 / (1 + Real.cosh u) : ℝ) : ℂ) ^ μ * Complex.Gamma μ) := by
  have hr : 0 < 1 + Real.cosh u := by have := Real.cosh_pos u; linarith
  simp_rw [mkern_eq]
  rw [integral_const_mul, Complex.integral_cpow_mul_exp_neg_mul_Ioi hμ hr]
  push_cast
  ring

theorem integral_norm_mkern_t {μ : ℂ} (hμ : 0 < μ.re) (ν : ℂ) (u : ℝ) :
    ∫ t in Ioi (0 : ℝ), ‖mkern μ ν t u‖ =
      Real.exp (ν.re * u) * ((1 / (1 + Real.cosh u)) ^ μ.re * Real.Gamma μ.re) := by
  have hr : 0 < 1 + Real.cosh u := by have := Real.cosh_pos u; linarith
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => norm_mkern ht u), integral_const_mul,
    Real.integral_rpow_mul_exp_neg_mul_Ioi hμ hr]

theorem continuousOn_mkern_t (μ ν : ℂ) (u : ℝ) : ContinuousOn (fun t => mkern μ ν t u) (Ioi 0) := by
  intro t ht
  have e : (fun t => mkern μ ν t u) = fun t : ℝ => Complex.exp (ν * u) * ((t : ℂ) ^ (μ - 1) *
      Complex.exp (-(((1 + Real.cosh u : ℝ) : ℂ) * t))) := funext fun t => mkern_eq μ ν t u
  rw [e]
  refine ContinuousAt.continuousWithinAt ?_
  have hc : ContinuousAt (fun t : ℝ => (t : ℂ) ^ (μ - 1)) t :=
    Complex.continuous_ofReal.continuousAt.cpow continuousAt_const
      (Complex.ofReal_mem_slitPlane.2 ht)
  exact continuousAt_const.mul (hc.mul (by fun_prop))

theorem integrableOn_mkern_t {μ : ℂ} (hμ : 0 < μ.re) (ν : ℂ) (u : ℝ) :
    IntegrableOn (fun t => mkern μ ν t u) (Ioi 0) := by
  have hr : 0 < 1 + Real.cosh u := by have := Real.cosh_pos u; linarith
  have hI := (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := μ.re - 1) (b := 1 + Real.cosh u)
    (by linarith) le_rfl hr).const_mul (Real.exp (ν.re * u))
  refine hI.mono' ?_ ?_
  · exact (continuousOn_mkern_t μ ν u).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_mkern ht, Real.rpow_one]; ring_nf; exact le_rfl

theorem integrable_mkern {μ ν : ℂ} (h : |ν.re| < μ.re) :
    Integrable (Function.uncurry fun t u => mkern μ ν t u) ((volume.restrict (Ioi 0)).prod volume) := by
  have hμ : 0 < μ.re := lt_of_le_of_lt (abs_nonneg _) h
  have hmeas : AEStronglyMeasurable (Function.uncurry fun t u => mkern μ ν t u)
      ((volume.restrict (Ioi 0)).prod volume) := by
    refine Measurable.aestronglyMeasurable ?_
    unfold Function.uncurry mkern RHTower.besselOrderExpKernel
    fun_prop
  rw [integrable_prod_iff' hmeas]
  refine ⟨Eventually.of_forall fun u => integrableOn_mkern_t hμ ν u, ?_⟩
  simp only [Function.uncurry_apply_pair]
  simp_rw [integral_norm_mkern_t hμ ν]
  have hc := RHTower.integrable_complex_cosh_cpow_neg_mul_exp (s := (μ.re : ℂ)) (a := (ν.re : ℂ))
    (by simpa using h)
  have hc' := (hc.norm.mul_const (Real.Gamma μ.re))
  refine hc'.mono' ?_ (Eventually.of_forall fun u => ?_)
  · refine Continuous.aestronglyMeasurable ?_
    have : Continuous fun u : ℝ => (1 / (1 + Real.cosh u)) ^ μ.re := by
      refine Continuous.rpow_const (by
        have : ∀ u, 1 + Real.cosh u ≠ 0 := fun u => by have := Real.cosh_pos u; linarith
        fun_prop (disch := exact this _)) fun u => Or.inr hμ.le
    fun_prop
  · have hcu := Real.cosh_pos u
    have hr : 0 < 1 + Real.cosh u := by linarith
    have hG := Real.Gamma_pos_of_pos hμ
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    rw [norm_mul, Complex.norm_exp, Complex.norm_cpow_eq_rpow_re_of_pos hcu]
    simp only [Complex.neg_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero]
    have h1 : (1 / (1 + Real.cosh u)) ^ μ.re ≤ Real.cosh u ^ (-μ.re) := by
      rw [Real.rpow_neg hcu.le, ← Real.inv_rpow hcu.le, one_div]
      exact Real.rpow_le_rpow (by positivity) (inv_anti₀ hcu (by linarith)) hμ.le
    calc Real.exp (ν.re * u) * ((1 / (1 + Real.cosh u)) ^ μ.re * Real.Gamma μ.re)
        ≤ Real.exp (ν.re * u) * (Real.cosh u ^ (-μ.re) * Real.Gamma μ.re) := by gcongr
      _ = _ := by ring

/-- **The Mellin transform of `K_ν(t) e^{-t}`**: for `|Re ν| < Re μ`,
`∫_0^∞ K_ν(t) e^{-t} t^{μ-1} dt = 2^{μ-1} Γ(μ) Γ(μ+ν) Γ(μ-ν) / Γ(2μ)`. -/
theorem integral_Kb_exp_cpow {μ ν : ℂ} (h : |ν.re| < μ.re) :
    ∫ t in Ioi (0 : ℝ), Kb ν t * ((Real.exp (-t) : ℝ) : ℂ) * (t : ℂ) ^ (μ - 1) =
      (2 : ℂ) ^ (μ - 1) * Complex.Gamma μ * Complex.Gamma (μ + ν) * Complex.Gamma (μ - ν) /
        Complex.Gamma (2 * μ) := by
  have hμ : 0 < μ.re := lt_of_le_of_lt (abs_nonneg _) h
  have h1 : ∀ t ∈ Ioi (0 : ℝ), Kb ν t * ((Real.exp (-t) : ℝ) : ℂ) * (t : ℂ) ^ (μ - 1) =
      (1 / 2 : ℂ) * ∫ u, mkern μ ν t u := by
    intro t ht
    have hK := RHTower.integral_besselOrderExpKernel_eq_two_mul (show 0 < t from ht) ν
    unfold mkern
    rw [integral_mul_const, integral_mul_const, hK, Kb]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi h1, integral_const_mul,
    integral_integral_swap (integrable_mkern h)]
  simp_rw [integral_mkern_t hμ ν, one_div_one_add_cosh_cpow]
  -- substitute `u = 2v`
  have hsub := Measure.integral_comp_mul_left (fun u : ℝ => Complex.exp (ν * u) *
    ((2 : ℂ) ^ (-μ) * ((Real.cosh (u / 2) : ℝ) : ℂ) ^ (-(2 * μ)) * Complex.Gamma μ)) 2
  have e2 : ∀ v : ℝ, Complex.exp (ν * ((2 * v : ℝ) : ℂ)) * ((2 : ℂ) ^ (-μ) *
      ((Real.cosh (2 * v / 2) : ℝ) : ℂ) ^ (-(2 * μ)) * Complex.Gamma μ) =
      (2 : ℂ) ^ (-μ) * Complex.Gamma μ *
        (((Real.cosh v : ℝ) : ℂ) ^ (-(2 * μ)) * Complex.exp ((2 * ν) * (v : ℂ))) := by
    intro v
    rw [show 2 * v / 2 = v by ring]
    push_cast
    ring_nf
  simp_rw [e2, integral_const_mul] at hsub
  have hcorp := RHTower.integral_complex_cosh_cpow_neg_mul_exp (s := 2 * μ) (a := 2 * ν)
    (by simp; linarith [neg_abs_le ν.re, le_abs_self ν.re])
    (by simp; linarith [neg_abs_le ν.re, le_abs_self ν.re])
  rw [hcorp] at hsub
  have hint : (∫ u : ℝ, Complex.exp (ν * u) *
      ((2 : ℂ) ^ (-μ) * ((Real.cosh (u / 2) : ℝ) : ℂ) ^ (-(2 * μ)) * Complex.Gamma μ)) =
      2 * ((2 : ℂ) ^ (-μ) * Complex.Gamma μ * ((2 : ℂ) ^ (2 * μ - 1) *
        (Complex.Gamma ((2 * μ + 2 * ν) / 2) * Complex.Gamma ((2 * μ - 2 * ν) / 2) /
          Complex.Gamma (2 * μ)))) := by
    rw [hsub]
    norm_num
    ring
  rw [show (fun u : ℝ => Complex.exp (ν * u) * (((2 : ℂ) ^ (-μ) *
      ((Real.cosh (u / 2) : ℝ) : ℂ) ^ (-(2 * μ))) * Complex.Gamma μ)) =
      fun u : ℝ => Complex.exp (ν * u) *
        ((2 : ℂ) ^ (-μ) * ((Real.cosh (u / 2) : ℝ) : ℂ) ^ (-(2 * μ)) * Complex.Gamma μ) from rfl, hint]
  rw [show (2 * μ + 2 * ν) / 2 = μ + ν by ring, show (2 * μ - 2 * ν) / 2 = μ - ν by ring]
  have h2 : (2 : ℂ) ^ (-μ) * (2 : ℂ) ^ (2 * μ - 1) = (2 : ℂ) ^ (μ - 1) := by
    rw [← Complex.cpow_add _ _ (by norm_num)]; congr 1; ring
  have hG : Complex.Gamma (2 * μ) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  field_simp
  rw [← h2]
  ring
