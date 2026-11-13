import GaloisForLFunctions.CompactHyperbolicSurfaces.ResolventKernelBounds
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# The difference kernel on the diagonal

`D_{a,b}(0) = (1/2π) Σ_{k ≥ 0} (1/(a + k) − 1/(b + k))` (`diffKernel_zero`).

With `t = sinh²(u/2)`: `ρ(t) = e^{−u/2}`, `√(t(1 + t)) = sinh(u/2) cosh(u/2)` and
`dt = sinh(u/2) cosh(u/2) du`, so
`4π D(0) = ∫_0^∞ (ρ^{2a−1} − ρ^{2b−1}) dt/(t√(1+t)) = ∫_0^∞ (e^{−(a−½)u} − e^{−(b−½)u}) du / sinh(u/2)`,
and `1/sinh(u/2) = 2e^{−u/2} Σ_k e^{−ku}` gives `2 Σ_k (1/(a+k) − 1/(b+k))`.
-/

open MeasureTheory Set Real
open scoped ENNReal

namespace GaloisForLFunctions.CompactHyperbolicSurfaces

noncomputable section

/-- The substitution `u ↦ sinh²(u/2)`. -/
def sinhSqHalf (u : ℝ) : ℝ := sinh (u / 2) ^ 2

theorem hasDerivAt_sinhSqHalf (u : ℝ) :
    HasDerivAt sinhSqHalf (sinh (u / 2) * cosh (u / 2)) u := by
  have h1 : HasDerivAt (fun u : ℝ => u / 2) (1 / 2) u := (hasDerivAt_id u).div_const 2
  have h2 : HasDerivAt (fun u => sinh (u / 2)) (cosh (u / 2) * (1 / 2)) u :=
    (Real.hasDerivAt_sinh (u / 2)).comp u h1
  have h3 := h2.pow 2
  refine h3.congr_deriv ?_
  rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
  push_cast
  ring

theorem sinhSqHalf_strictMonoOn : StrictMonoOn sinhSqHalf (Ioi 0) := by
  intro u hu v hv huv
  have hsu : 0 < sinh (u / 2) := Real.sinh_pos_iff.mpr (by have : (0:ℝ) < u := hu; linarith)
  have hlt : sinh (u / 2) < sinh (v / 2) := Real.sinh_strictMono (by linarith)
  unfold sinhSqHalf
  nlinarith

theorem image_sinhSqHalf : sinhSqHalf '' Ioi 0 = Ioi 0 := by
  ext t
  constructor
  · rintro ⟨u, hu, rfl⟩
    have : 0 < sinh (u / 2) := Real.sinh_pos_iff.mpr (by have : (0:ℝ) < u := hu; linarith)
    exact pow_pos this 2
  · intro ht
    have ht' : (0 : ℝ) < t := ht
    refine ⟨2 * arsinh (√t), by
      show (0 : ℝ) < 2 * arsinh (√t)
      have := Real.arsinh_pos_iff.mpr (Real.sqrt_pos.mpr ht'); linarith, ?_⟩
    simp only [sinhSqHalf]
    rw [mul_div_cancel_left₀ _ two_ne_zero, Real.sinh_arsinh, Real.sq_sqrt ht'.le]

theorem rho_sinhSqHalf {u : ℝ} (hu : 0 < u) : rho (sinhSqHalf u) = exp (-(u / 2)) := by
  have hs : 0 < sinh (u / 2) := Real.sinh_pos_iff.mpr (by linarith)
  have hc : 0 < cosh (u / 2) := Real.cosh_pos _
  rw [rho, sinhSqHalf, show 1 + sinh (u / 2) ^ 2 = cosh (u / 2) ^ 2 by rw [Real.cosh_sq]; ring,
    Real.sqrt_sq hc.le, Real.sqrt_sq hs.le, Real.cosh_sub_sinh]

theorem greenDensity_sinhSqHalf {s u : ℝ} (hu : 0 < u) :
    greenDensity s (sinhSqHalf u) = exp (-((s - 1 / 2) * u)) / (sinh (u / 2) * cosh (u / 2)) := by
  have hs : 0 < sinh (u / 2) := Real.sinh_pos_iff.mpr (by linarith)
  have hc : 0 < cosh (u / 2) := Real.cosh_pos _
  rw [greenDensity, rho_sinhSqHalf hu, Real.rpow_def_of_pos (exp_pos _), Real.log_exp, sinhSqHalf,
    show sinh (u / 2) ^ 2 * (1 + sinh (u / 2) ^ 2) = (sinh (u / 2) * cosh (u / 2)) ^ 2 by
      rw [mul_pow, Real.cosh_sq]; ring,
    Real.sqrt_sq (by positivity)]
  congr 2
  ring

/-- The substituted integrand. -/
theorem substituted_integrand {a b u : ℝ} (hu : 0 < u) :
    sinh (u / 2) * cosh (u / 2) * (greenDiff a b (sinhSqHalf u) * (√(sinhSqHalf u))⁻¹) =
      (exp (-((a - 1 / 2) * u)) - exp (-((b - 1 / 2) * u))) / sinh (u / 2) := by
  have hs : 0 < sinh (u / 2) := Real.sinh_pos_iff.mpr (by linarith)
  have hc : 0 < cosh (u / 2) := Real.cosh_pos _
  rw [greenDiff, greenDensity_sinhSqHalf hu, greenDensity_sinhSqHalf hu, sinhSqHalf,
    Real.sqrt_sq hs.le]
  field_simp

/-- **Geometric expansion.**  For `u > 0`,
`(e^{−(a−½)u} − e^{−(b−½)u})/sinh(u/2) = Σ_k 2(e^{−(a+k)u} − e^{−(b+k)u})`. -/
theorem hasSum_substituted {a b u : ℝ} (hu : 0 < u) :
    HasSum (fun k : ℕ => 2 * (exp (-((a + k) * u)) - exp (-((b + k) * u))))
      ((exp (-((a - 1 / 2) * u)) - exp (-((b - 1 / 2) * u))) / sinh (u / 2)) := by
  have hr0 : 0 ≤ exp (-u) := (exp_pos _).le
  have hr1 : exp (-u) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hg := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (2 * (exp (-(a * u)) - exp (-(b * u))))
  have hterm : ∀ k : ℕ, 2 * (exp (-(a * u)) - exp (-(b * u))) * exp (-u) ^ k =
      2 * (exp (-((a + k) * u)) - exp (-((b + k) * u))) := by
    intro k
    have e1 : exp (-(a * u)) * exp (-u) ^ k = exp (-((a + k) * u)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; ring_nf
    have e2 : exp (-(b * u)) * exp (-u) ^ k = exp (-((b + k) * u)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; ring_nf
    rw [← e1, ← e2]; ring
  have hval : 2 * (exp (-(a * u)) - exp (-(b * u))) * (1 - exp (-u))⁻¹ =
      (exp (-((a - 1 / 2) * u)) - exp (-((b - 1 / 2) * u))) / sinh (u / 2) := by
    have hs : 0 < sinh (u / 2) := Real.sinh_pos_iff.mpr (by linarith)
    have h1 : 0 < 1 - exp (-u) := by linarith
    have hsinh : sinh (u / 2) = exp (u / 2) * (1 - exp (-u)) / 2 := by
      rw [Real.sinh_eq, mul_sub, mul_one, ← Real.exp_add]
      ring_nf
    rw [hsinh]
    have he : exp (-((a - 1 / 2) * u)) = exp (-(a * u)) * exp (u / 2) := by
      rw [← Real.exp_add]; ring_nf
    have he' : exp (-((b - 1 / 2) * u)) = exp (-(b * u)) * exp (u / 2) := by
      rw [← Real.exp_add]; ring_nf
    rw [he, he']
    have : exp (u / 2) ≠ 0 := (exp_pos _).ne'
    field_simp
  rw [← hval]
  convert hg using 1
  funext k
  exact (hterm k).symm

theorem lintegral_exp_sub_exp {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d) :
    ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (2 * (exp (-(c * u)) - exp (-(d * u)))) =
      ENNReal.ofReal (2 * (1 / c - 1 / d)) := by
  have hd : 0 < d := lt_of_lt_of_le hc hcd
  have hic := (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hc) 0)
  have hid := (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hd) 0)
  have hint : IntegrableOn (fun u => 2 * (exp (-(c * u)) - exp (-(d * u)))) (Ioi 0) := by
    have h := (hic.sub hid).const_mul 2
    simpa only [neg_mul, Pi.sub_apply] using h
  rw [← ofReal_integral_eq_lintegral_ofReal hint]
  · congr 1
    rw [integral_const_mul, integral_sub (by simpa only [neg_mul] using hic.integrable)
      (by simpa only [neg_mul] using hid.integrable)]
    have e1 : ∫ u in Ioi (0 : ℝ), exp (-(c * u)) = 1 / c := by
      have := integral_exp_mul_Ioi (neg_lt_zero.mpr hc) 0
      simp only [neg_mul, mul_zero, exp_zero] at this
      rw [this]; field_simp
    have e2 : ∫ u in Ioi (0 : ℝ), exp (-(d * u)) = 1 / d := by
      have := integral_exp_mul_Ioi (neg_lt_zero.mpr hd) 0
      simp only [neg_mul, mul_zero, exp_zero] at this
      rw [this]; field_simp
    rw [e1, e2]
  · refine (ae_restrict_mem measurableSet_Ioi).mono fun u hu => ?_
    have hu' : (0 : ℝ) < u := hu
    have : exp (-(d * u)) ≤ exp (-(c * u)) := Real.exp_le_exp.mpr (by nlinarith)
    show (0 : ℝ) ≤ 2 * (exp (-(c * u)) - exp (-(d * u)))
    linarith

/-- **The diagonal value of the difference kernel.** -/
theorem diffKernel_zero {a b : ℝ} (ha : 1 / 2 < a) (hab : a ≤ b) :
    HasSum (fun k : ℕ => 1 / (2 * π) * (1 / (a + k) - 1 / (b + k))) (diffKernel a b 0) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  -- nonnegative integrand
  have hnn : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ greenDiff a b t * (√t)⁻¹ := fun t ht =>
    mul_nonneg (greenDiff_nonneg hab (le_of_lt ht)) (inv_nonneg.mpr (Real.sqrt_nonneg _))
  have hmeas : Measurable fun t => greenDiff a b t * (√t)⁻¹ :=
    ((measurable_greenDensity a).sub (measurable_greenDensity b)).mul
      (Real.continuous_sqrt.measurable.inv)
  have hI : ∫ t in Ioi (0 : ℝ), greenDiff a b t * (√t)⁻¹ =
      (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (greenDiff a b t * (√t)⁻¹)).toReal :=
    integral_eq_lintegral_of_nonneg_ae ((ae_restrict_mem measurableSet_Ioi).mono hnn)
      hmeas.aestronglyMeasurable
  -- substitution `t = sinh²(u/2)`
  have hsub : ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (greenDiff a b t * (√t)⁻¹) =
      ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal
        ((exp (-((a - 1 / 2) * u)) - exp (-((b - 1 / 2) * u))) / sinh (u / 2)) := by
    conv_lhs => rw [← image_sinhSqHalf]
    rw [lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
      (fun u _ => (hasDerivAt_sinhSqHalf u).hasDerivWithinAt) sinhSqHalf_strictMonoOn.injOn]
    refine setLIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu' : (0 : ℝ) < u := hu
    have hs : 0 < sinh (u / 2) := Real.sinh_pos_iff.mpr (by linarith)
    rw [abs_of_pos (mul_pos hs (Real.cosh_pos _)), ← ENNReal.ofReal_mul (by positivity),
      substituted_integrand hu']
  -- expand
  have hexp : ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal
        ((exp (-((a - 1 / 2) * u)) - exp (-((b - 1 / 2) * u))) / sinh (u / 2)) =
      ∑' k : ℕ, ENNReal.ofReal (2 * (1 / (a + k) - 1 / (b + k))) := by
    have hterm_nn : ∀ (u : ℝ), 0 < u → ∀ k : ℕ,
        0 ≤ 2 * (exp (-((a + k) * u)) - exp (-((b + k) * u))) := by
      intro u hu k
      have : exp (-((b + k) * u)) ≤ exp (-((a + k) * u)) :=
        Real.exp_le_exp.mpr (by nlinarith)
      linarith
    rw [← tsum_congr fun k : ℕ => lintegral_exp_sub_exp (by positivity : 0 < a + k)
      (by linarith : a + k ≤ b + k)]
    rw [← lintegral_tsum fun k => by fun_prop]
    refine setLIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu' : (0 : ℝ) < u := hu
    rw [← (hasSum_substituted hu').tsum_eq, ENNReal.ofReal_tsum_of_nonneg (hterm_nn u hu')
      (hasSum_substituted hu').summable]
  -- assemble
  have hsum : Summable fun k : ℕ => 2 * (1 / (a + k) - 1 / (b + k)) := by
    have hfin : ∑' k : ℕ, ENNReal.ofReal (2 * (1 / (a + k) - 1 / (b + k))) ≠ ∞ := by
      rw [← hexp, ← hsub]
      have hint : IntegrableOn (fun t => greenDiff a b t * (√t)⁻¹) (Ioi 0) := by
        have := integrableOn_greenDiff_shift ha hab 0
        simpa only [max_self, zero_add] using this
      exact (hasFiniteIntegral_iff_ofReal ((ae_restrict_mem measurableSet_Ioi).mono hnn)).mp
        hint.2 |>.ne
    have hnn' : ∀ k : ℕ, 0 ≤ 2 * (1 / (a + k) - 1 / (b + k)) := fun k => by
      have : 1 / (b + k) ≤ 1 / (a + k) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      linarith
    have := ENNReal.summable_toReal hfin
    exact this.congr fun k => ENNReal.toReal_ofReal (hnn' k)
  have hval : diffKernel a b 0 = 1 / (4 * π) * ∑' k : ℕ, 2 * (1 / (a + k) - 1 / (b + k)) := by
    rw [diffKernel, max_self]
    simp only [zero_add]
    rw [hI, hsub, hexp, ← ENNReal.ofReal_tsum_of_nonneg (fun k => by
        have : 1 / (b + k) ≤ 1 / (a + k) :=
          one_div_le_one_div_of_le (by positivity) (by linarith)
        linarith) hsum,
      ENNReal.toReal_ofReal (tsum_nonneg fun k => by
        have : 1 / (b + k) ≤ 1 / (a + k) :=
          one_div_le_one_div_of_le (by positivity) (by linarith)
        linarith)]
  rw [hval, ← tsum_mul_left]
  have hs2 := hsum.mul_left (1 / (4 * π))
  have hf : (fun k : ℕ => 1 / (2 * π) * (1 / (a + k) - 1 / (b + k))) =
      fun k => 1 / (4 * π) * (2 * (1 / (a + k) - 1 / (b + k))) := by
    funext k; ring
  rw [hf]
  exact hs2.hasSum

end

end GaloisForLFunctions.CompactHyperbolicSurfaces
