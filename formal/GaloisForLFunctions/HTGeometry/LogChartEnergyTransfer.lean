import GaloisForLFunctions.HTGeometry.PhysicalLogChart
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# The chart converts spatial energy into exponentially weighted log energy

Under `r = e^{-L}` a spatial derivative picks up the Jacobian twice and the measure gives one back:

`∫ ‖∂_r u‖² dr = ∫ e^{L} ‖F'(L)‖² dL`,   `u(r) = F(−log r)`.

So the spatial `H¹` norm is not the boundary-log `H¹` norm: it is the boundary-log norm of the
derivative weighted by `e^{L}`, that is, a weight of exponent `1/2` on the derivative itself.  A
profile whose derivative decays at any fixed polynomial rate therefore lies in `H¹(dL)` and *not* in
`H¹(dr)`, because the exponential beats every power.  The two statements below are the identity and
that separation.
-/

open Filter MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ## The chart on a terminal ray -/

theorem injOn_logChart_Ioi (L₀ : ℝ) : InjOn logChart (Ioi L₀) := by
  intro a _ b _ hab
  have := Real.exp_injective hab
  linarith

theorem image_logChart_Ioi' (L₀ : ℝ) :
    logChart '' Ioi L₀ = Ioo (0 : ℝ) (Real.exp (-L₀)) := by
  ext s
  constructor
  · rintro ⟨L, hL, rfl⟩
    exact ⟨Real.exp_pos _, Real.exp_lt_exp.mpr (by simpa using hL)⟩
  · rintro ⟨hs0, hs1⟩
    refine ⟨-Real.log s, ?_, ?_⟩
    · simp only [mem_Ioi]
      have : Real.log s < -L₀ := by
        rw [← Real.log_exp (-L₀)]
        exact Real.log_lt_log hs0 hs1
      linarith
    · rw [logChart, neg_neg, Real.exp_log hs0]

/-! ## The chart derivative of a transported profile -/

/-- The spatial derivative of the transported profile is the chart Jacobian times the log
derivative. -/
theorem hasDerivAt_logTransport {F F' : ℝ → X} (hF : ∀ L : ℝ, HasDerivAt F (F' L) L)
    {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun x : ℝ => F (-Real.log x)) ((-r⁻¹) • F' (-Real.log r)) r := by
  have hlog : HasDerivAt (fun x : ℝ => -Real.log x) (-r⁻¹) r :=
    (Real.hasDerivAt_log (ne_of_gt hr)).neg
  exact (hF (-Real.log r)).scomp r hlog

/-! ## The energy identity -/

/-- **The chart energy identity.**  The spatial squared-derivative mass on the punctured interval
is the exponentially weighted boundary-log mass on the terminal ray. -/
theorem integral_sq_spatial_eq_integral_exp_weighted (F' : ℝ → X) (L₀ : ℝ) :
    (∫ r in Ioo (0 : ℝ) (Real.exp (-L₀)), ‖(-r⁻¹) • F' (-Real.log r)‖ ^ 2)
      = ∫ L in Ioi L₀, Real.exp L * ‖F' L‖ ^ 2 := by
  have hderiv : ∀ L ∈ Ioi L₀, HasDerivWithinAt logChart (-Real.exp (-L)) (Ioi L₀) L :=
    fun L _ => (hasDerivAt_logChart L).hasDerivWithinAt
  have h := integral_image_eq_integral_abs_deriv_smul (F := ℝ) measurableSet_Ioi hderiv
    (injOn_logChart_Ioi L₀) (fun r => ‖(-r⁻¹) • F' (-Real.log r)‖ ^ 2)
  rw [image_logChart_Ioi' L₀] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioi fun L _ => ?_
  have hexp : (0 : ℝ) < Real.exp (-L) := Real.exp_pos _
  have hlog : -Real.log (logChart L) = L := by
    rw [logChart, Real.log_exp, neg_neg]
  rw [abs_neg, abs_of_pos hexp, smul_eq_mul, hlog, norm_smul, Real.norm_eq_abs, mul_pow,
    abs_of_nonpos (by
      have : (0 : ℝ) < (logChart L)⁻¹ := by
        rw [logChart]; positivity
      linarith : -(logChart L)⁻¹ ≤ 0)]
  have hinv : (logChart L)⁻¹ = Real.exp L := by
    rw [logChart, ← Real.exp_neg, neg_neg]
  have hne : Real.exp L ≠ 0 := Real.exp_ne_zero L
  rw [hinv, neg_neg, Real.exp_neg]
  field_simp

/-! ## Polynomial decay is not enough for the spatial norm -/

omit [NormedSpace ℝ X] in
/-- **The exponential weight defeats every polynomial rate.**  A derivative bounded below by a fixed
power on a terminal ray has infinite exponentially weighted mass, so it is never in the spatial
`H¹`, however fast the power decays. -/
theorem lintegral_exp_weighted_eq_top {f : ℝ → X} {c p L₀ : ℝ} (hc : 0 < c) (hL₀ : 0 < L₀)
    (hf : ∀ L ∈ Ioi L₀, c * L ^ (-p) ≤ ‖f L‖) :
    (∫⁻ L in Ioi L₀, ENNReal.ofReal (Real.exp L) * ‖f L‖ₑ ^ 2) = ⊤ := by
  -- eventually `exp L ≥ c⁻² L^{2p}`, so the integrand is at least `1`
  have hgrow : Tendsto (fun x : ℝ => Real.exp x / x ^ (2 * p)) atTop atTop :=
    tendsto_exp_div_rpow_atTop (2 * p)
  obtain ⟨L₁, hL₁⟩ := (hgrow.eventually_ge_atTop (c ^ 2)⁻¹).exists_forall_of_atTop
  set L₂ : ℝ := max L₁ (L₀ + 1) with hL₂
  have hL₂L₀ : L₀ < L₂ := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hL₂pos : 0 < L₂ := lt_trans hL₀ hL₂L₀
  have hone : ∀ L ∈ Ioi L₂, (1 : ℝ≥0∞)
      ≤ ENNReal.ofReal (Real.exp L) * ‖f L‖ₑ ^ 2 := by
    intro L hL
    have hLmem : L ∈ Ioi L₀ := lt_trans hL₂L₀ hL
    have hLpos : 0 < L := lt_trans hL₂pos hL
    have hgrowL : (c ^ 2)⁻¹ ≤ Real.exp L / L ^ (2 * p) :=
      hL₁ L (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hL))
    have hLp : (0 : ℝ) < L ^ (2 * p) := Real.rpow_pos_of_pos hLpos _
    have hbound : c * L ^ (-p) ≤ ‖f L‖ := hf L hLmem
    have hnn : (0 : ℝ) ≤ c * L ^ (-p) := by positivity
    have hsq : 1 ≤ Real.exp L * ‖f L‖ ^ 2 := by
      have hstep : (c * L ^ (-p)) ^ 2 ≤ ‖f L‖ ^ 2 := pow_le_pow_left₀ hnn hbound 2
      have hval : (c * L ^ (-p)) ^ 2 = c ^ 2 * (L ^ (2 * p))⁻¹ := by
        rw [mul_pow, ← Real.rpow_natCast (L ^ (-p)) 2, ← Real.rpow_mul hLpos.le,
          ← Real.rpow_neg hLpos.le]
        congr 2
        push_cast
        ring
      have hexpL : (c ^ 2)⁻¹ * L ^ (2 * p) ≤ Real.exp L := (le_div_iff₀ hLp).mp hgrowL
      have h1 : c ^ 2 * (L ^ (2 * p))⁻¹ ≤ ‖f L‖ ^ 2 := hval ▸ hstep
      have hprod : ((c ^ 2)⁻¹ * L ^ (2 * p)) * (c ^ 2 * (L ^ (2 * p))⁻¹) = 1 := by
        field_simp
      calc (1 : ℝ) = ((c ^ 2)⁻¹ * L ^ (2 * p)) * (c ^ 2 * (L ^ (2 * p))⁻¹) := hprod.symm
        _ ≤ Real.exp L * ‖f L‖ ^ 2 :=
            mul_le_mul hexpL h1
              (mul_nonneg (by positivity) (le_of_lt (inv_pos.mpr hLp)))
              (Real.exp_pos L).le
    calc (1 : ℝ≥0∞) = ENNReal.ofReal 1 := by simp
      _ ≤ ENNReal.ofReal (Real.exp L * ‖f L‖ ^ 2) := ENNReal.ofReal_le_ofReal hsq
      _ = ENNReal.ofReal (Real.exp L) * ‖f L‖ₑ ^ 2 := by
          rw [ENNReal.ofReal_mul (Real.exp_pos L).le, ← ofReal_norm,
            ← ENNReal.ofReal_pow (norm_nonneg _)]
  have hsub : Ioi L₂ ⊆ Ioi L₀ := Ioi_subset_Ioi hL₂L₀.le
  have hlow : volume (Ioi L₂)
      ≤ ∫⁻ L in Ioi L₀, ENNReal.ofReal (Real.exp L) * ‖f L‖ₑ ^ 2 := by
    calc volume (Ioi L₂) = ∫⁻ _ in Ioi L₂, (1 : ℝ≥0∞) := by
          rw [setLIntegral_one]
      _ ≤ ∫⁻ L in Ioi L₂, ENNReal.ofReal (Real.exp L) * ‖f L‖ₑ ^ 2 :=
          setLIntegral_mono' measurableSet_Ioi hone
      _ ≤ ∫⁻ L in Ioi L₀, ENNReal.ofReal (Real.exp L) * ‖f L‖ₑ ^ 2 :=
          lintegral_mono_set hsub
  rw [Real.volume_Ioi] at hlow
  exact top_le_iff.mp hlow

end GaloisForLFunctions.HTGeometry
