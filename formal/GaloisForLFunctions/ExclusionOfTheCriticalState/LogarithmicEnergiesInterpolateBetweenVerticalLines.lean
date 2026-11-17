import GaloisForLFunctions.ExclusionOfTheCriticalState.TheLogarithmicDerivativeOfZetaIsSublogarithmicRightOfTheZeros
import GaloisForLFunctions.HTGeometry.PaleyWienerHalfPlane
import GaloisForLFunctions.HTGeometry.HalfPlaneHardyShift

/-!
# Logarithmic energies interpolate between vertical lines

For a Hardy function `G` of the right half-plane, write
`E_k(σ) = ∫ log(|t| + 4)^k |G(σ + it)|² dt`. If `E_{k₀}(σ₀)` and `E_{k₁}(σ₁)` are finite, then
`E_k(σ)` is finite at every intermediate point `σ = (1 - τ)σ₀ + τσ₁`, `k = (1 - τ)k₀ + τk₁`
(`0 ≤ k₀, k₁ ≤ 2`): the exponent of the logarithm interpolates together with the line.

Mechanism. An analytic family `log(p)^{k(p)}` is not available: its argument grows like
`|t|/log |t|`. Instead the logarithm is frozen on windows.

* For a height `T` the function `G(w)(w + 2 + iT)^{-2}` is again a Hardy function, and by
  Paley–Wiener the Laplace transform of a datum `φ_T ∈ L²(0, ∞)`. Plancherel on a line turns
  the windowed mass `∫ |G(σ + it)|² ((σ + 2)² + (t + T)²)^{-2} dt` into `∫ |φ_T|² e^{-2σx} dx`,
  which is log-convex in `σ` by Hölder's inequality.
* On the window the weight `log(|t| + 4)^k` is `log(|T| + 4)^k` up to the factor
  `(1 + |t + T|)^k`, and `log(|T| + 4)^k` is the geometric mean of the endpoint weights. Hölder's
  inequality in `T` and Tonelli's theorem assemble the windows.
-/

noncomputable section
open MeasureTheory Set Filter Complex Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open HTGeometry

/-! ### Hölder's inequality for a geometric mean -/

theorem lintegral_rpow_mul_rpow_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {a₀ a₁ : α → ENNReal} (h0 : AEMeasurable a₀ μ) (h1 : AEMeasurable a₁ μ) {τ : ℝ}
    (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    (∫⁻ x, a₀ x ^ (1 - τ) * a₁ x ^ τ ∂μ) ≤
      (∫⁻ x, a₀ x ∂μ) ^ (1 - τ) * (∫⁻ x, a₁ x ∂μ) ^ τ := by
  have hτ' : 0 < 1 - τ := by linarith
  have hpq : ((1 - τ)⁻¹).HolderConjugate τ⁻¹ :=
    Real.holderConjugate_iff.mpr ⟨(one_lt_inv₀ hτ').mpr (by linarith), by
      rw [inv_inv, inv_inv]
      ring⟩
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq (h0.pow_const (1 - τ)) (h1.pow_const τ)
  have e0 : ∀ x, (a₀ x ^ (1 - τ)) ^ (1 - τ)⁻¹ = a₀ x := fun x => by
    rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hτ'.ne', ENNReal.rpow_one]
  have e1 : ∀ x, (a₁ x ^ τ) ^ τ⁻¹ = a₁ x := fun x => by
    rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hτ0.ne', ENNReal.rpow_one]
  simp only [Pi.mul_apply, e0, e1, one_div, inv_inv] at h
  exact h

/-! ### Three lines for the masses of a Hardy function -/

/-- Plancherel on a line, for the Paley–Wiener datum of a Hardy function. -/
theorem lintegral_norm_sq_line_eq_datum {H : ℂ → ℂ} {N : ℝ} (hH : IsHalfPlaneHardy H N) {σ : ℝ}
    (hσ : 0 < σ) :
    (∫⁻ ξ : ℝ, ENNReal.ofReal (‖H (rayLine σ ξ)‖ ^ 2)) =
      ∫⁻ x in Ioi (0 : ℝ),
        ENNReal.ofReal (Real.exp (-(2 * σ * x)) * ‖hardyDatum H hH x‖ ^ 2) := by
  have hφ := memLp_two_hardyDatum hH
  have hm := hH.memLp σ hσ
  have hint : Integrable fun ξ : ℝ => ‖H (rayLine σ ξ)‖ ^ 2 :=
    (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).1 hm
  have heq : (fun ξ : ℝ => ‖H (rayLine σ ξ)‖ ^ 2) =
      fun ξ : ℝ => ‖laplaceRay (hardyDatum H hH) (rayLine σ ξ)‖ ^ 2 :=
    funext fun ξ => by
      rw [isHalfPlaneHardy_eq_laplaceRay hH (w := rayLine σ ξ) (by rw [rayLine_re]; exact hσ)]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun ξ => sq_nonneg _), heq,
    integral_norm_sq_laplaceRay_line hφ hσ,
    ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_mul_norm_sq hφ hσ)
      (Eventually.of_forall fun x => mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]

/-- **Three lines in mean square.** The mass of a Hardy function on a vertical line is
log-convex in the abscissa: it is the weighted mass `∫ |φ|² e^{-2σx}` of one datum. -/
theorem lintegral_norm_sq_line_interp {H : ℂ → ℂ} {N : ℝ} (hH : IsHalfPlaneHardy H N)
    {σ₀ σ₁ τ : ℝ} (h0 : 0 < σ₀) (h1 : 0 < σ₁) (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    (∫⁻ ξ : ℝ, ENNReal.ofReal (‖H (rayLine ((1 - τ) * σ₀ + τ * σ₁) ξ)‖ ^ 2)) ≤
      (∫⁻ ξ : ℝ, ENNReal.ofReal (‖H (rayLine σ₀ ξ)‖ ^ 2)) ^ (1 - τ) *
        (∫⁻ ξ : ℝ, ENNReal.ofReal (‖H (rayLine σ₁ ξ)‖ ^ 2)) ^ τ := by
  have hτ' : 0 < 1 - τ := by linarith
  have hσ : 0 < (1 - τ) * σ₀ + τ * σ₁ := by positivity
  rw [lintegral_norm_sq_line_eq_datum hH hσ, lintegral_norm_sq_line_eq_datum hH h0,
    lintegral_norm_sq_line_eq_datum hH h1]
  have hφm : AEStronglyMeasurable (hardyDatum H hH) (volume.restrict (Ioi (0 : ℝ))) :=
    (aestronglyMeasurable_hardyDatum hH).restrict
  have hmeas : ∀ σ : ℝ, AEMeasurable (fun x : ℝ =>
      ENNReal.ofReal (Real.exp (-(2 * σ * x)) * ‖hardyDatum H hH x‖ ^ 2))
      (volume.restrict (Ioi (0 : ℝ))) := fun σ =>
    ENNReal.measurable_ofReal.comp_aemeasurable
      (((by fun_prop : Continuous fun x : ℝ => Real.exp (-(2 * σ * x))).measurable.aemeasurable).mul
        (hφm.norm.aemeasurable.pow_const 2))
  have key := lintegral_rpow_mul_rpow_le (volume.restrict (Ioi (0 : ℝ))) (hmeas σ₀) (hmeas σ₁)
    hτ0 hτ1
  refine le_trans (le_of_eq (lintegral_congr fun x => ?_)) key
  have hP : 0 ≤ ‖hardyDatum H hH x‖ ^ 2 := sq_nonneg _
  have hE0 := (Real.exp_pos (-(2 * σ₀ * x))).le
  have hE1 := (Real.exp_pos (-(2 * σ₁ * x))).le
  have e : ‖hardyDatum H hH x‖ ^ 2 =
      (‖hardyDatum H hH x‖ ^ 2) ^ (1 - τ) * (‖hardyDatum H hH x‖ ^ 2) ^ τ := by
    rw [← Real.rpow_add' hP (by rw [sub_add_cancel]; exact one_ne_zero), sub_add_cancel,
      Real.rpow_one]
  rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hE0 hP) hτ'.le,
    ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hE1 hP) hτ0.le,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (mul_nonneg hE0 hP) _)]
  congr 1
  rw [Real.mul_rpow hE0 hP, Real.mul_rpow hE1 hP, ← Real.exp_mul, ← Real.exp_mul]
  calc Real.exp (-(2 * ((1 - τ) * σ₀ + τ * σ₁) * x)) * ‖hardyDatum H hH x‖ ^ 2
      = (Real.exp (-(2 * σ₀ * x) * (1 - τ)) * Real.exp (-(2 * σ₁ * x) * τ)) *
          ((‖hardyDatum H hH x‖ ^ 2) ^ (1 - τ) * (‖hardyDatum H hH x‖ ^ 2) ^ τ) := by
        rw [← Real.exp_add, ← e]
        congr 2
        ring
    _ = _ := by ring

/-! ### Windows -/

/-- The window of width `σ + 2` around the height `-T`. -/
def lineWindow (σ T y : ℝ) : ℝ := (((σ + 2) ^ 2 + (y + T) ^ 2) ^ 2)⁻¹

theorem lineWindow_nonneg (σ T y : ℝ) : 0 ≤ lineWindow σ T y := by
  unfold lineWindow
  positivity

/-- The window is the squared modulus of the holomorphic multiplier `(w + 2 + iT)^{-2}`. -/
theorem norm_sq_mul_inv_shift_sq (G : ℂ → ℂ) (σ T ξ : ℝ) :
    ‖G (rayLine σ ξ) * (rayLine σ ξ + ((2 : ℂ) + (T : ℂ) * I))⁻¹ *
        (rayLine σ ξ + ((2 : ℂ) + (T : ℂ) * I))⁻¹‖ ^ 2 =
      ‖G (rayLine σ ξ)‖ ^ 2 * lineWindow σ T (2 * Real.pi * ξ) := by
  have hre : (rayLine σ ξ + ((2 : ℂ) + (T : ℂ) * I)).re = σ + 2 := by simp [rayLine]
  have him : (rayLine σ ξ + ((2 : ℂ) + (T : ℂ) * I)).im = 2 * Real.pi * ξ + T := by
    simp [rayLine]
  have hn : ‖rayLine σ ξ + ((2 : ℂ) + (T : ℂ) * I)‖ ^ 2 =
      (σ + 2) ^ 2 + (2 * Real.pi * ξ + T) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    ring
  rw [norm_mul, norm_mul, norm_inv, mul_pow, mul_pow, inv_pow, hn, mul_assoc, ← mul_inv, ← sq]
  rfl

theorem exists_isHalfPlaneHardy_window {G : ℂ → ℂ} {M : ℝ} (hG : IsHalfPlaneHardy G M) (T : ℝ) :
    ∃ N : ℝ, IsHalfPlaneHardy (fun w => G w * (w + ((2 : ℂ) + (T : ℂ) * I))⁻¹ *
      (w + ((2 : ℂ) + (T : ℂ) * I))⁻¹) N := by
  have hc : 0 < ((2 : ℂ) + (T : ℂ) * I).re := by simp
  exact ⟨_, isHalfPlaneHardy_mul_inv_shift (isHalfPlaneHardy_mul_inv_shift hG hc) hc⟩

/-- Three lines for the windowed masses. -/
theorem lintegral_window_line_interp {G : ℂ → ℂ} {M : ℝ} (hG : IsHalfPlaneHardy G M) (T : ℝ)
    {σ₀ σ₁ τ : ℝ} (h0 : 0 < σ₀) (h1 : 0 < σ₁) (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    (∫⁻ ξ : ℝ, ENNReal.ofReal (‖G (rayLine ((1 - τ) * σ₀ + τ * σ₁) ξ)‖ ^ 2 *
        lineWindow ((1 - τ) * σ₀ + τ * σ₁) T (2 * Real.pi * ξ))) ≤
      (∫⁻ ξ : ℝ, ENNReal.ofReal (‖G (rayLine σ₀ ξ)‖ ^ 2 *
        lineWindow σ₀ T (2 * Real.pi * ξ))) ^ (1 - τ) *
      (∫⁻ ξ : ℝ, ENNReal.ofReal (‖G (rayLine σ₁ ξ)‖ ^ 2 *
        lineWindow σ₁ T (2 * Real.pi * ξ))) ^ τ := by
  obtain ⟨N, hN⟩ := exists_isHalfPlaneHardy_window hG T
  have h := lintegral_norm_sq_line_interp hN h0 h1 hτ0 hτ1
  simp only [norm_sq_mul_inv_shift_sq G] at h
  exact h

/-- On a window the logarithmic weight at the centre is at most the weight at the point, up to
the factor `(1 + |t + T|)²`, which the window absorbs. -/
theorem log_rpow_mul_lineWindow_le {σ k : ℝ} (hσ : 0 ≤ σ) (hk0 : 0 ≤ k) (hk2 : k ≤ 2)
    (t T : ℝ) :
    Real.log (|T| + 4) ^ k * lineWindow σ T t ≤
      Real.log (|t| + 4) ^ k * (2 * (1 + (t + T) ^ 2)⁻¹) := by
  have hLT := one_le_log_abs_add_four T
  have hLt := one_le_log_abs_add_four t
  have hd : 0 ≤ |t + T| := abs_nonneg _
  have h1 : Real.log (|T| + 4) ≤ Real.log (|t| + 4) * (1 + |t + T|) := by
    have h := log_abs_add_four_le T (-t)
    rwa [abs_neg, sub_neg_eq_add, add_comm T t] at h
  have hLk : 0 ≤ Real.log (|t| + 4) ^ k := Real.rpow_nonneg (by linarith) _
  have h2 : Real.log (|T| + 4) ^ k ≤ Real.log (|t| + 4) ^ k * (1 + |t + T|) ^ 2 := by
    calc Real.log (|T| + 4) ^ k ≤ (Real.log (|t| + 4) * (1 + |t + T|)) ^ k :=
          Real.rpow_le_rpow (by linarith) h1 hk0
      _ = Real.log (|t| + 4) ^ k * (1 + |t + T|) ^ k :=
          Real.mul_rpow (by linarith) (by linarith)
      _ ≤ Real.log (|t| + 4) ^ k * (1 + |t + T|) ^ (2 : ℝ) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by linarith) hk2) hLk
      _ = _ := by rw [Real.rpow_two]
  have h3 : (1 + |t + T|) ^ 2 ≤ 2 * (1 + (t + T) ^ 2) := by
    nlinarith [sq_abs (t + T), sq_nonneg (|t + T| - 1)]
  have hx : 0 < 1 + (t + T) ^ 2 := by positivity
  have h4 : lineWindow σ T t ≤ ((1 + (t + T) ^ 2) ^ 2)⁻¹ := by
    unfold lineWindow
    refine inv_anti₀ (by positivity) (pow_le_pow_left₀ hx.le ?_ 2)
    nlinarith [sq_nonneg σ]
  calc Real.log (|T| + 4) ^ k * lineWindow σ T t
      ≤ (Real.log (|t| + 4) ^ k * (1 + |t + T|) ^ 2) * ((1 + (t + T) ^ 2) ^ 2)⁻¹ :=
        mul_le_mul h2 h4 (lineWindow_nonneg _ _ _) (mul_nonneg hLk (sq_nonneg _))
    _ ≤ (Real.log (|t| + 4) ^ k * (2 * (1 + (t + T) ^ 2))) * ((1 + (t + T) ^ 2) ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hLk) (by positivity)
    _ = _ := by
        field_simp

/-- On the unit window the weight at the centre is at least a quarter of the weight at the
point. -/
theorem le_log_rpow_mul_lineWindow {σ k : ℝ} (hσ : 0 ≤ σ) (hk0 : 0 ≤ k) (hk2 : k ≤ 2) {t T : ℝ}
    (hT : |t + T| ≤ 1) :
    Real.log (|t| + 4) ^ k / 4 * (((σ + 2) ^ 2 + 1) ^ 2)⁻¹ ≤
      Real.log (|T| + 4) ^ k * lineWindow σ T t := by
  have hLT := one_le_log_abs_add_four T
  have hLt := one_le_log_abs_add_four t
  have h1 : Real.log (|t| + 4) / 2 ≤ Real.log (|T| + 4) := by
    have h := log_abs_add_four_le (-t) T
    rw [abs_neg, show -t - T = -(t + T) by ring, abs_neg] at h
    have h' := h.trans (mul_le_mul_of_nonneg_left (by linarith : 1 + |t + T| ≤ 2) (by linarith))
    linarith
  have hLk : 0 ≤ Real.log (|t| + 4) ^ k := Real.rpow_nonneg (by linarith) _
  have h2 : Real.log (|t| + 4) ^ k / 4 ≤ Real.log (|T| + 4) ^ k := by
    have ha : (Real.log (|t| + 4) / 2) ^ k ≤ Real.log (|T| + 4) ^ k :=
      Real.rpow_le_rpow (by linarith) h1 hk0
    have hb : (Real.log (|t| + 4) / 2) ^ k = Real.log (|t| + 4) ^ k * (1 / 2 : ℝ) ^ k := by
      rw [div_eq_mul_one_div, Real.mul_rpow (by linarith) (by norm_num)]
    have hc : (1 / 4 : ℝ) ≤ (1 / 2 : ℝ) ^ k := by
      have h := Real.rpow_le_rpow_of_exponent_ge (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) hk2
      rw [Real.rpow_two] at h
      norm_num at h
      linarith
    rw [hb] at ha
    nlinarith [mul_le_mul_of_nonneg_left hc hLk]
  have h3 : (((σ + 2) ^ 2 + 1) ^ 2)⁻¹ ≤ lineWindow σ T t := by
    unfold lineWindow
    have hsq : (t + T) ^ 2 ≤ 1 := by
      have h := sq_abs (t + T)
      nlinarith [abs_nonneg (t + T)]
    refine inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith) 2)
  exact mul_le_mul h2 h3 (by positivity) (Real.rpow_nonneg (by linarith) _)

theorem lintegral_two_inv_one_add_sq_lt_top :
    (∫⁻ y : ℝ, ENNReal.ofReal (2 * (1 + y ^ 2)⁻¹)) < ⊤ :=
  (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun y : ℝ => by positivity)).mp
    (integrable_inv_one_add_sq.const_mul 2).2

/-! ### The windowed energies -/

/-- The energy density on the line `Re w = σ` seen through the window at `-T`, with the
logarithm frozen at the centre. -/
def windowedEnergy (G : ℂ → ℂ) (σ k T ξ : ℝ) : ℝ :=
  Real.log (|T| + 4) ^ k * (‖G (rayLine σ ξ)‖ ^ 2 * lineWindow σ T (2 * Real.pi * ξ))

theorem measurable_windowedEnergy {G : ℂ → ℂ} {σ : ℝ}
    (hGc : Continuous fun ξ : ℝ => G (rayLine σ ξ)) (k : ℝ) :
    Measurable fun p : ℝ × ℝ => ENNReal.ofReal (windowedEnergy G σ k p.1 p.2) := by
  have m1 : Measurable fun p : ℝ × ℝ => Real.log (|p.1| + 4) ^ k :=
    (Real.measurable_log.comp ((continuous_abs.measurable.comp measurable_fst).add_const 4)).pow_const k
  have m2 : Measurable fun p : ℝ × ℝ => ‖G (rayLine σ p.2)‖ ^ 2 :=
    ((hGc.measurable.comp measurable_snd).norm).pow_const 2
  have m3 : Measurable fun p : ℝ × ℝ => lineWindow σ p.1 (2 * Real.pi * p.2) := by
    unfold lineWindow
    fun_prop
  exact ENNReal.measurable_ofReal.comp (m1.mul (m2.mul m3))

/-- The windows add up to at most the logarithmic energy of the line. -/
theorem lintegral_windowedEnergy_le {G : ℂ → ℂ} {σ k : ℝ} (hσ : 0 ≤ σ) (hk0 : 0 ≤ k)
    (hk2 : k ≤ 2) (hGc : Continuous fun ξ : ℝ => G (rayLine σ ξ)) :
    (∫⁻ T : ℝ, ∫⁻ ξ : ℝ, ENNReal.ofReal (windowedEnergy G σ k T ξ)) ≤
      (∫⁻ y : ℝ, ENNReal.ofReal (2 * (1 + y ^ 2)⁻¹)) *
        ∫⁻ ξ : ℝ, ENNReal.ofReal
          (Real.log (|2 * Real.pi * ξ| + 4) ^ k * ‖G (rayLine σ ξ)‖ ^ 2) := by
  rw [lintegral_lintegral_swap (measurable_windowedEnergy hGc k).aemeasurable,
    ← lintegral_const_mul' _ _ lintegral_two_inv_one_add_sq_lt_top.ne]
  refine lintegral_mono fun ξ => ?_
  have hg : 0 ≤ ‖G (rayLine σ ξ)‖ ^ 2 := sq_nonneg _
  have hLk : 0 ≤ Real.log (|2 * Real.pi * ξ| + 4) ^ k :=
    Real.rpow_nonneg (by linarith [one_le_log_abs_add_four (2 * Real.pi * ξ)]) _
  calc (∫⁻ T : ℝ, ENNReal.ofReal (windowedEnergy G σ k T ξ))
      ≤ ∫⁻ T : ℝ, ENNReal.ofReal
            (Real.log (|2 * Real.pi * ξ| + 4) ^ k * ‖G (rayLine σ ξ)‖ ^ 2) *
          ENNReal.ofReal (2 * (1 + (2 * Real.pi * ξ + T) ^ 2)⁻¹) := by
        refine lintegral_mono fun T => ?_
        rw [← ENNReal.ofReal_mul (mul_nonneg hLk hg)]
        refine ENNReal.ofReal_le_ofReal ?_
        have h := log_rpow_mul_lineWindow_le hσ hk0 hk2 (2 * Real.pi * ξ) T
        unfold windowedEnergy
        calc Real.log (|T| + 4) ^ k *
              (‖G (rayLine σ ξ)‖ ^ 2 * lineWindow σ T (2 * Real.pi * ξ))
            = ‖G (rayLine σ ξ)‖ ^ 2 *
                (Real.log (|T| + 4) ^ k * lineWindow σ T (2 * Real.pi * ξ)) := by ring
          _ ≤ ‖G (rayLine σ ξ)‖ ^ 2 * (Real.log (|2 * Real.pi * ξ| + 4) ^ k *
                (2 * (1 + (2 * Real.pi * ξ + T) ^ 2)⁻¹)) := mul_le_mul_of_nonneg_left h hg
          _ = _ := by ring
    _ = ENNReal.ofReal (Real.log (|2 * Real.pi * ξ| + 4) ^ k * ‖G (rayLine σ ξ)‖ ^ 2) *
          ∫⁻ T : ℝ, ENNReal.ofReal (2 * (1 + (2 * Real.pi * ξ + T) ^ 2)⁻¹) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (Real.log (|2 * Real.pi * ξ| + 4) ^ k * ‖G (rayLine σ ξ)‖ ^ 2) *
          ∫⁻ y : ℝ, ENNReal.ofReal (2 * (1 + y ^ 2)⁻¹) := by
        rw [lintegral_add_left_eq_self (fun y : ℝ => ENNReal.ofReal (2 * (1 + y ^ 2)⁻¹))
          (2 * Real.pi * ξ)]
    _ = _ := mul_comm _ _

/-- The windows add up to at least a fixed multiple of the logarithmic energy of the line. -/
theorem le_lintegral_windowedEnergy {G : ℂ → ℂ} {σ k : ℝ} (hσ : 0 ≤ σ) (hk0 : 0 ≤ k)
    (hk2 : k ≤ 2) (hGc : Continuous fun ξ : ℝ => G (rayLine σ ξ)) :
    (∫⁻ ξ : ℝ, ENNReal.ofReal ((((σ + 2) ^ 2 + 1) ^ 2)⁻¹ / 2 *
        (Real.log (|2 * Real.pi * ξ| + 4) ^ k * ‖G (rayLine σ ξ)‖ ^ 2))) ≤
      ∫⁻ T : ℝ, ∫⁻ ξ : ℝ, ENNReal.ofReal (windowedEnergy G σ k T ξ) := by
  rw [lintegral_lintegral_swap (measurable_windowedEnergy hGc k).aemeasurable]
  refine lintegral_mono fun ξ => ?_
  have hg : 0 ≤ ‖G (rayLine σ ξ)‖ ^ 2 := sq_nonneg _
  have hLk : 0 ≤ Real.log (|2 * Real.pi * ξ| + 4) ^ k :=
    Real.rpow_nonneg (by linarith [one_le_log_abs_add_four (2 * Real.pi * ξ)]) _
  have hc : 0 ≤ (((σ + 2) ^ 2 + 1) ^ 2)⁻¹ := by positivity
  calc ENNReal.ofReal ((((σ + 2) ^ 2 + 1) ^ 2)⁻¹ / 2 *
        (Real.log (|2 * Real.pi * ξ| + 4) ^ k * ‖G (rayLine σ ξ)‖ ^ 2))
      = ENNReal.ofReal (Real.log (|2 * Real.pi * ξ| + 4) ^ k / 4 * (((σ + 2) ^ 2 + 1) ^ 2)⁻¹ *
          ‖G (rayLine σ ξ)‖ ^ 2) *
          volume (Icc (-(2 * Real.pi * ξ) - 1) (-(2 * Real.pi * ξ) + 1)) := by
        rw [Real.volume_Icc, ← ENNReal.ofReal_mul
          (mul_nonneg (mul_nonneg (div_nonneg hLk (by norm_num)) hc) hg)]
        congr 1
        ring
    _ = ∫⁻ _T in Icc (-(2 * Real.pi * ξ) - 1) (-(2 * Real.pi * ξ) + 1),
          ENNReal.ofReal (Real.log (|2 * Real.pi * ξ| + 4) ^ k / 4 *
            (((σ + 2) ^ 2 + 1) ^ 2)⁻¹ * ‖G (rayLine σ ξ)‖ ^ 2) := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ T in Icc (-(2 * Real.pi * ξ) - 1) (-(2 * Real.pi * ξ) + 1),
          ENNReal.ofReal (windowedEnergy G σ k T ξ) := by
        refine setLIntegral_mono' measurableSet_Icc fun T hT => ENNReal.ofReal_le_ofReal ?_
        have hT' : |2 * Real.pi * ξ + T| ≤ 1 :=
          abs_le.mpr ⟨by linarith [hT.1], by linarith [hT.2]⟩
        have h := le_log_rpow_mul_lineWindow hσ hk0 hk2 hT'
        unfold windowedEnergy
        calc Real.log (|2 * Real.pi * ξ| + 4) ^ k / 4 * (((σ + 2) ^ 2 + 1) ^ 2)⁻¹ *
              ‖G (rayLine σ ξ)‖ ^ 2
            ≤ Real.log (|T| + 4) ^ k * lineWindow σ T (2 * Real.pi * ξ) *
                ‖G (rayLine σ ξ)‖ ^ 2 := mul_le_mul_of_nonneg_right h hg
          _ = _ := by ring
    _ ≤ _ := setLIntegral_le_lintegral _ _

/-- For each window the energy is the geometric mean of the endpoint energies. -/
theorem lintegral_windowedEnergy_interp {G : ℂ → ℂ} {M : ℝ} (hG : IsHalfPlaneHardy G M)
    {σ₀ σ₁ k₀ k₁ τ : ℝ} (h0 : 0 < σ₀) (h1 : 0 < σ₁) (hτ0 : 0 < τ) (hτ1 : τ < 1) (T : ℝ) :
    (∫⁻ ξ : ℝ, ENNReal.ofReal
        (windowedEnergy G ((1 - τ) * σ₀ + τ * σ₁) ((1 - τ) * k₀ + τ * k₁) T ξ)) ≤
      (∫⁻ ξ : ℝ, ENNReal.ofReal (windowedEnergy G σ₀ k₀ T ξ)) ^ (1 - τ) *
        (∫⁻ ξ : ℝ, ENNReal.ofReal (windowedEnergy G σ₁ k₁ T ξ)) ^ τ := by
  have hL : 0 < Real.log (|T| + 4) := by linarith [one_le_log_abs_add_four T]
  have hτ' : 0 < 1 - τ := by linarith
  have hsplit : ∀ σ k : ℝ, (∫⁻ ξ : ℝ, ENNReal.ofReal (windowedEnergy G σ k T ξ)) =
      ENNReal.ofReal (Real.log (|T| + 4) ^ k) * ∫⁻ ξ : ℝ, ENNReal.ofReal
        (‖G (rayLine σ ξ)‖ ^ 2 * lineWindow σ T (2 * Real.pi * ξ)) := fun σ k => by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun ξ => ?_
    unfold windowedEnergy
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg hL.le _)]
  have hw : ENNReal.ofReal (Real.log (|T| + 4) ^ ((1 - τ) * k₀ + τ * k₁)) =
      ENNReal.ofReal (Real.log (|T| + 4) ^ k₀) ^ (1 - τ) *
        ENNReal.ofReal (Real.log (|T| + 4) ^ k₁) ^ τ := by
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hL.le _) hτ'.le,
      ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hL.le _) hτ0.le,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (Real.rpow_nonneg hL.le _) _),
      ← Real.rpow_mul hL.le, ← Real.rpow_mul hL.le, ← Real.rpow_add hL]
    congr 2
    ring
  rw [hsplit, hsplit, hsplit, ENNReal.mul_rpow_of_nonneg _ _ hτ'.le,
    ENNReal.mul_rpow_of_nonneg _ _ hτ0.le, hw]
  calc ENNReal.ofReal (Real.log (|T| + 4) ^ k₀) ^ (1 - τ) *
        ENNReal.ofReal (Real.log (|T| + 4) ^ k₁) ^ τ *
        ∫⁻ ξ : ℝ, ENNReal.ofReal (‖G (rayLine ((1 - τ) * σ₀ + τ * σ₁) ξ)‖ ^ 2 *
          lineWindow ((1 - τ) * σ₀ + τ * σ₁) T (2 * Real.pi * ξ))
      ≤ ENNReal.ofReal (Real.log (|T| + 4) ^ k₀) ^ (1 - τ) *
        ENNReal.ofReal (Real.log (|T| + 4) ^ k₁) ^ τ *
        ((∫⁻ ξ : ℝ, ENNReal.ofReal (‖G (rayLine σ₀ ξ)‖ ^ 2 *
            lineWindow σ₀ T (2 * Real.pi * ξ))) ^ (1 - τ) *
          (∫⁻ ξ : ℝ, ENNReal.ofReal (‖G (rayLine σ₁ ξ)‖ ^ 2 *
            lineWindow σ₁ T (2 * Real.pi * ξ))) ^ τ) :=
        mul_le_mul' le_rfl (lintegral_window_line_interp hG T h0 h1 hτ0 hτ1)
    _ = _ := by ring

/-! ### Interpolation -/

theorem integrable_log_rpow_mul_norm_sq_line_interp_aux {G : ℂ → ℂ} {M : ℝ}
    (hG : IsHalfPlaneHardy G M) {σ₀ σ₁ k₀ k₁ τ σ k : ℝ} (h0 : 0 < σ₀) (h1 : 0 < σ₁)
    (hk0 : 0 ≤ k₀) (hk0' : k₀ ≤ 2) (hk1 : 0 ≤ k₁) (hk1' : k₁ ≤ 2) (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hσeq : σ = (1 - τ) * σ₀ + τ * σ₁) (hkeq : k = (1 - τ) * k₀ + τ * k₁)
    (hE0 : Integrable fun t : ℝ =>
      Real.log (|t| + 4) ^ k₀ * ‖G ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2)
    (hE1 : Integrable fun t : ℝ =>
      Real.log (|t| + 4) ^ k₁ * ‖G ((σ₁ : ℂ) + (t : ℂ) * I)‖ ^ 2) :
    Integrable fun t : ℝ => Real.log (|t| + 4) ^ k * ‖G ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  have h2π : (2 * Real.pi) ≠ 0 := by positivity
  have hτ' : 0 < 1 - τ := by linarith
  have hσ : 0 < σ := by
    rw [hσeq]
    positivity
  have hk : 0 ≤ k := by
    rw [hkeq]
    positivity
  have hk' : k ≤ 2 := by
    rw [hkeq]
    nlinarith
  have hGc : ∀ s : ℝ, 0 < s → Continuous fun ξ : ℝ => G (rayLine s ξ) := fun s hs =>
    hG.holo.continuousOn.comp_continuous (by unfold rayLine; fun_prop) fun ξ => by simpa using hs
  have hLnn : ∀ (κ t : ℝ), 0 ≤ Real.log (|t| + 4) ^ κ := fun κ t =>
    Real.rpow_nonneg (by linarith [one_le_log_abs_add_four t]) _
  -- the endpoint energies in the frequency variable
  have hfin : ∀ {s κ : ℝ}, Integrable (fun t : ℝ =>
      Real.log (|t| + 4) ^ κ * ‖G ((s : ℂ) + (t : ℂ) * I)‖ ^ 2) →
      (∫⁻ ξ : ℝ, ENNReal.ofReal
        (Real.log (|2 * Real.pi * ξ| + 4) ^ κ * ‖G (rayLine s ξ)‖ ^ 2)) < ⊤ := by
    intro s κ h
    exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ξ : ℝ =>
      mul_nonneg (hLnn κ (2 * Real.pi * ξ)) (sq_nonneg _))).mp (h.comp_mul_left' h2π).2
  have hK := lintegral_two_inv_one_add_sq_lt_top
  have hA0 : (∫⁻ T : ℝ, ∫⁻ ξ : ℝ, ENNReal.ofReal (windowedEnergy G σ₀ k₀ T ξ)) < ⊤ :=
    (lintegral_windowedEnergy_le h0.le hk0 hk0' (hGc σ₀ h0)).trans_lt
      (ENNReal.mul_lt_top hK (hfin hE0))
  have hA1 : (∫⁻ T : ℝ, ∫⁻ ξ : ℝ, ENNReal.ofReal (windowedEnergy G σ₁ k₁ T ξ)) < ⊤ :=
    (lintegral_windowedEnergy_le h1.le hk1 hk1' (hGc σ₁ h1)).trans_lt
      (ENNReal.mul_lt_top hK (hfin hE1))
  -- Hölder over the windows
  have hm : ∀ (s κ : ℝ), 0 < s → AEMeasurable
      (fun T : ℝ => ∫⁻ ξ : ℝ, ENNReal.ofReal (windowedEnergy G s κ T ξ)) volume := fun s κ hs =>
    (measurable_windowedEnergy (hGc s hs) κ).lintegral_prod_right'.aemeasurable
  have hwin : ∀ T : ℝ, (∫⁻ ξ : ℝ, ENNReal.ofReal (windowedEnergy G σ k T ξ)) ≤
      (∫⁻ ξ : ℝ, ENNReal.ofReal (windowedEnergy G σ₀ k₀ T ξ)) ^ (1 - τ) *
        (∫⁻ ξ : ℝ, ENNReal.ofReal (windowedEnergy G σ₁ k₁ T ξ)) ^ τ := fun T => by
    rw [hσeq, hkeq]
    exact lintegral_windowedEnergy_interp hG h0 h1 hτ0 hτ1 T
  have hT : (∫⁻ T : ℝ, ∫⁻ ξ : ℝ, ENNReal.ofReal (windowedEnergy G σ k T ξ)) < ⊤ :=
    ((lintegral_mono hwin).trans
      (lintegral_rpow_mul_rpow_le volume (hm σ₀ k₀ h0) (hm σ₁ k₁ h1) hτ0 hτ1)).trans_lt
      (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hτ'.le hA0.ne)
        (ENNReal.rpow_lt_top_of_nonneg hτ0.le hA1.ne))
  have hlow := le_lintegral_windowedEnergy hσ.le hk hk' (hGc σ hσ)
  have hc : 0 < (((σ + 2) ^ 2 + 1) ^ 2)⁻¹ / 2 := by positivity
  have hξ : Integrable fun ξ : ℝ =>
      Real.log (|2 * Real.pi * ξ| + 4) ^ k * ‖G (rayLine σ ξ)‖ ^ 2 := by
    refine ⟨(((Real.measurable_log.comp ((continuous_abs.measurable.comp
      (measurable_const.mul measurable_id)).add_const 4)).pow_const k).mul
      (((hGc σ hσ).measurable.norm).pow_const 2)).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ξ : ℝ =>
        mul_nonneg (hLnn k (2 * Real.pi * ξ)) (sq_nonneg _))).mpr ?_⟩
    have h3 : ENNReal.ofReal ((((σ + 2) ^ 2 + 1) ^ 2)⁻¹ / 2) * (∫⁻ ξ : ℝ, ENNReal.ofReal
        (Real.log (|2 * Real.pi * ξ| + 4) ^ k * ‖G (rayLine σ ξ)‖ ^ 2)) ≠ ⊤ := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine ((le_of_eq (lintegral_congr fun ξ => ?_)).trans_lt (hlow.trans_lt hT)).ne
      exact (ENNReal.ofReal_mul hc.le).symm
    exact ENNReal.lt_top_of_mul_ne_top_right h3 (ENNReal.ofReal_pos.mpr hc).ne'
  exact (integrable_comp_mul_left_iff
    (fun t : ℝ => Real.log (|t| + 4) ^ k * ‖G ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) h2π).mp hξ

/-- **Logarithmic energies interpolate between vertical lines.** For a Hardy function `G` of
the right half-plane, lines `σ₀, σ₁ > 0` and exponents `0 ≤ k₀, k₁ ≤ 2`: if
`∫ log(|t| + 4)^{k_j} |G(σ_j + it)|² dt < ∞` for `j = 0, 1`, then
`∫ log(|t| + 4)^k |G(σ + it)|² dt < ∞` for `σ = (1 - τ)σ₀ + τσ₁`, `k = (1 - τ)k₀ + τk₁`. -/
theorem integrable_log_rpow_mul_norm_sq_line_interp {G : ℂ → ℂ} {M : ℝ}
    (hG : IsHalfPlaneHardy G M) {σ₀ σ₁ k₀ k₁ τ : ℝ} (h0 : 0 < σ₀) (h1 : 0 < σ₁)
    (hk0 : 0 ≤ k₀) (hk0' : k₀ ≤ 2) (hk1 : 0 ≤ k₁) (hk1' : k₁ ≤ 2) (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hE0 : Integrable fun t : ℝ =>
      Real.log (|t| + 4) ^ k₀ * ‖G ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2)
    (hE1 : Integrable fun t : ℝ =>
      Real.log (|t| + 4) ^ k₁ * ‖G ((σ₁ : ℂ) + (t : ℂ) * I)‖ ^ 2) :
    Integrable fun t : ℝ => Real.log (|t| + 4) ^ ((1 - τ) * k₀ + τ * k₁) *
      ‖G ((((1 - τ) * σ₀ + τ * σ₁ : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
  integrable_log_rpow_mul_norm_sq_line_interp_aux hG h0 h1 hk0 hk0' hk1 hk1' hτ0 hτ1 rfl rfl
    hE0 hE1

end GaloisForLFunctions.ExclusionOfTheCriticalState
