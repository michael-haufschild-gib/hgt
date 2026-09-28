import GaloisForLFunctions.RHTower.ThetaPrimeMomentPorts

/-!
# Translation sources of the theta port: the Xi ideal and one-prime moments

For sources decaying faster than every exponential the bilateral transform
`∫_ℝ e^{wu} f(u) du` obeys the translation law `∫ e^{wu} k(u + h) = e^{-wh} X(w)`, and splits into
half-line transforms by parity.

* **(6).** The odd part `j = ½Σ c_i[k(· + h_i) - k(· - h_i)]` of every finite real translation
  polynomial has `Q_{2j}(w) = ∫_ℝ e^{wu} j = -X(w) Σ c_i sinh(h_i w)`: it vanishes at every Xi zero,
  `j(0) = 0`, and the corrected port keeps the raw alternating normal derivative `-2b(γ)Ξ'(γ)`.
* **(7).** The log-time clock obeys `[U, T_h] = -h T_h`; the odd part of `[U, T_h]k` is again a
  translation polynomial.
* **(8)–(9).** The one-prime deletion `g_p = k - p^{-1/2}[k(· + L) + k(· - L)]/2` has transform
  `A_p X`; the correction `a_p = -k + 2u g_p` cancels every even jet at the cut and its port is
  exactly `X/2 + (A_p X)'`.
-/
open Complex Filter Topology Set MeasureTheory
open GaloisForLFunctions.HTGeometry
open scoped ContDiff ComplexConjugate

namespace RHTower

noncomputable section

/-! ## Bilateral transforms of translated sources -/

/-- A continuous source decaying faster than every exponential. -/
structure SuperExpSource (f : ℝ → ℝ) : Prop where
  continuous : Continuous f
  bound : ∀ A : ℝ, ∃ C, 0 ≤ C ∧ ∀ u, |f u| ≤ C * Real.exp (-(A * |u|))

theorem superExpSource_thetaCuspFullSource : SuperExpSource thetaCuspFullSource :=
  ⟨continuous_thetaCuspFullSource, exists_abs_thetaCuspFullSource_le⟩

namespace SuperExpSource

variable {f g : ℝ → ℝ}

theorem comp_add (hf : SuperExpSource f) (h : ℝ) : SuperExpSource fun u => f (u + h) := by
  refine ⟨hf.continuous.comp (continuous_add_const h), fun A => ?_⟩
  obtain ⟨C, hC, hb⟩ := hf.bound |A|
  refine ⟨C * Real.exp (|A| * |h|), by positivity, fun u => ?_⟩
  have h1 := hb (u + h)
  have h2 : |u| ≤ |u + h| + |h| := by
    have := abs_sub (u + h) h; rwa [add_sub_cancel_right] at this
  calc |f (u + h)| ≤ C * Real.exp (-(|A| * |u + h|)) := h1
    _ ≤ C * Real.exp (|A| * |h| + -(A * |u|)) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC
        nlinarith [le_abs_self A, abs_nonneg A, abs_nonneg u, mul_le_mul_of_nonneg_left h2 (abs_nonneg A)]
    _ = C * Real.exp (|A| * |h|) * Real.exp (-(A * |u|)) := by rw [Real.exp_add]; ring

theorem add (hf : SuperExpSource f) (hg : SuperExpSource g) : SuperExpSource fun u => f u + g u := by
  refine ⟨hf.continuous.add hg.continuous, fun A => ?_⟩
  obtain ⟨C₁, hC₁, h₁⟩ := hf.bound A
  obtain ⟨C₂, hC₂, h₂⟩ := hg.bound A
  exact ⟨C₁ + C₂, by positivity, fun u => (abs_add_le _ _).trans (by nlinarith [h₁ u, h₂ u])⟩

theorem const_mul (hf : SuperExpSource f) (c : ℝ) : SuperExpSource fun u => c * f u := by
  refine ⟨continuous_const.mul hf.continuous, fun A => ?_⟩
  obtain ⟨C, hC, h⟩ := hf.bound A
  refine ⟨|c| * C, by positivity, fun u => ?_⟩
  rw [abs_mul, mul_assoc]; exact mul_le_mul_of_nonneg_left (h u) (abs_nonneg c)

theorem mul_id (hf : SuperExpSource f) : SuperExpSource fun u => u * f u := by
  refine ⟨continuous_id.mul hf.continuous, fun A => ?_⟩
  obtain ⟨C, hC, h⟩ := hf.bound (A + 1)
  refine ⟨C, hC, fun u => ?_⟩
  rw [abs_mul]
  have hu : |u| ≤ Real.exp |u| := by linarith [Real.add_one_le_exp |u|]
  calc |u| * |f u| ≤ Real.exp |u| * (C * Real.exp (-((A + 1) * |u|))) :=
        mul_le_mul hu (h u) (abs_nonneg _) (Real.exp_pos _).le
    _ = C * Real.exp (-(A * |u|)) := by rw [mul_left_comm, ← Real.exp_add]; ring_nf

theorem integrable_cexp_mul (hf : SuperExpSource f) (w : ℂ) :
    Integrable fun x : ℝ => cexp (w * x) * (f x : ℂ) := by
  obtain ⟨C, hC, h⟩ := hf.bound (‖w‖ + 1)
  have hc := hf.continuous
  refine ((integrable_exp_neg_abs_line).const_mul C).mono' (by fun_prop)
    (Eventually.of_forall fun x => ?_)
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
  have hre : (w * x).re ≤ ‖w‖ * |x| :=
    (Complex.re_le_norm _).trans (by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs])
  calc Real.exp (w * x).re * |f x| ≤ Real.exp (‖w‖ * |x|) * (C * Real.exp (-((‖w‖ + 1) * |x|))) :=
        mul_le_mul (Real.exp_le_exp.mpr hre) (h x) (abs_nonneg _) (Real.exp_pos _).le
    _ = C * Real.exp (-|x|) := by rw [mul_left_comm, ← Real.exp_add]; ring_nf

theorem moment (hf : SuperExpSource f) (σ : ℝ) :
    IntegrableOn (fun u => Real.exp (σ * u) * ‖(f u : ℂ)‖) (Ioi 0) := by
  have h := (hf.integrable_cexp_mul σ).integrableOn (s := Ioi 0) |>.norm
  refine IntegrableOn.congr_fun h (fun u _ => ?_) measurableSet_Ioi
  rw [norm_mul, Complex.norm_exp]; simp

end SuperExpSource

/-- `X(w) = ∫_ℝ e^{wx} k(x) dx`. -/
theorem integral_cexp_mul_thetaCuspFullSource_eq_port (w : ℂ) :
    ∫ x : ℝ, cexp (w * x) * (thetaCuspFullSource x : ℂ) = thetaSymmetrizedPort w := by
  rw [integral_cexp_mul_thetaCuspFullSource, thetaSymmetrizedPort, thetaHalfLaplace_add_neg]

/-- **Translation law.** `∫_ℝ e^{wx} k(x + h) dx = e^{-wh} X(w)`. -/
theorem integral_cexp_mul_thetaCuspFullSource_add (w : ℂ) (h : ℝ) :
    ∫ x : ℝ, cexp (w * x) * (thetaCuspFullSource (x + h) : ℂ) = cexp (-(w * h)) * thetaSymmetrizedPort w := by
  set F : ℝ → ℂ := fun y => cexp (w * ((y : ℂ) - h)) * (thetaCuspFullSource y : ℂ)
  calc ∫ x : ℝ, cexp (w * x) * (thetaCuspFullSource (x + h) : ℂ) = ∫ x : ℝ, F (x + h) := by
        congr 1; ext x; simp only [F]; push_cast; ring_nf
    _ = ∫ x : ℝ, F x := integral_add_right_eq_self F h
    _ = cexp (-(w * h)) * thetaSymmetrizedPort w := by
        rw [← integral_cexp_mul_thetaCuspFullSource_eq_port, ← integral_const_mul]
        congr 1; ext y
        simp only [F]
        rw [show w * ((y : ℂ) - h) = -(w * h) + w * y by ring, Complex.exp_add]; ring

/-- For an odd source, `∫_ℝ e^{wx} f = ∫₀^∞ f(u)(e^{wu} - e^{-wu}) du`. -/
theorem integral_cexp_mul_of_odd {f : ℝ → ℝ} (hf : SuperExpSource f) (hodd : ∀ u, f (-u) = -f u)
    (w : ℂ) : ∫ x : ℝ, cexp (w * x) * (f x : ℂ) =
      ∫ u in Ioi (0 : ℝ), (f u : ℂ) * (cexp (w * u) - cexp (-(w * u))) := by
  have hint := hf.integrable_cexp_mul w
  rw [← intervalIntegral.integral_Iic_add_Ioi hint.integrableOn hint.integrableOn]
  have hneg : ∫ x in Iic (0 : ℝ), cexp (w * x) * (f x : ℂ) =
      ∫ u in Ioi (0 : ℝ), -(cexp (-(w * u)) * (f u : ℂ)) := by
    have h2 := integral_comp_neg_Iic 0 (fun u : ℝ => -(cexp (-(w * u)) * (f u : ℂ)))
    rw [neg_zero] at h2
    rw [← h2]
    refine setIntegral_congr_fun measurableSet_Iic fun x _ => ?_
    simp only [hodd, Complex.ofReal_neg, neg_neg, mul_neg]
  rw [hneg, ← integral_add ((hf.integrable_cexp_mul (-w)).integrableOn.neg.congr_fun
    (fun u _ => by simp [neg_mul]) measurableSet_Ioi) hint.integrableOn]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  ring

/-- For an even source, `∫_ℝ e^{wx} f = L_f(w) + L_f(-w)`. -/
theorem integral_cexp_mul_of_even {f : ℝ → ℝ} (hf : SuperExpSource f) (heven : ∀ u, f (-u) = f u)
    (w : ℂ) : ∫ x : ℝ, cexp (w * x) * (f x : ℂ) =
      halfLineExpTransform (fun u => (f u : ℂ)) w + halfLineExpTransform (fun u => (f u : ℂ)) (-w) := by
  have hint := hf.integrable_cexp_mul w
  rw [← intervalIntegral.integral_Iic_add_Ioi hint.integrableOn hint.integrableOn, add_comm,
    halfLineExpTransform, halfLineExpTransform]
  congr 1
  have h2 := integral_comp_neg_Iic 0 (fun u : ℝ => cexp (-w * u) * (f u : ℂ))
  rw [neg_zero] at h2
  rw [← h2]
  refine setIntegral_congr_fun measurableSet_Iic fun x _ => ?_
  simp only [heven, Complex.ofReal_neg]
  ring_nf

theorem SuperExpSource.sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ}
    (hf : ∀ i ∈ s, SuperExpSource (f i)) : SuperExpSource fun u => ∑ i ∈ s, f i u := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨continuous_const, fun A => ⟨0, le_rfl, fun u => by simp⟩⟩
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self i s)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-! ## Odd translation polynomials lie in the Xi ideal (6) -/

/-- The odd part `j(u) = ½ Σ c_i [k(u + h_i) - k(u - h_i)]` of a finite real translation
polynomial of the literal source. -/
def translationOddPart {n : ℕ} (c h : Fin n → ℝ) (u : ℝ) : ℝ :=
  1 / 2 * ∑ i, c i * (thetaCuspFullSource (u + h i) - thetaCuspFullSource (u - h i))

theorem translationOddPart_neg {n : ℕ} (c h : Fin n → ℝ) (u : ℝ) :
    translationOddPart c h (-u) = -translationOddPart c h u := by
  rw [translationOddPart, translationOddPart, ← mul_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show -u + h i = -(u - h i) by ring, show -u - h i = -(u + h i) by ring,
    thetaCuspFullSource_neg, thetaCuspFullSource_neg]
  ring

theorem translationOddPart_zero {n : ℕ} (c h : Fin n → ℝ) : translationOddPart c h 0 = 0 := by
  have := translationOddPart_neg c h 0
  rw [neg_zero] at this; linarith

theorem superExpSource_translationOddPart {n : ℕ} (c h : Fin n → ℝ) :
    SuperExpSource (translationOddPart c h) := by
  have hk := superExpSource_thetaCuspFullSource
  have hs := SuperExpSource.sum Finset.univ (f := fun i u => c i *
    (thetaCuspFullSource (u + h i) - thetaCuspFullSource (u - h i))) fun i _ =>
      ((hk.comp_add (h i)).add ((hk.comp_add (-h i)).const_mul (-1))).const_mul (c i) |>
        fun H => ⟨by have := continuous_thetaCuspFullSource; fun_prop, fun A => by
          obtain ⟨C, hC, hb⟩ := H.bound A
          exact ⟨C, hC, fun u => by
            have := hb u; simp only [sub_eq_add_neg, neg_one_mul] at this ⊢; exact this⟩⟩
  exact hs.const_mul (1 / 2)

/-- **The Xi ideal (6).** `∫_ℝ e^{wu} j(u) du = -X(w) Σ c_i sinh(h_i w)`. -/
theorem integral_cexp_mul_translationOddPart {n : ℕ} (c h : Fin n → ℝ) (w : ℂ) :
    ∫ x : ℝ, cexp (w * x) * (translationOddPart c h x : ℂ) =
      -(thetaSymmetrizedPort w * ∑ i, (c i : ℂ) * Complex.sinh (h i * w)) := by
  have hk := superExpSource_thetaCuspFullSource
  have hint : ∀ i, Integrable fun x : ℝ => (c i : ℂ) / 2 * (cexp (w * x) *
      (thetaCuspFullSource (x + h i) : ℂ) - cexp (w * x) * (thetaCuspFullSource (x + -h i) : ℂ)) :=
    fun i => (((hk.comp_add (h i)).integrable_cexp_mul w).sub
      ((hk.comp_add (-h i)).integrable_cexp_mul w)).const_mul _
  calc ∫ x : ℝ, cexp (w * x) * (translationOddPart c h x : ℂ)
      = ∫ x : ℝ, ∑ i, (c i : ℂ) / 2 * (cexp (w * x) * (thetaCuspFullSource (x + h i) : ℂ) -
          cexp (w * x) * (thetaCuspFullSource (x + -h i) : ℂ)) := by
        congr 1; ext x
        simp only [translationOddPart, sub_eq_add_neg]
        push_cast
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    _ = ∑ i, (c i : ℂ) / 2 * (cexp (-(w * h i)) * thetaSymmetrizedPort w -
          cexp (-(w * ((-h i : ℝ) : ℂ))) * thetaSymmetrizedPort w) := by
        rw [integral_finsetSum _ fun i _ => hint i]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_const_mul, integral_sub ((hk.comp_add (h i)).integrable_cexp_mul w)
          ((hk.comp_add (-h i)).integrable_cexp_mul w),
          integral_cexp_mul_thetaCuspFullSource_add, integral_cexp_mul_thetaCuspFullSource_add]
    _ = -(thetaSymmetrizedPort w * ∑ i, (c i : ℂ) * Complex.sinh (h i * w)) := by
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Complex.sinh]
        push_cast
        ring_nf

/-- **(6).** For the correction `a = 2j` on the positive ray, `Q_a(w) = -X(w) Σ c_i sinh(h_i w)`:
it vanishes at every Xi zero, on or off the critical line. -/
theorem causalCorrectionTransform_translation {n : ℕ} (c h : Fin n → ℝ) (w : ℂ) :
    causalCorrectionTransform (fun u => 2 * translationOddPart c h u) w =
      -(thetaSymmetrizedPort w * ∑ i, (c i : ℂ) * Complex.sinh (h i * w)) := by
  rw [← integral_cexp_mul_translationOddPart, integral_cexp_mul_of_odd
    (superExpSource_translationOddPart c h) (translationOddPart_neg c h), causalCorrectionTransform]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  rw [Complex.sinh]; push_cast; ring

theorem causalCorrectionTransform_translation_eq_zero {n : ℕ} (c h : Fin n → ℝ) {w : ℂ}
    (hw : thetaSymmetrizedPort w = 0) :
    causalCorrectionTransform (fun u => 2 * translationOddPart c h u) w = 0 := by
  rw [causalCorrectionTransform_translation, hw]; simp

/-- At a real zero the translation-corrected port is the raw port, and its imbalance has the
unchanged alternating raw normal derivative `-2 b(γ) Ξ'(γ)`. -/
theorem hasDerivAt_causalPortImbalance_translation {n : ℕ} (c h : Fin n → ℝ) {γ : ℝ}
    (hγ : Xi γ = 0) :
    HasDerivAt (fun α : ℝ => causalPortImbalance (fun u => 2 * translationOddPart c h u) (α + γ * I))
      (-2 * thetaHalfSineResponse γ * deriv Xi γ) 0 := by
  set a : ℝ → ℝ := fun u => 2 * translationOddPart c h u
  have hE : causalPort a = fun w => thetaHalfLaplace w +
      -(thetaSymmetrizedPort w * ∑ i, (c i : ℂ) * Complex.sinh (h i * w)) := by
    funext w; rw [causalPort, causalCorrectionTransform_translation]
  have hdiff : Differentiable ℂ (causalPort a) := by
    rw [hE]
    refine differentiable_thetaHalfLaplace.add (differentiable_thetaSymmetrizedPort.mul ?_).neg
    exact Differentiable.fun_sum fun i _ => (differentiable_const _).mul
      ((differentiable_const _).mul differentiable_id).csinh
  have hX : thetaSymmetrizedPort (γ * I) = 0 := by
    rw [thetaSymmetrizedPort_mul_I, hγ, Complex.ofReal_zero]
  have h := hasDerivAt_portImbalance_of_zero ((hdiff (γ * I)).hasDerivAt)
    (causalPort_add_reflect a) hX
  refine h.congr_deriv ?_
  rw [causalPort, causalCorrectionTransform_translation, hX, zero_mul, neg_zero, add_zero,
    thetaHalfLaplace_I_mul_of_Xi_eq_zero hγ, deriv_thetaSymmetrizedPort_mul_I, Complex.inner]
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-! ## The log-time clock and translations (7) -/

/-- The log-time clock `(Uf)(u) = u f(u)`. -/
def logTimeClock (f : ℝ → ℝ) (u : ℝ) : ℝ := u * f u

/-- The translation `(T_h f)(u) = f(u + h)`. -/
def logTimeShift (h : ℝ) (f : ℝ → ℝ) (u : ℝ) : ℝ := f (u + h)

/-- **(7).** `[U, T_h] = -h T_h`. -/
theorem logTimeClock_shift_commutator (h : ℝ) (f : ℝ → ℝ) (u : ℝ) :
    logTimeClock (logTimeShift h f) u - logTimeShift h (logTimeClock f) u = -h * logTimeShift h f u := by
  simp only [logTimeClock, logTimeShift]; ring

/-- The odd source part of `[U, T_h] k` is a translation polynomial, hence Xi-divisible. -/
theorem oddPart_logTimeClock_commutator (h u : ℝ) :
    (logTimeClock (logTimeShift h thetaCuspFullSource) u -
        logTimeShift h (logTimeClock thetaCuspFullSource) u -
      (logTimeClock (logTimeShift h thetaCuspFullSource) (-u) -
        logTimeShift h (logTimeClock thetaCuspFullSource) (-u))) / 2 =
      translationOddPart ![-h] ![h] u := by
  rw [logTimeClock_shift_commutator, logTimeClock_shift_commutator, translationOddPart]
  simp only [logTimeShift, Fin.sum_univ_one, Matrix.cons_val_zero]
  rw [show -u + h = -(u - h) by ring, thetaCuspFullSource_neg]
  ring

/-! ## The one-prime deleted source (8) and its moment correction (9) -/

/-- The symmetric one-prime deletion `g_p(u) = k(u) - p^{-1/2}[k(u + log p) + k(u - log p)]/2`. -/
def primeDeletedSource (p u : ℝ) : ℝ :=
  thetaCuspFullSource u - p ^ (-(1 / 2 : ℝ)) *
    (thetaCuspFullSource (u + Real.log p) + thetaCuspFullSource (u - Real.log p)) / 2

theorem primeDeletedSource_neg (p u : ℝ) : primeDeletedSource p (-u) = primeDeletedSource p u := by
  rw [primeDeletedSource, primeDeletedSource, thetaCuspFullSource_neg,
    show -u + Real.log p = -(u - Real.log p) by ring, show -u - Real.log p = -(u + Real.log p) by ring,
    thetaCuspFullSource_neg, thetaCuspFullSource_neg]
  ring

theorem superExpSource_primeDeletedSource (p : ℝ) : SuperExpSource (primeDeletedSource p) := by
  have hk := superExpSource_thetaCuspFullSource
  have h := hk.add ((((hk.comp_add (Real.log p)).add (hk.comp_add (-Real.log p))).const_mul
    (p ^ (-(1 / 2 : ℝ)) / 2)).const_mul (-1))
  refine ⟨by unfold primeDeletedSource; have := continuous_thetaCuspFullSource; fun_prop,
    fun A => ?_⟩
  obtain ⟨C, hC, hb⟩ := h.bound A
  refine ⟨C, hC, fun u => ?_⟩
  have := hb u
  simp only [primeDeletedSource, sub_eq_add_neg] at this ⊢
  convert this using 2
  ring

/-- **(8).** `∫_ℝ e^{wu} g_p(u) du = [1 - p^{-1/2} cosh(w log p)] X(w)`. -/
theorem integral_cexp_mul_primeDeletedSource (p : ℝ) (w : ℂ) :
    ∫ x : ℝ, cexp (w * x) * (primeDeletedSource p x : ℂ) =
      primeDeletionSymbol p w * thetaSymmetrizedPort w := by
  have hk := superExpSource_thetaCuspFullSource
  have h1 := hk.integrable_cexp_mul w
  have h2 := (hk.comp_add (Real.log p)).integrable_cexp_mul w
  have h3 := (hk.comp_add (-Real.log p)).integrable_cexp_mul w
  have e : (fun x : ℝ => cexp (w * x) * (primeDeletedSource p x : ℂ)) = fun x : ℝ =>
      cexp (w * x) * (thetaCuspFullSource x : ℂ) -
        ((p ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) / 2 * (cexp (w * x) * (thetaCuspFullSource (x + Real.log p) : ℂ) +
          cexp (w * x) * (thetaCuspFullSource (x + -Real.log p) : ℂ)) := by
    funext x; simp only [primeDeletedSource, sub_eq_add_neg]; push_cast; ring
  have h23 : Integrable fun x : ℝ => ((p ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) / 2 *
      (cexp (w * x) * (thetaCuspFullSource (x + Real.log p) : ℂ) +
        cexp (w * x) * (thetaCuspFullSource (x + -Real.log p) : ℂ)) := (h2.add h3).const_mul _
  rw [e, integral_sub h1 h23, integral_const_mul, integral_add h2 h3,
    integral_cexp_mul_thetaCuspFullSource_eq_port, integral_cexp_mul_thetaCuspFullSource_add,
    integral_cexp_mul_thetaCuspFullSource_add, primeDeletionSymbol, Complex.cosh]
  push_cast
  ring_nf

/-- The moment correction `a_p(u) = -k(u) + 2u g_p(u)`. -/
def primeMomentCorrection (p u : ℝ) : ℝ := -thetaCuspFullSource u + 2 * u * primeDeletedSource p u

/-- `a_p` cancels every even jet of the source at the cut: `k + a_p = 2u g_p` is odd. -/
theorem iteratedDeriv_even_primeMomentCorrection (p : ℝ) (m : ℕ) :
    iteratedDeriv (2 * m) (fun u => thetaCuspFullSource u + primeMomentCorrection p u) 0 = 0 := by
  set f : ℝ → ℝ := fun u => thetaCuspFullSource u + primeMomentCorrection p u
  have hodd : (fun x => f (-x)) = -f := by
    funext x
    simp only [f, primeMomentCorrection, Pi.neg_apply, primeDeletedSource_neg,
      thetaCuspFullSource_neg]
    ring
  have h := iteratedDeriv_comp_neg (2 * m) f 0
  rw [hodd, iteratedDeriv_neg, neg_zero, pow_mul, neg_one_sq, one_pow, one_smul] at h
  linarith

/-- **(9).** The exact port of the moment correction is `E_p = X/2 + (A_p X)'`. -/
theorem causalPort_primeMomentCorrection {p : ℝ} (hp : 1 < p) (w : ℂ) :
    causalPort (primeMomentCorrection p) w = primeMomentPort p w := by
  have hg := superExpSource_primeDeletedSource p
  have hug := hg.mul_id
  have hmeas : AEStronglyMeasurable (fun u : ℝ => (primeDeletedSource p u : ℂ))
      (volume.restrict (Ioi 0)) :=
    (Complex.continuous_ofReal.comp hg.continuous).aestronglyMeasurable
  -- `A_p X = L_g(z) + L_g(-z)` with `L_g` the half-line transform of the even source `g_p`
  have hG : (fun z => primeDeletionSymbol p z * thetaSymmetrizedPort z) = fun z =>
      halfLineExpTransform (fun u => (primeDeletedSource p u : ℂ)) z +
        halfLineExpTransform (fun u => (primeDeletedSource p u : ℂ)) (-z) := by
    funext z
    rw [← integral_cexp_mul_primeDeletedSource,
      integral_cexp_mul_of_even hg (primeDeletedSource_neg p)]
  have hL : ∀ z : ℂ, HasDerivAt (halfLineExpTransform fun u => (primeDeletedSource p u : ℂ))
      (halfLineExpTransform (fun u => (u : ℂ) * (primeDeletedSource p u : ℂ)) z) z := fun z =>
    hasDerivAt_halfLineExpTransform hmeas (hg.moment (z.re + 1)) (by linarith)
  have hderiv : deriv (fun z => primeDeletionSymbol p z * thetaSymmetrizedPort z) w =
      halfLineExpTransform (fun u => (u : ℂ) * (primeDeletedSource p u : ℂ)) w -
        halfLineExpTransform (fun u => (u : ℂ) * (primeDeletedSource p u : ℂ)) (-w) := by
    rw [hG]
    have h := (hL w).add ((hL (-w)).comp w (hasDerivAt_neg w))
    rw [show (fun z => halfLineExpTransform (fun u => (primeDeletedSource p u : ℂ)) z +
        halfLineExpTransform (fun u => (primeDeletedSource p u : ℂ)) (-z)) =
      (halfLineExpTransform fun u => (primeDeletedSource p u : ℂ)) +
        (halfLineExpTransform fun u => (primeDeletedSource p u : ℂ)) ∘ Neg.neg from rfl, h.deriv]
    ring
  rw [primeMomentPort_eq hp, hderiv, causalPort, causalCorrectionTransform, thetaSymmetrizedPort,
    thetaHalfLaplace, thetaHalfLaplaceTail, thetaHalfLaplace, thetaHalfLaplaceTail,
    halfLineExpTransform, halfLineExpTransform]
  have hk1 := integrableOn_cexp_mul_thetaCuspFullSource w (Ioi 0)
  have hk2 := integrableOn_cexp_mul_thetaCuspFullSource (-w) (Ioi 0)
  have hu1 : IntegrableOn (fun u : ℝ => cexp (w * u) * ((u : ℂ) * (primeDeletedSource p u : ℂ)))
      (Ioi 0) := (hug.integrable_cexp_mul w).integrableOn.congr_fun (fun u _ => by push_cast; ring)
        measurableSet_Ioi
  have hu2 : IntegrableOn (fun u : ℝ => cexp (-w * u) * ((u : ℂ) * (primeDeletedSource p u : ℂ)))
      (Ioi 0) := (hug.integrable_cexp_mul (-w)).integrableOn.congr_fun (fun u _ => by push_cast; ring)
        measurableSet_Ioi
  have hf1 : IntegrableOn (fun u : ℝ => -(cexp (w * u) * (thetaCuspFullSource u : ℂ) -
      cexp (-w * u) * (thetaCuspFullSource u : ℂ)) / 2) (Ioi 0) := (hk1.sub hk2).neg.div_const 2
  have hf2 : IntegrableOn (fun u : ℝ => cexp (w * u) * ((u : ℂ) * (primeDeletedSource p u : ℂ)) -
      cexp (-w * u) * ((u : ℂ) * (primeDeletedSource p u : ℂ))) (Ioi 0) := hu1.sub hu2
  have hQ : (∫ u in Ioi (0 : ℝ), (primeMomentCorrection p u : ℂ) * Complex.sinh (w * u)) =
      ∫ u in Ioi (0 : ℝ), ((-(cexp (w * u) * (thetaCuspFullSource u : ℂ) -
          cexp (-w * u) * (thetaCuspFullSource u : ℂ)) / 2) +
          (cexp (w * u) * ((u : ℂ) * (primeDeletedSource p u : ℂ)) -
          cexp (-w * u) * ((u : ℂ) * (primeDeletedSource p u : ℂ)))) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    simp only [primeMomentCorrection, Complex.sinh, neg_mul]
    push_cast
    ring
  rw [hQ, integral_add hf1 hf2, integral_div, integral_neg, integral_sub hk1 hk2,
    integral_sub hu1 hu2]
  simp only [neg_mul]
  ring

end

end RHTower
