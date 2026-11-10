import GaloisForLFunctions.SelectiveArithmetic.TheLiouvilleTwistFailsBeyondTheTrivialAperture
import GaloisForLFunctions.SelectiveArithmetic.TheHeightOfAPacketIsAMass

/-!
# A pole at the height fails beyond the trivial aperture

In the aspect of the height the sizes of the contacts pay Weil's form of every dominated system
with pole plane, on packets of bounded shape, up to the aperture `log log |t| − o(1)`
(`exists_height_margin`). Here the other side: beyond `log log |t| + log 2` the sizes pay nothing.

The **system aligned with the height `t`** has the contacts `w_t(n) = Λ(n) cos(t log n)`, half the
contacts of `ζ(s + it) ζ(s − it)`. It is dominated, and its poles sit at the heights `±t`, where
the pole plane of Weil's functional does not reach.

* **The correlation of a modulated packet** (`weilTest_modulatedTest`,
  `contactForm_modulatedTest`): for `F(u) = e^{−itu} f(u)` the correlation is
  `e^{−itx} (f ⋆ f̃)(x)`, so a contact `w(n)` is seen with the phase `cos(t log n)`. On its own
  height the aligned system is seen with `cos²(t log n)`.
* **Half of the contacts survive at some height** (`exists_height_contactForm_aligned_ge`): the
  mean of `cos²(t x)` over `t ∈ [T, 2T]` is at least `½ − 1/T` for `x ≥ ½`, so at some height of
  every dyadic window the contact form of the aligned system on a packet with nonnegative
  correlation is at least `(½ − 1/T)` times the contact form of the primes.
* **The upper bound of Weil's form at a height** (`re_weilFullFunctional_modulated_le`): for
  `e^{a} ≤ |t|` it is at most `(log(2 + |t|) + 5) ∫ f² + 5 ∫ f'²` minus the contact form.
* **The aligned system fails** (`exists_aligned_height_neg`, `exists_dominated_height_neg`): for
  every `η > 0`, every `C ≥ 0` and every large `T`, at every aperture
  `log log T + log 2 + η ≤ a ≤ log T` there is a height `t ∈ [T, 2T]` at which Weil's form of the
  aligned system on the modulated even polar packet is below `−C ∫ f'²`.

So in the aspect of the height the trivial aperture is `log log |t| + O(1)`: no margin
`c log |t| ∫ f² − C ∫ f'²` holds for all dominated systems beyond `log log |t| + log 2`. The
balance is that of the conductor: the mass `log t · e^{a}/2` of the polar packet against a quarter
of the Riesz mean `e^{2a}` of the primes.
-/

open Filter Topology MeasureTheory
open Zeta23
open scoped ArithmeticFunction.vonMangoldt Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SelectiveArithmetic

open AbsoluteGeometryOfSpecZ BiScaleUncertainty

/-! ### The correlation of a modulated packet -/

theorem modulatedTest_mul_conj (t : ℝ) (f : ℝ → ℝ) (u x : ℝ) :
    _root_.RHTower.modulatedTest t f u * conj (_root_.RHTower.modulatedTest t f (u - x)) =
      Complex.exp (-(Complex.I * (t : ℂ) * (x : ℂ))) *
        ((f u : ℂ) * conj ((f (u - x) : ℝ) : ℂ)) := by
  show Complex.exp (-(Complex.I * (t : ℂ) * (u : ℂ))) * (f u : ℂ) *
      conj (Complex.exp (-(Complex.I * (t : ℂ) * ((u - x : ℝ) : ℂ))) *
        ((f (u - x) : ℝ) : ℂ)) = _
  have hc : conj (Complex.exp (-(Complex.I * (t : ℂ) * ((u - x : ℝ) : ℂ)))) =
      Complex.exp (Complex.I * (t : ℂ) * ((u - x : ℝ) : ℂ)) := by
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  have he : Complex.exp (-(Complex.I * (t : ℂ) * (u : ℂ))) *
      Complex.exp (Complex.I * (t : ℂ) * ((u - x : ℝ) : ℂ)) =
      Complex.exp (-(Complex.I * (t : ℂ) * (x : ℂ))) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [map_mul, hc, ← he]
  ring

/-- **The correlation of a packet modulated to the height `t`** is `e^{−itx}` times the
correlation of the packet. -/
theorem weilTest_modulatedTest (t : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    EF.weilTest (_root_.RHTower.modulatedTest t f) (_root_.RHTower.modulatedTest t f) x =
      Complex.exp (-(Complex.I * (t : ℂ) * (x : ℂ))) * ((packetAutocorr f x : ℝ) : ℂ) := by
  rw [← weilTest_packet, _root_.RHTower.WeilSpectral.weilTest_apply,
    _root_.RHTower.WeilSpectral.weilTest_apply, ← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun u => modulatedTest_mul_conj t f u x)

theorem re_exp_neg_I_mul (t x : ℝ) :
    (Complex.exp (-(Complex.I * (t : ℂ) * (x : ℂ)))).re = Real.cos (t * x) := by
  have h : -(Complex.I * (t : ℂ) * (x : ℂ)) = ((-(t * x) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.exp_ofReal_mul_I_re, Real.cos_neg]

/-- At the lags `±x` a modulated packet shows the phase `cos(tx)`. -/
theorem re_weilTest_modulatedTest_add_neg (t : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    (EF.weilTest (_root_.RHTower.modulatedTest t f) (_root_.RHTower.modulatedTest t f) x +
        EF.weilTest (_root_.RHTower.modulatedTest t f) (_root_.RHTower.modulatedTest t f)
          (-x)).re = 2 * Real.cos (t * x) * packetAutocorr f x := by
  rw [weilTest_modulatedTest, weilTest_modulatedTest, packetAutocorr_neg, Complex.add_re,
    Complex.re_mul_ofReal, Complex.re_mul_ofReal, re_exp_neg_I_mul, re_exp_neg_I_mul, mul_neg,
    Real.cos_neg]
  ring

/-- **The contact form on a modulated packet**: the contact `w(n)` is seen with the phase
`cos(t log n)`. -/
theorem contactForm_modulatedTest (w : ℕ → ℝ) (t : ℝ) (f : ℝ → ℝ) (N : ℕ) :
    contactForm w (_root_.RHTower.modulatedTest t f) N =
      ∑ n ∈ Finset.Icc 2 N, w n / Real.sqrt n *
        (2 * Real.cos (t * Real.log n) * packetAutocorr f (Real.log n)) := by
  unfold contactForm
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [re_weilTest_modulatedTest_add_neg]

/-! ### The system aligned with a height -/

/-- The contacts of the system aligned with the height `t`: `Λ(n) cos(t log n)`, half the
contacts of `ζ(s + it) ζ(s − it)`. -/
def alignedWeight (t : ℝ) (n : ℕ) : ℝ := Λ n * Real.cos (t * Real.log n)

theorem dominated_alignedWeight (t : ℝ) : Dominated (alignedWeight t) := fun n => by
  unfold alignedWeight
  rw [abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  exact mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg (Real.abs_cos_le_one _)

/-! ### Half of the contacts survive at some height -/

/-- The mean of `cos²(tx)` over a dyadic window of heights: `∫_T^{2T} cos²(tx) dt ≥ T/2 − 1`
for `x ≥ ½`. -/
theorem integral_cos_mul_sq_ge {x : ℝ} (hx : 1 / 2 ≤ x) (T : ℝ) :
    T / 2 - 1 ≤ ∫ t in T..2 * T, Real.cos (t * x) ^ 2 := by
  have hx0 : 0 < x := by linarith
  have h : ∫ t in T..2 * T, Real.cos (t * x) ^ 2 =
      x⁻¹ • ∫ y in T * x..2 * T * x, Real.cos y ^ 2 :=
    intervalIntegral.integral_comp_mul_right (fun y => Real.cos y ^ 2) hx0.ne'
  rw [h, integral_cos_sq, smul_eq_mul]
  have h1 : -1 ≤ 2 * (Real.cos (2 * T * x) * Real.sin (2 * T * x)) := by
    nlinarith [sq_nonneg (Real.cos (2 * T * x) + Real.sin (2 * T * x)),
      Real.cos_sq_add_sin_sq (2 * T * x)]
  have h2 : 2 * (Real.cos (T * x) * Real.sin (T * x)) ≤ 1 := by
    nlinarith [sq_nonneg (Real.cos (T * x) - Real.sin (T * x)), Real.cos_sq_add_sin_sq (T * x)]
  have hinv0 : 0 < x⁻¹ := inv_pos.mpr hx0
  have hinv2 : x⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hx0 (by norm_num)]
    linarith
  have hxx : x⁻¹ * x = 1 := inv_mul_cancel₀ hx0.ne'
  have hP := mul_le_mul_of_nonneg_left
    (by linarith : (-1 : ℝ) ≤ Real.cos (2 * T * x) * Real.sin (2 * T * x) -
      Real.cos (T * x) * Real.sin (T * x)) hinv0.le
  have e : x⁻¹ * ((Real.cos (2 * T * x) * Real.sin (2 * T * x) -
        Real.cos (T * x) * Real.sin (T * x) + 2 * T * x - T * x) / 2) =
      x⁻¹ * (Real.cos (2 * T * x) * Real.sin (2 * T * x) -
        Real.cos (T * x) * Real.sin (T * x)) / 2 + T / 2 * (x⁻¹ * x) := by ring
  rw [e, hxx]
  linarith

/-- **Half of a nonnegative sum survives at some height.** For nonnegative coefficients on
integers `n ≥ 2` there is a height `t ∈ [T, 2T]` with
`Σ c(n) cos²(t log n) ≥ (½ − 1/T) Σ c(n)`: the maximum over the window is at least the mean. -/
theorem exists_height_sum_cos_sq_ge (s : Finset ℕ) (c : ℕ → ℝ) (hc : ∀ n ∈ s, 0 ≤ c n)
    (hs : ∀ n ∈ s, 2 ≤ n) {T : ℝ} (hT : 0 < T) :
    ∃ t ∈ Set.Icc T (2 * T),
      (1 / 2 - 1 / T) * ∑ n ∈ s, c n ≤ ∑ n ∈ s, c n * Real.cos (t * Real.log n) ^ 2 := by
  have hterm : ∀ n : ℕ, Continuous fun t : ℝ => c n * Real.cos (t * Real.log n) ^ 2 :=
    fun n => by fun_prop
  have hGc : Continuous fun t : ℝ => ∑ n ∈ s, c n * Real.cos (t * Real.log n) ^ 2 :=
    continuous_finset_sum _ fun n _ => hterm n
  have hTle : T ≤ 2 * T := by linarith
  obtain ⟨t₀, ht₀, hmax⟩ := (isCompact_Icc (a := T) (b := 2 * T)).exists_isMaxOn
    ⟨T, Set.left_mem_Icc.mpr hTle⟩ hGc.continuousOn
  refine ⟨t₀, ht₀, ?_⟩
  -- the mean over the window is at most the maximum
  have hup : ∫ t in T..2 * T, ∑ n ∈ s, c n * Real.cos (t * Real.log n) ^ 2 ≤
      T * ∑ n ∈ s, c n * Real.cos (t₀ * Real.log n) ^ 2 := by
    have h := intervalIntegral.integral_mono_on hTle (hGc.intervalIntegrable _ _)
      (intervalIntegrable_const (c := ∑ n ∈ s, c n * Real.cos (t₀ * Real.log n) ^ 2))
      fun t ht => isMaxOn_iff.mp hmax t ht
    rw [intervalIntegral.integral_const, smul_eq_mul] at h
    exact h.trans (le_of_eq (by ring))
  -- the mean of every term is at least `(T/2 − 1) c(n)`
  have hlow : (T / 2 - 1) * ∑ n ∈ s, c n ≤
      ∫ t in T..2 * T, ∑ n ∈ s, c n * Real.cos (t * Real.log n) ^ 2 := by
    rw [intervalIntegral.integral_finset_sum fun n _ => (hterm n).intervalIntegrable _ _,
      Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    rw [intervalIntegral.integral_const_mul]
    have hlog : 1 / 2 ≤ Real.log n := by
      have h2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
        have := Real.log_two_gt_d9
        linarith
      exact h2.trans (Real.log_le_log (by norm_num) (by exact_mod_cast hs n hn))
    have h := mul_le_mul_of_nonneg_left (integral_cos_mul_sq_ge hlog T) (hc n hn)
    linarith
  have hfin := hlow.trans hup
  have e : T * ((1 / 2 - 1 / T) * ∑ n ∈ s, c n) = (T / 2 - 1) * ∑ n ∈ s, c n := by
    have hTT : T * (1 / T) = 1 := mul_one_div_cancel hT.ne'
    linear_combination (-(∑ n ∈ s, c n)) * hTT
  exact le_of_mul_le_mul_left (by rw [e]; exact hfin) hT

/-- **At some height of every dyadic window the aligned system keeps half of the contact form of
the primes**, on a packet with nonnegative correlation. -/
theorem exists_height_contactForm_aligned_ge {f : ℝ → ℝ} (hA : ∀ y, 0 ≤ packetAutocorr f y)
    (N : ℕ) {T : ℝ} (hT : 0 < T) :
    ∃ t ∈ Set.Icc T (2 * T),
      (1 / 2 - 1 / T) * contactForm (fun n => Λ n) (fun u => (f u : ℂ)) N ≤
        contactForm (alignedWeight t) (_root_.RHTower.modulatedTest t f) N := by
  obtain ⟨t, ht, h⟩ := exists_height_sum_cos_sq_ge (Finset.Icc 2 N)
    (fun n => (Λ n : ℝ) / Real.sqrt n * (2 * packetAutocorr f (Real.log n)))
    (fun n _ => mul_nonneg
      (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
      (mul_nonneg zero_le_two (hA _)))
    (fun n hn => (Finset.mem_Icc.mp hn).1) hT
  refine ⟨t, ht, ?_⟩
  rw [contactForm_packet, contactForm_modulatedTest]
  refine h.trans (le_of_eq (Finset.sum_congr rfl fun n _ => ?_))
  show (Λ n : ℝ) / Real.sqrt n * (2 * packetAutocorr f (Real.log n)) *
      Real.cos (t * Real.log n) ^ 2 =
    Λ n * Real.cos (t * Real.log n) / Real.sqrt n *
      (2 * Real.cos (t * Real.log n) * packetAutocorr f (Real.log n))
  ring

/-! ### The upper bound of Weil's form at a height -/

/-- `S_∞(τ) ≤ log(2 + |t|) + 5 + (τ − t)²`. -/
theorem archimedeanWeilSymbol_le_height (τ t : ℝ) :
    _root_.RHTower.archimedeanWeilSymbol (τ / (2 * π)) ≤
      Real.log (2 + |t|) + 5 + (τ - t) ^ 2 := by
  have h := _root_.RHTower.archimedeanWeilSymbol_le_log_add τ
  have h1 : Real.log (1 + |τ|) ≤ Real.log (2 + |τ|) :=
    Real.log_le_log (by positivity) (by linarith)
  have h2 := log_two_add_abs_le t τ
  have e : (t - τ) ^ 2 = (τ - t) ^ 2 := by ring
  rw [e] at h2
  linarith

/-- **The archimedean energy at a height, from above**:
`(1/2π) ∫ |F̂|² S_∞ ≤ (log(2 + |t|) + 5) ∫ f² + ∫ f'²`. -/
theorem integral_arch_modulated_le {a : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (h0 : ∀ u, a ≤ |u| → f u = 0) (t : ℝ) :
    1 / (2 * π) * ∫ τ : ℝ, ‖paperFT (_root_.RHTower.modulatedTest t f) τ‖ ^ 2 *
        _root_.RHTower.archimedeanWeilSymbol (τ / (2 * π)) ≤
      (Real.log (2 + |t|) + 5) * (∫ u, f u ^ 2) + ∫ u, deriv f u ^ 2 := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hF := _root_.RHTower.modulatedTest_contDiff t hf2
  have hFs := _root_.RHTower.tsupport_modulatedTest_subset t (abs_le_of_ne_zero h0)
  have hG := _root_.RHTower.modulatedTest_contDiff t (contDiff_two_deriv hf)
  have hGs := _root_.RHTower.tsupport_modulatedTest_subset t (deriv_abs_le_of_ne_zero h0)
  have hI := _root_.RHTower.integrable_normSq_paperFT hF hFs
  have hI' := _root_.RHTower.integrable_normSq_paperFT hG hGs
  set L := Real.log (2 + |t|) + 5 with hL
  have hnorm : ∀ τ : ℝ, ‖paperFT (_root_.RHTower.modulatedTest t (deriv f)) τ‖ ^ 2 =
      (τ - t) ^ 2 * ‖paperFT (_root_.RHTower.modulatedTest t f) τ‖ ^ 2 := fun τ => by
    rw [paperFT_modulatedTest_deriv hf h0, norm_mul, mul_pow, norm_neg, norm_mul,
      Complex.norm_I, one_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hmono : ∫ τ : ℝ, ‖paperFT (_root_.RHTower.modulatedTest t f) τ‖ ^ 2 *
        _root_.RHTower.archimedeanWeilSymbol (τ / (2 * π)) ≤
      ∫ τ : ℝ, (L * ‖paperFT (_root_.RHTower.modulatedTest t f) τ‖ ^ 2 +
        ‖paperFT (_root_.RHTower.modulatedTest t (deriv f)) τ‖ ^ 2) := by
    refine integral_mono (_root_.RHTower.integrable_normSq_paperFT_mul_arch hF hFs)
      ((hI.const_mul L).add hI') fun τ => ?_
    show ‖paperFT (_root_.RHTower.modulatedTest t f) τ‖ ^ 2 *
        _root_.RHTower.archimedeanWeilSymbol (τ / (2 * π)) ≤
      L * ‖paperFT (_root_.RHTower.modulatedTest t f) τ‖ ^ 2 +
        ‖paperFT (_root_.RHTower.modulatedTest t (deriv f)) τ‖ ^ 2
    rw [hnorm]
    have h3 : _root_.RHTower.archimedeanWeilSymbol (τ / (2 * π)) ≤ L + (τ - t) ^ 2 := by
      rw [hL]
      exact archimedeanWeilSymbol_le_height τ t
    nlinarith [mul_le_mul_of_nonneg_left h3
      (sq_nonneg ‖paperFT (_root_.RHTower.modulatedTest t f) τ‖)]
  rw [integral_add (hI.const_mul L) hI', integral_const_mul,
    _root_.RHTower.integral_norm_paperFT_sq hF hFs,
    _root_.RHTower.integral_norm_paperFT_sq hG hGs, integral_norm_modulatedTest_sq,
    integral_norm_modulatedTest_sq] at hmono
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have h1 := mul_le_mul_of_nonneg_left hmono (by positivity : (0 : ℝ) ≤ 1 / (2 * π))
  have e : 1 / (2 * π) * (L * (2 * π * ∫ u, f u ^ 2) + 2 * π * ∫ u, deriv f u ^ 2) =
      L * (∫ u, f u ^ 2) + ∫ u, deriv f u ^ 2 := by
    field_simp
  rwa [e] at h1

/-- **Weil's form of a system with pole plane at a height, from above.** For `e^{a} ≤ |t|`, on a
packet modulated to the height `t`:
`Re W_w(F ⋆ F̃) ≤ (log(2 + |t|) + 5) ∫ f² + 5 ∫ f'²` minus the contact form. -/
theorem re_weilFullFunctional_modulated_le {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 3 f) (h0 : ∀ u, a ≤ |u| → f u = 0) (w : ℕ → ℝ) {t : ℝ}
    (ht : Real.exp a ≤ |t|) :
    (_root_.RHTower.weilFullFunctional w (EF.weilTest (_root_.RHTower.modulatedTest t f)
        (_root_.RHTower.modulatedTest t f))).re ≤
      (Real.log (2 + |t|) + 5) * (∫ u, f u ^ 2) + 5 * (∫ u, deriv f u ^ 2) -
        contactForm w (_root_.RHTower.modulatedTest t f) ⌊Real.exp (2 * a)⌋₊ := by
  have hF := _root_.RHTower.modulatedTest_contDiff t
    (hf.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))
  have hFs := _root_.RHTower.tsupport_modulatedTest_subset t (abs_le_of_ne_zero h0)
  have hpole := (abs_le.mp (abs_re_weilPoleTerm_modulated_le ha hf h0 ht)).2
  have harch := integral_arch_modulated_le hf h0 t
  have hsys := systemForm_eq hF hFs w 1
  rw [Real.log_one, zero_mul, add_zero] at hsys
  have e : systemForm w 1 a (_root_.RHTower.modulatedTest t f) =
      1 / (2 * π) * ∫ τ : ℝ, ‖paperFT (_root_.RHTower.modulatedTest t f) τ‖ ^ 2 *
        _root_.RHTower.weilAtomSymbol w ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) := by
    unfold systemForm
    simp only [Real.log_one, add_zero]
  rw [re_weilFullFunctional_eq_pole_add_symbol w hF hFs, ← e, hsys]
  linarith

/-! ### The aligned system fails beyond `log log T + log 2` -/

/-- **The system aligned with a height fails beyond the trivial aperture.** For every `η > 0`,
every `C ≥ 0` and every large `T`: at every aperture `a` with `log log T + log 2 + η ≤ a` and
`e^{a} ≤ T` there is a height `t ∈ [T, 2T]` at which Weil's form of the system aligned with `t`,
on the even polar packet modulated to `t`, is below `−C ∫ f'²`. -/
theorem exists_aligned_height_neg {η : ℝ} (hη : 0 < η) {C : ℝ} (hC : 0 ≤ C) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ a : ℝ, Real.log (Real.log T) + Real.log 2 + η ≤ a →
      Real.exp a ≤ T → ∃ t ∈ Set.Icc T (2 * T),
        (_root_.RHTower.weilFullFunctional (alignedWeight t)
          (EF.weilTest (_root_.RHTower.modulatedTest t (evenPolar a (η / 8)))
            (_root_.RHTower.modulatedTest t (evenPolar a (η / 8))))).re <
          -(C * ∫ u, deriv (evenPolar a (η / 8)) u ^ 2) := by
  obtain ⟨S, -, hS⟩ := exists_abs_deriv_smoothTransition_le
  set δ := η / 8 with hδdef
  have hδ : 0 < δ := by positivity
  set K := (1 / 2 + 2 * S / δ) ^ 2 with hKdef
  have hK : 0 ≤ K := sq_nonneg _
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hK' : 0 ≤ 2 * Real.log 4 + 5 + 2 * (5 + C) * K := by
    have : 0 ≤ (5 + C) * K := mul_nonneg (by linarith) hK
    linarith
  -- the constants of the prime number theorem
  have hη'0 : 0 < 1 - Real.exp (-η / 4) := by
    have : Real.exp (-η / 4) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
    rw [Real.exp_zero] at this
    linarith
  have hη'1 : 1 - Real.exp (-η / 4) ≤ 1 := by linarith [Real.exp_pos (-η / 4)]
  obtain ⟨Y₀, hY₀1, hY₀⟩ := exists_riesz_ge hη'0 hη'1
  have hκ : 0 < (Real.exp (-(3 * η / 4)) - Real.exp (-η)) / 2 := by
    have : Real.exp (-η) < Real.exp (-(3 * η / 4)) := Real.exp_lt_exp.mpr (by linarith)
    linarith
  obtain ⟨a₁, ha₁⟩ := eventually_atTop.mp
    (eventually_cubic_lt_exp (3 / 2 * (5 + (2 * Real.log 4 + 5 + 2 * (5 + C) * K)) + 41) hκ)
  set a₀ := max (max a₁ 1) (Real.log Y₀ / 2 + δ) with ha₀def
  refine ⟨max (Real.exp (Real.exp a₀)) (2 / (1 - Real.exp (-η / 4))),
    fun T hT a haT haexp => ?_⟩
  have hT1 : Real.exp (Real.exp a₀) ≤ T := (le_max_left _ _).trans hT
  have hT2 : 2 / (1 - Real.exp (-η / 4)) ≤ T := (le_max_right _ _).trans hT
  have hT0 : 0 < T := (Real.exp_pos _).trans_le hT1
  have hTge1 : 1 ≤ T := (Real.one_le_exp (Real.exp_pos a₀).le).trans hT1
  set x := Real.log T with hxdef
  have hxge : Real.exp a₀ ≤ x := by
    rw [hxdef, ← Real.log_exp (Real.exp a₀)]
    exact Real.log_le_log (Real.exp_pos _) hT1
  have hx0 : 0 < x := (Real.exp_pos _).trans_le hxge
  have hlogx : a₀ ≤ Real.log x := by
    rw [← Real.log_exp a₀]
    exact Real.log_le_log (Real.exp_pos _) hxge
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have haa₀ : a₀ ≤ a := by linarith
  have ha1 : 1 ≤ a := ((le_max_right a₁ 1).trans (le_max_left _ _)).trans haa₀
  have ha0 : 0 ≤ a := by linarith
  have haY : Real.log Y₀ / 2 + δ ≤ a := (le_max_right _ _).trans haa₀
  set E := Real.exp a with hEdef
  have hE : 0 < E := Real.exp_pos a
  have haE : a ≤ E := by linarith [Real.add_one_le_exp a]
  -- the height is below the aperture: `2 log T ≤ e^{−η} e^{a}`
  have hxE : 2 * x ≤ Real.exp (-η) * E := by
    have h1 : Real.exp (Real.log x + Real.log 2) ≤ Real.exp (a - η) :=
      Real.exp_le_exp.mpr (by linarith)
    rw [Real.exp_add, Real.exp_log hx0, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h1
    have h2 : Real.exp (a - η) = Real.exp (-η) * E := by
      rw [hEdef, ← Real.exp_add]
      congr 1
      ring
    linarith
  -- the mass of the polar packet
  set Mb := a + Real.sinh a with hMb
  have hsinh : Real.sinh a ≤ E / 2 := by
    rw [Real.sinh_eq]
    linarith [Real.exp_pos (-a)]
  have hsinh0 : 0 ≤ Real.sinh a := Real.sinh_nonneg_iff.mpr ha0
  have hMb0 : 0 ≤ Mb := by linarith
  have hMbE : Mb ≤ a + E / 2 := by linarith
  -- the Riesz mean at `Y = e^{2a − 2δ}`
  have hY : Y₀ ≤ Real.exp (2 * a - 2 * δ) := by
    have h1 : Real.log Y₀ ≤ 2 * a - 2 * δ := by linarith
    calc Y₀ = Real.exp (Real.log Y₀) := (Real.exp_log (by linarith)).symm
      _ ≤ Real.exp (2 * a - 2 * δ) := Real.exp_le_exp.mpr h1
  have hκ₁ : (1 - (1 - Real.exp (-η / 4))) * Real.exp (2 * a - 2 * δ) =
      Real.exp (-η / 2) * (Real.exp a * Real.exp a) := by
    rw [hδdef, sub_sub_cancel, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hriesz := hY₀ _ hY
  rw [hκ₁, ← sq] at hriesz
  have hCE := (mul_le_mul_of_nonneg_left hriesz (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans
    (contactForm_evenPolar_ge (a := a) hδ)
  -- a height at which half of the contact form survives
  obtain ⟨t, ht, hmean⟩ := exists_height_contactForm_aligned_ge
    (packetAutocorr_evenPolar_nonneg a δ) ⌊Real.exp (2 * a)⌋₊ hT0
  refine ⟨t, ht, ?_⟩
  have ht0 : 0 < t := hT0.trans_le ht.1
  have htabs : |t| = t := abs_of_pos ht0
  have htE : E ≤ |t| := by
    rw [htabs]
    exact haexp.trans ht.1
  have hE0 : ∀ u, a ≤ |u| → evenPolar a δ u = 0 := fun u hu => evenPolar_eq_zero hδ hu
  have hup := re_weilFullFunctional_modulated_le ha0 (contDiff_evenPolar a δ) hE0
    (alignedWeight t) htE
  have hhalf : Real.exp (-η / 4) / 2 ≤ 1 / 2 - 1 / T := by
    have h2 : 2 ≤ T * (1 - Real.exp (-η / 4)) := (div_le_iff₀ hη'0).mp hT2
    have h1 : 1 / T ≤ (1 - Real.exp (-η / 4)) / 2 := by
      rw [div_le_iff₀ hT0]
      linarith
    linarith
  have hC1 : Real.exp (-(3 * η / 4)) / 4 * E ^ 2 ≤
      contactForm (alignedWeight t) (_root_.RHTower.modulatedTest t (evenPolar a δ))
        ⌊Real.exp (2 * a)⌋₊ := by
    refine le_trans ?_ hmean
    have h := mul_le_mul hhalf hCE (by positivity) (by linarith [Real.exp_pos (-η / 4)])
    have e3 : Real.exp (-(3 * η / 4)) = Real.exp (-η / 4) * Real.exp (-η / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc Real.exp (-(3 * η / 4)) / 4 * E ^ 2
        = Real.exp (-η / 4) / 2 * (1 / 2 * (Real.exp (-η / 2) * E ^ 2)) := by
          rw [e3]
          ring
      _ ≤ _ := h
  -- the height in the archimedean mass
  have hlogt : Real.log (2 + |t|) ≤ x + Real.log 4 := by
    rw [htabs, hxdef, ← Real.log_mul hT0.ne' (by norm_num)]
    exact Real.log_le_log (by linarith) (by linarith [ht.2])
  -- the balance
  have hbal := polar_balance (x := 2 * x) (K := 2 * Real.log 4 + 5 + 2 * (5 + C) * K)
    (κ₁ := Real.exp (-(3 * η / 4))) (κ₂ := Real.exp (-η)) (M := Mb) ha1 hE haE hxE
    (Real.exp_pos _).le (Real.exp_le_one_iff.mpr (by linarith)) hMb0 hMbE hK'
    (by
      have h := ha₁ a (((le_max_left a₁ 1).trans (le_max_left _ _)).trans haa₀)
      rwa [hEdef])
  have hME := integral_evenPolar_sq_le ha0 hδ
  have hDE := integral_deriv_evenPolar_sq_le hS ha0 hδ
  rw [← hMb] at hME hDE
  rw [← hKdef] at hDE
  have hL0 : 0 ≤ Real.log (2 + |t|) + 5 := by
    have := Real.log_nonneg (by linarith [abs_nonneg t] : (1 : ℝ) ≤ 2 + |t|)
    linarith
  have hm1 := mul_le_mul_of_nonneg_left hME hL0
  have hm2 := mul_le_mul_of_nonneg_right
    (by linarith : Real.log (2 + |t|) + 5 ≤ x + Real.log 4 + 5) hMb0
  have hm3 := mul_le_mul_of_nonneg_left hDE (by linarith : (0 : ℝ) ≤ 5 + C)
  have hpos1 : 0 ≤ 4 * a * E * (2 + 2 * a) ^ 2 := by positivity
  have hpos2 : 0 ≤ 4 * (2 + 2 * a) ^ 2 * Mb := by positivity
  linarith

/-- **In the aspect of the height the sizes pay nothing beyond `log log t + log 2`.** For every
`η > 0` and every large `T` there are a height `t ∈ [T, 2T]`, a dominated system and a `C³` packet
vanishing off `(−a, a)`, `a = log log t + log 2 + η`, such that Weil's form of the system, with
pole plane, is negative on the packet modulated to the height `t`. -/
theorem exists_dominated_height_neg {η : ℝ} (hη : 0 < η) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∃ t ∈ Set.Icc T (2 * T), ∃ w : ℕ → ℝ, Dominated w ∧
      ∃ f : ℝ → ℝ, ContDiff ℝ 3 f ∧
        (∀ u, Real.log (Real.log t) + Real.log 2 + η ≤ |u| → f u = 0) ∧
        (_root_.RHTower.weilFullFunctional w
          (EF.weilTest (_root_.RHTower.modulatedTest t f)
            (_root_.RHTower.modulatedTest t f))).re < 0 := by
  obtain ⟨T₁, hT₁⟩ := exists_aligned_height_neg hη (le_refl (0 : ℝ))
  have hc : 0 < 1 / (2 * Real.exp η) := by positivity
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp (Real.isLittleO_log_id_atTop.def hc)
  refine ⟨max (max T₁ T₂) (Real.exp 1), fun T hT => ?_⟩
  have hTe : Real.exp 1 ≤ T := (le_max_right _ _).trans hT
  have hT0 : 0 < T := (Real.exp_pos 1).trans_le hTe
  have hx1 : 1 ≤ Real.log T := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hTe
  have hx0 : 0 < Real.log T := by linarith
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = Real.log (Real.log T) + Real.log 2 + η := ⟨_, rfl⟩
  have hexpa : Real.exp a = 2 * Real.exp η * Real.log T := by
    rw [hadef, Real.exp_add, Real.exp_add, Real.exp_log hx0,
      Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    ring
  -- `e^{a} = 2 e^{η} log T ≤ T`
  have hlogle : Real.log T ≤ 1 / (2 * Real.exp η) * T := by
    have h := hT₂ T (((le_max_right _ _).trans (le_max_left _ _)).trans hT)
    simp only [id_eq, Real.norm_eq_abs] at h
    rwa [abs_of_pos hx0, abs_of_pos hT0] at h
  have haT : Real.exp a ≤ T := by
    rw [hexpa]
    have h := mul_le_mul_of_nonneg_left hlogle (by positivity : (0 : ℝ) ≤ 2 * Real.exp η)
    have h1 : 2 * Real.exp η * (1 / (2 * Real.exp η)) = 1 :=
      mul_one_div_cancel (by positivity)
    have e : 2 * Real.exp η * (1 / (2 * Real.exp η) * T) = T := by
      linear_combination T * h1
    linarith
  obtain ⟨t, ht, hneg⟩ :=
    hT₁ T (((le_max_left _ _).trans (le_max_left _ _)).trans hT) a hadef.ge haT
  rw [zero_mul, neg_zero] at hneg
  have hlt : Real.log (Real.log T) ≤ Real.log (Real.log t) :=
    Real.log_le_log hx0 (Real.log_le_log hT0 ht.1)
  exact ⟨t, ht, alignedWeight t, dominated_alignedWeight t, evenPolar a (η / 8),
    contDiff_evenPolar a (η / 8),
    fun u hu => evenPolar_eq_zero (by positivity) (by linarith), hneg⟩

end GaloisForLFunctions.SelectiveArithmetic
