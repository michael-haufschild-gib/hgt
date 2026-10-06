import GaloisForLFunctions.RHTower.KuznetsovSameSignSpecWeightBounds
import GaloisForLFunctions.RHTower.PoissonArithmeticProgressionBound

/-!
# Same-sign weights from odd profiles

Let `G` be smooth and odd with `|G^{(n)}(w)| ≤ C_n e^{-2|w|}` for every `n` (an
`OddDecayProfile`).  Put

`h(t) = π⁻¹ ∫ G'(w) e^{-2itw} dw = π⁻¹ 𝓕(G')(t/π)`.

Then `(h, G, G')` is a same-sign weight (`OddDecayProfile.toWeight`): Fourier inversion gives
`∫ h(t) e^{2itw} dt = G'(w)`, and `k`-fold integration by parts gives `|h(t)| ≤ C_k |t|^{-k}`.
The weight is rapid (`OddDecayProfile.isRapid`): since `G → 0` at `±∞` and `G'` is even,
`∫ G' = ∫ w G'(w) dw = 0`, so `𝓕(G')(ξ) = ∫ (e^{-2πiξw} - 1 + 2πiξw) G'(w) dw = O(ξ²)`.
-/

open MeasureTheory Set Filter Topology Complex
open scoped FourierTransform

namespace GaloisForLFunctions.RHTower.DeckPointPair

noncomputable section

/-- A smooth odd profile all of whose derivatives decay like `e^{-2w}` on `w ≥ 0`. -/
structure OddDecayProfile where
  /-- The profile. -/
  G : ℝ → ℂ
  contDiff : ∀ n : ℕ, ContDiff ℝ n G
  odd : ∀ w, G (-w) = -G w
  decay : ∀ n : ℕ, ∃ C : ℝ, ∀ w, 0 ≤ w → ‖iteratedDeriv n G w‖ ≤ C * Real.exp (-(2 * w))

theorem integrable_exp_neg_abs' : Integrable fun x : ℝ => Real.exp (-|x|) := by
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul 2)
    (Continuous.aestronglyMeasurable (by fun_prop)) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
  have hq := Real.quadratic_le_exp_of_nonneg (abs_nonneg x)
  have hx2 : |x| ^ 2 = x ^ 2 := sq_abs x
  have hpos : 0 < 1 + x ^ 2 := by positivity
  rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
  rw [show 2 * (1 + x ^ 2)⁻¹ * Real.exp |x| = 2 * Real.exp |x| / (1 + x ^ 2) by field_simp]
  rw [le_div_iff₀ hpos]
  nlinarith [abs_nonneg x]

theorem pow_abs_mul_exp_neg_two_le (j : ℕ) (w : ℝ) :
    |w| ^ j * Real.exp (-(2 * |w|)) ≤ j.factorial * Real.exp (-|w|) := by
  have h := Real.pow_div_factorial_le_exp |w| (abs_nonneg w) j
  rw [div_le_iff₀ (by positivity)] at h
  calc |w| ^ j * Real.exp (-(2 * |w|)) ≤ Real.exp |w| * j.factorial * Real.exp (-(2 * |w|)) := by
        gcongr
    _ = j.factorial * (Real.exp |w| * Real.exp (-(2 * |w|))) := by ring
    _ = j.factorial * Real.exp (-|w|) := by rw [← Real.exp_add]; congr 2; ring

theorem norm_cexp_mul_I_sub_one_sub_le (y : ℝ) :
    ‖cexp (y * Complex.I) - 1 - y * Complex.I‖ ≤ 3 * y ^ 2 := by
  have hn : ‖(y : ℂ) * Complex.I‖ = |y| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rcases le_or_gt |y| 1 with h | h
  · have := Complex.norm_exp_sub_one_sub_id_le (x := (y : ℂ) * Complex.I) (by rw [hn]; exact h)
    rw [hn, sq_abs] at this
    nlinarith [sq_nonneg y]
  · have h1 : ‖cexp (y * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I y
    calc ‖cexp (y * Complex.I) - 1 - y * Complex.I‖
        ≤ ‖cexp (y * Complex.I)‖ + ‖(1 : ℂ)‖ + ‖(y : ℂ) * Complex.I‖ := by
          refine (norm_sub_le _ _).trans ?_
          gcongr
          exact norm_sub_le _ _
      _ = 2 + |y| := by rw [h1, hn, norm_one]; ring
      _ ≤ 3 * y ^ 2 := by nlinarith [sq_abs y, abs_nonneg y]

namespace OddDecayProfile

variable (P : OddDecayProfile)

theorem G_eq_neg_comp_neg : P.G = fun x => -P.G (-x) := funext fun x => by rw [P.odd, neg_neg]

/-- `G^{(n)}(-w) = (-1)^{n+1} G^{(n)}(w)`. -/
theorem iteratedDeriv_neg_eq (n : ℕ) (w : ℝ) :
    iteratedDeriv n P.G (-w) = -((-1 : ℝ) ^ n • iteratedDeriv n P.G w) := by
  conv_lhs => rw [P.G_eq_neg_comp_neg]
  rw [iteratedDeriv_fun_neg, iteratedDeriv_comp_neg, neg_neg]

theorem norm_iteratedDeriv_neg (n : ℕ) (w : ℝ) :
    ‖iteratedDeriv n P.G (-w)‖ = ‖iteratedDeriv n P.G w‖ := by
  rw [iteratedDeriv_neg_eq, norm_neg, norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]

theorem exists_bound (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w, ‖iteratedDeriv n P.G w‖ ≤ C * Real.exp (-(2 * |w|)) := by
  obtain ⟨C, hC⟩ := P.decay n
  refine ⟨max C 0, le_max_right _ _, fun w => ?_⟩
  have key : ∀ v, 0 ≤ v → ‖iteratedDeriv n P.G v‖ ≤ max C 0 * Real.exp (-(2 * v)) := fun v hv =>
    (hC v hv).trans (by gcongr; exact le_max_left _ _)
  rcases le_total 0 w with hw | hw
  · rw [abs_of_nonneg hw]; exact key w hw
  · rw [abs_of_nonpos hw, ← P.norm_iteratedDeriv_neg n w]; exact key (-w) (by linarith)

theorem hasDerivAt_iteratedDeriv (n : ℕ) (w : ℝ) :
    HasDerivAt (iteratedDeriv n P.G) (iteratedDeriv (n + 1) P.G w) w := by
  rw [iteratedDeriv_succ]
  exact ((P.contDiff (n + 1)).differentiable_iteratedDeriv n (by exact_mod_cast Nat.lt_succ_self n)
    w).hasDerivAt

theorem continuous_iteratedDeriv (n : ℕ) : Continuous (iteratedDeriv n P.G) :=
  (P.contDiff n).continuous_iteratedDeriv' n

theorem integrable_pow_abs_mul_iteratedDeriv (n j : ℕ) :
    Integrable fun w => |w| ^ j * ‖iteratedDeriv n P.G w‖ := by
  obtain ⟨C, hC, hb⟩ := P.exists_bound n
  refine (integrable_exp_neg_abs'.const_mul (C * j.factorial)).mono'
    (((continuous_abs.pow j).mul (P.continuous_iteratedDeriv n).norm).aestronglyMeasurable)
    (Eventually.of_forall fun w => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  calc |w| ^ j * ‖iteratedDeriv n P.G w‖ ≤ |w| ^ j * (C * Real.exp (-(2 * |w|))) := by
        gcongr; exact hb w
    _ = C * (|w| ^ j * Real.exp (-(2 * |w|))) := by ring
    _ ≤ C * (j.factorial * Real.exp (-|w|)) :=
        mul_le_mul_of_nonneg_left (pow_abs_mul_exp_neg_two_le j w) hC
    _ = _ := by ring

theorem integrable_iteratedDeriv (n : ℕ) : Integrable (iteratedDeriv n P.G) := by
  refine ((P.integrable_pow_abs_mul_iteratedDeriv n 0)).mono'
    (P.continuous_iteratedDeriv n).aestronglyMeasurable (Eventually.of_forall fun w => ?_)
  simp

theorem integrable_G_exp : Integrable fun w => ‖P.G w‖ * Real.exp |w| := by
  obtain ⟨C, hC, hb⟩ := P.exists_bound 0
  refine (integrable_exp_neg_abs'.const_mul C).mono'
    (Continuous.aestronglyMeasurable (by
      have := P.continuous_iteratedDeriv 0
      rw [iteratedDeriv_zero] at this
      fun_prop)) (Eventually.of_forall fun w => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  have := hb w
  rw [iteratedDeriv_zero] at this
  calc ‖P.G w‖ * Real.exp |w| ≤ C * Real.exp (-(2 * |w|)) * Real.exp |w| := by gcongr
    _ = C * Real.exp (-|w|) := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

theorem tendsto_G_atTop : Tendsto P.G atTop (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := P.exists_bound 0
  refine squeeze_zero_norm (a := fun w => C * Real.exp (-(2 * |w|))) (fun w => by
    simpa using hb w) ?_
  have : Tendsto (fun w : ℝ => -(2 * |w|)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp ((tendsto_abs_atTop_atTop).const_mul_atTop two_pos)
  simpa using (Real.tendsto_exp_atBot.comp this).const_mul C

theorem tendsto_G_atBot : Tendsto P.G atBot (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := P.exists_bound 0
  refine squeeze_zero_norm (a := fun w => C * Real.exp (-(2 * |w|))) (fun w => by
    simpa using hb w) ?_
  have : Tendsto (fun w : ℝ => -(2 * |w|)) atBot atBot :=
    tendsto_neg_atTop_atBot.comp ((tendsto_abs_atBot_atTop).const_mul_atTop two_pos)
  simpa using (Real.tendsto_exp_atBot.comp this).const_mul C

theorem hasDerivAt_G (w : ℝ) : HasDerivAt P.G (deriv P.G w) w := by
  have := P.hasDerivAt_iteratedDeriv 0 w
  simpa [iteratedDeriv_zero, iteratedDeriv_one] using this

theorem integrable_deriv : Integrable (deriv P.G) := by
  simpa [iteratedDeriv_one] using P.integrable_iteratedDeriv 1

theorem continuous_deriv : Continuous (deriv P.G) := by
  simpa [iteratedDeriv_one] using P.continuous_iteratedDeriv 1

/-- `∫ G' = 0`. -/
theorem integral_deriv_eq_zero : ∫ w, deriv P.G w = 0 := by
  rw [integral_of_hasDerivAt_of_tendsto P.hasDerivAt_G P.integrable_deriv P.tendsto_G_atBot
    P.tendsto_G_atTop, sub_zero]

theorem deriv_neg (w : ℝ) : deriv P.G (-w) = deriv P.G w := by
  have := P.iteratedDeriv_neg_eq 1 w
  simpa [iteratedDeriv_one] using this

theorem integrable_mul_deriv : Integrable fun w : ℝ => (w : ℂ) * deriv P.G w := by
  refine (P.integrable_pow_abs_mul_iteratedDeriv 1 1).mono'
    ((continuous_ofReal.mul P.continuous_deriv).aestronglyMeasurable)
    (Eventually.of_forall fun w => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, pow_one, iteratedDeriv_one]

/-- `∫ w G'(w) dw = 0`: the integrand is odd. -/
theorem integral_mul_deriv_eq_zero : ∫ w : ℝ, (w : ℂ) * deriv P.G w = 0 := by
  have h := integral_neg_eq_self (fun w : ℝ => (w : ℂ) * deriv P.G w) volume
  simp only [P.deriv_neg, ofReal_neg, neg_mul, integral_neg] at h
  have : (2 : ℂ) * ∫ w : ℝ, (w : ℂ) * deriv P.G w = 0 := by
    linear_combination -h
  simpa using this

/-! ## The spectral weight -/

/-- `h(t) = π⁻¹ 𝓕(G')(t/π) = π⁻¹ ∫ G'(w) e^{-2itw} dw`. -/
def h (t : ℝ) : ℂ := (Real.pi : ℂ)⁻¹ * 𝓕 (deriv P.G) (t / Real.pi)

theorem contDiff_deriv (k : ℕ) : ContDiff ℝ k (deriv P.G) := (P.contDiff (k + 1)).deriv'

theorem integrable_iteratedDeriv_deriv (j : ℕ) : Integrable (iteratedDeriv j (deriv P.G)) := by
  rw [← iteratedDeriv_succ']; exact P.integrable_iteratedDeriv (j + 1)

/-- `(2π|ξ|)^k |𝓕(G')(ξ)| ≤ ∫ |G^{(k+1)}|`. -/
theorem pow_mul_norm_fourier_deriv_le (k : ℕ) (ξ : ℝ) :
    (2 * Real.pi * |ξ|) ^ k * ‖𝓕 (deriv P.G) ξ‖ ≤ ∫ x, ‖iteratedDeriv (k + 1) P.G x‖ := by
  have := _root_.RHTower.pow_mul_norm_fourier_le_of_iteratedDeriv (P.contDiff_deriv k)
    (fun j _ => P.integrable_iteratedDeriv_deriv j) ξ
  rwa [← iteratedDeriv_succ'] at this

theorem integrable_fourier_deriv : Integrable (𝓕 (deriv P.G)) := by
  set M₁ := ∫ x, ‖iteratedDeriv (0 + 1) P.G x‖
  set M₃ := ∫ x, ‖iteratedDeriv (2 + 1) P.G x‖
  refine (integrable_inv_one_add_sq.const_mul (M₁ + M₃ / (2 * Real.pi) ^ 2)).mono'
    (continuous_fourier_of_integrable' P.integrable_deriv).aestronglyMeasurable
    (Eventually.of_forall fun ξ => ?_)
  have h0 := P.pow_mul_norm_fourier_deriv_le 0 ξ
  have h2 := P.pow_mul_norm_fourier_deriv_le 2 ξ
  rw [pow_zero, one_mul] at h0
  have hπ : 0 < (2 * Real.pi) ^ 2 := by positivity
  have hq : 0 < 1 + ξ ^ 2 := by positivity
  rw [le_mul_inv_iff₀ hq]
  rw [mul_pow, sq_abs] at h2
  rw [show (M₁ + M₃ / (2 * Real.pi) ^ 2) = (M₁ * (2 * Real.pi) ^ 2 + M₃) / (2 * Real.pi) ^ 2 by
    field_simp, le_div_iff₀ hπ]
  nlinarith [norm_nonneg (𝓕 (deriv P.G) ξ)]
where
  continuous_fourier_of_integrable' {f : ℝ → ℂ} (hf : Integrable f) : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hf

theorem continuous_h : Continuous P.h :=
  continuous_const.mul ((integrable_fourier_deriv.continuous_fourier_of_integrable'
    P.integrable_deriv).comp (by fun_prop))

theorem integrable_h : Integrable P.h := by
  have := (P.integrable_fourier_deriv.comp_div (by positivity : Real.pi ≠ 0)).const_mul
    (Real.pi : ℂ)⁻¹
  exact this

/-- **Fourier inversion**: `∫ h(t) e^{2itw} dt = G'(w)`. -/
theorem fourier_h (w : ℝ) : ∫ t : ℝ, P.h t * cexp (2 * t * w * Complex.I) = deriv P.G w := by
  have hinv := congrFun (P.continuous_deriv.fourierInv_fourier_eq P.integrable_deriv
    P.integrable_fourier_deriv) w
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul] at hinv
  have hsub := MeasureTheory.Measure.integral_comp_mul_left
    (fun t : ℝ => P.h t * cexp (2 * t * w * Complex.I)) Real.pi
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hpt : (fun ξ : ℝ => P.h (Real.pi * ξ) * cexp (2 * (Real.pi * ξ : ℝ) * w * Complex.I)) =
      fun ξ => (Real.pi : ℂ)⁻¹ *
        (cexp (((-2 * Real.pi * ξ * -w : ℝ) : ℂ) * Complex.I) • 𝓕 (deriv P.G) ξ) := by
    funext ξ
    simp only [h, smul_eq_mul]
    rw [mul_div_cancel_left₀ _ Real.pi_ne_zero]
    push_cast; ring_nf
  rw [hpt, integral_const_mul, hinv, abs_inv, abs_of_pos Real.pi_pos, Complex.real_smul] at hsub
  push_cast at hsub
  field_simp at hsub
  linear_combination -hsub

/-- **Rapid decay**: `|h(t)| (1+|t|)^A ≤ C_A t²`. -/
theorem isRapid_bound (A : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖P.h t‖ * (1 + |t|) ^ A ≤ C * t ^ 2 := by
  set Q := ∫ x : ℝ, |x| ^ 2 * ‖iteratedDeriv 1 P.G x‖
  set M := ∫ x, ‖iteratedDeriv (A + 2 + 1) P.G x‖
  have hQ : 0 ≤ Q := integral_nonneg fun _ => by positivity
  have hM : 0 ≤ M := integral_nonneg fun _ => norm_nonneg _
  refine ⟨12 * Q / Real.pi * 2 ^ A + M / Real.pi, by positivity, fun t => ?_⟩
  have hπ := Real.pi_pos
  have hht : ‖P.h t‖ = Real.pi⁻¹ * ‖𝓕 (deriv P.G) (t / Real.pi)‖ := by
    rw [h, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hπ.le]
  rcases le_or_gt |t| 1 with ht | ht
  · -- small `t`: second-order vanishing
    set ξ := t / Real.pi
    have hF : 𝓕 (deriv P.G) ξ = ∫ x : ℝ, (cexp (((-2 * Real.pi * x * ξ : ℝ) : ℂ) * Complex.I) - 1 -
        ((-2 * Real.pi * x * ξ : ℝ) : ℂ) * Complex.I) * deriv P.G x := by
      rw [Real.fourier_real_eq_integral_exp_smul]
      have hi1 : Integrable fun x : ℝ => cexp (((-2 * Real.pi * x * ξ : ℝ) : ℂ) * Complex.I) * deriv P.G x :=
        (P.integrable_deriv.bdd_mul (c := 1)
          (Continuous.aestronglyMeasurable (by fun_prop :
            Continuous fun x : ℝ => cexp (((-2 * Real.pi * x * ξ : ℝ) : ℂ) * Complex.I)))
          (Eventually.of_forall fun x => (Complex.norm_exp_ofReal_mul_I _).le))
      have hi3 : Integrable fun x : ℝ => ((-2 * Real.pi * x * ξ : ℝ) : ℂ) * Complex.I * deriv P.G x := by
        have := P.integrable_mul_deriv.const_mul (-2 * Real.pi * ξ * Complex.I)
        refine this.congr (Eventually.of_forall fun x => ?_)
        push_cast; ring
      have e : (fun x : ℝ => (cexp (((-2 * Real.pi * x * ξ : ℝ) : ℂ) * Complex.I) - 1 -
          ((-2 * Real.pi * x * ξ : ℝ) : ℂ) * Complex.I) * deriv P.G x) =
          fun x => cexp (((-2 * Real.pi * x * ξ : ℝ) : ℂ) * Complex.I) * deriv P.G x - deriv P.G x -
            ((-2 * Real.pi * x * ξ : ℝ) : ℂ) * Complex.I * deriv P.G x := by
        funext x; ring
      have hi12 : Integrable fun x : ℝ =>
          cexp (((-2 * Real.pi * x * ξ : ℝ) : ℂ) * Complex.I) * deriv P.G x - deriv P.G x :=
        hi1.sub P.integrable_deriv
      simp only [smul_eq_mul]
      rw [e, integral_sub hi12 hi3, integral_sub hi1 P.integrable_deriv, P.integral_deriv_eq_zero]
      have h3 : ∫ x : ℝ, ((-2 * Real.pi * x * ξ : ℝ) : ℂ) * Complex.I * deriv P.G x = 0 := by
        have : (fun x : ℝ => ((-2 * Real.pi * x * ξ : ℝ) : ℂ) * Complex.I * deriv P.G x) =
            fun x : ℝ => (-2 * Real.pi * ξ * Complex.I) * ((x : ℂ) * deriv P.G x) := by
          funext x; push_cast; ring
        rw [this, integral_const_mul, P.integral_mul_deriv_eq_zero, mul_zero]
      rw [h3, sub_zero, sub_zero]
    have hbound : ‖𝓕 (deriv P.G) ξ‖ ≤ 12 * Real.pi ^ 2 * ξ ^ 2 * Q := by
      rw [hF]
      refine (norm_integral_le_integral_norm _).trans ?_
      have hint : Integrable fun x : ℝ => 12 * Real.pi ^ 2 * ξ ^ 2 * (|x| ^ 2 * ‖iteratedDeriv 1 P.G x‖) :=
        (P.integrable_pow_abs_mul_iteratedDeriv 1 2).const_mul _
      calc ∫ x, ‖(cexp (((-2 * Real.pi * x * ξ : ℝ) : ℂ) * Complex.I) - 1 -
            ((-2 * Real.pi * x * ξ : ℝ) : ℂ) * Complex.I) * deriv P.G x‖
          ≤ ∫ x, 12 * Real.pi ^ 2 * ξ ^ 2 * (|x| ^ 2 * ‖iteratedDeriv 1 P.G x‖) := by
            refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hint
              (Eventually.of_forall fun x => ?_)
            dsimp only
            rw [norm_mul, iteratedDeriv_one]
            have := norm_cexp_mul_I_sub_one_sub_le (-2 * Real.pi * x * ξ)
            calc _ ≤ 3 * (-2 * Real.pi * x * ξ) ^ 2 * ‖deriv P.G x‖ := by gcongr
              _ = _ := by rw [sq_abs]; ring
        _ = 12 * Real.pi ^ 2 * ξ ^ 2 * Q := integral_const_mul _ _
    have hξ : Real.pi ^ 2 * ξ ^ 2 = t ^ 2 := by simp only [ξ]; field_simp
    have h1 : (1 + |t|) ^ A ≤ 2 ^ A := pow_le_pow_left₀ (by positivity) (by linarith) A
    calc ‖P.h t‖ * (1 + |t|) ^ A ≤ (Real.pi⁻¹ * (12 * Real.pi ^ 2 * ξ ^ 2 * Q)) * 2 ^ A := by
          rw [hht]; gcongr
      _ = 12 * Q / Real.pi * 2 ^ A * t ^ 2 := by
          rw [← hξ]; field_simp
      _ ≤ _ := by
          have : 0 ≤ M / Real.pi * t ^ 2 := by positivity
          nlinarith
  · -- large `t`: integration by parts
    set ξ := t / Real.pi
    have hb := P.pow_mul_norm_fourier_deriv_le (A + 2) ξ
    have hξ : 2 * Real.pi * |ξ| = 2 * |t| := by
      simp only [ξ, abs_div, abs_of_pos hπ]; field_simp
    rw [hξ] at hb
    have ht0 : 0 < |t| := by linarith
    have h1 : (1 + |t|) ^ A ≤ (2 * |t|) ^ A := pow_le_pow_left₀ (by positivity) (by linarith) A
    have ht2 : 1 ≤ t ^ 2 := by nlinarith [sq_abs t]
    have hF : ‖𝓕 (deriv P.G) ξ‖ * (2 * |t|) ^ A * (2 * |t|) ^ 2 ≤ M := by
      calc _ = (2 * |t|) ^ (A + 2) * ‖𝓕 (deriv P.G) ξ‖ := by rw [pow_add]; ring
        _ ≤ M := hb
    have h4 : 1 ≤ (2 * |t|) ^ 2 := by nlinarith
    calc ‖P.h t‖ * (1 + |t|) ^ A ≤ Real.pi⁻¹ * ‖𝓕 (deriv P.G) ξ‖ * (2 * |t|) ^ A := by
          rw [hht]; gcongr
      _ ≤ Real.pi⁻¹ * M := by
          rw [mul_assoc]
          gcongr
          nlinarith [norm_nonneg (𝓕 (deriv P.G) ξ), pow_nonneg (by positivity : (0 : ℝ) ≤ 2 * |t|) A]
      _ ≤ M / Real.pi * t ^ 2 := by
          rw [inv_mul_eq_div]
          nlinarith [div_nonneg hM hπ.le]
      _ ≤ _ := by
          have : 0 ≤ 12 * Q / Real.pi * 2 ^ A * t ^ 2 := by positivity
          nlinarith

/-- The same-sign weight `(h, G, G')`. -/
def toWeight : SameSignWeight where
  h := P.h
  G := P.G
  dG := deriv P.G
  continuous_h := P.continuous_h
  integrable_h := P.integrable_h
  hasDerivAt_G := P.hasDerivAt_G
  continuous_dG := P.continuous_deriv
  integrable_dG := P.integrable_deriv
  integrable_G_exp := P.integrable_G_exp
  fourier_h := P.fourier_h

theorem isRapid : P.toWeight.IsRapid := P.isRapid_bound

end OddDecayProfile

end

end GaloisForLFunctions.RHTower.DeckPointPair
