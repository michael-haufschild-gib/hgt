import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# Window means of finite trigonometric sums

For a finite sum `S(x) = Σ_q w_q e^{iγ_q x}` with complex coefficients and nonzero real frequencies,
the mean of `S` over a window of length `ℓ` is `O(1/ℓ)`, while the mean of `(Re S)²` is bounded
below by half the sum of the squared moduli of the coefficients, up to `O(1/ℓ)`, whenever equal
frequencies carry equal coefficients and opposite frequencies carry conjugate coefficients.  From a
small mean and a large mean square one extracts a point of the window where `Re S` is large: the
positivity extraction lemma.  These are the elementary ingredients of Bohr's relative density of the
positivity set of a real trigonometric polynomial with positive-real-part coefficients.
-/

open Complex Set

noncomputable section

namespace TrigSum

/-! ## Window integrals of exponentials -/

/-- `∫_A^{A+ℓ} e^{iγx} dx = (e^{iγ(A+ℓ)} − e^{iγA})/(iγ)` for `γ ≠ 0`. -/
theorem integral_exp_I_mul (γ : ℝ) (hγ : γ ≠ 0) (A ℓ : ℝ) :
    ∫ x in A..A + ℓ, cexp (I * (γ * x)) = (cexp (I * (γ * (A + ℓ))) - cexp (I * (γ * A))) / (I * γ) := by
  have hc : (I * (γ : ℂ)) ≠ 0 := mul_ne_zero I_ne_zero (by exact_mod_cast hγ)
  have := integral_exp_mul_complex (a := A) (b := A + ℓ) hc
  simp only [mul_assoc] at this ⊢
  push_cast at this ⊢
  convert this using 3

theorem norm_integral_exp_I_mul_le (γ : ℝ) (hγ : γ ≠ 0) (A ℓ : ℝ) :
    ‖∫ x in A..A + ℓ, cexp (I * (γ * x))‖ ≤ 2 / |γ| := by
  rw [integral_exp_I_mul γ hγ, norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs]
  have h1 : ‖cexp (I * (γ * (A + ℓ)))‖ = 1 := by
    rw [show I * (γ * ((A : ℂ) + ℓ)) = ((γ * (A + ℓ) : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have h2 : ‖cexp (I * (γ * A))‖ = 1 := by
    rw [show I * ((γ : ℂ) * A) = ((γ * A : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hγ0 : 0 < |γ| := abs_pos.mpr hγ
  rw [div_le_div_iff_of_pos_right hγ0]
  calc ‖cexp (I * (γ * (A + ℓ))) - cexp (I * (γ * A))‖
      ≤ ‖cexp (I * (γ * (A + ℓ)))‖ + ‖cexp (I * (γ * A))‖ := norm_sub_le _ _
    _ = 2 := by rw [h1, h2]; norm_num

theorem integral_exp_I_mul_zero (A ℓ : ℝ) :
    ∫ x in A..A + ℓ, cexp (I * ((0 : ℝ) * x)) = ℓ := by
  simp

/-- The window integral of `e^{iγx}` is `ℓ` if `γ = 0` and has norm `≤ 2/|γ|` otherwise. -/
theorem integral_exp_I_mul_cases (γ : ℝ) (A ℓ : ℝ) :
    (γ = 0 ∧ ∫ x in A..A + ℓ, cexp (I * (γ * x)) = ℓ) ∨
      (γ ≠ 0 ∧ ‖∫ x in A..A + ℓ, cexp (I * (γ * x))‖ ≤ 2 / |γ|) := by
  by_cases h : γ = 0
  · left; subst h; exact ⟨rfl, integral_exp_I_mul_zero A ℓ⟩
  · right; exact ⟨h, norm_integral_exp_I_mul_le γ h A ℓ⟩

/-! ## Finite trigonometric sums -/

variable {ι : Type*}

/-- `S(x) = Σ_{q ∈ F} w_q e^{iγ_q x}`. -/
def trigSum (F : Finset ι) (w : ι → ℂ) (γ : ι → ℝ) (x : ℝ) : ℂ :=
  ∑ q ∈ F, w q * cexp (I * (γ q * x))

theorem continuous_term (w : ℂ) (γ : ℝ) : Continuous fun x : ℝ => w * cexp (I * (γ * x)) := by
  fun_prop

theorem continuous_trigSum (F : Finset ι) (w : ι → ℂ) (γ : ι → ℝ) :
    Continuous (trigSum F w γ) := by
  unfold trigSum
  exact continuous_finsetSum _ fun q _ => continuous_term (w q) (γ q)

theorem norm_trigSum_le (F : Finset ι) (w : ι → ℂ) (γ : ι → ℝ) (x : ℝ) :
    ‖trigSum F w γ x‖ ≤ ∑ q ∈ F, ‖w q‖ := by
  unfold trigSum
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => le_of_eq ?_)
  rw [norm_mul, show I * ((γ q : ℂ) * x) = ((γ q * x : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, mul_one]

/-- `‖e^{iθ} − 1‖ ≤ |θ|`. -/
theorem norm_exp_I_mul_sub_one_le (θ : ℝ) : ‖cexp (I * θ) - 1‖ ≤ |θ| := by
  have := @Real.norm_exp_I_mul_ofReal_sub_one_le θ
  rwa [Real.norm_eq_abs] at this

/-- The trigonometric sum is Lipschitz with constant `Σ ‖w_q‖ |γ_q|`. -/
theorem norm_trigSum_sub_le (F : Finset ι) (w : ι → ℂ) (γ : ι → ℝ) (x y : ℝ) :
    ‖trigSum F w γ x - trigSum F w γ y‖ ≤ (∑ q ∈ F, ‖w q‖ * |γ q|) * |x - y| := by
  unfold trigSum
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
  have e : w q * cexp (I * (γ q * x)) - w q * cexp (I * (γ q * y))
      = w q * cexp (I * (γ q * y)) * (cexp (I * (γ q * (x - y) : ℝ)) - 1) := by
    rw [mul_sub, mul_one, mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast; ring
  rw [e, norm_mul, norm_mul, show I * ((γ q : ℂ) * y) = ((γ q * y : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, mul_one]
  have := norm_exp_I_mul_sub_one_le (γ q * (x - y))
  rw [abs_mul] at this
  calc ‖w q‖ * ‖cexp (I * ↑(γ q * (x - y))) - 1‖ ≤ ‖w q‖ * (|γ q| * |x - y|) := by gcongr
    _ = ‖w q‖ * |γ q| * |x - y| := by ring

/-- The window integral of the sum is small when all frequencies are nonzero. -/
theorem norm_integral_trigSum_le (F : Finset ι) (w : ι → ℂ) (γ : ι → ℝ)
    (hγ : ∀ q ∈ F, γ q ≠ 0) (A ℓ : ℝ) :
    ‖∫ x in A..A + ℓ, trigSum F w γ x‖ ≤ ∑ q ∈ F, ‖w q‖ * (2 / |γ q|) := by
  unfold trigSum
  rw [intervalIntegral.integral_finsetSum fun q _ => (continuous_term (w q) (γ q)).intervalIntegrable _ _]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q hq => ?_)
  rw [intervalIntegral.integral_const_mul, norm_mul]
  gcongr
  exact norm_integral_exp_I_mul_le (γ q) (hγ q hq) A ℓ

/-! ## The mean square of the real part -/

/-- `Re z · Re z' = (Re(z z') + Re(z z̄'))/2`. -/
theorem re_mul_re (z z' : ℂ) :
    z.re * z'.re = ((z * z').re + (z * starRingEnd ℂ z').re) / 2 := by
  simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]

/-- The pair term of `(Re S)²`. -/
def pairTerm (w : ι → ℂ) (γ : ι → ℝ) (q q' : ι) (x : ℝ) : ℝ :=
  ((w q * w q' * cexp (I * (((γ q : ℂ) + γ q') * x))).re
    + (w q * starRingEnd ℂ (w q') * cexp (I * (((γ q : ℂ) - γ q') * x))).re) / 2

theorem re_trigSum_sq (F : Finset ι) (w : ι → ℂ) (γ : ι → ℝ) (x : ℝ) :
    (trigSum F w γ x).re ^ 2 = ∑ q ∈ F, ∑ q' ∈ F, pairTerm w γ q q' x := by
  unfold trigSum
  rw [sq, Complex.re_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun q' _ => ?_
  rw [re_mul_re]
  unfold pairTerm
  congr 2
  · congr 1
    rw [show I * (((γ q : ℂ) + γ q') * x) = I * (γ q * x) + I * (γ q' * x) by ring,
      Complex.exp_add]
    ring
  · congr 1
    have hconj : starRingEnd ℂ (w q' * cexp (I * (γ q' * x)))
        = starRingEnd ℂ (w q') * cexp (-(I * (γ q' * x))) := by
      rw [map_mul, ← Complex.exp_conj]
      congr 2
      simp [Complex.conj_ofReal]
    rw [hconj, show I * (((γ q : ℂ) - γ q') * x) = I * (γ q * x) + -(I * (γ q' * x)) by ring,
      Complex.exp_add]
    ring

theorem continuous_pairTerm (w : ι → ℂ) (γ : ι → ℝ) (q q' : ι) :
    Continuous (pairTerm w γ q q') := by
  unfold pairTerm
  fun_prop

/-- The window integral of a pair term: the constant part when the frequency vanishes, and an
`O(1/ℓ)` bound otherwise. -/
theorem integral_re_mul_exp (c : ℂ) (γ : ℝ) (A ℓ : ℝ) :
    ∫ x in A..A + ℓ, (c * cexp (I * (γ * x))).re
      = (c * ∫ x in A..A + ℓ, cexp (I * (γ * x))).re := by
  have hint : IntervalIntegrable (fun x : ℝ => c * cexp (I * (γ * x))) MeasureTheory.volume A (A + ℓ) :=
    (continuous_term c γ).intervalIntegrable _ _
  rw [← intervalIntegral.integral_const_mul]
  have := Complex.reCLM.intervalIntegral_comp_comm hint
  simpa only [Complex.reCLM_apply] using this

theorem integral_re_mul_exp_ge (c : ℂ) (γ : ℝ) (A ℓ : ℝ) :
    ∫ x in A..A + ℓ, (c * cexp (I * (γ * x))).re
      ≥ (if γ = 0 then c.re * ℓ else 0) - (if γ = 0 then 0 else ‖c‖ * (2 / |γ|)) := by
  rw [integral_re_mul_exp]
  by_cases h : γ = 0
  · subst h
    simp
  · rw [if_neg h, if_neg h, zero_sub]
    have h1 := Complex.abs_re_le_norm (c * ∫ x in A..A + ℓ, cexp (I * (γ * x)))
    rw [norm_mul] at h1
    have h2 := norm_integral_exp_I_mul_le γ h A ℓ
    have h3 : ‖c‖ * ‖∫ x in A..A + ℓ, cexp (I * (γ * x))‖ ≤ ‖c‖ * (2 / |γ|) := by gcongr
    linarith [(abs_le.mp h1).1]

/-- The error term of a pair. -/
def pairError (w : ι → ℂ) (γ : ι → ℝ) (q q' : ι) : ℝ :=
  ‖w q‖ * ‖w q'‖ * ((if γ q + γ q' = 0 then 0 else 2 / |γ q + γ q'|)
    + (if γ q = γ q' then 0 else 2 / |γ q - γ q'|)) / 2

theorem pairError_nonneg (w : ι → ℂ) (γ : ι → ℝ) (q q' : ι) : 0 ≤ pairError w γ q q' := by
  unfold pairError
  have h1 : 0 ≤ (if γ q + γ q' = 0 then (0 : ℝ) else 2 / |γ q + γ q'|) := by split_ifs <;> positivity
  have h2 : 0 ≤ (if γ q = γ q' then (0 : ℝ) else 2 / |γ q - γ q'|) := by split_ifs <;> positivity
  positivity

/-- The main term of a pair. -/
def pairMain (w : ι → ℂ) (γ : ι → ℝ) (q q' : ι) : ℝ :=
  (if γ q + γ q' = 0 then (w q * w q').re else 0) + (if γ q = γ q' then (w q * starRingEnd ℂ (w q')).re else 0)

/-- Under the coefficient symmetry hypotheses the main term is nonnegative. -/
theorem pairMain_nonneg (w : ι → ℂ) (γ : ι → ℝ) (q q' : ι)
    (hsame : γ q = γ q' → w q = w q') (hopp : γ q + γ q' = 0 → w q' = starRingEnd ℂ (w q)) :
    0 ≤ pairMain w γ q q' := by
  unfold pairMain
  have h1 : 0 ≤ (if γ q + γ q' = 0 then (w q * w q').re else 0) := by
    split_ifs with h
    · rw [hopp h, Complex.mul_conj]; simp [Complex.normSq_nonneg]
    · exact le_rfl
  have h2 : 0 ≤ (if γ q = γ q' then (w q * starRingEnd ℂ (w q')).re else 0) := by
    split_ifs with h
    · rw [← hsame h, Complex.mul_conj]; simp [Complex.normSq_nonneg]
    · exact le_rfl
  linarith

theorem pairMain_zero_left (w : ι → ℂ) (γ : ι → ℝ) (q q' : ι) (h : w q = 0) :
    pairMain w γ q q' = 0 := by
  unfold pairMain; simp [h]

theorem pairMain_zero_right (w : ι → ℂ) (γ : ι → ℝ) (q q' : ι) (h : w q' = 0) :
    pairMain w γ q q' = 0 := by
  unfold pairMain; simp [h]

/-- With a nonzero frequency the self term is exactly `‖w q‖²`. -/
theorem pairMain_self_of_ne (w : ι → ℂ) (γ : ι → ℝ) (q : ι) (hγ : γ q ≠ 0) :
    pairMain w γ q q = ‖w q‖ ^ 2 := by
  unfold pairMain
  have h : γ q + γ q ≠ 0 := by intro h; apply hγ; linarith
  rw [if_neg h, if_pos rfl, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp [← Complex.ofReal_pow]

theorem pairMain_self_ge (w : ι → ℂ) (γ : ι → ℝ) (q : ι)
    (hopp : γ q + γ q = 0 → w q = starRingEnd ℂ (w q)) :
    ‖w q‖ ^ 2 ≤ pairMain w γ q q := by
  unfold pairMain
  have h1 : 0 ≤ (if γ q + γ q = 0 then (w q * w q).re else 0) := by
    split_ifs with h
    · have := hopp h
      rw [show w q * w q = w q * starRingEnd ℂ (w q) by rw [← this], Complex.mul_conj]
      simp [Complex.normSq_nonneg]
    · exact le_rfl
  rw [if_pos rfl, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [Complex.ofReal_re]
  linarith

theorem continuous_re_mul_exp (c : ℂ) (γ : ℝ) : Continuous fun x : ℝ => (c * cexp (I * (γ * x))).re := by
  fun_prop

/-- The window integral of a pair term is at least `pairMain · ℓ / 2 − pairError`. -/
theorem integral_pairTerm_ge (w : ι → ℂ) (γ : ι → ℝ) (q q' : ι) (A ℓ : ℝ) :
    pairMain w γ q q' * ℓ / 2 - pairError w γ q q' ≤ ∫ x in A..A + ℓ, pairTerm w γ q q' x := by
  have e : (fun x : ℝ => pairTerm w γ q q' x)
      = fun x : ℝ => ((w q * w q' * cexp (I * (((γ q + γ q' : ℝ) : ℂ) * (x : ℂ)))).re
        + (w q * starRingEnd ℂ (w q') * cexp (I * (((γ q - γ q' : ℝ) : ℂ) * (x : ℂ)))).re) / 2 := by
    funext x; unfold pairTerm; push_cast; ring_nf
  rw [e]
  have hi1 := (continuous_re_mul_exp (w q * w q') (γ q + γ q')).intervalIntegrable
    (μ := MeasureTheory.volume) A (A + ℓ)
  have hi2 := (continuous_re_mul_exp (w q * starRingEnd ℂ (w q')) (γ q - γ q')).intervalIntegrable
    (μ := MeasureTheory.volume) A (A + ℓ)
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add hi1 hi2]
  have h1 := integral_re_mul_exp_ge (w q * w q') (γ q + γ q') A ℓ
  have h2 := integral_re_mul_exp_ge (w q * starRingEnd ℂ (w q')) (γ q - γ q') A ℓ
  rw [norm_mul] at h1 h2
  rw [Complex.norm_conj] at h2
  simp only [sub_eq_zero] at h2
  unfold pairMain pairError
  by_cases hp : γ q + γ q' = 0 <;> by_cases hm : γ q = γ q'
  · simp only [if_pos hp, if_pos hm] at h1 h2 ⊢; linarith
  · simp only [if_pos hp, if_neg hm] at h1 h2 ⊢; linarith
  · simp only [if_neg hp, if_pos hm] at h1 h2 ⊢; linarith
  · simp only [if_neg hp, if_neg hm] at h1 h2 ⊢; linarith

/-- **The window mean square of `Re S` is at least half the sum of the squared moduli, up to
`O(1/ℓ)`.** -/
theorem integral_re_trigSum_sq_ge (F : Finset ι) (w : ι → ℂ) (γ : ι → ℝ)
    (hnn : ∀ q ∈ F, ∀ q' ∈ F, 0 ≤ pairMain w γ q q')
    (hself : ∀ q ∈ F, ‖w q‖ ^ 2 ≤ pairMain w γ q q) (A ℓ : ℝ) (hℓ : 0 ≤ ℓ) :
    (∑ q ∈ F, ‖w q‖ ^ 2) * ℓ / 2 - ∑ q ∈ F, ∑ q' ∈ F, pairError w γ q q'
      ≤ ∫ x in A..A + ℓ, (trigSum F w γ x).re ^ 2 := by
  have e : (fun x : ℝ => (trigSum F w γ x).re ^ 2) = fun x => ∑ q ∈ F, ∑ q' ∈ F, pairTerm w γ q q' x := by
    funext x; exact re_trigSum_sq F w γ x
  rw [e, intervalIntegral.integral_finsetSum fun q _ =>
    (continuous_finsetSum _ fun q' _ => continuous_pairTerm w γ q q').intervalIntegrable _ _]
  have hinner : ∀ q ∈ F, ∫ x in A..A + ℓ, ∑ q' ∈ F, pairTerm w γ q q' x
      = ∑ q' ∈ F, ∫ x in A..A + ℓ, pairTerm w γ q q' x := fun q _ =>
    intervalIntegral.integral_finsetSum fun q' _ => (continuous_pairTerm w γ q q').intervalIntegrable _ _
  rw [Finset.sum_congr rfl hinner]
  have hge : ∀ q ∈ F, ∑ q' ∈ F, (pairMain w γ q q' * ℓ / 2 - pairError w γ q q')
      ≤ ∑ q' ∈ F, ∫ x in A..A + ℓ, pairTerm w γ q q' x := fun q _ =>
    Finset.sum_le_sum fun q' _ => integral_pairTerm_ge w γ q q' A ℓ
  refine le_trans ?_ (Finset.sum_le_sum hge)
  simp_rw [Finset.sum_sub_distrib]
  rw [sub_le_sub_iff_right]
  -- `Σ_q Σ_{q'} pairMain ≥ Σ_q pairMain q q ≥ Σ_q ‖w q‖²`
  have hdiag : ∀ q ∈ F, ‖w q‖ ^ 2 * ℓ / 2 ≤ ∑ q' ∈ F, pairMain w γ q q' * ℓ / 2 := by
    intro q hq
    have h1 : ‖w q‖ ^ 2 ≤ pairMain w γ q q := hself q hq
    have h2 : pairMain w γ q q ≤ ∑ q' ∈ F, pairMain w γ q q' :=
      Finset.single_le_sum (fun q' hq' => hnn q hq q' hq') hq
    rw [← Finset.sum_div, ← Finset.sum_mul]
    have : 0 ≤ ℓ / 2 := by positivity
    calc ‖w q‖ ^ 2 * ℓ / 2 = ‖w q‖ ^ 2 * (ℓ / 2) := by ring
      _ ≤ (∑ q' ∈ F, pairMain w γ q q') * (ℓ / 2) := by gcongr; linarith
      _ = (∑ q' ∈ F, pairMain w γ q q') * ℓ / 2 := by ring
  calc (∑ q ∈ F, ‖w q‖ ^ 2) * ℓ / 2 = ∑ q ∈ F, ‖w q‖ ^ 2 * ℓ / 2 := by
        rw [Finset.sum_mul, Finset.sum_div]
    _ ≤ ∑ q ∈ F, ∑ q' ∈ F, pairMain w γ q q' * ℓ / 2 := Finset.sum_le_sum hdiag

/-! ## Positivity extraction -/

/-- **Positivity extraction.**  A function bounded by `W` on a window, with mean at least `−ε` and
mean square at least `m > Wε`, exceeds `(m − Wε)/(4W)` somewhere on the window. -/
theorem exists_ge_of_integral_bounds {f : ℝ → ℝ} {A ℓ W ε m : ℝ} (hℓ : 0 < ℓ)
    (hf : ContinuousOn f (Icc A (A + ℓ))) (hW : ∀ x ∈ Icc A (A + ℓ), |f x| ≤ W)
    (hmean : -(ε * ℓ) ≤ ∫ x in A..A + ℓ, f x) (hsq : m * ℓ ≤ ∫ x in A..A + ℓ, f x ^ 2)
    (hW0 : 0 < W) (hm : W * ε < m) :
    ∃ x ∈ Icc A (A + ℓ), (m - W * ε) / (4 * W) ≤ f x := by
  by_contra hcon
  push Not at hcon
  set s : ℝ := (m - W * ε) / (4 * W) with hs
  have hs0 : 0 < s := by rw [hs]; apply div_pos <;> linarith
  have hAle : A ≤ A + ℓ := by linarith
  have hfi : IntervalIntegrable f MeasureTheory.volume A (A + ℓ) :=
    (hf.intervalIntegrable_of_Icc hAle)
  have hf2 : IntervalIntegrable (fun x => f x ^ 2) MeasureTheory.volume A (A + ℓ) :=
    ((hf.pow 2).intervalIntegrable_of_Icc hAle)
  have hg : IntervalIntegrable (fun x => W * (2 * s - f x)) MeasureTheory.volume A (A + ℓ) :=
    ((continuousOn_const.sub hf).const_smul W |>.intervalIntegrable_of_Icc hAle)
  have hpt : ∀ x ∈ Icc A (A + ℓ), f x ^ 2 ≤ W * (2 * s - f x) := by
    intro x hx
    have h1 := hW x hx
    have h2 := hcon x hx
    have h3 := (abs_le.mp h1).1
    have h4 := (abs_le.mp h1).2
    nlinarith
  have hint := intervalIntegral.integral_mono_on hAle hf2 hg hpt
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
    (by simp) hfi,
    intervalIntegral.integral_const, smul_eq_mul, show A + ℓ - A = ℓ by ring] at hint
  have hs' : 4 * W * s = m - W * ε := by rw [hs]; field_simp
  have hs'' : 4 * W * s * ℓ = (m - W * ε) * ℓ := by rw [hs']
  have h1 : W * (-(ε * ℓ)) ≤ W * ∫ x in A..A + ℓ, f x := mul_le_mul_of_nonneg_left hmean hW0.le
  have h5 : 0 < (m - W * ε) * ℓ := mul_pos (by linarith) hℓ
  nlinarith

end TrigSum

end
