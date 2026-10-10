import GaloisForLFunctions.RHTower.XiGaussianHeatRouteCapstone
import GaloisForLFunctions.RHTower.RiemannVonMangoldt
import GaloisForLFunctions.RHTower.XiOrderedZeroCopyEnumeration
import GaloisForLFunctions.HTGeometry.PolynomialCoeffMassLagrange

/-!
# The heat Hankel form is positive on each fixed degree at small heat time

**Theorem** (`exists_heatHankel_pos_of_natDegree_le`).  For every degree `d` there is `a_d > 0`
such that for `0 < a < a_d` the heat Hankel form `H_a(P) = Σ_q e^{-a w_q} P(w_q)
\overline{P(\overline{w_q})}` is positive on every nonzero polynomial of degree `≤ d`.  This holds
unconditionally.

RH is the statement that one `a` works for every `d` (`riemannHypothesis_iff_heatHankel_nonneg`).
Unconditionally the window shrinks with `d`.  A fixed off-line pair needs degree `≫ a^{-1/2}` to be
seen, because the real frequencies dominating the weighted mass must first be killed.

Proof.  Rescale `Q(s) = P(s/a)`.  Each copy contributes at least
`e^{-σ}|Q(σ)|² − (1+2d)|ε| e^{-σ} coeffMass(Q)² (1+2|s|)^{2d}` with `s = a w_q = σ + iε`
(`re_exp_mul_eval_mul_conj_ge`).
* The errors sum to `O(a^{-1/2})` by `|ε| ≤ a|γ|` and the growth bound
  `Σ_q e^{-(a/4) Re w_q} ≤ (16/a) Σ_q |z_q|^{-2}`.
* By Riemann–von Mangoldt, each of `d + 1` separated windows `σ ∈ [x_k, y_k] ⊆ [1, 2]` holds
  `≫ a^{-1/2} log(1/a)` copies.
* Lagrange interpolation at the minimizers (`coeffMass_le_of_nodes`) turns these counts into
  `≫ a^{-1/2} log(1/a) · coeffMass(Q)²`.
-/

open Complex Filter Topology Set Polynomial
open GaloisForLFunctions.HTGeometry (coeffMass coeffMass_nonneg coeffMass_le_of_nodes
  re_exp_mul_eval_mul_conj_ge)

namespace RHTower

noncomputable section

/-! ## Windows of copies -/

/-- Copies with ordinate in `(T₁, T₂]`. -/
def xiCopiesWindow (T₁ T₂ : ℝ) : Finset XiZeroCopy := xiCopiesPos T₂ \ xiCopiesPos T₁

theorem mem_xiCopiesWindow {T₁ T₂ : ℝ} (hT₁ : 0 ≤ T₁) {q : XiZeroCopy} :
    q ∈ xiCopiesWindow T₁ T₂ ↔ T₁ < (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ T₂ := by
  rw [xiCopiesWindow, Finset.mem_sdiff, mem_xiCopiesPos, mem_xiCopiesPos]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    rw [abs_of_pos h2] at h1
    refine ⟨?_, h1⟩
    by_contra h
    push Not at h
    exact h3 ⟨by rw [abs_of_pos h2]; exact h, h2⟩
  · rintro ⟨h1, h2⟩
    have hpos : 0 < (q.1 : ℂ).im := lt_of_le_of_lt hT₁ h1
    refine ⟨⟨by rw [abs_of_pos hpos]; exact h2, hpos⟩, fun h => ?_⟩
    rw [abs_of_pos hpos] at h
    linarith [h.1]

theorem card_xiCopiesWindow {T₁ T₂ : ℝ} (hT₁ : 0 ≤ T₁) (hT : T₁ ≤ T₂) :
    ((xiCopiesWindow T₁ T₂).card : ℝ) = (xiZeroCount T₂ : ℝ) - xiZeroCount T₁ := by
  have hsub : xiCopiesPos T₁ ⊆ xiCopiesPos T₂ := fun q hq => by
    rw [mem_xiCopiesPos] at hq ⊢
    exact ⟨hq.1.trans hT, hq.2⟩
  rw [xiCopiesWindow, Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub)]
  have h1 := intCast_card_xiCopiesPos hT₁
  have h2 := intCast_card_xiCopiesPos (hT₁.trans hT)
  have e1 : ((xiCopiesPos T₁).card : ℝ) = (xiZeroCount T₁ : ℝ) := by exact_mod_cast h1
  have e2 : ((xiCopiesPos T₂).card : ℝ) = (xiZeroCount T₂ : ℝ) := by exact_mod_cast h2
  rw [e1, e2]

/-- **Riemann–von Mangoldt windows.**  If `T₁ ≤ T₂/r` with `r > 1`, then for `T₁` large the window
`(T₁, T₂]` holds at least `(1 − 1/r)/(4π) · T₂ log T₂` copies. -/
theorem exists_card_xiCopiesWindow_ge {r : ℝ} (hr : 1 < r) :
    ∃ T₀ : ℝ, 4 ≤ T₀ ∧ ∀ T₁ T₂ : ℝ, T₀ ≤ T₁ → r * T₁ ≤ T₂ →
      (1 - 1 / r) / (4 * Real.pi) * (T₂ * Real.log T₂) ≤ ((xiCopiesWindow T₁ T₂).card : ℝ) := by
  have hr0 : 0 < r := by linarith
  have hκ : 0 < 1 - 1 / r := by rw [sub_pos, div_lt_one hr0]; exact hr
  obtain ⟨T₀, hT₀, hclose⟩ :=
    exists_xiZeroCount_close ((1 - 1 / r) / (8 * Real.pi)) (div_pos hκ (by positivity))
  refine ⟨T₀, hT₀, fun T₁ T₂ hT₁ hT₂ => ?_⟩
  have hT₁4 : 4 ≤ T₁ := hT₀.trans hT₁
  have hT₁T₂ : T₁ ≤ T₂ := by nlinarith
  have hT₂0 : T₀ ≤ T₂ := hT₁.trans hT₁T₂
  rw [card_xiCopiesWindow (by linarith) hT₁T₂]
  have c1 := hclose T₁ hT₁
  have c2 := hclose T₂ hT₂0
  have hlog₁ : 0 ≤ Real.log T₁ := Real.log_nonneg (by linarith)
  have hlogle : Real.log T₁ ≤ Real.log T₂ := Real.log_le_log (by linarith) hT₁T₂
  have hT₁le : T₁ ≤ T₂ / r := by rw [le_div_iff₀ hr0]; linarith
  have hprod : T₁ * Real.log T₁ ≤ T₂ / r * Real.log T₂ :=
    mul_le_mul hT₁le hlogle hlog₁ (div_nonneg (by linarith) hr0.le)
  have hπ := Real.pi_pos
  rw [abs_le] at c1 c2
  have hX0 : 0 ≤ T₂ * Real.log T₂ := mul_nonneg (by linarith) (hlog₁.trans hlogle)
  have key : (1 / (2 * Real.pi)) * (T₂ * Real.log T₂) - (1 / (2 * Real.pi)) * (T₁ * Real.log T₁) ≥
      (1 / (2 * Real.pi)) * (1 - 1 / r) * (T₂ * Real.log T₂) := by
    have : T₁ * Real.log T₁ ≤ 1 / r * (T₂ * Real.log T₂) := by
      calc T₁ * Real.log T₁ ≤ T₂ / r * Real.log T₂ := hprod
        _ = 1 / r * (T₂ * Real.log T₂) := by ring
    have h2π : 0 < 1 / (2 * Real.pi) := by positivity
    nlinarith
  have hε : (1 - 1 / r) / (8 * Real.pi) * (T₁ * Real.log T₁) ≤
      (1 - 1 / r) / (8 * Real.pi) * (T₂ * Real.log T₂) :=
    mul_le_mul_of_nonneg_left (mul_le_mul hT₁T₂ hlogle hlog₁ (by linarith)) (by positivity)
  have e1 : (1 / (2 * Real.pi)) * (1 - 1 / r) = 4 * ((1 - 1 / r) / (8 * Real.pi)) := by
    field_simp; ring
  have e2 : (1 - 1 / r) / (4 * Real.pi) = 2 * ((1 - 1 / r) / (8 * Real.pi)) := by field_simp; ring
  rw [e2]
  nlinarith [c1.1, c1.2, c2.1, c2.2]

/-! ## The error budget -/

theorem one_add_mul_two_pow_le_exp (σ : ℝ) (hσ : -(1 / 4) ≤ σ) (d : ℕ) :
    (2 + 2 * σ) ^ (2 * d) ≤
      (2 : ℝ) ^ (2 * d) * 4 ^ (2 * d) * (2 * d).factorial * Real.exp (1 / 4) * Real.exp (σ / 4) := by
  set y := (1 + σ) / 4 with hy
  have hy0 : 0 ≤ y := by rw [hy]; linarith
  have h1 := Real.pow_div_factorial_le_exp y hy0 (2 * d)
  rw [div_le_iff₀ (by positivity)] at h1
  have h2 : (2 + 2 * σ) ^ (2 * d) = 2 ^ (2 * d) * 4 ^ (2 * d) * y ^ (2 * d) := by
    rw [hy, ← mul_pow, ← mul_pow]; congr 1; ring
  have h3 : Real.exp y = Real.exp (1 / 4) * Real.exp (σ / 4) := by
    rw [← Real.exp_add]; congr 1; rw [hy]; ring
  rw [h2]
  calc (2 : ℝ) ^ (2 * d) * 4 ^ (2 * d) * y ^ (2 * d)
      ≤ (2 : ℝ) ^ (2 * d) * 4 ^ (2 * d) * (Real.exp y * (2 * d).factorial) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by rw [h3]; ring

theorem mul_exp_neg_sq_le (v : ℝ) : v * Real.exp (-(v ^ 2 / 2)) ≤ 1 := by
  have h := Real.add_one_le_exp (v ^ 2 / 2)
  have : v ≤ Real.exp (v ^ 2 / 2) := by nlinarith [sq_nonneg (v - 1)]
  calc v * Real.exp (-(v ^ 2 / 2)) ≤ Real.exp (v ^ 2 / 2) * Real.exp (-(v ^ 2 / 2)) :=
        mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

/-- The scaled error of one copy is `O(√a e^{-(a/4) Re w})`. -/
theorem heat_error_le {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (d : ℕ) (q : XiZeroCopy) :
    |(((a : ℂ) * xiHeatFrequency q)).im| * Real.exp (-((a : ℂ) * xiHeatFrequency q).re) *
        (1 + 2 * ‖(a : ℂ) * xiHeatFrequency q‖) ^ (2 * d) ≤
      ((2 : ℝ) ^ (2 * d) * 4 ^ (2 * d) * (2 * d).factorial * Real.exp (1 / 4) * Real.exp (3 / 16)) *
        (Real.sqrt a * Real.exp (-(a / 4 * (xiHeatFrequency q).re))) := by
  set w := xiHeatFrequency q with hw
  set γ := (xiSpectralPoint q).re with hγ
  set C := (2 : ℝ) ^ (2 * d) * 4 ^ (2 * d) * (2 * d).factorial * Real.exp (1 / 4) with hC
  have hC0 : 0 ≤ C := by positivity
  have hsre : ((a : ℂ) * w).re = a * w.re := by simp
  have hsim : ((a : ℂ) * w).im = a * w.im := by simp
  have hsnorm : ‖(a : ℂ) * w‖ = a * ‖w‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ha.le]
  rw [hsre, hsim, hsnorm]
  set σ := a * w.re with hσ
  have hwre := xiHeatFrequency_re q
  have him4 := xiSpectralPoint_im_sq_lt_quarter q
  have hwnorm := norm_xiHeatFrequency_le_re q
  have hσlow : -(1 / 4) ≤ σ := by
    have := neg_quarter_lt_re_xiHeatFrequency q
    rw [hσ]; nlinarith
  have hbase : 1 + 2 * (a * ‖w‖) ≤ 2 + 2 * σ := by
    have : a * ‖w‖ ≤ σ + a / 2 := by rw [hσ]; nlinarith
    linarith
  have hpow : (1 + 2 * (a * ‖w‖)) ^ (2 * d) ≤ C * Real.exp (σ / 4) :=
    (pow_le_pow_left₀ (by positivity) hbase _).trans (one_add_mul_two_pow_le_exp σ hσlow d)
  have himw : |a * w.im| ≤ a * |γ| := by
    rw [abs_mul, abs_of_pos ha]
    exact mul_le_mul_of_nonneg_left (abs_im_xiHeatFrequency_le q) ha.le
  -- the Gaussian factor
  have hγ2 : w.re ≤ γ ^ 2 := by rw [hwre]; nlinarith [sq_nonneg (xiSpectralPoint q).im]
  have hσγ : a * γ ^ 2 - a / 4 ≤ σ := by rw [hσ, hwre]; nlinarith
  have hgauss : a * |γ| * Real.exp (-(3 * σ / 4)) ≤
      Real.exp (3 / 16) * (Real.sqrt a * Real.exp (-(a / 4 * w.re))) := by
    have hsa := Real.sqrt_nonneg a
    have hsa2 : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
    set v := Real.sqrt a * |γ| with hv
    have hv0 : 0 ≤ v := by positivity
    have hv2 : v ^ 2 = a * γ ^ 2 := by rw [hv, mul_pow, hsa2, sq_abs]
    have h1 := mul_exp_neg_sq_le v
    have h2 : Real.exp (-(3 * σ / 4)) ≤ Real.exp (3 / 16) * Real.exp (-(v ^ 2 / 2)) *
        Real.exp (-(a / 4 * w.re)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.2
      rw [hv2]
      have : a / 4 * w.re ≤ a / 4 * γ ^ 2 := mul_le_mul_of_nonneg_left hγ2 (by positivity)
      nlinarith
    have hav : a * |γ| = Real.sqrt a * v := by rw [hv, ← mul_assoc, Real.mul_self_sqrt ha.le]
    calc a * |γ| * Real.exp (-(3 * σ / 4)) = Real.sqrt a * v * Real.exp (-(3 * σ / 4)) := by
          rw [hav]
      _ ≤ Real.sqrt a * v * (Real.exp (3 / 16) * Real.exp (-(v ^ 2 / 2)) *
            Real.exp (-(a / 4 * w.re))) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = Real.exp (3 / 16) * (Real.sqrt a * Real.exp (-(a / 4 * w.re))) *
            (v * Real.exp (-(v ^ 2 / 2))) := by ring
      _ ≤ Real.exp (3 / 16) * (Real.sqrt a * Real.exp (-(a / 4 * w.re))) * 1 :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := mul_one _
  have he := (Real.exp_pos (-σ)).le
  calc |a * w.im| * Real.exp (-σ) * (1 + 2 * (a * ‖w‖)) ^ (2 * d)
      ≤ a * |γ| * Real.exp (-σ) * (C * Real.exp (σ / 4)) := by
        gcongr
    _ = C * (a * |γ| * Real.exp (-(3 * σ / 4))) := by
        have hexp : Real.exp (-σ) * Real.exp (σ / 4) = Real.exp (-(3 * σ / 4)) := by
          rw [← Real.exp_add]; congr 1; ring
        calc a * |γ| * Real.exp (-σ) * (C * Real.exp (σ / 4)) =
            C * (a * |γ| * (Real.exp (-σ) * Real.exp (σ / 4))) := by ring
          _ = _ := by rw [hexp]
    _ ≤ C * (Real.exp (3 / 16) * (Real.sqrt a * Real.exp (-(a / 4 * w.re)))) :=
        mul_le_mul_of_nonneg_left hgauss hC0
    _ = _ := by ring

theorem exp_neg_quarter_re_le {a : ℝ} (ha : 0 < a) (q : XiZeroCopy) :
    Real.exp (-(a / 4 * (xiHeatFrequency q).re)) ≤ 16 / a * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
  have hτ : 0 < (((a / 4 : ℝ)) : ℂ).re := by simp; linarith
  have h := norm_xiGaussianHeatTermC_le_growth hτ q
  rw [norm_xiGaussianHeatTermC] at h
  simp only [ofReal_re, ofReal_im, zero_pow (two_ne_zero), zero_div, Real.exp_zero, one_mul,
    zero_mul, sub_zero] at h
  have e : (a / 4) * (xiSpectralPoint q ^ (2 : ℕ)).re = a / 4 * (xiHeatFrequency q).re := rfl
  rw [e] at h
  calc Real.exp (-(a / 4 * (xiHeatFrequency q).re)) ≤ 4 / (a / 4) * (1 / ‖xiSpectralPoint q‖ ^ 2) := h
    _ = 16 / a * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by field_simp; ring

/-! ## The window theorem -/

theorem coeffMass_pos_of_ne_zero {Q : ℂ[X]} (hQ : Q ≠ 0) : 0 < coeffMass Q := by
  obtain ⟨k, hk⟩ : ∃ k, Q.coeff k ≠ 0 := by
    by_contra h
    push Not at h
    exact hQ (Polynomial.ext fun k => by simpa using h k)
  have hN : Q.natDegree < Q.natDegree + 1 := Nat.lt_succ_self _
  have hk' : k < Q.natDegree + 1 := Nat.lt_succ_of_le (le_natDegree_of_ne_zero hk)
  rw [GaloisForLFunctions.HTGeometry.coeffMass_eq_sum_range Q hN]
  exact lt_of_lt_of_le (norm_pos_iff.2 hk)
    (Finset.single_le_sum (f := fun i => ‖Q.coeff i‖) (fun i _ => norm_nonneg _)
      (Finset.mem_range.2 hk'))

/-- Copies in a window have scaled real part `σ = a Re w ∈ [x, y]`. -/
theorem scaled_re_mem_of_mem_window {a x y : ℝ} (ha : 0 < a) (hx : 0 ≤ x) {q : XiZeroCopy}
    (hq : q ∈ xiCopiesWindow (Real.sqrt (x / a + 1 / 4)) (Real.sqrt (y / a))) :
    x ≤ a * (xiHeatFrequency q).re ∧ a * (xiHeatFrequency q).re ≤ y := by
  rw [mem_xiCopiesWindow (Real.sqrt_nonneg _)] at hq
  obtain ⟨h1, h2⟩ := hq
  rw [← xiSpectralPoint_re_eq] at h1 h2
  set γ := (xiSpectralPoint q).re
  have hre := xiHeatFrequency_re q
  have him := xiSpectralPoint_im_sq_lt_quarter q
  have hpos : 0 < γ := lt_of_le_of_lt (Real.sqrt_nonneg _) h1
  have hT1 : Real.sqrt (x / a + 1 / 4) ^ 2 = x / a + 1 / 4 := Real.sq_sqrt (by positivity)
  have hy0 : 0 ≤ y / a := by
    by_contra hneg
    push Not at hneg
    have := Real.sqrt_eq_zero_of_nonpos hneg.le
    rw [this] at h2
    linarith
  have hT2 : Real.sqrt (y / a) ^ 2 = y / a := Real.sq_sqrt hy0
  have hγ1 : x / a + 1 / 4 < γ ^ 2 := by
    rw [← hT1]; exact pow_lt_pow_left₀ h1 (Real.sqrt_nonneg _) (by norm_num)
  have hγ2 : γ ^ 2 ≤ y / a := by
    rw [← hT2]; exact pow_le_pow_left₀ hpos.le h2 2
  rw [hre]
  constructor
  · have : x / a < γ ^ 2 - (xiSpectralPoint q).im ^ 2 := by linarith
    rw [div_lt_iff₀ ha] at this
    linarith
  · have : γ ^ 2 - (xiSpectralPoint q).im ^ 2 ≤ y / a := by nlinarith [sq_nonneg (xiSpectralPoint q).im]
    rw [le_div_iff₀ ha] at this
    linarith

/-! ## Rescaling and the lower bound -/

/-- The rescaled polynomial `Q(s) = P(s/a)`. -/
def heatRescale (a : ℝ) (P : ℂ[X]) : ℂ[X] := P.comp (C (a : ℂ)⁻¹ * X)

theorem eval_heatRescale {a : ℝ} (ha : 0 < a) (P : ℂ[X]) (w : ℂ) :
    (heatRescale a P).eval ((a : ℂ) * w) = P.eval w := by
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  rw [heatRescale, eval_comp, eval_mul, eval_C, eval_X, inv_mul_cancel_left₀ ha0]

theorem natDegree_heatRescale_le {a : ℝ} (ha : 0 < a) {d : ℕ} {P : ℂ[X]} (hP : P.natDegree ≤ d) :
    (heatRescale a P).natDegree ≤ d := by
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  rw [heatRescale, natDegree_comp, natDegree_C_mul_X _ (inv_ne_zero ha0), mul_one]
  exact hP

theorem heatRescale_ne_zero {a : ℝ} (ha : 0 < a) {P : ℂ[X]} (hP : P ≠ 0) :
    heatRescale a P ≠ 0 := by
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  intro hQ0
  apply hP
  have hcomp : (C (a : ℂ)⁻¹ * X).comp (C (a : ℂ) * X) = X := by
    rw [mul_comp, C_comp, X_comp, ← mul_assoc, ← C_mul, inv_mul_cancel₀ ha0, C_1, one_mul]
  have : P = (heatRescale a P).comp (C (a : ℂ) * X) := by
    rw [heatRescale, comp_assoc, hcomp, comp_X]
  rw [this, hQ0, zero_comp]

/-- The error constant `(1 + 2d) C_d · 16 · Σ_q |z_q|^{-2}`. -/
def heatWindowErrorConst (d : ℕ) : ℝ :=
  (1 + 2 * (d : ℝ)) * ((2 : ℝ) ^ (2 * d) * 4 ^ (2 * d) * (2 * d).factorial * Real.exp (1 / 4) *
    Real.exp (3 / 16)) * 16 * ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)

theorem heatWindowErrorConst_nonneg (d : ℕ) : 0 ≤ heatWindowErrorConst d := by
  have : 0 ≤ ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) :=
    tsum_nonneg fun _ => by positivity
  unfold heatWindowErrorConst
  positivity

/-- The pointwise error of one copy in the comparison with the real part. -/
def heatWindowError (a : ℝ) (d : ℕ) (M : ℝ) (q : XiZeroCopy) : ℝ :=
  (1 + 2 * (d : ℝ)) * M ^ 2 *
    (|((a : ℂ) * xiHeatFrequency q).im| * Real.exp (-((a : ℂ) * xiHeatFrequency q).re) *
      (1 + 2 * ‖(a : ℂ) * xiHeatFrequency q‖) ^ (2 * d))

theorem heatWindowError_nonneg (a : ℝ) (d : ℕ) (M : ℝ) (q : XiZeroCopy) :
    0 ≤ heatWindowError a d M q := by
  unfold heatWindowError; positivity

theorem heatWindowError_le {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (d : ℕ) (M : ℝ) (q : XiZeroCopy) :
    heatWindowError a d M q ≤
      (1 + 2 * (d : ℝ)) * M ^ 2 * ((2 : ℝ) ^ (2 * d) * 4 ^ (2 * d) * (2 * d).factorial *
        Real.exp (1 / 4) * Real.exp (3 / 16) * 16) / Real.sqrt a *
        (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
  have h1 := heat_error_le ha ha1 d q
  have h2 := exp_neg_quarter_re_le ha q
  have hk : 0 ≤ (1 + 2 * (d : ℝ)) * M ^ 2 := by positivity
  set Cd := (2 : ℝ) ^ (2 * d) * 4 ^ (2 * d) * (2 * d).factorial * Real.exp (1 / 4) *
    Real.exp (3 / 16) with hCd
  have hCd0 : 0 ≤ Cd := by positivity
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hsa2 : Real.sqrt a * (16 / a) = 16 / Real.sqrt a := by
    have e : a = Real.sqrt a * Real.sqrt a := (Real.mul_self_sqrt ha.le).symm
    calc Real.sqrt a * (16 / a) = Real.sqrt a * (16 / (Real.sqrt a * Real.sqrt a)) := by
          rw [← e]
      _ = 16 / Real.sqrt a := by field_simp
  calc heatWindowError a d M q ≤ (1 + 2 * (d : ℝ)) * M ^ 2 *
        (Cd * (Real.sqrt a * Real.exp (-(a / 4 * (xiHeatFrequency q).re)))) :=
        mul_le_mul_of_nonneg_left h1 hk
    _ ≤ (1 + 2 * (d : ℝ)) * M ^ 2 *
        (Cd * (Real.sqrt a * (16 / a * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ))))) := by
        gcongr
    _ = (1 + 2 * (d : ℝ)) * M ^ 2 * (Cd * (Real.sqrt a * (16 / a))) *
        (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by ring
    _ = _ := by rw [hsa2]; ring

theorem tsum_heatWindowError_le {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (d : ℕ) (M : ℝ) :
    Summable (heatWindowError a d M) ∧
      ∑' q, heatWindowError a d M q ≤ M ^ 2 * (heatWindowErrorConst d / Real.sqrt a) := by
  have hsumZ := xiSpectralPoint_inv_sq_summable
  have hle := heatWindowError_le ha ha1 d M
  have hS : Summable (heatWindowError a d M) :=
    (hsumZ.mul_left _).of_nonneg_of_le (heatWindowError_nonneg a d M) hle
  refine ⟨hS, (Summable.tsum_le_tsum hle hS (hsumZ.mul_left _)).trans (le_of_eq ?_)⟩
  rw [tsum_mul_left, heatWindowErrorConst]
  ring

/-- **The windowed lower bound.**  For every finite set `W` of copies,
`Re H_a(P) ≥ Σ_{q ∈ W} e^{-σ_q} |Q(σ_q)|² − ‖Q‖₁² E_d / √a`, where `Q(s) = P(s/a)` and
`σ_q = a Re w_q`. -/
theorem heatHankel_re_ge_window {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {d : ℕ} {P : ℂ[X]}
    (hP : P.natDegree ≤ d) (W : Finset XiZeroCopy) :
    ∑ q ∈ W, Real.exp (-(a * (xiHeatFrequency q).re)) *
        ‖(heatRescale a P).eval ((a * (xiHeatFrequency q).re : ℝ) : ℂ)‖ ^ 2 -
      coeffMass (heatRescale a P) ^ 2 * (heatWindowErrorConst d / Real.sqrt a) ≤
      (heatHankel a P P).re := by
  classical
  set Q := heatRescale a P with hQ
  set M := coeffMass Q with hM
  set main : XiZeroCopy → ℝ := fun q => Real.exp (-(a * (xiHeatFrequency q).re)) *
    ‖Q.eval ((a * (xiHeatFrequency q).re : ℝ) : ℂ)‖ ^ 2 with hmain
  have hQd := natDegree_heatRescale_le ha hP
  obtain ⟨herrS, herrT⟩ := tsum_heatWindowError_le ha ha1 d M
  have hterm : ∀ q, (if q ∈ W then main q else 0) - heatWindowError a d M q ≤
      (heatHankelTermAt a P P (xiHeatFrequency q)).re := by
    intro q
    have h := re_exp_mul_eval_mul_conj_ge Q hQd ((a : ℂ) * xiHeatFrequency q)
    have heq : heatHankelTermAt a P P (xiHeatFrequency q) =
        Complex.exp (-((a : ℂ) * xiHeatFrequency q)) * Q.eval ((a : ℂ) * xiHeatFrequency q) *
          (starRingEnd ℂ) (Q.eval ((starRingEnd ℂ) ((a : ℂ) * xiHeatFrequency q))) := by
      rw [heatHankelTermAt, hQ, eval_heatRescale ha, map_mul, Complex.conj_ofReal,
        eval_heatRescale ha, neg_mul]
    rw [heq]
    have hre : ((a : ℂ) * xiHeatFrequency q).re = a * (xiHeatFrequency q).re := by simp
    rw [hre] at h
    have hmain0 : 0 ≤ main q := by simp only [hmain]; positivity
    have herr0 := heatWindowError_nonneg a d M q
    have hle : main q - heatWindowError a d M q ≤
        (Complex.exp (-((a : ℂ) * xiHeatFrequency q)) * Q.eval ((a : ℂ) * xiHeatFrequency q) *
          (starRingEnd ℂ) (Q.eval ((starRingEnd ℂ) ((a : ℂ) * xiHeatFrequency q)))).re := by
      simp only [hmain, heatWindowError, hre]
      linarith
    split_ifs
    · exact hle
    · linarith
  have hsre : Summable fun q : XiZeroCopy => (heatHankelTermAt a P P (xiHeatFrequency q)).re :=
    (summable_heatHankelTermAt ha P P).mapL Complex.reCLM
  have hmainW : Summable fun q => (if q ∈ W then main q else 0) :=
    summable_of_ne_finset_zero (s := W) fun q hq => if_neg hq
  rw [heatHankel, Complex.re_tsum (summable_heatHankelTermAt ha P P)]
  have h1 := Summable.tsum_le_tsum hterm (hmainW.sub herrS) hsre
  rw [Summable.tsum_sub hmainW herrS, tsum_eq_sum (s := W) fun q hq => if_neg hq,
    Finset.sum_ite_mem, Finset.inter_self] at h1
  have : M ^ 2 * (heatWindowErrorConst d / Real.sqrt a) ≥ ∑' q, heatWindowError a d M q := herrT
  linarith

/-! ## Separated windows force coefficient mass -/

/-- **Lagrange on separated windows.**  If `d + 1` finite sets of points `σ ∈ [0, 2]` are pairwise
`h`-separated and each has at least `K > 0` elements, then every `Q` of degree `≤ d` satisfies
`Σ_k Σ_{q ∈ A_k} e^{-σ_q} |Q(σ_q)|² ≥ e^{-2} K ‖Q‖₁² / (L_d² (d + 1))` with `L_d = (3/h)^d`. -/
theorem sum_window_main_ge {ι : Type*} {d : ℕ} {h K : ℝ} (hh : 0 < h)
    (A : Fin (d + 1) → Finset ι) (σ : ι → ℝ)
    (hσ : ∀ k, ∀ q ∈ A k, 0 ≤ σ q ∧ σ q ≤ 2)
    (hsep : ∀ k k', k ≠ k' → ∀ q ∈ A k, ∀ q' ∈ A k', h ≤ |σ q - σ q'|)
    (hK : 0 < K) (hcard : ∀ k, K ≤ ((A k).card : ℝ)) (Q : ℂ[X]) (hQ : Q.natDegree ≤ d) :
    Real.exp (-2) * K * (coeffMass Q ^ 2 / ((((1 + 2) / h) ^ d) ^ 2 * (d + 1))) ≤
      ∑ k, ∑ q ∈ A k, Real.exp (-σ q) * ‖Q.eval (σ q : ℂ)‖ ^ 2 := by
  classical
  have hAne : ∀ k, (A k).Nonempty := fun k => by
    rw [← Finset.card_pos]; exact_mod_cast lt_of_lt_of_le hK (hcard k)
  choose t ht htmin using fun k =>
    (A k).exists_min_image (fun q => ‖Q.eval (σ q : ℂ)‖) (hAne k)
  set v : Fin (d + 1) → ℂ := fun k => (σ (t k) : ℂ) with hv
  have hv2 : ∀ k, ‖v k‖ ≤ 2 := fun k => by
    have h1 := hσ k (t k) (ht k)
    simp only [hv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h1.1]
    exact h1.2
  have hvsep : ∀ k k', k ≠ k' → h ≤ ‖v k - v k'‖ := fun k k' hkk => by
    simp only [hv]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact hsep k k' hkk _ (ht k) _ (ht k')
  set L := ((1 + 2) / h) ^ d with hL
  have hL0 : 0 < L := by positivity
  set M := coeffMass Q with hM
  have hM0 : 0 ≤ M := coeffMass_nonneg Q
  have hLag : M ≤ L * ∑ k, ‖Q.eval (v k)‖ := coeffMass_le_of_nodes v hh hv2 hvsep Q hQ
  have hCS := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin (d + 1))))
    (f := fun k => ‖Q.eval (v k)‖)
  rw [Finset.card_univ, Fintype.card_fin] at hCS
  push_cast at hCS
  have hblock : ∀ k, Real.exp (-2) * K * ‖Q.eval (v k)‖ ^ 2 ≤
      ∑ q ∈ A k, Real.exp (-σ q) * ‖Q.eval (σ q : ℂ)‖ ^ 2 := fun k => by
    have hterm' : ∀ q ∈ A k, Real.exp (-2) * ‖Q.eval (v k)‖ ^ 2 ≤
        Real.exp (-σ q) * ‖Q.eval (σ q : ℂ)‖ ^ 2 := fun q hq => by
      have he : Real.exp (-2) ≤ Real.exp (-σ q) := Real.exp_le_exp.2 (by linarith [(hσ k q hq).2])
      have hm : ‖Q.eval (v k)‖ ≤ ‖Q.eval (σ q : ℂ)‖ := htmin k q hq
      exact mul_le_mul he (pow_le_pow_left₀ (norm_nonneg _) hm 2) (by positivity) (by positivity)
    calc Real.exp (-2) * K * ‖Q.eval (v k)‖ ^ 2
        ≤ Real.exp (-2) * ((A k).card : ℝ) * ‖Q.eval (v k)‖ ^ 2 := by
          gcongr
          exact hcard k
      _ = ∑ q ∈ A k, Real.exp (-2) * ‖Q.eval (v k)‖ ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ _ := Finset.sum_le_sum hterm'
  have hd1 : (0 : ℝ) < d + 1 := by positivity
  have hM2 : M ^ 2 / (L ^ 2 * (d + 1)) ≤ ∑ k, ‖Q.eval (v k)‖ ^ 2 := by
    have h1 : M ^ 2 ≤ L ^ 2 * (∑ k, ‖Q.eval (v k)‖) ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hM0 hLag 2
    rw [div_le_iff₀ (by positivity)]
    have h2 := mul_le_mul_of_nonneg_left hCS (by positivity : (0 : ℝ) ≤ L ^ 2)
    nlinarith
  calc Real.exp (-2) * K * (M ^ 2 / (L ^ 2 * (d + 1)))
      ≤ Real.exp (-2) * K * ∑ k, ‖Q.eval (v k)‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hM2 (by positivity)
    _ = ∑ k, Real.exp (-2) * K * ‖Q.eval (v k)‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ _ := Finset.sum_le_sum fun k _ => hblock k

/-! ## The window theorem -/

/-- **Riemann–von Mangoldt windows at small heat time.**  For every `d` there are `c > 0` and
`a₁ ∈ (0, 1]` such that for `0 < a < a₁` there are `d + 1` sets of zero copies whose scaled real parts
`σ_q = a Re w_q` lie in `[0, 2]`, are pairwise `1/(2d+2)`-separated across sets, and each set has at
least `c a^{-1/2} log(a^{-1/2})` elements. -/
theorem exists_heat_windows (d : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∃ a₁ : ℝ, 0 < a₁ ∧ a₁ ≤ 1 ∧ ∀ a : ℝ, 0 < a → a < a₁ →
      ∃ A : Fin (d + 1) → Finset XiZeroCopy,
        (∀ k, ∀ q ∈ A k, 0 ≤ a * (xiHeatFrequency q).re ∧ a * (xiHeatFrequency q).re ≤ 2) ∧
        (∀ k k', k ≠ k' → ∀ q ∈ A k, ∀ q' ∈ A k',
          1 / (2 * (d : ℝ) + 2) ≤ |a * (xiHeatFrequency q).re - a * (xiHeatFrequency q').re|) ∧
        (∀ k, c * (Real.sqrt (1 / a) * Real.log (Real.sqrt (1 / a))) ≤ ((A k).card : ℝ)) := by
  classical
  obtain ⟨h, hh⟩ : ∃ h : ℝ, h = 1 / (2 * (d : ℝ) + 2) := ⟨_, rfl⟩
  have hh0 : 0 < h := by rw [hh]; positivity
  have hk_le : ∀ k : Fin (d + 1), (k : ℝ) ≤ d := fun k => by
    exact_mod_cast Nat.lt_succ_iff.1 k.2
  have hk2 : ∀ k : Fin (d + 1), (2 * (k : ℝ) + 1) * h ≤ 1 := fun k => by
    rw [hh, mul_one_div, div_le_one (by positivity)]; linarith [hk_le k]
  have hh1 : h ≤ 1 := by have := hk2 0; simp at this; linarith
  obtain ⟨x, hx⟩ : ∃ x : Fin (d + 1) → ℝ, ∀ k, x k = 1 + 2 * (k : ℝ) * h := ⟨_, fun _ => rfl⟩
  have hx1 : ∀ k, 1 ≤ x k := fun k => by
    rw [hx]; have : 0 ≤ (k : ℝ) := Nat.cast_nonneg _; nlinarith
  have hy2 : ∀ k, x k + h ≤ 2 := fun k => by rw [hx]; linarith [hk2 k]
  have hsepx : ∀ k k' : Fin (d + 1), (k : ℕ) < k' → x k + h + h ≤ x k' := fun k k' hkk => by
    rw [hx, hx]
    have : (k : ℝ) + 1 ≤ (k' : ℝ) := by exact_mod_cast hkk
    nlinarith
  set r₀ : ℝ := 1 + h / 16 with hr₀
  have hr₀1 : 1 < r₀ := by rw [hr₀]; linarith
  obtain ⟨T₀, hT₀, hwin⟩ := exists_card_xiCopiesWindow_ge hr₀1
  have hT₀0 : 0 < T₀ := by linarith
  set c : ℝ := (1 - 1 / r₀) / (4 * Real.pi) with hc
  have hc0 : 0 < c := by
    have : 1 / r₀ < 1 := by rw [div_lt_one (by linarith)]; exact hr₀1
    rw [hc]; exact div_pos (by linarith) (by positivity)
  refine ⟨c, hc0, min h (1 / T₀ ^ 2), lt_min hh0 (by positivity), (min_le_left _ _).trans hh1,
    fun a ha haa => ?_⟩
  have hah : a ≤ h := (haa.trans_le (min_le_left _ _)).le
  have ha1 : a ≤ 1 := hah.trans hh1
  have hT₀a : T₀ ^ 2 ≤ 1 / a := by
    have := (haa.trans_le (min_le_right _ _)).le
    rw [le_div_iff₀ (by positivity)] at this
    rw [le_div_iff₀ ha]
    linarith
  have hsa : T₀ ≤ Real.sqrt (1 / a) := by
    calc T₀ = Real.sqrt (T₀ ^ 2) := (Real.sqrt_sq hT₀0.le).symm
      _ ≤ Real.sqrt (1 / a) := Real.sqrt_le_sqrt hT₀a
  refine ⟨fun k => xiCopiesWindow (Real.sqrt (x k / a + 1 / 4)) (Real.sqrt ((x k + h) / a)),
    ?_, ?_, ?_⟩
  · intro k q hq
    have := scaled_re_mem_of_mem_window ha (by linarith [hx1 k]) hq
    exact ⟨by linarith [hx1 k], by linarith [hy2 k]⟩
  · intro k k' hkk q hq q' hq'
    have h1 := scaled_re_mem_of_mem_window ha (by linarith [hx1 k]) hq
    have h2 := scaled_re_mem_of_mem_window ha (by linarith [hx1 k']) hq'
    rw [← hh]
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hkk) with hl | hl
    · have := hsepx k k' hl
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      linarith
    · have := hsepx k' k hl
      rw [abs_of_nonneg (by linarith)]
      linarith
  · intro k
    have hxk := hx1 k
    have hxk2 := hy2 k
    have hT₁ : T₀ ≤ Real.sqrt (x k / a + 1 / 4) := by
      refine hsa.trans (Real.sqrt_le_sqrt ?_)
      have : 1 / a ≤ x k / a := div_le_div_of_nonneg_right hxk ha.le
      linarith
    have hratio : r₀ * Real.sqrt (x k / a + 1 / 4) ≤ Real.sqrt ((x k + h) / a) := by
      have hx0 : 0 ≤ x k / a + 1 / 4 := by positivity
      rw [show r₀ * Real.sqrt (x k / a + 1 / 4) = Real.sqrt (r₀ ^ 2 * (x k / a + 1 / 4)) by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by linarith)]]
      refine Real.sqrt_le_sqrt ?_
      have hr2 : r₀ ^ 2 ≤ 1 + h / 4 := by rw [hr₀]; nlinarith
      have key : (1 + h / 4) * (x k / a + 1 / 4) ≤ (x k + h) / a := by
        rw [le_div_iff₀ ha]
        have e : (1 + h / 4) * (x k / a + 1 / 4) * a = (1 + h / 4) * (x k + a / 4) := by
          field_simp
        rw [e]
        nlinarith [mul_nonneg hh0.le (by linarith : (0 : ℝ) ≤ 2 - x k),
          mul_nonneg hh0.le (by linarith : (0 : ℝ) ≤ 1 - a)]
      calc r₀ ^ 2 * (x k / a + 1 / 4) ≤ (1 + h / 4) * (x k / a + 1 / 4) :=
            mul_le_mul_of_nonneg_right hr2 hx0
        _ ≤ (x k + h) / a := key
    have hcnt := hwin _ _ hT₁ hratio
    have hT₂ : Real.sqrt (1 / a) ≤ Real.sqrt ((x k + h) / a) :=
      Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (by linarith) ha.le)
    have hl0 : 0 ≤ Real.log (Real.sqrt (1 / a)) := Real.log_nonneg (by linarith)
    have hmono : Real.sqrt (1 / a) * Real.log (Real.sqrt (1 / a)) ≤
        Real.sqrt ((x k + h) / a) * Real.log (Real.sqrt ((x k + h) / a)) :=
      mul_le_mul hT₂ (Real.log_le_log (by linarith) hT₂) hl0 (by linarith)
    exact (mul_le_mul_of_nonneg_left hmono hc0.le).trans hcnt

/-- **The small-time window.**  For every degree `d` there is `a₀ > 0` such that for every heat time
`0 < a < a₀` the heat Hankel form is positive on all nonzero polynomials of degree `≤ d`. -/
theorem exists_heatHankel_pos_of_natDegree_le (d : ℕ) :
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a : ℝ, 0 < a → a < a₀ → ∀ P : ℂ[X], P ≠ 0 → P.natDegree ≤ d →
      0 < (heatHankel a P P).re := by
  classical
  obtain ⟨c, hc, a₁, ha₁, ha₁1, hwin⟩ := exists_heat_windows d
  obtain ⟨h, hh⟩ : ∃ h : ℝ, h = 1 / (2 * (d : ℝ) + 2) := ⟨_, rfl⟩
  have hh0 : 0 < h := by rw [hh]; positivity
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = ((1 + 2) / h) ^ d := ⟨_, rfl⟩
  have hL0 : 0 < L := by rw [hL]; positivity
  have hE0 := heatWindowErrorConst_nonneg d
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = heatWindowErrorConst d := ⟨_, rfl⟩
  rw [← hE] at hE0
  have hd1 : (0 : ℝ) < d + 1 := by positivity
  have hLd : 0 < L ^ 2 * (d + 1) := by positivity
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, Λ = (E + 1) * Real.exp 2 * (L ^ 2 * (d + 1)) / c := ⟨_, rfl⟩
  refine ⟨min a₁ (Real.exp (-(2 * Λ))), lt_min ha₁ (Real.exp_pos _),
    fun a ha haa P hP hPd => ?_⟩
  have haa₁ : a < a₁ := haa.trans_le (min_le_left _ _)
  have ha1 : a ≤ 1 := haa₁.le.trans ha₁1
  have haΛ : a < Real.exp (-(2 * Λ)) := haa.trans_le (min_le_right _ _)
  obtain ⟨A, hσ, hsep, hcard⟩ := hwin a ha haa₁
  -- the logarithmic gain
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hs : Real.sqrt (1 / a) = 1 / Real.sqrt a := by
    rw [Real.sqrt_div' 1 ha.le, Real.sqrt_one]
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = Real.log (Real.sqrt (1 / a)) := ⟨_, rfl⟩
  have hℓΛ : Λ < ℓ := by
    have hla : Real.log a < -(2 * Λ) := by
      calc Real.log a < Real.log (Real.exp (-(2 * Λ))) := Real.log_lt_log ha haΛ
        _ = -(2 * Λ) := Real.log_exp _
    rw [hℓ, Real.log_sqrt (by positivity), one_div, Real.log_inv]
    linarith
  have hΛ0 : 0 < Λ := by rw [hΛ]; positivity
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = c * (Real.sqrt (1 / a) * ℓ) := ⟨_, rfl⟩
  have hK0 : 0 < K := by rw [hK, hs]; have : 0 < ℓ := hΛ0.trans hℓΛ; positivity
  -- the windowed lower bound
  have hdisj : (↑(Finset.univ : Finset (Fin (d + 1))) : Set (Fin (d + 1))).PairwiseDisjoint A := by
    intro k _ k' _ hkk
    refine Finset.disjoint_left.2 fun q hq hq' => ?_
    have := hsep k k' hkk q hq q hq'
    rw [sub_self, abs_zero] at this
    have : 0 < 1 / (2 * (d : ℝ) + 2) := by positivity
    linarith
  have hlow := heatHankel_re_ge_window ha ha1 hPd ((Finset.univ : Finset (Fin (d + 1))).biUnion A)
  rw [Finset.sum_biUnion hdisj, ← hE] at hlow
  set Q := heatRescale a P with hQ
  have hM : 0 < coeffMass Q := coeffMass_pos_of_ne_zero (heatRescale_ne_zero ha hP)
  have hmain : Real.exp (-2) * K * (coeffMass Q ^ 2 / ((((1 + 2) / (1 / (2 * (d : ℝ) + 2))) ^ d) ^ 2 *
      (d + 1))) ≤ ∑ k, ∑ q ∈ A k, Real.exp (-(a * (xiHeatFrequency q).re)) *
        ‖Q.eval ((a * (xiHeatFrequency q).re : ℝ) : ℂ)‖ ^ 2 :=
    sum_window_main_ge (by positivity) A (fun q => a * (xiHeatFrequency q).re) hσ hsep hK0
      (fun k => hK ▸ hℓ ▸ hcard k) Q (natDegree_heatRescale_le ha hPd)
  rw [← hh, ← hL] at hmain
  -- the gap
  have key : E < Real.exp (-2) * c * ℓ / (L ^ 2 * (d + 1)) := by
    rw [lt_div_iff₀ hLd]
    have h1 : (E + 1) * Real.exp 2 * (L ^ 2 * (d + 1)) < c * ℓ := by
      have := hℓΛ
      rw [hΛ, div_lt_iff₀ hc] at this
      linarith
    have he : Real.exp (-2) * Real.exp 2 = 1 := by rw [← Real.exp_add]; norm_num
    have h3 : Real.exp (-2) * ((E + 1) * Real.exp 2 * (L ^ 2 * (d + 1))) =
        (E + 1) * (L ^ 2 * (d + 1)) := by
      calc _ = (E + 1) * (L ^ 2 * (d + 1)) * (Real.exp (-2) * Real.exp 2) := by ring
        _ = _ := by rw [he, mul_one]
    calc E * (L ^ 2 * (d + 1)) < (E + 1) * (L ^ 2 * (d + 1)) :=
          mul_lt_mul_of_pos_right (by linarith) hLd
      _ = Real.exp (-2) * ((E + 1) * Real.exp 2 * (L ^ 2 * (d + 1))) := h3.symm
      _ < Real.exp (-2) * (c * ℓ) := mul_lt_mul_of_pos_left h1 (Real.exp_pos _)
      _ = Real.exp (-2) * c * ℓ := by ring
  have hgap : coeffMass Q ^ 2 * (E / Real.sqrt a) <
      Real.exp (-2) * K * (coeffMass Q ^ 2 / (L ^ 2 * (d + 1))) := by
    have e1 : Real.exp (-2) * K * (coeffMass Q ^ 2 / (L ^ 2 * (d + 1))) =
        coeffMass Q ^ 2 / Real.sqrt a * (Real.exp (-2) * c * ℓ / (L ^ 2 * (d + 1))) := by
      rw [hK, hs]; field_simp
    have e2 : coeffMass Q ^ 2 * (E / Real.sqrt a) = coeffMass Q ^ 2 / Real.sqrt a * E := by ring
    rw [e1, e2]
    exact mul_lt_mul_of_pos_left key (by positivity)
  linarith

end

end RHTower
