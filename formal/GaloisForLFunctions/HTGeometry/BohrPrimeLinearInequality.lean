import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Algebra.BigOperators.Associated

/-!
# Bohr's inequality for the prime part of a bounded Dirichlet series

**Theorem** (`sum_norm_prime_coeff_le`).  Let `B` be holomorphic on a neighbourhood of the closed
strip `σ ≤ Re s ≤ σ'`, bounded there by `M`, and equal on `Re s = σ'` to an absolutely convergent
Dirichlet series `Σ b(n) n^{−s}`.  Then for every finite set `P` of primes

`Σ_{p ∈ P} |b(p)| p^{−σ} ≤ 2M`.

So the prime coefficients of a bounded Dirichlet series are absolutely summable on every line of
boundedness.  This is Bohr's inequality for the linear part, with constant `2` in place of `1`.

**Proof.**
1. *Mean values move across the strip.*  For real `μ`, the window mean
   `T⁻¹∫_0^T B(σ+it) e^{iμt} dt` tends to `e^{−μσ} Σ_{log n = μ} b(n) n^{−σ'} e^{μσ'}`.
   The rectangle `[σ, σ'] × [0, T]` for `B(s) e^{μs}` contributes only horizontal sides of size
   `O(1)`.  On `Re s = σ'` the series converges absolutely, so the mean is taken termwise
   (`tendsto_windowMean_line`).
2. *A nonnegative Riesz kernel.*  `K_ψ(t) = ∏_{p∈P} (1 + cos(t log p + ψ_p)) ≥ 0` expands over
   `m ∈ {−1,0,1}^P` with frequencies `Σ m_p log p`.  Since the `log p` are linearly independent,
   its mean is `1`, so `|mean(B K_ψ)| ≤ M`.
3. *Extraction.*  Average over `ψ = θ + 2πk/K`, `k < K`, `K = |P| + 2`, against `e^{−2πik/K}`.  This
   keeps the vectors with `Σ m_p = 1`.  Among them only `m = e_p` has `Π p^{m_p} ∈ ℕ`, so the result
   is `½ Σ_p e^{iθ_p} b(p) p^{−σ}`.  Choosing `θ_p = −arg b(p)` gives the bound.
-/

open Complex Filter Topology Set MeasureTheory

noncomputable section

namespace GaloisForLFunctions.BohrPrime

/-- The window mean `T⁻¹ ∫_0^T f`. -/
def windowMean (f : ℝ → ℂ) (T : ℝ) : ℂ := (T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T, f t

theorem windowMean_exp (μ : ℝ) :
    Tendsto (windowMean fun t => cexp ((μ : ℂ) * I * t)) atTop
      (𝓝 (if μ = 0 then 1 else 0)) := by
  split_ifs with hμ
  · subst hμ
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    simp only [windowMean, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
      intervalIntegral.integral_const, sub_zero, Complex.real_smul, mul_one]
    exact (inv_mul_cancel₀ (by exact_mod_cast hT.ne')).symm
  · have hc : (μ : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hμ) I_ne_zero
    have hbound : ∀ T : ℝ, ‖∫ t in (0 : ℝ)..T, cexp ((μ : ℂ) * I * t)‖ ≤ 2 / |μ| := by
      intro T
      rw [integral_exp_mul_complex hc, norm_div, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs]
      refine div_le_div_of_nonneg_right ?_ (abs_nonneg μ)
      refine (norm_sub_le _ _).trans ?_
      rw [show (μ : ℂ) * I * (T : ℂ) = ((μ * T : ℝ) : ℂ) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, show (μ : ℂ) * I * ((0 : ℝ) : ℂ) = 0 by simp,
        Complex.exp_zero, norm_one]
      norm_num
    have hinv : Tendsto (fun T : ℝ => ‖((T : ℂ))⁻¹‖ * (2 / |μ|)) atTop (𝓝 0) := by
      have h := (tendsto_inv_atTop_zero (𝕜 := ℝ)).mul_const (2 / |μ|)
      rw [zero_mul] at h
      refine h.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
    refine squeeze_zero_norm' ?_ hinv
    filter_upwards with T
    rw [windowMean, norm_mul]
    exact mul_le_mul_of_nonneg_left (hbound T) (norm_nonneg _)

/-- A vertical translate of a Dirichlet term. -/
theorem term_line (b : ℕ → ℂ) (σ t : ℝ) (n : ℕ) :
    LSeries.term b ((σ : ℂ) + (t : ℂ) * I) n =
      LSeries.term b (σ : ℂ) n * cexp (((-Real.log n : ℝ) : ℂ) * I * t) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, Complex.cpow_add _ _
      (by exact_mod_cast hn), div_eq_mul_inv, div_eq_mul_inv, mul_inv, ← mul_assoc]
    congr 1
    rw [← Complex.cpow_neg, show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl,
      Complex.cpow_def_of_ne_zero (by exact_mod_cast hn0.ne'), ← Complex.ofReal_log hn0.le]
    congr 1
    push_cast
    ring

/-- **Mean values on a line of absolute convergence.**  The window mean of
`L(σ+it) e^{iμt}` tends to `Σ_n term(σ, n)·[log n = μ]`. -/
theorem tendsto_windowMean_line {b : ℕ → ℂ} {σ : ℝ} (hb : LSeriesSummable b (σ : ℂ)) (μ : ℝ) :
    Tendsto (windowMean fun t => LSeries b ((σ : ℂ) + (t : ℂ) * I) * cexp ((μ : ℂ) * I * t))
      atTop (𝓝 (∑' n : ℕ, LSeries.term b (σ : ℂ) n *
        (if μ - Real.log n = 0 then 1 else 0))) := by
  set a : ℕ → ℂ := fun n => LSeries.term b (σ : ℂ) n with ha
  have hsum : Summable fun n => ‖a n‖ := hb.norm
  have hpt : ∀ t : ℝ, LSeries b ((σ : ℂ) + (t : ℂ) * I) * cexp ((μ : ℂ) * I * t) =
      ∑' n, a n * cexp (((μ - Real.log n : ℝ) : ℂ) * I * t) := by
    intro t
    rw [LSeries, ← tsum_mul_right]
    refine tsum_congr fun n => ?_
    rw [term_line, mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hint : ∀ T : ℝ, 0 ≤ T → ∫ t in (0 : ℝ)..T,
      LSeries b ((σ : ℂ) + (t : ℂ) * I) * cexp ((μ : ℂ) * I * t) =
      ∑' n, a n * ∫ t in (0 : ℝ)..T, cexp (((μ - Real.log n : ℝ) : ℂ) * I * t) := by
    intro T hT
    have h := intervalIntegral.hasSum_integral_of_dominated_convergence (a := 0) (b := T)
      (μ := volume) (f := fun t => LSeries b ((σ : ℂ) + (t : ℂ) * I) * cexp ((μ : ℂ) * I * t))
      (F := fun n t => a n * cexp (((μ - Real.log n : ℝ) : ℂ) * I * t))
      (fun n _ => ‖a n‖) (fun n => by fun_prop)
      (fun n => Eventually.of_forall fun t _ => by
        rw [norm_mul, show (((μ - Real.log n : ℝ) : ℂ) * I * t) =
          ((((μ - Real.log n) * t : ℝ)) : ℂ) * I by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I, mul_one])
      (Eventually.of_forall fun _ _ => hsum) intervalIntegrable_const
      (Eventually.of_forall fun t _ => by
        rw [hpt t]
        exact (hsum.of_norm_bounded (fun n => by
          rw [norm_mul, show (((μ - Real.log n : ℝ) : ℂ) * I * t) =
            ((((μ - Real.log n) * t : ℝ)) : ℂ) * I by push_cast; ring,
            Complex.norm_exp_ofReal_mul_I, mul_one])).hasSum)
    rw [← h.tsum_eq]
    exact tsum_congr fun n => intervalIntegral.integral_const_mul _ _
  have hmean : ∀ᶠ T in atTop, windowMean (fun t => LSeries b ((σ : ℂ) + (t : ℂ) * I) *
      cexp ((μ : ℂ) * I * t)) T =
      ∑' n, a n * windowMean (fun t => cexp (((μ - Real.log n : ℝ) : ℂ) * I * t)) T := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    rw [windowMean, hint T hT, ← tsum_mul_left]
    exact tsum_congr fun n => by rw [windowMean]; ring
  refine (tendsto_tsum_of_dominated_convergence hsum (fun n => ?_) ?_).congr' (EventuallyEq.symm
    hmean)
  · exact (windowMean_exp (μ - Real.log n)).const_mul (a n)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT n
    rw [norm_mul]
    refine mul_le_of_le_one_right (norm_nonneg _) ?_
    rw [windowMean, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
    have hle := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := T) (C := 1)
      (f := fun t : ℝ => cexp (((μ - Real.log n : ℝ) : ℂ) * I * t)) fun t _ => le_of_eq (by
        rw [show (((μ - Real.log n : ℝ) : ℂ) * I * t) =
          ((((μ - Real.log n) * t : ℝ)) : ℂ) * I by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I])
    rw [sub_zero, abs_of_pos hT, one_mul] at hle
    rw [inv_mul_le_iff₀ hT, mul_one]
    exact hle

/-- **Mean values cross a strip of boundedness.**  If `H` is holomorphic on the closed strip
`σ ≤ Re s ≤ σ'` and bounded by `C` there, the window means of `H` on the two edges have the same
limit behaviour. -/
theorem tendsto_windowMean_sub {H : ℂ → ℂ} {σ σ' C : ℝ} (hσ : σ ≤ σ')
    (hH : DifferentiableOn ℂ H {z : ℂ | σ ≤ z.re ∧ z.re ≤ σ'})
    (hC : ∀ z : ℂ, σ ≤ z.re → z.re ≤ σ' → ‖H z‖ ≤ C) :
    Tendsto (fun T : ℝ => windowMean (fun t => H ((σ : ℂ) + (t : ℂ) * I)) T -
      windowMean (fun t => H ((σ' : ℂ) + (t : ℂ) * I)) T) atTop (𝓝 0) := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC σ (by simp) (by simpa using hσ))
  have hrect : ∀ T : ℝ, 0 ≤ T → ‖(∫ t in (0 : ℝ)..T, H ((σ : ℂ) + (t : ℂ) * I)) -
      ∫ t in (0 : ℝ)..T, H ((σ' : ℂ) + (t : ℂ) * I)‖ ≤ 2 * (C * (σ' - σ)) := by
    intro T hT
    have hd : DifferentiableOn ℂ H (uIcc ((σ : ℂ) + (0 : ℝ) * I).re
        ((σ' : ℂ) + (T : ℂ) * I).re ×ℂ uIcc ((σ : ℂ) + (0 : ℝ) * I).im
        ((σ' : ℂ) + (T : ℂ) * I).im) := by
      refine hH.mono fun z hz => ?_
      rw [Complex.mem_reProdIm] at hz
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        add_zero] at hz
      rw [uIcc_of_le hσ] at hz
      exact ⟨hz.1.1, hz.1.2⟩
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn H _ _ hd
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, add_im, mul_im, zero_add, ofReal_zero, zero_mul] at h
    have hside : ∀ y : ℝ, ‖∫ x in σ..σ', H ((x : ℂ) + (y : ℂ) * I)‖ ≤ C * (σ' - σ) := by
      intro y
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := σ) (b := σ') (C := C)
        (f := fun x : ℝ => H ((x : ℂ) + (y : ℂ) * I)) fun x hx => by
          rw [uIoc_of_le hσ] at hx
          exact hC _ (by simpa using hx.1.le) (by simpa using hx.2)
      rwa [abs_of_nonneg (by linarith)] at this
    have hk : (∫ t in (0 : ℝ)..T, H ((σ : ℂ) + (t : ℂ) * I)) -
        ∫ t in (0 : ℝ)..T, H ((σ' : ℂ) + (t : ℂ) * I) =
        -I * ((∫ x in σ..σ', H ((x : ℂ) + ((0 : ℝ) : ℂ) * I)) -
          ∫ x in σ..σ', H ((x : ℂ) + (T : ℂ) * I)) := by
      simp only [smul_eq_mul] at h
      have h' := h
      simp only [ofReal_zero, zero_mul, add_zero] at h' ⊢
      linear_combination I * h' + ((∫ t in (0 : ℝ)..T, H ((σ : ℂ) + (t : ℂ) * I)) -
        ∫ t in (0 : ℝ)..T, H ((σ' : ℂ) + (t : ℂ) * I)) * Complex.I_sq
    rw [hk, norm_mul, norm_neg, Complex.norm_I, one_mul]
    calc _ ≤ ‖∫ x in σ..σ', H ((x : ℂ) + ((0 : ℝ) : ℂ) * I)‖ +
          ‖∫ x in σ..σ', H ((x : ℂ) + (T : ℂ) * I)‖ := norm_sub_le _ _
      _ ≤ C * (σ' - σ) + C * (σ' - σ) := add_le_add (hside 0) (hside T)
      _ = 2 * (C * (σ' - σ)) := by ring
  have hinv : Tendsto (fun T : ℝ => ‖((T : ℂ))⁻¹‖ * (2 * (C * (σ' - σ)))) atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero (𝕜 := ℝ)).mul_const (2 * (C * (σ' - σ)))
    rw [zero_mul] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
  refine squeeze_zero_norm' ?_ hinv
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  rw [windowMean, windowMean, ← mul_sub, norm_mul]
  exact mul_le_mul_of_nonneg_left (hrect T hT) (norm_nonneg _)

/-- **Mean values on a line of boundedness.**  If `B` is holomorphic and bounded by `M` on the
closed strip `σ ≤ Re s ≤ σ'` and equals `Σ b(n) n^{−s}` (absolutely convergent) on `Re s = σ'`,
then the window mean of `B(σ+it) e^{iμt}` tends to
`e^{−μσ} e^{μσ'} Σ_n term(σ', n)·[log n = μ]`. -/
theorem tendsto_windowMean_strip {B : ℂ → ℂ} {b : ℕ → ℂ} {σ σ' M : ℝ} (hσ : σ ≤ σ')
    (hB : DifferentiableOn ℂ B {z : ℂ | σ ≤ z.re ∧ z.re ≤ σ'})
    (hM : ∀ z : ℂ, σ ≤ z.re → z.re ≤ σ' → ‖B z‖ ≤ M)
    (hbs : LSeriesSummable b (σ' : ℂ))
    (hBL : ∀ t : ℝ, B ((σ' : ℂ) + (t : ℂ) * I) = LSeries b ((σ' : ℂ) + (t : ℂ) * I)) (μ : ℝ) :
    Tendsto (windowMean fun t => B ((σ : ℂ) + (t : ℂ) * I) * cexp ((μ : ℂ) * I * t)) atTop
      (𝓝 (cexp (-((μ * σ : ℝ) : ℂ)) * (cexp ((μ * σ' : ℝ) : ℂ) *
        ∑' n : ℕ, LSeries.term b (σ' : ℂ) n * (if μ - Real.log n = 0 then 1 else 0)))) := by
  set H : ℂ → ℂ := fun z => B z * cexp ((μ : ℂ) * z) with hH
  have hHd : DifferentiableOn ℂ H {z : ℂ | σ ≤ z.re ∧ z.re ≤ σ'} :=
    hB.mul (fun z _ => ((differentiableAt_id.const_mul _).cexp).differentiableWithinAt)
  set E : ℝ := Real.exp (|μ| * (|σ| + |σ'|)) with hE
  have hHM : ∀ z : ℂ, σ ≤ z.re → z.re ≤ σ' → ‖H z‖ ≤ M * E := by
    intro z h1 h2
    rw [hH]
    simp only
    rw [norm_mul, Complex.norm_exp]
    refine mul_le_mul (hM z h1 h2) (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le
      ((norm_nonneg _).trans (hM z h1 h2))
    have : ((μ : ℂ) * z).re = μ * z.re := by simp
    rw [this]
    have hz : |z.re| ≤ |σ| + |σ'| := by
      rcases le_total 0 z.re with h | h
      · rw [abs_of_nonneg h]; linarith [le_abs_self σ', abs_nonneg σ]
      · rw [abs_of_nonpos h]; linarith [neg_abs_le σ, abs_nonneg σ']
    calc μ * z.re ≤ |μ * z.re| := le_abs_self _
      _ = |μ| * |z.re| := abs_mul _ _
      _ ≤ |μ| * (|σ| + |σ'|) := mul_le_mul_of_nonneg_left hz (abs_nonneg _)
  have hline : ∀ (c : ℝ) (g : ℝ → ℂ), (∀ t : ℝ, H ((c : ℂ) + (t : ℂ) * I) =
      cexp ((μ * c : ℝ) : ℂ) * g t) → ∀ T : ℝ,
      windowMean (fun t => H ((c : ℂ) + (t : ℂ) * I)) T = cexp ((μ * c : ℝ) : ℂ) *
        windowMean g T := by
    intro c g hg T
    simp only [windowMean, hg, intervalIntegral.integral_const_mul]
    ring
  have hHσ : ∀ t : ℝ, H ((σ : ℂ) + (t : ℂ) * I) = cexp ((μ * σ : ℝ) : ℂ) *
      (B ((σ : ℂ) + (t : ℂ) * I) * cexp ((μ : ℂ) * I * t)) := by
    intro t
    rw [hH]
    simp only
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hHσ' : ∀ t : ℝ, H ((σ' : ℂ) + (t : ℂ) * I) = cexp ((μ * σ' : ℝ) : ℂ) *
      (LSeries b ((σ' : ℂ) + (t : ℂ) * I) * cexp ((μ : ℂ) * I * t)) := by
    intro t
    rw [hH]
    simp only
    rw [hBL t, mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hsub := tendsto_windowMean_sub hσ hHd hHM
  have hright := (tendsto_windowMean_line hbs μ).const_mul (cexp ((μ * σ' : ℝ) : ℂ))
  have hleft : Tendsto (windowMean fun t => H ((σ : ℂ) + (t : ℂ) * I)) atTop
      (𝓝 (cexp ((μ * σ' : ℝ) : ℂ) * ∑' n : ℕ, LSeries.term b (σ' : ℂ) n *
        (if μ - Real.log n = 0 then 1 else 0))) := by
    have h := hsub.add (hright.congr fun T => (hline σ' _ hHσ' T).symm)
    rw [zero_add] at h
    exact h.congr fun T => by ring
  have hfin := hleft.const_mul (cexp (-((μ * σ : ℝ) : ℂ)))
  refine hfin.congr fun T => ?_
  rw [hline σ _ hHσ T, ← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]

/-- The coefficient extracted by the mean value at frequency `log p`. -/
theorem tsum_term_indicator_log {b : ℕ → ℂ} {s : ℂ} {p : ℕ} (hp : 0 < p) :
    ∑' n : ℕ, LSeries.term b s n * (if Real.log p - Real.log n = 0 then 1 else 0) =
      LSeries.term b s p := by
  rw [tsum_eq_single p]
  · simp
  · intro n hn
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    · have hne : Real.log p - Real.log n ≠ 0 := by
        intro h
        have h' : Real.log p = Real.log n := by linarith
        have := Real.log_injOn_pos (Set.mem_Ioi.mpr (by exact_mod_cast hp))
          (Set.mem_Ioi.mpr (by exact_mod_cast Nat.pos_of_ne_zero hn0)) h'
        exact hn (by exact_mod_cast this.symm)
      simp [hne]

/-- A frequency carrying no integer contributes nothing. -/
theorem tsum_term_indicator_eq_zero {b : ℕ → ℂ} {s : ℂ} {μ : ℝ}
    (hμ : ∀ n : ℕ, 0 < n → Real.log n ≠ μ) :
    ∑' n : ℕ, LSeries.term b s n * (if μ - Real.log n = 0 then 1 else 0) = 0 := by
  refine (tsum_congr fun n => ?_).trans tsum_zero
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have : μ - Real.log n ≠ 0 := fun h => hμ n (Nat.pos_of_ne_zero hn) (by linarith)
    simp [this]

/-! ## Signed prime products -/

/-- A `{−1, 0, 1}`-vector on a set of primes whose signed product of primes is a positive integer
has no `−1` entry. -/
theorem nonneg_of_log_eq {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {m : P → ℤ}
    (hm : ∀ i, m i = -1 ∨ m i = 0 ∨ m i = 1) {n : ℕ} (hn : 0 < n)
    (hlog : Real.log n = ∑ i : P, (m i : ℝ) * Real.log (i : ℕ)) : ∀ i, 0 ≤ m i := by
  classical
  set A : ℕ := ∏ i ∈ Finset.univ.filter (fun i : P => m i = 1), (i : ℕ) with hA
  set D : ℕ := ∏ i ∈ Finset.univ.filter (fun i : P => m i = -1), (i : ℕ) with hD
  have hpos : ∀ i : P, (0 : ℝ) < (i : ℕ) := fun i => by exact_mod_cast (hP _ i.2).pos
  have hsplit : ∑ i : P, (m i : ℝ) * Real.log (i : ℕ) =
      Real.log A - Real.log D := by
    rw [hA, hD, Nat.cast_prod, Nat.cast_prod, Real.log_prod (fun i _ => (hpos i).ne'),
      Real.log_prod (fun i _ => (hpos i).ne'), Finset.sum_filter, Finset.sum_filter,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases hm i with h | h | h <;> simp [h]
  have hDpos : (0 : ℝ) < D := by
    rw [hD, Nat.cast_prod]; exact Finset.prod_pos fun i _ => hpos i
  have hApos : (0 : ℝ) < A := by
    rw [hA, Nat.cast_prod]; exact Finset.prod_pos fun i _ => hpos i
  have heq : (n : ℝ) * D = A := by
    have h1 : Real.log ((n : ℝ) * D) = Real.log A := by
      rw [Real.log_mul (by exact_mod_cast hn.ne') hDpos.ne', hlog, hsplit]; ring
    exact Real.log_injOn_pos (Set.mem_Ioi.mpr (mul_pos (by exact_mod_cast hn) hDpos))
      (Set.mem_Ioi.mpr hApos) h1
  have heqN : n * D = A := by exact_mod_cast heq
  intro i₀
  by_contra hneg
  have hi₀ : m i₀ = -1 := by
    rcases hm i₀ with h | h | h
    · exact h
    · omega
    · omega
  have hdvdD : (i₀ : ℕ) ∣ D := Finset.dvd_prod_of_mem _ (by simp [hi₀])
  have hdvdA : (i₀ : ℕ) ∣ A := heqN ▸ dvd_mul_of_dvd_right hdvdD n
  obtain ⟨j, hj, hdj⟩ := (Prime.dvd_finsetProd_iff (hP _ i₀.2).prime _).mp hdvdA
  have hji : (i₀ : ℕ) = (j : ℕ) := (Nat.prime_dvd_prime_iff_eq (hP _ i₀.2) (hP _ j.2)).mp hdj
  have : i₀ = j := Subtype.ext hji
  rw [Finset.mem_filter] at hj
  rw [← this] at hj
  rw [hi₀] at hj
  exact absurd hj.2 (by norm_num)

/-- A nonnegative `{0,1}`-valued vector with coordinate sum `1` is a unit vector. -/
theorem exists_eq_single_of_sum_eq_one {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ι → ℤ}
    (hm : ∀ i, m i = -1 ∨ m i = 0 ∨ m i = 1) (hnn : ∀ i, 0 ≤ m i) (hsum : ∑ i, m i = 1) :
    ∃ i, m = Pi.single i 1 := by
  by_contra hno
  push Not at hno
  have h01 : ∀ i, m i = 0 ∨ m i = 1 := fun i => by
    rcases hm i with h | h | h
    · have := hnn i; omega
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨i, hi⟩ : ∃ i, m i = 1 := by
    by_contra hall
    push Not at hall
    have : ∑ i, m i = 0 := Finset.sum_eq_zero fun i _ => (h01 i).resolve_right (hall i)
    omega
  obtain ⟨j, hj⟩ : ∃ j, m j ≠ (Pi.single i (1 : ℤ) : ι → ℤ) j := by
    by_contra hall
    push Not at hall
    exact hno i (funext hall)
  have hji : j ≠ i := by
    intro h; subst h; simp [hi] at hj
  have hmj : m j = 1 := by
    rw [Pi.single_eq_of_ne hji] at hj
    exact (h01 j).resolve_left hj
  have hge : m i + m j ≤ ∑ k, m k := by
    rw [← Finset.sum_pair hji.symm]
    exact Finset.sum_le_sum_of_subset_of_nonneg (by simp) fun k _ _ => hnn k
  omega

/-! ## The Riesz kernel -/

/-- The sign set `{−1, 0, 1}`. -/
def signSet : Finset ℤ := {-1, 0, 1}

/-- The weights of `1 + cos x = ½ e^{−ix} + 1 + ½ e^{ix}`. -/
def rieszWeight (a : ℤ) : ℂ := if a = 0 then 1 else 1 / 2

theorem one_add_cos_eq_sum (x : ℝ) :
    ((1 + Real.cos x : ℝ) : ℂ) = ∑ a ∈ signSet, rieszWeight a * cexp ((a : ℂ) * (x : ℂ) * I) := by
  simp only [signSet, rieszWeight]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  push_cast
  rw [Complex.cos]
  simp only [neg_mul, one_mul, zero_mul, Complex.exp_zero, mul_one]
  ring_nf

/-- The Riesz product `∏_{p ∈ P} (1 + cos(t log p + ψ_p)) ≥ 0`. -/
def rieszProductKernel {P : Finset ℕ} (ψ : P → ℝ) (t : ℝ) : ℝ :=
  ∏ i : P, (1 + Real.cos (t * Real.log (i : ℕ) + ψ i))

theorem rieszProductKernel_nonneg {P : Finset ℕ} (ψ : P → ℝ) (t : ℝ) : 0 ≤ rieszProductKernel ψ t :=
  Finset.prod_nonneg fun i _ => by linarith [Real.neg_one_le_cos (t * Real.log (i : ℕ) + ψ i)]

/-- The frequency `Σ m_p log p` of an exponent vector. -/
def primeFreq {P : Finset ℕ} (m : P → ℤ) : ℝ := ∑ i : P, (m i : ℝ) * Real.log (i : ℕ)

/-- The coefficient of the frequency `Σ m_p log p` in the Riesz kernel. -/
def rieszCoeff {P : Finset ℕ} (ψ : P → ℝ) (m : P → ℤ) : ℂ :=
  (∏ i : P, rieszWeight (m i)) * cexp (((∑ i : P, (m i : ℝ) * ψ i : ℝ) : ℂ) * I)

theorem rieszProductKernel_eq_sum {P : Finset ℕ} (ψ : P → ℝ) (t : ℝ) :
    ((rieszProductKernel ψ t : ℝ) : ℂ) = ∑ m ∈ Fintype.piFinset fun _ : P => signSet,
      rieszCoeff ψ m * cexp ((primeFreq m : ℂ) * I * t) := by
  classical
  rw [rieszProductKernel, Complex.ofReal_prod]
  simp_rw [one_add_cos_eq_sum]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [rieszCoeff, primeFreq, Finset.prod_mul_distrib, ← Complex.exp_sum, mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- The only exponent vector of frequency `0` is `0`. -/
theorem eq_zero_of_primeFreq_eq_zero {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {m : P → ℤ}
    (hm : ∀ i, m i = -1 ∨ m i = 0 ∨ m i = 1) (h0 : primeFreq m = 0) : m = 0 := by
  have hnn := nonneg_of_log_eq hP hm one_pos (by rw [Nat.cast_one, Real.log_one, ← h0]; rfl)
  have hlog : ∀ i : P, 0 < Real.log (i : ℕ) := fun i =>
    Real.log_pos (by exact_mod_cast (hP _ i.2).one_lt)
  have hterms : ∀ i ∈ (Finset.univ : Finset P), 0 ≤ (m i : ℝ) * Real.log (i : ℕ) :=
    fun i _ => mul_nonneg (by exact_mod_cast hnn i) (hlog i).le
  have hall := (Finset.sum_eq_zero_iff_of_nonneg hterms).mp h0
  funext i
  have := hall i (Finset.mem_univ _)
  rcases mul_eq_zero.mp this with h | h
  · exact_mod_cast h
  · exact absurd h (hlog i).ne'

theorem mem_signSet {a : ℤ} : a ∈ signSet ↔ a = -1 ∨ a = 0 ∨ a = 1 := by
  simp [signSet]

/-- **The Riesz contraction.**  For a function `B` as in `tendsto_windowMean_strip`, every phase
vector `ψ` gives `|Σ_m c_m(ψ) L_m| ≤ M`, where `L_m` is the mean value of `B(σ+it)e^{i primeFreq(m) t}`. -/
theorem norm_sum_rieszCoeff_le {B : ℂ → ℂ} {b : ℕ → ℂ} {σ σ' M : ℝ} (hσ : σ ≤ σ')
    (hB : DifferentiableOn ℂ B {z : ℂ | σ ≤ z.re ∧ z.re ≤ σ'})
    (hM : ∀ z : ℂ, σ ≤ z.re → z.re ≤ σ' → ‖B z‖ ≤ M)
    (hbs : LSeriesSummable b (σ' : ℂ))
    (hBL : ∀ t : ℝ, B ((σ' : ℂ) + (t : ℂ) * I) = LSeries b ((σ' : ℂ) + (t : ℂ) * I))
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (ψ : P → ℝ) :
    ‖∑ m ∈ Fintype.piFinset (fun _ : P => signSet), rieszCoeff ψ m *
      (cexp (-((primeFreq m * σ : ℝ) : ℂ)) * (cexp ((primeFreq m * σ' : ℝ) : ℂ) *
        ∑' n : ℕ, LSeries.term b (σ' : ℂ) n *
          (if primeFreq m - Real.log n = 0 then 1 else 0)))‖ ≤ M := by
  classical
  set box := Fintype.piFinset fun _ : P => signSet with hbox
  set g : ℝ → ℂ := fun t => B ((σ : ℂ) + (t : ℂ) * I) with hg
  have hline : ∀ t : ℝ, (σ : ℂ) + (t : ℂ) * I ∈ {z : ℂ | σ ≤ z.re ∧ z.re ≤ σ'} := fun t => by
    simp [hσ]
  have hgc : Continuous g :=
    hB.continuousOn.comp_continuous (by fun_prop) hline
  have hgM : ∀ t, ‖g t‖ ≤ M := fun t => hM _ (hline t).1 (hline t).2
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hgM 0)
  set K : ℝ → ℝ := rieszProductKernel ψ with hK
  have hKc : Continuous K := by
    rw [hK]; unfold rieszProductKernel; fun_prop
  have hexpand : ∀ T : ℝ, windowMean (fun t => g t * ((K t : ℝ) : ℂ)) T =
      ∑ m ∈ box, rieszCoeff ψ m * windowMean
        (fun t => g t * cexp ((primeFreq m : ℂ) * I * t)) T := by
    intro T
    have hpt : ∀ t : ℝ, g t * ((K t : ℝ) : ℂ) =
        ∑ m ∈ box, rieszCoeff ψ m * (g t * cexp ((primeFreq m : ℂ) * I * t)) := by
      intro t
      rw [hK, rieszProductKernel_eq_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by ring
    simp only [windowMean]
    rw [intervalIntegral.integral_congr fun t _ => hpt t, intervalIntegral.integral_finsetSum
      (f := fun m t => rieszCoeff ψ m * (g t * cexp ((primeFreq m : ℂ) * I * t)))
      (fun m _ => (continuous_const.mul (hgc.mul (by fun_prop))).intervalIntegrable _ _),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [intervalIntegral.integral_const_mul]
    ring
  have hexpandK : ∀ T : ℝ, windowMean (fun t => ((K t : ℝ) : ℂ)) T =
      ∑ m ∈ box, rieszCoeff ψ m * windowMean (fun t => cexp ((primeFreq m : ℂ) * I * t)) T := by
    intro T
    simp only [windowMean, hK, rieszProductKernel_eq_sum]
    rw [intervalIntegral.integral_finsetSum
      (f := fun m t => rieszCoeff ψ m * cexp ((primeFreq m : ℂ) * I * t))
      (fun m _ => (continuous_const.mul (by fun_prop)).intervalIntegrable _ _), Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [intervalIntegral.integral_const_mul]
    ring
  have hlimK : Tendsto (windowMean fun t => ((K t : ℝ) : ℂ)) atTop (𝓝 1) := by
    have h := tendsto_finsetSum box fun m _ => (windowMean_exp (primeFreq m)).const_mul
      (rieszCoeff ψ m)
    have hval : ∑ m ∈ box, rieszCoeff ψ m * (if primeFreq m = 0 then 1 else 0) = 1 := by
      rw [Finset.sum_eq_single (0 : P → ℤ)]
      · simp [primeFreq, rieszCoeff, rieszWeight]
      · intro m hm hm0
        have hms : ∀ i, m i = -1 ∨ m i = 0 ∨ m i = 1 := fun i =>
          mem_signSet.mp (Fintype.mem_piFinset.mp hm i)
        rw [if_neg (fun h => hm0 (eq_zero_of_primeFreq_eq_zero hP hms h)), mul_zero]
      · intro h0
        exact absurd (Fintype.mem_piFinset.mpr fun i => mem_signSet.mpr (by simp)) h0
    rw [hval] at h
    exact h.congr fun T => (hexpandK T).symm
  have hlim := tendsto_finsetSum box fun m _ =>
    (tendsto_windowMean_strip hσ hB hM hbs hBL (primeFreq m)).const_mul (rieszCoeff ψ m)
  have hlimgK : Tendsto (windowMean fun t => g t * ((K t : ℝ) : ℂ)) atTop _ :=
    hlim.congr fun T => (hexpand T).symm
  have hbound : ∀ᶠ T in atTop, ‖windowMean (fun t => g t * ((K t : ℝ) : ℂ)) T‖ ≤
      M * ‖windowMean (fun t => ((K t : ℝ) : ℂ)) T‖ := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    have hint : ∫ t in (0 : ℝ)..T, ((K t : ℝ) : ℂ) = ((∫ t in (0 : ℝ)..T, K t : ℝ) : ℂ) :=
      intervalIntegral.integral_ofReal
    have hKint : 0 ≤ ∫ t in (0 : ℝ)..T, K t :=
      intervalIntegral.integral_nonneg hT.le fun t _ => rieszProductKernel_nonneg ψ t
    rw [windowMean, windowMean, norm_mul, norm_mul, hint, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hKint, ← mul_assoc, mul_comm M, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine (intervalIntegral.norm_integral_le_integral_norm hT.le).trans ?_
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hT.le
      ((hgc.mul (Complex.continuous_ofReal.comp hKc)).norm.intervalIntegrable _ _)
      ((continuous_const.mul hKc).intervalIntegrable _ _) fun t _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (rieszProductKernel_nonneg ψ t)]
    exact mul_le_mul_of_nonneg_right (hgM t) (rieszProductKernel_nonneg ψ t)
  have hfin := le_of_tendsto_of_tendsto hlimgK.norm (hlimK.norm.const_mul M) hbound
  rw [norm_one, mul_one] at hfin
  exact hfin

/-- Discrete orthogonality: `Σ_{j<k} e^{2πi jd/k} = k·[d = 0]` for `|d| < k`. -/
theorem sum_exp_two_pi_mul {k : ℕ} (hk : 0 < k) {d : ℤ} (hd : |d| < k) :
    ∑ j ∈ Finset.range k, cexp (2 * Real.pi * I * (j * d / k)) = if d = 0 then (k : ℂ) else 0 := by
  split_ifs with h0
  · subst h0; simp
  · set ζ : ℂ := cexp (2 * Real.pi * I * (d / k)) with hζ
    have hpow : ∀ j : ℕ, cexp (2 * Real.pi * I * (j * d / k)) = ζ ^ j := by
      intro j
      rw [hζ, ← Complex.exp_nat_mul]
      congr 1
      ring
    simp_rw [hpow]
    have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
    have hζk : ζ ^ k = 1 := by
      rw [hζ, ← Complex.exp_nat_mul, show (k : ℂ) * (2 * Real.pi * I * (d / k)) =
        (d : ℂ) * (2 * Real.pi * I) by field_simp]
      exact Complex.exp_int_mul_two_pi_mul_I d
    have hζ1 : ζ ≠ 1 := by
      intro h1
      obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
      have h2 : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
      have h3 : (d : ℂ) / k = n := mul_left_cancel₀ h2 (hn.trans (mul_comm _ _))
      rw [div_eq_iff hk0] at h3
      have h4 : d = n * k := by exact_mod_cast h3
      have hn0 : n ≠ 0 := by rintro rfl; simp at h4; exact h0 h4
      have : (k : ℤ) ≤ |d| := by
        rw [h4, abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ k)]
        exact le_mul_of_one_le_left (by positivity) (Int.one_le_abs hn0)
      omega
    have hgeom := geom_sum_eq hζ1 k
    rw [hgeom, hζk, sub_self, zero_div]

/-- **Bohr's inequality for the prime coefficients of a bounded Dirichlet series.**  Let `B` be
holomorphic on the closed strip `σ ≤ Re s ≤ σ'`, bounded by `M` there, and equal on `Re s = σ'` to
an absolutely convergent Dirichlet series `Σ b(n) n^{−s}`.  Then `Σ_{p∈P} |b(p)| p^{−σ} ≤ 2M` for
every finite set `P` of primes. -/
theorem sum_norm_prime_coeff_le {B : ℂ → ℂ} {b : ℕ → ℂ} {σ σ' M : ℝ} (hσ : σ ≤ σ')
    (hB : DifferentiableOn ℂ B {z : ℂ | σ ≤ z.re ∧ z.re ≤ σ'})
    (hM : ∀ z : ℂ, σ ≤ z.re → z.re ≤ σ' → ‖B z‖ ≤ M)
    (hbs : LSeriesSummable b (σ' : ℂ))
    (hBL : ∀ t : ℝ, B ((σ' : ℂ) + (t : ℂ) * I) = LSeries b ((σ' : ℂ) + (t : ℂ) * I))
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) :
    ∑ p ∈ P, ‖b p‖ * (p : ℝ) ^ (-σ) ≤ 2 * M := by
  classical
  set box := Fintype.piFinset fun _ : P => signSet with hbox
  set L : (P → ℤ) → ℂ := fun m => cexp (-((primeFreq m * σ : ℝ) : ℂ)) *
    (cexp ((primeFreq m * σ' : ℝ) : ℂ) * ∑' n : ℕ, LSeries.term b (σ' : ℂ) n *
      (if primeFreq m - Real.log n = 0 then 1 else 0)) with hL
  set k : ℕ := P.card + 2 with hk
  have hk0 : 0 < k := by omega
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk0.ne'
  set θ : P → ℝ := fun i => -Complex.arg (b i) with hθ
  set ψ : ℕ → P → ℝ := fun j i => θ i + 2 * Real.pi * j / k with hψ
  set wt : (P → ℤ) → ℂ := fun m => (∏ i : P, rieszWeight (m i)) *
    cexp (((∑ i : P, (m i : ℝ) * θ i : ℝ) : ℂ) * I) with hwt
  set deg : (P → ℤ) → ℤ := fun m => ∑ i : P, m i with hdeg
  have hcoeff : ∀ (j : ℕ) (m : P → ℤ), rieszCoeff (ψ j) m =
      wt m * cexp (2 * Real.pi * I * (j * deg m / k)) := by
    intro j m
    simp only [rieszCoeff, hwt, hψ, hdeg]
    rw [mul_assoc _ (cexp _) (cexp _), ← Complex.exp_add]
    congr 2
    push_cast
    have hsplit : (∑ x : P, ((m x : ℤ) : ℂ) * ((θ x : ℂ) + 2 * Real.pi * j / k)) =
        (∑ x : P, ((m x : ℤ) : ℂ) * θ x) + 2 * Real.pi * j / k * ∑ x : P, ((m x : ℤ) : ℂ) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [hsplit]
    ring
  -- the degree of a sign vector is small
  have hdegbd : ∀ m ∈ box, |deg m - 1| < k := by
    intro m hm
    have hm' : ∀ i, m i = -1 ∨ m i = 0 ∨ m i = 1 := fun i =>
      mem_signSet.mp (Fintype.mem_piFinset.mp hm i)
    have habs : |deg m| ≤ P.card := by
      calc |deg m| ≤ ∑ i : P, |m i| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : P, (1 : ℤ) := Finset.sum_le_sum fun i _ => by
            rcases hm' i with h | h | h <;> simp [h]
        _ = P.card := by simp
    have := abs_sub (deg m) 1
    rw [abs_one] at this
    omega
  -- discrete average over the diagonal rotation
  have havg : ∑ j ∈ Finset.range k, cexp (-(2 * Real.pi * I * (j * 1 / k))) *
      ∑ m ∈ box, rieszCoeff (ψ j) m * L m =
      k * ∑ m ∈ box.filter (fun m => deg m = 1), wt m * L m := by
    rw [Finset.sum_filter, Finset.mul_sum]
    simp_rw [hcoeff]
    rw [Finset.sum_congr rfl fun j _ => Finset.mul_sum _ _ _, Finset.sum_comm]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hsum : ∑ j ∈ Finset.range k, cexp (-(2 * Real.pi * I * (j * 1 / k))) *
        (wt m * cexp (2 * Real.pi * I * (j * deg m / k)) * L m) =
        wt m * L m * ∑ j ∈ Finset.range k,
          cexp (2 * Real.pi * I * (j * ((deg m - 1 : ℤ) : ℂ) / k)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show cexp (2 * Real.pi * I * (j * ((deg m - 1 : ℤ) : ℂ) / k)) =
        cexp (-(2 * Real.pi * I * (j * 1 / k))) * cexp (2 * Real.pi * I * (j * deg m / k)) by
          rw [← Complex.exp_add]; congr 1; push_cast; ring]
      ring
    rw [hsum, sum_exp_two_pi_mul hk0 (hdegbd m hm)]
    by_cases h1 : deg m = 1
    · simp [h1]; ring
    · simp [h1, sub_eq_zero]
  have hnormavg : ‖∑ m ∈ box.filter (fun m => deg m = 1), wt m * L m‖ ≤ M := by
    have h1 : ‖(k : ℂ) * ∑ m ∈ box.filter (fun m => deg m = 1), wt m * L m‖ ≤ k * M := by
      rw [← havg]
      refine (norm_sum_le _ _).trans ?_
      calc _ ≤ ∑ _j ∈ Finset.range k, M := Finset.sum_le_sum fun j _ => by
            rw [norm_mul, show (-(2 * Real.pi * I * ((j : ℂ) * 1 / k))) =
              ((-(2 * Real.pi * j / k) : ℝ) : ℂ) * I by push_cast; ring,
              Complex.norm_exp_ofReal_mul_I, one_mul]
            exact norm_sum_rieszCoeff_le hσ hB hM hbs hBL hP (ψ j)
        _ = k * M := by simp
    rw [norm_mul, Complex.norm_natCast] at h1
    exact le_of_mul_le_mul_left h1 (by exact_mod_cast hk0)
  -- only unit vectors survive
  have hsingle : ∑ m ∈ box.filter (fun m => deg m = 1), wt m * L m =
      ∑ i : P, wt (Pi.single i 1) * L (Pi.single i 1) := by
    have hinj : Set.InjOn (fun i : P => (Pi.single i (1 : ℤ) : P → ℤ)) ↑(Finset.univ : Finset P) := by
      intro i _ j _ hij
      by_contra hne
      have := congrFun hij i
      simp [Pi.single_eq_of_ne hne] at this
    rw [← Finset.sum_image (f := fun m => wt m * L m) hinj]
    refine (Finset.sum_subset (fun m hm => ?_) (fun m hm hnot => ?_)).symm
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hm
      refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun j => mem_signSet.mpr ?_, ?_⟩
      · by_cases hj : j = i
        · subst hj; simp
        · simp [Pi.single_eq_of_ne hj]
      · simp [hdeg, Finset.sum_pi_single']
    · obtain ⟨hmbox, hdeg1⟩ := Finset.mem_filter.mp hm
      have hm' : ∀ i, m i = -1 ∨ m i = 0 ∨ m i = 1 := fun i =>
        mem_signSet.mp (Fintype.mem_piFinset.mp hmbox i)
      by_contra hne
      have hL0 : L m ≠ 0 := right_ne_zero_of_mul hne
      have hS : ∃ n : ℕ, 0 < n ∧ Real.log n = primeFreq m := by
        by_contra hno
        push Not at hno
        apply hL0
        simp only [hL]
        rw [tsum_term_indicator_eq_zero fun n hn h => hno n hn h, mul_zero, mul_zero]
      obtain ⟨n, hn, hlog⟩ := hS
      have hnn := nonneg_of_log_eq hP hm' hn hlog
      obtain ⟨i, rfl⟩ := exists_eq_single_of_sum_eq_one hm' hnn hdeg1
      exact hnot (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  -- evaluation at a unit vector
  have hunit : ∀ i : P, wt (Pi.single i 1) * L (Pi.single i 1) =
      (((1 / 2) * (‖b (i : ℕ)‖ * ((i : ℕ) : ℝ) ^ (-σ)) : ℝ) : ℂ) := by
    intro i
    have hi0 : (0 : ℝ) < (i : ℕ) := by exact_mod_cast (hP _ i.2).pos
    have hfreq : primeFreq (Pi.single i (1 : ℤ)) = Real.log (i : ℕ) := by
      simp only [primeFreq]
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)]
      simp
    have hw : ∏ j : P, rieszWeight ((Pi.single i (1 : ℤ) : P → ℤ) j) = 1 / 2 := by
      rw [Finset.prod_eq_single i (fun j _ hj => by simp [rieszWeight, Pi.single_eq_of_ne hj])
        (by simp)]
      simp [rieszWeight]
    have hθs : ∑ j : P, ((Pi.single i (1 : ℤ) : P → ℤ) j : ℝ) * θ j = θ i := by
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)]
      simp
    have hLv : L (Pi.single i 1) = b (i : ℕ) * (((i : ℕ) : ℝ) ^ (-σ) : ℝ) := by
      simp only [hL]
      rw [hfreq, tsum_term_indicator_log (hP _ i.2).pos, LSeries.term_of_ne_zero
        (hP _ i.2).ne_zero, Real.rpow_def_of_pos hi0]
      rw [show ((i : ℕ) : ℂ) ^ (σ' : ℂ) = cexp ((Real.log (i : ℕ) * σ' : ℝ) : ℂ) by
        rw [show ((i : ℕ) : ℂ) = (((i : ℕ) : ℝ) : ℂ) by push_cast; rfl,
          Complex.cpow_def_of_ne_zero (by exact_mod_cast hi0.ne'), ← Complex.ofReal_log hi0.le]
        push_cast; ring_nf]
      push_cast
      rw [div_eq_mul_inv, ← Complex.exp_neg]
      rw [show ∀ (x y z w : ℂ), cexp x * (cexp y * (w * cexp z)) = w * cexp (x + y + z) from
        fun x y z w => by rw [Complex.exp_add, Complex.exp_add]; ring]
      congr 2
      ring
    simp only [hwt]
    rw [hw, hθs, hLv]
    have harg : cexp ((θ i : ℂ) * I) * b (i : ℕ) = (‖b (i : ℕ)‖ : ℂ) := by
      have h := Complex.norm_mul_exp_arg_mul_I (b (i : ℕ))
      simp only [hθ]
      rw [show ((-Complex.arg (b (i : ℕ)) : ℝ) : ℂ) * I = -((Complex.arg (b (i : ℕ)) : ℂ) * I) by
        push_cast; ring, Complex.exp_neg]
      nth_rewrite 2 [← h]
      field_simp
    push_cast
    rw [show (1 / 2 : ℂ) * cexp ((θ i : ℂ) * I) * (b (i : ℕ) * (((i : ℕ) : ℝ) ^ (-σ) : ℝ)) =
      (1 / 2 : ℂ) * (cexp ((θ i : ℂ) * I) * b (i : ℕ)) * (((i : ℕ) : ℝ) ^ (-σ) : ℝ) by ring,
      harg]
    ring
  rw [hsingle] at hnormavg
  simp_rw [hunit] at hnormavg
  rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg fun i _ => by positivity), ← Finset.mul_sum] at hnormavg
  have hsum := Finset.sum_coe_sort P (fun p : ℕ => ‖b p‖ * (p : ℝ) ^ (-σ))
  rw [← hsum]
  linarith

end GaloisForLFunctions.BohrPrime

end
