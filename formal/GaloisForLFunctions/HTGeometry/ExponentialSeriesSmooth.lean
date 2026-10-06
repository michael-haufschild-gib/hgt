import GaloisForLFunctions.HTGeometry.SmoothDerivativeChain

/-!
# Smooth exponential series

For coefficients `d : ℕ → ℂ` and exponents `m : ℕ → ℝ` with
`∑_k |d_k| |m_k|^n e^{|m_k| R} < ∞` for every `n` and `R` (`ExpSeriesAdmissible`), the series

`E(w) = ∑_k d_k e^{-m_k w}`

is smooth on `ℝ` and may be differentiated termwise: `E^{(n)} = ∑_k (-m_k)^n d_k e^{-m_k w}`
(`iteratedDeriv_expSeries`).  If every exponent is at least `μ`, then `|E^{(n)}(w)| ≤ C_n e^{-μ w}`
for `w ≥ 0` (`exists_bound_iteratedDeriv_expSeries`).
-/

open Real

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- `E(w) = ∑_k d_k e^{-m_k w}`. -/
def expSeries (d : ℕ → ℂ) (m : ℕ → ℝ) (w : ℝ) : ℂ :=
  ∑' k, d k * ((Real.exp (-(m k * w)) : ℝ) : ℂ)

/-- Summability of `|d_k| |m_k|^n e^{|m_k| R}` for all `n` and `R`. -/
def ExpSeriesAdmissible (d : ℕ → ℂ) (m : ℕ → ℝ) : Prop :=
  ∀ (n : ℕ) (R : ℝ), Summable fun k => ‖d k‖ * |m k| ^ n * Real.exp (|m k| * R)

theorem ExpSeriesAdmissible.deriv {d : ℕ → ℂ} {m : ℕ → ℝ} (h : ExpSeriesAdmissible d m) :
    ExpSeriesAdmissible (fun k => -(m k : ℂ) * d k) m := by
  intro n R
  refine (h (n + 1) R).congr fun k => ?_
  rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, pow_succ]
  ring

theorem norm_exp_neg_mul_le (m w R : ℝ) (hw : |w| ≤ R) :
    Real.exp (-(m * w)) ≤ Real.exp (|m| * R) := by
  refine Real.exp_le_exp.2 ?_
  calc -(m * w) ≤ |m * w| := neg_le_abs _
    _ = |m| * |w| := abs_mul _ _
    _ ≤ |m| * R := mul_le_mul_of_nonneg_left hw (abs_nonneg _)

theorem summable_expSeries {d : ℕ → ℂ} {m : ℕ → ℝ} (h : ExpSeriesAdmissible d m) (w : ℝ) :
    Summable fun k => d k * ((Real.exp (-(m k * w)) : ℝ) : ℂ) := by
  refine Summable.of_norm_bounded (h 0 |w|) fun k => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, pow_zero, mul_one]
  exact mul_le_mul_of_nonneg_left (norm_exp_neg_mul_le _ _ _ le_rfl) (norm_nonneg _)

/-- **Termwise differentiation.** -/
theorem hasDerivAt_expSeries {d : ℕ → ℂ} {m : ℕ → ℝ} (h : ExpSeriesAdmissible d m) (w : ℝ) :
    HasDerivAt (expSeries d m) (expSeries (fun k => -(m k : ℂ) * d k) m w) w := by
  have hterm : ∀ k (y : ℝ), HasDerivAt (fun y : ℝ => d k * ((Real.exp (-(m k * y)) : ℝ) : ℂ))
      (-(m k : ℂ) * d k * ((Real.exp (-(m k * y)) : ℝ) : ℂ)) y := fun k y => by
    have h1 : HasDerivAt (fun y : ℝ => -(m k * y)) (-(m k)) y := by
      have e : (fun y : ℝ => -(m k * y)) = fun y => -(m k) * y := by funext y; ring
      rw [e]; simpa using (hasDerivAt_id y).const_mul (-(m k))
    have h2 := (h1.exp.ofReal_comp).const_mul (d k)
    refine h2.congr_deriv ?_
    push_cast; ring
  refine hasDerivAt_tsum_of_isPreconnected (u := fun k => ‖d k‖ * |m k| ^ 1 * Real.exp (|m k| * (|w| + 1)))
    (t := Set.Ioo (w - 1) (w + 1)) (y₀ := w) (h 1 (|w| + 1)) isOpen_Ioo isPreconnected_Ioo
    (fun k y _ => hterm k y) (fun k y hy => ?_) ⟨by linarith, by linarith⟩ (summable_expSeries h w)
    ⟨by linarith, by linarith⟩
  have hy' : |y| ≤ |w| + 1 := by
    obtain ⟨h1, h2⟩ := hy
    rw [abs_le]; constructor <;> cases abs_cases w <;> linarith
  rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_of_nonneg (Real.exp_pos _).le, pow_one]
  calc |m k| * ‖d k‖ * Real.exp (-(m k * y)) = ‖d k‖ * |m k| * Real.exp (-(m k * y)) := by ring
    _ ≤ ‖d k‖ * |m k| * Real.exp (|m k| * (|w| + 1)) :=
        mul_le_mul_of_nonneg_left (norm_exp_neg_mul_le _ _ _ hy') (by positivity)

/-- The derivative chain `n ↦ ∑_k (-m_k)^n d_k e^{-m_k w}`. -/
def expSeriesChain (d : ℕ → ℂ) (m : ℕ → ℝ) (n : ℕ) : ℝ → ℂ :=
  expSeries (fun k => (-(m k : ℂ)) ^ n * d k) m

theorem ExpSeriesAdmissible.pow {d : ℕ → ℂ} {m : ℕ → ℝ} (h : ExpSeriesAdmissible d m) (n : ℕ) :
    ExpSeriesAdmissible (fun k => (-(m k : ℂ)) ^ n * d k) m := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
      have := ih.deriv
      refine fun j R => (this j R).congr fun k => ?_
      have e : -(m k : ℂ) * ((-(m k : ℂ)) ^ n * d k) = (-(m k : ℂ)) ^ (n + 1) * d k := by ring
      simp only [e]

theorem hasDerivAt_expSeriesChain {d : ℕ → ℂ} {m : ℕ → ℝ} (h : ExpSeriesAdmissible d m) (n : ℕ)
    (w : ℝ) : HasDerivAt (expSeriesChain d m n) (expSeriesChain d m (n + 1) w) w := by
  have := hasDerivAt_expSeries (h.pow n) w
  unfold expSeriesChain
  convert this using 2
  funext k; rw [pow_succ]; ring

theorem contDiff_expSeries {d : ℕ → ℂ} {m : ℕ → ℝ} (h : ExpSeriesAdmissible d m) (n : ℕ) :
    ContDiff ℝ n (expSeries d m) := by
  have := contDiff_nat_of_hasDerivAt_chain (hasDerivAt_expSeriesChain h) n 0
  simpa [expSeriesChain] using this

theorem iteratedDeriv_expSeries {d : ℕ → ℂ} {m : ℕ → ℝ} (h : ExpSeriesAdmissible d m) (n : ℕ) :
    iteratedDeriv n (expSeries d m) = expSeries (fun k => (-(m k : ℂ)) ^ n * d k) m := by
  have := iteratedDeriv_eq_of_hasDerivAt_chain (hasDerivAt_expSeriesChain h) 0 n
  simpa [expSeriesChain] using this

/-- **Decay on the right half-line**: if every exponent is at least `μ`, then
`|E(w)| ≤ (∑ |d_k|) e^{-μ w}` for `w ≥ 0`. -/
theorem norm_expSeries_le {d : ℕ → ℂ} {m : ℕ → ℝ} (h : ExpSeriesAdmissible d m) {μ : ℝ}
    (hm : ∀ k, μ ≤ m k) {w : ℝ} (hw : 0 ≤ w) :
    ‖expSeries d m w‖ ≤ (∑' k, ‖d k‖) * Real.exp (-(μ * w)) := by
  have hs : Summable fun k => ‖d k‖ := (h 0 0).congr fun k => by simp
  have hb : ∀ k, ‖d k * ((Real.exp (-(m k * w)) : ℝ) : ℂ)‖ ≤ ‖d k‖ * Real.exp (-(μ * w)) := fun k => by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith [hm k])) (norm_nonneg _)
  calc ‖expSeries d m w‖ ≤ ∑' k, ‖d k‖ * Real.exp (-(μ * w)) :=
        tsum_of_norm_bounded (hs.mul_right _).hasSum hb
    _ = _ := tsum_mul_right

theorem exists_bound_iteratedDeriv_expSeries {d : ℕ → ℂ} {m : ℕ → ℝ} (h : ExpSeriesAdmissible d m)
    {μ : ℝ} (hm : ∀ k, μ ≤ m k) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w, 0 ≤ w → ‖iteratedDeriv n (expSeries d m) w‖ ≤ C * Real.exp (-(μ * w)) := by
  refine ⟨∑' k, ‖(-(m k : ℂ)) ^ n * d k‖, tsum_nonneg fun _ => norm_nonneg _, fun w hw => ?_⟩
  rw [iteratedDeriv_expSeries h n]
  exact norm_expSeries_le (h.pow n) hm hw

end

end GaloisForLFunctions.HTGeometry
