import GaloisForLFunctions.RHTower.DeningerMobiusPreimage
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# The canonical preimage as a series of translates

In the logarithmic coordinate the Möbius series becomes a series of *translates* of the source,

`f_h(e^t) = ∑_{n ≥ 1} μ(n) h(log n + t)`,

so every derivative is obtained by differentiating the source once, with no chain-rule factor.  On
`(-1, ∞)` the translate `log n + t` exceeds `log n - 1`, so the source bound at exponent `2` gives
the uniform summable majorant `C n^{-2}` needed to differentiate the series term by term.

* `deningerExpSchwartz_iteratedDeriv_norm_le` : the source bound at every derivative order.
* `deningerLogSeries` : the `r`-th derivative series.
* `deningerLogSeries_hasDerivAt` : **the series may be differentiated term by term on `(-1, ∞)`.**
* `deningerLogSeries_zero_eq` : it is the canonical preimage in the logarithmic coordinate.
-/

namespace RHTower

open SchwartzMap ArithmeticFunction

open scoped ContDiff

noncomputable section

/-! ## The source bound at every derivative order -/

/-- The defining bound of the source, in iterated-derivative form. -/
theorem deningerExpSchwartz_iteratedDeriv_norm_le {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz)
    (A : ℝ) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖iteratedDeriv r (h : ℝ → ℂ) t‖ ≤ C * Real.exp (-(A * |t|)) := by
  obtain ⟨C, hC⟩ := hh A r
  refine ⟨max C 0, le_max_right _ _, fun t => ?_⟩
  have h0 := hC t
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at h0
  have hval : Real.exp (A * |t|) * ‖iteratedDeriv r (h : ℝ → ℂ) t‖ ≤ max C 0 :=
    le_trans h0 (le_max_left _ _)
  have hepos : (0 : ℝ) < Real.exp (A * |t|) := Real.exp_pos _
  rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ hepos]
  calc ‖iteratedDeriv r (h : ℝ → ℂ) t‖ * Real.exp (A * |t|)
      = Real.exp (A * |t|) * ‖iteratedDeriv r (h : ℝ → ℂ) t‖ := by ring
    _ ≤ max C 0 := hval

/-! ## The translate series -/

/-- The `r`-th derivative series of the canonical preimage in the logarithmic coordinate. -/
def deningerLogSeries (h : 𝓢(ℝ, ℂ)) (r : ℕ) (t : ℝ) : ℂ :=
  ∑' n : ℕ, ((moebius n : ℤ) : ℂ) * iteratedDeriv r (h : ℝ → ℂ) (Real.log n + t)

/-- **The uniform summable majorant of the translate series on `(-1, ∞)`.** -/
theorem deningerLogTerm_unif_bound {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (t : ℝ), -1 < t →
      ‖((moebius n : ℤ) : ℂ) * iteratedDeriv r (h : ℝ → ℂ) (Real.log n + t)‖
        ≤ C * (1 / (n : ℝ) ^ 2) := by
  obtain ⟨C, hCnn, hC⟩ := deningerExpSchwartz_iteratedDeriv_norm_le hh 2 r
  refine ⟨C * Real.exp 2, by positivity, fun n t ht => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hmu : ((moebius 0 : ℤ) : ℂ) = 0 := by simp
    rw [hmu, zero_mul, norm_zero]
    positivity
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le zero_lt_one hn1
    have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
    have hmu : ‖((moebius n : ℤ) : ℂ)‖ ≤ 1 := by
      rcases moebius_eq_or n with h1 | h1 | h1 <;> rw [h1] <;> norm_num
    rw [norm_mul]
    have hstep : ‖((moebius n : ℤ) : ℂ)‖ * ‖iteratedDeriv r (h : ℝ → ℂ) (Real.log n + t)‖
        ≤ 1 * ‖iteratedDeriv r (h : ℝ → ℂ) (Real.log n + t)‖ :=
      mul_le_mul_of_nonneg_right hmu (norm_nonneg _)
    rw [one_mul] at hstep
    refine le_trans hstep (le_trans (hC (Real.log n + t)) ?_)
    have hge : Real.log (n : ℝ) - 1 ≤ |Real.log (n : ℝ) + t| :=
      le_trans (by linarith) (le_abs_self _)
    have hexp : Real.exp (-(2 * |Real.log (n : ℝ) + t|))
        ≤ Real.exp 2 * (1 / (n : ℝ) ^ 2) := by
      have hle : -(2 * |Real.log (n : ℝ) + t|) ≤ 2 - 2 * Real.log (n : ℝ) := by linarith
      refine le_trans (Real.exp_le_exp.mpr hle) (le_of_eq ?_)
      have hsq : Real.exp (2 * Real.log (n : ℝ)) = (n : ℝ) ^ 2 := by
        rw [show (2 : ℝ) * Real.log (n : ℝ) = Real.log (n : ℝ) + Real.log (n : ℝ) by ring,
          Real.exp_add, Real.exp_log hnpos, ← pow_two]
      rw [show (2 : ℝ) - 2 * Real.log (n : ℝ) = 2 + -(2 * Real.log (n : ℝ)) by ring,
        Real.exp_add, Real.exp_neg, hsq, one_div]
    calc C * Real.exp (-(2 * |Real.log (n : ℝ) + t|))
        ≤ C * (Real.exp 2 * (1 / (n : ℝ) ^ 2)) := mul_le_mul_of_nonneg_left hexp hCnn
      _ = C * Real.exp 2 * (1 / (n : ℝ) ^ 2) := by ring

/-- Every term of the translate series is differentiable, with the next series as derivative. -/
theorem deningerLogTerm_hasDerivAt (h : 𝓢(ℝ, ℂ)) (r n : ℕ) (t : ℝ) :
    HasDerivAt (fun y : ℝ => ((moebius n : ℤ) : ℂ) * iteratedDeriv r (h : ℝ → ℂ)
        (Real.log n + y))
      (((moebius n : ℤ) : ℂ) * iteratedDeriv (r + 1) (h : ℝ → ℂ) (Real.log n + t)) t := by
  have hsm : ContDiff ℝ ∞ (iteratedDeriv r (h : ℝ → ℂ)) := by
    rw [iteratedDeriv_eq_iterate]
    exact (h.smooth').iterate_deriv r
  have hdiff : DifferentiableAt ℝ (iteratedDeriv r (h : ℝ → ℂ)) (Real.log n + t) :=
    (hsm.differentiable (by simp)).differentiableAt
  have hbase : HasDerivAt (iteratedDeriv r (h : ℝ → ℂ))
      (deriv (iteratedDeriv r (h : ℝ → ℂ)) (Real.log n + t)) (Real.log n + t) :=
    hdiff.hasDerivAt
  have hcomp := hbase.comp_const_add (Real.log n) t
  have hsucc : deriv (iteratedDeriv r (h : ℝ → ℂ)) = iteratedDeriv (r + 1) (h : ℝ → ℂ) :=
    (iteratedDeriv_succ (n := r) (f := (h : ℝ → ℂ))).symm
  rw [hsucc] at hcomp
  exact hcomp.const_mul _

/-- The `r`-th translate series converges absolutely on `(-1, ∞)`. -/
theorem deningerLogSeries_summable {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz) (r : ℕ)
    {t : ℝ} (ht : -1 < t) :
    Summable fun n : ℕ =>
      ((moebius n : ℤ) : ℂ) * iteratedDeriv r (h : ℝ → ℂ) (Real.log n + t) := by
  obtain ⟨C, hCnn, hC⟩ := deningerLogTerm_unif_bound hh r
  have hmaj : Summable fun n : ℕ => C * (1 / (n : ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left C
  exact Summable.of_norm_bounded hmaj fun n => hC n t ht

/-- **The translate series may be differentiated term by term on `(-1, ∞)`.** -/
theorem deningerLogSeries_hasDerivAt {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz) (r : ℕ)
    {t : ℝ} (ht : -1 < t) :
    HasDerivAt (deningerLogSeries h r) (deningerLogSeries h (r + 1) t) t := by
  obtain ⟨C, hCnn, hC⟩ := deningerLogTerm_unif_bound hh (r + 1)
  have hmaj : Summable fun n : ℕ => C * (1 / (n : ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left C
  have hopen : IsOpen (Set.Ioi (-1 : ℝ)) := isOpen_Ioi
  have hconn : IsPreconnected (Set.Ioi (-1 : ℝ)) := (convex_Ioi (-1 : ℝ)).isPreconnected
  have hzero : (0 : ℝ) ∈ Set.Ioi (-1 : ℝ) := by norm_num
  exact hasDerivAt_tsum_of_isPreconnected hmaj hopen hconn
    (fun n y _ => deningerLogTerm_hasDerivAt h r n y)
    (fun n y hy => hC n y hy) hzero
    (deningerLogSeries_summable hh r (by norm_num)) ht

/-- The zeroth translate series is the canonical preimage in the logarithmic coordinate. -/
theorem deningerLogSeries_zero_eq {h : 𝓢(ℝ, ℂ)} (t : ℝ) :
    deningerLogSeries h 0 t = deningerMobiusPreimage h (Real.exp t) := by
  rw [deningerLogSeries, deningerMobiusPreimage]
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [iteratedDeriv_zero, deningerLogPull_apply,
      Real.log_mul (ne_of_gt hnpos) (ne_of_gt (Real.exp_pos t)), Real.log_exp]

end

end RHTower
