import GaloisForLFunctions.RHTower.DeningerMeyerOscillator

/-!
# Derivatives of the exponential weight

The weight `t ↦ e^{ct}` has `j`-th derivative `c^j e^{ct}`, so its iterated differentials have norm
`|c|^j e^{ct}`.  Combined with the Leibniz bound this controls every derivative of a weighted
function by the derivatives of the function itself, in both directions.

* `deningerExpWeightC_iteratedFDeriv_norm` : `‖D^j e^{ct}‖ = |c|^j e^{ct}`.
* `deningerWeighted_iteratedFDeriv_bound` : **Leibniz for the weighted function.**
* `deningerUnweighted_iteratedFDeriv_bound` : **the same bound read backwards.**
-/

namespace RHTower

open SchwartzMap

noncomputable section

/-- The complex exponential weight `t ↦ e^{ct}`. -/
def deningerExpWeightC (c : ℝ) : ℝ → ℂ := fun t => ((Real.exp (c * t) : ℝ) : ℂ)

theorem deningerExpWeightC_contDiff (c : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (deningerExpWeightC c) :=
  Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))

theorem deningerExpWeightC_iteratedDeriv (c : ℝ) (j : ℕ) :
    iteratedDeriv j (deningerExpWeightC c) = fun t => (c : ℂ) ^ j * deningerExpWeightC c t := by
  induction j with
  | zero => simp [iteratedDeriv_zero]
  | succ j ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    have hd : HasDerivAt (fun s : ℝ => (c : ℂ) ^ j * deningerExpWeightC c s)
        ((c : ℂ) ^ j * ((c : ℂ) * deningerExpWeightC c t)) t := by
      have hbase : HasDerivAt (fun s : ℝ => Real.exp (c * s)) (Real.exp (c * t) * c) t := by
        simpa using ((hasDerivAt_id t).const_mul c).exp
      have hC : HasDerivAt (deningerExpWeightC c) ((c : ℂ) * deningerExpWeightC c t) t := by
        have hr := hbase.ofReal_comp
        have hcast : ((Real.exp (c * t) * c : ℝ) : ℂ) = (c : ℂ) * deningerExpWeightC c t := by
          rw [deningerExpWeightC]
          push_cast
          ring
        rw [hcast] at hr
        exact hr
      exact hC.const_mul _
    rw [hd.deriv]
    ring

theorem deningerExpWeightC_iteratedFDeriv_norm (c : ℝ) (j : ℕ) (t : ℝ) :
    ‖iteratedFDeriv ℝ j (deningerExpWeightC c) t‖ = |c| ^ j * Real.exp (c * t) := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, deningerExpWeightC_iteratedDeriv]
  rw [norm_mul, deningerExpWeightC, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), norm_pow, Complex.norm_real, Real.norm_eq_abs]

/-- **Leibniz bound for a weighted function.** -/
theorem deningerWeighted_iteratedFDeriv_bound {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (c : ℝ)
    (b : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ b (fun t => deningerExpWeightC c t * f t) x‖
      ≤ ∑ j ∈ Finset.range (b + 1), (b.choose j : ℝ) * (|c| ^ j * Real.exp (c * x))
          * ‖iteratedFDeriv ℝ (b - j) f x‖ := by
  refine le_trans (norm_iteratedFDeriv_mul_le (deningerExpWeightC_contDiff c) hf x
    (by exact_mod_cast le_top)) (le_of_eq ?_)
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [deningerExpWeightC_iteratedFDeriv_norm]

/-- **The same bound read backwards**: the unweighted derivatives are controlled by the weighted
ones, because the inverse weight is again an exponential. -/
theorem deningerUnweighted_iteratedFDeriv_bound {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (c : ℝ)
    (b : ℕ) (x : ℝ) :
    Real.exp (c * x) * ‖iteratedFDeriv ℝ b f x‖
      ≤ ∑ j ∈ Finset.range (b + 1), (b.choose j : ℝ) * |c| ^ j
          * ‖iteratedFDeriv ℝ (b - j) (fun t => deningerExpWeightC c t * f t) x‖ := by
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun t => deningerExpWeightC c t * f t) :=
    (deningerExpWeightC_contDiff c).mul hf
  have hcancel : (fun t => deningerExpWeightC (-c) t * (deningerExpWeightC c t * f t)) = f := by
    funext t
    rw [deningerExpWeightC, deningerExpWeightC, ← mul_assoc, ← Complex.ofReal_mul,
      ← Real.exp_add]
    have hzero : -c * t + c * t = 0 := by ring
    rw [hzero, Real.exp_zero, Complex.ofReal_one, one_mul]
  have hbd := deningerWeighted_iteratedFDeriv_bound hg (-c) b x
  rw [hcancel] at hbd
  have hmul : Real.exp (c * x) * ‖iteratedFDeriv ℝ b f x‖
      ≤ Real.exp (c * x) * ∑ j ∈ Finset.range (b + 1), (b.choose j : ℝ)
          * (|(-c)| ^ j * Real.exp (-c * x))
          * ‖iteratedFDeriv ℝ (b - j) (fun t => deningerExpWeightC c t * f t) x‖ :=
    mul_le_mul_of_nonneg_left hbd (Real.exp_pos _).le
  refine le_trans hmul (le_of_eq ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hexp : Real.exp (c * x) * Real.exp (-c * x) = 1 := by
    rw [← Real.exp_add]
    have : c * x + -c * x = 0 := by ring
    rw [this, Real.exp_zero]
  calc Real.exp (c * x) * ((b.choose j : ℝ) * (|(-c)| ^ j * Real.exp (-c * x))
        * ‖iteratedFDeriv ℝ (b - j) (fun t => deningerExpWeightC c t * f t) x‖)
      = ((b.choose j : ℝ) * |(-c)| ^ j
          * ‖iteratedFDeriv ℝ (b - j) (fun t => deningerExpWeightC c t * f t) x‖)
        * (Real.exp (c * x) * Real.exp (-c * x)) := by ring
    _ = (b.choose j : ℝ) * |c| ^ j
          * ‖iteratedFDeriv ℝ (b - j) (fun t => deningerExpWeightC c t * f t) x‖ := by
        rw [hexp, mul_one, abs_neg]

end

end RHTower
