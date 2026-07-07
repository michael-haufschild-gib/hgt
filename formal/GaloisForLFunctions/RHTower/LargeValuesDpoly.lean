/-
The large-values inequality for a Dirichlet polynomial, on top of `SecondMoment`.

The Dirichlet polynomial `D(t) = ∑_{n∈s} aₙ n^{-it}` (`SecondMoment.dpoly`) has derivative
`D'(t) = −i ∑_{n∈s} aₙ (log n) n^{-it} = −i · dpoly(a·log)`, so `‖D'(t)‖ = ‖dpoly(a·log)(t)‖`.  Feeding
`f = D`, `f' = D'` to the abstract large-values inequality `LargeValues.large_values_count` gives a
bound on the number of grid points where `‖D‖` is large, in terms of the second moment of `D` and of
its log-weighted companion `dpoly(a·log)`:

  R · V² ≤ (δ^{-1}+η^{-1}) ∫_A^{A+Rδ}‖D‖² + η ∫_A^{A+Rδ}‖dpoly(a·log)‖²      (any η > 0).

Both integrals are Montgomery–Vaughan second moments (`SecondMoment.secondMoment_upper_bound`): the
first with coefficients `aₙ`, the second with `aₙ log n`.  This is the "large values from the second
moment" step — the Dirichlet-polynomial heart of Carlson's density argument, self-contained on
`SecondMoment`.
-/
import GaloisForLFunctions.RHTower.SecondMoment
import GaloisForLFunctions.RHTower.LargeValues

open Complex Real MeasureTheory intervalIntegral RealInnerProductSpace

namespace RHTower

/-- The derivative of `t ↦ cterm a t n` in `t` is `−i · cterm(a·log) t n`. -/
theorem cterm_hasDerivAt (a : ℕ → ℝ) (n : ℕ) (t : ℝ) :
    HasDerivAt (fun t => cterm a t n) (-I * cterm (fun m => a m * Real.log m) t n) t := by
  unfold cterm
  have hlin : HasDerivAt (fun t : ℝ => -(t : ℂ) * I * (Real.log n : ℂ))
      (-(I * (Real.log n : ℂ))) t := by
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
    have := (h1.neg.mul_const I).mul_const (Real.log n : ℂ)
    simpa using this
  have := (hlin.cexp).const_mul (a n : ℂ)
  convert this using 1
  push_cast; ring

/-- `t ↦ cterm a t n` is differentiable. -/
theorem cterm_differentiable (a : ℕ → ℝ) (n : ℕ) :
    Differentiable ℝ (fun t => cterm a t n) :=
  fun t => (cterm_hasDerivAt a n t).differentiableAt

/-- The derivative of the Dirichlet polynomial `D = dpoly a s` is `−i · dpoly(a·log) s`. -/
theorem dpoly_hasDerivAt (a : ℕ → ℝ) (s : Finset ℕ) (t : ℝ) :
    HasDerivAt (fun t => dpoly a s t)
      (-I * dpoly (fun m => a m * Real.log m) s t) t := by
  have hval : -I * dpoly (fun m => a m * Real.log m) s t
      = ∑ n ∈ s, -I * cterm (fun m => a m * Real.log m) t n := by
    rw [dpoly, Finset.mul_sum]
  rw [hval]
  have hfun : (∑ i ∈ s, fun t => cterm a t i) = (fun t => dpoly a s t) := by
    funext t; rw [Finset.sum_apply]; rfl
  have hsum := HasDerivAt.sum (fun n (_ : n ∈ s) => cterm_hasDerivAt a n t)
  rwa [hfun] at hsum

/-- `D = dpoly a s` is continuous. -/
theorem dpoly_continuous (a : ℕ → ℝ) (s : Finset ℕ) : Continuous (fun t => dpoly a s t) := by
  unfold dpoly
  exact continuous_finsetSum s (fun n _ => (cterm_differentiable a n).continuous)

/-- `‖D'‖ = ‖dpoly(a·log)‖`, since `‖−i·z‖ = ‖z‖`. -/
theorem norm_dpoly_deriv (a : ℕ → ℝ) (s : Finset ℕ) (t : ℝ) :
    ‖-I * dpoly (fun m => a m * Real.log m) s t‖
      = ‖dpoly (fun m => a m * Real.log m) s t‖ := by
  rw [norm_mul, norm_neg, Complex.norm_I, one_mul]

/-- **The large-values inequality for a Dirichlet polynomial.**  If `R` grid points `A+rδ` all have
`‖D‖ ≥ V ≥ 0`, then `R·V² ≤ (δ^{-1}+η^{-1})∫‖D‖² + η∫‖dpoly(a·log)‖²` — the count of large values is
controlled by the second moments of `D` and its log-weighted companion. -/
theorem large_values_dpoly (a : ℕ → ℝ) (s : Finset ℕ) {A δ V η : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hV0 : 0 ≤ V) (R : ℕ)
    (hV : ∀ r, r < R → V ≤ ‖dpoly a s (A + r * δ)‖) :
    (R : ℝ) * V ^ 2 ≤ (1 / δ + 1 / η) * (∫ u in A..A + R * δ, ‖dpoly a s u‖ ^ 2)
      + η * (∫ u in A..A + R * δ, ‖dpoly (fun m => a m * Real.log m) s u‖ ^ 2) := by
  set alog : ℕ → ℝ := fun m => a m * Real.log m with halog
  set f : ℝ → ℂ := fun t => dpoly a s t with hf_def
  set f' : ℝ → ℂ := fun t => -I * dpoly alog s t with hf'_def
  have hf : ∀ y ∈ Set.Icc A (A + R * δ), HasDerivAt f (f' y) y :=
    fun y _ => dpoly_hasDerivAt a s y
  have hfc : Continuous f := dpoly_continuous a s
  have hf'c : Continuous f' := continuous_const.mul (dpoly_continuous alog s)
  have hAle : A ≤ A + R * δ := le_add_of_nonneg_right (by positivity)
  have hgint : IntervalIntegrable (fun y => ‖f y‖ ^ 2) volume A (A + R * δ) :=
    (hfc.norm.pow 2).intervalIntegrable _ _
  have hsqf'int : IntervalIntegrable (fun y => ‖f' y‖ ^ 2) volume A (A + R * δ) :=
    (hf'c.norm.pow 2).intervalIntegrable _ _
  have hcrossint : IntervalIntegrable (fun y => 2 * (‖f y‖ * ‖f' y‖)) volume A (A + R * δ) :=
    (continuous_const.mul (hfc.norm.mul hf'c.norm)).intervalIntegrable _ _
  have hg'int : IntervalIntegrable (fun y => 2 * inner ℝ (f y) (f' y)) volume A (A + R * δ) :=
    (continuous_const.mul (continuous_inner.comp (hfc.prodMk hf'c))).intervalIntegrable _ _
  have hlvc := large_values_count hδ hη hV0 R hf hg'int hgint hsqf'int hcrossint hV
  -- replace ∫‖f'‖² with ∫‖dpoly(a·log)‖²
  have heq : (∫ u in A..A + R * δ, ‖f' u‖ ^ 2)
      = ∫ u in A..A + R * δ, ‖dpoly alog s u‖ ^ 2 :=
    intervalIntegral.integral_congr (fun y _ => by rw [hf'_def, norm_dpoly_deriv])
  rw [heq] at hlvc
  exact hlvc

end RHTower
