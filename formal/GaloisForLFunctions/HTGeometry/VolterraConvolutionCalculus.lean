import GaloisForLFunctions.HTGeometry.VolterraConvolutionAlgebra

/-!
# Differentiation of Volterra convolutions

For `f` of class `C¹` and continuous `g`, writing `f = f(0) + f' ⋆ 1` and using associativity gives
the integrated identity `(f ⋆ g)(t) = f(0) ∫₀^t g + ∫₀^t (f' ⋆ g)`, hence the Leibniz rule
`(f ⋆ g)' = f(0) g + f' ⋆ g`.  For smooth `f, g` it iterates to
`(f ⋆ g)^{(n)} = Σ_{j<n} f^{(j)}(0) g^{(n-1-j)} + f^{(n)} ⋆ g`, so the jets of `f ⋆ g` at the
origin are the truncated Cauchy products of the jets of `f` and `g`.
-/

open Set MeasureTheory
open scoped ContDiff

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- A Volterra convolution vanishes at the origin. -/
theorem volterraConv_apply_zero (f g : ℝ → ℝ) : volterraConv f g 0 = 0 := by
  simp [volterraConv]

/-- Convolution with the constant `1` is the primitive from the origin. -/
theorem volterraConv_one_left (g : ℝ → ℝ) (t : ℝ) :
    volterraConv (fun _ => 1) g t = ∫ s in (0 : ℝ)..t, g s := by
  simp [volterraConv]

theorem volterraConv_one_right (f : ℝ → ℝ) (t : ℝ) :
    volterraConv f (fun _ => 1) t = ∫ s in (0 : ℝ)..t, f s := by
  rw [volterraConv_comm, volterraConv_one_left]

/-- **Integrated Leibniz rule.** `(f ⋆ g)(t) = f(0) ∫₀^t g + ∫₀^t (f' ⋆ g)`. -/
theorem volterraConv_eq_integral_of_hasDerivAt {f f' g : ℝ → ℝ}
    (hf : ∀ s, HasDerivAt f (f' s) s) (hf' : Continuous f') (hg : Continuous g) (t : ℝ) :
    volterraConv f g t =
      f 0 * (∫ s in (0 : ℝ)..t, g s) + ∫ s in (0 : ℝ)..t, volterraConv f' g s := by
  have hfu : ∀ u, f u = f 0 + volterraConv f' (fun _ => 1) u := by
    intro u
    rw [volterraConv_one_right, intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => hf s) (hf'.intervalIntegrable _ _)]
    ring
  have hI : Continuous (volterraConv f' fun _ => (1 : ℝ)) :=
    continuous_volterraConv hf' continuous_const
  have hsplit : volterraConv f g t = f 0 * (∫ s in (0 : ℝ)..t, g s) +
      volterraConv (volterraConv f' fun _ => 1) g t := by
    have h1 : IntervalIntegrable (fun s => f 0 * g s) volume 0 t :=
      (hg.const_mul _).intervalIntegrable _ _
    have h2 : IntervalIntegrable (fun s => volterraConv f' (fun _ => 1) (t - s) * g s) volume 0 t :=
      ((hI.comp (continuous_const.sub continuous_id)).mul hg).intervalIntegrable _ _
    rw [volterraConv, volterraConv, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add h1 h2]
    refine intervalIntegral.integral_congr fun s _ => ?_
    rw [hfu (t - s)]; ring
  rw [hsplit, volterraConv_comm' f' (fun _ => (1 : ℝ)),
    volterraConv_assoc continuous_const hf' hg, volterraConv_one_left]

/-- **Leibniz rule.** For `f ∈ C¹` and continuous `g`, `(f ⋆ g)' = f(0) g + f' ⋆ g`. -/
theorem hasDerivAt_volterraConv {f f' g : ℝ → ℝ}
    (hf : ∀ s, HasDerivAt f (f' s) s) (hf' : Continuous f') (hg : Continuous g) (t : ℝ) :
    HasDerivAt (volterraConv f g) (f 0 * g t + volterraConv f' g t) t := by
  have hfun : volterraConv f g = fun u =>
      f 0 * (∫ s in (0 : ℝ)..u, g s) + ∫ s in (0 : ℝ)..u, volterraConv f' g s :=
    funext (volterraConv_eq_integral_of_hasDerivAt hf hf' hg)
  rw [hfun]
  exact ((hg.integral_hasStrictDerivAt 0 t).hasDerivAt.const_mul _).add
    ((continuous_volterraConv hf' hg).integral_hasStrictDerivAt 0 t).hasDerivAt

theorem natCast_lt_infty (m : ℕ) : ((m : ℕ) : WithTop ℕ∞) < ∞ :=
  WithTop.coe_lt_coe.mpr (ENat.coe_lt_top m)

/-- **Iterated Leibniz rule.** For smooth `f, g`,
`(f ⋆ g)^{(n)} = Σ_{j<n} f^{(j)}(0) g^{(n-1-j)} + f^{(n)} ⋆ g`. -/
theorem iteratedDeriv_volterraConv {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (n : ℕ) :
    iteratedDeriv n (volterraConv f g) = fun t =>
      ∑ j ∈ Finset.range n, iteratedDeriv j f 0 * iteratedDeriv (n - 1 - j) g t +
        volterraConv (iteratedDeriv n f) g t := by
  have hdf : ∀ k s, HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f s) s := by
    intro k s
    rw [iteratedDeriv_succ]
    exact ((hf.differentiable_iteratedDeriv k (natCast_lt_infty k)) s).hasDerivAt
  have hdg : ∀ k s, HasDerivAt (iteratedDeriv k g) (iteratedDeriv (k + 1) g s) s := by
    intro k s
    rw [iteratedDeriv_succ]
    exact ((hg.differentiable_iteratedDeriv k (natCast_lt_infty k)) s).hasDerivAt
  induction n with
  | zero => funext t; simp
  | succ n ih =>
    funext t
    rw [iteratedDeriv_succ, ih]
    have hsum : HasDerivAt (fun t => ∑ j ∈ Finset.range n,
        iteratedDeriv j f 0 * iteratedDeriv (n - 1 - j) g t)
        (∑ j ∈ Finset.range n, iteratedDeriv j f 0 * iteratedDeriv (n - 1 - j + 1) g t) t :=
      HasDerivAt.fun_sum fun j _ => (hdg _ t).const_mul _
    have hconv := hasDerivAt_volterraConv (hdf n)
      (hf.continuous_iteratedDeriv (n + 1) (natCast_lt_infty _).le) hg.continuous t
    rw [(hsum.fun_add hconv).deriv, Finset.sum_range_succ]
    have hidx : ∀ j ∈ Finset.range n, iteratedDeriv j f 0 * iteratedDeriv (n - 1 - j + 1) g t =
        iteratedDeriv j f 0 * iteratedDeriv (n + 1 - 1 - j) g t := by
      intro j hj
      rw [Finset.mem_range] at hj
      rw [show n - 1 - j + 1 = n + 1 - 1 - j by omega]
    rw [Finset.sum_congr rfl hidx, show n + 1 - 1 - n = 0 by omega, iteratedDeriv_zero]
    ring

/-- The jets of `f ⋆ g` at the origin are the truncated Cauchy products of the jets:
`(f ⋆ g)^{(n)}(0) = Σ_{j<n} f^{(j)}(0) g^{(n-1-j)}(0)`. -/
theorem iteratedDeriv_volterraConv_zero {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (n : ℕ) :
    iteratedDeriv n (volterraConv f g) 0 =
      ∑ j ∈ Finset.range n, iteratedDeriv j f 0 * iteratedDeriv (n - 1 - j) g 0 := by
  rw [iteratedDeriv_volterraConv hf hg]
  simp only [volterraConv_apply_zero, add_zero]

/-- Iterated derivatives of `t f(t)`: `(τ f)^{(n)} = τ f^{(n)} + n f^{(n-1)}`. -/
theorem iteratedDeriv_id_mul_real {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    iteratedDeriv (n + 1) (fun t => t * f t) = fun t =>
      t * iteratedDeriv (n + 1) f t + (n + 1) * iteratedDeriv n f t := by
  have hdf : ∀ k s, HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f s) s := by
    intro k s
    rw [iteratedDeriv_succ]
    exact ((hf.differentiable_iteratedDeriv k (natCast_lt_infty k)) s).hasDerivAt
  induction n with
  | zero =>
    funext t
    rw [iteratedDeriv_one]
    have h := (hasDerivAt_id' t).fun_mul (hdf 0 t)
    rw [iteratedDeriv_zero] at h
    rw [h.deriv, iteratedDeriv_zero]; push_cast; ring
  | succ n ih =>
    funext t
    rw [iteratedDeriv_succ, ih]
    have h := ((hasDerivAt_id' t).fun_mul (hdf (n + 1) t)).fun_add
      ((hdf n t).const_mul ((n : ℝ) + 1))
    rw [h.deriv]; push_cast; ring

end GaloisForLFunctions.HTGeometry
