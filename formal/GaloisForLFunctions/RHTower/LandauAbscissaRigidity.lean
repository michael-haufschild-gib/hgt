import Mathlib

/-!
# Landau's abscissa identity for Laplace transforms of nonnegative measures

Mathlib has no Laplace transform.  This file builds the arithmetic core of Landau's theorem on
the abscissa of convergence of a Laplace–Stieltjes transform of a nonnegative measure, in the
exact (`ℝ≥0∞`-valued) form in which no convergence hypothesis is needed at all:

```text
∫_{(0,∞)} e^{-(a-t)u} dν(u) = Σ_{k≥0} (t^k/k!) ∫_{(0,∞)} u^k e^{-au} dν(u),      t ≥ 0.
```

Both sides are elements of `ℝ≥0∞`, so the identity holds *including* the divergent cases.  It
says that the Taylor series of the transform at a real point `a` has radius of convergence
exactly `a - σ_c`, `σ_c` the abscissa; equivalently, the transform cannot be continued
analytically past its abscissa.  This is the engine behind the rigidity theorem: a nonzero
nonnegative deformation of a von Mangoldt measure must place a **real** pole at its abscissa.

The main results are `landau_exchange` (the identity), `laplaceMass_ne_top_of_moments`
(convergence transfer, the direction Landau's theorem is used in), and
`laplaceMoments_eq_top_of_laplaceMass_eq_top` (its converse).
-/

open MeasureTheory Filter Real Set
open scoped ENNReal NNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- The `k`-th Laplace moment of `ν` at the real abscissa `a`, valued in `ℝ≥0∞`. -/
def laplaceMoment (ν : Measure ℝ) (a : ℝ) (k : ℕ) : ℝ≥0∞ :=
  ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (u ^ k * Real.exp (-a * u)) ∂ν

/-- The Laplace–Stieltjes transform of `ν` at the real point `σ`, valued in `ℝ≥0∞`. -/
def laplaceMass (ν : Measure ℝ) (σ : ℝ) : ℝ≥0∞ :=
  ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-σ * u)) ∂ν

section Pointwise

/-- Termwise expansion of the shifted exponential kernel. -/
theorem exp_shift_tsum (a t u : ℝ) :
    Real.exp (-(a - t) * u) = ∑' k : ℕ, t ^ k / (k.factorial : ℝ) * (u ^ k * Real.exp (-a * u)) := by
  have hsplit : Real.exp (-(a - t) * u) = Real.exp (t * u) * Real.exp (-a * u) := by
    rw [← Real.exp_add]; ring_nf
  have hexp : Real.exp (t * u) = ∑' k : ℕ, (t * u) ^ k / (k.factorial : ℝ) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  rw [hsplit, hexp, ← tsum_mul_right]
  exact tsum_congr fun k => by rw [mul_pow]; ring

theorem summable_shift_terms (a t u : ℝ) :
    Summable fun k : ℕ => t ^ k / (k.factorial : ℝ) * (u ^ k * Real.exp (-a * u)) := by
  have h : Summable fun k : ℕ => (t * u) ^ k / (k.factorial : ℝ) := Real.summable_pow_div_factorial (t * u)
  have h2 := h.mul_right (Real.exp (-a * u))
  refine h2.congr fun k => ?_
  rw [mul_pow]; ring

/-- The `ℝ≥0∞` form of the pointwise expansion, valid for every `u ≥ 0` and `t ≥ 0`. -/
theorem ofReal_exp_shift_tsum {a t u : ℝ} (ht : 0 ≤ t) (hu : 0 ≤ u) :
    ENNReal.ofReal (Real.exp (-(a - t) * u))
      = ∑' k : ℕ, ENNReal.ofReal (t ^ k / (k.factorial : ℝ)) *
          ENNReal.ofReal (u ^ k * Real.exp (-a * u)) := by
  have hnn : ∀ k : ℕ, 0 ≤ t ^ k / (k.factorial : ℝ) * (u ^ k * Real.exp (-a * u)) := by
    intro k; positivity
  rw [exp_shift_tsum a t u,
    ENNReal.ofReal_tsum_of_nonneg hnn (summable_shift_terms a t u)]
  refine tsum_congr fun k => ?_
  rw [← ENNReal.ofReal_mul (by positivity)]

end Pointwise

section Measurability

theorem measurable_kernel (a : ℝ) (k : ℕ) :
    Measurable fun u : ℝ => ENNReal.ofReal (u ^ k * Real.exp (-a * u)) := by
  refine ENNReal.measurable_ofReal.comp ?_
  fun_prop

end Measurability

/-- **Landau's exchange identity.**  For every real `a` and every `t ≥ 0`,

```text
∫_{(0,∞)} e^{-(a-t)u} dν = Σ_k (t^k/k!) ∫_{(0,∞)} u^k e^{-au} dν
```

as an identity in `ℝ≥0∞`; in particular no convergence hypothesis is required, and the two sides
are simultaneously finite or infinite. -/
theorem landau_exchange (ν : Measure ℝ) (a t : ℝ) (ht : 0 ≤ t) :
    laplaceMass ν (a - t)
      = ∑' k : ℕ, ENNReal.ofReal (t ^ k / (k.factorial : ℝ)) * laplaceMoment ν a k := by
  have hswap :
      (∑' k : ℕ, ENNReal.ofReal (t ^ k / (k.factorial : ℝ)) * laplaceMoment ν a k)
        = ∫⁻ u in Ioi (0 : ℝ), ∑' k : ℕ, ENNReal.ofReal (t ^ k / (k.factorial : ℝ)) *
            ENNReal.ofReal (u ^ k * Real.exp (-a * u)) ∂ν := by
    rw [MeasureTheory.lintegral_tsum]
    · refine tsum_congr fun k => ?_
      rw [laplaceMoment, MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    · intro k
      exact ((measurable_kernel a k).const_mul _).aemeasurable
  rw [hswap, laplaceMass]
  refine MeasureTheory.setLIntegral_congr_fun measurableSet_Ioi ?_
  intro u hu
  exact ofReal_exp_shift_tsum ht (le_of_lt hu)

/-- **Convergence transfer (the Landau direction).**  If the moment series of `ν` at `a`
converges with radius parameter `t ≥ 0`, then the Laplace transform already converges at
`a - t`.  Contrapositively, the transform cannot be analytically continued past its abscissa. -/
theorem laplaceMass_ne_top_of_moments (ν : Measure ℝ) {a t : ℝ} (ht : 0 ≤ t)
    (h : (∑' k : ℕ, ENNReal.ofReal (t ^ k / (k.factorial : ℝ)) * laplaceMoment ν a k) ≠ ⊤) :
    laplaceMass ν (a - t) ≠ ⊤ := by
  rw [landau_exchange ν a t ht]; exact h

/-- Converse transfer: divergence of the transform at `a - t` forces the moment series to
diverge, i.e. the Taylor radius at `a` is at most `t`. -/
theorem laplaceMoments_eq_top_of_laplaceMass_eq_top (ν : Measure ℝ) {a t : ℝ} (ht : 0 ≤ t)
    (h : laplaceMass ν (a - t) = ⊤) :
    (∑' k : ℕ, ENNReal.ofReal (t ^ k / (k.factorial : ℝ)) * laplaceMoment ν a k) = ⊤ := by
  rw [← landau_exchange ν a t ht]; exact h

section Monotone

/-- The transform of a nonnegative measure is antitone in the abscissa on `(0,∞)`. -/
theorem laplaceMass_antitone (ν : Measure ℝ) {σ τ : ℝ} (h : σ ≤ τ) :
    laplaceMass ν τ ≤ laplaceMass ν σ := by
  refine MeasureTheory.lintegral_mono_ae ?_
  filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (0 : ℝ)))] with u hu
  have hu' : (0 : ℝ) < u := hu
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by nlinarith))

end Monotone

section Abscissa

/-- `IsAbscissa ν c` says that `c` is the abscissa of convergence of the Laplace transform of the
nonnegative measure `ν`: the transform converges strictly to the right of `c` and diverges
strictly to the left. -/
def IsAbscissa (ν : Measure ℝ) (c : ℝ) : Prop :=
  (∀ σ : ℝ, c < σ → laplaceMass ν σ ≠ ⊤) ∧ (∀ σ : ℝ, σ < c → laplaceMass ν σ = ⊤)

/-- **The Taylor radius at a real point equals the distance to the abscissa: convergence side.**
For `a` to the right of the abscissa `c`, the moment series at `a` converges for every radius
parameter below `a - c`. -/
theorem moments_ne_top_of_lt_abscissaDist {ν : Measure ℝ} {c a t : ℝ}
    (hc : IsAbscissa ν c) (ht : 0 ≤ t) (hlt : t < a - c) :
    (∑' k : ℕ, ENNReal.ofReal (t ^ k / (k.factorial : ℝ)) * laplaceMoment ν a k) ≠ ⊤ := by
  rw [← landau_exchange ν a t ht]
  exact hc.1 (a - t) (by linarith)

/-- **The Taylor radius at a real point equals the distance to the abscissa: divergence side.**
Beyond `a - c` the moment series diverges, so the radius is exactly `a - c` and the transform has
no analytic continuation to a disc about `a` of radius larger than `a - c`. -/
theorem moments_eq_top_of_gt_abscissaDist {ν : Measure ℝ} {c a t : ℝ}
    (hc : IsAbscissa ν c) (ht : 0 ≤ t) (hgt : a - c < t) :
    (∑' k : ℕ, ENNReal.ofReal (t ^ k / (k.factorial : ℝ)) * laplaceMoment ν a k) = ⊤ := by
  rw [← landau_exchange ν a t ht]
  exact hc.2 (a - t) (by linarith)

end Abscissa

section Domination

/-- The modulus of the complex Laplace kernel is the real kernel at the same real part. -/
theorem norm_cexp_neg_mul (z : ℂ) (u : ℝ) :
    ‖Complex.exp (-z * (u : ℂ))‖ = Real.exp (-z.re * u) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

/-- **Domination by the real point.**  For a nonnegative measure, the complex Laplace transform is
bounded in modulus by the real transform at the same real part.  This is the inequality
`|N(z)| ≤ N(Re z)`, which forces an entire transform of a nonnegative measure with vanishing real
limits to be a bounded entire function, hence constant. -/
theorem norm_complexLaplace_le (ν : Measure ℝ) (z : ℂ) :
    ‖∫ u in Ioi (0 : ℝ), Complex.exp (-z * (u : ℂ)) ∂ν‖
      ≤ ∫ u in Ioi (0 : ℝ), Real.exp (-z.re * u) ∂ν := by
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  exact integral_congr_ae (Eventually.of_forall fun u => norm_cexp_neg_mul z u)

end Domination

end GaloisForLFunctions.RHTower
