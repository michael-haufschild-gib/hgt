import GaloisForLFunctions.RHTower.XiSliceHeatTransferPositivity
import GaloisForLFunctions.HTGeometry.HermiteGaussianMomentBounds

/-!
# Hermite representation of the heated slice coefficients

Let `S(t, y) = ξ(½+y+it) ξ(½−y+it)` be the horizontal slice (`xiSliceProduct`) and
`T_n(λ, 0, t)` the heated slice coefficients (`xiSliceHeatTransfer`).  With the Hermite–Gaussians
`g_n(w) = He_n(w) e^{−w²/2}`:

**Theorem** (`integral_hermiteGauss_mul_xiSliceProduct`).  For `λ ≥ 0`, every height `t` and every
order `n`,

  `∫ g_n(w) S(t, √λ w) dw = √(2π) · λ^{n/2} · n! · T_n(λ, 0, t)`.

So the heated coefficient is a Hermite-weighted Gaussian average of the slice along the real axis
of the slice variable.  The slice there is `|ξ(½+y+it)|² ≥ 0`, and `He_n` is positive beyond `2√n`,
so heated positivity reduces to comparing the slice near `y = √λ·w` for large `w` with its size
near the centre.

Proof.  `S(t, y) = ∫∫ Φ(u)Φ(v) e^{it(u+v) + y(u−v)}` (`cosTransform_slice_eq_integral`).  Fubini
(the majorant `|g_n(w)| e^{w²/4} · Φ(u)e^{2λu²} · Φ(v)e^{2λv²}` uses `√λ|w||r| ≤ w²/4 + λr²`) and
the exponential moments `∫ e^{ρw} g_n(w) dw = √(2π) ρⁿ e^{ρ²/2}` at `ρ = √λ(u−v)`
(`integral_exp_mul_hermiteGauss`) give the kernel `√(2π) λ^{n/2} (u−v)ⁿ e^{λ(u−v)²/2}` of
`n!·T_n(λ, 0, t)`.
-/

open Complex MeasureTheory Filter Topology Polynomial
open GaloisForLFunctions.HTGeometry

namespace RHTower.DeBruijn

noncomputable section

/-- The slice of `Ξ` as a double integral over the kernel. -/
theorem xiSliceProduct_eq_integral (t : ℝ) (y : ℂ) :
    xiSliceProduct t y = ∫ p : ℝ × ℝ, ((riemannKernelReal p.1 * riemannKernelReal p.2 : ℝ) : ℂ) *
      cexp (I * t * (p.1 + p.2) + y * (p.1 - p.2)) := by
  rw [← cosTransform_riemannKernel_slice t]
  exact cosTransform_slice_eq_integral riemannKernelReal t y

theorem sqrt_mul_abs_le (lam w r : ℝ) (hlam : 0 ≤ lam) :
    Real.sqrt lam * w * r ≤ w ^ 2 / 4 + lam * r ^ 2 := by
  have hs : Real.sqrt lam ^ 2 = lam := Real.sq_sqrt hlam
  nlinarith [sq_nonneg (w / 2 - Real.sqrt lam * r)]

/-- The triple integrand `g_n(w) Φ(u) Φ(v) e^{it(u+v) + √λ w (u−v)}` is integrable on
`ℝ × ℝ²`. -/
theorem integrable_hermiteKernel {lam : ℝ} (hlam : 0 ≤ lam) (t : ℝ) (n : ℕ) :
    Integrable (Function.uncurry fun (w : ℝ) (p : ℝ × ℝ) => (hermiteGauss n w : ℂ) *
      (((riemannKernelReal p.1 * riemannKernelReal p.2 : ℝ) : ℂ) *
        cexp (I * t * (p.1 + p.2) + ((Real.sqrt lam * w : ℝ) : ℂ) * (p.1 - p.2)))) := by
  set Φ := riemannKernelReal with hΦ
  have hΦ0 : ∀ u, 0 ≤ Φ u := riemannKernel_superExp.nonneg
  set s := Real.sqrt lam with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg lam
  have hs2 : s ^ 2 = lam := Real.sq_sqrt hlam
  -- the integrand on `ℝ × (ℝ × ℝ)`
  set F : ℝ → ℝ × ℝ → ℂ := fun w p => (hermiteGauss n w : ℂ) *
    (((Φ p.1 * Φ p.2 : ℝ) : ℂ) * cexp (I * t * (p.1 + p.2) + ((s * w : ℝ) : ℂ) * (p.1 - p.2)))
    with hF
  -- integrability
  have hker := riemannKernel_superExp.mul_exp_sq (t := 2 * lam) (by positivity)
  have hK1 : Integrable (fun u : ℝ => Φ u * Real.exp (2 * lam * u ^ 2)) := by
    simpa using hker.integrable_mul_exp 0
  have hH : Integrable (fun w : ℝ => ‖(Polynomial.map (Int.castRingHom ℝ) (hermite n)).eval w *
      Real.exp (-(1 / 4 * w ^ 2))‖) :=
    (RHTower.integrable_polyEval_mul_gauss _ (b := 1 / 4) (by norm_num)).norm
  show Integrable (Function.uncurry F)
  refine (hH.mul_prod (hK1.mul_prod hK1)).mono' ?_ (Eventually.of_forall fun z => ?_)
  · refine Continuous.aestronglyMeasurable ?_
    have hc := riemannKernel_superExp.continuous
    have hg : Continuous (hermiteGauss n) := by
      unfold hermiteGauss
      exact (Polynomial.continuous_aeval _).mul (by fun_prop)
    simp only [hF]
    fun_prop
  · obtain ⟨w, u, v⟩ := z
    simp only [Function.uncurry, hF, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hexp : ‖cexp (I * t * ((u : ℂ) + v) + ((s * w : ℝ) : ℂ) * ((u : ℂ) - v))‖ =
        Real.exp (s * w * (u - v)) := by
      rw [Complex.norm_exp]
      congr 1
      simp
    rw [hexp, abs_of_nonneg (hΦ0 u), abs_of_nonneg (hΦ0 v)]
    have hgw : |hermiteGauss n w| * Real.exp (w ^ 2 / 4) =
        |(Polynomial.map (Int.castRingHom ℝ) (hermite n)).eval w| * Real.exp (-(1 / 4 * w ^ 2)) := by
      unfold hermiteGauss
      rw [abs_mul, Real.abs_exp, eval_map, ← algebraMap_int_eq, ← aeval_def, mul_assoc,
        ← Real.exp_add]
      congr 2
      ring
    have hbound : Real.exp (s * w * (u - v)) ≤
        Real.exp (w ^ 2 / 4) * (Real.exp (2 * lam * u ^ 2) * Real.exp (2 * lam * v ^ 2)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have h1 := sqrt_mul_abs_le lam w (u - v) hlam
      rw [← hs] at h1
      nlinarith [sq_nonneg (u + v), mul_nonneg hlam (sq_nonneg (u + v))]
    calc |hermiteGauss n w| * (Φ u * Φ v * Real.exp (s * w * (u - v)))
        ≤ |hermiteGauss n w| * (Φ u * Φ v *
            (Real.exp (w ^ 2 / 4) * (Real.exp (2 * lam * u ^ 2) * Real.exp (2 * lam * v ^ 2)))) := by
          gcongr
          exact mul_nonneg (hΦ0 u) (hΦ0 v)
      _ = (|hermiteGauss n w| * Real.exp (w ^ 2 / 4)) *
            ((Φ u * Real.exp (2 * lam * u ^ 2)) * (Φ v * Real.exp (2 * lam * v ^ 2))) := by ring
      _ = _ := by
          rw [hgw, Real.abs_exp]

/-- **Hermite representation.**  `∫ g_n(w) S(t, √λ w) dw = √(2π) λ^{n/2} n! T_n(λ, 0, t)`. -/
theorem integral_hermiteGauss_mul_xiSliceProduct {lam : ℝ} (hlam : 0 ≤ lam) (t : ℝ) (n : ℕ) :
    ∫ w : ℝ, (hermiteGauss n w : ℂ) * xiSliceProduct t ((Real.sqrt lam * w : ℝ) : ℂ) =
      ((Real.sqrt (2 * Real.pi) * Real.sqrt lam ^ n * n.factorial : ℝ) : ℂ) *
        xiSliceHeatTransfer lam 0 t n := by
  set Φ := riemannKernelReal with hΦ
  have hΦ0 : ∀ u, 0 ≤ Φ u := riemannKernel_superExp.nonneg
  set s := Real.sqrt lam with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg lam
  have hs2 : s ^ 2 = lam := Real.sq_sqrt hlam
  -- the integrand on `ℝ × (ℝ × ℝ)`
  set F : ℝ → ℝ × ℝ → ℂ := fun w p => (hermiteGauss n w : ℂ) *
    (((Φ p.1 * Φ p.2 : ℝ) : ℂ) * cexp (I * t * (p.1 + p.2) + ((s * w : ℝ) : ℂ) * (p.1 - p.2)))
    with hF
  have hLHS : ∫ w : ℝ, (hermiteGauss n w : ℂ) * xiSliceProduct t ((s * w : ℝ) : ℂ) =
      ∫ w : ℝ, ∫ p : ℝ × ℝ, F w p := by
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp only [hF]
    rw [xiSliceProduct_eq_integral, ← integral_const_mul]
  have hInt : Integrable (Function.uncurry F) := integrable_hermiteKernel hlam t n
  rw [hLHS, integral_integral_swap hInt]
  -- the inner integral over `w`
  unfold xiSliceHeatTransfer
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  have hinner : ∀ w : ℝ, F w p = ((Φ p.1 * Φ p.2 : ℝ) : ℂ) * cexp (I * t * (p.1 + p.2)) *
      ((Real.exp ((s * (p.1 - p.2)) * w) * hermiteGauss n w : ℝ) : ℂ) := by
    intro w
    simp only [hF]
    rw [Complex.exp_add]
    push_cast
    rw [show ((s : ℂ) * w * ((p.1 : ℂ) - p.2)) = ((s : ℂ) * ((p.1 : ℂ) - p.2)) * w by ring]
    ring
  simp_rw [hinner]
  rw [integral_const_mul, integral_complex_ofReal, integral_exp_mul_hermiteGauss]
  have hfac : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  have hsq : (s * (p.1 - p.2)) ^ 2 / 2 = lam * (p.1 - p.2) ^ 2 / 2 := by
    rw [mul_pow, hs2]
  rw [hsq]
  simp only [zero_mul, Real.exp_zero, mul_one]
  have hfacC : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  rw [hΦ]
  push_cast
  field_simp
  rw [mul_pow]
  ring

/-- The Hermite–slice integrand `g_n(w) S(t, √λ w)` is integrable. -/
theorem integrable_hermiteGauss_mul_xiSliceProduct {lam : ℝ} (hlam : 0 ≤ lam) (t : ℝ) (n : ℕ) :
    Integrable fun w : ℝ => (hermiteGauss n w : ℂ) * xiSliceProduct t ((Real.sqrt lam * w : ℝ) : ℂ) := by
  have h := (integrable_hermiteKernel hlam t n).integral_prod_left
  refine h.congr (Eventually.of_forall fun w => ?_)
  simp only [Function.uncurry_apply_pair]
  rw [xiSliceProduct_eq_integral, ← integral_const_mul]

end

end RHTower.DeBruijn
