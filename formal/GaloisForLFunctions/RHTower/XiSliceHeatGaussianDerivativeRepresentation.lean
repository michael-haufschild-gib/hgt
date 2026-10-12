import GaloisForLFunctions.RHTower.XiSliceHeatHermiteRepresentation

/-!
# The heated slice coefficients as Gaussian averages of slice derivatives

Let `S(t, x) = ξ(½+x+it) ξ(½−x+it)` and `T_n(λ, 0, t)` the heated slice coefficients
(`xiSliceHeatTransfer`), i.e. the `n`-th Taylor coefficient at `0` of `e^{(λ/2)∂ₓ²} S(t, ·)`.

**Theorem** (`xiSliceHeatTransfer_eq_integral_iteratedDeriv`).  For `λ ≥ 0`,

  `√(2π) · T_n(λ, 0, t) = ∫ e^{−w²/2} · S^{(n)}(t, √λ w)/n! dw`,

so `T_n(λ, 0, t) = E[S^{(n)}(t, √λ Z)]/n!` for a standard Gaussian `Z`: the heat in the slice
variable averages the Taylor coefficients of the slice over the real centres `√λ Z`.

Proof.  At a real centre `x₀` the Taylor coefficient is the kernel moment
`∫∫ Φ(u)Φ(v) e^{x₀(u−v)} (u−v)ⁿ/n! e^{it(u+v)}` (`kernelSliceMoment_eq_iteratedDeriv`).  Fubini (the
majorant `e^{−w²/4} · Φ(u)e^{(2λ+1)u²} · Φ(v)e^{(2λ+1)v²}` uses `√λ|w||r| ≤ w²/4 + λr²` and
`|r|ⁿ/n! ≤ e^{|r|}`) and `∫ e^{ρw} e^{−w²/2} dw = √(2π) e^{ρ²/2}` at `ρ = √λ(u−v)`
(`integral_exp_mul_gauss`) give the kernel `√(2π) e^{λ(u−v)²/2} (u−v)ⁿ/n!` of `T_n(λ, 0, t)`.
-/

open Complex MeasureTheory Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower.DeBruijn

noncomputable section

theorem pow_div_factorial_le_exp_abs (r : ℝ) (n : ℕ) :
    |r| ^ n / n.factorial ≤ Real.exp |r| := by
  have h := Real.pow_div_factorial_le_exp |r| (abs_nonneg r) n
  simpa using h

/-- The triple integrand `e^{−w²/2} Φ(u)Φ(v) e^{√λ w (u−v)} (u−v)ⁿ/n! e^{it(u+v)}` is integrable on
`ℝ × ℝ²`. -/
theorem integrable_gaussKernelMoment {lam : ℝ} (hlam : 0 ≤ lam) (t : ℝ) (n : ℕ) :
    Integrable (Function.uncurry fun (w : ℝ) (p : ℝ × ℝ) =>
      ((Real.exp (-(w ^ 2 / 2)) : ℝ) : ℂ) *
        (((riemannKernelReal p.1 * riemannKernelReal p.2 *
          Real.exp ((Real.sqrt lam * w) * (p.1 - p.2)) * ((p.1 - p.2) ^ n / n.factorial) : ℝ) : ℂ)
          * cexp (I * t * (p.1 + p.2)))) := by
  set Φ := riemannKernelReal with hΦ
  have hΦ0 : ∀ u, 0 ≤ Φ u := riemannKernel_superExp.nonneg
  set s := Real.sqrt lam with hs
  have hker := riemannKernel_superExp.mul_exp_sq (t := 2 * lam + 1) (by positivity)
  have hK1 : Integrable (fun u : ℝ => Φ u * Real.exp ((2 * lam + 1) * u ^ 2)) := by
    simpa using hker.integrable_mul_exp 0
  have hG : Integrable (fun w : ℝ => Real.exp 2 * Real.exp (-(1 / 4) * w ^ 2)) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 4)).const_mul _
  refine (hG.mul_prod (hK1.mul_prod hK1)).mono' ?_ (Eventually.of_forall fun z => ?_)
  · refine Continuous.aestronglyMeasurable ?_
    have hc := riemannKernel_superExp.continuous
    fun_prop
  · obtain ⟨w, u, v⟩ := z
    simp only [Function.uncurry, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [norm_cexp_I_mul_ofReal_add, mul_one, abs_of_nonneg (Real.exp_pos _).le]
    have hpoly : |(u - v) ^ n / (n.factorial : ℝ)| ≤ Real.exp |u - v| := by
      rw [abs_div, abs_pow, Nat.abs_cast]
      exact pow_div_factorial_le_exp_abs _ n
    have habs : |u - v| ≤ 2 + u ^ 2 + v ^ 2 := by
      have h1 := abs_sub (u) (v)
      have h2 : |u| ≤ 1 + u ^ 2 := by nlinarith [abs_nonneg u, sq_abs u, sq_nonneg (|u| - 1)]
      have h3 : |v| ≤ 1 + v ^ 2 := by nlinarith [abs_nonneg v, sq_abs v, sq_nonneg (|v| - 1)]
      linarith
    have hbound : Real.exp (-(w ^ 2 / 2)) * Real.exp (s * w * (u - v)) * Real.exp |u - v|
        ≤ (Real.exp 2 * Real.exp (-(1 / 4) * w ^ 2))
          * (Real.exp ((2 * lam + 1) * u ^ 2) * Real.exp ((2 * lam + 1) * v ^ 2)) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have h1 := sqrt_mul_abs_le lam w (u - v) hlam
      rw [← hs] at h1
      nlinarith [sq_nonneg (u + v), mul_nonneg hlam (sq_nonneg (u + v))]
    rw [abs_of_nonneg (hΦ0 u), abs_of_nonneg (hΦ0 v), Real.abs_exp]
    calc Real.exp (-(w ^ 2 / 2)) * (Φ u * Φ v * Real.exp (s * w * (u - v))
          * |(u - v) ^ n / (n.factorial : ℝ)|)
        ≤ Real.exp (-(w ^ 2 / 2)) * (Φ u * Φ v * Real.exp (s * w * (u - v)) * Real.exp |u - v|) := by
          gcongr
          exact mul_nonneg (mul_nonneg (hΦ0 u) (hΦ0 v)) (Real.exp_pos _).le
      _ = Φ u * Φ v * (Real.exp (-(w ^ 2 / 2)) * Real.exp (s * w * (u - v)) * Real.exp |u - v|) := by
          ring
      _ ≤ Φ u * Φ v * ((Real.exp 2 * Real.exp (-(1 / 4) * w ^ 2))
          * (Real.exp ((2 * lam + 1) * u ^ 2) * Real.exp ((2 * lam + 1) * v ^ 2))) :=
          mul_le_mul_of_nonneg_left hbound (mul_nonneg (hΦ0 u) (hΦ0 v))
      _ = _ := by ring

/-- **Gaussian average of the kernel moments.**
`∫ e^{−w²/2} M_n(Φ, √λ w, t) dw = √(2π) T_n(λ, 0, t)`. -/
theorem integral_gauss_mul_kernelSliceMoment {lam : ℝ} (hlam : 0 ≤ lam) (t : ℝ) (n : ℕ) :
    ∫ w : ℝ, ((Real.exp (-(w ^ 2 / 2)) : ℝ) : ℂ)
        * kernelSliceMoment riemannKernelReal (Real.sqrt lam * w) t n
      = ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * xiSliceHeatTransfer lam 0 t n := by
  set Φ := riemannKernelReal with hΦ
  set s := Real.sqrt lam with hs
  have hs2 : s ^ 2 = lam := Real.sq_sqrt hlam
  set F : ℝ → ℝ × ℝ → ℂ := fun w p => ((Real.exp (-(w ^ 2 / 2)) : ℝ) : ℂ) *
    (((Φ p.1 * Φ p.2 * Real.exp ((s * w) * (p.1 - p.2)) * ((p.1 - p.2) ^ n / n.factorial) : ℝ) : ℂ)
      * cexp (I * t * (p.1 + p.2))) with hF
  have hLHS : ∫ w : ℝ, ((Real.exp (-(w ^ 2 / 2)) : ℝ) : ℂ) * kernelSliceMoment Φ (s * w) t n =
      ∫ w : ℝ, ∫ p : ℝ × ℝ, F w p := by
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp only [hF, kernelSliceMoment]
    rw [← integral_const_mul]
  have hInt : Integrable (Function.uncurry F) := integrable_gaussKernelMoment hlam t n
  rw [hLHS, integral_integral_swap hInt]
  unfold xiSliceHeatTransfer
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  have hinner : ∀ w : ℝ, F w p = ((Φ p.1 * Φ p.2 * ((p.1 - p.2) ^ n / n.factorial) : ℝ) : ℂ)
      * cexp (I * t * (p.1 + p.2))
      * ((Real.exp ((s * (p.1 - p.2)) * w) * Real.exp (-(w ^ 2 / 2)) : ℝ) : ℂ) := by
    intro w
    simp only [hF]
    push_cast
    rw [show ((s : ℂ) * w * ((p.1 : ℂ) - p.2)) = ((s : ℂ) * ((p.1 : ℂ) - p.2)) * w by ring]
    ring
  simp_rw [hinner]
  rw [integral_const_mul, integral_complex_ofReal]
  have hgauss := integral_exp_mul_gauss (s * (p.1 - p.2))
  rw [show (∫ w : ℝ, Real.exp (s * (p.1 - p.2) * w) * Real.exp (-(w ^ 2 / 2)))
      = ∫ w : ℝ, Real.exp (s * (p.1 - p.2) * w) * Real.exp (-(w ^ 2 / 2)) from rfl] at hgauss ⊢
  rw [hgauss]
  have hsq : (s * (p.1 - p.2)) ^ 2 / 2 = lam * (p.1 - p.2) ^ 2 / 2 := by
    rw [mul_pow, hs2]
  rw [hsq]
  simp only [zero_mul, Real.exp_zero, mul_one]
  rw [hΦ]
  push_cast
  ring

/-- **Gaussian-derivative representation.**  `√(2π) T_n(λ, 0, t) = ∫ e^{−w²/2} S^{(n)}(t, √λ w)/n! dw`. -/
theorem xiSliceHeatTransfer_eq_integral_iteratedDeriv {lam : ℝ} (hlam : 0 ≤ lam) (t : ℝ) (n : ℕ) :
    ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * xiSliceHeatTransfer lam 0 t n
      = ∫ w : ℝ, ((Real.exp (-(w ^ 2 / 2)) : ℝ) : ℂ)
        * (iteratedDeriv n (xiSliceProduct t) ((Real.sqrt lam * w : ℝ) : ℂ) / n.factorial) := by
  rw [← integral_gauss_mul_kernelSliceMoment hlam t n]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only
  rw [kernelSliceMoment_eq_iteratedDeriv riemannKernel_superExp, cosTransform_riemannKernel_slice]

end

end RHTower.DeBruijn
