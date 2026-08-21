import GaloisForLFunctions.HTGeometry.DaiYoshikawa.SpectralZetaMellin

/-!
# The Mellin representation of the spectral zeta function

Summing the scaled Gamma integral `∫_0^∞ e^{−λt} t^{s−1} dt = Γ(s) λ^{−s}` over a spectrum turns the
spectral zeta function into a Mellin transform of the heat trace:

```text
Γ(s) Σ_n λ_n^{−s} = ∫_0^∞ ( Σ_n e^{−λ_n t} ) t^{s−1} dt ,
```

valid whenever `Σ_n λ_n^{−s}` converges.  This is the identity underlying the definition of analytic
torsion in Section 3.1 of Dai–Yoshikawa, *Degeneration of Riemann surfaces and small eigenvalues of
the Laplacian* (arXiv:2509.06151v2).

The interchange of sum and integral is legitimate because the integrands are nonnegative and the
integrals of their norms are exactly the terms `Γ(s) λ_n^{−s}` of the convergent series.
-/

open MeasureTheory Set Real

namespace GaloisForLFunctions.HTGeometry.DaiYoshikawa

/-- The scaled Gamma integrand is integrable on `(0,∞)`. -/
theorem integrableOn_exp_neg_mul_rpow {lam s : ℝ} (hlam : 0 < lam) (hs : 0 < s) :
    IntegrableOn (fun t => Real.exp (-(lam * t)) * t ^ (s - 1)) (Ioi (0 : ℝ)) volume := by
  have hbase : IntegrableOn (fun y : ℝ => Real.exp (-y) * y ^ (s - 1)) (Ioi (0 : ℝ)) volume :=
    Real.GammaIntegral_convergent hs
  have hscaled : IntegrableOn
      (fun x : ℝ => Real.exp (-(lam * x)) * (lam * x) ^ (s - 1)) (Ioi (0 : ℝ)) volume := by
    have h := (integrableOn_Ioi_comp_mul_left_iff
      (fun y : ℝ => Real.exp (-y) * y ^ (s - 1)) 0 hlam).mpr (by simpa using hbase)
    simpa using h
  have hfactor : IntegrableOn
      (fun x : ℝ => lam ^ (s - 1) * (Real.exp (-(lam * x)) * x ^ (s - 1)))
      (Ioi (0 : ℝ)) volume := by
    refine hscaled.congr_fun (fun x hx => ?_) measurableSet_Ioi
    have hx0 : (0 : ℝ) < x := hx
    show Real.exp (-(lam * x)) * (lam * x) ^ (s - 1)
      = lam ^ (s - 1) * (Real.exp (-(lam * x)) * x ^ (s - 1))
    rw [Real.mul_rpow hlam.le hx0.le]
    ring
  have hne : lam ^ (s - 1) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hlam _)
  have hinv : IntegrableOn
      (fun x : ℝ => (lam ^ (s - 1))⁻¹ * (lam ^ (s - 1) * (Real.exp (-(lam * x)) * x ^ (s - 1))))
      (Ioi (0 : ℝ)) volume := hfactor.const_mul _
  refine hinv.congr_fun (fun x _ => ?_) measurableSet_Ioi
  show (lam ^ (s - 1))⁻¹ * (lam ^ (s - 1) * (Real.exp (-(lam * x)) * x ^ (s - 1)))
    = Real.exp (-(lam * x)) * x ^ (s - 1)
  field_simp

/-- The integral of the norm of the scaled Gamma integrand. -/
theorem integral_norm_exp_neg_mul_rpow {lam s : ℝ} (hlam : 0 < lam) (hs : 0 < s) :
    (∫ t in Ioi (0 : ℝ), ‖Real.exp (-(lam * t)) * t ^ (s - 1)‖) = Real.Gamma s / lam ^ s := by
  have hcongr : ∀ t ∈ Ioi (0 : ℝ),
      ‖Real.exp (-(lam * t)) * t ^ (s - 1)‖ = Real.exp (-(lam * t)) * t ^ (s - 1) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg ht0.le _))]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hcongr,
    integral_exp_neg_mul_rpow hlam hs]

/-- **The Mellin representation of the spectral zeta function.**

`Γ(s) Σ_n λ_n^{−s} = ∫_0^∞ Σ_n e^{−λ_n t} t^{s−1} dt` for a positive spectrum whose zeta series
converges. -/
theorem gamma_mul_tsum_rpow_neg {lam : ℕ → ℝ} {s : ℝ} (hs : 0 < s)
    (hpos : ∀ n, 0 < lam n) (hsum : Summable fun n => lam n ^ (-s)) :
    Real.Gamma s * ∑' n, lam n ^ (-s)
      = ∫ t in Ioi (0 : ℝ), ∑' n, Real.exp (-(lam n * t)) * t ^ (s - 1) := by
  have hint : ∀ n, IntegrableOn (fun t => Real.exp (-(lam n * t)) * t ^ (s - 1))
      (Ioi (0 : ℝ)) volume := fun n => integrableOn_exp_neg_mul_rpow (hpos n) hs
  have hnormsum : Summable fun n =>
      ∫ t in Ioi (0 : ℝ), ‖Real.exp (-(lam n * t)) * t ^ (s - 1)‖ := by
    refine (hsum.mul_left (Real.Gamma s)).congr fun n => ?_
    rw [integral_norm_exp_neg_mul_rpow (hpos n) hs, Real.rpow_neg (hpos n).le]
    field_simp
  have hswap := integral_tsum_of_summable_integral_norm hint hnormsum
  rw [← hswap]
  have hterm : ∀ n, (∫ t in Ioi (0 : ℝ), Real.exp (-(lam n * t)) * t ^ (s - 1))
      = Real.Gamma s * lam n ^ (-s) := fun n =>
    (gamma_mul_rpow_neg_eq_integral (hpos n) hs).symm
  rw [tsum_congr hterm, tsum_mul_left]


/-- **The Mellin identity in heat-trace form.**

`Γ(s) ζ(s) = ∫_0^∞ Θ(t) t^{s−1} dt` with `Θ(t) = Σ_n e^{−λ_n t}` the heat trace of a strictly
positive spectrum. -/
theorem gamma_mul_tsum_rpow_neg_heatTrace {lam : ℕ → ℝ} {s : ℝ} (hs : 0 < s)
    (hpos : ∀ n, 0 < lam n) (hsum : Summable fun n => lam n ^ (-s)) :
    Real.Gamma s * ∑' n, lam n ^ (-s)
      = ∫ t in Ioi (0 : ℝ), (∑' n, Real.exp (-(lam n * t))) * t ^ (s - 1) := by
  rw [gamma_mul_tsum_rpow_neg hs hpos hsum]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  exact tsum_mul_right

end GaloisForLFunctions.HTGeometry.DaiYoshikawa
