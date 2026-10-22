import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmFredholmRangeDivisor

/-!
# The literal integer Mellin expansion of the source primitive

A theta-type source is one presented by its integer series

`k(x) = e^{x/2} ∑_{n ≥ 1} h(n e^x)`.

For such a source the tail of the tilted primitive expands termwise on the actual integers:

`∫_x^∞ k(y) e^{i z y} dy = ∑_{n ≥ 1} n^{-s(z)} H_s^tail(n e^x)`,

with `s(z) = 1/2 + i z` and the incomplete Mellin tail
`H_s^tail(X) = ∫_X^∞ h(t) t^{s-1} dt`.  Unlike the completed scalar transform each term retains the
scale cutoff `n e^x`.

The single-term identity is the exponential change of variables `t = n e^y`; the interchange of the
sum with the integral is the hypothesis `integral_tsum` needs.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace HedenmalmThetaSeries

open HedenmalmQuantile HedenmalmPrimeTranslation

/-- The incomplete Mellin tail `H_s^tail(X) = ∫_X^∞ h(t) t^{s-1} dt`, written with the exponential
form of the power so that no branch choice is involved on the positive axis. -/
def mellinTail (h : ℝ → ℂ) (s : ℂ) (X : ℝ) : ℂ :=
  ∫ t in Ioi X, h t * Complex.exp ((s - 1) * ((Real.log t : ℝ) : ℂ))

/-- The scaled exponential chart `y ↦ c e^y`. -/
theorem image_expChart {c : ℝ} (hc : 0 < c) (x : ℝ) :
    (fun y : ℝ => c * Real.exp y) '' Ioi x = Ioi (c * Real.exp x) := by
  ext t
  simp only [mem_image, mem_Ioi]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr hy) hc
  · intro ht
    refine ⟨Real.log (t / c), ?_, ?_⟩
    · have hpos : 0 < t / c := by
        have : 0 < t := lt_trans (by positivity) ht
        positivity
      have hgt : Real.exp x < t / c := by
        rw [lt_div_iff₀ hc, mul_comm]
        exact ht
      have := Real.log_lt_log (Real.exp_pos x) hgt
      rwa [Real.log_exp] at this
    · rw [Real.exp_log (by
        have : 0 < t := lt_trans (by positivity) ht
        positivity)]
      field_simp

theorem injOn_expChart {c : ℝ} (hc : 0 < c) (x : ℝ) :
    InjOn (fun y : ℝ => c * Real.exp y) (Ioi x) := by
  intro a _ b _ hab
  have hmul : c * Real.exp a = c * Real.exp b := hab
  exact Real.exp_eq_exp.mp (mul_left_cancel₀ hc.ne' hmul)

/-- **The single-term change of variables `t = c e^y`.** -/
theorem mellinTail_expChart (h : ℝ → ℂ) (s : ℂ) {c : ℝ} (hc : 0 < c) (x : ℝ) :
    mellinTail h s (c * Real.exp x)
      = Complex.exp (s * ((Real.log c : ℝ) : ℂ))
        * ∫ y in Ioi x, h (c * Real.exp y) * Complex.exp (s * (y : ℂ)) := by
  have hderiv : ∀ y ∈ Ioi x,
      HasDerivWithinAt (fun y : ℝ => c * Real.exp y) (c * Real.exp y) (Ioi x) y := by
    intro y _
    exact ((Real.hasDerivAt_exp y).const_mul c).hasDerivWithinAt
  have hchange := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi hderiv (injOn_expChart hc x)
    (fun t => h t * Complex.exp ((s - 1) * ((Real.log t : ℝ) : ℂ)))
  rw [image_expChart hc x] at hchange
  rw [mellinTail, hchange, ← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
  have hcy : (0 : ℝ) < c * Real.exp y := by positivity
  have hlog : Real.log (c * Real.exp y) = Real.log c + y := by
    rw [Real.log_mul hc.ne' (Real.exp_ne_zero y), Real.log_exp]
  have habs : |c * Real.exp y| = c * Real.exp y := abs_of_pos hcy
  rw [habs, hlog, Complex.real_smul]
  push_cast
  rw [show ((c : ℂ) * Complex.exp (y : ℂ)) * (h (c * Real.exp y)
        * Complex.exp ((s - 1) * ((Real.log c : ℝ) + (y : ℂ))))
      = h (c * Real.exp y) * (((c : ℂ) * Complex.exp (y : ℂ))
        * Complex.exp ((s - 1) * ((Real.log c : ℝ) + (y : ℂ)))) by ring]
  rw [show Complex.exp (s * ((Real.log c : ℝ) : ℂ))
        * (h (c * Real.exp y) * Complex.exp (s * (y : ℂ)))
      = h (c * Real.exp y) * (Complex.exp (s * ((Real.log c : ℝ) : ℂ))
        * Complex.exp (s * (y : ℂ))) by ring]
  congr 1
  have hcexp : (c : ℂ) = Complex.exp (((Real.log c : ℝ) : ℂ)) := by
    rw [← Complex.ofReal_exp, Real.exp_log hc]
  rw [hcexp, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

/-- A source presented by its integer theta series. -/
structure ThetaSeriesSource where
  base : PositiveDensitySource
  h : ℝ → ℂ
  series : ∀ x : ℝ, ((base.k x : ℝ) : ℂ)
    = Complex.exp ((x : ℂ) / 2) * ∑' n : ℕ, h (((n : ℝ) + 1) * Real.exp x)

/-- **The literal integer Mellin expansion.**  The tail of the tilted primitive is the sum over the
actual integers of the incomplete Mellin tails, each with its own scale cutoff `n e^x`. -/
theorem tail_eq_tsum_mellinTail (T : ThetaSeriesSource) (z : ℂ) (x : ℝ)
    (hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun y : ℝ => T.h (((n : ℝ) + 1) * Real.exp y)
        * Complex.exp (dirichletExponent z * (y : ℂ)))
      (volume.restrict (Ioi x)))
    (hsum : ∑' n : ℕ, ∫⁻ y in Ioi x,
      ‖T.h (((n : ℝ) + 1) * Real.exp y)
        * Complex.exp (dirichletExponent z * (y : ℂ))‖ₑ ≠ ⊤) :
    (∫ y in Ioi x, ((T.base.k y : ℝ) : ℂ) * sourceChar z y)
      = ∑' n : ℕ, Complex.exp (-(dirichletExponent z * ((Real.log ((n : ℝ) + 1) : ℝ) : ℂ)))
        * mellinTail T.h (dirichletExponent z) (((n : ℝ) + 1) * Real.exp x) := by
  have hpt : ∀ y : ℝ, ((T.base.k y : ℝ) : ℂ) * sourceChar z y
      = ∑' n : ℕ, T.h (((n : ℝ) + 1) * Real.exp y)
        * Complex.exp (dirichletExponent z * (y : ℂ)) := by
    intro y
    rw [T.series y, sourceChar, tsum_mul_right]
    rw [show Complex.exp ((y : ℂ) / 2) * (∑' n : ℕ, T.h (((n : ℝ) + 1) * Real.exp y))
          * Complex.exp (Complex.I * z * (y : ℂ))
        = (∑' n : ℕ, T.h (((n : ℝ) + 1) * Real.exp y))
          * (Complex.exp ((y : ℂ) / 2) * Complex.exp (Complex.I * z * (y : ℂ))) from by ring]
    congr 1
    rw [← Complex.exp_add, dirichletExponent]
    congr 1
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun y _ => hpt y)]
  rw [MeasureTheory.integral_tsum hmeas hsum]
  refine tsum_congr fun n => ?_
  have hc : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [mellinTail_expChart T.h (dirichletExponent z) hc x, ← mul_assoc, ← Complex.exp_add]
  simp

end HedenmalmThetaSeries

end

end RHTower
