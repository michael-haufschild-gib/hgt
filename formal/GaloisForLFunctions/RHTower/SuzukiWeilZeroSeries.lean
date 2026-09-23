import GaloisForLFunctions.RHTower.XiGuinandWeilExplicitFormula
import GaloisForLFunctions.RHTower.CCMQuartetPaleyWiener
import GaloisForLFunctions.RHTower.XiHadamardFactorization
import GaloisForLFunctions.RHTower.CCMRectangularTwoEdge

/-!
# Suzuki's Xi-zero series `P_t(z)` and its Laplace transform

Suzuki, *On the Hilbert space derived from the Weil distribution* (arXiv:2301.00421v3), equation
(3.2), defines

```text
P_t(z) = ∑_{γ ∈ Γ} m_γ ((e^{-iγt} - 1)/γ) · 1/(z - γ),      t ≥ 0.
```

This module defines it over the corpus's multiplicity-exact divisor `XiZeroCopy`, proves the
absolute convergence and the exponential growth bound `‖P_t(z)‖ ≪_z e^{|t|/2}`, and computes its
**Laplace transform in `t`** in closed form:

```text
∫_0^∞ P_t(z) e^{-σt} dt = (T(-iσ) - T(-z)) / (σ (iσ - z)),        σ > 1/2,
```

where `T = xiRelativeResolventTrace` is the corpus's regularized Cauchy trace over the divisor.
The point is that the right-hand side is *absolutely convergent* and is exactly the object the
corpus's Guinand--Weil explicit formula
(`continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace`) evaluates in prime and
archimedean terms.  Both base points `-iσ` and `-z` land in the corpus's admissible region, which is
why the functional-equation reflection `xiZeroCopyReflectEquiv` is applied to the divisor before the
partial-fraction split.

Everything here is unconditional.
-/

open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.RHTower

namespace RHTower
noncomputable section

/-! ## The Xi-zero series `P_t(z)` of Suzuki eq. (3.2) -/

/-- The `q`-th summand of Suzuki eq. (3.2). -/
def suzukiPtZeroTerm (t : ℝ) (z : ℂ) (q : XiZeroCopy) : ℂ :=
  (Complex.exp (-(I * xiSpectralPoint q * (t : ℂ))) - 1) /
    (xiSpectralPoint q * (z - xiSpectralPoint q))

/-- **Suzuki eq. (3.2).**  The multiplicity-exact Xi-zero series `P_t(z)`. -/
def suzukiPtZeroSum (t : ℝ) (z : ℂ) : ℂ := ∑' q : XiZeroCopy, suzukiPtZeroTerm t z q

/-- The reciprocal resolvent product is summable over the divisor, for every base point. -/
theorem summable_xiResolventProduct (z : ℂ) :
    Summable (fun q : XiZeroCopy => (xiSpectralPoint q * (xiSpectralPoint q - z))⁻¹) := by
  rcases eq_or_ne z 0 with rfl | hz
  · have h : Summable (fun q : XiZeroCopy => 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) :=
      xiSpectralPoint_inv_sq_summable
    refine Summable.of_norm (h.congr fun q => ?_)
    rw [sub_zero, norm_inv, norm_mul, sq, one_div]
  · have hbase := summable_xi_relativeResolventTerms z
    refine (hbase.mul_left (-1 / z)).congr fun q => ?_
    set w : ℂ := xiSpectralPoint q * (xiSpectralPoint q - z) with hw
    rw [div_eq_mul_inv (-z) w, ← mul_assoc]
    have hcoef : (-1 / z) * (-z) = 1 := by field_simp
    rw [hcoef, one_mul]

/-- The exponential factor of the zero series is bounded by `e^{|t|/2}`. -/
theorem norm_suzukiPtZeroExp_le (t : ℝ) (q : XiZeroCopy) :
    ‖Complex.exp (-(I * xiSpectralPoint q * (t : ℂ)))‖ ≤ Real.exp (|t| / 2) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hstrip : |(I * xiSpectralPoint q).re| < (1 / 2 : ℝ) :=
    abs_re_I_mul_xiSpectralPoint_le_half q
  have hre : (-(I * xiSpectralPoint q * (t : ℂ))).re
      = -((I * xiSpectralPoint q).re * t) := by
    simp [Complex.mul_re]
  rw [hre]
  have h1 : -((I * xiSpectralPoint q).re * t) ≤ |(I * xiSpectralPoint q).re * t| :=
    neg_le_abs _
  have h2 : |(I * xiSpectralPoint q).re * t| ≤ (1 / 2 : ℝ) * |t| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hstrip.le (abs_nonneg t)
  linarith

/-- Termwise norm bound of the Xi-zero series. -/
theorem norm_suzukiPtZeroTerm_le (t : ℝ) (z : ℂ) (q : XiZeroCopy) :
    ‖suzukiPtZeroTerm t z q‖ ≤
      (Real.exp (|t| / 2) + 1) * ‖(xiSpectralPoint q * (xiSpectralPoint q - z))⁻¹‖ := by
  have hden : xiSpectralPoint q * (z - xiSpectralPoint q)
      = -(xiSpectralPoint q * (xiSpectralPoint q - z)) := by ring
  rw [suzukiPtZeroTerm, div_eq_mul_inv, hden, inv_neg, mul_neg, norm_neg, norm_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  calc ‖Complex.exp (-(I * xiSpectralPoint q * (t : ℂ))) - 1‖
      ≤ ‖Complex.exp (-(I * xiSpectralPoint q * (t : ℂ)))‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ ≤ Real.exp (|t| / 2) + 1 := by
        have := norm_suzukiPtZeroExp_le t q
        simp only [norm_one]
        linarith

theorem summable_xiResolventProduct_norm (z : ℂ) :
    Summable (fun q : XiZeroCopy => ‖(xiSpectralPoint q * (xiSpectralPoint q - z))⁻¹‖) :=
  summable_norm_iff.mpr (summable_xiResolventProduct z)

theorem summable_suzukiPtZeroTerm (t : ℝ) (z : ℂ) : Summable (suzukiPtZeroTerm t z) := by
  have hn : Summable (fun q : XiZeroCopy =>
      (Real.exp (|t| / 2) + 1) * ‖(xiSpectralPoint q * (xiSpectralPoint q - z))⁻¹‖) :=
    (summable_xiResolventProduct_norm z).mul_left _
  exact Summable.of_norm_bounded hn (norm_suzukiPtZeroTerm_le t z)

/-- Exponential growth bound for the zero series. -/
theorem norm_suzukiPtZeroSum_le (t : ℝ) (z : ℂ) :
    ‖suzukiPtZeroSum t z‖ ≤ (Real.exp (|t| / 2) + 1) *
      ∑' q : XiZeroCopy, ‖(xiSpectralPoint q * (xiSpectralPoint q - z))⁻¹‖ := by
  have hn : Summable (fun q : XiZeroCopy =>
      (Real.exp (|t| / 2) + 1) * ‖(xiSpectralPoint q * (xiSpectralPoint q - z))⁻¹‖) :=
    (summable_xiResolventProduct_norm z).mul_left _
  have hnorm : Summable (fun q : XiZeroCopy => ‖suzukiPtZeroTerm t z q‖) :=
    (summable_suzukiPtZeroTerm t z).norm
  calc ‖suzukiPtZeroSum t z‖
      ≤ ∑' q : XiZeroCopy, ‖suzukiPtZeroTerm t z q‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' q : XiZeroCopy,
          (Real.exp (|t| / 2) + 1) * ‖(xiSpectralPoint q * (xiSpectralPoint q - z))⁻¹‖ :=
        Summable.tsum_le_tsum (norm_suzukiPtZeroTerm_le t z) hnorm hn
    _ = (Real.exp (|t| / 2) + 1) *
          ∑' q : XiZeroCopy, ‖(xiSpectralPoint q * (xiSpectralPoint q - z))⁻¹‖ :=
        (summable_xiResolventProduct_norm z).tsum_mul_left _


/-! ## The Laplace transform of the Xi-zero series -/

/-- The Laplace integrand of one divisor copy, split into two exponential rays. -/
theorem suzukiPtZeroLaplaceTerm_eq (σ : ℝ) (z : ℂ) (q : XiZeroCopy) (t : ℝ) :
    suzukiPtZeroTerm t z q * Complex.exp (-((σ : ℂ) * (t : ℂ)))
      = (xiSpectralPoint q * (z - xiSpectralPoint q))⁻¹ *
          (Complex.exp (-((I * xiSpectralPoint q + (σ : ℂ)) * (t : ℂ)))
            - Complex.exp (-((σ : ℂ) * (t : ℂ)))) := by
  rw [suzukiPtZeroTerm, div_eq_mul_inv,
    show -((I * xiSpectralPoint q + (σ : ℂ)) * (t : ℂ))
      = -(I * xiSpectralPoint q * (t : ℂ)) + -((σ : ℂ) * (t : ℂ)) by ring,
    Complex.exp_add]
  ring

/-- The shifted rate has positive real part above the abscissa `1/2`. -/
theorem re_I_mul_xiSpectralPoint_add_ofReal_pos {σ : ℝ} (hσ : 1 / 2 < σ) (q : XiZeroCopy) :
    0 < (I * xiSpectralPoint q + (σ : ℂ)).re := by
  have hstrip : |(I * xiSpectralPoint q).re| < (1 / 2 : ℝ) :=
    abs_re_I_mul_xiSpectralPoint_le_half q
  have h := (abs_lt.mp hstrip).1
  simp only [Complex.add_re, Complex.ofReal_re]
  linarith

theorem integrableOn_suzukiPtZeroLaplaceTerm {σ : ℝ} (hσ : 1 / 2 < σ) (z : ℂ) (q : XiZeroCopy) :
    IntegrableOn (fun t : ℝ => suzukiPtZeroTerm t z q * Complex.exp (-((σ : ℂ) * (t : ℂ))))
      (Ioi (0 : ℝ)) volume := by
  have h1 := integrableOn_Ioi_cexp_neg_mul (re_I_mul_xiSpectralPoint_add_ofReal_pos hσ q)
  have h2 : IntegrableOn (fun t : ℝ => Complex.exp (-((σ : ℂ) * (t : ℂ)))) (Ioi (0 : ℝ)) volume := by
    refine integrableOn_Ioi_cexp_neg_mul ?_
    simpa using by linarith
  have h3 : IntegrableOn (fun t : ℝ =>
      (xiSpectralPoint q * (z - xiSpectralPoint q))⁻¹ *
        (Complex.exp (-((I * xiSpectralPoint q + (σ : ℂ)) * (t : ℂ)))
          - Complex.exp (-((σ : ℂ) * (t : ℂ))))) (Ioi (0 : ℝ)) volume :=
    Integrable.const_mul (h1.sub h2) _
  refine h3.congr (Filter.Eventually.of_forall fun t => ?_)
  exact (suzukiPtZeroLaplaceTerm_eq σ z q t).symm

/-- Exact Laplace transform of one divisor copy. -/
theorem integral_suzukiPtZeroLaplaceTerm {σ : ℝ} (hσ : 1 / 2 < σ) (z : ℂ) (q : XiZeroCopy) :
    (∫ t in Ioi (0 : ℝ), suzukiPtZeroTerm t z q * Complex.exp (-((σ : ℂ) * (t : ℂ))))
      = ((σ : ℂ) * (xiSpectralPoint q - I * (σ : ℂ)) * (xiSpectralPoint q - z))⁻¹ := by
  have hσ0 : (0 : ℝ) < σ := by linarith
  have hσC : ((σ : ℂ)) ≠ 0 := by
    simpa using ne_of_gt hσ0
  have hrate := re_I_mul_xiSpectralPoint_add_ofReal_pos hσ q
  have hrateNe : I * xiSpectralPoint q + (σ : ℂ) ≠ 0 := by
    intro h
    rw [h] at hrate
    simp at hrate
  have hγ : xiSpectralPoint q ≠ 0 := xiSpectralPoint_ne_zero q
  have h1 := integrableOn_Ioi_cexp_neg_mul hrate
  have h2 : IntegrableOn (fun t : ℝ => Complex.exp (-((σ : ℂ) * (t : ℂ)))) (Ioi (0 : ℝ)) volume := by
    refine integrableOn_Ioi_cexp_neg_mul ?_
    simpa using hσ0
  have hval : (∫ t in Ioi (0 : ℝ), suzukiPtZeroTerm t z q * Complex.exp (-((σ : ℂ) * (t : ℂ))))
      = (xiSpectralPoint q * (z - xiSpectralPoint q))⁻¹ *
          ((I * xiSpectralPoint q + (σ : ℂ))⁻¹ - ((σ : ℂ))⁻¹) := by
    rw [setIntegral_congr_fun measurableSet_Ioi
      (fun t _ => suzukiPtZeroLaplaceTerm_eq σ z q t)]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_sub h1 h2,
      integral_Ioi_cexp_neg_mul hrate, integral_Ioi_cexp_neg_mul (by simpa using hσ0)]
  rw [hval]
  have hIσ : xiSpectralPoint q - I * (σ : ℂ) ≠ 0 := by
    intro h
    apply hrateNe
    have : I * (xiSpectralPoint q - I * (σ : ℂ)) = I * xiSpectralPoint q + (σ : ℂ) := by
      rw [mul_sub, ← mul_assoc, Complex.I_mul_I]
      ring
    rw [← this, h, mul_zero]
  rcases eq_or_ne (xiSpectralPoint q) z with hzq | hzq
  · rw [hzq]
    simp
  · have hzne : z - xiSpectralPoint q ≠ 0 := sub_ne_zero.mpr (Ne.symm hzq)
    have hzne' : xiSpectralPoint q - z ≠ 0 := sub_ne_zero.mpr hzq
    have hrw : I * xiSpectralPoint q + (σ : ℂ) = I * (xiSpectralPoint q - I * (σ : ℂ)) := by
      rw [mul_sub, ← mul_assoc, Complex.I_mul_I]
      ring
    rw [hrw]
    field_simp
    linear_combination ((σ : ℂ) * (xiSpectralPoint q - z)) * Complex.I_sq


/-! ## Summability of the Laplace masses -/

theorem norm_suzukiPtZeroLaplaceTerm_le {σ : ℝ} (z : ℂ) (q : XiZeroCopy)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖suzukiPtZeroTerm t z q * Complex.exp (-((σ : ℂ) * (t : ℂ)))‖
      ≤ ‖(xiSpectralPoint q * (xiSpectralPoint q - z))⁻¹‖ *
          (Real.exp (-((σ - 1 / 2) * t)) + Real.exp (-(σ * t))) := by
  rw [suzukiPtZeroLaplaceTerm_eq, norm_mul]
  have hcoef : ‖(xiSpectralPoint q * (z - xiSpectralPoint q))⁻¹‖
      = ‖(xiSpectralPoint q * (xiSpectralPoint q - z))⁻¹‖ := by
    rw [show xiSpectralPoint q * (z - xiSpectralPoint q)
      = -(xiSpectralPoint q * (xiSpectralPoint q - z)) by ring, inv_neg, norm_neg]
  rw [hcoef]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hstrip : |(I * xiSpectralPoint q).re| < (1 / 2 : ℝ) :=
    abs_re_I_mul_xiSpectralPoint_le_half q
  have h1 : ‖Complex.exp (-((I * xiSpectralPoint q + (σ : ℂ)) * (t : ℂ)))‖
      ≤ Real.exp (-((σ - 1 / 2) * t)) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hre : (-((I * xiSpectralPoint q + (σ : ℂ)) * (t : ℂ))).re
        = -(((I * xiSpectralPoint q).re + σ) * t) := by
      simp [Complex.mul_re, Complex.add_re]
    rw [hre]
    have hlow : (σ - 1 / 2 : ℝ) ≤ (I * xiSpectralPoint q).re + σ := by
      have := (abs_lt.mp hstrip).1
      linarith
    nlinarith [hlow, ht]
  have h2 : ‖Complex.exp (-((σ : ℂ) * (t : ℂ)))‖ = Real.exp (-(σ * t)) := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re]
  calc ‖Complex.exp (-((I * xiSpectralPoint q + (σ : ℂ)) * (t : ℂ)))
          - Complex.exp (-((σ : ℂ) * (t : ℂ)))‖
      ≤ ‖Complex.exp (-((I * xiSpectralPoint q + (σ : ℂ)) * (t : ℂ)))‖
          + ‖Complex.exp (-((σ : ℂ) * (t : ℂ)))‖ := norm_sub_le _ _
    _ ≤ Real.exp (-((σ - 1 / 2) * t)) + Real.exp (-(σ * t)) := by rw [h2]; linarith

theorem integral_norm_suzukiPtZeroLaplaceTerm_le {σ : ℝ} (hσ : 1 / 2 < σ) (z : ℂ)
    (q : XiZeroCopy) :
    (∫ t in Ioi (0 : ℝ), ‖suzukiPtZeroTerm t z q * Complex.exp (-((σ : ℂ) * (t : ℂ)))‖)
      ≤ ‖(xiSpectralPoint q * (xiSpectralPoint q - z))⁻¹‖ * (1 / (σ - 1 / 2) + 1 / σ) := by
  have hσ0 : (0 : ℝ) < σ := by linarith
  have hσ1 : (0 : ℝ) < σ - 1 / 2 := by linarith
  have hI1 : IntegrableOn (fun t : ℝ => Real.exp (-((σ - 1 / 2) * t))) (Ioi (0 : ℝ)) volume := by
    refine (exp_neg_integrableOn_Ioi (0 : ℝ) hσ1).congr
      (Filter.Eventually.of_forall fun t => ?_)
    ring_nf
  have hI2 : IntegrableOn (fun t : ℝ => Real.exp (-(σ * t))) (Ioi (0 : ℝ)) volume := by
    refine (exp_neg_integrableOn_Ioi (0 : ℝ) hσ0).congr
      (Filter.Eventually.of_forall fun t => ?_)
    ring_nf
  have hmaj : IntegrableOn (fun t : ℝ =>
      ‖(xiSpectralPoint q * (xiSpectralPoint q - z))⁻¹‖ *
        (Real.exp (-((σ - 1 / 2) * t)) + Real.exp (-(σ * t)))) (Ioi (0 : ℝ)) volume :=
    Integrable.const_mul (Integrable.add hI1 hI2) _
  have hnorm : IntegrableOn
      (fun t : ℝ => ‖suzukiPtZeroTerm t z q * Complex.exp (-((σ : ℂ) * (t : ℂ)))‖)
      (Ioi (0 : ℝ)) volume := (integrableOn_suzukiPtZeroLaplaceTerm hσ z q).norm
  have hmono : (∫ t in Ioi (0 : ℝ), ‖suzukiPtZeroTerm t z q * Complex.exp (-((σ : ℂ) * (t : ℂ)))‖)
      ≤ ∫ t in Ioi (0 : ℝ), ‖(xiSpectralPoint q * (xiSpectralPoint q - z))⁻¹‖ *
          (Real.exp (-((σ - 1 / 2) * t)) + Real.exp (-(σ * t))) := by
    refine setIntegral_mono_on hnorm hmaj measurableSet_Ioi fun t ht => ?_
    exact norm_suzukiPtZeroLaplaceTerm_le z q (le_of_lt ht)
  refine hmono.trans_eq ?_
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hI1 hI2]
  congr 1
  rw [integral_Ioi_exp_neg_mul hσ1, integral_Ioi_exp_neg_mul hσ0]


/-- The centered completed Xi source is even. -/
theorem XiC_neg (z : ℂ) : XiC (-z) = XiC z := by
  change xi (1 / 2 + (-z) * Complex.I) = xi (1 / 2 + z * Complex.I)
  rw [show (1 : ℂ) / 2 + (-z) * Complex.I = 1 - (1 / 2 + z * Complex.I) by ring]
  exact xi_one_sub _

theorem summable_integral_norm_suzukiPtZeroLaplace {σ : ℝ} (hσ : 1 / 2 < σ) (z : ℂ) :
    Summable (fun q : XiZeroCopy =>
      ∫ t in Ioi (0 : ℝ), ‖suzukiPtZeroTerm t z q * Complex.exp (-((σ : ℂ) * (t : ℂ)))‖) := by
  have hmaj : Summable (fun q : XiZeroCopy =>
      ‖(xiSpectralPoint q * (xiSpectralPoint q - z))⁻¹‖ * (1 / (σ - 1 / 2) + 1 / σ)) :=
    (summable_xiResolventProduct_norm z).mul_right _
  refine Summable.of_nonneg_of_le (fun q => ?_) (fun q => ?_) hmaj
  · exact MeasureTheory.integral_nonneg fun t => norm_nonneg _
  · exact integral_norm_suzukiPtZeroLaplaceTerm_le hσ z q

/-- **The Laplace transform of `P_t(z)` in `t`, as a sum over the divisor.** -/
theorem integral_suzukiPtZeroSum_laplace_eq_tsum {σ : ℝ} (hσ : 1 / 2 < σ) (z : ℂ) :
    (∫ t in Ioi (0 : ℝ), suzukiPtZeroSum t z * Complex.exp (-((σ : ℂ) * (t : ℂ))))
      = ∑' q : XiZeroCopy,
          ((σ : ℂ) * (xiSpectralPoint q - I * (σ : ℂ)) * (xiSpectralPoint q - z))⁻¹ := by
  have h := MeasureTheory.integral_tsum_of_summable_integral_norm
      (F := fun (q : XiZeroCopy) (t : ℝ) =>
        suzukiPtZeroTerm t z q * Complex.exp (-((σ : ℂ) * (t : ℂ))))
      (μ := volume.restrict (Ioi (0 : ℝ)))
      (fun q => integrableOn_suzukiPtZeroLaplaceTerm hσ z q)
      (summable_integral_norm_suzukiPtZeroLaplace hσ z)
  have hpt : ∀ t : ℝ,
      (∑' q : XiZeroCopy, suzukiPtZeroTerm t z q * Complex.exp (-((σ : ℂ) * (t : ℂ))))
        = suzukiPtZeroSum t z * Complex.exp (-((σ : ℂ) * (t : ℂ))) := fun t => tsum_mul_right
  calc (∫ t in Ioi (0 : ℝ), suzukiPtZeroSum t z * Complex.exp (-((σ : ℂ) * (t : ℂ))))
      = ∫ t in Ioi (0 : ℝ),
          ∑' q : XiZeroCopy, suzukiPtZeroTerm t z q * Complex.exp (-((σ : ℂ) * (t : ℂ))) := by
        exact (setIntegral_congr_fun measurableSet_Ioi fun t _ => hpt t).symm
    _ = ∑' q : XiZeroCopy,
          ∫ t in Ioi (0 : ℝ), suzukiPtZeroTerm t z q * Complex.exp (-((σ : ℂ) * (t : ℂ))) := h.symm
    _ = ∑' q : XiZeroCopy,
          ((σ : ℂ) * (xiSpectralPoint q - I * (σ : ℂ)) * (xiSpectralPoint q - z))⁻¹ :=
        tsum_congr fun q => integral_suzukiPtZeroLaplaceTerm hσ z q


/-- The purely imaginary point `-iσ` lies off the Xi divisor for `σ > 1/2`. -/
theorem XiC_neg_I_mul_ofReal_ne_zero {σ : ℝ} (hσ : 1 / 2 < σ) :
    XiC (-(I * (σ : ℂ))) ≠ 0 := by
  refine XiC_ne_zero_of_admissible (XiExplicitAdmissible_of_one_lt_re ?_)
  have hval : (1 : ℂ) / 2 + (-(I * (σ : ℂ))) * Complex.I = 1 / 2 + (σ : ℂ) := by
    linear_combination (-(σ : ℂ)) * Complex.I_sq
  rw [hval]
  simp only [Complex.add_re, Complex.ofReal_re]
  norm_num
  linarith

/-- **Partial-fraction evaluation of the Laplace sum.** -/
theorem tsum_suzukiPtZeroLaplaceValue {σ : ℝ} (hσ : 1 / 2 < σ) {z : ℂ} (hz : XiC z ≠ 0)
    (hzσ : I * (σ : ℂ) - z ≠ 0) :
    (∑' q : XiZeroCopy,
        ((σ : ℂ) * (xiSpectralPoint q - I * (σ : ℂ)) * (xiSpectralPoint q - z))⁻¹)
      = (xiRelativeResolventTrace (-(I * (σ : ℂ))) - xiRelativeResolventTrace (-z)) /
          ((σ : ℂ) * (I * (σ : ℂ) - z)) := by
  have hσ0 : ((σ : ℂ)) ≠ 0 := by
    simpa using ne_of_gt (show (0:ℝ) < σ by linarith)
  have hzneg : XiC (-z) ≠ 0 := by rwa [XiC_neg]
  have hIσ : XiC (-(I * (σ : ℂ))) ≠ 0 := XiC_neg_I_mul_ofReal_ne_zero hσ
  have hzσ' : (σ : ℂ) * I - z ≠ 0 := by rwa [mul_comm]
  have hnez : ∀ q : XiZeroCopy, xiSpectralPoint q + z ≠ 0 := by
    intro q h
    apply hzneg
    have hq : xiSpectralPoint q = -z := by linear_combination h
    rw [← hq]
    exact XiC_xiSpectralPoint_eq_zero q
  have hneIσ : ∀ q : XiZeroCopy, xiSpectralPoint q + I * (σ : ℂ) ≠ 0 := by
    intro q h
    apply hIσ
    have hq : xiSpectralPoint q = -(I * (σ : ℂ)) := by linear_combination h
    rw [← hq]
    exact XiC_xiSpectralPoint_eq_zero q
  -- reindex by functional-equation reflection
  have hrefl : (∑' q : XiZeroCopy,
        ((σ : ℂ) * (xiSpectralPoint q - I * (σ : ℂ)) * (xiSpectralPoint q - z))⁻¹)
      = ∑' q : XiZeroCopy,
        ((σ : ℂ) * (xiSpectralPoint q + I * (σ : ℂ)) * (xiSpectralPoint q + z))⁻¹ := by
    have := xiZeroCopyReflectEquiv.tsum_eq
      (fun q : XiZeroCopy =>
        ((σ : ℂ) * (xiSpectralPoint q - I * (σ : ℂ)) * (xiSpectralPoint q - z))⁻¹)
    rw [← this]
    refine tsum_congr fun q => ?_
    rw [xiSpectralPoint_reflect]
    congr 1
    ring
  rw [hrefl]
  -- partial fractions
  have hterm : ∀ q : XiZeroCopy,
      ((σ : ℂ) * (xiSpectralPoint q + I * (σ : ℂ)) * (xiSpectralPoint q + z))⁻¹
        = ((σ : ℂ) * (I * (σ : ℂ) - z))⁻¹ *
            (xiRelativeResolventTerm (-(I * (σ : ℂ))) q - xiRelativeResolventTerm (-z) q) := by
    intro q
    have h1 := hnez q
    have h2 := hneIσ q
    have hγ : xiSpectralPoint q ≠ 0 := xiSpectralPoint_ne_zero q
    have hres : xiRelativeResolventTerm (-(I * (σ : ℂ))) q - xiRelativeResolventTerm (-z) q
        = (xiSpectralPoint q + z)⁻¹ - (xiSpectralPoint q + I * (σ : ℂ))⁻¹ := by
      rw [xiRelativeResolventTerm, xiRelativeResolventTerm,
        show xiSpectralPoint q - -(I * (σ : ℂ)) = xiSpectralPoint q + I * (σ : ℂ) by ring,
        show xiSpectralPoint q - -z = xiSpectralPoint q + z by ring]
      ring
    have hkey : (xiSpectralPoint q + z)⁻¹ - (xiSpectralPoint q + I * (σ : ℂ))⁻¹
        = (I * (σ : ℂ) - z) /
            ((xiSpectralPoint q + z) * (xiSpectralPoint q + I * (σ : ℂ))) := by
      rw [inv_sub_inv h1 h2]
      congr 1
      ring
    rw [hres, hkey]
    field_simp
  have hsum : Summable (fun q : XiZeroCopy =>
      xiRelativeResolventTerm (-(I * (σ : ℂ))) q - xiRelativeResolventTerm (-z) q) :=
    (summable_xiRelativeResolventTerm hIσ).sub (summable_xiRelativeResolventTerm hzneg)
  rw [tsum_congr hterm, hsum.tsum_mul_left,
    Summable.tsum_sub (summable_xiRelativeResolventTerm hIσ)
      (summable_xiRelativeResolventTerm hzneg)]
  rw [xiRelativeResolventTrace, xiRelativeResolventTrace, div_eq_mul_inv, mul_comm]

/-- **The Laplace transform of the Xi-zero series.**  For `σ > 1/2` and a base point off the
divisor, the Laplace transform of Suzuki's `P_t(z)` is a difference of two Xi relative resolvent
traces. -/
theorem integral_suzukiPtZeroSum_laplace {σ : ℝ} (hσ : 1 / 2 < σ) {z : ℂ} (hz : XiC z ≠ 0)
    (hzσ : I * (σ : ℂ) - z ≠ 0) :
    (∫ t in Ioi (0 : ℝ), suzukiPtZeroSum t z * Complex.exp (-((σ : ℂ) * (t : ℂ))))
      = (xiRelativeResolventTrace (-(I * (σ : ℂ))) - xiRelativeResolventTrace (-z)) /
          ((σ : ℂ) * (I * (σ : ℂ) - z)) := by
  rw [integral_suzukiPtZeroSum_laplace_eq_tsum hσ z]
  exact tsum_suzukiPtZeroLaplaceValue hσ hz hzσ

end
end RHTower
