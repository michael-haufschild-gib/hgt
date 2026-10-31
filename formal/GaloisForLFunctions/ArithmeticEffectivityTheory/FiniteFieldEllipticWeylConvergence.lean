import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticGlobalSpectralIntegral
import GaloisForLFunctions.HTGeometry.LoopEisenstein.AffineA1FiniteFieldWeylPoles
import GaloisForLFunctions.HTGeometry.ExponentialLatticeWeight

/-!
# Absolute convergence of the actual elliptic Weyl series

Nonnegative adelic height bounds every arithmetic zeta ratio on a closed
half-plane by one real radial integral. The resulting exponential bound
in inversion length is dominated by the degree rotation's Gaussian decay.
-/

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
open MeasureTheory HTGeometry.LoopEisenstein
open scoped NNReal
noncomputable section

/-- Every actual normalized logarithmic local height is nonnegative. -/
theorem adelicLogHeight_nonneg (a : Adeles) : 0 ≤ adelicLogHeight a :=
  add_nonneg (finsum_nonneg fun v => Real.log_nonneg (le_max_left 1 _))
    (Real.log_nonneg (le_max_left 1 _))

/-- Increasing the real spectral parameter decreases the absolute kernel. -/
theorem norm_ellipticAdeleSpectralKernel_le (s : ℂ) (σ : ℝ) (hs : σ ≤ s.re) (a : Adeles) :
    ‖ellipticAdeleSpectralKernel s a‖ ≤ ‖ellipticAdeleSpectralKernel (σ : ℂ) a‖ := by
  rw [norm_ellipticAdeleSpectralKernel,norm_ellipticAdeleSpectralKernel,Complex.ofReal_re]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right (add_le_add_right hs 1) (adelicLogHeight_nonneg a)
  linarith only [h]

private theorem localSpectralParameter_three_eq (s : ℂ) :
    localSpectralParameter 3 s = zetaCoordinate s := by
  unfold localSpectralParameter zetaCoordinate
  simp only [NNReal.coe_ofNat]
  congr 1
  ring

/-- The actual radial integral ratio is the previously defined arithmetic zeta ratio. -/
theorem ellipticSpectralZetaRatio_eq_arithmeticZetaRatio (s : ℂ) :
    ellipticSpectralZetaRatio s = arithmeticZetaRatio s := by
  simp only [ellipticSpectralZetaRatio,localSpectralParameter_three_eq,
    arithmeticZetaRatio,arithmeticZeta,zetaCoordinate_add_one]

/-- A finite real radial integral supplies a uniform half-plane majorant. -/
def ellipticSpectralMajorant (σ : ℝ) : ℝ :=
  1 + ∫ a, ‖ellipticAdeleSpectralKernel (σ : ℂ) a‖ ∂adeleHaar

theorem ellipticSpectralMajorant_one_le (σ : ℝ) : 1 ≤ ellipticSpectralMajorant σ := by
  have h : 0 ≤ ∫ a, ‖ellipticAdeleSpectralKernel (σ : ℂ) a‖ ∂adeleHaar :=
    integral_nonneg (fun _ => norm_nonneg _)
  exact le_add_of_nonneg_right h

/-- The arithmetic zeta ratio has a uniform bound on each closed half-plane `Re(s)≥σ>1`. -/
theorem norm_arithmeticZetaRatio_le_majorant (σ : ℝ) (hσ : 1 < σ)
    (s : ℂ) (hs : σ ≤ s.re) : ‖arithmeticZetaRatio s‖ ≤ ellipticSpectralMajorant σ := by
  have hsi := ellipticAdeleSpectralKernel_integrable s (hσ.trans_le hs)
  have hσi := ellipticAdeleSpectralKernel_integrable (σ : ℂ) hσ
  calc
    ‖arithmeticZetaRatio s‖ = ‖∫ a, ellipticAdeleSpectralKernel s a ∂adeleHaar‖ := by
      rw [integral_ellipticAdeleSpectralKernel s (hσ.trans_le hs),
        ellipticSpectralZetaRatio_eq_arithmeticZetaRatio]
    _ ≤ ∫ a, ‖ellipticAdeleSpectralKernel s a‖ ∂adeleHaar := norm_integral_le_integral_norm _
    _ ≤ ∫ a, ‖ellipticAdeleSpectralKernel (σ : ℂ) a‖ ∂adeleHaar :=
      integral_mono hsi.norm hσi.norm (norm_ellipticAdeleSpectralKernel_le s σ hs)
    _ ≤ ellipticSpectralMajorant σ := by unfold ellipticSpectralMajorant; linarith

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein.AffineA1
open ArithmeticEffectivityTheory.FiniteFieldEllipticBase
noncomputable section

/-- One rate bounds all actual elliptic root factors in a fixed Godement chamber. -/
def ellipticCoefficientRate (p : ℂ × ℂ) : ℝ :=
  ellipticSpectralMajorant (min (chamberCoordinate p.1).re (chamberCoordinate p.2).re)

theorem ellipticCoefficientRate_pos (p : ℂ × ℂ) : 0 < ellipticCoefficientRate p :=
  zero_lt_one.trans_le (ellipticSpectralMajorant_one_le _)

private theorem root_arithmeticZetaRatio_norm_le_exp (p : ℂ × ℂ) (w : Weyl) :
    ∀ β ∈ inversions w,
      ‖arithmeticZetaRatio (rootArgument (godementParameter p) β)‖ ≤ Real.exp (ellipticCoefficientRate p) := by
  intro β hβ
  have hσ := lt_min (chamberCoordinate_re_gt_one p.1) (chamberCoordinate_re_gt_one p.2)
  have h : ‖arithmeticZetaRatio (rootArgument (godementParameter p) β)‖ ≤ ellipticCoefficientRate p :=
    norm_arithmeticZetaRatio_le_majorant _ hσ _ (rootArgument_re_ge_min p w β hβ)
  apply h.trans
  have he := Real.add_one_le_exp (ellipticCoefficientRate p)
  linarith only [he]

/-- Actual elliptic coefficients grow at most exponentially in the exact inversion count. -/
theorem finiteFieldCoefficient_norm_le_exp (p : ℂ × ℂ) (w : Weyl) :
    ‖finiteFieldCoefficient (godementParameter p) w‖ ≤
      Real.exp ((inversions w).card * ellipticCoefficientRate p) := by
  calc
    ‖finiteFieldCoefficient (godementParameter p) w‖ ≤
        ∏ β ∈ inversions w, ‖arithmeticZetaRatio (rootArgument (godementParameter p) β)‖ :=
      Finset.norm_prod_le _ _
    _ ≤ ∏ _β ∈ inversions w, Real.exp (ellipticCoefficientRate p) :=
      Finset.prod_le_prod (fun _ _ => norm_nonneg _) (root_arithmeticZetaRatio_norm_le_exp p w)
    _ = Real.exp ((inversions w).card * ellipticCoefficientRate p) := by
      rw [Finset.prod_const, ← Real.exp_nat_mul]

private theorem finiteFieldCoefficient_translation_norm_le_exp (p : ℂ × ℂ) (m : ℤ) :
    ‖finiteFieldCoefficient (godementParameter p) (.r m)‖ ≤
      Real.exp ((2*m).natAbs * ellipticCoefficientRate p) := by
  simpa only [inversions_translation_card] using finiteFieldCoefficient_norm_le_exp p (.r m)

private theorem finiteFieldCoefficient_reflection_norm_le_exp (p : ℂ × ℂ) (m : ℤ) :
    ‖finiteFieldCoefficient (godementParameter p) (.sr m)‖ ≤
      Real.exp ((2*m+1).natAbs * ellipticCoefficientRate p) := by
  simpa only [inversions_reflection_card] using finiteFieldCoefficient_norm_le_exp p (.sr m)

private theorem summable_quadratic_abs {a : ℝ} (ha : 0 < a) (b c : ℝ) :
    Summable (fun m : ℤ => Real.exp (c + b * |(m : ℝ)| - a * (m : ℝ) ^ 2)) := by
  have hgeom : Summable (fun m : ℤ => Real.exp (-|(m : ℝ)|)) := by
    simpa only [neg_one_mul] using
      GaloisForLFunctions.HTGeometry.summable_exp_neg_abs_int (c := 1) zero_lt_one
  have hmajor := hgeom.mul_left (Real.exp (c + (b + 1) ^ 2 / (4 * a)))
  apply hmajor.of_nonneg_of_le (fun _ => (Real.exp_pos _).le)
  intro m
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hsq := sq_nonneg (2 * a * |(m : ℝ)| - (b + 1))
  simp only [sub_sq, mul_pow, sq_abs] at hsq
  have hcomplete : (b + 1) * |(m : ℝ)| - a * (m : ℝ) ^ 2 ≤
      (b + 1) ^ 2 / (4 * a) := by
    apply (le_div_iff₀ (show 0 < 4 * a by positivity)).mpr
    nlinarith only [hsq]
  linarith only [hcomplete]

private theorem translation_coefficient_bound (p : ℂ × ℂ) (m : ℤ) :
    ‖finiteFieldCoefficient (godementParameter p) (.r m)‖ ≤
      Real.exp ((2 * |(m : ℝ)| + 1) * ellipticCoefficientRate p) := by
  have h := finiteFieldCoefficient_translation_norm_le_exp p m
  have he : ((2 * m).natAbs : ℝ) = 2 * |(m : ℝ)| := by
    simp [Nat.cast_natAbs, Int.cast_abs, abs_mul]
  rw [he] at h
  apply h.trans (Real.exp_le_exp.mpr ?_)
  nlinarith only [ellipticCoefficientRate_pos p]

private theorem reflection_coefficient_bound (p : ℂ × ℂ) (m : ℤ) :
    ‖finiteFieldCoefficient (godementParameter p) (.sr m)‖ ≤
      Real.exp ((2 * |(m : ℝ)| + 1) * ellipticCoefficientRate p) := by
  have h := finiteFieldCoefficient_reflection_norm_le_exp p m
  have he : ((2 * m + 1).natAbs : ℝ) = |2 * (m : ℝ) + 1| := by
    simp [Nat.cast_natAbs, Int.cast_abs]
  rw [he] at h
  apply h.trans (Real.exp_le_exp.mpr ?_)
  have hlength : |2 * (m : ℝ) + 1| ≤ 2 * |(m : ℝ)| + 1 := by
    apply abs_le.mpr
    constructor
    · linarith only [neg_abs_le (m : ℝ)]
    · linarith only [le_abs_self (m : ℝ)]
  exact mul_le_mul_of_nonneg_right hlength (ellipticCoefficientRate_pos p).le

/-- A Gaussian majorant for the complete translation summand, including its arithmetic denominator. -/
theorem norm_finiteFieldWeylTerm_translation_le (p : ℂ × ℂ) (t z r : ℝ) (m : ℤ) :
    ‖finiteFieldWeylTerm (godementParameter p) t z r (.r m)‖ ≤
      Real.exp (translationConstant p t z + ellipticCoefficientRate p +
        (2 * ellipticCoefficientRate p + |translationLinear p t r|) * |(m : ℝ)| -
          gaussianRate p r * (m : ℝ) ^ 2) := by
  rw [finiteFieldWeylTerm, norm_mul, norm_exp_weylExponent_translation]
  calc
    _ ≤ Real.exp ((2 * |(m : ℝ)| + 1) * ellipticCoefficientRate p) *
        Real.exp (translationConstant p t z + translationLinear p t r * m -
          gaussianRate p r * (m : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right (translation_coefficient_bound p m) (Real.exp_pos _).le
    _ ≤ _ := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hlinear : translationLinear p t r * (m : ℝ) ≤
          |translationLinear p t r| * |(m : ℝ)| := by
        rw [← abs_mul]
        exact le_abs_self _
      nlinarith only [hlinear]

/-- The second dihedral family admits the same form of Gaussian majorant. -/
theorem norm_finiteFieldWeylTerm_reflection_le (p : ℂ × ℂ) (t z r : ℝ) (m : ℤ) :
    ‖finiteFieldWeylTerm (godementParameter p) t z r (.sr m)‖ ≤
      Real.exp (reflectionConstant p t z + ellipticCoefficientRate p +
        (2 * ellipticCoefficientRate p + |reflectionLinear p t r|) * |(m : ℝ)| -
          gaussianRate p r * (m : ℝ) ^ 2) := by
  rw [finiteFieldWeylTerm, norm_mul, norm_exp_weylExponent_reflection]
  calc
    _ ≤ Real.exp ((2 * |(m : ℝ)| + 1) * ellipticCoefficientRate p) *
        Real.exp (reflectionConstant p t z + reflectionLinear p t r * m -
          gaussianRate p r * (m : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right (reflection_coefficient_bound p m) (Real.exp_pos _).le
    _ ≤ _ := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hlinear : reflectionLinear p t r * (m : ℝ) ≤
          |reflectionLinear p t r| * |(m : ℝ)| := by
        rw [← abs_mul]
        exact le_abs_self _
      nlinarith only [hlinear]

theorem summable_norm_finiteFieldTranslation (p : ℂ × ℂ) (t z r : ℝ) :
    Summable (fun m : ℤ => ‖finiteFieldWeylTerm (godementParameter p) t z r (.r m)‖) := by
  exact (summable_quadratic_abs (gaussianRate_pos p r)
    (2 * ellipticCoefficientRate p + |translationLinear p t r|)
    (translationConstant p t z + ellipticCoefficientRate p)).of_nonneg_of_le
      (fun _ => norm_nonneg _) (norm_finiteFieldWeylTerm_translation_le p t z r)

theorem summable_norm_finiteFieldReflection (p : ℂ × ℂ) (t z r : ℝ) :
    Summable (fun m : ℤ => ‖finiteFieldWeylTerm (godementParameter p) t z r (.sr m)‖) := by
  exact (summable_quadratic_abs (gaussianRate_pos p r)
    (2 * ellipticCoefficientRate p + |reflectionLinear p t r|)
    (reflectionConstant p t z + ellipticCoefficientRate p)).of_nonneg_of_le
      (fun _ => norm_nonneg _) (norm_finiteFieldWeylTerm_reflection_le p t z r)

/-- Absolute convergence over the entire infinite affine Weyl group. -/
theorem summable_norm_finiteFieldWeylTerm (p : ℂ × ℂ) (t z r : ℝ) :
    Summable (fun w : Weyl => ‖finiteFieldWeylTerm (godementParameter p) t z r w‖) := by
  apply (DihedralGroup.equivSum.symm.summable_iff).mp
  exact Summable.sum _ (summable_norm_finiteFieldTranslation p t z r) (summable_norm_finiteFieldReflection p t z r)

theorem summable_finiteFieldWeylTerm (p : ℂ × ℂ) (t z r : ℝ) : Summable (finiteFieldWeylTerm (godementParameter p) t z r) :=
  (summable_norm_finiteFieldWeylTerm p t z r).of_norm

theorem hasSum_finiteFieldWeylTerm (p : ℂ × ℂ) (t z r : ℝ) :
    HasSum (finiteFieldWeylTerm (godementParameter p) t z r) (finiteFieldWeylSum (godementParameter p) t z r) :=
  (summable_finiteFieldWeylTerm p t z r).hasSum

/-- The Weyl expansion is exactly its translation series plus its reflection series. -/
theorem finiteFieldWeylSum_eq_two_series_chamber (p : ℂ × ℂ) (t z r : ℝ) :
    finiteFieldWeylSum (godementParameter p) t z r = (∑' m : ℤ, finiteFieldWeylTerm (godementParameter p) t z r (.r m)) +
      ∑' m : ℤ, finiteFieldWeylTerm (godementParameter p) t z r (.sr m) := by
  rw [finiteFieldWeylSum, ← DihedralGroup.equivSum.symm.tsum_eq (finiteFieldWeylTerm (godementParameter p) t z r)]
  exact Summable.tsum_sum (summable_norm_finiteFieldTranslation p t z r).of_norm
    (summable_norm_finiteFieldReflection p t z r).of_norm

/-- Absolute convergence holds at every parameter in the full Godement chamber. -/
theorem summable_norm_finiteFieldWeylTerm_of_re_gt_one (lam : ℂ × ℂ)
    (h₀ : 1 < lam.1.re) (h₁ : 1 < lam.2.re) (t z r : ℝ) :
    Summable (fun w : Weyl => ‖finiteFieldWeylTerm lam t z r w‖) := by
  have h : lam ∈ Set.range godementParameter := by
    rw [range_godementParameter]
    exact ⟨h₀, h₁⟩
  obtain ⟨p, rfl⟩ := h
  exact summable_norm_finiteFieldWeylTerm p t z r

/-- The two-series identity holds throughout the full Godement chamber. -/
theorem finiteFieldWeylSum_eq_two_series_of_re_gt_one (lam : ℂ × ℂ)
    (h₀ : 1 < lam.1.re) (h₁ : 1 < lam.2.re) (t z r : ℝ) :
    finiteFieldWeylSum lam t z r =
      (∑' m : ℤ, finiteFieldWeylTerm lam t z r (.r m)) +
        ∑' m : ℤ, finiteFieldWeylTerm lam t z r (.sr m) := by
  have h : lam ∈ Set.range godementParameter := by
    rw [range_godementParameter]
    exact ⟨h₀, h₁⟩
  obtain ⟨p, rfl⟩ := h
  exact finiteFieldWeylSum_eq_two_series_chamber p t z r

end

end GaloisForLFunctions.HTGeometry.LoopEisenstein.AffineA1

#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.norm_arithmeticZetaRatio_le_majorant
#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.AffineA1.finiteFieldCoefficient_norm_le_exp
#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.AffineA1.summable_norm_finiteFieldWeylTerm

#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.AffineA1.finiteFieldWeylSum_eq_two_series_chamber

#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.AffineA1.summable_norm_finiteFieldWeylTerm_of_re_gt_one
#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.AffineA1.finiteFieldWeylSum_eq_two_series_of_re_gt_one
