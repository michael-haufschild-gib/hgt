/-
# Canonical Class-I CGL vertical lines converge to the same safe-line integral

For every certified primitive Class-I zero, the genuinely smoothed CGL
integrand is integrable on the canonical safe line.  The finite right vertical
edges converge to that integral, and the already proved vanishing horizontal
edges transfer the same convergence to the canonical left vertical edges.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiClassIMellinTail
import GaloisForLFunctions.RHTower.ChenGuptaLiSmoothedNonprincipalContour
import GaloisForLFunctions.RHTower.ChenGuptaLiPrimitiveClassISmoothedVerticalBalance

open Complex Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- The Gamma-completed L-series of every shifted full CGL detector coefficient
sequence is integrable on the safe inversion line. -/
theorem gamma_mul_LSeries_cglFull_verticalIntegrable_two
    (X q : ℕ) (χ : DirichletCharacter ℂ (q + 1)) (s : CGLRightHalfPlanePoint) :
    Complex.VerticalIntegrable (fun w => Complex.Gamma w *
      LSeries (cglShiftedDetectorProductCoefficient X q χ s) w) 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_cglShiftedDetectorProductCoefficient_uniformBound
  let g : ℕ → ℂ := (C : ℂ)⁻¹ • cglShiftedDetectorProductCoefficient X q χ s
  have hg : ∀ k, ‖g k‖ ≤ 1 := by
    intro k
    have hC0 : C ≠ 0 := hC.ne'
    calc
      ‖g k‖ = C⁻¹ * ‖cglShiftedDetectorProductCoefficient X q χ s k‖ := by
        simp only [g, Pi.smul_apply, norm_smul, norm_inv, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hC]
      _ ≤ C⁻¹ * C := mul_le_mul_of_nonneg_left (hbound X q χ s k) (inv_nonneg.mpr hC.le)
      _ = 1 := inv_mul_cancel₀ hC0
  have hbase := RHTower.Sieve.gamma_mul_LSeries_verticalIntegrable_two hg
  apply (hbase.const_mul (C : ℂ)).congr
  exact Filter.Eventually.of_forall fun t => by
    dsimp [g]
    rw [LSeries_smul]
    have hC0 : (C : ℂ) ≠ 0 := by exact_mod_cast hC.ne'
    field_simp [hC0]

/-- On the CGL safe line, the literal smoothing factor has constant modulus. -/
theorem norm_cglSmoothingWeight_safeLine
    (Y : ℕ) (t : ℝ) :
    ‖((Y + 1 : ℕ) : ℂ) ^ ((2 : ℂ) + (t : ℂ) * I)‖ = (Y + 1 : ℕ) ^ (2 : ℕ) := by
  have hYpos : (0 : ℝ) < (Y + 1 : ℕ) := by positivity
  rw [show ((Y + 1 : ℕ) : ℂ) = (((Y + 1 : ℕ) : ℝ) : ℂ) by norm_num,
    Complex.norm_cpow_eq_rpow_re_of_pos hYpos]
  norm_num

/-- The genuinely smoothed CGL integrand of every certified primitive Class-I
zero is integrable on the safe line `Re(w)=2`. -/
theorem cglPrimitiveClassI_smoothedSafeLine_integrable
    (X n Y : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLPrimitiveClassIWindowZero n χ τ H) :
    Integrable (fun t : ℝ => cglSmoothedNonprincipalDetectorMellinIntegrand X n Y
      (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).toCGLNonprincipalCriticalStripLZero
      ((2 : ℂ) + (t : ℂ) * I)) := by
  let s := cglPrimitiveClassIWindowZeroRightHalfPlanePoint n χ τ H z
  let f := fun t : ℝ => Complex.Gamma ((2 : ℂ) + (t : ℂ) * I) *
    LSeries (cglShiftedDetectorProductCoefficient X n χ.1.1 s) ((2 : ℂ) + (t : ℂ) * I)
  have hf : Integrable f := by
    have hbase := gamma_mul_LSeries_cglFull_verticalIntegrable_two X n χ.1.1 s
    change Integrable (fun t : ℝ => Complex.Gamma ((2 : ℂ) + (t : ℂ) * I) *
      LSeries (cglShiftedDetectorProductCoefficient X n χ.1.1 s) ((2 : ℂ) + (t : ℂ) * I)) at hbase
    simpa [f] using hbase
  have hYne : ((Y + 1 : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.succ_ne_zero Y)
  let W : ℝ → ℂ := fun t => ((Y + 1 : ℕ) : ℂ) ^ ((2 : ℂ) + (t : ℂ) * I)
  have hweight : Continuous W := by
    dsimp [W]
    apply (differentiable_id.const_cpow (Or.inl hYne)).continuous.comp
    fun_prop
  have hweighted : Integrable (fun t : ℝ => (W t * f t)) := by
    apply Integrable.mono' (hf.norm.const_mul ((Y + 1 : ℕ) ^ (2 : ℕ)))
      (hweight.aestronglyMeasurable.mul hf.aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun t => by
      change ‖((Y + 1 : ℕ) : ℂ) ^ ((2 : ℂ) + (t : ℂ) * I) * f t‖ ≤ _
      rw [norm_mul, norm_cglSmoothingWeight_safeLine]
  apply hweighted.congr
  exact Filter.Eventually.of_forall fun t => by
    have hchar :
        (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).character = χ.1.1 := rfl
    have hpoint :
        (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).point = z.1.1 := rfl
    unfold cglSmoothedNonprincipalDetectorMellinIntegrand cglDetectorMellinIntegrand
    rw [hchar, hpoint]
    change W t * f t = ((Y + 1 : ℕ) : ℂ) ^ ((2 : ℂ) + (t : ℂ) * I) *
      (Complex.Gamma ((2 : ℂ) + (t : ℂ) * I) *
        (zeroDetectionMobiusPolynomial X (n + 1) χ.1.1 (z.1.1 + ((2 : ℂ) + (t : ℂ) * I)) *
          DirichletCharacter.LFunction χ.1.1 (z.1.1 + ((2 : ℂ) + (t : ℂ) * I))))
    dsimp [W, f]
    have hs : s.1 = z.1.1 := rfl
    rw [← hs]
    rw [cglShiftedDetectorProductCoefficient_initialLine_LSeries X n χ.1.1 s t]

/-- The finite canonical right vertical CGL edge converges to its full
source-weighted safe-line integral. -/
theorem tendsto_cglPrimitiveClassI_smoothedSafeLine_truncation
    (X n Y : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLPrimitiveClassIWindowZero n χ τ H) :
    Tendsto (fun K : ℕ =>
      ∫ t in (-((K + 1 : ℕ) : ℝ))..((K + 1 : ℕ) : ℝ),
        cglSmoothedNonprincipalDetectorMellinIntegrand X n Y
          (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).toCGLNonprincipalCriticalStripLZero
          ((2 : ℂ) + (t : ℂ) * I)) atTop
      (𝓝 (∫ t : ℝ,
        cglSmoothedNonprincipalDetectorMellinIntegrand X n Y
          (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).toCGLNonprincipalCriticalStripLZero
          ((2 : ℂ) + (t : ℂ) * I))) := by
  have hpos : Tendsto (fun K : ℕ => ((K + 1 : ℕ) : ℝ)) atTop atTop := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hneg : Tendsto (fun K : ℕ => -((K + 1 : ℕ) : ℝ)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hpos
  exact MeasureTheory.intervalIntegral_tendsto_integral
    (cglPrimitiveClassI_smoothedSafeLine_integrable X n Y χ τ H z) hneg hpos

/-- The finite canonical left vertical CGL edge converges to the same full
source-weighted safe-line integral, with no separate left-edge assumption. -/
theorem tendsto_cglPrimitiveClassI_smoothedLeftLine_truncation
    (X n Y : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLPrimitiveClassIWindowZero n χ τ H) :
    Tendsto (fun K : ℕ =>
      ∫ t in (-((K + 1 : ℕ) : ℝ))..((K + 1 : ℕ) : ℝ),
        cglSmoothedNonprincipalDetectorMellinIntegrand X n Y
          (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).toCGLNonprincipalCriticalStripLZero
          ((((1 / 2 : ℝ) - z.1.1.re : ℝ) : ℂ) + (t : ℂ) * I)) atTop
      (𝓝 (∫ t : ℝ,
        cglSmoothedNonprincipalDetectorMellinIntegrand X n Y
          (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).toCGLNonprincipalCriticalStripLZero
          ((2 : ℂ) + (t : ℂ) * I))) := by
  let J : ℂ := ∫ t : ℝ,
    cglSmoothedNonprincipalDetectorMellinIntegrand X n Y
      (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).toCGLNonprincipalCriticalStripLZero
      ((2 : ℂ) + (t : ℂ) * I)
  have hright := tendsto_cglPrimitiveClassI_smoothedSafeLine_truncation X n Y χ τ H z
  change Tendsto _ atTop (𝓝 J) at hright
  have hgap := tendsto_cglPrimitiveClassISmoothedCanonicalVerticalGap X n Y χ τ H z
  have hrightS := hright.const_smul I
  have hleftS := hrightS.sub hgap
  rw [sub_zero] at hleftS
  have hleftS' : Tendsto (fun K : ℕ => I •
      (∫ t in (-((K + 1 : ℕ) : ℝ))..((K + 1 : ℕ) : ℝ),
        cglSmoothedNonprincipalDetectorMellinIntegrand X n Y
          (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).toCGLNonprincipalCriticalStripLZero
          ((((1 / 2 : ℝ) - z.1.1.re : ℝ) : ℂ) + (t : ℂ) * I))) atTop (𝓝 (I • J)) := by
    refine hleftS.congr fun K => ?_
    module
  have hleft := hleftS'.const_smul (-I)
  have hminusI_mul_I : (-I : ℂ) * I = 1 := by
    rw [neg_mul, Complex.I_mul_I]
    norm_num
  have hIJ : (-I : ℂ) • (I • J) = J := by
    simp only [smul_eq_mul]
    calc
      -I * (I * J) = ((-I : ℂ) * I) * J := by ring
      _ = J := by rw [hminusI_mul_I, one_mul]
  rw [hIJ] at hleft
  refine hleft.congr fun K => ?_
  simp only [smul_eq_mul]
  calc
    -I * (I * (∫ t in (-((K + 1 : ℕ) : ℝ))..((K + 1 : ℕ) : ℝ),
        cglSmoothedNonprincipalDetectorMellinIntegrand X n Y
          (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).toCGLNonprincipalCriticalStripLZero
          ((((1 / 2 : ℝ) - z.1.1.re : ℝ) : ℂ) + (t : ℂ) * I))) =
        ((-I : ℂ) * I) * (∫ t in (-((K + 1 : ℕ) : ℝ))..((K + 1 : ℕ) : ℝ),
          cglSmoothedNonprincipalDetectorMellinIntegrand X n Y
            (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).toCGLNonprincipalCriticalStripLZero
            ((((1 / 2 : ℝ) - z.1.1.re : ℝ) : ℂ) + (t : ℂ) * I)) := by ring
    _ = _ := by rw [hminusI_mul_I, one_mul]

end RHTower
