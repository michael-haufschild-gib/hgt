/-
# Quantitative safe-line tails for Chen--Gupta--Li Class I

This module replaces qualitative truncation of the actual CGL left Mellin
line with a closed exponential exterior bound.  Gamma decay is uniform over
the full moving strip `Re(w) ∈ [-1/2,0]`; the smoothing factor is contractive
there; the finite mollifier is closed by its cutoff; and the primitive
Dirichlet L-function has cubic strip growth.  Polynomial absorption then
leaves rate `exp (-pi |t| / 4)`, whose two rays integrate exactly.

The resulting `log^(2 : ℕ) T` tail tends to zero at the literal source cutoff,
uniformly in the smoothing scale `Y`.  A pole-avoiding functional-equation
edge and Phragmén--Lindelöf propagation additionally replace the old
character-dependent strip constant by an explicit universal coefficient
times conductor squared.  The final pointwise and two-ray bounds therefore
hold simultaneously for every primitive source row.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiClassIILeftIntegrand
import GaloisForLFunctions.RHTower.DirichletLPhragmenInputs
import GaloisForLFunctions.RHTower.ChenGuptaLiPoleAvoidingConductorStrip
import GaloisForLFunctions.RHTower.SelbergClass.BarnesHorizontalEdges
import GaloisForLFunctions.RHTower.PerronPolyExpAbsorb
import GaloisForLFunctions.RHTower.LegStripThreshold

open Complex Set MeasureTheory Filter Topology

noncomputable section

namespace RHTower

/-- The CGL left-line integrand has one conductor-explicit polynomial-times-
Gamma envelope simultaneously for every primitive source row.  Unlike the
fixed-row theorem below, the only row dependence is displayed explicitly as
`(n+1)²`; neither existential witness depends on the character or conductor. -/
theorem exists_uniform_norm_cglPrimitiveClassI_leftLineIntegrand_polynomialExponential_le :
    ∃ (CΓ : ℝ) (NΓ : ℕ), 0 ≤ CΓ ∧
      ∀ (X n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
        (z : CGLPrimitiveClassIWindowZero n χ τ H) (Y : ℕ) (t : ℝ), 1 ≤ |t| →
        ‖cglSmoothedNonprincipalDetectorMellinIntegrand X n Y
          (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).toCGLNonprincipalCriticalStripLZero
          (cglPrimitiveClassILeftLinePoint n χ τ H z t)‖ ≤
          (CΓ * (X + 1 : ℕ) *
            (4 * cglDirichletLRightEdgeConstant * (n + 1 : ℕ) ^ (2 : ℝ)) *
            (‖z.1.1‖ + 5) ^ 3) * |t| ^ (NΓ + 3) *
              Real.exp (-(Real.pi * |t| / 2)) := by
  obtain ⟨CΓ, NΓ, hCΓ, hΓ⟩ :=
    exists_bound_norm_Gamma_vertical_strip_arbitrary (a := -(1 / 2 : ℝ)) (b := 0)
  refine ⟨CΓ, NΓ, hCΓ, ?_⟩
  intro X n χ τ H z Y t ht
  have hzlt :=
    (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).lt_one
  change z.1.1.re < 1 at hzlt
  have hsmooth :
      ‖((Y + 1 : ℕ) : ℂ) ^ (cglPrimitiveClassILeftLinePoint n χ τ H z t)‖ ≤ 1 := by
    have hYpos : (0 : ℝ) < (Y + 1 : ℕ) := by positivity
    have hYone : (1 : ℝ) ≤ (Y + 1 : ℕ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le Y)
    rw [show ((Y + 1 : ℕ) : ℂ) = (((Y + 1 : ℕ) : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos hYpos]
    apply Real.rpow_le_one_of_one_le_of_nonpos hYone
    simp only [cglPrimitiveClassILeftLinePoint, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero]
    linarith [z.2]
  have hGamma :
      ‖Complex.Gamma (cglPrimitiveClassILeftLinePoint n χ τ H z t)‖ ≤
        CΓ * |t| ^ NΓ * Real.exp (-(Real.pi * |t| / 2)) := by
    have hbase := hΓ ((1 / 2 : ℝ) - z.1.1.re) t (by linarith) (by linarith [z.2]) ht
    simpa [cglPrimitiveClassILeftLinePoint] using hbase
  let P : CGLLemma62PrimitiveCharacter :=
    { modulus := ⟨n + 1, Nat.succ_pos n⟩
      character := χ.1.1
      nonprincipal := χ.1.2
      primitive := χ.2 }
  have hordinate :
      4 + |z.1.1.im + t| ≤ (‖z.1.1‖ + 5) * |t| := by
    have him : |z.1.1.im| ≤ ‖z.1.1‖ := Complex.abs_im_le_norm z.1.1
    have hadd := abs_add_le z.1.1.im t
    have ht0 := abs_nonneg t
    have hz0 := norm_nonneg z.1.1
    nlinarith
  have hL0 := norm_primitiveLFunction_criticalLine_conductorUniform_le P
    (z.1.1.im + t)
  have hpower : (4 + |z.1.1.im + t|) ^ 3 ≤
      ((‖z.1.1‖ + 5) * |t|) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hordinate 3
  have hA : 0 ≤ 4 * cglDirichletLRightEdgeConstant *
      (n + 1 : ℕ) ^ (2 : ℝ) := by
    exact mul_nonneg (mul_nonneg (by norm_num) cglDirichletLRightEdgeConstant_pos.le)
      (Real.rpow_nonneg (by positivity) _)
  have hL :
      ‖DirichletCharacter.LFunction χ.1.1
        (cglCriticalLinePoint (z.1.1.im + t)).1‖ ≤
        (4 * cglDirichletLRightEdgeConstant * (n + 1 : ℕ) ^ (2 : ℝ)) *
          ((‖z.1.1‖ + 5) * |t|) ^ 3 := by
    change ‖DirichletCharacter.LFunction P.character
      ((1 / 2 : ℂ) + ((z.1.1.im + t : ℝ) : ℂ) * I)‖ ≤ _
    exact hL0.trans (mul_le_mul_of_nonneg_left hpower hA)
  have hM := norm_cglPrimitiveClassILeftLine_mollifier_le X n χ τ H z t
  rw [cglPrimitiveClassI_leftLineIntegrand_eq_weight_mul_LValue,
    cglPrimitiveClassILeftLineWeight, norm_mul, norm_mul, norm_mul]
  calc
    ‖((Y + 1 : ℕ) : ℂ) ^ cglPrimitiveClassILeftLinePoint n χ τ H z t‖ *
          ‖Complex.Gamma (cglPrimitiveClassILeftLinePoint n χ τ H z t)‖ *
          ‖zeroDetectionMobiusPolynomial X (n + 1) χ.1.1
            (cglCriticalLinePoint (z.1.1.im + t)).1‖ *
          ‖DirichletCharacter.LFunction χ.1.1
            (cglCriticalLinePoint (z.1.1.im + t)).1‖
        ≤ 1 * (CΓ * |t| ^ NΓ * Real.exp (-(Real.pi * |t| / 2))) *
          (X + 1 : ℕ) *
            ((4 * cglDirichletLRightEdgeConstant * (n + 1 : ℕ) ^ (2 : ℝ)) *
              ((‖z.1.1‖ + 5) * |t|) ^ 3) := by
            gcongr
    _ = (CΓ * (X + 1 : ℕ) *
          (4 * cglDirichletLRightEdgeConstant * (n + 1 : ℕ) ^ (2 : ℝ)) *
          (‖z.1.1‖ + 5) ^ 3) * (|t| ^ NΓ * |t| ^ 3) *
            Real.exp (-(Real.pi * |t| / 2)) := by
          rw [mul_pow]
          ring
    _ = (CΓ * (X + 1 : ℕ) *
          (4 * cglDirichletLRightEdgeConstant * (n + 1 : ℕ) ^ (2 : ℝ)) *
          (‖z.1.1‖ + 5) ^ 3) * |t| ^ (NΓ + 3) *
            Real.exp (-(Real.pi * |t| / 2)) := by
          rw [pow_add]

/-- The actual CGL left-line integrand has a polynomial times sharp Gamma
envelope, uniformly in the smoothing scale `Y`.  The exponent is universal;
the amplitude inherits the current character-dependent L-strip constant. -/
theorem exists_norm_cglPrimitiveClassI_leftLineIntegrand_polynomialExponential_le
    (X n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLPrimitiveClassIWindowZero n χ τ H) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ (Y : ℕ) (t : ℝ), 1 ≤ |t| →
      ‖cglSmoothedNonprincipalDetectorMellinIntegrand X n Y
        (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).toCGLNonprincipalCriticalStripLZero
        (cglPrimitiveClassILeftLinePoint n χ τ H z t)‖ ≤
        C * |t| ^ N * Real.exp (-(Real.pi * |t| / 2)) := by
  obtain ⟨CΓ, NΓ, hCΓ, hΓ⟩ :=
    exists_bound_norm_Gamma_vertical_strip_arbitrary (a := -(1 / 2 : ℝ)) (b := 0)
  obtain ⟨CL, hCL, hL⟩ := bound_LFunction_strip χ.1.2 χ.2
  refine ⟨CΓ * (X + 1 : ℕ) * CL * (‖z.1.1‖ + 5) ^ 3, NΓ + 3, by positivity, ?_⟩
  intro Y t ht
  have hzlt :=
    (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).lt_one
  change z.1.1.re < 1 at hzlt
  have hsmooth :
      ‖((Y + 1 : ℕ) : ℂ) ^ (cglPrimitiveClassILeftLinePoint n χ τ H z t)‖ ≤ 1 := by
    have hYpos : (0 : ℝ) < (Y + 1 : ℕ) := by positivity
    have hYone : (1 : ℝ) ≤ (Y + 1 : ℕ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le Y)
    rw [show ((Y + 1 : ℕ) : ℂ) = (((Y + 1 : ℕ) : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos hYpos]
    apply Real.rpow_le_one_of_one_le_of_nonpos hYone
    simp only [cglPrimitiveClassILeftLinePoint, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero]
    linarith [z.2]
  have hGamma :
      ‖Complex.Gamma (cglPrimitiveClassILeftLinePoint n χ τ H z t)‖ ≤
        CΓ * |t| ^ NΓ * Real.exp (-(Real.pi * |t| / 2)) := by
    have hbase := hΓ ((1 / 2 : ℝ) - z.1.1.re) t (by linarith) (by linarith [z.2]) ht
    simpa [cglPrimitiveClassILeftLinePoint] using hbase
  have hpoint :
      ‖(cglCriticalLinePoint (z.1.1.im + t)).1 - 4‖ ≤
        (‖z.1.1‖ + 5) * |t| := by
    have him : |z.1.1.im| ≤ ‖z.1.1‖ := Complex.abs_im_le_norm z.1.1
    have ht0 : 0 ≤ |t| := abs_nonneg _
    have hz0 : 0 ≤ ‖z.1.1‖ := norm_nonneg _
    change ‖((1 / 2 : ℂ) + ((z.1.1.im + t : ℝ) : ℂ) * I) - 4‖ ≤ _
    calc
      ‖((1 / 2 : ℂ) + ((z.1.1.im + t : ℝ) : ℂ) * I) - 4‖
          ≤ ‖((1 / 2 : ℂ) - 4)‖ + ‖((z.1.1.im + t : ℝ) : ℂ) * I‖ := by
            convert norm_add_le ((1 / 2 : ℂ) - 4)
              (((z.1.1.im + t : ℝ) : ℂ) * I) using 1
            all_goals ring
      _ = 7 / 2 + |z.1.1.im + t| := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
            norm_num
      _ ≤ 7 / 2 + |z.1.1.im| + |t| := by
            linarith [abs_add_le z.1.1.im t]
      _ ≤ (‖z.1.1‖ + 5) * |t| := by
            nlinarith
  have hL0 := hL (cglCriticalLinePoint (z.1.1.im + t)).1
    (by norm_num [cglCriticalLinePoint]) (by norm_num [cglCriticalLinePoint])
  have hpower :
      ‖(cglCriticalLinePoint (z.1.1.im + t)).1 - 4‖ ^ 3 ≤
        ((‖z.1.1‖ + 5) * |t|) ^ 3 :=
    pow_le_pow_left₀ (norm_nonneg _) hpoint 3
  have hL :
      ‖DirichletCharacter.LFunction χ.1.1
        (cglCriticalLinePoint (z.1.1.im + t)).1‖ ≤
        CL * ((‖z.1.1‖ + 5) * |t|) ^ 3 :=
    hL0.trans (mul_le_mul_of_nonneg_left hpower hCL.le)
  have hM := norm_cglPrimitiveClassILeftLine_mollifier_le X n χ τ H z t
  rw [cglPrimitiveClassI_leftLineIntegrand_eq_weight_mul_LValue,
    cglPrimitiveClassILeftLineWeight, norm_mul, norm_mul, norm_mul]
  calc
    ‖((Y + 1 : ℕ) : ℂ) ^ cglPrimitiveClassILeftLinePoint n χ τ H z t‖ *
          ‖Complex.Gamma (cglPrimitiveClassILeftLinePoint n χ τ H z t)‖ *
          ‖zeroDetectionMobiusPolynomial X (n + 1) χ.1.1
            (cglCriticalLinePoint (z.1.1.im + t)).1‖ *
          ‖DirichletCharacter.LFunction χ.1.1
            (cglCriticalLinePoint (z.1.1.im + t)).1‖
        ≤ 1 * (CΓ * |t| ^ NΓ * Real.exp (-(Real.pi * |t| / 2))) *
          (X + 1 : ℕ) * (CL * ((‖z.1.1‖ + 5) * |t|) ^ 3) := by
            gcongr
    _ = (CΓ * (X + 1 : ℕ) * CL * (‖z.1.1‖ + 5) ^ 3) *
          (|t| ^ NΓ * |t| ^ 3) * Real.exp (-(Real.pi * |t| / 2)) := by
            rw [mul_pow]
            ring
    _ = (CΓ * (X + 1 : ℕ) * CL * (‖z.1.1‖ + 5) ^ 3) *
          |t| ^ (NΓ + 3) * Real.exp (-(Real.pi * |t| / 2)) := by
            rw [pow_add]

/-- Polynomial absorption is universal across all primitive source rows.  The
remaining amplitude displays every dependence on cutoff, conductor, and zero
geometry; `D` depends only on the fixed Gamma strip. -/
theorem exists_uniform_norm_cglPrimitiveClassI_leftLineIntegrand_exponential_le :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ (X n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
        (z : CGLPrimitiveClassIWindowZero n χ τ H) (Y : ℕ) (t : ℝ), 1 ≤ |t| →
        ‖cglSmoothedNonprincipalDetectorMellinIntegrand X n Y
          (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).toCGLNonprincipalCriticalStripLZero
          (cglPrimitiveClassILeftLinePoint n χ τ H z t)‖ ≤
          (D * (X + 1 : ℕ) *
            (4 * cglDirichletLRightEdgeConstant * (n + 1 : ℕ) ^ (2 : ℝ)) *
            (‖z.1.1‖ + 5) ^ 3) * Real.exp (-(Real.pi * |t| / 4)) := by
  obtain ⟨CΓ, NΓ, hCΓ, hbound⟩ :=
    exists_uniform_norm_cglPrimitiveClassI_leftLineIntegrand_polynomialExponential_le
  let D : ℝ := CΓ * ((NΓ + 3).factorial : ℝ) *
    (2 / (Real.pi / 2)) ^ (NΓ + 3)
  refine ⟨D, by dsimp [D]; positivity, ?_⟩
  intro X n χ τ H z Y t ht
  have habsorb := pow_mul_exp_neg_le_absorb_half
    (b := Real.pi / 2) (u := |t|) (by positivity) (abs_nonneg t) (NΓ + 3)
  have habsorb' :
      |t| ^ (NΓ + 3) * Real.exp (-(Real.pi * |t| / 2)) ≤
        ((NΓ + 3).factorial : ℝ) * (2 / (Real.pi / 2)) ^ (NΓ + 3) *
          Real.exp (-(Real.pi * |t| / 4)) := by
    convert habsorb using 1 <;> ring
  have hpoly := hbound X n χ τ H z Y t ht
  have hrow : 0 ≤ (X + 1 : ℕ) *
      (4 * cglDirichletLRightEdgeConstant * (n + 1 : ℕ) ^ (2 : ℝ)) *
      (‖z.1.1‖ + 5) ^ 3 := by
    exact mul_nonneg
      (mul_nonneg (by positivity)
        (mul_nonneg (mul_nonneg (by norm_num) cglDirichletLRightEdgeConstant_pos.le)
          (Real.rpow_nonneg (by positivity) _)))
      (by positivity)
  calc
    ‖cglSmoothedNonprincipalDetectorMellinIntegrand X n Y
        (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).toCGLNonprincipalCriticalStripLZero
        (cglPrimitiveClassILeftLinePoint n χ τ H z t)‖
      ≤ (CΓ * (X + 1 : ℕ) *
          (4 * cglDirichletLRightEdgeConstant * (n + 1 : ℕ) ^ (2 : ℝ)) *
          (‖z.1.1‖ + 5) ^ 3) *
            |t| ^ (NΓ + 3) * Real.exp (-(Real.pi * |t| / 2)) := hpoly
    _ = (CΓ * ((X + 1 : ℕ) *
          (4 * cglDirichletLRightEdgeConstant * (n + 1 : ℕ) ^ (2 : ℝ)) *
          (‖z.1.1‖ + 5) ^ 3)) *
            (|t| ^ (NΓ + 3) * Real.exp (-(Real.pi * |t| / 2))) := by ring
    _ ≤ (CΓ * ((X + 1 : ℕ) *
          (4 * cglDirichletLRightEdgeConstant * (n + 1 : ℕ) ^ (2 : ℝ)) *
          (‖z.1.1‖ + 5) ^ 3)) *
            (((NΓ + 3).factorial : ℝ) * (2 / (Real.pi / 2)) ^ (NΓ + 3) *
              Real.exp (-(Real.pi * |t| / 4))) := by
      exact mul_le_mul_of_nonneg_left habsorb' (mul_nonneg hCΓ hrow)
    _ = (D * (X + 1 : ℕ) *
          (4 * cglDirichletLRightEdgeConstant * (n + 1 : ℕ) ^ (2 : ℝ)) *
          (‖z.1.1‖ + 5) ^ 3) * Real.exp (-(Real.pi * |t| / 4)) := by
      dsimp [D]
      ring

/-- Half of the Gamma exponential rate absorbs every polynomial factor,
leaving an integrable envelope uniform in `Y`. -/
theorem exists_norm_cglPrimitiveClassI_leftLineIntegrand_exponential_le
    (X n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLPrimitiveClassIWindowZero n χ τ H) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (Y : ℕ) (t : ℝ), 1 ≤ |t| →
      ‖cglSmoothedNonprincipalDetectorMellinIntegrand X n Y
        (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).toCGLNonprincipalCriticalStripLZero
        (cglPrimitiveClassILeftLinePoint n χ τ H z t)‖ ≤
        A * Real.exp (-(Real.pi * |t| / 4)) := by
  obtain ⟨C, N, hC, hbound⟩ :=
    exists_norm_cglPrimitiveClassI_leftLineIntegrand_polynomialExponential_le X n χ τ H z
  let A : ℝ := C * (N.factorial : ℝ) * (2 / (Real.pi / 2)) ^ N
  refine ⟨A, by dsimp [A]; positivity, ?_⟩
  intro Y t ht
  have habsorb := pow_mul_exp_neg_le_absorb_half
    (b := Real.pi / 2) (u := |t|) (by positivity) (abs_nonneg t) N
  have habsorb' :
      |t| ^ N * Real.exp (-(Real.pi * |t| / 2)) ≤
        (N.factorial : ℝ) * (2 / (Real.pi / 2)) ^ N *
          Real.exp (-(Real.pi * |t| / 4)) := by
    convert habsorb using 1 <;> ring
  calc
    ‖cglSmoothedNonprincipalDetectorMellinIntegrand X n Y
        (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).toCGLNonprincipalCriticalStripLZero
        (cglPrimitiveClassILeftLinePoint n χ τ H z t)‖
      ≤ C * |t| ^ N * Real.exp (-(Real.pi * |t| / 2)) := hbound Y t ht
    _ = C * (|t| ^ N * Real.exp (-(Real.pi * |t| / 2))) := by ring
    _ ≤ C * ((N.factorial : ℝ) * (2 / (Real.pi / 2)) ^ N *
          Real.exp (-(Real.pi * |t| / 4))) :=
      mul_le_mul_of_nonneg_left habsorb' hC
    _ = A * Real.exp (-(Real.pi * |t| / 4)) := by
      dsimp [A]
      ring

/-- Sum of the two exterior rays outside the symmetric CGL truncation. -/
def cglPrimitiveClassILeftLineExteriorIntegral
    (X n Y : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLPrimitiveClassIWindowZero n χ τ H) (B : ℝ) : ℂ :=
  (∫ t in Iic (-B),
    cglSmoothedNonprincipalDetectorMellinIntegrand X n Y
      (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).toCGLNonprincipalCriticalStripLZero
      (cglPrimitiveClassILeftLinePoint n χ τ H z t)) +
  (∫ t in Ici B,
    cglSmoothedNonprincipalDetectorMellinIntegrand X n Y
      (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).toCGLNonprincipalCriticalStripLZero
      (cglPrimitiveClassILeftLinePoint n χ τ H z t))

/-- Exact two-ray integration of any certified CGL pointwise exponential
majorant.  This form preserves explicit conductor dependence. -/
theorem cglPrimitiveClassI_leftLine_exteriorIntegral_exponential_bound_of_pointwise
    (X n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLPrimitiveClassIWindowZero n χ τ H) (A : ℝ)
    (hbound : ∀ (Y : ℕ) (t : ℝ), 1 ≤ |t| →
      ‖cglSmoothedNonprincipalDetectorMellinIntegrand X n Y
        (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).toCGLNonprincipalCriticalStripLZero
        (cglPrimitiveClassILeftLinePoint n χ τ H z t)‖ ≤
        A * Real.exp (-(Real.pi * |t| / 4))) :
    ∀ (Y : ℕ) (B : ℝ), 1 ≤ B →
      ‖cglPrimitiveClassILeftLineExteriorIntegral X n Y χ τ H z B‖ ≤
        (8 * A / Real.pi) * Real.exp (-(Real.pi * B / 4)) := by
  intro Y B hB
  let f : ℝ → ℂ := fun t =>
    cglSmoothedNonprincipalDetectorMellinIntegrand X n Y
      (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).toCGLNonprincipalCriticalStripLZero
      (cglPrimitiveClassILeftLinePoint n χ τ H z t)
  have hrightMajor : IntegrableOn
      (fun t : ℝ => A * Real.exp (-(Real.pi / 4) * t)) (Ici B) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact (integrableOn_exp_mul_Ioi (a := -(Real.pi / 4))
      (by have := Real.pi_pos; linarith) B).const_mul A
  have hrightPoint : ∀ᵐ t ∂volume.restrict (Ici B),
      ‖f t‖ ≤ A * Real.exp (-(Real.pi / 4) * t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t htmem
    change B ≤ t at htmem
    have ht0 : 0 ≤ t := by linarith
    have ht1 : 1 ≤ |t| := by rw [abs_of_nonneg ht0]; linarith
    have h := hbound Y t ht1
    dsimp [f]
    rw [abs_of_nonneg ht0] at h
    convert h using 1
    all_goals ring
  have hrightNorm := norm_integral_le_of_norm_le hrightMajor hrightPoint
  have hright :
      ‖∫ t in Ici B, f t‖ ≤
        (4 * A / Real.pi) * Real.exp (-(Real.pi * B / 4)) := by
    calc
      ‖∫ t in Ici B, f t‖
          ≤ ∫ t in Ici B, A * Real.exp (-(Real.pi / 4) * t) := hrightNorm
      _ = A * (∫ t in Ici B, Real.exp (-(Real.pi / 4) * t)) := by
            rw [integral_const_mul]
      _ = A * (-Real.exp (-(Real.pi / 4) * B) / (-(Real.pi / 4))) := by
            rw [integral_Ici_eq_integral_Ioi,
              integral_exp_mul_Ioi (a := -(Real.pi / 4))
                (by have := Real.pi_pos; linarith) B]
      _ = (4 * A / Real.pi) * Real.exp (-(Real.pi * B / 4)) := by
            field_simp [ne_of_gt Real.pi_pos]
  have hleftMajor : IntegrableOn
      (fun t : ℝ => A * Real.exp ((Real.pi / 4) * t)) (Iic (-B)) := by
    exact (integrableOn_exp_mul_Iic (a := Real.pi / 4) (by positivity) (-B)).const_mul A
  have hleftPoint : ∀ᵐ t ∂volume.restrict (Iic (-B)),
      ‖f t‖ ≤ A * Real.exp ((Real.pi / 4) * t) := by
    filter_upwards [ae_restrict_mem measurableSet_Iic] with t htmem
    change t ≤ -B at htmem
    have ht0 : t ≤ 0 := by linarith
    have ht1 : 1 ≤ |t| := by rw [abs_of_nonpos ht0]; linarith
    have h := hbound Y t ht1
    dsimp [f]
    rw [abs_of_nonpos ht0] at h
    convert h using 1
    all_goals ring
  have hleftNorm := norm_integral_le_of_norm_le hleftMajor hleftPoint
  have hleft :
      ‖∫ t in Iic (-B), f t‖ ≤
        (4 * A / Real.pi) * Real.exp (-(Real.pi * B / 4)) := by
    calc
      ‖∫ t in Iic (-B), f t‖
          ≤ ∫ t in Iic (-B), A * Real.exp ((Real.pi / 4) * t) := hleftNorm
      _ = A * (∫ t in Iic (-B), Real.exp ((Real.pi / 4) * t)) := by
            rw [integral_const_mul]
      _ = A * (Real.exp ((Real.pi / 4) * (-B)) / (Real.pi / 4)) := by
            rw [integral_exp_mul_Iic (a := Real.pi / 4) (by positivity) (-B)]
      _ = (4 * A / Real.pi) * Real.exp (-(Real.pi * B / 4)) := by
            field_simp [ne_of_gt Real.pi_pos]
  change ‖(∫ t in Iic (-B), f t) + (∫ t in Ici B, f t)‖ ≤ _
  calc
    ‖(∫ t in Iic (-B), f t) + (∫ t in Ici B, f t)‖
        ≤ ‖∫ t in Iic (-B), f t‖ + ‖∫ t in Ici B, f t‖ := norm_add_le _ _
    _ ≤ (4 * A / Real.pi) * Real.exp (-(Real.pi * B / 4)) +
        (4 * A / Real.pi) * Real.exp (-(Real.pi * B / 4)) := add_le_add hleft hright
    _ = (8 * A / Real.pi) * Real.exp (-(Real.pi * B / 4)) := by ring

/-- Exact two-ray integration gives an exterior bound of rate
`exp (-pi B / 4)`, uniformly in `Y`. -/
theorem exists_cglPrimitiveClassI_leftLine_exteriorIntegral_exponential_bound
    (X n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLPrimitiveClassIWindowZero n χ τ H) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (Y : ℕ) (B : ℝ), 1 ≤ B →
      ‖cglPrimitiveClassILeftLineExteriorIntegral X n Y χ τ H z B‖ ≤
        (8 * A / Real.pi) * Real.exp (-(Real.pi * B / 4)) := by
  obtain ⟨A, hA, hbound⟩ :=
    exists_norm_cglPrimitiveClassI_leftLineIntegrand_exponential_le X n χ τ H z
  exact ⟨A, hA,
    cglPrimitiveClassI_leftLine_exteriorIntegral_exponential_bound_of_pointwise
      X n χ τ H z A hbound⟩

/-- The actual two-sided CGL exterior integral has a conductor-explicit bound
with one universal amplitude constant for every primitive source row. -/
theorem exists_uniform_cglPrimitiveClassI_leftLine_exteriorIntegral_exponential_bound :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ (X n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
        (z : CGLPrimitiveClassIWindowZero n χ τ H) (Y : ℕ) (B : ℝ), 1 ≤ B →
        ‖cglPrimitiveClassILeftLineExteriorIntegral X n Y χ τ H z B‖ ≤
          (8 * (D * (X + 1 : ℕ) *
            (4 * cglDirichletLRightEdgeConstant * (n + 1 : ℕ) ^ (2 : ℝ)) *
            (‖z.1.1‖ + 5) ^ 3) / Real.pi) *
              Real.exp (-(Real.pi * B / 4)) := by
  obtain ⟨D, hD, hpoint⟩ :=
    exists_uniform_norm_cglPrimitiveClassI_leftLineIntegrand_exponential_le
  refine ⟨D, hD, ?_⟩
  intro X n χ τ H z Y B hB
  let A : ℝ := D * (X + 1 : ℕ) *
    (4 * cglDirichletLRightEdgeConstant * (n + 1 : ℕ) ^ (2 : ℝ)) *
    (‖z.1.1‖ + 5) ^ 3
  have hbound : ∀ (Y' : ℕ) (t : ℝ), 1 ≤ |t| →
      ‖cglSmoothedNonprincipalDetectorMellinIntegrand X n Y'
        (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).toCGLNonprincipalCriticalStripLZero
        (cglPrimitiveClassILeftLinePoint n χ τ H z t)‖ ≤
        A * Real.exp (-(Real.pi * |t| / 4)) := by
    intro Y' t ht
    exact hpoint X n χ τ H z Y' t ht
  exact cglPrimitiveClassI_leftLine_exteriorIntegral_exponential_bound_of_pointwise
    X n χ τ H z A hbound Y B hB

/-- The exact source majorant at `B = log^(2 : ℕ) T` tends to zero. -/
theorem tendsto_cglSafeLine_logSquareMajorant_zero (A : ℝ) :
    Tendsto (fun T : ℝ =>
      (8 * A / Real.pi) * Real.exp (-(Real.pi * Real.log T ^ 2 / 4)))
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun T : ℝ => Real.log T) atTop atTop := Real.tendsto_log_atTop
  have hsq : Tendsto (fun T : ℝ => Real.log T ^ 2) atTop atTop := by
    simpa only [pow_two] using hlog.atTop_mul_atTop₀ hlog
  have hgain : Tendsto (fun T : ℝ =>
      (Real.pi / 4) * Real.log T ^ 2) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by positivity) hsq
  have hexp := Real.tendsto_exp_neg_atTop_nhds_zero.comp hgain
  have hscaled := hexp.const_mul (8 * A / Real.pi)
  have hscaled0 : Tendsto (fun T : ℝ =>
      (8 * A / Real.pi) * Real.exp (-((Real.pi / 4) * Real.log T ^ 2)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero] using hscaled
  apply hscaled0.congr'
  exact Eventually.of_forall fun T => by
    ring

/-- At CGL's literal `log^(2 : ℕ) T` cutoff, the actual two-sided left-line tail
tends to zero for every fixed primitive row, uniformly in `Y`. -/
theorem tendsto_cglPrimitiveClassI_leftLine_logSquareExteriorIntegral
    (X n Y : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLPrimitiveClassIWindowZero n χ τ H) :
    Tendsto (fun T : ℝ =>
      ‖cglPrimitiveClassILeftLineExteriorIntegral X n Y χ τ H z
        (Real.log T ^ 2)‖) atTop (𝓝 0) := by
  obtain ⟨A, _, hbound⟩ :=
    exists_cglPrimitiveClassI_leftLine_exteriorIntegral_exponential_bound X n χ τ H z
  have hlog : Tendsto (fun T : ℝ => Real.log T) atTop atTop := Real.tendsto_log_atTop
  have hcutoff : ∀ᶠ T : ℝ in atTop, 1 ≤ Real.log T ^ 2 := by
    filter_upwards [hlog.eventually (eventually_ge_atTop (1 : ℝ))] with T hT
    nlinarith [sq_nonneg (Real.log T - 1)]
  refine squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) ?_
    (tendsto_cglSafeLine_logSquareMajorant_zero A)
  filter_upwards [hcutoff] with T hT
  exact hbound Y (Real.log T ^ 2) hT

end RHTower
