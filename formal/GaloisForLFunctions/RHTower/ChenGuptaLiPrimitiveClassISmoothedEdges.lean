/-
# Smoothed horizontal-edge decay for Chen--Gupta--Li class-I detectors

This is the horizontal estimate for the actual CGL Section 12 smoothing
factor `(Y + 1)^w`, rather than its unsmoothed auxiliary integrand.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiPrimitiveClassIHorizontalEdges
import GaloisForLFunctions.RHTower.ChenGuptaLiSmoothedNonprincipalContour

open Complex Filter Topology intervalIntegral

noncomputable section

namespace RHTower

/-- On the canonical horizontal class-I edges, CGL's literal Mellin smoothing
factor has a closed bound depending only on its integer scale. -/
theorem norm_cglClassISmoothingWeight_le
    (Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLPrimitiveClassIWindowZero n χ τ H)
    (u : Set.Icc ((1 / 2 : ℝ) - z.1.1.re) 2)
    (ε : CGLClassIHorizontalEdgeSign) (K : ℕ) :
    ‖((Y + 1 : ℕ) : ℂ) ^ ((u.1 : ℂ) +
      ((ε.1 * (K + 1 : ℕ) : ℝ) : ℂ) * I)‖ ≤ (Y + 1 : ℕ) ^ (2 : ℕ) := by
  have hYpos : (0 : ℝ) < (Y + 1 : ℕ) := by positivity
  have hYone : (1 : ℝ) ≤ (Y + 1 : ℕ) := by
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le Y))
  have hre : ((u.1 : ℂ) + ((ε.1 * (K + 1 : ℕ) : ℝ) : ℂ) * I).re = u.1 := by
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero]
    ring
  rw [show ((Y + 1 : ℕ) : ℂ) = (((Y + 1 : ℕ) : ℝ) : ℂ) by norm_num,
    Complex.norm_cpow_eq_rpow_re_of_pos hYpos, hre]
  calc
    ((Y + 1 : ℕ) : ℝ) ^ u.1 ≤ ((Y + 1 : ℕ) : ℝ) ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hYone u.2.2
    _ = (Y + 1 : ℕ) ^ (2 : ℕ) := by norm_num

/-- Uniform polynomial-exponential control of the genuinely smoothed CGL
class-I detector integrand on both canonical finite horizontal edges. -/
theorem exists_norm_cglPrimitiveClassISmoothedHorizontalDetectorMellinIntegrand_le
    (X n Y : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLPrimitiveClassIWindowZero n χ τ H) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀
      (u : Set.Icc ((1 / 2 : ℝ) - z.1.1.re) 2)
      (ε : CGLClassIHorizontalEdgeSign) (K : ℕ),
      ‖cglSmoothedNonprincipalDetectorMellinIntegrand X n Y
        (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).toCGLNonprincipalCriticalStripLZero
        ((u.1 : ℂ) + ((ε.1 * (K + 1 : ℕ) : ℝ) : ℂ) * I)‖ ≤
        C * (K + 1 : ℕ) ^ N * Real.exp (-(Real.pi * (K + 1 : ℕ) / 2)) := by
  obtain ⟨C, N, hC, hbound⟩ :=
    exists_norm_cglPrimitiveClassIHorizontalSignedDetectorMellinIntegrand_le X n χ τ H z
  refine ⟨(Y + 1 : ℕ) ^ (2 : ℕ) * C, N, by positivity, ?_⟩
  intro u ε K
  have hweight := norm_cglClassISmoothingWeight_le Y n χ τ H z u ε K
  have hdetector := hbound u ε K
  unfold cglSmoothedNonprincipalDetectorMellinIntegrand
  rw [norm_mul]
  calc
    ‖((Y + 1 : ℕ) : ℂ) ^ ((u.1 : ℂ) + ((ε.1 * (K + 1 : ℕ) : ℝ) : ℂ) * I)‖ *
        ‖cglDetectorMellinIntegrand X n
          (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).toCGLNonprincipalCriticalStripLZero.toCGLCriticalStripLZero
          ((u.1 : ℂ) + ((ε.1 * (K + 1 : ℕ) : ℝ) : ℂ) * I)‖ ≤
        ((Y + 1 : ℕ) ^ (2 : ℕ) : ℝ) *
          (C * (K + 1 : ℕ) ^ N * Real.exp (-(Real.pi * (K + 1 : ℕ) / 2))) :=
      mul_le_mul hweight hdetector (norm_nonneg _) (by positivity)
    _ = ((Y + 1 : ℕ) ^ (2 : ℕ) * C) *
          (K + 1 : ℕ) ^ N * Real.exp (-(Real.pi * (K + 1 : ℕ) / 2)) := by ring

/-- The genuinely smoothed finite horizontal class-I edge integrals obey the
same closed polynomial-exponential envelope. -/
theorem exists_norm_cglPrimitiveClassISmoothedHorizontalEdgeIntegral_le
    (X n Y : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLPrimitiveClassIWindowZero n χ τ H) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ (ε : CGLClassIHorizontalEdgeSign) (K : ℕ),
      ‖∫ u in ((1 / 2 : ℝ) - z.1.1.re)..2,
        cglSmoothedNonprincipalDetectorMellinIntegrand X n Y
          (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).toCGLNonprincipalCriticalStripLZero
          ((u : ℂ) + ((ε.1 * (K + 1 : ℕ) : ℝ) : ℂ) * I)‖ ≤
        (C * (K + 1 : ℕ) ^ N * Real.exp (-(Real.pi * (K + 1 : ℕ) / 2))) *
          |2 - ((1 / 2 : ℝ) - z.1.1.re)| := by
  obtain ⟨C, N, hC, hbound⟩ :=
    exists_norm_cglPrimitiveClassISmoothedHorizontalDetectorMellinIntegrand_le X n Y χ τ H z
  refine ⟨C, N, hC, ?_⟩
  intro ε K
  have hleft : (1 / 2 : ℝ) - z.1.1.re ≤ 2 := by linarith [z.2]
  exact intervalIntegral.norm_integral_le_of_norm_le_const (fun u hu => by
    rw [Set.uIoc_of_le hleft] at hu
    simpa using hbound ⟨u, hu.1.le, hu.2⟩ ε K)


/-- The genuinely smoothed horizontal detector integral at either certified
class-I orientation tends to zero along the literal canonical heights. -/
theorem tendsto_cglPrimitiveClassISmoothedHorizontalSignedEdgeIntegral
    (X n Y : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLPrimitiveClassIWindowZero n χ τ H) (ε : CGLClassIHorizontalEdgeSign) :
    Tendsto (fun K : ℕ =>
      ∫ u in ((1 / 2 : ℝ) - z.1.1.re)..2,
        cglSmoothedNonprincipalDetectorMellinIntegrand X n Y
          (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).toCGLNonprincipalCriticalStripLZero
          ((u : ℂ) + ((ε.1 * (K + 1 : ℕ) : ℝ) : ℂ) * I)) atTop (𝓝 0) := by
  obtain ⟨C, N, _, hbound⟩ :=
    exists_norm_cglPrimitiveClassISmoothedHorizontalEdgeIntegral_le X n Y χ τ H z
  have hcore : Tendsto (fun T : ℝ => C * T ^ N *
      Real.exp (-((Real.pi / 2) * T))) atTop (𝓝 0) :=
    tendsto_const_mul_pow_mul_exp_neg (by positivity) N C
  have hheight : Tendsto (fun K : ℕ => (K : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hcoreK := hcore.comp hheight
  have hcoreK' : Tendsto (fun K : ℕ => C * (K + 1 : ℕ) ^ N *
      Real.exp (-(Real.pi * (K + 1 : ℕ) / 2))) atTop (𝓝 0) := by
    refine hcoreK.congr fun K => ?_
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
    ring
  have hlength : Tendsto (fun K : ℕ =>
      (C * (K + 1 : ℕ) ^ N * Real.exp (-(Real.pi * (K + 1 : ℕ) / 2))) *
        |2 - ((1 / 2 : ℝ) - z.1.1.re)|) atTop (𝓝 0) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      hcoreK'.mul_const |2 - ((1 / 2 : ℝ) - z.1.1.re)|
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun K => norm_nonneg _) ?_ hlength
  exact Eventually.of_forall (fun K => hbound ε K)

/-- The actual upper side of the source-weighted canonical class-I detector
rectangle tends to zero. -/
theorem tendsto_cglPrimitiveClassISmoothedUpperHorizontalEdge
    (X n Y : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLPrimitiveClassIWindowZero n χ τ H) :
    Tendsto (fun K : ℕ =>
      ∫ u in ((1 / 2 : ℝ) - z.1.1.re)..2,
        cglSmoothedNonprincipalDetectorMellinIntegrand X n Y
          (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).toCGLNonprincipalCriticalStripLZero
          ((u : ℂ) + ((K + 1 : ℕ) : ℂ) * I)) atTop (𝓝 0) := by
  simpa [cglClassIUpperHorizontalEdgeSign] using
    tendsto_cglPrimitiveClassISmoothedHorizontalSignedEdgeIntegral X n Y χ τ H z
      cglClassIUpperHorizontalEdgeSign

/-- The actual lower side of the source-weighted canonical class-I detector
rectangle tends to zero. -/
theorem tendsto_cglPrimitiveClassISmoothedLowerHorizontalEdge
    (X n Y : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLPrimitiveClassIWindowZero n χ τ H) :
    Tendsto (fun K : ℕ =>
      ∫ u in ((1 / 2 : ℝ) - z.1.1.re)..2,
        cglSmoothedNonprincipalDetectorMellinIntegrand X n Y
          (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).toCGLNonprincipalCriticalStripLZero
          ((u : ℂ) - ((K + 1 : ℕ) : ℂ) * I)) atTop (𝓝 0) := by
  refine (tendsto_cglPrimitiveClassISmoothedHorizontalSignedEdgeIntegral X n Y χ τ H z
    cglClassILowerHorizontalEdgeSign).congr fun K => ?_
  apply intervalIntegral.integral_congr
  intro u _
  simp only [cglClassILowerHorizontalEdgeSign, Subtype.coe_mk]
  push_cast
  ring

end RHTower
