/-
# Uniform horizontal-edge decay for Chen--Gupta--Li class-I detectors

For each actual primitive nonprincipal class-I zero, this module proves that
both finite horizontal sides of its canonical CGL detector rectangle tend to
zero at the literal heights `K + 1`.  The proof combines the existing uniform
Gamma vertical-strip bound with the finite detector cutoff and the proved
primitive Dirichlet-L polynomial strip bound.

No RH, GRH, zero-density estimate, large-value estimate, or caller-supplied
analytic premise is used.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiPrimitiveClassIContours
import GaloisForLFunctions.RHTower.SelbergClass.BarnesHorizontalEdges

open Complex Filter Topology intervalIntegral

noncomputable section

namespace RHTower

/-- A certified orientation of a horizontal CGL contour edge. -/
abbrev CGLClassIHorizontalEdgeSign := {ε : ℝ // |ε| = 1}

/-- The translated detector point on either canonical horizontal class-I edge.
Its real part remains in the detector's closed right half-plane. -/
def cglPrimitiveClassIHorizontalSignedShiftPoint
    (n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLPrimitiveClassIWindowZero n χ τ H)
    (u : Set.Icc ((1 / 2 : ℝ) - z.1.1.re) 2)
    (ε : CGLClassIHorizontalEdgeSign) (K : ℕ) : CGLRightHalfPlanePoint :=
  ⟨z.1.1 + (u.1 : ℂ) + ((ε.1 * (K + 1 : ℕ) : ℝ) : ℂ) * I, by
    simp
    linarith [u.2.1]⟩

/-- The translated L-function argument on either horizontal class-I edge has
at most linear growth in the literal edge height. -/
theorem norm_cglPrimitiveClassIHorizontalSignedShiftPoint_sub_four_le
    (n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLPrimitiveClassIWindowZero n χ τ H)
    (u : Set.Icc ((1 / 2 : ℝ) - z.1.1.re) 2)
    (ε : CGLClassIHorizontalEdgeSign) (K : ℕ) :
    ‖(cglPrimitiveClassIHorizontalSignedShiftPoint n χ τ H z u ε K).1 - 4‖ ≤
      (‖z.1.1‖ + 7) * (K + 1 : ℕ) := by
  have hlt := (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).lt_one
  change z.1.1.re < 1 at hlt
  have hu : |u.1| ≤ 2 := by
    rw [abs_le]
    constructor
    · linarith [u.2.1]
    · exact u.2.2
  have hT : (1 : ℝ) ≤ (K + 1 : ℕ) := by
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le K))
  have hT0 : (0 : ℝ) ≤ (K + 1 : ℕ) := le_trans zero_le_one hT
  have hET : ‖((ε.1 * (K + 1 : ℕ) : ℝ) : ℂ) * I‖ = (K + 1 : ℕ) := by
    rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
      abs_mul, ε.2, abs_of_nonneg hT0, one_mul]
  have hbase :
      ‖(cglPrimitiveClassIHorizontalSignedShiftPoint n χ τ H z u ε K).1 - 4‖ ≤
        ‖z.1.1‖ + 2 + (K + 1 : ℕ) + 4 := by
    change ‖z.1.1 + (u.1 : ℂ) + ((ε.1 * (K + 1 : ℕ) : ℝ) : ℂ) * I - 4‖ ≤ _
    calc
      ‖z.1.1 + (u.1 : ℂ) + ((ε.1 * (K + 1 : ℕ) : ℝ) : ℂ) * I - 4‖
          ≤ ‖z.1.1 + (u.1 : ℂ) + ((ε.1 * (K + 1 : ℕ) : ℝ) : ℂ) * I‖ + ‖(4 : ℂ)‖ :=
            norm_sub_le _ _
      _ ≤ (‖z.1.1 + (u.1 : ℂ)‖ + ‖((ε.1 * (K + 1 : ℕ) : ℝ) : ℂ) * I‖) + ‖(4 : ℂ)‖ := by
            gcongr
            exact norm_add_le _ _
      _ ≤ ((‖z.1.1‖ + ‖(u.1 : ℂ)‖) + ‖((ε.1 * (K + 1 : ℕ) : ℝ) : ℂ) * I‖) + ‖(4 : ℂ)‖ := by
            gcongr
            exact norm_add_le _ _
      _ ≤ ‖z.1.1‖ + 2 + (K + 1 : ℕ) + 4 := by
            rw [hET, Complex.norm_real, Real.norm_eq_abs]
            norm_num
            gcongr
  have hnorm : 0 ≤ ‖z.1.1‖ := norm_nonneg _
  have hfactor : 0 ≤ ‖z.1.1‖ + 6 := by linarith
  have hdelta : 0 ≤ (‖z.1.1‖ + 6) * ((K + 1 : ℕ) - 1) :=
    mul_nonneg hfactor (sub_nonneg.mpr hT)
  nlinarith

/-- The established primitive Dirichlet-L strip bound applies uniformly to
both canonical class-I horizontal edges. -/
theorem exists_cglPrimitiveClassIHorizontalSignedShift_LFunction_bound
    (n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLPrimitiveClassIWindowZero n χ τ H) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Set.Icc ((1 / 2 : ℝ) - z.1.1.re) 2)
      (ε : CGLClassIHorizontalEdgeSign) (K : ℕ),
      ‖DirichletCharacter.LFunction χ.1.1
        (cglPrimitiveClassIHorizontalSignedShiftPoint n χ τ H z u ε K).1‖ ≤
        C * ‖(cglPrimitiveClassIHorizontalSignedShiftPoint n χ τ H z u ε K).1 - 4‖ ^ 3 := by
  obtain ⟨C, hC, hbound⟩ := bound_LFunction_strip χ.1.2 χ.2
  refine ⟨C, hC, fun u ε K => hbound _ ?_ ?_⟩
  · have hlow : -2 ≤ z.1.1.re + u.1 := by linarith [u.2.1]
    simpa [cglPrimitiveClassIHorizontalSignedShiftPoint] using hlow
  · have hhigh : z.1.1.re + u.1 ≤ 3 := by
      have hlt := (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).lt_one
      change z.1.1.re < 1 at hlt
      linarith [u.2.2, hlt]
    simpa [cglPrimitiveClassIHorizontalSignedShiftPoint] using hhigh

/-- Uniform polynomial-exponential control of the class-I detector integrand
on either horizontal edge of its canonical finite rectangle. -/
theorem exists_norm_cglPrimitiveClassIHorizontalSignedDetectorMellinIntegrand_le
    (X n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLPrimitiveClassIWindowZero n χ τ H) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀
      (u : Set.Icc ((1 / 2 : ℝ) - z.1.1.re) 2)
      (ε : CGLClassIHorizontalEdgeSign) (K : ℕ),
      ‖cglDetectorMellinIntegrand X n
        (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).toCGLNonprincipalCriticalStripLZero.toCGLCriticalStripLZero
        ((u.1 : ℂ) + ((ε.1 * (K + 1 : ℕ) : ℝ) : ℂ) * I)‖ ≤
        C * (K + 1 : ℕ) ^ N * Real.exp (-(Real.pi * (K + 1 : ℕ) / 2)) := by
  obtain ⟨CΓ, NΓ, hCΓ, hΓ⟩ :=
    exists_bound_norm_Gamma_vertical_strip_arbitrary (a := -(1 / 2 : ℝ)) (b := 2)
  obtain ⟨CL, hCL, hL⟩ :=
    exists_cglPrimitiveClassIHorizontalSignedShift_LFunction_bound n χ τ H z
  refine ⟨CΓ * (X + 1 : ℕ) * CL * (‖z.1.1‖ + 7) ^ 3, NΓ + 3, by positivity, ?_⟩
  intro u ε K
  have hlt := (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).lt_one
  change z.1.1.re < 1 at hlt
  have hT : (1 : ℝ) ≤ (K + 1 : ℕ) := by
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le K))
  have hT0 : (0 : ℝ) ≤ (K + 1 : ℕ) := le_trans zero_le_one hT
  have hUlow : -(1 / 2 : ℝ) ≤ u.1 := by linarith [u.2.1]
  have hETabs : |ε.1 * (K + 1 : ℕ)| = (K + 1 : ℕ) := by
    rw [abs_mul, ε.2, abs_of_nonneg hT0, one_mul]
  have hGamma := hΓ u.1 (ε.1 * (K + 1 : ℕ)) hUlow u.2.2 (by
    rw [hETabs]
    exact hT)
  have hGamma' :
      ‖Complex.Gamma ((u.1 : ℂ) + ((ε.1 * (K + 1 : ℕ) : ℝ) : ℂ) * I)‖ ≤
        CΓ * (K + 1 : ℕ) ^ NΓ * Real.exp (-(Real.pi * (K + 1 : ℕ) / 2)) := by
    rw [hETabs] at hGamma
    simpa only [Nat.cast_add, Nat.cast_one] using hGamma
  have hshift := norm_cglPrimitiveClassIHorizontalSignedShiftPoint_sub_four_le n χ τ H z u ε K
  have hpower :
      ‖(cglPrimitiveClassIHorizontalSignedShiftPoint n χ τ H z u ε K).1 - 4‖ ^ 3 ≤
        ((‖z.1.1‖ + 7) * (K + 1 : ℕ)) ^ 3 := by
    exact pow_le_pow_left₀ (norm_nonneg _) hshift 3
  have hL' :
      ‖DirichletCharacter.LFunction χ.1.1
        (cglPrimitiveClassIHorizontalSignedShiftPoint n χ τ H z u ε K).1‖ ≤
        CL * ((‖z.1.1‖ + 7) * (K + 1 : ℕ)) ^ 3 := by
    exact (hL u ε K).trans (mul_le_mul_of_nonneg_left hpower hCL.le)
  have hM :
      ‖zeroDetectionMobiusPolynomial X (n + 1) χ.1.1
        (cglPrimitiveClassIHorizontalSignedShiftPoint n χ τ H z u ε K).1‖ ≤ (X + 1 : ℕ) :=
    norm_zeroDetectionMobiusPolynomial_le_cutoff X (n + 1) χ.1.1
      (cglPrimitiveClassIHorizontalSignedShiftPoint n χ τ H z u ε K)
  have hML :
      ‖zeroDetectionMobiusPolynomial X (n + 1) χ.1.1
          (cglPrimitiveClassIHorizontalSignedShiftPoint n χ τ H z u ε K).1‖ *
        ‖DirichletCharacter.LFunction χ.1.1
          (cglPrimitiveClassIHorizontalSignedShiftPoint n χ τ H z u ε K).1‖ ≤
        (X + 1 : ℕ) * (CL * ((‖z.1.1‖ + 7) * (K + 1 : ℕ)) ^ 3) := by
    exact mul_le_mul hM hL' (norm_nonneg _) (by positivity)
  have hchar :
      (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).character = χ.1.1 := rfl
  have hpoint :
      (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).point = z.1.1 := rfl
  unfold cglDetectorMellinIntegrand
  rw [hchar, hpoint]
  have hshiftpoint :
      z.1.1 + ((u.1 : ℂ) + ((ε.1 * (K + 1 : ℕ) : ℝ) : ℂ) * I) =
        (cglPrimitiveClassIHorizontalSignedShiftPoint n χ τ H z u ε K).1 := by
    simp only [cglPrimitiveClassIHorizontalSignedShiftPoint, Subtype.coe_mk]
    ring
  rw [hshiftpoint]
  change ‖Complex.Gamma ((u.1 : ℂ) + ((ε.1 * (K + 1 : ℕ) : ℝ) : ℂ) * I) *
      (zeroDetectionMobiusPolynomial X (n + 1) χ.1.1
        (cglPrimitiveClassIHorizontalSignedShiftPoint n χ τ H z u ε K).1 *
        DirichletCharacter.LFunction χ.1.1
          (cglPrimitiveClassIHorizontalSignedShiftPoint n χ τ H z u ε K).1)‖ ≤ _
  rw [norm_mul, norm_mul]
  calc
    ‖Complex.Gamma ((u.1 : ℂ) + ((ε.1 * (K + 1 : ℕ) : ℝ) : ℂ) * I)‖ *
        (‖zeroDetectionMobiusPolynomial X (n + 1) χ.1.1
          (cglPrimitiveClassIHorizontalSignedShiftPoint n χ τ H z u ε K).1‖ *
        ‖DirichletCharacter.LFunction χ.1.1
          (cglPrimitiveClassIHorizontalSignedShiftPoint n χ τ H z u ε K).1‖)
      ≤ (CΓ * (K + 1 : ℕ) ^ NΓ * Real.exp (-(Real.pi * (K + 1 : ℕ) / 2))) *
          ((X + 1 : ℕ) * (CL * ((‖z.1.1‖ + 7) * (K + 1 : ℕ)) ^ 3)) :=
        mul_le_mul hGamma' hML (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
    _ = (CΓ * (X + 1 : ℕ) * CL * (‖z.1.1‖ + 7) ^ 3) *
          (K + 1 : ℕ) ^ (NΓ + 3) * Real.exp (-(Real.pi * (K + 1 : ℕ) / 2)) := by
        rw [mul_pow]
        have hpow : ((K + 1 : ℕ) : ℝ) ^ NΓ * ((K + 1 : ℕ) : ℝ) ^ 3 =
            ((K + 1 : ℕ) : ℝ) ^ (NΓ + 3) := by
          rw [← pow_add]
        calc
          CΓ * (K + 1 : ℕ) ^ NΓ * Real.exp (-(Real.pi * (K + 1 : ℕ) / 2)) *
              ((X + 1 : ℕ) * (CL * ((‖z.1.1‖ + 7) ^ 3 * (K + 1 : ℕ) ^ 3))) =
              (CΓ * (X + 1 : ℕ) * CL * (‖z.1.1‖ + 7) ^ 3) *
                ((K + 1 : ℕ) ^ NΓ * (K + 1 : ℕ) ^ 3) *
                  Real.exp (-(Real.pi * (K + 1 : ℕ) / 2)) := by ring
          _ = (CΓ * (X + 1 : ℕ) * CL * (‖z.1.1‖ + 7) ^ 3) *
                (K + 1 : ℕ) ^ (NΓ + 3) *
                  Real.exp (-(Real.pi * (K + 1 : ℕ) / 2)) := by rw [hpow]

/-- The corresponding finite horizontal class-I edge integrals obey the
same closed polynomial-exponential envelope. -/
theorem exists_norm_cglPrimitiveClassIHorizontalSignedEdgeIntegral_le
    (X n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLPrimitiveClassIWindowZero n χ τ H) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ (ε : CGLClassIHorizontalEdgeSign) (K : ℕ),
      ‖∫ u in ((1 / 2 : ℝ) - z.1.1.re)..2,
        cglDetectorMellinIntegrand X n
          (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).toCGLNonprincipalCriticalStripLZero.toCGLCriticalStripLZero
          ((u : ℂ) + ((ε.1 * (K + 1 : ℕ) : ℝ) : ℂ) * I)‖ ≤
        (C * (K + 1 : ℕ) ^ N * Real.exp (-(Real.pi * (K + 1 : ℕ) / 2))) *
          |2 - ((1 / 2 : ℝ) - z.1.1.re)| := by
  obtain ⟨C, N, hC, hbound⟩ :=
    exists_norm_cglPrimitiveClassIHorizontalSignedDetectorMellinIntegrand_le X n χ τ H z
  refine ⟨C, N, hC, ?_⟩
  intro ε K
  have hleft : (1 / 2 : ℝ) - z.1.1.re ≤ 2 := by linarith [z.2]
  exact intervalIntegral.norm_integral_le_of_norm_le_const (fun u hu => by
    rw [Set.uIoc_of_le hleft] at hu
    simpa using hbound ⟨u, hu.1.le, hu.2⟩ ε K)


/-- The horizontal detector integral at either certified class-I orientation
tends to zero along the literal canonical rectangle heights. -/
theorem tendsto_cglPrimitiveClassIHorizontalSignedEdgeIntegral
    (X n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLPrimitiveClassIWindowZero n χ τ H) (ε : CGLClassIHorizontalEdgeSign) :
    Tendsto (fun K : ℕ =>
      ∫ u in ((1 / 2 : ℝ) - z.1.1.re)..2,
        cglDetectorMellinIntegrand X n
          (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).toCGLNonprincipalCriticalStripLZero.toCGLCriticalStripLZero
          ((u : ℂ) + ((ε.1 * (K + 1 : ℕ) : ℝ) : ℂ) * I)) atTop (𝓝 0) := by
  obtain ⟨C, N, _, hbound⟩ :=
    exists_norm_cglPrimitiveClassIHorizontalSignedEdgeIntegral_le X n χ τ H z
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

/-- Certified upper orientation for a CGL class-I horizontal edge. -/
def cglClassIUpperHorizontalEdgeSign : CGLClassIHorizontalEdgeSign := ⟨1, by norm_num⟩

/-- Certified lower orientation for a CGL class-I horizontal edge. -/
def cglClassILowerHorizontalEdgeSign : CGLClassIHorizontalEdgeSign := ⟨-1, by norm_num⟩

/-- The actual upper horizontal side of every canonical primitive class-I
detector rectangle tends to zero. -/
theorem tendsto_cglPrimitiveClassIUpperHorizontalEdge
    (X n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLPrimitiveClassIWindowZero n χ τ H) :
    Tendsto (fun K : ℕ =>
      ∫ u in ((1 / 2 : ℝ) - z.1.1.re)..2,
        cglDetectorMellinIntegrand X n
          (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).toCGLNonprincipalCriticalStripLZero.toCGLCriticalStripLZero
          ((u : ℂ) + ((K + 1 : ℕ) : ℂ) * I)) atTop (𝓝 0) := by
  simpa [cglClassIUpperHorizontalEdgeSign] using
    tendsto_cglPrimitiveClassIHorizontalSignedEdgeIntegral X n χ τ H z
      cglClassIUpperHorizontalEdgeSign

/-- The actual lower horizontal side of every canonical primitive class-I
detector rectangle tends to zero. -/
theorem tendsto_cglPrimitiveClassILowerHorizontalEdge
    (X n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLPrimitiveClassIWindowZero n χ τ H) :
    Tendsto (fun K : ℕ =>
      ∫ u in ((1 / 2 : ℝ) - z.1.1.re)..2,
        cglDetectorMellinIntegrand X n
          (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).toCGLNonprincipalCriticalStripLZero.toCGLCriticalStripLZero
          ((u : ℂ) - ((K + 1 : ℕ) : ℂ) * I)) atTop (𝓝 0) := by
  refine (tendsto_cglPrimitiveClassIHorizontalSignedEdgeIntegral X n χ τ H z
    cglClassILowerHorizontalEdgeSign).congr fun K => ?_
  apply intervalIntegral.integral_congr
  intro u _
  simp only [cglClassILowerHorizontalEdgeSign, Subtype.coe_mk]
  push_cast
  ring

end RHTower
