import GaloisForLFunctions.HTGeometry.ReturnExcisedOptimalDesignCoareaLaw
import GaloisForLFunctions.HTGeometry.ComplexIntegralGram
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.ConjSqrt
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

open Filter MeasureTheory Matrix Set
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem finiteMatrixHilbertSchmidt_trace_cauchy
    {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ) :
    ‖(Xᴴ * Y).trace‖ ^ 2 ≤
      ((Xᴴ * X).trace).re * ((Yᴴ * Y).trace).re := by
  classical
  let x : Fin n × Fin n → ℂ := fun p => X p.1 p.2
  let y : Fin n × Fin n → ℂ := fun p => Y p.1 p.2
  have hxy : finiteComplexInner x y = (Xᴴ * Y).trace := by
    rw [finiteComplexInner, Fintype.sum_prod_type]
    simp only [x, y, Matrix.trace, Matrix.diag_apply,
      Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [Finset.sum_comm]
    simp only [starRingEnd_apply]
  have hxx :
      ‖WithLp.toLp 2 x‖ ^ 2 = ((Xᴴ * X).trace).re := by
    rw [@norm_sq_eq_re_inner ℂ, inner_toLp_eq_finiteComplexInner]
    have h : finiteComplexInner x x = (Xᴴ * X).trace := by
      rw [finiteComplexInner, Fintype.sum_prod_type]
      simp only [x, Matrix.trace, Matrix.diag_apply,
        Matrix.mul_apply, Matrix.conjTranspose_apply]
      rw [Finset.sum_comm]
      simp only [starRingEnd_apply]
    simpa using congrArg Complex.re h
  have hyy :
      ‖WithLp.toLp 2 y‖ ^ 2 = ((Yᴴ * Y).trace).re := by
    rw [@norm_sq_eq_re_inner ℂ, inner_toLp_eq_finiteComplexInner]
    have : finiteComplexInner y y = (Yᴴ * Y).trace := by
      rw [finiteComplexInner, Fintype.sum_prod_type]
      simp only [y, Matrix.trace, Matrix.diag_apply,
        Matrix.mul_apply, Matrix.conjTranspose_apply]
      rw [Finset.sum_comm]
      simp only [starRingEnd_apply]
    simpa using congrArg Complex.re this
  have hcs := norm_inner_le_norm (𝕜 := ℂ)
    (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  rw [inner_toLp_eq_finiteComplexInner, hxy] at hcs
  have hsq := pow_le_pow_left₀ (norm_nonneg ((Xᴴ * Y).trace)) hcs 2
  rwa [mul_pow, hxx, hyy] at hsq

/-- Canonical finite-dimensional Bures root fidelity. -/
def finiteBuresRootFidelity {n : ℕ}
    (C M : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  (CFC.sqrt (CFC.conjSqrt C M)).trace.re

theorem finiteBuresRootFidelity_sq_le_reporter_product_of_posDef
    {n : ℕ} {C M A : Matrix (Fin n) (Fin n) ℂ}
    (hC : C.PosDef) (hM : M.PosDef) (hA : A.PosDef) :
    finiteBuresRootFidelity C M ^ 2 ≤
      ((C * A).trace).re * ((M * A⁻¹).trace).re := by
  classical
  let P : Matrix (Fin n) (Fin n) ℂ := CFC.sqrt C
  let Q : Matrix (Fin n) (Fin n) ℂ := CFC.sqrt M
  let T : Matrix (Fin n) (Fin n) ℂ := CFC.sqrt A
  let W : Matrix (Fin n) (Fin n) ℂ := CFC.conjSqrt C M
  let S : Matrix (Fin n) (Fin n) ℂ := CFC.sqrt W
  let Z : Matrix (Fin n) (Fin n) ℂ := P * Q
  have hC0 : 0 ≤ C := Matrix.nonneg_iff_posSemidef.mpr hC.posSemidef
  have hM0 : 0 ≤ M := Matrix.nonneg_iff_posSemidef.mpr hM.posSemidef
  have hA0 : 0 ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA.posSemidef
  have hPH : Pᴴ = P := by
    simpa [P, Matrix.star_eq_conjTranspose] using (CFC.sqrt_nonneg C).star_eq
  have hQH : Qᴴ = Q := by
    simpa [Q, Matrix.star_eq_conjTranspose] using (CFC.sqrt_nonneg M).star_eq
  have hTH : Tᴴ = T := by
    simpa [T, Matrix.star_eq_conjTranspose] using (CFC.sqrt_nonneg A).star_eq
  have hP2 : P * P = C := by
    simpa [P, pow_two] using CFC.sq_sqrt C hC0
  have hQ2 : Q * Q = M := by
    simpa [Q, pow_two] using CFC.sq_sqrt M hM0
  have hT2 : T * T = A := by
    simpa [T, pow_two] using CFC.sq_sqrt A hA0
  have hPunit : IsUnit P := (CFC.isUnit_sqrt_iff C hC0).2 hC.isUnit
  have hQunit : IsUnit Q := (CFC.isUnit_sqrt_iff M hM0).2 hM.isUnit
  have hTunit : IsUnit T := (CFC.isUnit_sqrt_iff A hA0).2 hA.isUnit
  have hWpos : W.PosDef := by
    rw [← Matrix.isStrictlyPositive_iff_posDef]
    exact (CFC.isStrictlyPositive_conjSqrt_iff C M hC.isStrictlyPositive).2
      hM.isStrictlyPositive
  have hW0 : 0 ≤ W := Matrix.nonneg_iff_posSemidef.mpr hWpos.posSemidef
  have hSH : Sᴴ = S := by
    simpa [S, Matrix.star_eq_conjTranspose] using (CFC.sqrt_nonneg W).star_eq
  have hS2 : S * S = W := by
    simpa [S, pow_two] using CFC.sq_sqrt W hW0
  have hSunit : IsUnit S := (CFC.isUnit_sqrt_iff W hW0).2 hWpos.isUnit
  have hZZH : Z * Zᴴ = W := by
    simp only [Z, Matrix.conjTranspose_mul, hPH, hQH]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q Q P, hQ2]
    simp [W, P, CFC.conjSqrt_apply, Matrix.mul_assoc]
  have hZunit : IsUnit Z := hPunit.mul hQunit
  have hZdet : IsUnit Z.det := Z.isUnit_iff_isUnit_det.mp hZunit
  have hZHdet : IsUnit Zᴴ.det :=
    Zᴴ.isUnit_iff_isUnit_det.mp hZunit.star
  let U : Matrix (Fin n) (Fin n) ℂ := Z⁻¹ * S
  have hUUH : U * Uᴴ = 1 := by
    calc
      U * Uᴴ = Z⁻¹ * (S * S) * Zᴴ⁻¹ := by
        simp only [U, Matrix.conjTranspose_mul,
          Matrix.conjTranspose_nonsing_inv, hSH]
        noncomm_ring
      _ = Z⁻¹ * (Z * Zᴴ) * Zᴴ⁻¹ := by rw [hS2, hZZH]
      _ = 1 := by
        rw [← Matrix.mul_assoc Z⁻¹ Z Zᴴ,
          Matrix.nonsing_inv_mul Z hZdet, Matrix.one_mul,
          Matrix.mul_nonsing_inv Zᴴ hZHdet]
  have hZU : Z * U = S := by
    simp only [U, ← Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv Z hZdet, Matrix.one_mul]
  have hTdet : IsUnit T.det := T.isUnit_iff_isUnit_det.mp hTunit
  have hTinvH : T⁻¹ᴴ = T⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hTH]
  have hAinv : A⁻¹ = T⁻¹ * T⁻¹ := by
    letI : Invertible A := hA.isUnit.nonempty_invertible.some
    letI : Invertible T := hTunit.nonempty_invertible.some
    apply Matrix.mul_left_injective_of_invertible (A := A)
    change A⁻¹ * A = (T⁻¹ * T⁻¹) * A
    rw [Matrix.inv_mul_of_invertible, ← hT2]
    simp [Matrix.mul_assoc, Matrix.inv_mul_of_invertible]
  let X : Matrix (Fin n) (Fin n) ℂ := T * P
  let Y : Matrix (Fin n) (Fin n) ℂ := T⁻¹ * Q * U
  have hXHY : Xᴴ * Y = S := by
    simp only [X, Y, Matrix.conjTranspose_mul, hPH, hTH]
    rw [show P * T * (T⁻¹ * Q * U) =
      P * (T * T⁻¹) * Q * U by noncomm_ring]
    rw [Matrix.mul_nonsing_inv T hTdet, Matrix.mul_one]
    change Z * U = S
    exact hZU
  have hXX : ((Xᴴ * X).trace).re = ((C * A).trace).re := by
    apply congrArg Complex.re
    simp only [X, Matrix.conjTranspose_mul, hPH, hTH]
    rw [show P * T * (T * P) = P * (T * T) * P by noncomm_ring]
    rw [hT2, Matrix.trace_mul_cycle, hP2, Matrix.trace_mul_comm]
  have hYY : ((Yᴴ * Y).trace).re = ((M * A⁻¹).trace).re := by
    apply congrArg Complex.re
    simp only [Y, Matrix.conjTranspose_mul, hQH, hTinvH]
    rw [Matrix.trace_mul_cycle]
    rw [show T⁻¹ * Q * U * Uᴴ * (Q * T⁻¹) =
      (T⁻¹ * Q) * (U * Uᴴ) * (Q * T⁻¹) by noncomm_ring]
    rw [hUUH, Matrix.mul_one]
    rw [show T⁻¹ * Q * (Q * T⁻¹) =
      T⁻¹ * (Q * Q) * T⁻¹ by noncomm_ring]
    rw [Matrix.trace_mul_cycle, hQ2, ← hAinv,
      Matrix.trace_mul_comm]
  have htraceS : 0 ≤ S.trace := by
    simpa [S] using (CFC.sqrt_nonneg W).trace_nonneg
  have htraceSre : 0 ≤ S.trace.re := (Complex.nonneg_iff.mp htraceS).1
  have htraceSim : S.trace.im = 0 := (Complex.nonneg_iff.mp htraceS).2.symm
  have hnormTraceS : ‖S.trace‖ = S.trace.re := by
    rw [Complex.norm_def, Complex.normSq_apply, htraceSim]
    rw [zero_mul, add_zero, ← pow_two, Real.sqrt_sq htraceSre]
  have hcs := finiteMatrixHilbertSchmidt_trace_cauchy X Y
  rw [hXHY, hXX, hYY, hnormTraceS] at hcs
  simpa [finiteBuresRootFidelity, S, W] using hcs

/-- Geometric-mean reporter attaining the Bures variational bound for
positive-definite pairs. -/
def finiteBuresOptimalReporter {n : ℕ}
    (C M : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  CFC.conjSqrt C⁻¹ (CFC.sqrt (CFC.conjSqrt C M))

theorem finiteBuresOptimalReporter_posDef
    {n : ℕ} {C M : Matrix (Fin n) (Fin n) ℂ}
    (hC : C.PosDef) (hM : M.PosDef) :
    (finiteBuresOptimalReporter C M).PosDef := by
  rw [← Matrix.isStrictlyPositive_iff_posDef]
  apply (CFC.isStrictlyPositive_conjSqrt_iff C⁻¹
    (CFC.sqrt (CFC.conjSqrt C M)) hC.inv.isStrictlyPositive).2
  apply IsStrictlyPositive.sqrt
  exact (CFC.isStrictlyPositive_conjSqrt_iff C M
    hC.isStrictlyPositive).2 hM.isStrictlyPositive

theorem trace_mul_finiteBuresOptimalReporter_eq_root
    {n : ℕ} {C M : Matrix (Fin n) (Fin n) ℂ}
    (hC : C.PosDef) :
    (C * finiteBuresOptimalReporter C M).trace =
      (CFC.sqrt (CFC.conjSqrt C M)).trace := by
  classical
  let P : Matrix (Fin n) (Fin n) ℂ := CFC.sqrt C
  let S : Matrix (Fin n) (Fin n) ℂ :=
    CFC.sqrt (CFC.conjSqrt C M)
  have hC0 : 0 ≤ C := Matrix.nonneg_iff_posSemidef.mpr hC.posSemidef
  have hP2 : P * P = C := by
    simpa [P, pow_two] using CFC.sq_sqrt C hC0
  have hPunit : IsUnit P := (CFC.isUnit_sqrt_iff C hC0).2 hC.isUnit
  have hPdet : IsUnit P.det := P.isUnit_iff_isUnit_det.mp hPunit
  have hsqrtInv : CFC.sqrt C⁻¹ = P⁻¹ := by
    rw [Matrix.nonsing_inv_eq_ringInverse, CFC.sqrt_ringInverse,
      ← Matrix.nonsing_inv_eq_ringInverse]
  change (C * (CFC.sqrt C⁻¹ * S * CFC.sqrt C⁻¹)).trace = S.trace
  rw [hsqrtInv, ← hP2]
  rw [show (P * P) * (P⁻¹ * S * P⁻¹) =
    P * (P * P⁻¹) * S * P⁻¹ by noncomm_ring]
  rw [Matrix.mul_nonsing_inv P hPdet, Matrix.mul_one]
  rw [Matrix.trace_mul_cycle]
  rw [Matrix.nonsing_inv_mul P hPdet, Matrix.one_mul]

theorem finiteBuresOptimalReporter_inv
    {n : ℕ} {C M : Matrix (Fin n) (Fin n) ℂ}
    (hC : C.PosDef) :
    (finiteBuresOptimalReporter C M)⁻¹ =
      CFC.sqrt C * (CFC.sqrt (CFC.conjSqrt C M))⁻¹ * CFC.sqrt C := by
  let S : Matrix (Fin n) (Fin n) ℂ :=
    CFC.sqrt (CFC.conjSqrt C M)
  change (CFC.conjSqrt C⁻¹ S)⁻¹ = CFC.sqrt C * S⁻¹ * CFC.sqrt C
  rw [Matrix.nonsing_inv_eq_ringInverse]
  rw [CFC.ringInverse_conjSqrt C⁻¹ S hC.inv.isStrictlyPositive]
  rw [← Matrix.nonsing_inv_eq_ringInverse]
  rw [← Matrix.nonsing_inv_eq_ringInverse]
  letI : Invertible C := hC.isUnit.nonempty_invertible.some
  rw [Matrix.inv_inv_of_invertible]
  rfl

theorem trace_mul_finiteBuresOptimalReporter_inv_eq_root
    {n : ℕ} {C M : Matrix (Fin n) (Fin n) ℂ}
    (hC : C.PosDef) (hM : M.PosDef) :
    (M * (finiteBuresOptimalReporter C M)⁻¹).trace =
      (CFC.sqrt (CFC.conjSqrt C M)).trace := by
  classical
  let P : Matrix (Fin n) (Fin n) ℂ := CFC.sqrt C
  let W : Matrix (Fin n) (Fin n) ℂ := CFC.conjSqrt C M
  let S : Matrix (Fin n) (Fin n) ℂ := CFC.sqrt W
  have hWpos : W.PosDef := by
    rw [← Matrix.isStrictlyPositive_iff_posDef]
    exact (CFC.isStrictlyPositive_conjSqrt_iff C M
      hC.isStrictlyPositive).2 hM.isStrictlyPositive
  have hW0 : 0 ≤ W := Matrix.nonneg_iff_posSemidef.mpr hWpos.posSemidef
  have hS2 : S * S = W := by
    simpa [S, pow_two] using CFC.sq_sqrt W hW0
  have hSunit : IsUnit S := (CFC.isUnit_sqrt_iff W hW0).2 hWpos.isUnit
  have hSdet : IsUnit S.det := S.isUnit_iff_isUnit_det.mp hSunit
  have hW : P * M * P = W := by
    simp [P, W, CFC.conjSqrt_apply]
  rw [finiteBuresOptimalReporter_inv hC]
  change (M * (P * S⁻¹ * P)).trace = S.trace
  rw [show M * (P * S⁻¹ * P) =
    (M * P) * (S⁻¹ * P) by noncomm_ring]
  rw [Matrix.trace_mul_comm]
  rw [show S⁻¹ * P * (M * P) =
    S⁻¹ * (P * M * P) by noncomm_ring]
  rw [hW, ← hS2]
  rw [show S⁻¹ * (S * S) = (S⁻¹ * S) * S by noncomm_ring]
  rw [Matrix.nonsing_inv_mul S hSdet, Matrix.one_mul]

theorem finiteBuresOptimalReporter_product_eq_rootFidelity_sq
    {n : ℕ} {C M : Matrix (Fin n) (Fin n) ℂ}
    (hC : C.PosDef) (hM : M.PosDef) :
    ((C * finiteBuresOptimalReporter C M).trace).re *
        ((M * (finiteBuresOptimalReporter C M)⁻¹).trace).re =
      finiteBuresRootFidelity C M ^ 2 := by
  rw [congrArg Complex.re
      (trace_mul_finiteBuresOptimalReporter_eq_root hC),
    congrArg Complex.re
      (trace_mul_finiteBuresOptimalReporter_inv_eq_root hC hM)]
  simp [finiteBuresRootFidelity, pow_two]

/-- Infimum of positive-reporter products for a fixed positive matrix pair. -/
def finiteBuresReporterCapacity {n : ℕ}
    (C M : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  sInf {q : ℝ | ∃ A : Matrix (Fin n) (Fin n) ℂ,
    A.PosDef ∧ q = ((C * A).trace).re * ((M * A⁻¹).trace).re}

/-- **Positive-definite Alberti product identity.**  The infimum over every
positive reporter equals canonical Bures root fidelity squared, and the
geometric-mean reporter attains it. -/
theorem finiteBuresReporterCapacity_eq_rootFidelity_sq_of_posDef
    {n : ℕ} {C M : Matrix (Fin n) (Fin n) ℂ}
    (hC : C.PosDef) (hM : M.PosDef) :
    finiteBuresReporterCapacity C M = finiteBuresRootFidelity C M ^ 2 := by
  let values : Set ℝ := {q : ℝ | ∃ A : Matrix (Fin n) (Fin n) ℂ,
    A.PosDef ∧ q = ((C * A).trace).re * ((M * A⁻¹).trace).re}
  have hnonempty : values.Nonempty := by
    refine ⟨((C * finiteBuresOptimalReporter C M).trace).re *
      ((M * (finiteBuresOptimalReporter C M)⁻¹).trace).re, ?_⟩
    exact ⟨finiteBuresOptimalReporter C M,
      finiteBuresOptimalReporter_posDef hC hM, rfl⟩
  have hlower : ∀ q ∈ values, finiteBuresRootFidelity C M ^ 2 ≤ q := by
    intro q hq
    obtain ⟨A, hA, rfl⟩ := hq
    exact finiteBuresRootFidelity_sq_le_reporter_product_of_posDef
      hC hM hA
  have hbdd : BddBelow values := ⟨finiteBuresRootFidelity C M ^ 2, hlower⟩
  unfold finiteBuresReporterCapacity
  change sInf values = finiteBuresRootFidelity C M ^ 2
  apply le_antisymm
  · apply csInf_le hbdd
    refine ⟨finiteBuresOptimalReporter C M,
      finiteBuresOptimalReporter_posDef hC hM, ?_⟩
    exact (finiteBuresOptimalReporter_product_eq_rootFidelity_sq hC hM).symm
  · exact le_csInf hnonempty hlower

/-- Strictly positive identity regularization of a finite positive matrix. -/
def finitePositiveMatrixRegularization {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℂ) (ε : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  B + ε • 1

theorem finitePositiveMatrixRegularization_posDef
    {n : ℕ} {B : Matrix (Fin n) (Fin n) ℂ}
    (hB : B.PosSemidef) {ε : ℝ} (hε : 0 < ε) :
    (finitePositiveMatrixRegularization B ε).PosDef := by
  exact Matrix.PosDef.posSemidef_add hB (Matrix.PosDef.one.smul hε)

theorem tendsto_finitePositiveMatrixRegularization
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) :
    Tendsto (finitePositiveMatrixRegularization B)
      (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 B) := by
  have hcont : ContinuousAt (finitePositiveMatrixRegularization B) 0 := by
    unfold finitePositiveMatrixRegularization
    fun_prop
  simpa [finitePositiveMatrixRegularization] using
    hcont.tendsto.mono_left nhdsWithin_le_nhds

theorem tendsto_sqrt_finitePositiveMatrixRegularization
    {n : ℕ} [Nonempty (Fin n)] {B : Matrix (Fin n) (Fin n) ℂ}
    (hB : B.PosSemidef) :
    Tendsto (fun ε ↦ CFC.sqrt (finitePositiveMatrixRegularization B ε))
      (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (CFC.sqrt B)) := by
  letI : CStarAlgebra (Matrix (Fin n) (Fin n) ℂ) := {}
  have hB0 : 0 ≤ B := Matrix.nonneg_iff_posSemidef.mpr hB
  let positiveCone : Set (Matrix (Fin n) (Fin n) ℂ) := {D | 0 ≤ D}
  have hsqrt : ContinuousWithinAt
      (CFC.sqrt : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
      positiveCone B := by
    exact CFC.continuousOn_sqrt B hB0
  have hmaps : ∀ᶠ ε in 𝓝[Set.Ioi (0 : ℝ)] 0,
      finitePositiveMatrixRegularization B ε ∈ positiveCone := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact Matrix.nonneg_iff_posSemidef.mpr
      (finitePositiveMatrixRegularization_posDef hB hε).posSemidef
  have hreg : Tendsto (finitePositiveMatrixRegularization B)
      (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝[positiveCone] B) :=
    tendsto_nhdsWithin_iff.2
      ⟨tendsto_finitePositiveMatrixRegularization B, hmaps⟩
  exact hsqrt.tendsto.comp hreg

theorem tendsto_finiteBuresRootFidelity_regularization
    {n : ℕ} [Nonempty (Fin n)]
    {C M : Matrix (Fin n) (Fin n) ℂ}
    (hC : C.PosSemidef) (hM : M.PosSemidef) :
    Tendsto (fun ε ↦ finiteBuresRootFidelity
        (finitePositiveMatrixRegularization C ε)
        (finitePositiveMatrixRegularization M ε))
      (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (finiteBuresRootFidelity C M)) := by
  letI : CStarAlgebra (Matrix (Fin n) (Fin n) ℂ) := {}
  let L : Filter ℝ := 𝓝[Set.Ioi (0 : ℝ)] 0
  let Creg : ℝ → Matrix (Fin n) (Fin n) ℂ :=
    finitePositiveMatrixRegularization C
  let Mreg : ℝ → Matrix (Fin n) (Fin n) ℂ :=
    finitePositiveMatrixRegularization M
  let W : Matrix (Fin n) (Fin n) ℂ := CFC.conjSqrt C M
  let Wreg : ℝ → Matrix (Fin n) (Fin n) ℂ :=
    fun ε ↦ CFC.conjSqrt (Creg ε) (Mreg ε)
  have hCreg : Tendsto (fun ε ↦ CFC.sqrt (Creg ε)) L
      (𝓝 (CFC.sqrt C)) := by
    exact tendsto_sqrt_finitePositiveMatrixRegularization hC
  have hMreg : Tendsto Mreg L (𝓝 M) := by
    exact tendsto_finitePositiveMatrixRegularization M
  have hWreg : Tendsto Wreg L (𝓝 W) := by
    have hmul := hCreg.mul (hMreg.mul hCreg)
    simpa [Wreg, W, Creg, Mreg, CFC.conjSqrt_apply,
      Matrix.mul_assoc] using hmul
  have hW0 : 0 ≤ W := by
    have hC0 : 0 ≤ C := Matrix.nonneg_iff_posSemidef.mpr hC
    have hM0 : 0 ≤ M := Matrix.nonneg_iff_posSemidef.mpr hM
    dsimp [W]
    simpa using (CFC.conjSqrt_le_conjSqrt (c := C) hM0)
  let positiveCone : Set (Matrix (Fin n) (Fin n) ℂ) := {D | 0 ≤ D}
  have hWmaps : ∀ᶠ ε in L, Wreg ε ∈ positiveCone := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hCε := finitePositiveMatrixRegularization_posDef hC hε
    have hMε := finitePositiveMatrixRegularization_posDef hM hε
    have hWε : (Wreg ε).PosDef := by
      rw [← Matrix.isStrictlyPositive_iff_posDef]
      exact (CFC.isStrictlyPositive_conjSqrt_iff (Creg ε) (Mreg ε)
        hCε.isStrictlyPositive).2 hMε.isStrictlyPositive
    exact Matrix.nonneg_iff_posSemidef.mpr hWε.posSemidef
  have hWregWithin : Tendsto Wreg L (𝓝[positiveCone] W) :=
    tendsto_nhdsWithin_iff.2 ⟨hWreg, hWmaps⟩
  have hsqrtW : Tendsto (fun ε ↦ CFC.sqrt (Wreg ε)) L
      (𝓝 (CFC.sqrt W)) := by
    exact (CFC.continuousOn_sqrt W hW0).tendsto.comp hWregWithin
  have htraceRe : Continuous
      (fun D : Matrix (Fin n) (Fin n) ℂ ↦ D.trace.re) := by
    unfold Matrix.trace
    fun_prop
  have hfinal := htraceRe.continuousAt.tendsto.comp hsqrtW
  change Tendsto (fun ε ↦ (CFC.sqrt (Wreg ε)).trace.re) L
    (𝓝 (CFC.sqrt W).trace.re) at hfinal
  simpa [finiteBuresRootFidelity, L, Wreg, W, Creg, Mreg,
    Function.comp_apply] using hfinal

/-- Fixed-pair product selected by one positive reporter. -/
def finiteBuresReporterProduct {n : ℕ}
    (C M A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ((C * A).trace).re * ((M * A⁻¹).trace).re

theorem tendsto_finiteBuresReporterProduct_regularization
    {n : ℕ} (C M A : Matrix (Fin n) (Fin n) ℂ) :
    Tendsto (fun ε ↦ finiteBuresReporterProduct
        (finitePositiveMatrixRegularization C ε)
        (finitePositiveMatrixRegularization M ε) A)
      (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (finiteBuresReporterProduct C M A)) := by
  have hcont : ContinuousAt (fun ε : ℝ ↦ finiteBuresReporterProduct
      (finitePositiveMatrixRegularization C ε)
      (finitePositiveMatrixRegularization M ε) A) 0 := by
    unfold finiteBuresReporterProduct finitePositiveMatrixRegularization Matrix.trace
    fun_prop
  simpa [finiteBuresReporterProduct, finitePositiveMatrixRegularization] using
    hcont.tendsto.mono_left nhdsWithin_le_nhds

/-- Real trace pairing of two finite positive semidefinite matrices is
nonnegative. -/
theorem finiteMatrix_re_trace_mul_nonneg_of_posSemidef
    {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ ((A * B).trace).re := by
  obtain ⟨D, hD⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  have hBfactor : B = D.conjTranspose * D := by
    simpa only [Matrix.star_eq_conjTranspose] using hD
  have hPSD : (D * A * D.conjTranspose).PosSemidef :=
    hA.mul_mul_conjTranspose_same D
  have htrace : 0 ≤ (D * A * D.conjTranspose).trace := hPSD.trace_nonneg
  have hre : 0 ≤ ((D * A * D.conjTranspose).trace).re :=
    (RCLike.nonneg_iff.mp htrace).1
  rw [hBfactor]
  have heq :
      (A * (D.conjTranspose * D)).trace =
        (D * A * D.conjTranspose).trace := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  rw [heq]
  exact hre

/-- Canonical Bures root fidelity squared is below every positive-reporter
product for arbitrary positive semidefinite pairs, including singular pairs. -/
theorem finiteBuresRootFidelity_sq_le_reporter_product
    {n : ℕ} {C M A : Matrix (Fin n) (Fin n) ℂ}
    (hC : C.PosSemidef) (hM : M.PosSemidef) (hA : A.PosDef) :
    finiteBuresRootFidelity C M ^ 2 ≤ finiteBuresReporterProduct C M A := by
  classical
  cases n with
  | zero =>
      have hCzero : C = 0 := Subsingleton.elim _ _
      have hMzero : M = 0 := Subsingleton.elim _ _
      have hAzero : A = 0 := Subsingleton.elim _ _
      subst C
      subst M
      subst A
      simp [finiteBuresRootFidelity, finiteBuresReporterProduct]
  | succ n =>
      let L : Filter ℝ := 𝓝[Set.Ioi (0 : ℝ)] 0
      have hfid := tendsto_finiteBuresRootFidelity_regularization hC hM
      have hprod := tendsto_finiteBuresReporterProduct_regularization C M A
      apply le_of_tendsto_of_tendsto (hfid.pow 2) hprod
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact finiteBuresRootFidelity_sq_le_reporter_product_of_posDef
        (finitePositiveMatrixRegularization_posDef hC hε)
        (finitePositiveMatrixRegularization_posDef hM hε) hA

theorem finiteBuresReporterCapacity_values_nonempty
    {n : ℕ} (C M : Matrix (Fin n) (Fin n) ℂ) :
    {q : ℝ | ∃ A : Matrix (Fin n) (Fin n) ℂ,
      A.PosDef ∧ q = ((C * A).trace).re * ((M * A⁻¹).trace).re}.Nonempty := by
  refine ⟨((C * 1).trace).re * ((M * (1 : Matrix (Fin n) (Fin n) ℂ)⁻¹).trace).re,
    1, Matrix.PosDef.one, rfl⟩

theorem finiteBuresReporterCapacity_le_product
    {n : ℕ} {C M A : Matrix (Fin n) (Fin n) ℂ}
    (hC : C.PosSemidef) (hM : M.PosSemidef) (hA : A.PosDef) :
    finiteBuresReporterCapacity C M ≤ finiteBuresReporterProduct C M A := by
  unfold finiteBuresReporterCapacity
  apply csInf_le
  · refine ⟨finiteBuresRootFidelity C M ^ 2, ?_⟩
    rintro q ⟨B, hB, rfl⟩
    simpa [finiteBuresReporterProduct] using
      finiteBuresRootFidelity_sq_le_reporter_product hC hM hB
  · exact ⟨A, hA, rfl⟩

theorem re_trace_mul_le_regularization
    {n : ℕ} (C A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosSemidef) {ε : ℝ} (hε : 0 < ε) :
    ((C * A).trace).re ≤
      ((finitePositiveMatrixRegularization C ε * A).trace).re := by
  have hextraPSD : (ε • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef :=
    (Matrix.PosDef.one.smul hε).posSemidef
  have hextra := finiteMatrix_re_trace_mul_nonneg_of_posSemidef
    hextraPSD hA
  unfold finitePositiveMatrixRegularization
  rw [Matrix.add_mul, Matrix.trace_add, Complex.add_re]
  linarith

theorem finiteBuresReporterProduct_le_regularization
    {n : ℕ} {C M A : Matrix (Fin n) (Fin n) ℂ}
    (hC : C.PosSemidef) (hM : M.PosSemidef) (hA : A.PosDef)
    {ε : ℝ} (hε : 0 < ε) :
    finiteBuresReporterProduct C M A ≤
      finiteBuresReporterProduct
        (finitePositiveMatrixRegularization C ε)
        (finitePositiveMatrixRegularization M ε) A := by
  have hx0 : 0 ≤ ((C * A).trace).re :=
    finiteMatrix_re_trace_mul_nonneg_of_posSemidef hC hA.posSemidef
  have hy0 : 0 ≤ ((M * A⁻¹).trace).re :=
    finiteMatrix_re_trace_mul_nonneg_of_posSemidef hM hA.inv.posSemidef
  have hx := re_trace_mul_le_regularization C A hA.posSemidef hε
  have hy := re_trace_mul_le_regularization M A⁻¹ hA.inv.posSemidef hε
  unfold finiteBuresReporterProduct
  exact mul_le_mul hx hy hy0 (hx0.trans hx)

theorem finiteBuresReporterCapacity_le_rootFidelity_sq
    {n : ℕ} {C M : Matrix (Fin n) (Fin n) ℂ}
    (hC : C.PosSemidef) (hM : M.PosSemidef) :
    finiteBuresReporterCapacity C M ≤ finiteBuresRootFidelity C M ^ 2 := by
  classical
  cases n with
  | zero =>
      have hCzero : C = 0 := Subsingleton.elim _ _
      have hMzero : M = 0 := Subsingleton.elim _ _
      subst C
      subst M
      simp [finiteBuresReporterCapacity, finiteBuresRootFidelity]
      apply csInf_le
      · exact ⟨0, by rintro q ⟨_, rfl⟩; rfl⟩
      · exact ⟨⟨1, Matrix.PosDef.one⟩, rfl⟩
  | succ n =>
      let L : Filter ℝ := 𝓝[Set.Ioi (0 : ℝ)] 0
      have hfid := tendsto_finiteBuresRootFidelity_regularization hC hM
      apply ge_of_tendsto (hfid.pow 2)
      filter_upwards [self_mem_nhdsWithin] with ε hε
      let Cε := finitePositiveMatrixRegularization C ε
      let Mε := finitePositiveMatrixRegularization M ε
      let Aε := finiteBuresOptimalReporter Cε Mε
      have hCε : Cε.PosDef := finitePositiveMatrixRegularization_posDef hC hε
      have hMε : Mε.PosDef := finitePositiveMatrixRegularization_posDef hM hε
      have hAε : Aε.PosDef := finiteBuresOptimalReporter_posDef hCε hMε
      calc
        finiteBuresReporterCapacity C M ≤ finiteBuresReporterProduct C M Aε :=
          finiteBuresReporterCapacity_le_product hC hM hAε
        _ ≤ finiteBuresReporterProduct Cε Mε Aε :=
          finiteBuresReporterProduct_le_regularization hC hM hAε hε
        _ = finiteBuresRootFidelity Cε Mε ^ 2 := by
          simpa [finiteBuresReporterProduct, Aε] using
            finiteBuresOptimalReporter_product_eq_rootFidelity_sq hCε hMε

/-- **Full finite-dimensional Alberti product identity.**  For every pair of
positive semidefinite matrices, including singular matrices, the infimum over
all positive-definite reporters equals canonical Bures root fidelity squared. -/
theorem finiteBuresReporterCapacity_eq_rootFidelity_sq
    {n : ℕ} {C M : Matrix (Fin n) (Fin n) ℂ}
    (hC : C.PosSemidef) (hM : M.PosSemidef) :
    finiteBuresReporterCapacity C M = finiteBuresRootFidelity C M ^ 2 := by
  apply le_antisymm
  · exact finiteBuresReporterCapacity_le_rootFidelity_sq hC hM
  · unfold finiteBuresReporterCapacity
    apply le_csInf (finiteBuresReporterCapacity_values_nonempty C M)
    rintro q ⟨A, hA, rfl⟩
    simpa [finiteBuresReporterProduct] using
      finiteBuresRootFidelity_sq_le_reporter_product hC hM hA

/-! ## Alberti half-sum identity -/

/-- Bures root fidelity is nonnegative for every positive semidefinite pair. -/
theorem finiteBuresRootFidelity_nonneg
    {n : ℕ} {C M : Matrix (Fin n) (Fin n) ℂ}
    (hM : M.PosSemidef) :
    0 ≤ finiteBuresRootFidelity C M := by
  have hM0 : 0 ≤ M := Matrix.nonneg_iff_posSemidef.mpr hM
  have hW0 : 0 ≤ CFC.conjSqrt C M := by
    simpa using (CFC.conjSqrt_le_conjSqrt (c := C) hM0)
  have htrace : 0 ≤ (CFC.sqrt (CFC.conjSqrt C M)).trace := by
    simpa using (CFC.sqrt_nonneg (CFC.conjSqrt C M)).trace_nonneg
  exact (Complex.nonneg_iff.mp htrace).1

/-- Additive Alberti objective selected by one positive reporter. -/
def finiteBuresReporterHalfSum {n : ℕ}
    (C M A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  (((C * A).trace).re + ((M * A⁻¹).trace).re) / 2

/-- The Bures root fidelity lies below every additive Alberti objective. -/
theorem finiteBuresRootFidelity_le_reporterHalfSum
    {n : ℕ} {C M A : Matrix (Fin n) (Fin n) ℂ}
    (hC : C.PosSemidef) (hM : M.PosSemidef) (hA : A.PosDef) :
    finiteBuresRootFidelity C M ≤ finiteBuresReporterHalfSum C M A := by
  have hx : 0 ≤ ((C * A).trace).re :=
    finiteMatrix_re_trace_mul_nonneg_of_posSemidef hC hA.posSemidef
  have hy : 0 ≤ ((M * A⁻¹).trace).re :=
    finiteMatrix_re_trace_mul_nonneg_of_posSemidef hM hA.inv.posSemidef
  have hf : 0 ≤ finiteBuresRootFidelity C M :=
    finiteBuresRootFidelity_nonneg hM
  have hsq : finiteBuresRootFidelity C M ^ 2 ≤
      ((C * A).trace).re * ((M * A⁻¹).trace).re := by
    simpa [finiteBuresReporterProduct] using
      finiteBuresRootFidelity_sq_le_reporter_product hC hM hA
  unfold finiteBuresReporterHalfSum
  nlinarith [sq_nonneg (((C * A).trace).re - ((M * A⁻¹).trace).re)]

/-- Infimum of additive Alberti objectives over every positive reporter. -/
def finiteBuresReporterHalfSumCapacity {n : ℕ}
    (C M : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  sInf {q : ℝ | ∃ A : Matrix (Fin n) (Fin n) ℂ,
    A.PosDef ∧ q = finiteBuresReporterHalfSum C M A}

theorem finiteBuresReporterHalfSumCapacity_values_nonempty
    {n : ℕ} (C M : Matrix (Fin n) (Fin n) ℂ) :
    {q : ℝ | ∃ A : Matrix (Fin n) (Fin n) ℂ,
      A.PosDef ∧ q = finiteBuresReporterHalfSum C M A}.Nonempty := by
  exact ⟨finiteBuresReporterHalfSum C M 1, 1, Matrix.PosDef.one, rfl⟩

theorem finiteBuresReporterHalfSumCapacity_le_halfSum
    {n : ℕ} {C M A : Matrix (Fin n) (Fin n) ℂ}
    (hC : C.PosSemidef) (hM : M.PosSemidef) (hA : A.PosDef) :
    finiteBuresReporterHalfSumCapacity C M ≤
      finiteBuresReporterHalfSum C M A := by
  unfold finiteBuresReporterHalfSumCapacity
  apply csInf_le
  · refine ⟨finiteBuresRootFidelity C M, ?_⟩
    rintro q ⟨B, hB, rfl⟩
    exact finiteBuresRootFidelity_le_reporterHalfSum hC hM hB
  · exact ⟨A, hA, rfl⟩

theorem finiteBuresRootFidelity_le_reporterHalfSumCapacity
    {n : ℕ} {C M : Matrix (Fin n) (Fin n) ℂ}
    (hC : C.PosSemidef) (hM : M.PosSemidef) :
    finiteBuresRootFidelity C M ≤
      finiteBuresReporterHalfSumCapacity C M := by
  unfold finiteBuresReporterHalfSumCapacity
  apply le_csInf (finiteBuresReporterHalfSumCapacity_values_nonempty C M)
  rintro q ⟨A, hA, rfl⟩
  exact finiteBuresRootFidelity_le_reporterHalfSum hC hM hA

/-- For positive-definite pairs, the geometric-mean reporter balances both
trace channels and attains the additive Alberti objective. -/
theorem finiteBuresOptimalReporter_halfSum_eq_rootFidelity
    {n : ℕ} {C M : Matrix (Fin n) (Fin n) ℂ}
    (hC : C.PosDef) (hM : M.PosDef) :
    finiteBuresReporterHalfSum C M (finiteBuresOptimalReporter C M) =
      finiteBuresRootFidelity C M := by
  rw [finiteBuresReporterHalfSum,
    congrArg Complex.re (trace_mul_finiteBuresOptimalReporter_eq_root hC),
    congrArg Complex.re
      (trace_mul_finiteBuresOptimalReporter_inv_eq_root hC hM)]
  simp [finiteBuresRootFidelity]

theorem finiteBuresReporterHalfSum_le_regularization
    {n : ℕ} {C M A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef) {ε : ℝ} (hε : 0 < ε) :
    finiteBuresReporterHalfSum C M A ≤
      finiteBuresReporterHalfSum
        (finitePositiveMatrixRegularization C ε)
        (finitePositiveMatrixRegularization M ε) A := by
  unfold finiteBuresReporterHalfSum
  exact div_le_div_of_nonneg_right
    (add_le_add
      (re_trace_mul_le_regularization C A hA.posSemidef hε)
      (re_trace_mul_le_regularization M A⁻¹ hA.inv.posSemidef hε))
    (by norm_num)

theorem finiteBuresReporterHalfSumCapacity_le_rootFidelity
    {n : ℕ} {C M : Matrix (Fin n) (Fin n) ℂ}
    (hC : C.PosSemidef) (hM : M.PosSemidef) :
    finiteBuresReporterHalfSumCapacity C M ≤
      finiteBuresRootFidelity C M := by
  classical
  cases n with
  | zero =>
      have hCzero : C = 0 := Subsingleton.elim _ _
      have hMzero : M = 0 := Subsingleton.elim _ _
      subst C
      subst M
      have h := finiteBuresReporterHalfSumCapacity_le_halfSum
        (C := (0 : Matrix (Fin 0) (Fin 0) ℂ)) (M := 0) (A := 1)
        hC hM Matrix.PosDef.one
      simpa [finiteBuresReporterHalfSum, finiteBuresRootFidelity] using h
  | succ n =>
      let L : Filter ℝ := 𝓝[Set.Ioi (0 : ℝ)] 0
      have hfid := tendsto_finiteBuresRootFidelity_regularization hC hM
      apply ge_of_tendsto hfid
      filter_upwards [self_mem_nhdsWithin] with ε hε
      let Cε := finitePositiveMatrixRegularization C ε
      let Mε := finitePositiveMatrixRegularization M ε
      let Aε := finiteBuresOptimalReporter Cε Mε
      have hCε : Cε.PosDef := finitePositiveMatrixRegularization_posDef hC hε
      have hMε : Mε.PosDef := finitePositiveMatrixRegularization_posDef hM hε
      have hAε : Aε.PosDef := finiteBuresOptimalReporter_posDef hCε hMε
      calc
        finiteBuresReporterHalfSumCapacity C M ≤
            finiteBuresReporterHalfSum C M Aε :=
          finiteBuresReporterHalfSumCapacity_le_halfSum hC hM hAε
        _ ≤ finiteBuresReporterHalfSum Cε Mε Aε :=
          finiteBuresReporterHalfSum_le_regularization hAε hε
        _ = finiteBuresRootFidelity Cε Mε := by
          exact finiteBuresOptimalReporter_halfSum_eq_rootFidelity hCε hMε

/-- **Full finite-dimensional Alberti half-sum identity.**  For every pair
of positive semidefinite matrices, including singular matrices, the infimum
of the additive reporter objective is exactly Bures root fidelity. -/
theorem finiteBuresReporterHalfSumCapacity_eq_rootFidelity
    {n : ℕ} {C M : Matrix (Fin n) (Fin n) ℂ}
    (hC : C.PosSemidef) (hM : M.PosSemidef) :
    finiteBuresReporterHalfSumCapacity C M =
      finiteBuresRootFidelity C M := by
  exact le_antisymm
    (finiteBuresReporterHalfSumCapacity_le_rootFidelity hC hM)
    (finiteBuresRootFidelity_le_reporterHalfSumCapacity hC hM)

/-- Bures root fidelity is continuous in its positive-semidefinite target
argument.  No invertibility of either matrix is required. -/
theorem continuousOn_finiteBuresRootFidelity_right
    {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ) :
    ContinuousOn (finiteBuresRootFidelity C)
      {M : Matrix (Fin n) (Fin n) ℂ | M.PosSemidef} := by
  letI : CStarAlgebra (Matrix (Fin n) (Fin n) ℂ) := {}
  let positiveCone : Set (Matrix (Fin n) (Fin n) ℂ) := {D | 0 ≤ D}
  have hW : Continuous
      (fun M : Matrix (Fin n) (Fin n) ℂ => CFC.conjSqrt C M) := by
    simp only [CFC.conjSqrt_apply]
    fun_prop
  have hmaps : MapsTo (fun M : Matrix (Fin n) (Fin n) ℂ =>
      CFC.conjSqrt C M)
      {M : Matrix (Fin n) (Fin n) ℂ | M.PosSemidef} positiveCone := by
    intro M hM
    simpa [positiveCone] using
      (CFC.conjSqrt_le_conjSqrt (c := C) hM.nonneg)
  have hsqrt : ContinuousOn
      (fun M : Matrix (Fin n) (Fin n) ℂ =>
        CFC.sqrt (CFC.conjSqrt C M))
      {M : Matrix (Fin n) (Fin n) ℂ | M.PosSemidef} := by
    exact CFC.continuousOn_sqrt.comp hW.continuousOn hmaps
  have htraceRe : Continuous
      (fun D : Matrix (Fin n) (Fin n) ℂ => D.trace.re) := by
    unfold Matrix.trace
    fun_prop
  have hfinal := htraceRe.comp_continuousOn hsqrt
  change ContinuousOn (fun M : Matrix (Fin n) (Fin n) ℂ =>
    (CFC.sqrt (CFC.conjSqrt C M)).trace.re)
    {M : Matrix (Fin n) (Fin n) ℂ | M.PosSemidef}
  exact hfinal

end

end GaloisForLFunctions.HTGeometry
