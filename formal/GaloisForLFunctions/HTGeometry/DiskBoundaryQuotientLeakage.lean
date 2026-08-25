import GaloisForLFunctions.HTGeometry.HardyBoundaryCayleyIdentification
import GaloisForLFunctions.HTGeometry.ModelSpaceLeakageDenseRank
import GaloisForLFunctions.HTGeometry.RestrictedAdjointCancellationQuotient

/-!
# Literal boundary leakage of a disk inner quotient

For bounded analytic disk multipliers `A` and `B`, with `B` inner, this file constructs the
literal real-line boundary multiplier `A / B` through the exact Cayley half-density.  Its
anti-causal compression factors exactly as the canonical projection of `M_A` onto `K_B`, followed
by an isometric embedding of `K_B` into lower Hardy space.  No boundary continuity is assumed:
the construction uses the Riesz--Fischer boundary representatives.
-/

open Complex MeasureTheory
open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

local instance : CompleteSpace UpperHardyL2 :=
  RHTower.isClosed_hardyL2.completeSpace_coe

local instance : CompleteSpace LowerHardyL2 :=
  RHTower.hardyL2.isClosed_orthogonal.completeSpace_coe

/-- Algebraic rank at least `r` for a bounded operator between Hilbert spaces. -/
def ContinuousLinearMapRankAtLeast
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (T : H →L[ℂ] K) (r : ℕ) : Prop :=
  ∃ v : Fin r → H, LinearIndependent ℂ (fun i => T (v i))

/-- Multiplication by a nonzero scalar preserves every algebraic rank level of a bounded
operator. -/
theorem continuousLinearMapRankAtLeast_smul_iff
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (T : H →L[ℂ] K) (c : ℂ) (hc : c ≠ 0) (r : ℕ) :
    ContinuousLinearMapRankAtLeast (c • T) r ↔
      ContinuousLinearMapRankAtLeast T r := by
  have hscale {v : Fin r → K} (hv : LinearIndependent ℂ v)
      {a : ℂ} (ha : a ≠ 0) :
      LinearIndependent ℂ (fun i => a • v i) := by
    rw [Fintype.linearIndependent_iff] at hv ⊢
    intro d hd
    apply hv d
    apply (smul_right_injective K ha)
    simpa [Finset.smul_sum, smul_smul, mul_comm] using hd
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨v, ?_⟩
    have hinv := hscale hv (inv_ne_zero hc)
    simpa [smul_smul, hc] using hinv
  · rintro ⟨v, hv⟩
    refine ⟨v, ?_⟩
    simpa only [ContinuousLinearMap.smul_apply] using hscale hv hc

/-- A unit-modulus scalar does not change the operator norm of a bounded complex-linear map. -/
theorem norm_smul_continuousLinearMap_of_norm_eq_one
    {H K : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    (T : H →L[ℂ] K) (c : ℂ) (hc : ‖c‖ = 1) :
    ‖c • T‖ = ‖T‖ := by
  apply le_antisymm
  · apply (c • T).opNorm_le_bound (norm_nonneg T)
    intro x
    change ‖c • T x‖ ≤ ‖T‖ * ‖x‖
    rw [norm_smul, hc, one_mul]
    exact T.le_opNorm x
  · apply T.opNorm_le_bound (norm_nonneg (c • T))
    intro x
    have h := (c • T).le_opNorm x
    change ‖c • T x‖ ≤ ‖c • T‖ * ‖x‖ at h
    rw [norm_smul, hc, one_mul] at h
    exact h

/-- Algebraic rank passes from a bounded Hilbert operator to its adjoint. -/
theorem continuousLinearMapRankAtLeast_adjoint_of
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (T : H →L[ℂ] K) {r : ℕ}
    (hT : ContinuousLinearMapRankAtLeast T r) :
    ContinuousLinearMapRankAtLeast T.adjoint r := by
  obtain ⟨v, hv⟩ := hT
  refine ⟨fun i => T (v i), ?_⟩
  rw [Fintype.linearIndependent_iff] at hv ⊢
  intro c hc
  apply hv c
  have hzero : T.adjoint (∑ i, c i • T (v i)) = 0 := by
    simpa only [map_sum, map_smul] using hc
  have hsum : ∑ i, c i • T (v i) = T (∑ i, c i • v i) := by
    simp only [map_sum, map_smul]
  rw [hsum] at hzero ⊢
  have hnorm : ‖∑ i, c i • T (v i)‖ ^ 2 = 0 := by
    rw [hsum]
    rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)]
    rw [← ContinuousLinearMap.adjoint_inner_right, hzero]
    simp
  have hy : ∑ i, c i • T (v i) = 0 := by
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)
  simpa only [map_sum, map_smul] using hy

/-- A bounded Hilbert operator and its adjoint have the same full algebraic rank profile. -/
theorem continuousLinearMapRankAtLeast_adjoint_iff
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (T : H →L[ℂ] K) (r : ℕ) :
    ContinuousLinearMapRankAtLeast T.adjoint r ↔
      ContinuousLinearMapRankAtLeast T r := by
  constructor
  · intro h
    simpa only [ContinuousLinearMap.adjoint_adjoint] using
      continuousLinearMapRankAtLeast_adjoint_of T.adjoint h
  · exact continuousLinearMapRankAtLeast_adjoint_of T

/-- Algebraic rank profile for operators with literal upper-Hardy domain. -/
def UpperHardyBoundaryOperatorRankAtLeast
    (T : UpperHardyL2 →L[ℂ] LowerHardyL2) (r : ℕ) : Prop :=
  ContinuousLinearMapRankAtLeast T r

/-- Everywhere-unimodular patch of an inner multiplier's Riesz--Fischer boundary value. -/
def diskInnerBoundarySymbol (B : DiskMultiplier) (z : Circle) : ℂ :=
  if ‖diskMultiplierBoundarySymbol B z‖ = 1 then
    diskMultiplierBoundarySymbol B z else 1

theorem measurable_diskInnerBoundarySymbol (B : DiskMultiplier) :
    Measurable (diskInnerBoundarySymbol B) := by
  apply Measurable.ite
  · exact measurableSet_eq_fun
      (measurable_diskMultiplierBoundarySymbol B).norm measurable_const
  · exact measurable_diskMultiplierBoundarySymbol B
  · exact measurable_const

@[simp] theorem norm_diskInnerBoundarySymbol (B : DiskMultiplier) (z : Circle) :
    ‖diskInnerBoundarySymbol B z‖ = 1 := by
  rw [diskInnerBoundarySymbol]
  split_ifs with h
  · exact h
  · simp

theorem diskInnerBoundarySymbol_ae (B : DiskMultiplier)
    (hBbd : B.bd = 1) (hB : HardyMultiplierIsometry B) :
    diskInnerBoundarySymbol B =ᵐ[circleLebesgue]
      diskMultiplierBoundaryFun B := by
  filter_upwards [diskMultiplierBoundarySymbol_ae B,
    ae_norm_diskMultiplierBoundaryFun_eq_one B hBbd hB] with z hsymbol hnorm
  rw [diskInnerBoundarySymbol, if_pos]
  · exact hsymbol
  · rwa [hsymbol]

/-- Pulled-back real-line multiplication by a disk multiplier's boundary value. -/
def diskBoundaryLineMul (A : DiskMultiplier) :
    RealLineL2 →L[ℂ] RealLineL2 :=
  lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ))
    ((measurable_diskMultiplierBoundarySymbol A).comp
      continuous_circleCayley.measurable)
    A.bd_nonneg (fun x => norm_diskMultiplierBoundarySymbol_le A (circleCayley x))

/-- Pulled-back real-line unitary multiplication by an inner boundary value. -/
def diskInnerBoundaryLineUnitary (B : DiskMultiplier) :
    RealLineL2 ≃ₗᵢ[ℂ] RealLineL2 :=
  RHTower.unimodularMulUnitary
    (fun x => diskInnerBoundarySymbol B (circleCayley x))
    ((measurable_diskInnerBoundarySymbol B).comp
      continuous_circleCayley.measurable).aestronglyMeasurable
    (fun x => norm_diskInnerBoundarySymbol B (circleCayley x))

theorem diskBoundaryLineMul_apply_hardy (A : DiskMultiplier) (f : HardyDisk) :
    diskBoundaryLineMul A
        (((hardyDiskLineCayleyCLM f : UpperHardyL2) : RealLineL2)) =
      (((hardyDiskLineCayleyCLM (hardyMul A f) : UpperHardyL2) : RealLineL2)) := by
  have htransport := circleLineCayleyIsometry_mul
    (measurable_diskMultiplierBoundarySymbol A) A.bd_nonneg
    (norm_diskMultiplierBoundarySymbol_le A) (hardyDiskBoundary f)
  change circleLineCayleyIsometry
      (diskMultiplierBoundaryMul A (hardyDiskBoundary f)) =
    diskBoundaryLineMul A (circleLineCayleyIsometry (hardyDiskBoundary f)) at htransport
  rw [diskMultiplierBoundaryMul_apply,
    circleLineCayleyIsometry_hardyDiskBoundary,
    circleLineCayleyIsometry_hardyDiskBoundary, map_smul] at htransport
  have hI : (I : ℂ) ≠ 0 := by norm_num
  exact ((smul_right_injective RealLineL2 hI) htransport).symm

theorem diskInnerBoundaryLineUnitary_eq_lineMul
    (B : DiskMultiplier) (hBbd : B.bd = 1)
    (hB : HardyMultiplierIsometry B) :
    (diskInnerBoundaryLineUnitary B).toLinearIsometry.toContinuousLinearMap =
      diskBoundaryLineMul B := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  have hinner := RHTower.unimodularMulUnitary_ae
    (fun x => diskInnerBoundarySymbol B (circleCayley x))
    ((measurable_diskInnerBoundarySymbol B).comp
      continuous_circleCayley.measurable).aestronglyMeasurable
    (fun x => norm_diskInnerBoundarySymbol B (circleCayley x)) f
  have hline := lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure ℝ))
    ((measurable_diskMultiplierBoundarySymbol B).comp
      continuous_circleCayley.measurable)
    B.bd_nonneg (fun x => norm_diskMultiplierBoundarySymbol_le B (circleCayley x)) f
  have hboundaryCircle := diskInnerBoundarySymbol_ae B hBbd hB
  have hsymbolCircle := diskMultiplierBoundarySymbol_ae B
  have hboundaryWeighted := hboundaryCircle.comp_tendsto
    circleCayley_weighted_measurePreserving.quasiMeasurePreserving.tendsto_ae
  have hsymbolWeighted := hsymbolCircle.comp_tendsto
    circleCayley_weighted_measurePreserving.quasiMeasurePreserving.tendsto_ae
  have hboundary := (withDensity_realDensity_ae_eq measurable_standardCauchyWeight
    standardCauchyWeight_pos).mp hboundaryWeighted
  have hsymbol := (withDensity_realDensity_ae_eq measurable_standardCauchyWeight
    standardCauchyWeight_pos).mp hsymbolWeighted
  filter_upwards [hinner, hline, hboundary, hsymbol] with x hi hl hb hs
  calc
    ((diskInnerBoundaryLineUnitary B f : RealLineL2) : ℝ → ℂ) x =
        diskInnerBoundarySymbol B (circleCayley x) * f x := by
      change (((RHTower.unimodularMulUnitary
        (fun x => diskInnerBoundarySymbol B (circleCayley x)) _ _) f :
          RealLineL2) : ℝ → ℂ) x = _
      exact hi
    _ = diskMultiplierBoundarySymbol B (circleCayley x) * f x := by
      change diskInnerBoundarySymbol B (circleCayley x) =
        diskMultiplierBoundaryFun B (circleCayley x) at hb
      change diskMultiplierBoundarySymbol B (circleCayley x) =
        diskMultiplierBoundaryFun B (circleCayley x) at hs
      rw [hb, hs]
    _ = ((diskBoundaryLineMul B f : RealLineL2) : ℝ → ℂ) x := by
      symm
      change (((lpBoundedMulCLM
        ((measurable_diskMultiplierBoundarySymbol B).comp
          continuous_circleCayley.measurable)
        B.bd_nonneg
        (fun x => norm_diskMultiplierBoundarySymbol_le B (circleCayley x))) f :
          RealLineL2) : ℝ → ℂ) x = _
      simpa only [Function.comp_apply] using hl

theorem diskInnerBoundaryLineUnitary_apply_hardy
    (B : DiskMultiplier) (hBbd : B.bd = 1)
    (hB : HardyMultiplierIsometry B) (f : HardyDisk) :
    diskInnerBoundaryLineUnitary B
        (((hardyDiskLineCayleyCLM f : UpperHardyL2) : RealLineL2)) =
      (((hardyDiskLineCayleyCLM (hardyMul B f) : UpperHardyL2) : RealLineL2)) := by
  rw [show diskInnerBoundaryLineUnitary B
      (((hardyDiskLineCayleyCLM f : UpperHardyL2) : RealLineL2)) =
    (diskInnerBoundaryLineUnitary B).toLinearIsometry.toContinuousLinearMap
      (((hardyDiskLineCayleyCLM f : UpperHardyL2) : RealLineL2)) from rfl,
    diskInnerBoundaryLineUnitary_eq_lineMul B hBbd hB,
    diskBoundaryLineMul_apply_hardy]

/-- Whole-line multiplication by the inner quotient `A / B`. -/
def diskBoundaryInnerQuotientMul
    (A B : DiskMultiplier) (hBbd : B.bd = 1)
    (hB : HardyMultiplierIsometry B) :
    RealLineL2 →L[ℂ] RealLineL2 :=
  (diskInnerBoundaryLineUnitary B).symm.toLinearIsometry.toContinuousLinearMap.comp
    (diskBoundaryLineMul A)

/-- Pointwise representative of inverse-inner multiplication on the real line. -/
theorem diskInnerBoundaryLineUnitary_symm_ae
    (B : DiskMultiplier) (f : RealLineL2) :
    (diskInnerBoundaryLineUnitary B).symm f =ᵐ[(volume : Measure ℝ)]
      fun x => (diskInnerBoundarySymbol B (circleCayley x))⁻¹ * f x := by
  have hmeas : AEStronglyMeasurable
      (fun x => diskInnerBoundarySymbol B (circleCayley x)) volume :=
    ((measurable_diskInnerBoundarySymbol B).comp
      continuous_circleCayley.measurable).aestronglyMeasurable
  have hnorm : ∀ x : ℝ,
      ‖(diskInnerBoundarySymbol B (circleCayley x))⁻¹‖ = 1 := fun x => by
    rw [norm_inv, norm_diskInnerBoundarySymbol, inv_one]
  change RHTower.unimodularMulAux
      (fun x => (diskInnerBoundarySymbol B (circleCayley x))⁻¹)
      hmeas.inv₀ hnorm f =ᵐ[(volume : Measure ℝ)] _
  exact RHTower.unimodularMulAux_ae
    (fun x => (diskInnerBoundarySymbol B (circleCayley x))⁻¹)
    hmeas.inv₀ hnorm f

/-- Pointwise representative of the literal pulled-back quotient multiplication. -/
theorem diskBoundaryInnerQuotientMul_ae
    (A B : DiskMultiplier) (hBbd : B.bd = 1)
    (hB : HardyMultiplierIsometry B) (f : RealLineL2) :
    diskBoundaryInnerQuotientMul A B hBbd hB f =ᵐ[(volume : Measure ℝ)]
      fun x => (diskInnerBoundarySymbol B (circleCayley x))⁻¹ *
        diskMultiplierBoundarySymbol A (circleCayley x) * f x := by
  have hA := lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure ℝ))
    ((measurable_diskMultiplierBoundarySymbol A).comp
      continuous_circleCayley.measurable)
    A.bd_nonneg (fun x => norm_diskMultiplierBoundarySymbol_le A (circleCayley x)) f
  have hBae := diskInnerBoundaryLineUnitary_symm_ae B (diskBoundaryLineMul A f)
  filter_upwards [hA, hBae] with x hAx hBx
  change (((diskBoundaryLineMul A f : RealLineL2) : ℝ → ℂ) x) =
    diskMultiplierBoundarySymbol A (circleCayley x) * f x at hAx
  change ((diskBoundaryInnerQuotientMul A B hBbd hB f : RealLineL2) : ℝ → ℂ) x = _
  rw [diskBoundaryInnerQuotientMul, ContinuousLinearMap.comp_apply]
  change (((diskInnerBoundaryLineUnitary B).symm
    (diskBoundaryLineMul A f) : RealLineL2) : ℝ → ℂ) x = _
  rw [hBx, hAx]
  ring

/-- Literal anti-causal compression of the pulled-back boundary quotient `A / B`. -/
def diskBoundaryInnerQuotientLeakage
    (A B : DiskMultiplier) (hBbd : B.bd = 1)
    (hB : HardyMultiplierIsometry B) :
    UpperHardyL2 →L[ℂ] LowerHardyL2 :=
  hardyLeakage (diskBoundaryInnerQuotientMul A B hBbd hB)

/-- Ambient inverse-inner image of the denominator model space. -/
def diskBoundaryModelEmbeddingAmbient
    (B : DiskMultiplier) (hBbd : B.bd = 1)
    (hB : HardyMultiplierIsometry B) :
    hardyMultiplierModelSpace B →L[ℂ] RealLineL2 :=
  (diskInnerBoundaryLineUnitary B).symm.toLinearIsometry.toContinuousLinearMap.comp
    (UpperHardyL2.subtypeL.comp
      (hardyDiskLineCayleyCLM.comp (hardyMultiplierModelSpace B).subtypeL))

theorem diskBoundaryModelEmbeddingAmbient_mem_lower
    (B : DiskMultiplier) (hBbd : B.bd = 1)
    (hB : HardyMultiplierIsometry B)
    (k : hardyMultiplierModelSpace B) :
    diskBoundaryModelEmbeddingAmbient B hBbd hB k ∈ LowerHardyL2 := by
  change diskBoundaryModelEmbeddingAmbient B hBbd hB k ∈
    Submodule.orthogonal RHTower.hardyL2
  rw [Submodule.mem_orthogonal]
  intro q hq
  let f : HardyDisk := hardyLineDiskCayleyCLM ⟨q, hq⟩
  have hqeq : q = (((hardyDiskLineCayleyCLM f : UpperHardyL2) : RealLineL2)) := by
    change q = (((hardyDiskLineCayleyCLM (hardyLineDiskCayleyCLM ⟨q, hq⟩) :
      UpperHardyL2) : RealLineL2))
    exact congrArg (fun u : UpperHardyL2 => (u : RealLineL2))
      (hardyDiskLineCayleyCLM_apply_hardyLineDiskCayleyCLM ⟨q, hq⟩).symm
  have hunitary := (diskInnerBoundaryLineUnitary B).inner_map_map
    (diskBoundaryModelEmbeddingAmbient B hBbd hB k)
    (((hardyDiskLineCayleyCLM f : UpperHardyL2) : RealLineL2))
  have hembed : diskInnerBoundaryLineUnitary B
      (diskBoundaryModelEmbeddingAmbient B hBbd hB k) =
      (((hardyDiskLineCayleyCLM (k : HardyDisk) : UpperHardyL2) : RealLineL2)) := by
    exact (diskInnerBoundaryLineUnitary B).apply_symm_apply _
  have hBf := diskInnerBoundaryLineUnitary_apply_hardy B hBbd hB f
  rw [hembed, hBf] at hunitary
  have hkorthRaw : inner ℂ (hardyMul B f) (k : HardyDisk) = 0 :=
    (Submodule.mem_orthogonal
      (LinearMap.range ((hardyMul B : HardyDisk →L[ℂ] HardyDisk) :
        HardyDisk →ₗ[ℂ] HardyDisk)) (k : HardyDisk)).mp
      k.property (hardyMul B f) ⟨f, rfl⟩
  have hkorth : inner ℂ (k : HardyDisk) (hardyMul B f) = 0 :=
    inner_eq_zero_symm.mp hkorthRaw
  have hcayley : inner ℂ
      (hardyDiskLineCayleyCLM (k : HardyDisk))
      (hardyDiskLineCayleyCLM (hardyMul B f)) = 0 := by
    rw [inner_hardyDiskLineCayleyCLM, hkorth]
  rw [hqeq]
  exact inner_eq_zero_symm.mpr (hunitary.symm.trans hcayley)

/-- Inverse-inner multiplication identifies the model channel isometrically with lower Hardy. -/
def diskBoundaryModelEmbedding
    (B : DiskMultiplier) (hBbd : B.bd = 1)
    (hB : HardyMultiplierIsometry B) :
    hardyMultiplierModelSpace B →L[ℂ] LowerHardyL2 :=
  (diskBoundaryModelEmbeddingAmbient B hBbd hB).codRestrict
    LowerHardyL2 (diskBoundaryModelEmbeddingAmbient_mem_lower B hBbd hB)

theorem norm_diskBoundaryModelEmbedding
    (B : DiskMultiplier) (hBbd : B.bd = 1)
    (hB : HardyMultiplierIsometry B)
    (k : hardyMultiplierModelSpace B) :
    ‖diskBoundaryModelEmbedding B hBbd hB k‖ = ‖k‖ := by
  change ‖(diskInnerBoundaryLineUnitary B).symm
      (((hardyDiskLineCayleyCLM (k : HardyDisk) : UpperHardyL2) : RealLineL2))‖ = ‖k‖
  rw [(diskInnerBoundaryLineUnitary B).symm.norm_map]
  change ‖hardyDiskLineCayleyCLM (k : HardyDisk)‖ = ‖(k : HardyDisk)‖
  rw [norm_hardyDiskLineCayleyCLM]

def diskBoundaryModelEmbeddingIsometry
    (B : DiskMultiplier) (hBbd : B.bd = 1)
    (hB : HardyMultiplierIsometry B) :
    hardyMultiplierModelSpace B →ₗᵢ[ℂ] LowerHardyL2 where
  toLinearMap := (diskBoundaryModelEmbedding B hBbd hB).toLinearMap
  norm_map' := norm_diskBoundaryModelEmbedding B hBbd hB

/-- Exact factorization of literal quotient leakage through the denominator model channel. -/
theorem diskBoundaryInnerQuotientLeakage_eq_modelEmbedding_comp
    (A B : DiskMultiplier) (hBbd : B.bd = 1)
    (hB : HardyMultiplierIsometry B) :
    diskBoundaryInnerQuotientLeakage A B hBbd hB =
      (diskBoundaryModelEmbedding B hBbd hB).comp
        ((modelSpaceLeakageCore (hardyMultiplierModelSpace B) (hardyMul A)).comp
          hardyLineDiskCayleyCLM) := by
  apply ContinuousLinearMap.ext
  intro u
  let f : HardyDisk := hardyLineDiskCayleyCLM u
  have hueq : u = hardyDiskLineCayleyCLM f := by
    exact (hardyDiskLineCayleyCLM_apply_hardyLineDiskCayleyCLM u).symm
  let K := hardyMultiplierModelSpace B
  let y : HardyDisk := hardyMul A f
  let p : HardyDisk := K.starProjection y
  let r : HardyDisk := y - p
  have hrange : r ∈ LinearMap.range ((hardyMul B : HardyDisk →L[ℂ] HardyDisk) :
      HardyDisk →ₗ[ℂ] HardyDisk) := by
    have hrorth : r ∈ Submodule.orthogonal K :=
      K.sub_starProjection_mem_orthogonal y
    rw [hardyMultiplierModelSpace_orthogonal_eq_range_of_isometry B hB] at hrorth
    exact hrorth
  obtain ⟨g, hg⟩ := hrange
  have hmul : diskBoundaryInnerQuotientMul A B hBbd hB
      ((u : UpperHardyL2) : RealLineL2) =
      diskBoundaryModelEmbeddingAmbient B hBbd hB
        (modelSpaceLeakageCore K (hardyMul A) f) +
      (((hardyDiskLineCayleyCLM g : UpperHardyL2) : RealLineL2)) := by
    change (diskInnerBoundaryLineUnitary B).symm
        (diskBoundaryLineMul A ((u : UpperHardyL2) : RealLineL2)) = _
    rw [hueq, diskBoundaryLineMul_apply_hardy]
    have hy : hardyMul A f = p + r := by dsimp [p, r]; abel
    rw [hy, map_add]
    have hr : r = hardyMul B g := hg.symm
    rw [hr]
    have hBg := diskInnerBoundaryLineUnitary_apply_hardy B hBbd hB g
    calc
      (diskInnerBoundaryLineUnitary B).symm
          ((((hardyDiskLineCayleyCLM p : UpperHardyL2) : RealLineL2)) +
            (((hardyDiskLineCayleyCLM (hardyMul B g) : UpperHardyL2) :
              RealLineL2))) =
        (diskInnerBoundaryLineUnitary B).symm
            (((hardyDiskLineCayleyCLM p : UpperHardyL2) : RealLineL2)) +
          (diskInnerBoundaryLineUnitary B).symm
            (((hardyDiskLineCayleyCLM (hardyMul B g) : UpperHardyL2) :
              RealLineL2)) := by rw [map_add]
      _ = (diskInnerBoundaryLineUnitary B).symm
            (((hardyDiskLineCayleyCLM p : UpperHardyL2) : RealLineL2)) +
          (((hardyDiskLineCayleyCLM g : UpperHardyL2) : RealLineL2)) := by
        rw [← hBg, (diskInnerBoundaryLineUnitary B).symm_apply_apply]
      _ = _ := rfl
  change LowerHardyL2.orthogonalProjectionOnto
      (diskBoundaryInnerQuotientMul A B hBbd hB
        ((u : UpperHardyL2) : RealLineL2)) =
    (diskBoundaryModelEmbedding B hBbd hB
      (modelSpaceLeakageCore K (hardyMul A) f) : LowerHardyL2)
  rw [hmul, map_add]
  have hmodel := LowerHardyL2.orthogonalProjection_mem_subspace_eq_self
    (diskBoundaryModelEmbedding B hBbd hB
      (modelSpaceLeakageCore K (hardyMul A) f))
  change LowerHardyL2.orthogonalProjectionOnto
      (diskBoundaryModelEmbeddingAmbient B hBbd hB
        (modelSpaceLeakageCore K (hardyMul A) f)) =
    diskBoundaryModelEmbedding B hBbd hB
      (modelSpaceLeakageCore K (hardyMul A) f) at hmodel
  have hzero : LowerHardyL2.orthogonalProjectionOnto
      (((hardyDiskLineCayleyCLM g : UpperHardyL2) : RealLineL2)) = 0 := by
    rw [Submodule.orthogonalProjectionOnto_eq_zero_iff]
    rw [show Submodule.orthogonal LowerHardyL2 = RHTower.hardyL2 by
      exact Submodule.orthogonal_orthogonal RHTower.hardyL2]
    exact (hardyDiskLineCayleyCLM g).property
  rw [hmodel, hzero, add_zero]

/-- The literal quotient leakage has exactly the norm of its disk model-space core.  Both Cayley
transport on the domain and inverse-inner model embedding on the codomain are isometric. -/
theorem norm_diskBoundaryInnerQuotientLeakage_eq_modelSpaceLeakageCore
    (A B : DiskMultiplier) (hBbd : B.bd = 1)
    (hB : HardyMultiplierIsometry B) :
    ‖diskBoundaryInnerQuotientLeakage A B hBbd hB‖ =
      ‖modelSpaceLeakageCore (hardyMultiplierModelSpace B) (hardyMul A)‖ := by
  let T := modelSpaceLeakageCore (hardyMultiplierModelSpace B) (hardyMul A)
  let Q := diskBoundaryInnerQuotientLeakage A B hBbd hB
  have hQ : Q = (diskBoundaryModelEmbedding B hBbd hB).comp
      (T.comp hardyLineDiskCayleyCLM) :=
    diskBoundaryInnerQuotientLeakage_eq_modelEmbedding_comp A B hBbd hB
  apply le_antisymm
  · apply Q.opNorm_le_bound (norm_nonneg T)
    intro u
    rw [hQ]
    change ‖diskBoundaryModelEmbedding B hBbd hB
      (T (hardyLineDiskCayleyCLM u))‖ ≤ _
    rw [norm_diskBoundaryModelEmbedding]
    simpa only [norm_hardyLineDiskCayleyCLM] using
      T.le_opNorm (hardyLineDiskCayleyCLM u)
  · apply T.opNorm_le_bound (norm_nonneg Q)
    intro f
    have hQf : Q (hardyDiskLineCayleyCLM f) =
        diskBoundaryModelEmbedding B hBbd hB (T f) := by
      rw [hQ]
      change diskBoundaryModelEmbedding B hBbd hB
        (T (hardyLineDiskCayleyCLM (hardyDiskLineCayleyCLM f))) = _
      rw [hardyLineDiskCayleyCLM_apply_hardyDiskLineCayleyCLM]
    calc
      ‖T f‖ = ‖diskBoundaryModelEmbedding B hBbd hB (T f)‖ :=
        (norm_diskBoundaryModelEmbedding B hBbd hB (T f)).symm
      _ = ‖Q (hardyDiskLineCayleyCLM f)‖ := congrArg norm hQf.symm
      _ ≤ ‖Q‖ * ‖hardyDiskLineCayleyCLM f‖ := Q.le_opNorm _
      _ = ‖Q‖ * ‖f‖ := by rw [norm_hardyDiskLineCayleyCLM]

theorem diskBoundaryInnerQuotientLeakage_rankAtLeast_iff
    (A B : DiskMultiplier) (hBbd : B.bd = 1)
    (hB : HardyMultiplierIsometry B) (r : ℕ) :
    UpperHardyBoundaryOperatorRankAtLeast
        (diskBoundaryInnerQuotientLeakage A B hBbd hB) r ↔
      RestrictedAdjointRankAtLeast
        (hardyMultiplierModelSpace B) (hardyMul A) r := by
  let K := hardyMultiplierModelSpace B
  let T : HardyDisk →L[ℂ] K := modelSpaceLeakageCore K (hardyMul A)
  have hfactor := diskBoundaryInnerQuotientLeakage_eq_modelEmbedding_comp
    A B hBbd hB
  have happly : ∀ u : UpperHardyL2,
      diskBoundaryInnerQuotientLeakage A B hBbd hB u =
        diskBoundaryModelEmbedding B hBbd hB
          (T (hardyLineDiskCayleyCLM u)) := by
    intro u
    have h := congrArg (fun S : UpperHardyL2 →L[ℂ] LowerHardyL2 => S u) hfactor
    simpa only [T, ContinuousLinearMap.comp_apply] using h
  have hrank : UpperHardyBoundaryOperatorRankAtLeast
      (diskBoundaryInnerQuotientLeakage A B hBbd hB) r ↔
      ContinuousLinearMapRankAtLeast T r := by
    constructor
    · rintro ⟨v, hv⟩
      refine ⟨fun i => hardyLineDiskCayleyCLM (v i), ?_⟩
      rw [Fintype.linearIndependent_iff] at hv ⊢
      intro c hc
      apply hv c
      calc
        ∑ i, c i • diskBoundaryInnerQuotientLeakage A B hBbd hB (v i) =
            ∑ i, c i • diskBoundaryModelEmbedding B hBbd hB
              (T (hardyLineDiskCayleyCLM (v i))) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [happly]
        _ = diskBoundaryModelEmbedding B hBbd hB
              (∑ i, c i • T (hardyLineDiskCayleyCLM (v i))) := by
          simp only [map_sum, map_smul]
        _ = 0 := by rw [hc, map_zero]
    · rintro ⟨v, hv⟩
      refine ⟨fun i => hardyDiskLineCayleyCLM (v i), ?_⟩
      rw [Fintype.linearIndependent_iff] at hv ⊢
      intro c hc
      apply hv c
      apply (diskBoundaryModelEmbeddingIsometry B hBbd hB).injective
      calc
        diskBoundaryModelEmbeddingIsometry B hBbd hB
            (∑ i, c i • T (v i)) =
          ∑ i, c i • diskBoundaryModelEmbedding B hBbd hB (T (v i)) := by
            simp only [map_sum, map_smul]
            rfl
        _ = ∑ i, c i • diskBoundaryInnerQuotientLeakage A B hBbd hB
            (hardyDiskLineCayleyCLM (v i)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [happly, hardyLineDiskCayleyCLM_apply_hardyDiskLineCayleyCLM]
        _ = 0 := hc
        _ = diskBoundaryModelEmbeddingIsometry B hBbd hB 0 := by rw [map_zero]
  rw [hrank, ← continuousLinearMapRankAtLeast_adjoint_iff T r]
  change (∃ v : Fin r → K, LinearIndependent ℂ (fun i => T.adjoint (v i))) ↔ _
  have hadj : ∀ y : K, T.adjoint y = (hardyMul A).adjoint (y : HardyDisk) := by
    intro y
    exact adjoint_modelSpaceLeakageCore_apply K (hardyMul A) y
  constructor <;> rintro ⟨v, hv⟩ <;> refine ⟨v, ?_⟩
  · simpa only [hadj] using hv
  · simpa only [hadj] using hv

theorem diskBoundaryInnerQuotientLeakage_rankAtLeast_iff_uncancelledQuotient
    (A B : DiskMultiplier) (hBbd : B.bd = 1)
    (hB : HardyMultiplierIsometry B) (r : ℕ) :
    UpperHardyBoundaryOperatorRankAtLeast
        (diskBoundaryInnerQuotientLeakage A B hBbd hB) r ↔
      HasIndependentDimensionAtLeast
        (RestrictedAdjointUncancelledQuotient
          (hardyMultiplierModelSpace B) (hardyMul A)) r := by
  rw [diskBoundaryInnerQuotientLeakage_rankAtLeast_iff A B hBbd hB r]
  exact restrictedAdjointRankAtLeast_iff_uncancelledQuotient
    (hardyMultiplierModelSpace B) (hardyMul A) r

end
end GaloisForLFunctions.HTGeometry
