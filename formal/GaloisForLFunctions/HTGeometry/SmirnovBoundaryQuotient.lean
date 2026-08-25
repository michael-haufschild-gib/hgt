import GaloisForLFunctions.HTGeometry.DiskMultiplierLineBoundary
import GaloisForLFunctions.HTGeometry.HardyBoundaryCayleyIdentification

open Complex MeasureTheory Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Operator-theoretic outer bounded multiplier: its Hardy vector is cyclic for the shift. -/
def IsOuterDiskMultiplier (φ : DiskMultiplier) : Prop :=
  cyclicSubspace (hardyOf φ) = ⊤

private def polynomialHardyCore : Type := polyMultiples hardyOne

private def polynomialCoreMul (φ : DiskMultiplier) : polynomialHardyCore → HardyDisk :=
  fun f => hardyMul φ f.1

private theorem denseRange_polynomialHardyCore_val :
    DenseRange (fun f : polynomialHardyCore => (f.1 : HardyDisk)) := by
  rw [denseRange_iff_closure_range]
  have hrange : Set.range (fun f : polynomialHardyCore => (f.1 : HardyDisk)) =
      ((polyMultiples hardyOne : Submodule ℂ HardyDisk) : Set HardyDisk) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hclosure : closure ((polyMultiples hardyOne : Submodule ℂ HardyDisk) : Set HardyDisk) =
      Set.univ := by
    have h := congrArg (fun V : Submodule ℂ HardyDisk => (V : Set HardyDisk))
      cyclicSubspace_hardyOne
    simpa [cyclicSubspace, Submodule.topologicalClosure_coe] using h
  rw [hrange]
  exact hclosure

theorem isOuterDiskMultiplier_iff_denseRange (φ : DiskMultiplier) :
    IsOuterDiskMultiplier φ ↔ DenseRange (hardyMul φ) := by
  have hrangeCore : Set.range (polynomialCoreMul φ) =
      (((polyMultiples hardyOne).map
        ((hardyMul φ : HardyDisk →L[ℂ] HardyDisk) : HardyDisk →ₗ[ℂ] HardyDisk) :
          Submodule ℂ HardyDisk) : Set HardyDisk) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hcore_iff : IsOuterDiskMultiplier φ ↔ DenseRange (polynomialCoreMul φ) := by
    rw [IsOuterDiskMultiplier, hardyOf, cyclicSubspace, polyMultiples_map]
    rw [denseRange_iff_closure_range, hrangeCore]
    constructor <;> intro h
    · have hc := congrArg (fun V : Submodule ℂ HardyDisk => (V : Set HardyDisk)) h
      simpa [Submodule.topologicalClosure_coe] using hc
    · apply SetLike.coe_injective
      simpa [Submodule.topologicalClosure_coe] using h
  constructor
  · intro houter
    have hcore := hcore_iff.mp houter
    rw [denseRange_iff_closure_range] at hcore ⊢
    apply Set.Subset.antisymm (Set.subset_univ _)
    rw [← hcore]
    apply closure_mono
    intro y hy
    obtain ⟨x, rfl⟩ := hy
    exact ⟨x.1, rfl⟩
  · intro hdense
    apply hcore_iff.mpr
    exact hdense.comp denseRange_polynomialHardyCore_val (hardyMul φ).continuous

theorem IsOuterDiskMultiplier.mul {φ ψ : DiskMultiplier}
    (hφ : IsOuterDiskMultiplier φ) (hψ : IsOuterDiskMultiplier ψ) :
    IsOuterDiskMultiplier (φ.mul ψ) := by
  rw [isOuterDiskMultiplier_iff_denseRange] at hφ hψ ⊢
  have hcomp := hφ.comp hψ (hardyMul φ).continuous
  have hfun : (hardyMul (φ.mul ψ) : HardyDisk → HardyDisk) =
      (hardyMul φ : HardyDisk → HardyDisk) ∘
        (hardyMul ψ : HardyDisk → HardyDisk) := by
    funext f
    exact (hardyMul_mul φ ψ f).symm
  rw [hfun]
  exact hcomp

@[simp] theorem polyMultiples_zero : polyMultiples (0 : HardyDisk) = ⊥ := by
  rw [polyMultiples]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨n, rfl⟩
    simp
  · exact bot_le

@[simp] theorem cyclicSubspace_zero : cyclicSubspace (0 : HardyDisk) = ⊥ := by
  rw [cyclicSubspace, polyMultiples_zero]
  apply SetLike.coe_injective
  rw [Submodule.topologicalClosure_coe]
  simp

theorem IsOuterDiskMultiplier.exists_nonzero
    {φ : DiskMultiplier} (hφ : IsOuterDiskMultiplier φ) :
    ∃ z ∈ Metric.ball (0 : ℂ) 1, φ.fn z ≠ 0 := by
  by_contra h
  push Not at h
  have hzero : hardyOf φ = 0 := by
    refine hardyDisk_ext fun z hz => ?_
    rw [hardyFun_hardyOf φ hz, h z (by simpa [Metric.mem_ball, dist_zero_right] using hz)]
    have : hardyFun (0 : HardyDisk) z = 0 := by
      rw [hardyFun]
      simp
    exact this.symm
  rw [IsOuterDiskMultiplier, hzero, cyclicSubspace_zero] at hφ
  exact (show (⊥ : Submodule ℂ HardyDisk) ≠ ⊤ by
    intro hbot
    have hone : hardyOne = 0 := by
      apply Subtype.ext
      have := congrArg (fun V : Submodule ℂ HardyDisk => hardyOne ∈ V) hbot
      simpa using this
    have hcoord := congrArg (fun f : HardyDisk => f 0) hone
    norm_num [hardyOne, lp.single_apply] at hcoord) hφ

/-- Exact Smirnov-class boundary datum: a quotient of bounded analytic functions by a cyclic
(outer) bounded denominator. -/
structure DiskSmirnovBoundary where
  numerator : DiskMultiplier
  denominator : DiskMultiplier
  denominator_outer : IsOuterDiskMultiplier denominator

/-- Measurable real-line boundary representative of a Smirnov quotient. -/
def DiskSmirnovBoundary.boundary (F : DiskSmirnovBoundary) (x : ℝ) : ℂ :=
  diskMultiplierLineBoundary F.numerator x /
    diskMultiplierLineBoundary F.denominator x

theorem DiskSmirnovBoundary.measurable_boundary (F : DiskSmirnovBoundary) :
    Measurable F.boundary :=
  (measurable_diskMultiplierLineBoundary F.numerator).div
    (measurable_diskMultiplierLineBoundary F.denominator)

theorem DiskSmirnovBoundary.denominator_ne_zero_ae (F : DiskSmirnovBoundary) :
    ∀ᵐ x ∂volume, diskMultiplierLineBoundary F.denominator x ≠ 0 :=
  diskMultiplierLineBoundary_ne_zero_ae F.denominator
    F.denominator_outer.exists_nonzero

theorem isOuterDiskMultiplier_one :
    IsOuterDiskMultiplier DiskMultiplier.one :=
  cyclicSubspace_hardyOf_eq_top (φ := DiskMultiplier.one)
    (ψ := DiskMultiplier.one) (fun _ _ => by simp [DiskMultiplier.one])

theorem diskMultiplierLineBoundary_one_ae :
    diskMultiplierLineBoundary DiskMultiplier.one =ᵐ[volume] fun _ => 1 := by
  have hcircle : diskMultiplierBoundaryFun DiskMultiplier.one =ᵐ[circleLebesgue]
      fun _ => 1 := by
    have hhardy : hardyOf DiskMultiplier.one = hardyOne := by
      rw [hardyOf, hardyMul_one]
    rw [diskMultiplierBoundaryFun, hhardy, hardyOne, hardyDiskBoundary_single]
    filter_upwards [circleMonomialLp_coeFn_ae circleLebesgue 0] with z hz
    simpa using hz
  have hweighted := hcircle.comp_tendsto
    circleCayley_weighted_measurePreserving.quasiMeasurePreserving.tendsto_ae
  have hvolume := (withDensity_realDensity_ae_eq measurable_standardCauchyWeight
    standardCauchyWeight_pos).mp hweighted
  filter_upwards [diskMultiplierLineBoundary_ae DiskMultiplier.one, hvolume]
      with x hrep hone
  rw [hrep]
  simpa [Function.comp_apply] using hone

/-- Every bounded analytic multiplier embeds in the exact Smirnov boundary algebra. -/
def DiskSmirnovBoundary.ofMultiplier (φ : DiskMultiplier) : DiskSmirnovBoundary where
  numerator := φ
  denominator := DiskMultiplier.one
  denominator_outer := isOuterDiskMultiplier_one

theorem DiskSmirnovBoundary.boundary_ofMultiplier_ae (φ : DiskMultiplier) :
    (DiskSmirnovBoundary.ofMultiplier φ).boundary =ᵐ[volume]
      diskMultiplierLineBoundary φ := by
  filter_upwards [diskMultiplierLineBoundary_one_ae] with x hx
  rw [DiskSmirnovBoundary.boundary, DiskSmirnovBoundary.ofMultiplier, hx, div_one]

/-- Product in the exact Smirnov boundary algebra. -/
def DiskSmirnovBoundary.mul (F G : DiskSmirnovBoundary) : DiskSmirnovBoundary where
  numerator := F.numerator.mul G.numerator
  denominator := F.denominator.mul G.denominator
  denominator_outer := F.denominator_outer.mul G.denominator_outer

theorem DiskSmirnovBoundary.boundary_mul_ae (F G : DiskSmirnovBoundary) :
    (F.mul G).boundary =ᵐ[volume] fun x => F.boundary x * G.boundary x := by
  filter_upwards [diskMultiplierLineBoundary_mul_ae F.numerator G.numerator,
    diskMultiplierLineBoundary_mul_ae F.denominator G.denominator,
    F.denominator_ne_zero_ae, G.denominator_ne_zero_ae] with x hnum hden hF hG
  rw [DiskSmirnovBoundary.boundary, DiskSmirnovBoundary.boundary,
    DiskSmirnovBoundary.boundary]
  change diskMultiplierLineBoundary (F.numerator.mul G.numerator) x /
      diskMultiplierLineBoundary (F.denominator.mul G.denominator) x = _
  rw [hnum, hden]
  field_simp

end

end GaloisForLFunctions.HTGeometry
