import GaloisForLFunctions.RHTower.HedenmalmThetaComplexResolventRow

/-!
# Closed source-faithful theta differential pencil

Centering the compact theta source inverse produces the closed weighted derivative, but every
nonzero source eigenmode has a nonzero mean.  The rank-one mean correction in this file restores
that scalar mode.  Its resulting closed unbounded pencil has exactly the literal source-pencil
kernels, hence exactly the completed Xi zero divisor.
-/

open Complex Function MeasureTheory Set Filter Topology Module
open scoped ENNReal

namespace RHTower.HedenmalmThetaSource

noncomputable section

open HedenmalmQuantile HedenmalmHilbertSchmidt HedenmalmClosedWeightedDerivative
  HedenmalmFredholmRange GaloisForLFunctions.HTGeometry

private abbrev H := Lp ℂ 2 unitIntervalMeasure

local instance factTwoNeTopThetaSourceDifferentialPencil : Fact ((2 : ENNReal) ≠ ⊤) :=
  ⟨by norm_num⟩

local instance thetaSourceDifferentialPencilComplete : CompleteSpace thetaCentered :=
  thetaCentered_isClosed.completeSpace_coe

/-- The source graph coordinate corrected by its unavoidable scalar monopole. -/
def thetaSourceDifferentialRangeMap (z : ℂ) : thetaCentered →L[ℂ] H :=
  thetaShiftedRangeMap z -
    z • ((thetaPinnedMeanCLM.comp thetaCenteredSourceInverse).smulRight pinnedOne)

theorem thetaSourceDifferentialRangeMap_apply (z : ℂ) (k : thetaCentered) :
    thetaSourceDifferentialRangeMap z k =
      (k : H) + z • (thetaCenteredSourceInverse k -
        pinnedMean (thetaCenteredSourceInverse k) • pinnedOne) := by
  simp [thetaSourceDifferentialRangeMap, thetaShiftedRangeMap_apply,
    thetaPinnedMeanCLM_apply]
  module

/-- Closed unbounded source pencil retaining the scalar mode discarded by centering. -/
def thetaSourceDifferentialPencil (z : ℂ) : H →ₗ.[ℂ] H :=
  closedGraphTransform thetaCentered thetaCenteredSourceInverse
    (thetaSourceDifferentialRangeMap z)

theorem thetaSourceDifferentialPencil_apply_B (z : ℂ) (k : thetaCentered) :
    thetaCenteredSourceInverse k ∈ (thetaSourceDifferentialPencil z).domain ∧
      thetaSourceDifferentialPencil z
        ⟨thetaCenteredSourceInverse k,
          (closedGraphTransform_apply_B thetaCentered thetaCenteredSourceInverse
            (thetaSourceDifferentialRangeMap z)
              thetaCenteredSourceInverse_injective k).1⟩ =
        thetaSourceDifferentialRangeMap z k :=
  closedGraphTransform_apply_B thetaCentered thetaCenteredSourceInverse
    (thetaSourceDifferentialRangeMap z) thetaCenteredSourceInverse_injective k

/-- The repaired closed pencil has precisely the literal bounded source-pencil kernel. -/
theorem thetaSourcePencil_apply_eq_zero_iff_exists_differential_kernel (z : ℂ) (f : H) :
    thetaSourcePencil z f = 0 ↔
      ∃ hf : f ∈ (thetaSourceDifferentialPencil z).domain,
        thetaSourceDifferentialPencil z ⟨f, hf⟩ = 0 := by
  constructor
  · intro hsource
    have hsource' : f + z • thetaKernelOperator f = 0 := by
      simpa [thetaSourcePencil] using hsource
    let m : ℂ := pinnedMean f
    let k0 : thetaCentered := ⟨f - m • pinnedOne, by
      rw [mem_thetaCentered_iff]
      calc
        pinnedMean (f - m • pinnedOne) =
            thetaPinnedMeanCLM (f - m • pinnedOne) :=
          (thetaPinnedMeanCLM_apply _).symm
        _ = 0 := by
          rw [map_sub, map_smul, thetaPinnedMeanCLM_apply,
            thetaPinnedMeanCLM_apply, pinnedMean_pinnedOne]
          simp [m, smul_eq_mul]⟩
    let k : thetaCentered := (-z) • k0
    have hB0 : thetaCenteredSourceInverse k0 = thetaKernelOperator f := by
      rw [thetaCenteredSourceInverse, ContinuousLinearMap.comp_apply]
      change thetaCompactSourceInverse (f - m • pinnedOne) = thetaKernelOperator f
      rw [map_sub, map_smul, ← thetaKernelOperator_eq_thetaCompactSourceInverse,
        thetaKernelOperator_pinnedOne, smul_zero, sub_zero]
    have hzf : z • thetaKernelOperator f = -f :=
      eq_neg_of_add_eq_zero_right hsource'
    have hBk : thetaCenteredSourceInverse k = f := by
      change thetaCenteredSourceInverse ((-z) • k0) = f
      rw [map_smul, hB0, neg_smul, hzf, neg_neg]
    have hJk : thetaSourceDifferentialRangeMap z k = 0 := by
      rw [thetaSourceDifferentialRangeMap_apply, hBk]
      change (-z) • (f - m • pinnedOne) + z •
        (f - pinnedMean f • pinnedOne) = 0
      dsimp only [m]
      module
    refine ⟨?_, ?_⟩
    · rw [← hBk]
      exact (thetaSourceDifferentialPencil_apply_B z k).1
    · simpa only [hBk] using (thetaSourceDifferentialPencil_apply_B z k).2.trans hJk
  · rintro ⟨hfdom, hdiff⟩
    have hfrange : f ∈ thetaCenteredSourceInverse.range := by
      simpa only [thetaSourceDifferentialPencil, closedGraphTransform_domain] using hfdom
    rcases hfrange with ⟨k, hk⟩
    have hdomk : thetaCenteredSourceInverse k ∈ (thetaSourceDifferentialPencil z).domain :=
      (thetaSourceDifferentialPencil_apply_B z k).1
    have heq : (⟨f, hfdom⟩ : (thetaSourceDifferentialPencil z).domain) =
        ⟨thetaCenteredSourceInverse k, hdomk⟩ := Subtype.ext hk.symm
    have hJk : thetaSourceDifferentialRangeMap z k = 0 := by
      rw [← (thetaSourceDifferentialPencil_apply_B z k).2]
      rw [← heq]
      exact hdiff
    have hsource' := congrArg thetaKernelOperator hJk
    rw [thetaSourceDifferentialRangeMap_apply, map_add, map_smul, map_sub,
      map_smul, thetaKernelOperator_pinnedOne, smul_zero, sub_zero] at hsource'
    have hBkin : thetaKernelOperator (k : H) = f := by
      rw [← hk]
      change thetaKernelOperator (k : H) = thetaCompactSourceInverse (k : H)
      rw [thetaKernelOperator_eq_thetaCompactSourceInverse]
    have hKB : thetaKernelOperator (thetaCenteredSourceInverse k) =
        thetaKernelOperator f := congrArg thetaKernelOperator hk
    rw [hBkin, hKB] at hsource'
    simpa [thetaSourcePencil] using hsource'

theorem thetaSourceDifferentialGraphMap_antilipschitz (z : ℂ) :
    ∃ c : NNReal, AntilipschitzWith c
      (thetaCenteredSourceInverse.prod (thetaSourceDifferentialRangeMap z)) := by
  let c : NNReal := ⟨1 + ‖z‖ * (1 + ‖pinnedOne‖), by positivity⟩
  refine ⟨c, (thetaCenteredSourceInverse.prod
    (thetaSourceDifferentialRangeMap z)).antilipschitz_of_bound ?_⟩
  intro k
  have hdecomp : (k : H) = thetaSourceDifferentialRangeMap z k -
      z • (thetaCenteredSourceInverse k -
        pinnedMean (thetaCenteredSourceInverse k) • pinnedOne) := by
    rw [thetaSourceDifferentialRangeMap_apply]
    module
  calc
    ‖k‖ = ‖thetaSourceDifferentialRangeMap z k - z •
        (thetaCenteredSourceInverse k -
          pinnedMean (thetaCenteredSourceInverse k) • pinnedOne)‖ := by
      rw [← hdecomp]
      rfl
    _ ≤ ‖thetaSourceDifferentialRangeMap z k‖ + ‖z •
        (thetaCenteredSourceInverse k -
          pinnedMean (thetaCenteredSourceInverse k) • pinnedOne)‖ :=
      norm_sub_le _ _
    _ = ‖thetaSourceDifferentialRangeMap z k‖ + ‖z‖ *
        ‖thetaCenteredSourceInverse k -
          pinnedMean (thetaCenteredSourceInverse k) • pinnedOne‖ := by
      rw [norm_smul]
    _ ≤ ‖thetaSourceDifferentialRangeMap z k‖ + ‖z‖ *
        (‖thetaCenteredSourceInverse k‖ +
          ‖pinnedMean (thetaCenteredSourceInverse k) • pinnedOne‖) := by
      gcongr
      exact norm_sub_le _ _
    _ = ‖thetaSourceDifferentialRangeMap z k‖ + ‖z‖ *
        (‖thetaCenteredSourceInverse k‖ +
          ‖pinnedMean (thetaCenteredSourceInverse k)‖ * ‖pinnedOne‖) := by
      rw [norm_smul]
    _ ≤ ‖thetaSourceDifferentialRangeMap z k‖ + ‖z‖ *
        (‖thetaCenteredSourceInverse k‖ +
          ‖thetaCenteredSourceInverse k‖ * ‖pinnedOne‖) := by
      gcongr
      exact norm_pinnedMean_le _
    _ = ‖thetaSourceDifferentialRangeMap z k‖ +
        (‖z‖ * (1 + ‖pinnedOne‖)) * ‖thetaCenteredSourceInverse k‖ := by
      ring
    _ ≤ ‖(thetaCenteredSourceInverse.prod (thetaSourceDifferentialRangeMap z)) k‖ +
        (‖z‖ * (1 + ‖pinnedOne‖)) *
          ‖(thetaCenteredSourceInverse.prod (thetaSourceDifferentialRangeMap z)) k‖ := by
      gcongr
      · exact norm_snd_le
          ((thetaCenteredSourceInverse.prod (thetaSourceDifferentialRangeMap z)) k)
      · exact norm_fst_le
          ((thetaCenteredSourceInverse.prod (thetaSourceDifferentialRangeMap z)) k)
    _ = (c : ℝ) *
        ‖(thetaCenteredSourceInverse.prod (thetaSourceDifferentialRangeMap z)) k‖ := by
      change _ = (1 + ‖z‖ * (1 + ‖pinnedOne‖)) *
        ‖(thetaCenteredSourceInverse.prod (thetaSourceDifferentialRangeMap z)) k‖
      ring

theorem thetaSourceDifferentialPencil_isClosed (z : ℂ) :
    (thetaSourceDifferentialPencil z).IsClosed := by
  rcases thetaSourceDifferentialGraphMap_antilipschitz z with ⟨c, hc⟩
  exact closedGraphTransform_isClosed thetaCentered thetaCenteredSourceInverse
    (thetaSourceDifferentialRangeMap z) thetaCenteredSourceInverse_injective hc

/-- The closed differential pencil has exactly the literal completed-Xi zero divisor. -/
theorem XiC_eq_zero_iff_exists_thetaSourceDifferentialPencil_kernel (z : ℂ) :
    XiC z = 0 ↔ ∃ f : H, f ≠ 0 ∧
      ∃ hf : f ∈ (thetaSourceDifferentialPencil z).domain,
        thetaSourceDifferentialPencil z ⟨f, hf⟩ = 0 := by
  constructor
  · intro hXi
    have hz : z ≠ 0 := fun hz => XiC_zero_ne (hz ▸ hXi)
    obtain ⟨_, f, hf0, hf⟩ :=
      (XiC_eq_zero_iff_sourcePencil_not_isUnit_iff_eigenvector z).mp hXi
    have hsource : thetaSourcePencil z f = 0 := by
      rw [thetaSourcePencil, add_apply, one_apply_eq_self, smul_apply, hf, smul_smul]
      field_simp [hz]
      simp
    obtain ⟨hfdom, hdiff⟩ :=
      (thetaSourcePencil_apply_eq_zero_iff_exists_differential_kernel z f).mp hsource
    exact ⟨f, hf0, hfdom, hdiff⟩
  · rintro ⟨f, hf0, hfdom, hdiff⟩
    have hsource : thetaSourcePencil z f = 0 :=
      (thetaSourcePencil_apply_eq_zero_iff_exists_differential_kernel z f).mpr ⟨hfdom, hdiff⟩
    apply (thetaSourcePencil_not_isUnit_iff_XiC_eq_zero z).mp
    intro hunit
    apply hf0
    exact (ContinuousLinearMap.isUnit_iff_bijective.mp hunit).1 (by simpa using hsource)

end

end RHTower.HedenmalmThetaSource
