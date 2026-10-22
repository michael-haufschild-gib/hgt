import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaSourceDifferentialGreen

/-!
# The theta divisor as a nonzero augmented boundary response

The existing augmented Green readout cancels the source Green defect, but its kernel is trivial
at every parameter. It therefore cannot replace the literal source pencil as a divisor-bearing
operator. This does not obstruct GTA's nonnormal source mechanism.

The positive survivor is exact: the source mean is injective on every literal pencil kernel.
Consequently each Xi zero has a unique source kernel vector with mean one, and its augmented
readout is an explicit boundary-only output. These statements preserve the zero set; they do not
assert algebraic multiplicity transport, transverse neutrality, or RH.
-/

open Complex MeasureTheory
open scoped ENNReal

namespace RHTower.HedenmalmThetaSource
noncomputable section
open HedenmalmQuantile HedenmalmHilbertSchmidt HedenmalmClosedWeightedDerivative
private abbrev H := Lp ℂ 2 unitIntervalMeasure

/-- A literal kernel vector with zero source mean vanishes. -/
theorem thetaSourceDifferential_kernel_mean_zero
    (z : ℂ) (k : thetaCentered)
    (hk : thetaSourceDifferentialRangeMap z k = 0)
    (hm : pinnedMean (thetaCenteredSourceInverse k) = 0) : k = 0 := by
  apply thetaShiftedRangeMap_injective z
  rw [map_zero, thetaShiftedRangeMap_apply]
  simpa only [thetaSourceDifferentialRangeMap_apply, hm, zero_smul, sub_zero] using hk

/-- The source mean distinguishes all vectors in each literal pencil kernel. -/
theorem thetaSourceDifferential_kernel_mean_injective
    (z : ℂ) (k l : thetaCentered)
    (hk : thetaSourceDifferentialRangeMap z k = 0)
    (hl : thetaSourceDifferentialRangeMap z l = 0)
    (hm : pinnedMean (thetaCenteredSourceInverse k) =
      pinnedMean (thetaCenteredSourceInverse l)) : k = l := by
  apply sub_eq_zero.mp
  apply thetaSourceDifferential_kernel_mean_zero z (k - l)
  · rw [map_sub, hk, hl, sub_self]
  · rw [map_sub, ← thetaPinnedMeanCLM_apply, map_sub,
      thetaPinnedMeanCLM_apply, thetaPinnedMeanCLM_apply, hm, sub_self]

/-- Every nonzero literal kernel vector has a nonzero source mean. -/
theorem thetaSourceDifferential_kernel_mean_ne_zero
    (z : ℂ) (k : thetaCentered)
    (hk : thetaSourceDifferentialRangeMap z k = 0) (hk0 : k ≠ 0) :
    pinnedMean (thetaCenteredSourceInverse k) ≠ 0 := by
  intro hm
  exact hk0 (thetaSourceDifferential_kernel_mean_zero z k hk hm)

/-- The Green-cancelling augmented readout has trivial kernel at every parameter. -/
theorem thetaSourceDifferentialBoundaryAugmentedReadout_zero_iff
    (z : ℂ) (k : thetaCentered) :
    thetaSourceDifferentialBoundaryAugmentedReadout z
      (thetaSourceDifferentialBoundaryCoordinateElement z k) = 0 ↔ k = 0 := by
  constructor
  · intro h
    have henergy := congrArg Prod.fst h
    have hk : thetaSourceDifferentialRangeMap z k = 0 := by
      apply thetaMetricRoot_injective
      simpa only [thetaSourceDifferentialBoundaryAugmentedReadout,
        thetaSourceDifferentialBoundaryEnergyReadout_apply, Prod.fst_zero, map_zero] using henergy
    by_cases hz : z = 0
    · apply Subtype.ext
      simpa [thetaSourceDifferentialRangeMap_apply, hz] using hk
    · have hport := congrArg (fun x : H × (ℂ × ℂ) => x.2.1) h
      have hm : (Complex.I / 2 * z) * pinnedMean (thetaCenteredSourceInverse k) = 0 := by
        simpa only [thetaSourceDifferentialBoundaryAugmentedReadout,
          thetaSourceDifferentialBoundaryPort_apply, Prod.smul_fst, smul_eq_mul,
          Prod.snd_zero, Prod.fst_zero] using hport
      have hc : Complex.I / 2 * z ≠ 0 :=
        mul_ne_zero (div_ne_zero Complex.I_ne_zero (by norm_num)) hz
      exact thetaSourceDifferential_kernel_mean_zero z k hk
        ((mul_eq_zero.mp hm).resolve_left hc)
  · rintro rfl
    simp [thetaSourceDifferentialBoundaryAugmentedReadout,
      thetaSourceDifferentialBoundaryEnergyReadout_apply,
      thetaSourceDifferentialBoundaryPort_apply, ← thetaPinnedMeanCLM_apply]

theorem XiC_eq_zero_iff_unique_normalized_source_kernel (z : ℂ) :
    XiC z = 0 ↔ ∃! k : thetaCentered,
      thetaSourceDifferentialRangeMap z k = 0 ∧
        pinnedMean (thetaCenteredSourceInverse k) = 1 := by
  rw [XiC_eq_zero_iff_thetaSourceDifferentialBoundaryRelation_nonzero_vertical,
    thetaSourceDifferentialBoundaryRelation_nonzero_vertical_iff]
  constructor
  · rintro ⟨k, hk, hSk⟩
    have hk0 : k ≠ 0 := by
      intro h
      exact hSk (by rw [h, map_zero])
    have hm := thetaSourceDifferential_kernel_mean_ne_zero z k hk hk0
    let l := (pinnedMean (thetaCenteredSourceInverse k))⁻¹ • k
    have hl : thetaSourceDifferentialRangeMap z l = 0 := by
      simp [l, hk]
    have hml : pinnedMean (thetaCenteredSourceInverse l) = 1 := by
      simp only [l, map_smul, pinnedMean_smul]
      exact inv_mul_cancel₀ hm
    refine ⟨l, ⟨hl, hml⟩, ?_⟩
    intro y hy
    exact thetaSourceDifferential_kernel_mean_injective z y l hy.1 hl
      (hy.2.trans hml.symm)
  · rintro ⟨k, hk, _⟩
    refine ⟨k, hk.1, ?_⟩
    intro hzero
    have hm := hk.2
    rw [hzero, ← thetaPinnedMeanCLM_apply, map_zero] at hm
    exact zero_ne_one hm

/-- A normalized divisor response survives as an explicit boundary-only augmented output. -/
theorem thetaSourceDifferentialBoundaryAugmentedReadout_normalized_kernel
    (z : ℂ) (k : thetaCentered)
    (hk : thetaSourceDifferentialRangeMap z k = 0)
    (hm : pinnedMean (thetaCenteredSourceInverse k) = 1) :
    thetaSourceDifferentialBoundaryAugmentedReadout z
      (thetaSourceDifferentialBoundaryCoordinateElement z k) =
        (0, (Complex.I / 2 * z, Complex.I / 2 * z * thetaCenteredDipoleTrace k)) := by
  simp [thetaSourceDifferentialBoundaryAugmentedReadout,
    thetaSourceDifferentialBoundaryEnergyReadout_apply,
    thetaSourceDifferentialBoundaryPort_apply, hk, hm, smul_eq_mul]

end
end RHTower.HedenmalmThetaSource
