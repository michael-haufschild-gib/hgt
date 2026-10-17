import GaloisForLFunctions.BiScaleUncertainty.CoprimeAlternatingProjectionRate

/-!
# Concrete data for two infinite divisor grids

Shared nodes are assigned to the first grid. A closed kernel of the common-range
projection encodes the remaining second-grid data without duplicate values.
-/

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear

/-- Continuous synthesis with unnormalized, prescribed nodal values. -/
def coprimeExtensionL (d : ℕ) : TraceData →L[ℝ] Velocity :=
  Real.sqrt 2 • (tentSynthesis d).toContinuousLinearMap

@[simp]
theorem coprimeExtensionL_apply (d : ℕ) (a : TraceData) :
    coprimeExtensionL d a = coprimeExtension d a := by
  simp [coprimeExtensionL, coprimeExtension]

@[simp]
theorem coprimeCoefficients_extension (d : ℕ) (a : TraceData) :
    coprimeCoefficients d (coprimeExtension d a) = a := by
  simp [coprimeCoefficients, coprimeExtension, tentAnalysis_tentSynthesis, smul_smul]

theorem norm_sq_coprimeExtension (d : ℕ) (a : TraceData) :
    ‖coprimeExtension d a‖ ^ 2 = 2 * ‖a‖ ^ 2 := by
  rw [norm_sq_velocity, coprimeExtension_energy, norm_sq_traceData]

theorem coprimeCoefficients_lcm_extension (d e j : ℕ) (b : TraceData) :
    coprimeCoefficients e (coprimeProjector (coprimeLcm d e)
        (coprimeExtension e b)) j =
      if d + 2 ∣ coprimeCenter e j then b j else 0 := by
  have h := (coprimeProjector (coprimeLcm d e)).adjoint_inner_right
    (tentVelocity e j) (coprimeExtension e b)
  rw [coprimeProjector_adjoint, coprimeLcmProjector_tent] at h
  rw [coprimeCoefficients_apply, ← inner_tentVelocity_velocity, h]
  split_ifs with hj
  · have hc := congrArg (fun a : TraceData => a j) (coprimeCoefficients_extension e b)
    simpa only [coprimeCoefficients_apply, ← inner_tentVelocity_velocity] using hc
  · simp

/-- The second component has no common-range part. -/
def twoGridDataSpace (d e : ℕ) : Submodule ℝ (TraceData × TraceData) :=
  (((coprimeProjector (coprimeLcm d e)).comp (coprimeExtensionL e)).comp
    (ContinuousLinearMap.snd ℝ TraceData TraceData)).ker

abbrev TwoGridData (d e : ℕ) := twoGridDataSpace d e

theorem twoGridData_common_zero (d e : ℕ) (v : TwoGridData d e) :
    coprimeProjector (coprimeLcm d e) (coprimeExtension e v.1.2) = 0 := by
  have h := v.2
  change coprimeProjector (coprimeLcm d e) (coprimeExtensionL e v.1.2) = 0 at h
  rwa [coprimeExtensionL_apply] at h

theorem mem_twoGridDataSpace_iff (d e : ℕ) (a b : TraceData) :
    (a, b) ∈ twoGridDataSpace d e ↔
      ∀ j, d + 2 ∣ coprimeCenter e j → b j = 0 := by
  change coprimeProjector (coprimeLcm d e) (coprimeExtensionL e b) = 0 ↔ _
  rw [coprimeExtensionL_apply]
  constructor
  · intro h j hj
    have hc := coprimeCoefficients_lcm_extension d e j b
    rw [h, if_pos hj] at hc
    simpa [coprimeCoefficients] using hc.symm
  · intro h
    apply ((coprimeProjector (coprimeLcm d e)).hasSum
      (hasSum_coprimeExtension e b)).unique
    convert hasSum_zero (β := ℕ) (α := Velocity) using 1
    funext j
    simp only [map_smul, coprimeLcmProjector_tent]
    by_cases hj : d + 2 ∣ coprimeCenter e j
    · simp [hj, h j hj]
    · simp [hj]

instance twoGridData_completeSpace (d e : ℕ) : CompleteSpace (TwoGridData d e) :=
  (ContinuousLinearMap.isClosed_ker _).completeSpace_coe

/-- Canonical deletion of duplicate values from the second grid. -/
def twoGridEraseCommon (d e : ℕ) (b : TraceData) : TraceData :=
  b - coprimeCoefficients e (coprimeProjector (coprimeLcm d e) (coprimeExtension e b))

theorem twoGridEraseCommon_apply (d e j : ℕ) (b : TraceData) :
    twoGridEraseCommon d e b j = if d + 2 ∣ coprimeCenter e j then 0 else b j := by
  simp only [twoGridEraseCommon, lp.coeFn_sub, Pi.sub_apply,
    coprimeCoefficients_lcm_extension]
  split_ifs <;> simp

/-- Arbitrary square-summable pair data determine a unique shared-node convention. -/
def twoGridData (d e : ℕ) (a b : TraceData) : TwoGridData d e :=
  ⟨(a, twoGridEraseCommon d e b),
    (mem_twoGridDataSpace_iff d e a _).2 (fun j hj => by
      simp [twoGridEraseCommon_apply, hj])⟩

/-- Sum of the two genuinely convergent tent series. -/
def twoGridExtension (d e : ℕ) : TwoGridData d e →L[ℝ] Velocity :=
  ((coprimeExtensionL d).coprod (coprimeExtensionL e)).comp (twoGridDataSpace d e).subtypeL

@[simp]
theorem twoGridExtension_apply (d e : ℕ) (v : TwoGridData d e) :
    twoGridExtension d e v = coprimeExtension d v.1.1 + coprimeExtension e v.1.2 := by
  simp [twoGridExtension]

/-- Squared union nodal norm, with common nodes counted once. -/
def twoGridMass (d e : ℕ) (v : TwoGridData d e) : ℝ := ‖v.1.1‖ ^ 2 + ‖v.1.2‖ ^ 2

theorem twoGridMass_eq_tsum (d e : ℕ) (v : TwoGridData d e) :
    twoGridMass d e v = (∑' j, (v.1.1 j)^2) + ∑' j, (v.1.2 j)^2 := by
  simp only [twoGridMass, norm_sq_traceData]

theorem twoGridMass_nonneg (d e : ℕ) (v : TwoGridData d e) : 0 ≤ twoGridMass d e v :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem primitive_twoGrid_second_at_first (d e j : ℕ) (v : TwoGridData d e) :
    primitive (coprimeExtension e v.1.2) (coprimeCenter d j) = 0 := by
  rw [primitive_coprimeExtension_nat]
  split_ifs with h
  · apply (mem_twoGridDataSpace_iff d e v.1.1 v.1.2).1 v.2
    rw [coprimeCenter_index h.1 h.2]
    exact coprimeCenter_dvd d j
  · rfl

/-- Every integer trace, including off-union zeros and the common nodes. -/
theorem primitive_twoGridExtension (d e k : ℕ) (v : TwoGridData d e) :
    primitive (twoGridExtension d e v) k =
      (if 0 < k ∧ d + 2 ∣ k then v.1.1 (k / (d + 2) - 1) else 0) +
      (if 0 < k ∧ e + 2 ∣ k then v.1.2 (k / (e + 2) - 1) else 0) := by
  rw [← inner_prefixCell, twoGridExtension_apply, inner_add_right,
    inner_prefixCell, inner_prefixCell, primitive_coprimeExtension_nat,
    primitive_coprimeExtension_nat]

theorem primitive_twoGridExtension_first (d e j : ℕ) (v : TwoGridData d e) :
    primitive (twoGridExtension d e v) (coprimeCenter d j) = v.1.1 j := by
  rw [← inner_prefixCell, twoGridExtension_apply, inner_add_right,
    inner_prefixCell, inner_prefixCell, primitive_coprimeExtension_active,
    primitive_twoGrid_second_at_first, add_zero]

theorem log_twoGridExtension (d e k : ℕ) (v : TwoGridData d e) :
    logPrimitive (twoGridExtension d e v) (Real.log (k + 1)) =
      primitive (twoGridExtension d e v) (k + 1) := by
  rw [logPrimitive, Real.exp_log (by positivity : (0 : ℝ) < k + 1)]

theorem hasSum_extension_curvature (d : ℕ) (a : TraceData) (q : Velocity) :
    HasSum (fun j => a j * traceCurvature q d j) ⟪coprimeExtension d a, q⟫ := by
  have h := (innerSL ℝ q).hasSum (hasSum_coprimeExtension d a)
  simp only [innerSL_apply_apply, real_inner_smul_right] at h
  have hfun (j : ℕ) : a j * ⟪q, tentVelocity d j⟫ = a j * traceCurvature q d j := by
    congr 1
    exact (real_inner_comm _ _).trans (inner_tentVelocity_velocity d j q)
  have hnew := h.congr_fun (fun j => (hfun j).symm)
  have hlimit : ⟪q, coprimeExtension d a⟫ = ⟪coprimeExtension d a, q⟫ :=
    real_inner_comm (coprimeExtension d a) q
  rwa [hlimit] at hnew

/-- Each cross-family adjacent pair occurs once in this absolutely convergent series. -/
def twoGridAdjacentTerm (d e : ℕ) (v : TwoGridData d e) (j : ℕ) : ℝ :=
  v.1.1 j * (primitive (coprimeExtension e v.1.2) ((coprimeCenter d j : ℝ) - 1) +
    primitive (coprimeExtension e v.1.2) ((coprimeCenter d j : ℝ) + 1))

theorem hasSum_twoGridAdjacentTerm (d e : ℕ) (v : TwoGridData d e) :
    HasSum (twoGridAdjacentTerm d e v)
      (-⟪coprimeExtension d v.1.1, coprimeExtension e v.1.2⟫) := by
  apply (hasSum_extension_curvature d v.1.1 (coprimeExtension e v.1.2)).neg.congr_fun
  intro j
  simp only [twoGridAdjacentTerm, traceCurvature, primitive_twoGrid_second_at_first]
  ring

/-- Exact infinite joint energy, retaining the signed adjacent-node interaction. -/
theorem twoGridExtension_energy (d e : ℕ) (v : TwoGridData d e) :
    ‖twoGridExtension d e v‖ ^ 2 =
      2 * twoGridMass d e v - 2 * ∑' j, twoGridAdjacentTerm d e v j := by
  rw [(hasSum_twoGridAdjacentTerm d e v).tsum_eq, twoGridExtension_apply,
    norm_add_sq_real, norm_sq_coprimeExtension, norm_sq_coprimeExtension, twoGridMass]
  ring

/-- The adjacent energy reads only the two neighboring second-grid nodal values. -/
theorem twoGridAdjacentTerm_eq (d e : ℕ) (v : TwoGridData d e) (j : ℕ) :
    twoGridAdjacentTerm d e v j = v.1.1 j *
      ((if e + 2 ∣ coprimeCenter d j - 1 then
          v.1.2 ((coprimeCenter d j - 1) / (e + 2) - 1) else 0) +
        (if e + 2 ∣ coprimeCenter d j + 1 then
          v.1.2 ((coprimeCenter d j + 1) / (e + 2) - 1) else 0)) := by
  have hn := coprimeCenter_ge_two d j
  have hm : ((coprimeCenter d j : ℝ) - 1) = ((coprimeCenter d j - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ coprimeCenter d j)]
    simp
  have hp : ((coprimeCenter d j : ℝ) + 1) = ((coprimeCenter d j + 1 : ℕ) : ℝ) := by simp
  simp only [twoGridAdjacentTerm, hm, hp, primitive_coprimeExtension_nat,
    show 0 < coprimeCenter d j - 1 by omega,
    show 0 < coprimeCenter d j + 1 by omega, true_and]

theorem primitive_twoGridExtension_second (d e j : ℕ) (v : TwoGridData d e) :
    primitive (twoGridExtension d e v) (coprimeCenter e j) =
      if d + 2 ∣ coprimeCenter e j then
        v.1.1 (coprimeCenter e j / (d + 2) - 1) else v.1.2 j := by
  rw [← inner_prefixCell, twoGridExtension_apply, inner_add_right,
    inner_prefixCell, inner_prefixCell, primitive_coprimeExtension_active,
    primitive_coprimeExtension_nat]
  have hp : 0 < coprimeCenter e j := by have := coprimeCenter_ge_two e j; omega
  simp only [hp, true_and]
  split_ifs with h
  · rw [(mem_twoGridDataSpace_iff d e v.1.1 v.1.2).1 v.2 j h, add_zero]
  · rw [zero_add]

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
