import GaloisForLFunctions.BiScaleUncertainty.CoprimeTentHilbertFrame
import GaloisForLFunctions.BiScaleUncertainty.SobolevLogarithmicTransport

/-!
# Infinite coprime trace extension and energy projection

Every ℓ² sequence has an actual L² tent extension with every integer trace and
exact energy. The adjoint of normalized synthesis constructs the square-summable
second differences of every rough primitive. The resulting orthogonal projection
has an exact energy defect and a unique best-approximation law.
-/

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
set_option autoImplicit false

/-- Unnormalized synthesis realizes the prescribed nodal amplitudes. -/
def coprimeExtension (d : ℕ) (v : TraceData) : Velocity :=
  tentSynthesis d (Real.sqrt 2 • v)

private theorem sqrt_two_ne_zero : Real.sqrt 2 ≠ 0 :=
  ne_of_gt (Real.sqrt_pos.2 (by norm_num))

theorem hasSum_coprimeExtension (d : ℕ) (v : TraceData) :
    HasSum (fun j => v j • tentVelocity d j) (coprimeExtension d v) := by
  change HasSum _ (tentSynthesis d (Real.sqrt 2 • v))
  apply (hasSum_tentSynthesis d (Real.sqrt 2 • v)).congr_fun
  intro j
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, normalizedTent, smul_smul]
  congr 1
  field_simp [sqrt_two_ne_zero]

theorem coprimeExtension_energy (d : ℕ) (v : TraceData) :
    (∫ t, (coprimeExtension d v t)^2) = 2 * ∑' j, (v j)^2 := by
  rw [← norm_sq_velocity, coprimeExtension, (tentSynthesis d).norm_map,
    norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by norm_num),
    norm_sq_traceData]

/-- All integer traces, including every forbidden node, are determined exactly. -/
theorem primitive_coprimeExtension_sum (d n : ℕ) (v : TraceData) :
    primitive (coprimeExtension d v) n =
      ∑' j, if n = coprimeCenter d j then v j else 0 := by
  have h := (innerSL ℝ (prefixCell n)).hasSum (hasSum_coprimeExtension d v)
  simp only [innerSL_apply_apply, real_inner_smul_right,
    inner_prefixCell_tentVelocity, mul_ite, mul_one, mul_zero] at h
  rw [inner_prefixCell] at h
  exact h.tsum_eq.symm

theorem primitive_coprimeExtension_active (d j : ℕ) (v : TraceData) :
    primitive (coprimeExtension d v) (coprimeCenter d j) = v j := by
  rw [primitive_coprimeExtension_sum]
  simp only [(coprimeCenter_injective d).eq_iff]
  exact tsum_ite_eq' j (fun k => v k)

theorem primitive_coprimeExtension_nat (d n : ℕ) (v : TraceData) :
    primitive (coprimeExtension d v) n =
      if 0 < n ∧ d+2 ∣ n then v (n / (d+2) - 1) else 0 := by
  split_ifs with h
  · obtain ⟨k, hk⟩ := h.2
    have hkpos : 1 ≤ k := by
      by_contra hn
      have : k = 0 := by omega
      simp [this] at hk
      omega
    have hj : n = coprimeCenter d (k-1) := by
      simpa [coprimeCenter, Nat.sub_add_cancel hkpos] using hk
    rw [hj, primitive_coprimeExtension_active]
    simp [coprimeCenter]
  · rw [primitive_coprimeExtension_sum]
    have hz (j : ℕ) : (if n = coprimeCenter d j then v j else 0) = 0 := by
      apply if_neg
      intro hj
      apply h
      refine ⟨?_, ⟨j+1, hj⟩⟩
      rw [hj]
      have := coprimeCenter_ge_two d j
      omega
    simp only [hz, tsum_zero]

theorem log_coprimeExtension_active (d j : ℕ) (v : TraceData) :
    logPrimitive (coprimeExtension d v) (Real.log (coprimeCenter d j)) = v j := by
  have hp : 0 < (coprimeCenter d j : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by omega : 0 < 2) (coprimeCenter_ge_two d j)
  rw [logPrimitive, Real.exp_log hp, primitive_coprimeExtension_active]

/-- Half the centered second differences, as an actual ℓ² element. -/
def coprimeCoefficients (d : ℕ) (q : Velocity) : TraceData :=
  (Real.sqrt 2)⁻¹ • tentAnalysis d q

theorem coprimeCoefficients_apply (d j : ℕ) (q : Velocity) :
    coprimeCoefficients d q j = traceCurvature q d j / 2 := by
  simp only [coprimeCoefficients, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    tentAnalysis_apply]
  have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp [sqrt_two_ne_zero]
  rw [hs]
  ring

theorem summable_traceCurvature_sq (d : ℕ) (q : Velocity) :
    Summable (fun j => (traceCurvature q d j)^2) := by
  have h := lp.summable_inner (𝕜 := ℝ) (coprimeCoefficients d q) (coprimeCoefficients d q)
  have he : (fun j => (traceCurvature q d j)^2) =
      fun j => 4 * ⟪coprimeCoefficients d q j, coprimeCoefficients d q j⟫ := by
    funext j
    rw [coprimeCoefficients_apply]
    simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
    ring
  rw [he]
  exact h.mul_left 4

def coprimeProjection (d : ℕ) (q : Velocity) : Velocity :=
  tentSynthesis d (tentAnalysis d q)

theorem coprimeProjection_eq_extension (d : ℕ) (q : Velocity) :
    coprimeProjection d q = coprimeExtension d (coprimeCoefficients d q) := by
  simp [coprimeProjection, coprimeExtension, coprimeCoefficients, smul_smul]

theorem coprimeProjection_extension (d : ℕ) (v : TraceData) :
    coprimeProjection d (coprimeExtension d v) = coprimeExtension d v := by
  simp only [coprimeProjection, coprimeExtension, tentAnalysis_tentSynthesis]

theorem coprimeProjection_idempotent (d : ℕ) (q : Velocity) :
    coprimeProjection d (coprimeProjection d q) = coprimeProjection d q := by
  simp only [coprimeProjection, tentAnalysis_tentSynthesis]

theorem coprimeProjection_active_trace (d j : ℕ) (q : Velocity) :
    primitive (coprimeProjection d q) (coprimeCenter d j) = traceCurvature q d j / 2 := by
  rw [coprimeProjection_eq_extension, primitive_coprimeExtension_active,
    coprimeCoefficients_apply]

theorem inner_extension_projection_residual (d : ℕ) (v : TraceData) (q : Velocity) :
    ⟪coprimeExtension d v, q - coprimeProjection d q⟫ = 0 := by
  rw [inner_sub_right]
  have h := (tentSynthesis d).toContinuousLinearMap.adjoint_inner_right
    (Real.sqrt 2 • v) q
  change ⟪Real.sqrt 2 • v, tentAnalysis d q⟫ = ⟪coprimeExtension d v, q⟫ at h
  change ⟪coprimeExtension d v, q⟫ -
    ⟪tentSynthesis d (Real.sqrt 2 • v), tentSynthesis d (tentAnalysis d q)⟫ = 0
  rw [(tentSynthesis d).inner_map_map, ← h, sub_self]

/-- The closed range is characterized by the explicitly constructed projection. -/
theorem coprimeProjection_eq_self_iff (d : ℕ) (q : Velocity) :
    coprimeProjection d q = q ↔ ∃ v : TraceData, coprimeExtension d v = q := by
  constructor
  · intro h
    exact ⟨coprimeCoefficients d q, (coprimeProjection_eq_extension d q).symm.trans h⟩
  · rintro ⟨v, rfl⟩
    exact coprimeProjection_extension d v

theorem range_coprimeExtension (d : ℕ) :
    Set.range (coprimeExtension d) = Set.range (tentSynthesis d) := by
  ext q
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨Real.sqrt 2 • v, rfl⟩
  · rintro ⟨v, rfl⟩
    refine ⟨(Real.sqrt 2)⁻¹ • v, ?_⟩
    simp [coprimeExtension, smul_smul]

theorem isClosed_range_coprimeExtension (d : ℕ) :
    IsClosed (Set.range (coprimeExtension d)) := by
  rw [range_coprimeExtension]
  exact isClosed_range_tentSynthesis d

theorem range_tentSynthesis_closed_span (d : ℕ) :
    (tentSynthesis d).toLinearMap.range =
      (Submodule.span ℝ (Set.range (normalizedTent d))).topologicalClosure := by
  have h := (orthonormal_normalizedTent d).orthogonalFamily.range_linearIsometry
  change (tentSynthesis d).toLinearMap.range =
    (⨆ j, (LinearMap.toSpanSingleton ℝ Velocity (normalizedTent d j)).range).topologicalClosure at h
  simpa [← LinearMap.span_singleton_eq_range, ← Submodule.span_iUnion] using h

/-- The exact infinite coprime energy defect for every physical L² velocity. -/
theorem coprime_projection_energy_decomposition (d : ℕ) (q : Velocity) :
    (∫ t, (q t)^2) = (1/2 : ℝ) * (∑' j, (traceCurvature q d j)^2) +
      ∫ t, ((q - coprimeProjection d q) t)^2 := by
  have ho := inner_extension_projection_residual d (coprimeCoefficients d q) q
  rw [← coprimeProjection_eq_extension, inner_sub_right,
    real_inner_self_eq_norm_sq] at ho
  have he := coprimeExtension_energy d (coprimeCoefficients d q)
  rw [← coprimeProjection_eq_extension, ← norm_sq_velocity] at he
  have ht : (∑' j, (coprimeCoefficients d q j)^2) =
      (1/4 : ℝ) * ∑' j, (traceCurvature q d j)^2 := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro j
    rw [coprimeCoefficients_apply]
    ring
  rw [ht] at he
  rw [← norm_sq_velocity, ← norm_sq_velocity, norm_sub_sq_real, real_inner_comm,
    sub_eq_zero.mp ho, he]
  ring

theorem coprime_curvature_energy_le (d : ℕ) (q : Velocity) :
    (1/2 : ℝ) * (∑' j, (traceCurvature q d j)^2) ≤ ∫ t, (q t)^2 := by
  rw [coprime_projection_energy_decomposition d q, ← norm_sq_velocity]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- Every coefficient error contributes exactly twice its ℓ² energy. -/
theorem coprime_best_approximation (d : ℕ) (q : Velocity) (v : TraceData) :
    (∫ t, ((q - coprimeExtension d v) t)^2) =
      (∫ t, ((q - coprimeProjection d q) t)^2) +
      2 * ∑' j, (coprimeCoefficients d q j - v j)^2 := by
  have hlin : coprimeProjection d q - coprimeExtension d v =
      coprimeExtension d (coprimeCoefficients d q - v) := by
    rw [coprimeProjection_eq_extension]
    simp [coprimeExtension, smul_sub, map_sub]
  have ho := inner_extension_projection_residual d (coprimeCoefficients d q - v) q
  rw [← hlin] at ho
  have he := coprimeExtension_energy d (coprimeCoefficients d q - v)
  rw [← hlin, ← norm_sq_velocity] at he
  have hid : q - coprimeExtension d v =
      (q - coprimeProjection d q) + (coprimeProjection d q - coprimeExtension d v) := by abel
  rw [← norm_sq_velocity, ← norm_sq_velocity, hid, norm_add_sq_real, real_inner_comm, ho]
  rw [he]
  simp

theorem coprime_best_approximation_le (d : ℕ) (q : Velocity) (v : TraceData) :
    (∫ t, ((q - coprimeProjection d q) t)^2) ≤
      ∫ t, ((q - coprimeExtension d v) t)^2 := by
  rw [coprime_best_approximation]
  apply le_add_of_nonneg_right
  exact mul_nonneg (by norm_num) (tsum_nonneg fun j => sq_nonneg _)

/-- Equality in best approximation determines every coefficient. -/
theorem coprime_best_approximation_eq_iff (d : ℕ) (q : Velocity) (v : TraceData) :
    (∫ t, ((q - coprimeExtension d v) t)^2) =
      (∫ t, ((q - coprimeProjection d q) t)^2) ↔ v = coprimeCoefficients d q := by
  have hn : (∑' j, (coprimeCoefficients d q j - v j)^2) =
      ‖coprimeCoefficients d q - v‖^2 := by
    simpa using (norm_sq_traceData (coprimeCoefficients d q - v)).symm
  rw [coprime_best_approximation, hn]
  constructor
  · intro h
    have hz : ‖coprimeCoefficients d q - v‖ = 0 := by
      simpa only [add_eq_left, mul_eq_zero, OfNat.ofNat_ne_zero, false_or,
        sq_eq_zero_iff] using h
    exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm
  · rintro rfl
    simp

/-- The infinite second-difference bound retains the exact equality classifier. -/
theorem coprime_curvature_energy_eq_iff (d : ℕ) (q : Velocity) :
    (∫ t, (q t)^2) = (1/2 : ℝ) * (∑' j, (traceCurvature q d j)^2) ↔
      ∃ v : TraceData, coprimeExtension d v = q := by
  rw [coprime_projection_energy_decomposition d q, ← norm_sq_velocity]
  constructor
  · intro h
    have hz : ‖q - coprimeProjection d q‖ = 0 := by
      simpa only [add_eq_left, sq_eq_zero_iff] using h
    exact (coprimeProjection_eq_self_iff d q).mp
      (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm
  · intro h
    rw [(coprimeProjection_eq_self_iff d q).mpr h]
    simp

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
