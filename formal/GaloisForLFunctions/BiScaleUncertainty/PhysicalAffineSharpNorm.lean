import GaloisForLFunctions.BiScaleUncertainty.PhysicalAffineProducers
import GaloisForLFunctions.BiScaleUncertainty.PhysicalAntiperiodicRigidity

/-!
# Sharp physical affine commutator norm and nonattainment

Explicit unit producers force the sharp norm at every nonzero affine gap.
Antiperiodic rigidity classifies every norm attainer. The quantitative
producer defect tends to zero on the actual physical energy space.
-/

noncomputable section
open Filter
open scoped Topology
namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
set_option autoImplicit false

theorem physicalAffineCommutator_zero_gap (a b : ℝ) (h : b*(a-1) = 0) :
    physicalAffineCommutator a b = 0 := by
  have hab : a*b = b := by nlinarith only [h]
  apply ContinuousLinearMap.ext
  intro q
  simp only [physicalAffineCommutator_factor, hab, sub_self, map_zero, zero_apply]

theorem physicalAffineCommutator_zero_scale (b : ℝ) : physicalAffineCommutator 0 b = 0 := by
  apply ContinuousLinearMap.ext
  intro q
  simp only [physicalAffineCommutator_apply, physicalDilation_zero, map_zero, sub_self, zero_apply]

theorem norm_physicalAffineCommutator (a b : ℝ) :
    ‖physicalAffineCommutator a b‖ = if b*(a-1) = 0 then 0 else 2*Real.sqrt |a| := by
  by_cases hc : b*(a-1) = 0
  · rw [if_pos hc, physicalAffineCommutator_zero_gap a b hc, norm_zero]
  · rw [if_neg hc]
    apply le_antisymm (norm_physicalAffineCommutator_le a b)
    have hn (n : ℕ) : |a| * (4-2/((n : ℝ)+1)) ≤ ‖physicalAffineCommutator a b‖^2 := by
      have h := (physicalAffineCommutator a b).le_opNorm (physicalAffineProducer a b n)
      rw [physicalAffineProducer_norm, if_neg hc, mul_one] at h
      have he := physicalAffineProducer_energy a b n
      rw [if_neg hc] at he
      nlinarith only [h, he, norm_nonneg (physicalAffineCommutator a b),
        norm_nonneg (physicalAffineCommutator a b (physicalAffineProducer a b n))]
    have ht : Tendsto (fun n : ℕ => |a| * (4-2/((n : ℝ)+1))) atTop (𝓝 (4*|a|)) := by
      have h := (((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2).const_sub 4).const_mul |a|
      simpa only [div_eq_mul_inv, mul_one, one_mul, mul_zero, zero_mul, sub_zero,
        mul_assoc, mul_comm, mul_left_comm] using h
    have hl := le_of_tendsto ht (Eventually.of_forall hn)
    nlinarith only [hl, Real.sq_sqrt (abs_nonneg a), norm_nonneg (physicalAffineCommutator a b),
      Real.sqrt_nonneg |a|]

theorem physicalAffineCommutator_zero_iff (a b : ℝ) :
    physicalAffineCommutator a b = 0 ↔ a = 0 ∨ a = 1 ∨ b = 0 := by
  constructor
  · intro h
    by_cases ha : a = 0
    · exact Or.inl ha
    · have hc : b*(a-1) = 0 := by
        by_contra hc
        have hn := norm_physicalAffineCommutator a b
        rw [h, norm_zero, if_neg hc] at hn
        have hp : 0 < Real.sqrt |a| := Real.sqrt_pos.mpr (abs_pos.mpr ha)
        linarith only [hn, hp]
      rcases mul_eq_zero.mp hc with hb | ha1
      · exact Or.inr (Or.inr hb)
      · exact Or.inr (Or.inl (sub_eq_zero.mp ha1))
  · rintro (rfl | rfl | rfl)
    · exact physicalAffineCommutator_zero_scale b
    · exact physicalAffineCommutator_zero_gap 1 b (by simp)
    · exact physicalAffineCommutator_zero_gap a 0 (by simp)

theorem physicalAffineCommutator_norm_attainment_iff (a b : ℝ) (q : Velocity) :
    ‖physicalAffineCommutator a b q‖ = ‖physicalAffineCommutator a b‖*‖q‖ ↔
      physicalAffineCommutator a b = 0 ∨ q = 0 := by
  constructor
  · intro h
    by_cases hC : physicalAffineCommutator a b = 0
    · exact Or.inl hC
    · have hc : b*(a-1) ≠ 0 := fun hgap => hC (physicalAffineCommutator_zero_gap a b hgap)
      have hn := norm_physicalAffineCommutator a b
      rw [if_neg hc] at hn
      have he : ‖physicalAffineCommutator a b q‖^2 = 4*|a| * ‖q‖^2 := by
        rw [h, hn, mul_pow, mul_pow, Real.sq_sqrt (abs_nonneg a)]
        ring
      rcases (physicalAffineCommutator_maximal_energy_iff a b q).mp he with ha | hq
      · have hz : physicalAffineCommutator a b = 0 := by
          rw [ha]
          exact physicalAffineCommutator_zero_scale b
        exact False.elim (hC hz)
      · exact Or.inr hq
  · rintro (hC | hq)
    · simp [hC]
    · simp [hq]

theorem physicalAffineProducer_defect_tendsto (a b : ℝ) :
    Tendsto (fun n : ℕ => 4*|a| * ‖physicalAffineProducer a b n‖^2-
      ‖physicalAffineCommutator a b (physicalAffineProducer a b n)‖^2) atTop (𝓝 0) := by
  simp only [physicalAffineProducer_defect]
  by_cases hc : b*(a-1) = 0
  · simp only [if_pos hc]
    exact tendsto_const_nhds
  · simp only [if_neg hc]
    simpa only [div_eq_mul_inv, mul_one, one_mul, mul_zero, mul_assoc] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2*|a|)

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
