import GaloisForLFunctions.HTGeometry.GomesSpinFourOuterSymmetry

/-!
# Complete carrier-level classification of factor-exchange intertwiners

This strengthens the existing Spin(4) instance of arXiv:2607.24901v1,
Proposition 3. The real-linear commutant is scalar. Every real-linear
factor-exchange intertwiner is a scalar conjugation, and precisely the two
signed conjugations preserve norm. Exchange remains outer on the represented
gauge action; passing through its central kernel does not remove the obstruction.
-/

open scoped Quaternion
noncomputable section
set_option synthInstance.maxHeartbeats 100000
namespace GaloisForLFunctions.HTGeometry

/-- Quaternion conjugation as a real-linear carrier transformation. -/
def quaternionConjugationLinear : EventQuaternion →ₗ[ℝ] EventQuaternion where
  toFun := star
  map_add' := star_add
  map_smul' r q := by simp

/-- The entire real-linear commutant of the existing two-sided gauge action is scalar. -/
theorem spinFour_linear_commutant (F : EventQuaternion →ₗ[ℝ] EventQuaternion) :
    (∀ g : SpinFourGaugeGroup, ∀ q, F (g • q) = g • F q) ↔
      ∀ q, F q = (F 1).re • q := by
  constructor
  · intro h
    have hleft (u : QuaternionGaugeGroup) : F u.1 = u.1 * F 1 := by
      have hh := h (u,1) 1
      change F (u.1 * 1 * star (1 : EventQuaternion)) = u.1 * F 1 * star (1 : EventQuaternion) at hh
      simpa using hh
    have hq (q : EventQuaternion) : F q = q * F 1 := by
      by_cases hz : q = 0
      · simp [hz]
      have hn : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hz
      let u : QuaternionGaugeGroup := ⟨‖q‖⁻¹ • q, by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]⟩
      have hh := congrArg (fun z : EventQuaternion => ‖q‖ • z) (hleft u)
      change ‖q‖ • F (‖q‖⁻¹ • q) = ‖q‖ • ((‖q‖⁻¹ • q) * F 1) at hh
      simpa only [map_smul, smul_smul, mul_inv_cancel₀ hn, one_smul,
        smul_mul_assoc] using hh
    have hc (v : QuaternionGaugeGroup) : F 1 * star v.1 = star v.1 * F 1 := by
      have hh := h (1,v) 1
      change F (1 * 1 * star v.1) = 1 * F 1 * star v.1 at hh
      simp only [one_mul] at hh
      rw [hq (star v.1)] at hh
      exact hh.symm
    have hi := hc quaternionGaugeI
    have hj := hc quaternionGaugeJ
    have hk := congrArg (fun z : EventQuaternion => z.imJ) hi
    have hji := congrArg (fun z : EventQuaternion => z.imK) hi
    have hii := congrArg (fun z : EventQuaternion => z.imK) hj
    simp [quaternionGaugeI, quaternionGaugeJ, quaternionGaugeIValue,
      quaternionGaugeJValue] at hk hji hii
    have hk0 : (F 1).imK = 0 := by linarith
    have hj0 : (F 1).imJ = 0 := by linarith
    have hi0 : (F 1).imI = 0 := by linarith
    intro q
    rw [hq]
    have hr : F 1 = ((F 1).re : EventQuaternion) := by
      ext <;> simp [hi0, hj0, hk0]
    rw [hr]
    ext <;> simp <;> ring
  · intro h g q
    rw [h (g • q), h q]
    change (F 1).re • (g.1.1 * q * star g.2.1) =
      g.1.1 * ((F 1).re • q) * star g.2.1
    simp only [mul_smul_comm, smul_mul_assoc]

/-- All real-linear factor-exchange intertwiners are scalar quaternion conjugations. -/
theorem spinFour_factorSwap_intertwiners (F : EventQuaternion →ₗ[ℝ] EventQuaternion) :
    (∀ g : SpinFourGaugeGroup, ∀ q, F (g • q) = spinFourFactorSwap g • F q) ↔
      ∀ q, F q = (F 1).re • star q := by
  constructor
  · intro h
    have hc : ∀ g : SpinFourGaugeGroup, ∀ q,
        (quaternionConjugationLinear.comp F) (g • q) =
          g • (quaternionConjugationLinear.comp F) q := by
      intro g q
      change star (F (g • q)) = g • star (F q)
      rw [h, quaternionStar_spinFour_intertwines, spinFourFactorSwap_twice]
    have hh := (spinFour_linear_commutant (quaternionConjugationLinear.comp F)).mp hc
    intro q
    have hstar := congrArg star (hh q)
    simpa [quaternionConjugationLinear] using hstar
  · intro h g q
    rw [h (g • q), h q, quaternionStar_spinFour_intertwines]
    change (F 1).re • (g.2.1 * star q * star g.1.1) =
      g.2.1 * ((F 1).re • star q) * star g.1.1
    simp only [mul_smul_comm, smul_mul_assoc]

/-- Among norm-preserving maps the entire factor-exchange family consists of the two conjugations. -/
theorem spinFour_factorSwap_orthogonal_intertwiners
    (F : EventQuaternion →ₗ[ℝ] EventQuaternion) :
    ((∀ g : SpinFourGaugeGroup, ∀ q, F (g • q) = spinFourFactorSwap g • F q) ∧
      ∀ q, Quaternion.normSq (F q) = Quaternion.normSq q) ↔
        F = quaternionConjugationLinear ∨ F = -quaternionConjugationLinear := by
  constructor
  · rintro ⟨h, hn⟩
    have hf := (spinFour_factorSwap_intertwiners F).mp h
    have hr := hn 1
    rw [hf 1] at hr
    simp only [star_one, Quaternion.normSq_smul, map_one, mul_one] at hr
    rcases sq_eq_one_iff.mp hr with hp | hm
    · left
      apply LinearMap.ext
      intro q
      simpa [hp, quaternionConjugationLinear] using hf q
    · right
      apply LinearMap.ext
      intro q
      simpa [hm, quaternionConjugationLinear] using hf q
  · rintro (rfl | rfl)
    · exact ⟨quaternionStar_spinFour_intertwines, Quaternion.normSq_star⟩
    · constructor
      · intro g q
        change -star (g • q) = spinFourFactorSwap g • (-star q)
        rw [quaternionStar_spinFour_intertwines]
        change -(g.2.1 * star q * star g.1.1) = g.2.1 * (-star q) * star g.1.1
        simp only [mul_neg, neg_mul]
      · intro q
        change Quaternion.normSq (-star q) = Quaternion.normSq q
        simp [Quaternion.normSq_star]

/-- No element of the actual gauge image implements factor exchange by conjugation.
The conclusion is at the represented-action level, so the central kernel cannot remove the obstruction. -/
theorem spinFour_factorSwap_not_inner_on_carrier :
    ¬ ∃ k : SpinFourGaugeGroup, ∀ g : SpinFourGaugeGroup, ∀ q : EventQuaternion,
      k • (g • q) = spinFourFactorSwap g • (k • q) := by
  rintro ⟨k,h⟩
  have ha : k.1.1 ≠ (0 : EventQuaternion) := by
    intro hz
    have hn := quaternionGauge_normSq k.1
    simp [hz] at hn
  have hb : star k.2.1 ≠ (0 : EventQuaternion) := by
    intro hz
    have hn := quaternionGauge_normSq k.2
    have hnorm := Quaternion.normSq_star k.2.1
    rw [hz] at hnorm
    simp only [map_zero] at hnorm
    exact zero_ne_one (hnorm.trans hn)
  have hc (u : QuaternionGaugeGroup) (q : EventQuaternion) :
      u.1 * q * star k.2.1 = q * star k.2.1 * star u.1 := by
    have hh := h (u,1) q
    change k.1.1 * (u.1 * q * star (1 : EventQuaternion)) * star k.2.1 =
      1 * (k.1.1 * q * star k.2.1) * star u.1 at hh
    simp only [star_one, mul_one, one_mul, mul_assoc] at hh
    apply mul_left_cancel₀ ha
    simpa only [mul_assoc] using hh
  apply quaternionGaugeGroup_nonabelian
  intro u v
  apply Subtype.ext
  apply mul_right_cancel₀ hb
  change (u.1 * v.1) * star k.2.1 = (v.1 * u.1) * star k.2.1
  have hp := hc u 1
  simp only [mul_one, one_mul] at hp
  calc
    u.1 * v.1 * star k.2.1 = v.1 * star k.2.1 * star u.1 := hc u v.1
    _ = v.1 * (star k.2.1 * star u.1) := mul_assoc _ _ _
    _ = v.1 * (u.1 * star k.2.1) := by rw [← hp]
    _ = v.1 * u.1 * star k.2.1 := (mul_assoc _ _ _).symm

end GaloisForLFunctions.HTGeometry
