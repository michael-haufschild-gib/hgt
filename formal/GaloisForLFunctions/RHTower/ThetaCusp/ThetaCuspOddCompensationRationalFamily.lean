import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCenterCompensationSign
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspNativeOddSchurFarTail

/-!
# An explicit rational family of center compensation determinants

Every coefficient in the fixed rational interval shares positive neighborhoods
of both center ends. The canonical coefficient lies in this interval. Its
unique correction-sign transition selects explicit lower comparison endpoints;
the remaining compact determinant inequalities are not asserted here.
-/

open Filter Topology Set
namespace RHTower
noncomputable section

/-- Complete affine dependence of the seam determinant on the correction coefficient. -/
theorem thetaCuspNativeOddCompensatedDet_zero_factor (C : ℝ) :
    thetaCuspNativeOddCompensatedDet C 0 =
      thetaCuspNativeOddHeadDet 0 * thetaCuspFullSource 0^(2 : ℕ) *
        (3*C-thetaCuspNativeOddCompensationCoefficient) := by
  have hd := (thetaCuspNativeOddHeadDet_pos 0).ne'
  have hp := (thetaCuspFullSource_pos_all 0).ne'
  unfold thetaCuspNativeOddCompensatedDet thetaCuspNativeOddCompensationCoefficient
    thetaCuspCenterCompensationSource
  simp only [mul_zero, zero_mul, add_zero]
  field_simp
  ring

/-- Every coefficient at least one billion repairs the literal seam determinant. -/
theorem thetaCuspNativeOddCompensatedDet_zero_pos_of_coefficient_lower
    {C : ℝ} (hC : 1000000000 ≤ C) :
    0 < thetaCuspNativeOddCompensatedDet C 0 := by
  rw [thetaCuspNativeOddCompensatedDet_zero_factor]
  have hm := thetaCuspNativeOddCompensationCoefficient_bounds.2
  exact mul_pos (mul_pos (thetaCuspNativeOddHeadDet_pos 0)
    (sq_pos_of_pos (thetaCuspFullSource_pos_all 0))) (by linarith)

/-- The determinant increases with the coefficient on the positive correction chamber. -/
theorem thetaCuspNativeOddCompensatedDet_mono_coefficient
    {L C x : ℝ} (hLC : L ≤ C) (hG : 0 ≤ thetaCuspCenterCompensationSource x) :
    thetaCuspNativeOddCompensatedDet L x ≤ thetaCuspNativeOddCompensatedDet C x := by
  have h := mul_le_mul_of_nonneg_right hLC
    (mul_nonneg (thetaCuspNativeOddHeadDet_pos x).le hG)
  unfold thetaCuspNativeOddCompensatedDet
  nlinarith only [h]

/-- The determinant decreases with the coefficient on the negative correction chamber. -/
theorem thetaCuspNativeOddCompensatedDet_anti_coefficient
    {C U x : ℝ} (hCU : C ≤ U) (hG : thetaCuspCenterCompensationSource x ≤ 0) :
    thetaCuspNativeOddCompensatedDet U x ≤ thetaCuspNativeOddCompensatedDet C x := by
  have h := mul_le_mul_of_nonpos_right hCU
    (mul_nonpos_of_nonneg_of_nonpos (thetaCuspNativeOddHeadDet_pos x).le hG)
  unfold thetaCuspNativeOddCompensatedDet
  nlinarith only [h]

/-- Positive endpoint determinants control every coefficient between them. -/
theorem thetaCuspNativeOddCompensatedDet_pos_of_endpoints
    {L C U x : ℝ} (hLC : L ≤ C) (hCU : C ≤ U)
    (hL : 0 < thetaCuspNativeOddCompensatedDet L x)
    (hU : 0 < thetaCuspNativeOddCompensatedDet U x) :
    0 < thetaCuspNativeOddCompensatedDet C x := by
  rcases le_total 0 (thetaCuspCenterCompensationSource x) with hG | hG
  · exact hL.trans_le (thetaCuspNativeOddCompensatedDet_mono_coefficient hLC hG)
  · exact hU.trans_le (thetaCuspNativeOddCompensatedDet_anti_coefficient hCU hG)

private theorem continuous_compensatedDet (C : ℝ) :
    Continuous (thetaCuspNativeOddCompensatedDet C) := by
  have hn := continuous_thetaCuspNativeReflectionJet
  have hp := thetaCuspSchwartzReal.continuous
  change Continuous thetaCuspFullSource at hp
  have hG : Continuous thetaCuspCenterCompensationSource := by
    have heq : thetaCuspCenterCompensationSource =
        fun x => thetaCuspFullSource x^(2 : ℕ) * thetaCuspCenterCompensationSign x :=
      funext thetaCuspCenterCompensationSource_eq_sign
    rw [heq]
    exact (hp.pow 2).mul continuous_thetaCuspCenterCompensationSign
  unfold thetaCuspNativeOddCompensatedDet thetaCuspNativeOddHeadDet
    thetaCuspNativeOddHankelThreeDet HilbertMetric.signedEvenHankelThreeDet
  fun_prop

private theorem positive_near_zero {C : ℝ} (hC : 1000000000 ≤ C) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, |x| < δ →
      0 < thetaCuspNativeOddCompensatedDet C x := by
  have he := (continuous_compensatedDet C).continuousAt.eventually
    (eventually_gt_nhds (thetaCuspNativeOddCompensatedDet_zero_pos_of_coefficient_lower hC))
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.mp he
  exact ⟨δ, hδ, fun x hx => hb (by simpa [Real.dist_eq] using hx)⟩

/-- One center neighborhood works for the full explicit coefficient interval. -/
theorem exists_thetaCuspNativeOddCompensatedDet_rationalFamily_pos_near_zero :
    ∃ δ : ℝ, 0 < δ ∧ ∀ C : ℝ, 1000000000 ≤ C → C ≤ 3000000000 →
      ∀ x : ℝ, |x| < δ → 0 < thetaCuspNativeOddCompensatedDet C x := by
  obtain ⟨δ₀, hδ₀, h₀⟩ := positive_near_zero (C := 1000000000) (by norm_num)
  obtain ⟨δ₁, hδ₁, h₁⟩ := positive_near_zero (C := 3000000000) (by norm_num)
  refine ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, fun C hC₀ hC₁ x hx => ?_⟩
  exact thetaCuspNativeOddCompensatedDet_pos_of_endpoints hC₀ hC₁
    (h₀ x ((lt_min_iff.mp hx).1)) (h₁ x ((lt_min_iff.mp hx).2))

/-- One cofinal center ray works uniformly for every coefficient in the explicit interval. -/
theorem eventually_thetaCuspNativeOddCompensatedDet_rationalFamily_pos :
    ∀ᶠ x : ℝ in atTop, ∀ C : ℝ, 1000000000 ≤ C → C ≤ 3000000000 →
      0 < thetaCuspNativeOddCompensatedDet C x := by
  filter_upwards [eventually_thetaCuspNativeOddCompensatedDet_pos 1000000000,
    eventually_thetaCuspNativeOddCompensatedDet_pos 3000000000] with x h₀ h₁
  intro C hC₀ hC₁
  exact thetaCuspNativeOddCompensatedDet_pos_of_endpoints hC₀ hC₁ h₀ h₁

/-- A common compact center interval contains every possible failure in the rational family. -/
theorem exists_thetaCuspNativeOddCompensatedDet_rationalFamily_positive_ends :
    ∃ δ X : ℝ, 0 < δ ∧ δ < X ∧
      (∀ C : ℝ, 1000000000 ≤ C → C ≤ 3000000000 →
        (∀ x : ℝ, 0 < x → x < δ → 0 < thetaCuspNativeOddCompensatedDet C x) ∧
        (∀ x : ℝ, X ≤ x → 0 < thetaCuspNativeOddCompensatedDet C x)) := by
  obtain ⟨δ, hδ, hb⟩ := exists_thetaCuspNativeOddCompensatedDet_rationalFamily_pos_near_zero
  obtain ⟨X, hX⟩ := eventually_atTop.1
    eventually_thetaCuspNativeOddCompensatedDet_rationalFamily_pos
  refine ⟨δ, max X (δ+1), hδ, lt_of_lt_of_le (by linarith) (le_max_right _ _),
    fun C hC₀ hC₁ => ⟨?_, ?_⟩⟩
  · intro x hx hxd
    exact hb C hC₀ hC₁ x (by rwa [abs_of_pos hx])
  · intro x hx
    exact hX x ((le_max_left _ _).trans hx) C hC₀ hC₁

/-- The canonical source determinant is bounded below by explicit rational endpoints,
with the unique source transition selecting the correct endpoint. -/
theorem exists_thetaCuspNativeOddCompensatedDet_rationalChamber_lower :
    ∃ τ : ℝ, 0 < τ ∧
      (∀ x : ℝ, 0 ≤ x → x ≤ τ →
        thetaCuspNativeOddCompensatedDet 1000000000 x ≤
          thetaCuspNativeOddCompensatedDet thetaCuspNativeOddCompensationCoefficient x) ∧
      (∀ x : ℝ, τ ≤ x →
        thetaCuspNativeOddCompensatedDet 3000000000 x ≤
          thetaCuspNativeOddCompensatedDet thetaCuspNativeOddCompensationCoefficient x) := by
  obtain ⟨τ, hτ, hsign⟩ := exists_thetaCuspCenterCompensationSource_transition
  have hC := thetaCuspNativeOddCompensationCoefficient_bounds
  refine ⟨τ, hτ, ?_, ?_⟩
  · intro x hx hxτ
    apply thetaCuspNativeOddCompensatedDet_mono_coefficient hC.1.le
    exact le_of_not_gt fun hn => (not_lt_of_ge hxτ) ((hsign x hx).2.2.mp hn)
  · intro x hτx
    apply thetaCuspNativeOddCompensatedDet_anti_coefficient hC.2.le
    have hx : 0 ≤ x := hτ.le.trans hτx
    exact le_of_not_gt fun hp => (not_lt_of_ge hτx) ((hsign x hx).1.mp hp)

end
end RHTower
