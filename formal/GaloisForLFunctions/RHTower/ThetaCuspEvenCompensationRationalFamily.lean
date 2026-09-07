import GaloisForLFunctions.RHTower.ThetaCuspEvenCompensationCoefficient
import GaloisForLFunctions.RHTower.ThetaCuspCenterCompensationSign
import GaloisForLFunctions.RHTower.ThetaCuspEvenFourCenterIntegration

/-! # Uniform rational family for the remaining even rank-four source comparison -/
open Filter Topology
open GaloisForLFunctions.HTGeometry
namespace RHTower
noncomputable section

/-- At every physical center, the two endpoint matrices control the whole coefficient interval. -/
theorem thetaCuspNativeEvenFourCompensated_posDef_of_endpoints
    {L C U x : ℝ} (hx : 0 ≤ x) (hLC : L ≤ C) (hCU : C ≤ U)
    (hL : (thetaCuspNativeEvenFourCompensated L x).PosDef)
    (hU : (thetaCuspNativeEvenFourCompensated U x).PosDef) :
    (thetaCuspNativeEvenFourCompensated C x).PosDef := by
  rw [thetaCuspNativeEvenFourCompensated_posDef_iff hx] at hL hU ⊢
  rcases le_total 0 (thetaCuspCenterCompensationSource x) with hG | hG
  · exact hL.trans_le (add_le_add le_rfl (mul_le_mul_of_nonneg_right hLC hG))
  · exact hU.trans_le (add_le_add le_rfl (mul_le_mul_of_nonpos_right hCU hG))

private theorem positive_near_zero {C : ℝ} (hC : 1000000000000 ≤ C) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, |x| < δ →
      (thetaCuspNativeEvenFourCompensated C x).PosDef := by
  have hHerm (x : ℝ) : (thetaCuspNativeEvenFourCompensated C x).IsHermitian := by
    rw [Matrix.IsHermitian]
    ext i j
    simp [thetaCuspNativeEvenFourCompensated, add_comm, and_comm]
  have ht (i j : Fin 4) : Tendsto (fun x => thetaCuspNativeEvenFourCompensated C x i j)
      (𝓝 0) (𝓝 (thetaCuspNativeEvenFourCompensated C 0 i j)) := by
    have hM := continuous_thetaCuspNativeEvenFourCompensated C
    have hc : Continuous (fun x => thetaCuspNativeEvenFourCompensated C x i j) := by fun_prop
    exact hc.continuousAt.tendsto
  have h := posDef_eventually_of_tendsto
    (thetaCuspNativeEvenFourCompensated_zero_posDef_of_coefficient_lower hC)
    (Filter.Eventually.of_forall hHerm) ht
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.mp h
  exact ⟨δ, hδ, fun x hx => hb (by simpa [Real.dist_eq] using hx)⟩

/-- One physical seam interval works for every coefficient in the explicit rational band. -/
theorem exists_thetaCuspEvenCompensation_rationalFamily_posDef_near_zero :
    ∃ δ : ℝ, 0 < δ ∧ ∀ C x : ℝ, 1000000000000 ≤ C → C ≤ 3000000000000 →
      0 ≤ x → x < δ → (thetaCuspNativeEvenFourCompensated C x).PosDef := by
  obtain ⟨δL, hδL, hL⟩ := positive_near_zero (C := 1000000000000) (by norm_num)
  obtain ⟨δU, hδU, hU⟩ := positive_near_zero (C := 3000000000000) (by norm_num)
  refine ⟨min δL δU, lt_min hδL hδU, fun C x hCL hCU hx hδ => ?_⟩
  exact thetaCuspNativeEvenFourCompensated_posDef_of_endpoints hx hCL hCU
    (hL x (by rw [abs_of_nonneg hx]; exact (lt_min_iff.mp hδ).1))
    (hU x (by rw [abs_of_nonneg hx]; exact (lt_min_iff.mp hδ).2))

/-- A common finite gap contains every possible failure in the entire rational family. -/
theorem exists_thetaCuspEvenCompensation_rationalFamily_compact_gap :
    ∃ δ R : ℝ, 0 < δ ∧ δ ≤ R ∧ ∀ C x : ℝ,
      1000000000000 ≤ C → C ≤ 3000000000000 → 0 ≤ x → (x < δ ∨ R ≤ x) →
        (thetaCuspNativeEvenFourCompensated C x).PosDef := by
  obtain ⟨δ, hδ, hnear⟩ := exists_thetaCuspEvenCompensation_rationalFamily_posDef_near_zero
  obtain ⟨RL, _, hL⟩ := exists_thetaCuspNativeEvenFourCompensated_posDef_tail 1000000000000
  obtain ⟨RU, _, hU⟩ := exists_thetaCuspNativeEvenFourCompensated_posDef_tail 3000000000000
  refine ⟨δ, max δ (max RL RU), hδ, le_max_left _ _, fun C x hCL hCU hx h => ?_⟩
  rcases h with h | h
  · exact hnear C x hCL hCU hx h
  · have hRL : RL ≤ x := (le_max_left RL RU).trans ((le_max_right δ _).trans h)
    have hRU : RU ≤ x := (le_max_right RL RU).trans ((le_max_right δ _).trans h)
    exact thetaCuspNativeEvenFourCompensated_posDef_of_endpoints hx hCL hCU (hL x hRL) (hU x hRU)

/-- The exact weighted source family has the same aperture-independent compact gap. -/
theorem exists_thetaCuspCenterCorrectedEvenFour_rationalFamily_compact_gap :
    ∃ δ R : ℝ, 0 < δ ∧ δ ≤ R ∧ ∀ C a r : ℝ,
      1000000000000 ≤ C → C ≤ 3000000000000 → 0 < a → 0 < r → (r < δ ∨ R ≤ r) →
        (thetaCuspCenterCorrectedEvenFour a C r).PosDef := by
  obtain ⟨δ, R, hδ, hR, hsource⟩ := exists_thetaCuspEvenCompensation_rationalFamily_compact_gap
  refine ⟨2*δ, 2*R, by positivity, by linarith, fun C a r hCL hCU ha hr h => ?_⟩
  apply thetaCuspCenterCorrectedEvenFour_posDef_of_source ha (by linarith) hr
  apply hsource C (r/2) hCL hCU (by positivity)
  rcases h with h | h
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

/-- The unique source sign transition selects one fixed rational lower comparison on each side. -/
theorem exists_thetaCuspEvenCompensation_rationalChamber_lower :
    ∃ τ : ℝ, 0 < τ ∧
      (∀ x : ℝ, 0 ≤ x → x ≤ τ →
        thetaCuspNativeEvenFourSchur x + 1000000000000*thetaCuspCenterCompensationSource x ≤
          thetaCuspNativeEvenFourSchur x +
            thetaCuspNativeEvenCompensationCoefficient*thetaCuspCenterCompensationSource x) ∧
      (∀ x : ℝ, τ ≤ x →
        thetaCuspNativeEvenFourSchur x + 3000000000000*thetaCuspCenterCompensationSource x ≤
          thetaCuspNativeEvenFourSchur x +
            thetaCuspNativeEvenCompensationCoefficient*thetaCuspCenterCompensationSource x) := by
  obtain ⟨τ, hτ, hsign⟩ := exists_thetaCuspCenterCompensationSource_transition
  have hC := thetaCuspNativeEvenCompensationCoefficient_bounds
  refine ⟨τ, hτ, ?_, ?_⟩
  · intro x hx hxτ
    have hG : 0 ≤ thetaCuspCenterCompensationSource x :=
      le_of_not_gt fun hn => (not_lt_of_ge hxτ) ((hsign x hx).2.2.mp hn)
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hC.1.le hG)
  · intro x hτx
    have hx : 0 ≤ x := hτ.le.trans hτx
    have hG : thetaCuspCenterCompensationSource x ≤ 0 :=
      le_of_not_gt fun hp => (not_lt_of_ge hτx) ((hsign x hx).1.mp hp)
    exact add_le_add le_rfl (mul_le_mul_of_nonpos_right hC.2.le hG)

end
end RHTower
