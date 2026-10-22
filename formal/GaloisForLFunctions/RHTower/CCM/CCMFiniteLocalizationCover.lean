import GaloisForLFunctions.RHTower.CCM.CCMFiniteLocalizationChain
import GaloisForLFunctions.RHTower.CCM.CCMThetaSeparatedAngle
import GaloisForLFunctions.RHTower.CCM.CCMSmoothSourceRecentering

/-!
# Constructed finite localization of every smooth source

Compactness supplies finitely many small balls. Smooth compact angles equal
pi/2 on a smaller covering ball and vanish outside a larger ball. Sequential
cosine/sine splitting therefore leaves zero remainder, with every retained
piece in the center-independent positive local class.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped SchwartzMap

namespace RHTower

theorem exists_schwartz_localizing_angle (c delta : ℝ) (hd : 0 < delta) :
    ∃ theta : 𝓢(ℝ, ℝ), HasCompactSupport theta ∧
      tsupport theta ⊆ Metric.ball c delta ∧
      ∀ x ∈ Metric.ball c (delta / 4), theta x = Real.pi / 2 := by
  have hsmall : delta / 4 < delta / 2 := by linarith
  have hlarge : delta / 2 < delta := half_lt_self hd
  have hdisj : Disjoint (Metric.ball c (delta / 2))ᶜ (Metric.closedBall c (delta / 4)) :=
    Set.disjoint_left.mpr fun x hx hy => hx (Metric.closedBall_subset_ball hsmall hy)
  obtain ⟨theta, hc, hzero, hone⟩ := exists_schwartz_separating_angle
    Metric.isOpen_ball.isClosed_compl (isCompact_closedBall c (delta / 4)) hdisj (Real.pi / 2)
  have hs : Function.support theta ⊆ Metric.ball c (delta / 2) := by
    intro x hx
    by_contra hout
    exact hx (hzero x hout)
  refine ⟨theta, hc, ?_, fun x hx => hone x (Metric.ball_subset_closedBall hx)⟩
  exact (closure_minimal (hs.trans Metric.ball_subset_closedBall)
    Metric.isClosed_closedBall).trans (Metric.closedBall_subset_ball hlarge)

theorem exists_ccmFiniteLocalization_cover (delta : ℝ) (hd : 0 < delta)
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a) :
    ∃ angles : List 𝓢(ℝ, ℝ),
      (∀ theta ∈ angles, HasCompactSupport theta) ∧
      (∀ v ∈ ccmLocalizationPieces u angles, ∃ c : ℝ, tsupport v ⊆ Metric.ball c delta) ∧
      (∀ x, ccmLocalizationRemainder u angles x = 0) := by
  classical
  obtain ⟨s, hs⟩ := u.hasCompactSupport.elim_finite_subcover
    (fun c : ℝ => Metric.ball c (delta / 4)) (fun _ => Metric.isOpen_ball) (by
      intro x _
      exact mem_iUnion.mpr ⟨x, Metric.mem_ball_self (by positivity)⟩)
  choose theta hcompact hsupport hone using fun c => exists_schwartz_localizing_angle c delta hd
  let angles := s.toList.map theta
  have hangle : ∀ eta ∈ angles, ∃ c : ℝ, tsupport eta ⊆ Metric.ball c delta := by
    intro eta he
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp he
    exact ⟨c, hsupport c⟩
  refine ⟨angles, ?_, ccmLocalizationPieces_support u angles delta hangle, ?_⟩
  · intro eta he
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp he
    exact hcompact c
  · intro x
    by_cases hx : u x = 0
    · exact ccmLocalizationRemainder_apply_eq_zero u angles x hx
    · obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.mp (hs (subset_closure hx))
      apply ccmLocalizationRemainder_apply_eq_zero_of_mem u angles (theta c)
        (List.mem_map.mpr ⟨c, Finset.mem_toList.mpr hc, rfl⟩) x
      rw [hone c x hxc, Real.cos_pi_div_two]

theorem ccmSmoothSourcePhysicalMass_eq_zero_of_pointwise {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (hu : ∀ x, u x = 0) :
    ‖ccmArchimedeanFormEmbedding a u.toCCMFormVector‖ ^ 2 = 0 := by
  rw [← ccmSmooth_integral_norm_sq_eq_physical]
  simp only [hu, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), integral_zero]

/-- Every actual source has a finite, mass-preserving localization into positive
pieces, with its entire arithmetic discrepancy retained as signed totals. -/
theorem exists_ccmFiniteLocalization_positive_assembly :
    ∃ delta C : ℝ, 0 < delta ∧ 0 < C ∧
      ∀ (a : SuzukiPositiveAperture) (u : CCMComplexSmoothInteriorSource a),
      ∃ angles : List 𝓢(ℝ, ℝ),
        (∀ theta ∈ angles, HasCompactSupport theta) ∧
        (∀ v ∈ ccmLocalizationPieces u angles, ∃ c : ℝ, tsupport v ⊆ Metric.ball c delta) ∧
        (∀ x, ccmLocalizationRemainder u angles x = 0) ∧
        (((ccmLocalizationPieces u angles).map
          (fun v => ‖ccmArchimedeanFormEmbedding a v.toCCMFormVector‖ ^ 2)).sum =
          ‖ccmArchimedeanFormEmbedding a u.toCCMFormVector‖ ^ 2) ∧
        (C * ‖ccmArchimedeanFormEmbedding a u.toCCMFormVector‖ ^ 2 ≤
          ((ccmLocalizationPieces u angles).map
            (fun v => ccmRestrictedWeilSourceQuadratic a v.toCCMFormVector)).sum) ∧
        (ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector =
          ((ccmLocalizationPieces u angles).map
            (fun v => ccmRestrictedWeilSourceQuadratic a v.toCCMFormVector)).sum -
          ccmLocalizationPrimeTotal u angles + ccmLocalizationContinuousTotal u angles) := by
  obtain ⟨delta, C, hd, hC, hgap⟩ := exists_ccmSmoothSource_center_independent_gap
  refine ⟨delta, C, hd, hC, fun a u => ?_⟩
  obtain ⟨angles, hc, hs, hz⟩ := exists_ccmFiniteLocalization_cover delta hd u
  have hm := ccmLocalization_mass_conservation u angles
  rw [ccmSmoothSourcePhysicalMass_eq_zero_of_pointwise _ hz, zero_add] at hm
  have he := ccmLocalization_energy_conservation u angles
  rw [ccmSmoothSourceQuadratic_eq_zero_of_pointwise _ hz, zero_add] at he
  refine ⟨angles, hc, hs, hz, hm, ?_, he⟩
  rw [← hm]
  have hsum : ∀ l : List (CCMComplexSmoothInteriorSource a),
      (∀ v ∈ l, ∃ c : ℝ, tsupport v ⊆ Metric.ball c delta) →
      C * (l.map (fun v => ‖ccmArchimedeanFormEmbedding a v.toCCMFormVector‖ ^ 2)).sum ≤
        (l.map (fun v => ccmRestrictedWeilSourceQuadratic a v.toCCMFormVector)).sum := by
    intro l hl
    induction l with
    | nil => simp
    | cons v rest ih =>
      obtain ⟨c, hv⟩ := hl v List.mem_cons_self
      have ht := ih (fun w hw => hl w (List.mem_cons_of_mem _ hw))
      simpa only [List.map_cons, List.sum_cons, mul_add] using add_le_add (hgap a v c hv) ht
  exact hsum _ hs

end RHTower
