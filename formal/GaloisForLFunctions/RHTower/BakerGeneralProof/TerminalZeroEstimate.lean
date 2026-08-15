import GaloisForLFunctions.RHTower.BakerGeneralProof.RepeatedFrequencyGrowthBound

/-!
# Terminal gap-free zero estimate

For a nonzero exponential polynomial, choose maximum-modulus points on radii `R` and `4R`.
Multipoint Schwarz supplies lower growth from prescribed zeros, while repeated-frequency contour
interpolation supplies upper growth. Positivity of the inner maximum follows from the analytic
identity theorem, so it can be cancelled. The resulting explicit inequality has no frequency-gap
constant.
-/

open scoped Classical
open Complex Metric Filter
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RHTower.BakerGeneralProof

theorem norm_sphereMax_pos_of_ne_zero
    (F : ℂ → ℂ) (hF : ∀ z, AnalyticAt ℂ F z) (hFne : F ≠ 0)
    {R : ℝ} (hR : 0 < R) {zR : ℂ}
    (hmax : ∀ w : ℂ, ‖w‖ ≤ R → ‖F w‖ ≤ ‖F zR‖) :
    0 < ‖F zR‖ := by
  by_contra hnot
  have hzR : ‖F zR‖ = 0 := le_antisymm (le_of_not_gt hnot) (norm_nonneg _)
  have hev : F =ᶠ[nhds (0 : ℂ)] 0 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hR] with w hw
    have hwR : ‖w‖ ≤ R := by
      have : ‖w‖ < R := by simpa [mem_ball, dist_zero_right] using hw
      exact this.le
    have hFw := hmax w hwR
    rw [hzR] at hFw
    have : F w = 0 := norm_eq_zero.mp (le_antisymm hFw (norm_nonneg _))
    simpa using this
  have hAnalytic : AnalyticOnNhd ℂ F (Set.univ : Set ℂ) :=
    fun z _ => hF z
  have hall := hAnalytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ (0 : ℂ)) hev
  apply hFne
  funext z
  simpa using hall (Set.mem_univ z)

/--
Terminal gap-free zero estimate. Uniform multiplicity at finitely many points forces this explicit
inequality; its right side depends on an upper frequency radius but not pairwise frequency gaps.
-/
theorem repeatedFrequency_terminal_zero_inequality
    {I : Type*} [Fintype I]
    (P : I → Polynomial ℂ) (mu : I → ℂ) (K : ℕ)
    (hP : ∀ i, (P i).natDegree < K)
    (hFne : exponentialPolynomial P mu ≠ 0)
    {Omega R : ℝ} (hOmega : 0 ≤ Omega)
    (hmu : ∀ i, ‖mu i‖ ≤ Omega)
    (hR : 0 < R)
    (points : Finset ℂ) (mult : ℕ)
    (hpoints : ∀ c ∈ points, ‖c‖ ≤ R)
    (horder : ∀ c ∈ points,
      mult ≤ analyticOrderAt (exponentialPolynomial P mu) c) :
    (3 * R) ^ (mult * points.card) ≤
      (2 * R) ^ (mult * points.card) *
        (frequencyContourRadius Omega *
          (Real.exp ((4 * R) * frequencyContourRadius Omega) *
            (frequencyContourRadius Omega ^ (Fintype.card I * K) *
              (1 + Omega) ^ (Fintype.card I * K)) /
            (frequencyContourRadius Omega - Omega) ^ (Fintype.card I * K))) *
        ∑ m ∈ Finset.range (Fintype.card I * K + 1),
          (m.factorial : ℝ) / R ^ m := by
  let F : ℂ → ℂ := exponentialPolynomial P mu
  have hF : ∀ z, AnalyticAt ℂ F z := fun z =>
    analyticAt_exponentialPolynomial P mu z
  have hdiff : Differentiable ℂ F := differentiable_exponentialPolynomial P mu
  obtain ⟨zR, hzR, hmaxR⟩ := exists_sphere_isMaxOn hdiff hR
  have h4R : 0 < 4 * R := by positivity
  obtain ⟨z4, hz4, hmax4⟩ := exists_sphere_isMaxOn hdiff h4R
  have hMR : 0 < ‖F zR‖ :=
    norm_sphereMax_pos_of_ne_zero F hF hFne hR hmaxR
  have hlower :
      (3 * R) ^ (mult * points.card) * ‖F zR‖ ≤
        (2 * R) ^ (mult * points.card) * ‖F z4‖ := by
    exact multipoint_four_radius_growth F hF points mult hR hpoints horder hzR hmax4
  have hboundaryR : ∀ w ∈ sphere (0 : ℂ) R, ‖F w‖ ≤ ‖F zR‖ := by
    intro w hw
    apply hmaxR w
    have : ‖w‖ = R := by simpa [mem_sphere_iff_norm] using hw
    exact this.le
  have hupper := norm_exponentialPolynomial_le_repeatedFrequency
    P mu K hP hOmega hmu hR hboundaryR z4
  change ‖F z4‖ ≤ _ at hupper
  rw [hz4] at hupper
  let J : ℝ := ∑ m ∈ Finset.range (Fintype.card I * K + 1),
    (m.factorial : ℝ) / R ^ m
  have hsum :
      (∑ m ∈ Finset.range (Fintype.card I * K + 1),
          (m.factorial : ℝ) * ‖F zR‖ / R ^ m) = J * ‖F zR‖ := by
    dsimp [J]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m hm
    ring
  rw [hsum] at hupper
  have hupper' :
      ‖F z4‖ ≤
        ((frequencyContourRadius Omega *
          (Real.exp ((4 * R) * frequencyContourRadius Omega) *
            (frequencyContourRadius Omega ^ (Fintype.card I * K) *
              (1 + Omega) ^ (Fintype.card I * K)) /
            (frequencyContourRadius Omega - Omega) ^ (Fintype.card I * K))) * J) *
          ‖F zR‖ := by
    simpa only [mul_assoc] using hupper
  have hB : 0 ≤ (2 * R) ^ (mult * points.card) := by positivity
  have hcombined :
      (3 * R) ^ (mult * points.card) * ‖F zR‖ ≤
        (2 * R) ^ (mult * points.card) *
          ((frequencyContourRadius Omega *
            (Real.exp ((4 * R) * frequencyContourRadius Omega) *
              (frequencyContourRadius Omega ^ (Fintype.card I * K) *
                (1 + Omega) ^ (Fintype.card I * K)) /
              (frequencyContourRadius Omega - Omega) ^ (Fintype.card I * K))) *
            J * ‖F zR‖) :=
    hlower.trans (mul_le_mul_of_nonneg_left hupper' hB)
  apply (mul_le_mul_iff_right₀ hMR).mp
  simpa only [J, mul_assoc, mul_comm, mul_left_comm] using hcombined

end GaloisForLFunctions.RHTower.BakerGeneralProof
