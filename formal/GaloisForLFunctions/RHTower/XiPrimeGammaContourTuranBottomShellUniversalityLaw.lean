import GaloisForLFunctions.RHTower.XiGaussianExplicitFormulaRectangle
import GaloisForLFunctions.RHTower.XiHeatTuranBottomDetection

/-!
# Xi prime–Gamma contour Turán bottom-shell universality

One admissible arithmetic rectangle simultaneously approximates the first three Gaussian heat
moments. Continuity of their Turán determinant transfers RH near-positivity and off-critical
bottom-shell negativity to one finite continued prime--Gamma source contour.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Normalized prime--Gamma contour for the `n`-th Gaussian heat moment. -/
def xiGaussianSourceContourMoment
    (t : ℝ) (n : ℕ) (z₁ z₂ : ℂ) : ℂ :=
  (2 * Real.pi * I)⁻¹ *
    rectIntegral (fun z => xiGaussianTestC t n z *
      continuedPrimeArchSourceRelativeTrace z) z₁ z₂

/-- First three exact Gaussian heat moments as one finite packet. -/
def xiGaussianHeatMomentPacket (t : ℝ) : Fin 3 → ℂ :=
  fun n => xiGaussianHeatMoment n t

/-- First three normalized arithmetic source contours on one common rectangle. -/
def xiGaussianSourceContourMomentPacket
    (t : ℝ) (z₁ z₂ : ℂ) : Fin 3 → ℂ :=
  fun n => xiGaussianSourceContourMoment t n z₁ z₂

/-- Order-two Turán determinant of a three-moment complex packet. -/
def xiGaussianMomentPacketTuran (M : Fin 3 → ℂ) : ℝ :=
  (M 0).re * (M 2).re - (M 1).re ^ 2

theorem continuous_xiGaussianMomentPacketTuran :
    Continuous xiGaussianMomentPacketTuran := by
  unfold xiGaussianMomentPacketTuran
  fun_prop

theorem xiGaussianMomentPacketTuran_heatMomentPacket (t : ℝ) :
    xiGaussianMomentPacketTuran (xiGaussianHeatMomentPacket t) =
      xiHeatTuranDefect t := by
  rfl

/--
One admissible arithmetic rectangle simultaneously approximates all moments needed by the
order-two Gaussian heat Hankel determinant.
-/
theorem exists_admissible_gaussianSource_contour_approximates_heatMomentPacket
    {t : ℝ} (ht : 0 < t) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ z₁ z₂ : ℂ,
      z₁.re < z₂.re ∧ z₁.im < z₂.im ∧
      ∀ i : Fin 3,
        dist (xiGaussianSourceContourMomentPacket t z₁ z₂ i)
          (xiGaussianHeatMomentPacket t i) < epsilon := by
  classical
  let f : Fin 3 → XiZeroCopy → ℂ := fun i q =>
    (xiSpectralPoint q ^ 2) ^ (i : ℕ) * xiGaussianHeatTerm t q
  have hsum (i : Fin 3) : Summable (f i) := by
    simpa only [f] using summable_xiGaussianHeatMonomialTerm ht (i : ℕ)
  have hevent (i : Fin 3) : ∀ᶠ s : Finset XiZeroCopy in atTop,
      dist (∑ q ∈ s, f i q) (xiGaussianHeatMomentPacket t i) < epsilon := by
    have hball : Metric.ball (∑' q, f i q) epsilon ∈ nhds (∑' q, f i q) :=
      Metric.ball_mem_nhds _ hepsilon
    have hpartial := (hsum i).hasSum.eventually hball
    simpa only [Metric.mem_ball, xiGaussianHeatMomentPacket,
      xiGaussianHeatMoment, f] using hpartial
  have heventAll : ∀ᶠ s : Finset XiZeroCopy in atTop,
      ∀ i : Fin 3,
        dist (∑ q ∈ s, f i q) (xiGaussianHeatMomentPacket t i) < epsilon :=
    Filter.eventually_all.mpr hevent
  rw [eventually_atTop] at heventAll
  obtain ⟨F, hF⟩ := heventAll
  obtain ⟨z₁, z₂, hre, him, hpacket, hbot, htop, hright, hleft⟩ :=
    exists_admissible_rectangle_containing_xiZeroCopy_finset F
  refine ⟨z₁, z₂, hre, him, fun i => ?_⟩
  have hpi : (2 * Real.pi * I : ℂ) ≠ 0 := by
    have hpi0 : (Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast Real.pi_ne_zero
    simp [hpi0, Complex.I_ne_zero]
  have hcontour :=
    rectIntegral_continuedPrimeArchSourceRelativeTrace_eq_xiZeroCopyClosedRectangleSum
      (analyticOnNhd_xiGaussianTestC t (i : ℕ)) hre him hbot htop hright hleft
  have hnorm :
      xiGaussianSourceContourMomentPacket t z₁ z₂ i =
        ∑ q ∈ xiZeroCopyClosedRectangle z₁ z₂, f i q := by
    rw [xiGaussianSourceContourMomentPacket, xiGaussianSourceContourMoment,
      hcontour, ← mul_assoc, inv_mul_cancel₀ hpi, one_mul]
    exact Finset.sum_congr rfl fun q _ =>
      xiGaussianTestC_spectralPoint t (i : ℕ) q
  rw [hnorm]
  apply hF
  intro q hq
  rw [mem_xiZeroCopyClosedRectangle]
  apply Complex.mem_reProdIm.mpr
  rw [Set.uIcc_of_le hre.le, Set.uIcc_of_le him.le]
  exact ⟨⟨(hpacket q hq).1.le, (hpacket q hq).2.1.le⟩,
    ⟨(hpacket q hq).2.2.1.le, (hpacket q hq).2.2.2.le⟩⟩

/-- Under RH, one arithmetic contour Turán determinant can be made arbitrarily nearly
nonnegative. -/
theorem exists_primeGammaContourTuran_gt_neg_epsilon_of_rh
    (hRH : RiemannHypothesis) {t : ℝ} (ht : 0 < t)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ z₁ z₂ : ℂ,
      z₁.re < z₂.re ∧ z₁.im < z₂.im ∧
      -epsilon <
        xiGaussianMomentPacketTuran
          (xiGaussianSourceContourMomentPacket t z₁ z₂) := by
  let M := xiGaussianHeatMomentPacket t
  have hM :
      M ∈ {A : Fin 3 → ℂ | -epsilon < xiGaussianMomentPacketTuran A} := by
    change -epsilon < xiHeatTuranDefect t
    have hnonneg := xiHeatTuranDefect_nonneg_of_riemannHypothesis hRH ht
    linarith
  have hopen : IsOpen {A : Fin 3 → ℂ |
      -epsilon < xiGaussianMomentPacketTuran A} :=
    isOpen_lt continuous_const continuous_xiGaussianMomentPacketTuran
  obtain ⟨delta, hdelta, hball⟩ := Metric.isOpen_iff.mp hopen M hM
  obtain ⟨z₁, z₂, hre, him, happrox⟩ :=
    exists_admissible_gaussianSource_contour_approximates_heatMomentPacket
      ht hdelta
  refine ⟨z₁, z₂, hre, him, ?_⟩
  apply hball
  rw [Metric.mem_ball]
  exact (dist_pi_lt_iff hdelta).2 (by simpa only [M] using happrox)

/--
If the bottom squared shell is one off-critical conjugate pair, then all sufficiently late heat
times admit one arithmetic contour with strictly negative Turán determinant.
-/
theorem exists_eventually_negative_primeGammaContourTuran_of_bottom_conjugate_pair
    {q₀ : XiZeroCopy}
    (hmin : ∀ q : XiZeroCopy,
      (xiSpectralPoint q₀ ^ 2).re ≤ (xiSpectralPoint q ^ 2).re)
    (him : (xiSpectralPoint q₀ ^ 2).im ≠ 0)
    (hbottom : ∀ q : XiZeroCopy,
      (xiSpectralPoint q ^ 2).re = (xiSpectralPoint q₀ ^ 2).re →
      xiSpectralPoint q ^ 2 = xiSpectralPoint q₀ ^ 2 ∨
        xiSpectralPoint q ^ 2 = (starRingEnd ℂ) (xiSpectralPoint q₀ ^ 2)) :
    ∃ T : ℝ, ∀ t : ℝ, T < t →
      ∃ z₁ z₂ : ℂ,
        z₁.re < z₂.re ∧ z₁.im < z₂.im ∧
        xiGaussianMomentPacketTuran
          (xiGaussianSourceContourMomentPacket t z₁ z₂) < 0 := by
  obtain ⟨T₀, hT₀⟩ :=
    exists_neg_xiHeatTuranDefect_of_bottom_conjugate_pair hmin him hbottom
  refine ⟨max T₀ 0, fun t ht => ?_⟩
  have ht₀ : T₀ < t := lt_of_le_of_lt (le_max_left _ _) ht
  have htpos : 0 < t := lt_of_le_of_lt (le_max_right _ _) ht
  let M := xiGaussianHeatMomentPacket t
  have hM : M ∈ {A : Fin 3 → ℂ | xiGaussianMomentPacketTuran A < 0} := by
    change xiHeatTuranDefect t < 0
    exact hT₀ t ht₀
  have hopen : IsOpen {A : Fin 3 → ℂ | xiGaussianMomentPacketTuran A < 0} :=
    isOpen_lt continuous_xiGaussianMomentPacketTuran continuous_const
  obtain ⟨delta, hdelta, hball⟩ := Metric.isOpen_iff.mp hopen M hM
  obtain ⟨z₁, z₂, hre, himrect, happrox⟩ :=
    exists_admissible_gaussianSource_contour_approximates_heatMomentPacket
      htpos hdelta
  refine ⟨z₁, z₂, hre, himrect, ?_⟩
  apply hball
  rw [Metric.mem_ball]
  exact (dist_pi_lt_iff hdelta).2 (by simpa only [M] using happrox)

/--
**Xi prime–Gamma contour Turán bottom-shell universality.**

One finite arithmetic contour packet is nearly Turán-positive under RH and eventually
Turán-negative for a simple off-critical bottom shell.
-/
theorem xi_primeGammaContourTuran_bottomShellUniversality :
    (RiemannHypothesis → ∀ (t : ℝ), 0 < t →
      ∀ epsilon : ℝ, 0 < epsilon →
        ∃ z₁ z₂ : ℂ,
          z₁.re < z₂.re ∧ z₁.im < z₂.im ∧
          -epsilon <
            xiGaussianMomentPacketTuran
              (xiGaussianSourceContourMomentPacket t z₁ z₂)) ∧
    ∀ q₀ : XiZeroCopy,
      (∀ q : XiZeroCopy,
        (xiSpectralPoint q₀ ^ 2).re ≤ (xiSpectralPoint q ^ 2).re) →
      (xiSpectralPoint q₀ ^ 2).im ≠ 0 →
      (∀ q : XiZeroCopy,
        (xiSpectralPoint q ^ 2).re = (xiSpectralPoint q₀ ^ 2).re →
        xiSpectralPoint q ^ 2 = xiSpectralPoint q₀ ^ 2 ∨
          xiSpectralPoint q ^ 2 = (starRingEnd ℂ) (xiSpectralPoint q₀ ^ 2)) →
      ∃ T : ℝ, ∀ t : ℝ, T < t →
        ∃ z₁ z₂ : ℂ,
          z₁.re < z₂.re ∧ z₁.im < z₂.im ∧
          xiGaussianMomentPacketTuran
            (xiGaussianSourceContourMomentPacket t z₁ z₂) < 0 := by
  constructor
  · intro hRH t ht epsilon hepsilon
    exact exists_primeGammaContourTuran_gt_neg_epsilon_of_rh
      hRH ht hepsilon
  · intro q₀ hmin him hbottom
    exact exists_eventually_negative_primeGammaContourTuran_of_bottom_conjugate_pair
      hmin him hbottom

end

end RHTower
