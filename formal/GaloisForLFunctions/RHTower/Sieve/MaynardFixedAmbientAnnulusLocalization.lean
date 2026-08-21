import GaloisForLFunctions.RHTower.Sieve.MaynardFixedAmbientPacketNatOrder

open Complex MeasureTheory Set

namespace RHTower.Sieve

noncomputable section

/-- Pole-cancelled low-frequency localization with source base `M` frozen independently of the
physical Mellin base `N`. -/
theorem norm_intervalIntegral_fixedSource_mul_normalizedKernelDefect_le_fixedPolylog
    (L X k : ℕ) (hX : 1 ≤ X) (T0 t M N H R U : ℝ)
    (hM : 0 < M) (hN : 0 < N) (hH : 0 < H) (hR : 0 < R) (hHR : H ≤ R)
    (hU : 0 ≤ U) (hsmall : U * (2 * R / N) ≤ 1) :
    ‖∫ y in (-U)..U,
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t M
          ((1 : ℂ) + (y : ℝ) * Complex.I) *
        (routeTNormalizedSmoothWindowMellin N R
            ((1 : ℂ) + (y : ℝ) * Complex.I) -
          routeTNormalizedSmoothWindowMellin N H
            ((1 : ℂ) + (y : ℝ) * Complex.I))‖ ≤
      16 * heathBrownWindowRelevantFixedPolylogBound L X k M 1 *
        (R / N) * U ^ 2 := by
  let P : ℝ := heathBrownWindowRelevantFixedPolylogBound L X k M 1
  have hA : ∀ y : ℝ,
      ‖heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t M
          ((1 : ℂ) + (y : ℝ) * Complex.I)‖ ≤ P := by
    intro y
    exact norm_heathBrownWindowRelevantEligibleDyadicAggregate_le_fixedPolylog
      L X k hX T0 t M 1 y hM (by norm_num)
  have hP : 0 ≤ P := (norm_nonneg _).trans (hA 0)
  have hpoint : ∀ y ∈ Set.uIoc (-U) U,
      ‖heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t M
          ((1 : ℂ) + (y : ℝ) * Complex.I) *
        (routeTNormalizedSmoothWindowMellin N R
            ((1 : ℂ) + (y : ℝ) * Complex.I) -
          routeTNormalizedSmoothWindowMellin N H
            ((1 : ℂ) + (y : ℝ) * Complex.I))‖ ≤
        P * (8 * U * (R / N)) := by
    intro y hy
    have hyIoc : y ∈ Set.Ioc (-U) U := by
      simpa [Set.uIoc_of_le (by linarith : -U ≤ U)] using hy
    have hyabs : |y| ≤ U := abs_le.mpr ⟨hyIoc.1.le, hyIoc.2⟩
    let s : ℂ := (1 : ℂ) + (y : ℝ) * Complex.I
    have hsre : 0 < s.re := by simp [s]
    have hsnorm : ‖s - 1‖ = |y| := by
      simp [s]
    have hsmallY : ‖s - 1‖ * (2 * R / N) ≤ 1 := by
      rw [hsnorm]
      exact (mul_le_mul_of_nonneg_right hyabs (by positivity : 0 ≤ 2 * R / N)).trans hsmall
    have hkernel := norm_routeTNormalizedSmoothWindowMellin_sub_le_reference
      hN hH hR hHR hsre hsmallY
    have hkernel' :
        ‖routeTNormalizedSmoothWindowMellin N R s -
            routeTNormalizedSmoothWindowMellin N H s‖ ≤
          8 * U * (R / N) := by
      rw [show s.re = 1 by simp [s], sub_self, Real.rpow_zero, mul_one, hsnorm] at hkernel
      exact hkernel.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hyabs (by norm_num : (0 : ℝ) ≤ 8))
        (by positivity))
    rw [norm_mul]
    exact mul_le_mul (hA y) hkernel' (norm_nonneg _) hP
  have hinterval := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  rw [abs_of_nonneg (by linarith : 0 ≤ U - -U)] at hinterval
  dsimp only [P] at hinterval ⊢
  convert hinterval using 1 <;> ring

/-- A full fixed-source adjacent defect localizes to a literal annulus while retaining arbitrary
Mellin order and keeping source base `M` independent of physical base `N`. -/
theorem exists_norm_setIntegral_fixedSource_mul_adjacentKernel_natOrder_annulus_ge
    (j : ℕ) (hj : 1 ≤ j) :
    ∃ Cj : ℝ, 1 ≤ Cj ∧
      ∀ (L X k : ℕ) (T0 t : ℝ) {M N H R U V B : ℝ},
        1 ≤ X → 0 < M → 1 ≤ N → 0 < H → 0 < R →
        H ≤ R → R ≤ 2 * H → R ≤ N →
        0 ≤ U → U ≤ V → 0 < V → U * (2 * R / N) ≤ 1 →
        B ≤ ‖∫ y : ℝ,
          heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t M
                ((1 : ℂ) + (y : ℝ) * Complex.I) *
            (routeTNormalizedSmoothWindowMellin N R
                ((1 : ℂ) + (y : ℝ) * Complex.I) -
              routeTNormalizedSmoothWindowMellin N H
                ((1 : ℂ) + (y : ℝ) * Complex.I))‖ →
        B - 16 * heathBrownWindowRelevantFixedPolylogBound L X k M 1 *
              (R / N) * U ^ 2 -
            heathBrownWindowRelevantFixedPolylogBound L X k M 1 *
              (Cj * (N / R) ^ (j + 1) * V ^ (-(j : ℝ))) ≤
          ‖∫ y in {y : ℝ | U ≤ |y| ∧ |y| < V},
            heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t M
                  ((1 : ℂ) + (y : ℝ) * Complex.I) *
              (routeTNormalizedSmoothWindowMellin N R
                  ((1 : ℂ) + (y : ℝ) * Complex.I) -
                routeTNormalizedSmoothWindowMellin N H
                  ((1 : ℂ) + (y : ℝ) * Complex.I))‖ := by
  obtain ⟨Cj, hCj, htail⟩ :=
    exists_integral_norm_fixedSource_mul_adjacentKernel_natOrder_tail_le j hj
  refine ⟨Cj, hCj, ?_⟩
  intro L X k T0 t M N H R U V B hX hM hN hH hR hHR hRH hRN hU hUV hV
    hsmall hfull
  let f : ℝ → ℂ := fun y =>
    heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t M
          ((1 : ℂ) + (y : ℝ) * Complex.I) *
      (routeTNormalizedSmoothWindowMellin N R
          ((1 : ℂ) + (y : ℝ) * Complex.I) -
        routeTNormalizedSmoothWindowMellin N H
          ((1 : ℂ) + (y : ℝ) * Complex.I))
  let P : ℝ := heathBrownWindowRelevantFixedPolylogBound L X k M 1
  have hsourceBound : ∀ y : ℝ,
      ‖heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t M
        ((1 : ℂ) + (y : ℝ) * Complex.I)‖ ≤ P := by
    intro y
    exact norm_heathBrownWindowRelevantEligibleDyadicAggregate_le_fixedPolylog
      L X k hX T0 t M 1 y hM (by norm_num)
  have hsourceCont : Continuous (fun y : ℝ =>
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t M
        ((1 : ℂ) + (y : ℝ) * Complex.I)) :=
    continuous_heathBrownWindowRelevantEligibleDyadicAggregate_line
      L X k T0 t M 1
  have hkint : Integrable (fun y : ℝ =>
      routeTNormalizedSmoothWindowMellin N R
          ((1 : ℂ) + (y : ℝ) * Complex.I) -
        routeTNormalizedSmoothWindowMellin N H
          ((1 : ℂ) + (y : ℝ) * Complex.I)) :=
    (integrable_routeTNormalizedSmoothWindowMellin_one (zero_lt_one.trans_le hN) hR).sub
      (integrable_routeTNormalizedSmoothWindowMellin_one (zero_lt_one.trans_le hN) hH)
  have hf : Integrable f := by
    exact hkint.bdd_mul hsourceCont.aestronglyMeasurable
      (Filter.Eventually.of_forall hsourceBound)
  have hlow :=
    norm_intervalIntegral_fixedSource_mul_normalizedKernelDefect_le_fixedPolylog
      L X k hX T0 t M N H R U hM (zero_lt_one.trans_le hN) hH hR hHR hU hsmall
  have hfar := htail L X k T0 t hX hM hN hH hR hHR hRH hRN hV
  exact norm_setIntegral_annulus_ge_of_low_tail hf hU hUV
    (by simpa only [f] using hfull)
    (by simpa only [f, P] using hlow)
    (by simpa only [f, P] using hfar)

end

end RHTower.Sieve
