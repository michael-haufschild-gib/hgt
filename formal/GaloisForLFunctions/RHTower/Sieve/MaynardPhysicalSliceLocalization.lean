import GaloisForLFunctions.RHTower.Sieve.MaynardPhysicalSliceCellReceiver
import GaloisForLFunctions.RHTower.Sieve.MaynardAdjacentAggregateReflection

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction Complex MeasureTheory Set Filter

/-- Complete Route-T adjacent defect, from the multiscale window-relevant aggregate directly to
the literal physical von Mangoldt slice. -/
theorem integral_windowRelevant_mul_adjacentNormalizedMellin_eq_physicalSlice
    (L X k : ℕ) (hXL : X < (L + 1) ^ k) {T0 t N H R : ℝ}
    (hT0 : 1 < T0)
    (hscale : ((2 ^ (2 * k) : ℕ) : ℝ) * T0 ^ t ≤ N)
    (hN : 0 < N) (hH : 0 < H) (hR : 0 < R) (hHR : H ≤ R)
    (hsupportR : N + 2 * R ≤ X) :
    (∫ y : ℝ,
      heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t N
          ((1 : ℂ) + (y : ℝ) * I) *
        (routeTNormalizedSmoothWindowMellin N R
            ((1 : ℂ) + (y : ℝ) * I) -
          routeTNormalizedSmoothWindowMellin N H
            ((1 : ℂ) + (y : ℝ) * I))) =
      ∫ y : ℝ,
        dirPoly ⌊N + 2 * R⌋₊
            (routeTVonMangoldtSliceCoeff ⌊N⌋₊ ⌊N + 2 * R⌋₊) (-y) *
          (routeTNormalizedSmoothWindowMellin N R
              ((1 : ℂ) + (y : ℝ) * I) -
            routeTNormalizedSmoothWindowMellin N H
              ((1 : ℂ) + (y : ℝ) * I)) := by
  exact (integral_windowRelevant_mul_adjacentNormalizedMellin_eq_observed
    L X k T0 t N R hN hH hR hHR (by norm_num)).trans
      (integral_observed_mul_adjacentNormalizedMellin_eq_physicalSlice
        L X k hXL hT0 hscale hN hH hR hHR hsupportR)

theorem integrable_physicalSlice_mul_adjacentNormalizedMellin
    {A B : ℕ} (hA : 1 ≤ A) {N H R : ℝ}
    (hN : 0 < N) (hH : 0 < H) (hR : 0 < R) :
    Integrable (fun y : ℝ =>
      dirPoly B (routeTVonMangoldtSliceCoeff A B) (-y) *
        (routeTNormalizedSmoothWindowMellin N R
            ((1 : ℂ) + (y : ℝ) * I) -
          routeTNormalizedSmoothWindowMellin N H
            ((1 : ℂ) + (y : ℝ) * I))) := by
  let F : ℝ → ℂ := fun y =>
    dirPoly B (routeTVonMangoldtSliceCoeff A B) (-y)
  let K : ℝ → ℂ := fun y =>
    routeTNormalizedSmoothWindowMellin N R ((1 : ℂ) + (y : ℝ) * I) -
      routeTNormalizedSmoothWindowMellin N H ((1 : ℂ) + (y : ℝ) * I)
  have hFc : Continuous F :=
    (continuous_dirPoly B (routeTVonMangoldtSliceCoeff A B)).comp continuous_neg
  have hKint : Integrable K :=
    (integrable_routeTNormalizedSmoothWindowMellin_one hN hR).sub
      (integrable_routeTNormalizedSmoothWindowMellin_one hN hH)
  have hFbound : ∀ y : ℝ, ‖F y‖ ≤ (B : ℝ) * (Real.log B / A) := by
    intro y
    exact norm_dirPoly_routeTVonMangoldtSliceCoeff_le hA (-y)
  exact hKint.bdd_mul hFc.aestronglyMeasurable
    (Filter.Eventually.of_forall hFbound)

theorem norm_intervalIntegral_physicalSlice_mul_adjacentKernel_low_le
    {A B : ℕ} (hA : 1 ≤ A) {N H R U : ℝ}
    (hN : 0 < N) (hH : 0 < H) (hR : 0 < R) (hHR : H ≤ R)
    (hU : 0 ≤ U) (hsmall : U * (2 * R / N) ≤ 1) :
    ‖∫ y in (-U)..U,
      dirPoly B (routeTVonMangoldtSliceCoeff A B) (-y) *
        (routeTNormalizedSmoothWindowMellin N R
            ((1 : ℂ) + (y : ℝ) * I) -
          routeTNormalizedSmoothWindowMellin N H
            ((1 : ℂ) + (y : ℝ) * I))‖ ≤
      16 * ((B : ℝ) * (Real.log B / A)) * (R / N) * U ^ (2 : ℕ) := by
  let P : ℝ := (B : ℝ) * (Real.log B / A)
  have hP : 0 ≤ P :=
    (norm_nonneg (dirPoly B (routeTVonMangoldtSliceCoeff A B) 0)).trans
      (norm_dirPoly_routeTVonMangoldtSliceCoeff_le (B := B) hA 0)
  have hpoint : ∀ y ∈ Set.uIoc (-U) U,
      ‖dirPoly B (routeTVonMangoldtSliceCoeff A B) (-y) *
        (routeTNormalizedSmoothWindowMellin N R
            ((1 : ℂ) + (y : ℝ) * I) -
          routeTNormalizedSmoothWindowMellin N H
            ((1 : ℂ) + (y : ℝ) * I))‖ ≤
        P * (8 * U * (R / N)) := by
    intro y hy
    have hyIoc : y ∈ Set.Ioc (-U) U := by
      simpa [Set.uIoc_of_le (by linarith : -U ≤ U)] using hy
    have hyabs : |y| ≤ U := abs_le.mpr ⟨hyIoc.1.le, hyIoc.2⟩
    let s : ℂ := (1 : ℂ) + (y : ℝ) * I
    have hsre : s.re = 1 := by simp [s]
    have hsnorm : ‖s - 1‖ = |y| := by simp [s, Real.norm_eq_abs]
    have hsmallY : ‖s - 1‖ * (2 * R / N) ≤ 1 := by
      rw [hsnorm]
      exact (mul_le_mul_of_nonneg_right hyabs (by positivity)).trans hsmall
    have hkernel := norm_routeTNormalizedSmoothWindowMellin_sub_le_reference
      hN hH hR hHR (by simpa [hsre]) hsmallY
    norm_num [hsre, hsnorm] at hkernel
    rw [norm_mul]
    exact mul_le_mul
      (norm_dirPoly_routeTVonMangoldtSliceCoeff_le hA (-y))
      (hkernel.trans (by
        have hfac : (0 : ℝ) ≤ 8 * (R / N) := by positivity
        nlinarith)) (norm_nonneg _) hP
  have hinterval := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  rw [abs_of_nonneg (by linarith : 0 ≤ U - -U)] at hinterval
  dsimp only [P] at hinterval ⊢
  convert hinterval using 1 <;> ring

theorem exists_integral_norm_physicalSlice_mul_adjacentKernel_tail_le :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {A B : ℕ}, 1 ≤ A → ∀ {N H R U : ℝ},
        0 < N → 0 < H → 0 < R → H ≤ R → R ≤ 2 * H → R ≤ N → 0 < U →
        (∫ y in {y : ℝ | U ≤ |y|},
          ‖dirPoly B (routeTVonMangoldtSliceCoeff A B) (-y) *
            (routeTNormalizedSmoothWindowMellin N R
                ((1 : ℂ) + (y : ℝ) * I) -
              routeTNormalizedSmoothWindowMellin N H
                ((1 : ℂ) + (y : ℝ) * I))‖) ≤
          ((B : ℝ) * (Real.log B / A)) *
            (130 * C * (N / R) ^ (2 : ℕ) / U) := by
  obtain ⟨C, hC, htail⟩ :=
    exists_integral_routeTAdjacentNormalizedKernel_one_general_tail_le
  refine ⟨C, hC, ?_⟩
  intro A B hA N H R U hN hH hR hHR hRH hRN hU
  let F : ℝ → ℂ := fun y =>
    dirPoly B (routeTVonMangoldtSliceCoeff A B) (-y)
  let K : ℝ → ℂ := fun y =>
    routeTNormalizedSmoothWindowMellin N R ((1 : ℂ) + (y : ℝ) * I) -
      routeTNormalizedSmoothWindowMellin N H ((1 : ℂ) + (y : ℝ) * I)
  let P : ℝ := (B : ℝ) * (Real.log B / A)
  have hKint : Integrable (fun y => ‖K y‖) := by
    exact ((integrable_routeTNormalizedSmoothWindowMellin_one hN hR).sub
      (integrable_routeTNormalizedSmoothWindowMellin_one hN hH)).norm
  have hprod : Integrable (fun y => ‖F y * K y‖) :=
    (integrable_physicalSlice_mul_adjacentNormalizedMellin hA hN hH hR).norm
  have hP : 0 ≤ P := (norm_nonneg (F 0)).trans (by
    simpa only [F, neg_zero] using
      norm_dirPoly_routeTVonMangoldtSliceCoeff_le (B := B) hA 0)
  have hmono : (∫ y in {y : ℝ | U ≤ |y|}, ‖F y * K y‖) ≤
      ∫ y in {y : ℝ | U ≤ |y|}, P * ‖K y‖ := by
    apply setIntegral_mono_on hprod.integrableOn
      (hKint.const_mul P).integrableOn
        (measurableSet_le measurable_const continuous_abs.measurable)
    intro y _hy
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (norm_dirPoly_routeTVonMangoldtSliceCoeff_le hA (-y)) (norm_nonneg _)
  have hscale : (∫ y in {y : ℝ | U ≤ |y|}, P * ‖K y‖) =
      P * ∫ y in {y : ℝ | U ≤ |y|}, ‖K y‖ := by
    rw [MeasureTheory.integral_const_mul]
  have hfar := htail N H R U hN hH hR hHR hRH hRN hU
  calc
    (∫ y in {y : ℝ | U ≤ |y|},
        ‖dirPoly B (routeTVonMangoldtSliceCoeff A B) (-y) *
          (routeTNormalizedSmoothWindowMellin N R
              ((1 : ℂ) + (y : ℝ) * I) -
            routeTNormalizedSmoothWindowMellin N H
              ((1 : ℂ) + (y : ℝ) * I))‖) =
        ∫ y in {y : ℝ | U ≤ |y|}, ‖F y * K y‖ := by rfl
    _ ≤ ∫ y in {y : ℝ | U ≤ |y|}, P * ‖K y‖ := hmono
    _ = P * ∫ y in {y : ℝ | U ≤ |y|}, ‖K y‖ := hscale
    _ ≤ P * (130 * C * (N / R) ^ (2 : ℕ) / U) :=
      mul_le_mul_of_nonneg_left (by simpa only [K] using hfar) hP
    _ = _ := by rfl

theorem conj_physicalSlice_mul_adjacentKernel
    (A B : ℕ) (N H R y : ℝ) :
    dirPoly B (routeTVonMangoldtSliceCoeff A B) (-(-y)) *
        (routeTNormalizedSmoothWindowMellin N R
            ((1 : ℂ) + ((-y : ℝ) : ℂ) * I) -
          routeTNormalizedSmoothWindowMellin N H
            ((1 : ℂ) + ((-y : ℝ) : ℂ) * I)) =
      (starRingEnd ℂ)
        (dirPoly B (routeTVonMangoldtSliceCoeff A B) (-y) *
          (routeTNormalizedSmoothWindowMellin N R
              ((1 : ℂ) + (y : ℝ) * I) -
            routeTNormalizedSmoothWindowMellin N H
              ((1 : ℂ) + (y : ℝ) * I))) := by
  have hpoly := dirPoly_conj_neg B (routeTVonMangoldtSliceCoeff A B) y
  simp only [conj_routeTVonMangoldtSliceCoeff] at hpoly
  rw [map_mul, map_sub, ← hpoly,
    conj_routeTNormalizedSmoothWindowMellin,
    conj_routeTNormalizedSmoothWindowMellin]
  congr 1 <;> simp

/-- Full signed physical-slice mass, after explicit low and far-tail costs, survives on one
positive central or outer wing. -/
theorem exists_positive_interval_norm_ge_quarter_of_physicalSlice_annulus :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {A B : ℕ}, 1 ≤ A → ∀ {N H R D U T V : ℝ},
        0 < N → 0 < H → 0 < R → H ≤ R → R ≤ 2 * H → R ≤ N →
        0 ≤ U → U ≤ T → T ≤ V → 0 < V → U * (2 * R / N) ≤ 1 →
        D ≤ ‖∫ y : ℝ,
          dirPoly B (routeTVonMangoldtSliceCoeff A B) (-y) *
            (routeTNormalizedSmoothWindowMellin N R
                ((1 : ℂ) + (y : ℝ) * I) -
              routeTNormalizedSmoothWindowMellin N H
                ((1 : ℂ) + (y : ℝ) * I))‖ →
        let E := D -
          16 * ((B : ℝ) * (Real.log B / A)) * (R / N) * U ^ (2 : ℕ) -
          ((B : ℝ) * (Real.log B / A)) *
            (130 * C * (N / R) ^ (2 : ℕ) / V)
        E / 4 ≤ ‖∫ y in U..T,
          dirPoly B (routeTVonMangoldtSliceCoeff A B) (-y) *
            (routeTNormalizedSmoothWindowMellin N R
                ((1 : ℂ) + (y : ℝ) * I) -
              routeTNormalizedSmoothWindowMellin N H
                ((1 : ℂ) + (y : ℝ) * I))‖ ∨
        E / 4 ≤ ‖∫ y in T..V,
          dirPoly B (routeTVonMangoldtSliceCoeff A B) (-y) *
            (routeTNormalizedSmoothWindowMellin N R
                ((1 : ℂ) + (y : ℝ) * I) -
              routeTNormalizedSmoothWindowMellin N H
                ((1 : ℂ) + (y : ℝ) * I))‖ := by
  obtain ⟨C, hC, htail⟩ :=
    exists_integral_norm_physicalSlice_mul_adjacentKernel_tail_le
  refine ⟨C, hC, ?_⟩
  intro A B hA N H R D U T V hN hH hR hHR hRH hRN hU hUT hTV hV hsmall hfull
  let f : ℝ → ℂ := fun y =>
    dirPoly B (routeTVonMangoldtSliceCoeff A B) (-y) *
      (routeTNormalizedSmoothWindowMellin N R
          ((1 : ℂ) + (y : ℝ) * I) -
        routeTNormalizedSmoothWindowMellin N H
          ((1 : ℂ) + (y : ℝ) * I))
  let E : ℝ := D -
    16 * ((B : ℝ) * (Real.log B / A)) * (R / N) * U ^ (2 : ℕ) -
    ((B : ℝ) * (Real.log B / A)) *
      (130 * C * (N / R) ^ (2 : ℕ) / V)
  change E / 4 ≤ ‖∫ y in U..T,
      dirPoly B (routeTVonMangoldtSliceCoeff A B) (-y) *
        (routeTNormalizedSmoothWindowMellin N R
            ((1 : ℂ) + (y : ℝ) * I) -
          routeTNormalizedSmoothWindowMellin N H
            ((1 : ℂ) + (y : ℝ) * I))‖ ∨
    E / 4 ≤ ‖∫ y in T..V,
      dirPoly B (routeTVonMangoldtSliceCoeff A B) (-y) *
        (routeTNormalizedSmoothWindowMellin N R
            ((1 : ℂ) + (y : ℝ) * I) -
          routeTNormalizedSmoothWindowMellin N H
            ((1 : ℂ) + (y : ℝ) * I))‖
  have hf : Integrable f :=
    integrable_physicalSlice_mul_adjacentNormalizedMellin hA hN hH hR
  have hlow := norm_intervalIntegral_physicalSlice_mul_adjacentKernel_low_le
    (B := B) hA hN hH hR hHR hU hsmall
  have hfar := htail (A := A) (B := B) hA
    (N := N) (H := H) (R := R) (U := V) hN hH hR hHR hRH hRN hV
  have hannulus : E ≤ ‖∫ y in {y : ℝ | U ≤ |y| ∧ |y| < V}, f y‖ := by
    exact norm_setIntegral_annulus_ge_of_low_tail hf hU (hUT.trans hTV)
      (by simpa only [f] using hfull)
      (by simpa only [f, E] using hlow)
      (by simpa only [f, E] using hfar)
  have hconj : ∀ y : ℝ, f (-y) = (starRingEnd ℂ) (f y) := by
    intro y
    exact conj_physicalSlice_mul_adjacentKernel A B N H R y
  simpa only [f, E] using
    exists_positive_interval_norm_ge_quarter_of_annulus_of_conj
      hf hconj hU hUT hTV hannulus

end RHTower.Sieve
