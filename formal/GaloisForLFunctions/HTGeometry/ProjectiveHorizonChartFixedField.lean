import GaloisForLFunctions.HTGeometry.ProjectiveHorizonAffineJetIndependence
import GaloisForLFunctions.HTGeometry.FreeJetTranslationFixedField

/-!
# The exact chart horizon field

Because the affine chart jets are algebraically independent, the free rational jet field on the
chart index embeds onto the projective jet field of that chart.  Under the embedding the chart
unipotent group acts by independent translations of the zeroth-order coordinates, so the
translation fixed-field theorem transports and identifies the observer-invariant part of the chart
field with the positive-order tail.

This is the reverse inclusion of the chart horizon law: `mathcal H_(ker e_i^*)` is exactly the part
of the chart field invariant under `U_(ker e_i^*)`.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-- Index type of the affine coordinates of the chart at `i`. -/
abbrev ChartIndex (i : n) := {k : n // k ≠ i}

omit [Fintype n] [DecidableEq n] in
/-- The chart coordinate of the chart's own direction is constant. -/
theorem affineJet_self (i : n) (l : ℕ) :
    affineJet (K := K) i i l = if l = 0 then 1 else 0 := by
  induction l with
  | zero => simpa using affineCoord_self i
  | succ l ih =>
      rw [affineJet_succ, ih]
      rcases eq_or_ne l 0 with rfl | hl
      · simp [Derivation.map_one_eq_zero]
      · simp [hl]

/-! ## The chart model embedding -/

/-- Evaluation of the free chart model at the affine chart jets. -/
def chartEvalPoly (i : n) :
    MvPolynomial (ChartIndex i × ℕ) K →ₐ[K] HomogeneousJetField n K :=
  MvPolynomial.aeval fun p : ChartIndex i × ℕ => affineJet i p.1.1 p.2

omit [Fintype n] [DecidableEq n] in
@[simp]
theorem chartEvalPoly_X (i : n) (p : ChartIndex i × ℕ) :
    chartEvalPoly (K := K) i (MvPolynomial.X p) = affineJet i p.1.1 p.2 := by
  simp [chartEvalPoly]

omit [Fintype n] in
theorem chartEvalPoly_injective (i : n) :
    Function.Injective (chartEvalPoly (K := K) i) :=
  algebraicIndependent_affineJet i

/-- The free chart model field, embedded in the homogeneous jet field. -/
def chartEval (i : n) :
    FreeCoordinateRationalField K (ChartIndex i × ℕ) →ₐ[K] HomogeneousJetField n K :=
  { IsFractionRing.lift (chartEvalPoly_injective (K := K) i) with
    commutes' := fun c => by
      show IsFractionRing.lift (chartEvalPoly_injective (K := K) i)
        (algebraMap K (FreeCoordinateRationalField K (ChartIndex i × ℕ)) c) = _
      rw [IsScalarTower.algebraMap_apply K (MvPolynomial (ChartIndex i × ℕ) K)
          (FreeCoordinateRationalField K (ChartIndex i × ℕ)),
        IsFractionRing.lift_algebraMap]
      exact (chartEvalPoly i).commutes c }

omit [Fintype n] in
@[simp]
theorem chartEval_algebraMap (i : n) (p : MvPolynomial (ChartIndex i × ℕ) K) :
    chartEval i (algebraMap (MvPolynomial (ChartIndex i × ℕ) K)
        (FreeCoordinateRationalField K (ChartIndex i × ℕ)) p) = chartEvalPoly i p :=
  IsFractionRing.lift_algebraMap (chartEvalPoly_injective (K := K) i) p

omit [Fintype n] in
@[simp]
theorem chartEval_freeCoordinate (i : n) (p : ChartIndex i × ℕ) :
    chartEval (K := K) i (freeCoordinate K (ChartIndex i × ℕ) p) = affineJet i p.1.1 p.2 := by
  rw [freeCoordinate, chartEval_algebraMap, chartEvalPoly_X]

omit [Fintype n] in
theorem chartEval_injective (i : n) : Function.Injective (chartEval (K := K) i) :=
  (chartEval (K := K) i).toRingHom.injective

/-! ## The chart field is the image of the model -/

omit [Fintype n] [DecidableEq n] in
theorem chartEvalPoly_mem_projectiveJetField (i : n)
    (p : MvPolynomial (ChartIndex i × ℕ) K) :
    chartEvalPoly (K := K) i p ∈ projectiveJetField i K := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
      exact (projectiveJetField i K).algebraMap_mem c
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p q hp =>
      rw [map_mul, chartEvalPoly_X]
      exact mul_mem hp (affineJet_mem_projectiveJetField i q.1.1 q.2)

omit [Fintype n] in
theorem chartEval_mem_projectiveJetField (i : n)
    (z : FreeCoordinateRationalField K (ChartIndex i × ℕ)) :
    chartEval i z ∈ projectiveJetField i K := by
  obtain ⟨a, b, _, rfl⟩ :=
    IsFractionRing.div_surjective (A := MvPolynomial (ChartIndex i × ℕ) K) z
  rw [map_div₀, chartEval_algebraMap, chartEval_algebraMap]
  exact div_mem (chartEvalPoly_mem_projectiveJetField i a)
    (chartEvalPoly_mem_projectiveJetField i b)

omit [Fintype n] in
theorem exists_chartEval_of_mem_projectiveJetField (i : n)
    {f : HomogeneousJetField n K} (hf : f ∈ projectiveJetField i K) :
    ∃ z, chartEval (K := K) i z = f := by
  have hrange : projectiveJetField i K ≤ (chartEval (K := K) i).fieldRange := by
    rw [projectiveJetField, IntermediateField.adjoin_le_iff]
    rintro _ ⟨k, l, rfl⟩
    by_cases hk : k = i
    · rw [hk, affineJet_self]
      split
      · exact (chartEval (K := K) i).fieldRange.one_mem
      · exact (chartEval (K := K) i).fieldRange.zero_mem
    · exact ⟨freeCoordinate K (ChartIndex i × ℕ) (⟨k, hk⟩, l),
        chartEval_freeCoordinate i (⟨k, hk⟩, l)⟩
  exact hrange hf

/-! ## Transport of the chart unipotent translation -/

/-- The unimodular matrix realising the unit translation of the `k`-th affine coordinate. -/
def chartUnitTranslation {i k : n} (hk : k ≠ i) : SpecialLinearGroup n K :=
  transvectionSL k i hk (-1 : K)

theorem chartUnitTranslation_mem {i k : n} (hk : k ≠ i) :
    chartUnitTranslation (K := K) hk ∈ chartSubsetStabilizer (K := K) {i} :=
  transvectionSL_mem_chartSubsetStabilizer (s := {i}) (Set.mem_singleton i) hk (-1 : K)

theorem chartUnitTranslation_inv_apply {i k : n} (hk : k ≠ i) (m : n) (hm : m ≠ i) :
    (((chartUnitTranslation (K := K) hk)⁻¹ : SpecialLinearGroup n K) : Matrix n n K) m i =
      if m = k then 1 else 0 := by
  have hinv : ((chartUnitTranslation (K := K) hk)⁻¹ : SpecialLinearGroup n K) =
      transvectionSL k i hk 1 := by
    refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
    show Matrix.transvection k i (-1 : K) * Matrix.transvection k i 1 = 1
    rw [Matrix.transvection_mul_transvection_same _ _ hk]
    simp
  rw [hinv]
  show Matrix.transvection k i (1 : K) m i = _
  rw [Matrix.transvection]
  rcases eq_or_ne m k with rfl | hmk
  · simp [Matrix.one_apply_ne hm]
  · simp [Matrix.one_apply_ne hm, hmk, Ne.symm hmk]

theorem linearJetAction_affineJet_chartUnitTranslation {i k : n} (hk : k ≠ i)
    (q : ChartIndex i × ℕ) :
    (chartUnitTranslation (K := K) hk) • affineJet i q.1.1 q.2 =
      affineJet i q.1.1 q.2 +
        algebraMap K (HomogeneousJetField n K) (if q = (⟨k, hk⟩, 0) then 1 else 0) := by
  obtain ⟨⟨m, hm⟩, l⟩ := q
  cases l with
  | zero =>
      rw [affineJet_zero,
        linearJetAction_affineCoord_of_mem hm (chartUnitTranslation_mem hk),
        chartUnitTranslation_inv_apply hk m hm]
      congr 2
      by_cases hmk : m = k
      · subst hmk; simp
      · simp [hmk, Subtype.ext_iff]
  | succ l =>
      rw [linearJetAction_affineJet_succ_of_mem hm l (chartUnitTranslation_mem hk)]
      simp

theorem chartEval_translation {i k : n} (hk : k ≠ i)
    (z : FreeCoordinateRationalField K (ChartIndex i × ℕ)) :
    chartEval i (freeCoordinateTranslationAt K (ChartIndex i × ℕ) (⟨k, hk⟩, 0) 1 z) =
      (chartUnitTranslation (K := K) hk) • chartEval i z := by
  classical
  have hgen : ∀ q : ChartIndex i × ℕ,
      chartEval i (freeCoordinateTranslationAt K (ChartIndex i × ℕ) (⟨k, hk⟩, 0) 1
          (freeCoordinate K (ChartIndex i × ℕ) q)) =
        (chartUnitTranslation (K := K) hk) •
          chartEval i (freeCoordinate K (ChartIndex i × ℕ) q) := by
    intro q
    rw [chartEval_freeCoordinate, linearJetAction_affineJet_chartUnitTranslation hk]
    rcases eq_or_ne q (⟨k, hk⟩, 0) with rfl | hq
    · rw [freeCoordinateTranslationAt_self, map_add, chartEval_freeCoordinate,
        AlgHom.commutes, if_pos rfl]
    · rw [freeCoordinateTranslationAt_of_ne hq, chartEval_freeCoordinate, if_neg hq,
        map_zero, add_zero]
  have hL : ((chartEval (K := K) i).comp
      (((freeCoordinateTranslationAt K (ChartIndex i × ℕ) (⟨k, hk⟩, 0) 1).toAlgHom).comp
        (IsScalarTower.toAlgHom K (MvPolynomial (ChartIndex i × ℕ) K)
          (FreeCoordinateRationalField K (ChartIndex i × ℕ))))) =
      (((linearJetFieldEquiv (chartUnitTranslation (K := K) hk)).toAlgHom).comp
        ((chartEval (K := K) i).comp
          (IsScalarTower.toAlgHom K (MvPolynomial (ChartIndex i × ℕ) K)
            (FreeCoordinateRationalField K (ChartIndex i × ℕ))))) := by
    apply MvPolynomial.algHom_ext
    intro q
    show chartEval i (freeCoordinateTranslationAt K (ChartIndex i × ℕ) (⟨k, hk⟩, 0) 1
        (freeCoordinate K (ChartIndex i × ℕ) q)) =
      (chartUnitTranslation (K := K) hk) • chartEval i (freeCoordinate K (ChartIndex i × ℕ) q)
    exact hgen q
  have hpoly : ∀ p : MvPolynomial (ChartIndex i × ℕ) K,
      chartEval i (freeCoordinateTranslationAt K (ChartIndex i × ℕ) (⟨k, hk⟩, 0) 1
          (algebraMap (MvPolynomial (ChartIndex i × ℕ) K)
            (FreeCoordinateRationalField K (ChartIndex i × ℕ)) p)) =
        (chartUnitTranslation (K := K) hk) •
          chartEval i (algebraMap (MvPolynomial (ChartIndex i × ℕ) K)
            (FreeCoordinateRationalField K (ChartIndex i × ℕ)) p) := by
    intro p
    exact AlgHom.congr_fun hL p
  obtain ⟨a, b, _, rfl⟩ :=
    IsFractionRing.div_surjective (A := MvPolynomial (ChartIndex i × ℕ) K) z
  rw [map_div₀, map_div₀, hpoly, hpoly]
  simp only [linearJetAction_apply, map_div₀]

/-! ## The exact chart horizon field -/

/-- **Exact chart horizon law.**  Inside the projective jet field of the chart at `i`, the elements
invariant under the observer group of `ker e_i^*` are exactly the positive-order affine jets.  This
is the reverse inclusion of `mathcal H_(ker e_i^*) = F^(U_(ker e_i^*))`. -/
theorem mem_chartTailField_of_mem_horizonField [CharZero K] (i : n)
    {f : HomogeneousJetField n K} (hmem : f ∈ projectiveJetField i K)
    (hfix : ∀ g ∈ chartSubsetStabilizer (K := K) {i}, g • f = f) :
    f ∈ chartTailField i K := by
  classical
  obtain ⟨z, rfl⟩ := exists_chartEval_of_mem_projectiveJetField i hmem
  have hz : z ∈ freeCoordinateTailField K (ChartIndex i) 1 := by
    rw [mem_freeCoordinateTailField_iff]
    rintro ⟨k, hk⟩ m hm
    have hm0 : m = 0 := by omega
    subst hm0
    have hfixed : freeCoordinateTranslationAt K (ChartIndex i × ℕ) (⟨k, hk⟩, 0) 1 z = z := by
      apply chartEval_injective i
      rw [chartEval_translation hk]
      exact hfix _ (chartUnitTranslation_mem hk)
    have hcompl :=
      mem_freeCoordinateField_complement_of_unitTranslation_fixed
        (C := K) (σ := ChartIndex i × ℕ) (⟨k, hk⟩, 0) hfixed
    exact (mem_freeCoordinateField_iff ({((⟨k, hk⟩, 0) : ChartIndex i × ℕ)}ᶜ) z).1 hcompl
      (⟨k, hk⟩, 0) (by simp)
  have himg : ∀ w ∈ freeCoordinateTailField K (ChartIndex i) 1,
      chartEval (K := K) i w ∈ chartTailField i K := by
    intro w hw
    refine IntermediateField.adjoin_induction K
      (s := freeCoordinate K (ChartIndex i × ℕ) '' {j | 1 ≤ j.2})
      (p := fun y _ => chartEval (K := K) i y ∈ chartTailField i K) ?_ ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨⟨⟨m, hm⟩, l⟩, hl, rfl⟩
      simp only [Set.mem_setOf_eq] at hl
      rw [chartEval_freeCoordinate]
      obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
      exact IntermediateField.subset_adjoin K _ ⟨m, hm, l', rfl⟩
    · intro c
      rw [AlgHom.commutes]
      exact (chartTailField i K).algebraMap_mem c
    · intro x y _ _ hx hy
      rw [map_add]
      exact add_mem hx hy
    · intro x _ hx
      rw [map_inv₀]
      exact inv_mem hx
    · intro x y _ _ hx hy
      rw [map_mul]
      exact mul_mem hx hy
  exact himg z hz

/-- **Chart horizon law.**  Inside the projective jet field of the chart at `i`, the derivative
horizon `mathcal H_(ker e_i^*)` and the observer fixed field `mathcal I_({e_i^*})` agree. -/
theorem mem_chartTailField_iff_mem_horizonField [CharZero K] (i : n)
    {f : HomogeneousJetField n K} (hmem : f ∈ projectiveJetField i K) :
    f ∈ chartTailField i K ↔ f ∈ horizonField (K := K) {i} :=
  ⟨fun hf => chartTailField_le_horizonField i hf,
    fun hf => mem_chartTailField_of_mem_horizonField i hmem hf⟩

end

end GaloisForLFunctions.HTGeometry
