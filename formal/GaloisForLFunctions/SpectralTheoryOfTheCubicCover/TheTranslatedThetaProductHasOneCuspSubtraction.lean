import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheOppositeTranslationsPreserveTheCubicMultiplier

/-!
# Opposite theta translations share one cusp

The rational cusp sets of the translates by `ω` and `−ω` intersect only at
infinity. The product of their linear cusp subtractions consequently has just
one growing cusp term.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical MatrixGroups ComplexConjugate

namespace GaloisForLFunctions.SpectralTheoryOfTheCubicCover

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein
  MetaplecticMobiusDescent.CubicKubota MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

theorem integralTranslation_mul (a b : O) :
    integralTranslation a * integralTranslation b = integralTranslation (a + b) := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [integralTranslation, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem integralTranslation_neg (b : O) :
    integralTranslation (-b) = (integralTranslation b)⁻¹ := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [integralTranslation]

theorem height_integralTranslation (b : O) (w : HyperbolicSpace) :
    hyperbolicHeight (integralComplexMatrix (integralTranslation b) • w) = hyperbolicHeight w := by
  obtain ⟨z, v, hv, rfl⟩ := upperPoint_surjective w
  rw [integralTranslation_action, hyperbolicHeight_upperPoint, hyperbolicHeight_upperPoint]

private theorem three_dvd_int_add_omega (a b : ℤ)
    (h : (3 : O) ∣ (a : O) + (b : O) * omega) :
    (3 : ℤ) ∣ a ∧ (3 : ℤ) ∣ b := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨u, v, hxv⟩ := Coordinates.exists_coordinates x
  have he : Coordinates.eval a b = Coordinates.eval (3 * u) (3 * v) := by
    rw [Coordinates.eval, Coordinates.eval]
    rw [hxv] at hx
    push_cast
    linear_combination hx
  have hc := Coordinates.unique_coordinates he
  exact ⟨⟨u, hc.1⟩, ⟨v, hc.2⟩⟩

/-- Only the two copies of infinity can meet after opposite translations by `ω`. -/
theorem rationalRep_translation_pair (q q' : RationalFourCusp)
    (h : (3 : O) ∣
      (rationalEmbedding (rationalRep q') * integralTranslation (-2 * omega) *
        (rationalEmbedding (rationalRep q))⁻¹) 1 0) :
    q = .inl () ∧ q' = .inl () := by
  have he :
      (rationalEmbedding (rationalRep q') * integralTranslation (-2 * omega) *
        (rationalEmbedding (rationalRep q))⁻¹) 1 0 =
      ((rationalRep q' 1 0 * rationalRep q 1 1 -
        rationalRep q' 1 1 * rationalRep q 1 0 : ℤ) : O) +
      ((2 * rationalRep q' 1 0 * rationalRep q 1 0 : ℤ) : O) * omega := by
    simp [integralTranslation, rationalEmbedding, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.adjugate_fin_two]
    ring
  rw [he] at h
  obtain ⟨h1, h2⟩ := three_dvd_int_add_omega _ _ h
  rcases q with ⟨⟩ | ⟨⟩ | ⟨⟩ | ⟨⟩ <;>
    rcases q' with ⟨⟩ | ⟨⟩ | ⟨⟩ | ⟨⟩ <;>
    simp [rationalRep, rationalFourCuspRep, ModularGroup.coe_S, ModularGroup.coe_T,
      pow_two, Matrix.mul_apply, Fin.sum_univ_two] at h1 h2 ⊢

/-- Distinct translated rational cusp profiles have disjoint high support. -/
theorem translation_cross_zero (F : ℝ → ℂ) (q q' : RationalFourCusp)
    (hq : ¬ (q = .inl () ∧ q' = .inl ())) (w : HyperbolicSpace) :
    cuspCutoffCorrection 1 F
      (rationalComplex (rationalRep q) • (integralComplexMatrix (integralTranslation omega) • w)) *
      cuspCutoffCorrection 1 F
        (rationalComplex (rationalRep q') • (integralComplexMatrix (integralTranslation (-omega)) • w)) = 0 := by
  by_contra hne
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hne
  obtain ⟨n, hn⟩ := exists_high_of_cutoff_ne_zero F _ h1
  obtain ⟨n', hn'⟩ := exists_high_of_cutoff_ne_zero F _ h2
  let g₁ : SL(2, O) := (n : SL(2, O)) * rationalEmbedding (rationalRep q) * integralTranslation omega
  let g₂ : SL(2, O) := (n' : SL(2, O)) * rationalEmbedding (rationalRep q') * integralTranslation (-omega)
  have e1 : complexMatrix n •
      (rationalComplex (rationalRep q) • (integralComplexMatrix (integralTranslation omega) • w)) =
        integralComplexMatrix g₁ • w := by
    dsimp only [g₁]
    rw [map_mul, map_mul, mul_smul, mul_smul]
    rfl
  have e2 : complexMatrix n' •
      (rationalComplex (rationalRep q') • (integralComplexMatrix (integralTranslation (-omega)) • w)) =
        integralComplexMatrix g₂ • w := by
    dsimp only [g₂]
    rw [map_mul, map_mul, mul_smul, mul_smul]
    rfl
  rw [e1] at hn
  rw [e2] at hn'
  let A : SL(2, O) := rationalEmbedding (rationalRep q') * integralTranslation (-2 * omega) *
    (rationalEmbedding (rationalRep q))⁻¹
  have hg : g₂ * g₁⁻¹ = (n' : SL(2, O)) * A * (n : SL(2, O))⁻¹ := by
    have htt : integralTranslation (-omega) * (integralTranslation omega)⁻¹ =
        integralTranslation (-2 * omega) := by
      rw [← integralTranslation_neg, integralTranslation_mul]
      congr 1
      ring
    calc
      _ = (n' : SL(2, O)) * rationalEmbedding (rationalRep q') *
          (integralTranslation (-omega) * (integralTranslation omega)⁻¹) *
          (rationalEmbedding (rationalRep q))⁻¹ * (n : SL(2, O))⁻¹ := by
        dsimp only [g₁, g₂]
        group
      _ = _ := by rw [htt]; dsimp only [A]; group
  have h0 : (g₂ * g₁⁻¹) 1 0 = 0 := by
    by_contra hc
    have hp := integral_hyperbolicHeight_mul_le_one (g₂ * g₁⁻¹) hc (integralComplexMatrix g₁ • w)
    rw [map_mul, map_inv, mul_smul, inv_smul_smul] at hp
    nlinarith only [hp, hn, hn']
  obtain ⟨k, hk⟩ := levelThree_conj_lower n n' A
  rw [← hg, h0] at hk
  exact hq (rationalRep_translation_pair q q' ⟨-k, by linear_combination -hk⟩)

/-- Opposite translates of a real cutoff profile multiply to its conjugate square. -/
theorem cutoff_opposite_translations_mul (b : O) (F : ℝ → ℂ)
    (hF : ∀ t, conj (F t) = F t) (y : HyperbolicSpace) :
    cuspCutoffCorrection 1 F (integralComplexMatrix (integralTranslation b) • y) *
      cuspCutoffCorrection 1 F (integralComplexMatrix (integralTranslation (-b)) • y) =
        conj (cuspCutoffCorrection 1 (fun t => F t * F t) y) := by
  by_cases hhigh : ∃ n : levelThree, 1 < hyperbolicHeight (complexMatrix n • y)
  · obtain ⟨n, hn⟩ := hhigh
    have h1 : 1 < cosetHeight (cosetOf (levelThreeConjugate (integralTranslation b) n))
        (integralComplexMatrix (integralTranslation b) • y) := by
      rw [cosetHeight_cosetOf, high_conj _ (height_integralTranslation b)]
      exact hn
    have h2 : 1 < cosetHeight (cosetOf (levelThreeConjugate (integralTranslation (-b)) n))
        (integralComplexMatrix (integralTranslation (-b)) • y) := by
      rw [cosetHeight_cosetOf, high_conj _ (height_integralTranslation (-b))]
      exact hn
    have h0 : 1 < cosetHeight (cosetOf n) y := by rwa [cosetHeight_cosetOf]
    rw [cuspCutoffCorrection_eq 1 le_rfl F _ _ h1,
      cuspCutoffCorrection_eq 1 le_rfl F _ _ h2,
      cuspCutoffCorrection_eq 1 le_rfl _ _ _ h0]
    simp only [cosetCharacter_cosetOf, cosetHeight_cosetOf,
      high_conj _ (height_integralTranslation b), high_conj _ (height_integralTranslation (-b))]
    set t := hyperbolicHeight (complexMatrix n • y)
    have hc : conj ((complexCharacter n)⁻¹ * (F t * F t)) =
        complexCharacter n * (F t * F t) := by
      rw [map_mul, map_inv₀, conj_complexCharacter, inv_inv, map_mul, hF]
    rw [hc]
    calc
      _ = (complexCharacter (levelThreeConjugate (integralTranslation b) n) *
          complexCharacter (levelThreeConjugate (integralTranslation (-b)) n))⁻¹ * (F t * F t) := by
        rw [mul_inv]
        ring
      _ = _ := by rw [complexCharacter_opposite_shifts, complexCharacter_sq_eq_inv, inv_inv]
  · push Not at hhigh
    have hlow : ∀ m : levelThree, ¬ 1 < hyperbolicHeight
        (complexMatrix m • (integralComplexMatrix (integralTranslation b) • y)) := by
      intro m hm
      have key : complexMatrix (levelThreeConjugate (integralTranslation (-b)) m) • y =
          integralComplexMatrix (integralTranslation (-b)) •
            (complexMatrix m • (integralComplexMatrix (integralTranslation b) • y)) := by
        rw [conj_smul, integralTranslation_neg, map_inv, inv_smul_smul]
      exact (hhigh (levelThreeConjugate (integralTranslation (-b)) m)).not_gt
        (by rw [key, height_integralTranslation]; exact hm)
    rw [cutoff_eq_zero_of_low F _ hlow,
      cutoff_eq_zero_of_low _ y fun m hm => (hhigh m).not_gt hm, zero_mul, map_zero]

/-- The sole growing term of the opposite translated product. -/
def translatedSubtraction (w : HyperbolicSpace) : ℂ :=
  thetaCoeff ^ 2 * conj (cuspCutoffCorrection 1 (growthProfile (Set.Ici 2)) w)

theorem translation_term (q q' : RationalFourCusp) (w : HyperbolicSpace) :
    cuspCutoffCorrection 1 (thinProfile (Set.Ici 2))
      (rationalComplex (rationalRep q) • (integralComplexMatrix (integralTranslation omega) • w)) *
      cuspCutoffCorrection 1 (thinProfile (Set.Ici 2))
        (rationalComplex (rationalRep q') • (integralComplexMatrix (integralTranslation (-omega)) • w)) =
      if q = .inl () ∧ q' = .inl () then
        conj (cuspCutoffCorrection 1 (growthProfile (Set.Ici 2)) w) else 0 := by
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    simp only [rationalRep, rationalFourCuspRep, map_one, one_smul]
    rw [cutoff_opposite_translations_mul _ _ (conj_thinProfile _)]
    congr 2
    funext t
    exact thinProfile_mul_self _ le_rfl t
  · exact translation_cross_zero _ q q' h w

/-- Multiplying the two four-cusp linear subtractions leaves only infinity. -/
theorem thetaLinear_translation_mul (w : HyperbolicSpace) :
    thetaLinear (integralComplexMatrix (integralTranslation omega) • w) *
      thetaLinear (integralComplexMatrix (integralTranslation (-omega)) • w) =
        translatedSubtraction w := by
  simp only [thetaLinear, linearSubtraction, translatedSubtraction]
  rw [mul_mul_mul_comm, ← pow_two, Finset.sum_mul_sum]
  congr 1
  have he (q : RationalFourCusp) :
      (∑ q' : RationalFourCusp,
        if q = .inl () ∧ q' = .inl () then
          conj (cuspCutoffCorrection 1 (growthProfile (Set.Ici 2)) w) else 0) =
      if q = .inl () then conj (cuspCutoffCorrection 1 (growthProfile (Set.Ici 2)) w) else 0 := by
    by_cases hq : q = .inl ()
    · simp only [hq, true_and, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    · simp only [hq, false_and, if_false, Finset.sum_const_zero]
  simp only [translation_term, he, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Uniform cancellation of the cusp growth in products of integral translates. -/
theorem theta_translated_product_remainder_bounded :
    ∃ C : ℝ, ∀ (g h : SL(2, O)) (w : HyperbolicSpace),
      ‖sourceTheta (integralComplexMatrix g • w) * sourceTheta (integralComplexMatrix h • w) -
        thetaLinear (integralComplexMatrix g • w) * thetaLinear (integralComplexMatrix h • w)‖ ≤ C := by
  obtain ⟨A, B, hA, _, hbd⟩ := thetaLinear_bounds
  refine ⟨2 * A * B, fun g h w => ?_⟩
  obtain ⟨M, z, v, hv, hMw, -, hfloor⟩ := bianchi_reduction_height_floor w
  have hw : w = integralComplexMatrix M⁻¹ • upperPoint z v hv := by
    rw [← hMw, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  have he (a : SL(2, O)) : integralComplexMatrix a • w =
      integralComplexMatrix (a * M⁻¹) • upperPoint z v hv := by
    rw [hw, ← mul_smul, ← map_mul]
  obtain ⟨_, hh1, hd1⟩ := hbd (g * M⁻¹) z v hv hfloor
  obtain ⟨hθ2, _, hd2⟩ := hbd (h * M⁻¹) z v hv hfloor
  rw [he g, he h]
  set a₁ := sourceTheta (integralComplexMatrix (g * M⁻¹) • upperPoint z v hv)
  set b₁ := thetaLinear (integralComplexMatrix (g * M⁻¹) • upperPoint z v hv)
  set a₂ := sourceTheta (integralComplexMatrix (h * M⁻¹) • upperPoint z v hv)
  set b₂ := thetaLinear (integralComplexMatrix (h * M⁻¹) • upperPoint z v hv)
  set p := 1 + v ^ ((2 : ℝ) / 3)
  have hfirst : ‖a₁ - b₁‖ * ‖a₂‖ ≤ A * B := by
    calc
      _ ≤ ‖a₁ - b₁‖ * (A * p) := mul_le_mul_of_nonneg_left hθ2 (norm_nonneg _)
      _ = A * (‖a₁ - b₁‖ * p) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hd1 hA
  have hsecond : ‖b₁‖ * ‖a₂ - b₂‖ ≤ A * B := by
    calc
      _ ≤ (A * p) * ‖a₂ - b₂‖ := mul_le_mul_of_nonneg_right hh1 (norm_nonneg _)
      _ = A * (‖a₂ - b₂‖ * p) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hd2 hA
  rw [show a₁ * a₂ - b₁ * b₂ = (a₁ - b₁) * a₂ + b₁ * (a₂ - b₂) by ring]
  calc
    _ ≤ ‖a₁ - b₁‖ * ‖a₂‖ + ‖b₁‖ * ‖a₂ - b₂‖ := by
      simpa only [norm_mul] using norm_add_le ((a₁ - b₁) * a₂) (b₁ * (a₂ - b₂))
    _ ≤ 2 * A * B := by linarith only [hfirst, hsecond]

/-- The product at opposite translations by the cubic root. -/
def translatedThetaProduct (w : HyperbolicSpace) : ℂ :=
  sourceTheta (integralComplexMatrix (integralTranslation omega) • w) *
    sourceTheta (integralComplexMatrix (integralTranslation (-omega)) • w)

def translatedRenormalized (w : HyperbolicSpace) : ℂ :=
  translatedThetaProduct w - translatedSubtraction w

theorem translatedThetaProduct_automorphy (n : levelThree) (w : HyperbolicSpace) :
    translatedThetaProduct (complexMatrix n • w) =
      (complexCharacter n)⁻¹ * translatedThetaProduct w :=
  sourceTheta_opposite_shifts_automorphy omega n w

theorem translatedThetaProduct_continuous : Continuous translatedThetaProduct :=
  (cubicSourceResidualFunction_continuous.comp (continuous_hyperbolic_action _)).mul
    (cubicSourceResidualFunction_continuous.comp (continuous_hyperbolic_action _))

theorem translatedSubtraction_automorphy (n : levelThree) (w : HyperbolicSpace) :
    translatedSubtraction (complexMatrix n • w) =
      (complexCharacter n)⁻¹ * translatedSubtraction w := by
  rw [translatedSubtraction, translatedSubtraction,
    cuspCutoffCorrection_automorphy 1 le_rfl, map_mul, conj_complexCharacter]
  ring

theorem translatedSubtraction_measurable : Measurable translatedSubtraction :=
  measurable_const.mul (Complex.continuous_conj.measurable.comp
    (cuspCutoffCorrection_measurable 1 _ (growthProfile_measurable _ measurableSet_Ici)))

theorem translatedRenormalized_automorphy (n : levelThree) (w : HyperbolicSpace) :
    translatedRenormalized (complexMatrix n • w) =
      (complexCharacter n)⁻¹ * translatedRenormalized w := by
  rw [translatedRenormalized, translatedRenormalized, translatedThetaProduct_automorphy,
    translatedSubtraction_automorphy]
  ring

theorem translatedRenormalized_measurable : Measurable translatedRenormalized :=
  translatedThetaProduct_continuous.measurable.sub translatedSubtraction_measurable

theorem translatedRenormalized_bounded :
    ∃ C : ℝ, ∀ w : HyperbolicSpace, ‖translatedRenormalized w‖ ≤ C := by
  obtain ⟨C, hC⟩ := theta_translated_product_remainder_bounded
  refine ⟨C, fun w => ?_⟩
  simpa only [translatedRenormalized, translatedThetaProduct, thetaLinear_translation_mul] using
    hC (integralTranslation omega) (integralTranslation (-omega)) w

theorem translatedRenormalized_memLp :
    MemLp translatedRenormalized 2 (hyperbolicVolume.restrict levelSet) := by
  haveI : IsFiniteMeasure (hyperbolicVolume.restrict levelSet) :=
    isFiniteMeasure_restrict.mpr levelSet_volume_lt_top.ne
  obtain ⟨C, hC⟩ := translatedRenormalized_bounded
  exact MemLp.of_bound translatedRenormalized_measurable.aestronglyMeasurable C
    (Filter.Eventually.of_forall hC)

end GaloisForLFunctions.SpectralTheoryOfTheCubicCover
