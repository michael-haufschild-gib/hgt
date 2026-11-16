import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheTranslatedDifferenceIsTheUnramifiedSquare

/-!
# The unramified square factors through the untwisted series

Outside `3O`, the source mask leaves a primary generator or its negative.
These two signs contribute equally. Factoring cube frequencies therefore
leaves exactly the untwisted squarefree series.
-/

noncomputable section
open scoped BigOperators Classical

namespace GaloisForLFunctions.SpectralTheoryOfTheCubicCover

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicKubota

private def signedPrimary (p : Bool × GoodIdeal) : O :=
  frequencySplit ((if p.1 then (-1 : Oˣ) else 1), 0, p.2)

private theorem signedPrimary_injective : Function.Injective signedPrimary := by
  rintro ⟨b, I⟩ ⟨c, J⟩ he
  have h := frequencySplit_injective he
  have hI := congrArg (fun p : Oˣ × ℕ × GoodIdeal => p.2.2) h
  have hu := congrArg (fun p : Oˣ × ℕ × GoodIdeal => (p.1 : O)) h
  change I = J at hI
  subst J
  cases b <;> cases c <;> simp_all

private theorem three_not_dvd_primary (a : O) (hp : lambda ^ 2 ∣ a - 1) :
    ¬ (3 : O) ∣ a := by
  intro hd
  have h1 : (3 : O) ∣ 1 := by
    simpa only [sub_sub_cancel] using dvd_sub hd (three_dvd_primary_sub_one a hp)
  have hlambda : lambda ∣ (1 : O) :=
    (dvd_pow_self lambda (by decide : (2 : ℕ) ≠ 0)).trans (lambda_sq_dvd_three.trans h1)
  exact lambda_not_isUnit (isUnit_of_dvd_one hlambda)

theorem twistedPrimarySeries_one (w : ℂ) :
    twistedPrimarySeries 1 w = ∑' I : Ideal O, unramifiedNormWeight w I *
      rationalSourceResidualFourierCoefficient (primaryIdealGenerator I) ^ 2 := by
  unfold twistedPrimarySeries
  refine tsum_congr fun I => ?_
  by_cases hI : primaryIdealGenerator I = 0
  · rw [unramifiedNormWeight_of_bad w I hI, zero_mul, zero_mul]
  · rw [symbol_one_numerator _ (primaryIdealGenerator_spec I hI).2, map_one, one_pow, one_mul]

/-- The two primary signs give the unramified part of the squared theta series. -/
theorem unramifiedSquare_eq_primary (s : ℂ) (hs : 4 < s.re) :
    besselDirichlet unramifiedSquareCoeff s =
      2 * ((4 * Real.pi * ‖cuspFrequency 1‖ : ℝ) : ℂ) ^ (-s) *
        twistedPrimarySeries 1 (s / 2) := by
  let F : O → ℂ := fun h => if h = 0 then 0 else unramifiedSquareCoeff h *
    ((4 * Real.pi * ‖cuspFrequency h‖ : ℝ) : ℂ) ^ (-s)
  let g : Ideal O → ℂ := fun I => unramifiedNormWeight (s / 2) I *
    rationalSourceResidualFourierCoefficient (primaryIdealGenerator I) ^ 2
  let a : ℂ := ((4 * Real.pi * ‖cuspFrequency 1‖ : ℝ) : ℂ) ^ (-s)
  have hF : Summable F := by
    refine Summable.of_norm_bounded (summable_thetaSqDirichlet_term s hs).norm fun h => ?_
    by_cases hh : h = 0
    · simp [F, hh]
    · by_cases hd : (3 : O) ∣ h
      · simp only [F, if_neg hh, unramifiedSquareCoeff, if_pos hd, zero_mul, norm_zero]
        exact norm_nonneg _
      · simp only [F, if_neg hh, unramifiedSquareCoeff, if_neg hd, le_refl]
  have hsupp : Function.support F ⊆ Set.range signedPrimary := by
    intro h hh
    have hh0 : h ≠ 0 := fun hz => hh (by simp [F, hz])
    have h3 : ¬ (3 : O) ∣ h := fun hd => hh (by simp [F, unramifiedSquareCoeff, hd])
    have hT : rationalSourceResidualFourierCoefficient h ≠ 0 :=
      fun hz => hh (by simp [F, unramifiedSquareCoeff, hz])
    rcases primary_or_negative_primary_of_source_mask h h3
      (sourceFourier_phase_of_ne_zero h hh0 hT) with hp | hp
    · have hg := primaryIdealGenerator_span h hh0 hp
      refine ⟨(false, ⟨Ideal.span {h}, by rw [hg]; exact hh0⟩), ?_⟩
      simp [signedPrimary, frequencySplit, hg]
    · have hg := primaryIdealGenerator_span (-h) (neg_ne_zero.mpr hh0) hp
      refine ⟨(true, ⟨Ideal.span {-h}, by rw [hg]; exact neg_ne_zero.mpr hh0⟩), ?_⟩
      simp only [signedPrimary, frequencySplit, if_true, Units.val_neg, Units.val_one,
        pow_zero, mul_one, neg_one_mul, hg, neg_neg]
  have hneg (h : O) : F (-h) = F h := by
    simp only [F, neg_eq_zero, unramifiedSquareCoeff, dvd_neg,
      rationalSourceResidualFourierCoefficient_neg, cuspFrequency_neg, norm_neg]
  have hterm (b : Bool) (I : GoodIdeal) : F (signedPrimary (b, I)) = a * g I.1 := by
    have hp := (primaryIdealGenerator_spec I.1 I.2).2
    have hbase : F (primaryIdealGenerator I.1) = a * g I.1 := by
      dsimp only [F]
      rw [if_neg I.2, unramifiedSquareCoeff, if_neg (three_not_dvd_primary _ hp)]
      have hw := frequencyWeight_split s 1 I.1 I.2
      simp only [one_mul] at hw
      rw [hw]
      dsimp only [a, g]
      ring
    cases b
    · simpa only [signedPrimary, frequencySplit, Bool.false_eq_true, if_false, Units.val_one,
        pow_zero, one_mul] using hbase
    · simpa only [signedPrimary, frequencySplit, if_true, Units.val_neg, Units.val_one,
        pow_zero, mul_one, neg_one_mul, hneg] using hbase
  have hG := hF.comp_injective signedPrimary_injective
  have hgood : (∑' I : GoodIdeal, g I.1) = ∑' I : Ideal O, g I := by
    refine tsum_subtype_eq_of_support_subset (s := {I : Ideal O | primaryIdealGenerator I ≠ 0}) ?_
    intro I hI
    by_contra hb
    exact hI (by
      dsimp only [g]
      rw [unramifiedNormWeight_of_bad _ _ (not_not.mp hb), zero_mul])
  calc
    besselDirichlet unramifiedSquareCoeff s = ∑' h, F h := rfl
    _ = ∑' p : Bool × GoodIdeal, F (signedPrimary p) :=
      (signedPrimary_injective.tsum_eq hsupp).symm
    _ = ∑' b : Bool, ∑' I : GoodIdeal, F (signedPrimary (b, I)) := hG.tsum_prod
    _ = 2 * a * ∑' I : Ideal O, g I := by
      simp only [hterm, tsum_mul_left, hgood, tsum_fintype]
      simp only [Fintype.sum_bool]
      ring
    _ = _ := by rw [twistedPrimarySeries_one]

/-- Cube removal leaves the actual untwisted squarefree series. -/
theorem unramifiedSquare_eq_squarefree (s : ℂ) (hs : 4 < s.re) :
    besselDirichlet unramifiedSquareCoeff s =
      2 * ((4 * Real.pi * ‖cuspFrequency 1‖ : ℝ) : ℂ) ^ (-s) *
        (star rationalSourceThetaScalar ^ 2 * unramifiedIdealZeta (3 * (s / 2) - 1) *
          twistedSquarefreeSeries 1 (s / 2)) := by
  have hw : 1 < (s / 2).re := by rw [Complex.div_ofNat_re]; linarith
  have he := twistedPrimarySeries_eq (1 : Oˣ) 0 (s / 2) hw
  simp only [Units.val_one, pow_zero, mul_one] at he
  rw [unramifiedSquare_eq_primary s hs, he]

end GaloisForLFunctions.SpectralTheoryOfTheCubicCover
