import GaloisForLFunctions.SignedArithmeticHodgeTheory.DyadicHaarCoordinatesReadTheOriginalSource
import GaloisForLFunctions.ArithmeticIndexDescent.GammaBoundedCompleteProfilesHaveCompactDetails
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheArchimedeanPairingOfTwoAtoms

/-!
# The compactness boundary between detail labels and translation levels

Each fixed level of Gamma-bounded complete-source details has a compact
envelope. A single nonzero Haar generator has infinitely many orthogonal
dyadic translates, all with the same original Gamma energy. Keeping whole
translation orbits is therefore essential; finite-generator approximation
does not imply finite-dimensional or compact approximation across levels.
-/

noncomputable section
open MeasureTheory Set RHTower
open scoped InnerProductSpace

namespace GaloisForLFunctions.SignedArithmeticHodgeTheory
open HTGeometry ArithmeticCastelnuovoSeveri.LogCells BiarithmeticGaugeGeometry

/-- A compact envelope for the actual details at any one fixed dyadic level. -/
def singleLevelGammaDetailEnvelope (j : ℕ) : Set (Lp ℂ 2 halfLineMeasure) :=
  (halfLineRightShift (Real.log 2) ^ j) '' closure ArithmeticIndexDescent.gammaUnitDetails

theorem isCompact_singleLevelGammaDetailEnvelope (j : ℕ) :
    IsCompact (singleLevelGammaDetailEnvelope j) :=
  ArithmeticIndexDescent.isCompact_closure_gammaUnitDetails.image
    (halfLineRightShift (Real.log 2) ^ j).continuous

theorem singleLevelGammaDetails_mem_envelope (j : ℕ) (q d : ℕ → ℝ) (X : ℕ)
    (hΓ : levyEnergy (completePairProfile q d X) ≤ 1) :
    (halfLineRightShift (Real.log 2) ^ j) (haarSection d X) ∈
      singleLevelGammaDetailEnvelope j :=
  ⟨haarSection d X, subset_closure ⟨q, d, X, rfl, hΓ⟩, rfl⟩

/-- The entire dyadic translation orbit of the first actual balanced Haar source. -/
def firstHaarTranslationOrbit (j : ℕ) : Lp ℂ 2 halfLineMeasure :=
  (halfLineRightShift (Real.log 2) ^ j) (haarAtom 1)

private theorem firstHaarTranslationOrbit_eq (j : ℕ) :
    firstHaarTranslationOrbit j = (Real.sqrt (haarMass 1) : ℂ) •
      logCellEmbedding (logCellDyadicOrbit (j, some (1 : ℕ+))) :=
  (sqrt_haarMass_smul_logCellEmbedding_detail_pow 1 j).symm

/-- The actual translated Haar sources form an infinite orthogonal family of fixed positive mass. -/
theorem inner_firstHaarTranslationOrbit (j k : ℕ) :
    inner ℂ (firstHaarTranslationOrbit j) (firstHaarTranslationOrbit k) =
      if j = k then (haarMass 1 : ℂ) else 0 := by
  have hU : inner ℂ
      (logCellEmbedding (logCellDyadicOrbit (j, some (1 : ℕ+))))
      (logCellEmbedding (logCellDyadicOrbit (k, some (1 : ℕ+)))) =
      inner ℂ (logCellDyadicOrbit (j, some (1 : ℕ+)))
        (logCellDyadicOrbit (k, some (1 : ℕ+))) :=
    LinearIsometry.inner_map_map logCellIsometry _ _
  rw [firstHaarTranslationOrbit_eq, firstHaarTranslationOrbit_eq,
    inner_smul_left, inner_smul_right, Complex.conj_ofReal, hU,
    orthonormal_iff_ite.mp orthonormal_logCellDyadicOrbit]
  by_cases hjk : j = k
  · subst k
    simp only [ite_true, mul_one, ← Complex.ofReal_mul, ← pow_two,
      Real.sq_sqrt (haarMass_pos (le_refl 1)).le]
  · simp only [Prod.mk.injEq, hjk, false_and, if_false, mul_zero]

/-- Distinct levels retain a fixed positive physical L² separation. -/
theorem dist_firstHaarTranslationOrbit_sq {j k : ℕ} (hjk : j ≠ k) :
    dist (firstHaarTranslationOrbit j) (firstHaarTranslationOrbit k) ^ 2 = 2 * haarMass 1 := by
  have hnorm := inner_self_eq_norm_sq (𝕜 := ℂ)
    (firstHaarTranslationOrbit j - firstHaarTranslationOrbit k)
  simp only [inner_sub_left, inner_sub_right, inner_firstHaarTranslationOrbit,
    ite_true, if_neg hjk, if_neg hjk.symm, sub_zero, zero_sub,
    Complex.sub_re, Complex.neg_re, Complex.ofReal_re] at hnorm
  rw [dist_eq_norm]
  linarith only [hnorm]

theorem firstHaarTranslationOrbit_injective : Function.Injective firstHaarTranslationOrbit := by
  intro j k he
  by_contra hne
  have h := dist_firstHaarTranslationOrbit_sq hne
  rw [he, dist_self, zero_pow (by norm_num : 2 ≠ 0)] at h
  have hm := haarMass_pos (le_refl 1)
  linarith only [h, hm]

/-- Even one full generator orbit is not totally bounded in the original L² space. -/
theorem not_totallyBounded_firstHaarTranslationOrbit :
    ¬ TotallyBounded (range firstHaarTranslationOrbit) := by
  intro htb
  have hm := haarMass_pos (le_refl 1)
  obtain ⟨T, hTsub, hTfin, hcover⟩ := Metric.finite_approx_of_totallyBounded htb
    (Real.sqrt (haarMass 1)) (Real.sqrt_pos.mpr hm)
  have hsub : range firstHaarTranslationOrbit ⊆ T := by
    rintro x ⟨j, rfl⟩
    have hmem := hcover (mem_range_self j)
    simp only [mem_iUnion, Metric.mem_ball] at hmem
    obtain ⟨y, hyT, hy⟩ := hmem
    obtain ⟨k, rfl⟩ := hTsub hyT
    have hjk : j = k := by
      by_contra hne
      have hd := dist_firstHaarTranslationOrbit_sq hne
      have hnn := dist_nonneg (x := firstHaarTranslationOrbit j) (y := firstHaarTranslationOrbit k)
      have hs := Real.sq_sqrt hm.le
      nlinarith only [hd, hy, hnn, hs, Real.sqrt_nonneg (haarMass 1), hm]
    simpa only [hjk] using hyT
  exact (infinite_range_of_injective firstHaarTranslationOrbit_injective).not_finite (hTfin.subset hsub)

/-- Literal source profiles for the orthogonal orbit. -/
def firstHaarTranslatedProfile (j : ℕ) (x : ℝ) : ℝ :=
  haarProfile 1 (x - j * Real.log 2)

theorem firstHaarTranslationOrbit_coeFn (j : ℕ) :
    (halfLineExtend (firstHaarTranslationOrbit j) : ℝ → ℂ) =ᵐ[volume]
      fun x => (firstHaarTranslatedProfile j x : ℂ) :=
  halfLineExtend_haarAtom_pow_coeFn 1 j

/-- The infinite orthogonal orbit has one common original Gamma energy. -/
theorem levyEnergy_firstHaarTranslatedProfile (j : ℕ) :
    levyEnergy (firstHaarTranslatedProfile j) = levyEnergy (haarProfile 1) :=
  SpacingScaleHarmonicAnalysis.levyEnergy_translate (g := haarProfile 1) (j * Real.log 2)

theorem firstHaarTranslatedProfile_compact (j : ℕ) :
    HasCompactSupport (firstHaarTranslatedProfile j) :=
  (haarProfile_compact 1).comp_homeomorph (Homeomorph.subRight (j * Real.log 2))

theorem firstHaarTranslatedProfile_bv (j : ℕ) :
    BoundedVariationOn (firstHaarTranslatedProfile j) univ :=
  ne_top_of_le_ne_top (haarProfile_bv 1)
    (eVariationOn.comp_le_of_monotoneOn (haarProfile 1) (fun x => x - j * Real.log 2)
      (fun _ _ _ _ h => sub_le_sub_right h _) (fun _ _ => mem_univ _))

end GaloisForLFunctions.SignedArithmeticHodgeTheory

#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.isCompact_singleLevelGammaDetailEnvelope
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.not_totallyBounded_firstHaarTranslationOrbit
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.inner_firstHaarTranslationOrbit
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.levyEnergy_firstHaarTranslatedProfile
