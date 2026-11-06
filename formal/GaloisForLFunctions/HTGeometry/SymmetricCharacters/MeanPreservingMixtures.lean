import GaloisForLFunctions.HTGeometry.SymmetricCharacters.MixtureRigidity
import GaloisForLFunctions.HTGeometry.SymmetricCharacters.CountableColoring

/-!
# Countable color mixtures and their sharp variance loss

Finite probability mixtures of summable color alphabets remain positive coherent characters.
Their transposition value is the expected squared color mass. Subtracting the squared mass of
the mean alphabet leaves a nonnegative total variance, zero exactly when all positive-mass
components agree pointwise with that mean. Square summability controls every interchange.
-/

open scoped BigOperators Classical
noncomputable section
namespace GaloisForLFunctions.SymmetricCharacters

variable {I A : Type*} [Fintype I]
/-- The coordinatewise mean of a finite color mixture. -/
def colorMean (mix : I → NNReal) (v : I → A → ℝ) (a : A) : ℝ :=
  ∑ i, (mix i : ℝ) * v i a

/-- Jensen's square bound makes the mean alphabet square summable. -/
theorem colorMean_sq_summable (mix : I → NNReal) (hmix : (∑ i, (mix i : ℝ)) = 1)
    (v : I → A → ℝ) (hv : ∀ i, Summable fun a => v i a ^ 2) :
    Summable (fun a => colorMean mix v a ^ 2) := by
  have hF : Summable (fun a => ∑ i, (mix i : ℝ) * v i a ^ 2) :=
    summable_sum (fun i _ => (hv i).mul_left (mix i : ℝ))
  refine Summable.of_nonneg_of_le (fun a => sq_nonneg _) (fun a => ?_) hF
  have h := mixtureDefect_nonneg mix (fun i => v i a)
  simp only [mixtureDefect, hmix, one_mul] at h
  exact sub_nonneg.mp h

/-- Total color variance is summable as a difference of two square-mass families. -/
theorem colorVariance_summable (mix : I → NNReal) (hmix : (∑ i, (mix i : ℝ)) = 1)
    (v : I → A → ℝ) (hv : ∀ i, Summable fun a => v i a ^ 2) :
    Summable (fun a => mixtureDefect mix (fun i => v i a)) := by
  have hF : Summable (fun a => ∑ i, (mix i : ℝ) * v i a ^ 2) :=
    summable_sum (fun i _ => (hv i).mul_left (mix i : ℝ))
  simpa only [mixtureDefect, hmix, one_mul, colorMean] using
    hF.sub (colorMean_sq_summable mix hmix v hv)

/-- Probability colors lie in `[0,1]`, so square mass is dominated by total mass. -/
theorem probabilityColor_sq_summable (w : A → NNReal)
    (hw : Summable (fun a => (w a : ℝ))) (hm : (∑' a, (w a : ℝ)) = 1) :
    Summable (fun a => (w a : ℝ) ^ 2) := by
  refine Summable.of_nonneg_of_le (fun a => sq_nonneg _) (fun a => ?_) hw
  have hle : (w a : ℝ) ≤ 1 := by
    rw [← hm]
    exact hw.le_tsum a (fun b _ => (w b).coe_nonneg)
  simpa only [pow_two, mul_one] using mul_le_mul_of_nonneg_left hle (w a).coe_nonneg

/-- Sum of the weighted variances of all color coordinates. -/
def colorMixtureVariance (mix : I → NNReal) (v : I → A → ℝ) : ℝ :=
  ∑' a, mixtureDefect mix (fun i => v i a)

theorem colorMixtureVariance_nonneg (mix : I → NNReal) (v : I → A → ℝ) :
    0 ≤ colorMixtureVariance mix v :=
  tsum_nonneg (fun a => mixtureDefect_nonneg mix (fun i => v i a))

/-- Expected square mass decomposes into the square mass of the mean and total variance. -/
theorem colorMixtureVariance_eq (mix : I → NNReal) (hmix : (∑ i, (mix i : ℝ)) = 1)
    (v : I → A → ℝ) (hv : ∀ i, Summable fun a => v i a ^ 2) :
    colorMixtureVariance mix v =
      (∑ i, (mix i : ℝ) * ∑' a, v i a ^ 2) - ∑' a, colorMean mix v a ^ 2 := by
  have hF : Summable (fun a => ∑ i, (mix i : ℝ) * v i a ^ 2) :=
    summable_sum (fun i _ => (hv i).mul_left (mix i : ℝ))
  have hm := colorMean_sq_summable mix hmix v hv
  unfold colorMixtureVariance
  simp only [mixtureDefect, hmix, one_mul]
  change (∑' a, ((∑ i, (mix i : ℝ) * v i a ^ 2) - colorMean mix v a ^ 2)) = _
  rw [hF.tsum_sub hm, Summable.tsum_finsetSum (fun i _ => (hv i).mul_left (mix i : ℝ))]
  simp only [tsum_mul_left, colorMean]

/-- Zero total variance forces every supported pair of alphabets to agree pointwise. -/
theorem colorMixtureVariance_eq_zero_iff (mix : I → NNReal)
    (hmix : (∑ i, (mix i : ℝ)) = 1) (v : I → A → ℝ)
    (hv : ∀ i, Summable fun a => v i a ^ 2) :
    colorMixtureVariance mix v = 0 ↔
      ∀ a i j, mix i = 0 ∨ mix j = 0 ∨ v i a = v j a := by
  constructor
  · intro h a
    apply (mixtureDefect_eq_zero_iff mix (fun i => v i a)).mp
    have hle := (colorVariance_summable mix hmix v hv).le_tsum a
      (fun b _ => mixtureDefect_nonneg mix (fun i => v i b))
    change mixtureDefect mix (fun i => v i a) ≤ colorMixtureVariance mix v at hle
    rw [h] at hle
    exact le_antisymm hle (mixtureDefect_nonneg mix (fun i => v i a))
  · intro h
    have he (a : A) : mixtureDefect mix (fun i => v i a) = 0 :=
      (mixtureDefect_eq_zero_iff mix (fun i => v i a)).mpr (h a)
    simp only [colorMixtureVariance, he, tsum_zero]

/-- Every positive-mass component equals the mean exactly when total variance vanishes. -/
theorem colorMixtureVariance_eq_zero_iff_mean (mix : I → NNReal)
    (hmix : (∑ i, (mix i : ℝ)) = 1) (v : I → A → ℝ)
    (hv : ∀ i, Summable fun a => v i a ^ 2) :
    colorMixtureVariance mix v = 0 ↔
      ∀ i, mix i ≠ 0 → ∀ a, v i a = colorMean mix v a := by
  rw [colorMixtureVariance_eq_zero_iff mix hmix v hv]
  constructor
  · intro h i hi a
    calc
      v i a = (∑ j, (mix j : ℝ)) * v i a := by rw [hmix, one_mul]
      _ = colorMean mix v a := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : mix j = 0
        · simp [hj]
        · rw [((h a i j).resolve_left hi).resolve_left hj]
  · intro h a i j
    by_cases hi : mix i = 0
    · exact Or.inl hi
    by_cases hj : mix j = 0
    · exact Or.inr (Or.inl hj)
    exact Or.inr (Or.inr ((h i hi a).trans (h j hj a).symm))

open scoped ComplexOrder
variable {X J : Type*} [Fintype X]

/-- Finite mixture of independent-color characters over a summable alphabet. -/
def wordCharacterMixture (mix : I → NNReal) (w : I → A → NNReal)
    (σ : Equiv.Perm X) : ℝ := ∑ i, (mix i : ℝ) * wordCharacter (w i) σ

/-- Mixture positivity follows by summing nonnegative multiples of positive Gram matrices. -/
theorem wordCharacterMixture_posSemidef [Fintype J] (mix : I → NNReal)
    (w : I → A → NNReal) (hw : ∀ i, Summable fun a => (w i a : ℝ))
    (g : J → Equiv.Perm X) :
    Matrix.PosSemidef (fun j k => (wordCharacterMixture mix w ((g j)⁻¹ * g k) : ℂ)) := by
  have h := Matrix.posSemidef_sum Finset.univ (fun i _ =>
    (wordCharacter_posSemidef (w i) (hw i) g).smul
      (Complex.zero_le_real.mpr (mix i).coe_nonneg))
  convert h using 1
  ext j k
  simp only [wordCharacterMixture, Complex.ofReal_sum, Complex.ofReal_mul,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

theorem wordCharacterMixture_one (mix : I → NNReal)
    (hmix : (∑ i, (mix i : ℝ)) = 1) (w : I → A → NNReal)
    (hw : ∀ i, Summable fun a => (w i a : ℝ)) (hm : ∀ i, (∑' a, (w i a : ℝ)) = 1) :
    wordCharacterMixture mix w (1 : Equiv.Perm X) = 1 := by
  have hval (i : I) : wordCharacter (w i) (1 : Equiv.Perm X) = 1 := by
    rw [wordCharacter_one _ (hw i), hm i, one_pow]
  simp only [wordCharacterMixture, hval, mul_one, hmix]

theorem wordCharacterMixture_conj (mix : I → NNReal) (w : I → A → NNReal)
    (σ τ : Equiv.Perm X) :
    wordCharacterMixture mix w (τ * σ * τ⁻¹) = wordCharacterMixture mix w σ := by
  simp only [wordCharacterMixture, wordCharacter_conj]

/-- Probability alphabets retain the same mixture under restriction by one fixed position. -/
theorem wordCharacterMixture_restriction (mix : I → NNReal) (w : I → A → NNReal)
    (hw : ∀ i, Summable fun a => (w i a : ℝ)) (hm : ∀ i, (∑' a, (w i a : ℝ)) = 1)
    (σ : Equiv.Perm X) :
    wordCharacterMixture mix w (Equiv.optionCongr σ) = wordCharacterMixture mix w σ := by
  have hval (i : I) : wordCharacter (w i) (Equiv.optionCongr σ) = wordCharacter (w i) σ := by
    rw [wordCharacter_optionCongr _ (hw i), hm i, one_mul]
  simp only [wordCharacterMixture, hval]

/-- A transposition reads the expected squared color mass. -/
theorem wordCharacterMixture_transposition (mix : I → NNReal) (w : I → A → NNReal) :
    wordCharacterMixture mix w (finRotate 2) = ∑ i, (mix i : ℝ) * ∑' a, (w i a : ℝ) ^ 2 := by
  simp only [wordCharacterMixture, show 2 = 1 + 1 from rfl, wordCharacter_finRotate]

end GaloisForLFunctions.SymmetricCharacters
