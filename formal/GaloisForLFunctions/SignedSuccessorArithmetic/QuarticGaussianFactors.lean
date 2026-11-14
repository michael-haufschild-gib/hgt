import GaloisForLFunctions.SignedSuccessorArithmetic.QuarticGaussCorrelation
import GaloisForLFunctions.RHTower.GaussianTwoSquaresCount

/-!
# Gaussian prime factors from quartic successor counts

The four nonzero values of a quartic character are Gaussian units. Differences
of their occurrence counts give the two integer coordinates of its successor
correlation. For the residue sources at five and forty-one, the exact norm law
therefore produces Gaussian prime factors of those rational primes. Their
squares also determine the fourth powers of the corresponding Gauss sums.
-/

noncomputable section
open scoped Classical
open Complex Finset RHTower RHTower.GaussianTwoSquares

namespace GaloisForLFunctions.SignedSuccessorArithmetic

local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
local instance : Fact (Nat.Prime 41) := ⟨by norm_num⟩

/-- Gaussian coordinates obtained by counting the four unit values. -/
def gaussianUnitCounts {A : Type*} [Fintype A] (f : A → ℂ) : GaussianInt :=
  ⟨((univ.filter fun x => f x = 1).card : ℤ) - (univ.filter fun x => f x = -1).card,
    ((univ.filter fun x => f x = I).card : ℤ) - (univ.filter fun x => f x = -I).card⟩

private theorem fourth_root_values {z : ℂ} (hz : z ^ 4 = 1) :
    z = 1 ∨ z = -1 ∨ z = I ∨ z = -I := by
  have h : (z - 1) * (z + 1) * (z - I) * (z + I) = 0 := by
    linear_combination hz - (z ^ 2 - 1) * I_sq
  rcases mul_eq_zero.mp h with h | h
  · rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact Or.inl (sub_eq_zero.mp h)
      · exact Or.inr (Or.inl (eq_neg_of_add_eq_zero_left h))
    · exact Or.inr (Or.inr (Or.inl (sub_eq_zero.mp h)))
  · exact Or.inr (Or.inr (Or.inr (eq_neg_of_add_eq_zero_left h)))

private theorem quartic_values {F : Type*} [Field F] (χ : MulChar F ℂ)
    (hχ : χ ^ 4 = 1) (x : F) :
    χ x = 0 ∨ χ x = 1 ∨ χ x = -1 ∨ χ x = I ∨ χ x = -I := by
  by_cases hx : x = 0
  · left
    rw [hx, MulChar.map_zero]
  · right
    apply fourth_root_values
    have h := congrArg (fun η : MulChar F ℂ => η x) hχ
    rw [MulChar.pow_apply' _ (by norm_num), MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)] at h
    exact h

private theorem gaussianUnitCounts_embedding {A : Type*} [Fintype A] (f : A → ℂ)
    (hf : ∀ x, f x = 0 ∨ f x = 1 ∨ f x = -1 ∨ f x = I ∨ f x = -I) :
    (gaussianUnitCounts f : ℂ) = ∑ x, f x := by
  have hterm (x : A) : f x =
      ((if f x = 1 then 1 else 0) - (if f x = -1 then 1 else 0)) +
        ((if f x = I then 1 else 0) - (if f x = -I then 1 else 0)) * I := by
    rcases hf x with h | h | h | h | h <;> rw [h] <;> norm_num [Complex.ext_iff]
  symm
  calc
    ∑ x, f x = ∑ x,
        (((if f x = 1 then 1 else 0) - (if f x = -1 then 1 else 0)) +
          ((if f x = I then 1 else 0) - (if f x = -I then 1 else 0)) * I) :=
      sum_congr rfl (fun x _ => hterm x)
    _ = (gaussianUnitCounts f : ℂ) := by
      simp only [sum_add_distrib, ← sum_mul, sum_sub_distrib, sum_boole,
        gaussianUnitCounts, GaussianInt.toComplex_def, Int.cast_sub, Int.cast_natCast]

private theorem successor_counts_embedding {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (hχ : χ ^ 4 = 1) :
    (gaussianUnitCounts (fun x : F => χ x * χ (x + 1)) : ℂ) = charSuccCorr χ χ := by
  apply gaussianUnitCounts_embedding
  intro x
  simpa only [map_mul] using quartic_values χ hχ (x * (x + 1))

/-- The Gaussian factor encoded by the actual quartic successor statistic at five. -/
def fiveQuarticGaussianFactor : GaussianInt :=
  gaussianUnitCounts (fun x : ZMod 5 =>
    deningerQ8FiveResidueQuarticChar x * deningerQ8FiveResidueQuarticChar (x + 1))

/-- The Gaussian factor encoded by the actual quartic successor statistic at forty-one. -/
def fortyOneQuarticGaussianFactor : GaussianInt :=
  gaussianUnitCounts (fun x : ZMod 41 =>
    deningerQ8FortyOneResidueQuarticChar x * deningerQ8FortyOneResidueQuarticChar (x + 1))

/-- The coordinate counts recover the exact complex correlation at five. -/
theorem fiveQuarticGaussianFactor_embedding :
    (fiveQuarticGaussianFactor : ℂ) =
      charSuccCorr deningerQ8FiveResidueQuarticChar deningerQ8FiveResidueQuarticChar :=
  successor_counts_embedding _ deningerQ8FiveResidueQuarticChar_fourth_eq_one

/-- The coordinate counts recover the exact complex correlation at forty-one. -/
theorem fortyOneQuarticGaussianFactor_embedding :
    (fortyOneQuarticGaussianFactor : ℂ) =
      charSuccCorr deningerQ8FortyOneResidueQuarticChar deningerQ8FortyOneResidueQuarticChar := by
  apply successor_counts_embedding
  rw [← deningerQ8FortyOneResidueQuarticChar_orderOf]
  exact pow_orderOf_eq_one _

/-- Square-root cancellation gives an integral Gaussian norm of five. -/
theorem fiveQuarticGaussianFactor_norm : fiveQuarticGaussianFactor.norm = 5 := by
  have h := five_quartic_successor_norm_sq
  rw [← fiveQuarticGaussianFactor_embedding, ← Complex.normSq_eq_norm_sq,
    ← GaussianInt.intCast_real_norm] at h
  exact_mod_cast h

/-- Square-root cancellation gives an integral Gaussian norm of forty-one. -/
theorem fortyOneQuarticGaussianFactor_norm : fortyOneQuarticGaussianFactor.norm = 41 := by
  have h := fortyOne_quartic_successor_norm_sq
  rw [← fortyOneQuarticGaussianFactor_embedding, ← Complex.normSq_eq_norm_sq,
    ← GaussianInt.intCast_real_norm] at h
  exact_mod_cast h

/-- The quartic count at five is a Gaussian prime. -/
theorem fiveQuarticGaussianFactor_prime : Prime fiveQuarticGaussianFactor :=
  prime_of_norm_prime Nat.prime_five fiveQuarticGaussianFactor_norm

/-- The quartic count at forty-one is a Gaussian prime. -/
theorem fortyOneQuarticGaussianFactor_prime : Prime fortyOneQuarticGaussianFactor :=
  prime_of_norm_prime (by norm_num : Nat.Prime 41) fortyOneQuarticGaussianFactor_norm

/-- The successor statistic supplies the Gaussian splitting of five. -/
theorem fiveQuarticGaussianFactor_split :
    fiveQuarticGaussianFactor * star fiveQuarticGaussianFactor = (5 : GaussianInt) := by
  rw [← Zsqrtd.norm_eq_mul_conj, fiveQuarticGaussianFactor_norm]
  rfl

/-- The successor statistic supplies the Gaussian splitting of forty-one. -/
theorem fortyOneQuarticGaussianFactor_split :
    fortyOneQuarticGaussianFactor * star fortyOneQuarticGaussianFactor = (41 : GaussianInt) := by
  rw [← Zsqrtd.norm_eq_mul_conj, fortyOneQuarticGaussianFactor_norm]
  rfl

/-- The quartic Gauss fourth power at five retains the square of its Gaussian prime factor. -/
theorem five_quartic_gauss_gaussian_factor :
    gaussSum deningerQ8FiveResidueQuarticChar ZMod.stdAddChar ^ 4 =
      5 * (fiveQuarticGaussianFactor : ℂ) ^ 2 := by
  rw [fiveQuarticGaussianFactor_embedding, five_quartic_gauss_fourth]

/-- The same Gaussian-factor identity holds for the actual residue source at forty-one. -/
theorem fortyOne_quartic_gauss_gaussian_factor :
    gaussSum deningerQ8FortyOneResidueQuarticChar ZMod.stdAddChar ^ 4 =
      41 * (fortyOneQuarticGaussianFactor : ℂ) ^ 2 := by
  rw [fortyOneQuarticGaussianFactor_embedding, fortyOne_quartic_gauss_fourth]

end GaloisForLFunctions.SignedSuccessorArithmetic
