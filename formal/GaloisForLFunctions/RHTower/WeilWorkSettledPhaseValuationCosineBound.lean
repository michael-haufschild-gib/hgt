import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseDivisibilityFourier
import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseValuationMasks
import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseRationalBound

/-!
# Fixed valuation bounds for the actual source square convolution

Every exact valuation mask is a difference of two finite rational cosine
averages. Full source positivity therefore bounds its normalized Mellin value.
-/

open Complex Set Filter Topology
noncomputable section
namespace RHTower.WeilSingularArithmetic

def normalizedCoefficientMellin (f : ℕ → ℂ) (σ : ℝ) : ℝ :=
  (σ - 1) ^ 2 * (Gammaℝ (σ : ℂ) * LSeries f (σ : ℂ)).re

def BoundedNormalizedMellin (f : ℕ → ℂ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ σ : ℝ in 𝓝[>] 1, |normalizedCoefficientMellin f σ| ≤ C

theorem normalizedCoefficientMellin_sub {f g : ℕ → ℂ} {σ : ℝ}
    (hf : LSeriesSummable f (σ : ℂ)) (hg : LSeriesSummable g (σ : ℂ)) :
    normalizedCoefficientMellin (f - g) σ =
      normalizedCoefficientMellin f σ - normalizedCoefficientMellin g σ := by
  simp only [normalizedCoefficientMellin, LSeries_sub hf hg, mul_sub, Complex.sub_re]

theorem boundedNormalizedMellin_sub {f g : ℕ → ℂ}
    (hsf : ∀ σ : ℝ, 1 < σ → LSeriesSummable f (σ : ℂ))
    (hsg : ∀ σ : ℝ, 1 < σ → LSeriesSummable g (σ : ℂ))
    (hf : BoundedNormalizedMellin f) (hg : BoundedNormalizedMellin g) :
    BoundedNormalizedMellin (f - g) := by
  obtain ⟨C, hC, hf⟩ := hf
  obtain ⟨D, hD, hg⟩ := hg
  refine ⟨C + D, add_nonneg hC hD, ?_⟩
  filter_upwards [self_mem_nhdsWithin, hf, hg] with σ hσ hf hg
  rw [normalizedCoefficientMellin_sub (hsf σ hσ) (hsg σ hσ)]
  exact (abs_sub _ _).trans (add_le_add hf hg)

private theorem summable_sourceCosineCoeff {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (r : ℝ) {s : ℂ} (hs : 1 < s.re) : LSeriesSummable (sourceCosineCoeff lam r) s :=
  (sourceSquareCoeff_summable hW hs).norm.of_norm_bounded fun n =>
    LSeries.norm_term_le s (norm_sourceCosineCoeff_le lam r n)

theorem boundedNormalizedMellin_cosineMask {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (Q : ℕ) [NeZero Q] (w : ℕ → ℝ) (a : ZMod Q → ℝ)
    (ha : ∀ n : ℕ, w n =
      ∑ j : ZMod Q, a j * Real.cos (2 * Real.pi * ((n : ℝ) * (j.val / Q)))) :
    BoundedNormalizedMellin (fun n => (w n : ℂ) * sourceSquareCoeff lam n) := by
  classical
  have hq : 0 < Q := Nat.pos_of_ne_zero (NeZero.ne Q)
  choose C hC0 hC using fun j : ZMod Q =>
    exists_abs_sourceCosineSeries_rat_normalized_le hW j.val hq
  refine ⟨∑ j : ZMod Q, |a j| * C j,
    Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (hC0 j)), ?_⟩
  have hall := Filter.eventually_all.mpr hC
  filter_upwards [self_mem_nhdsWithin, hall] with σ hσ hCσ
  have hcoeff : (fun n => (w n : ℂ) * sourceSquareCoeff lam n) =
      ∑ j : ZMod Q, (a j : ℂ) • sourceCosineCoeff lam (j.val / Q) := by
    funext n
    simp only [ha n, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, sourceCosineCoeff, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hseries : LSeries (fun n => (w n : ℂ) * sourceSquareCoeff lam n) (σ : ℂ) =
      ∑ j : ZMod Q, (a j : ℂ) * sourceCosineSeries lam (j.val / Q) (σ : ℂ) := by
    have hj (j : ZMod Q) : LSeriesSummable
        ((a j : ℂ) • sourceCosineCoeff lam ((j.val : ℝ) / Q)) (σ : ℂ) :=
      LSeriesSummable.smul (a j : ℂ)
        (summable_sourceCosineCoeff hW ((j.val : ℝ) / Q) (s := (σ : ℂ)) hσ)
    rw [hcoeff, LSeries_sum (fun (j : ZMod Q) _ => hj j)]
    simp only [LSeries_smul, sourceCosineSeries]
  have he : normalizedCoefficientMellin
      (fun n => (w n : ℂ) * sourceSquareCoeff lam n) σ =
      ∑ j : ZMod Q, a j * ((σ - 1) ^ 2 * (Gammaℝ (σ : ℂ) *
        sourceCosineSeries lam (j.val / Q) (σ : ℂ)).re) := by
    rw [normalizedCoefficientMellin, hseries, Finset.mul_sum, Complex.re_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hj : Gammaℝ (σ : ℂ) * ((a j : ℂ) * sourceCosineSeries lam (j.val / Q) (σ : ℂ)) =
        (a j : ℂ) * (Gammaℝ (σ : ℂ) * sourceCosineSeries lam (j.val / Q) (σ : ℂ)) := by ring
    rw [hj]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  rw [he]
  calc
    _ ≤ ∑ j : ZMod Q, |a j * ((σ - 1) ^ 2 * (Gammaℝ (σ : ℂ) *
        sourceCosineSeries lam (j.val / Q) (σ : ℂ)).re)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := Finset.sum_le_sum fun j _ => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hCσ j) (abs_nonneg _)

def divisibilityPart (Q : ℕ) (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  (divisibilityMask Q n : ℂ) * f n

theorem summable_divisibilityPart (Q : ℕ) {f : ℕ → ℂ} {s : ℂ}
    (hf : LSeriesSummable f s) : LSeriesSummable (divisibilityPart Q f) s := by
  refine hf.norm.of_norm_bounded fun n => LSeries.norm_term_le s ?_
  by_cases hn : Q ∣ n <;> simp [divisibilityPart, divisibilityMask, hn]

theorem valuationPart_eq_sub_divisibilityPart (p k : ℕ) (f : ℕ → ℂ) :
    valuationPart p k f = divisibilityPart (p ^ k) f - divisibilityPart (p ^ (k + 1)) f := by
  funext n
  have hd : p ^ (k + 1) ∣ n → p ^ k ∣ n := fun h =>
    (show p ^ k ∣ p ^ (k + 1) by rw [pow_succ]; exact dvd_mul_right _ _).trans h
  by_cases hk : p ^ k ∣ n <;> by_cases hk1 : p ^ (k + 1) ∣ n <;>
    simp_all [valuationPart, valuationMask, divisibilityPart, divisibilityMask]

theorem boundedNormalizedMellin_divisibility_sourceSquare {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (Q : ℕ) [NeZero Q] :
    BoundedNormalizedMellin (divisibilityPart Q (sourceSquareCoeff lam)) :=
  boundedNormalizedMellin_cosineMask hW Q (divisibilityMask Q) (fun _ => (Q : ℝ)⁻¹)
    (divisibilityMask_cosine_expansion Q)

theorem boundedNormalizedMellin_valuation_sourceSquare {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {p : ℕ} (hp : p ≠ 0) (k : ℕ) :
    BoundedNormalizedMellin (valuationPart p k (sourceSquareCoeff lam)) := by
  letI : NeZero (p ^ k) := ⟨pow_ne_zero k hp⟩
  letI : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero (k + 1) hp⟩
  rw [valuationPart_eq_sub_divisibilityPart]
  exact boundedNormalizedMellin_sub
    (fun σ hσ => summable_divisibilityPart _
      (sourceSquareCoeff_summable hW (s := (σ : ℂ)) hσ))
    (fun σ hσ => summable_divisibilityPart _
      (sourceSquareCoeff_summable hW (s := (σ : ℂ)) hσ))
    (boundedNormalizedMellin_divisibility_sourceSquare hW _)
    (boundedNormalizedMellin_divisibility_sourceSquare hW _)

end RHTower.WeilSingularArithmetic
