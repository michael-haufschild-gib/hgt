import GaloisForLFunctions.BiScaleUncertainty.RegularizedGramDescent
import GaloisForLFunctions.BiScaleUncertainty.SignedGramCutoffHierarchy

/-!
# A finite quantitative producer for full signed-Gram optimization

Repeated measurable minimum-price responses use the explicit step `2/(t+2)`.
The actual original objective is within a prescribed error of every admissible
competitor after a source-independent finite number of iterations. No attained
optimizer, coercivity constant, or external convergence premise is used.
-/

set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators CompactlySupported
open RHTower.ArchimedeanAnomaly
namespace GaloisForLFunctions.BiScaleUncertainty.PhysicalCollarPartition
noncomputable section
variable {n : ℕ}

def regularizedStepSize (t : ℕ) : Icc (0 : ℝ) 1 :=
  ⟨2 / ((t : ℝ) + 2), by
    constructor
    · positivity
    · apply (div_le_iff₀ (by positivity : 0 < (t : ℝ) + 2)).2
      have ht : 0 ≤ (t : ℝ) := Nat.cast_nonneg t
      linarith only [ht]⟩

def regularizedIterate (f : C_c(ℝ, ℝ)) (ε : ℝ) (n : ℕ) : ℕ → PhysicalCollarPartition n
  | 0 => equalMultiplicity n
  | t + 1 => (regularizedIterate f ε n t).mixture
      ((regularizedIterate f ε n t).regularizedMinimumResponse f ε) (regularizedStepSize t)

theorem regularizedIterate_recurrence (f : C_c(ℝ, ℝ)) {ε : ℝ} (hε : 0 < ε)
    (η : PhysicalCollarPartition n) (t : ℕ) :
    η.regularizedGramCoefficient f ε - (regularizedIterate f ε n (t + 1)).regularizedGramCoefficient f ε ≤
      (1 - 2 / ((t : ℝ) + 2)) *
        (η.regularizedGramCoefficient f ε - (regularizedIterate f ε n t).regularizedGramCoefficient f ε) +
        regularizedCurvature f n ε * (2 / ((t : ℝ) + 2)) ^ 2 := by
  have hg := (regularizedIterate f ε n t).regularizedGram_damped_gain f hε (regularizedStepSize t)
  have hc := mul_le_mul_of_nonneg_left
    ((regularizedIterate f ε n t).regularizedGram_comparison η f hε.le)
    (regularizedStepSize t).property.1
  change 2 / ((t : ℝ) + 2) * _ - regularizedCurvature f n ε * (2 / ((t : ℝ) + 2)) ^ 2 ≤
    (regularizedIterate f ε n (t + 1)).regularizedGramCoefficient f ε - _ at hg
  change 2 / ((t : ℝ) + 2) * _ ≤ 2 / ((t : ℝ) + 2) * _ at hc
  nlinarith only [hg, hc]

private theorem quadratic_recurrence_bound (B : ℝ) (hB : 0 ≤ B) (E : ℕ → ℝ)
    (h : ∀ t : ℕ, E (t + 1) ≤ (1 - 2 / ((t : ℝ) + 2)) * E t + B * (2 / ((t : ℝ) + 2)) ^ 2) :
    ∀ t : ℕ, E (t + 1) ≤ 4 * B / ((t : ℝ) + 3) := by
  intro t
  induction t with
  | zero =>
    have h0 := h 0
    norm_num at h0 ⊢
    linarith only [h0, hB]
  | succ t ih =>
    let x : ℝ := (t : ℝ) + 3
    have hx : 0 < x := by dsimp [x]; positivity
    have hxx : 0 < x + 1 := by linarith only [hx]
    have hx2 : 0 < x ^ 2 := by positivity
    have hcoef : 0 ≤ 1 - 2 / x := by
      apply sub_nonneg.mpr
      apply (div_le_iff₀ hx).2
      dsimp [x]
      have ht : 0 ≤ (t : ℝ) := Nat.cast_nonneg t
      linarith only [ht]
    have hm := mul_le_mul_of_nonneg_left ih hcoef
    have hr := h (t + 1)
    have he : (1 - 2 / x) * (4 * B / x) + B * (2 / x) ^ 2 = 4 * B * (x - 1) / x ^ 2 := by
      field_simp [hx.ne']
      ring
    have hu : 4 * B * (x - 1) / x ^ 2 ≤ 4 * B / (x + 1) := by
      apply (div_le_div_iff₀ hx2 hxx).2
      nlinarith only [hB]
    have hb : (1 - 2 / x) * (4 * B / x) + B * (2 / x) ^ 2 ≤ 4 * B / (x + 1) := by
      rw [he]
      exact hu
    dsimp [x] at hm hb
    norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_succ, add_assoc] at hr hb ⊢
    nlinarith only [hm, hr, hb]

/-- Uniform competitor error after finitely many actual physical updates. -/
theorem regularizedIterate_error (f : C_c(ℝ, ℝ)) {ε : ℝ} (hε : 0 < ε)
    (η : PhysicalCollarPartition n) (t : ℕ) :
    η.regularizedGramCoefficient f ε - (regularizedIterate f ε n (t + 1)).regularizedGramCoefficient f ε ≤
      4 * regularizedCurvature f n ε / ((t : ℝ) + 3) :=
  quadratic_recurrence_bound _ (regularizedCurvature_nonneg f n hε.le)
    (fun t => η.regularizedGramCoefficient f ε - (regularizedIterate f ε n t).regularizedGramCoefficient f ε)
    (regularizedIterate_recurrence f hε η) t

/-- Reconciliation with the unsmoothed source coefficient costs only one error budget. -/
theorem regularizedIterate_original_error (f : C_c(ℝ, ℝ)) {ε : ℝ} (hε : 0 < ε)
    (η : PhysicalCollarPartition n) (t : ℕ) :
    η.signedGramCoefficient f - (regularizedIterate f ε n (t + 1)).signedGramCoefficient f ≤
      ε * logarithmicCollarRadius * autocorr f 0 +
        4 * regularizedCurvature f n ε / ((t : ℝ) + 3) := by
  have he := regularizedIterate_error f hε η t
  have hη := η.regularizedGramCoefficient_error f hε.le
  have hρ := (regularizedIterate f ε n (t + 1)).regularizedGramCoefficient_error f hε.le
  linarith only [he, hη.2, hρ.1]

def gramProducerIterations (n k : ℕ) : ℕ :=
  ⌈8 * fibreMassBound n * transportedMass n * ((k : ℝ) + 1) ^ 2⌉₊

/-- A finite, completely specified physical partition at any requested accuracy. -/
def quantitativeGramProducer (f : C_c(ℝ, ℝ)) (n k : ℕ) : PhysicalCollarPartition n :=
  regularizedIterate f (1 / ((k : ℝ) + 1)) n (gramProducerIterations n k + 1)

private theorem producer_curvature_budget (f : C_c(ℝ, ℝ)) (n k : ℕ) :
    4 * regularizedCurvature f n (1 / ((k : ℝ) + 1)) /
        ((gramProducerIterations n k : ℝ) + 3) ≤ autocorr f 0 / ((k : ℝ) + 1) := by
  have hk : 0 < (k : ℝ) + 1 := by positivity
  have ht : 0 < (gramProducerIterations n k : ℝ) + 3 := by positivity
  have hc := Nat.le_ceil (8 * fibreMassBound n * transportedMass n * ((k : ℝ) + 1) ^ 2)
  change _ ≤ (gramProducerIterations n k : ℝ) at hc
  have hm := mul_le_mul_of_nonneg_left hc (autocorr_zero_nonneg f)
  apply (div_le_div_iff₀ ht hk).2
  have he : 4 * regularizedCurvature f n (1 / ((k : ℝ) + 1)) * ((k : ℝ) + 1) =
      autocorr f 0 * (8 * fibreMassBound n * transportedMass n * ((k : ℝ) + 1) ^ 2) := by
    unfold regularizedCurvature
    field_simp [hk.ne']
    ring
  rw [he]
  nlinarith only [hm, autocorr_zero_nonneg f]

/-- Unconditional allocation error, with a work count depending only on cutoff and accuracy. -/
theorem quantitativeGramProducer_competitor_error (f : C_c(ℝ, ℝ)) (k : ℕ)
    (η : PhysicalCollarPartition n) :
    η.signedGramCoefficient f - (quantitativeGramProducer f n k).signedGramCoefficient f ≤
      autocorr f 0 * (logarithmicCollarRadius + 1) / ((k : ℝ) + 1) := by
  have hε : 0 < 1 / ((k : ℝ) + 1) := by positivity
  have he := regularizedIterate_original_error f hε η (gramProducerIterations n k)
  have hb := producer_curvature_budget f n k
  have hid : 1 / ((k : ℝ) + 1) * logarithmicCollarRadius * autocorr f 0 +
      autocorr f 0 / ((k : ℝ) + 1) = autocorr f 0 * (logarithmicCollarRadius + 1) / ((k : ℝ) + 1) := by
    ring
  change η.signedGramCoefficient f - (quantitativeGramProducer f n k).signedGramCoefficient f ≤ _ at he
  linarith only [he, hb, hid]

theorem quantitativeGramProducer_error (f : C_c(ℝ, ℝ)) (n k : ℕ) :
    0 ≤ signedGramOptimalCoefficient f n - (quantitativeGramProducer f n k).signedGramCoefficient f ∧
    signedGramOptimalCoefficient f n - (quantitativeGramProducer f n k).signedGramCoefficient f ≤
      autocorr f 0 * (logarithmicCollarRadius + 1) / ((k : ℝ) + 1) := by
  refine ⟨sub_nonneg.mpr ((quantitativeGramProducer f n k).signedGramCoefficient_le_optimal f), ?_⟩
  have hu : signedGramOptimalCoefficient f n ≤ (quantitativeGramProducer f n k).signedGramCoefficient f +
      autocorr f 0 * (logarithmicCollarRadius + 1) / ((k : ℝ) + 1) := by
    apply csSup_le
    · exact ⟨(equalMultiplicity n).signedGramCoefficient f, equalMultiplicity n, rfl⟩
    · rintro c ⟨η, rfl⟩
      have h := quantitativeGramProducer_competitor_error f k η
      linarith only [h]
  linarith only [hu]

end
end GaloisForLFunctions.BiScaleUncertainty.PhysicalCollarPartition
