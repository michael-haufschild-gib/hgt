import GaloisForLFunctions.BiScaleUncertainty.SignedGramResponseOptimality

/-!
# An explicit monotone physical response ladder

Accept the least-price response when its actual full-Gram coefficient improves.
Its exact remaining dual budget is the minimum of the incumbent gap and the
response curvature remainder. Physical extension followed by this accepted
step constructs monotone coefficients at increasing cutoffs, with finite
produced limit and certified error to the optimized limiting coefficient.
-/

set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators CompactlySupported ENNReal
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm
namespace GaloisForLFunctions.BiScaleUncertainty.PhysicalCollarPartition
noncomputable section
variable {n : ℕ}

def gramResponseStep (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) :
    PhysicalCollarPartition n := by
  classical
  exact if ρ.signedGramCoefficient f ≤ (ρ.gramMinimumResponse f).signedGramCoefficient f
    then ρ.gramMinimumResponse f else ρ

theorem gramResponseStep_coefficient (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) :
    (ρ.gramResponseStep f).signedGramCoefficient f =
      max (ρ.signedGramCoefficient f) ((ρ.gramMinimumResponse f).signedGramCoefficient f) := by
  classical
  unfold gramResponseStep
  split_ifs with h
  · exact (max_eq_right h).symm
  · exact (max_eq_left (lt_of_not_ge h).le).symm

theorem signedGramCoefficient_le_responseStep (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) :
    ρ.signedGramCoefficient f ≤ (ρ.gramResponseStep f).signedGramCoefficient f := by
  rw [ρ.gramResponseStep_coefficient f]
  exact le_max_left _ _

theorem gramResponseStep_exact_gain (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) :
    (ρ.gramResponseStep f).signedGramCoefficient f - ρ.signedGramCoefficient f =
      max 0 (ρ.gramGap f - ∫ y in Ioo 0 logarithmicCollarRadius,
        ρ.gramRemainder (ρ.gramMinimumResponse f) f y) := by
  rw [ρ.gramResponseStep_coefficient f, ← max_sub_sub_right, sub_self,
    ρ.gramMinimumResponse_exact_gain f]

/-- The accepted response spends exactly the smaller of the two dual error budgets. -/
theorem gramResponseStep_dual_deficit (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) :
    ρ.signedGramCoefficient f + ρ.gramGap f - (ρ.gramResponseStep f).signedGramCoefficient f =
      min (ρ.gramGap f) (∫ y in Ioo 0 logarithmicCollarRadius,
        ρ.gramRemainder (ρ.gramMinimumResponse f) f y) := by
  rw [show ρ.signedGramCoefficient f + ρ.gramGap f - (ρ.gramResponseStep f).signedGramCoefficient f =
    ρ.gramGap f - ((ρ.gramResponseStep f).signedGramCoefficient f - ρ.signedGramCoefficient f) by ring,
    ρ.gramResponseStep_exact_gain f]
  by_cases h : ρ.gramGap f ≤ ∫ y in Ioo 0 logarithmicCollarRadius,
      ρ.gramRemainder (ρ.gramMinimumResponse f) f y
  · simp only [max_eq_left (sub_nonpos.mpr h), min_eq_left h, sub_zero]
  · have hle := (lt_of_not_ge h).le
    rw [max_eq_right (sub_nonneg.mpr hle), min_eq_right hle]
    ring

theorem gramResponseStep_optimal_error (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) :
    0 ≤ signedGramOptimalCoefficient f n - (ρ.gramResponseStep f).signedGramCoefficient f ∧
      signedGramOptimalCoefficient f n - (ρ.gramResponseStep f).signedGramCoefficient f ≤
        min (ρ.gramGap f) (∫ y in Ioo 0 logarithmicCollarRadius,
          ρ.gramRemainder (ρ.gramMinimumResponse f) f y) := by
  have hl := (ρ.gramResponseStep f).signedGramCoefficient_le_optimal f
  have hu := (ρ.signedGramOptimalCoefficient_gap_bounds f).2
  have hd := ρ.gramResponseStep_dual_deficit f
  constructor <;> linarith only [hl, hu, hd]

theorem gramResponseStep_limiting_error (ρ : PhysicalCollarPartition n) (f : C_c(ℝ, ℝ)) :
    0 ≤ limitingSignedGramCoefficient f - (ρ.gramResponseStep f).signedGramCoefficient f ∧
      limitingSignedGramCoefficient f - (ρ.gramResponseStep f).signedGramCoefficient f ≤
        min (ρ.gramGap f) (∫ y in Ioo 0 logarithmicCollarRadius,
          ρ.gramRemainder (ρ.gramMinimumResponse f) f y) +
            2 * autocorr f 0 * collarCutoffTailMass n := by
  have hg := ρ.gramResponseStep_optimal_error f
  have ht := limitingSignedGramCoefficient_sub_bounds f n
  constructor <;> linarith only [hg.1, hg.2, ht.1, ht.2]

/-- Start with the explicit one-collar partition, then extend and accept a price response. -/
def gramResponseLadder (f : C_c(ℝ, ℝ)) : (n : ℕ) → PhysicalCollarPartition n
  | 0 => equalMultiplicity 0
  | n + 1 => ((gramResponseLadder f n).extend (Nat.le_succ n)).gramResponseStep f

def gramResponseCoefficient (f : C_c(ℝ, ℝ)) (n : ℕ) : ℝ :=
  (gramResponseLadder f n).signedGramCoefficient f

theorem gramResponseCoefficient_monotone (f : C_c(ℝ, ℝ)) :
    Monotone (gramResponseCoefficient f) := by
  apply monotone_nat_of_le_succ
  intro n
  exact ((gramResponseLadder f n).signedGramCoefficient_le_extend (Nat.le_succ n) f).trans
    (((gramResponseLadder f n).extend (Nat.le_succ n)).signedGramCoefficient_le_responseStep f)

theorem gramResponseCoefficient_bounds (f : C_c(ℝ, ℝ)) (n : ℕ) :
    0 ≤ gramResponseCoefficient f n ∧
      gramResponseCoefficient f n ≤ signedGramOptimalCoefficient f n :=
  ⟨((gramResponseLadder f n).signedGramCoefficient_bounds f).1,
    (gramResponseLadder f n).signedGramCoefficient_le_optimal f⟩

theorem gramResponseCoefficient_bddAbove (f : C_c(ℝ, ℝ)) :
    BddAbove (Set.range (gramResponseCoefficient f)) := by
  refine ⟨2 * autocorr f 0 * collarTailMass, ?_⟩
  rintro c ⟨n, rfl⟩
  exact ((gramResponseLadder f n).signedGramCoefficient_bounds f).2

def limitingGramResponseCoefficient (f : C_c(ℝ, ℝ)) : ℝ :=
  ⨆ n, gramResponseCoefficient f n

theorem gramResponseCoefficient_le_limit (f : C_c(ℝ, ℝ)) (n : ℕ) :
    gramResponseCoefficient f n ≤ limitingGramResponseCoefficient f :=
  le_ciSup (gramResponseCoefficient_bddAbove f) n

theorem limitingGramResponseCoefficient_bounds (f : C_c(ℝ, ℝ)) :
    0 ≤ limitingGramResponseCoefficient f ∧
      limitingGramResponseCoefficient f ≤ limitingSignedGramCoefficient f :=
  ⟨(gramResponseCoefficient_bounds f 0).1.trans (gramResponseCoefficient_le_limit f 0),
    ciSup_le fun n => (gramResponseCoefficient_bounds f n).2.trans
      (signedGramOptimalCoefficient_le_limit f n)⟩

theorem gramResponseCoefficient_tendsto (f : C_c(ℝ, ℝ)) :
    Filter.Tendsto (gramResponseCoefficient f) Filter.atTop
      (nhds (limitingGramResponseCoefficient f)) :=
  tendsto_atTop_ciSup (gramResponseCoefficient_monotone f) (gramResponseCoefficient_bddAbove f)

theorem gramResponseCoefficient_limiting_error (f : C_c(ℝ, ℝ)) (n : ℕ) :
    0 ≤ limitingSignedGramCoefficient f - gramResponseCoefficient f n ∧
      limitingSignedGramCoefficient f - gramResponseCoefficient f n ≤
        (gramResponseLadder f n).gramGap f + 2 * autocorr f 0 * collarCutoffTailMass n :=
  (gramResponseLadder f n).limitingSignedGramCoefficient_trial_bounds f

/-- The next cutoff has the smaller gap-or-curvature certificate of its explicit extension. -/
theorem gramResponseCoefficient_successor_error (f : C_c(ℝ, ℝ)) (n : ℕ) :
    0 ≤ limitingSignedGramCoefficient f - gramResponseCoefficient f (n + 1) ∧
      limitingSignedGramCoefficient f - gramResponseCoefficient f (n + 1) ≤
        min (((gramResponseLadder f n).extend (Nat.le_succ n)).gramGap f)
          (∫ y in Ioo 0 logarithmicCollarRadius,
            ((gramResponseLadder f n).extend (Nat.le_succ n)).gramRemainder
              (((gramResponseLadder f n).extend (Nat.le_succ n)).gramMinimumResponse f) f y) +
                2 * autocorr f 0 * collarCutoffTailMass (n + 1) :=
  ((gramResponseLadder f n).extend (Nat.le_succ n)).gramResponseStep_limiting_error f

theorem gramResponseCoefficient_source_energy (f : C_c(ℝ, ℝ)) (n : ℕ) :
    ENNReal.ofReal (gramResponseCoefficient f n) ≤
      ∫⁻ x in Ioo 0 (logarithmicCollarEndpoint n),
        continuousArchIncrementDensity (compactAutocorrKernel f) x :=
  (gramResponseLadder f n).signedGramCoefficient_source_energy f

theorem gramResponseNormalizedCoefficient_monotone (f : C_c(ℝ, ℝ)) :
    Monotone (fun n => gramResponseCoefficient f n / autocorr f 0) := by
  intro n m h
  exact div_le_div_of_nonneg_right (gramResponseCoefficient_monotone f h) (autocorr_zero_nonneg f)

/-- Produced monotone lower bounds and a quantitative error certificate for actual smooth sources. -/
theorem gramResponse_normalized_source_certificate (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) (n : ℕ) :
    gramResponseCoefficient f n / autocorr f 0 ≤
        limitingGramResponseCoefficient f / autocorr f 0 ∧
      limitingGramResponseCoefficient f / autocorr f 0 ≤ biScaleLevyEnergy f / autocorr f 0 ∧
      limitingSignedGramCoefficient f / autocorr f 0 - gramResponseCoefficient f n / autocorr f 0 ≤
        (gramResponseLadder f n).gramGap f / autocorr f 0 +
          8 * Real.exp (logarithmicCollarRadius / 2) /
            (Real.sqrt ((n + 2 : ℕ) : ℝ) * (1 - 2 / (((n + 2 : ℕ) : ℝ) ^ 2))) := by
  refine ⟨div_le_div_of_nonneg_right (gramResponseCoefficient_le_limit f n) (autocorr_zero_nonneg f),
    ?_, ((gramResponseLadder f n).limitingSignedGramNormalized_trial_bounds f).2⟩
  exact div_le_div_of_nonneg_right
    ((limitingGramResponseCoefficient_bounds f).2.trans (limitingSignedGramCoefficient_le_energy f hf))
    (autocorr_zero_nonneg f)

end
end GaloisForLFunctions.BiScaleUncertainty.PhysicalCollarPartition
