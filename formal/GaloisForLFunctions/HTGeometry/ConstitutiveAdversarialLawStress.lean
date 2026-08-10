import Mathlib

/-!
# Constitutive adversarial law stress

Prefix cylinders are laminar, so their static shattering dimension is one.  Nevertheless a
source-consistent adaptive challenge can force every deterministic response to fail for an
arbitrary finite number of rounds.  Fractional prediction lowers the per-round minimax loss to
one half but does not remove the adaptive horizon.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

def prefixCylinderContains (p b : List Bool) : Prop :=
  p <+: b

def PrefixSingletonShattered (p : List Bool) : Prop :=
  (∃ b, prefixCylinderContains p b) ∧
    (∃ b, ¬ prefixCylinderContains p b)

def PrefixPairShattered (p q : List Bool) : Prop :=
  (∃ b, prefixCylinderContains p b ∧ prefixCylinderContains q b) ∧
    (∃ b, prefixCylinderContains p b ∧ ¬ prefixCylinderContains q b) ∧
    (∃ b, ¬ prefixCylinderContains p b ∧ prefixCylinderContains q b) ∧
    (∃ b, ¬ prefixCylinderContains p b ∧ ¬ prefixCylinderContains q b)

theorem prefixSingletonShattered_false :
    PrefixSingletonShattered [false] := by
  constructor
  · exact ⟨[false], by simp [prefixCylinderContains]⟩
  · exact ⟨[true], by simp [prefixCylinderContains]⟩

theorem distinctPrefixes_not_pairShattered {p q : List Bool} (_hpq : p ≠ q) :
    ¬ PrefixPairShattered p q := by
  intro h
  rcases h with ⟨h₁₁, h₁₀, h₀₁, _h₀₀⟩
  rcases h₁₁ with ⟨b, hpb, hqb⟩
  rcases List.prefix_or_prefix_of_prefix hpb hqb with hpref | qpref
  · rcases h₀₁ with ⟨c, hnpc, hqc⟩
    exact hnpc (hpref.trans hqc)
  · rcases h₁₀ with ⟨c, hpc, hnqc⟩
    exact hnqc (qpref.trans hpc)

theorem prefixStaticDimensionOne_closed :
    PrefixSingletonShattered [false] ∧
      ∀ p q : List Bool, p ≠ q → ¬ PrefixPairShattered p q := by
  exact ⟨prefixSingletonShattered_false, fun _ _ => distinctPrefixes_not_pairShattered⟩

def adversarialPrefix (policy : List Bool → Bool) : ℕ → List Bool
  | 0 => []
  | n + 1 =>
      adversarialPrefix policy n ++ [policy (adversarialPrefix policy n)]

def adversarialQuery (policy : List Bool → Bool) (n : ℕ) : List Bool :=
  adversarialPrefix policy n ++ [false]

theorem adversarialPrefix_length (policy : List Bool → Bool) (n : ℕ) :
    (adversarialPrefix policy n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [adversarialPrefix, ih]

theorem adversarialPrefix_prefix_succ (policy : List Bool → Bool) (n : ℕ) :
    adversarialPrefix policy n <+: adversarialPrefix policy (n + 1) := by
  simp only [adversarialPrefix]
  exact List.prefix_append _ _

theorem adversarialPrefix_mono (policy : List Bool → Bool) {m n : ℕ} (hmn : m ≤ n) :
    adversarialPrefix policy m <+: adversarialPrefix policy n := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
      exact ih.trans (adversarialPrefix_prefix_succ policy n)

theorem distinctChildren_not_commonPrefix
    {p target : List Bool} {a b : Bool} (hab : a ≠ b) :
    ¬ (p ++ [a] <+: target ∧ p ++ [b] <+: target) := by
  rintro ⟨ha, hb⟩
  rcases List.prefix_or_prefix_of_prefix ha hb with habp | hbap
  · have heq : p ++ [a] = p ++ [b] := habp.eq_of_length_le (by simp)
    have hsingle : [a] = [b] := List.append_right_injective p heq
    exact hab (by simpa using hsingle)
  · have heq : p ++ [b] = p ++ [a] := hbap.eq_of_length_le (by simp)
    have hsingle : [b] = [a] := List.append_right_injective p heq
    exact hab (by simpa using hsingle.symm)

theorem adversarialQuery_membership_iff_prediction_false
    (policy : List Bool → Bool) {k d : ℕ} (hkd : k < d) :
    adversarialQuery policy k <+: adversarialPrefix policy d ↔
      policy (adversarialPrefix policy k) = false := by
  have hnext : adversarialPrefix policy (k + 1) <+: adversarialPrefix policy d :=
    adversarialPrefix_mono policy (Nat.succ_le_iff.mpr hkd)
  cases hpolicy : policy (adversarialPrefix policy k) with
  | false =>
      simpa [adversarialQuery, adversarialPrefix, hpolicy] using hnext
  | true =>
      have hnot : ¬ adversarialQuery policy k <+: adversarialPrefix policy d := by
        intro hquery
        apply distinctChildren_not_commonPrefix (p := adversarialPrefix policy k)
          (target := adversarialPrefix policy d) (a := false) (b := true) (by decide)
        refine ⟨?_, ?_⟩
        · simpa [adversarialQuery] using hquery
        · simpa [adversarialPrefix, hpolicy] using hnext
      simpa [hpolicy] using hnot

theorem adversarialTranscript_forces_every_round
    (policy : List Bool → Bool) (d : ℕ) :
    (adversarialPrefix policy d).length = d ∧
      ∀ k < d,
        (adversarialQuery policy k <+: adversarialPrefix policy d ↔
          policy (adversarialPrefix policy k) = false) := by
  exact ⟨adversarialPrefix_length policy d,
    fun _ hk => adversarialQuery_membership_iff_prediction_false policy hk⟩

def convexAdversarialNextBit (u : ℝ) : Bool :=
  if (1 / 2 : ℝ) ≤ u then true else false

def convexAdversarialLabel (u : ℝ) : Bool :=
  !convexAdversarialNextBit u

def binaryLinearLoss (u : ℝ) (label : Bool) : ℝ :=
  if label then 1 - u else u

theorem convexAdversarialLoss_ge_half (u : ℝ) :
    (1 / 2 : ℝ) ≤ binaryLinearLoss u (convexAdversarialLabel u) := by
  by_cases hu : (1 / 2 : ℝ) ≤ u
  · have huinv : (2 : ℝ)⁻¹ ≤ u := by
      simpa [one_div] using hu
    have hlabel : convexAdversarialLabel u = false := by
      simp [convexAdversarialLabel, convexAdversarialNextBit, huinv]
    rw [hlabel]
    simpa [binaryLinearLoss] using hu
  · have hu' : u < (1 / 2 : ℝ) := lt_of_not_ge hu
    have huinv : u < (2 : ℝ)⁻¹ := by
      simpa [one_div] using hu'
    have hlabel : convexAdversarialLabel u = true := by
      simp [convexAdversarialLabel, convexAdversarialNextBit, huinv]
    rw [hlabel]
    simp only [binaryLinearLoss, if_true]
    linarith

theorem halfPrediction_exact_loss (label : Bool) :
    binaryLinearLoss (1 / 2 : ℝ) label = 1 / 2 := by
  cases label <;> norm_num [binaryLinearLoss]

def convexAdversarialPolicy (policy : List Bool → ℝ) : List Bool → Bool :=
  fun p => convexAdversarialNextBit (policy p)

theorem convexAdversarialTranscript_membership
    (policy : List Bool → ℝ) {k d : ℕ} (hkd : k < d) :
    adversarialQuery (convexAdversarialPolicy policy) k <+:
        adversarialPrefix (convexAdversarialPolicy policy) d ↔
      convexAdversarialLabel
        (policy (adversarialPrefix (convexAdversarialPolicy policy) k)) = true := by
  rw [adversarialQuery_membership_iff_prediction_false _ hkd]
  simp [convexAdversarialPolicy, convexAdversarialLabel]

theorem convexAdversarialCumulativeLoss_ge_half
    (policy : List Bool → ℝ) (d : ℕ) :
    (d : ℝ) / 2 ≤
      ∑ k ∈ Finset.range d,
        binaryLinearLoss
          (policy (adversarialPrefix (convexAdversarialPolicy policy) k))
          (convexAdversarialLabel
            (policy (adversarialPrefix (convexAdversarialPolicy policy) k))) := by
  calc
    (d : ℝ) / 2 = ∑ _k ∈ Finset.range d, (1 / 2 : ℝ) := by
      simp [Finset.card_range]
      ring
    _ ≤ _ := by
      exact Finset.sum_le_sum fun k _hk =>
        convexAdversarialLoss_ge_half
          (policy (adversarialPrefix (convexAdversarialPolicy policy) k))

theorem constantHalfCumulativeLoss_exact (labels : ℕ → Bool) (d : ℕ) :
    (∑ k ∈ Finset.range d, binaryLinearLoss (1 / 2 : ℝ) (labels k)) =
      (d : ℝ) / 2 := by
  calc
    (∑ k ∈ Finset.range d, binaryLinearLoss (1 / 2 : ℝ) (labels k)) =
        ∑ _k ∈ Finset.range d, (1 / 2 : ℝ) := by
      apply Finset.sum_congr rfl
      intro k _hk
      exact halfPrediction_exact_loss (labels k)
    _ = (d : ℝ) / 2 := by
      simp [Finset.card_range]
      ring

theorem convexAdaptiveMinimaxValue_closed (d : ℕ) :
    (∀ policy : List Bool → ℝ,
      (d : ℝ) / 2 ≤
        ∑ k ∈ Finset.range d,
          binaryLinearLoss
            (policy (adversarialPrefix (convexAdversarialPolicy policy) k))
            (convexAdversarialLabel
              (policy (adversarialPrefix (convexAdversarialPolicy policy) k)))) ∧
      (∀ labels : ℕ → Bool,
        (∑ k ∈ Finset.range d, binaryLinearLoss (1 / 2 : ℝ) (labels k)) =
          (d : ℝ) / 2) := by
  exact ⟨fun policy => convexAdversarialCumulativeLoss_ge_half policy d,
    fun labels => constantHalfCumulativeLoss_exact labels d⟩

theorem constitutiveAdversarialLawStress_closed :
    PrefixSingletonShattered [false] ∧
      (∀ p q : List Bool, p ≠ q → ¬ PrefixPairShattered p q) ∧
      (∀ (policy : List Bool → Bool) (d : ℕ),
        (adversarialPrefix policy d).length = d ∧
          ∀ k < d,
            (adversarialQuery policy k <+: adversarialPrefix policy d ↔
              policy (adversarialPrefix policy k) = false)) ∧
      (∀ u : ℝ, (1 / 2 : ℝ) ≤
        binaryLinearLoss u (convexAdversarialLabel u)) ∧
      (∀ d : ℕ,
        (∀ policy : List Bool → ℝ,
          (d : ℝ) / 2 ≤
            ∑ k ∈ Finset.range d,
              binaryLinearLoss
                (policy (adversarialPrefix (convexAdversarialPolicy policy) k))
                (convexAdversarialLabel
                  (policy (adversarialPrefix (convexAdversarialPolicy policy) k)))) ∧
          (∀ labels : ℕ → Bool,
            (∑ k ∈ Finset.range d, binaryLinearLoss (1 / 2 : ℝ) (labels k)) =
              (d : ℝ) / 2)) := by
  exact ⟨prefixSingletonShattered_false,
    fun _ _ => distinctPrefixes_not_pairShattered,
    adversarialTranscript_forces_every_round,
    convexAdversarialLoss_ge_half,
    convexAdaptiveMinimaxValue_closed⟩

end

end GaloisForLFunctions.HTGeometry
