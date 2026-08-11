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

/-- Binary words of a fixed length are counted by powers of two. -/
theorem card_lengthWords (n : ℕ) : Nat.card {c : List Bool // c.length = n} = 2 ^ n := by
  have h : Nat.card (List.Vector Bool n) = 2 ^ n := by
    rw [Nat.card_eq_fintype_card, card_vector]
    simp
  exact h

/-- **Version space count.**  After `k` rounds the source-consistent laws are exactly the
completions of the current prefix, so there are `2 ^ (d - k)` of them. -/
theorem versionSpace_card (policy : List Bool → Bool) {k d : ℕ} (hk : k ≤ d) :
    Nat.card {b : List Bool //
        b.length = d ∧ prefixCylinderContains (adversarialPrefix policy k) b} = 2 ^ (d - k) := by
  have hlen : (adversarialPrefix policy k).length = k := adversarialPrefix_length policy k
  have e : {b : List Bool //
      b.length = d ∧ prefixCylinderContains (adversarialPrefix policy k) b} ≃
      {c : List Bool // c.length = d - k} := by
    refine
      { toFun := fun b => ⟨b.1.drop k, ?_⟩
        invFun := fun c => ⟨adversarialPrefix policy k ++ c.1, ?_, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · rw [List.length_drop, b.2.1]
    · rw [List.length_append, hlen, c.2]
      omega
    · exact List.prefix_append _ _
    · rintro ⟨bl, hlend, hpref⟩
      apply Subtype.ext
      have hpre : bl.take k = adversarialPrefix policy k := by
        rw [prefixCylinderContains, List.prefix_iff_eq_take, hlen] at hpref
        exact hpref.symm
      show adversarialPrefix policy k ++ bl.drop k = bl
      rw [← hpre, List.take_append_drop]
    · intro c
      apply Subtype.ext
      show (adversarialPrefix policy k ++ c.1).drop k = c.1
      exact List.drop_left' hlen
  rw [Nat.card_congr e, card_lengthWords]

/-- A depth-`r` shattered challenge tree over length-`d` source laws: every label history is
realized by some law, and the test asked at stage `k` depends only on the earlier labels. -/
def ShatteredChallengeDepth (d r : ℕ) (query : ∀ k : ℕ, (Fin k → Bool) → List Bool) : Prop :=
  ∀ y : Fin r → Bool, ∃ b : List Bool, b.length = d ∧
    ∀ k : Fin r,
      (prefixCylinderContains
        (query (k : ℕ) fun j : Fin (k : ℕ) => y ⟨(j : ℕ), j.2.trans k.2⟩) b ↔ y k = true)

/-- **Sequential dimension bound.**  Distinct label histories of a shattered challenge tree need
distinct source laws, so a depth-`r` tree over length-`d` laws forces `r ≤ d`. -/
theorem shatteredChallengeDepth_le (d r : ℕ) (query : ∀ k : ℕ, (Fin k → Bool) → List Bool)
    (h : ShatteredChallengeDepth d r query) : r ≤ d := by
  classical
  letI : Fintype {l : List Bool // l.length = d} := List.Vector.instFintype
  choose f hflen hfspec using h
  have hinj : Function.Injective
      (fun y : Fin r → Bool => (⟨f y, hflen y⟩ : {l : List Bool // l.length = d})) := by
    intro y y' hyy
    have hff : f y = f y' := congrArg Subtype.val hyy
    by_contra hne
    have hex : ∃ k : ℕ, ∃ hk : k < r, y ⟨k, hk⟩ ≠ y' ⟨k, hk⟩ := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
      exact ⟨(i : ℕ), i.2, by simpa using hi⟩
    obtain ⟨hm, hmne⟩ := Nat.find_spec hex
    have hbefore : ∀ (j : ℕ) (hj : j < r), j < Nat.find hex → y ⟨j, hj⟩ = y' ⟨j, hj⟩ := by
      intro j hj hjm
      by_contra hjne
      have hp : ∃ hk : j < r, y ⟨j, hk⟩ ≠ y' ⟨j, hk⟩ := ⟨hj, hjne⟩
      have := Nat.find_min' hex hp
      omega
    have hquery : (fun j : Fin (Nat.find hex) => y ⟨(j : ℕ), j.2.trans hm⟩)
        = fun j : Fin (Nat.find hex) => y' ⟨(j : ℕ), j.2.trans hm⟩ := by
      funext j
      exact hbefore (j : ℕ) (j.2.trans hm) j.2
    have h1 := hfspec y ⟨Nat.find hex, hm⟩
    have h2 := hfspec y' ⟨Nat.find hex, hm⟩
    rw [hquery, hff] at h1
    have hiff : y ⟨Nat.find hex, hm⟩ = true ↔ y' ⟨Nat.find hex, hm⟩ = true := h1.symm.trans h2
    refine hmne ?_
    cases hy : y ⟨Nat.find hex, hm⟩ <;> cases hy' : y' ⟨Nat.find hex, hm⟩ <;>
      simp only [hy, hy'] at hiff ⊢ <;> simp at hiff
  have hcard := Fintype.card_le_of_injective _ hinj
  have hleft : Fintype.card (Fin r → Bool) = 2 ^ r := by simp
  have hright : Fintype.card {l : List Bool // l.length = d} = 2 ^ d := by
    have hv : Fintype.card (List.Vector Bool d) = 2 ^ d := by
      rw [card_vector]
      simp
    exact hv
  rw [hleft, hright] at hcard
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hcard

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
