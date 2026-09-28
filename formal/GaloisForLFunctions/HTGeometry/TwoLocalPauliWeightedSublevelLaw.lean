import GaloisForLFunctions.HTGeometry.TwoLocalPauliSpectralSublevelLaw

/-!
# Weighted quenched sublevel bounds on the full Pauli source chart

For each system size there is one source ball and one constant such that the
weighted mass of nonzero near-resonant spectral characters has a power-law
tail. The character dictionary may be countably infinite. Its cardinality
does not enter: a probability weighting has total mass one, and repeated
characters retain the sum of their weights. Replica orders are unrestricted.

For source-dependent weights, the bound instead charges the total mass of a
fixed pointwise envelope. No measurability assumption on those weights or
on the spectral labels is needed: measurable outer covers supply the upper
bound. This is not free adaptation of the probability weighting.

The source ball and constants are local and existential, and may depend on
system size. Removing the zero character removes the permanent collision
sector, not the initial easy time interval. No observer-Jacobian, source
fibre-sheet, complete-circuit incidence, or first-return bound is asserted.
-/

open MeasureTheory Set Metric
open scoped BigOperators ENNReal

namespace GaloisForLFunctions.HTGeometry
noncomputable section

noncomputable local instance weightedBoolCubeFintype
    {I : Type*} [Fintype I] : Fintype (I → Bool) := Fintype.ofFinite _

private theorem weighted_indicator_outer_tail
    {X J : Type*} [MeasurableSpace X] [Countable J]
    (μ : Measure X) (s : J → Set X) (w : J → ℝ≥0∞) (τ : ℝ≥0∞) :
    τ * μ {x | τ ≤ ∑' j, (s j).indicator (fun _ => w j) x} ≤
      ∑' j, w j * μ (s j) := by
  classical
  let f : X → ℝ≥0∞ :=
    fun x => ∑' j, (toMeasurable μ (s j)).indicator (fun _ => w j) x
  have hm (j : J) :
      Measurable ((toMeasurable μ (s j)).indicator (fun _ : X => w j)) :=
    measurable_const.indicator (measurableSet_toMeasurable μ (s j))
  have hfm : Measurable f := Measurable.tsum hm
  have hle (x : X) : (∑' j, (s j).indicator (fun _ => w j) x) ≤ f x := by
    apply ENNReal.tsum_le_tsum
    intro j
    by_cases hx : x ∈ s j
    · simp only [indicator_of_mem hx,
        indicator_of_mem (subset_toMeasurable μ (s j) hx)]
      exact le_rfl
    · simp only [indicator_of_notMem hx]
      exact bot_le
  calc
    _ ≤ τ * μ {x | τ ≤ f x} :=
      mul_le_mul_right (measure_mono (fun x hx => hx.trans (hle x))) τ
    _ ≤ ∫⁻ x, f x ∂μ := mul_meas_ge_le_lintegral hfm τ
    _ = ∑' j, w j * μ (s j) := by
      rw [show (∫⁻ x, f x ∂μ) =
          ∑' j, ∫⁻ x, (toMeasurable μ (s j)).indicator (fun _ => w j) x ∂μ from
        lintegral_tsum (fun j => (hm j).aemeasurable)]
      simp only [lintegral_indicator_const (measurableSet_toMeasurable μ _),
        measure_toMeasurable]

/-- All projective integer spectral characters, including the zero character. -/
abbrev PauliBalancedIntegerCharacter (n : ℕ) :=
  {k : (Fin n → Bool) → ℤ // SpectralCharacterBalanced k}

/-- A translated spectral sublevel event, with the zero character excluded. -/
def pauliCharacterNearSet (n : ℕ) (k : PauliBalancedIntegerCharacter n)
    (c ε : ℝ) : Set (Fin (pauliSourceDimension n) → ℝ) :=
  {p | k.val ≠ 0 ∧
    |c + commonReferencePauliAction (fun x => (k.val x : ℝ)) (pauliSourceEquiv n p)| < ε}

/-- Weighted near-resonance mass; weights may depend on the drawn source point. -/
def pauliWeightedNearMass (n : ℕ) {J : Type*} [Countable J]
    (k : J → PauliBalancedIntegerCharacter n) (c : J → ℝ)
    (a : (Fin (pauliSourceDimension n) → ℝ) → J → ℝ≥0∞)
    (ε : ℝ) (p : Fin (pauliSourceDimension n) → ℝ) : ℝ≥0∞ :=
  ∑' j, (pauliCharacterNearSet n (k j) (c j) ε).indicator (fun _ => a p j) p

private theorem pauli_character_near_measure_le
    (n : ℕ) {ρ K : ℝ} (hK : 0 < K)
    (hsmall : ∀ (c : ℝ) (k : (Fin n → Bool) → ℤ),
      SpectralCharacterBalanced k → k ≠ 0 → ∀ ε : ℝ, 0 < ε →
        volume.real {p ∈ ball (0 : Fin (pauliSourceDimension n) → ℝ) ρ |
          |c + commonReferencePauliAction (fun x => (k x : ℝ)) (pauliSourceEquiv n p)| < ε} ≤
          K * ε ^ (((pauliSourceDimension n : ℝ) * (n + 1 : ℕ))⁻¹) *
            volume.real (ball (0 : Fin (pauliSourceDimension n) → ℝ) ρ))
    (k : PauliBalancedIntegerCharacter n) (c : ℝ) {ε : ℝ} (hε : 0 < ε) :
    volume (ball (0 : Fin (pauliSourceDimension n) → ℝ) ρ ∩
        pauliCharacterNearSet n k c ε) ≤
      ENNReal.ofReal (K * ε ^ (((pauliSourceDimension n : ℝ) * (n + 1 : ℕ))⁻¹)) *
        volume (ball (0 : Fin (pauliSourceDimension n) → ℝ) ρ) := by
  classical
  by_cases hk : k.val = 0
  · simp only [pauliCharacterNearSet, hk, ne_eq, not_true_eq_false, false_and,
      setOf_false, inter_empty, measure_empty, zero_le]
  · have hfin : volume (ball (0 : Fin (pauliSourceDimension n) → ℝ) ρ ∩
        pauliCharacterNearSet n k c ε) ≠ ∞ :=
      ne_top_of_le_ne_top measure_ball_ne_top (measure_mono inter_subset_left)
    have hbfin : volume (ball (0 : Fin (pauliSourceDimension n) → ℝ) ρ) ≠ ∞ :=
      measure_ball_ne_top
    have hnonneg : 0 ≤ K * ε ^ (((pauliSourceDimension n : ℝ) * (n + 1 : ℕ))⁻¹) :=
      mul_nonneg hK.le (Real.rpow_nonneg hε.le _)
    have h := ENNReal.ofReal_le_ofReal (hsmall c k.val k.property hk ε hε)
    have hset : {p ∈ ball (0 : Fin (pauliSourceDimension n) → ℝ) ρ |
        |c + commonReferencePauliAction (fun x => (k.val x : ℝ)) (pauliSourceEquiv n p)| < ε} =
        ball (0 : Fin (pauliSourceDimension n) → ℝ) ρ ∩ pauliCharacterNearSet n k c ε := by
      ext p
      simp only [mem_setOf_eq, mem_inter_iff, pauliCharacterNearSet, hk,
        ne_eq, not_false_eq_true, true_and]
    rw [hset] at h
    simpa only [measureReal_def, ENNReal.ofReal_mul hnonneg,
      ENNReal.ofReal_toReal hbfin, ENNReal.ofReal_toReal hfin] using h

/-- A fixed probability weighting has a quenched tail bound with no dictionary-size factor.
The same local constants work for all countable dictionaries and all translations. -/
theorem pauliWeightedNearMass_quenched (n : ℕ) :
    ∃ ρ K : ℝ, 0 < ρ ∧ 0 < K ∧
      ∀ (J : Type) [Countable J] (w : PMF J)
        (k : J → PauliBalancedIntegerCharacter n) (c : J → ℝ)
        (ε : ℝ), 0 < ε → ∀ τ : ℝ≥0∞,
          τ * volume {p ∈ ball (0 : Fin (pauliSourceDimension n) → ℝ) ρ |
            τ ≤ pauliWeightedNearMass n k c (fun _ j => w j) ε p} ≤
              ENNReal.ofReal (K * ε ^ (((pauliSourceDimension n : ℝ) * (n + 1 : ℕ))⁻¹)) *
                volume (ball (0 : Fin (pauliSourceDimension n) → ℝ) ρ) := by
  obtain ⟨ρ, K, hρ, hK, hsmall⟩ := pauliBalancedIntegerAction_uniform_smallBall n
  refine ⟨ρ, K, hρ, hK, ?_⟩
  intro J _ w k c ε hε τ
  let B := ball (0 : Fin (pauliSourceDimension n) → ℝ) ρ
  let s : J → Set (Fin (pauliSourceDimension n) → ℝ) :=
    fun j => B ∩ pauliCharacterNearSet n (k j) (c j) ε
  have hset : {p ∈ B | τ ≤ pauliWeightedNearMass n k c (fun _ j => w j) ε p} ⊆
      {p | τ ≤ ∑' j, (s j).indicator (fun _ => w j) p} := by
    intro p hp
    have hind (j : J) : (s j).indicator (fun _ => w j) p =
        (pauliCharacterNearSet n (k j) (c j) ε).indicator (fun _ => w j) p := by
      exact congrFun (indicator_indicator B (pauliCharacterNearSet n (k j) (c j) ε)
        (fun _ => w j)).symm p |>.trans (indicator_of_mem hp.1 _)
    simpa only [mem_setOf_eq, hind, pauliWeightedNearMass] using hp.2
  calc
    _ ≤ τ * volume {p | τ ≤ ∑' j, (s j).indicator (fun _ => w j) p} :=
      mul_le_mul_right (measure_mono hset) τ
    _ ≤ ∑' j, w j * volume (s j) := weighted_indicator_outer_tail volume s w τ
    _ ≤ ∑' j, w j *
        (ENNReal.ofReal (K * ε ^ (((pauliSourceDimension n : ℝ) * (n + 1 : ℕ))⁻¹)) *
          volume B) := ENNReal.tsum_le_tsum fun j =>
      mul_le_mul_right (pauli_character_near_measure_le n hK hsmall (k j) (c j) hε) (w j)
    _ = _ := by rw [ENNReal.tsum_mul_right, w.tsum_coe, one_mul]

/-- Source-dependent weights are permitted with their actual envelope cost retained.
The subtype records a pointwise coefficient bound, not an assumed spectral suppression estimate. -/
theorem pauliWeightedNearMass_quenched_envelope (n : ℕ) :
    ∃ ρ K : ℝ, 0 < ρ ∧ 0 < K ∧
      ∀ (J : Type) [Countable J] (w : J → ℝ≥0∞)
        (k : J → PauliBalancedIntegerCharacter n) (c : J → ℝ)
        (a : (Fin (pauliSourceDimension n) → ℝ) → (j : J) → Set.Iic (w j))
        (ε : ℝ), 0 < ε → ∀ τ : ℝ≥0∞,
          τ * volume {p ∈ ball (0 : Fin (pauliSourceDimension n) → ℝ) ρ |
            τ ≤ pauliWeightedNearMass n k c (fun p j => (a p j).val) ε p} ≤
              (∑' j, w j) *
                (ENNReal.ofReal (K * ε ^ (((pauliSourceDimension n : ℝ) * (n + 1 : ℕ))⁻¹)) *
                  volume (ball (0 : Fin (pauliSourceDimension n) → ℝ) ρ)) := by
  obtain ⟨ρ, K, hρ, hK, hsmall⟩ := pauliBalancedIntegerAction_uniform_smallBall n
  refine ⟨ρ, K, hρ, hK, ?_⟩
  intro J _ w k c a ε hε τ
  let B := ball (0 : Fin (pauliSourceDimension n) → ℝ) ρ
  let s : J → Set (Fin (pauliSourceDimension n) → ℝ) :=
    fun j => B ∩ pauliCharacterNearSet n (k j) (c j) ε
  have hpoint (p : Fin (pauliSourceDimension n) → ℝ) (hp : p ∈ B) :
      pauliWeightedNearMass n k c (fun p j => (a p j).val) ε p ≤
        ∑' j, (s j).indicator (fun _ => w j) p := by
    apply ENNReal.tsum_le_tsum
    intro j
    change _ ≤ (B ∩ pauliCharacterNearSet n (k j) (c j) ε).indicator (fun _ => w j) p
    rw [← indicator_indicator, indicator_of_mem hp]
    exact indicator_le_indicator (a p j).property
  calc
    _ ≤ τ * volume {p | τ ≤ ∑' j, (s j).indicator (fun _ => w j) p} :=
      mul_le_mul_right (measure_mono (fun p hp => hp.2.trans (hpoint p hp.1))) τ
    _ ≤ ∑' j, w j * volume (s j) := weighted_indicator_outer_tail volume s w τ
    _ ≤ ∑' j, w j *
        (ENNReal.ofReal (K * ε ^ (((pauliSourceDimension n : ℝ) * (n + 1 : ℕ))⁻¹)) *
          volume B) := ENNReal.tsum_le_tsum fun j =>
      mul_le_mul_right (pauli_character_near_measure_le n hK hsmall (k j) (c j) hε) (w j)
    _ = _ := ENNReal.tsum_mul_right

/-- The balanced character represented by equal-order forward and backward replica counts. -/
def pauliReplicaBalancedCharacter (n r : ℕ)
    (q : {k : (Fin n → Bool) → ℤ // SpectralCharacterReplicaRealizes r k}) :
    PauliBalancedIntegerCharacter n := by
  refine ⟨q.val, ?_⟩
  obtain ⟨p, m, hp, hm, hk⟩ := q.property
  unfold SpectralCharacterBalanced
  simp_rw [hk, Finset.sum_sub_distrib, ← Nat.cast_sum, hp, hm, sub_self]

/-- Uniform quenched weighted sublevel bound at every replica order.
Radius and constant are chosen before the order, dictionary, and probability weights. -/
theorem pauliReplicaWeightedNearMass_allOrders_quenched (n : ℕ) :
    ∃ ρ K : ℝ, 0 < ρ ∧ 0 < K ∧
      ∀ (r : ℕ) (J : Type) [Countable J] (w : PMF J)
        (k : J → {k : (Fin n → Bool) → ℤ // SpectralCharacterReplicaRealizes r k})
        (c : J → ℝ) (ε : ℝ), 0 < ε → ∀ τ : ℝ≥0∞,
          τ * volume {p ∈ ball (0 : Fin (pauliSourceDimension n) → ℝ) ρ |
            τ ≤ pauliWeightedNearMass n (fun j => pauliReplicaBalancedCharacter n r (k j))
              c (fun _ j => w j) ε p} ≤
              ENNReal.ofReal (K * ε ^ (((pauliSourceDimension n : ℝ) * (n + 1 : ℕ))⁻¹)) *
                volume (ball (0 : Fin (pauliSourceDimension n) → ℝ) ρ) := by
  obtain ⟨ρ, K, hρ, hK, hmass⟩ := pauliWeightedNearMass_quenched n
  exact ⟨ρ, K, hρ, hK, fun r J _ w k c ε hε τ =>
    hmass J w (fun j => pauliReplicaBalancedCharacter n r (k j)) c ε hε τ⟩

end
end GaloisForLFunctions.HTGeometry
