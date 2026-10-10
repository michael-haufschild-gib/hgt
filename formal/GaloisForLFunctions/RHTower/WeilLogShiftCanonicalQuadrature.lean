import GaloisForLFunctions.RHTower.WeilLogShiftCanonicalCluster
import GaloisForLFunctions.RHTower.WeilLogShiftMomentRatios
import GaloisForLFunctions.RHTower.WeilLogShiftMomentProbabilities
import GaloisForLFunctions.RHTower.WeilLogShiftGramExactImage

/-! Interleaved disjoint probability profiles with exponentially close actual Gram readings. -/

open scoped BigOperators
noncomputable section
namespace RHTower

theorem finiteWeilClusterLogNodes_strictMono (r k : ℕ) :
    StrictMono (finiteWeilClusterLogNodes r k) := by
  intro i j hij
  rw [finiteWeilClusterLogNodes_apply, finiteWeilClusterLogNodes_apply]
  have hlt : (((k + 2) + (i : ℕ) : ℕ) : ℝ) < (((k + 2) + (j : ℕ) : ℕ) : ℝ) := by
    exact_mod_cast (show k + 2 + (i : ℕ) < k + 2 + (j : ℕ) by omega)
  have hlog := Real.log_lt_log
    (show 0 < (((k + 2) + (i : ℕ) : ℕ) : ℝ) by positivity) hlt
  linarith only [hlog]

theorem finiteWeilCanonicalCluster_ratio (r k : ℕ) (i j : Fin (r + 2)) (hij : i ≠ j) :
    finiteWeilCanonicalCluster r k j / finiteWeilCanonicalCluster r k i =
      -∏ l ∈ (Finset.univ.erase i).erase j,
        (finiteWeilClusterLogNodes r k i - finiteWeilClusterLogNodes r k l) /
          (finiteWeilClusterLogNodes r k j - finiteWeilClusterLogNodes r k l) :=
  finiteWeilNormalizedMomentDual_ratio _ (finiteWeilClusterLogNodes_injective r k) i j hij

/-- The canonical orientation is positive at the last node and alternates at every step. -/
theorem finiteWeilCanonicalCluster_alternation (r k : ℕ) :
    0 < finiteWeilCanonicalCluster r k (Fin.last (r + 1)) ∧
    ∀ i : Fin (r + 1), finiteWeilCanonicalCluster r k i.castSucc *
      finiteWeilCanonicalCluster r k i.succ < 0 :=
  ⟨finiteWeilNormalizedMomentDual_last_pos _ (finiteWeilClusterLogNodes_strictMono r k),
    finiteWeilNormalizedMomentDual_adjacent_mul_neg _ (finiteWeilClusterLogNodes_strictMono r k)⟩

theorem finiteWeilCanonicalCluster_sum_zero (r k : ℕ) :
    ∑ i, finiteWeilCanonicalCluster r k i = 0 := by
  simpa only [pow_zero, mul_one] using
    (finiteWeilCanonicalCluster_spec r k).2.2.1 0 (Nat.zero_le r)

def finiteWeilCanonicalPositiveProfile (r k : ℕ) : Fin (r + 2) → ℝ :=
  finiteWeilPositiveProfile (finiteWeilCanonicalCluster r k)

def finiteWeilCanonicalNegativeProfile (r k : ℕ) : Fin (r + 2) → ℝ :=
  finiteWeilNegativeProfile (finiteWeilCanonicalCluster r k)

/-- Disjoint interleaved probabilities cover every node, have absolute difference
two, and agree on every centered logarithmic moment through order `r`. -/
theorem finiteWeilCanonicalProfiles_spec (r k : ℕ) :
    (∀ i, 0 ≤ finiteWeilCanonicalPositiveProfile r k i ∧
      0 ≤ finiteWeilCanonicalNegativeProfile r k i ∧
      finiteWeilCanonicalPositiveProfile r k i * finiteWeilCanonicalNegativeProfile r k i = 0 ∧
      0 < finiteWeilCanonicalPositiveProfile r k i + finiteWeilCanonicalNegativeProfile r k i) ∧
    (∑ i, finiteWeilCanonicalPositiveProfile r k i) = 1 ∧
    (∑ i, finiteWeilCanonicalNegativeProfile r k i) = 1 ∧
    (∑ i, |finiteWeilCanonicalPositiveProfile r k i -
      finiteWeilCanonicalNegativeProfile r k i|) = 2 ∧
    (∀ p ≤ r, (∑ i, finiteWeilCanonicalPositiveProfile r k i *
      finiteWeilClusterLogNodes r k i ^ p) =
        ∑ i, finiteWeilCanonicalNegativeProfile r k i * finiteWeilClusterLogNodes r k i ^ p) ∧
    (∀ i : Fin (r + 1),
      (finiteWeilCanonicalPositiveProfile r k i.castSucc -
        finiteWeilCanonicalNegativeProfile r k i.castSucc) *
      (finiteWeilCanonicalPositiveProfile r k i.succ -
        finiteWeilCanonicalNegativeProfile r k i.succ) < 0) := by
  have hs := finiteWeilCanonicalCluster_spec r k
  have hz := finiteWeilCanonicalCluster_sum_zero r k
  obtain ⟨hp, hpsum, hqsum, htv⟩ := finiteWeil_profiles_spec
    (finiteWeilCanonicalCluster r k) hs.1 hz hs.2.1
  refine ⟨hp, hpsum, hqsum, htv, ?_, ?_⟩
  · intro p hp
    apply sub_eq_zero.mp
    unfold finiteWeilCanonicalPositiveProfile finiteWeilCanonicalNegativeProfile
    rw [finiteWeil_profile_pairing]
    rw [hs.2.2.1 p hp, mul_zero]
  · intro i
    have ht := (finiteWeil_profile_scale_bounds (finiteWeilCanonicalCluster r k) hs.1 hz).1
    change (finiteWeilPositiveProfile _ _ - finiteWeilNegativeProfile _ _) *
      (finiteWeilPositiveProfile _ _ - finiteWeilNegativeProfile _ _) < 0
    rw [finiteWeil_profile_difference, finiteWeil_profile_difference]
    have heq : ((2 / finiteWeilAbsMass (finiteWeilCanonicalCluster r k)) *
        finiteWeilCanonicalCluster r k i.castSucc) *
        ((2 / finiteWeilAbsMass (finiteWeilCanonicalCluster r k)) *
          finiteWeilCanonicalCluster r k i.succ) =
        ((2 / finiteWeilAbsMass (finiteWeilCanonicalCluster r k)) *
          (2 / finiteWeilAbsMass (finiteWeilCanonicalCluster r k))) *
        (finiteWeilCanonicalCluster r k i.castSucc * finiteWeilCanonicalCluster r k i.succ) := by
      ring
    rw [heq]
    exact mul_neg_of_pos_of_neg (mul_pos ht ht) ((finiteWeilCanonicalCluster_alternation r k).2 i)

/-- An actual test separates the two profiles with readings exactly one and zero. -/
theorem exists_finiteWeilGram_separates_canonical_profiles (r : ℕ) (s : Finset ℕ) (k : ℕ)
    (hmem : ∀ i : Fin (r + 2), k + (i : ℕ) ∈ s) :
    ∃ w : FiniteWeilGramTest,
      (∑ i, finiteWeilCanonicalPositiveProfile r k i *
        finiteWeilGramCoefficientVector s w ⟨k + (i : ℕ), hmem i⟩) = 1 ∧
      (∑ i, finiteWeilCanonicalNegativeProfile r k i *
        finiteWeilGramCoefficientVector s w ⟨k + (i : ℕ), hmem i⟩) = 0 := by
  let e : Fin (r + 2) → s := fun i => ⟨k + (i : ℕ), hmem i⟩
  have he : Function.Injective e := by
    intro i j hij
    have hv := congrArg Subtype.val hij
    apply Fin.ext
    dsimp [e] at hv
    omega
  let y : Fin (r + 2) → ℝ := fun i => if 0 < finiteWeilCanonicalCluster r k i then 1 else 0
  obtain ⟨w, hw⟩ := surjective_finiteWeilGramCoefficientVector s (Function.extend e y (fun _ => 0))
  have hv (i : Fin (r + 2)) : finiteWeilGramCoefficientVector s w (e i) = y i := by
    rw [hw]
    exact he.extend_apply y (fun _ => 0) i
  refine ⟨w, ?_, ?_⟩
  · calc
      _ = ∑ i, finiteWeilCanonicalPositiveProfile r k i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hv]
        exact (finiteWeil_profile_positive_indicator (finiteWeilCanonicalCluster r k) i).1
      _ = 1 := (finiteWeilCanonicalProfiles_spec r k).2.1
  · apply Finset.sum_eq_zero
    intro i _
    rw [hv]
    exact (finiteWeil_profile_positive_indicator (finiteWeilCanonicalCluster r k) i).2

/-- The two explicit disjoint probabilities give exponentially close readings
to every actual finite Gram test whose native cost is controlled. -/
theorem exists_finiteWeilGram_probability_profile_sensitivity :
    ∃ B L : ℝ, 0 < B ∧ 1 ≤ L ∧ ∀ (r : ℕ) (s : Finset ℕ) (k : ℕ)
      (hmem : ∀ i : Fin (r + 2), k + (i : ℕ) ∈ s),
      4 * L * ((r + 1 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) →
      (∃ w : FiniteWeilGramTest,
        (∑ i, finiteWeilCanonicalPositiveProfile r k i *
          finiteWeilGramCoefficientVector s w ⟨k + (i : ℕ), hmem i⟩) = 1 ∧
        (∑ i, finiteWeilCanonicalNegativeProfile r k i *
          finiteWeilGramCoefficientVector s w ⟨k + (i : ℕ), hmem i⟩) = 0) ∧
      ∀ w : FiniteWeilGramTest,
        |(∑ i, finiteWeilCanonicalPositiveProfile r k i *
          finiteWeilGramCoefficientVector s w ⟨k + (i : ℕ), hmem i⟩) -
        (∑ i, finiteWeilCanonicalNegativeProfile r k i *
          finiteWeilGramCoefficientVector s w ⟨k + (i : ℕ), hmem i⟩)| *
          (((k + 2 : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ r) ≤ B * finiteWeilGramTailCost 1 w := by
  obtain ⟨B, L, hB, hL, hbound⟩ := exists_finiteWeilGram_canonical_cluster_sensitivity
  refine ⟨B, L, hB, hL, fun r s k hmem hwidth =>
    ⟨exists_finiteWeilGram_separates_canonical_profiles r s k hmem, fun w => ?_⟩⟩
  let e : Fin (r + 2) → s := fun i => ⟨k + (i : ℕ), hmem i⟩
  have he : Function.Injective e := by
    intro i j hij
    have hv := congrArg Subtype.val hij
    apply Fin.ext
    dsimp [e] at hv
    omega
  let d : s → ℝ := Function.extend e (finiteWeilCanonicalCluster r k) (fun _ => 0)
  have hform : finiteWeilGramForm s w d =
      ∑ i, finiteWeilCanonicalCluster r k i * finiteWeilGramCoefficientVector s w (e i) := by
    simpa only [finiteWeilGramCoefficientVector_pairing, mul_comm] using
      finiteWeil_extend_pairing e he (finiteWeilCanonicalCluster r k)
        (finiteWeilGramCoefficientVector s w)
  have hgap := finiteWeil_profiles_pairing_le (finiteWeilCanonicalCluster r k)
    (finiteWeilCanonicalCluster_spec r k).1 (finiteWeilCanonicalCluster_sum_zero r k)
    (fun i => finiteWeilGramCoefficientVector s w (e i))
  have hc := (hbound r s k hmem hwidth).2.2 w
  rw [hform] at hc
  exact (mul_le_mul_of_nonneg_right hgap (by positivity)).trans hc

end RHTower
