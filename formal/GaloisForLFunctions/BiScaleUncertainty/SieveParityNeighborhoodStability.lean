import GaloisForLFunctions.BiScaleUncertainty.SieveParityCutoffRecovery
import GaloisForLFunctions.BiScaleUncertainty.SieveParitySharpWitnesses

/-! Pairwise local stability in actual neighborhoods of the parity source. -/

open scoped BigOperators
open Finset
open GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.ParityNeighborhood
set_option autoImplicit false
local instance (N : ℕ) : NeZero N.factorial := ⟨Nat.factorial_ne_zero N⟩

/-- Actual inverse weights of the parity source with coefficient two. -/
def parityWeights (N : ℕ) : ℕ → ℝ :=
  _root_.RHTower.pmRamanujanResidueCoeff (fun q => if q = 2 then 2 else 0) N

theorem coordinate_parityWeights (N : ℕ) (hN : 2 ≤ N) (q : ℕ) :
    selbergMultiplesCoord N (parityWeights N) q = if q = 2 then 2 else 0 := by
  rw [parityWeights, selbergMultiplesCoord_ramanujan_inverse]
  by_cases hq : q ∈ Icc 1 N
  · simp [hq]
  · have hq2 : q ≠ 2 := by
      intro hh
      subst q
      exact hq (by simp; omega)
    simp [hq, hq2]

theorem coordinate_sup_error (N : ℕ) (c e : ℕ → ℝ) (D : ℝ)
    (herr : ∀ n, |sieveSeq N e n-sieveSeq N c n| ≤ D) (q : ℕ) (hq : q ∈ Icc 1 N) :
    |selbergMultiplesCoord N e q-selbergMultiplesCoord N c q| ≤ D := by
  have hh := translated_coordinate_error N c e 0 D (by simpa using herr)
    ((N.factorial/q : ℕ) : ZMod N.factorial)
  rw [frequency_order hq] at hh
  simpa only [Nat.cast_zero, zero_mul, AddChar.map_zero_eq_one, one_mul,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hh

/-- The unit physical ball around twice parity supplies the coefficient box used in recovery. -/
theorem parity_ball_coordinates (N : ℕ) (hN : 2 ≤ N) (c : ℕ → ℝ)
    (hball : ∀ n, |sieveSeq N c n-sieveSeq N (parityWeights N) n| ≤ 1) :
    1 ≤ selbergMultiplesCoord N c 2 ∧ ∀ q ∈ Icc 1 N, |selbergMultiplesCoord N c q| ≤ 3 := by
  have h2 : 2 ∈ Icc 1 N := by simp; omega
  have hh2 := coordinate_sup_error N (parityWeights N) c 1 hball 2 h2
  rw [coordinate_parityWeights N hN, if_pos rfl] at hh2
  have hb2 := abs_le.mp hh2
  have hc2 : 1 ≤ selbergMultiplesCoord N c 2 := by linarith
  refine ⟨hc2, ?_⟩
  intro q hq
  by_cases he : q = 2
  · subst q
    rw [abs_of_nonneg (by linarith : 0 ≤ selbergMultiplesCoord N c 2)]
    linarith
  · have hh := coordinate_sup_error N (parityWeights N) c 1 hball q hq
    rw [coordinate_parityWeights N hN, if_neg he, sub_zero] at hh
    linarith

/-- Both signs of each explicit witness approach the actual parity source uniformly. -/
theorem sharp_near_parity (N A B : ℕ) (hN : 2 ≤ N)
    (hA : A ∈ Icc 1 N) (hB : B ∈ Icc 1 N) (hB2 : B ≠ 2)
    (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    |sieveSeq N (sharpWeights N A B t) n-sieveSeq N (parityWeights N) n| ≤
        (∑ q ∈ Icc 1 N, (q.totient : ℝ))*t ∧
    |sieveSeq N (sharpFlippedWeights N A B t) n-sieveSeq N (parityWeights N) n| ≤
        (∑ q ∈ Icc 1 N, (q.totient : ℝ))*t := by
  have h2 : 2 ∈ Icc 1 N := by simp; omega
  have hp (q : ℕ) : |sharpProfile A B t q-(if q = 2 then 2 else 0)| ≤ t := by
    by_cases hq2 : q = 2
    · simp [sharpProfile, hq2, ht]
    · by_cases hqab : q = A ∨ q = B <;> simp [sharpProfile, hq2, hqab, abs_of_nonneg ht, ht]
  have hf (q : ℕ) : |flipProfile B (sharpProfile A B t) q-(if q = 2 then 2 else 0)| ≤ t := by
    by_cases hq2 : q = 2
    · subst q
      simp [flipProfile, sharpProfile, Ne.symm hB2, ht]
    · have hh := hp q
      simp only [if_neg hq2, sub_zero] at hh ⊢
      by_cases hqB : q = B <;> simpa [flipProfile, hqB] using hh
  constructor
  · apply sieveSeq_error_le_totient_sum N (sharpWeights N A B t) (parityWeights N) t _ n
    intro q _
    rw [coordinate_sharpWeights N A B t h2 hA hB, coordinate_parityWeights N hN]
    exact hp q
  · apply sieveSeq_error_le_totient_sum N (sharpFlippedWeights N A B t) (parityWeights N) t _ n
    intro q _
    rw [coordinate_sharpFlippedWeights N A B t h2 hA hB, coordinate_parityWeights N hN]
    exact hf q

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments.ParityNeighborhood

open scoped BigOperators
open Finset
open GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.ParityNeighborhood
set_option autoImplicit false

/-- Pairwise recovery on an actual signal neighborhood, using complete fifth/sixth arrays. -/
def LocalPairwiseHolder (N : ℕ) (b : ℕ → ℝ) (α : ℝ) : Prop :=
  ∃ R : ℝ, 0 < R ∧ ∃ C : ℝ, 0 ≤ C ∧
    ∀ (c e : ℕ → ℝ) (ε : ℝ), 0 ≤ ε →
      (∀ n, |sieveSeq N c n-sieveSeq N b n| ≤ R) →
      (∀ n, |sieveSeq N e n-sieveSeq N b n| ≤ R) →
      (∀ v : Fin 5 → ℕ, |translatedMoment N c v-translatedMoment N e v| ≤ ε) →
      (∀ v : Fin 6 → ℕ, |translatedMoment N c v-translatedMoment N e v| ≤ ε) →
      ∃ h : ℕ, ∀ n, |sieveSeq N e n-sieveSeq N c (n+h)| ≤ C*ε^α

private theorem holder_of_small_error (N d : ℕ) (hd : d ≠ 0)
    (hsmall : ∀ (c e : ℕ → ℝ) (δ : ℝ), 0 ≤ δ → 4*δ < 1 →
      (∀ n, |sieveSeq N c n-sieveSeq N (parityWeights N) n| ≤ 1) →
      (∀ n, |sieveSeq N e n-sieveSeq N (parityWeights N) n| ≤ 1) →
      (∀ v : Fin 5 → ℕ, |translatedMoment N c v-translatedMoment N e v| ≤ δ^d) →
      (∀ v : Fin 6 → ℕ, |translatedMoment N c v-translatedMoment N e v| ≤ δ^d) →
      ∃ h : ℕ, ∀ n, |sieveSeq N e n-sieveSeq N c (n+h)| ≤
        12*(∑ q ∈ Icc 1 N, (q.totient : ℝ))*δ) :
    LocalPairwiseHolder N (parityWeights N) (1/(d : ℝ)) := by
  have hW : 0 ≤ ∑ q ∈ Icc 1 N, (q.totient : ℝ) := by positivity
  refine ⟨1, by norm_num, 12*(∑ q ∈ Icc 1 N, (q.totient : ℝ))+8,
    by positivity, ?_⟩
  intro c e ε hε hc he h5 h6
  let δ : ℝ := ε^(1/(d : ℝ))
  have hδ : 0 ≤ δ := Real.rpow_nonneg hε _
  have hp : δ^d = ε := by
    simpa only [δ, one_div] using Real.rpow_inv_natCast_pow hε hd
  by_cases hs : 4*δ < 1
  · obtain ⟨h, hh⟩ := hsmall c e δ hδ hs hc he
      (by simpa only [hp] using h5) (by simpa only [hp] using h6)
    refine ⟨h, fun n => (hh n).trans ?_⟩
    change 12*(∑ q ∈ Icc 1 N, (q.totient : ℝ))*δ ≤
      (12*(∑ q ∈ Icc 1 N, (q.totient : ℝ))+8)*δ
    nlinarith only [hδ]
  · refine ⟨0, fun n => ?_⟩
    have hb : |sieveSeq N e n-sieveSeq N c n| ≤ 2 := by
      have hh := abs_sub_le (sieveSeq N e n) (sieveSeq N (parityWeights N) n)
        (sieveSeq N c n)
      rw [abs_sub_comm (sieveSeq N (parityWeights N) n)] at hh
      linarith [hc n, he n]
    have hmul : 0 ≤ (12*(∑ q ∈ Icc 1 N, (q.totient : ℝ)))*δ := by positivity
    change |sieveSeq N e n-sieveSeq N c (n+0)| ≤
      (12*(∑ q ∈ Icc 1 N, (q.totient : ℝ))+8)*δ
    simp only [Nat.add_zero]
    push Not at hs
    nlinarith only [hb, hs, hmul]

theorem local_holder_three (N : ℕ) (hN : 2 ≤ N) (hN12 : N < 12) :
    LocalPairwiseHolder N (parityWeights N) (1/3) := by
  apply holder_of_small_error N 3 (by decide)
  intro c e δ hδ hs hc he h5 h6
  have hc' := parity_ball_coordinates N hN c hc
  have he' := parity_ball_coordinates N hN e he
  exact exists_translate_error_small_three N hN hN12 c e δ hδ hs
    hc'.1 he'.1 he'.2 h5 h6

theorem local_holder_five (N : ℕ) (hN : 2 ≤ N) (hN20 : N < 20) :
    LocalPairwiseHolder N (parityWeights N) (1/5) := by
  apply holder_of_small_error N 5 (by decide)
  intro c e δ hδ hs hc he h5 h6
  have hc' := parity_ball_coordinates N hN c hc
  have he' := parity_ball_coordinates N hN e he
  exact exists_translate_error_small_five N hN hN20 c e δ hδ hs
    hc'.1 he'.1 he'.2 h5 h6

theorem local_holder_six (N : ℕ) :
    LocalPairwiseHolder N (parityWeights N) (1/6) := by
  apply holder_of_small_error N 6 (by decide)
  intro c e δ hδ hs _hc _he h5 h6
  obtain ⟨h, hh⟩ := exists_physical_translate_error N c e δ hδ (by linarith) h5 h6
  refine ⟨h, fun n => (hh n).trans ?_⟩
  have hW : 0 ≤ (∑ q ∈ Icc 1 N, (q.totient : ℝ))*δ := by positivity
  nlinarith only [hW]

/-- With only the constant and parity modes admitted, the inverse is locally Lipschitz. -/
theorem local_holder_two : LocalPairwiseHolder 2 (parityWeights 2) 1 := by
  refine ⟨1, by norm_num, 5, by norm_num, ?_⟩
  intro c e ε hε hc he h5 h6
  have hc' := parity_ball_coordinates 2 (by decide) c hc
  have he' := parity_ball_coordinates 2 (by decide) e he
  have h2 : 2 ∈ Icc 1 2 := by decide
  have hanchor : |selbergMultiplesCoord 2 c 2^6-selbergMultiplesCoord 2 e 2^6| ≤ ε := by
    have hh := anchored_square_error 2 c e ε h6 h2 h2
    simpa only [← pow_add] using hh
  have hc2 := (anchor_gaps _ _ ε hc'.1 he'.1 hanchor).1
  have hc1 := anchored_linear _ _ _ _ ε hc'.1 he'.1
    (he'.2 1 (by decide)) hanchor (anchored_constant_error 2 c e ε h5 h2)
  refine ⟨0, fun n => ?_⟩
  have hh := sieveSeq_error_le_coordinate_sum 2 e c n
  have hset : Icc 1 2 = {1, 2} := by decide
  simp only [hset, sum_insert (by decide : 1 ∉ ({2} : Finset ℕ)), sum_singleton] at hh
  norm_num only [Nat.totient_one, Nat.totient_two, Nat.cast_one, one_mul] at hh
  rw [abs_sub_comm (selbergMultiplesCoord 2 e 1),
    abs_sub_comm (selbergMultiplesCoord 2 e 2)] at hh
  simpa only [Nat.add_zero, Real.rpow_one] using (hh.trans (by linarith : _ ≤ 5*ε))

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments.ParityNeighborhood
