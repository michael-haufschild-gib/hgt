import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.LocalRootCollisionEvents
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.SquarefreeDivisorWeights

/-! Bounds for the weight of collisions with prescribed factor
degrees and prime. For a pair of factors, the smaller degree
cancels against its irreducible count. -/

noncomputable section

open Polynomial Finset WindowedLandauTheory.CyclotomicNorms

namespace WindowedLandauTheory.ConcN

open FiniteWeight

variable (g N : ℕ) [Fact g.Prime]

def polynomialWeight (c : Fin N → ZMod g) : ℝ := squarefreeWeight g (monicOf c)

theorem polynomialWeight_nonneg (c : Fin N → ZMod g) : 0 ≤ polynomialWeight g N c :=
  squarefreeWeight_nonneg g _

private theorem weight_divisorEvent_le (P : (ZMod g)[X]) (hP : P.Monic) :
    weight (polynomialWeight g N) (divisorEvent g N P) ≤ squarefreeWeight g P := by
  classical
  rw [divisorEvent, weight_eq_filter']
  exact squarefree_divisor_weight_le g N P hP _ (fun _ h => Finset.mem_filter.mp h)

theorem residue_denom_pos {δ : ℕ} (hδ : 1 ≤ δ) : (0 : ℝ) < (g : ℝ) ^ δ - 1 := by
  have hg : (1 : ℝ) < g := by exact_mod_cast (Fact.out : g.Prime).one_lt
  exact sub_pos.mpr (one_lt_pow₀ hg (by omega))

theorem weight_same_factor_le (δ l : ℕ) (hl : l.Prime) (hδ : 2 ≤ δ)
    (hsmall : l ^ (4 * padicValNat l (g ^ δ - 1)) ≤ g ^ δ) :
    weight (polynomialWeight g N) (⋃ a ∈ sameFactorCandidates g δ l, divisorEvent g N (monicOf a)) ≤
      (g : ℝ) ^ (3 * (δ : ℝ) / 4) * ((g : ℝ) ^ δ - 1)⁻¹ := by
  refine (weight_biUnion_le _ (polynomialWeight_nonneg g N) _ _).trans ?_
  have hpos := residue_denom_pos g (show 1 ≤ δ by omega)
  calc
    ∑ a ∈ sameFactorCandidates g δ l, weight (polynomialWeight g N) (divisorEvent g N (monicOf a)) ≤
        ∑ _a ∈ sameFactorCandidates g δ l, ((g : ℝ) ^ δ - 1)⁻¹ := by
      refine Finset.sum_le_sum fun a ha => (weight_divisorEvent_le g N _ (monic_monicOf a)).trans_eq ?_
      have hi := (mem_nonzeroIrreducibleCoefficients.mp ((mem_sameFactorCandidates g).mp ha).1).1
      rw [squarefreeWeight_of_irreducible g _ hi (monic_monicOf a), natDegree_monicOf]
    _ = ((sameFactorCandidates g δ l).card : ℝ) * ((g : ℝ) ^ δ - 1)⁻¹ := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (same_factor_count g δ l hl hδ hsmall) (inv_nonneg.mpr hpos.le)

theorem weight_cross_factor_le (δ δ' l : ℕ) (hl : l.Prime) (hδ : 1 ≤ δ) (hδ' : 1 ≤ δ')
    (hsmall : l ^ (4 * padicValNat l (g ^ δ - 1)) ≤ g ^ δ) :
    weight (polynomialWeight g N) (⋃ b ∈ nonzeroIrreducibleCoefficients (ZMod g) δ',
      ⋃ a ∈ crossFactorCandidates g δ l (monicOf b), divisorEvent g N (monicOf a * monicOf b)) ≤
      (g : ℝ) ^ ((δ : ℝ) / 4) * ((g : ℝ) ^ δ - 1)⁻¹ := by
  let U := nonzeroIrreducibleCoefficients (ZMod g) δ'
  let W := (g : ℝ) ^ ((δ : ℝ) / 4)
  let A := ((g : ℝ) ^ δ - 1)⁻¹
  let B := ((g : ℝ) ^ δ' - 1)⁻¹
  have hA : 0 ≤ A := inv_nonneg.mpr (residue_denom_pos g hδ).le
  have hB : 0 ≤ B := inv_nonneg.mpr (residue_denom_pos g hδ').le
  have hW : 0 ≤ W := by positivity
  have hinner (b : Fin δ' → ZMod g) (hb : b ∈ U) :
      weight (polynomialWeight g N) (⋃ a ∈ crossFactorCandidates g δ l (monicOf b),
        divisorEvent g N (monicOf a * monicOf b)) ≤ (δ' : ℝ) * W * (A * B) := by
    refine (weight_biUnion_le _ (polynomialWeight_nonneg g N) _ _).trans ?_
    have hcount := cross_factor_count g δ l hl hδ (monicOf b)
    rw [natDegree_monicOf] at hcount
    have hcountR : ((crossFactorCandidates g δ l (monicOf b)).card : ℝ) ≤
        (δ' : ℝ) * ((l ^ padicValNat l (g ^ δ - 1) : ℕ) : ℝ) := by exact_mod_cast hcount
    calc
      ∑ a ∈ crossFactorCandidates g δ l (monicOf b),
          weight (polynomialWeight g N) (divisorEvent g N (monicOf a * monicOf b)) ≤
          ∑ _a ∈ crossFactorCandidates g δ l (monicOf b), A * B := by
        refine Finset.sum_le_sum fun a ha => (weight_divisorEvent_le g N _ ((monic_monicOf a).mul (monic_monicOf b))).trans_eq ?_
        have hai := (mem_nonzeroIrreducibleCoefficients.mp ((mem_crossFactorCandidates g).mp ha).1).1
        have hbi := (mem_nonzeroIrreducibleCoefficients.mp hb).1
        rw [squarefreeWeight_mul g _ _ (monic_monicOf a).ne_zero (monic_monicOf b).ne_zero,
          squarefreeWeight_of_irreducible g _ hai (monic_monicOf a),
          squarefreeWeight_of_irreducible g _ hbi (monic_monicOf b), natDegree_monicOf, natDegree_monicOf]
      _ = ((crossFactorCandidates g δ l (monicOf b)).card : ℝ) * (A * B) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (hcountR.trans (mul_le_mul_of_nonneg_left (primary_le_rpow_quarter hsmall) (Nat.cast_nonneg _))) (mul_nonneg hA hB)
  refine (weight_biUnion_le _ (polynomialWeight_nonneg g N) _ _).trans ?_
  have hU := irreducible_count_upper_nonzero (ZMod g) δ' hδ'
  rw [ZMod.card] at hU
  have hUR : (U.card : ℝ) * (δ' : ℝ) ≤ (g : ℝ) ^ δ' - 1 := by
    have h : (δ' : ℝ) * (U.card : ℝ) ≤ ((g ^ δ' - 1 : ℕ) : ℝ) := by exact_mod_cast hU
    rwa [Nat.cast_sub (Nat.one_le_pow _ _ (Fact.out : g.Prime).pos), Nat.cast_pow, Nat.cast_one, mul_comm] at h
  calc
    ∑ b ∈ U, weight (polynomialWeight g N) (⋃ a ∈ crossFactorCandidates g δ l (monicOf b),
        divisorEvent g N (monicOf a * monicOf b)) ≤ ∑ _b ∈ U, (δ' : ℝ) * W * (A * B) :=
      Finset.sum_le_sum hinner
    _ = ((U.card : ℝ) * δ') * (W * A * B) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ ((g : ℝ) ^ δ' - 1) * (W * A * B) :=
      mul_le_mul_of_nonneg_right hUR (mul_nonneg (mul_nonneg hW hA) hB)
    _ = W * A := by
      change _ * (W * A * ((g : ℝ) ^ δ' - 1)⁻¹) = W * A
      field_simp [(residue_denom_pos g hδ').ne']

end WindowedLandauTheory.ConcN

#print axioms WindowedLandauTheory.ConcN.weight_cross_factor_le
