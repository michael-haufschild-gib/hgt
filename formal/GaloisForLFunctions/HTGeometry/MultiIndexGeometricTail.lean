import GaloisForLFunctions.HTGeometry.FinitePiProductSummability

/-!
# The multi-index geometric tail is linear in the nome

For a finite family of nonnegative numbers all bounded by `t ≤ 1/2`, the sum of the multi-index
monomials `∏ a_i^{n_i}` over all nonzero multi-indices is at most a constant times `t`: every such
monomial has total degree at least one, so one factor of `t` splits off and the rest is dominated by
the corresponding monomial at `1/2`.

The constant depends only on the number of parameters, and no closed form for the geometric product
is needed.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {ι : Type} [Fintype ι]

/-- The total multi-index geometric mass at the half nome. -/
def multiIndexHalfSum (ι : Type) [Fintype ι] : ℝ :=
  ∑' n : ι → ℕ, ∏ i : ι, (1 / 2 : ℝ) ^ n i

theorem summable_multiIndexMonomial {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i < 1) :
    Summable (fun n : ι → ℕ => ∏ i : ι, a i ^ n i) :=
  summable_fintype_pi_product_of_nonneg ι (fun i n => a i ^ n)
    (fun i => summable_geometric_of_lt_one (ha i) (ha1 i))
    (fun i n => pow_nonneg (ha i) n)

theorem multiIndexHalfSum_nonneg : 0 ≤ multiIndexHalfSum ι := by
  rw [multiIndexHalfSum]
  refine tsum_nonneg fun n => ?_
  positivity

/-- The full multi-index mass is monotone in the base. -/
theorem tsum_multiIndexMonomial_le_half {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i)
    (hah : ∀ i, a i ≤ 1 / 2) :
    ∑' n : ι → ℕ, ∏ i : ι, a i ^ n i ≤ multiIndexHalfSum ι := by
  have ha1 : ∀ i, a i < 1 := fun i => lt_of_le_of_lt (hah i) (by norm_num)
  have hsumA : Summable (fun n : ι → ℕ => ∏ i : ι, a i ^ n i) :=
    summable_multiIndexMonomial ha ha1
  have hsumH : Summable (fun n : ι → ℕ => ∏ i : ι, (1 / 2 : ℝ) ^ n i) :=
    summable_multiIndexMonomial (fun _ => by norm_num) (fun _ => by norm_num)
  refine hsumA.tsum_le_tsum (fun n => ?_) hsumH
  exact Finset.prod_le_prod (fun i _ => pow_nonneg (ha i) _)
    (fun i _ => pow_le_pow_left₀ (ha i) (hah i) _)

/-- A nonzero multi-index has total degree at least one. -/
theorem one_le_sum_of_ne_zero {n : ι → ℕ} (hn : n ≠ 0) : 1 ≤ ∑ i : ι, n i := by
  by_contra hcon
  refine hn ?_
  have hzero : ∑ i : ι, n i = 0 := by omega
  funext i
  have := (Finset.sum_eq_zero_iff.mp hzero) i (Finset.mem_univ i)
  simpa using this

/-- **The multi-index tail is linear in the nome.**  Every nonzero multi-index monomial in numbers
bounded by `t ≤ 1/2` is at most `2t` times the corresponding monomial at `1/2`. -/
theorem tsum_multiIndex_tail_le {a : ι → ℝ} {t : ℝ} (ha : ∀ i, 0 ≤ a i) (hat : ∀ i, a i ≤ t)
    (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) :
    ∑' n : ι → ℕ, (if n = 0 then 0 else ∏ i : ι, a i ^ n i)
      ≤ (2 * multiIndexHalfSum ι) * t := by
  classical
  have ha1 : ∀ i, a i < 1 := fun i => lt_of_le_of_lt (le_trans (hat i) ht) (by norm_num)
  have hhalf0 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hhalf1 : (1 / 2 : ℝ) < 1 := by norm_num
  have hsumA : Summable (fun n : ι → ℕ => ∏ i : ι, a i ^ n i) :=
    summable_multiIndexMonomial ha ha1
  have hsumH : Summable (fun n : ι → ℕ => ∏ i : ι, (1 / 2 : ℝ) ^ n i) :=
    summable_multiIndexMonomial (fun _ => hhalf0) (fun _ => hhalf1)
  have hsumIte : Summable (fun n : ι → ℕ => if n = 0 then 0 else ∏ i : ι, a i ^ n i) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hsumA
    · by_cases h : n = 0
      · rw [if_pos h]
      · rw [if_neg h]
        exact Finset.prod_nonneg fun i _ => pow_nonneg (ha i) _
    · by_cases h : n = 0
      · rw [if_pos h]
        exact Finset.prod_nonneg fun i _ => pow_nonneg (ha i) _
      · rw [if_neg h]
  have hterm : ∀ n : ι → ℕ, (if n = 0 then 0 else ∏ i : ι, a i ^ n i)
      ≤ (2 * t) * ∏ i : ι, (1 / 2 : ℝ) ^ n i := by
    intro n
    by_cases hn : n = 0
    · rw [if_pos hn]
      have : (0 : ℝ) ≤ ∏ i : ι, (1 / 2 : ℝ) ^ n i := Finset.prod_nonneg fun i _ => by positivity
      nlinarith
    · rw [if_neg hn]
      have hd : 1 ≤ ∑ i : ι, n i := one_le_sum_of_ne_zero hn
      have hA : ∏ i : ι, a i ^ n i ≤ t ^ (∑ i : ι, n i) := by
        rw [← Finset.prod_pow_eq_pow_sum]
        exact Finset.prod_le_prod (fun i _ => pow_nonneg (ha i) _)
          (fun i _ => pow_le_pow_left₀ (ha i) (hat i) _)
      have hH : ∏ i : ι, (1 / 2 : ℝ) ^ n i = (1 / 2 : ℝ) ^ (∑ i : ι, n i) :=
        Finset.prod_pow_eq_pow_sum _ _ _
      obtain ⟨d, hd'⟩ : ∃ d : ℕ, ∑ i : ι, n i = d + 1 := ⟨∑ i : ι, n i - 1, by omega⟩
      rw [hH, hd']
      calc ∏ i : ι, a i ^ n i ≤ t ^ (d + 1) := by rw [hd'] at hA; exact hA
        _ = t * t ^ d := by ring
        _ ≤ t * (1 / 2 : ℝ) ^ d := by
            have : t ^ d ≤ (1 / 2 : ℝ) ^ d := pow_le_pow_left₀ ht0 ht d
            nlinarith
        _ = (2 * t) * (1 / 2 : ℝ) ^ (d + 1) := by
            rw [pow_succ]
            ring
  calc ∑' n : ι → ℕ, (if n = 0 then 0 else ∏ i : ι, a i ^ n i)
      ≤ ∑' n : ι → ℕ, (2 * t) * ∏ i : ι, (1 / 2 : ℝ) ^ n i :=
        hsumIte.tsum_le_tsum hterm (hsumH.mul_left (2 * t))
    _ = (2 * t) * multiIndexHalfSum ι := by
        rw [multiIndexHalfSum, tsum_mul_left]
    _ = (2 * multiIndexHalfSum ι) * t := by ring

end

end GaloisForLFunctions.HTGeometry
