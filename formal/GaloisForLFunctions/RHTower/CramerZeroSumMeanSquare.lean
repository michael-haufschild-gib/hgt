import GaloisForLFunctions.RHTower.ZetaZeroSumMeanSquare
import GaloisForLFunctions.RHTower.VonKochChebyshevBound
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Cramér's uniform mean-square estimate for critical-line zero sums

Partition the zeros by `2^k ≤ |γ| < 2^(k+1)`. The local zero count and harmonic row
bound give shell energy `O(D² X⁻¹ (k+1)³ 2⁻ᵏ)` for coefficients bounded by `D/|γ|`.
Weighted Cauchy–Schwarz with weights `(3/4)^k` sums every finite collection of shells
with one constant independent of its largest ordinate. Dominated convergence then
extends the bound to absolutely convergent coefficient families.

The only analytic premise of the resulting estimates is RH. In particular, no bound
for an infinite zero-pair sum is assumed. Short-window smoothing can use these bounds
uniformly as its width tends to zero.
-/

open Complex Finset MeasureTheory Set Filter Topology

namespace RHTower
noncomputable section

private def cramerCountConstant : ℝ := |xiLineTwoLogDerivConstant| + 20

private theorem cramerCountConstant_pos : 0 < cramerCountConstant := by
  dsimp [cramerCountConstant]
  positivity

private theorem cramer_log_bound (k : ℕ) {s : ℝ} (hs : 0 < s)
    (hs' : s ≤ 8 * (2 : ℝ) ^ (k + 1)) :
    |xiLineTwoLogDerivConstant| + 1 + Real.log s ≤
      cramerCountConstant * ((k : ℝ) + 1) := by
  have hlog := Real.log_le_log hs hs'
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hlog
  have h2 : Real.log 2 ≤ 2 := (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
  have h8 : Real.log 8 ≤ 8 := (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hA := abs_nonneg xiLineTwoLogDerivConstant
  dsimp [cramerCountConstant]
  push_cast at hlog
  nlinarith [mul_nonneg hk hA]

private def cramerHeightIndex (q : XiZeroCopy) : ℕ :=
  Classical.choose (exists_nat_pow_near
    (show (1 : ℝ) ≤ |zeroOrdinate q| by linarith [four_lt_abs_zeroOrdinate q])
    (by norm_num : (1 : ℝ) < 2))

private theorem cramerHeightIndex_spec (q : XiZeroCopy) :
    (2 : ℝ) ^ cramerHeightIndex q ≤ |zeroOrdinate q| ∧
      |zeroOrdinate q| < (2 : ℝ) ^ (cramerHeightIndex q + 1) :=
  Classical.choose_spec (exists_nat_pow_near
    (show (1 : ℝ) ≤ |zeroOrdinate q| by linarith [four_lt_abs_zeroOrdinate q])
    (by norm_num : (1 : ℝ) < 2))

private theorem cramer_shell_card (F : Finset XiZeroCopy) (k : ℕ)
    (hF : ∀ q ∈ F, |zeroOrdinate q| < (2 : ℝ) ^ (k + 1)) :
    (F.card : ℝ) ≤ 80 * cramerCountConstant * ((k : ℝ) + 1) * (2 : ℝ) ^ k := by
  have hR : (1 : ℝ) ≤ 2 ^ (k + 1) := one_le_pow₀ (by norm_num)
  have hsub : F ⊆ xiCopiesBelow ((2 : ℝ) ^ (k + 1)) :=
    fun q hq => mem_xiCopiesBelow.mpr (hF q hq).le
  have hc : (F.card : ℝ) ≤ (xiCopiesBelow ((2 : ℝ) ^ (k + 1))).card := by
    exact_mod_cast Finset.card_le_card hsub
  have hcount := card_xiCopiesBelow_le_log (S := (2 : ℝ) ^ (k + 1)) (by positivity)
  have hlog := cramer_log_bound k (s := (2 : ℝ) ^ (k + 1) + 6)
    (by positivity) (by linarith)
  have hA := le_abs_self xiLineTwoLogDerivConstant
  have hB := cramerCountConstant_pos
  have hc0 : 0 ≤ xiLineTwoLogDerivConstant + Real.log ((2 : ℝ) ^ (k + 1) + 6) :=
    add_nonneg xiLineTwoLogDerivConstant_nonneg (Real.log_nonneg (by linarith))
  calc
    _ ≤ 20 * (2 ^ (k + 1) + 1) *
        (xiLineTwoLogDerivConstant + Real.log (2 ^ (k + 1) + 6)) := hc.trans hcount
    _ ≤ 20 * (2 * 2 ^ (k + 1)) * (cramerCountConstant * ((k : ℝ) + 1)) := by
      gcongr <;> first | positivity | linarith
    _ = _ := by rw [pow_succ]; ring

private theorem cramer_shell_row (F : Finset XiZeroCopy) (k : ℕ)
    (hF : ∀ q ∈ F, |zeroOrdinate q| < (2 : ℝ) ^ (k + 1))
    {q : XiZeroCopy} (hq : q ∈ F) :
    ∑ q' ∈ F, 1 / (1 + |(q.1 : ℂ).im - (q'.1 : ℂ).im|) ≤
      32 * cramerCountConstant ^ 2 * ((k : ℝ) + 1) ^ 2 := by
  have hR : (1 : ℝ) ≤ 2 ^ (k + 1) := one_le_pow₀ (by norm_num)
  have hqR := hF q hq
  have hb : ∀ q' ∈ F,
      |(q'.1 : ℂ).im - (q.1 : ℂ).im| ≤ 2 * (2 : ℝ) ^ (k + 1) := by
    intro q' hq'
    have h := abs_sub (zeroOrdinate q') (zeroOrdinate q)
    have hq'R := hF q' hq'
    change |zeroOrdinate q' - zeroOrdinate q| ≤ _
    linarith
  have h := sum_inv_one_add_abs_im_sub_le F (by positivity) hb
  have hlog₁ := cramer_log_bound k
    (s := |zeroOrdinate q| + 2 * (2 : ℝ) ^ (k + 1) + 4)
    (by positivity) (by linarith)
  have hlog₂ := cramer_log_bound k (s := 2 * (2 : ℝ) ^ (k + 1) + 1)
    (by positivity) (by linarith)
  have hA := abs_nonneg xiLineTwoLogDerivConstant
  have hB := cramerCountConstant_pos
  have hL : 0 ≤ Real.log (2 * (2 : ℝ) ^ (k + 1) + 1) :=
    Real.log_nonneg (by linarith)
  simp_rw [abs_sub_comm (q.1 : ℂ).im] at ⊢
  calc
    _ ≤ 32 * (|xiLineTwoLogDerivConstant| +
        Real.log (|zeroOrdinate q| + 2 * 2 ^ (k + 1) + 4)) *
        (1 + Real.log (2 * 2 ^ (k + 1) + 1)) := h
    _ ≤ 32 * (cramerCountConstant * ((k : ℝ) + 1)) *
        (cramerCountConstant * ((k : ℝ) + 1)) := by
      gcongr <;> first | positivity | linarith
    _ = _ := by ring

private theorem cramer_shell_energy (hRH : RiemannHypothesis) {X D : ℝ}
    (hX : 0 < X) (hD : 0 ≤ D) (F : Finset XiZeroCopy) (c : XiZeroCopy → ℂ) (k : ℕ)
    (hF : ∀ q ∈ F, cramerHeightIndex q = k)
    (hc : ∀ q ∈ F, ‖c q‖ ≤ D / |zeroOrdinate q|) :
    ∫ x in X..2 * X, ‖∑ q ∈ F, c q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2 / x ^ 3 ≤
      10240 * cramerCountConstant ^ 3 * D ^ 2 / X *
        (((k : ℝ) + 1) ^ 3 * (1 / 2 : ℝ) ^ k) := by
  have hlo : ∀ q ∈ F, (2 : ℝ) ^ k ≤ |zeroOrdinate q| := by
    intro q hq
    simpa only [hF q hq] using (cramerHeightIndex_spec q).1
  have hhi : ∀ q ∈ F, |zeroOrdinate q| < (2 : ℝ) ^ (k + 1) := by
    intro q hq
    simpa only [hF q hq] using (cramerHeightIndex_spec q).2
  have hpow : (0 : ℝ) < 2 ^ k := by positivity
  have hcb : ∀ q ∈ F, ‖c q‖ ^ 2 ≤ D ^ 2 / ((2 : ℝ) ^ k) ^ 2 := by
    intro q hq
    have h := (hc q hq).trans (div_le_div_of_nonneg_left hD hpow (hlo q hq))
    simpa only [div_pow] using pow_le_pow_left₀ (norm_nonneg _) h 2
  have hmean := integral_norm_sq_zeroSum_div_cube_le hX F c
    (fun q hq => cramer_shell_row F k hhi hq)
  have he : ∀ q : XiZeroCopy, X ^ (2 * (q.1 : ℂ).re - 2) = X⁻¹ := by
    intro q
    rw [xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q]
    norm_num [Real.rpow_neg_one]
  simp_rw [he] at hmean
  have hsum : ∑ q ∈ F, ‖c q‖ ^ 2 * X⁻¹ ≤
      (80 * cramerCountConstant * ((k : ℝ) + 1) * (2 : ℝ) ^ k) *
        (D ^ 2 / ((2 : ℝ) ^ k) ^ 2 * X⁻¹) := by
    calc
      _ ≤ ∑ q ∈ F, D ^ 2 / ((2 : ℝ) ^ k) ^ 2 * X⁻¹ := by
        apply Finset.sum_le_sum
        intro q hq
        exact mul_le_mul_of_nonneg_right (hcb q hq) (inv_nonneg.mpr hX.le)
      _ = (F.card : ℝ) * (D ^ 2 / ((2 : ℝ) ^ k) ^ 2 * X⁻¹) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (cramer_shell_card F k hhi) (by positivity)
  refine hmean.trans ((mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq ?_)
  rw [div_pow, one_pow]
  field_simp
  ring

private theorem cramer_summable_shell_budget :
    Summable (fun k : ℕ => ((k : ℝ) + 1) ^ 3 * (2 / 3 : ℝ) ^ k) := by
  have h0 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 0
    (r := 2 / 3) (by norm_num)
  have h1 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
    (r := 2 / 3) (by norm_num)
  have h2 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2
    (r := 2 / 3) (by norm_num)
  have h3 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 3
    (r := 2 / 3) (by norm_num)
  apply (h3.add ((h2.mul_left 3).add ((h1.mul_left 3).add h0))).congr
  intro k
  ring

private theorem cramer_sum_continuous {X : ℝ} (hX : 0 < X)
    (F : Finset XiZeroCopy) (c : XiZeroCopy → ℂ) :
    ContinuousOn (fun x : ℝ =>
      ‖∑ q ∈ F, c q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2 / x ^ 3) (uIcc X (2 * X)) := by
  have hx : ∀ x ∈ uIcc X (2 * X), 0 < x := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    exact hX.trans_le hx.1
  apply ContinuousOn.div _ (continuousOn_id.pow 3) (fun x h => pow_ne_zero _ (hx x h).ne')
  apply ContinuousOn.pow _ 2
  apply ContinuousOn.norm
  apply continuousOn_finsetSum
  intro q _
  apply continuousOn_const.mul
  apply continuousOn_of_forall_continuousAt
  intro x h
  exact Complex.continuousAt_ofReal_cpow_const x _ (Or.inr (hx x h).ne')

/-- A finite universal constant for the zero-sum mean square; no sharp value is needed. -/
def cramerZeroEnergyConstant : ℝ :=
  40960 * cramerCountConstant ^ 3 *
    ∑' k : ℕ, ((k : ℝ) + 1) ^ 3 * (2 / 3 : ℝ) ^ k

theorem cramerZeroEnergyConstant_nonneg : 0 ≤ cramerZeroEnergyConstant := by
  unfold cramerZeroEnergyConstant
  have := cramerCountConstant_pos
  positivity

/-- The shell form of the mean-square bound: each dyadic shell `k` present in `F` contributes
`(k + 1)³ (2/3)^k`. -/
private theorem cramer_finite_zero_energy_shells (hRH : RiemannHypothesis) {X D : ℝ}
    (hX : 0 < X) (hD : 0 ≤ D) (F : Finset XiZeroCopy) (c : XiZeroCopy → ℂ)
    (hc : ∀ q ∈ F, ‖c q‖ ≤ D / |zeroOrdinate q|) :
    ∫ x in X..2 * X, ‖∑ q ∈ F, c q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2 / x ^ 3 ≤
      (40960 * cramerCountConstant ^ 3 * D ^ 2 / X) *
        ∑ k ∈ F.image cramerHeightIndex, ((k : ℝ) + 1) ^ 3 * (2 / 3 : ℝ) ^ k := by
  classical
  let S := F.image cramerHeightIndex
  let Fk (k : ℕ) := F.filter (fun q => cramerHeightIndex q = k)
  let H (k : ℕ) (x : ℝ) := ∑ q ∈ Fk k, c q * (x : ℂ) ^ (q.1 : ℂ)
  have hsplit (x : ℝ) : (∑ q ∈ F, c q * (x : ℂ) ^ (q.1 : ℂ)) = ∑ k ∈ S, H k x := by
    exact (Finset.sum_fiberwise_of_maps_to
      (fun q hq => Finset.mem_image_of_mem _ hq)
      (fun q => c q * (x : ℂ) ^ (q.1 : ℂ))).symm
  have hweights : ∑ k ∈ S, (3 / 4 : ℝ) ^ k ≤ 4 := by
    have hs := summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 3 / 4)
      (by norm_num : (3 / 4 : ℝ) < 1)
    calc
      _ ≤ ∑' k : ℕ, (3 / 4 : ℝ) ^ k := hs.sum_le_tsum S (by intros; positivity)
      _ = 4 := by rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
  have hpt (x : ℝ) (hx : x ∈ Icc X (2 * X)) :
      ‖∑ q ∈ F, c q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2 / x ^ 3 ≤
        4 * ∑ k ∈ S, (‖H k x‖ ^ 2 / x ^ 3) / (3 / 4 : ℝ) ^ k := by
    have hx0 := hX.trans_le hx.1
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul S
      (f := fun k => (3 / 4 : ℝ) ^ k)
      (g := fun k => ‖H k x‖ ^ 2 / (3 / 4 : ℝ) ^ k)
      (r := fun k => ‖H k x‖)
      (by intros; positivity) (by intros; positivity)
      (fun k _ => by rw [mul_div_cancel₀ _ (by positivity)] )
    have hs0 : 0 ≤ ∑ k ∈ S, ‖H k x‖ ^ 2 / (3 / 4 : ℝ) ^ k := by positivity
    have hn : ‖∑ q ∈ F, c q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2 ≤
        4 * ∑ k ∈ S, ‖H k x‖ ^ 2 / (3 / 4 : ℝ) ^ k := by
      rw [hsplit]
      exact (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le S (fun k => H k x)) 2).trans
        (hcs.trans (mul_le_mul_of_nonneg_right hweights hs0))
    calc
      _ ≤ (4 * ∑ k ∈ S, ‖H k x‖ ^ 2 / (3 / 4 : ℝ) ^ k) / x ^ 3 :=
        div_le_div_of_nonneg_right hn (by positivity)
      _ = _ := by simp only [mul_div_assoc, Finset.sum_div]; congr 1; apply Finset.sum_congr rfl; intros; ring
  have hi (k : ℕ) : IntervalIntegrable
      (fun x : ℝ => (‖H k x‖ ^ 2 / x ^ 3) / (3 / 4 : ℝ) ^ k) volume X (2 * X) :=
    ((cramer_sum_continuous hX (Fk k) c).div_const _).intervalIntegrable
  have hE (k : ℕ) :
      (∫ x in X..2 * X, ‖H k x‖ ^ 2 / x ^ 3) / (3 / 4 : ℝ) ^ k ≤
        10240 * cramerCountConstant ^ 3 * D ^ 2 / X *
          (((k : ℝ) + 1) ^ 3 * (2 / 3 : ℝ) ^ k) := by
    have h := cramer_shell_energy hRH hX hD (Fk k) c k
      (fun q hq => (Finset.mem_filter.mp hq).2)
      (fun q hq => hc q (Finset.mem_filter.mp hq).1)
    calc
      _ ≤ (10240 * cramerCountConstant ^ 3 * D ^ 2 / X *
          (((k : ℝ) + 1) ^ 3 * (1 / 2 : ℝ) ^ k)) / (3 / 4 : ℝ) ^ k := by
        exact div_le_div_of_nonneg_right h (by positivity)
      _ = _ := by simp only [mul_div_assoc, ← div_pow]; norm_num
  calc
    _ ≤ ∫ x in X..2 * X, 4 * ∑ k ∈ S,
        (‖H k x‖ ^ 2 / x ^ 3) / (3 / 4 : ℝ) ^ k :=
      intervalIntegral.integral_mono_on (by linarith)
        (cramer_sum_continuous hX F c).intervalIntegrable
        (by simpa only [Finset.sum_apply] using
          ((IntervalIntegrable.sum S (fun k _ => hi k)).const_mul 4)) hpt
    _ = 4 * ∑ k ∈ S, (∫ x in X..2 * X, ‖H k x‖ ^ 2 / x ^ 3) / (3 / 4 : ℝ) ^ k := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum (fun k _ => hi k)]
      simp only [intervalIntegral.integral_div]
    _ ≤ 4 * ∑ k ∈ S, 10240 * cramerCountConstant ^ 3 * D ^ 2 / X *
        (((k : ℝ) + 1) ^ 3 * (2 / 3 : ℝ) ^ k) := by
      gcongr with k hk
      exact hE k
    _ = (40960 * cramerCountConstant ^ 3 * D ^ 2 / X) *
        ∑ k ∈ S, ((k : ℝ) + 1) ^ 3 * (2 / 3 : ℝ) ^ k := by rw [← Finset.mul_sum]; ring

/-- Uniform mean-square control of every finite critical-line zero sum with `1/|γ|`
coefficients; the bound is independent of the largest ordinate. -/
theorem cramer_finite_zero_energy (hRH : RiemannHypothesis) {X D : ℝ}
    (hX : 0 < X) (hD : 0 ≤ D) (F : Finset XiZeroCopy) (c : XiZeroCopy → ℂ)
    (hc : ∀ q ∈ F, ‖c q‖ ≤ D / |zeroOrdinate q|) :
    ∫ x in X..2 * X, ‖∑ q ∈ F, c q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2 / x ^ 3 ≤
      cramerZeroEnergyConstant * D ^ 2 / X := by
  refine (cramer_finite_zero_energy_shells hRH hX hD F c hc).trans ?_
  calc (40960 * cramerCountConstant ^ 3 * D ^ 2 / X) *
        ∑ k ∈ F.image cramerHeightIndex, ((k : ℝ) + 1) ^ 3 * (2 / 3 : ℝ) ^ k
      ≤ (40960 * cramerCountConstant ^ 3 * D ^ 2 / X) *
          ∑' k : ℕ, ((k : ℝ) + 1) ^ 3 * (2 / 3 : ℝ) ^ k := by
        apply mul_le_mul_of_nonneg_left
          (cramer_summable_shell_budget.sum_le_tsum _ (by intros; positivity))
        have := cramerCountConstant_pos
        positivity
    _ = _ := by unfold cramerZeroEnergyConstant; ring

/-- The constant of the shell-tail mean square. -/
def cramerTailConstant : ℝ := 40960 * cramerCountConstant ^ 3

theorem cramerTailConstant_nonneg : 0 ≤ cramerTailConstant := by
  unfold cramerTailConstant
  have := cramerCountConstant_pos
  positivity

/-- The share of the shells `k ≥ k₀`: `Σ_{k ≥ k₀} (k + 1)³ (2/3)^k`. -/
def cramerShellTail (k₀ : ℕ) : ℝ :=
  ∑' k : ℕ, (((k + k₀ : ℕ) : ℝ) + 1) ^ 3 * (2 / 3 : ℝ) ^ (k + k₀)

theorem cramerShellTail_nonneg (k₀ : ℕ) : 0 ≤ cramerShellTail k₀ :=
  tsum_nonneg fun _ => by positivity

/-- The high shells carry a vanishing share: `Σ_{k ≥ k₀} (k + 1)³ (2/3)^k → 0`. -/
theorem tendsto_cramerShellTail : Tendsto cramerShellTail atTop (𝓝 0) :=
  tendsto_sum_nat_add fun k : ℕ => ((k : ℝ) + 1) ^ 3 * (2 / 3 : ℝ) ^ k

/-- **The high-shell mean square.** Under RH, a finite zero sum with coefficients
`‖c_q‖ ≤ D/|γ_q|` supported on `|γ_q| ≥ 2^{k₀}` has dyadic mean square at most
`C_tail D²/X · Σ_{k ≥ k₀} (k + 1)³ (2/3)^k`. -/
theorem cramer_finite_zero_energy_tail (hRH : RiemannHypothesis) {X D : ℝ}
    (hX : 0 < X) (hD : 0 ≤ D) (F : Finset XiZeroCopy) (c : XiZeroCopy → ℂ)
    (hc : ∀ q ∈ F, ‖c q‖ ≤ D / |zeroOrdinate q|) (k₀ : ℕ)
    (hF : ∀ q ∈ F, (2 : ℝ) ^ k₀ ≤ |zeroOrdinate q|) :
    ∫ x in X..2 * X, ‖∑ q ∈ F, c q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2 / x ^ 3 ≤
      cramerTailConstant * D ^ 2 / X * cramerShellTail k₀ := by
  refine (cramer_finite_zero_energy_shells hRH hX hD F c hc).trans ?_
  unfold cramerTailConstant
  have hk : ∀ k ∈ F.image cramerHeightIndex, k₀ ≤ k := by
    intro k hk
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hk
    by_contra hlt
    have h1 := (cramerHeightIndex_spec q).2
    have h2 : (2 : ℝ) ^ (cramerHeightIndex q + 1) ≤ 2 ^ k₀ :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    linarith [hF q hq]
  have hsum : ∑ k ∈ F.image cramerHeightIndex, ((k : ℝ) + 1) ^ 3 * (2 / 3 : ℝ) ^ k ≤
      cramerShellTail k₀ := by
    have hinj : Set.InjOn (fun k : ℕ => k - k₀) (F.image cramerHeightIndex : Set ℕ) :=
      fun a ha b hb h => by
        have := hk a ha; have := hk b hb; simp only at h; omega
    have hre : ∑ k ∈ F.image cramerHeightIndex, ((k : ℝ) + 1) ^ 3 * (2 / 3 : ℝ) ^ k =
        ∑ j ∈ (F.image cramerHeightIndex).image (fun k => k - k₀),
          (((j + k₀ : ℕ) : ℝ) + 1) ^ 3 * (2 / 3 : ℝ) ^ (j + k₀) := by
      rw [Finset.sum_image hinj]
      refine Finset.sum_congr rfl fun k hk' => ?_
      rw [Nat.sub_add_cancel (hk k hk')]
    rw [hre]
    exact (cramer_summable_shell_budget.comp_injective (add_left_injective k₀)).sum_le_tsum _
      (fun _ _ => by positivity)
  exact mul_le_mul_of_nonneg_left hsum (by have := cramerCountConstant_pos; positivity)

/-- The same bound for an absolutely convergent zero sum. This will be applied to
short-window coefficients before the smoothing parameter tends to zero. -/
theorem cramer_summable_zero_energy (hRH : RiemannHypothesis) {X D : ℝ}
    (hX : 1 ≤ X) (hD : 0 ≤ D) (c : XiZeroCopy → ℂ)
    (hc : ∀ q, ‖c q‖ ≤ D / |zeroOrdinate q|) (hcs : Summable (fun q => ‖c q‖)) :
    ∫ x in X..2 * X, ‖∑' q : XiZeroCopy, c q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2 / x ^ 3 ≤
      cramerZeroEnergyConstant * D ^ 2 / X := by
  have hX0 : 0 < X := by linarith
  have hXX : X ≤ 2 * X := by linarith
  let B := (2 * X) * ∑' q : XiZeroCopy, ‖c q‖
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hterm (x : ℝ) (hx : x ∈ uIcc X (2 * X)) (q : XiZeroCopy) :
      ‖c q * (x : ℂ) ^ (q.1 : ℂ)‖ ≤ (2 * X) * ‖c q‖ := by
    rw [uIcc_of_le hXX] at hx
    have hx1 : 1 ≤ x := hX.trans hx.1
    have hx0 : 0 < x := by linarith
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have hp : x ^ (q.1 : ℂ).re ≤ 2 * X := by
      calc
        _ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (xiZeroCopy_re_lt_one q).le
        _ = x := Real.rpow_one x
        _ ≤ _ := hx.2
    nlinarith [norm_nonneg (c q)]
  have hs (x : ℝ) (hx : x ∈ uIcc X (2 * X)) :
      Summable (fun q : XiZeroCopy => c q * (x : ℂ) ^ (q.1 : ℂ)) :=
    Summable.of_norm_bounded (hcs.mul_left (2 * X)) (hterm x hx)
  have hnorm (F : Finset XiZeroCopy) (x : ℝ) (hx : x ∈ uIcc X (2 * X)) :
      ‖∑ q ∈ F, c q * (x : ℂ) ^ (q.1 : ℂ)‖ ≤ B := by
    calc
      _ ≤ ∑ q ∈ F, ‖c q * (x : ℂ) ^ (q.1 : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ q ∈ F, (2 * X) * ‖c q‖ := Finset.sum_le_sum (fun q _ => hterm x hx q)
      _ = (2 * X) * ∑ q ∈ F, ‖c q‖ := (Finset.mul_sum ..).symm
      _ ≤ B := mul_le_mul_of_nonneg_left
        (hcs.sum_le_tsum F (fun q _ => norm_nonneg _)) (by positivity)
  have ht : Tendsto (fun F : Finset XiZeroCopy =>
      ∫ x in X..2 * X, ‖∑ q ∈ F, c q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2 / x ^ 3)
      atTop (𝓝 (∫ x in X..2 * X, ‖∑' q : XiZeroCopy,
        c q * (x : ℂ) ^ (q.1 : ℂ)‖ ^ 2 / x ^ 3)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (bound := fun _ => B ^ 2 / X ^ 3)
    · exact Eventually.of_forall (fun F =>
        ((cramer_sum_continuous hX0 F c).mono uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc)
    · apply Eventually.of_forall
      intro F
      apply ae_of_all
      intro x hx
      have hx' := uIoc_subset_uIcc hx
      have hxX : X ≤ x :=
        (show x ∈ Set.Icc X (2 * X) from by simpa only [Set.uIcc_of_le hXX] using hx').1
      have hx0 : 0 < x := hX0.trans_le hxX
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      apply div_le_div₀ (by positivity)
        (pow_le_pow_left₀ (norm_nonneg _) (hnorm F x hx') 2)
        (by positivity) (pow_le_pow_left₀ hX0.le hxX 3)
    · exact intervalIntegrable_const
    · apply ae_of_all
      intro x hx
      exact ((hs x (uIoc_subset_uIcc hx)).hasSum.norm.pow 2).div_const (x ^ 3)
  exact le_of_tendsto ht (Eventually.of_forall
    (fun F => cramer_finite_zero_energy hRH hX0 hD F c (fun q _ => hc q)))

end
end RHTower
