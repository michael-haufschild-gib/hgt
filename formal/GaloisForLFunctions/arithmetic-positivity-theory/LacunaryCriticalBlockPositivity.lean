import GaloisForLFunctions.«arithmetic-positivity-theory».CriticalPrimeChannelCrossBlockDecay

/-!
# Positivity of compact critical sources across lacunary blocks

A **lacunary block family** consists of dyadic blocks `S_0, …, S_{J-1}` at scales
`M_0 ≥ 3` with `M_{i+1} ≥ M_i⁸`. The number of blocks is unbounded, so a pattern on the union
spans scales from `M_0` to `M_0^{8^{J-1}}`. This module proves that the complete energy of the
compact doubly collared source of such a pattern is positive definite once `M_0` is large. The
same conclusion holds for the full Weil functional of `ζ` on the corresponding compact test.

* **Finite dilation form.** At truncation `V` only the dilations `2 ≤ r ≤ ⌈2V⌉` see the source.
  Its prime channel is then the finite sum
  `∑_r (Λ(r)/r) ∫_{v>1} ψ(v) χ(rv/V) B_b(v) B_b(rv) dv`.
* **Block expansion.** Over a disjoint union of blocks, the prime channel splits into block-pair
  couplings. The diagonal couplings are the prime channels of the single blocks, bounded by
  `C_T ∑ b²`.
* **Lacunary decay.** For `m⁸ ≤ n` the cross-block decay satisfies
  `τ(m, n) ≤ 50 m^{-1/16} n^{-1/16}`. Each off-diagonal coupling is therefore at most
  `50 K w_i w_{i'} ‖b_i‖ ‖b_{i'}‖` with `w_i = M_i^{-1/16}`. By Cauchy–Schwarz the off-diagonal
  part is at most `50 K (∑ w_i²) ∑ b² ≤ 100 K ∑ b²`, because `M_i ≥ 256^i` makes
  `∑ M_i^{-1/8} ≤ 2`.
* **Assembly.** The archimedean channel is logarithmically coercive above the lowest scale `M_0`.
  The Gamma and polar channels are `ℓ²`-bounded on any support above `M_0`. Hence
  `E(g^V) ≥ (s_T (log M_0 - c_T) - K_lac) ∑ b²`, uniformly in `V` and in the number of blocks.

Across lacunary blocks, the prime coupling of two critical patterns is therefore a summable
perturbation of the block-diagonal form.
-/

open MeasureTheory Set Filter
open scoped Topology
open _root_.Zeta23

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

/-! ### The doubly collared prime channel as a finite dilation sum -/

/-- Dilations `2 ≤ r ≤ ⌈2V⌉` that see a doubly collared source of truncation `V`. -/
def truncationDilations (V : ℝ) : Finset ℕ := Finset.Ico 2 (⌈2 * V⌉₊ + 1)

theorem two_le_of_mem_truncationDilations {V : ℝ} {r : ℕ} (hr : r ∈ truncationDilations V) :
    2 ≤ r :=
  (Finset.mem_Ico.mp hr).1

private theorem integral_truncatedWeight_eq_zero {V : ℝ} (hV : 0 < V) {r : ℕ} (hr : 2 * V ≤ r)
    (f : ℝ → ℝ) : ∫ v in Ioi 1, criticalTruncatedWeight ((r : ℝ) / V) v * f v = 0 := by
  refine setIntegral_eq_zero_of_forall_eq_zero fun v hv => ?_
  have hv1 : (1 : ℝ) < v := hv
  rw [criticalTruncatedWeight, criticalUpperCutoff_eq_zero, mul_zero, zero_mul]
  rw [div_mul_eq_mul_div, le_div_iff₀ hV]
  nlinarith

/-- A prime atom of a doubly collared source is the dilation correlation of its phase
combination against `ψ(v) χ(rv/V)`. -/
theorem criticalTruncatedPrimeAtom_eq {V : ℝ} (hV : 0 < V) (S : Finset ℕ) (b : ℕ → ℝ) {r : ℕ}
    (hr : 2 ≤ r) :
    criticalTruncatedPrimeAtom V S b r = (ArithmeticFunction.vonMangoldt r : ℝ) / r *
      ∫ v in Ioi 1, criticalTruncatedWeight ((r : ℝ) / V) v *
        (realPhaseCombination S b v * realPhaseCombination S b (r * v)) := by
  have hr0 : (0 : ℝ) < r := by
    have : (2 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  unfold criticalTruncatedPrimeAtom
  rw [if_pos hr, integral_criticalTruncatedSource_mul_dilate hV S b hr]
  have hw : (∫ v in Ioi 1, criticalCollarWeight v * criticalUpperCutoff (r * v / V) *
      (realPhaseCombination S b v * realPhaseCombination S b (r * v))) =
      ∫ v in Ioi 1, criticalTruncatedWeight ((r : ℝ) / V) v *
        (realPhaseCombination S b v * realPhaseCombination S b (r * v)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
    simp only [criticalTruncatedWeight]
    rw [show (r : ℝ) / V * v = r * v / V by ring]
  rw [hw]
  have hs0 : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr0
  field_simp
  rw [Real.sq_sqrt hr0.le]

/-- **Finite dilation form of the doubly collared prime channel.** -/
theorem criticalTruncatedPrimeEnergy_eq_sum {V : ℝ} (hV : 0 < V) (S : Finset ℕ) (b : ℕ → ℝ) :
    criticalTruncatedPrimeEnergy V S b = ∑ r ∈ truncationDilations V,
      (ArithmeticFunction.vonMangoldt r : ℝ) / r *
        ∫ v in Ioi 1, criticalTruncatedWeight ((r : ℝ) / V) v *
          (realPhaseCombination S b v * realPhaseCombination S b (r * v)) := by
  unfold criticalTruncatedPrimeEnergy
  rw [tsum_eq_sum (s := truncationDilations V) fun r hr => ?_]
  · exact Finset.sum_congr rfl fun r hr =>
      criticalTruncatedPrimeAtom_eq hV S b (two_le_of_mem_truncationDilations hr)
  · simp only [truncationDilations, Finset.mem_Ico, not_and_or, not_le, not_lt] at hr
    rcases hr with hr | hr
    · unfold criticalTruncatedPrimeAtom; rw [if_neg (by omega), zero_mul]
    · rw [criticalTruncatedPrimeAtom_eq hV S b (by
        have : 1 ≤ ⌈2 * V⌉₊ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by positivity)).ne'
        omega), integral_truncatedWeight_eq_zero hV (by
        have h1 : 2 * V ≤ ⌈2 * V⌉₊ := Nat.le_ceil _
        have h2 : (⌈2 * V⌉₊ : ℝ) ≤ r := by exact_mod_cast (show ⌈2 * V⌉₊ ≤ r by omega)
        linarith), mul_zero]

/-! ### Expansion over a union of blocks -/

private theorem integrableOn_mul_bdd'' {φ g : ℝ → ℝ} (hφ : IntegrableOn φ (Ioi 1)) (hg : Continuous g)
    {C : ℝ} (hC : ∀ v, |g v| ≤ C) : IntegrableOn (fun v => φ v * g v) (Ioi 1) := by
  refine (hφ.norm.const_mul C).mono' (hφ.aestronglyMeasurable.mul hg.aestronglyMeasurable)
    (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs, mul_comm C]
  exact mul_le_mul_of_nonneg_left (hC v) (abs_nonneg _)

theorem realPhaseCombination_biUnion {I : Finset ℕ} {S : ℕ → Finset ℕ}
    (hd : (I : Set ℕ).PairwiseDisjoint S) (b : ℕ → ℝ) (v : ℝ) :
    realPhaseCombination (I.biUnion S) b v = ∑ i ∈ I, realPhaseCombination (S i) b v := by
  unfold realPhaseCombination
  rw [Finset.sum_biUnion hd]

/-- A dilation correlation over a union of blocks splits into block-pair correlations. -/
theorem integral_weight_biUnion_dilate {φ : ℝ → ℝ} (hφ : IntegrableOn φ (Ioi 1)) {I : Finset ℕ}
    {S : ℕ → Finset ℕ} (hd : (I : Set ℕ).PairwiseDisjoint S) (b : ℕ → ℝ) (r : ℕ) :
    ∫ v in Ioi 1, φ v * (realPhaseCombination (I.biUnion S) b v *
        realPhaseCombination (I.biUnion S) b (r * v)) =
      ∑ i ∈ I, ∑ i' ∈ I, ∫ v in Ioi 1, φ v *
        (realPhaseCombination (S i) b v * realPhaseCombination (S i') b (r * v)) := by
  have hint (i i' : ℕ) : IntegrableOn (fun v => φ v *
      (realPhaseCombination (S i) b v * realPhaseCombination (S i') b (r * v))) (Ioi 1) :=
    integrableOn_mul_bdd'' hφ ((continuous_realPhaseCombination _ _).mul
      ((continuous_realPhaseCombination _ _).comp (continuous_const.mul continuous_id)))
      (C := (2 * ∑ n ∈ S i, |b n|) * (2 * ∑ n ∈ S i', |b n|)) fun v => by
        rw [abs_mul]
        exact mul_le_mul (abs_realPhaseCombination_le_two_mul _ _ _)
          (abs_realPhaseCombination_le_two_mul _ _ _) (abs_nonneg _)
          (by have := Finset.sum_nonneg fun n (_ : n ∈ S i) => abs_nonneg (b n); positivity)
  simp_rw [realPhaseCombination_biUnion hd, Finset.sum_mul_sum, Finset.mul_sum]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun i' _ => hint i i']
  exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun i' _ => hint i i'

/-- Block-pair prime coupling of a doubly collared source. -/
def truncatedBlockCoupling (V : ℝ) (S S' : Finset ℕ) (b : ℕ → ℝ) : ℝ :=
  ∑ r ∈ truncationDilations V, (ArithmeticFunction.vonMangoldt r : ℝ) / r *
    ∫ v in Ioi 1, criticalTruncatedWeight ((r : ℝ) / V) v *
      (realPhaseCombination S b v * realPhaseCombination S' b (r * v))

/-- **Block expansion of the prime channel.** Over a disjoint union of blocks, the doubly collared
prime channel is the sum of all block-pair couplings, and the diagonal couplings are the prime
channels of the blocks. -/
theorem criticalTruncatedPrimeEnergy_biUnion {V : ℝ} (hV : 0 < V) {I : Finset ℕ}
    {S : ℕ → Finset ℕ} (hd : (I : Set ℕ).PairwiseDisjoint S) (b : ℕ → ℝ) :
    criticalTruncatedPrimeEnergy V (I.biUnion S) b =
      ∑ i ∈ I, ∑ i' ∈ I, truncatedBlockCoupling V (S i) (S i') b := by
  rw [criticalTruncatedPrimeEnergy_eq_sum hV]
  simp_rw [integral_weight_biUnion_dilate (integrableOn_criticalTruncatedWeight _) hd, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  rfl

theorem truncatedBlockCoupling_self {V : ℝ} (hV : 0 < V) (S : Finset ℕ) (b : ℕ → ℝ) :
    truncatedBlockCoupling V S S b = criticalTruncatedPrimeEnergy V S b :=
  (criticalTruncatedPrimeEnergy_eq_sum hV S b).symm

/-! ### Lacunary block families -/

/-- A **lacunary block family**: for `i < J`, `S_i` is a dyadic block at `M_i`, with `M_0 ≥ 3` and
`M_{i+1} ≥ M_i⁸`. -/
def IsLacunaryBlockFamily (J : ℕ) (M : ℕ → ℕ) (S : ℕ → Finset ℕ) : Prop :=
  3 ≤ M 0 ∧ (∀ i, i + 1 < J → M i ^ 8 ≤ M (i + 1)) ∧ ∀ i < J, DyadicScaleBlock (S i) (M i)

namespace IsLacunaryBlockFamily

variable {J : ℕ} {M : ℕ → ℕ} {S : ℕ → Finset ℕ}

theorem three_le (h : IsLacunaryBlockFamily J M S) : ∀ i < J, 3 ≤ M i := by
  intro i
  induction i with
  | zero => intro _; exact h.1
  | succ i ih =>
    intro hi
    calc 3 ≤ M i := ih (by omega)
      _ ≤ M i ^ 8 := Nat.le_self_pow (by norm_num) _
      _ ≤ M (i + 1) := h.2.1 i hi

theorem pow_le (h : IsLacunaryBlockFamily J M S) {i i' : ℕ} (hii : i < i') (hi' : i' < J) :
    M i ^ 8 ≤ M i' := by
  obtain ⟨d, rfl⟩ : ∃ d, i' = i + 1 + d := ⟨i' - (i + 1), by omega⟩
  induction d with
  | zero => exact h.2.1 i (by omega)
  | succ d ih =>
    calc M i ^ 8 ≤ M (i + 1 + d) := ih (by omega) (by omega)
      _ ≤ M (i + 1 + d) ^ 8 := Nat.le_self_pow (by norm_num) _
      _ ≤ M (i + 1 + (d + 1)) := h.2.1 _ (by omega)

theorem le_of_lt (h : IsLacunaryBlockFamily J M S) {i i' : ℕ} (hii : i < i') (hi' : i' < J) :
    M i ≤ M i' :=
  (Nat.le_self_pow (by norm_num) _).trans (h.pow_le hii hi')

theorem growth (h : IsLacunaryBlockFamily J M S) : ∀ i < J, 256 ^ i ≤ M i := by
  intro i
  induction i with
  | zero => intro _; have := h.1; simp only [pow_zero]; omega
  | succ i ih =>
    intro hi
    have h3 := h.three_le i (by omega)
    have h7 : 256 ≤ M i ^ 7 := le_trans (by norm_num) (Nat.pow_le_pow_left h3 7)
    calc 256 ^ (i + 1) = 256 ^ i * 256 := pow_succ _ _
      _ ≤ M i * M i ^ 7 := Nat.mul_le_mul (ih (by omega)) h7
      _ = M i ^ 8 := by ring
      _ ≤ M (i + 1) := h.2.1 i hi

theorem pairwiseDisjoint (h : IsLacunaryBlockFamily J M S) :
    ((Finset.range J : Finset ℕ) : Set ℕ).PairwiseDisjoint S := by
  intro i hi i' hi' hne
  simp only [Finset.coe_range, Set.mem_Iio] at hi hi'
  have key : ∀ j j', j < j' → j' < J → Disjoint (S j) (S j') := by
    intro j j' hjj hj'
    rw [Finset.disjoint_left]
    intro n hn hn'
    have h1 := (h.2.2 j (by omega) n hn).2
    have h2 := (h.2.2 j' hj' n hn').1
    have h3 := h.three_le j (by omega)
    have h8 := h.pow_le hjj hj'
    have : 2 * M j < M j ^ 8 := by
      calc 2 * M j < M j * M j := by nlinarith
        _ = M j ^ 2 := by ring
        _ ≤ M j ^ 8 := Nat.pow_le_pow_right (by omega) (by norm_num)
    omega
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact key i i' hlt hi'
  · exact (key i' i hlt hi).symm

theorem lower (h : IsLacunaryBlockFamily J M S) {n : ℕ} (hn : n ∈ (Finset.range J).biUnion S) :
    M 0 ≤ n + 1 := by
  obtain ⟨i, hi, hn⟩ := Finset.mem_biUnion.mp hn
  have hi := Finset.mem_range.mp hi
  have hb := (h.2.2 i hi n hn).1
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · exact hb
  · exact (h.le_of_lt hpos hi).trans hb

end IsLacunaryBlockFamily

/-- **Lacunary cross-block decay.** If `m ≥ 1` and `m⁸ ≤ n`, then `τ(m, n) ≤ 50 m^{-1/16} n^{-1/16}`. -/
theorem crossBlockDecay_le_of_pow_le {m n : ℕ} (hm : 1 ≤ m) (hmn : m ^ 8 ≤ n) :
    crossBlockDecay m n ≤ 50 * ((m : ℝ) ^ (1 / 16 : ℝ))⁻¹ * ((n : ℝ) ^ (1 / 16 : ℝ))⁻¹ := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hn1 : (1 : ℝ) ≤ n := by
    have : 1 ≤ n := le_trans (Nat.one_le_pow _ _ hm) hmn
    exact_mod_cast this
  set x := (n : ℝ) ^ (1 / 32 : ℝ)
  have hx1 : 1 ≤ x := Real.one_le_rpow hn1 (by norm_num)
  have hx0 : 0 < x := by linarith
  have hnx : (n : ℝ) = x ^ 32 := by
    rw [← Real.rpow_natCast x, ← Real.rpow_mul (by linarith)]; norm_num
  have hmx : (m : ℝ) ≤ x ^ 4 := by
    have h8 : (m : ℝ) ^ 8 ≤ (x ^ 4) ^ 8 := by
      rw [← pow_mul, show 4 * 8 = 32 by norm_num, ← hnx]; exact_mod_cast hmn
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp h8
  have hn16 : (n : ℝ) ^ (1 / 16 : ℝ) = x ^ 2 := by
    rw [hnx, ← Real.rpow_natCast x 32, ← Real.rpow_mul hx0.le, ← Real.rpow_natCast x 2]; norm_num
  have hm16 : (m : ℝ) ^ (1 / 16 : ℝ) ≤ x := by
    calc (m : ℝ) ^ (1 / 16 : ℝ) ≤ (x ^ 4) ^ (1 / 16 : ℝ) :=
          Real.rpow_le_rpow (by linarith) hmx (by norm_num)
      _ = x ^ (1 / 4 : ℝ) := by rw [← Real.rpow_natCast x 4, ← Real.rpow_mul hx0.le]; norm_num
      _ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
      _ = x := Real.rpow_one x
  have hm16p : 0 < (m : ℝ) ^ (1 / 16 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  -- the logarithm
  have hlog : 1 + Real.log n ≤ 32 * x := by
    rw [hnx, Real.log_pow]
    have := Real.log_le_sub_one_of_pos hx0
    push_cast; linarith
  -- the square root
  have hinner : 1 / (n : ℝ) + m * Real.sqrt (m / n) ≤ 2 / x ^ 10 := by
    have h1 : 1 / (n : ℝ) ≤ 1 / x ^ 10 := by
      rw [hnx]; exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ hx1 (by norm_num))
    have h2 : Real.sqrt (m / n) ≤ 1 / x ^ 14 := by
      rw [show (1 : ℝ) / x ^ 14 = Real.sqrt ((1 / x ^ 14) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
      refine Real.sqrt_le_sqrt ?_
      rw [hnx, div_le_iff₀ (by positivity)]
      calc (m : ℝ) ≤ x ^ 4 := hmx
        _ = (1 / x ^ 14) ^ 2 * x ^ 32 := by field_simp
    have h3 : (m : ℝ) * Real.sqrt (m / n) ≤ 1 / x ^ 10 := by
      calc (m : ℝ) * Real.sqrt (m / n) ≤ x ^ 4 * (1 / x ^ 14) :=
            mul_le_mul hmx h2 (Real.sqrt_nonneg _) (by positivity)
        _ = 1 / x ^ 10 := by field_simp
    calc _ ≤ 1 / x ^ 10 + 1 / x ^ 10 := add_le_add h1 h3
      _ = 2 / x ^ 10 := by ring
  have hsq : Real.sqrt (1 / (n : ℝ) + m * Real.sqrt (m / n)) ≤ 3 / 2 / x ^ 5 := by
    refine (Real.sqrt_le_sqrt hinner).trans ?_
    rw [show (3 / 2 : ℝ) / x ^ 5 = Real.sqrt ((3 / 2 / x ^ 5) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
    refine Real.sqrt_le_sqrt ?_
    rw [div_pow, div_pow, ← pow_mul]
    exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
  unfold crossBlockDecay
  have h0 : 0 ≤ 1 + Real.log n := by have := Real.log_nonneg hn1; linarith
  calc (1 + Real.log n) * Real.sqrt (1 / (n : ℝ) + m * Real.sqrt (m / n)) ≤ (32 * x) * (3 / 2 / x ^ 5) :=
        mul_le_mul hlog hsq (Real.sqrt_nonneg _) (by positivity)
    _ = 48 / x ^ 4 := by field_simp; norm_num
    _ ≤ 50 / x ^ 3 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have : x ^ 3 ≤ x ^ 4 := pow_le_pow_right₀ hx1 (by norm_num)
        nlinarith [pow_pos hx0 3]
    _ = 50 * x⁻¹ * (x ^ 2)⁻¹ := by field_simp
    _ ≤ 50 * ((m : ℝ) ^ (1 / 16 : ℝ))⁻¹ * ((n : ℝ) ^ (1 / 16 : ℝ))⁻¹ := by
        rw [hn16]
        gcongr

/-- `∑_{i<J} M_i^{-1/8} ≤ 2` on a lacunary family. -/
theorem IsLacunaryBlockFamily.sum_weight_sq_le {J : ℕ} {M : ℕ → ℕ} {S : ℕ → Finset ℕ}
    (h : IsLacunaryBlockFamily J M S) :
    ∑ i ∈ Finset.range J, (((M i : ℝ) ^ (1 / 16 : ℝ))⁻¹) ^ 2 ≤ 2 := by
  refine le_trans (Finset.sum_le_sum fun i hi => ?_) (sum_geometric_two_le J)
  have hi := Finset.mem_range.mp hi
  have hg : ((256 : ℕ) ^ i : ℝ) ≤ M i := by exact_mod_cast h.growth i hi
  have hM0 : (0 : ℝ) < M i := by have := h.three_le i hi; positivity
  have e1 : (((M i : ℝ) ^ (1 / 16 : ℝ))⁻¹) ^ 2 = ((M i : ℝ) ^ (1 / 8 : ℝ))⁻¹ := by
    rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_mul hM0.le]; norm_num
  have e2 : (((256 : ℕ) : ℝ) ^ i) ^ (1 / 8 : ℝ) = 2 ^ i := by
    rw [show (((256 : ℕ) : ℝ) ^ i) = ((2 : ℝ) ^ i) ^ 8 by push_cast; rw [← pow_mul, mul_comm, pow_mul]; norm_num,
      show (1 / 8 : ℝ) = ((8 : ℕ) : ℝ)⁻¹ by norm_num, Real.pow_rpow_inv_natCast (by positivity) (by norm_num)]
  have : (2 : ℝ) ^ i ≤ (M i : ℝ) ^ (1 / 8 : ℝ) := by
    rw [← e2]; exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hg) (by norm_num)
  rw [e1, one_div_pow, one_div ((2 : ℝ) ^ i)]
  exact inv_anti₀ (by positivity) this

/-! ### The prime channel on lacunary unions of blocks -/

theorem crossBlockConstant_nonneg {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) : 0 ≤ crossBlockConstant A B := by
  unfold crossBlockConstant crossBlockHarmonicMass
  have h1 : 0 ≤ ∑' k, crossBlockHarmonicSeries k := tsum_nonneg crossBlockHarmonicSeries_nonneg
  have h2 : 0 ≤ ∑' l, crossBlockDualSeries l := tsum_nonneg crossBlockDualSeries_nonneg
  positivity

/-- The cross-block constant of doubly collared sources. -/
def truncatedCrossBlockConstant : ℝ := crossBlockConstant criticalCollarMass criticalTruncatedCurvature

theorem truncatedCrossBlockConstant_nonneg : 0 ≤ truncatedCrossBlockConstant :=
  crossBlockConstant_nonneg (integral_nonneg fun _ => abs_nonneg _) criticalTruncatedCurvature_nonneg

/-- **Cross-block coupling of doubly collared sources.** On two blocks of a lacunary pair
(`m⁸ ≤ n` for the smaller scale `m` and the larger `n`), the coupling is at most
`50 K m^{-1/16} n^{-1/16} ‖b_S‖ ‖b_{S'}‖`, in either dilation order and uniformly in `V`. -/
theorem abs_truncatedBlockCoupling_le_of_pow_le {V : ℝ} (hV : 0 < V) {S S' : Finset ℕ} {M M' : ℕ}
    (hS : DyadicScaleBlock S M) (hS' : DyadicScaleBlock S' M') (hM : 1 ≤ M) (hM' : 1 ≤ M')
    (hlac : M ^ 8 ≤ M' ∨ M' ^ 8 ≤ M) (b : ℕ → ℝ) :
    |truncatedBlockCoupling V S S' b| ≤ 50 * truncatedCrossBlockConstant *
      ((M : ℝ) ^ (1 / 16 : ℝ))⁻¹ * ((M' : ℝ) ^ (1 / 16 : ℝ))⁻¹ *
        Real.sqrt (∑ n ∈ S, b n ^ 2) * Real.sqrt (∑ n ∈ S', b n ^ 2) := by
  have hl (m : ℕ) : 0 ≤ (m : ℝ) / V := by positivity
  have hA := fun m f => (abs_weightCosineTransform_criticalTruncatedWeight_le (hl m)).1 f
  have hB := fun m f hf => (abs_weightCosineTransform_criticalTruncatedWeight_le (hl m)).2 f hf
  have hφ : ∀ r ∈ truncationDilations V, IntegrableOn (criticalTruncatedWeight ((r : ℝ) / V)) (Ioi 1) :=
    fun r _ => integrableOn_criticalTruncatedWeight _
  have hR := fun r hr => two_le_of_mem_truncationDilations (V := V) (r := r) hr
  have hK := truncatedCrossBlockConstant_nonneg
  have hX : 0 ≤ Real.sqrt (∑ n ∈ S, b n ^ 2) * Real.sqrt (∑ n ∈ S', b n ^ 2) := by positivity
  rcases hlac with h8 | h8
  · have hMM : M ≤ M' := (Nat.le_self_pow (by norm_num) _).trans h8
    have h := abs_sum_integral_crossBlock_up_le (φ := fun r => criticalTruncatedWeight ((r : ℝ) / V))
      hφ hA hB criticalTruncatedCurvature_nonneg hR hM hMM hS hS' b b
    have hτ := crossBlockDecay_le_of_pow_le hM h8
    unfold truncatedBlockCoupling
    refine h.trans ?_
    calc truncatedCrossBlockConstant * crossBlockDecay M M' * Real.sqrt (∑ n ∈ S, b n ^ 2) *
          Real.sqrt (∑ n ∈ S', b n ^ 2) =
          truncatedCrossBlockConstant * crossBlockDecay M M' *
            (Real.sqrt (∑ n ∈ S, b n ^ 2) * Real.sqrt (∑ n ∈ S', b n ^ 2)) := by ring
      _ ≤ truncatedCrossBlockConstant * (50 * ((M : ℝ) ^ (1 / 16 : ℝ))⁻¹ * ((M' : ℝ) ^ (1 / 16 : ℝ))⁻¹) *
            (Real.sqrt (∑ n ∈ S, b n ^ 2) * Real.sqrt (∑ n ∈ S', b n ^ 2)) := by gcongr
      _ = _ := by ring
  · have hMM : M' ≤ M := (Nat.le_self_pow (by norm_num) _).trans h8
    have h := abs_sum_integral_crossBlock_down_le (φ := fun r => criticalTruncatedWeight ((r : ℝ) / V))
      hφ hA hB criticalTruncatedCurvature_nonneg hR hM' hMM hS hS' b b
    have hτ := crossBlockDecay_le_of_pow_le hM' h8
    unfold truncatedBlockCoupling
    refine h.trans ?_
    calc truncatedCrossBlockConstant * crossBlockDecay M' M * Real.sqrt (∑ n ∈ S, b n ^ 2) *
          Real.sqrt (∑ n ∈ S', b n ^ 2) =
          truncatedCrossBlockConstant * crossBlockDecay M' M *
            (Real.sqrt (∑ n ∈ S, b n ^ 2) * Real.sqrt (∑ n ∈ S', b n ^ 2)) := by ring
      _ ≤ truncatedCrossBlockConstant * (50 * ((M' : ℝ) ^ (1 / 16 : ℝ))⁻¹ * ((M : ℝ) ^ (1 / 16 : ℝ))⁻¹) *
            (Real.sqrt (∑ n ∈ S, b n ^ 2) * Real.sqrt (∑ n ∈ S', b n ^ 2)) := by gcongr
      _ = _ := by ring

/-- Lacunary prime constant `C_T + 100 K`. -/
def lacunaryPrimeConstant : ℝ := criticalTruncatedPrimeConstant + 100 * truncatedCrossBlockConstant

/-- **The prime channel on lacunary unions is `ℓ²`-bounded.** For every lacunary block family, every
truncation and every real pattern on the union of the blocks, `|P(g^V)| ≤ (C_T + 100 K) ∑ b_n²`,
with no restriction on the number of blocks. -/
theorem abs_criticalTruncatedPrimeEnergy_le_of_lacunary {V : ℝ} (hV : 0 < V) {J : ℕ} {M : ℕ → ℕ}
    {S : ℕ → Finset ℕ} (h : IsLacunaryBlockFamily J M S) (b : ℕ → ℝ) :
    |criticalTruncatedPrimeEnergy V ((Finset.range J).biUnion S) b| ≤
      lacunaryPrimeConstant * ∑ n ∈ (Finset.range J).biUnion S, b n ^ 2 := by
  set I := Finset.range J
  set X : ℕ → ℝ := fun i => ∑ n ∈ S i, b n ^ 2
  set s : ℕ → ℝ := fun i => Real.sqrt (X i)
  set w : ℕ → ℝ := fun i => ((M i : ℝ) ^ (1 / 16 : ℝ))⁻¹
  set K := truncatedCrossBlockConstant
  have hK := truncatedCrossBlockConstant_nonneg
  have hX (i : ℕ) : 0 ≤ X i := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hw (i : ℕ) : 0 ≤ w i := by simp only [w]; positivity
  have hd := h.pairwiseDisjoint
  have hE : ∑ n ∈ I.biUnion S, b n ^ 2 = ∑ i ∈ I, X i := Finset.sum_biUnion hd
  have hM1 : ∀ i ∈ I, 1 ≤ M i := fun i hi => by
    have := h.three_le i (Finset.mem_range.mp hi); omega
  -- diagonal couplings
  have hdiag : ∀ i ∈ I, |truncatedBlockCoupling V (S i) (S i) b| ≤ criticalTruncatedPrimeConstant * X i :=
    fun i hi => by
      rw [truncatedBlockCoupling_self hV]
      exact abs_criticalTruncatedPrimeEnergy_le hV (hM1 i hi) (h.2.2 i (Finset.mem_range.mp hi)) b
  -- off-diagonal couplings
  have hoff : ∀ i ∈ I, ∀ i' ∈ I, i ≠ i' →
      |truncatedBlockCoupling V (S i) (S i') b| ≤ 50 * K * (w i * s i) * (w i' * s i') := by
    intro i hi i' hi' hne
    have hi1 := Finset.mem_range.mp hi
    have hi1' := Finset.mem_range.mp hi'
    have hlac : M i ^ 8 ≤ M i' ∨ M i' ^ 8 ≤ M i := by
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · exact Or.inl (h.pow_le hlt hi1')
      · exact Or.inr (h.pow_le hlt hi1)
    refine (abs_truncatedBlockCoupling_le_of_pow_le hV (h.2.2 i hi1) (h.2.2 i' hi1') (hM1 i hi)
      (hM1 i' hi') hlac b).trans (le_of_eq ?_)
    simp only [w, s, X, K]
    ring
  have hsplit : ∑ i ∈ I, ∑ i' ∈ I, truncatedBlockCoupling V (S i) (S i') b =
      ∑ i ∈ I, truncatedBlockCoupling V (S i) (S i) b +
        ∑ i ∈ I, ∑ i' ∈ I.erase i, truncatedBlockCoupling V (S i) (S i') b := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i hi => (Finset.add_sum_erase I _ hi).symm
  have hdiagsum : |∑ i ∈ I, truncatedBlockCoupling V (S i) (S i) b| ≤
      criticalTruncatedPrimeConstant * ∑ i ∈ I, X i := by
    rw [Finset.mul_sum]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hdiag)
  have hoffsum : |∑ i ∈ I, ∑ i' ∈ I.erase i, truncatedBlockCoupling V (S i) (S i') b| ≤
      100 * K * ∑ i ∈ I, X i := by
    have hnn (i i' : ℕ) : 0 ≤ 50 * K * (w i * s i) * (w i' * s i') := by
      have := hw i; have := hw i'; simp only [s]; positivity
    calc _ ≤ ∑ i ∈ I, ∑ i' ∈ I.erase i, 50 * K * (w i * s i) * (w i' * s i') :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi =>
            (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i' hi' =>
              hoff i hi i' (Finset.mem_of_mem_erase hi') (Finset.ne_of_mem_erase hi').symm))
      _ ≤ ∑ i ∈ I, ∑ i' ∈ I, 50 * K * (w i * s i) * (w i' * s i') :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            fun i' _ _ => hnn i i'
      _ = 50 * K * (∑ i ∈ I, w i * s i) ^ 2 := by
          rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i' _ => by ring
      _ ≤ 50 * K * ((∑ i ∈ I, w i ^ 2) * ∑ i ∈ I, s i ^ 2) :=
          mul_le_mul_of_nonneg_left (Finset.sum_mul_sq_le_sq_mul_sq I w s) (by positivity)
      _ ≤ 50 * K * (2 * ∑ i ∈ I, X i) := by
          have hs2 : ∑ i ∈ I, s i ^ 2 = ∑ i ∈ I, X i :=
            Finset.sum_congr rfl fun i _ => Real.sq_sqrt (hX i)
          rw [hs2]
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_
            (Finset.sum_nonneg fun i _ => hX i)) (by positivity)
          exact h.sum_weight_sq_le
      _ = 100 * K * ∑ i ∈ I, X i := by ring
  rw [criticalTruncatedPrimeEnergy_biUnion hV hd, hsplit, hE]
  refine (abs_add_le _ _).trans ?_
  unfold lacunaryPrimeConstant
  linarith

/-! ### Positivity across lacunary blocks -/

/-- Channel constant `|Ω(0)| U + 288 a_R a_E + 2 (C_T + 100 K)` of lacunary unions. -/
def lacunaryChannelConstant : ℝ :=
  |EF.gammaBracket 0| * criticalCollarMassUpper +
    288 * criticalTruncatedReadoutConstant * criticalTruncatedEndpointConstant +
    2 * lacunaryPrimeConstant

theorem neg_le_criticalTruncatedChannels_of_lacunary {J : ℕ} {M : ℕ → ℕ} {S : ℕ → Finset ℕ}
    (h : IsLacunaryBlockFamily J M S) (b : ℕ → ℝ) {V : ℝ} (hV : 1 ≤ V) :
    -(lacunaryChannelConstant * ∑ n ∈ (Finset.range J).biUnion S, b n ^ 2) ≤
      EF.gammaBracket 0 * sourceAutocorrelation (criticalTruncatedSource V ((Finset.range J).biUnion S) b) 0 +
        2 * (criticalTruncatedPolarReadout V ((Finset.range J).biUnion S) b *
          criticalTruncatedPolarEndpoint V ((Finset.range J).biUnion S) b) -
        2 * criticalTruncatedPrimeEnergy V ((Finset.range J).biUnion S) b := by
  set T := (Finset.range J).biUnion S
  set E := ∑ n ∈ T, b n ^ 2
  have hE : 0 ≤ E := Finset.sum_nonneg fun _ _ => sq_nonneg _
  set Tr := ∑ n ∈ T, |b n| / ((n + 1 : ℕ) : ℝ)
  have hTr : 0 ≤ Tr := Finset.sum_nonneg fun n _ => by positivity
  have hV0 : 0 < V := by linarith
  have hM : 2 ≤ M 0 := by have := h.1; omega
  have hM0 : (2 : ℝ) ≤ M 0 := by exact_mod_cast hM
  set ac := sourceAutocorrelation (criticalTruncatedSource V T b) 0
  have hac0 : 0 ≤ ac := by
    unfold ac sourceAutocorrelation
    exact integral_nonneg fun y => by simp only [sub_zero]; exact mul_self_nonneg _
  have hac := sourceAutocorrelation_criticalTruncatedSource_zero_le V T b
  have hΩ : -(|EF.gammaBracket 0| * (criticalCollarMassUpper * E)) ≤ EF.gammaBracket 0 * ac := by
    have h1 : -(|EF.gammaBracket 0| * ac) ≤ EF.gammaBracket 0 * ac := by
      have := neg_abs_le (EF.gammaBracket 0 * ac)
      rwa [abs_mul, abs_of_nonneg hac0] at this
    have h2 : |EF.gammaBracket 0| * ac ≤ |EF.gammaBracket 0| * (criticalCollarMassUpper * E) :=
      mul_le_mul_of_nonneg_left hac (abs_nonneg _)
    linarith
  have hT2 := sq_sum_abs_div_succ_le T b hM fun n hn => h.lower hn
  set a := criticalTruncatedReadoutConstant
  set c := criticalTruncatedEndpointConstant
  have ha : 0 ≤ a := by
    unfold a criticalTruncatedReadoutConstant
    have : 0 ≤ ∫ v in Ioi 1, |deriv criticalCollarWeight v| := integral_nonneg fun _ => abs_nonneg _
    have := smoothTransitionSlope_nonneg
    have : 0 ≤ criticalCollarMass := integral_nonneg fun _ => abs_nonneg _
    positivity
  have hc : 0 ≤ c := by
    unfold c criticalTruncatedEndpointConstant
    have : 0 ≤ ∫ v in Ioi 1, |deriv criticalCollarEndpointWeight v| :=
      integral_nonneg fun _ => abs_nonneg _
    have := smoothTransitionSlope_nonneg
    positivity
  have hpol : |criticalTruncatedPolarReadout V T b * criticalTruncatedPolarEndpoint V T b| ≤
      144 * a * c * E := by
    rw [abs_mul]
    have h1 := abs_criticalTruncatedPolarReadout_le hV0 T b
    have h2 := abs_criticalTruncatedPolarEndpoint_le hV T b
    have h12 := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    have hTE : Tr ^ 2 ≤ E := hT2.trans (by
      have : 2 / (M 0 : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hM0
      nlinarith)
    calc _ ≤ a * (12 * Tr) * (c * (12 * Tr)) := h12
      _ = 144 * a * c * Tr ^ 2 := by ring
      _ ≤ 144 * a * c * E := mul_le_mul_of_nonneg_left hTE (by positivity)
  have hP := abs_criticalTruncatedPrimeEnergy_le_of_lacunary hV0 h b
  have hP' := (abs_le.mp hP).2
  have hpol' := (abs_le.mp hpol).1
  unfold lacunaryChannelConstant
  nlinarith

/-- **Complete energy on lacunary unions of blocks.** For every lacunary block family, every
truncation `V ≥ V₀` and every real pattern on the union of its blocks,
`E(g^V) ≥ (s_T (log M_0 - c_T) - K_lac) ∑ b_n²`, uniformly in `V` and in the number of blocks. -/
theorem criticalTruncatedCompleteEnergy_ge_of_lacunary {J : ℕ} {M : ℕ → ℕ} {S : ℕ → Finset ℕ}
    (h : IsLacunaryBlockFamily J M S) (b : ℕ → ℝ) {V : ℝ} (hV : criticalTruncationThreshold ≤ V) :
    (((criticalTruncatedArchLogSlope * (Real.log (M 0) - criticalTruncatedArchLogOffset) -
        lacunaryChannelConstant) * ∑ n ∈ (Finset.range J).biUnion S, b n ^ 2 : ℝ) : EReal) ≤
      criticalTruncatedCompleteEnergy V ((Finset.range J).biUnion S) b := by
  set T := (Finset.range J).biUnion S
  set E := ∑ n ∈ T, b n ^ 2
  have hV1 : 1 ≤ V := by
    have := (le_max_left _ _).trans hV
    linarith [factorialWindowLength_pos]
  have hM : 2 ≤ M 0 := by have := h.1; omega
  set X := criticalTruncatedArchLogSlope * (Real.log (M 0) - criticalTruncatedArchLogOffset) * E
  have hlev : (X : EReal) ≤ (sourceLevyEnergy (criticalTruncatedSource V T b) : EReal) := by
    have h1 := ofReal_le_criticalTruncatedLevyEnergy T b hM (fun n hn => h.lower hn) hV
    have h2 := EReal.coe_ennreal_le_coe_ennreal_iff.mpr h1
    rw [EReal.coe_ennreal_ofReal] at h2
    exact le_trans (EReal.coe_le_coe_iff.mpr (le_max_left _ _)) h2
  have hch := neg_le_criticalTruncatedChannels_of_lacunary h b hV1
  unfold criticalTruncatedCompleteEnergy
  rw [show (criticalTruncatedArchLogSlope * (Real.log (M 0) - criticalTruncatedArchLogOffset) -
      lacunaryChannelConstant) * E = X + -(lacunaryChannelConstant * E) by ring, EReal.coe_add]
  exact add_le_add hlev (EReal.coe_le_coe_iff.mpr hch)

/-- **Positivity across lacunary blocks.** There is a scale `M₀` such that for every lacunary block
family with base scale `M_0 ≥ M₀`, with any number of blocks, every truncation `V ≥ V₀` and every
nonzero real pattern on the union of the blocks, the complete energy of the compact source `g^V`
is strictly positive. -/
theorem exists_criticalTruncatedCompleteEnergy_pos_of_lacunary :
    ∃ M₀ : ℕ, ∀ (J : ℕ) (M : ℕ → ℕ) (S : ℕ → Finset ℕ), IsLacunaryBlockFamily J M S → M₀ ≤ M 0 →
      ∀ V : ℝ, criticalTruncationThreshold ≤ V → ∀ b : ℕ → ℝ,
        (∃ n ∈ (Finset.range J).biUnion S, b n ≠ 0) →
          0 < criticalTruncatedCompleteEnergy V ((Finset.range J).biUnion S) b := by
  have hs := criticalTruncatedArchLogSlope_pos
  have hlog : Tendsto (fun M : ℕ => Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp (hlog.eventually_gt_atTop
    (criticalTruncatedArchLogOffset + lacunaryChannelConstant / criticalTruncatedArchLogSlope))
  refine ⟨M₀, fun J M S h hM V hV b hb => ?_⟩
  have hlogM := hM₀ (M 0) hM
  obtain ⟨j, hj, hbj⟩ := hb
  have hE : 0 < ∑ n ∈ (Finset.range J).biUnion S, b n ^ 2 :=
    lt_of_lt_of_le (by positivity) (Finset.single_le_sum (fun i _ => sq_nonneg (b i)) hj)
  have hgap : 0 < criticalTruncatedArchLogSlope * (Real.log (M 0) - criticalTruncatedArchLogOffset) -
      lacunaryChannelConstant := by
    have h1 : lacunaryChannelConstant / criticalTruncatedArchLogSlope <
        Real.log (M 0) - criticalTruncatedArchLogOffset := by linarith
    have h2 := (div_lt_iff₀ hs).mp h1
    linarith
  exact lt_of_lt_of_le (EReal.coe_pos.mpr (mul_pos hgap hE))
    (criticalTruncatedCompleteEnergy_ge_of_lacunary h b hV)

/-- **Weil positivity of `ζ` across lacunary blocks.** There is `M₀` such that for every lacunary
block family with base scale at least `M₀` and any number of blocks, every truncation `V ≥ V₀` and
every nonzero real pattern, the full Weil functional of `ζ` is strictly positive on the compact
test `g^V ⋆ g̃^V`. The patterns may span scales from `M_0` to `M_0^{8^{J-1}}`. -/
theorem exists_compactFullWeilEnergy_pos_of_lacunary :
    ∃ M₀ : ℕ, ∀ (J : ℕ) (M : ℕ → ℕ) (S : ℕ → Finset ℕ), IsLacunaryBlockFamily J M S → M₀ ≤ M 0 →
      ∀ V : ℝ, ∀ hV : 0 < V, criticalTruncationThreshold ≤ V → ∀ b : ℕ → ℝ,
        (∃ n ∈ (Finset.range J).biUnion S, b n ≠ 0) →
          0 < compactFullWeilEnergy (criticalTruncatedTest hV ((Finset.range J).biUnion S) b) := by
  obtain ⟨M₀, hM₀⟩ := exists_criticalTruncatedCompleteEnergy_pos_of_lacunary
  refine ⟨M₀, fun J M S h hM V hV hVt b hb => ?_⟩
  have := hM₀ J M S h hM V hVt b hb
  rw [← compactFullWeilEnergy_criticalTruncatedTest hV] at this
  exact EReal.coe_pos.mp this

end GaloisForLFunctions.ArithmeticPositivityTheory
