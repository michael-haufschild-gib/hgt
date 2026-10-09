import GaloisForLFunctions.RHTower.WeilLogShiftFiniteGramCostGrowth
import GaloisForLFunctions.RHTower.WeilLogShiftFactorialCoefficientCriterion

/-!
# Matching quadratic Gram-certificate cost for singleton supports

Every singleton arithmetic support has a normalized certificate with exactly
two tests and cost bounded above and below by universal multiples of n².
At large indices an explicit two-point construction supplies the upper bound;
finite certificate existence absorbs the remaining indices.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

open WeilExcess

private def singletonWeilUnit (k : ℕ) : ({k} : Finset ℕ) → ℝ :=
  Pi.single ⟨k, by simp⟩ 1

private theorem singletonWeilUnit_norm (k : ℕ) : ‖singletonWeilUnit k‖ = 1 := by
  simp only [singletonWeilUnit, Pi.norm_single, norm_one]

private theorem singletonWeilUnit_ne_zero (k : ℕ) : singletonWeilUnit k ≠ 0 := by
  intro h
  have hn := singletonWeilUnit_norm k
  simp only [h, norm_zero, zero_ne_one] at hn

private theorem singletonWeil_eq_smul (k : ℕ) (c : ({k} : Finset ℕ) → ℝ) :
    c = c ⟨k, by simp⟩ • singletonWeilUnit k := by
  funext j
  have hj : j = (⟨k, by simp⟩ : ({k} : Finset ℕ)) :=
    Subtype.ext (Finset.mem_singleton.mp j.property)
  rw [hj]
  simp [singletonWeilUnit]

private theorem singletonWeilUnit_potential (k : ℕ) (y : ℝ) :
    finiteWeilPotential {k} (singletonWeilUnit k) y = pairedLogKernel y (k + 2) := by
  classical
  simp only [finiteWeilPotential, singletonWeilUnit]
  rw [Finset.sum_eq_single (⟨k, by simp⟩ : ({k} : Finset ℕ))]
  · simp
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, zero_mul]
  · intro h
    exact (h (Finset.mem_univ _)).elim

private theorem singletonWeil_pair_certificate (k : ℕ) (wp wm : FiniteWeilGramTest)
    (hp : finiteWeilGramForm {k} wp (singletonWeilUnit k) < -1)
    (hm : 1 < finiteWeilGramForm {k} wm (singletonWeilUnit k)) :
    FiniteWeilGramNormCertificate {k} {wp, wm} := by
  classical
  intro c hc
  let t := c ⟨k, by simp⟩
  have hrep : c = t • singletonWeilUnit k := singletonWeil_eq_smul k c
  have ht : t ≠ 0 := by
    intro h
    apply hc
    rw [hrep, h, zero_smul]
  have hnorm : ‖c‖ = |t| := by
    rw [hrep, norm_smul, Real.norm_eq_abs, singletonWeilUnit_norm, mul_one]
  have happ (w : FiniteWeilGramTest) :
      finiteWeilGramForm {k} w c = t * finiteWeilGramForm {k} w (singletonWeilUnit k) := by
    rw [hrep, map_smul, smul_eq_mul]
  rcases lt_or_gt_of_ne ht with hneg | hpos
  · refine ⟨wm, by simp, ?_⟩
    rw [happ, hnorm, abs_of_neg hneg]
    simpa only [mul_one, neg_neg] using mul_lt_mul_of_neg_left hm hneg
  · refine ⟨wp, by simp, ?_⟩
    rw [happ, hnorm, abs_of_pos hpos]
    simpa only [mul_neg, mul_one] using mul_lt_mul_of_pos_left hp hpos

/-- In one arithmetic coefficient dimension, two opposite-sign witnesses
already form a complete normalized certificate. -/
theorem exists_two_test_singletonWeil_certificate (k : ℕ) :
    ∃ tests : Finset FiniteWeilGramTest, tests.card = 2 ∧
      FiniteWeilGramNormCertificate {k} tests := by
  classical
  obtain ⟨tests, htests⟩ := exists_finiteWeilGram_norm_certificate {k}
  obtain ⟨wp, _, hp⟩ := htests (singletonWeilUnit k) (singletonWeilUnit_ne_zero k)
  obtain ⟨wm, _, hm⟩ := htests (-singletonWeilUnit k) (neg_ne_zero.mpr (singletonWeilUnit_ne_zero k))
  rw [singletonWeilUnit_norm] at hp
  rw [map_neg, norm_neg, singletonWeilUnit_norm] at hm
  have hm' : 1 < finiteWeilGramForm {k} wm (singletonWeilUnit k) := by linarith
  have hne : wp ≠ wm := by
    intro h
    rw [h] at hp
    linarith
  exact ⟨{wp, wm}, Finset.card_pair hne, singletonWeil_pair_certificate k wp wm hp hm'⟩

private def singletonTwoPointTest (k : ℕ) (ε : ℝ) (a : NNReal) : FiniteWeilGramTest :=
  ⟨2, ![0, Real.log (k + 2 : ℕ)], ![1, ε], a⟩

private theorem singletonTwoPointTest_apply (k : ℕ) (ε : ℝ) (a : NNReal) :
    finiteWeilGramForm {k} (singletonTwoPointTest k ε a) (singletonWeilUnit k) =
      -(a : ℝ) * ((1 + ε ^ 2) * pairedLogKernel 0 (k + 2) +
        2 * ε * pairedLogKernel (Real.log (k + 2 : ℕ)) (k + 2)) := by
  rw [singletonTwoPointTest, finiteWeilGramForm_apply]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    singletonWeilUnit_potential, sub_self, sub_zero, zero_sub, pairedLogKernel_neg]
  ring

private theorem singletonTwoPointTest_cost (B : ℝ) (k : ℕ) (a : NNReal)
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    finiteWeilGramTailCost B (singletonTwoPointTest k ε a) =
      (a : ℝ) * B * (2 + 2 * (((k + 2 : ℕ) : ℝ) ^ 2)) := by
  have hlog := Real.log_natCast_nonneg (k + 2)
  have hexp : Real.exp (2 * Real.log (k + 2 : ℕ)) = ((k + 2 : ℕ) : ℝ) ^ 2 := by
    rw [show 2 * Real.log (k + 2 : ℕ) = Real.log (((k + 2 : ℕ) : ℝ) ^ 2) by
      rw [Real.log_pow]; push_cast; ring]
    exact Real.exp_log (by positivity)
  dsimp only [singletonTwoPointTest, finiteWeilGramTailCost]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  have habs : |ε| = 1 := by rcases hε with rfl | rfl <;> norm_num
  simp only [abs_mul, abs_one, habs, one_mul, mul_one, sub_self, sub_zero,
    zero_sub, abs_neg, abs_zero, mul_zero, Real.exp_zero, abs_of_nonneg hlog, hexp]
  ring

private theorem exists_eventual_singletonWeil_cost_bound (B : ℝ) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      ∃ tests : Finset FiniteWeilGramTest, tests.card = 2 ∧
        FiniteWeilGramNormCertificate {k} tests ∧
        (∑ w ∈ tests, finiteWeilGramTailCost B w) ≤ C * (((k + 2 : ℕ) : ℝ) ^ 2) := by
  classical
  let K := riemannAutocorr 0
  have hK : 0 < K := riemannAutocorr_pos 0
  let a : NNReal := ⟨2 / K, (div_pos (by norm_num) hK).le⟩
  have ha : 0 < (a : ℝ) := div_pos (by norm_num) hK
  have haK : (a : ℝ) * K = 2 := div_mul_cancel₀ _ hK.ne'
  obtain ⟨D, _, hD⟩ := exists_pairedLogKernel_inverseSquare_envelope
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * D / K)
  refine ⟨8 * (a : ℝ) * B, by positivity, N, ?_⟩
  intro k hk
  let q : ℝ := ((k + 2 : ℕ) : ℝ) ^ 2
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hNk : (N : ℝ) ≤ k := by exact_mod_cast hk
  have hq : 0 < q := by dsimp only [q]; positivity
  have hq1 : 1 ≤ q := by dsimp only [q]; push_cast; nlinarith
  have hNq : (N : ℝ) ≤ q := by dsimp only [q]; push_cast; nlinarith
  have hthreshold : 2 * D < K * q := by
    have h := (div_lt_iff₀ hK).mp (hN.trans_le hNq)
    nlinarith
  have hsmall : pairedLogKernel 0 (k + 2) ≤ K / 2 := by
    have h := hD 0 (k + 2) (by omega)
    simp only [abs_zero, mul_zero, Real.exp_zero, mul_one] at h
    calc
      _ ≤ D * q⁻¹ := h
      _ ≤ K / 2 := by
        rw [← div_eq_mul_inv, div_le_iff₀ hq]
        nlinarith
  have hlarge : K ≤ pairedLogKernel (Real.log (k + 2 : ℕ)) (k + 2) :=
    riemannAutocorr_zero_le_pairedLogKernel_log (k + 2)
  have hzero : 0 ≤ pairedLogKernel 0 (k + 2) := (pairedLogKernel_pos 0 (k + 2)).le
  let wp := singletonTwoPointTest k 1 a
  let wm := singletonTwoPointTest k (-1) a
  have hp : finiteWeilGramForm {k} wp (singletonWeilUnit k) < -1 := by
    have hbase : 2 * K ≤ 2 * pairedLogKernel 0 (k + 2) +
        2 * pairedLogKernel (Real.log (k + 2 : ℕ)) (k + 2) := by linarith
    have h := mul_le_mul_of_nonneg_left hbase a.property
    dsimp only [wp]
    rw [singletonTwoPointTest_apply]
    norm_num only
    nlinarith
  have hm : 1 < finiteWeilGramForm {k} wm (singletonWeilUnit k) := by
    have hbase : K ≤ 2 * (pairedLogKernel (Real.log (k + 2 : ℕ)) (k + 2) -
        pairedLogKernel 0 (k + 2)) := by linarith
    have h := mul_le_mul_of_nonneg_left hbase a.property
    dsimp only [wm]
    rw [singletonTwoPointTest_apply]
    norm_num only
    nlinarith
  have hne : wp ≠ wm := by
    intro h
    rw [h] at hp
    linarith
  refine ⟨{wp, wm}, Finset.card_pair hne,
    singletonWeil_pair_certificate k wp wm hp hm, ?_⟩
  rw [Finset.sum_pair hne]
  have hcostp := singletonTwoPointTest_cost B k a 1 (Or.inl rfl)
  have hcostm := singletonTwoPointTest_cost B k a (-1) (Or.inr rfl)
  change finiteWeilGramTailCost B wp + finiteWeilGramTailCost B wm ≤ (8 * (a : ℝ) * B) * q
  calc
    _ = (4 * (a : ℝ) * B) * (1 + q) := by
      dsimp only [wp, wm]
      rw [hcostp, hcostm]
      dsimp only [q]
      ring
    _ ≤ (4 * (a : ℝ) * B) * (2 * q) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by ring

private theorem finiteWeilGramTailCost_nonneg {B : ℝ} (hB : 0 ≤ B)
    (w : FiniteWeilGramTest) : 0 ≤ finiteWeilGramTailCost B w := by
  rcases w with ⟨N, x, u, a⟩
  dsimp only [finiteWeilGramTailCost]
  positivity

/-- Every normalized singleton Gram certificate has a quadratic cost lower bound,
and exactly two tests attain a matching upper bound at every arithmetic index.
The multiplicative constants are not asserted to be optimal. -/
theorem exists_singletonWeil_quadratic_cost_certificate :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧
      (∀ (k : ℕ) (tests : Finset FiniteWeilGramTest),
        FiniteWeilGramNormCertificate {k} tests →
        2 * (((k + 2 : ℕ) : ℝ) ^ 2) < ∑ w ∈ tests, finiteWeilGramTailCost B w) ∧
      ∀ k : ℕ,
      ∃ tests : Finset FiniteWeilGramTest, tests.card = 2 ∧
        FiniteWeilGramNormCertificate {k} tests ∧
        (∑ w ∈ tests, finiteWeilGramTailCost B w) ≤ C * (((k + 2 : ℕ) : ℝ) ^ 2) := by
  classical
  obtain ⟨B, hB, _, hlower, _⟩ := exists_finiteWeilGram_cost_bounds
  obtain ⟨C₀, hC₀, N, hlarge⟩ := exists_eventual_singletonWeil_cost_bound B hB
  choose exceptional hcard hcert using exists_two_test_singletonWeil_certificate
  let D (k : ℕ) := ∑ w ∈ exceptional k, finiteWeilGramTailCost B w
  have hD (k : ℕ) : 0 ≤ D k :=
    Finset.sum_nonneg fun w _ => finiteWeilGramTailCost_nonneg hB.le w
  let C := C₀ + (∑ k ∈ Finset.range N, D k) + 1
  have hsum : 0 ≤ ∑ k ∈ Finset.range N, D k := Finset.sum_nonneg fun k _ => hD k
  have hC : 0 < C := by dsimp only [C]; linarith
  have hC₀C : C₀ ≤ C := by dsimp only [C]; linarith
  refine ⟨B, C, hB, hC, ?_, ?_⟩
  · intro k tests ht
    exact hlower {k} tests ht ⟨k, by simp⟩
  intro k
  by_cases hk : k < N
  · have hDk : D k ≤ C := by
      have h := Finset.single_le_sum (fun j _ => hD j) (Finset.mem_range.mpr hk)
      dsimp only [C]
      linarith
    have hq : 1 ≤ (((k + 2 : ℕ) : ℝ) ^ 2) := by
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) k]
    refine ⟨exceptional k, hcard k, hcert k, ?_⟩
    change D k ≤ C * _
    exact hDk.trans (by nlinarith)
  · obtain ⟨tests, hc, ht, hu⟩ := hlarge k (by omega)
    exact ⟨tests, hc, ht, hu.trans (mul_le_mul_of_nonneg_right hC₀C (sq_nonneg _))⟩

end RHTower
