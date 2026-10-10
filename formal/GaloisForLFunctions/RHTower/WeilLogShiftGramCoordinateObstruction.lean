import GaloisForLFunctions.RHTower.WeilLogShiftExponentialClusterCost
import GaloisForLFunctions.RHTower.WeilLogShiftGramImage
import GaloisForLFunctions.RHTower.WeilLogShiftGramLeakageAlgebra
import Mathlib.Data.Finset.Max

/-! Small cluster sensitivity makes at least one exact coordinate spike expensive,
uniformly over all actual test nodes, amplitudes, and outer scales. -/

open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable section
namespace RHTower

theorem finiteWeilGramForm_tailCost_sensitivity {s : Finset ℕ} {c : s → ℝ} {B q : ℝ}
    (hq : 0 < q)
    (hc : ∀ y, |finiteWeilPotential s c y| ≤ B * Real.exp (2 * |y|) * q⁻¹)
    (w : FiniteWeilGramTest) :
    |finiteWeilGramForm s w c| * q ≤ finiteWeilGramTailCost B w := by
  rcases w with ⟨N, x, u, a⟩
  have ha : |(a : ℝ)| = (a : ℝ) := abs_of_nonneg (NNReal.coe_nonneg a)
  have hsum : |∑ i, ∑ j, u i * u j * finiteWeilPotential s c (x j - x i)| ≤
      (∑ i, ∑ j, |u i * u j| * (B * Real.exp (2 * |x j - x i|))) * q⁻¹ := by
    calc
      _ ≤ ∑ i, |∑ j, u i * u j * finiteWeilPotential s c (x j - x i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, (|u i * u j| * (B * Real.exp (2 * |x j - x i|))) * q⁻¹ := by
        apply Finset.sum_le_sum
        intro i _
        calc
          _ ≤ ∑ j, |u i * u j * finiteWeilPotential s c (x j - x i)| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ _ := by
            apply Finset.sum_le_sum
            intro j _
            rw [abs_mul, mul_assoc]
            exact mul_le_mul_of_nonneg_left (hc _) (abs_nonneg _)
      _ = _ := by simp only [Finset.sum_mul]
  have hb : |finiteWeilGramForm s ⟨N, x, u, a⟩ c| ≤
      finiteWeilGramTailCost B ⟨N, x, u, a⟩ * q⁻¹ := by
    rw [finiteWeilGramForm_apply, abs_mul, abs_neg, ha]
    simpa only [finiteWeilGramTailCost, mul_assoc] using
      mul_le_mul_of_nonneg_left hsum (NNReal.coe_nonneg a)
  exact (le_div_iff₀ hq).mp (by simpa only [div_eq_mul_inv] using hb)

/-- Logarithmic coordinates centered at the first arithmetic label of a cluster. -/
def finiteWeilCenteredLog (k j : ℕ) : ℝ :=
  Real.log ((j + 2 : ℕ) : ℝ) - Real.log ((k + 2 : ℕ) : ℝ)

/-- Preserve the chosen cluster coefficients while selecting a unit coordinate. -/
theorem exists_finiteWeilGram_cluster_dual_of_coefficients (r : ℕ)
    (s : Finset ℕ) (k : ℕ) (hmem : ∀ i : Fin (r + 2), k + (i : ℕ) ∈ s)
    {B q : ℝ} (hq : 0 < q)
    (c : Fin (r + 2) → ℝ) (hc : ‖c‖ = 1) (hpot : ∀ y : ℝ,
      |∑ i, c i * pairedLogKernel y ((k + 2) + (i : ℕ))| ≤
        B * Real.exp (2 * |y|) * q⁻¹) :
    let e : Fin (r + 2) → s := fun i => ⟨k + (i : ℕ), hmem i⟩
    let d : s → ℝ := Function.extend e c (fun _ => 0)
    ∃ i : s, ‖d‖ = 1 ∧ |d i| = 1 ∧
      (∑ j ∈ Finset.univ.erase i, |d j|) ≤ ((r + 1 : ℕ) : ℝ) ∧
      ∀ w : FiniteWeilGramTest,
        |finiteWeilGramForm s w d| * q ≤ finiteWeilGramTailCost B w := by
  obtain ⟨j, _, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun j : Fin (r + 2) => |c j|) Finset.univ_nonempty
  have htop : ‖c‖ ≤ |c j| := (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr fun i => by
    simpa only [Real.norm_eq_abs] using hmax i (Finset.mem_univ i)
  have hcj : |c j| = 1 := le_antisymm
    (by simpa only [Real.norm_eq_abs, hc] using norm_le_pi_norm c j) (by simpa only [hc] using htop)
  let e : Fin (r + 2) → s := fun i => ⟨k + (i : ℕ), hmem i⟩
  have he : Function.Injective e := by
    intro i j hij
    have hv := congrArg Subtype.val hij
    apply Fin.ext
    dsimp [e] at hv
    omega
  let d : s → ℝ := Function.extend e c (fun _ => 0)
  have hpotential (y : ℝ) : finiteWeilPotential s d y =
      ∑ i, c i * pairedLogKernel y ((k + 2) + (i : ℕ)) := by
    unfold finiteWeilPotential
    symm
    apply Fintype.sum_of_injective e he
    · intro i hi
      dsimp [d]
      rw [Function.extend_apply' c (fun _ => 0) i hi, zero_mul]
    · intro i
      dsimp [d]
      rw [he.extend_apply]
      congr 2
      dsimp [e]
      omega
  have hd : ‖d‖ = 1 := (finiteWeil_extend_norm e he c).trans hc
  have hdj : |d (e j)| = 1 := by dsimp [d]; rw [he.extend_apply, hcj]
  have htotal : (∑ i, |d i|) ≤ ((r + 2 : ℕ) : ℝ) := by
    rw [finiteWeil_extend_abs_sum e he c]
    calc
      (∑ i, |c i|) ≤ ∑ _ : Fin (r + 2), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [Real.norm_eq_abs, hc] using norm_le_pi_norm c i
      _ = _ := by simp
  have hoff : (∑ i ∈ Finset.univ.erase (e j), |d i|) ≤ ((r + 1 : ℕ) : ℝ) := by
    have hs := Finset.sum_erase_add Finset.univ (fun i => |d i|) (Finset.mem_univ (e j))
    rw [hdj] at hs
    push_cast at htotal ⊢
    linarith only [hs, htotal]
  refine ⟨e j, hd, hdj, hoff, ?_⟩
  exact fun w => finiteWeilGramForm_tailCost_sensitivity hq
    (fun y => by rw [hpotential]; exact hpot y) w

/-- A cluster supplies a unit dual vector with bounded weight away from its largest coordinate. -/
theorem exists_finiteWeilGram_cluster_dual_witness (r : ℕ)
    (s : Finset ℕ) (k : ℕ) (hmem : ∀ i : Fin (r + 2), k + (i : ℕ) ∈ s)
    {B q : ℝ} (hq : 0 < q)
    (hbound : ∃ c : Fin (r + 2) → ℝ, ‖c‖ = 1 ∧ ∀ y : ℝ,
      |∑ i, c i * pairedLogKernel y ((k + 2) + (i : ℕ))| ≤
        B * Real.exp (2 * |y|) * q⁻¹) :
    ∃ i : s, ∃ d : s → ℝ, ‖d‖ = 1 ∧ |d i| = 1 ∧
      (∑ j ∈ Finset.univ.erase i, |d j|) ≤ ((r + 1 : ℕ) : ℝ) ∧
      ∀ w : FiniteWeilGramTest,
        |finiteWeilGramForm s w d| * q ≤ finiteWeilGramTailCost B w := by
  obtain ⟨c, hc, hpot⟩ := hbound
  obtain ⟨i, hd, hdi, hoff, hdual⟩ :=
    exists_finiteWeilGram_cluster_dual_of_coefficients r s k hmem hq c hc hpot
  exact ⟨i, Function.extend (fun j : Fin (r + 2) => (⟨k + (j : ℕ), hmem j⟩ : s)) c (fun _ => 0),
    hd, hdi, hoff, hdual⟩

/-- Exact cluster moments survive extension to the full coefficient support. -/
theorem exists_finiteWeilGram_cluster_moment_dual_witness (r : ℕ)
    (s : Finset ℕ) (k : ℕ) (hmem : ∀ i : Fin (r + 2), k + (i : ℕ) ∈ s)
    {B q : ℝ} (hq : 0 < q)
    (hbound : ∃ c : Fin (r + 2) → ℝ, ‖c‖ = 1 ∧
      (∀ p ≤ r, ∑ i, c i * (Real.log (((k + 2) + (i : ℕ) : ℕ) : ℝ) -
        Real.log ((k + 2 : ℕ) : ℝ)) ^ p = 0) ∧ ∀ y : ℝ,
      |∑ i, c i * pairedLogKernel y ((k + 2) + (i : ℕ))| ≤
        B * Real.exp (2 * |y|) * q⁻¹) :
    ∃ i : s, ∃ d : s → ℝ, ‖d‖ = 1 ∧ |d i| = 1 ∧
      (∑ j ∈ Finset.univ.erase i, |d j|) ≤ ((r + 1 : ℕ) : ℝ) ∧
      (∀ p ≤ r, ∑ j, d j * finiteWeilCenteredLog k j ^ p = 0) ∧
      ∀ w : FiniteWeilGramTest,
        |finiteWeilGramForm s w d| * q ≤ finiteWeilGramTailCost B w := by
  obtain ⟨c, hc, hm, hpot⟩ := hbound
  let e : Fin (r + 2) → s := fun j => ⟨k + (j : ℕ), hmem j⟩
  have he : Function.Injective e := by
    intro i j hij
    have hv := congrArg Subtype.val hij
    apply Fin.ext
    dsimp [e] at hv
    omega
  let d : s → ℝ := Function.extend e c (fun _ => 0)
  obtain ⟨i, hd, hdi, hoff, hdual⟩ :=
    exists_finiteWeilGram_cluster_dual_of_coefficients r s k hmem hq c hc hpot
  refine ⟨i, d, hd, hdi, hoff, ?_, hdual⟩
  intro p hp
  change (∑ j, Function.extend e c (fun _ => 0) j * finiteWeilCenteredLog k j ^ p) = 0
  rw [finiteWeil_extend_pairing e he c]
  have heval (j : Fin (r + 2)) : finiteWeilCenteredLog k (e j) =
      Real.log (((k + 2) + (j : ℕ) : ℕ) : ℝ) - Real.log ((k + 2 : ℕ) : ℝ) := by
    dsimp [finiteWeilCenteredLog, e]
    rw [show k + (j : ℕ) + 2 = k + 2 + (j : ℕ) by omega]
  simpa only [heval] using hm p hp

/-- The full vector must be a spike: uncontrolled other coefficients do not suffice. -/
theorem exists_finiteWeilGram_cluster_coordinate_obstruction (r : ℕ)
    (s : Finset ℕ) (k : ℕ) (hmem : ∀ i : Fin (r + 2), k + (i : ℕ) ∈ s)
    {B q : ℝ} (hq : 0 < q)
    (hbound : ∃ c : Fin (r + 2) → ℝ, ‖c‖ = 1 ∧ ∀ y : ℝ,
      |∑ i, c i * pairedLogKernel y ((k + 2) + (i : ℕ))| ≤
        B * Real.exp (2 * |y|) * q⁻¹) :
    ∃ i : s, ∀ w : FiniteWeilGramTest,
      finiteWeilGramCoefficientVector s w = Pi.single i 1 →
        q ≤ finiteWeilGramTailCost B w := by
  obtain ⟨i, d, _, hdi, _, hdual⟩ :=
    exists_finiteWeilGram_cluster_dual_witness r s k hmem hq hbound
  refine ⟨i, fun w hw => ?_⟩
  have hform : finiteWeilGramForm s w d = d i := by
    rw [finiteWeilGramCoefficientVector_pairing, hw]
    simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  simpa only [hform, hdi, one_mul] using hdual w

/-- At every large cutoff, a dual vector detects response with exponential sensitivity. -/
theorem exists_finiteWeilGram_exponential_moment_dual_witness :
    ∃ B : ℝ, 0 < B ∧ ∃ K : ℕ, 2 ≤ K ∧ ∀ N : ℕ, 2 * K ≤ N →
      ∃ i : Finset.range N, ∃ d : Finset.range N → ℝ, ‖d‖ = 1 ∧ |d i| = 1 ∧
        (∑ j ∈ Finset.univ.erase i, |d j|) ≤ ((N / K : ℕ) : ℝ) - 1 ∧
        (∀ p ≤ N / K - 2, ∑ j, d j * finiteWeilCenteredLog (N - N / K) j ^ p = 0) ∧
        ∀ w : FiniteWeilGramTest,
          |finiteWeilGramForm (Finset.range N) w d| * (2 : ℝ) ^ (N / K) ≤
            B * finiteWeilGramTailCost 1 w := by
  obtain ⟨B, L, hB, hL, hbound⟩ :=
    exists_pairedLogKernel_geometric_cluster_envelope_with_moments
  obtain ⟨K, hKreal⟩ := exists_nat_gt (4 * L + 1)
  have hK2 : 2 ≤ K := by
    have h : (2 : ℝ) ≤ (K : ℝ) := by linarith
    exact_mod_cast h
  have hK : 0 < K := by omega
  refine ⟨B, hB, K, hK2, ?_⟩
  intro N hN
  let q : ℕ := N / K
  let r : ℕ := q - 2
  let k : ℕ := N - q
  have hq2 : 2 ≤ q := (Nat.le_div_iff_mul_le hK).mpr hN
  have hqN : q ≤ N := Nat.div_le_self N K
  have hrq : r + 2 = q := by dsimp [r]; omega
  have hkq : k + q = N := by dsimp [k]; omega
  have hKq : K * q ≤ N := by
    simpa only [Nat.mul_comm] using Nat.div_mul_le_self N K
  have hbudget : 4 * L * ((r + 1 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by
    have hqcast : (r : ℝ) + 2 = (q : ℝ) := by exact_mod_cast hrq
    have hkcast : (k : ℝ) + (q : ℝ) = (N : ℝ) := by exact_mod_cast hkq
    have hprod : (K : ℝ) * (q : ℝ) ≤ (N : ℝ) := by exact_mod_cast hKq
    have hm := mul_le_mul_of_nonneg_right hKreal.le (Nat.cast_nonneg (α := ℝ) q)
    push_cast
    nlinarith
  obtain ⟨i, d, hd, hdi, hoff, hm, hdual⟩ := exists_finiteWeilGram_cluster_moment_dual_witness r
    (Finset.range N) k (fun j => by
      apply Finset.mem_range.mpr
      have := j.isLt
      omega) (by positivity) (hbound r (k + 2) hbudget)
  refine ⟨i, d, hd, hdi, ?_, hm, ?_⟩
  · have hqcast : (r : ℝ) + 2 = (q : ℝ) := by exact_mod_cast hrq
    change (∑ j ∈ Finset.univ.erase i, |d j|) ≤ (q : ℝ) - 1
    push_cast at hoff
    linarith only [hoff, hqcast]
  intro w
  have hn2 : (2 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ k + 2 by omega)
  have hfactor : (4 : ℝ) ≤ (((k + 2 : ℕ) : ℝ) ^ 2) := by nlinarith
  have hpower : (2 : ℝ) ^ q ≤ (((k + 2 : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ r) := by
    calc
      (2 : ℝ) ^ q = (2 : ℝ) ^ (r + 2) := by rw [hrq]
      _ = 4 * (2 : ℝ) ^ r := by rw [pow_add]; norm_num; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hfactor (by positivity)
  have hscale : finiteWeilGramTailCost B w = B * finiteWeilGramTailCost 1 w := by
    simpa only [mul_one] using finiteWeilGramTailCost_scale B 1 w
  exact (mul_le_mul_of_nonneg_left hpower (abs_nonneg _)).trans ((hdual w).trans_eq hscale)

/-- The exponential dual estimate without exposing its exact moment equations. -/
theorem exists_finiteWeilGram_exponential_dual_witness :
    ∃ B : ℝ, 0 < B ∧ ∃ K : ℕ, 2 ≤ K ∧ ∀ N : ℕ, 2 * K ≤ N →
      ∃ i : Finset.range N, ∃ d : Finset.range N → ℝ, ‖d‖ = 1 ∧ |d i| = 1 ∧
        (∑ j ∈ Finset.univ.erase i, |d j|) ≤ ((N / K : ℕ) : ℝ) - 1 ∧
        ∀ w : FiniteWeilGramTest,
          |finiteWeilGramForm (Finset.range N) w d| * (2 : ℝ) ^ (N / K) ≤
            B * finiteWeilGramTailCost 1 w := by
  obtain ⟨B, hB, K, hK, hdual⟩ := exists_finiteWeilGram_exponential_moment_dual_witness
  refine ⟨B, hB, K, hK, fun N hN => ?_⟩
  obtain ⟨i, d, hd, hdi, hoff, _, hc⟩ := hdual N hN
  exact ⟨i, d, hd, hdi, hoff, hc⟩

/-- At every large cutoff, one coordinate spike forces exponential native cost. -/
theorem exists_finiteWeilGram_exponential_coordinate_obstruction :
    ∃ c : ℝ, 0 < c ∧ ∃ K : ℕ, 2 ≤ K ∧ ∀ N : ℕ, 2 * K ≤ N →
      ∃ i : Finset.range N, ∀ w : FiniteWeilGramTest,
        finiteWeilGramCoefficientVector (Finset.range N) w = Pi.single i 1 →
          c * (2 : ℝ) ^ (N / K) ≤ finiteWeilGramTailCost 1 w := by
  obtain ⟨B, hB, K, hK, hdual⟩ := exists_finiteWeilGram_exponential_dual_witness
  refine ⟨B⁻¹, inv_pos.mpr hB, K, hK, fun N hN => ?_⟩
  obtain ⟨i, d, _, hdi, _, hcost⟩ := hdual N hN
  refine ⟨i, fun w hw => ?_⟩
  have hform : finiteWeilGramForm (Finset.range N) w d = d i := by
    rw [finiteWeilGramCoefficientVector_pairing, hw]
    simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  have hb : (2 : ℝ) ^ (N / K) ≤ B * finiteWeilGramTailCost 1 w := by
    simpa only [hform, hdi, one_mul] using hcost w
  calc
    B⁻¹ * (2 : ℝ) ^ (N / K) ≤ B⁻¹ * (B * finiteWeilGramTailCost 1 w) :=
      mul_le_mul_of_nonneg_left hb (inv_pos.mpr hB).le
    _ = finiteWeilGramTailCost 1 w := by rw [← mul_assoc, inv_mul_cancel₀ hB.ne', one_mul]

end RHTower
