import GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow.TheExcessOfAnOverlapStepAndTheFourStepLadderToRatioThree
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.WeakenedOrTwistedContactsGiveASecondBoundStateOnWindowsOfRatioThreeAndFour
import Mathlib.NumberTheory.Chebyshev

/-!
# The floor-graph operator norm and top-octave blindness of window gluing

This module establishes the finite-matrix operator bounds and gluing obstructions of the
reweighted neutral window `windowMatrix (reweightedNeutral ω Q) R J`:

1. **Bipartite operator norm of every floor map (`abs_sum_floorGraph_le`, `sum_vonMangoldt_div_sqrt_le`)**:
   Because `b ↦ ⌊b / k⌋` assigns at most one parent to each upper block and at most `k` children
   to each lower block, weighted AM–GM gives
   `|∑_{i, j < J} σ_i σ_j floorGraph k (R + i) (R + j)| ≤ (2 Λ(k) / √k) ∑_{i < J} σ_i²` at every
   block size `R ≥ 1` and length `J`. Dyadic summation against Chebyshev's bound
   `ψ(x) ≤ (log 4 + 4) x` bounds `∑_{2 ≤ k ≤ Q} 2 Λ(k) / √k ≤ floorContactSqrtConst * √Q`.

2. **Uniform prime-free and reweighted lower bounds (`sum_reweightedNeutral_ge`,
   `hermNegIndex_reweightedNeutral_shift_eq_zero`)**:
   Combining the nonnegative Dirichlet form of the archimedean jets with `blockPotential_ge_of_ratio`
   at `Q = 1` and the floor-graph operator norm proves that raising `reweightedNeutral ω (3K + 1)`
   on `(R, (3K + 1)R]` by an `O(√K)` shift eliminates all negative squares (`hermNegIndex = 0`)
   uniformly across every block size `R ≥ 1`.

3. **Wide-overlap top-octave blindness (`reweightedNeutral_eq_of_agree_below_ratio`,
   `neutralWindow_doubling_topOctave_decomposition`)**:
   When gluing `(R, (3K + 1)R]` and `(2R, (6K + 2)R]` across `(2R, (3K + 1)R]` to form the doubled
   window `(R, (6K + 1)R]`, every floor map `k ≥ 3K + 2` vanishes identically on both half-windows,
   on the middle, and on the middle couplings, acting solely on the direct end-to-end block
   `(R, 2R] × ((3K + 1)R, (6K + 1)R]`.

4. **Gluing-indistinguishable sub-Euler countermodel and un-updated doubling jump
   (`subEulerGluingWeight`, `two_le_hermNegIndex_subEulerGluingWeight`,
   `two_le_hermNegIndex_neutralWindow_halfCutoff_of_primeSums`)**:
   For every certified cutoff `Q₀`, `subEulerGluingWeight Q₀` takes values in `{0, 1}`, satisfies
   `ω(p^r) = ω(p)` on all prime powers, agrees identically with `neutralWindow` up to `Q₀` and on
   every dyadic middle `(D, 2D]`, yet acquires at least two negative squares up to shift
   `c₀ √K_m − C₀` along `K_m = 8 · 256^m` at every block size `R ≥ 1`. Likewise, the un-updated
   glued matrix `neutralWindow (3K + 1) R (6KR)` acquires at least two negative squares up to
   `c₁ √K − C₁` (`R ≥ 6`) whenever short prime intervals near `K` carry linear harmonic mass.
-/

open Finset Matrix
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.AbsoluteGeometryOfSpecZ
open GaloisForLFunctions.MixingArithmeticOfTheFloorTrees
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow

/-! ## 1. Bipartite operator norm of a single floor map and Chebyshev `1/√k` sum -/

/-- Weighted AM–GM for a single floor-map edge: `2 |x y| ≤ x² / √k + √k y²`. -/
lemma two_mul_abs_le_div_sqrt_add_mul_sqrt {k : ℕ} (hk : 1 ≤ k) (x y : ℝ) :
    2 * (|x| * |y|) ≤ x ^ 2 / Real.sqrt k + Real.sqrt k * y ^ 2 := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hkpos
  have hsq : 0 ≤ (|x| / Real.sqrt (Real.sqrt k) - Real.sqrt (Real.sqrt k) * |y|) ^ 2 := sq_nonneg _
  have h1 : (|x| / Real.sqrt (Real.sqrt k)) ^ 2 = x ^ 2 / Real.sqrt k := by
    rw [div_pow, sq_abs, Real.sq_sqrt hsk.le]
  have h2 : (Real.sqrt (Real.sqrt k) * |y|) ^ 2 = Real.sqrt k * y ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hsk.le, sq_abs]
  have h3 : 2 * (|x| / Real.sqrt (Real.sqrt k)) * (Real.sqrt (Real.sqrt k) * |y|) = 2 * (|x| * |y|) := by
    have hs2 : Real.sqrt (Real.sqrt k) ≠ 0 := (Real.sqrt_pos.mpr hsk).ne'
    field_simp [hs2]
  nlinarith

/-- On `[R, R + J)`, for fixed lower block `R + i` (`R ≥ 1, k ≥ 2`), at most `k` indices `j < J`
satisfy `R + i < R + j` and `(R + j) / k = R + i`. -/
lemma card_children_floor_le {R J k i : ℕ} (hk : 2 ≤ k) :
    ((range J).filter (fun j => i < j ∧ (R + j) / k = R + i)).card ≤ k := by
  calc ((range J).filter (fun j => i < j ∧ (R + j) / k = R + i)).card
      ≤ (Ico ((R + i) * k) ((R + i) * k + k)).card := by
        refine Finset.card_le_card_of_injOn (fun j => R + j) (fun j hj => ?_)
          (fun j₁ _ j₂ _ h => by dsimp at h; omega)
        have hdiv := (Finset.mem_filter.mp hj).2.2
        refine Finset.mem_Ico.mpr ⟨?_, ?_⟩
        · exact (Nat.le_div_iff_mul_le (by omega : 0 < k)).mp hdiv.ge
        · have h2 := (Nat.div_lt_iff_lt_mul (by omega : 0 < k)).mp
            (show (R + j) / k < R + i + 1 by omega)
          nlinarith
    _ = k := by simp

/-- On `[R, R + J)`, for fixed upper block `R + j`, at most one index `i < J` satisfies
`(R + j) / k = R + i`. -/
lemma card_parents_floor_le_one (R J k j : ℕ) :
    ((range J).filter (fun i => i < j ∧ (R + j) / k = R + i)).card ≤ 1 := by
  refine Finset.card_le_one.mpr fun i₁ hi₁ i₂ hi₂ => ?_
  have h1 := (Finset.mem_filter.mp hi₁).2.2
  have h2 := (Finset.mem_filter.mp hi₂).2.2
  omega

/-- **Bipartite operator-norm bound for `floorGraph k`**: on any window `(R, R + J]` (`R ≥ 1`)
and `k ≥ 2`, the quadratic form of `floorGraph k` has magnitude at most `(2 Λ(k) / √k) ∑ σ_i²`. -/
theorem abs_sum_floorGraph_le {R : ℕ} (hR : 1 ≤ R) {k : ℕ} (hk : 2 ≤ k) (J : ℕ) (σ : ℕ → ℝ) :
    |∑ i ∈ range J, ∑ j ∈ range J, σ i * σ j * floorGraph k (R + i) (R + j)| ≤
      2 * (Λ k : ℝ) / Real.sqrt k * ∑ i ∈ range J, σ i ^ 2 := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hkpos
  have hlam : 0 ≤ (Λ k : ℝ) / k := div_nonneg ArithmeticFunction.vonMangoldt_nonneg hkpos.le
  -- Off-diagonal split: `floorGraph k a a = 0` for `a ≥ 1`, `k ≥ 2`.
  have hdiag : ∀ i, floorGraph k (R + i) (R + i) = 0 := fun i =>
    floorGraph_eq_zero hk le_rfl (by omega)
  have hsymm : ∑ i ∈ range J, ∑ j ∈ range J, σ i * σ j * floorGraph k (R + i) (R + j) =
      2 * ∑ i ∈ range J, ∑ j ∈ (range J).filter (fun j => i < j ∧ (R + j) / k = R + i),
        σ i * σ j * ((Λ k : ℝ) / k) := by
    have h1 : ∀ i ∈ range J, ∑ j ∈ range J, σ i * σ j * floorGraph k (R + i) (R + j) =
        ∑ j ∈ (range J).filter (fun j => i < j ∧ (R + j) / k = R + i), σ i * σ j * ((Λ k : ℝ) / k) +
          ∑ j ∈ (range J).filter (fun j => j < i ∧ (R + i) / k = R + j), σ i * σ j * ((Λ k : ℝ) / k) := by
      intro i _
      have hterm : ∀ j ∈ range J, σ i * σ j * floorGraph k (R + i) (R + j) =
          (if i < j ∧ (R + j) / k = R + i then σ i * σ j * ((Λ k : ℝ) / k) else 0) +
            (if j < i ∧ (R + i) / k = R + j then σ i * σ j * ((Λ k : ℝ) / k) else 0) := by
        intro j _
        rcases lt_trichotomy i j with hij | rfl | hji
        · rw [floorGraph_of_le k (by omega : R + i ≤ R + j)]
          by_cases hd : (R + j) / k = R + i
          · rw [if_pos hd, if_pos ⟨hij, hd⟩, if_neg (by omega)]; ring
          · rw [if_neg hd, if_neg (fun h => hd h.2), if_neg (by omega)]; ring
        · simp only [hdiag i, lt_irrefl, false_and, ↓reduceIte, mul_zero, add_zero]
        · rw [floorGraph_comm, floorGraph_of_le k (by omega : R + j ≤ R + i)]
          by_cases hd : (R + i) / k = R + j
          · rw [if_pos hd, if_neg (by omega), if_pos ⟨hji, hd⟩]; ring
          · rw [if_neg hd, if_neg (by omega), if_neg (fun h => hd h.2)]; ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_filter, Finset.sum_filter]
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
    have hswap : ∑ i ∈ range J, ∑ j ∈ (range J).filter (fun j => j < i ∧ (R + i) / k = R + j),
        σ i * σ j * ((Λ k : ℝ) / k) =
      ∑ j ∈ range J, ∑ i ∈ (range J).filter (fun i => j < i ∧ (R + i) / k = R + j),
        σ j * σ i * ((Λ k : ℝ) / k) := by
      simp only [Finset.sum_filter]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by
        split_ifs <;> ring
    rw [hswap]
    ring
  rw [hsymm, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc 2 * |∑ i ∈ range J, ∑ j ∈ (range J).filter (fun j => i < j ∧ (R + j) / k = R + i),
          σ i * σ j * ((Λ k : ℝ) / k)|
      ≤ 2 * ∑ i ∈ range J, ∑ j ∈ (range J).filter (fun j => i < j ∧ (R + j) / k = R + i),
          |σ i * σ j * ((Λ k : ℝ) / k)| := by
        gcongr
        exact (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ = ((Λ k : ℝ) / k) * ∑ i ∈ range J,
          ∑ j ∈ (range J).filter (fun j => i < j ∧ (R + j) / k = R + i), 2 * (|σ i| * |σ j|) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [abs_mul, abs_mul, abs_of_nonneg hlam]
        ring
    _ ≤ ((Λ k : ℝ) / k) * ∑ i ∈ range J,
          ∑ j ∈ (range J).filter (fun j => i < j ∧ (R + j) / k = R + i),
            (σ i ^ 2 / Real.sqrt k + Real.sqrt k * σ j ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ hlam
        exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          two_mul_abs_le_div_sqrt_add_mul_sqrt (by omega) (σ i) (σ j)
    _ ≤ ((Λ k : ℝ) / k) * (Real.sqrt k * ∑ i ∈ range J, σ i ^ 2 +
          Real.sqrt k * ∑ j ∈ range J, σ j ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ hlam
        have hsplit : ∑ i ∈ range J,
            ∑ j ∈ (range J).filter (fun j => i < j ∧ (R + j) / k = R + i),
              (σ i ^ 2 / Real.sqrt k + Real.sqrt k * σ j ^ 2) =
          (∑ i ∈ range J, ∑ _j ∈ (range J).filter (fun j => i < j ∧ (R + j) / k = R + i),
              σ i ^ 2 / Real.sqrt k) +
            (∑ j ∈ range J, ∑ _i ∈ (range J).filter (fun i => i < j ∧ (R + j) / k = R + i),
              Real.sqrt k * σ j ^ 2) := by
          simp only [Finset.sum_add_distrib]
          congr 1
          simp only [Finset.sum_filter]
          rw [Finset.sum_comm]
        rw [hsplit]
        refine add_le_add ?_ ?_
        · calc ∑ i ∈ range J, ∑ _j ∈ (range J).filter (fun j => i < j ∧ (R + j) / k = R + i),
                σ i ^ 2 / Real.sqrt k
              ≤ ∑ i ∈ range J, (k : ℝ) * (σ i ^ 2 / Real.sqrt k) := by
                refine Finset.sum_le_sum fun i _ => ?_
                rw [Finset.sum_const, nsmul_eq_mul]
                exact mul_le_mul_of_nonneg_right
                  (by exact_mod_cast card_children_floor_le hk)
                  (div_nonneg (sq_nonneg _) hsk.le)
            _ = Real.sqrt k * ∑ i ∈ range J, σ i ^ 2 := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun i _ => ?_
                field_simp [hsk.ne']
                rw [Real.sq_sqrt hkpos.le]
                ring
        · calc ∑ j ∈ range J, ∑ _i ∈ (range J).filter (fun i => i < j ∧ (R + j) / k = R + i),
                Real.sqrt k * σ j ^ 2
              ≤ ∑ j ∈ range J, (1 : ℝ) * (Real.sqrt k * σ j ^ 2) := by
                refine Finset.sum_le_sum fun j _ => ?_
                rw [Finset.sum_const, nsmul_eq_mul]
                exact mul_le_mul_of_nonneg_right
                  (by exact_mod_cast card_parents_floor_le_one R J k j)
                  (mul_nonneg hsk.le (sq_nonneg _))
            _ = Real.sqrt k * ∑ j ∈ range J, σ j ^ 2 := by
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl fun j _ => one_mul _
    _ = 2 * (Λ k : ℝ) / Real.sqrt k * ∑ i ∈ range J, σ i ^ 2 := by
        field_simp [hkpos.ne', hsk.ne']
        rw [Real.sq_sqrt hkpos.le]
        ring

/-- Explicit constant for the Chebyshev `1/√k` sum: `8 * (2 + √2) * (log 4 + 4)`. -/
def floorContactSqrtConst : ℝ := 8 * (2 + Real.sqrt 2) * (Real.log 4 + 4)

lemma floorContactSqrtConst_pos : 0 < floorContactSqrtConst := by
  unfold floorContactSqrtConst
  positivity

/-- Geometric sum of `(√2)^r` up to `L`: `∑_{r < L} (√2)^r ≤ (2 + √2) * (√2)^L`. -/
lemma sum_sqrt_two_pow_le (L : ℕ) :
    ∑ r ∈ range L, (Real.sqrt 2) ^ r ≤ (2 + Real.sqrt 2) * (Real.sqrt 2) ^ L := by
  induction L with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, pow_zero, mul_one]
    positivity
  | succ L ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have hp : 0 ≤ (Real.sqrt 2) ^ L := pow_nonneg (Real.sqrt_nonneg 2) L
    -- `(2 + √2) * 1 + 1 = 3 + √2 = (2 + √2) * √2`? Check `(2 + √2) * (√2 - 1) = √2 * 2 - 2 + 2 - √2 = √2 > 1`!
    have hstep : (2 + Real.sqrt 2) + 1 ≤ (2 + Real.sqrt 2) * Real.sqrt 2 := by
      have hgt : (1.41 : ℝ) < Real.sqrt 2 := by
        rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1.41)]
        exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      nlinarith
    nlinarith

/-- **Chebyshev `1/√k` sum bound**: `∑_{2 ≤ k ≤ Q} 2 Λ(k) / √k ≤ floorContactSqrtConst * √Q`
for every `Q ≥ 1`. -/
theorem sum_vonMangoldt_div_sqrt_le {Q : ℕ} (hQ : 1 ≤ Q) :
    ∑ k ∈ Icc 2 Q, 2 * (Λ k : ℝ) / Real.sqrt k ≤ floorContactSqrtConst * Real.sqrt Q := by
  let L := Nat.log 2 Q + 1
  have hlt : Q < 2 ^ L := Nat.lt_pow_succ_log_self (by norm_num) Q
  -- Cover `Icc 2 Q` by the dyadic shells `Ico (2^r) (2^(r+1))` for `r ∈ range L`.
  have hcover : Icc 2 Q ⊆ (range L).biUnion (fun r => Ico (2 ^ r) (2 ^ (r + 1))) := by
    intro k hk
    rcases Finset.mem_Icc.mp hk with ⟨hk2, hkQ⟩
    refine Finset.mem_biUnion.mpr ⟨Nat.log 2 k, Finset.mem_range.mpr ?_, Finset.mem_Ico.mpr ⟨?_, ?_⟩⟩
    · exact Nat.lt_succ_of_le (Nat.log_mono_right hkQ)
    · exact Nat.pow_log_le_self 2 (by omega)
    · exact Nat.lt_pow_succ_log_self (by norm_num) k
  have hsqrt_pow2 : ∀ n : ℕ, Real.sqrt (((2 ^ n : ℕ) : ℝ)) = (Real.sqrt 2) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, pow_succ, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), ih, Nat.cast_ofNat]
  have hdisj : Set.PairwiseDisjoint (↑(range L)) (fun r : ℕ => Ico (2 ^ r) (2 ^ (r + 1))) := by
    intro r₁ _ r₂ _ hne
    change Disjoint (Ico (2 ^ r₁) (2 ^ (r₁ + 1))) (Ico (2 ^ r₂) (2 ^ (r₂ + 1)))
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    rcases Finset.mem_Ico.mp hk1 with ⟨h1a, h1b⟩
    rcases Finset.mem_Ico.mp hk2 with ⟨h2a, h2b⟩
    rcases lt_or_gt_of_ne hne with hlt' | hgt'
    · have : 2 ^ (r₁ + 1) ≤ 2 ^ r₂ := Nat.pow_le_pow_right (by norm_num) hlt'
      omega
    · have : 2 ^ (r₂ + 1) ≤ 2 ^ r₁ := Nat.pow_le_pow_right (by norm_num) hgt'
      omega
  have hnonneg : ∀ k, 0 ≤ 2 * (Λ k : ℝ) / Real.sqrt k := fun k =>
    div_nonneg (mul_nonneg zero_le_two ArithmeticFunction.vonMangoldt_nonneg) (Real.sqrt_nonneg _)
  calc ∑ k ∈ Icc 2 Q, 2 * (Λ k : ℝ) / Real.sqrt k
      ≤ ∑ k ∈ (range L).biUnion (fun r => Ico (2 ^ r) (2 ^ (r + 1))),
          2 * (Λ k : ℝ) / Real.sqrt k :=
        Finset.sum_le_sum_of_subset_of_nonneg hcover (fun k _ _ => hnonneg k)
    _ = ∑ r ∈ range L, ∑ k ∈ Ico (2 ^ r) (2 ^ (r + 1)), 2 * (Λ k : ℝ) / Real.sqrt k :=
        Finset.sum_biUnion hdisj
    _ ≤ ∑ r ∈ range L, 4 * (Real.log 4 + 4) * (Real.sqrt 2) ^ r := by
        refine Finset.sum_le_sum fun r _ => ?_
        have hs2r : Real.sqrt (((2 ^ r : ℕ) : ℝ)) = (Real.sqrt 2) ^ r := hsqrt_pow2 r
        have hshell : ∑ k ∈ Ico (2 ^ r) (2 ^ (r + 1)), 2 * (Λ k : ℝ) / Real.sqrt k ≤
            (2 / (Real.sqrt 2) ^ r) * ∑ k ∈ Ico (2 ^ r) (2 ^ (r + 1)), (Λ k : ℝ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun k hk => ?_
          have hkr : 2 ^ r ≤ k := (Finset.mem_Ico.mp hk).1
          have hsk_ge : (Real.sqrt 2) ^ r ≤ Real.sqrt k := by
            rw [← hs2r]
            exact Real.sqrt_le_sqrt (by exact_mod_cast hkr)
          have hs_pos : 0 < (Real.sqrt 2) ^ r := by positivity
          calc 2 * (Λ k : ℝ) / Real.sqrt k
              ≤ 2 * (Λ k : ℝ) / (Real.sqrt 2) ^ r :=
                div_le_div_of_nonneg_left (mul_nonneg zero_le_two ArithmeticFunction.vonMangoldt_nonneg)
                  hs_pos hsk_ge
            _ = (2 / (Real.sqrt 2) ^ r) * (Λ k : ℝ) := by ring
        have hpsi : ∑ k ∈ Ico (2 ^ r) (2 ^ (r + 1)), (Λ k : ℝ) ≤
            (Real.log 4 + 4) * (2 * (2 : ℝ) ^ r) := by
          have hsub : Ico (2 ^ r) (2 ^ (r + 1)) ⊆ Icc 0 ⌊((2 ^ (r + 1) : ℕ) : ℝ)⌋₊ := by
            intro k hk
            rw [Nat.floor_natCast]
            exact Finset.mem_Icc.mpr ⟨Nat.zero_le k, (Finset.mem_Ico.mp hk).2.le⟩
          calc ∑ k ∈ Ico (2 ^ r) (2 ^ (r + 1)), (Λ k : ℝ)
              ≤ ∑ k ∈ Icc 0 ⌊((2 ^ (r + 1) : ℕ) : ℝ)⌋₊, (Λ k : ℝ) :=
                Finset.sum_le_sum_of_subset_of_nonneg hsub
                  (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
            _ = Chebyshev.psi ((2 ^ (r + 1) : ℕ) : ℝ) := (Chebyshev.psi_eq_sum_Icc _).symm
            _ ≤ (Real.log 4 + 4) * ((2 ^ (r + 1) : ℕ) : ℝ) :=
                Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg _)
            _ = (Real.log 4 + 4) * (2 * (2 : ℝ) ^ r) := by
                push_cast; ring
        have h2eq : (2 : ℝ) ^ r = ((Real.sqrt 2) ^ r) * ((Real.sqrt 2) ^ r) := by
          rw [← mul_pow, Real.mul_self_sqrt (by norm_num)]
        have hs_pos : 0 < (Real.sqrt 2) ^ r := by positivity
        calc ∑ k ∈ Ico (2 ^ r) (2 ^ (r + 1)), 2 * (Λ k : ℝ) / Real.sqrt k
            ≤ (2 / (Real.sqrt 2) ^ r) * ((Real.log 4 + 4) * (2 * (2 : ℝ) ^ r)) :=
              hshell.trans (mul_le_mul_of_nonneg_left hpsi (by positivity))
          _ = 4 * (Real.log 4 + 4) * (Real.sqrt 2) ^ r := by
              rw [h2eq]
              field_simp [hs_pos.ne']
              ring
    _ = 4 * (Real.log 4 + 4) * ∑ r ∈ range L, (Real.sqrt 2) ^ r := by rw [← Finset.mul_sum]
    _ ≤ 4 * (Real.log 4 + 4) * ((2 + Real.sqrt 2) * (Real.sqrt 2) ^ L) := by
        gcongr
        exact sum_sqrt_two_pow_le L
    _ ≤ floorContactSqrtConst * Real.sqrt Q := by
        have hlow : 2 ^ (Nat.log 2 Q) ≤ Q := Nat.pow_log_le_self 2 (by omega)
        have hsL : (Real.sqrt 2) ^ L = Real.sqrt 2 * Real.sqrt (((2 ^ Nat.log 2 Q : ℕ) : ℝ)) := by
          dsimp [L]
          rw [pow_succ, mul_comm, hsqrt_pow2]
        have hsqQ : Real.sqrt (((2 ^ Nat.log 2 Q : ℕ) : ℝ)) ≤ Real.sqrt Q :=
          Real.sqrt_le_sqrt (by exact_mod_cast hlow)
        have hs2_lt : Real.sqrt 2 ≤ 2 := by
          rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
          exact Real.sqrt_le_sqrt (by norm_num)
        have hL_le : (Real.sqrt 2) ^ L ≤ 2 * Real.sqrt Q := by
          rw [hsL]
          exact mul_le_mul hs2_lt hsqQ (Real.sqrt_nonneg _) zero_le_two
        unfold floorContactSqrtConst
        have hc0 : 0 ≤ 4 * (Real.log 4 + 4) * (2 + Real.sqrt 2) := by
          have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
          positivity
        calc 4 * (Real.log 4 + 4) * ((2 + Real.sqrt 2) * (Real.sqrt 2) ^ L)
            = 4 * (Real.log 4 + 4) * (2 + Real.sqrt 2) * (Real.sqrt 2) ^ L := by ring
          _ ≤ 4 * (Real.log 4 + 4) * (2 + Real.sqrt 2) * (2 * Real.sqrt Q) :=
              mul_le_mul_of_nonneg_left hL_le hc0
          _ = 8 * (2 + Real.sqrt 2) * (Real.log 4 + 4) * Real.sqrt Q := by ring

/-! ## 2. Universal prime-free and reweighted quadratic-form lower bounds -/

/-- Elementary bound `log x ≤ 2 √x` for all `x > 0`. -/
lemma log_le_two_mul_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hlog : Real.log x = 2 * Real.log (Real.sqrt x) := by
    have h := Real.log_pow (Real.sqrt x) 2
    rw [Real.sq_sqrt hx.le, Nat.cast_ofNat] at h
    exact h
  linarith [Real.log_le_sub_one_of_pos hsx]

/-- Rewriting `reweightedNeutral` against the prime-free kernel `neutralBlock 1` for positive block
indices `1 ≤ a, b`. -/
theorem reweightedNeutral_eq_one_sub (ω : ℕ → ℝ) (Q : ℕ) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    reweightedNeutral ω Q a b = neutralBlock 1 a b - ∑ k ∈ Icc 2 Q, ω k * floorGraph k a b := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · rw [reweightedNeutral_of_lt ω Q hab, neutralBlock_of_lt hab, floorContact_one]
    ring
  · have h1 : ∑ k ∈ Icc 2 Q, (1 - ω k) * floorGraph k a a = 0 :=
      Finset.sum_eq_zero fun k hk => by
        rw [floorGraph_eq_zero (Finset.mem_Icc.mp hk).1 le_rfl (by omega), mul_zero]
    have h2 : ∑ k ∈ Icc 2 Q, ω k * floorGraph k a a = 0 :=
      Finset.sum_eq_zero fun k hk => by
        rw [floorGraph_eq_zero (Finset.mem_Icc.mp hk).1 le_rfl (by omega), mul_zero]
    rw [reweightedNeutral, h1, h2, add_zero, sub_zero, neutralBlock, neutralBlock,
      blockMatrix_self ha, blockMatrix_self ha]
  · have hcomm : ∑ k ∈ Icc 2 Q, ω k * floorGraph k a b = ∑ k ∈ Icc 2 Q, ω k * floorGraph k b a :=
      Finset.sum_congr rfl fun k _ => by rw [floorGraph_comm]
    rw [reweightedNeutral_comm, neutralBlock_comm, hcomm, reweightedNeutral_of_lt ω Q hba,
      neutralBlock_of_lt hba, floorContact_one]
    ring

/-- Every diagonal entry `reweightedNeutral ω Q a a` (`1 ≤ a`) is bounded above by
`log(a + 1) + 1`. -/
theorem reweightedNeutral_self_le (ω : ℕ → ℝ) (Q : ℕ) {a : ℕ} (ha : 1 ≤ a) :
    reweightedNeutral ω Q a a ≤ Real.log ((a : ℝ) + 1) + 1 := by
  have h0 : ∑ k ∈ Icc 2 Q, ω k * floorGraph k a a = 0 :=
    Finset.sum_eq_zero fun k hk => by
      rw [floorGraph_eq_zero (Finset.mem_Icc.mp hk).1 le_rfl (by omega), mul_zero]
  rw [reweightedNeutral_eq_one_sub ω Q ha ha, h0, sub_zero, neutralBlock, blockMatrix_self ha]
  have hjet : 0 ≤ blockJet a a := by
    unfold blockJet
    have h1 := (xLogXDiff_pos (n := a + a + 1) (by omega)).le
    rw [Nat.sub_self, xLogXDiff_zero]
    linarith
  have hdens : blockDensity a ≤ xLogXStep a := by
    have hγ : 0 < Real.eulerMascheroniConstant := by
      linarith [Real.one_half_lt_eulerMascheroniConstant]
    have hπ : 0 ≤ Real.log (2 * Real.pi) :=
      Real.log_nonneg (by linarith [Real.two_le_pi])
    change xLogXStep a - (Real.eulerMascheroniConstant + Real.log (2 * Real.pi)) ≤ xLogXStep a
    linarith
  linarith [xLogXStep_le a]

/-- When `ω ≥ 0`, every off-diagonal entry of `reweightedNeutral ω Q` is nonpositive. -/
theorem reweightedNeutral_nonpos_of_ne {ω : ℕ → ℝ} (hω : ∀ k, 0 ≤ ω k) (Q : ℕ) {a b : ℕ}
    (hne : a ≠ b) : reweightedNeutral ω Q a b ≤ 0 := by
  have hlt : ∀ {x y : ℕ}, x < y → reweightedNeutral ω Q x y ≤ 0 := fun {x y} hxy => by
    rw [reweightedNeutral_of_lt ω Q hxy]
    have hjet : 0 < blockJet x y := by
      unfold blockJet
      linarith [xLogXDiff_pos (n := x + y + 1) (by omega), xLogXDiff_pos (n := y - x) (by omega)]
    have hsum : 0 ≤ ∑ k ∈ Icc 2 Q, ω k * floorGraph k x y :=
      Finset.sum_nonneg fun k _ => mul_nonneg (hω k) (by
        unfold floorGraph; split_ifs
        · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k)
        · exact le_rfl)
    linarith
  rcases lt_or_gt_of_ne hne with h | h
  · exact hlt h
  · rw [reweightedNeutral_comm]; exact hlt h

/-- **Prime-free quadratic-form lower bound**: on `(R, R + J]` with `1 ≤ R`, `1 ≤ K`, and
`J ≤ 3KR`, the prime-free neutral kernel `neutralBlock 1` is bounded below by
`-(5 + 10 √K) ∑ σ_i²`. -/
theorem sum_neutralBlock_one_ge {R K J : ℕ} (hR : 1 ≤ R) (hK : 1 ≤ K) (hJ : J ≤ 3 * K * R)
    (σ : ℕ → ℝ) :
    -(5 + 10 * Real.sqrt K) * ∑ i ∈ range J, σ i ^ 2 ≤
      ∑ i ∈ range J, ∑ j ∈ range J, σ i * σ j * neutralBlock 1 (R + i) (R + j) := by
  rw [sum_sum_mul_eq_rowSum_sub_pairs σ (fun i j => neutralBlock 1 (R + i) (R + j))
    (fun i j => neutralBlock_comm 1 _ _)]
  have hpairs : ∑ i ∈ range J, ∑ j ∈ range J,
      neutralBlock 1 (R + i) (R + j) * (σ i - σ j) ^ 2 ≤ 0 := by
    refine Finset.sum_nonpos fun i _ => Finset.sum_nonpos fun j _ => ?_
    by_cases hij : i = j
    · subst hij; simp
    · exact mul_nonpos_of_nonpos_of_nonneg (neutralBlock_neg (by omega) 1).le (sq_nonneg _)
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hl1 : Real.log (3 * (K : ℝ) + 1) ≤ 4 * Real.sqrt K := by
    calc Real.log (3 * (K : ℝ) + 1)
        ≤ 2 * Real.sqrt (3 * (K : ℝ) + 1) := log_le_two_mul_sqrt (by positivity)
      _ ≤ 2 * Real.sqrt (4 * (K : ℝ)) := by gcongr; linarith
      _ = 4 * Real.sqrt K := by
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
            show Real.sqrt 4 = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq zero_le_two]]
          ring
  have hl2 : Real.log (1 + (3 * (K : ℝ) + 1)) ≤ 6 * Real.sqrt K := by
    calc Real.log (1 + (3 * (K : ℝ) + 1))
        ≤ 2 * Real.sqrt (1 + (3 * (K : ℝ) + 1)) := log_le_two_mul_sqrt (by positivity)
      _ ≤ 2 * Real.sqrt (9 * (K : ℝ)) := by gcongr; linarith
      _ = 6 * Real.sqrt K := by
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 9),
            show Real.sqrt 9 = 3 by rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
          ring
  have hrow : -(5 + 10 * Real.sqrt K) * ∑ i ∈ range J, σ i ^ 2 ≤
      ∑ i ∈ range J, σ i ^ 2 * ∑ l ∈ range J, neutralBlock 1 (R + i) (R + l) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi' : i < J := Finset.mem_range.mp hi
    have hrat : ((R + J : ℕ) : ℝ) ≤ (3 * (K : ℝ) + 1) * R := by
      exact_mod_cast (show R + J ≤ (3 * K + 1) * R by nlinarith)
    have hpot := blockPotential_ge_of_ratio (Q := 1) hR hi'
      (γ := 3 * (K : ℝ) + 1) (by linarith) hrat
    have hpcs : primeContactSum 1 = 0 := by simp [primeContactSum]
    rw [hpcs, mul_zero, add_zero] at hpot
    change -(5 + 10 * Real.sqrt K) * σ i ^ 2 ≤ σ i ^ 2 * blockPotential 1 R J i
    have hbound : -(5 + 10 * Real.sqrt K) ≤ blockPotential 1 R J i := by linarith
    nlinarith [sq_nonneg (σ i)]
  linarith

/-- Explicit slope constant for the universal `O(√K)` shift of `reweightedNeutral`. -/
def reweightedShiftSlope (B : ℝ) : ℝ := 2 * floorContactSqrtConst * B + 10

/-- **Uniform reweighted quadratic-form lower bound**: for any bounded contact weights `|ω k| ≤ B`
(`B ≥ 0`), any `1 ≤ R`, `1 ≤ K`, `Q ≤ 4K`, and `J ≤ 3KR`, the quadratic form of
`reweightedNeutral ω Q` on `(R, R + J]` is at least `-(reweightedShiftSlope B * √K + 5) ∑ σ_i²`. -/
theorem sum_reweightedNeutral_ge {ω : ℕ → ℝ} {B : ℝ} (hB : 0 ≤ B) (hω : ∀ k, |ω k| ≤ B)
    {R K Q J : ℕ} (hR : 1 ≤ R) (hK : 1 ≤ K) (hQ : Q ≤ 4 * K) (hJ : J ≤ 3 * K * R)
    (σ : ℕ → ℝ) :
    -(reweightedShiftSlope B * Real.sqrt K + 5) * ∑ i ∈ range J, σ i ^ 2 ≤
      ∑ i ∈ range J, ∑ j ∈ range J, σ i * σ j * reweightedNeutral ω Q (R + i) (R + j) := by
  have heq : ∑ i ∈ range J, ∑ j ∈ range J, σ i * σ j * reweightedNeutral ω Q (R + i) (R + j) =
      ∑ i ∈ range J, ∑ j ∈ range J, σ i * σ j * neutralBlock 1 (R + i) (R + j) +
        ∑ k ∈ Icc 2 Q, (-ω k) *
          ∑ i ∈ range J, ∑ j ∈ range J, σ i * σ j * floorGraph k (R + i) (R + j) := by
    have hcongr : ∀ i ∈ range J, ∀ j ∈ range J,
        σ i * σ j * reweightedNeutral ω Q (R + i) (R + j) =
          σ i * σ j * (neutralBlock 1 (R + i) (R + j) +
            ∑ k ∈ Icc 2 Q, (-ω k) * floorGraph k (R + i) (R + j)) := by
      intro i _ j _
      rw [reweightedNeutral_eq_one_sub ω Q (by omega) (by omega), sub_eq_add_neg,
        ← Finset.sum_neg_distrib]
      congr 2
      exact Finset.sum_congr rfl fun k _ => by ring
    calc ∑ i ∈ range J, ∑ j ∈ range J, σ i * σ j * reweightedNeutral ω Q (R + i) (R + j)
        = ∑ i ∈ range J, ∑ j ∈ range J, σ i * σ j * (neutralBlock 1 (R + i) (R + j) +
            ∑ k ∈ Icc 2 Q, (-ω k) * floorGraph k (R + i) (R + j)) :=
          Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => hcongr i hi j hj
      _ = _ := sum_form_add_sum J σ (Icc 2 Q) (fun k => -ω k)
          (fun i j => neutralBlock 1 (R + i) (R + j))
          (fun k i j => floorGraph k (R + i) (R + j))
  rw [heq]
  have hsq : 0 ≤ ∑ i ∈ range J, σ i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hfg : -(2 * floorContactSqrtConst * B * Real.sqrt K * ∑ i ∈ range J, σ i ^ 2) ≤
      ∑ k ∈ Icc 2 Q, (-ω k) *
        ∑ i ∈ range J, ∑ j ∈ range J, σ i * σ j * floorGraph k (R + i) (R + j) := by
    have hterm : ∑ k ∈ Icc 2 Q,
        |(-ω k) * ∑ i ∈ range J, ∑ j ∈ range J, σ i * σ j * floorGraph k (R + i) (R + j)| ≤
          B * (∑ k ∈ Icc 2 (4 * K), 2 * (Λ k : ℝ) / Real.sqrt k) * ∑ i ∈ range J, σ i ^ 2 := by
      calc ∑ k ∈ Icc 2 Q,
            |(-ω k) * ∑ i ∈ range J, ∑ j ∈ range J, σ i * σ j * floorGraph k (R + i) (R + j)|
          ≤ ∑ k ∈ Icc 2 Q, B * (2 * (Λ k : ℝ) / Real.sqrt k * ∑ i ∈ range J, σ i ^ 2) := by
            refine Finset.sum_le_sum fun k hk => ?_
            rw [abs_mul, abs_neg]
            exact mul_le_mul (hω k) (abs_sum_floorGraph_le hR (Finset.mem_Icc.mp hk).1 J σ)
              (abs_nonneg _) hB
        _ ≤ ∑ k ∈ Icc 2 (4 * K), B * (2 * (Λ k : ℝ) / Real.sqrt k * ∑ i ∈ range J, σ i ^ 2) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.Icc_subset_Icc_right hQ) fun k _ _ => ?_
            exact mul_nonneg hB (mul_nonneg
              (div_nonneg (mul_nonneg zero_le_two ArithmeticFunction.vonMangoldt_nonneg)
                (Real.sqrt_nonneg _)) hsq)
        _ = B * (∑ k ∈ Icc 2 (4 * K), 2 * (Λ k : ℝ) / Real.sqrt k) * ∑ i ∈ range J, σ i ^ 2 := by
            rw [← Finset.mul_sum, ← Finset.sum_mul, mul_assoc]
    have hsumQ : ∑ k ∈ Icc 2 (4 * K), 2 * (Λ k : ℝ) / Real.sqrt k ≤
        2 * floorContactSqrtConst * Real.sqrt K := by
      calc ∑ k ∈ Icc 2 (4 * K), 2 * (Λ k : ℝ) / Real.sqrt k
          ≤ floorContactSqrtConst * Real.sqrt ((4 * K : ℕ) : ℝ) :=
            sum_vonMangoldt_div_sqrt_le (by omega)
        _ = 2 * floorContactSqrtConst * Real.sqrt K := by
            rw [Nat.cast_mul, Nat.cast_ofNat, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
              show Real.sqrt 4 = 2 by
                rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq zero_le_two]]
            ring
    have habs : |∑ k ∈ Icc 2 Q, (-ω k) *
        ∑ i ∈ range J, ∑ j ∈ range J, σ i * σ j * floorGraph k (R + i) (R + j)| ≤
          2 * floorContactSqrtConst * B * Real.sqrt K * ∑ i ∈ range J, σ i ^ 2 := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (hterm.trans ?_)
      have := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsumQ hB) hsq
      linarith
    linarith [(abs_le.mp habs).1]
  have h1 := sum_neutralBlock_one_ge hR hK hJ σ
  unfold reweightedShiftSlope
  linarith

/-- Raising `windowMatrix (reweightedNeutral ω Q) R J` by `reweightedShiftSlope B * √K + 5`
eliminates all negative squares (`hermNegIndex = 0`) at every block size `R : ℕ` (including `R = 0`
when `J = 0`). -/
theorem hermNegIndex_reweightedNeutral_shift_eq_zero {ω : ℕ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hω : ∀ k, |ω k| ≤ B) (R : ℕ) {K Q J : ℕ} (hK : 1 ≤ K) (hQ : Q ≤ 4 * K)
    (hJ : J ≤ 3 * K * R) {a : ℝ} (ha : reweightedShiftSlope B * Real.sqrt K + 5 ≤ a) :
    hermNegIndex ((windowMatrix (reweightedNeutral ω Q) R J +
      Matrix.diagonal fun _ => a).map (↑) : Matrix (Fin J) (Fin J) ℂ) = 0 := by
  rw [hermNegIndex_eq_zero_iff_forall]
  intro x
  rcases Nat.eq_zero_or_pos R with rfl | hR
  · have hJ0 : J = 0 := by omega
    subst hJ0
    simp [dotProduct]
  · have hexp : x ⬝ᵥ ((windowMatrix (reweightedNeutral ω Q) R J +
        Matrix.diagonal fun _ => a) *ᵥ x) =
        ∑ i ∈ range J, ∑ j ∈ range J,
          extendFin x i * extendFin x j * reweightedNeutral ω Q (R + i) (R + j) +
        a * ∑ i ∈ range J, extendFin x i ^ 2 := by
      have h1 : x ⬝ᵥ ((windowMatrix (reweightedNeutral ω Q) R J +
          Matrix.diagonal fun _ => a) *ᵥ x) =
          (∑ i : Fin J, ∑ j : Fin J, x i * x j * windowMatrix (reweightedNeutral ω Q) R J i j) +
            a * ∑ i : Fin J, x i ^ 2 := by
        rw [Matrix.add_mulVec, dotProduct_add]
        congr 1
        · simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
        · simp only [dotProduct, Matrix.mulVec_diagonal, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      rw [h1, sum_fin_windowMatrix_eq]
      congr 2
      rw [← Fin.sum_univ_eq_sum_range (fun i => extendFin x i ^ 2) J]
      exact Finset.sum_congr rfl fun i _ => by rw [extendFin_coe]
    rw [hexp]
    have hlow := sum_reweightedNeutral_ge hB hω hR hK hQ hJ (extendFin x)
    have hsq : 0 ≤ ∑ i ∈ range J, extendFin x i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    nlinarith

/-! ## 3. Wide-overlap top-octave blindness -/

/-- No floor map `k ≥ 2` connects blocks `a ≤ b` of ratio `b < k * a`. -/
lemma floorGraph_eq_zero_of_lt_mul {k a b : ℕ} (hk : 2 ≤ k) (hab : a ≤ b) (hb : b < k * a) :
    floorGraph k a b = 0 := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · omega
  · rw [floorGraph_of_le k hab, if_neg]
    intro hdiv
    have := (Nat.le_div_iff_mul_le (by omega : 0 < k)).mp hdiv.ge
    nlinarith

/-- Whenever `ω₁` and `ω₂` agree on `Icc 2 Q₁` and `max a b < (Q₁ + 1) * min a b` (`1 ≤ a, b`),
all contacts above `Q₁` vanish and `reweightedNeutral ω₁ Q₁ a b = reweightedNeutral ω₂ Q₂ a b`. -/
theorem reweightedNeutral_eq_of_agree_below_ratio {ω₁ ω₂ : ℕ → ℝ} {Q₁ Q₂ a b : ℕ}
    (hQ : Q₁ ≤ Q₂) (hω : ∀ k ∈ Icc 2 Q₁, ω₁ k = ω₂ k) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hrat : max a b < (Q₁ + 1) * min a b) :
    reweightedNeutral ω₁ Q₁ a b = reweightedNeutral ω₂ Q₂ a b := by
  rw [reweightedNeutral_eq_one_sub ω₁ Q₁ ha hb, reweightedNeutral_eq_one_sub ω₂ Q₂ ha hb]
  congr 1
  have hsub : Icc 2 Q₁ ⊆ Icc 2 Q₂ := Finset.Icc_subset_Icc_right hQ
  rw [← Finset.sum_sdiff hsub]
  have hzero : ∑ k ∈ Icc 2 Q₂ \ Icc 2 Q₁, ω₂ k * floorGraph k a b = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    rcases Finset.mem_sdiff.mp hk with ⟨hk2, hk1⟩
    have hk2' := (Finset.mem_Icc.mp hk2).1
    have hk_gt : Q₁ + 1 ≤ k := by
      rw [Finset.mem_Icc, not_and_or, not_le] at hk1
      rcases hk1 with h | h <;> omega
    have hfg0 : floorGraph k a b = 0 := by
      rcases le_total a b with hab | hba
      · rw [max_eq_right hab, min_eq_left hab] at hrat
        exact floorGraph_eq_zero_of_lt_mul hk2' hab (lt_of_lt_of_le hrat (by nlinarith))
      · rw [max_eq_left hba, min_eq_right hba] at hrat
        rw [floorGraph_comm]
        exact floorGraph_eq_zero_of_lt_mul hk2' hba (lt_of_lt_of_le hrat (by nlinarith))
    rw [hfg0, mul_zero]
  rw [hzero, zero_add]
  exact Finset.sum_congr rfl fun k hk => by rw [hω k hk]

/-- **Left-half blindness**: on `(R, (3K + 1)R]`, `reweightedNeutral ω₂ Q₂` (`Q₂ ≥ 3K + 1`)
depends only on `ω` up to `3K + 1`. -/
theorem windowMatrix_reweightedNeutral_leftHalf_eq {ω₁ ω₂ : ℕ → ℝ} {K Q₂ R : ℕ}
    (hR : 1 ≤ R) (hQ : 3 * K + 1 ≤ Q₂) (hω : ∀ k ∈ Icc 2 (3 * K + 1), ω₁ k = ω₂ k) :
    windowMatrix (reweightedNeutral ω₁ (3 * K + 1)) R (3 * K * R) =
      windowMatrix (reweightedNeutral ω₂ Q₂) R (3 * K * R) := by
  ext i j
  simp only [windowMatrix, Matrix.of_apply]
  refine reweightedNeutral_eq_of_agree_below_ratio hQ hω (by omega) (by omega) ?_
  have hi := i.2; have hj := j.2
  rcases le_total (i : ℕ) (j : ℕ) with hij | hji
  · rw [max_eq_right (by omega), min_eq_left (by omega)]; nlinarith
  · rw [max_eq_left (by omega), min_eq_right (by omega)]; nlinarith

/-- **Right-half blindness**: on `(2R, (6K + 2)R]` (which contains both the middle `(2R, (3K + 1)R]`
and the upper half `(2R, (6K + 1)R]` of the doubled window), `reweightedNeutral ω₂ Q₂`
(`Q₂ ≥ 3K + 1`) depends only on `ω` up to `3K + 1`. -/
theorem windowMatrix_reweightedNeutral_rightHalf_eq {ω₁ ω₂ : ℕ → ℝ} {K Q₂ R : ℕ}
    (hR : 1 ≤ R) (hQ : 3 * K + 1 ≤ Q₂) (hω : ∀ k ∈ Icc 2 (3 * K + 1), ω₁ k = ω₂ k) :
    windowMatrix (reweightedNeutral ω₁ (3 * K + 1)) (2 * R) (6 * K * R) =
      windowMatrix (reweightedNeutral ω₂ Q₂) (2 * R) (6 * K * R) := by
  ext i j
  simp only [windowMatrix, Matrix.of_apply]
  refine reweightedNeutral_eq_of_agree_below_ratio hQ hω (by omega) (by omega) ?_
  have hi := i.2; have hj := j.2
  rcases le_total (i : ℕ) (j : ℕ) with hij | hji
  · rw [max_eq_right (by omega), min_eq_left (by omega)]; nlinarith
  · rw [max_eq_left (by omega), min_eq_right (by omega)]; nlinarith

/-- **Exact top-octave decomposition of window doubling**: on `(R, (6K + 1)R]` (`1 ≤ R`), the
true neutral window `neutralWindow (6K + 1) R (6KR)` differs from the un-updated glued matrix
`neutralWindow (3K + 1) R (6KR)` by `-∑_{k = 3K + 2}^{6K + 1} windowMatrix (floorGraph k) R (6KR)`,
and every summand vanishes outside `(R, 2R] × ((3K + 1)R, (6K + 1)R]` and its transpose. -/
theorem neutralWindow_doubling_topOctave_decomposition {K R : ℕ} (hR : 1 ≤ R) :
    neutralWindow (6 * K + 1) R (6 * K * R) =
      neutralWindow (3 * K + 1) R (6 * K * R) -
        ∑ k ∈ Icc (3 * K + 2) (6 * K + 1), windowMatrix (floorGraph k) R (6 * K * R) ∧
    ∀ k ∈ Icc (3 * K + 2) (6 * K + 1), ∀ i j : Fin (6 * K * R),
      windowMatrix (floorGraph k) R (6 * K * R) i j ≠ 0 →
        ((i : ℕ) < R ∧ 3 * K * R < (j : ℕ)) ∨ ((j : ℕ) < R ∧ 3 * K * R < (i : ℕ)) := by
  constructor
  · ext i j
    simp only [neutralWindow, windowMatrix, Matrix.of_apply, Matrix.sub_apply, Matrix.sum_apply]
    have h1 := reweightedNeutral_eq_one_sub (fun _ => 1) (6 * K + 1)
      (a := R + i) (b := R + j) (by omega) (by omega)
    have h2 := reweightedNeutral_eq_one_sub (fun _ => 1) (3 * K + 1)
      (a := R + i) (b := R + j) (by omega) (by omega)
    have hrew : ∀ Q, reweightedNeutral (fun _ => 1) Q (R + i) (R + j) =
        neutralBlock Q (R + i) (R + j) := fun Q => by
      simp [reweightedNeutral]
    rw [hrew] at h1 h2
    simp only [one_mul] at h1 h2
    have hsplit : Icc 2 (6 * K + 1) = Icc 2 (3 * K + 1) ∪ Icc (3 * K + 2) (6 * K + 1) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_union]; omega
    have hdisj : Disjoint (Icc 2 (3 * K + 1)) (Icc (3 * K + 2) (6 * K + 1)) := by
      rw [Finset.disjoint_left]
      intro k hk1 hk2
      have := (Finset.mem_Icc.mp hk1).2; have := (Finset.mem_Icc.mp hk2).1; omega
    rw [h1, h2, hsplit, Finset.sum_union hdisj]
    ring
  · intro k hk i j hne
    simp only [windowMatrix, Matrix.of_apply] at hne
    rcases Finset.mem_Icc.mp hk with ⟨hk_lo, hk_hi⟩
    have hi := i.2; have hj := j.2
    rcases lt_trichotomy (i : ℕ) (j : ℕ) with hij | heq | hji
    · rw [floorGraph_of_le k (by omega)] at hne
      have hdiv : (R + (j : ℕ)) / k = R + (i : ℕ) := by
        by_contra h; exact hne (if_neg h)
      have hmul := (Nat.le_div_iff_mul_le (by omega : 0 < k)).mp hdiv.ge
      left
      constructor
      · by_contra hiR; nlinarith
      · nlinarith
    · exfalso
      have : R + (i : ℕ) = R + (j : ℕ) := by omega
      rw [this, floorGraph_eq_zero (by omega) le_rfl (by omega)] at hne
      exact hne rfl
    · rw [floorGraph_comm, floorGraph_of_le k (by omega)] at hne
      have hdiv : (R + (i : ℕ)) / k = R + (j : ℕ) := by
        by_contra h; exact hne (if_neg h)
      have hmul := (Nat.le_div_iff_mul_le (by omega : 0 < k)).mp hdiv.ge
      right
      constructor
      · by_contra hjR; nlinarith
      · nlinarith

/-! ## 4. Two-cluster negative-plane machinery, `subEulerGluingWeight`, and un-updated jump -/

/-- Symmetric two-vector criterion for `2 ≤ hermNegIndex`: diagonal upper bounds `α, γ` with
`α < 0` and cross magnitude `|bilin G w₁ w₂| ≤ M` (`0 ≤ M`) satisfying `M² < α * γ`. -/
theorem two_le_hermNegIndex_of_diag_and_abs_cross {ι : Type*} [Fintype ι]
    (G : Matrix ι ι ℝ) (hG : ∀ i j, G i j = G j i) (w₁ w₂ : ι → ℝ) {α γ M : ℝ}
    (_ : 0 ≤ M) (h1 : bilin G w₁ w₁ ≤ α) (h2 : bilin G w₂ w₂ ≤ γ)
    (hc : |bilin G w₁ w₂| ≤ M) (hα : α < 0) (hdisc : M ^ 2 < α * γ) :
    2 ≤ hermNegIndex (G.map (↑) : Matrix ι ι ℂ) := by
  refine two_le_hermNegIndex_of_two_vectors G w₁ w₂ (α := α) (γ := γ) (c := bilin G w₁ w₂)
    (fun s t => ?_) hα ?_
  · have hexp : bilin G (fun i => s * w₁ i + t * w₂ i) (fun i => s * w₁ i + t * w₂ i) =
        bilin G w₁ w₁ * s ^ 2 + 2 * bilin G w₁ w₂ * s * t + bilin G w₂ w₂ * t ^ 2 := by
      unfold bilin
      have h21 : ∑ i : ι, ∑ j : ι, w₂ i * w₁ j * G i j =
          ∑ i : ι, ∑ j : ι, w₁ i * w₂ j * G i j := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hG j i]; ring
      have hlin : ∑ i : ι, ∑ j : ι, (s * w₁ i + t * w₂ i) * (s * w₁ j + t * w₂ j) * G i j =
          s ^ 2 * (∑ i : ι, ∑ j : ι, w₁ i * w₁ j * G i j) +
            s * t * (∑ i : ι, ∑ j : ι, w₁ i * w₂ j * G i j) +
            s * t * (∑ i : ι, ∑ j : ι, w₂ i * w₁ j * G i j) +
            t ^ 2 * (∑ i : ι, ∑ j : ι, w₂ i * w₂ j * G i j) := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      rw [hlin, h21]
      ring
    rw [hexp]
    nlinarith [sq_nonneg s, sq_nonneg t]
  · have hcsq : (bilin G w₁ w₂) ^ 2 ≤ M ^ 2 := by
      rw [← sq_abs (bilin G w₁ w₂)]
      exact pow_le_pow_left₀ (abs_nonneg _) hc 2
    linarith

/-- Polarization of `abs_sum_floorGraph_le`: bilinear bound on `floorGraph k` for any two step
vectors `u, v`. -/
theorem abs_bilin_floorGraph_le {R : ℕ} (hR : 1 ≤ R) {k : ℕ} (hk : 2 ≤ k) (J : ℕ)
    (u v : ℕ → ℝ) :
    |∑ i ∈ range J, ∑ j ∈ range J, u i * v j * floorGraph k (R + i) (R + j)| ≤
      (Λ k : ℝ) / Real.sqrt k * (∑ i ∈ range J, u i ^ 2 + ∑ i ∈ range J, v i ^ 2) := by
  have hp := abs_sum_floorGraph_le hR hk J (fun i => u i + v i)
  have hm := abs_sum_floorGraph_le hR hk J (fun i => u i - v i)
  have hpol : 4 * ∑ i ∈ range J, ∑ j ∈ range J, u i * v j * floorGraph k (R + i) (R + j) =
      (∑ i ∈ range J, ∑ j ∈ range J, (u i + v i) * (u j + v j) * floorGraph k (R + i) (R + j)) -
        (∑ i ∈ range J, ∑ j ∈ range J, (u i - v i) * (u j - v j) * floorGraph k (R + i) (R + j)) := by
    have hcomm : ∑ i ∈ range J, ∑ j ∈ range J, v i * u j * floorGraph k (R + i) (R + j) =
        ∑ i ∈ range J, ∑ j ∈ range J, u i * v j * floorGraph k (R + i) (R + j) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
        rw [floorGraph_comm]; ring
    have hdiff :
        (∑ i ∈ range J, ∑ j ∈ range J, (u i + v i) * (u j + v j) * floorGraph k (R + i) (R + j)) -
        (∑ i ∈ range J, ∑ j ∈ range J, (u i - v i) * (u j - v j) * floorGraph k (R + i) (R + j)) =
          2 * (∑ i ∈ range J, ∑ j ∈ range J, u i * v j * floorGraph k (R + i) (R + j)) +
            2 * (∑ i ∈ range J, ∑ j ∈ range J, v i * u j * floorGraph k (R + i) (R + j)) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [hdiff, hcomm]; ring
  have hnorm : ∑ i ∈ range J, (u i + v i) ^ 2 + ∑ i ∈ range J, (u i - v i) ^ 2 =
      2 * (∑ i ∈ range J, u i ^ 2 + ∑ i ∈ range J, v i ^ 2) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h4 : 4 * |∑ i ∈ range J, ∑ j ∈ range J, u i * v j * floorGraph k (R + i) (R + j)| ≤
      2 * (Λ k : ℝ) / Real.sqrt k *
        (∑ i ∈ range J, (u i + v i) ^ 2 + ∑ i ∈ range J, (u i - v i) ^ 2) := by
    have h1 : |4 * ∑ i ∈ range J, ∑ j ∈ range J, u i * v j * floorGraph k (R + i) (R + j)| =
        4 * |∑ i ∈ range J, ∑ j ∈ range J, u i * v j * floorGraph k (R + i) (R + j)| := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    rw [← h1, hpol]
    exact (abs_sub _ _).trans (by linarith)
  rw [hnorm] at h4
  have h4_eq : 2 * (Λ k : ℝ) / Real.sqrt k *
      (2 * (∑ i ∈ range J, u i ^ 2 + ∑ i ∈ range J, v i ^ 2)) =
      4 * ((Λ k : ℝ) / Real.sqrt k * (∑ i ∈ range J, u i ^ 2 + ∑ i ∈ range J, v i ^ 2)) := by
    ring
  linarith

/-- Sub-square-root logarithm bound `log x ≤ ε √x + 4 / ε` for all `x > 0` and `ε > 0`. -/
lemma log_le_eps_mul_sqrt_add {x ε : ℝ} (hx : 0 < x) (hε : 0 < ε) :
    Real.log x ≤ ε * Real.sqrt x + 4 / ε := by
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have ht : 0 < Real.sqrt (Real.sqrt x) := Real.sqrt_pos.mpr hsx
  have hlog : Real.log x ≤ 4 * Real.sqrt (Real.sqrt x) := by
    have h4 : Real.sqrt (Real.sqrt x) ^ 4 = x := by
      calc Real.sqrt (Real.sqrt x) ^ 4 = (Real.sqrt (Real.sqrt x) ^ 2) ^ 2 := by ring
        _ = x := by rw [Real.sq_sqrt hsx.le, Real.sq_sqrt hx.le]
    have hl := Real.log_pow (Real.sqrt (Real.sqrt x)) 4
    rw [h4, Nat.cast_ofNat] at hl
    linarith [Real.log_le_sub_one_of_pos ht]
  have ham : 0 ≤ (ε * Real.sqrt (Real.sqrt x) - 2) ^ 2 := sq_nonneg _
  have ht2 : Real.sqrt (Real.sqrt x) ^ 2 = Real.sqrt x := Real.sq_sqrt hsx.le
  have hdiv : 4 * ε * Real.sqrt (Real.sqrt x) ≤ ε ^ 2 * Real.sqrt x + 4 := by nlinarith
  have hfin : 4 * Real.sqrt (Real.sqrt x) ≤ ε * Real.sqrt x + 4 / ε := by
    calc 4 * Real.sqrt (Real.sqrt x)
        = (4 * ε * Real.sqrt (Real.sqrt x)) / ε := by field_simp [hε.ne']
      _ ≤ (ε ^ 2 * Real.sqrt x + 4) / ε := div_le_div_of_nonneg_right hdiv hε.le
      _ = ε * Real.sqrt x + 4 / ε := by field_simp [hε.ne']
  linarith

/-- Rewriting `bilin (windowMatrix K R₀ J₀ + a I)` on step functions into `range J₀` sums. -/
lemma bilin_windowMatrix_add_diagonal_coe (K : ℕ → ℕ → ℝ) (R₀ J₀ : ℕ) (a : ℝ) (x y : ℕ → ℝ) :
    bilin (windowMatrix K R₀ J₀ + Matrix.diagonal (fun _ : Fin J₀ => a))
        (fun i : Fin J₀ => x i) (fun i : Fin J₀ => y i) =
      (∑ i ∈ range J₀, ∑ l ∈ range J₀, x i * y l * K (R₀ + i) (R₀ + l)) +
        a * ∑ i ∈ range J₀, x i * y i := by
  have h1 : bilin (windowMatrix K R₀ J₀ + Matrix.diagonal (fun _ : Fin J₀ => a))
      (fun i : Fin J₀ => x i) (fun i : Fin J₀ => y i) =
      bilin (windowMatrix K R₀ J₀) (fun i : Fin J₀ => x i) (fun i : Fin J₀ => y i) +
        bilin (Matrix.diagonal (fun _ : Fin J₀ => a))
          (fun i : Fin J₀ => x i) (fun i : Fin J₀ => y i) := by
    unfold bilin
    simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib]
  have hwin : bilin (windowMatrix K R₀ J₀) (fun i : Fin J₀ => x i) (fun i : Fin J₀ => y i) =
      ∑ i ∈ range J₀, ∑ l ∈ range J₀, x i * y l * K (R₀ + i) (R₀ + l) := by
    unfold bilin
    rw [← Fin.sum_univ_eq_sum_range (fun i => ∑ l ∈ range J₀, x i * y l * K (R₀ + i) (R₀ + l)) J₀]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Fin.sum_univ_eq_sum_range (fun l => x i * y l * K (R₀ + i) (R₀ + l)) J₀]
    rfl
  rw [h1, hwin]
  congr 1
  unfold bilin
  have hdiag : ∀ i : Fin J₀,
      ∑ l : Fin J₀, x i * y l * (Matrix.diagonal (fun _ : Fin J₀ => a)) i l = a * (x i * y i) := by
    intro i
    rw [Finset.sum_eq_single i
      (fun l _ hli => by simp [hli.symm])
      (fun hi => absurd (Finset.mem_univ i) hi)]
    simp; ring
  simp_rw [hdiag]
  rw [← Finset.mul_sum, ← Fin.sum_univ_eq_sum_range (fun i => x i * y i) J₀]

/-- Refinement invariance + principal-submatrix monotonicity for two negative squares of
`windowMatrix (reweightedNeutral ω Q) + a I`: any coarse witness pair `(u, v)` on `(R₀, R₀ + J₀]`
lifts to every refinement `m ≥ 1` and every enclosing window `(R, R + J]`
(`R ≤ m R₀`, `m R₀ + m J₀ ≤ R + J`). -/
theorem two_le_hermNegIndex_reweightedNeutral_of_coarse {R₀ m R J₀ J Q : ℕ} (hR₀ : 1 ≤ R₀)
    (hm : 1 ≤ m) (hlo : R ≤ m * R₀) (hhi : m * R₀ + m * J₀ ≤ R + J) (ω : ℕ → ℝ) (a : ℝ)
    (u v : ℕ → ℝ) {α γ M : ℝ} (hM0 : 0 ≤ M)
    (hu : bilin (windowMatrix (reweightedNeutral ω Q) R₀ J₀ + Matrix.diagonal (fun _ : Fin J₀ => a))
      (fun j : Fin J₀ => u j) (fun j : Fin J₀ => u j) ≤ α)
    (hv : bilin (windowMatrix (reweightedNeutral ω Q) R₀ J₀ + Matrix.diagonal (fun _ : Fin J₀ => a))
      (fun j : Fin J₀ => v j) (fun j : Fin J₀ => v j) ≤ γ)
    (huv : |bilin (windowMatrix (reweightedNeutral ω Q) R₀ J₀ + Matrix.diagonal (fun _ : Fin J₀ => a))
      (fun j : Fin J₀ => u j) (fun j : Fin J₀ => v j)| ≤ M)
    (hα : α < 0) (hdisc : M ^ 2 < α * γ) :
    2 ≤ hermNegIndex ((windowMatrix (reweightedNeutral ω Q) R J +
      Matrix.diagonal (fun _ : Fin J => a)).map (↑) : Matrix (Fin J) (Fin J) ℂ) := by
  let G₀ : Matrix (Fin J₀) (Fin J₀) ℝ :=
    windowMatrix (reweightedNeutral ω Q) R₀ J₀ + Matrix.diagonal (fun _ : Fin J₀ => a)
  let Gₘ : Matrix (Fin (m * J₀)) (Fin (m * J₀)) ℝ :=
    windowMatrix (reweightedNeutral ω Q) (m * R₀) (m * J₀) +
      Matrix.diagonal (fun _ : Fin (m * J₀) => a)
  have hsymm : ∀ c n, ∀ i j : Fin n,
      (windowMatrix (reweightedNeutral ω Q) c n + Matrix.diagonal (fun _ : Fin n => a)) i j =
        (windowMatrix (reweightedNeutral ω Q) c n + Matrix.diagonal (fun _ : Fin n => a)) j i := by
    intro c n i j
    simp only [Matrix.add_apply, windowMatrix, Matrix.of_apply, Matrix.diagonal_apply]
    rw [reweightedNeutral_comm]
    by_cases hij : i = j
    · subst hij; rfl
    · rw [if_neg hij, if_neg (Ne.symm hij)]
  have hquad : ∀ x : ℕ → ℝ,
      bilin Gₘ (fun i : Fin (m * J₀) => refineStep m x i)
        (fun i : Fin (m * J₀) => refineStep m x i) =
        bilin G₀ (fun j : Fin J₀ => x j) (fun j : Fin J₀ => x j) := by
    intro x
    dsimp only [Gₘ, G₀]
    rw [bilin_windowMatrix_add_diagonal_coe, bilin_windowMatrix_add_diagonal_coe,
      sum_reweightedNeutral_refine hR₀ hm ω Q J₀ x]
    have hsq1 : ∑ i ∈ range (m * J₀), refineStep m x i * refineStep m x i =
        ∑ i ∈ range (m * J₀), refineStep m x i ^ 2 :=
      Finset.sum_congr rfl fun _ _ => (sq _).symm
    have hsq2 : ∑ i ∈ range J₀, x i * x i = ∑ i ∈ range J₀, x i ^ 2 :=
      Finset.sum_congr rfl fun _ _ => (sq _).symm
    rw [hsq1, hsq2, sum_refineStep_sq hm J₀ x]
  have hbilin : bilin Gₘ (fun i : Fin (m * J₀) => refineStep m u i)
        (fun i : Fin (m * J₀) => refineStep m v i) =
      bilin G₀ (fun j : Fin J₀ => u j) (fun j : Fin J₀ => v j) := by
    have hpol : ∀ {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ), (∀ i j, H i j = H j i) →
        ∀ x y : Fin n → ℝ,
          2 * bilin H x y = bilin H (fun i => x i + y i) (fun i => x i + y i) -
            bilin H x x - bilin H y y := by
      intro n H hH x y
      unfold bilin
      have hcomm : ∑ i : Fin n, ∑ j : Fin n, y i * x j * H i j =
          ∑ i : Fin n, ∑ j : Fin n, x i * y j * H i j := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hH j i]; ring
      have hexp : ∑ i : Fin n, ∑ j : Fin n, (x i + y i) * (x j + y j) * H i j =
          (∑ i : Fin n, ∑ j : Fin n, x i * x j * H i j) +
            (∑ i : Fin n, ∑ j : Fin n, x i * y j * H i j) +
            (∑ i : Fin n, ∑ j : Fin n, y i * x j * H i j) +
            (∑ i : Fin n, ∑ j : Fin n, y i * y j * H i j) := by
        simp only [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      rw [hexp, hcomm]; ring
    have href_add : (fun i : Fin (m * J₀) => refineStep m u i + refineStep m v i) =
        (fun i : Fin (m * J₀) => refineStep m (fun j => u j + v j) i) := by
      funext i; simp only [refineStep]; ring
    have h1 := hpol Gₘ (hsymm (m * R₀) (m * J₀)) (fun i : Fin (m * J₀) => refineStep m u i)
      (fun i : Fin (m * J₀) => refineStep m v i)
    have h2 := hpol G₀ (hsymm R₀ J₀) (fun j : Fin J₀ => u j) (fun j : Fin J₀ => v j)
    rw [href_add, hquad (fun j => u j + v j), hquad u, hquad v] at h1
    linarith
  have h2m : 2 ≤ hermNegIndex (Gₘ.map (↑) : Matrix (Fin (m * J₀)) (Fin (m * J₀)) ℂ) :=
    two_le_hermNegIndex_of_diag_and_abs_cross Gₘ (hsymm (m * R₀) (m * J₀))
      (fun i : Fin (m * J₀) => refineStep m u i)
      (fun i : Fin (m * J₀) => refineStep m v i) hM0
      ((hquad u).le.trans hu) ((hquad v).le.trans hv) (by rw [hbilin]; exact huv) hα hdisc
  let f : Fin (m * J₀) → Fin J := fun i => ⟨m * R₀ - R + i.1, by omega⟩
  have hsub : ((windowMatrix (reweightedNeutral ω Q) R J +
      Matrix.diagonal (fun _ : Fin J => a)).map (↑) : Matrix (Fin J) (Fin J) ℂ).submatrix f f =
      (Gₘ.map (↑) : Matrix (Fin (m * J₀)) (Fin (m * J₀)) ℂ) := by
    ext i j
    simp only [Gₘ, Matrix.submatrix_apply, Matrix.map_apply, Matrix.add_apply, windowMatrix,
      Matrix.of_apply, Matrix.diagonal_apply, f]
    have heq1 : R + (m * R₀ - R + (i : ℕ)) = m * R₀ + (i : ℕ) := by omega
    have heq2 : R + (m * R₀ - R + (j : ℕ)) = m * R₀ + (j : ℕ) := by omega
    rw [heq1, heq2]
    congr 2
    by_cases hij : i = j
    · subst hij; simp
    · have hne : (⟨m * R₀ - R + (i : ℕ), by omega⟩ : Fin J) ≠
          ⟨m * R₀ - R + (j : ℕ), by omega⟩ := by
        intro h
        apply hij
        ext
        have := congrArg Fin.val h
        dsimp at this
        omega
      rw [if_neg hne, if_neg hij]
  exact h2m.trans (by rw [← hsub]; exact HeckeKreinToeplitz.hermNegIndex_submatrix_le _ f)

/-- Unit-norm two-scale cluster vector placing mass `1/2` on block offset `p₀` and mass `1/2`
uniformly across `[q₀, q₀ + L)`. -/
def clusterVec (p₀ q₀ L : ℕ) (j : ℕ) : ℝ :=
  if j = p₀ then 1 / Real.sqrt 2
  else if q₀ ≤ j ∧ j < q₀ + L then 1 / Real.sqrt (2 * (L : ℝ))
  else 0

lemma clusterVec_nonneg (p₀ q₀ L j : ℕ) : 0 ≤ clusterVec p₀ q₀ L j := by
  unfold clusterVec
  split_ifs <;> positivity

lemma sum_clusterVec_sq {p₀ q₀ L J₀ : ℕ} (hpq : p₀ < q₀) (hqJ : q₀ + L ≤ J₀) (hL : 1 ≤ L) :
    ∑ j ∈ range J₀, clusterVec p₀ q₀ L j ^ 2 = 1 := by
  have hsplit : ∑ j ∈ range J₀, clusterVec p₀ q₀ L j ^ 2 =
      (∑ j ∈ {p₀}, (1 / Real.sqrt 2 : ℝ) ^ 2) +
        (∑ j ∈ Ico q₀ (q₀ + L), (1 / Real.sqrt (2 * (L : ℝ))) ^ 2) := by
    have hdisj : Disjoint ({p₀} : Finset ℕ) (Ico q₀ (q₀ + L)) := by
      rw [Finset.disjoint_left]
      intro j hj1 hj2
      rw [Finset.mem_singleton] at hj1
      have := (Finset.mem_Ico.mp hj2).1
      omega
    have hsub : ({p₀} ∪ Ico q₀ (q₀ + L)) ⊆ range J₀ := by
      intro j hj
      rcases Finset.mem_union.mp hj with hj1 | hj2
      · rw [Finset.mem_singleton] at hj1; exact Finset.mem_range.mpr (by omega)
      · have := (Finset.mem_Ico.mp hj2).2; exact Finset.mem_range.mpr (by omega)
    rw [← Finset.sum_subset hsub]
    · rw [Finset.sum_union hdisj]
      congr 1
      · refine Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.mem_singleton.mp hj]
        simp [clusterVec]
      · refine Finset.sum_congr rfl fun j hj => ?_
        rcases Finset.mem_Ico.mp hj with ⟨h1, h2⟩
        have hne : j ≠ p₀ := by omega
        simp [clusterVec, hne, h1, h2]
    · intro j _ hjnot
      rw [Finset.mem_union, Finset.mem_singleton, Finset.mem_Ico, not_or] at hjnot
      simp [clusterVec, hjnot.1, hjnot.2]
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  rw [hsplit, Finset.sum_singleton, Finset.sum_const, Nat.card_Ico, Nat.add_sub_cancel_left,
    nsmul_eq_mul, div_pow, div_pow, one_pow, Real.sq_sqrt zero_le_two,
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * L)]
  field_simp [hLpos.ne']
  ring

lemma clusterVec_mul_eq_zero {p₁ q₁ L₁ p₂ q₂ L₂ : ℕ} (hp : p₁ < p₂) (hpq : p₂ < q₁)
    (hq : q₁ + L₁ ≤ q₂) (j : ℕ) :
    clusterVec p₁ q₁ L₁ j * clusterVec p₂ q₂ L₂ j = 0 := by
  unfold clusterVec
  split_ifs <;> first | simp only [mul_zero, zero_mul] | (exfalso; omega)

/-- **Self-pairing upper bound for `clusterVec`**: for nonnegative weights `ω ≥ 0`, all diagonal
entries are bounded by `log(R₀ + J₀ + 1) + 1 + a` while all off-diagonal entries are nonpositive,
retaining at least the lower-to-upper floor-contact attraction. -/
theorem bilin_reweightedNeutral_clusterVec_le {ω : ℕ → ℝ} (hω : ∀ k, 0 ≤ ω k)
    {R₀ Q J₀ p₀ q₀ L : ℕ} (hR₀ : 1 ≤ R₀) (hpq : p₀ < q₀) (hqJ : q₀ + L ≤ J₀) (hL : 1 ≤ L)
    (a : ℝ) :
    bilin (windowMatrix (reweightedNeutral ω Q) R₀ J₀ + Matrix.diagonal (fun _ : Fin J₀ => a))
        (fun j : Fin J₀ => clusterVec p₀ q₀ L j) (fun j : Fin J₀ => clusterVec p₀ q₀ L j) ≤
      Real.log (((R₀ + J₀ : ℕ) : ℝ) + 1) + 1 + a -
        (1 / Real.sqrt L) * ∑ k ∈ Icc 2 Q, ω k *
          ∑ l ∈ Ico q₀ (q₀ + L), floorGraph k (R₀ + p₀) (R₀ + l) := by
  rw [bilin_windowMatrix_add_diagonal_coe]
  have hdiag_split : ∑ i ∈ range J₀, ∑ l ∈ range J₀,
      clusterVec p₀ q₀ L i * clusterVec p₀ q₀ L l * reweightedNeutral ω Q (R₀ + i) (R₀ + l) =
      (∑ i ∈ range J₀, clusterVec p₀ q₀ L i ^ 2 * reweightedNeutral ω Q (R₀ + i) (R₀ + i)) +
        ∑ i ∈ range J₀, ∑ l ∈ (range J₀).erase i,
          clusterVec p₀ q₀ L i * clusterVec p₀ q₀ L l * reweightedNeutral ω Q (R₀ + i) (R₀ + l) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← Finset.add_sum_erase _ _ hi]
    ring
  rw [hdiag_split]
  have hsq_eq : ∑ i ∈ range J₀, clusterVec p₀ q₀ L i * clusterVec p₀ q₀ L i = 1 := by
    simpa only [sq] using sum_clusterVec_sq hpq hqJ hL
  have hdiag_le : (∑ i ∈ range J₀,
      clusterVec p₀ q₀ L i ^ 2 * reweightedNeutral ω Q (R₀ + i) (R₀ + i)) +
        a * ∑ i ∈ range J₀, clusterVec p₀ q₀ L i * clusterVec p₀ q₀ L i ≤
      Real.log (((R₀ + J₀ : ℕ) : ℝ) + 1) + 1 + a := by
    rw [hsq_eq, mul_one]
    have h1 : ∑ i ∈ range J₀,
        clusterVec p₀ q₀ L i ^ 2 * reweightedNeutral ω Q (R₀ + i) (R₀ + i) ≤
        (Real.log (((R₀ + J₀ : ℕ) : ℝ) + 1) + 1) * ∑ i ∈ range J₀, clusterVec p₀ q₀ L i ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i hi => ?_
      have hi' := Finset.mem_range.mp hi
      have hself := reweightedNeutral_self_le ω Q (a := R₀ + i) (by omega)
      have hlog : Real.log (((R₀ + i : ℕ) : ℝ) + 1) ≤ Real.log (((R₀ + J₀ : ℕ) : ℝ) + 1) := by
        refine Real.log_le_log (by positivity) ?_
        have : ((R₀ + i : ℕ) : ℝ) ≤ ((R₀ + J₀ : ℕ) : ℝ) := by exact_mod_cast (by omega : R₀ + i ≤ R₀ + J₀)
        linarith
      nlinarith [sq_nonneg (clusterVec p₀ q₀ L i)]
    rw [sum_clusterVec_sq hpq hqJ hL, mul_one] at h1
    linarith
  -- Off-diagonal sum is at most the `(p₀, l)` and `(l, p₀)` pairs for `l ∈ Ico q₀ (q₀ + L)`.
  let P : Finset (ℕ × ℕ) := (range J₀).biUnion fun i => ((range J₀).erase i).map
    ⟨fun l => (i, l), fun _ _ h => (Prod.mk.inj h).2⟩
  let S : Finset (ℕ × ℕ) :=
    (Ico q₀ (q₀ + L)).map ⟨fun l => (p₀, l), fun _ _ h => (Prod.mk.inj h).2⟩ ∪
      (Ico q₀ (q₀ + L)).map ⟨fun l => (l, p₀), fun _ _ h => (Prod.mk.inj h).1⟩
  have hSP : S ⊆ P := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx1 | hx2 <;>
    · rcases Finset.mem_map.mp ‹_› with ⟨l, hl, rfl⟩
      rcases Finset.mem_Ico.mp hl with ⟨hl1, hl2⟩
      refine Finset.mem_biUnion.mpr ⟨_, Finset.mem_range.mpr (by omega),
        Finset.mem_map.mpr ⟨_, Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩, rfl⟩⟩
  have hoff_eq : ∑ i ∈ range J₀, ∑ l ∈ (range J₀).erase i,
      clusterVec p₀ q₀ L i * clusterVec p₀ q₀ L l * reweightedNeutral ω Q (R₀ + i) (R₀ + l) =
      ∑ x ∈ P, clusterVec p₀ q₀ L x.1 * clusterVec p₀ q₀ L x.2 *
        reweightedNeutral ω Q (R₀ + x.1) (R₀ + x.2) := by
    dsimp [P]
    rw [Finset.sum_biUnion]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_map]; rfl
    · intro i₁ _ i₂ _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      rcases Finset.mem_map.mp hx1 with ⟨l₁, _, rfl⟩
      rcases Finset.mem_map.mp hx2 with ⟨l₂, _, h2⟩
      exact hne (Prod.mk.inj h2).1.symm
  have hoff_nonpos : ∀ x ∈ P, x ∉ S →
      clusterVec p₀ q₀ L x.1 * clusterVec p₀ q₀ L x.2 *
        reweightedNeutral ω Q (R₀ + x.1) (R₀ + x.2) ≤ 0 := by
    intro x hx _
    rcases Finset.mem_biUnion.mp hx with ⟨i, _, hx'⟩
    rcases Finset.mem_map.mp hx' with ⟨l, hl, rfl⟩
    have hne : R₀ + i ≠ R₀ + l := by
      have := (Finset.mem_erase.mp hl).1; omega
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (clusterVec_nonneg _ _ _ _) (clusterVec_nonneg _ _ _ _))
      (reweightedNeutral_nonpos_of_ne hω Q hne)
  have hS_disj : Disjoint
      ((Ico q₀ (q₀ + L)).map ⟨fun l => (p₀, l), fun _ _ h => (Prod.mk.inj h).2⟩)
      ((Ico q₀ (q₀ + L)).map ⟨fun l => (l, p₀), fun _ _ h => (Prod.mk.inj h).1⟩) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rcases Finset.mem_map.mp hx1 with ⟨l₁, hl₁, rfl⟩
    rcases Finset.mem_map.mp hx2 with ⟨l₂, _, h2⟩
    have := (Finset.mem_Ico.mp hl₁).1
    have := (Prod.mk.inj h2).2
    omega
  have hS_val : ∑ x ∈ S, clusterVec p₀ q₀ L x.1 * clusterVec p₀ q₀ L x.2 *
      reweightedNeutral ω Q (R₀ + x.1) (R₀ + x.2) ≤
      -(1 / Real.sqrt L) * ∑ k ∈ Icc 2 Q, ω k *
        ∑ l ∈ Ico q₀ (q₀ + L), floorGraph k (R₀ + p₀) (R₀ + l) := by
    dsimp [S]
    rw [Finset.sum_union hS_disj, Finset.sum_map, Finset.sum_map]
    have hsame : ∑ l ∈ Ico q₀ (q₀ + L),
        clusterVec p₀ q₀ L l * clusterVec p₀ q₀ L p₀ * reweightedNeutral ω Q (R₀ + l) (R₀ + p₀) =
        ∑ l ∈ Ico q₀ (q₀ + L),
          clusterVec p₀ q₀ L p₀ * clusterVec p₀ q₀ L l * reweightedNeutral ω Q (R₀ + p₀) (R₀ + l) :=
      Finset.sum_congr rfl fun l _ => by rw [reweightedNeutral_comm]; ring
    dsimp only [Function.Embedding.coeFn_mk]
    rw [hsame, ← two_mul]
    have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
    have hprod : ∀ l ∈ Ico q₀ (q₀ + L),
        2 * (clusterVec p₀ q₀ L p₀ * clusterVec p₀ q₀ L l) = 1 / Real.sqrt L := by
      intro l hl
      rcases Finset.mem_Ico.mp hl with ⟨hl1, hl2⟩
      have hne : l ≠ p₀ := by omega
      have h1 : clusterVec p₀ q₀ L p₀ = 1 / Real.sqrt 2 := by simp [clusterVec]
      have h2 : clusterVec p₀ q₀ L l = 1 / Real.sqrt (2 * (L : ℝ)) := by
        simp [clusterVec, hne, hl1, hl2]
      rw [h1, h2, Real.sqrt_mul zero_le_two]
      have hs2_ne : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr zero_lt_two).ne'
      have hsL_ne : Real.sqrt (L : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hLpos).ne'
      field_simp [hs2_ne, hsL_ne]
      rw [Real.sq_sqrt zero_le_two]
    have hterm_le : 2 * ∑ l ∈ Ico q₀ (q₀ + L),
        clusterVec p₀ q₀ L p₀ * clusterVec p₀ q₀ L l * reweightedNeutral ω Q (R₀ + p₀) (R₀ + l) ≤
        ∑ l ∈ Ico q₀ (q₀ + L),
          (1 / Real.sqrt L) * (-(∑ k ∈ Icc 2 Q, ω k * floorGraph k (R₀ + p₀) (R₀ + l))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun l hl => ?_
      have heq_p : 2 * (clusterVec p₀ q₀ L p₀ * clusterVec p₀ q₀ L l *
          reweightedNeutral ω Q (R₀ + p₀) (R₀ + l)) =
          (1 / Real.sqrt L) * reweightedNeutral ω Q (R₀ + p₀) (R₀ + l) := by
        rw [← mul_assoc, hprod l hl]
      rw [heq_p]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have hl1 := (Finset.mem_Ico.mp hl).1
      rw [reweightedNeutral_of_lt ω Q (by omega : R₀ + p₀ < R₀ + l)]
      have hjet : 0 < blockJet (R₀ + p₀) (R₀ + l) := by
        unfold blockJet
        linarith [xLogXDiff_pos (n := R₀ + p₀ + (R₀ + l) + 1) (by omega),
          xLogXDiff_pos (n := R₀ + l - (R₀ + p₀)) (by omega)]
      linarith
    refine hterm_le.trans (le_of_eq ?_)
    rw [← Finset.mul_sum, Finset.sum_neg_distrib, Finset.sum_comm]
    simp only [← Finset.mul_sum]
    ring
  have hoff_le : ∑ i ∈ range J₀, ∑ l ∈ (range J₀).erase i,
      clusterVec p₀ q₀ L i * clusterVec p₀ q₀ L l * reweightedNeutral ω Q (R₀ + i) (R₀ + l) ≤
      -(1 / Real.sqrt L) * ∑ k ∈ Icc 2 Q, ω k *
        ∑ l ∈ Ico q₀ (q₀ + L), floorGraph k (R₀ + p₀) (R₀ + l) := by
    rw [hoff_eq, ← Finset.sum_sdiff hSP]
    have hrest : ∑ x ∈ P \ S, clusterVec p₀ q₀ L x.1 * clusterVec p₀ q₀ L x.2 *
        reweightedNeutral ω Q (R₀ + x.1) (R₀ + x.2) ≤ 0 :=
      Finset.sum_nonpos fun x hx =>
        hoff_nonpos x (Finset.mem_sdiff.mp hx).1 (Finset.mem_sdiff.mp hx).2
    linarith
  linarith

/-- Cross-pairing magnitude bound between two separated `clusterVec` packets on
`reweightedNeutral ω Q + a I`: the diagonal shift cancels identically, the off-diagonal jets sum to
at most `1 + (√L₁ + √L₂ + √(L₁ L₂)) * (2 / d)`, and the floor contacts enter linearly. -/
theorem abs_bilin_reweightedNeutral_clusterVec_le (ω : ℕ → ℝ)
    {R₀ Q J₀ p₁ q₁ L₁ p₂ q₂ L₂ d : ℕ} (hp : p₁ < p₂) (hpd : p₂ + d ≤ q₁)
    (hqd : q₁ + L₁ + d ≤ q₂) (hqJ : q₂ + L₂ ≤ J₀) (hd : 1 ≤ d) (hL₁ : 1 ≤ L₁) (hL₂ : 1 ≤ L₂)
    (a : ℝ) :
    |bilin (windowMatrix (reweightedNeutral ω Q) R₀ J₀ + Matrix.diagonal (fun _ : Fin J₀ => a))
        (fun i : Fin J₀ => clusterVec p₁ q₁ L₁ i)
        (fun j : Fin J₀ => clusterVec p₂ q₂ L₂ j)| ≤
      1 + (Real.sqrt L₁ + Real.sqrt L₂ + Real.sqrt ((L₁ : ℝ) * L₂)) * (2 / (d : ℝ)) +
        ∑ k ∈ Icc 2 Q, |ω k| *
          |∑ i ∈ range J₀, ∑ j ∈ range J₀,
            clusterVec p₁ q₁ L₁ i * clusterVec p₂ q₂ L₂ j * floorGraph k (R₀ + i) (R₀ + j)| := by
  rw [bilin_windowMatrix_add_diagonal_coe]
  have horth : ∑ i ∈ range J₀, clusterVec p₁ q₁ L₁ i * clusterVec p₂ q₂ L₂ i = 0 :=
    Finset.sum_eq_zero fun i _ => clusterVec_mul_eq_zero hp (by omega) (by omega) i
  rw [horth, mul_zero, add_zero]
  let jetTerm : ℕ → ℕ → ℝ := fun i j =>
    if i = j then 0 else blockJet (min (R₀ + i) (R₀ + j)) (max (R₀ + i) (R₀ + j))
  have hdecomp : ∑ i ∈ range J₀, ∑ j ∈ range J₀,
      clusterVec p₁ q₁ L₁ i * clusterVec p₂ q₂ L₂ j * reweightedNeutral ω Q (R₀ + i) (R₀ + j) =
      -(∑ i ∈ range J₀, ∑ j ∈ range J₀,
          clusterVec p₁ q₁ L₁ i * clusterVec p₂ q₂ L₂ j * jetTerm i j) -
        ∑ k ∈ Icc 2 Q, ω k * ∑ i ∈ range J₀, ∑ j ∈ range J₀,
          clusterVec p₁ q₁ L₁ i * clusterVec p₂ q₂ L₂ j * floorGraph k (R₀ + i) (R₀ + j) := by
    have hpt : ∀ i ∈ range J₀, ∀ j ∈ range J₀,
        clusterVec p₁ q₁ L₁ i * clusterVec p₂ q₂ L₂ j * reweightedNeutral ω Q (R₀ + i) (R₀ + j) =
          clusterVec p₁ q₁ L₁ i * clusterVec p₂ q₂ L₂ j *
            (-jetTerm i j + ∑ k ∈ Icc 2 Q, (-ω k) * floorGraph k (R₀ + i) (R₀ + j)) := by
      intro i _ j _
      rcases lt_trichotomy i j with hij | rfl | hji
      · have hlt : R₀ + i < R₀ + j := by omega
        simp only [jetTerm, hij.ne, ↓reduceIte, min_eq_left hlt.le, max_eq_right hlt.le,
          reweightedNeutral_of_lt ω Q hlt]
        congr 1; rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
        congr 1; exact Finset.sum_congr rfl fun k _ => by ring
      · rw [clusterVec_mul_eq_zero hp (by omega) (by omega) i, zero_mul, zero_mul]
      · have hlt : R₀ + j < R₀ + i := by omega
        have hcomm : ∑ k ∈ Icc 2 Q, (-ω k) * floorGraph k (R₀ + i) (R₀ + j) =
            ∑ k ∈ Icc 2 Q, (-ω k) * floorGraph k (R₀ + j) (R₀ + i) :=
          Finset.sum_congr rfl fun k _ => by rw [floorGraph_comm]
        simp only [jetTerm, hji.ne', ↓reduceIte, min_eq_right hlt.le, max_eq_left hlt.le]
        rw [reweightedNeutral_comm, reweightedNeutral_of_lt ω Q hlt, hcomm]
        congr 1; rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
        congr 1; exact Finset.sum_congr rfl fun k _ => by ring
    calc ∑ i ∈ range J₀, ∑ j ∈ range J₀,
          clusterVec p₁ q₁ L₁ i * clusterVec p₂ q₂ L₂ j * reweightedNeutral ω Q (R₀ + i) (R₀ + j)
        = ∑ i ∈ range J₀, ∑ j ∈ range J₀,
          clusterVec p₁ q₁ L₁ i * clusterVec p₂ q₂ L₂ j *
            (-jetTerm i j + ∑ k ∈ Icc 2 Q, (-ω k) * floorGraph k (R₀ + i) (R₀ + j)) :=
          Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => hpt i hi j hj
      _ = _ := by
          -- Bilinear version of `sum_form_add_sum`
          have hin : ∀ i ∈ range J₀,
              ∑ j ∈ range J₀, clusterVec p₁ q₁ L₁ i * clusterVec p₂ q₂ L₂ j *
                (-jetTerm i j + ∑ k ∈ Icc 2 Q, (-ω k) * floorGraph k (R₀ + i) (R₀ + j)) =
              -(∑ j ∈ range J₀, clusterVec p₁ q₁ L₁ i * clusterVec p₂ q₂ L₂ j * jetTerm i j) -
                ∑ k ∈ Icc 2 Q, ω k * ∑ j ∈ range J₀,
                  clusterVec p₁ q₁ L₁ i * clusterVec p₂ q₂ L₂ j * floorGraph k (R₀ + i) (R₀ + j) := by
            intro i _
            have h1 : ∀ j ∈ range J₀,
                clusterVec p₁ q₁ L₁ i * clusterVec p₂ q₂ L₂ j *
                  (-jetTerm i j + ∑ k ∈ Icc 2 Q, (-ω k) * floorGraph k (R₀ + i) (R₀ + j)) =
                -(clusterVec p₁ q₁ L₁ i * clusterVec p₂ q₂ L₂ j * jetTerm i j) -
                  ∑ k ∈ Icc 2 Q, ω k *
                    (clusterVec p₁ q₁ L₁ i * clusterVec p₂ q₂ L₂ j * floorGraph k (R₀ + i) (R₀ + j)) := by
              intro j _
              rw [mul_add, Finset.mul_sum]
              have hsum_neg : ∑ k ∈ Icc 2 Q,
                  clusterVec p₁ q₁ L₁ i * clusterVec p₂ q₂ L₂ j *
                    (-ω k * floorGraph k (R₀ + i) (R₀ + j)) =
                  -(∑ k ∈ Icc 2 Q, ω k *
                    (clusterVec p₁ q₁ L₁ i * clusterVec p₂ q₂ L₂ j *
                      floorGraph k (R₀ + i) (R₀ + j))) := by
                rw [← Finset.sum_neg_distrib]
                exact Finset.sum_congr rfl fun k _ => by ring
              rw [hsum_neg]
              ring
            rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
              Finset.sum_comm (t := Icc 2 Q)]
            congr 1
            exact Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
          rw [Finset.sum_congr rfl hin, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
            Finset.sum_comm (t := Icc 2 Q)]
          congr 1
          exact Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
  rw [hdecomp]
  have hjet_nonneg : 0 ≤ ∑ i ∈ range J₀, ∑ j ∈ range J₀,
      clusterVec p₁ q₁ L₁ i * clusterVec p₂ q₂ L₂ j * jetTerm i j := by
    refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
    refine mul_nonneg (mul_nonneg (clusterVec_nonneg _ _ _ _) (clusterVec_nonneg _ _ _ _)) ?_
    dsimp [jetTerm]
    split_ifs with hij
    · exact le_rfl
    · unfold blockJet
      have hlt : min (R₀ + i) (R₀ + j) < max (R₀ + i) (R₀ + j) := by omega
      linarith [xLogXDiff_pos (n := min (R₀ + i) (R₀ + j) + max (R₀ + i) (R₀ + j) + 1) (by omega),
        xLogXDiff_pos (n := max (R₀ + i) (R₀ + j) - min (R₀ + i) (R₀ + j)) (by omega)]
  have hjet_le : ∑ i ∈ range J₀, ∑ j ∈ range J₀,
      clusterVec p₁ q₁ L₁ i * clusterVec p₂ q₂ L₂ j * jetTerm i j ≤
      1 + (Real.sqrt L₁ + Real.sqrt L₂ + Real.sqrt ((L₁ : ℝ) * L₂)) * (2 / (d : ℝ)) := by
    -- Split `clusterVec` into singleton + `Ico` on both sides.
    have hsplit_vec : ∀ p₀ q₀ L, p₀ < q₀ → q₀ + L ≤ J₀ → ∀ f : ℕ → ℝ,
        ∑ i ∈ range J₀, clusterVec p₀ q₀ L i * f i =
          (1 / Real.sqrt 2) * f p₀ +
            (1 / Real.sqrt (2 * (L : ℝ))) * ∑ i ∈ Ico q₀ (q₀ + L), f i := by
      intro p₀ q₀ L hp0 hq0 f
      have hdisj : Disjoint ({p₀} : Finset ℕ) (Ico q₀ (q₀ + L)) := by
        rw [Finset.disjoint_left]
        intro i hi1 hi2; rw [Finset.mem_singleton] at hi1; have := (Finset.mem_Ico.mp hi2).1; omega
      have hsub : ({p₀} ∪ Ico q₀ (q₀ + L)) ⊆ range J₀ := by
        intro i hi
        rcases Finset.mem_union.mp hi with hi1 | hi2
        · rw [Finset.mem_singleton] at hi1; exact Finset.mem_range.mpr (by omega)
        · have := (Finset.mem_Ico.mp hi2).2; exact Finset.mem_range.mpr (by omega)
      rw [← Finset.sum_subset hsub]
      · rw [Finset.sum_union hdisj, Finset.sum_singleton, Finset.mul_sum]
        congr 1
        · simp [clusterVec]
        · refine Finset.sum_congr rfl fun i hi => ?_
          rcases Finset.mem_Ico.mp hi with ⟨h1, h2⟩
          have hne : i ≠ p₀ := by omega
          simp [clusterVec, hne, h1, h2]
      · intro i _ hinot
        rw [Finset.mem_union, Finset.mem_singleton, Finset.mem_Ico, not_or] at hinot
        simp [clusterVec, hinot.1, hinot.2]
    have hlhs : ∑ i ∈ range J₀, ∑ j ∈ range J₀,
        clusterVec p₁ q₁ L₁ i * clusterVec p₂ q₂ L₂ j * jetTerm i j =
        (1 / Real.sqrt 2) * ((1 / Real.sqrt 2) * jetTerm p₁ p₂ +
            (1 / Real.sqrt (2 * (L₂ : ℝ))) * ∑ j ∈ Ico q₂ (q₂ + L₂), jetTerm p₁ j) +
          (1 / Real.sqrt (2 * (L₁ : ℝ))) * ∑ i ∈ Ico q₁ (q₁ + L₁),
            ((1 / Real.sqrt 2) * jetTerm i p₂ +
              (1 / Real.sqrt (2 * (L₂ : ℝ))) * ∑ j ∈ Ico q₂ (q₂ + L₂), jetTerm i j) := by
      have hin : ∀ i, ∑ j ∈ range J₀,
          clusterVec p₁ q₁ L₁ i * clusterVec p₂ q₂ L₂ j * jetTerm i j =
          clusterVec p₁ q₁ L₁ i * ∑ j ∈ range J₀, clusterVec p₂ q₂ L₂ j * jetTerm i j := by
        intro i; rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      simp_rw [hin, hsplit_vec p₂ q₂ L₂ (by omega) hqJ]
      exact hsplit_vec p₁ q₁ L₁ (by omega) (by omega) _
    rw [hlhs]
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
    have hjet_d : ∀ i j, i ≠ j → d ≤ max i j - min i j → jetTerm i j ≤ 2 / (d : ℝ) := by
      intro i j hne hgap
      dsimp [jetTerm]
      rw [if_neg hne]
      have hlt : min (R₀ + i) (R₀ + j) < max (R₀ + i) (R₀ + j) := by omega
      have h1 := blockJet_le_two_div hlt
      have hdiff : d ≤ max (R₀ + i) (R₀ + j) - min (R₀ + i) (R₀ + j) := by omega
      exact h1.trans (div_le_div_of_nonneg_left zero_le_two hdpos (by exact_mod_cast hdiff))
    have ht1 : (1 / Real.sqrt 2) * ((1 / Real.sqrt 2) * jetTerm p₁ p₂) ≤ 1 := by
      have hj12 : jetTerm p₁ p₂ ≤ 2 := by
        dsimp [jetTerm]
        rw [if_neg hp.ne]
        have hlt : R₀ + p₁ < R₀ + p₂ := by omega
        rw [min_eq_left hlt.le, max_eq_right hlt.le]
        exact (blockJet_le_two_div hlt).trans
          ((div_le_iff₀ (by exact_mod_cast (show 0 < R₀ + p₂ - (R₀ + p₁) by omega))).mpr
            (by have : (1 : ℝ) ≤ ((R₀ + p₂ - (R₀ + p₁) : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ R₀ + p₂ - (R₀ + p₁))
                linarith))
      have hs2 : (1 / Real.sqrt 2) * (1 / Real.sqrt 2) = (1 / 2 : ℝ) := by
        rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt zero_le_two]
      nlinarith
    have hL₁pos : (0 : ℝ) < L₁ := by exact_mod_cast hL₁
    have hL₂pos : (0 : ℝ) < L₂ := by exact_mod_cast hL₂
    have ht2 : (1 / Real.sqrt 2) *
        ((1 / Real.sqrt (2 * (L₂ : ℝ))) * ∑ j ∈ Ico q₂ (q₂ + L₂), jetTerm p₁ j) ≤
        Real.sqrt L₂ * (2 / (d : ℝ)) := by
      have hsum : ∑ j ∈ Ico q₂ (q₂ + L₂), jetTerm p₁ j ≤ (L₂ : ℝ) * (2 / (d : ℝ)) := by
        calc ∑ j ∈ Ico q₂ (q₂ + L₂), jetTerm p₁ j
            ≤ ∑ _j ∈ Ico q₂ (q₂ + L₂), 2 / (d : ℝ) := by
              refine Finset.sum_le_sum fun j hj => ?_
              have hj1 := (Finset.mem_Ico.mp hj).1
              exact hjet_d p₁ j (by omega) (by omega)
          _ = (L₂ : ℝ) * (2 / (d : ℝ)) := by simp [Nat.card_Ico, nsmul_eq_mul]
      have hcoef : (1 / Real.sqrt 2) * (1 / Real.sqrt (2 * (L₂ : ℝ))) * (L₂ : ℝ) =
          Real.sqrt L₂ / 2 := by
        rw [Real.sqrt_mul zero_le_two]
        have hs2_ne : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr zero_lt_two).ne'
        have hsL_ne : Real.sqrt (L₂ : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hL₂pos).ne'
        field_simp [hs2_ne, hsL_ne]
        rw [Real.sq_sqrt zero_le_two, Real.sq_sqrt hL₂pos.le]
        ring
      calc (1 / Real.sqrt 2) *
            ((1 / Real.sqrt (2 * (L₂ : ℝ))) * ∑ j ∈ Ico q₂ (q₂ + L₂), jetTerm p₁ j)
          ≤ (1 / Real.sqrt 2) * ((1 / Real.sqrt (2 * (L₂ : ℝ))) * ((L₂ : ℝ) * (2 / (d : ℝ)))) := by
            gcongr
        _ = (Real.sqrt L₂ / 2) * (2 / (d : ℝ)) := by rw [← mul_assoc, ← mul_assoc, hcoef]
        _ ≤ Real.sqrt L₂ * (2 / (d : ℝ)) := by
            nlinarith [Real.sqrt_nonneg L₂, show (0 : ℝ) ≤ 2 / d by positivity]
    have ht3 : (1 / Real.sqrt (2 * (L₁ : ℝ))) * ∑ i ∈ Ico q₁ (q₁ + L₁),
        ((1 / Real.sqrt 2) * jetTerm i p₂ +
          (1 / Real.sqrt (2 * (L₂ : ℝ))) * ∑ j ∈ Ico q₂ (q₂ + L₂), jetTerm i j) ≤
        (Real.sqrt L₁ + Real.sqrt ((L₁ : ℝ) * L₂)) * (2 / (d : ℝ)) := by
      have hin_le : ∀ i ∈ Ico q₁ (q₁ + L₁),
          (1 / Real.sqrt 2) * jetTerm i p₂ +
            (1 / Real.sqrt (2 * (L₂ : ℝ))) * ∑ j ∈ Ico q₂ (q₂ + L₂), jetTerm i j ≤
          ((1 / Real.sqrt 2) + (L₂ : ℝ) / Real.sqrt (2 * (L₂ : ℝ))) * (2 / (d : ℝ)) := by
        intro i hi
        rcases Finset.mem_Ico.mp hi with ⟨hi1, hi2⟩
        have h1 := hjet_d i p₂ (by omega) (by omega)
        have h2 : ∑ j ∈ Ico q₂ (q₂ + L₂), jetTerm i j ≤ (L₂ : ℝ) * (2 / (d : ℝ)) := by
          calc ∑ j ∈ Ico q₂ (q₂ + L₂), jetTerm i j
              ≤ ∑ _j ∈ Ico q₂ (q₂ + L₂), 2 / (d : ℝ) := by
                refine Finset.sum_le_sum fun j hj => ?_
                have hj1 := (Finset.mem_Ico.mp hj).1
                exact hjet_d i j (by omega) (by omega)
            _ = (L₂ : ℝ) * (2 / (d : ℝ)) := by simp [Nat.card_Ico, nsmul_eq_mul]
        have hc1 : 0 ≤ (1 / Real.sqrt 2 : ℝ) := by positivity
        have hc2 : 0 ≤ (1 / Real.sqrt (2 * (L₂ : ℝ)) : ℝ) := by positivity
        calc (1 / Real.sqrt 2) * jetTerm i p₂ +
              (1 / Real.sqrt (2 * (L₂ : ℝ))) * ∑ j ∈ Ico q₂ (q₂ + L₂), jetTerm i j
            ≤ (1 / Real.sqrt 2) * (2 / (d : ℝ)) +
              (1 / Real.sqrt (2 * (L₂ : ℝ))) * ((L₂ : ℝ) * (2 / (d : ℝ))) :=
              add_le_add (mul_le_mul_of_nonneg_left h1 hc1) (mul_le_mul_of_nonneg_left h2 hc2)
          _ = ((1 / Real.sqrt 2) + (L₂ : ℝ) / Real.sqrt (2 * (L₂ : ℝ))) * (2 / (d : ℝ)) := by ring
      have hsum_i : ∑ i ∈ Ico q₁ (q₁ + L₁),
          ((1 / Real.sqrt 2) * jetTerm i p₂ +
            (1 / Real.sqrt (2 * (L₂ : ℝ))) * ∑ j ∈ Ico q₂ (q₂ + L₂), jetTerm i j) ≤
          (L₁ : ℝ) * (((1 / Real.sqrt 2) + (L₂ : ℝ) / Real.sqrt (2 * (L₂ : ℝ))) * (2 / (d : ℝ))) := by
        calc ∑ i ∈ Ico q₁ (q₁ + L₁), _
            ≤ ∑ _i ∈ Ico q₁ (q₁ + L₁),
                ((1 / Real.sqrt 2) + (L₂ : ℝ) / Real.sqrt (2 * (L₂ : ℝ))) * (2 / (d : ℝ)) :=
              Finset.sum_le_sum hin_le
          _ = _ := by simp [Nat.card_Ico, nsmul_eq_mul]
      have hcoef : (1 / Real.sqrt (2 * (L₁ : ℝ))) * (L₁ : ℝ) *
          ((1 / Real.sqrt 2) + (L₂ : ℝ) / Real.sqrt (2 * (L₂ : ℝ))) =
          (Real.sqrt L₁ + Real.sqrt ((L₁ : ℝ) * L₂)) / 2 := by
        simp_rw [Real.sqrt_mul zero_le_two]
        rw [Real.sqrt_mul hL₁pos.le]
        have hs2_ne : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr zero_lt_two).ne'
        have hsL₁_ne : Real.sqrt (L₁ : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hL₁pos).ne'
        have hsL₂_ne : Real.sqrt (L₂ : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hL₂pos).ne'
        field_simp [hs2_ne, hsL₁_ne, hsL₂_ne]
        rw [Real.sq_sqrt zero_le_two, Real.sq_sqrt hL₁pos.le, Real.sq_sqrt hL₂pos.le]
        ring
      calc (1 / Real.sqrt (2 * (L₁ : ℝ))) * ∑ i ∈ Ico q₁ (q₁ + L₁), _
          ≤ (1 / Real.sqrt (2 * (L₁ : ℝ))) *
              ((L₁ : ℝ) * (((1 / Real.sqrt 2) + (L₂ : ℝ) / Real.sqrt (2 * (L₂ : ℝ))) * (2 / (d : ℝ)))) :=
            mul_le_mul_of_nonneg_left hsum_i (by positivity)
        _ = ((Real.sqrt L₁ + Real.sqrt ((L₁ : ℝ) * L₂)) / 2) * (2 / (d : ℝ)) := by
            rw [← mul_assoc, ← mul_assoc, hcoef]
        _ ≤ (Real.sqrt L₁ + Real.sqrt ((L₁ : ℝ) * L₂)) * (2 / (d : ℝ)) := by
            nlinarith [Real.sqrt_nonneg L₁, Real.sqrt_nonneg ((L₁ : ℝ) * L₂),
              show (0 : ℝ) ≤ 2 / d by positivity]
    rw [mul_add]
    linarith
  have htri : |-(∑ i ∈ range J₀, ∑ j ∈ range J₀,
        clusterVec p₁ q₁ L₁ i * clusterVec p₂ q₂ L₂ j * jetTerm i j) -
      ∑ k ∈ Icc 2 Q, ω k * ∑ i ∈ range J₀, ∑ j ∈ range J₀,
        clusterVec p₁ q₁ L₁ i * clusterVec p₂ q₂ L₂ j * floorGraph k (R₀ + i) (R₀ + j)| ≤
      |∑ i ∈ range J₀, ∑ j ∈ range J₀,
        clusterVec p₁ q₁ L₁ i * clusterVec p₂ q₂ L₂ j * jetTerm i j| +
      ∑ k ∈ Icc 2 Q, |ω k| * |∑ i ∈ range J₀, ∑ j ∈ range J₀,
        clusterVec p₁ q₁ L₁ i * clusterVec p₂ q₂ L₂ j * floorGraph k (R₀ + i) (R₀ + j)| := by
    rw [← neg_add', abs_neg]
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [abs_mul]
  rw [abs_of_nonneg hjet_nonneg] at htri
  linarith

/-! ### 4.1 The gluing-indistinguishable sub-Euler countermodel -/

/-- Prime predicate for `subEulerGluingWeight Q₀`: all primes up to `Q₀`, together with the sparse
bands `(256^m, 3 · 256^m]` (`m ≥ 1`). -/
def subEulerPrimePred (Q₀ p : ℕ) : Prop :=
  p ≤ Q₀ ∨ ∃ m : ℕ, 1 ≤ m ∧ 256 ^ m < p ∧ p ≤ 3 * 256 ^ m

/-- **Gluing-indistinguishable sub-Euler contact weight**: `ω(k) ∈ {0, 1}` equals `1` at `k = 1`
and whenever `k.minFac` satisfies `subEulerPrimePred Q₀`, ensuring exact prime-power constancy
`ω(p^r) = ω(p)` (`r ≥ 1`) and `ω(k) = 1` for all `1 ≤ k ≤ Q₀`. -/
def subEulerGluingWeight (Q₀ k : ℕ) : ℝ :=
  open Classical in if k = 1 ∨ subEulerPrimePred Q₀ k.minFac then 1 else 0

theorem subEulerGluingWeight_nonneg (Q₀ k : ℕ) : 0 ≤ subEulerGluingWeight Q₀ k := by
  unfold subEulerGluingWeight; split_ifs <;> norm_num

theorem subEulerGluingWeight_le_one (Q₀ k : ℕ) : subEulerGluingWeight Q₀ k ≤ 1 := by
  unfold subEulerGluingWeight; split_ifs <;> norm_num

theorem abs_subEulerGluingWeight_le_one (Q₀ k : ℕ) : |subEulerGluingWeight Q₀ k| ≤ 1 := by
  rw [abs_of_nonneg (subEulerGluingWeight_nonneg Q₀ k)]
  exact subEulerGluingWeight_le_one Q₀ k

/-- **Finite-prefix agreement**: `subEulerGluingWeight Q₀ k = 1` for all `1 ≤ k ≤ Q₀`. -/
theorem subEulerGluingWeight_eq_one_of_le {Q₀ k : ℕ} (hk1 : 1 ≤ k) (hkQ : k ≤ Q₀) :
    subEulerGluingWeight Q₀ k = 1 := by
  unfold subEulerGluingWeight subEulerPrimePred
  rcases eq_or_lt_of_le hk1 with rfl | hk2
  · rw [if_pos (Or.inl rfl)]
  · rw [if_pos (Or.inr (Or.inl ((Nat.minFac_le (by omega)).trans hkQ)))]

/-- **Sub-Euler prime-power constancy**: `subEulerGluingWeight Q₀ (p^r) = subEulerGluingWeight Q₀ p`
for every prime `p` and every `r ≥ 1`. -/
theorem subEulerGluingWeight_prime_pow {Q₀ p r : ℕ} (hp : p.Prime) (hr : 1 ≤ r) :
    subEulerGluingWeight Q₀ (p ^ r) = subEulerGluingWeight Q₀ p := by
  have hp2 := hp.two_le
  have hpr_gt : 1 < p ^ r := one_lt_pow₀ hp.one_lt (by omega)
  have hmin_pow : (p ^ r).minFac = p := by
    have hmf_prime : (p ^ r).minFac.Prime := Nat.minFac_prime hpr_gt.ne'
    have hdvd : (p ^ r).minFac ∣ p := hmf_prime.dvd_of_dvd_pow (Nat.minFac_dvd _)
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | hself
    · exact absurd h1 hmf_prime.ne_one
    · exact hself
  unfold subEulerGluingWeight
  rw [hmin_pow, hp.minFac_eq]
  have hne1 : p ^ r ≠ 1 := hpr_gt.ne'
  have hne2 : p ≠ 1 := hp.ne_one
  simp only [hne1, hne2, false_or]

/-- Every prime in the band `(256^m, 3 · 256^m]` (`m ≥ 1`) has `subEulerGluingWeight Q₀ p = 1`. -/
theorem subEulerGluingWeight_eq_one_of_mem_band {Q₀ m p : ℕ} (hm : 1 ≤ m) (hp : p.Prime)
    (hlo : 256 ^ m < p) (hhi : p ≤ 3 * 256 ^ m) :
    subEulerGluingWeight Q₀ p = 1 := by
  unfold subEulerGluingWeight subEulerPrimePred
  rw [hp.minFac_eq, if_pos (Or.inr (Or.inr ⟨m, hm, hlo, hhi⟩))]

/-- **Exact finite-prefix window indistinguishability**: up to cutoff `Q₀`, all neutral and block
windows of `subEulerGluingWeight Q₀` coincide entry-for-entry with those of `ζ`. -/
theorem windowMatrix_subEulerGluingWeight_eq_neutralWindow {Q₀ Q R J : ℕ} (hQ : Q ≤ Q₀) :
    windowMatrix (reweightedNeutral (subEulerGluingWeight Q₀) Q) R J = neutralWindow Q R J := by
  ext i j
  simp only [neutralWindow, windowMatrix, Matrix.of_apply, reweightedNeutral]
  have hz : ∑ k ∈ Icc 2 Q, (1 - subEulerGluingWeight Q₀ k) * floorGraph k (R + i) (R + j) = 0 :=
    Finset.sum_eq_zero fun k hk => by
      rcases Finset.mem_Icc.mp hk with ⟨hk2, hkQ⟩
      rw [subEulerGluingWeight_eq_one_of_le (by omega) (hkQ.trans hQ), sub_self, zero_mul]
  rw [hz, add_zero]

/-- Explicit `ψ - θ` bound `ψ x - θ x ≤ 3 (log 4 + 4) √x` for all `x : ℝ`. -/
lemma psi_sub_theta_le_three_mul_sqrt (x : ℝ) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 3 * (Real.log 4 + 4) * Real.sqrt x := by
  rcases le_total x 1 with hx | hx
  · rw [Chebyshev.theta_eq_zero_of_le_one hx, Chebyshev.psi_eq_zero_of_le_one hx, sub_self]
    positivity
  · have hbound : ∀ n : ℕ, 2 ≤ n →
        Chebyshev.psi (x ^ (n : ℝ)⁻¹) ≤ (Real.log 4 + 4) * Real.sqrt x := by
      intro n hn
      have hx0 : 0 ≤ x := by linarith
      calc Chebyshev.psi (x ^ (n : ℝ)⁻¹)
          ≤ (Real.log 4 + 4) * x ^ (n : ℝ)⁻¹ := Chebyshev.psi_le_const_mul_self (by positivity)
        _ ≤ (Real.log 4 + 4) * Real.sqrt x := by
            rw [Real.sqrt_eq_rpow]
            refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx ?_)
              (by have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); positivity)
            rw [one_div]
            exact inv_anti₀ zero_lt_two (by exact_mod_cast hn)
    linarith [Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x, hbound 2 le_rfl,
      hbound 3 (by norm_num), hbound 5 (by norm_num)]

/-- **Elementary Chebyshev lower bound on `(N, 3N]`**: along `N = 256^m` (`m ≥ 4`),
`∑_{p ∈ (N, 3N], p.Prime} log p ≥ N / 2`. -/
theorem sum_prime_log_band_ge {m : ℕ} (hm : 4 ≤ m) :
    ((256 ^ m : ℕ) : ℝ) / 2 ≤
      ∑ p ∈ (Ioc (256 ^ m) (3 * 256 ^ m)).filter Nat.Prime, Real.log p := by
  set N : ℕ := 256 ^ m
  have hN_pos : 0 < N := pow_pos (by norm_num) m
  have hN_ge : 256 ^ 4 ≤ N := Nat.pow_le_pow_right (by norm_num) hm
  have hdiff_eq : Chebyshev.theta ((3 * N : ℕ) : ℝ) - Chebyshev.theta (N : ℝ) =
      ∑ p ∈ (Ioc N (3 * N)).filter Nat.Prime, Real.log p := by
    rw [Chebyshev.theta, Chebyshev.theta, Nat.floor_natCast, Nat.floor_natCast]
    have hsub : (Ioc 0 N).filter Nat.Prime ⊆ (Ioc 0 (3 * N)).filter Nat.Prime :=
      Finset.filter_subset_filter _ (Finset.Ioc_subset_Ioc_right (by omega))
    rw [← Finset.sum_sdiff hsub]
    have hsdiff : (Ioc 0 (3 * N)).filter Nat.Prime \ (Ioc 0 N).filter Nat.Prime =
        (Ioc N (3 * N)).filter Nat.Prime := by
      ext p
      simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Ioc]
      constructor
      · rintro ⟨⟨⟨hp0, hp3⟩, hp⟩, hnot⟩
        exact ⟨⟨by by_contra h; exact hnot ⟨⟨hp0, not_lt.mp h⟩, hp⟩, hp3⟩, hp⟩
      · rintro ⟨⟨hpN, hp3⟩, hp⟩
        exact ⟨⟨⟨by omega, hp3⟩, hp⟩, fun h => by omega⟩
    rw [hsdiff]; ring
  rw [← hdiff_eq]
  have hlo := Chebyshev.theta_ge (3 * N)
  have hhi := Chebyshev.theta_le_log4_mul_x (x := (N : ℝ)) (Nat.cast_nonneg N)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow, Nat.cast_ofNat]
  -- Bound `log(3N + 1)` and `2 √(3N) log(3N)` explicitly using `N ≥ 256^4`.
  have hNR : (4294967296 : ℝ) ≤ (N : ℝ) := by
    have : (4294967296 : ℕ) ≤ N := (by norm_num : 4294967296 ≤ 256 ^ 4).trans hN_ge
    exact_mod_cast this
  have h3N_pos : (0 : ℝ) < ((3 * N : ℕ) : ℝ) := by positivity
  have hl1 : Real.log (((3 * N : ℕ) : ℝ) + 1) ≤ (1 / 100 : ℝ) * N := by
    have h1 := log_le_eps_mul_sqrt_add (x := ((3 * N : ℕ) : ℝ) + 1) (ε := 1 / 400)
      (by positivity) (by norm_num)
    have hsq : Real.sqrt (((3 * N : ℕ) : ℝ) + 1) ≤ 2 * Real.sqrt N := by
      rw [← Real.sqrt_sq zero_le_two, ← Real.sqrt_mul (by norm_num)]
      refine Real.sqrt_le_sqrt ?_
      push_cast; linarith
    have hsN_le : Real.sqrt N ≤ (N : ℝ) / 65536 := by
      have hsq65 : (65536 : ℝ) ^ 2 ≤ N := by linarith
      have h65 : (65536 : ℝ) ≤ Real.sqrt N := by
        rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 65536)]
        exact Real.sqrt_le_sqrt hsq65
      have hmul : 65536 * Real.sqrt N ≤ Real.sqrt N * Real.sqrt N :=
        mul_le_mul_of_nonneg_right h65 (Real.sqrt_nonneg N)
      rw [Real.mul_self_sqrt (Nat.cast_nonneg N)] at hmul
      linarith
    linarith
  have hl2 : 2 * Real.sqrt ((3 * N : ℕ) : ℝ) * Real.log ((3 * N : ℕ) : ℝ) ≤
      (1 / 10 : ℝ) * N := by
    have hlog := log_le_eps_mul_sqrt_add (x := ((3 * N : ℕ) : ℝ)) (ε := 1 / 100)
      h3N_pos (by norm_num)
    have hs3 : Real.sqrt ((3 * N : ℕ) : ℝ) ≤ 2 * Real.sqrt N := by
      rw [← Real.sqrt_sq zero_le_two, ← Real.sqrt_mul (by norm_num)]
      refine Real.sqrt_le_sqrt ?_
      push_cast; linarith
    have hsN_sq : Real.sqrt ((3 * N : ℕ) : ℝ) * Real.sqrt ((3 * N : ℕ) : ℝ) = 3 * (N : ℝ) := by
      rw [Real.mul_self_sqrt (Nat.cast_nonneg _)]; push_cast; rfl
    have hsN_le : Real.sqrt N ≤ (N : ℝ) / 65536 := by
      have hsq65 : (65536 : ℝ) ^ 2 ≤ N := by linarith
      have h65 : (65536 : ℝ) ≤ Real.sqrt N := by
        rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 65536)]
        exact Real.sqrt_le_sqrt hsq65
      have hmul : 65536 * Real.sqrt N ≤ Real.sqrt N * Real.sqrt N :=
        mul_le_mul_of_nonneg_right h65 (Real.sqrt_nonneg N)
      rw [Real.mul_self_sqrt (Nat.cast_nonneg N)] at hmul
      linarith
    have hprod : 2 * Real.sqrt ((3 * N : ℕ) : ℝ) * Real.log ((3 * N : ℕ) : ℝ) ≤
        2 * Real.sqrt ((3 * N : ℕ) : ℝ) *
          ((1 / 100) * Real.sqrt ((3 * N : ℕ) : ℝ) + 4 / (1 / 100)) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    nlinarith
  have hlog2N : (69 / 100 : ℝ) * N ≤ (N : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_left (by linarith [Real.log_two_gt_d9]) (Nat.cast_nonneg N)
  have h3N_mul : ((3 * N : ℕ) : ℝ) * Real.log 2 = 3 * ((N : ℝ) * Real.log 2) := by
    push_cast; ring
  have hlog4_mul : Real.log 4 * (N : ℝ) = 2 * ((N : ℝ) * Real.log 2) := by
    rw [hlog4]; ring
  linarith [hlo, hhi, hl1, hl2, hlog2N, h3N_mul, hlog4_mul]

/-- Explicit cross-magnitude constant for the two-cluster witness of `subEulerGluingWeight`. -/
def subEulerCrossConst : ℝ :=
  73 + 5 * floorContactSqrtConst + 90 * (Real.log 4 + 4)

/-- Lower bound on the prime-band floor attraction on `(1 + p₀)` to `[1 + q₀, 1 + q₀ + L)` for
`subEulerGluingWeight Q₀` at scale `N = 256^m` (`m ≥ 4`). -/
private lemma subEuler_fiber_sum_ge (Q₀ : ℕ) {m p₀ q₀ L : ℕ} (hm : 4 ≤ m)
    (hinc : ∀ p ∈ (Ioc (256 ^ m) (3 * 256 ^ m)).filter Nat.Prime,
      1 + q₀ ≤ p * (1 + p₀) ∧ p * (1 + p₀) + p ≤ 1 + q₀ + L) :
    ((256 ^ m : ℕ) : ℝ) / 2 ≤
      ∑ k ∈ Icc 2 (3 * (8 * 256 ^ m) + 1), subEulerGluingWeight Q₀ k *
        ∑ l ∈ Ico q₀ (q₀ + L), floorGraph k (1 + p₀) (1 + l) := by
  have hsubP : (Ioc (256 ^ m) (3 * 256 ^ m)).filter Nat.Prime ⊆ Icc 2 (3 * (8 * 256 ^ m) + 1) := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpI, hpP⟩
    have hp3 := (Finset.mem_Ioc.mp hpI).2
    exact Finset.mem_Icc.mpr ⟨hpP.two_le, by omega⟩
  have hnonneg_k : ∀ k ∈ Icc 2 (3 * (8 * 256 ^ m) + 1),
      k ∉ (Ioc (256 ^ m) (3 * 256 ^ m)).filter Nat.Prime →
      0 ≤ subEulerGluingWeight Q₀ k * ∑ l ∈ Ico q₀ (q₀ + L), floorGraph k (1 + p₀) (1 + l) := by
    intro k _ _
    refine mul_nonneg (subEulerGluingWeight_nonneg Q₀ k) (Finset.sum_nonneg fun l _ => ?_)
    unfold floorGraph; split_ifs
    · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k)
    · exact le_rfl
  refine (sum_prime_log_band_ge hm).trans ((Finset.sum_le_sum fun p hp => ?_).trans
    (Finset.sum_le_sum_of_subset_of_nonneg hsubP hnonneg_k))
  rcases Finset.mem_filter.mp hp with ⟨hpI, hpP⟩
  rcases Finset.mem_Ioc.mp hpI with ⟨hp_lo, hp_hi⟩
  rw [subEulerGluingWeight_eq_one_of_mem_band (by omega) hpP hp_lo hp_hi, one_mul]
  obtain ⟨hb1, hb2⟩ := hinc p hp
  have hpos_pm : 1 ≤ p * (1 + p₀) := Nat.mul_pos hpP.pos (by omega)
  have hF_sub : Ico (p * (1 + p₀) - 1) (p * (1 + p₀) - 1 + p) ⊆ Ico q₀ (q₀ + L) := by
    intro l hl
    rcases Finset.mem_Ico.mp hl with ⟨hl1, hl2⟩
    exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  have hF_val : ∑ l ∈ Ico (p * (1 + p₀) - 1) (p * (1 + p₀) - 1 + p),
      floorGraph p (1 + p₀) (1 + l) = Real.log p := by
    have hterm : ∀ l ∈ Ico (p * (1 + p₀) - 1) (p * (1 + p₀) - 1 + p),
        floorGraph p (1 + p₀) (1 + l) = Real.log p / p := by
      intro l hl
      rcases Finset.mem_Ico.mp hl with ⟨hl1, hl2⟩
      have h1l : p * (1 + p₀) ≤ 1 + l := by omega
      have h2l : 1 + l < (1 + p₀ + 1) * p := by
        calc 1 + l < p * (1 + p₀) + p := by omega
          _ = (1 + p₀ + 1) * p := by ring
      have hdiv : (1 + l) / p = 1 + p₀ := by
        refine le_antisymm ?_ ?_
        · exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hpP.pos).mpr h2l)
        · exact (Nat.le_div_iff_mul_le hpP.pos).mpr (by rw [mul_comm]; exact h1l)
      have hle_pl : 1 + p₀ ≤ 1 + l := by
        have hp2 := hpP.two_le
        calc 1 + p₀ ≤ 2 * (1 + p₀) := by omega
          _ ≤ p * (1 + p₀) := Nat.mul_le_mul_right _ hp2
          _ ≤ 1 + l := h1l
      rw [floorGraph_of_le p hle_pl, if_pos hdiv, ArithmeticFunction.vonMangoldt_apply_prime hpP]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Nat.card_Ico, Nat.add_sub_cancel_left,
      nsmul_eq_mul]
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast hpP.pos
    field_simp [hp_pos.ne']
  rw [← hF_val]
  refine Finset.sum_le_sum_of_subset_of_nonneg hF_sub fun l _ _ => ?_
  unfold floorGraph; split_ifs
  · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg p)
  · exact le_rfl

/-- Jet cross-term bound `≤ 73` for the separated cluster pair at any scale `N ≥ 256`. -/
private lemma subEuler_jet_cross_bound {N : ℕ} (hN : 256 ≤ N) :
    1 + (Real.sqrt ((5 * N : ℕ) : ℝ) + Real.sqrt ((17 * N : ℕ) : ℝ) +
      Real.sqrt (((5 * N : ℕ) : ℝ) * ((17 * N : ℕ) : ℝ))) * (2 / ((N / 2 : ℕ) : ℝ)) ≤ 73 := by
  have hN_pos_r : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hd_pos : (0 : ℝ) < ((N / 2 : ℕ) : ℝ) := by exact_mod_cast (show 0 < N / 2 by omega)
  have hdiv_le : 2 / ((N / 2 : ℕ) : ℝ) ≤ 6 / (N : ℝ) := by
    rw [div_le_div_iff₀ hd_pos hN_pos_r]
    have h1 : (N : ℝ) ≤ 3 * ((N / 2 : ℕ) : ℝ) := by
      exact_mod_cast (show N ≤ 3 * (N / 2) by omega)
    linarith
  have hs85 : Real.sqrt (((5 * N : ℕ) : ℝ) * ((17 * N : ℕ) : ℝ)) ≤ 10 * (N : ℝ) := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 10 * N)]
    refine Real.sqrt_le_sqrt ?_
    push_cast; nlinarith
  have hsN_N : 8 * Real.sqrt N ≤ 2 * (N : ℝ) := by
    have h16 : (16 : ℝ) ≤ Real.sqrt N := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 16)]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hN)
    have hmul := mul_le_mul_of_nonneg_right h16 (Real.sqrt_nonneg N)
    rw [Real.mul_self_sqrt hN_pos_r.le] at hmul
    linarith
  have hs5 : Real.sqrt ((5 * N : ℕ) : ℝ) ≤ 3 * Real.sqrt N := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.sqrt_mul (by norm_num)]
    refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hs17 : Real.sqrt ((17 * N : ℕ) : ℝ) ≤ 5 * Real.sqrt N := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.sqrt_mul (by norm_num)]
    refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 5)]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsum_s : Real.sqrt ((5 * N : ℕ) : ℝ) + Real.sqrt ((17 * N : ℕ) : ℝ) +
      Real.sqrt (((5 * N : ℕ) : ℝ) * ((17 * N : ℕ) : ℝ)) ≤ 12 * (N : ℝ) := by
    linarith [hs85, hsN_N, hs5, hs17]
  have hmul : (Real.sqrt ((5 * N : ℕ) : ℝ) + Real.sqrt ((17 * N : ℕ) : ℝ) +
      Real.sqrt (((5 * N : ℕ) : ℝ) * ((17 * N : ℕ) : ℝ))) * (2 / ((N / 2 : ℕ) : ℝ)) ≤
      (12 * (N : ℝ)) * (6 / (N : ℝ)) :=
    mul_le_mul hsum_s hdiv_le (by positivity) (by positivity)
  have heq72 : (12 * (N : ℝ)) * (6 / (N : ℝ)) = 72 := by
    field_simp [hN_pos_r.ne']; ring
  linarith [hmul, heq72]

/-- Support geometry of cross-contacts between `clusterVec 0 (N - 1) (5 * N)` and
`clusterVec 6 (7 * N - 1) (17 * N)` for `k ≥ 25` (`N ≥ 1000`). -/
private lemma subEuler_support_out {N k : ℕ} (hN : 1000 ≤ N) (hk25 : 25 ≤ k)
    (hsum_ne : ∑ i ∈ range (3 * (8 * N)), ∑ j ∈ range (3 * (8 * N)),
      clusterVec 0 (N - 1) (5 * N) i * clusterVec 6 (7 * N - 1) (17 * N) j *
        floorGraph k (1 + i) (1 + j) ≠ 0) :
    N < 8 * k ∧ k ≤ 24 * N ∧ ¬(N < k ∧ k ≤ 3 * N) := by
  obtain ⟨i, _, hj_ex⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum_ne
  obtain ⟨j, _, hij_ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hj_ex
  have hui : clusterVec 0 (N - 1) (5 * N) i ≠ 0 := fun h => hij_ne (by rw [h, zero_mul, zero_mul])
  have hvj : clusterVec 6 (7 * N - 1) (17 * N) j ≠ 0 :=
    fun h => hij_ne (by rw [h, mul_zero, zero_mul])
  have hfg : floorGraph k (1 + i) (1 + j) ≠ 0 := fun h => hij_ne (by rw [h, mul_zero])
  have hi_supp : i = 0 ∨ (N - 1 ≤ i ∧ i < 6 * N - 1) := by
    unfold clusterVec at hui
    by_cases h0 : i = 0
    · exact Or.inl h0
    · rw [if_neg h0] at hui
      by_cases hI : N - 1 ≤ i ∧ i < N - 1 + 5 * N
      · exact Or.inr ⟨hI.1, by omega⟩
      · rw [if_neg hI] at hui; exact absurd rfl hui
  have hj_supp : j = 6 ∨ (7 * N - 1 ≤ j ∧ j < 24 * N - 1) := by
    unfold clusterVec at hvj
    by_cases h6 : j = 6
    · exact Or.inl h6
    · rw [if_neg h6] at hvj
      by_cases hJ : 7 * N - 1 ≤ j ∧ j < 7 * N - 1 + 17 * N
      · exact Or.inr ⟨hJ.1, by omega⟩
      · rw [if_neg hJ] at hvj; exact absurd rfl hvj
  rcases hi_supp with rfl | ⟨hi1, hi2⟩ <;> rcases hj_supp with rfl | ⟨hj1, hj2⟩
  · exfalso; exact hfg (floorGraph_eq_zero_of_lt_mul (by omega) (by omega) (by omega))
  · rw [floorGraph_of_le k (by omega)] at hfg
    have hdiv : (1 + j) / k = 1 := by by_contra h; exact hfg (if_neg h)
    have h1 := (Nat.le_div_iff_mul_le (by omega : 0 < k)).mp hdiv.ge
    have h2 := (Nat.div_lt_iff_lt_mul (by omega : 0 < k)).mp (show (1 + j) / k < 2 by omega)
    exact ⟨by omega, by omega, by omega⟩
  · rw [floorGraph_comm, floorGraph_of_le k (by omega)] at hfg
    have hdiv : (1 + i) / k = 7 := by by_contra h; exact hfg (if_neg h)
    have h1 := (Nat.le_div_iff_mul_le (by omega : 0 < k)).mp hdiv.ge
    have h2 := (Nat.div_lt_iff_lt_mul (by omega : 0 < k)).mp (show (1 + i) / k < 8 by omega)
    exact ⟨by omega, by omega, by omega⟩
  · exfalso
    have hlt_prod : 1 + j < k * (1 + i) := by
      have h1 : 1 + j < 25 * (1 + i) := by omega
      have h2 : 25 * (1 + i) ≤ k * (1 + i) := Nat.mul_le_mul_right (1 + i) hk25
      exact lt_of_lt_of_le h1 h2
    exact hfg (floorGraph_eq_zero_of_lt_mul (by omega) (by omega) hlt_prod)

/-- Composite-tail cross-contact bound for any `|ω| ≤ 1` whose active `k ≥ 25` are composite in
`(N / 8, 24 N]`. -/
private lemma subEuler_contact_cross_of_N {ω : ℕ → ℝ} (hω1 : ∀ k, |ω k| ≤ 1) {N : ℕ}
    (hN : 1000 ≤ N)
    (hsupp : ∀ k ∈ Icc 25 (3 * (8 * N) + 1),
      ω k * ∑ i ∈ range (3 * (8 * N)), ∑ j ∈ range (3 * (8 * N)),
        clusterVec 0 (N - 1) (5 * N) i * clusterVec 6 (7 * N - 1) (17 * N) j *
          floorGraph k (1 + i) (1 + j) ≠ 0 →
      ¬k.Prime ∧ N < 8 * k ∧ k ≤ 24 * N) :
    ∑ k ∈ Icc 2 (3 * (8 * N) + 1), |ω k| *
      |∑ i ∈ range (3 * (8 * N)), ∑ j ∈ range (3 * (8 * N)),
        clusterVec 0 (N - 1) (5 * N) i * clusterVec 6 (7 * N - 1) (17 * N) j *
          floorGraph k (1 + i) (1 + j)| ≤
      5 * floorContactSqrtConst + 90 * (Real.log 4 + 4) := by
  have hN_pos_r : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hsN_pos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN_pos_r
  have hu_sq : ∑ i ∈ range (3 * (8 * N)), clusterVec 0 (N - 1) (5 * N) i ^ 2 = 1 :=
    sum_clusterVec_sq (by omega) (by omega) (by omega)
  have hv_sq : ∑ j ∈ range (3 * (8 * N)), clusterVec 6 (7 * N - 1) (17 * N) j ^ 2 = 1 :=
    sum_clusterVec_sq (by omega) (by omega) (by omega)
  have hsplit_Q : Icc 2 (3 * (8 * N) + 1) = Icc 2 24 ∪ Icc 25 (3 * (8 * N) + 1) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hdisj_Q : Disjoint (Icc 2 24) (Icc 25 (3 * (8 * N) + 1)) := by
    rw [Finset.disjoint_left]; intro k h1 h2
    have := (Finset.mem_Icc.mp h1).2; have := (Finset.mem_Icc.mp h2).1; omega
  rw [hsplit_Q, Finset.sum_union hdisj_Q]
  refine add_le_add ?_ ?_
  · calc ∑ k ∈ Icc 2 24, |ω k| *
          |∑ i ∈ range (3 * (8 * N)), ∑ j ∈ range (3 * (8 * N)),
            clusterVec 0 (N - 1) (5 * N) i * clusterVec 6 (7 * N - 1) (17 * N) j *
              floorGraph k (1 + i) (1 + j)|
        ≤ ∑ k ∈ Icc 2 24, 2 * (Λ k : ℝ) / Real.sqrt k := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hb := abs_bilin_floorGraph_le le_rfl (Finset.mem_Icc.mp hk).1 (3 * (8 * N))
            (clusterVec 0 (N - 1) (5 * N)) (clusterVec 6 (7 * N - 1) (17 * N))
          rw [hu_sq, hv_sq] at hb
          calc |ω k| * |∑ i ∈ range (3 * (8 * N)), ∑ j ∈ range (3 * (8 * N)),
                clusterVec 0 (N - 1) (5 * N) i * clusterVec 6 (7 * N - 1) (17 * N) j *
                  floorGraph k (1 + i) (1 + j)|
              ≤ 1 * ((Λ k : ℝ) / Real.sqrt k * (1 + 1)) :=
                mul_le_mul (hω1 k) hb (abs_nonneg _) zero_le_one
            _ = 2 * (Λ k : ℝ) / Real.sqrt k := by ring
      _ ≤ floorContactSqrtConst * Real.sqrt (24 : ℝ) :=
          sum_vonMangoldt_div_sqrt_le (Q := 24) (by norm_num)
      _ ≤ 5 * floorContactSqrtConst := by
          have hs24 : Real.sqrt 24 ≤ 5 := by
            rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 5)]
            exact Real.sqrt_le_sqrt (by norm_num)
          exact (mul_comm _ _).trans_le
            (mul_le_mul_of_nonneg_right hs24 floorContactSqrtConst_pos.le)
  · rw [← Finset.sum_filter_ne_zero]
    have hsubC : (Icc 25 (3 * (8 * N) + 1)).filter (fun k =>
        |ω k| * |∑ i ∈ range (3 * (8 * N)), ∑ j ∈ range (3 * (8 * N)),
          clusterVec 0 (N - 1) (5 * N) i * clusterVec 6 (7 * N - 1) (17 * N) j *
            floorGraph k (1 + i) (1 + j)| ≠ 0) ⊆
        (Ioc 0 ⌊((24 * N : ℕ) : ℝ)⌋₊).filter (fun k => ¬k.Prime) := by
      intro k hk
      rcases Finset.mem_filter.mp hk with ⟨hkI, hkne⟩
      rw [← abs_mul, abs_ne_zero] at hkne
      obtain ⟨hnp, _, hk24⟩ := hsupp k hkI hkne
      rw [Finset.mem_filter, Finset.mem_Ioc, Nat.floor_natCast]
      have := (Finset.mem_Icc.mp hkI).1
      exact ⟨⟨by omega, hk24⟩, hnp⟩
    have hcomp_le : ∑ k ∈ (Icc 25 (3 * (8 * N) + 1)).filter (fun k =>
        |ω k| * |∑ i ∈ range (3 * (8 * N)), ∑ j ∈ range (3 * (8 * N)),
          clusterVec 0 (N - 1) (5 * N) i * clusterVec 6 (7 * N - 1) (17 * N) j *
            floorGraph k (1 + i) (1 + j)| ≠ 0),
        |ω k| * |∑ i ∈ range (3 * (8 * N)), ∑ j ∈ range (3 * (8 * N)),
          clusterVec 0 (N - 1) (5 * N) i * clusterVec 6 (7 * N - 1) (17 * N) j *
            floorGraph k (1 + i) (1 + j)| ≤
        ∑ k ∈ (Ioc 0 ⌊((24 * N : ℕ) : ℝ)⌋₊).filter (fun k => ¬k.Prime),
          (2 * Real.sqrt 8 / Real.sqrt N) * (Λ k : ℝ) := by
      refine (Finset.sum_le_sum fun k hk => ?_).trans
        (Finset.sum_le_sum_of_subset_of_nonneg hsubC fun k _ _ =>
          mul_nonneg (by positivity) ArithmeticFunction.vonMangoldt_nonneg)
      rcases Finset.mem_filter.mp hk with ⟨hkI, hkne⟩
      rw [← abs_mul, abs_ne_zero] at hkne
      obtain ⟨_, hk_lo, _⟩ := hsupp k hkI hkne
      have hb := abs_bilin_floorGraph_le le_rfl
        (by have := (Finset.mem_Icc.mp hkI).1; omega) (3 * (8 * N))
        (clusterVec 0 (N - 1) (5 * N)) (clusterVec 6 (7 * N - 1) (17 * N))
      rw [hu_sq, hv_sq] at hb
      have hsk_ge : Real.sqrt N / Real.sqrt 8 ≤ Real.sqrt k := by
        rw [div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num)), ← Real.sqrt_mul (Nat.cast_nonneg k)]
        exact Real.sqrt_le_sqrt (by exact_mod_cast hk_lo.le)
      calc |ω k| * |∑ i ∈ range (3 * (8 * N)), ∑ j ∈ range (3 * (8 * N)),
            clusterVec 0 (N - 1) (5 * N) i * clusterVec 6 (7 * N - 1) (17 * N) j *
              floorGraph k (1 + i) (1 + j)|
          ≤ 1 * ((Λ k : ℝ) / Real.sqrt k * (1 + 1)) :=
            mul_le_mul (hω1 k) hb (abs_nonneg _) zero_le_one
        _ = 2 * (Λ k : ℝ) / Real.sqrt k := by ring
        _ ≤ 2 * (Λ k : ℝ) / (Real.sqrt N / Real.sqrt 8) :=
            div_le_div_of_nonneg_left
              (mul_nonneg zero_le_two ArithmeticFunction.vonMangoldt_nonneg)
              (div_pos hsN_pos (Real.sqrt_pos.mpr (by norm_num))) hsk_ge
        _ = (2 * Real.sqrt 8 / Real.sqrt N) * (Λ k : ℝ) := by ring
    refine hcomp_le.trans ?_
    rw [← Finset.mul_sum, ← Chebyshev.psi_sub_theta_eq_sum_not_prime ((24 * N : ℕ) : ℝ)]
    have hpt := psi_sub_theta_le_three_mul_sqrt ((24 * N : ℕ) : ℝ)
    have hprod : (2 * Real.sqrt 8 / Real.sqrt N) *
        (3 * (Real.log 4 + 4) * Real.sqrt ((24 * N : ℕ) : ℝ)) =
        6 * (Real.sqrt 8 * Real.sqrt 24) * (Real.log 4 + 4) := by
      rw [Nat.cast_mul, Nat.cast_ofNat, Real.sqrt_mul (by norm_num)]
      field_simp [hsN_pos.ne']
      ring
    have hs192 : Real.sqrt 8 * Real.sqrt 24 ≤ 15 := by
      rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8),
        ← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 15)]
      exact Real.sqrt_le_sqrt (by norm_num)
    calc (2 * Real.sqrt 8 / Real.sqrt N) *
          (Chebyshev.psi ((24 * N : ℕ) : ℝ) - Chebyshev.theta ((24 * N : ℕ) : ℝ))
        ≤ (2 * Real.sqrt 8 / Real.sqrt N) *
            (3 * (Real.log 4 + 4) * Real.sqrt ((24 * N : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hpt (by positivity)
      _ = 6 * (Real.sqrt 8 * Real.sqrt 24) * (Real.log 4 + 4) := hprod
      _ ≤ 90 * (Real.log 4 + 4) := by
          have hc : 0 ≤ Real.log 4 + 4 := by
            have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); positivity
          nlinarith [hs192, hc]

/-- Scale-`N` assembly of the two-negative-squares witness for `subEulerGluingWeight`. -/
private lemma two_le_hermNegIndex_subEuler_of_N {ω : ℕ → ℝ} (hω0 : ∀ k, 0 ≤ ω k)
    (hω1 : ∀ k, |ω k| ≤ 1) {N R : ℕ} (hN : 1000 ≤ N) (hR : 1 ≤ R)
    (hf1 : (N : ℝ) / 2 ≤ ∑ k ∈ Icc 2 (3 * (8 * N) + 1), ω k *
      ∑ l ∈ Ico (N - 1) (N - 1 + 5 * N), floorGraph k (1 + 0) (1 + l))
    (hf2 : (N : ℝ) / 2 ≤ ∑ k ∈ Icc 2 (3 * (8 * N) + 1), ω k *
      ∑ l ∈ Ico (7 * N - 1) (7 * N - 1 + 17 * N), floorGraph k (1 + 6) (1 + l))
    (hsupp : ∀ k ∈ Icc 25 (3 * (8 * N) + 1),
      ω k * ∑ i ∈ range (3 * (8 * N)), ∑ j ∈ range (3 * (8 * N)),
        clusterVec 0 (N - 1) (5 * N) i * clusterVec 6 (7 * N - 1) (17 * N) j *
          floorGraph k (1 + i) (1 + j) ≠ 0 →
      ¬k.Prime ∧ N < 8 * k ∧ k ≤ 24 * N)
    {a : ℝ} (ha : a ≤ (1 / 60 : ℝ) * Real.sqrt ((8 * N : ℕ) : ℝ) - (subEulerCrossConst + 20000)) :
    2 ≤ hermNegIndex ((windowMatrix (reweightedNeutral ω (3 * (8 * N) + 1)) R (3 * (8 * N) * R) +
      Matrix.diagonal (fun _ : Fin (3 * (8 * N) * R) => a)).map (↑) :
        Matrix (Fin (3 * (8 * N) * R)) (Fin (3 * (8 * N) * R)) ℂ) := by
  have hN_pos_r : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hsN_pos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN_pos_r
  have hsK_eq : Real.sqrt ((8 * N : ℕ) : ℝ) = Real.sqrt 8 * Real.sqrt (N : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.sqrt_mul (by norm_num)]
  have hs8_lt : Real.sqrt 8 < 3 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hattr1 : (1 / 18 : ℝ) * Real.sqrt ((8 * N : ℕ) : ℝ) ≤
      (1 / Real.sqrt ((5 * N : ℕ) : ℝ)) * ((N : ℝ) / 2) := by
    have hs5_lt : Real.sqrt 5 ≤ 3 := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)]; exact Real.sqrt_le_sqrt (by norm_num)
    have h1 : (1 / Real.sqrt ((5 * N : ℕ) : ℝ)) * ((N : ℝ) / 2) =
        Real.sqrt N / (2 * Real.sqrt 5) := by
      rw [Nat.cast_mul, Nat.cast_ofNat, Real.sqrt_mul (by norm_num)]
      have hs5_ne : Real.sqrt 5 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
      field_simp [hs5_ne, hsN_pos.ne']
      rw [Real.sq_sqrt hN_pos_r.le]
    rw [h1, hsK_eq]
    have hdiv : Real.sqrt N / 6 ≤ Real.sqrt N / (2 * Real.sqrt 5) :=
      div_le_div_of_nonneg_left hsN_pos.le (by positivity) (by linarith)
    nlinarith [hs8_lt, hsN_pos, hdiv]
  have hattr2 : (1 / 30 : ℝ) * Real.sqrt ((8 * N : ℕ) : ℝ) ≤
      (1 / Real.sqrt ((17 * N : ℕ) : ℝ)) * ((N : ℝ) / 2) := by
    have hs17_lt : Real.sqrt 17 ≤ 5 := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 5)]; exact Real.sqrt_le_sqrt (by norm_num)
    have h1 : (1 / Real.sqrt ((17 * N : ℕ) : ℝ)) * ((N : ℝ) / 2) =
        Real.sqrt N / (2 * Real.sqrt 17) := by
      rw [Nat.cast_mul, Nat.cast_ofNat, Real.sqrt_mul (by norm_num)]
      have hs17_ne : Real.sqrt 17 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
      field_simp [hs17_ne, hsN_pos.ne']
      rw [Real.sq_sqrt hN_pos_r.le]
    rw [h1, hsK_eq]
    have hdiv : Real.sqrt N / 10 ≤ Real.sqrt N / (2 * Real.sqrt 17) :=
      div_le_div_of_nonneg_left hsN_pos.le (by positivity) (by linarith)
    nlinarith [hs8_lt, hsN_pos, hdiv]
  have hlog_diag : Real.log (((1 + 3 * (8 * N) : ℕ) : ℝ) + 1) + 1 ≤
      (1 / 120 : ℝ) * Real.sqrt ((8 * N : ℕ) : ℝ) + 19000 := by
    have h1 := log_le_eps_mul_sqrt_add (x := ((1 + 3 * (8 * N) : ℕ) : ℝ) + 1) (ε := 1 / 400)
      (by positivity) (by norm_num)
    norm_num at h1
    have hsq : Real.sqrt (((1 + 3 * (8 * N) : ℕ) : ℝ) + 1) ≤ 3 * Real.sqrt ((8 * N : ℕ) : ℝ) := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3), ← Real.sqrt_mul (by norm_num)]
      refine Real.sqrt_le_sqrt ?_
      push_cast; linarith [hN_pos_r]
    linarith [h1, hsq, Real.sqrt_nonneg ((8 * N : ℕ) : ℝ)]
  have hu_raw := bilin_reweightedNeutral_clusterVec_le hω0
    (R₀ := 1) (Q := 3 * (8 * N) + 1) (J₀ := 3 * (8 * N)) (p₀ := 0) (q₀ := N - 1) (L := 5 * N)
    le_rfl (by omega) (by omega) (by omega) a
  have hv_raw := bilin_reweightedNeutral_clusterVec_le hω0
    (R₀ := 1) (Q := 3 * (8 * N) + 1) (J₀ := 3 * (8 * N)) (p₀ := 6) (q₀ := 7 * N - 1) (L := 17 * N)
    le_rfl (by omega) (by omega) (by omega) a
  have hcross_raw := abs_bilin_reweightedNeutral_clusterVec_le ω
    (R₀ := 1) (Q := 3 * (8 * N) + 1) (J₀ := 3 * (8 * N))
    (p₁ := 0) (q₁ := N - 1) (L₁ := 5 * N)
    (p₂ := 6) (q₂ := 7 * N - 1) (L₂ := 17 * N) (d := N / 2)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) a
  have hjet_num := subEuler_jet_cross_bound (show 256 ≤ N by omega)
  have hcont_num := subEuler_contact_cross_of_N hω1 hN hsupp
  have hM0 : 0 ≤ subEulerCrossConst := by
    unfold subEulerCrossConst
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    have := floorContactSqrtConst_pos
    positivity
  have huv_le : |bilin (windowMatrix (reweightedNeutral ω (3 * (8 * N) + 1)) 1 (3 * (8 * N)) +
        Matrix.diagonal (fun _ : Fin (3 * (8 * N)) => a))
      (fun i : Fin (3 * (8 * N)) => clusterVec 0 (N - 1) (5 * N) i)
      (fun j : Fin (3 * (8 * N)) => clusterVec 6 (7 * N - 1) (17 * N) j)| ≤
      subEulerCrossConst := by
    unfold subEulerCrossConst at *
    linarith [hcross_raw, hjet_num, hcont_num]
  have hu_le : bilin (windowMatrix (reweightedNeutral ω (3 * (8 * N) + 1)) 1 (3 * (8 * N)) +
        Matrix.diagonal (fun _ : Fin (3 * (8 * N)) => a))
      (fun j : Fin (3 * (8 * N)) => clusterVec 0 (N - 1) (5 * N) j)
      (fun j : Fin (3 * (8 * N)) => clusterVec 0 (N - 1) (5 * N) j) ≤
      -(subEulerCrossConst + 1) := by
    have hmul1 := mul_le_mul_of_nonneg_left hf1
      (by positivity : (0 : ℝ) ≤ 1 / Real.sqrt ((5 * N : ℕ) : ℝ))
    linarith [hu_raw, hmul1, hattr1, hlog_diag, ha, Real.sqrt_nonneg ((8 * N : ℕ) : ℝ)]
  have hv_le : bilin (windowMatrix (reweightedNeutral ω (3 * (8 * N) + 1)) 1 (3 * (8 * N)) +
        Matrix.diagonal (fun _ : Fin (3 * (8 * N)) => a))
      (fun j : Fin (3 * (8 * N)) => clusterVec 6 (7 * N - 1) (17 * N) j)
      (fun j : Fin (3 * (8 * N)) => clusterVec 6 (7 * N - 1) (17 * N) j) ≤
      -(subEulerCrossConst + 1) := by
    have hmul2 := mul_le_mul_of_nonneg_left hf2
      (by positivity : (0 : ℝ) ≤ 1 / Real.sqrt ((17 * N : ℕ) : ℝ))
    linarith [hv_raw, hmul2, hattr2, hlog_diag, ha, Real.sqrt_nonneg ((8 * N : ℕ) : ℝ)]
  exact two_le_hermNegIndex_reweightedNeutral_of_coarse (R₀ := 1) (m := R)
    (R := R) (J₀ := 3 * (8 * N)) (J := 3 * (8 * N) * R) (Q := 3 * (8 * N) + 1)
    le_rfl hR (by omega)
    (by have : R * (3 * (8 * N)) = 3 * (8 * N) * R := mul_comm _ _; omega)
    ω a (clusterVec 0 (N - 1) (5 * N)) (clusterVec 6 (7 * N - 1) (17 * N))
    hM0 hu_le hv_le huv_le (by linarith [hM0]) (by nlinarith [hM0])

/-- **Two negative squares up to `c₀ √K − C₀` for `subEulerGluingWeight Q₀`**: for every `Q₀ : ℕ`
and every `m ≥ Q₀ + 4`, setting `K = 8 · 256^m`, the reweighted neutral window of
`subEulerGluingWeight Q₀` on `(R, (3K + 1)R]` has `2 ≤ hermNegIndex` at every block size `R ≥ 1`
and every shift `a ≤ (1 / 60) √K − (subEulerCrossConst + 20000)`. -/
theorem two_le_hermNegIndex_subEulerGluingWeight (Q₀ : ℕ) {m R : ℕ} (hm : Q₀ + 4 ≤ m)
    (hR : 1 ≤ R) {a : ℝ}
    (ha : a ≤ (1 / 60 : ℝ) * Real.sqrt ((8 * 256 ^ m : ℕ) : ℝ) - (subEulerCrossConst + 20000)) :
    2 ≤ hermNegIndex ((windowMatrix (reweightedNeutral (subEulerGluingWeight Q₀)
      (3 * (8 * 256 ^ m) + 1)) R (3 * (8 * 256 ^ m) * R) +
      Matrix.diagonal (fun _ : Fin (3 * (8 * 256 ^ m) * R) => a)).map (↑) :
        Matrix (Fin (3 * (8 * 256 ^ m) * R)) (Fin (3 * (8 * 256 ^ m) * R)) ℂ) := by
  have hm4 : 4 ≤ m := by omega
  have hN_big : 1000 ≤ 256 ^ m :=
    (by norm_num : 1000 ≤ 256 ^ 4).trans (Nat.pow_le_pow_right (by norm_num) hm4)
  have h8Q₀_lt : 8 * Q₀ < 256 ^ m := by
    have hQlt : Q₀ < 256 ^ Q₀ :=
      (Nat.lt_two_pow_self (n := Q₀)).trans_le (Nat.pow_le_pow_left (by norm_num) Q₀)
    have hpow : 256 ^ Q₀ * 256 ^ 4 ≤ 256 ^ m := by
      rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) hm
    have h8 : 8 * Q₀ < 256 ^ Q₀ * 16 := by
      have := Nat.one_le_pow Q₀ 256 (by norm_num); omega
    have h16 : 256 ^ Q₀ * 16 ≤ 256 ^ Q₀ * 256 ^ 4 :=
      Nat.mul_le_mul_left _ (by norm_num)
    exact lt_of_lt_of_le h8 (h16.trans hpow)
  refine two_le_hermNegIndex_subEuler_of_N (subEulerGluingWeight_nonneg Q₀)
    (abs_subEulerGluingWeight_le_one Q₀) hN_big hR
    (subEuler_fiber_sum_ge Q₀ hm4 fun p hp => ?_)
    (subEuler_fiber_sum_ge Q₀ hm4 fun p hp => ?_)
    (fun k hk hne => ?_) ha
  · rcases Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1 with ⟨h1, h2⟩
    omega
  · rcases Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1 with ⟨h1, h2⟩
    omega
  · have hω_ne : subEulerGluingWeight Q₀ k ≠ 0 := fun h => hne (by rw [h, zero_mul])
    have hsum_ne : ∑ i ∈ range (3 * (8 * 256 ^ m)), ∑ j ∈ range (3 * (8 * 256 ^ m)),
        clusterVec 0 (256 ^ m - 1) (5 * 256 ^ m) i *
          clusterVec 6 (7 * 256 ^ m - 1) (17 * 256 ^ m) j *
          floorGraph k (1 + i) (1 + j) ≠ 0 := fun h => hne (by rw [h, mul_zero])
    obtain ⟨hk_lo, hk_hi, hnot_band⟩ :=
      subEuler_support_out hN_big (Finset.mem_Icc.mp hk).1 hsum_ne
    refine ⟨?_, hk_lo, hk_hi⟩
    intro hk_prime
    unfold subEulerGluingWeight subEulerPrimePred at hω_ne
    rw [hk_prime.minFac_eq] at hω_ne
    have hcond : k = 1 ∨ k ≤ Q₀ ∨ ∃ r : ℕ, 1 ≤ r ∧ 256 ^ r < k ∧ k ≤ 3 * 256 ^ r := by
      by_contra hc; exact hω_ne (if_neg hc)
    rcases hcond with rfl | hQ₀ | ⟨r, _, hr_lo, hr_hi⟩
    · exact hk_prime.ne_one rfl
    · omega
    · rcases lt_trichotomy r m with hrm | rfl | hmr
      · have hpow : 256 ^ r * 256 ≤ 256 ^ m := by
          rw [← pow_succ]; exact Nat.pow_le_pow_right (by norm_num) hrm
        omega
      · exact hnot_band ⟨hr_lo, hr_hi⟩
      · have hpow : 256 ^ m * 256 ≤ 256 ^ r := by
          rw [← pow_succ]; exact Nat.pow_le_pow_right (by norm_num) hmr
        omega

/-! ### 4.2 Un-updated doubling jump on `neutralWindow (3K + 1)` -/

/-- Full-fiber prime attraction lower bound at coarse block size `2` (`2 + p₀` to
`[2 + q₀, 2 + q₀ + L)`). -/
private lemma halfCutoff_full_window_prime_sum {Q p₀ q₀ L : ℕ} {P : Finset ℕ}
    (hP : P ⊆ (Icc 2 Q).filter Nat.Prime)
    (hcov : ∀ p ∈ P, p * (2 + p₀) ≤ 2 + q₀ ∧ 2 + q₀ + L ≤ p * (2 + p₀ + 1)) :
    (L : ℝ) * (∑ p ∈ P, Real.log p / p) ≤
      ∑ k ∈ Icc 2 Q, (1 : ℝ) * ∑ l ∈ Ico q₀ (q₀ + L), floorGraph k (2 + p₀) (2 + l) := by
  have hsub : P ⊆ Icc 2 Q := fun p hp => (Finset.mem_filter.mp (hP hp)).1
  have hnonneg : ∀ k ∈ Icc 2 Q, k ∉ P →
      0 ≤ (1 : ℝ) * ∑ l ∈ Ico q₀ (q₀ + L), floorGraph k (2 + p₀) (2 + l) := by
    intro k _ _
    refine mul_nonneg zero_le_one (Finset.sum_nonneg fun l _ => ?_)
    unfold floorGraph; split_ifs
    · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k)
    · exact le_rfl
  rw [Finset.mul_sum]
  refine (Finset.sum_le_sum fun p hp => ?_).trans
    (Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg)
  have hpP : p.Prime := (Finset.mem_filter.mp (hP hp)).2
  obtain ⟨hc1, hc2⟩ := hcov p hp
  rw [one_mul]
  have hterm : ∀ l ∈ Ico q₀ (q₀ + L), floorGraph p (2 + p₀) (2 + l) = Real.log p / p := by
    intro l hl
    rcases Finset.mem_Ico.mp hl with ⟨hl1, hl2⟩
    have h1l : p * (2 + p₀) ≤ 2 + l := by omega
    have h2l : 2 + l < (2 + p₀ + 1) * p := by
      calc 2 + l < p * (2 + p₀ + 1) := by omega
        _ = (2 + p₀ + 1) * p := mul_comm _ _
    have hdiv : (2 + l) / p = 2 + p₀ := by
      refine le_antisymm ?_ ?_
      · exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hpP.pos).mpr h2l)
      · exact (Nat.le_div_iff_mul_le hpP.pos).mpr (by rw [mul_comm]; exact h1l)
    have hle_pl : 2 + p₀ ≤ 2 + l := by
      have hp2 := hpP.two_le
      calc 2 + p₀ ≤ 2 * (2 + p₀) := by omega
        _ ≤ p * (2 + p₀) := Nat.mul_le_mul_right _ hp2
        _ ≤ 2 + l := h1l
    rw [floorGraph_of_le p hle_pl, if_pos hdiv, ArithmeticFunction.vonMangoldt_apply_prime hpP]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Nat.card_Ico, Nat.add_sub_cancel_left,
    nsmul_eq_mul]

/-- Every cross-contact term between `clusterVec 0 (6K + L - 2) L` and
`clusterVec 1 (9K + 2 + L) L` (`L = K / 20`, `2 ≤ k ≤ 3K + 1`) vanishes outside
`i ∈ Ico (6K + L - 2) (6K + 2L - 2)` and `j = 1`. -/
private lemma halfCutoff_cross_vanish_outside {K k i j : ℕ} (hK : 200 ≤ K) (hk2 : 2 ≤ k)
    (hkQ : k ≤ 3 * K + 1)
    (hnot : ¬(6 * K + K / 20 - 2 ≤ i ∧ i < 6 * K + K / 20 - 2 + K / 20 ∧ j = 1)) :
    clusterVec 0 (6 * K + K / 20 - 2) (K / 20) i *
      clusterVec 1 (9 * K + 2 + K / 20) (K / 20) j *
      floorGraph k (2 + i) (2 + j) = 0 := by
  by_cases hui : clusterVec 0 (6 * K + K / 20 - 2) (K / 20) i = 0
  · rw [hui, zero_mul, zero_mul]
  by_cases hvj : clusterVec 1 (9 * K + 2 + K / 20) (K / 20) j = 0
  · rw [hvj, mul_zero, zero_mul]
  have hi_s : i = 0 ∨ (6 * K + K / 20 - 2 ≤ i ∧ i < 6 * K + K / 20 - 2 + K / 20) := by
    unfold clusterVec at hui
    by_cases h0 : i = 0
    · exact Or.inl h0
    · rw [if_neg h0] at hui
      by_cases hI : 6 * K + K / 20 - 2 ≤ i ∧ i < 6 * K + K / 20 - 2 + K / 20
      · exact Or.inr hI
      · rw [if_neg hI] at hui; exact absurd rfl hui
  have hj_s : j = 1 ∨ (9 * K + 2 + K / 20 ≤ j ∧ j < 9 * K + 2 + K / 20 + K / 20) := by
    unfold clusterVec at hvj
    by_cases h1 : j = 1
    · exact Or.inl h1
    · rw [if_neg h1] at hvj
      by_cases hJ : 9 * K + 2 + K / 20 ≤ j ∧ j < 9 * K + 2 + K / 20 + K / 20
      · exact Or.inr hJ
      · rw [if_neg hJ] at hvj; exact absurd rfl hvj
  rcases hi_s with rfl | ⟨hi1, hi2⟩ <;> rcases hj_s with rfl | ⟨hj1, hj2⟩
  · rw [floorGraph_eq_zero_of_lt_mul hk2 (by omega) (by omega), mul_zero]
  · rw [floorGraph_of_le k (by omega), if_neg, mul_zero]
    intro hdiv
    have hlt3 := (Nat.div_lt_iff_lt_mul (by omega : 0 < k)).mp (show (2 + j) / k < 3 by omega)
    omega
  · exact absurd ⟨hi1, hi2, rfl⟩ hnot
  · have hlt_prod : 2 + j < k * (2 + i) := by
      have h1 : 2 + j < 2 * (2 + i) := by omega
      have h2 : 2 * (2 + i) ≤ k * (2 + i) := Nat.mul_le_mul_right (2 + i) hk2
      exact lt_of_lt_of_le h1 h2
    rw [floorGraph_eq_zero_of_lt_mul hk2 (by omega) hlt_prod, mul_zero]

/-- Contact cross-sum bound `≤ (21 / 100) √(K / 20)` on `neutralWindow (3K + 1)`. -/
private lemma halfCutoff_contact_cross_bound {K : ℕ} (hK : 200 ≤ K)
    (hC : ∑ k ∈ Icc (3 * K / 2 + 1) (21 * K / 10), (Λ k : ℝ) / k ≤ 42 / 100) :
    ∑ k ∈ Icc 2 (3 * K + 1), |(1 : ℝ)| *
      |∑ i ∈ range (10 * K), ∑ j ∈ range (10 * K),
        clusterVec 0 (6 * K + K / 20 - 2) (K / 20) i *
          clusterVec 1 (9 * K + 2 + K / 20) (K / 20) j *
          floorGraph k (2 + i) (2 + j)| ≤
      (21 / 100 : ℝ) * Real.sqrt ((K / 20 : ℕ) : ℝ) := by
  have hL_pos : (0 : ℝ) < ((K / 20 : ℕ) : ℝ) := by exact_mod_cast (show 0 < K / 20 by omega)
  have hsL_pos : 0 < Real.sqrt ((K / 20 : ℕ) : ℝ) := Real.sqrt_pos.mpr hL_pos
  have hterm_le : ∀ k ∈ Icc 2 (3 * K + 1),
      |(1 : ℝ)| * |∑ i ∈ range (10 * K), ∑ j ∈ range (10 * K),
        clusterVec 0 (6 * K + K / 20 - 2) (K / 20) i *
          clusterVec 1 (9 * K + 2 + K / 20) (K / 20) j *
          floorGraph k (2 + i) (2 + j)| ≤
      if k ∈ Icc (3 * K / 2 + 1) (21 * K / 10) then
        (Real.sqrt ((K / 20 : ℕ) : ℝ) / 2) * ((Λ k : ℝ) / k) else 0 := by
    intro k hk
    rw [abs_one, one_mul]
    rcases Finset.mem_Icc.mp hk with ⟨hk2, hkQ⟩
    have hnn : ∀ i j, 0 ≤ clusterVec 0 (6 * K + K / 20 - 2) (K / 20) i *
        clusterVec 1 (9 * K + 2 + K / 20) (K / 20) j * floorGraph k (2 + i) (2 + j) := fun i j =>
      mul_nonneg (mul_nonneg (clusterVec_nonneg _ _ _ _) (clusterVec_nonneg _ _ _ _)) (by
        unfold floorGraph; split_ifs
        · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k)
        · exact le_rfl)
    rw [abs_of_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hnn i j)]
    by_cases hk_in : k ∈ Icc (3 * K / 2 + 1) (21 * K / 10)
    · rw [if_pos hk_in]
      have hsum_eq : ∑ i ∈ range (10 * K), ∑ j ∈ range (10 * K),
          clusterVec 0 (6 * K + K / 20 - 2) (K / 20) i *
            clusterVec 1 (9 * K + 2 + K / 20) (K / 20) j * floorGraph k (2 + i) (2 + j) =
          ∑ i ∈ Ico (6 * K + K / 20 - 2) (6 * K + K / 20 - 2 + K / 20),
            clusterVec 0 (6 * K + K / 20 - 2) (K / 20) i *
              clusterVec 1 (9 * K + 2 + K / 20) (K / 20) 1 * floorGraph k (2 + i) 3 := by
        have hin : ∀ i ∈ range (10 * K),
            ∑ j ∈ range (10 * K),
              clusterVec 0 (6 * K + K / 20 - 2) (K / 20) i *
                clusterVec 1 (9 * K + 2 + K / 20) (K / 20) j * floorGraph k (2 + i) (2 + j) =
            if 6 * K + K / 20 - 2 ≤ i ∧ i < 6 * K + K / 20 - 2 + K / 20 then
              clusterVec 0 (6 * K + K / 20 - 2) (K / 20) i *
                clusterVec 1 (9 * K + 2 + K / 20) (K / 20) 1 * floorGraph k (2 + i) 3 else 0 := by
          intro i _
          by_cases hI : 6 * K + K / 20 - 2 ≤ i ∧ i < 6 * K + K / 20 - 2 + K / 20
          · rw [if_pos hI, Finset.sum_eq_single 1
              (fun j _ hj1 => halfCutoff_cross_vanish_outside hK hk2 hkQ (fun h => hj1 h.2.2))
              (fun h1 => absurd (Finset.mem_range.mpr (by omega)) h1)]
          · rw [if_neg hI]
            exact Finset.sum_eq_zero fun j _ =>
              halfCutoff_cross_vanish_outside hK hk2 hkQ (fun h => hI ⟨h.1, h.2.1⟩)
        rw [Finset.sum_congr rfl hin, ← Finset.sum_filter]
        have hfil : (range (10 * K)).filter
            (fun i => 6 * K + K / 20 - 2 ≤ i ∧ i < 6 * K + K / 20 - 2 + K / 20) =
            Ico (6 * K + K / 20 - 2) (6 * K + K / 20 - 2 + K / 20) := by
          ext i; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
        rw [hfil]
      rw [hsum_eq]
      have hpt : ∀ i ∈ Ico (6 * K + K / 20 - 2) (6 * K + K / 20 - 2 + K / 20),
          clusterVec 0 (6 * K + K / 20 - 2) (K / 20) i *
            clusterVec 1 (9 * K + 2 + K / 20) (K / 20) 1 * floorGraph k (2 + i) 3 ≤
            (1 / (2 * Real.sqrt ((K / 20 : ℕ) : ℝ))) * ((Λ k : ℝ) / k) := by
        intro i hi
        rcases Finset.mem_Ico.mp hi with ⟨hi1, hi2⟩
        have hui : clusterVec 0 (6 * K + K / 20 - 2) (K / 20) i =
            1 / Real.sqrt (2 * ((K / 20 : ℕ) : ℝ)) := by
          unfold clusterVec
          rw [if_neg (by omega), if_pos ⟨hi1, hi2⟩]
        have hv1 : clusterVec 1 (9 * K + 2 + K / 20) (K / 20) 1 = 1 / Real.sqrt 2 := by
          simp [clusterVec]
        have huv_val : clusterVec 0 (6 * K + K / 20 - 2) (K / 20) i *
            clusterVec 1 (9 * K + 2 + K / 20) (K / 20) 1 =
            1 / (2 * Real.sqrt ((K / 20 : ℕ) : ℝ)) := by
          rw [hui, hv1, Real.sqrt_mul zero_le_two]
          have hs2_ne : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr zero_lt_two).ne'
          field_simp [hs2_ne, hsL_pos.ne']
          rw [Real.sq_sqrt zero_le_two]
        rw [huv_val]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        unfold floorGraph; split_ifs
        · exact le_rfl
        · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k)
      calc ∑ i ∈ Ico (6 * K + K / 20 - 2) (6 * K + K / 20 - 2 + K / 20),
            clusterVec 0 (6 * K + K / 20 - 2) (K / 20) i *
              clusterVec 1 (9 * K + 2 + K / 20) (K / 20) 1 * floorGraph k (2 + i) 3
          ≤ ∑ _i ∈ Ico (6 * K + K / 20 - 2) (6 * K + K / 20 - 2 + K / 20),
              (1 / (2 * Real.sqrt ((K / 20 : ℕ) : ℝ))) * ((Λ k : ℝ) / k) := Finset.sum_le_sum hpt
        _ = (Real.sqrt ((K / 20 : ℕ) : ℝ) / 2) * ((Λ k : ℝ) / k) := by
            rw [Finset.sum_const, Nat.card_Ico, Nat.add_sub_cancel_left, nsmul_eq_mul]
            field_simp [hsL_pos.ne']
            rw [Real.sq_sqrt hL_pos.le]
    · rw [if_neg hk_in]
      refine le_of_eq (Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_)
      by_cases hcase : 6 * K + K / 20 - 2 ≤ i ∧ i < 6 * K + K / 20 - 2 + K / 20 ∧ j = 1
      · rcases hcase with ⟨hi1, hi2, rfl⟩
        have hfg0 : floorGraph k (2 + i) 3 = 0 := by
          rw [floorGraph_comm, floorGraph_of_le k (by omega), if_neg]
          intro hdiv
          have h1 := (Nat.le_div_iff_mul_le (by omega : 0 < k)).mp hdiv.ge
          have h2 := (Nat.div_lt_iff_lt_mul (by omega : 0 < k)).mp
            (show (2 + i) / k < 4 by omega)
          exact hk_in (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        rw [hfg0, mul_zero]
      · exact halfCutoff_cross_vanish_outside hK hk2 hkQ hcase
  have hsubC : Icc (3 * K / 2 + 1) (21 * K / 10) ⊆ Icc 2 (3 * K + 1) :=
    Finset.Icc_subset_Icc (by omega) (by omega)
  calc ∑ k ∈ Icc 2 (3 * K + 1), |(1 : ℝ)| *
          |∑ i ∈ range (10 * K), ∑ j ∈ range (10 * K),
            clusterVec 0 (6 * K + K / 20 - 2) (K / 20) i *
              clusterVec 1 (9 * K + 2 + K / 20) (K / 20) j * floorGraph k (2 + i) (2 + j)|
      ≤ ∑ k ∈ Icc 2 (3 * K + 1), if k ∈ Icc (3 * K / 2 + 1) (21 * K / 10) then
          (Real.sqrt ((K / 20 : ℕ) : ℝ) / 2) * ((Λ k : ℝ) / k) else 0 :=
        Finset.sum_le_sum hterm_le
    _ = (Real.sqrt ((K / 20 : ℕ) : ℝ) / 2) *
          ∑ k ∈ Icc (3 * K / 2 + 1) (21 * K / 10), (Λ k : ℝ) / k := by
        rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hsubC,
          ← Finset.mul_sum]
    _ ≤ (Real.sqrt ((K / 20 : ℕ) : ℝ) / 2) * (42 / 100) :=
        mul_le_mul_of_nonneg_left hC (by positivity)
    _ = (21 / 100 : ℝ) * Real.sqrt ((K / 20 : ℕ) : ℝ) := by ring

/-- **Un-updated glued-matrix jump on `neutralWindow (3K + 1)`**: whenever the prime bands
`[2.1K + 1, 3K]` and `[2.3K + 2, 3K]` and the cross-band `[1.5K + 1, 2.1K]` carry their PNT
harmonic weights (`K ≥ 200`), the un-updated glued matrix `neutralWindow (3K + 1) R (6KR) + a I`
has `2 ≤ hermNegIndex` at every block size `R ≥ 6` and every shift
`a ≤ (1 / 2000) √K − 40000`. -/
theorem two_le_hermNegIndex_neutralWindow_halfCutoff_of_primeSums {K R : ℕ} (hK : 200 ≤ K)
    (hR : 6 ≤ R)
    (hS₁ : (28 / 100 : ℝ) ≤
      ∑ p ∈ (Icc (21 * K / 10 + 1) (3 * K)).filter Nat.Prime, Real.log p / p)
    (hS₂ : (20 / 100 : ℝ) ≤
      ∑ p ∈ (Icc (23 * K / 10 + 2) (3 * K)).filter Nat.Prime, Real.log p / p)
    (hC : ∑ k ∈ Icc (3 * K / 2 + 1) (21 * K / 10), (Λ k : ℝ) / k ≤ 42 / 100)
    {a : ℝ} (ha : a ≤ (1 / 2000 : ℝ) * Real.sqrt K - 40000) :
    2 ≤ hermNegIndex ((neutralWindow (3 * K + 1) R (6 * K * R) +
      Matrix.diagonal (fun _ : Fin (6 * K * R) => a)).map (↑) :
        Matrix (Fin (6 * K * R)) (Fin (6 * K * R)) ℂ) := by
  have hL_pos : (0 : ℝ) < ((K / 20 : ℕ) : ℝ) := by exact_mod_cast (show 0 < K / 20 by omega)
  have hsL_pos : 0 < Real.sqrt ((K / 20 : ℕ) : ℝ) := Real.sqrt_pos.mpr hL_pos
  have hrew : neutralWindow (3 * K + 1) R (6 * K * R) =
      windowMatrix (reweightedNeutral (fun _ => 1) (3 * K + 1)) R (6 * K * R) := by
    ext i j; simp [neutralWindow, windowMatrix, reweightedNeutral]
  rw [hrew]
  have hsqL : (1 / Real.sqrt ((K / 20 : ℕ) : ℝ)) * ((K / 20 : ℕ) : ℝ) =
      Real.sqrt ((K / 20 : ℕ) : ℝ) := by
    field_simp [hsL_pos.ne']
    exact (Real.sq_sqrt hL_pos.le).symm
  have hw1 : (28 / 100 : ℝ) * Real.sqrt ((K / 20 : ℕ) : ℝ) ≤
      (1 / Real.sqrt ((K / 20 : ℕ) : ℝ)) * ∑ k ∈ Icc 2 (3 * K + 1), (1 : ℝ) *
        ∑ l ∈ Ico (6 * K + K / 20 - 2) (6 * K + K / 20 - 2 + K / 20),
          floorGraph k (2 + 0) (2 + l) := by
    have h1 := halfCutoff_full_window_prime_sum (Q := 3 * K + 1) (p₀ := 0)
      (q₀ := 6 * K + K / 20 - 2) (L := K / 20)
      (P := (Icc (21 * K / 10 + 1) (3 * K)).filter Nat.Prime)
      (Finset.filter_subset_filter _ (Finset.Icc_subset_Icc (by omega) (by omega)))
      (fun p hp => by
        rcases Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1 with ⟨_, _⟩
        constructor <;> omega)
    calc (28 / 100 : ℝ) * Real.sqrt ((K / 20 : ℕ) : ℝ)
        ≤ (∑ p ∈ (Icc (21 * K / 10 + 1) (3 * K)).filter Nat.Prime, Real.log p / p) *
            Real.sqrt ((K / 20 : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right hS₁ hsL_pos.le
      _ = (1 / Real.sqrt ((K / 20 : ℕ) : ℝ)) * (((K / 20 : ℕ) : ℝ) *
            ∑ p ∈ (Icc (21 * K / 10 + 1) (3 * K)).filter Nat.Prime, Real.log p / p) := by
          rw [← mul_assoc, hsqL, mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)
  have hw2 : (20 / 100 : ℝ) * Real.sqrt ((K / 20 : ℕ) : ℝ) ≤
      (1 / Real.sqrt ((K / 20 : ℕ) : ℝ)) * ∑ k ∈ Icc 2 (3 * K + 1), (1 : ℝ) *
        ∑ l ∈ Ico (9 * K + 2 + K / 20) (9 * K + 2 + K / 20 + K / 20),
          floorGraph k (2 + 1) (2 + l) := by
    have h1 := halfCutoff_full_window_prime_sum (Q := 3 * K + 1) (p₀ := 1)
      (q₀ := 9 * K + 2 + K / 20) (L := K / 20)
      (P := (Icc (23 * K / 10 + 2) (3 * K)).filter Nat.Prime)
      (Finset.filter_subset_filter _ (Finset.Icc_subset_Icc (by omega) (by omega)))
      (fun p hp => by
        rcases Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1 with ⟨_, _⟩
        constructor <;> omega)
    calc (20 / 100 : ℝ) * Real.sqrt ((K / 20 : ℕ) : ℝ)
        ≤ (∑ p ∈ (Icc (23 * K / 10 + 2) (3 * K)).filter Nat.Prime, Real.log p / p) *
            Real.sqrt ((K / 20 : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right hS₂ hsL_pos.le
      _ = (1 / Real.sqrt ((K / 20 : ℕ) : ℝ)) * (((K / 20 : ℕ) : ℝ) *
            ∑ p ∈ (Icc (23 * K / 10 + 2) (3 * K)).filter Nat.Prime, Real.log p / p) := by
          rw [← mul_assoc, hsqL, mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)
  have hu_raw := bilin_reweightedNeutral_clusterVec_le (ω := fun _ => 1) (fun _ => zero_le_one)
    (R₀ := 2) (Q := 3 * K + 1) (J₀ := 10 * K) (p₀ := 0) (q₀ := 6 * K + K / 20 - 2) (L := K / 20)
    (by norm_num) (by omega) (by omega) (by omega) a
  have hv_raw := bilin_reweightedNeutral_clusterVec_le (ω := fun _ => 1) (fun _ => zero_le_one)
    (R₀ := 2) (Q := 3 * K + 1) (J₀ := 10 * K) (p₀ := 1) (q₀ := 9 * K + 2 + K / 20) (L := K / 20)
    (by norm_num) (by omega) (by omega) (by omega) a
  have hcross_raw := abs_bilin_reweightedNeutral_clusterVec_le (fun _ => (1 : ℝ))
    (R₀ := 2) (Q := 3 * K + 1) (J₀ := 10 * K)
    (p₁ := 0) (q₁ := 6 * K + K / 20 - 2) (L₁ := K / 20)
    (p₂ := 1) (q₂ := 9 * K + 2 + K / 20) (L₂ := K / 20) (d := K / 20)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) a
  have hjet_7 : 1 + (Real.sqrt ((K / 20 : ℕ) : ℝ) + Real.sqrt ((K / 20 : ℕ) : ℝ) +
      Real.sqrt (((K / 20 : ℕ) : ℝ) * ((K / 20 : ℕ) : ℝ))) * (2 / ((K / 20 : ℕ) : ℝ)) ≤ 7 := by
    rw [Real.sqrt_mul_self hL_pos.le]
    have hsL_le : Real.sqrt ((K / 20 : ℕ) : ℝ) ≤ ((K / 20 : ℕ) : ℝ) := by
      have h1 : (1 : ℝ) ≤ Real.sqrt ((K / 20 : ℕ) : ℝ) := by
        rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by exact_mod_cast (show 1 ≤ K / 20 by omega))
      have := mul_le_mul_of_nonneg_right h1 hsL_pos.le
      rwa [one_mul, Real.mul_self_sqrt hL_pos.le] at this
    have hmul : (Real.sqrt ((K / 20 : ℕ) : ℝ) + Real.sqrt ((K / 20 : ℕ) : ℝ) +
        ((K / 20 : ℕ) : ℝ)) * (2 / ((K / 20 : ℕ) : ℝ)) ≤
        (3 * ((K / 20 : ℕ) : ℝ)) * (2 / ((K / 20 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have heq6 : (3 * ((K / 20 : ℕ) : ℝ)) * (2 / ((K / 20 : ℕ) : ℝ)) = 6 := by
      field_simp [hL_pos.ne']; ring
    linarith [hmul, heq6]
  have hcont_21 := halfCutoff_contact_cross_bound hK hC
  have hsK_le : Real.sqrt K ≤ 5 * Real.sqrt ((K / 20 : ℕ) : ℝ) := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 5), ← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt (by exact_mod_cast (show K ≤ 25 * (K / 20) by omega))
  have ha_L : Real.log (((2 + 10 * K : ℕ) : ℝ) + 1) + 1 + a ≤
      (1 / 200 : ℝ) * Real.sqrt ((K / 20 : ℕ) : ℝ) - 50 := by
    have h1 := log_le_eps_mul_sqrt_add (x := ((2 + 10 * K : ℕ) : ℝ) + 1) (ε := 1 / 8000)
      (by positivity) (by norm_num)
    norm_num at h1
    have hsq : Real.sqrt (((2 + 10 * K : ℕ) : ℝ) + 1) ≤ 4 * Real.sqrt K := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4), ← Real.sqrt_mul (by norm_num)]
      refine Real.sqrt_le_sqrt ?_
      have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
      push_cast; linarith
    linarith [h1, hsq, hsK_le, ha, Real.sqrt_nonneg K, hsL_pos]
  have hu_le : bilin (windowMatrix (reweightedNeutral (fun _ => 1) (3 * K + 1)) 2 (10 * K) +
        Matrix.diagonal (fun _ : Fin (10 * K) => a))
      (fun j : Fin (10 * K) => clusterVec 0 (6 * K + K / 20 - 2) (K / 20) j)
      (fun j : Fin (10 * K) => clusterVec 0 (6 * K + K / 20 - 2) (K / 20) j) ≤
      -((55 / 200 : ℝ) * Real.sqrt ((K / 20 : ℕ) : ℝ) + 50) := by
    linarith [hu_raw, hw1, ha_L]
  have hv_le : bilin (windowMatrix (reweightedNeutral (fun _ => 1) (3 * K + 1)) 2 (10 * K) +
        Matrix.diagonal (fun _ : Fin (10 * K) => a))
      (fun j : Fin (10 * K) => clusterVec 1 (9 * K + 2 + K / 20) (K / 20) j)
      (fun j : Fin (10 * K) => clusterVec 1 (9 * K + 2 + K / 20) (K / 20) j) ≤
      -((39 / 200 : ℝ) * Real.sqrt ((K / 20 : ℕ) : ℝ) + 50) := by
    linarith [hv_raw, hw2, ha_L]
  have huv_le : |bilin (windowMatrix (reweightedNeutral (fun _ => 1) (3 * K + 1)) 2 (10 * K) +
        Matrix.diagonal (fun _ : Fin (10 * K) => a))
      (fun i : Fin (10 * K) => clusterVec 0 (6 * K + K / 20 - 2) (K / 20) i)
      (fun j : Fin (10 * K) => clusterVec 1 (9 * K + 2 + K / 20) (K / 20) j)| ≤
      (21 / 100 : ℝ) * Real.sqrt ((K / 20 : ℕ) : ℝ) + 7 := by
    linarith [hcross_raw, hjet_7, hcont_21]
  refine two_le_hermNegIndex_reweightedNeutral_of_coarse (R₀ := 2) (m := (R + 1) / 2)
    (R := R) (J₀ := 10 * K) (J := 6 * K * R) (Q := 3 * K + 1) (by norm_num) (by omega)
    (by omega) (by
      have hm_hi : 2 * ((R + 1) / 2) ≤ R + 1 := by omega
      have hmul : (5 * K + 1) * (2 * ((R + 1) / 2)) ≤ (5 * K + 1) * (R + 1) :=
        Nat.mul_le_mul_left _ hm_hi
      have h1 : ((R + 1) / 2) * 2 + ((R + 1) / 2) * (10 * K) =
          (5 * K + 1) * (2 * ((R + 1) / 2)) := by ring
      have h2 : (5 * K + 1) * (R + 1) ≤ R + 6 * K * R := by
        have hKR : 5 * K + 1 ≤ K * R := by
          calc 5 * K + 1 ≤ 6 * K := by omega
            _ = K * 6 := mul_comm _ _
            _ ≤ K * R := Nat.mul_le_mul_left K hR
        calc (5 * K + 1) * (R + 1) = 5 * (K * R) + R + (5 * K + 1) := by ring
          _ ≤ 5 * (K * R) + R + K * R := Nat.add_le_add_left hKR _
          _ = R + 6 * K * R := by ring
      exact (h1.symm ▸ hmul).trans h2)
    (fun _ => 1) a
    (clusterVec 0 (6 * K + K / 20 - 2) (K / 20))
    (clusterVec 1 (9 * K + 2 + K / 20) (K / 20))
    (M := (21 / 100 : ℝ) * Real.sqrt ((K / 20 : ℕ) : ℝ) + 7)
    (α := -((55 / 200 : ℝ) * Real.sqrt ((K / 20 : ℕ) : ℝ) + 50))
    (γ := -((39 / 200 : ℝ) * Real.sqrt ((K / 20 : ℕ) : ℝ) + 50))
    (by positivity) hu_le hv_le huv_le (by linarith [hsL_pos]) ?_
  nlinarith [Real.sq_sqrt hL_pos.le, hsL_pos]

end GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow

end

