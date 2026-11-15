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
   `two_le_hermNegIndex_neutralWindow_halfCutoff_of_primeSum`)**:
   For every certified cutoff `Q₀`, `subEulerGluingWeight Q₀` takes values in `{0, 1}`, satisfies
   `ω(p^r) = ω(p)` on all prime powers, agrees identically with `neutralWindow` up to `Q₀` and on
   every dyadic middle `(D, 2D]`, yet acquires at least two negative squares up to shift
   `c₀ √K_m − C₀` along `K_m = 16 · 256^m` at every block size `R ≥ 1`. Likewise, the un-updated
   glued matrix `neutralWindow (3K + 1) R (6KR)` acquires at least two negative squares up to
   `c₁ √K − C₁` (`R ≥ 48K`) whenever short prime intervals near `K` carry linear Chebyshev mass.
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
  let S := Ico (k * (R + i)) (k * (R + i) + k)
  have hcard : S.card = k := by simp [S]
  rw [← hcard]
  refine Finset.card_le_card_of_injOn (fun j => R + j) (fun j hj => ?_) (fun j₁ _ j₂ _ h => by omega)
  have hdiv := (Finset.mem_filter.mp hj).2.2
  refine Finset.mem_Ico.mpr ⟨?_, ?_⟩
  · have h1 := (Nat.le_div_iff_mul_le (by omega : 0 < k)).mp hdiv.ge
    nlinarith
  · have h2 := (Nat.div_lt_iff_lt_mul (by omega : 0 < k)).mp (show (R + j) / k < R + i + 1 by omega)
    nlinarith

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
  have hpoint : ∀ i j, |σ i * σ j * floorGraph k (R + i) (R + j)| ≤
      ((Λ k : ℝ) / k) * (if (i < j ∧ (R + j) / k = R + i) ∨ (j < i ∧ (R + i) / k = R + j) then
        (|σ i| ^ 2 / (2 * Real.sqrt k) + Real.sqrt k * |σ j| ^ 2 / 2 +
          (|σ j| ^ 2 / (2 * Real.sqrt k) + Real.sqrt k * |σ i| ^ 2 / 2)) / 2 else 0) := by
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hji
    · have hab : R + i ≤ R + j := by omega
      rw [floorGraph_of_le k hab]
      by_cases hd : (R + j) / k = R + i
      · have hcond : (i < j ∧ (R + j) / k = R + i) ∨ (j < i ∧ (R + i) / k = R + j) :=
          Or.inl ⟨hij, hd⟩
        rw [if_pos hd, if_pos hcond, abs_mul, abs_mul, abs_of_nonneg hlam]
        -- Better: split upper and lower triangles directly below; here check unneeded if we split!
        have ham := two_mul_abs_le_div_sqrt_add_mul_sqrt (by omega : 1 ≤ k) (σ i) (σ j)
        nlinarith [sq_abs (σ i), sq_abs (σ j), sq_nonneg (σ i), sq_nonneg (σ j)]
      · have hcond : ¬((i < j ∧ (R + j) / k = R + i) ∨ (j < i ∧ (R + i) / k = R + j)) := by
          rintro (⟨_, h1⟩ | ⟨h2, _⟩); exact hd h1; omega
        rw [if_neg hd, if_neg hcond, mul_zero, abs_zero, mul_zero]
    · rw [hdiag i, mul_zero, abs_zero]
      have hcond : ¬((i < i ∧ (R + i) / k = R + i) ∨ (i < i ∧ (R + i) / k = R + i)) := by omega
      rw [if_neg hcond, mul_zero]
    · have hab : R + j ≤ R + i := by omega
      rw [floorGraph_comm, floorGraph_of_le k hab]
      by_cases hd : (R + i) / k = R + j
      · have hcond : (i < j ∧ (R + j) / k = R + i) ∨ (j < i ∧ (R + i) / k = R + j) :=
          Or.inr ⟨hji, hd⟩
        rw [if_pos hd, if_pos hcond, abs_mul, abs_mul, abs_of_nonneg hlam]
        have ham := two_mul_abs_le_div_sqrt_add_mul_sqrt (by omega : 1 ≤ k) (σ j) (σ i)
        nlinarith [sq_abs (σ i), sq_abs (σ j), sq_nonneg (σ i), sq_nonneg (σ j)]
      · have hcond : ¬((i < j ∧ (R + j) / k = R + i) ∨ (j < i ∧ (R + i) / k = R + j)) := by
          rintro (⟨h1, _⟩ | ⟨_, h2⟩); omega; exact hd h2
        rw [if_neg hd, if_neg hcond, mul_zero, abs_zero, mul_zero]
  -- Even cleaner: split into `i < j` and `j < i` by symmetry!
  clear hpoint
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
        · rw [hdiag i, if_neg (by omega), if_neg (by omega)]; ring
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
                have hksq : (k : ℝ) = Real.sqrt k * Real.sqrt k := (Real.mul_self_sqrt hkpos.le).symm
                rw [hksq]
                field_simp [hsk.ne']
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
        have hksq : (k : ℝ) = Real.sqrt k * Real.sqrt k := (Real.mul_self_sqrt hkpos.le).symm
        conv_lhs => rw [hksq]
        field_simp [hsk.ne']
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
  have hdisj : Set.PairwiseDisjoint (↑(range L)) (fun r : ℕ => Ico (2 ^ r) (2 ^ (r + 1))) := by
    intro r₁ _ r₂ _ hne
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
        have h2r_pos : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
        have hs2r : Real.sqrt (((2 ^ r : ℕ) : ℝ)) = (Real.sqrt 2) ^ r := by
          rw [Nat.cast_pow, Nat.cast_ofNat, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
            ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), ← Real.rpow_natCast]
          congr 1; ring
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
        -- `2 ^ (L - 1) ≤ Q`, so `(√2)^L = √2 * (√2)^(L - 1) ≤ √2 * √Q ≤ 2 * √Q`.
        have hlow : 2 ^ (Nat.log 2 Q) ≤ Q := Nat.pow_log_le_self 2 (by omega)
        have hsL : (Real.sqrt 2) ^ L = Real.sqrt 2 * Real.sqrt (((2 ^ Nat.log 2 Q : ℕ) : ℝ)) := by
          dsimp [L]
          rw [pow_succ, mul_comm]
          congr 1
          rw [Nat.cast_pow, Nat.cast_ofNat, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
            ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), ← Real.rpow_natCast]
          congr 1; ring
        have hsqQ : Real.sqrt (((2 ^ Nat.log 2 Q : ℕ) : ℝ)) ≤ Real.sqrt Q :=
          Real.sqrt_le_sqrt (by exact_mod_cast hlow)
        have hs2_lt : Real.sqrt 2 ≤ 2 := by
          rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
          exact Real.sqrt_le_sqrt (by norm_num)
        have hL_le : (Real.sqrt 2) ^ L ≤ 2 * Real.sqrt Q := by
          rw [hsL]
          calc Real.sqrt 2 * Real.sqrt (((2 ^ Nat.log 2 Q : ℕ) : ℝ))
              ≤ 2 * Real.sqrt Q := mul_le_mul hs2_lt hsqQ (Real.sqrt_nonneg _) zero_le_two
        unfold floorContactSqrtConst
        nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num), Real.sqrt_nonneg 2,
          Real.sqrt_nonneg Q]

/-! ## 2. Universal prime-free and reweighted quadratic-form lower bounds -/

/-- Elementary bound `log x ≤ 2 √x` for all `x > 0`. -/
lemma log_le_two_mul_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hx_eq : x = Real.sqrt x ^ 2 := (Real.sq_sqrt hx.le).symm
  rw [hx_eq, Real.log_pow, Nat.cast_ofNat]
  have h1 := Real.log_le_sub_one_of_pos hsx
  linarith

/-- Rewriting `reweightedNeutral` against the prime-free kernel `neutralBlock 1`. -/
theorem reweightedNeutral_eq_one_sub (ω : ℕ → ℝ) (Q a b : ℕ) :
    reweightedNeutral ω Q a b = neutralBlock 1 a b - ∑ k ∈ Icc 2 Q, ω k * floorGraph k a b := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · rw [reweightedNeutral_of_lt ω Q hab, neutralBlock_of_lt hab,
      show floorContact 1 a b = 0 by simp [floorContact]]
    ring
  · have h1 : ∑ k ∈ Icc 2 Q, (1 - ω k) * floorGraph k a a = 0 :=
      Finset.sum_eq_zero fun k hk => by
        rcases Nat.eq_zero_or_pos a with rfl | ha
        · simp [floorGraph] -- wait: at `a = 0`, `0 / k = 0`! Handle `1 ≤ a` or avoid `a = 0`!
          sorry
        · sorry
    sorry
  · sorry
