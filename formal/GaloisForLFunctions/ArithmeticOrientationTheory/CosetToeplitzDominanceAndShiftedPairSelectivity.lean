import GaloisForLFunctions.ArithmeticOrientationTheory.TheRatioPartDecomposesOverCosets
import GaloisForLFunctions.ArithmeticOrientationTheory.TheEffectivityConeFromSections
import GaloisForLFunctions.ArithmeticIncidencePositivity.TotalLatticeCrossingLaw

/-!
# Beyond the coset law: unit-coset scale suppression, archimedean dominance, and shifted-pair selectivity

By the coset law (`towerOddPrimeSide_eq`), the odd prime side of the tower of `p` for a profile
`q : ℕ → ℝ` supported on `[1, X]` is

    towerOddPrimeSide q X p K =
      log p · (2 Σ_{a' ∈ pfreeLabels p X} cosetToeplitz q p X (2K) a' − (S_p(q, K)² − q(1)²)).

This module resolves **Open Problem 2** ("Beyond the coset law") by proving the exact algebraic
structure of the unit-coset difference, characterizing the class of profiles on which the coset
Toeplitz forms plus the archimedean–polar odd kernel dominate the unit-coset Hankel square, and
establishing the selectivity of that class against the non-tempered shifted pair `ζ(s − a)ζ(s + a)`:

1. **Axis-pair cancellation and `q(1)`-invariance (`two_mul_ratioCorr_sub_productCorr_update_one`,
   `towerOddPrimeSide_update_one`, `latticeOddPrimeSide_update_one`, `towerOddPrimeSide_eq_interior`).**
   For every integer `m ≥ 2` and `X ≥ 1`, the axis contribution `2 q(1) q(m)` to `2 R_q(m)` cancels
   the boundary divisors `d = 1` and `d = m` in `P_q(m) = Σ_{d ∣ m} q(d) q(m/d)` identically. Thus
   `2 R_q(m) − P_q(m)`, `towerOddPrimeSide`, and `latticeOddPrimeSide` are completely independent of
   `q(1)`. On the unit coset `a' = 1`, the `i = 0` axis slice of `2 cosetToeplitz` cancels the cross
   term `2 q(1) S_p^+(q, K)` of `S_p(q, K)² − q(1)²`, reducing the unit-coset Hankel term to the
   interior square `towerInteriorMellin q p K ^ 2 = (Σ_{1 ≤ i ≤ K} q(p^i) p^{−i/2})²`.

2. **The unit-coset scale-suppression identity (`towerInteriorMellin_sq_eq`,
   `unitCoset_toeplitz_sub_hankel_eq`, `towerOddPrimeSide_eq_scaleSuppressed_sub_diag`).**
   Expanding `towerInteriorMellin q p K ^ 2` into its diagonal `Σ_{1 ≤ i ≤ K} p^{−i} q(p^i)²` and
   off-diagonal correlations `2 Σ_{k ≥ 1} p^{−k/2} Σ_{i ≥ 1} p^{−i} q(p^i) q(p^{i+k})` proves that on
   the unit coset, twice the interior Toeplitz form minus the interior Hankel square equals

       2 Σ_{k=1}^K p^{−k/2} Σ_{i=1}^K (1 − p^{−i}) q(p^i) q(p^{i+k}) − Σ_{i=1}^K p^{−i} q(p^i)².

   Every off-diagonal pair `(p^i, p^{i+k})` carries the strictly positive scale-suppressed weight
   `(1 − p^{−i}) p^{−k/2} > 0`; the reflected diagonal `−log p Σ_{i=1}^K p^{−i} q(p^i)²` is the sole
   negative term of the odd prime side on coset-coherent profiles.

3. **Archimedean–polar dominance and Cauchy–Schwarz control (`archReflectedDiagWeight`,
   `towerArchDiagForm`, `towerTotalOddForm`, `towerTotalOddForm_nonneg_iff`,
   `towerInteriorMellin_sq_le_half_towerArchDiagForm`, `towerTotalOddForm_ge_half_towerArchDiagForm`).**
   Adding the archimedean–polar reflected-diagonal weight
   `W_arch(n) = −archPairKernel(−log n, log n) = (n − 1)²/(2n) − n³/(n⁴ − 1)` turns the diagonal
   coefficient at `p^i` into `−totalLatticeCrossingKernel(p^i, p^i) = W_arch(p^i) − log p / p^i`,
   which is strictly positive iff `p^i ≥ 4` (every prime power except `2` and `3`). Moreover, for all
   `n ≥ 4`, `W_arch(n) > n / 6`, so the geometric Cauchy–Schwarz ratio satisfies
   `Σ_{p^i ≥ 4} (log p · p^{−i}) / W_arch(p^i) ≤ 1 / 2`. Consequently, for **every** profile `q` of
   **arbitrary sign** (with `q(2) = 0` at `p = 2` and `q(3) = 0` at `p = 3`), the archimedean
   diagonal alone dominates twice the interior Hankel square:
   `log p · towerInteriorMellin q p K ^ 2 ≤ (1 / 2) towerArchDiagForm q p K`.

4. **The shifted-pair rank-two coset law and selectivity against `ζ(s − a)ζ(s + a)`
   (`shiftedTowerProductPart_eq_add_sq`, `shiftedTowerOddPrimeSide_eq`,
   `two_mul_towerProductPart_lt_shiftedTowerProductPart`, `shifted_productAtom_gt_ratioAtom_of_one_le`,
   `shiftedTowerTotalOddForm_point_neg_of_one_le`, `sum_shiftedHankelRatio_gt_two_mul`).**
   For the shifted pair `Λ_a(n) = Λ(n)(n^a + n^{−a})`, the tower product part is no longer rank one,
   but the sum of **two** shifted Mellin squares at `s = ½ − a` and `s = ½ + a`. For every `a ≠ 0`,
   the shifted product part strictly exceeds twice the unshifted product part, its normalized point
   charges `log p (p^{2ia} + p^{−2ia})` grow exponentially with `i`, its Cauchy–Schwarz ratio
   `Σ_{i=1}^K (p^{2ia} + p^{−2ia}) > 2K` diverges as `K → ∞`, and for `|a| ≥ 1` both the off-diagonal
   tower comparison and the reflected-diagonal dominance reverse at every prime power `p^i ≥ 4`.
-/

open Finset ArithmeticFunction
open GaloisForLFunctions.ArithmeticIncidencePositivity

namespace GaloisForLFunctions.ArithmeticOrientationTheory

noncomputable section
set_option autoImplicit false

/-! ### Part I: Axis-pair cancellation and `q(1)`-invariance -/

/-- Splitting `range (N + 1)` at `0` into `f 0` and `Icc 1 N`. -/
theorem sum_range_succ_eq_zero_add_sum_Icc (f : ℕ → ℝ) (N : ℕ) :
    ∑ i ∈ range (N + 1), f i = f 0 + ∑ i ∈ Icc 1 N, f i := by
  have h : range (N + 1) = insert 0 (Icc 1 N) := by
    ext i
    simp only [mem_range, mem_insert, mem_Icc]
    omega
  have hnot : (0 : ℕ) ∉ Icc 1 N := by simp
  rw [h, sum_insert hnot]

/-- For `X ≥ 1` and `m ≥ 2`, the ratio correlation splits into the axis term `q(1) q(m)` and the
interior sum over `a ∈ Icc 2 X`. -/
theorem ratioCorr_eq_one_add_Icc_two (q : ℕ → ℝ) {X m : ℕ} (hX : 1 ≤ X) :
    ratioCorr q X m = q 1 * q m + ∑ a ∈ Icc 2 X, q a * q (a * m) := by
  unfold ratioCorr
  have hIcc : Icc 1 X = insert 1 (Icc 2 X) := by
    ext a
    simp only [mem_Icc, mem_insert]
    omega
  have hnotmem : (1 : ℕ) ∉ Icc 2 X := by simp
  rw [hIcc, sum_insert hnotmem, one_mul]

/-- For `m ≥ 2`, the product correlation splits into `2 q(1) q(m)` (from `d = 1` and `d = m`) and
the proper-divisor sum over `(m.divisors.erase 1).erase m`. -/
theorem productCorr_eq_two_mul_one_add_proper (q : ℕ → ℝ) {m : ℕ} (hm : 2 ≤ m) :
    productCorr q m =
      2 * (q 1 * q m) + ∑ d ∈ (m.divisors.erase 1).erase m, q d * q (m / d) := by
  unfold productCorr
  have h1mem : 1 ∈ m.divisors := Nat.one_mem_divisors.2 (by omega)
  have hmmem : m ∈ m.divisors.erase 1 :=
    mem_erase.2 ⟨by omega, Nat.mem_divisors_self m (by omega)⟩
  rw [← sum_erase_add _ _ h1mem, ← sum_erase_add _ _ hmmem]
  rw [Nat.div_one, Nat.div_self (by omega)]
  ring

/-- **Axis-pair cancellation**: for every `X ≥ 1` and `m ≥ 2`, `2 R_q(m) − P_q(m)` is independent
of `q(1)`. -/
theorem two_mul_ratioCorr_sub_productCorr_eq_interior (q : ℕ → ℝ) {X m : ℕ}
    (hX : 1 ≤ X) (hm : 2 ≤ m) :
    2 * ratioCorr q X m - productCorr q m =
      2 * ∑ a ∈ Icc 2 X, q a * q (a * m) -
        ∑ d ∈ (m.divisors.erase 1).erase m, q d * q (m / d) := by
  rw [ratioCorr_eq_one_add_Icc_two q hX, productCorr_eq_two_mul_one_add_proper q hm]
  ring

/-- Updating `q` at `1` leaves `2 R_q(m) − P_q(m)` unchanged for every `X ≥ 1` and `m ≥ 2`. -/
theorem two_mul_ratioCorr_sub_productCorr_update_one (q : ℕ → ℝ) (c : ℝ) {X m : ℕ}
    (hX : 1 ≤ X) (hm : 2 ≤ m) :
    2 * ratioCorr (Function.update q 1 c) X m - productCorr (Function.update q 1 c) m =
      2 * ratioCorr q X m - productCorr q m := by
  rw [two_mul_ratioCorr_sub_productCorr_eq_interior _ hX hm,
    two_mul_ratioCorr_sub_productCorr_eq_interior q hX hm]
  congr 1
  · congr 1
    refine sum_congr rfl fun a ha => ?_
    have ha2 : 2 ≤ a := (mem_Icc.1 ha).1
    have ham : 2 ≤ a * m := by nlinarith
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  · refine sum_congr rfl fun d hd => ?_
    have hdm : d ≠ m := (mem_erase.1 hd).1
    have hd1 : d ≠ 1 := (mem_erase.1 (mem_erase.1 hd).2).1
    have hdiv : d ∈ m.divisors := mem_of_mem_erase (mem_of_mem_erase hd)
    have hdvd : d ∣ m := Nat.dvd_of_mem_divisors hdiv
    have hquot1 : m / d ≠ 1 := by
      intro hq1
      have hmul := Nat.div_mul_cancel hdvd
      rw [hq1, one_mul] at hmul
      exact hdm hmul
    rw [Function.update_of_ne hd1, Function.update_of_ne hquot1]

/-- **`towerOddPrimeSide` is independent of `q(1)`.** -/
theorem towerOddPrimeSide_update_one (q : ℕ → ℝ) (c : ℝ) {X p : ℕ} (hX : 1 ≤ X)
    (hp : p.Prime) (K : ℕ) :
    towerOddPrimeSide (Function.update q 1 c) X p K = towerOddPrimeSide q X p K := by
  unfold towerOddPrimeSide
  refine sum_congr rfl fun k hk => ?_
  have hk1 : 1 ≤ k := (mem_Icc.1 hk).1
  have hpk : 2 ≤ p ^ k := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
  rw [two_mul_ratioCorr_sub_productCorr_update_one q c hX hpk]

/-- **`latticeOddPrimeSide` is independent of `q(1)`.** -/
theorem latticeOddPrimeSide_update_one (q : ℕ → ℝ) (c : ℝ) {X : ℕ} (hX : 1 ≤ X)
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (K : ℕ) :
    latticeOddPrimeSide (Function.update q 1 c) X S K = latticeOddPrimeSide q X S K := by
  unfold latticeOddPrimeSide
  refine sum_congr rfl fun p hp => sum_congr rfl fun k _ => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [vonMangoldt_apply_one]
  · have hpk : 2 ≤ p ^ k := le_trans (hS p hp).two_le (Nat.le_self_pow (by omega) p)
    rw [two_mul_ratioCorr_sub_productCorr_update_one q c hX hpk]

/-- The interior tower Mellin sum `S_p^+(q, K) = Σ_{1 ≤ i ≤ K} q(p^i) p^{−i/2}` over positive
exponents `i ≥ 1`. -/
def towerInteriorMellin (q : ℕ → ℝ) (p K : ℕ) : ℝ :=
  ∑ i ∈ Icc 1 K, q (p ^ i) * (p : ℝ) ^ (-(i : ℝ) / 2)

/-- Splitting the tower Mellin sum at `i = 0`: `S_p(q, K) = q(1) + S_p^+(q, K)`. -/
theorem towerMellin_eq_add_interior (q : ℕ → ℝ) (p K : ℕ) :
    towerMellin q p K = q 1 + towerInteriorMellin q p K := by
  unfold towerMellin towerInteriorMellin
  rw [sum_range_succ_eq_zero_add_sum_Icc]
  simp

/-- Setting `q(1) = 0` turns `towerMellin` into `towerInteriorMellin`. -/
theorem towerMellin_update_one_zero (q : ℕ → ℝ) {p : ℕ} (hp : p.Prime) (K : ℕ) :
    towerMellin (Function.update q 1 0) p K = towerInteriorMellin q p K := by
  rw [towerMellin_eq_add_interior, Function.update_self, zero_add]
  unfold towerInteriorMellin
  refine sum_congr rfl fun i hi => ?_
  have hi1 : 1 ≤ i := (mem_Icc.1 hi).1
  have hpi : p ^ i ≠ 1 := by
    have : 2 ≤ p ^ i := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
    omega
  rw [Function.update_of_ne hpi]

/-- On every non-unit coset `a' ≠ 1`, updating `q(1)` leaves `cosetToeplitz` unchanged. -/
theorem cosetToeplitz_update_one_of_ne_one (q : ℕ → ℝ) (c : ℝ) {p : ℕ} (hp : p.Prime)
    (X L : ℕ) {a' : ℕ} (ha' : a' ∈ pfreeLabels p X) (hne : a' ≠ 1) :
    cosetToeplitz (Function.update q 1 c) p X L a' = cosetToeplitz q p X L a' := by
  have ha2 : 2 ≤ a' := by
    have h1 : 1 ≤ a' := (mem_Icc.1 (mem_filter.1 ha').1).1
    omega
  unfold cosetToeplitz
  refine sum_congr rfl fun k _ => congrArg _ (sum_congr rfl fun i _ => ?_)
  have h1 : p ^ i * a' ≠ 1 := by
    have : 2 ≤ p ^ i * a' := by nlinarith [Nat.one_le_pow i p hp.pos]
    omega
  have h2 : p ^ (i + k) * a' ≠ 1 := by
    have : 2 ≤ p ^ (i + k) * a' := by nlinarith [Nat.one_le_pow (i + k) p hp.pos]
    omega
  rw [Function.update_of_ne h1, Function.update_of_ne h2]

/-- **The interior coset law**: for every profile `q` supported on `[1, X]` (with arbitrary `q(1)`),
`towerOddPrimeSide q X p K` is `log p` times twice the interior coset Toeplitz forms minus the
interior Mellin square `towerInteriorMellin q p K ^ 2`. -/
theorem towerOddPrimeSide_eq_interior (q : ℕ → ℝ) {X : ℕ} (hX : 1 ≤ X)
    (hq : ∀ n, X < n → q n = 0) {p : ℕ} (hp : p.Prime) {K : ℕ}
    (hK : ∀ i, K < i → q (p ^ i) = 0) :
    towerOddPrimeSide q X p K =
      Real.log p * (2 * ∑ a' ∈ pfreeLabels p X,
          cosetToeplitz (Function.update q 1 0) p X (2 * K) a' -
        towerInteriorMellin q p K ^ 2) := by
  have hq0 : ∀ n, X < n → Function.update q 1 0 n = 0 := fun n hn => by
    rw [Function.update_of_ne (by omega)]
    exact hq n hn
  have hK0 : ∀ i, K < i → Function.update q 1 0 (p ^ i) = 0 := fun i hi => by
    have hpi : p ^ i ≠ 1 := by
      have : 2 ≤ p ^ i := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
      omega
    rw [Function.update_of_ne hpi]
    exact hK i hi
  rw [← towerOddPrimeSide_update_one q 0 hX hp K,
    towerOddPrimeSide_eq (Function.update q 1 0) hq0 hp hK0,
    towerMellin_update_one_zero q hp K, Function.update_self]
  ring

/-! ### Part II: The exact unit-coset scale-suppression identity -/

/-- The interior unit-coset Toeplitz form `Σ_{1 ≤ k ≤ K} p^{−k/2} Σ_{1 ≤ i ≤ K} q(p^i) q(p^{i+k})`. -/
def interiorUnitToeplitz (q : ℕ → ℝ) (p K : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 K, (p : ℝ) ^ (-(k : ℝ) / 2) * ∑ i ∈ Icc 1 K, q (p ^ i) * q (p ^ (i + k))

/-- The scale-suppressed unit-coset Toeplitz form
`Σ_{1 ≤ k ≤ K} p^{−k/2} Σ_{1 ≤ i ≤ K} (1 − p^{−i}) q(p^i) q(p^{i+k})`. -/
def scaleSuppressedUnitToeplitz (q : ℕ → ℝ) (p K : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 K, (p : ℝ) ^ (-(k : ℝ) / 2) *
    ∑ i ∈ Icc 1 K, (1 - (p : ℝ) ^ (-(i : ℝ))) * q (p ^ i) * q (p ^ (i + k))

/-- On the unit coset `a' = 1` with `q(1) = 0` and `q(p^i) = 0` for `i > K`, `cosetToeplitz`
equals `interiorUnitToeplitz`. -/
theorem cosetToeplitz_update_one_zero_unit (q : ℕ → ℝ) {X : ℕ} (hq : ∀ n, X < n → q n = 0)
    {p : ℕ} (hp : p.Prime) {K : ℕ} (hK : ∀ i, K < i → q (p ^ i) = 0) :
    cosetToeplitz (Function.update q 1 0) p X (2 * K) 1 = interiorUnitToeplitz q p K := by
  unfold cosetToeplitz interiorUnitToeplitz
  have hinner : ∀ k : ℕ, 1 ≤ k →
      ∑ i ∈ range (Nat.log p X + 1),
          Function.update q 1 0 (p ^ i * 1) * Function.update q 1 0 (p ^ (i + k) * 1) =
        ∑ i ∈ Icc 1 K, q (p ^ i) * q (p ^ (i + k)) := by
    intro k hk1
    rw [sum_range_succ_eq_zero_add_sum_Icc]
    simp only [pow_zero, mul_one, Function.update_self, zero_mul, zero_add]
    have term_eq : ∀ i : ℕ, 1 ≤ i →
        Function.update q 1 0 (p ^ i) * Function.update q 1 0 (p ^ (i + k)) =
          q (p ^ i) * q (p ^ (i + k)) := fun i hi1 => by
      have h1 : p ^ i ≠ 1 := by
        have : 2 ≤ p ^ i := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
        omega
      have h2 : p ^ (i + k) ≠ 1 := by
        have : 2 ≤ p ^ (i + k) := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
        omega
      rw [Function.update_of_ne h1, Function.update_of_ne h2]
    have hL : ∑ i ∈ Icc 1 (Nat.log p X),
          Function.update q 1 0 (p ^ i) * Function.update q 1 0 (p ^ (i + k)) =
        ∑ i ∈ Icc 1 (Nat.log p X), q (p ^ i) * q (p ^ (i + k)) :=
      sum_congr rfl fun i hi => term_eq i (mem_Icc.1 hi).1
    rw [hL]
    rcases le_or_gt K (Nat.log p X) with hKlog | hKlog
    · symm
      refine sum_subset (Icc_subset_Icc_right hKlog) fun i hi hnot => ?_
      have hi1 : 1 ≤ i := (mem_Icc.1 hi).1
      have hiK : K < i := by simp only [mem_Icc] at hnot; omega
      rw [hK i hiK, zero_mul]
    · refine sum_subset (Icc_subset_Icc_right hKlog.le) fun i hi hnot => ?_
      have hi1 : 1 ≤ i := (mem_Icc.1 hi).1
      have hilog : Nat.log p X < i := by simp only [mem_Icc] at hnot; omega
      have hpX : X < p ^ i := by
        by_contra hle
        push Not at hle
        have := Nat.le_log_of_pow_le hp.one_lt hle
        omega
      rw [hq (p ^ i) hpX, zero_mul]
  have hsub : Icc 1 K ⊆ Icc 1 (2 * K) := Icc_subset_Icc_right (by omega)
  rw [← sum_subset hsub]
  · refine sum_congr rfl fun k hk => ?_
    rw [hinner k (mem_Icc.1 hk).1]
  · intro k hk2K hnotK
    have hk1 : 1 ≤ k := (mem_Icc.1 hk2K).1
    have hkK : K < k := by simp only [mem_Icc] at hnotK; omega
    rw [hinner k hk1]
    have hzero : ∑ i ∈ Icc 1 K, q (p ^ i) * q (p ^ (i + k)) = 0 :=
      sum_eq_zero fun i _ => by rw [hK (i + k) (by omega), mul_zero]
    rw [hzero, mul_zero]

/-- **Square of an `Icc 1 K` sum into diagonal and strict upper triangle.** -/
theorem sq_sum_Icc_eq_diag_add_upper (f : ℕ → ℝ) (K : ℕ) :
    (∑ i ∈ Icc 1 K, f i) ^ 2 =
      ∑ i ∈ Icc 1 K, f i ^ 2 + 2 * ∑ i ∈ Icc 1 K, ∑ j ∈ Icc (i + 1) K, f i * f j := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hIcc : Icc 1 (K + 1) = insert (K + 1) (Icc 1 K) := by
      ext i; simp only [mem_Icc, mem_insert]; omega
    have hnot : K + 1 ∉ Icc 1 K := by simp
    rw [hIcc, sum_insert hnot, sum_insert hnot, sum_insert hnot]
    have hempty : Icc (K + 1 + 1) (K + 1) = ∅ := by simp
    rw [hempty, sum_empty, zero_add]
    have hinner : ∑ i ∈ Icc 1 K, ∑ j ∈ Icc (i + 1) (K + 1), f i * f j =
        ∑ i ∈ Icc 1 K, (f i * f (K + 1) + ∑ j ∈ Icc (i + 1) K, f i * f j) := by
      refine sum_congr rfl fun i hi => ?_
      have hiK : i ≤ K := (mem_Icc.1 hi).2
      have hJ : Icc (i + 1) (K + 1) = insert (K + 1) (Icc (i + 1) K) := by
        ext j; simp only [mem_Icc, mem_insert]; omega
      have hnotJ : K + 1 ∉ Icc (i + 1) K := by simp
      rw [hJ, sum_insert hnotJ]
    rw [hinner, sum_add_distrib, ← sum_mul]
    linear_combination ih

/-- Shifting the upper-triangular sum `j ∈ Icc (i + 1) K` to `k ∈ Icc 1 K` for a sequence vanishing
past `K`. -/
theorem sum_Icc_upper_eq_sum_shift {f : ℕ → ℝ} {K : ℕ} (hf : ∀ m, K < m → f m = 0)
    (i : ℕ) :
    ∑ j ∈ Icc (i + 1) K, f i * f j = ∑ k ∈ Icc 1 K, f i * f (i + k) := by
  rcases le_or_gt i K with hiK | hiK
  · have hbij : ∑ j ∈ Icc (i + 1) K, f i * f j = ∑ k ∈ Icc 1 (K - i), f i * f (i + k) := by
      refine sum_bij (fun j _ => j - i) ?_ ?_ ?_ ?_
      · intro j hj
        simp only [mem_Icc] at hj ⊢
        omega
      · intro j₁ hj₁ j₂ hj₂ hsub
        simp only [mem_Icc] at hj₁ hj₂
        omega
      · intro k hk
        simp only [mem_Icc] at hk
        refine ⟨i + k, mem_Icc.2 ⟨by omega, by omega⟩, by omega⟩
      · intro j hj
        simp only [mem_Icc] at hj
        rw [Nat.add_sub_of_le (by omega)]
    rw [hbij]
    refine sum_subset (Icc_subset_Icc_right (Nat.sub_le K i)) fun k hk hnot => ?_
    simp only [mem_Icc] at hk hnot
    rw [hf (i + k) (by omega), mul_zero]
  · have hemp : Icc (i + 1) K = ∅ := Icc_eq_empty (by omega)
    rw [hemp, sum_empty]
    symm
    refine sum_eq_zero fun k hk => ?_
    have hk1 : 1 ≤ k := (mem_Icc.1 hk).1
    rw [hf (i + k) (by omega), mul_zero]

/-- **Expansion of the interior tower Mellin square**:
`towerInteriorMellin q p K ^ 2 = Σ_{1 ≤ i ≤ K} p^{−i} q(p^i)² + 2 Σ_{k=1}^K p^{−k/2} Σ_{i=1}^K p^{−i} q(p^i) q(p^{i+k})`. -/
theorem towerInteriorMellin_sq_eq (q : ℕ → ℝ) {p : ℕ} (hp : p.Prime) {K : ℕ}
    (hK : ∀ i, K < i → q (p ^ i) = 0) :
    towerInteriorMellin q p K ^ 2 =
      ∑ i ∈ Icc 1 K, (p : ℝ) ^ (-(i : ℝ)) * q (p ^ i) ^ 2 +
        2 * ∑ k ∈ Icc 1 K, (p : ℝ) ^ (-(k : ℝ) / 2) *
          ∑ i ∈ Icc 1 K, (p : ℝ) ^ (-(i : ℝ)) * q (p ^ i) * q (p ^ (i + k)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  set f : ℕ → ℝ := fun i => q (p ^ i) * (p : ℝ) ^ (-(i : ℝ) / 2) with hf_def
  have hfK : ∀ m, K < m → f m = 0 := fun m hm => by simp [hf_def, hK m hm]
  unfold towerInteriorMellin
  rw [sq_sum_Icc_eq_diag_add_upper f K]
  congr 1
  · refine sum_congr rfl fun i _ => ?_
    simp only [hf_def, mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
    have hexp : -(i : ℝ) / 2 * ((2 : ℕ) : ℝ) = -(i : ℝ) := by push_cast; ring
    rw [hexp, mul_comm]
  · congr 1
    have hshift : ∑ i ∈ Icc 1 K, ∑ j ∈ Icc (i + 1) K, f i * f j =
        ∑ i ∈ Icc 1 K, ∑ k ∈ Icc 1 K, f i * f (i + k) :=
      sum_congr rfl fun i _ => sum_Icc_upper_eq_sum_shift hfK i
    rw [hshift, sum_comm]
    refine sum_congr rfl fun k _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun i _ => ?_
    simp only [hf_def, Nat.cast_add]
    have hsplit : (p : ℝ) ^ (-((i : ℝ) + (k : ℝ)) / 2) =
        (p : ℝ) ^ (-(i : ℝ) / 2) * (p : ℝ) ^ (-(k : ℝ) / 2) := by
      rw [← Real.rpow_add hp0]
      congr 1; ring
    have hdouble : (p : ℝ) ^ (-(i : ℝ) / 2) * (p : ℝ) ^ (-(i : ℝ) / 2) =
        (p : ℝ) ^ (-(i : ℝ)) := by
      rw [← Real.rpow_add hp0]
      congr 1; ring
    rw [hsplit]
    linear_combination q (p ^ i) * q (p ^ (i + k)) * (p : ℝ) ^ (-(k : ℝ) / 2) * hdouble

/-- **The exact unit-coset net identity**: twice the interior unit-coset Toeplitz form minus the
interior Mellin square equals twice the scale-suppressed unit-coset Toeplitz form minus the
reflected diagonal `Σ_{1 ≤ i ≤ K} p^{−i} q(p^i)²`. -/
theorem unitCoset_toeplitz_sub_hankel_eq (q : ℕ → ℝ) {p : ℕ} (hp : p.Prime) {K : ℕ}
    (hK : ∀ i, K < i → q (p ^ i) = 0) :
    2 * interiorUnitToeplitz q p K - towerInteriorMellin q p K ^ 2 =
      2 * scaleSuppressedUnitToeplitz q p K -
        ∑ i ∈ Icc 1 K, (p : ℝ) ^ (-(i : ℝ)) * q (p ^ i) ^ 2 := by
  rw [towerInteriorMellin_sq_eq q hp hK]
  unfold interiorUnitToeplitz scaleSuppressedUnitToeplitz
  have hcombine : ∀ k ∈ Icc 1 K,
      (p : ℝ) ^ (-(k : ℝ) / 2) * ∑ i ∈ Icc 1 K, q (p ^ i) * q (p ^ (i + k)) -
        (p : ℝ) ^ (-(k : ℝ) / 2) *
          ∑ i ∈ Icc 1 K, (p : ℝ) ^ (-(i : ℝ)) * q (p ^ i) * q (p ^ (i + k)) =
      (p : ℝ) ^ (-(k : ℝ) / 2) *
        ∑ i ∈ Icc 1 K, (1 - (p : ℝ) ^ (-(i : ℝ))) * q (p ^ i) * q (p ^ (i + k)) := by
    intro k _
    rw [← mul_sub, ← sum_sub_distrib]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    ring
  have hsum := sum_congr rfl hcombine
  rw [sum_sub_distrib] at hsum
  linarith

/-- **The complete scale-suppressed coset decomposition of `towerOddPrimeSide`**:
the odd prime side of the tower of `p` splits into the non-unit coset Toeplitz forms (`a' ≠ 1`),
the scale-suppressed unit-coset Toeplitz form (with positive weights `1 − p^{−i} > 0`), and the
reflected diagonal `−log p Σ_{1 ≤ i ≤ K} p^{−i} q(p^i)²`. -/
theorem towerOddPrimeSide_eq_scaleSuppressed_sub_diag (q : ℕ → ℝ) {X : ℕ} (hX : 1 ≤ X)
    (hq : ∀ n, X < n → q n = 0) {p : ℕ} (hp : p.Prime) {K : ℕ}
    (hK : ∀ i, K < i → q (p ^ i) = 0) :
    towerOddPrimeSide q X p K =
      Real.log p * (2 * ∑ a' ∈ (pfreeLabels p X).erase 1, cosetToeplitz q p X (2 * K) a' +
        2 * scaleSuppressedUnitToeplitz q p K -
        ∑ i ∈ Icc 1 K, (p : ℝ) ^ (-(i : ℝ)) * q (p ^ i) ^ 2) := by
  rw [towerOddPrimeSide_eq_interior q hX hq hp hK]
  have h1mem : 1 ∈ pfreeLabels p X := by
    simp only [pfreeLabels, mem_filter, mem_Icc]
    exact ⟨⟨le_rfl, hX⟩, hp.not_dvd_one⟩
  rw [← sum_erase_add _ _ h1mem, cosetToeplitz_update_one_zero_unit q hq hp hK]
  have herase : ∑ a' ∈ (pfreeLabels p X).erase 1,
        cosetToeplitz (Function.update q 1 0) p X (2 * K) a' =
      ∑ a' ∈ (pfreeLabels p X).erase 1, cosetToeplitz q p X (2 * K) a' :=
    sum_congr rfl fun a' ha' =>
      cosetToeplitz_update_one_of_ne_one q 0 hp X (2 * K) (mem_of_mem_erase ha') (mem_erase.1 ha').1
  rw [herase]
  have hunit := unitCoset_toeplitz_sub_hankel_eq q hp hK
  congr 1
  linarith

/-! ### Part III: Archimedean–polar dominance and Cauchy–Schwarz control -/

/-- The archimedean–polar reflected-diagonal weight at `n`:
`W_arch(n) = −archPairKernel(−log n, log n) = 2 sinh²(log n / 2) − ω(2 log n)`. -/
def archReflectedDiagWeight (n : ℕ) : ℝ :=
  -archPairKernel (-Real.log n) (Real.log n)

/-- The archimedean–polar reflected-diagonal quadratic form on the tower of `p` through `p^K`:
`Σ_{1 ≤ i ≤ K} W_arch(p^i) q(p^i)²`. -/
def towerArchDiagForm (q : ℕ → ℝ) (p K : ℕ) : ℝ :=
  ∑ i ∈ Icc 1 K, archReflectedDiagWeight (p ^ i) * q (p ^ i) ^ 2

/-- The total odd tower form: `towerOddPrimeSide q X p K + towerArchDiagForm q p K`. -/
def towerTotalOddForm (q : ℕ → ℝ) (X p K : ℕ) : ℝ :=
  towerOddPrimeSide q X p K + towerArchDiagForm q p K

/-- At `(p^i, p^i)` (`i ≥ 1`), the product atom is `log p · p^{−i}`. -/
theorem productAtom_pow_self {p i : ℕ} (hp : p.Prime) (hi : 1 ≤ i) :
    productAtom (p ^ i) (p ^ i) = Real.log p * (p : ℝ) ^ (-(i : ℝ)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rw [productAtom_pow_pow hp (by omega : 1 ≤ i + i)]
  have hsq : ((p ^ (i + i) : ℕ) : ℝ) = ((p : ℝ) ^ i) ^ 2 := by
    push_cast; ring
  rw [hsq, Real.sqrt_sq (by positivity), Real.rpow_neg hp0.le, Real.rpow_natCast, div_eq_mul_inv]

/-- On the reflected diagonal `p^i` (`i ≥ 1`), the archimedean–polar weight minus the prime Hankel
diagonal weight is `−totalLatticeCrossingKernel (p^i) (p^i)`. -/
theorem archReflectedDiagWeight_sub_primeDiag_eq {p i : ℕ} (hp : p.Prime) (hi : 1 ≤ i) :
    archReflectedDiagWeight (p ^ i) - Real.log p * (p : ℝ) ^ (-(i : ℝ)) =
      -totalLatticeCrossingKernel (p ^ i) (p ^ i) := by
  unfold archReflectedDiagWeight totalLatticeCrossingKernel
  rw [productAtom_pow_self hp hi]
  ring

/-- **Exact decomposition of `towerTotalOddForm`**: adding `towerArchDiagForm` turns the reflected
diagonal into `Σ_{1 ≤ i ≤ K} (−totalLatticeCrossingKernel (p^i) (p^i)) q(p^i)²`. -/
theorem towerTotalOddForm_eq (q : ℕ → ℝ) {X : ℕ} (hX : 1 ≤ X)
    (hq : ∀ n, X < n → q n = 0) {p : ℕ} (hp : p.Prime) {K : ℕ}
    (hK : ∀ i, K < i → q (p ^ i) = 0) :
    towerTotalOddForm q X p K =
      2 * Real.log p * ∑ a' ∈ (pfreeLabels p X).erase 1, cosetToeplitz q p X (2 * K) a' +
        2 * Real.log p * scaleSuppressedUnitToeplitz q p K +
        ∑ i ∈ Icc 1 K, (-totalLatticeCrossingKernel (p ^ i) (p ^ i)) * q (p ^ i) ^ 2 := by
  unfold towerTotalOddForm towerArchDiagForm
  rw [towerOddPrimeSide_eq_scaleSuppressed_sub_diag q hX hq hp hK]
  have hdiag : ∑ i ∈ Icc 1 K, archReflectedDiagWeight (p ^ i) * q (p ^ i) ^ 2 -
        Real.log p * ∑ i ∈ Icc 1 K, (p : ℝ) ^ (-(i : ℝ)) * q (p ^ i) ^ 2 =
      ∑ i ∈ Icc 1 K, (-totalLatticeCrossingKernel (p ^ i) (p ^ i)) * q (p ^ i) ^ 2 := by
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun i hi => ?_
    have hi1 : 1 ≤ i := (mem_Icc.1 hi).1
    rw [← archReflectedDiagWeight_sub_primeDiag_eq hp hi1]
    ring
  linarith

/-- **Exact characterization of the dominance class (`towerTotalOddForm ≥ 0`)**:
on a profile `q` supported on `[1, X]`, the coset Toeplitz forms plus the archimedean–polar
reflected diagonal dominate the unit-coset Hankel square iff the non-unit coset Toeplitz sum, the
scale-suppressed unit-coset Toeplitz sum, and the net reflected diagonal have nonnegative total. -/
theorem towerTotalOddForm_nonneg_iff (q : ℕ → ℝ) {X : ℕ} (hX : 1 ≤ X)
    (hq : ∀ n, X < n → q n = 0) {p : ℕ} (hp : p.Prime) {K : ℕ}
    (hK : ∀ i, K < i → q (p ^ i) = 0) :
    0 ≤ towerTotalOddForm q X p K ↔
      0 ≤ 2 * Real.log p * ∑ a' ∈ (pfreeLabels p X).erase 1, cosetToeplitz q p X (2 * K) a' +
        2 * Real.log p * scaleSuppressedUnitToeplitz q p K +
        ∑ i ∈ Icc 1 K, (-totalLatticeCrossingKernel (p ^ i) (p ^ i)) * q (p ^ i) ^ 2 := by
  rw [towerTotalOddForm_eq q hX hq hp hK]

/-- For every integer `n ≥ 4`, the reflected-diagonal total crossing kernel is nonpositive, so
`0 ≤ −totalLatticeCrossingKernel n n`. -/
theorem neg_totalLatticeCrossingKernel_diag_nonneg_of_four_le {n : ℕ} (hn : 4 ≤ n) :
    0 ≤ -totalLatticeCrossingKernel n n := by
  have hn2 : 2 ≤ n := by omega
  have hnot : ¬ (0 < totalLatticeCrossingKernel n n) := by
    rw [totalLatticeCrossingKernel_pos_iff hn2 hn2]
    omega
  linarith [not_lt.1 hnot]

/-- Closed rational form of `archReflectedDiagWeight n` for `n ≥ 2`. -/
theorem archReflectedDiagWeight_eq {n : ℕ} (hn : 2 ≤ n) :
    archReflectedDiagWeight n =
      (((n : ℝ) - 1) ^ 2 * ((n : ℝ) ^ 4 - 1) - 2 * (n : ℝ) ^ 4) /
        (2 * (n : ℝ) * ((n : ℝ) ^ 4 - 1)) := by
  unfold archReflectedDiagWeight
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnn : (1 : ℝ) < (n : ℝ) * (n : ℝ) := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  rw [archPairKernel_neg_log_log hn0 hn0 hnn, Real.sqrt_mul_self hn0.le]
  have hpow : ((n : ℝ) * (n : ℝ)) ^ 2 = (n : ℝ) ^ 4 := by ring
  rw [hpow, ← neg_div]
  congr 1
  ring

/-- **Linear lower bound on `archReflectedDiagWeight`:** for every `n ≥ 4`,
`(n : ℝ) / 6 < archReflectedDiagWeight n`. -/
theorem div_six_lt_archReflectedDiagWeight {n : ℕ} (hn : 4 ≤ n) :
    (n : ℝ) / 6 < archReflectedDiagWeight n := by
  rw [archReflectedDiagWeight_eq (by omega)]
  set x : ℝ := (n : ℝ) with hx_def
  have hx4 : 4 ≤ x := by rw [hx_def]; exact_mod_cast hn
  have hx4_pow : 256 ≤ x ^ 4 := by
    have h2 : 16 ≤ x ^ 2 := by nlinarith
    nlinarith
  have hden : 0 < 2 * x * (x ^ 4 - 1) := by nlinarith
  rw [div_lt_div_iff₀ (by norm_num) hden]
  have hid : ((x - 1) ^ 2 * (x ^ 4 - 1) - 2 * x ^ 4) * 6 - x * (2 * x * (x ^ 4 - 1)) =
      (4 * (x - 4) ^ 2 + 20 * (x - 4)) * (x ^ 4 - 1) + 10 * (x ^ 4 - 256) + 2538 := by ring
  have h1 : 0 ≤ (4 * (x - 4) ^ 2 + 20 * (x - 4)) * (x ^ 4 - 1) :=
    mul_nonneg (by positivity) (by linarith)
  linarith

/-- Telescoping geometric sum over `Icc m K`. -/
theorem sum_Icc_geom_mul_one_sub {r : ℝ} (m K : ℕ) (hmK : m ≤ K) :
    (∑ i ∈ Icc m K, r ^ i) * (1 - r) = r ^ m - r ^ (K + 1) := by
  induction K with
  | zero =>
    obtain rfl : m = 0 := by omega
    simp
  | succ K ih =>
    rcases eq_or_lt_of_le hmK with rfl | hlt
    · simp; ring
    · have hmK' : m ≤ K := by omega
      have hIcc : Icc m (K + 1) = insert (K + 1) (Icc m K) := by
        ext i; simp only [mem_Icc, mem_insert]; omega
      have hnot : K + 1 ∉ Icc m K := by simp
      rw [hIcc, sum_insert hnot, add_mul, ih hmK']
      ring

/-- Upper bound for a geometric sum over `Icc m K` with `0 ≤ r < 1`. -/
theorem sum_Icc_geom_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (m K : ℕ) :
    ∑ i ∈ Icc m K, r ^ i ≤ r ^ m / (1 - r) := by
  have h1r : 0 < 1 - r := by linarith
  rw [le_div_iff₀ h1r]
  rcases le_or_gt m K with hmK | hmK
  · rw [sum_Icc_geom_mul_one_sub m K hmK]
    have : 0 ≤ r ^ (K + 1) := pow_nonneg hr0 _
    linarith
  · rw [Icc_eq_empty (by omega), sum_empty, zero_mul]
    exact pow_nonneg hr0 m

/-- For every `x ≥ 5`, `6 * Real.log x ≤ (x ^ 2 - 1) / 2`. -/
theorem six_mul_log_le_sq_sub_one_div_two {x : ℝ} (hx : 5 ≤ x) :
    6 * Real.log x ≤ (x ^ 2 - 1) / 2 := by
  have hx0 : 0 < x := by linarith
  have hsplit : Real.log x = 2 * Real.log 2 + Real.log (x / 4) := by
    have h4 : x = 2 ^ 2 * (x / 4) := by ring
    conv_lhs => rw [h4]
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast; ring
  have hlog_div : Real.log (x / 4) ≤ x / 4 - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hl2 := Real.log_two_lt_d9
  have hquad : 0 ≤ (x - 5) * (x + 2) := mul_nonneg (by linarith) (by linarith)
  have hexp : x ^ 2 = (x - 5) * (x + 2) + 3 * x + 10 := by ring
  linarith

/-- **Cauchy–Schwarz ratio bound on prime towers**: for every prime `p` and `K : ℕ`, the sum of
`log p · p^{−i} / archReflectedDiagWeight (p^i)` over `i ∈ Icc 1 K` with `4 ≤ p^i` is at most
`1 / 2`. -/
theorem sum_primeDiag_div_archReflectedDiagWeight_le_half {p : ℕ} (hp : p.Prime) (K : ℕ) :
    ∑ i ∈ (Icc 1 K).filter (fun i => 4 ≤ p ^ i),
      Real.log p * (p : ℝ) ^ (-(i : ℝ)) / archReflectedDiagWeight (p ^ i) ≤ 1 / 2 := by
  have hp2 : 2 ≤ p := hp.two_le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlog0 : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  set r : ℝ := ((p : ℝ) ^ 2)⁻¹ with hr_def
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by
    rw [hr_def]
    apply inv_lt_one_of_one_lt₀
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    nlinarith
  have hterm : ∀ i ∈ (Icc 1 K).filter (fun i => 4 ≤ p ^ i),
      Real.log p * (p : ℝ) ^ (-(i : ℝ)) / archReflectedDiagWeight (p ^ i) ≤
        6 * Real.log p * r ^ i := by
    intro i hi
    have hi4 : 4 ≤ p ^ i := (mem_filter.1 hi).2
    have hW := div_six_lt_archReflectedDiagWeight hi4
    have hpi_pos : (0 : ℝ) < (p ^ i : ℕ) := by exact_mod_cast (by omega : 0 < p ^ i)
    have hdiv : Real.log p * (p : ℝ) ^ (-(i : ℝ)) / archReflectedDiagWeight (p ^ i) ≤
        Real.log p * (p : ℝ) ^ (-(i : ℝ)) / (((p ^ i : ℕ) : ℝ) / 6) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hW.le
    refine hdiv.trans (le_of_eq ?_)
    rw [Nat.cast_pow, Real.rpow_neg hp0.le, Real.rpow_natCast, hr_def, inv_pow]
    have hpow2 : ((p : ℝ) ^ 2) ^ i = (p : ℝ) ^ i * (p : ℝ) ^ i := by ring
    rw [hpow2, mul_inv]
    ring
  refine (sum_le_sum hterm).trans ?_
  rw [← mul_sum]
  have h1mr : 1 - r = ((p : ℝ) ^ 2 - 1) / (p : ℝ) ^ 2 := by
    rw [hr_def]
    field_simp
  rcases Nat.lt_or_ge p 5 with hp5 | hp5
  · -- `p = 2` or `p = 3`: `4 ≤ p^i` implies `2 ≤ i`
    have hp3 : p ≤ 3 := by
      by_contra h
      have h4 : p = 4 := by omega
      subst h4
      norm_num at hp
    have hsub : (Icc 1 K).filter (fun i => 4 ≤ p ^ i) ⊆ Icc 2 K := by
      intro i hi
      simp only [mem_filter, mem_Icc] at hi ⊢
      refine ⟨?_, hi.1.2⟩
      by_contra hi1
      obtain rfl : i = 1 := by omega
      simp only [pow_one] at hi
      omega
    have hgeom : ∑ i ∈ (Icc 1 K).filter (fun i => 4 ≤ p ^ i), r ^ i ≤ r ^ 2 / (1 - r) :=
      (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => pow_nonneg hr0 _).trans
        (sum_Icc_geom_le hr0 hr1 2 K)
    refine (mul_le_mul_of_nonneg_left hgeom (by positivity)).trans ?_
    have hr2 : r ^ 2 / (1 - r) = 1 / ((p : ℝ) ^ 2 * ((p : ℝ) ^ 2 - 1)) := by
      rw [h1mr, hr_def]
      have hp2_ne : (p : ℝ) ^ 2 - 1 ≠ 0 := by
        have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
        nlinarith
      field_simp
    rw [hr2]
    interval_cases p
    · -- `p = 2`
      simp only [Nat.cast_ofNat]
      linarith [Real.log_two_lt_d9]
    · -- `p = 3`
      simp only [Nat.cast_ofNat]
      have hl3 : Real.log 3 ≤ 2 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
        linarith
      linarith
  · -- `p ≥ 5`: `Icc 1 K`
    have hsub : (Icc 1 K).filter (fun i => 4 ≤ p ^ i) ⊆ Icc 1 K := filter_subset _ _
    have hgeom : ∑ i ∈ (Icc 1 K).filter (fun i => 4 ≤ p ^ i), r ^ i ≤ r ^ 1 / (1 - r) :=
      (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => pow_nonneg hr0 _).trans
        (sum_Icc_geom_le hr0 hr1 1 K)
    refine (mul_le_mul_of_nonneg_left hgeom (by positivity)).trans ?_
    have hr1_eq : r ^ 1 / (1 - r) = 1 / ((p : ℝ) ^ 2 - 1) := by
      rw [pow_one, h1mr, hr_def]
      have hp2_ne : (p : ℝ) ^ 2 - 1 ≠ 0 := by
        have : (5 : ℝ) ≤ p := by exact_mod_cast hp5
        nlinarith
      field_simp
    rw [hr1_eq, mul_one_div]
    have hp5' : (5 : ℝ) ≤ p := by exact_mod_cast hp5
    have hdiv_pos : 0 < (p : ℝ) ^ 2 - 1 := by nlinarith
    rw [div_le_iff₀ hdiv_pos]
    linarith [six_mul_log_le_sq_sub_one_div_two hp5']

/-- **Unconditional Cauchy–Schwarz dominance for arbitrary-sign profiles**:
for every prime `p`, every `K : ℕ`, and every profile `q : ℕ → ℝ` of **arbitrary sign** satisfying
`q 2 = 0` (when `p = 2`) and `q 3 = 0` (when `p = 3`), the archimedean–polar reflected diagonal
alone dominates twice the interior Hankel square:
`Real.log p * towerInteriorMellin q p K ^ 2 ≤ (1 / 2) * towerArchDiagForm q p K`. -/
theorem towerInteriorMellin_sq_le_half_towerArchDiagForm (q : ℕ → ℝ) {p : ℕ} (hp : p.Prime)
    (K : ℕ) (hq23 : ∀ i ∈ Icc 1 K, p ^ i < 4 → q (p ^ i) = 0) :
    Real.log p * towerInteriorMellin q p K ^ 2 ≤ (1 / 2) * towerArchDiagForm q p K := by
  set S := (Icc 1 K).filter (fun i => 4 ≤ p ^ i) with hS_def
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlog0 : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hmellin : towerInteriorMellin q p K =
      ∑ i ∈ S, q (p ^ i) * (p : ℝ) ^ (-(i : ℝ) / 2) := by
    unfold towerInteriorMellin
    symm
    refine sum_subset (filter_subset _ _) fun i hi hnot => ?_
    have hlt4 : p ^ i < 4 := by
      simp only [hS_def, mem_filter, hi, true_and, not_le] at hnot
      exact hnot
    rw [hq23 i hi hlt4, zero_mul]
  have harch : towerArchDiagForm q p K =
      ∑ i ∈ S, archReflectedDiagWeight (p ^ i) * q (p ^ i) ^ 2 := by
    unfold towerArchDiagForm
    symm
    refine sum_subset (filter_subset _ _) fun i hi hnot => ?_
    have hlt4 : p ^ i < 4 := by
      simp only [hS_def, mem_filter, hi, true_and, not_le] at hnot
      exact hnot
    rw [hq23 i hi hlt4, sq, mul_zero, mul_zero]
  rw [hmellin, harch]
  set u : ℕ → ℝ := fun i => Real.sqrt (archReflectedDiagWeight (p ^ i)) * q (p ^ i)
  set v : ℕ → ℝ := fun i => (p : ℝ) ^ (-(i : ℝ) / 2) / Real.sqrt (archReflectedDiagWeight (p ^ i))
  have huv : ∀ i ∈ S, q (p ^ i) * (p : ℝ) ^ (-(i : ℝ) / 2) = u i * v i := by
    intro i hi
    have hi4 : 4 ≤ p ^ i := (mem_filter.1 hi).2
    have hW : 0 < archReflectedDiagWeight (p ^ i) :=
      lt_trans (by positivity) (div_six_lt_archReflectedDiagWeight hi4)
    have hsq : Real.sqrt (archReflectedDiagWeight (p ^ i)) ≠ 0 := (Real.sqrt_pos.2 hW).ne'
    dsimp [u, v]
    field_simp
  have hu2 : ∀ i ∈ S, u i ^ 2 = archReflectedDiagWeight (p ^ i) * q (p ^ i) ^ 2 := by
    intro i hi
    have hi4 : 4 ≤ p ^ i := (mem_filter.1 hi).2
    have hW : 0 ≤ archReflectedDiagWeight (p ^ i) :=
      (lt_trans (by positivity) (div_six_lt_archReflectedDiagWeight hi4)).le
    dsimp [u]
    rw [mul_pow, Real.sq_sqrt hW]
  have hv2 : ∀ i ∈ S, Real.log p * v i ^ 2 =
      Real.log p * (p : ℝ) ^ (-(i : ℝ)) / archReflectedDiagWeight (p ^ i) := by
    intro i hi
    have hi4 : 4 ≤ p ^ i := (mem_filter.1 hi).2
    have hW : 0 ≤ archReflectedDiagWeight (p ^ i) :=
      (lt_trans (by positivity) (div_six_lt_archReflectedDiagWeight hi4)).le
    dsimp [v]
    rw [div_pow, Real.sq_sqrt hW, ← Real.rpow_natCast ((p : ℝ) ^ _), ← Real.rpow_mul hp0.le]
    have hexp : -(i : ℝ) / 2 * ((2 : ℕ) : ℝ) = -(i : ℝ) := by push_cast; ring
    rw [hexp, mul_div_assoc]
  rw [sum_congr rfl huv]
  have hcs1 : (∑ i ∈ S, u i * v i) ^ 2 ≤
      (∑ i ∈ S, archReflectedDiagWeight (p ^ i) * q (p ^ i) ^ 2) * ∑ i ∈ S, v i ^ 2 := by
    calc (∑ i ∈ S, u i * v i) ^ 2
        ≤ (∑ i ∈ S, u i ^ 2) * ∑ i ∈ S, v i ^ 2 := sum_mul_sq_le_sq_mul_sq S u v
      _ = (∑ i ∈ S, archReflectedDiagWeight (p ^ i) * q (p ^ i) ^ 2) * ∑ i ∈ S, v i ^ 2 := by
          rw [sum_congr rfl hu2]
  have hcs2 : Real.log p * ∑ i ∈ S, v i ^ 2 ≤ 1 / 2 := by
    rw [mul_sum, sum_congr rfl hv2]
    exact sum_primeDiag_div_archReflectedDiagWeight_le_half hp K
  have hsum_u_nonneg : 0 ≤ ∑ i ∈ S, archReflectedDiagWeight (p ^ i) * q (p ^ i) ^ 2 := by
    refine sum_nonneg fun i hi => ?_
    have hi4 : 4 ≤ p ^ i := (mem_filter.1 hi).2
    have hW : 0 ≤ archReflectedDiagWeight (p ^ i) :=
      (lt_trans (by positivity) (div_six_lt_archReflectedDiagWeight hi4)).le
    exact mul_nonneg hW (sq_nonneg _)
  have h1 := mul_le_mul_of_nonneg_left hcs1 hlog0
  have h2 := mul_le_mul_of_nonneg_left hcs2 hsum_u_nonneg
  have h3 : Real.log p *
      ((∑ i ∈ S, archReflectedDiagWeight (p ^ i) * q (p ^ i) ^ 2) * ∑ i ∈ S, v i ^ 2) =
    (∑ i ∈ S, archReflectedDiagWeight (p ^ i) * q (p ^ i) ^ 2) *
      (Real.log p * ∑ i ∈ S, v i ^ 2) := by ring
  linarith

/-- For every prime `p ≥ 5` and every profile `q : ℕ → ℝ` of **arbitrary sign**,
`Real.log p * towerInteriorMellin q p K ^ 2 ≤ (1 / 2) * towerArchDiagForm q p K`. -/
theorem towerInteriorMellin_sq_le_half_towerArchDiagForm_of_five_le (q : ℕ → ℝ) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (K : ℕ) :
    Real.log p * towerInteriorMellin q p K ^ 2 ≤ (1 / 2) * towerArchDiagForm q p K := by
  refine towerInteriorMellin_sq_le_half_towerArchDiagForm q hp K fun i hi hlt4 => ?_
  have hi1 : 1 ≤ i := (mem_Icc.1 hi).1
  have : 5 ≤ p ^ i := le_trans hp5 (Nat.le_self_pow (by omega) p)
  omega

/-- **Global tower lower bound**: for any profile `q` supported on `[1, X]` with `q(p^i) = 0` for
`p^i < 4`, `towerTotalOddForm q X p K` is at least the interior Toeplitz correlation plus half of
`towerArchDiagForm q p K`. -/
theorem towerTotalOddForm_ge_half_towerArchDiagForm (q : ℕ → ℝ) {X : ℕ} (hX : 1 ≤ X)
    (hq : ∀ n, X < n → q n = 0) {p : ℕ} (hp : p.Prime) {K : ℕ}
    (hK : ∀ i, K < i → q (p ^ i) = 0) (hq23 : ∀ i ∈ Icc 1 K, p ^ i < 4 → q (p ^ i) = 0) :
    2 * Real.log p * ∑ a' ∈ pfreeLabels p X,
        cosetToeplitz (Function.update q 1 0) p X (2 * K) a' +
      (1 / 2) * towerArchDiagForm q p K ≤ towerTotalOddForm q X p K := by
  unfold towerTotalOddForm
  rw [towerOddPrimeSide_eq_interior q hX hq hp hK]
  have hcs := towerInteriorMellin_sq_le_half_towerArchDiagForm q hp K hq23
  linarith

/-! ### Part IV: The shifted-pair rank-two coset law -/

/-- The shifted tower Mellin sum `S_{p, a}(q, K) = Σ_{0 ≤ i ≤ K} q(p^i) p^{i(a − 1/2)}` at
`s = ½ − a`. -/
def shiftedTowerMellin (a : ℝ) (q : ℕ → ℝ) (p K : ℕ) : ℝ :=
  ∑ i ∈ range (K + 1), q (p ^ i) * (p : ℝ) ^ ((i : ℝ) * (a - 1 / 2))

/-- The product (frustrating) part of the tower of `p` for the shifted pair `ζ(s − a)ζ(s + a)`. -/
def shiftedTowerProductPart (a : ℝ) (q : ℕ → ℝ) (p K : ℕ) : ℝ :=
  ∑ k ∈ range (2 * K + 1),
    shiftedPairVonMangoldt a (p ^ k) * ((p ^ k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) * productCorr q (p ^ k)

/-- The shifted one-sided Toeplitz form of the coset `a'` in the tower of `p` at shift `a`:
`Σ_{1 ≤ k ≤ L} p^{k(a − 1/2)} Σ_i q(p^i a') q(p^{i+k} a')`. -/
def shiftedCosetToeplitz (a : ℝ) (q : ℕ → ℝ) (p X L : ℕ) (a' : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 L, (p : ℝ) ^ ((k : ℝ) * (a - 1 / 2)) *
    ∑ i ∈ range (Nat.log p X + 1), q (p ^ i * a') * q (p ^ (i + k) * a')

/-- The odd prime side of the tower of `p` for the shifted pair `ζ(s − a)ζ(s + a)`. -/
def shiftedTowerOddPrimeSide (a : ℝ) (q : ℕ → ℝ) (X p K : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 (2 * K),
    shiftedPairVonMangoldt a (p ^ k) * ((p ^ k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) *
      (2 * ratioCorr q X (p ^ k) - productCorr q (p ^ k))

/-- General Cauchy product along a prime tower with exponent weight `σ`:
`Σ_{1 ≤ k ≤ 2K} p^{kσ} P_q(p^k) = (Σ_{0 ≤ i ≤ K} q(p^i) p^{iσ})² − q(1)²`. -/
theorem sum_rpow_productCorr_prime_pow (σ : ℝ) (q : ℕ → ℝ) {p : ℕ} (hp : p.Prime) {K : ℕ}
    (hK : ∀ i, K < i → q (p ^ i) = 0) :
    ∑ k ∈ Icc 1 (2 * K), (p : ℝ) ^ ((k : ℝ) * σ) * productCorr q (p ^ k) =
      (∑ i ∈ range (K + 1), q (p ^ i) * (p : ℝ) ^ ((i : ℝ) * σ)) ^ 2 - q 1 ^ 2 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  set u : ℕ → ℝ := fun i => q (p ^ i) * (p : ℝ) ^ ((i : ℝ) * σ) with hu_def
  have hu : ∀ i, K < i → u i = 0 := fun i hi => by simp [hu_def, hK i hi]
  have hterm : ∀ k : ℕ, (p : ℝ) ^ ((k : ℝ) * σ) * productCorr q (p ^ k) =
      ∑ i ∈ range (k + 1), u i * u (k - i) := by
    intro k
    rw [productCorr_prime_pow q hp k, mul_sum]
    refine sum_congr rfl fun i hi => ?_
    have hik : i ≤ k := Nat.lt_succ_iff.1 (mem_range.1 hi)
    simp only [hu_def]
    have hsplit : (p : ℝ) ^ ((k : ℝ) * σ) =
        (p : ℝ) ^ ((i : ℝ) * σ) * (p : ℝ) ^ (((k - i : ℕ) : ℝ) * σ) := by
      rw [← Real.rpow_add hp0, Nat.cast_sub hik]
      congr 1; ring
    rw [hsplit]
    ring
  rw [sq_sum_eq_sum_cauchy hu, sum_range_succ_eq_zero_add_sum_Icc]
  have h0 : ∑ i ∈ range (0 + 1), u i * u (0 - i) = q 1 ^ 2 := by simp [hu_def, sq]
  rw [h0]
  have hsum : ∑ i ∈ Icc 1 (2 * K), ∑ j ∈ range (i + 1), u j * u (i - j) =
      ∑ k ∈ Icc 1 (2 * K), (p : ℝ) ^ ((k : ℝ) * σ) * productCorr q (p ^ k) :=
    sum_congr rfl fun k _ => (hterm k).symm
  linarith

/-- At a prime power `p^k` (`k ≥ 1`), the critical shifted-pair weight splits into the two exponents
`a − 1/2` and `−a − 1/2`. -/
theorem shiftedPairVonMangoldt_mul_rpow_neg_half (a : ℝ) {p : ℕ} (hp : p.Prime) {k : ℕ}
    (hk : 1 ≤ k) :
    shiftedPairVonMangoldt a (p ^ k) * ((p ^ k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) =
      Real.log p * ((p : ℝ) ^ ((k : ℝ) * (a - 1 / 2)) + (p : ℝ) ^ ((k : ℝ) * (-a - 1 / 2))) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  unfold shiftedPairVonMangoldt
  rw [vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hp, Nat.cast_pow,
    ← Real.rpow_natCast, ← Real.rpow_mul hp0.le, ← Real.rpow_mul hp0.le, ← Real.rpow_mul hp0.le,
    mul_assoc, add_mul, ← Real.rpow_add hp0, ← Real.rpow_add hp0]
  have h1 : (k : ℝ) * a + (k : ℝ) * -(1 / 2 : ℝ) = (k : ℝ) * (a - 1 / 2) := by ring
  have h2 : (k : ℝ) * -a + (k : ℝ) * -(1 / 2 : ℝ) = (k : ℝ) * (-a - 1 / 2) := by ring
  rw [h1, h2]

/-- **The shifted-pair rank-two tower law**: whereas the product part of a tower for `ζ(s)` is one
rank-one square `log p · (S_p(q)² − q(1)²)`, the product part for `ζ(s − a)ζ(s + a)` is the sum of
**two** shifted Mellin squares at `s = ½ − a` and `s = ½ + a`. -/
theorem shiftedTowerProductPart_eq_add_sq (a : ℝ) (q : ℕ → ℝ) {p : ℕ} (hp : p.Prime) {K : ℕ}
    (hK : ∀ i, K < i → q (p ^ i) = 0) :
    shiftedTowerProductPart a q p K =
      Real.log p * ((shiftedTowerMellin a q p K ^ 2 - q 1 ^ 2) +
        (shiftedTowerMellin (-a) q p K ^ 2 - q 1 ^ 2)) := by
  unfold shiftedTowerProductPart shiftedTowerMellin
  rw [sum_range_succ_eq_zero_add_sum_Icc]
  have h0 : shiftedPairVonMangoldt a (p ^ 0) * ((p ^ 0 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) *
      productCorr q (p ^ 0) = 0 := by
    simp [shiftedPairVonMangoldt, vonMangoldt_apply_one]
  rw [h0, zero_add]
  have hrew : ∑ k ∈ Icc 1 (2 * K),
        shiftedPairVonMangoldt a (p ^ k) * ((p ^ k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) *
          productCorr q (p ^ k) =
      Real.log p * ∑ k ∈ Icc 1 (2 * K), (p : ℝ) ^ ((k : ℝ) * (a - 1 / 2)) * productCorr q (p ^ k) +
        Real.log p * ∑ k ∈ Icc 1 (2 * K),
          (p : ℝ) ^ ((k : ℝ) * (-a - 1 / 2)) * productCorr q (p ^ k) := by
    rw [← mul_add, ← sum_add_distrib, mul_sum]
    refine sum_congr rfl fun k hk => ?_
    rw [shiftedPairVonMangoldt_mul_rpow_neg_half a hp (mem_Icc.1 hk).1]
    ring
  rw [hrew, sum_rpow_productCorr_prime_pow (a - 1 / 2) q hp hK,
    sum_rpow_productCorr_prime_pow (-a - 1 / 2) q hp hK]
  ring

/-- **The shifted-pair coset law**: the odd prime side of a tower for `ζ(s − a)ζ(s + a)` is
`log p` times twice the sum of the two shifted coset Toeplitz forms minus the two shifted Mellin
squares. -/
theorem shiftedTowerOddPrimeSide_eq (a : ℝ) (q : ℕ → ℝ) {X : ℕ} (hq : ∀ n, X < n → q n = 0)
    {p : ℕ} (hp : p.Prime) {K : ℕ} (hK : ∀ i, K < i → q (p ^ i) = 0) :
    shiftedTowerOddPrimeSide a q X p K =
      Real.log p * (2 * ∑ a' ∈ pfreeLabels p X,
          (shiftedCosetToeplitz a q p X (2 * K) a' + shiftedCosetToeplitz (-a) q p X (2 * K) a') -
        (shiftedTowerMellin a q p K ^ 2 - q 1 ^ 2) -
        (shiftedTowerMellin (-a) q p K ^ 2 - q 1 ^ 2)) := by
  have hprod : ∑ k ∈ Icc 1 (2 * K),
        shiftedPairVonMangoldt a (p ^ k) * ((p ^ k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) *
          productCorr q (p ^ k) =
      shiftedTowerProductPart a q p K := by
    unfold shiftedTowerProductPart
    rw [sum_range_succ_eq_zero_add_sum_Icc]
    simp [shiftedPairVonMangoldt, vonMangoldt_apply_one]
  have hrat : ∑ k ∈ Icc 1 (2 * K),
        shiftedPairVonMangoldt a (p ^ k) * ((p ^ k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) *
          ratioCorr q X (p ^ k) =
      Real.log p * ∑ a' ∈ pfreeLabels p X,
        (shiftedCosetToeplitz a q p X (2 * K) a' +
          shiftedCosetToeplitz (-a) q p X (2 * K) a') := by
    unfold shiftedCosetToeplitz
    have hL : ∀ k ∈ Icc 1 (2 * K),
        shiftedPairVonMangoldt a (p ^ k) * ((p ^ k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) *
          ratioCorr q X (p ^ k) =
        ∑ a' ∈ pfreeLabels p X, Real.log p *
          (((p : ℝ) ^ ((k : ℝ) * (a - 1 / 2)) *
              ∑ i ∈ range (Nat.log p X + 1), q (p ^ i * a') * q (p ^ (i + k) * a')) +
            ((p : ℝ) ^ ((k : ℝ) * (-a - 1 / 2)) *
              ∑ i ∈ range (Nat.log p X + 1), q (p ^ i * a') * q (p ^ (i + k) * a'))) := by
      intro k hk
      rw [shiftedPairVonMangoldt_mul_rpow_neg_half a hp (mem_Icc.1 hk).1,
        ratioCorr_prime_pow_eq_sum_cosets q hq hp k, mul_sum]
      refine sum_congr rfl fun a' _ => by ring
    rw [sum_congr rfl hL, sum_comm, mul_sum]
    refine sum_congr rfl fun a' _ => ?_
    rw [← mul_sum, sum_add_distrib]
  have hsplit : shiftedTowerOddPrimeSide a q X p K =
      2 * (∑ k ∈ Icc 1 (2 * K),
          shiftedPairVonMangoldt a (p ^ k) * ((p ^ k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) *
            ratioCorr q X (p ^ k)) -
        ∑ k ∈ Icc 1 (2 * K),
          shiftedPairVonMangoldt a (p ^ k) * ((p ^ k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) *
            productCorr q (p ^ k) := by
    unfold shiftedTowerOddPrimeSide
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun k _ => by ring
  rw [hsplit, hrat, hprod, shiftedTowerProductPart_eq_add_sq a q hp hK]
  ring

/-! ### Part V: Selectivity of the coset dominance class against `ζ(s − a)ζ(s + a)` -/

/-- For every `n ≥ 2` and `a ≠ 0`, `2 < (n : ℝ) ^ a + (n : ℝ) ^ (-a)`. -/
theorem two_lt_rpow_add_rpow_neg_of_two_le {n : ℕ} (hn : 2 ≤ n) {a : ℝ} (ha : a ≠ 0) :
    2 < (n : ℝ) ^ a + (n : ℝ) ^ (-a) := by
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hneg : 0 < (n : ℝ) ^ (-a) := Real.rpow_pos_of_pos hn_pos (-a)
  have hne : (n : ℝ) ^ a ≠ 1 := by
    intro h1
    have hlog := congrArg Real.log h1
    rw [Real.log_rpow hn_pos, Real.log_one] at hlog
    have hlog_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
    exact mul_ne_zero ha hlog_pos.ne' hlog
  have hprod : (n : ℝ) ^ a * (n : ℝ) ^ (-a) = 1 := by
    rw [← Real.rpow_add hn_pos, add_neg_cancel, Real.rpow_zero]
  have hsq : 0 < (n : ℝ) ^ (-a) * ((n : ℝ) ^ a - 1) ^ 2 :=
    mul_pos hneg (sq_pos_of_ne_zero (sub_ne_zero.mpr hne))
  have hid : (n : ℝ) ^ a + (n : ℝ) ^ (-a) - 2 = (n : ℝ) ^ (-a) * ((n : ℝ) ^ a - 1) ^ 2 := by
    linear_combination -((n : ℝ) ^ a - 2) * hprod
  linarith

/-- **Selectivity I (Strict inflation of the tower product part at every `a ≠ 0`)**:
for every `a ≠ 0`, every prime `p`, and every nonnegative profile `q` with `q(p^{i₀}) > 0` for some
`1 ≤ i₀ ≤ K`, `2 * towerProductPart q p K < shiftedTowerProductPart a q p K`. -/
theorem two_mul_towerProductPart_lt_shiftedTowerProductPart {a : ℝ} (ha : a ≠ 0)
    {q : ℕ → ℝ} (hq_nn : ∀ n, 0 ≤ q n) {p : ℕ} (hp : p.Prime) {K i₀ : ℕ}
    (hi₀1 : 1 ≤ i₀) (hi₀K : i₀ ≤ K) (hq_pos : 0 < q (p ^ i₀)) :
    2 * towerProductPart q p K < shiftedTowerProductPart a q p K := by
  unfold towerProductPart shiftedTowerProductPart
  rw [mul_sum]
  refine sum_lt_sum (fun k _ => ?_) ⟨2 * i₀, mem_range.2 (by omega), ?_⟩
  · have hP : 0 ≤ productCorr q (p ^ k) :=
      sum_nonneg fun d _ => mul_nonneg (hq_nn d) (hq_nn _)
    have hrpow : 0 ≤ ((p ^ k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
    have hprod_nn : 0 ≤ ((p ^ k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) * productCorr q (p ^ k) :=
      mul_nonneg hrpow hP
    have hle := mul_le_mul_of_nonneg_right (two_mul_vonMangoldt_le_shiftedPair a (p ^ k)) hprod_nn
    linarith
  · have hpk2 : 2 ≤ p ^ (2 * i₀) := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
    have hgt2 := two_lt_rpow_add_rpow_neg_of_two_le hpk2 ha
    have hΛ_pos : 0 < (Λ (p ^ (2 * i₀)) : ℝ) := by
      rw [vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hp]
      exact Real.log_pos (by exact_mod_cast hp.one_lt)
    have hshift_gt : 2 * (Λ (p ^ (2 * i₀)) : ℝ) < shiftedPairVonMangoldt a (p ^ (2 * i₀)) := by
      unfold shiftedPairVonMangoldt
      nlinarith
    have hrpow_pos : 0 < ((p ^ (2 * i₀) : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < p ^ (2 * i₀))) _
    have hP_pos : 0 < productCorr q (p ^ (2 * i₀)) := by
      rw [productCorr_prime_pow q hp (2 * i₀)]
      have hmem : i₀ ∈ range (2 * i₀ + 1) := mem_range.2 (by omega)
      have hsingle : q (p ^ i₀) * q (p ^ (2 * i₀ - i₀)) ≤
          ∑ i ∈ range (2 * i₀ + 1), q (p ^ i) * q (p ^ (2 * i₀ - i)) :=
        single_le_sum (f := fun i => q (p ^ i) * q (p ^ (2 * i₀ - i)))
          (fun i _ => mul_nonneg (hq_nn _) (hq_nn _)) hmem
      have hsub : 2 * i₀ - i₀ = i₀ := by omega
      rw [hsub] at hsingle
      nlinarith [mul_pos hq_pos hq_pos]
    have hprod_pos : 0 < ((p ^ (2 * i₀) : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) * productCorr q (p ^ (2 * i₀)) :=
      mul_pos hrpow_pos hP_pos
    have hlt := mul_lt_mul_of_pos_right hshift_gt hprod_pos
    linarith

/-- **Selectivity II (Divergence of the shifted Cauchy–Schwarz ratio for every `a ≠ 0`)**:
whereas the unshifted Cauchy–Schwarz ratio is bounded by `1/2` uniformly in `K`, the shifted-pair
Hankel-to-prime-diagonal ratio `Σ_{1 ≤ i ≤ K} (p^{2ia} + p^{−2ia})` strictly exceeds `2K` for every
`a ≠ 0` and `K ≥ 1`. -/
theorem sum_shiftedHankelRatio_gt_two_mul {a : ℝ} (ha : a ≠ 0) {p : ℕ} (hp : p.Prime)
    {K : ℕ} (hK : 1 ≤ K) :
    2 * (K : ℝ) < ∑ i ∈ Icc 1 K, ((p : ℝ) ^ (2 * (i : ℝ) * a) + (p : ℝ) ^ (-(2 * (i : ℝ) * a))) := by
  have h2K : 2 * (K : ℝ) = ∑ _i ∈ Icc 1 K, (2 : ℝ) := by
    rw [sum_const, Nat.card_Icc]
    have : K + 1 - 1 = K := by omega
    rw [this, nsmul_eq_mul]
    ring
  rw [h2K]
  refine sum_lt_sum (fun i hi => ?_) ⟨1, mem_Icc.2 ⟨le_rfl, hK⟩, ?_⟩
  · have hi1 : 1 ≤ i := (mem_Icc.1 hi).1
    exact (two_lt_rpow_add_rpow_neg_of_two_le hp.two_le (mul_ne_zero (mul_ne_zero two_ne_zero
      (by exact_mod_cast (by omega : i ≠ 0))) ha)).le
  · exact two_lt_rpow_add_rpow_neg_of_two_le hp.two_le
      (mul_ne_zero (by norm_num : (2 : ℝ) * (1 : ℕ) ≠ 0) ha)

/-- **Selectivity III (Reversal of the off-diagonal tower comparison for `|a| ≥ 1`)**:
while `ζ(s)` satisfies `Λ(p^{i+j}) p^{−(i+j)/2} ≤ Λ(p^{j−i}) p^{−(j−i)/2}` on every tower pair
`1 ≤ i < j` (`primeKernel_tower_le`), for `|a| ≥ 1` the shifted pair reverses the inequality at
every prime `p` and every `1 ≤ i < j`, creating positive (frustrating) off-diagonal overlaps on the
lattice itself. -/
theorem shifted_productAtom_gt_ratioAtom_of_one_le {a : ℝ} (ha : 1 ≤ |a|) {p i j : ℕ}
    (hp : p.Prime) (hi : 1 ≤ i) (hij : i < j) :
    shiftedPairVonMangoldt a (p ^ (j - i)) * ((p ^ (j - i) : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) <
      shiftedPairVonMangoldt a (p ^ (i + j)) * ((p ^ (i + j) : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlog : 0 < Real.log p := Real.log_pos hp1
  rw [shiftedPairVonMangoldt_mul_rpow_neg_half a hp (by omega),
    shiftedPairVonMangoldt_mul_rpow_neg_half a hp (by omega)]
  apply mul_lt_mul_of_pos_left _ hlog
  have hcast_lt : ((j - i : ℕ) : ℝ) < ((i + j : ℕ) : ℝ) := by exact_mod_cast (by omega : j - i < i + j)
  have hcast_pos : (0 : ℝ) < ((j - i : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < j - i)
  have hdiff_ge : (2 : ℝ) ≤ ((i + j : ℕ) : ℝ) - ((j - i : ℕ) : ℝ) := by
    rw [← Nat.cast_sub (by omega : j - i ≤ i + j)]
    exact_mod_cast (by omega : 2 ≤ i + j - (j - i))
  rcases le_total 0 a with ha0 | ha0
  · have ha1 : 1 ≤ a := by rwa [abs_of_nonneg ha0] at ha
    have h1 : (p : ℝ) ^ (((j - i : ℕ) : ℝ) * (a - 1 / 2)) + (1 : ℝ) ≤
        2 * (p : ℝ) ^ (((j - i : ℕ) : ℝ) * (a - 1 / 2)) := by
      have : (1 : ℝ) ≤ (p : ℝ) ^ (((j - i : ℕ) : ℝ) * (a - 1 / 2)) :=
        Real.one_le_rpow hp1.le (by nlinarith)
      linarith
    have h2 : (p : ℝ) ^ (((j - i : ℕ) : ℝ) * (-a - 1 / 2)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hp1 (by nlinarith)
    have h3 : (2 : ℝ) ≤ (p : ℝ) ^ ((((i + j : ℕ) : ℝ) - ((j - i : ℕ) : ℝ)) * (a - 1 / 2)) := by
      calc (2 : ℝ) ≤ (p : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]; exact_mod_cast hp.two_le
        _ ≤ (p : ℝ) ^ ((((i + j : ℕ) : ℝ) - ((j - i : ℕ) : ℝ)) * (a - 1 / 2)) :=
          Real.rpow_le_rpow_of_exponent_le hp1.le (by nlinarith)
    have h4 : 2 * (p : ℝ) ^ (((j - i : ℕ) : ℝ) * (a - 1 / 2)) ≤
        (p : ℝ) ^ (((i + j : ℕ) : ℝ) * (a - 1 / 2)) := by
      calc 2 * (p : ℝ) ^ (((j - i : ℕ) : ℝ) * (a - 1 / 2))
          ≤ (p : ℝ) ^ ((((i + j : ℕ) : ℝ) - ((j - i : ℕ) : ℝ)) * (a - 1 / 2)) *
              (p : ℝ) ^ (((j - i : ℕ) : ℝ) * (a - 1 / 2)) :=
            mul_le_mul_of_nonneg_right h3 (by positivity)
        _ = (p : ℝ) ^ (((i + j : ℕ) : ℝ) * (a - 1 / 2)) := by
            rw [← Real.rpow_add hp0]; congr 1; ring
    have h5 : 0 < (p : ℝ) ^ (((i + j : ℕ) : ℝ) * (-a - 1 / 2)) := Real.rpow_pos_of_pos hp0 _
    linarith
  · have ha1 : 1 ≤ -a := by rwa [abs_of_neg (lt_of_le_of_ne ha0 (by rintro rfl; norm_num at ha))] at ha
    have h1 : (p : ℝ) ^ (((j - i : ℕ) : ℝ) * (-a - 1 / 2)) + (1 : ℝ) ≤
        2 * (p : ℝ) ^ (((j - i : ℕ) : ℝ) * (-a - 1 / 2)) := by
      have : (1 : ℝ) ≤ (p : ℝ) ^ (((j - i : ℕ) : ℝ) * (-a - 1 / 2)) :=
        Real.one_le_rpow hp1.le (by nlinarith)
      linarith
    have h2 : (p : ℝ) ^ (((j - i : ℕ) : ℝ) * (a - 1 / 2)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hp1 (by nlinarith)
    have h3 : (2 : ℝ) ≤ (p : ℝ) ^ ((((i + j : ℕ) : ℝ) - ((j - i : ℕ) : ℝ)) * (-a - 1 / 2)) := by
      calc (2 : ℝ) ≤ (p : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]; exact_mod_cast hp.two_le
        _ ≤ (p : ℝ) ^ ((((i + j : ℕ) : ℝ) - ((j - i : ℕ) : ℝ)) * (-a - 1 / 2)) :=
          Real.rpow_le_rpow_of_exponent_le hp1.le (by nlinarith)
    have h4 : 2 * (p : ℝ) ^ (((j - i : ℕ) : ℝ) * (-a - 1 / 2)) ≤
        (p : ℝ) ^ (((i + j : ℕ) : ℝ) * (-a - 1 / 2)) := by
      calc 2 * (p : ℝ) ^ (((j - i : ℕ) : ℝ) * (-a - 1 / 2))
          ≤ (p : ℝ) ^ ((((i + j : ℕ) : ℝ) - ((j - i : ℕ) : ℝ)) * (-a - 1 / 2)) *
              (p : ℝ) ^ (((j - i : ℕ) : ℝ) * (-a - 1 / 2)) :=
            mul_le_mul_of_nonneg_right h3 (by positivity)
        _ = (p : ℝ) ^ (((i + j : ℕ) : ℝ) * (-a - 1 / 2)) := by
            rw [← Real.rpow_add hp0]; congr 1; ring
    have h5 : 0 < (p : ℝ) ^ (((i + j : ℕ) : ℝ) * (a - 1 / 2)) := Real.rpow_pos_of_pos hp0 _
    linarith

/-- **Selectivity IV (Reversal of reflected-diagonal dominance for `|a| ≥ 1`)**:
for every `|a| ≥ 1`, every prime `p`, and every `i ≥ 1`, whereas `ζ(s)` satisfies
`log p · p^{−i} ≤ archReflectedDiagWeight(p^i)` whenever `p^i ≥ 4`, the shifted pair's reflected-
diagonal prime weight `log p · p^{−i} (p^{2ia} + p^{−2ia})` strictly exceeds
`archReflectedDiagWeight(p^i)`. -/
theorem archReflectedDiagWeight_lt_shiftedPrimeDiag_of_one_le {a : ℝ} (ha : 1 ≤ |a|)
    {p i : ℕ} (hp : p.Prime) (hi : 1 ≤ i) :
    archReflectedDiagWeight (p ^ i) <
      Real.log p * (p : ℝ) ^ (-(i : ℝ)) *
        ((p : ℝ) ^ (2 * (i : ℝ) * a) + (p : ℝ) ^ (-(2 * (i : ℝ) * a))) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpi2 : 2 ≤ p ^ i := le_trans hp2 (Nat.le_self_pow (by omega) p)
  -- Upper bound on `archReflectedDiagWeight (p^i) < p^i / 2`
  have hW_lt : archReflectedDiagWeight (p ^ i) < (p : ℝ) ^ (i : ℝ) / 2 := by
    set x : ℝ := (p : ℝ) ^ (i : ℝ) with hx_def
    have hcast : ((p ^ i : ℕ) : ℝ) = x := by rw [hx_def, Real.rpow_natCast, Nat.cast_pow]
    rw [archReflectedDiagWeight_eq hpi2, hcast]
    have hx2 : 2 ≤ x := by rw [← hcast]; exact_mod_cast hpi2
    have hx4 : 16 ≤ x ^ 4 := by
      have : 4 ≤ x ^ 2 := by nlinarith
      nlinarith
    have hden : 0 < 2 * x * (x ^ 4 - 1) := by nlinarith
    rw [div_lt_div_iff₀ hden (by norm_num)]
    nlinarith
  -- Lower bound on the shifted prime diagonal `> (2 / 3) * p^i`
  have hlog2 : (2 / 3 : ℝ) < Real.log p := by
    calc (2 / 3 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
      _ ≤ Real.log p := Real.log_le_log (by norm_num) (by exact_mod_cast hp2)
  have hshift_ge : (p : ℝ) ^ (i : ℝ) ≤
      (p : ℝ) ^ (-(i : ℝ)) * ((p : ℝ) ^ (2 * (i : ℝ) * a) + (p : ℝ) ^ (-(2 * (i : ℝ) * a))) := by
    have hi_pos : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    rcases le_total 0 a with ha0 | ha0
    · have ha1 : 1 ≤ a := by rwa [abs_of_nonneg ha0] at ha
      have h1 : (p : ℝ) ^ (i : ℝ) ≤ (p : ℝ) ^ (-(i : ℝ)) * (p : ℝ) ^ (2 * (i : ℝ) * a) := by
        rw [← Real.rpow_add hp0]
        exact Real.rpow_le_rpow_of_exponent_le hp1.le (by nlinarith)
      have h2 : 0 ≤ (p : ℝ) ^ (-(i : ℝ)) * (p : ℝ) ^ (-(2 * (i : ℝ) * a)) := by positivity
      linarith
    · have ha1 : 1 ≤ -a := by
        rwa [abs_of_neg (lt_of_le_of_ne ha0 (by rintro rfl; norm_num at ha))] at ha
      have h1 : (p : ℝ) ^ (i : ℝ) ≤ (p : ℝ) ^ (-(i : ℝ)) * (p : ℝ) ^ (-(2 * (i : ℝ) * a)) := by
        rw [← Real.rpow_add hp0]
        exact Real.rpow_le_rpow_of_exponent_le hp1.le (by nlinarith)
      have h2 : 0 ≤ (p : ℝ) ^ (-(i : ℝ)) * (p : ℝ) ^ (2 * (i : ℝ) * a) := by positivity
      linarith
  have hpi_pos : 0 < (p : ℝ) ^ (i : ℝ) := Real.rpow_pos_of_pos hp0 _
  calc archReflectedDiagWeight (p ^ i)
      < (p : ℝ) ^ (i : ℝ) / 2 := hW_lt
    _ < (2 / 3) * (p : ℝ) ^ (i : ℝ) := by linarith
    _ ≤ (2 / 3) * ((p : ℝ) ^ (-(i : ℝ)) *
          ((p : ℝ) ^ (2 * (i : ℝ) * a) + (p : ℝ) ^ (-(2 * (i : ℝ) * a)))) :=
        mul_le_mul_of_nonneg_left hshift_ge (by norm_num)
    _ < Real.log p * ((p : ℝ) ^ (-(i : ℝ)) *
          ((p : ℝ) ^ (2 * (i : ℝ) * a) + (p : ℝ) ^ (-(2 * (i : ℝ) * a)))) :=
        mul_lt_mul_of_pos_right hlog2 (lt_of_lt_of_le hpi_pos hshift_ge)
    _ = Real.log p * (p : ℝ) ^ (-(i : ℝ)) *
          ((p : ℝ) ^ (2 * (i : ℝ) * a) + (p : ℝ) ^ (-(2 * (i : ℝ) * a))) := by ring

/-- **Master synthesis beyond the coset law**: unites `q(1)`-invariance of the odd prime side, the
exact scale-suppressed unit-coset decomposition, the unconditional Cauchy–Schwarz dominance bound
`log p · towerInteriorMellin q p K ^ 2 ≤ (1/2) towerArchDiagForm q p K` for arbitrary-sign profiles,
the shifted-pair rank-two coset law, and the four-part selectivity against `ζ(s − a)ζ(s + a)`. -/
theorem cosetToeplitz_dominance_and_shiftedPair_selectivity_synthesis :
    -- (1) `q(1)`-invariance of `towerOddPrimeSide`
    (∀ (q : ℕ → ℝ) (c : ℝ) {X p : ℕ}, 1 ≤ X → p.Prime → ∀ K : ℕ,
      towerOddPrimeSide (Function.update q 1 c) X p K = towerOddPrimeSide q X p K) ∧
    -- (2) Exact decomposition of `towerTotalOddForm` into Toeplitz forms and `-totalLatticeCrossingKernel`
    (∀ (q : ℕ → ℝ) {X : ℕ}, 1 ≤ X → (∀ n, X < n → q n = 0) →
      ∀ {p : ℕ}, p.Prime → ∀ {K : ℕ}, (∀ i, K < i → q (p ^ i) = 0) →
      towerTotalOddForm q X p K =
        2 * Real.log p * ∑ a' ∈ (pfreeLabels p X).erase 1, cosetToeplitz q p X (2 * K) a' +
          2 * Real.log p * scaleSuppressedUnitToeplitz q p K +
          ∑ i ∈ Icc 1 K, (-totalLatticeCrossingKernel (p ^ i) (p ^ i)) * q (p ^ i) ^ 2) ∧
    -- (3) Unconditional Cauchy–Schwarz dominance of the interior Hankel square on `p ≥ 5`
    (∀ (q : ℕ → ℝ) {p : ℕ}, p.Prime → 5 ≤ p → ∀ K : ℕ,
      Real.log p * towerInteriorMellin q p K ^ 2 ≤ (1 / 2) * towerArchDiagForm q p K) ∧
    -- (4) Shifted-pair rank-two tower product law
    (∀ (a : ℝ) (q : ℕ → ℝ) {p : ℕ}, p.Prime → ∀ {K : ℕ}, (∀ i, K < i → q (p ^ i) = 0) →
      shiftedTowerProductPart a q p K =
        Real.log p * ((shiftedTowerMellin a q p K ^ 2 - q 1 ^ 2) +
          (shiftedTowerMellin (-a) q p K ^ 2 - q 1 ^ 2))) ∧
    -- (5) Selectivity: divergence of the shifted Cauchy–Schwarz ratio at every `a ≠ 0` and reversal
    -- of both off-diagonal and reflected-diagonal dominance for `|a| ≥ 1`
    ((∀ {a : ℝ}, a ≠ 0 → ∀ {p : ℕ}, p.Prime → ∀ {K : ℕ}, 1 ≤ K →
        2 * (K : ℝ) <
          ∑ i ∈ Icc 1 K, ((p : ℝ) ^ (2 * (i : ℝ) * a) + (p : ℝ) ^ (-(2 * (i : ℝ) * a)))) ∧
      (∀ {a : ℝ}, 1 ≤ |a| → ∀ {p i : ℕ}, p.Prime → 1 ≤ i →
        archReflectedDiagWeight (p ^ i) <
          Real.log p * (p : ℝ) ^ (-(i : ℝ)) *
            ((p : ℝ) ^ (2 * (i : ℝ) * a) + (p : ℝ) ^ (-(2 * (i : ℝ) * a))))) :=
  ⟨fun q c {_ _} hX hp K => towerOddPrimeSide_update_one q c hX hp K,
   fun q {_} hX hq {_} hp {_} hK => towerTotalOddForm_eq q hX hq hp hK,
   fun q {_} hp hp5 K => towerInteriorMellin_sq_le_half_towerArchDiagForm_of_five_le q hp hp5 K,
   fun a q {_} hp {_} hK => shiftedTowerProductPart_eq_add_sq a q hp hK,
   ⟨fun {_} ha {_} hp {_} hK => sum_shiftedHankelRatio_gt_two_mul ha hp hK,
    fun {_} ha {_ _} hp hi => archReflectedDiagWeight_lt_shiftedPrimeDiag_of_one_le ha hp hi⟩⟩

end

end GaloisForLFunctions.ArithmeticOrientationTheory
