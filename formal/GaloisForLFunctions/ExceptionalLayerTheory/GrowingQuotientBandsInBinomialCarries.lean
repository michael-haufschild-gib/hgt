import GaloisForLFunctions.ExceptionalLayerTheory.BinaryCarryTentAndAdjacentQuotientIntervals
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.SubSevenEighthsZeroFreeHalfPlane
import Mathlib.NumberTheory.Bertrand

/-!
# Growing quotient bands in binary-carry prime sums

We classify the two natural decompositions of the distinct-prime binary-carry
first total into growing quotient bands:

1. **Moving-cutoff quotient slices** `S_d(X) = ∑_{k < X} ∑_{m ≤ k, ⌊k/m⌋ = d} w(m)`:
   the odd slices `d = 2Q + 1` partition `ordinaryLastClassTotal 2 X` exactly. Each
   slice decomposes into an interior linear sum up to `⌊X/(d+1)⌋` plus a boundary
   floor-discontinuity strip on `(⌊X/(d+1)⌋, ⌊X/d⌋]`. Unconditionally,
   `|S_{2Q+1}(X)| ≤ C_β (X / (2Q + 2))^{1 + β}` for every `β > 20999 / 24000`
   (in particular `O((X / (2Q + 2))^{15/8})` exact), which is summable in absolute
   value over all bands `Q < X` and strictly beats the unsigned trivial bound
   `≥ X² / (64 (d + 1)² log X)` whenever `(log X)⁸ = o(X / (d + 1))`. Conversely,
   an `O_ε(X^{3/2 + ε})` bound on even one single slice `S_d(X)` (`d ≥ 1`) is
   equivalent to `RiemannHypothesis`.

2. **Outer-cutoff paired quotient bands** `T_out(Q, X) = ∑_{m ∈ (⌊X/(2Q+2)⌋, ⌊X/(2Q)⌋]} w(m) B_m(X)`:
   unconditionally `|T_out(Q, X)| ≤ C_β X (X / (2Q))^β` for every `β > 20999 / 24000`
   (`O(X (X / (2Q))^{7/8})` exact). Near `√X`, however, the carry weight `B_m(X)` has
   uniform positive sign `≥ X / 3` across both `⌊X/m⌋ = 2Q` and `⌊X/m⌋ = 2Q + 1`:
   prime-free bands achieve zero cancellation (`|T_out| = T_out^triv`), and by
   Bertrand's postulate prime-bearing short bands above `√X` satisfy
   `(1 - ε) T_out^triv(Q, X) ≤ |T_out(Q, X)|`.
-/

noncomputable section

open Finset Filter Topology Complex ArithmeticFunction
open scoped LSeries.notation
open _root_.RHTower.WeilFiniteType

namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Unconditionally, `zeroReSup ≤ 20999 / 24000 = 7 / 8 - 1 / 24000`. -/
theorem zeroReSup_le_sub_seven_eighths : _root_.RHTower.zeroReSup ≤ 20999 / 24000 := by
  refine _root_.RHTower.zeroReSup_le_of_forall_re_le fun z => ?_
  by_contra hgt
  exact GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_ne_zero_of_sub_seven_eighths_lt_re
    (not_le.mp hgt) (_root_.RHTower.riemannZeta_eq_zero_of_xiZeroCopy z)

/-! ## 1. Moving-cutoff quotient slices -/

/-- Cumulative centered ordinary-prime sum over pairs `(k, m)` (`1 ≤ m ≤ k < X`) with `⌊k/m⌋ = d`. -/
def movingQuotientSlice (d X : ℕ) : ℝ :=
  ∑ k ∈ range X, ∑ m ∈ (Icc 1 k).filter (fun m => k / m = d), ordinaryPrimeCountWeight m

/-- Odd moving-cutoff quotient band `d = 2Q + 1` in the binary-carry first total. -/
def movingOddQuotientBand (Q X : ℕ) : ℝ :=
  movingQuotientSlice (2 * Q + 1) X

/-- Trivial unsigned benchmark for the moving-cutoff quotient slice `d`. -/
def movingQuotientSliceTrivial (d X : ℕ) : ℝ :=
  ∑ k ∈ range X, ∑ m ∈ (Icc 1 k).filter (fun m => k / m = d), |ordinaryPrimeCountWeight m|

/-- The odd moving-cutoff quotient bands `Q < X` partition `ordinaryLastClassTotal 2 X` exactly. -/
theorem sum_movingOddQuotientBand_eq_ordinaryLastClassTotal (X : ℕ) :
    (∑ Q ∈ range X, movingOddQuotientBand Q X) = ordinaryLastClassTotal 2 X := by
  unfold movingOddQuotientBand movingQuotientSlice ordinaryLastClassTotal quotientClassMassOf
  rw [sum_comm]
  refine sum_congr rfl fun k hk => ?_
  have hkX : k < X := mem_range.mp hk
  simp_rw [sum_filter (p := fun m => k / m = _)]
  calc
    (∑ Q ∈ range X, ∑ m ∈ Icc 1 k, if k / m = 2 * Q + 1 then ordinaryPrimeCountWeight m else 0) =
        ∑ m ∈ Icc 1 k, ∑ Q ∈ range X,
          if k / m = 2 * Q + 1 then ordinaryPrimeCountWeight m else 0 := sum_comm
    _ = ∑ m ∈ Icc 1 k, ordinaryPrimeCountWeight m * (if 2 ∣ k / m + 1 then 1 else 0) := by
      refine sum_congr rfl fun m _ => ?_
      by_cases hd : 2 ∣ k / m + 1
      · rw [if_pos hd, mul_one]
        let Q₀ := (k / m) / 2
        have hkm : k / m = 2 * Q₀ + 1 := by omega
        have hQ₀ : Q₀ ∈ range X := mem_range.mpr (by
          have : k / m ≤ k := Nat.div_le_self k m
          omega)
        rw [sum_eq_single_of_mem Q₀ hQ₀]
        · exact if_pos hkm
        · intro Q _ hne
          exact if_neg (by omega)
      · rw [if_neg hd, mul_zero]
        exact sum_eq_zero fun Q _ => if_neg (by omega)

private theorem Ioc_zero_eq_Icc_one (n : ℕ) : Ioc 0 n = Icc 1 n := by
  ext k
  simp only [mem_Ioc, mem_Icc]
  omega

private theorem slice_multiplicity_identity (f : ℕ → ℝ) {d : ℕ} (hd : 1 ≤ d) (X : ℕ) :
    (∑ k ∈ range X, ∑ m ∈ (Icc 1 k).filter (fun m => k / m = d), f m) =
      (∑ m ∈ Icc 1 (X / (d + 1)), (m : ℝ) * f m) +
        ∑ m ∈ Ioc (X / (d + 1)) (X / d), ((X : ℝ) - (d : ℝ) * m) * f m := by
  have hext (k : ℕ) (hk : k ∈ range X) :
      (∑ m ∈ (Icc 1 k).filter (fun m => k / m = d), f m) =
        ∑ m ∈ Icc 1 X, if k / m = d then f m else 0 := by
    rw [sum_filter]
    apply sum_subset (Icc_subset_Icc_right (mem_range.mp hk).le)
    intro m hm hnot
    have hm1 := (mem_Icc.mp hm).1
    have hkm : k < m := by by_contra! hle; exact hnot (mem_Icc.mpr ⟨hm1, hle⟩)
    rw [Nat.div_eq_of_lt hkm, if_neg (by omega)]
  rw [sum_congr rfl hext, sum_comm]
  have hcount (m : ℕ) (hm : m ∈ Icc 1 X) :
      (∑ k ∈ range X, if k / m = d then f m else 0) =
        (((Ico (d * m) (min X ((d + 1) * m))).card : ℕ) : ℝ) * f m := by
    have hm0 : 0 < m := (mem_Icc.mp hm).1
    rw [← sum_filter]
    have hset : (range X).filter (fun k => k / m = d) = Ico (d * m) (min X ((d + 1) * m)) := by
      ext k
      simp only [mem_filter, mem_range, mem_Ico, lt_min_iff]
      constructor
      · rintro ⟨hkX, hdiv⟩
        have h1 : d * m ≤ k := by
          have := Nat.div_mul_le_self k m
          rwa [hdiv] at this
        have h2 : k < (d + 1) * m := (Nat.div_lt_iff_lt_mul hm0).mp (by omega)
        exact ⟨h1, hkX, h2⟩
      · rintro ⟨h1, hkX, h2⟩
        refine ⟨hkX, le_antisymm ?_ ?_⟩
        · exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hm0).mpr h2)
        · exact (Nat.le_div_iff_mul_le hm0).mpr h1
    rw [hset, sum_const, nsmul_eq_mul]
  rw [sum_congr rfl hcount]
  have hM₂ : X / d ≤ X := Nat.div_le_self X d
  have hM₁₂ : X / (d + 1) ≤ X / d := Nat.div_le_div_left (Nat.le_succ d) (by omega)
  have htrim : (∑ m ∈ Icc 1 X, (((Ico (d * m) (min X ((d + 1) * m))).card : ℕ) : ℝ) * f m) =
      ∑ m ∈ Icc 1 (X / d), (((Ico (d * m) (min X ((d + 1) * m))).card : ℕ) : ℝ) * f m := by
    symm
    apply sum_subset (Icc_subset_Icc_right hM₂)
    intro m hm hnot
    have hm1 := (mem_Icc.mp hm).1
    have hgt : X / d < m := by by_contra! hle; exact hnot (mem_Icc.mpr ⟨hm1, hle⟩)
    have hlt : X < d * m := by
      have := (Nat.div_lt_iff_lt_mul (by omega : 0 < d)).mp hgt
      linarith
    have hempty : Ico (d * m) (min X ((d + 1) * m)) = ∅ := by
      rw [Ico_eq_empty_iff]
      have : min X ((d + 1) * m) ≤ X := min_le_left _ _
      omega
    simp [hempty]
  rw [htrim, ← Ioc_zero_eq_Icc_one, ← sum_Ioc_consecutive _ (Nat.zero_le (X / (d + 1))) hM₁₂,
    Ioc_zero_eq_Icc_one]
  congr 1
  · refine sum_congr rfl fun m hm => ?_
    have hm_le := (mem_Icc.mp hm).2
    have hmul : (d + 1) * m ≤ X := by
      have := (Nat.le_div_iff_mul_le (by omega : 0 < d + 1)).mp hm_le
      linarith
    rw [min_eq_right hmul, Nat.card_Ico]
    have hsub : (d + 1) * m - d * m = m := by
      have : (d + 1) * m = d * m + m := Nat.succ_mul d m
      omega
    rw [hsub]
  · refine sum_congr rfl fun m hm => ?_
    obtain ⟨hm_gt, hm_le⟩ := mem_Ioc.mp hm
    have hlt : X < (d + 1) * m := by
      have := (Nat.div_lt_iff_lt_mul (by omega : 0 < d + 1)).mp hm_gt
      linarith
    have hge : d * m ≤ X := by
      have := (Nat.le_div_iff_mul_le (by omega : 0 < d)).mp hm_le
      linarith
    rw [min_eq_left hlt.le, Nat.card_Ico, Nat.cast_sub hge, Nat.cast_mul]

/-- Exact decomposition of `movingQuotientSlice d X` (`d ≥ 1`) into an interior linear sum
up to `⌊X / (d + 1)⌋` plus a boundary floor-discontinuity strip on `(⌊X / (d + 1)⌋, ⌊X / d⌋]`. -/
theorem movingQuotientSlice_eq_interior_add_boundary_strip {d : ℕ} (hd : 1 ≤ d) (X : ℕ) :
    movingQuotientSlice d X =
      (∑ m ∈ Icc 1 (X / (d + 1)), (m : ℝ) * ordinaryPrimeCountWeight m) +
        ∑ m ∈ Ioc (X / (d + 1)) (X / d), ((X : ℝ) - (d : ℝ) * m) * ordinaryPrimeCountWeight m :=
  slice_multiplicity_identity ordinaryPrimeCountWeight hd X

/-- Exact interior plus boundary-strip formula for `movingQuotientSliceTrivial d X` (`d ≥ 1`). -/
theorem movingQuotientSliceTrivial_eq_interior_add_boundary_strip {d : ℕ} (hd : 1 ≤ d) (X : ℕ) :
    movingQuotientSliceTrivial d X =
      (∑ m ∈ Icc 1 (X / (d + 1)), (m : ℝ) * |ordinaryPrimeCountWeight m|) +
        ∑ m ∈ Ioc (X / (d + 1)) (X / d), ((X : ℝ) - (d : ℝ) * m) * |ordinaryPrimeCountWeight m| :=
  slice_multiplicity_identity (fun m => |ordinaryPrimeCountWeight m|) hd X

/-- Abel bound on `movingQuotientSlice d X` from uniform partial-sum bounds up to `⌊X / d⌋`. -/
theorem abs_movingQuotientSlice_le_of_prefix {d : ℕ} (hd : 1 ≤ d) (X : ℕ) {B : ℝ} (hB0 : 0 ≤ B)
    (hpref : ∀ j ≤ X / d, |∑ m ∈ Icc 1 j, ordinaryPrimeCountWeight m| ≤ B) :
    |movingQuotientSlice d X| ≤ 4 * B * ((X / (d + 1) : ℕ) : ℝ) := by
  rw [movingQuotientSlice_eq_interior_add_boundary_strip hd X]
  let M₁ := X / (d + 1)
  let M₂ := X / d
  have hM₁₂ : M₁ ≤ M₂ := Nat.div_le_div_left (Nat.le_succ d) (by omega)
  rcases Nat.eq_zero_or_pos M₁ with hM₁0 | hM₁_pos
  · have hint : (∑ m ∈ Icc 1 M₁, (m : ℝ) * ordinaryPrimeCountWeight m) = 0 := by simp [hM₁0]
    have hbdry : (∑ m ∈ Ioc M₁ M₂, ((X : ℝ) - (d : ℝ) * m) * ordinaryPrimeCountWeight m) = 0 := by
      have hXlt : X < d + 1 := (Nat.div_eq_zero_iff.mp hM₁0).resolve_left (by omega)
      refine sum_eq_zero fun m hm => ?_
      obtain ⟨hm0, hmle⟩ := mem_Ioc.mp (hM₁0 ▸ hm)
      have hdX : d ≤ X := by
        have hpos_M₂ : 0 < M₂ := lt_of_lt_of_le hm0 hmle
        have := (Nat.le_div_iff_mul_le (by omega : 0 < d)).mp hpos_M₂
        omega
      have hXd : X = d := by omega
      have hm1 : m = 1 := by
        have : M₂ = 1 := by dsimp [M₂]; rw [hXd, Nat.div_self hd]
        omega
      rw [hXd, hm1, Nat.cast_one, mul_one, sub_self, zero_mul]
    change |(∑ m ∈ Icc 1 M₁, _) + ∑ m ∈ Ioc M₁ M₂, _| ≤ 4 * B * (M₁ : ℝ)
    rw [hint, hbdry, hM₁0]
    simp
  · have hM₂_pos : 1 ≤ M₂ := lt_of_lt_of_le hM₁_pos hM₁₂
    have hint_le : |∑ m ∈ Icc 1 M₁, (m : ℝ) * ordinaryPrimeCountWeight m| ≤ 2 * B * (M₁ : ℝ) := by
      let w₁ : ℕ → ℝ := fun m => (M₁ : ℝ) - m
      have hsplit : (∑ m ∈ Icc 1 M₁, (m : ℝ) * ordinaryPrimeCountWeight m) =
          (M₁ : ℝ) * (∑ m ∈ Icc 1 M₁, ordinaryPrimeCountWeight m) -
            ∑ m ∈ Icc 1 M₁, ordinaryPrimeCountWeight m * w₁ m := by
        rw [mul_sum, ← sum_sub_distrib]
        exact sum_congr rfl fun m _ => by dsimp only [w₁]; ring
      have hab₁ := _root_.RHTower.abs_sum_mul_le_of_antitone (a := ordinaryPrimeCountWeight)
        (w := w₁) hM₁_pos (fun j hj => hpref j (hj.trans hM₁₂))
        (fun k _ hk => by dsimp only [w₁]; exact sub_nonneg.mpr (by exact_mod_cast hk))
        (fun k _ _ => by dsimp only [w₁]; push_cast; linarith)
      have hw₁_le : w₁ 1 ≤ M₁ := by dsimp only [w₁]; norm_num
      have hterm1 : |(M₁ : ℝ) * ∑ m ∈ Icc 1 M₁, ordinaryPrimeCountWeight m| ≤ B * (M₁ : ℝ) := by
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg M₁), mul_comm]
        exact mul_le_mul_of_nonneg_right (hpref M₁ hM₁₂) (Nat.cast_nonneg M₁)
      have hterm2 : |∑ m ∈ Icc 1 M₁, ordinaryPrimeCountWeight m * w₁ m| ≤ B * (M₁ : ℝ) :=
        hab₁.trans (mul_le_mul_of_nonneg_left hw₁_le hB0)
      rw [hsplit]
      exact (abs_sub _ _).trans ((add_le_add hterm1 hterm2).trans_eq (by ring))
    have hbdry_le :
        |∑ m ∈ Ioc M₁ M₂, ((X : ℝ) - (d : ℝ) * m) * ordinaryPrimeCountWeight m| ≤
          2 * B * (M₁ : ℝ) := by
      rcases eq_or_lt_of_le hM₁₂ with hEq | hLt
      · rw [hEq, Ioc_self, sum_empty, abs_zero]
        positivity
      · have htop_nat : X < (d + 1) * (M₁ + 1) := by
          have := (Nat.div_lt_iff_lt_mul (by omega : 0 < d + 1)).mp (Nat.lt_succ_self M₁)
          linarith
        have htop_le : X ≤ d * (M₁ + 1) + M₁ := by linarith
        have hbot_nat : d * (M₁ + 1) ≤ X := by
          have : M₁ + 1 ≤ M₂ := hLt
          have := (Nat.le_div_iff_mul_le (by omega : 0 < d)).mp this
          linarith
        let c₀ : ℝ := (X : ℝ) - (d : ℝ) * ((M₁ : ℝ) + 1)
        have hc₀_nonneg : 0 ≤ c₀ := by
          dsimp only [c₀]
          have : (d : ℝ) * ((M₁ : ℝ) + 1) ≤ X := by exact_mod_cast hbot_nat
          linarith only [this]
        have hc₀_le : c₀ ≤ M₁ := by
          dsimp only [c₀]
          have : (X : ℝ) ≤ (d : ℝ) * ((M₁ : ℝ) + 1) + M₁ := by exact_mod_cast htop_le
          linarith only [this]
        let w₂ : ℕ → ℝ := fun m => if m ≤ M₁ then c₀ else (X : ℝ) - (d : ℝ) * m
        have hw₂_1 : w₂ 1 = c₀ := if_pos hM₁_pos
        have hw₂_nonneg (k : ℕ) (_ : 1 ≤ k) (hk : k ≤ M₂) : 0 ≤ w₂ k := by
          dsimp only [w₂]
          split_ifs with h
          · exact hc₀_nonneg
          · have : d * k ≤ X := by
              have := (Nat.le_div_iff_mul_le (by omega : 0 < d)).mp hk
              linarith
            have hR : (d : ℝ) * k ≤ X := by exact_mod_cast this
            linarith only [hR]
        have hw₂_anti (k : ℕ) (_ : 1 ≤ k) (_ : k < M₂) : w₂ (k + 1) ≤ w₂ k := by
          dsimp only [w₂, c₀]
          by_cases hk1 : k + 1 ≤ M₁
          · rw [if_pos hk1, if_pos (by omega)]
          · rw [if_neg hk1]
            by_cases hk0 : k ≤ M₁
            · have hkEq : k = M₁ := by omega
              rw [if_pos hk0, hkEq]
              push_cast
              linarith
            · rw [if_neg hk0]
              push_cast
              have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
              linarith
        have hsplit₂ : (∑ m ∈ Ioc M₁ M₂, ((X : ℝ) - (d : ℝ) * m) * ordinaryPrimeCountWeight m) =
            (∑ m ∈ Icc 1 M₂, ordinaryPrimeCountWeight m * w₂ m) -
              c₀ * ∑ m ∈ Icc 1 M₁, ordinaryPrimeCountWeight m := by
          rw [← Ioc_zero_eq_Icc_one M₂, ← sum_Ioc_consecutive _ (Nat.zero_le M₁) hM₁₂,
            Ioc_zero_eq_Icc_one M₁]
          have hhead : (∑ m ∈ Icc 1 M₁, ordinaryPrimeCountWeight m * w₂ m) =
              c₀ * ∑ m ∈ Icc 1 M₁, ordinaryPrimeCountWeight m := by
            rw [mul_sum]
            refine sum_congr rfl fun m hm => ?_
            dsimp only [w₂]
            rw [if_pos (mem_Icc.mp hm).2, mul_comm]
          have htail : (∑ m ∈ Ioc M₁ M₂, ordinaryPrimeCountWeight m * w₂ m) =
              ∑ m ∈ Ioc M₁ M₂, ((X : ℝ) - (d : ℝ) * m) * ordinaryPrimeCountWeight m := by
            refine sum_congr rfl fun m hm => ?_
            dsimp only [w₂]
            rw [if_neg (not_le.mpr (mem_Ioc.mp hm).1), mul_comm]
          linarith only [hhead, htail]
        have hab₂ := _root_.RHTower.abs_sum_mul_le_of_antitone (a := ordinaryPrimeCountWeight)
          (w := w₂) hM₂_pos hpref hw₂_nonneg hw₂_anti
        rw [hw₂_1] at hab₂
        have ht1 : |∑ m ∈ Icc 1 M₂, ordinaryPrimeCountWeight m * w₂ m| ≤ B * (M₁ : ℝ) :=
          hab₂.trans (mul_le_mul_of_nonneg_left hc₀_le hB0)
        have ht2 : |c₀ * ∑ m ∈ Icc 1 M₁, ordinaryPrimeCountWeight m| ≤ B * (M₁ : ℝ) := by
          rw [abs_mul, abs_of_nonneg hc₀_nonneg, mul_comm]
          exact mul_le_mul (hpref M₁ hM₁₂) hc₀_le hc₀_nonneg hB0
        rw [hsplit₂]
        exact (abs_sub _ _).trans ((add_le_add ht1 ht2).trans_eq (by ring))
    change |(∑ m ∈ Icc 1 M₁, _) + ∑ m ∈ Ioc M₁ M₂, _| ≤ 4 * B * (M₁ : ℝ)
    exact (abs_add_le _ _).trans ((add_le_add hint_le hbdry_le).trans_eq (by ring))

/-- Unconditional sub-`7/8` uniform slice bound and absolute summability over all odd bands:
for every `β > 20999 / 24000`, `|S_d(X)| ≤ C_β (X / (d + 1))^{1 + β}` for all `d ≥ 1` and
`∑_{Q < X} |movingOddQuotientBand Q X| ≤ C_sum X^{1 + β}`. -/
theorem exists_movingOddQuotientBand_uniform_and_summable {β : ℝ}
    (hβ : (20999 / 24000 : ℝ) < β) :
    ∃ C Csum : ℝ, 0 ≤ C ∧ 0 ≤ Csum ∧
      (∀ d X : ℕ, 1 ≤ d →
        |movingQuotientSlice d X| ≤ C * ((X : ℝ) / ((d : ℝ) + 1)) ^ (1 + β)) ∧
      (∀ X : ℕ,
        (∑ Q ∈ range X, |movingOddQuotientBand Q X|) ≤ Csum * (X : ℝ) ^ (1 + β)) := by
  have hΘ : _root_.RHTower.zeroReSup < β := zeroReSup_le_sub_seven_eighths.trans_lt hβ
  have hβ0 : 0 < β := by linarith
  obtain ⟨K, hK0, hpref⟩ := ordinary_prefix_power hΘ
  let C := 4 * (2 : ℝ) ^ β * K
  have hC0 : 0 ≤ C := by dsimp only [C]; positivity
  have hslice_all (d X : ℕ) (hd : 1 ≤ d) :
      |movingQuotientSlice d X| ≤ C * ((X : ℝ) / ((d : ℝ) + 1)) ^ (1 + β) := by
    rcases lt_or_ge X (d + 1) with hlt | hge
    · let B := K * ((X / d : ℕ) : ℝ) ^ β
      have hB0 : 0 ≤ B := by dsimp only [B]; positivity
      have h0 : X / (d + 1) = 0 := Nat.div_eq_of_lt hlt
      have hab := abs_movingQuotientSlice_le_of_prefix hd X hB0 fun j hj => by
        rcases Nat.eq_zero_or_pos j with rfl | hj0
        · simp [hB0]
        · exact (hpref j hj0).trans (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (Nat.cast_nonneg j) (by exact_mod_cast hj) hβ0.le) hK0)
      rw [h0, Nat.cast_zero, mul_zero] at hab
      exact hab.trans (by positivity)
    · let M₁ := X / (d + 1)
      let M₂ := X / d
      let B := K * (M₂ : ℝ) ^ β
      have hB0 : 0 ≤ B := by dsimp only [B]; positivity
      have hab := abs_movingQuotientSlice_le_of_prefix hd X hB0 fun j hj => by
        rcases Nat.eq_zero_or_pos j with rfl | hj0
        · simp [hB0]
        · exact (hpref j hj0).trans (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (Nat.cast_nonneg j) (by exact_mod_cast hj) hβ0.le) hK0)
      have hd_pos : (0 : ℝ) < d := by exact_mod_cast hd
      have hd1_pos : (0 : ℝ) < (d : ℝ) + 1 := by positivity
      have hX_pos : (0 : ℝ) < (X : ℝ) / ((d : ℝ) + 1) :=
        div_pos (by exact_mod_cast (by omega : 0 < X)) hd1_pos
      have hM₁_le : (M₁ : ℝ) ≤ (X : ℝ) / ((d : ℝ) + 1) := by
        simpa [M₁, Nat.cast_add, Nat.cast_one] using (Nat.cast_div_le (m := X) (n := d + 1))
      have hM₂_le : (M₂ : ℝ) ≤ 2 * ((X : ℝ) / ((d : ℝ) + 1)) := by
        have h1 : (M₂ : ℝ) ≤ (X : ℝ) / d := Nat.cast_div_le
        refine h1.trans ?_
        rw [mul_div_assoc', div_le_div_iff₀ hd_pos hd1_pos]
        have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
        have hXR : (0 : ℝ) ≤ X := Nat.cast_nonneg X
        nlinarith only [hdR, hXR]
      have hB_le : B ≤ K * (2 : ℝ) ^ β * ((X : ℝ) / ((d : ℝ) + 1)) ^ β := by
        dsimp only [B]
        calc
          K * (M₂ : ℝ) ^ β ≤ K * (2 * ((X : ℝ) / ((d : ℝ) + 1))) ^ β :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg M₂) hM₂_le hβ0.le) hK0
          _ = K * (2 : ℝ) ^ β * ((X : ℝ) / ((d : ℝ) + 1)) ^ β := by
            rw [Real.mul_rpow (by norm_num) hX_pos.le]
            ring
      calc
        |movingQuotientSlice d X| ≤ 4 * B * (M₁ : ℝ) := hab
        _ ≤ 4 * (K * (2 : ℝ) ^ β * ((X : ℝ) / ((d : ℝ) + 1)) ^ β) *
              ((X : ℝ) / ((d : ℝ) + 1)) := by
          exact mul_le_mul (mul_le_mul_of_nonneg_left hB_le (by norm_num)) hM₁_le
            (Nat.cast_nonneg M₁) (by positivity)
        _ = C * (((X : ℝ) / ((d : ℝ) + 1)) ^ β * ((X : ℝ) / ((d : ℝ) + 1)) ^ (1 : ℝ)) := by
          rw [Real.rpow_one]
          dsimp only [C]
          ring
        _ = C * ((X : ℝ) / ((d : ℝ) + 1)) ^ (1 + β) := by
          rw [← Real.rpow_add hX_pos, add_comm β 1]
  have hsum_nat : Summable (fun Q : ℕ => (((Q + 1 : ℕ) : ℝ)) ^ (-(1 + β))) :=
    (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by linarith))
  let S := ∑' Q : ℕ, (((Q + 1 : ℕ) : ℝ)) ^ (-(1 + β))
  have hS0 : 0 ≤ S := tsum_nonneg fun _ => by positivity
  refine ⟨C, C * S, hC0, mul_nonneg hC0 hS0, hslice_all, fun X => ?_⟩
  have hterm (Q : ℕ) :
      |movingOddQuotientBand Q X| ≤
        (C * (X : ℝ) ^ (1 + β)) * (((Q + 1 : ℕ) : ℝ)) ^ (-(1 + β)) := by
    have hd : 1 ≤ 2 * Q + 1 := by omega
    have hb := hslice_all (2 * Q + 1) X hd
    have hden_pos : (0 : ℝ) < ((2 * Q + 1 : ℕ) : ℝ) + 1 := by positivity
    have hQ_pos : (0 : ℝ) < ((Q + 1 : ℕ) : ℝ) := by positivity
    have hQ_le : ((Q + 1 : ℕ) : ℝ) ≤ ((2 * Q + 1 : ℕ) : ℝ) + 1 := by push_cast; linarith
    have hrpow : (((2 * Q + 1 : ℕ) : ℝ) + 1) ^ (-(1 + β)) ≤
        (((Q + 1 : ℕ) : ℝ)) ^ (-(1 + β)) :=
      Real.rpow_le_rpow_of_nonpos hQ_pos hQ_le (by linarith)
    calc
      |movingOddQuotientBand Q X|
          ≤ C * ((X : ℝ) / (((2 * Q + 1 : ℕ) : ℝ) + 1)) ^ (1 + β) := hb
      _ = (C * (X : ℝ) ^ (1 + β)) * (((2 * Q + 1 : ℕ) : ℝ) + 1) ^ (-(1 + β)) := by
        rw [Real.div_rpow (Nat.cast_nonneg X) hden_pos.le, Real.rpow_neg hden_pos.le,
          div_eq_mul_inv]
        ring
      _ ≤ (C * (X : ℝ) ^ (1 + β)) * (((Q + 1 : ℕ) : ℝ)) ^ (-(1 + β)) :=
        mul_le_mul_of_nonneg_left hrpow (by positivity)
  calc
    (∑ Q ∈ range X, |movingOddQuotientBand Q X|)
        ≤ ∑ Q ∈ range X, (C * (X : ℝ) ^ (1 + β)) * (((Q + 1 : ℕ) : ℝ)) ^ (-(1 + β)) :=
      sum_le_sum fun Q _ => hterm Q
    _ = (C * (X : ℝ) ^ (1 + β)) * ∑ Q ∈ range X, (((Q + 1 : ℕ) : ℝ)) ^ (-(1 + β)) := by
      rw [← mul_sum]
    _ ≤ (C * (X : ℝ) ^ (1 + β)) * S := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact hsum_nat.sum_le_tsum (range X) fun _ _ => by positivity
    _ = (C * S) * (X : ℝ) ^ (1 + β) := by ring

/-- Exact exponent `15 / 8` specialization (`7 / 8 > 20999 / 24000`) for moving quotient slices
and their absolute sum over all odd bands. -/
theorem exists_movingOddQuotientBand_fifteen_eighths_exact :
    ∃ C Csum : ℝ, 0 ≤ C ∧ 0 ≤ Csum ∧
      (∀ d X : ℕ, 1 ≤ d →
        |movingQuotientSlice d X| ≤ C * ((X : ℝ) / ((d : ℝ) + 1)) ^ (15 / 8 : ℝ)) ∧
      (∀ X : ℕ,
        (∑ Q ∈ range X, |movingOddQuotientBand Q X|) ≤ Csum * (X : ℝ) ^ (15 / 8 : ℝ)) := by
  have h158 : (1 : ℝ) + (7 / 8 : ℝ) = (15 / 8 : ℝ) := by norm_num
  simpa only [h158] using
    exists_movingOddQuotientBand_uniform_and_summable (β := 7 / 8) (by norm_num)

/-- Elementary unsigned lower bound: whenever `8 * (d + 1) ≤ X`, composite even integers
alone force `movingQuotientSliceTrivial d X ≥ X² / (64 (d + 1)² log X)`. -/
theorem movingQuotientSliceTrivial_lower_bound {d X : ℕ} (hd : 1 ≤ d)
    (hX : 8 * (d + 1) ≤ X) :
    (X : ℝ) ^ 2 / (64 * ((d : ℝ) + 1) ^ 2 * Real.log X) ≤ movingQuotientSliceTrivial d X := by
  rw [movingQuotientSliceTrivial_eq_interior_add_boundary_strip hd X]
  let M₁ := X / (d + 1)
  have hM₁_ge8 : 8 ≤ M₁ := (Nat.le_div_iff_mul_le (by omega : 0 < d + 1)).mpr (by linarith)
  have hX_ge2 : 2 ≤ X := by omega
  have hlogX_pos : 0 < Real.log X := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  have hbdry_nonneg :
      0 ≤ ∑ m ∈ Ioc M₁ (X / d), ((X : ℝ) - (d : ℝ) * m) * |ordinaryPrimeCountWeight m| := by
    refine sum_nonneg fun m hm => mul_nonneg ?_ (abs_nonneg _)
    have hmul : d * m ≤ X := by
      have := (Nat.le_div_iff_mul_le (by omega : 0 < d)).mp (mem_Ioc.mp hm).2
      linarith
    have hR : (d : ℝ) * m ≤ X := by exact_mod_cast hmul
    linarith only [hR]
  -- Restrict interior sum to `m = 2 * j` for `j ∈ Ioc (M₁ / 4) (M₁ / 2)`
  let J := Ioc (M₁ / 4) (M₁ / 2)
  have himg_sub : J.image (fun j => 2 * j) ⊆ Icc 1 M₁ := by
    intro m hm
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hm
    obtain ⟨hj1, hj2⟩ := mem_Ioc.mp hj
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  have hinj : Set.InjOn (fun j : ℕ => 2 * j) J := fun _ _ _ _ heq =>
    Nat.eq_of_mul_eq_mul_left two_pos heq
  have heven_not_prime (j : ℕ) (hj : j ∈ J) : ¬ (2 * j).Prime := by
    have hj_gt : M₁ / 4 < j := (mem_Ioc.mp hj).1
    have hj_ge3 : 3 ≤ j := by omega
    intro hp
    rcases (Nat.dvd_prime hp).mp (dvd_mul_right 2 j) with h1 | h2 <;> omega
  have hterm_lb (j : ℕ) (hj : j ∈ J) :
      ((M₁ : ℝ) / 2) * (Real.log X)⁻¹ ≤
        ((2 * j : ℕ) : ℝ) * |ordinaryPrimeCountWeight (2 * j)| := by
    obtain ⟨hj1, hj2⟩ := mem_Ioc.mp hj
    have hnp := heven_not_prime j hj
    have h2j_ge6 : 6 ≤ 2 * j := by omega
    have h2j_leX : 2 * j ≤ X := by
      have : M₁ ≤ X := Nat.div_le_self X (d + 1)
      omega
    have hlog2j_pos : 0 < Real.log (2 * j : ℕ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < 2 * j))
    have hlog_le : Real.log (2 * j : ℕ) ≤ Real.log X :=
      Real.log_le_log (by positivity) (by exact_mod_cast h2j_leX)
    have hinv_ge : (Real.log X)⁻¹ ≤ (Real.log (2 * j : ℕ))⁻¹ := inv_anti₀ hlog2j_pos hlog_le
    have hw_eq : |ordinaryPrimeCountWeight (2 * j)| = (Real.log (2 * j : ℕ))⁻¹ := by
      change |(if (2 * j).Prime then (1 : ℝ) else 0) - (Real.log (2 * j : ℕ))⁻¹| = _
      rw [if_neg hnp, zero_sub, abs_neg, abs_of_pos (inv_pos.mpr hlog2j_pos)]
    have hm_ge : (M₁ : ℝ) / 2 ≤ ((2 * j : ℕ) : ℝ) := by
      have : M₁ < 4 * j := by omega
      have hR : (M₁ : ℝ) ≤ 4 * (j : ℝ) := by exact_mod_cast this.le
      push_cast
      linarith only [hR]
    rw [hw_eq]
    exact mul_le_mul hm_ge hinv_ge (inv_nonneg.mpr hlogX_pos.le) (by positivity)
  have hcard_ge : (M₁ : ℝ) / 8 ≤ (J.card : ℝ) := by
    have hc : J.card = M₁ / 2 - M₁ / 4 := Nat.card_Ioc (M₁ / 4) (M₁ / 2)
    have hnat : M₁ ≤ 8 * (M₁ / 2 - M₁ / 4) := by omega
    have hR : (M₁ : ℝ) ≤ 8 * (J.card : ℝ) := by rw [hc]; exact_mod_cast hnat
    linarith only [hR]
  have hM₁_half : (X : ℝ) / (2 * ((d : ℝ) + 1)) ≤ M₁ := by
    have hnat : X < 2 * (d + 1) * M₁ := by
      have hlt : X < (d + 1) * (M₁ + 1) := by
        have := (Nat.div_lt_iff_lt_mul (by omega : 0 < d + 1)).mp (Nat.lt_succ_self M₁)
        linarith
      nlinarith only [hlt, hM₁_ge8]
    have hR : (X : ℝ) ≤ 2 * ((d : ℝ) + 1) * M₁ := by exact_mod_cast hnat.le
    exact (div_le_iff₀ (by positivity)).mpr (by linarith only [hR])
  have hint_ge : (M₁ : ℝ) ^ 2 / (16 * Real.log X) ≤
      ∑ m ∈ Icc 1 M₁, (m : ℝ) * |ordinaryPrimeCountWeight m| := by
    calc
      (M₁ : ℝ) ^ 2 / (16 * Real.log X)
          = ((M₁ : ℝ) / 8) * (((M₁ : ℝ) / 2) * (Real.log X)⁻¹) := by ring
      _ ≤ (J.card : ℝ) * (((M₁ : ℝ) / 2) * (Real.log X)⁻¹) :=
        mul_le_mul_of_nonneg_right hcard_ge (by positivity)
      _ = ∑ _j ∈ J, ((M₁ : ℝ) / 2) * (Real.log X)⁻¹ := by
        rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ j ∈ J, ((2 * j : ℕ) : ℝ) * |ordinaryPrimeCountWeight (2 * j)| :=
        sum_le_sum hterm_lb
      _ = ∑ m ∈ J.image (fun j : ℕ => 2 * j), (m : ℝ) * |ordinaryPrimeCountWeight m| :=
        (sum_image (f := fun m : ℕ => (m : ℝ) * |ordinaryPrimeCountWeight m|) hinj).symm
      _ ≤ ∑ m ∈ Icc 1 M₁, (m : ℝ) * |ordinaryPrimeCountWeight m| :=
        sum_le_sum_of_subset_of_nonneg himg_sub fun m _ _ => by positivity
  have hsq : (X : ℝ) ^ 2 / (64 * ((d : ℝ) + 1) ^ 2 * Real.log X) ≤
      (M₁ : ℝ) ^ 2 / (16 * Real.log X) := by
    have hsq_M : ((X : ℝ) / (2 * ((d : ℝ) + 1))) ^ 2 ≤ (M₁ : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hM₁_half 2
    calc
      (X : ℝ) ^ 2 / (64 * ((d : ℝ) + 1) ^ 2 * Real.log X)
          = ((X : ℝ) / (2 * ((d : ℝ) + 1))) ^ 2 / (16 * Real.log X) := by field_simp; ring
      _ ≤ (M₁ : ℝ) ^ 2 / (16 * Real.log X) :=
        div_le_div_of_nonneg_right hsq_M (by positivity)
  linarith only [hsq, hint_ge, hbdry_nonneg]

/-- Successive jump function supported on `{d, d + 1}` isolating the single quotient level `d`. -/
def sliceJumpAF (d : ℕ) : ArithmeticFunction ℝ where
  toFun j := if j = 0 then 0 else (if j = d then 1 else 0) - (if j = d + 1 then 1 else 0)
  map_zero' := rfl

private theorem sliceJumpAF_sum_eq {d : ℕ} (hd : 1 ≤ d) (u : ℕ) :
    (∑ j ∈ Icc 1 u, sliceJumpAF d j) = if u = d then 1 else 0 := by
  induction u with
  | zero =>
    have : 0 ≠ d := by omega
    simp [this]
  | succ u ih =>
    rw [sum_Icc_succ_top (by omega : 1 ≤ u + 1), ih]
    change (if u = d then (1 : ℝ) else 0) +
      (if u + 1 = 0 then 0 else (if u + 1 = d then 1 else 0) - (if u + 1 = d + 1 then 1 else 0)) = _
    rw [if_neg (Nat.succ_ne_zero u)]
    have heq : (u + 1 = d + 1) ↔ (u = d) := by omega
    simp only [heq]
    ring

private theorem sliceJumpAF_supportedIn (d : ℕ) : SupportedIn (d + 1) (sliceJumpAF d) := by
  refine ⟨ArithmeticFunction.map_zero, fun n hn => ?_⟩
  change (if n = 0 then (0 : ℝ) else (if n = d then 1 else 0) - (if n = d + 1 then 1 else 0)) = 0
  have hn0 : n ≠ 0 := by omega
  have hnd : n ≠ d := by omega
  have hnd1 : n ≠ d + 1 := by omega
  simp [hn0, hnd, hnd1]

private theorem exists_sliceJump_euler_point {d : ℕ} (hd : 1 ≤ d) :
    ∃ x : ℝ, 3 < x ∧ dirPoly (d + 1) (sliceJumpAF d) x ≠ 0 := by
  have hsup := sliceJumpAF_supportedIn d
  by_contra! h
  have hz : (fun x : ℝ => LSeries (fun n => (sliceJumpAF d n : ℂ)) x) =ᶠ[atTop] 0 := by
    filter_upwards [eventually_gt_atTop (3 : ℝ)] with x hx
    rw [LSeries_eq_dirPoly hsup]
    exact h x hx
  have htop := (LSeriesSummable_of_supportedIn hsup 2).abscissaOfAbsConv_le
  have hall := (LSeries_eventually_eq_zero_iff'.mp hz).resolve_right
    (ne_top_of_le_ne_top (EReal.coe_ne_top _) htop)
  have h0 := Complex.ofReal_eq_zero.mp (hall d (by omega))
  have h1 : sliceJumpAF d d = 1 := by
    change (if d = 0 then (0 : ℝ) else (if d = d then 1 else 0) - (if d = d + 1 then 1 else 0)) = 1
    have hd0 : d ≠ 0 := by omega
    simp [hd0]
  linarith only [h0, h1]

/-- Any `O(X^{b + 1})` bound (`1/2 ≤ b < 1`) on even a single moving quotient slice `d ≥ 1`
excludes all `ζ`-zeros in `Re s > b` and forces `zeroReSup ≤ b`. -/
theorem movingQuotientSlice_bound_excludes_zero_and_bounds_zeroReSup {d : ℕ} (hd : 1 ≤ d)
    {b C : ℝ} (hb : 1 / 2 ≤ b) (hb1 : b < 1)
    (h : ∀ X : ℕ, 1 ≤ X → |movingQuotientSlice d X| ≤ C * (X : ℝ) ^ (b + 1)) :
    (∀ ρ : ℂ, b < ρ.re → riemannZeta ρ ≠ 0) ∧ _root_.RHTower.zeroReSup ≤ b := by
  have hC : 0 ≤ |C| := abs_nonneg C
  have hb0 : 0 ≤ b := by linarith only [hb]
  let g := sliceJumpAF d
  let c : ℕ → ℝ := fun n => (ordinaryPrimeCountWeight * g) n
  have hsup : SupportedIn (d + 1) g := sliceJumpAF_supportedIn d
  have hslice_eq (X : ℕ) :
      (X : ℝ) * triangularPrimeProfile c (X : ℝ)⁻¹ = movingQuotientSlice d X := by
    rw [triangularPrimeProfile_sample, movingQuotientSlice]
    refine sum_congr rfl fun k _ => ?_
    dsimp only [c]
    rw [_root_.RHTower.sum_Icc_mul_apply, sum_filter]
    refine sum_congr rfl fun m _ => ?_
    rw [sliceJumpAF_sum_eq hd]
    split_ifs <;> ring
  have hprofile (N : ℕ) (hN : 1 ≤ N) :
      |triangularPrimeProfile c (N : ℝ)⁻¹| ≤ |C| * (N : ℝ) ^ b := by
    have hp : 0 < (N : ℝ) := by exact_mod_cast hN
    have hh := (h N hN).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
    rw [← hslice_eq N, abs_mul, abs_of_pos hp, Real.rpow_add_one hp.ne'] at hh
    exact le_of_mul_le_mul_left (hh.trans_eq (by ring)) hp
  let H := triangularDirichletContinuation c
  let D := dirPoly (d + 1) g
  have hU : IsOpen {s : ℂ | b < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hH : DifferentiableOn ℂ H {s : ℂ | b < s.re} :=
    fun _ hs => (differentiableAt_triangularDirichletContinuation c hC hb0 hprofile hs).differentiableWithinAt
  have hD : Differentiable ℂ D := differentiable_dirPoly (d + 1) g
  have hG : MeromorphicOn (H / D) {s : ℂ | b < s.re} :=
    fun z hz => ((hH.analyticOnNhd hU z hz).meromorphicAt).div ((hD.analyticAt z).meromorphicAt)
  let f : ℕ → ℂ := fun n => (c n : ℂ)
  have hconv : f = ((fun n => (ordinaryPrimeCountWeight n : ℂ)) ⍟ fun n => (g n : ℂ)) := by
    funext n
    rw [LSeries.convolution_def]
    exact _root_.RHTower.Sieve.coe_mul_apply _ _ _
  have hf_sum {s : ℂ} (hs : 1 < s.re) : LSeriesSummable f s := by
    rw [hconv]
    exact (ordinaryPrimeCountWeight_summable hs).convolution (LSeriesSummable_of_supportedIn hsup s)
  have hf2 : LSeriesSummable f 2 := hf_sum (by norm_num)
  let M := ∑' n, ‖LSeries.term f 2 n‖
  have hcoef (n : ℕ) : |c (n + 1)| ≤ M * ((n : ℝ) + 1) ^ (2 : ℝ) := by
    have he : ‖LSeries.term f 2 (n + 1)‖ ≤ M := hf2.norm.le_tsum (n + 1) (fun _ _ => norm_nonneg _)
    rw [LSeries.norm_term_eq, if_neg (Nat.succ_ne_zero n)] at he
    simp only [f, Complex.norm_real, Real.norm_eq_abs,
      show (2 : ℂ).re = (2 : ℝ) by norm_num, Nat.cast_succ] at he
    exact (div_le_iff₀ (by positivity : 0 < ((n : ℝ) + 1) ^ (2 : ℝ))).mp he
  have hH_eq {s : ℂ} (hs : 3 < s.re) :
      H s = LSeries (fun n => (ordinaryPrimeCountWeight n : ℂ)) s * D s := by
    have hs1 : 1 < s.re := by linarith only [hs]
    have ha := ordinaryPrimeCountWeight_summable hs1
    have hg := LSeriesSummable_of_supportedIn hsup s
    dsimp only [H]
    rw [triangularDirichletContinuation_eq_series c hcoef (by linarith only [hs]) (by linarith only [hs])]
    have hs' := (hasSum_nat_add_iff' 1).mpr (hf_sum hs1).hasSum
    simp only [sum_range_one, LSeries.term_zero, sub_zero] at hs'
    have hL_eq : LSeries f s = LSeries (fun n => (ordinaryPrimeCountWeight n : ℂ)) s * D s := by
      rw [hconv, LSeries_convolution' ha hg, LSeries_eq_dirPoly hsup]
    rw [← hL_eq]
    refine (tsum_congr (g := fun n => LSeries.term f s (n + 1)) fun n => ?_).trans hs'.tsum_eq
    rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n), Complex.cpow_neg, div_eq_mul_inv]
    simp [f]
  obtain ⟨x, hx3, hxD⟩ := exists_sliceJump_euler_point hd
  have hx1 : 1 < x := (by norm_num : (1 : ℝ) < 3).trans hx3
  have hzf : ∀ ρ : ℂ, b < ρ.re → riemannZeta ρ ≠ 0 := by
    intro ρ hρ
    apply ordinaryPrimeCount_series_continuation_excludes_right_zero hb (hb1.trans hx1) hx1 hG _ hρ
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (x : ℂ) ∈ {s : ℂ | 3 < s.re} from hx3),
      hD.continuous.continuousAt.eventually_ne hxD] with s hs hd_ne
    change H s / D s = _
    rw [hH_eq hs, mul_div_cancel_right₀ _ hd_ne]
  refine ⟨hzf, _root_.RHTower.zeroReSup_le_of_forall_re_le fun z => ?_⟩
  by_contra hgt
  exact hzf (z.1 : ℂ) (not_le.mp hgt) (_root_.RHTower.riemannZeta_eq_zero_of_xiZeroCopy z)

/-- For every fixed `d ≥ 1`, `O_ε(X^{3/2 + ε})` cancellation on the single moving quotient slice
`movingQuotientSlice d` is unconditionally equivalent to `RiemannHypothesis`. -/
theorem riemannHypothesis_iff_one_movingQuotientSlice {d : ℕ} (hd : 1 ≤ d) :
    RiemannHypothesis ↔
      ∀ b : ℝ, 1 / 2 < b → b < 1 → ∃ C : ℝ, ∀ X : ℕ, 1 ≤ X →
        |movingQuotientSlice d X| ≤ C * (X : ℝ) ^ (b + 1) := by
  constructor
  · intro hRH b hb _
    have hΘ : _root_.RHTower.zeroReSup ≤ 1 / 2 :=
      _root_.RHTower.zeroReSup_le_of_forall_re_le fun q =>
        (_root_.RHTower.xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q).le
    obtain ⟨K, hK0, hpref⟩ := ordinary_prefix_power (hΘ.trans_lt hb)
    have hb0 : 0 < b := by linarith only [hb]
    refine ⟨4 * K, fun X hX => ?_⟩
    have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
    let B := K * (X : ℝ) ^ b
    have hB0 : 0 ≤ B := by dsimp only [B]; positivity
    have hab := abs_movingQuotientSlice_le_of_prefix hd X hB0 fun j hj => by
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · simp [hB0]
      · have hjX : j ≤ X := hj.trans (Nat.div_le_self X d)
        exact (hpref j hj0).trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg j) (by exact_mod_cast hjX) hb0.le) hK0)
    have hM₁_le : ((X / (d + 1) : ℕ) : ℝ) ≤ X := by exact_mod_cast Nat.div_le_self X (d + 1)
    calc
      |movingQuotientSlice d X| ≤ 4 * B * ((X / (d + 1) : ℕ) : ℝ) := hab
      _ ≤ 4 * (K * (X : ℝ) ^ b) * (X : ℝ) :=
        mul_le_mul_of_nonneg_left hM₁_le (by positivity)
      _ = 4 * K * (X : ℝ) ^ (b + 1) := by
        rw [Real.rpow_add_one hX0.ne']
        ring
  · intro h
    apply _root_.RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip.mpr
    intro ρ hρ hhi
    obtain ⟨b, hb, hbρ⟩ := exists_between hρ
    obtain ⟨C, hC⟩ := h b hb (hbρ.trans hhi)
    exact (movingQuotientSlice_bound_excludes_zero_and_bounds_zeroReSup hd hb.le
      (hbρ.trans hhi) hC).1 ρ hbρ

/-! ## 2. Outer-cutoff paired quotient bands and Bertrand's postulate near `√X` -/

/-- Paired outer-cutoff quotient band summing `w(m) B_m(X)` across `(⌊X/(2Q+2)⌋, ⌊X/(2Q)⌋]`. -/
def outerQuotientPairBand (Q X : ℕ) : ℝ :=
  ∑ m ∈ Ioc (X / (2 * Q + 2)) (X / (2 * Q)),
    ordinaryPrimeCountWeight m * discreteQuotientMean binaryCarryProfile m X

/-- Trivial unsigned benchmark for the paired outer-cutoff quotient band. -/
def outerQuotientPairBandTrivial (Q X : ℕ) : ℝ :=
  ∑ m ∈ Ioc (X / (2 * Q + 2)) (X / (2 * Q)),
    |ordinaryPrimeCountWeight m| * discreteQuotientMean binaryCarryProfile m X

/-- Unconditional sub-`7/8` bound on `outerQuotientPairBand Q X`:
for every `β > 20999 / 24000`, `|outerQuotientPairBand Q X| ≤ C_β X (X / (2Q))^β` for all `Q ≥ 1`. -/
theorem exists_outerQuotientPairBand_sub_seven_eighths {β : ℝ}
    (hβ : (20999 / 24000 : ℝ) < β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Q X : ℕ, 1 ≤ Q →
      |outerQuotientPairBand Q X| ≤ C * (X : ℝ) * ((X : ℝ) / (2 * (Q : ℝ))) ^ β := by
  have hΘ : _root_.RHTower.zeroReSup < β := zeroReSup_le_sub_seven_eighths.trans_lt hβ
  have hβ0 : 0 < β := by linarith
  obtain ⟨K, hK0, hpref⟩ := ordinary_prefix_power hΘ
  refine ⟨5 * K, by positivity, fun Q X hQ => ?_⟩
  let A := X / (2 * Q + 2)
  let B := X / (2 * Q)
  have hAB : A ≤ B := Nat.div_le_div_left (by omega) (by omega)
  rcases eq_or_lt_of_le hAB with hEq | hLt
  · simp only [outerQuotientPairBand]
    change |∑ m ∈ Ioc A B, _| ≤ _
    rw [hEq, Ioc_self, sum_empty, abs_zero]
    positivity
  · have hB_pos : 1 ≤ B := lt_of_le_of_lt (Nat.zero_le A) hLt
    let c : ℕ → ℝ := fun m => if A < m then ordinaryPrimeCountWeight m else 0
    let f : ℕ → ℝ := fun m => discreteQuotientMean binaryCarryProfile m X
    have hband_eq : outerQuotientPairBand Q X = ∑ m ∈ Icc 1 B, c m * f m := by
      rw [outerQuotientPairBand, ← Ioc_zero_eq_Icc_one B,
        ← sum_Ioc_consecutive _ (Nat.zero_le A) hAB]
      have hhead : (∑ m ∈ Ioc 0 A, c m * f m) = 0 :=
        sum_eq_zero fun m hm => by simp [c, not_lt.mpr (mem_Ioc.mp hm).2]
      have htail : (∑ m ∈ Ioc A B, c m * f m) =
          ∑ m ∈ Ioc A B, ordinaryPrimeCountWeight m * f m :=
        sum_congr rfl fun m hm => by simp [c, (mem_Ioc.mp hm).1]
      rw [hhead, zero_add, htail]
    have hc_pref_zero (n : ℕ) (hn : n ≤ A) : (∑ k ∈ Icc 1 n, c k) = 0 :=
      sum_eq_zero fun k hk => by simp [c, not_lt.mpr ((mem_Icc.mp hk).2.trans hn)]
    have hc_pref_le (n : ℕ) (hn : n ≤ B) :
        |∑ k ∈ Icc 1 n, c k| ≤ 2 * K * (B : ℝ) ^ β := by
      rcases le_or_gt n A with hnA | hAn
      · rw [hc_pref_zero n hnA, abs_zero]
        positivity
      · have hsplit : (∑ k ∈ Icc 1 n, c k) =
            (∑ k ∈ Icc 1 n, ordinaryPrimeCountWeight k) -
              ∑ k ∈ Icc 1 A, ordinaryPrimeCountWeight k := by
          have hLHS_c : (∑ k ∈ Icc 1 n, c k) = ∑ k ∈ Ioc A n, ordinaryPrimeCountWeight k := by
            rw [← Ioc_zero_eq_Icc_one n, ← sum_Ioc_consecutive _ (Nat.zero_le A) hAn.le]
            have h0 : (∑ k ∈ Ioc 0 A, c k) = 0 :=
              sum_eq_zero fun k hk => by simp [c, not_lt.mpr (mem_Ioc.mp hk).2]
            have h1 : (∑ k ∈ Ioc A n, c k) = ∑ k ∈ Ioc A n, ordinaryPrimeCountWeight k :=
              sum_congr rfl fun k hk => by simp [c, (mem_Ioc.mp hk).1]
            rw [h0, zero_add, h1]
          have h2 : (∑ k ∈ Icc 1 n, ordinaryPrimeCountWeight k) =
              (∑ k ∈ Icc 1 A, ordinaryPrimeCountWeight k) +
                ∑ k ∈ Ioc A n, ordinaryPrimeCountWeight k := by
            rw [← Ioc_zero_eq_Icc_one n, ← Ioc_zero_eq_Icc_one A,
              sum_Ioc_consecutive _ (Nat.zero_le A) hAn.le]
          linarith only [hLHS_c, h2]
        have hn1 : 1 ≤ n := lt_of_le_of_lt (Nat.zero_le A) hAn
        have hpn : |∑ k ∈ Icc 1 n, ordinaryPrimeCountWeight k| ≤ K * (B : ℝ) ^ β :=
          (hpref n hn1).trans (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast hn) hβ0.le) hK0)
        have hpA : |∑ k ∈ Icc 1 A, ordinaryPrimeCountWeight k| ≤ K * (B : ℝ) ^ β := by
          rcases Nat.eq_zero_or_pos A with hA0 | hA0
          · rw [hA0]
            simp only [Icc_eq_empty (by omega : ¬ 1 ≤ 0), sum_empty, abs_zero]
            positivity
          · exact (hpref A hA0).trans (mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow (Nat.cast_nonneg A) (by exact_mod_cast hAB) hβ0.le) hK0)
        rw [hsplit]
        exact (abs_sub _ _).trans ((add_le_add hpn hpA).trans_eq (by ring))
    have hf_bound (m : ℕ) (hm : 0 < m) : 0 ≤ f m ∧ f m ≤ (X : ℝ) / 2 := by
      refine ⟨sum_nonneg fun k _ => (binaryCarryProfile_bounds _).1, ?_⟩
      dsimp only [f]
      rw [discreteQuotientMean_binaryCarryProfile_eq_half_sub_tent hm X]
      linarith only [(binaryCarryTent_bounds hm X).1]
    have hab := sum_smul_eq_prefix_differences c f B
    simp only [smul_eq_mul] at hab
    rw [hband_eq, hab]
    have hbdry : |(∑ k ∈ Icc 1 B, c k) * f (B + 1)| ≤ K * (X : ℝ) * (B : ℝ) ^ β := by
      have hfB1 := hf_bound (B + 1) (Nat.succ_pos B)
      rw [abs_mul, abs_of_nonneg hfB1.1]
      exact (mul_le_mul (hc_pref_le B le_rfl) hfB1.2 hfB1.1 (by positivity)).trans_eq (by ring)
    have hdiff_sum :
        |∑ n ∈ Icc 1 B, (∑ k ∈ Icc 1 n, c k) * (f n - f (n + 1))| ≤
          4 * K * (X : ℝ) * (B : ℝ) ^ β := by
      -- Only `n ∈ Ioc A B` contribute since `c` vanishes up to `A`
      rw [← Ioc_zero_eq_Icc_one B, ← sum_Ioc_consecutive _ (Nat.zero_le A) hAB]
      have hz : (∑ n ∈ Ioc 0 A, (∑ k ∈ Icc 1 n, c k) * (f n - f (n + 1))) = 0 :=
        sum_eq_zero fun n hn => by rw [hc_pref_zero n (mem_Ioc.mp hn).2, zero_mul]
      rw [hz, zero_add]
      have hA_step : (X : ℝ) / ((A : ℝ) + 1) ≤ 4 * (Q : ℝ) := by
        have hlt : X < (2 * Q + 2) * (A + 1) := by
          have := (Nat.div_lt_iff_lt_mul (by omega : 0 < 2 * Q + 2)).mp (Nat.lt_succ_self A)
          linarith
        have hle_nat : X ≤ 4 * Q * (A + 1) := by nlinarith only [hlt, hQ]
        have hR : (X : ℝ) ≤ 4 * (Q : ℝ) * ((A : ℝ) + 1) := by exact_mod_cast hle_nat
        exact (div_le_iff₀ (by positivity)).mpr hR
      have hterm (n : ℕ) (hn : n ∈ Ioc A B) :
          |(∑ k ∈ Icc 1 n, c k) * (f n - f (n + 1))| ≤
            (2 * K * (B : ℝ) ^ β) * (4 * (Q : ℝ)) := by
        obtain ⟨hnA, hnB⟩ := mem_Ioc.mp hn
        have hn_pos : 0 < n := lt_of_le_of_lt (Nat.zero_le A) hnA
        have hlip : |f n - f (n + 1)| ≤ (X : ℝ) / ((n : ℝ) + 1) :=
          discreteQuotientMean_lipschitz binaryCarryProfile binaryCarryProfile_bounds hn_pos X
        have hAn : (A : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hnA 1
        have hdiv_le : (X : ℝ) / ((n : ℝ) + 1) ≤ 4 * (Q : ℝ) :=
          (div_le_div_of_nonneg_left (Nat.cast_nonneg X) (by positivity) hAn).trans hA_step
        rw [abs_mul]
        exact mul_le_mul (hc_pref_le n hnB) (hlip.trans hdiv_le) (abs_nonneg _) (by positivity)
      have hcard_le : ((Ioc A B).card : ℝ) ≤ B := by
        rw [Nat.card_Ioc A B]
        exact_mod_cast Nat.sub_le B A
      have hQB_le : 4 * (Q : ℝ) * B ≤ 2 * (X : ℝ) := by
        have hmul : 2 * Q * B ≤ X := Nat.mul_div_le X (2 * Q)
        have hR : 2 * (Q : ℝ) * B ≤ X := by exact_mod_cast hmul
        linarith only [hR]
      calc
        |∑ n ∈ Ioc A B, (∑ k ∈ Icc 1 n, c k) * (f n - f (n + 1))|
            ≤ ∑ n ∈ Ioc A B, |(∑ k ∈ Icc 1 n, c k) * (f n - f (n + 1))| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ _n ∈ Ioc A B, (2 * K * (B : ℝ) ^ β) * (4 * (Q : ℝ)) := sum_le_sum hterm
        _ = ((Ioc A B).card : ℝ) * ((2 * K * (B : ℝ) ^ β) * (4 * (Q : ℝ))) := by
          rw [sum_const, nsmul_eq_mul]
        _ ≤ (B : ℝ) * ((2 * K * (B : ℝ) ^ β) * (4 * (Q : ℝ))) :=
          mul_le_mul_of_nonneg_right hcard_le (by positivity)
        _ = (2 * K * (B : ℝ) ^ β) * (4 * (Q : ℝ) * B) := by ring
        _ ≤ (2 * K * (B : ℝ) ^ β) * (2 * (X : ℝ)) :=
          mul_le_mul_of_nonneg_left hQB_le (by positivity)
        _ = 4 * K * (X : ℝ) * (B : ℝ) ^ β := by ring
    have hB_div : (B : ℝ) ≤ (X : ℝ) / (2 * (Q : ℝ)) := by
      simpa [B, Nat.cast_mul] using (Nat.cast_div_le (m := X) (n := 2 * Q))
    have hpow_le : (B : ℝ) ^ β ≤ ((X : ℝ) / (2 * (Q : ℝ))) ^ β :=
      Real.rpow_le_rpow (Nat.cast_nonneg B) hB_div hβ0.le
    calc
      |((∑ k ∈ Icc 1 B, c k) * f (B + 1)) +
          ∑ n ∈ Icc 1 B, (∑ k ∈ Icc 1 n, c k) * (f n - f (n + 1))|
          ≤ |(∑ k ∈ Icc 1 B, c k) * f (B + 1)| +
              |∑ n ∈ Icc 1 B, (∑ k ∈ Icc 1 n, c k) * (f n - f (n + 1))| := abs_add_le _ _
      _ ≤ K * (X : ℝ) * (B : ℝ) ^ β + 4 * K * (X : ℝ) * (B : ℝ) ^ β := add_le_add hbdry hdiff_sum
      _ = 5 * K * (X : ℝ) * (B : ℝ) ^ β := by ring
      _ ≤ 5 * K * (X : ℝ) * ((X : ℝ) / (2 * (Q : ℝ))) ^ β :=
        mul_le_mul_of_nonneg_left hpow_le (by positivity)

/-- Exact exponent `7 / 8` specialization for `outerQuotientPairBand Q X`. -/
theorem exists_outerQuotientPairBand_seven_eighths_exact :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Q X : ℕ, 1 ≤ Q →
      |outerQuotientPairBand Q X| ≤ C * (X : ℝ) * ((X : ℝ) / (2 * (Q : ℝ))) ^ (7 / 8 : ℝ) :=
  exists_outerQuotientPairBand_sub_seven_eighths (β := 7 / 8) (by norm_num)

/-- On any prime-free outer-cutoff band (`2Q + 2 ≤ X`), every summand has negative sign and
`|outerQuotientPairBand Q X| = outerQuotientPairBandTrivial Q X` (zero cancellation). -/
theorem outerQuotientPairBand_abs_eq_trivial_of_primeFree {Q X : ℕ}
    (hX : 2 * Q + 2 ≤ X)
    (hnp : ∀ m ∈ Ioc (X / (2 * Q + 2)) (X / (2 * Q)), ¬ m.Prime) :
    outerQuotientPairBand Q X = -outerQuotientPairBandTrivial Q X ∧
      |outerQuotientPairBand Q X| = outerQuotientPairBandTrivial Q X := by
  have hA1 : 1 ≤ X / (2 * Q + 2) := (Nat.one_le_div_iff (by omega)).mpr hX
  have heq : outerQuotientPairBand Q X = -outerQuotientPairBandTrivial Q X := by
    rw [outerQuotientPairBand, outerQuotientPairBandTrivial, ← sum_neg_distrib]
    refine sum_congr rfl fun m hm => ?_
    have hm_gt := (mem_Ioc.mp hm).1
    have hm2 : 2 ≤ m := by omega
    have hlog_pos : 0 < Real.log m := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
    have hw : ordinaryPrimeCountWeight m = -(Real.log m)⁻¹ := by
      change (if m.Prime then (1 : ℝ) else 0) - (Real.log m)⁻¹ = _
      rw [if_neg (hnp m hm), zero_sub]
    rw [hw, abs_neg, abs_of_pos (inv_pos.mpr hlog_pos), neg_mul]
  refine ⟨heq, ?_⟩
  have htriv_nonneg : 0 ≤ outerQuotientPairBandTrivial Q X :=
    sum_nonneg fun m _ => mul_nonneg (abs_nonneg _)
      (sum_nonneg fun k _ => (binaryCarryProfile_bounds _).1)
  rw [heq, abs_neg, abs_of_nonneg htriv_nonneg]

private theorem mem_outer_band_cover (X : ℕ) {a b p : ℕ} (hab : a ≤ b)
    (hp : p ∈ Ioc (X / (2 * b + 2)) (X / (2 * a))) :
    ∃ Q ∈ Icc a b, p ∈ Ioc (X / (2 * Q + 2)) (X / (2 * Q)) := by
  induction b, hab using Nat.le_induction with
  | base => exact ⟨a, mem_Icc.mpr ⟨le_rfl, le_rfl⟩, hp⟩
  | succ b hab ih =>
    obtain ⟨hp_lo, hp_hi⟩ := mem_Ioc.mp hp
    by_cases hmid : X / (2 * b + 2) < p
    · obtain ⟨Q, hQ, hpQ⟩ := ih (mem_Ioc.mpr ⟨hmid, hp_hi⟩)
      exact ⟨Q, mem_Icc.mpr ⟨(mem_Icc.mp hQ).1, (mem_Icc.mp hQ).2.trans (Nat.le_succ b)⟩, hpQ⟩
    · refine ⟨b + 1, mem_Icc.mpr ⟨by omega, le_rfl⟩, mem_Ioc.mpr ⟨hp_lo, ?_⟩⟩
      have : 2 * (b + 1) = 2 * b + 2 := by omega
      rw [this]
      exact not_lt.mp hmid

/-- Near `√X`, Bertrand's postulate produces for every `ε > 0` and all sufficiently large `X`
a paired outer-cutoff band above `√X` of width at most `13` containing a prime and satisfying
`X / 4 ≤ outerQuotientPairBand Q X` and
`(1 - ε) * outerQuotientPairBandTrivial Q X ≤ |outerQuotientPairBand Q X|`. -/
theorem eventually_exists_sqrt_band_near_trivial {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∃ Q : ℕ,
      X.sqrt / 5 + 1 ≤ Q ∧ 2 * Q + 2 < X.sqrt ∧
      (∀ m ∈ Ioc (X / (2 * Q + 2)) (X / (2 * Q)), X.sqrt < m) ∧
      (Ioc (X / (2 * Q + 2)) (X / (2 * Q))).card ≤ 13 ∧
      (∃ p ∈ Ioc (X / (2 * Q + 2)) (X / (2 * Q)), p.Prime) ∧
      (X : ℝ) / 4 ≤ outerQuotientPairBand Q X ∧
      (1 - ε) * outerQuotientPairBandTrivial Q X ≤ |outerQuotientPairBand Q X| := by
  let Mlog : ℝ := max 84 (84 / ε)
  let T : ℕ := max 35 ⌈Real.exp Mlog⌉₊
  refine eventually_atTop.mpr ⟨T * T, fun X hX => ?_⟩
  let S := X.sqrt
  have hTS : T ≤ S := Nat.le_sqrt.mpr hX
  have hS35 : 35 ≤ S := (le_max_left 35 _).trans hTS
  have hexp_le : Real.exp Mlog ≤ S :=
    (Nat.le_ceil _).trans (by exact_mod_cast ((le_max_right 35 _).trans hTS))
  have hS_pos : (0 : ℝ) < S := by exact_mod_cast (by omega : 0 < S)
  have hMlog_le : Mlog ≤ Real.log S := by
    rw [← Real.log_exp Mlog]
    exact Real.log_le_log (Real.exp_pos _) hexp_le
  have hlog84 : (84 : ℝ) ≤ Real.log S := (le_max_left 84 _).trans hMlog_le
  have hlog_eps : 84 / ε ≤ Real.log S := (le_max_right 84 _).trans hMlog_le
  have hlogS_pos : 0 < Real.log S := by linarith only [hlog84]
  let q₀ := S / 5 + 1
  have hq₀_hi : 4 * q₀ + 2 < S := by omega
  have hS_le_div : S ≤ X / S := (Nat.le_div_iff_mul_le (by omega)).mpr (Nat.sqrt_le X)
  let L₀ := X / (4 * q₀ + 2)
  have hSL : S ≤ L₀ := hS_le_div.trans (Nat.div_le_div_left hq₀_hi.le (by omega))
  obtain ⟨p, hp_prime, hp_gt, hp_le⟩ := Nat.exists_prime_lt_and_le_two_mul L₀ (by omega)
  have h2L_le : 2 * L₀ ≤ X / (2 * q₀) := by
    have h1 : L₀ ≤ X / (4 * q₀) := Nat.div_le_div_left (by omega) (by omega)
    have h2 : X / (4 * q₀) = (X / (2 * q₀)) / 2 := by
      rw [Nat.div_div_eq_div_mul]
      ring_nf
    have h3 : 2 * ((X / (2 * q₀)) / 2) ≤ X / (2 * q₀) := Nat.mul_div_le _ 2
    omega
  have hp_cov : p ∈ Ioc (X / (2 * (2 * q₀) + 2)) (X / (2 * q₀)) := by
    have : 2 * (2 * q₀) + 2 = 4 * q₀ + 2 := by omega
    rw [this]
    exact mem_Ioc.mpr ⟨hp_gt, hp_le.trans h2L_le⟩
  obtain ⟨Q, hQ_mem, hpJ⟩ := mem_outer_band_cover X (by omega : q₀ ≤ 2 * q₀) hp_cov
  obtain ⟨hQ_lo, hQ_hi⟩ := mem_Icc.mp hQ_mem
  have hQ1 : 1 ≤ Q := by omega
  have h2Q2_lt : 2 * Q + 2 < S := by omega
  let A := X / (2 * Q + 2)
  let B := X / (2 * Q)
  let J := Ioc A B
  have hSA : S ≤ A := hS_le_div.trans (Nat.div_le_div_left h2Q2_lt.le (by omega))
  have hm_gt_S : ∀ m ∈ J, S < m := fun m hm => hSA.trans_lt (mem_Ioc.mp hm).1
  have hcard13 : J.card ≤ 13 := by
    rw [show J.card = B - A from Nat.card_Ioc A B]
    have h5Q : S + 1 ≤ 5 * Q := by omega
    have hX_lt_sq : X < (S + 1) * (S + 1) := Nat.lt_succ_sqrt X
    have hX_lt_Q : X < 2 * Q * (Q + 1) * 13 := by nlinarith only [h5Q, hX_lt_sq, hQ1]
    have hB_mul : (2 * Q) * B ≤ X := Nat.mul_div_le X (2 * Q)
    have hA_mul : X < (2 * Q + 2) * (A + 1) := by
      have := (Nat.div_lt_iff_lt_mul (by omega : 0 < 2 * Q + 2)).mp (Nat.lt_succ_self A)
      linarith
    have hBA : 2 * Q * (Q + 1) * B < 2 * Q * (Q + 1) * (A + 14) := by
      nlinarith only [hB_mul, hA_mul, hX_lt_Q, hQ1]
    have hlt14 : B < A + 14 := lt_of_mul_lt_mul_left hBA (by positivity)
    omega
  have hm_carry (m : ℕ) (hm : m ∈ J) :
      (X : ℝ) / 3 ≤ discreteQuotientMean binaryCarryProfile m X ∧
        discreteQuotientMean binaryCarryProfile m X ≤ (X : ℝ) / 2 := by
    obtain ⟨hmA, hmB⟩ := mem_Ioc.mp hm
    have hm_pos : 0 < m := by omega
    have hge_2Q : 2 * Q ≤ X / m := (Nat.le_div_iff_mul_le hm_pos).mpr
      ((Nat.mul_le_mul_left (2 * Q) hmB).trans (Nat.mul_div_le X (2 * Q)))
    have hlt_2Q2 : X / m < 2 * Q + 2 := (Nat.div_lt_iff_lt_mul hm_pos).mpr (by
      have := (Nat.div_lt_iff_lt_mul (by omega : 0 < 2 * Q + 2)).mp hmA
      linarith)
    have hband : X / m = 2 * Q ∨ X / m = 2 * Q + 1 := by omega
    have hadj := discreteQuotientMean_binaryCarryProfile_adjacent_intervals hQ1 hm_pos hband
    exact ⟨hadj.2.1, hadj.2.2⟩
  have hinv_le (m : ℕ) (hm : m ∈ J) : (Real.log m)⁻¹ ≤ (Real.log S)⁻¹ ∧ (Real.log m)⁻¹ ≤ 1 / 84 := by
    have hSm : (S : ℝ) ≤ m := by exact_mod_cast (hm_gt_S m hm).le
    have hlog_le : Real.log S ≤ Real.log m := Real.log_le_log hS_pos hSm
    have h1 : (Real.log m)⁻¹ ≤ (Real.log S)⁻¹ := inv_anti₀ hlogS_pos hlog_le
    have h2 : (Real.log S)⁻¹ ≤ 1 / 84 := by
      rw [one_div]
      exact inv_anti₀ (by norm_num) hlog84
    exact ⟨h1, h1.trans h2⟩
  -- Lower bound `outerQuotientPairBand Q X ≥ X / 4` by isolating `p ∈ J`
  have hband_lb : (X : ℝ) / 4 ≤ outerQuotientPairBand Q X := by
    rw [outerQuotientPairBand]
    change (X : ℝ) / 4 ≤ ∑ m ∈ J, _
    rw [← add_sum_erase _ _ hpJ]
    have hp_w : (83 / 84 : ℝ) ≤ ordinaryPrimeCountWeight p := by
      change (83 / 84 : ℝ) ≤ (if p.Prime then 1 else 0) - (Real.log p)⁻¹
      rw [if_pos hp_prime]
      linarith only [(hinv_le p hpJ).2]
    have hp_B := (hm_carry p hpJ).1
    have hp_term : (83 / 252 : ℝ) * X ≤
        ordinaryPrimeCountWeight p * discreteQuotientMean binaryCarryProfile p X := by
      calc
        (83 / 252 : ℝ) * X = (83 / 84 : ℝ) * ((X : ℝ) / 3) := by ring
        _ ≤ ordinaryPrimeCountWeight p * discreteQuotientMean binaryCarryProfile p X :=
          mul_le_mul hp_w hp_B (by positivity) (by linarith only [hp_w])
    have herase_term (m : ℕ) (hm : m ∈ J.erase p) :
        -((1 / 168 : ℝ) * X) ≤
          ordinaryPrimeCountWeight m * discreteQuotientMean binaryCarryProfile m X := by
      have hmJ := mem_of_mem_erase hm
      have hw_lo : -(1 / 84 : ℝ) ≤ ordinaryPrimeCountWeight m := by
        change -(1 / 84 : ℝ) ≤ (if m.Prime then 1 else 0) - (Real.log m)⁻¹
        have hinv := (hinv_le m hmJ).2
        split_ifs <;> linarith only [hinv]
      have hB := hm_carry m hmJ
      have hB0 : 0 ≤ discreteQuotientMean binaryCarryProfile m X :=
        (by positivity : (0 : ℝ) ≤ (X : ℝ) / 3).trans hB.1
      by_cases hw0 : 0 ≤ ordinaryPrimeCountWeight m
      · exact (neg_nonpos.mpr (by positivity)).trans (mul_nonneg hw0 hB0)
      · have habs_w : -ordinaryPrimeCountWeight m ≤ 1 / 84 := by linarith only [hw_lo]
        have hm1 : (-ordinaryPrimeCountWeight m) * discreteQuotientMean binaryCarryProfile m X ≤
            (1 / 84 : ℝ) * ((X : ℝ) / 2) :=
          mul_le_mul habs_w hB.2 hB0 (by norm_num)
        linarith only [hm1]
    have herase_card : ((J.erase p).card : ℝ) ≤ 12 := by
      have hc : (J.erase p).card = J.card - 1 := card_erase_of_mem hpJ
      have h12 : (J.erase p).card ≤ 12 := by omega
      exact_mod_cast h12
    have herase_sum : -((12 / 168 : ℝ) * X) ≤
        ∑ m ∈ J.erase p, ordinaryPrimeCountWeight m * discreteQuotientMean binaryCarryProfile m X := by
      calc
        -((12 / 168 : ℝ) * X) = 12 * (-((1 / 168 : ℝ) * X)) := by ring
        _ ≤ ((J.erase p).card : ℝ) * (-((1 / 168 : ℝ) * X)) := by
          have hX0 : (0 : ℝ) ≤ X := Nat.cast_nonneg X
          nlinarith only [herase_card, hX0]
        _ = ∑ _m ∈ J.erase p, -((1 / 168 : ℝ) * X) := by rw [sum_const, nsmul_eq_mul]
        _ ≤ ∑ m ∈ J.erase p,
              ordinaryPrimeCountWeight m * discreteQuotientMean binaryCarryProfile m X :=
          sum_le_sum herase_term
    have hX0 : (0 : ℝ) ≤ X := Nat.cast_nonneg X
    linarith only [hp_term, herase_sum, hX0]
  -- Bound `outerQuotientPairBandTrivial Q X - outerQuotientPairBand Q X ≤ 13 * X / log S`
  have hdiff_le :
      outerQuotientPairBandTrivial Q X - outerQuotientPairBand Q X ≤
        13 * ((X : ℝ) / Real.log S) := by
    rw [outerQuotientPairBandTrivial, outerQuotientPairBand, ← sum_sub_distrib]
    change (∑ m ∈ J, _) ≤ _
    have hterm_diff (m : ℕ) (hm : m ∈ J) :
        |ordinaryPrimeCountWeight m| * discreteQuotientMean binaryCarryProfile m X -
            ordinaryPrimeCountWeight m * discreteQuotientMean binaryCarryProfile m X ≤
          (X : ℝ) / Real.log S := by
      have hB := hm_carry m hm
      have hB0 : 0 ≤ discreteQuotientMean binaryCarryProfile m X :=
        (by positivity : (0 : ℝ) ≤ (X : ℝ) / 3).trans hB.1
      have hinv := hinv_le m hm
      have hsub_w : |ordinaryPrimeCountWeight m| - ordinaryPrimeCountWeight m ≤
          2 * (Real.log S)⁻¹ := by
        change |(if m.Prime then (1 : ℝ) else 0) - (Real.log m)⁻¹| -
          ((if m.Prime then (1 : ℝ) else 0) - (Real.log m)⁻¹) ≤ _
        by_cases hmp : m.Prime
        · rw [if_pos hmp]
          have hpos : 0 ≤ 1 - (Real.log m)⁻¹ := by linarith only [hinv.2]
          rw [abs_of_nonneg hpos, sub_self]
          positivity
        · rw [if_neg hmp, zero_sub, abs_neg]
          have hlogm_pos : 0 ≤ (Real.log m)⁻¹ :=
            inv_nonneg.mpr (Real.log_nonneg (by exact_mod_cast (by have := hm_gt_S m hm; omega : 1 ≤ m)))
          rw [abs_of_nonneg hlogm_pos]
          linarith only [hinv.1]
      calc
        |ordinaryPrimeCountWeight m| * discreteQuotientMean binaryCarryProfile m X -
            ordinaryPrimeCountWeight m * discreteQuotientMean binaryCarryProfile m X
            = (|ordinaryPrimeCountWeight m| - ordinaryPrimeCountWeight m) *
                discreteQuotientMean binaryCarryProfile m X := (sub_mul ..).symm
        _ ≤ (2 * (Real.log S)⁻¹) * ((X : ℝ) / 2) :=
          mul_le_mul hsub_w hB.2 hB0 (by positivity)
        _ = (X : ℝ) / Real.log S := by ring
    have hcardR : (J.card : ℝ) ≤ 13 := by exact_mod_cast hcard13
    calc
      (∑ m ∈ J, (|ordinaryPrimeCountWeight m| * discreteQuotientMean binaryCarryProfile m X -
          ordinaryPrimeCountWeight m * discreteQuotientMean binaryCarryProfile m X))
          ≤ ∑ _m ∈ J, (X : ℝ) / Real.log S := sum_le_sum hterm_diff
      _ = (J.card : ℝ) * ((X : ℝ) / Real.log S) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ 13 * ((X : ℝ) / Real.log S) := mul_le_mul_of_nonneg_right hcardR (by positivity)
  have htriv_ge : (X : ℝ) / 4 ≤ outerQuotientPairBandTrivial Q X := by
    have hle_abs : outerQuotientPairBand Q X ≤ |outerQuotientPairBand Q X| := le_abs_self _
    have habs_le_triv : |outerQuotientPairBand Q X| ≤ outerQuotientPairBandTrivial Q X := by
      rw [outerQuotientPairBand, outerQuotientPairBandTrivial]
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun m _ => ?_)
      have hBm0 : 0 ≤ discreteQuotientMean binaryCarryProfile m X :=
        sum_nonneg fun k _ => (binaryCarryProfile_bounds _).1
      rw [abs_mul, abs_of_nonneg hBm0]
    exact hband_lb.trans (hle_abs.trans habs_le_triv)
  have h13_eps : 13 * ((X : ℝ) / Real.log S) ≤ ε * outerQuotientPairBandTrivial Q X := by
    have hinv_eps : (Real.log S)⁻¹ ≤ ε / 84 := by
      have h1 : (Real.log S)⁻¹ ≤ (84 / ε)⁻¹ := inv_anti₀ (div_pos (by norm_num) hε) hlog_eps
      rwa [inv_div] at h1
    have hX0 : (0 : ℝ) ≤ X := Nat.cast_nonneg X
    calc
      13 * ((X : ℝ) / Real.log S) = 13 * (X : ℝ) * (Real.log S)⁻¹ := by ring
      _ ≤ 13 * (X : ℝ) * (ε / 84) := mul_le_mul_of_nonneg_left hinv_eps (by positivity)
      _ ≤ ε * ((X : ℝ) / 4) := by nlinarith only [hX0, hε]
      _ ≤ ε * outerQuotientPairBandTrivial Q X := mul_le_mul_of_nonneg_left htriv_ge hε.le
  refine ⟨Q, hQ_lo, h2Q2_lt, hm_gt_S, hcard13, ⟨p, hpJ, hp_prime⟩, hband_lb, ?_⟩
  have hle_abs : outerQuotientPairBand Q X ≤ |outerQuotientPairBand Q X| := le_abs_self _
  linarith only [hdiff_le, h13_eps, hle_abs]

#print axioms sum_movingOddQuotientBand_eq_ordinaryLastClassTotal
#print axioms movingQuotientSlice_eq_interior_add_boundary_strip
#print axioms exists_movingOddQuotientBand_fifteen_eighths_exact
#print axioms movingQuotientSliceTrivial_lower_bound
#print axioms riemannHypothesis_iff_one_movingQuotientSlice
#print axioms exists_outerQuotientPairBand_seven_eighths_exact
#print axioms outerQuotientPairBand_abs_eq_trivial_of_primeFree
#print axioms eventually_exists_sqrt_band_near_trivial

end GaloisForLFunctions.ExceptionalLayerTheory
