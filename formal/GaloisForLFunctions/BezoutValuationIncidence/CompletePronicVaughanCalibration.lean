import GaloisForLFunctions.BezoutValuationIncidence.PronicPotentialSelfCancellationAndInteriorGradientConservation
import GaloisForLFunctions.RHTower.MobiusSquareRectangularBilinear
import GaloisForLFunctions.RHTower.PMRamanujanComplementarySourceBounds
import Mathlib.Analysis.PSeries

/-!
# Complete weighted Vaughan calibration of the pronic energy

The literal moving floor kernel yields five source components and all twenty-five
weighted Gram entries. Existing logarithmic Möbius cancellation bounds their signed
mixed sum uniformly in both Vaughan cutoffs; its squared majorant remains nonsummable
below half damping. The active boundary changes centered-source energy by a bounded
amount. Component sign flips identify the mixed observation omitted by diagonal data.
-/

open Finset Filter ArithmeticFunction RHTower
open GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators Topology

noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence

set_option autoImplicit false

/-- The moving floor weight of the literal damped divisor prefix. -/
def pmPronicFloorWeight (ε : ℝ) (n d : ℕ) : ℝ :=
  (d : ℝ) ^ (-ε) * (n / d : ℕ)

/-- The centered prefix retains the complete zeta density. -/
theorem pmCenteredPrefix_eq_weighted_floor (ε : ℝ) (n : ℕ) :
    pmPowerDampedCenteredDivisorPrefix ε n =
      (∑ d ∈ Icc 1 n, (moebius d : ℝ) * pmPronicFloorWeight ε n d) -
        (pmPowerDampedDivisorDensity ε).re * n := by
  have h := congrArg Complex.re
    (pmPowerDampedDivisorSum_eq_floor_sum ε (x := (n : ℝ))
      (Nat.cast_nonneg _) (N := n) (by simp))
  have hf (d : ℕ) : (⌊(n : ℝ) / d⌋ : ℝ) = (n / d : ℕ) := by
    rw [← Int.natCast_floor_eq_floor (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)),
      Nat.floor_div_eq_div, Int.cast_natCast]
  simp only [pmPowerDampedDivisorSum, Nat.floor_natCast, Complex.ofReal_re,
    Complex.re_sum, pmPowerDampedMobiusCoeff, ← Complex.ofReal_intCast, ← Complex.ofReal_mul,
    hf] at h
  rw [pmPowerDampedCenteredDivisorPrefix_eq, h]
  simp only [pmPronicFloorWeight, mul_assoc]

/-- Both small legs, both-large remainder, density and active boundary stay separate. -/
def pmPronicVaughanPiece (ε : ℝ) (U V n : ℕ) : Fin 5 → ℝ :=
  ![∑ d ∈ Icc 1 (min U n), (moebius d : ℝ) * pmPronicFloorWeight ε n d,
    ∑ d ∈ Icc 1 (min V n), (moebius d : ℝ) * pmPronicFloorWeight ε n d,
    -(∑ a ∈ Icc 1 (min U n), (moebius a : ℝ) *
      ∑ b ∈ Icc 1 (min V n), (moebius b : ℝ) *
        ∑ k ∈ Icc 1 (n / (a * b)), pmPronicFloorWeight ε n (a * b * k)),
    ∑ a ∈ Ioc (min U n) n, (moebius a : ℝ) *
      ∑ b ∈ Ioc (min V n) n, (moebius b : ℝ) *
        ∑ k ∈ Icc 1 (n / (a * b)), pmPronicFloorWeight ε n (a * b * k),
    -(pmPowerDampedDivisorDensity ε).re * n -
      addDiff (pmActiveSawtoothComponent ε) n]

/-- Exact Vaughan expansion at every moving endpoint, including the active correction. -/
theorem sum_pmPronicVaughanPiece (ε : ℝ) (U V n : ℕ) :
    (∑ i : Fin 5, pmPronicVaughanPiece ε U V n i) = pmBezoutInteriorPrefix ε n := by
  have h := sum_moebius_weight_eq_rectangular_with_tail
    (min_le_right U n) (min_le_right V n) (pmPronicFloorWeight ε n)
  have ha := pmPowerDampedCenteredDivisorPrefix_eq_bezout_active_pair_add_interior ε n
  rw [pmCenteredPrefix_eq_weighted_floor, h] at ha
  simp only [pmPronicVaughanPiece, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero]
  linarith

/-- Weighted Gram entries retain every moving floor endpoint and principal term. -/
def pmPronicVaughanGram (ε : ℝ) (U V T : ℕ) (i j : Fin 5) : ℝ :=
  ∑ n ∈ Icc 1 T, pmPronicVaughanPiece ε U V n i *
    pmPronicVaughanPiece ε U V n j / (pronicSeq n : ℝ)

/-- The complete receiver is the sum of all twenty-five signed Gram entries. -/
theorem pmInteriorPronicEnergy_eq_vaughanGram (ε : ℝ) (U V T : ℕ) :
    pmBezoutInteriorPronicEnergy ε T =
      ∑ i : Fin 5, ∑ j : Fin 5, pmPronicVaughanGram ε U V T i j := by
  calc
    _ = ∑ n ∈ Icc 1 T,
        (∑ i : Fin 5, pmPronicVaughanPiece ε U V n i) *
          (∑ j : Fin 5, pmPronicVaughanPiece ε U V n j) / (pronicSeq n : ℝ) := by
      simp only [sum_pmPronicVaughanPiece, ← sq, pmBezoutInteriorPronicEnergy]
    _ = ∑ n ∈ Icc 1 T, ∑ i : Fin 5, ∑ j : Fin 5,
        pmPronicVaughanPiece ε U V n i * pmPronicVaughanPiece ε U V n j /
          (pronicSeq n : ℝ) := by
      simp only [Finset.sum_mul_sum, Finset.sum_div]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      rfl

/-- Off-diagonal signed contribution, with both orientations retained. -/
def pmPronicVaughanMixedRemainder (ε : ℝ) (U V T : ℕ) : ℝ :=
  ∑ i : Fin 5, ∑ j : Fin 5, if i = j then 0 else pmPronicVaughanGram ε U V T i j

/-- Diagonal observations leave exactly this signed mixed remainder unpaid. -/
theorem pmInteriorPronicEnergy_eq_diagonal_add_mixed (ε : ℝ) (U V T : ℕ) :
    pmBezoutInteriorPronicEnergy ε T =
      (∑ i : Fin 5, pmPronicVaughanGram ε U V T i i) +
        pmPronicVaughanMixedRemainder ε U V T := by
  rw [pmInteriorPronicEnergy_eq_vaughanGram, pmPronicVaughanMixedRemainder,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h := Finset.sum_filter_add_sum_filter_not (s := (univ : Finset (Fin 5)))
    (fun j => i = j) (pmPronicVaughanGram ε U V T i)
  simpa [Finset.sum_filter] using h.symm

/-- The exact energy majorant obtained by squaring logarithmic source cancellation. -/
def pmPronicLogMajorant (ε : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) ^ (1 - ε) / Real.log (n : ℝ) ^ 4) ^ 2 / (pronicSeq n : ℝ)

private theorem interior_log_bound (ε : Set.Ioo (0 : ℝ) (1 / 2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      |pmBezoutInteriorPrefix ε n| ≤
        3 / 2 + C * (n : ℝ) ^ (1 - (ε : ℝ)) / Real.log (n : ℝ) ^ 4 := by
  obtain ⟨C, hC, h⟩ := pmPowerDampedDivisorRemainder_eventually_log_four ε.property.1 ε.property.2
  refine ⟨C, hC, ?_⟩
  filter_upwards [h] with n hn
  have he := pmPowerDampedDivisorRemainder_eq_centered_prefix ε.property.1 (Nat.cast_nonneg n)
  simp only [Nat.floor_natCast, Int.fract_natCast, Complex.ofReal_zero, mul_zero, sub_zero] at he
  have ha : |pmPowerDampedCenteredDivisorPrefix ε n| ≤
      1 + C * (n : ℝ) ^ (1 - (ε : ℝ)) / Real.log (n : ℝ) ^ 4 := by
    simpa only [he, Complex.norm_real, Real.norm_eq_abs] using hn
  have hs := pmPowerDampedCenteredDivisorPrefix_eq_bezout_active_pair_add_interior (ε : ℝ) n
  have hi : pmBezoutInteriorPrefix ε n = pmPowerDampedCenteredDivisorPrefix ε n -
      addDiff (pmActiveSawtoothComponent ε) n := by linarith
  rw [hi]
  have hb := abs_sub (pmPowerDampedCenteredDivisorPrefix ε n)
    (addDiff (pmActiveSawtoothComponent ε) n)
  have hc := abs_addDiff_pmActiveSawtoothComponent_le_half ε.property.1.le n
  linarith

/-- The complete interior receiver inherits a logarithmic saving, with every initial term retained. -/
theorem pmInteriorPronicEnergy_logarithmic_bound (ε : Set.Ioo (0 : ℝ) (1 / 2)) :
    ∃ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℕ,
      pmBezoutInteriorPronicEnergy ε (N + L) ≤
        pmBezoutInteriorPronicEnergy ε N + 9 / 2 +
          2 * C ^ 2 * ∑ n ∈ Ioc N (N + L), pmPronicLogMajorant ε n := by
  obtain ⟨C, hC, h⟩ := interior_log_bound ε
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  refine ⟨N, C, hC, fun L => ?_⟩
  have hsplit : Icc 1 (N + L) = Icc 1 N ∪ Ioc N (N + L) := by
    ext n
    simp only [mem_Icc, mem_union, mem_Ioc]
    omega
  have hdisj : Disjoint (Icc 1 N) (Ioc N (N + L)) := by
    rw [disjoint_left]
    intro n hn hm
    have := (mem_Icc.mp hn).2
    have := (mem_Ioc.mp hm).1
    omega
  have hpoint (n : ℕ) (hn : n ∈ Ioc N (N + L)) :
      pmBezoutInteriorPrefix ε n ^ 2 / (pronicSeq n : ℝ) ≤
        (9 / 2 : ℝ) * (1 / (pronicSeq n : ℝ)) +
          2 * C ^ 2 * pmPronicLogMajorant ε n := by
    have hb := hN n (mem_Ioc.mp hn).1.le
    let g := (n : ℝ) ^ (1 - (ε : ℝ)) / Real.log (n : ℝ) ^ 4
    have hg : 0 ≤ g := by dsimp [g]; positivity
    have hgC : 0 ≤ C * g := mul_nonneg hC hg
    have hb' : |pmBezoutInteriorPrefix ε n| ≤ 3 / 2 + C * g := by
      simpa only [g, mul_div_assoc] using hb
    have hs : pmBezoutInteriorPrefix ε n ^ 2 ≤ 9 / 2 + 2 * C ^ 2 * g ^ 2 := by
      have hsq := sq_nonneg (3 / 2 - C * g)
      have ha := abs_nonneg (pmBezoutInteriorPrefix ε n)
      have hab := sq_abs (pmBezoutInteriorPrefix ε n)
      nlinarith
    have hh := div_le_div_of_nonneg_right hs (Nat.cast_nonneg (α := ℝ) (pronicSeq n))
    dsimp only [pmPronicLogMajorant]
    dsimp only [g] at hh
    calc
      _ ≤ (9 / 2 + 2 * C ^ 2 * ((n : ℝ) ^ (1 - (ε : ℝ)) /
          Real.log (n : ℝ) ^ 4) ^ 2) / (pronicSeq n : ℝ) := hh
      _ = _ := by ring
  have hrecip : (∑ n ∈ Ioc N (N + L), (1 : ℝ) / (pronicSeq n : ℝ)) ≤ 1 := by
    apply le_trans ?_ (sum_one_div_pronicSeq_le_one (N + L))
    apply sum_le_sum_of_subset_of_nonneg
    · intro n hn
      obtain ⟨hlo, hhi⟩ := mem_Ioc.mp hn
      exact mem_Icc.mpr ⟨by omega, hhi⟩
    · intro n _ _
      positivity
  have htail := sum_le_sum hpoint
  rw [sum_add_distrib, ← mul_sum, ← mul_sum] at htail
  unfold pmBezoutInteriorPronicEnergy
  rw [hsplit, sum_union hdisj]
  linarith

private theorem harmonic_le_log_majorant (ε : ℝ) {n : ℕ} (hn : 2 ≤ n)
    (hlog : Real.log (n : ℝ) ^ 8 ≤ (n : ℝ) ^ (1 - 2 * ε)) :
    1 / (n : ℝ) ≤ 2 * pmPronicLogMajorant ε n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  have hl : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  have he : (n : ℝ) * (n : ℝ) ^ (1 - 2 * ε) = ((n : ℝ) ^ (1 - ε)) ^ 2 := by
    calc
      _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (1 - 2 * ε) := by rw [Real.rpow_one]
      _ = (n : ℝ) ^ (1 + (1 - 2 * ε)) := (Real.rpow_add hn0 _ _).symm
      _ = (n : ℝ) ^ ((1 - ε) * 2) := by congr 1; ring
      _ = _ := by rw [Real.rpow_mul hn0.le, Real.rpow_two]
  have hm := mul_le_mul_of_nonneg_left hlog hn0.le
  rw [he] at hm
  have hp : Real.log (n : ℝ) ^ 8 * ((n : ℝ) + 1) ≤
      2 * ((n : ℝ) ^ (1 - ε)) ^ 2 := by
    have hnle : (n : ℝ) + 1 ≤ 2 * n := by linarith
    have hh := mul_le_mul_of_nonneg_left hnle (pow_nonneg hl.le 8)
    nlinarith
  unfold pmPronicLogMajorant
  rw [div_pow, ← pow_mul]
  rw [show (4 : ℕ) * 2 = 8 by omega]
  simp only [pronicSeq, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rw [div_div, ← mul_div_assoc]
  apply (div_le_div_iff₀ hn0 (by positivity)).mpr
  have hh := mul_le_mul_of_nonneg_left hp hn0.le
  nlinarith

/-- This particular source-derived upper bound remains nonsummable at every sub-half damping. -/
theorem not_summable_pmPronicLogMajorant (ε : Set.Ioo (0 : ℝ) (1 / 2)) :
    ¬ Summable (pmPronicLogMajorant ε) := by
  have hδ : 0 < 1 - 2 * (ε : ℝ) := by linarith [ε.property.2]
  have hsmall := ((isLittleO_log_rpow_rpow_atTop (8 : ℝ) hδ).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))).bound (c := 1) (by norm_num)
  have hev : ∀ᶠ n : ℕ in atTop, 1 / (n : ℝ) ≤ 2 * pmPronicLogMajorant ε n := by
    filter_upwards [hsmall, eventually_ge_atTop 2] with n hs hn
    have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
    have hl : 0 ≤ Real.log (n : ℝ) := (Real.log_pos hn1).le
    simp only [Function.comp_def, Real.norm_of_nonneg (Real.rpow_nonneg hl _),
      Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _), one_mul] at hs
    rw [show Real.log (n : ℝ) ^ (8 : ℝ) = Real.log (n : ℝ) ^ (8 : ℕ) from
      Real.rpow_natCast _ 8] at hs
    exact harmonic_le_log_majorant ε hn hs
  intro hsum
  have hhar : Summable (fun n : ℕ => 1 / (n : ℝ)) :=
    (hsum.mul_left 2).of_norm_bounded_eventually_nat
      (hev.mono fun n hn => by simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 / (n : ℝ))] using hn)
  have hp : Summable (fun n : ℕ => (n : ℝ) ^ (-1 : ℝ)) := by
    simpa only [Real.rpow_neg_one, one_div] using hhar
  have hh := Real.summable_nat_rpow.mp hp
  linarith

/-- Source-derived signed bound relative to the diagonal budget, uniformly in both cutoffs. -/
theorem pmPronicVaughanMixedRemainder_logarithmic_bound
    (ε : Set.Ioo (0 : ℝ) (1 / 2)) :
    ∃ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ U V L : ℕ,
      pmPronicVaughanMixedRemainder ε U V (N + L) ≤
        pmBezoutInteriorPronicEnergy ε N + 9 / 2 +
          2 * C ^ 2 * (∑ n ∈ Ioc N (N + L), pmPronicLogMajorant ε n) -
            ∑ i : Fin 5, pmPronicVaughanGram ε U V (N + L) i i := by
  obtain ⟨N, C, hC, hb⟩ := pmInteriorPronicEnergy_logarithmic_bound ε
  refine ⟨N, C, hC, fun U V L => ?_⟩
  have he := pmInteriorPronicEnergy_eq_diagonal_add_mixed (ε : ℝ) U V (N + L)
  linarith [hb L]

/-- Flipping a component preserves its diagonal energy; no alternative arithmetic source is asserted. -/
theorem pmPronicVaughan_flip_diagonal (ε : ℝ) (U V T : ℕ) (k i : Fin 5) :
    (∑ n ∈ Icc 1 T,
      (if i = k then -pmPronicVaughanPiece ε U V n i else pmPronicVaughanPiece ε U V n i) ^ 2 /
        (pronicSeq n : ℝ)) = pmPronicVaughanGram ε U V T i i := by
  by_cases h : i = k <;> simp [h, pmPronicVaughanGram, pow_two]

/-- A component sign flip removes twice that component from the complete source. -/
theorem sum_pmPronicVaughanPiece_flip (ε : ℝ) (U V n : ℕ) (k : Fin 5) :
    (∑ i : Fin 5,
      if i = k then -pmPronicVaughanPiece ε U V n i else pmPronicVaughanPiece ε U V n i) =
      pmBezoutInteriorPrefix ε n - 2 * pmPronicVaughanPiece ε U V n k := by
  have hp (i : Fin 5) :
      (if i = k then -pmPronicVaughanPiece ε U V n i else pmPronicVaughanPiece ε U V n i) =
      pmPronicVaughanPiece ε U V n i -
        2 * (if i = k then pmPronicVaughanPiece ε U V n i else 0) := by
    by_cases h : i = k <;> simp only [h, if_true, if_false] <;> ring
  simp_rw [hp]
  rw [sum_sub_distrib, ← mul_sum, sum_pmPronicVaughanPiece]
  simp

/-- The exact signed observation missing from diagonal data is the cross pairing with the other components. -/
theorem pmPronicVaughan_flip_energy_gap (ε : ℝ) (U V T : ℕ) (k : Fin 5) :
    pmBezoutInteriorPronicEnergy ε T -
      (∑ n ∈ Icc 1 T,
        (pmBezoutInteriorPrefix ε n - 2 * pmPronicVaughanPiece ε U V n k) ^ 2 /
          (pronicSeq n : ℝ)) =
      4 * ((∑ j : Fin 5, pmPronicVaughanGram ε U V T k j) -
        pmPronicVaughanGram ε U V T k k) := by
  have hc : (∑ j : Fin 5, pmPronicVaughanGram ε U V T k j) =
      ∑ n ∈ Icc 1 T, pmPronicVaughanPiece ε U V n k * pmBezoutInteriorPrefix ε n /
        (pronicSeq n : ℝ) := by
    unfold pmPronicVaughanGram
    rw [sum_comm]
    apply sum_congr rfl
    intro n _
    rw [← sum_div, ← mul_sum, sum_pmPronicVaughanPiece]
  rw [hc, pmBezoutInteriorPronicEnergy, pmPronicVaughanGram]
  simp only [← sum_sub_distrib, mul_sum]
  apply sum_congr rfl
  intro n _
  ring

/-- The active boundary changes the energy density by an absolutely summable sequence. -/
theorem summable_pmInteriorPronicEnergy_difference
    (ε : Set.Ioo (0 : ℝ) (1 / 2)) :
    Summable (fun n : ℕ =>
      |(pmBezoutInteriorPrefix ε n ^ 2 - pmPowerDampedCenteredDivisorPrefix ε n ^ 2) /
        (pronicSeq n : ℝ)|) := by
  obtain ⟨C, hC, hI⟩ := interior_log_bound ε
  have hlog : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n : ℝ) :=
    ((Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
      (eventually_ge_atTop 1))
  have hmajor : Summable (fun n : ℕ =>
      (7 / 4 : ℝ) * (1 / (n : ℝ) ^ 2) + C * (n : ℝ) ^ (-1 - (ε : ℝ))) :=
    ((Real.summable_one_div_nat_pow.mpr (by omega : 1 < (2 : ℕ))).mul_left (7 / 4)).add
      ((Real.summable_nat_rpow.mpr (by linarith [ε.property.1])).mul_left C)
  apply hmajor.of_norm_bounded_eventually_nat
  filter_upwards [hI, hlog, eventually_ge_atTop 1] with n hIn hl hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : 0 ≤ (pronicSeq n : ℝ) := Nat.cast_nonneg _
  have hpow : (1 : ℝ) ≤ Real.log (n : ℝ) ^ 4 := one_le_pow₀ hl
  have hib : |pmBezoutInteriorPrefix ε n| ≤
      3 / 2 + C * (n : ℝ) ^ (1 - (ε : ℝ)) := by
    have hdiv := div_le_self
      (mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg n) (1 - (ε : ℝ)))) hpow
    linarith
  let D := addDiff (pmActiveSawtoothComponent ε) n
  have hd : |D| ≤ 1 / 2 := abs_addDiff_pmActiveSawtoothComponent_le_half ε.property.1.le n
  have hdsq : D ^ 2 ≤ 1 / 4 := by nlinarith [abs_nonneg D, sq_abs D]
  have hprod := mul_le_mul_of_nonneg_left hd
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (abs_nonneg (pmBezoutInteriorPrefix ε n)))
  have hform : pmBezoutInteriorPrefix ε n ^ 2 - pmPowerDampedCenteredDivisorPrefix ε n ^ 2 =
      -(2 * pmBezoutInteriorPrefix ε n * D + D ^ 2) := by
    rw [pmPowerDampedCenteredDivisorPrefix_eq_bezout_active_pair_add_interior]
    dsimp [D]
    ring
  have hnum : |pmBezoutInteriorPrefix ε n ^ 2 - pmPowerDampedCenteredDivisorPrefix ε n ^ 2| ≤
      7 / 4 + C * (n : ℝ) ^ (1 - (ε : ℝ)) := by
    rw [hform, abs_neg]
    have ha := abs_add_le (2 * pmBezoutInteriorPrefix ε n * D) (D ^ 2)
    simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_nonneg (sq_nonneg D)] at ha
    linarith
  have hr : (n : ℝ) ^ (1 - (ε : ℝ)) / (n : ℝ) ^ 2 =
      (n : ℝ) ^ (-1 - (ε : ℝ)) := by
    rw [← Real.rpow_two, ← Real.rpow_sub hn0]
    congr 1
    ring
  simp only [Real.norm_eq_abs, abs_abs, abs_div, abs_of_nonneg hp]
  calc
    _ ≤ (7 / 4 + C * (n : ℝ) ^ (1 - (ε : ℝ))) / (pronicSeq n : ℝ) :=
      div_le_div_of_nonneg_right hnum hp
    _ ≤ (7 / 4 + C * (n : ℝ) ^ (1 - (ε : ℝ))) / (n : ℝ) ^ 2 := by
      have hden : (n : ℝ) ^ 2 ≤ (pronicSeq n : ℝ) := by
        simp only [pronicSeq, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        nlinarith
      gcongr
    _ = _ := by rw [add_div, mul_div_assoc, hr]; ring

/-- The interior/source energy difference is uniformly bounded, without bounding either energy. -/
theorem pmInteriorPronicEnergy_sub_source_uniformly_bounded
    (ε : Set.Ioo (0 : ℝ) (1 / 2)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℕ,
      |pmBezoutInteriorPronicEnergy ε T - pmPowerDampedDivisorDiscreteEnergy ε T| ≤ K := by
  let f : ℕ → ℝ := fun n =>
    (pmBezoutInteriorPrefix ε n ^ 2 - pmPowerDampedCenteredDivisorPrefix ε n ^ 2) /
      (pronicSeq n : ℝ)
  have hs : Summable (fun n => |f n|) := summable_pmInteriorPronicEnergy_difference ε
  refine ⟨∑' n, |f n|, tsum_nonneg (fun n => abs_nonneg (f n)), fun T => ?_⟩
  rw [pmBezoutInteriorPronicEnergy, pmPowerDampedDivisorDiscreteEnergy_eq_sum_pronicSeq,
    ← sum_sub_distrib]
  simp only [← sub_div]
  exact (abs_sum_le_sum_abs f (Icc 1 T)).trans (hs.sum_le_tsum _ (fun n _ => abs_nonneg (f n)))

end GaloisForLFunctions.BezoutValuationIncidence
