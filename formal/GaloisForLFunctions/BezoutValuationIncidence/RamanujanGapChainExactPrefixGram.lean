import GaloisForLFunctions.BezoutValuationIncidence.RamanujanDilationProfileResidueGapBudget
import GaloisForLFunctions.BezoutValuationIncidence.RamanujanOrderedGapCollectivePrefixEnergy
import GaloisForLFunctions.BezoutValuationIncidence.DilationJumpValuationClock
import GaloisForLFunctions.BezoutValuationIncidence.NonMarkovianLagOperatorAlgebraAndPrimePowerRevival

/-!
# Exact gap-chain prefix Gram and arithmetic visibility

On each quotient cell the two jump locations split the literal distance into
constant pieces. Their pronic masses leave the harmonic square of the jump
coefficient and a telescoping primitive boundary. The resulting finite-prefix
identity retains all signed Möbius cancellation before squaring. For an ordered
gap chain, every cross term belongs to one endpoint product. The exact Gram
gives a uniform half-energy lower bound, visibility at the valuation clock,
and coefficient recovery at primitive resets, without full-period averaging.
-/

open Finset RHTower
open scoped BigOperators
namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-- The literal scaled primitive distance at one pronic atom. -/
def ramanujanScaledPrimitiveDistanceTerm (r p q n : ℕ) : ℝ :=
  ((p : ℝ) * (pmRamanujanPrimitive r (n / p)).re -
    (q : ℝ) * (pmRamanujanPrimitive r (n / q)).re) ^ 2 /
      ((n : ℝ) * ((n : ℝ) + 1))

private theorem first_cell_quotients {p h k n : ℕ} (hk : 0 < k)
    (hkh : k * h ≤ p) (hn : n ∈ Ico (k * p) (k * (p + h))) :
    n / p = k ∧ n / (p + h) = k - 1 := by
  have hnl := (mem_Ico.mp hn).1
  have hnu := (mem_Ico.mp hn).2
  have hnp : n < (k + 1) * p := by nlinarith
  have hpred : (k - 1) * (p + h) ≤ n := by
    have he : k - 1 + 1 = k := Nat.sub_add_cancel hk
    nlinarith
  have hpredU : n < (k - 1 + 1) * (p + h) := by
    simpa only [Nat.sub_add_cancel hk] using hnu
  exact ⟨Nat.div_eq_of_lt_le hnl hnp, Nat.div_eq_of_lt_le hpred hpredU⟩

private theorem second_cell_quotients {p h k n : ℕ}
    (hn : n ∈ Ico (k * (p + h)) ((k + 1) * p)) :
    n / p = k ∧ n / (p + h) = k := by
  have hnl := (mem_Ico.mp hn).1
  have hnu := (mem_Ico.mp hn).2
  exact ⟨Nat.div_eq_of_lt_le (by nlinarith) hnu,
    Nat.div_eq_of_lt_le hnl (by nlinarith)⟩

private theorem actual_distance_block (r : ℕ) {p h k : ℕ}
    (hp : 0 < p) (hk : 0 < k) (hkh : k * h ≤ p) :
    (∑ n ∈ Ico (k * p) ((k + 1) * p),
      ramanujanScaledPrimitiveDistanceTerm r p (p + h) n) =
      (h : ℝ) * (d4BMRamanujanNaturalCoefficient k r).re ^ 2 / k +
        (h : ℝ) ^ 2 / p *
          ((pmRamanujanPrimitive r (k - 1)).re ^ 2 / k -
            (pmRamanujanPrimitive r k).re ^ 2 / ((k : ℝ) + 1)) := by
  have hleft : k * p ≤ k * (p + h) := by nlinarith
  have hright : k * (p + h) ≤ (k + 1) * p := by nlinarith
  rw [← sum_Ico_consecutive _ hleft hright]
  have hfirst : (∑ n ∈ Ico (k * p) (k * (p + h)),
      ramanujanScaledPrimitiveDistanceTerm r p (p + h) n) =
      ((p : ℝ) * (pmRamanujanPrimitive r k).re -
        ((p : ℝ) + h) * (pmRamanujanPrimitive r (k - 1)).re) ^ 2 *
        (1 / ((k : ℝ) * p) - 1 / ((k : ℝ) * ((p : ℝ) + h))) := by
    calc
      _ = ∑ n ∈ Ico (k * p) (k * (p + h)),
          ((p : ℝ) * (pmRamanujanPrimitive r k).re -
            ((p : ℝ) + h) * (pmRamanujanPrimitive r (k - 1)).re) ^ 2 *
            (1 / ((n : ℝ) * ((n : ℝ) + 1))) := by
        apply sum_congr rfl
        intro n hn
        obtain ⟨hdivp, hdivq⟩ := first_cell_quotients hk hkh hn
        rw [ramanujanScaledPrimitiveDistanceTerm, hdivp, hdivq]
        push_cast
        ring
      _ = _ := by
        rw [← mul_sum, sum_Ico_reciprocal_pronic (Nat.mul_pos hk hp) hleft]
        push_cast
        rfl
  have hsecond : (∑ n ∈ Ico (k * (p + h)) ((k + 1) * p),
      ramanujanScaledPrimitiveDistanceTerm r p (p + h) n) =
      ((h : ℝ) * (pmRamanujanPrimitive r k).re) ^ 2 *
        (1 / ((k : ℝ) * ((p : ℝ) + h)) - 1 / (((k : ℝ) + 1) * p)) := by
    calc
      _ = ∑ n ∈ Ico (k * (p + h)) ((k + 1) * p),
          ((h : ℝ) * (pmRamanujanPrimitive r k).re) ^ 2 *
            (1 / ((n : ℝ) * ((n : ℝ) + 1))) := by
        apply sum_congr rfl
        intro n hn
        obtain ⟨hdivp, hdivq⟩ := second_cell_quotients hn
        rw [ramanujanScaledPrimitiveDistanceTerm, hdivp, hdivq]
        push_cast
        ring
      _ = _ := by
        rw [← mul_sum, sum_Ico_reciprocal_pronic
          (Nat.mul_pos hk (by omega : 0 < p + h)) hright]
        push_cast
        rfl
  rw [hfirst, hsecond]
  have hs := congrArg Complex.re (pmRamanujanPrimitive_succ r (k - 1))
  simp only [Nat.sub_add_cancel hk, Complex.add_re] at hs
  rw [hs]
  have hpR : (p : ℝ) ≠ 0 := by positivity
  have hkR : (k : ℝ) ≠ 0 := by positivity
  have hqR : (p : ℝ) + h ≠ 0 := by positivity
  field_simp
  ring

private theorem actual_distance_prefix (r : ℕ) {p h : ℕ} (hp : 0 < p)
    (K : ℕ) (hK : K * h ≤ p) :
    (∑ n ∈ range ((K + 1) * p), ramanujanScaledPrimitiveDistanceTerm r p (p + h) n) =
      (h : ℝ) * (∑ k ∈ Icc 1 K, (d4BMRamanujanNaturalCoefficient k r).re ^ 2 / k) -
        (h : ℝ) ^ 2 / p * (pmRamanujanPrimitive r K).re ^ 2 / ((K : ℝ) + 1) := by
  induction K with
  | zero =>
    simp only [zero_add, one_mul, Icc_eq_empty_of_lt (by omega : 0 < 1),
      sum_empty, mul_zero, pmRamanujanPrimitive, Complex.zero_re, zero_pow (by omega : 2 ≠ 0),
      zero_div, sub_zero]
    apply sum_eq_zero
    intro n hn
    have hnp := mem_range.mp hn
    have hnq : n < p + h := by omega
    simp [ramanujanScaledPrimitiveDistanceTerm, Nat.div_eq_of_lt hnp,
      Nat.div_eq_of_lt hnq, pmRamanujanPrimitive]
  | succ K ih =>
    have hK' : K * h ≤ p := by nlinarith
    have hcut : (K + 1) * p ≤ (K + 1 + 1) * p := by nlinarith
    rw [← sum_range_add_sum_Ico _ hcut, ih hK',
      actual_distance_block r hp (by omega : 0 < K + 1) hK,
      sum_Icc_succ_top (by omega : 1 ≤ K + 1)]
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    ring

/-- Exact distance energy up to any requested quotient depth before overlap begins. -/
theorem ramanujanDilationDistance_prefix_eq (r K : ℕ) (p h : ℕ+) :
    let T := min K ((p : ℕ) / h)
    (∑ n ∈ range ((T + 1) * p), ramanujanScaledPrimitiveDistanceTerm r p (p + h) n) =
      (h : ℝ) * (∑ k ∈ Icc 1 T, (d4BMRamanujanNaturalCoefficient k r).re ^ 2 / k) -
        (h : ℝ) ^ 2 / p * (pmRamanujanPrimitive r T).re ^ 2 / ((T : ℝ) + 1) := by
  apply actual_distance_prefix r p.pos
  exact (Nat.mul_le_mul_right (h : ℕ) (min_le_right K _)).trans
    (Nat.div_mul_le_self (p : ℕ) h)

/-- The exact finite-prefix jump energy bounds the full original profile distance from below. -/
theorem ramanujanDilationProfile_ge_jump_energy (r K : ℕ) (p h : ℕ+) :
    let T := min K ((p : ℕ) / h)
    (h : ℝ) * (∑ k ∈ Icc 1 T, (d4BMRamanujanNaturalCoefficient k (r + 2)).re ^ 2 / k) -
        (h : ℝ) ^ 2 / p * (pmRamanujanPrimitive (r + 2) T).re ^ 2 / ((T : ℝ) + 1) ≤
      ((p : ℝ) + ((p : ℝ) + h)) * pmRamanujanPrimitiveGram (r + 2) (r + 2) -
        2 * Real.sqrt p * Real.sqrt ((p : ℝ) + h) *
          pmRamanujanDilationProfile (r + 2) (by omega) ((p : ℝ) / ((p : ℝ) + h)) := by
  dsimp only
  rw [← ramanujanDilationDistance_prefix_eq (r + 2) K p h]
  have hs := hasSum_scaled_pmRamanujanPrimitive_distance r p (p + h)
  have hb := hs.summable.sum_le_tsum
    (range ((min K ((p : ℕ) / h) + 1) * p))
    (fun n _ => div_nonneg (sq_nonneg _) (by positivity))
  rw [hs.tsum_eq] at hb
  simpa only [ramanujanScaledPrimitiveDistanceTerm, PNat.add_coe, Nat.cast_add] using hb

private theorem actual_distance_common_prefix (r K P p h : ℕ)
    (hP : 0 < P) (hPp : P ≤ p) (hupper : K * (p + h) ≤ (K + 1) * P) :
    (∑ n ∈ range ((K + 1) * P), ramanujanScaledPrimitiveDistanceTerm r p (p + h) n) =
      (h : ℝ) * (∑ k ∈ Icc 1 K, (d4BMRamanujanNaturalCoefficient k r).re ^ 2 / k) -
        (h : ℝ) ^ 2 / P * (pmRamanujanPrimitive r K).re ^ 2 / ((K : ℝ) + 1) := by
  have hp : 0 < p := hP.trans_le hPp
  have hKh : K * h ≤ p := by nlinarith [Nat.mul_le_mul_left K hPp]
  have hcut : (K + 1) * P ≤ (K + 1) * p := Nat.mul_le_mul_left _ hPp
  have hs := actual_distance_prefix r hp K hKh
  rw [← sum_range_add_sum_Ico _ hcut] at hs
  have ht : (∑ n ∈ Ico ((K + 1) * P) ((K + 1) * p),
      ramanujanScaledPrimitiveDistanceTerm r p (p + h) n) =
      (h : ℝ) ^ 2 * (pmRamanujanPrimitive r K).re ^ 2 *
        (1 / (((K : ℝ) + 1) * P) - 1 / (((K : ℝ) + 1) * p)) := by
    calc
      _ = ∑ n ∈ Ico ((K + 1) * P) ((K + 1) * p),
          ((h : ℝ) ^ 2 * (pmRamanujanPrimitive r K).re ^ 2) *
            (1 / ((n : ℝ) * ((n : ℝ) + 1))) := by
        apply sum_congr rfl
        intro n hn
        have hl := (mem_Ico.mp hn).1
        have hu := (mem_Ico.mp hn).2
        have hdivp : n / p = K := Nat.div_eq_of_lt_le (by nlinarith) hu
        have hdivq : n / (p + h) = K :=
          Nat.div_eq_of_lt_le (by omega) (by nlinarith)
        rw [ramanujanScaledPrimitiveDistanceTerm, hdivp, hdivq]
        push_cast
        ring
      _ = _ := by
        rw [← mul_sum, sum_Ico_reciprocal_pronic (by positivity) hcut]
        push_cast
        rfl
  rw [ht] at hs
  have hP0 : (P : ℝ) ≠ 0 := by positivity
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have he : (h : ℝ) ^ 2 / p * (pmRamanujanPrimitive r K).re ^ 2 / ((K : ℝ) + 1) +
      (h : ℝ) ^ 2 * (pmRamanujanPrimitive r K).re ^ 2 *
        (1 / (((K : ℝ) + 1) * P) - 1 / (((K : ℝ) + 1) * p)) =
      (h : ℝ) ^ 2 / P * (pmRamanujanPrimitive r K).re ^ 2 / ((K : ℝ) + 1) := by
    field_simp
    ring
  linarith

private def actual_gap (r p h n : ℕ) : ℝ :=
  (p : ℝ) * (pmRamanujanPrimitive r (n / p)).re -
    ((p + h : ℕ) : ℝ) * (pmRamanujanPrimitive r (n / (p + h))).re

private theorem ordered_gap_covariance (r K P p h g l : ℕ)
    (hP : 0 < P) (hPp : P ≤ p)
    (hupper : K * (p + h + g + l) ≤ (K + 1) * P) :
    (∑ n ∈ range ((K + 1) * P),
      actual_gap r p h n * actual_gap r (p + h + g) l n /
        ((n : ℝ) * ((n : ℝ) + 1))) =
      -(h : ℝ) * l / P * (pmRamanujanPrimitive r K).re ^ 2 / ((K : ℝ) + 1) := by
  have h₁ := actual_distance_common_prefix r K P p (h + g + l) hP hPp (by nlinarith)
  have h₂ := actual_distance_common_prefix r K P (p + h) g hP (by omega) (by nlinarith)
  have h₃ := actual_distance_common_prefix r K P p (h + g) hP hPp (by nlinarith)
  have h₄ := actual_distance_common_prefix r K P (p + h) (g + l) hP (by omega) (by nlinarith)
  have he : 2 * (∑ n ∈ range ((K + 1) * P),
      actual_gap r p h n * actual_gap r (p + h + g) l n /
        ((n : ℝ) * ((n : ℝ) + 1))) =
      (∑ n ∈ range ((K + 1) * P),
        ramanujanScaledPrimitiveDistanceTerm r p (p + (h + g + l)) n) +
      (∑ n ∈ range ((K + 1) * P),
        ramanujanScaledPrimitiveDistanceTerm r (p + h) (p + h + g) n) -
      (∑ n ∈ range ((K + 1) * P),
        ramanujanScaledPrimitiveDistanceTerm r p (p + (h + g)) n) -
      (∑ n ∈ range ((K + 1) * P),
        ramanujanScaledPrimitiveDistanceTerm r (p + h) (p + h + (g + l)) n) := by
    rw [mul_sum, ← sum_add_distrib, ← sum_sub_distrib, ← sum_sub_distrib]
    apply sum_congr rfl
    intro n _
    simp only [actual_gap, ramanujanScaledPrimitiveDistanceTerm, Nat.add_assoc]
    ring
  rw [h₁, h₂, h₃, h₄] at he
  push_cast at he
  linear_combination he / 2

private theorem chain_endpoint_bounds (K m offset : ℕ) (h : ℕ → ℕ)
    {i : ℕ} (hi : i ∈ range m) :
    pronicGapChainLower K m offset h 0 ≤ pronicGapChainLower K m offset h i ∧
    pronicGapChainLower K m offset h i + h i ≤
      pronicGapChainLower K m offset h 0 + ∑ j ∈ range m, h j := by
  have hs : (∑ j ∈ range (i + 1), h j) ≤ ∑ j ∈ range m, h j :=
    sum_le_sum_of_subset (range_mono (mem_range.mp hi))
  rw [Finset.sum_range_succ] at hs
  simp only [pronicGapChainLower, sum_range_zero, add_zero]
  omega

private theorem chain_endpoints_ordered (K m offset : ℕ) (h : ℕ → ℕ)
    {i j : ℕ} (hij : i < j) :
    pronicGapChainLower K m offset h i + h i ≤ pronicGapChainLower K m offset h j := by
  have hs : (∑ t ∈ range (i + 1), h t) ≤ ∑ t ∈ range j, h t :=
    sum_le_sum_of_subset (range_mono hij)
  rw [Finset.sum_range_succ] at hs
  simp only [pronicGapChainLower]
  omega

/-- The full signed gap-chain Gram is diagonal jump energy minus one endpoint product. -/
theorem ramanujanGapChainPacket_bilinear_prefix_eq (r K m offset : ℕ)
    (h : ℕ → ℕ) (a b : ℕ → ℝ) :
    let P := pronicGapChainLower K m offset h 0
    (∑ n ∈ range ((K + 1) * P),
      ramanujanGapChainPacket r K m offset h a n * ramanujanGapChainPacket r K m offset h b n /
        ((n : ℝ) * ((n : ℝ) + 1))) =
      (∑ i ∈ range m, a i * b i * (h i : ℝ)) *
        (∑ k ∈ Icc 1 K, (d4BMRamanujanNaturalCoefficient k (r + 2)).re ^ 2 / k) -
      (∑ i ∈ range m, a i * (h i : ℝ)) * (∑ i ∈ range m, b i * (h i : ℝ)) / P *
        (pmRamanujanPrimitive (r + 2) K).re ^ 2 / ((K : ℝ) + 1) := by
  classical
  let P := pronicGapChainLower K m offset h 0
  let p (i : ℕ) := pronicGapChainLower K m offset h i
  let J := ∑ k ∈ Icc 1 K, (d4BMRamanujanNaturalCoefficient k (r + 2)).re ^ 2 / k
  let E := (pmRamanujanPrimitive (r + 2) K).re ^ 2 / ((K : ℝ) + 1)
  let C (i j : ℕ) := ∑ n ∈ range ((K + 1) * P),
    actual_gap (r + 2) (p i) (h i) n * actual_gap (r + 2) (p j) (h j) n /
      ((n : ℝ) * ((n : ℝ) + 1))
  have hP : 0 < P := by simp only [P, pronicGapChainLower]; positivity
  have hcluster : K * (P + ∑ j ∈ range m, h j) ≤ (K + 1) * P := by
    dsimp only [P, pronicGapChainLower]
    simp only [sum_range_zero, add_zero]
    nlinarith
  have hb (i : ℕ) (hi : i ∈ range m) :
      P ≤ p i ∧ K * (p i + h i) ≤ (K + 1) * P := by
    have hi' := chain_endpoint_bounds K m offset h hi
    exact ⟨hi'.1, (Nat.mul_le_mul_left K hi'.2).trans hcluster⟩
  have hd (i : ℕ) (hi : i ∈ range m) :
      C i i = (h i : ℝ) * J - (h i : ℝ) ^ 2 / P * E := by
    have hd := actual_distance_common_prefix (r + 2) K P (p i) (h i) hP
      (hb i hi).1 (hb i hi).2
    simpa only [C, actual_gap, ramanujanScaledPrimitiveDistanceTerm, J, E,
      pow_two, div_mul_eq_mul_div, mul_div_assoc] using hd
  have ho (i : ℕ) (hi : i ∈ range m) (j : ℕ) (hj : j ∈ range m)
      (hij : i < j) : C i j = -(h i : ℝ) * h j / P * E := by
    have horder : p i + h i ≤ p j := chain_endpoints_ordered K m offset h hij
    let g := p j - (p i + h i)
    have hg : p i + h i + g = p j := by dsimp only [g]; omega
    have hc := ordered_gap_covariance (r + 2) K P (p i) (h i) g (h j)
      hP (hb i hi).1 (by rw [hg]; exact (hb j hj).2)
    rw [hg] at hc
    simpa only [C, E, mul_div_assoc] using hc
  have hc (i : ℕ) (hi : i ∈ range m) (j : ℕ) (hj : j ∈ range m) :
      C i j = (if i = j then (h i : ℝ) * J else 0) -
        (h i : ℝ) * h j / P * E := by
    rcases lt_trichotomy i j with hij | hij | hij
    · rw [if_neg (ne_of_lt hij), ho i hi j hj hij]
      ring
    · subst j
      rw [if_pos rfl, hd i hi]
      ring
    · have hsymm : C i j = C j i := by
        apply sum_congr rfl
        intro n _
        ring
      rw [if_neg (ne_of_gt hij), hsymm, ho j hj i hi hij]
      ring
  have hexpand : (∑ n ∈ range ((K + 1) * P),
      ramanujanGapChainPacket r K m offset h a n * ramanujanGapChainPacket r K m offset h b n /
        ((n : ℝ) * ((n : ℝ) + 1))) =
      ∑ i ∈ range m, ∑ j ∈ range m, a i * b j * C i j := by
    calc
      _ = ∑ n ∈ range ((K + 1) * P), ∑ i ∈ range m, ∑ j ∈ range m,
          a i * b j * (actual_gap (r + 2) (p i) (h i) n *
            actual_gap (r + 2) (p j) (h j) n / ((n : ℝ) * ((n : ℝ) + 1))) := by
        apply sum_congr rfl
        intro n _
        simp only [ramanujanGapChainPacket, sum_mul_sum, sum_div]
        apply sum_congr rfl
        intro i _
        apply sum_congr rfl
        intro j _
        simp only [actual_gap, p]
        ring
      _ = _ := by
        rw [sum_comm]
        apply sum_congr rfl
        intro i _
        rw [sum_comm]
        apply sum_congr rfl
        intro j _
        rw [← mul_sum]
  have hrewrite : (∑ i ∈ range m, ∑ j ∈ range m, a i * b j * C i j) =
      (∑ i ∈ range m, ∑ j ∈ range m,
        a i * b j * (if i = j then (h i : ℝ) * J else 0)) -
      (∑ i ∈ range m, ∑ j ∈ range m,
        a i * b j * ((h i : ℝ) * h j / P * E)) := by
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro i hi
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro j hj
    rw [hc i hi j hj]
    ring
  have hdiag : (∑ i ∈ range m, ∑ j ∈ range m,
      a i * b j * (if i = j then (h i : ℝ) * J else 0)) =
      (∑ i ∈ range m, a i * b i * (h i : ℝ)) * J := by
    rw [sum_mul]
    apply sum_congr rfl
    intro i hi
    rw [sum_eq_single i]
    · rw [if_pos rfl]
      ring
    · intro j _ hji
      rw [if_neg (Ne.symm hji), mul_zero]
    · intro hnot
      exact False.elim (hnot hi)
  have hboundary : (∑ i ∈ range m, ∑ j ∈ range m,
      a i * b j * ((h i : ℝ) * h j / P * E)) =
      (∑ i ∈ range m, a i * (h i : ℝ)) * (∑ i ∈ range m, b i * (h i : ℝ)) / P * E := by
    rw [Finset.sum_mul_sum]
    simp only [sum_mul, sum_div]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    ring
  change _ = (∑ i ∈ range m, a i * b i * (h i : ℝ)) * J -
    (∑ i ∈ range m, a i * (h i : ℝ)) * (∑ i ∈ range m, b i * (h i : ℝ)) / P *
      (pmRamanujanPrimitive (r + 2) K).re ^ 2 / ((K : ℝ) + 1)
  rw [hexpand, hrewrite, hdiag, hboundary]
  simp only [E, mul_div_assoc]

/-- The exact packet energy retains all signs in one nonnegative boundary correction. -/
theorem ramanujanGapChainPacket_prefix_energy_eq (r K m offset : ℕ)
    (h : ℕ → ℕ) (a : ℕ → ℝ) :
    let P := pronicGapChainLower K m offset h 0
    (∑ n ∈ range ((K + 1) * P),
      (ramanujanGapChainPacket r K m offset h a n) ^ 2 /
        ((n : ℝ) * ((n : ℝ) + 1))) =
      (∑ i ∈ range m, (a i) ^ 2 * (h i : ℝ)) *
        (∑ k ∈ Icc 1 K, (d4BMRamanujanNaturalCoefficient k (r + 2)).re ^ 2 / k) -
      (∑ i ∈ range m, a i * (h i : ℝ)) ^ 2 / P *
        (pmRamanujanPrimitive (r + 2) K).re ^ 2 / ((K : ℝ) + 1) := by
  simpa only [pow_two] using ramanujanGapChainPacket_bilinear_prefix_eq r K m offset h a a

/-- The literal harmonic jump energy controls every signed chain without a cofactor cost. -/
theorem ramanujanGapChainPacket_prefix_energy_le_jump_squares (r K m offset : ℕ)
    (h : ℕ → ℕ) (a : ℕ → ℝ) :
    let P := pronicGapChainLower K m offset h 0
    (∑ n ∈ range ((K + 1) * P),
      (ramanujanGapChainPacket r K m offset h a n) ^ 2 /
        ((n : ℝ) * ((n : ℝ) + 1))) ≤
      (∑ i ∈ range m, (a i) ^ 2 * (h i : ℝ)) *
        (∑ k ∈ Icc 1 K, (d4BMRamanujanNaturalCoefficient k (r + 2)).re ^ 2 / k) := by
  dsimp only
  rw [ramanujanGapChainPacket_prefix_energy_eq]
  exact sub_le_self _ (by positivity)

private theorem primitive_mul_reset {r : ℕ} (hr : 1 < r) (t : ℕ) :
    pmRamanujanPrimitive r (r * t) = 0 := by
  induction t with
  | zero => simp [pmRamanujanPrimitive]
  | succ t ih => rw [Nat.mul_succ, pmRamanujanPrimitive_periodic hr, ih]

/-- At a primitive reset the short-prefix signed-chain Gram is exactly diagonal. -/
theorem ramanujanGapChainPacket_period_reset_bilinear_eq (r t m offset : ℕ)
    (h : ℕ → ℕ) (a b : ℕ → ℝ) :
    let K := (r + 2) * t
    let P := pronicGapChainLower K m offset h 0
    (∑ n ∈ range ((K + 1) * P),
      ramanujanGapChainPacket r K m offset h a n * ramanujanGapChainPacket r K m offset h b n /
        ((n : ℝ) * ((n : ℝ) + 1))) =
      (∑ i ∈ range m, a i * b i * (h i : ℝ)) *
        (∑ k ∈ Icc 1 K, (d4BMRamanujanNaturalCoefficient k (r + 2)).re ^ 2 / k) := by
  dsimp only
  rw [ramanujanGapChainPacket_bilinear_prefix_eq, primitive_mul_reset (by omega)]
  simp

private theorem primitive_jump_energy_pos (r t : ℕ) :
    0 < ∑ k ∈ Icc 1 ((r + 2) * (t + 1)),
      (d4BMRamanujanNaturalCoefficient k (r + 2)).re ^ 2 / k := by
  have hmem : r + 2 ∈ Icc 1 ((r + 2) * (t + 1)) := by
    rw [mem_Icc]
    constructor <;> nlinarith
  have hs := single_le_sum
    (fun k (_ : k ∈ Icc 1 ((r + 2) * (t + 1))) =>
      div_nonneg (sq_nonneg (d4BMRamanujanNaturalCoefficient k (r + 2)).re)
        (Nat.cast_nonneg k)) hmem
  apply lt_of_lt_of_le _ hs
  rw [ramanujanNaturalCoefficient_re_eq_lagCoefficient,
    ramanujanLagCoefficient_of_dvd (dvd_refl _)]
  have hphi : 0 < (r + 2).totient := Nat.totient_pos.mpr (by omega)
  positivity

/-- One finite-prefix inner product recovers each signed gap coefficient at a primitive reset. -/
theorem ramanujanGapChainPacket_period_reset_coefficient_readout
    (r t m offset : ℕ) (h : ℕ → ℕ+) (a : ℕ → ℝ) (j : Fin m) :
    let K := (r + 2) * (t + 1)
    let hn : ℕ → ℕ := fun i => h i
    let P := pronicGapChainLower K m offset hn 0
    let p := pronicGapChainLower K m offset hn j
    (∑ n ∈ range ((K + 1) * P),
      ramanujanGapChainPacket r K m offset hn a n *
        ((p : ℝ) * (pmRamanujanPrimitive (r + 2) (n / p)).re -
          ((p + hn j : ℕ) : ℝ) * (pmRamanujanPrimitive (r + 2) (n / (p + hn j))).re) /
        ((n : ℝ) * ((n : ℝ) + 1))) /
      ((h j : ℝ) * (∑ k ∈ Icc 1 K,
        (d4BMRamanujanNaturalCoefficient k (r + 2)).re ^ 2 / k)) = a j := by
  classical
  let K := (r + 2) * (t + 1)
  let hn : ℕ → ℕ := fun i => h i
  let P := pronicGapChainLower K m offset hn 0
  let p := pronicGapChainLower K m offset hn j
  let b : ℕ → ℝ := fun i => if i = (j : ℕ) then 1 else 0
  let J := ∑ k ∈ Icc 1 K, (d4BMRamanujanNaturalCoefficient k (r + 2)).re ^ 2 / k
  have hj : (j : ℕ) ∈ range m := mem_range.mpr j.isLt
  have hb (n : ℕ) : ramanujanGapChainPacket r K m offset hn b n =
      actual_gap (r + 2) p (hn j) n := by
    unfold ramanujanGapChainPacket
    rw [sum_eq_single (j : ℕ)]
    · simp only [b, if_pos rfl, one_mul, actual_gap, p]
    · intro i _ hij
      simp only [b, if_neg hij, zero_mul]
    · intro hnot
      exact False.elim (hnot hj)
  have hd : (∑ i ∈ range m, a i * b i * (hn i : ℝ)) = a j * (h j : ℝ) := by
    rw [sum_eq_single (j : ℕ)]
    · simp only [b, if_pos rfl, mul_one, hn]
    · intro i _ hij
      simp only [b, if_neg hij, mul_zero, zero_mul]
    · intro hnot
      exact False.elim (hnot hj)
  have he := ramanujanGapChainPacket_period_reset_bilinear_eq r (t + 1) m offset hn a b
  change (∑ n ∈ range ((K + 1) * P),
      ramanujanGapChainPacket r K m offset hn a n *
        ramanujanGapChainPacket r K m offset hn b n /
          ((n : ℝ) * ((n : ℝ) + 1))) = _ at he
  simp only [hb, hd] at he
  change (∑ n ∈ range ((K + 1) * P),
      ramanujanGapChainPacket r K m offset hn a n * actual_gap (r + 2) p (hn j) n /
        ((n : ℝ) * ((n : ℝ) + 1))) / ((h j : ℝ) * J) = a j
  rw [he]
  have hJ : 0 < J := primitive_jump_energy_pos r t
  have hh : 0 < (h j : ℝ) := by exact_mod_cast (h j).pos
  apply (div_eq_iff (ne_of_gt (mul_pos hh hJ))).mpr
  ring

private theorem primitive_boundary_le_jump_energy (r K : ℕ) :
    (pmRamanujanPrimitive r K).re ^ 2 ≤
      (∑ k ∈ Icc 1 K, (d4BMRamanujanNaturalCoefficient k r).re ^ 2 / k) *
        K * ((K : ℝ) + 1) / 2 := by
  have hs : (∑ k ∈ Icc 1 K, (k : ℝ)) = (K : ℝ) * ((K : ℝ) + 1) / 2 := by
    induction K with
    | zero => simp
    | succ K ih =>
      rw [sum_Icc_succ_top (by omega : 1 ≤ K + 1), ih]
      push_cast
      ring
  have hc := sum_sq_le_sum_mul_sum_of_sq_le_mul (Icc 1 K)
    (r := fun k => (d4BMRamanujanNaturalCoefficient k r).re)
    (f := fun k => (d4BMRamanujanNaturalCoefficient k r).re ^ 2 / (k : ℝ))
    (g := fun k => (k : ℝ))
    (fun k _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg k))
    (fun k _ => Nat.cast_nonneg k) (fun k hk => by
      have hk0 : (k : ℝ) ≠ 0 := by
        have hkpos := (mem_Icc.mp hk).1
        positivity
      rw [div_mul_cancel₀ _ hk0])
  rw [hs] at hc
  simpa only [pmRamanujanPrimitive, Complex.re_sum, mul_div_assoc, mul_assoc] using hc

/-- Every signed gap chain keeps at least half its intrinsic harmonic jump energy. -/
theorem ramanujanGapChainPacket_prefix_energy_sandwich (r K m offset : ℕ)
    (h : ℕ → ℕ) (a : ℕ → ℝ) :
    let P := pronicGapChainLower K m offset h 0
    let W := (∑ i ∈ range m, (a i) ^ 2 * (h i : ℝ)) *
      (∑ k ∈ Icc 1 K, (d4BMRamanujanNaturalCoefficient k (r + 2)).re ^ 2 / k)
    W / 2 ≤ (∑ n ∈ range ((K + 1) * P),
      (ramanujanGapChainPacket r K m offset h a n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) ∧
    (∑ n ∈ range ((K + 1) * P),
      (ramanujanGapChainPacket r K m offset h a n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) ≤ W := by
  let P := pronicGapChainLower K m offset h 0
  let H : ℝ := ∑ i ∈ range m, (h i : ℝ)
  let V := ∑ i ∈ range m, (a i) ^ 2 * (h i : ℝ)
  let J := ∑ k ∈ Icc 1 K, (d4BMRamanujanNaturalCoefficient k (r + 2)).re ^ 2 / k
  let B := ∑ i ∈ range m, a i * (h i : ℝ)
  let A := (pmRamanujanPrimitive (r + 2) K).re
  have hP : 0 < (P : ℝ) := by dsimp only [P, pronicGapChainLower]; positivity
  have hH : 0 ≤ H := sum_nonneg fun i _ => Nat.cast_nonneg (h i)
  have hV : 0 ≤ V :=
    sum_nonneg fun i _ => mul_nonneg (sq_nonneg (a i)) (Nat.cast_nonneg (h i))
  have hJ : 0 ≤ J := sum_nonneg fun k _ =>
    div_nonneg (sq_nonneg (d4BMRamanujanNaturalCoefficient k (r + 2)).re) (Nat.cast_nonneg k)
  have hpform : (P : ℝ) = (K : ℝ) * H + offset + 1 := by
    simp [P, pronicGapChainLower, H]
  have hKP : (K : ℝ) * H ≤ P := by
    rw [hpform]
    have ho : 0 ≤ (offset : ℝ) := Nat.cast_nonneg offset
    linarith
  have hB : B ^ 2 ≤ H * V :=
    sum_sq_le_sum_mul_sum_of_sq_le_mul (range m)
      (fun i _ => Nat.cast_nonneg (h i))
      (fun i _ => mul_nonneg (sq_nonneg (a i)) (Nat.cast_nonneg (h i)))
      (fun i _ => le_of_eq (by ring))
  have hA : A ^ 2 ≤ J * K * ((K : ℝ) + 1) / 2 :=
    primitive_boundary_le_jump_energy (r + 2) K
  have hb : B ^ 2 / P * A ^ 2 / ((K : ℝ) + 1) ≤ V * J / 2 := by
    calc
      _ = (B ^ 2 * A ^ 2) / ((P : ℝ) * ((K : ℝ) + 1)) := by field_simp
      _ ≤ (H * V * (J * K * ((K : ℝ) + 1) / 2)) /
          ((P : ℝ) * ((K : ℝ) + 1)) :=
        div_le_div_of_nonneg_right
          (mul_le_mul hB hA (sq_nonneg A) (mul_nonneg hH hV)) (by positivity)
      _ = ((K : ℝ) * H / P) * (V * J) / 2 := by
        field_simp
      _ ≤ V * J / 2 := by
        have hr : (K : ℝ) * H / P ≤ 1 := (div_le_one hP).mpr hKP
        nlinarith [mul_le_mul_of_nonneg_right hr (mul_nonneg hV hJ)]
  constructor
  · rw [ramanujanGapChainPacket_prefix_energy_eq]
    change V * J / 2 ≤ V * J - B ^ 2 / P * A ^ 2 / ((K : ℝ) + 1)
    linarith
  · exact ramanujanGapChainPacket_prefix_energy_le_jump_squares r K m offset h a

private theorem jump_energy_zero_iff_clock (r K : ℕ) :
    (∑ k ∈ Icc 1 K, (d4BMRamanujanNaturalCoefficient k (r + 2)).re ^ 2 / k) = 0 ↔
      K < lagVisibilityClock (r + 2) := by
  have hC : 0 < lagVisibilityClock (r + 2) := Nat.pos_of_ne_zero
    (fun hz => by have := (lagVisibilityClock_eq_zero_iff (r + 2)).mp hz; omega)
  constructor
  · intro hz
    by_contra hnot
    have hmem : lagVisibilityClock (r + 2) ∈ Icc 1 K := mem_Icc.mpr ⟨hC, by omega⟩
    have hc := (ramanujanNaturalCoefficient_re_ne_zero_iff_clock
      (r + 2) (lagVisibilityClock (r + 2))).mpr ⟨by omega, dvd_refl _⟩
    have hp : 0 < (d4BMRamanujanNaturalCoefficient (lagVisibilityClock (r + 2))
        (r + 2)).re ^ 2 / (lagVisibilityClock (r + 2) : ℝ) :=
      div_pos (sq_pos_of_ne_zero hc) (by exact_mod_cast hC)
    have hs := single_le_sum
      (fun k (_ : k ∈ Icc 1 K) =>
        div_nonneg (sq_nonneg (d4BMRamanujanNaturalCoefficient k (r + 2)).re)
          (Nat.cast_nonneg k)) hmem
    rw [hz] at hs
    linarith
  · intro hK
    apply sum_eq_zero
    intro k hk
    have hc : (d4BMRamanujanNaturalCoefficient k (r + 2)).re = 0 := by
      by_contra hne
      have hd := ((ramanujanNaturalCoefficient_re_ne_zero_iff_clock (r + 2) k).mp hne).2
      have hle := Nat.le_of_dvd (mem_Icc.mp hk).1 hd
      have hkK := (mem_Icc.mp hk).2
      omega
    simp only [hc, zero_pow (by omega : 2 ≠ 0), zero_div]

/-- The valuation clock is the exact visibility boundary for every signed physical gap chain. -/
theorem ramanujanGapChainPacket_prefix_energy_zero_iff_clock (r K m offset : ℕ)
    (h : ℕ → ℕ) (a : ℕ → ℝ) :
    let P := pronicGapChainLower K m offset h 0
    (∑ n ∈ range ((K + 1) * P),
      (ramanujanGapChainPacket r K m offset h a n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) = 0 ↔
      K < lagVisibilityClock (r + 2) ∨ ∀ i ∈ range m, a i = 0 ∨ h i = 0 := by
  let P := pronicGapChainLower K m offset h 0
  let V := ∑ i ∈ range m, (a i) ^ 2 * (h i : ℝ)
  let J := ∑ k ∈ Icc 1 K, (d4BMRamanujanNaturalCoefficient k (r + 2)).re ^ 2 / k
  let E := ∑ n ∈ range ((K + 1) * P),
    (ramanujanGapChainPacket r K m offset h a n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))
  have hV : 0 ≤ V :=
    sum_nonneg fun i _ => mul_nonneg (sq_nonneg (a i)) (Nat.cast_nonneg (h i))
  have hJ : 0 ≤ J := sum_nonneg fun k _ =>
    div_nonneg (sq_nonneg (d4BMRamanujanNaturalCoefficient k (r + 2)).re) (Nat.cast_nonneg k)
  have hE : 0 ≤ E := sum_nonneg fun n _ =>
    div_nonneg (sq_nonneg (ramanujanGapChainPacket r K m offset h a n)) (by positivity)
  have hs : V * J / 2 ≤ E ∧ E ≤ V * J :=
    ramanujanGapChainPacket_prefix_energy_sandwich r K m offset h a
  have he : E = 0 ↔ V * J = 0 := by
    constructor
    · intro hz
      have hl := hs.1
      rw [hz] at hl
      nlinarith [mul_nonneg hV hJ]
    · intro hz
      have hu := hs.2
      rw [hz] at hu
      exact le_antisymm hu hE
  have hv : V = 0 ↔ ∀ i ∈ range m, a i = 0 ∨ h i = 0 := by
    dsimp only [V]
    rw [sum_eq_zero_iff_of_nonneg (fun i _ => mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _))]
    simp only [mul_eq_zero, pow_eq_zero_iff (by omega : 2 ≠ 0), Nat.cast_eq_zero]
  change E = 0 ↔ _
  rw [he, mul_eq_zero, hv, jump_energy_zero_iff_clock, or_comm]

end
end GaloisForLFunctions.BezoutValuationIncidence
