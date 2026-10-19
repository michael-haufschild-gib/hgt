import GaloisForLFunctions.BezoutValuationIncidence.RamanujanGapChainExactPrefixGram
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusRamanujanMoment

/-!
# Conditional-tail completion of the exact gap-chain Gram

The finite head mean determines a constant in the tail. Its forced energy
cancels the endpoint correction in the exact head Gram, leaving the intrinsic
harmonic jump energy and one nonnegative centered-tail remainder.
-/

open Finset RHTower
open scoped BigOperators
namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

private theorem scaled_primitive_block_sum (r p K : ℕ) (hp : 0 < p) :
    (∑ n ∈ range ((K + 1) * p),
      (p : ℝ) * (pmRamanujanPrimitive r (n / p)).re / ((n : ℝ) * ((n : ℝ) + 1))) =
      ∑ k ∈ Icc 1 K, (pmRamanujanPrimitive r k).re / ((k : ℝ) * ((k : ℝ) + 1)) := by
  induction K with
  | zero =>
    simp only [zero_add, one_mul, Icc_eq_empty_of_lt (by omega : 0 < 1), sum_empty]
    apply sum_eq_zero
    intro n hn
    simp [Nat.div_eq_of_lt (mem_range.mp hn), pmRamanujanPrimitive]
  | succ K ih =>
    have hcut : (K + 1) * p ≤ (K + 1 + 1) * p := by nlinarith
    rw [← sum_range_add_sum_Ico _ hcut, ih,
      sum_Icc_succ_top (by omega : 1 ≤ K + 1)]
    congr 1
    calc
      _ = (p : ℝ) * (pmRamanujanPrimitive r (K + 1)).re *
          (∑ n ∈ Ico ((K + 1) * p) ((K + 1 + 1) * p),
            1 / ((n : ℝ) * ((n : ℝ) + 1))) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro n hn
        rw [Nat.div_eq_of_lt_le (mem_Ico.mp hn).1 (mem_Ico.mp hn).2]
        ring
      _ = _ := by
        rw [sum_Ico_reciprocal_pronic (by positivity) hcut]
        push_cast
        have hp0 : (p : ℝ) ≠ 0 := by positivity
        field_simp
        ring

private theorem scaled_primitive_common_prefix_mean (r K P p : ℕ)
    (hP : 0 < P) (hPp : P ≤ p) (hKp : K * p ≤ (K + 1) * P) :
    (∑ n ∈ range ((K + 1) * P),
      (p : ℝ) * (pmRamanujanPrimitive r (n / p)).re / ((n : ℝ) * ((n : ℝ) + 1))) =
      (∑ k ∈ Icc 1 K, (d4BMRamanujanNaturalCoefficient k r).re / k) -
        (p : ℝ) * (pmRamanujanPrimitive r K).re / (((K : ℝ) + 1) * P) := by
  have hp : 0 < p := hP.trans_le hPp
  have hcut := Nat.mul_le_mul_left (K + 1) hPp
  have hs := scaled_primitive_block_sum r p K hp
  rw [← sum_range_add_sum_Ico _ hcut, pmRamanujanPrimitive_reciprocal_partial] at hs
  have ht : (∑ n ∈ Ico ((K + 1) * P) ((K + 1) * p),
      (p : ℝ) * (pmRamanujanPrimitive r (n / p)).re / ((n : ℝ) * ((n : ℝ) + 1))) =
      (p : ℝ) * (pmRamanujanPrimitive r K).re *
        (1 / (((K : ℝ) + 1) * P) - 1 / (((K : ℝ) + 1) * p)) := by
    calc
      _ = (p : ℝ) * (pmRamanujanPrimitive r K).re *
          (∑ n ∈ Ico ((K + 1) * P) ((K + 1) * p),
            1 / ((n : ℝ) * ((n : ℝ) + 1))) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro n hn
        have hd : n / p = K :=
          Nat.div_eq_of_lt_le (hKp.trans (mem_Ico.mp hn).1) (mem_Ico.mp hn).2
        rw [hd]
        ring
      _ = _ := by
        rw [sum_Ico_reciprocal_pronic (by positivity) hcut]
        push_cast
        rfl
  rw [ht] at hs
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hP0 : (P : ℝ) ≠ 0 := by positivity
  have he : (pmRamanujanPrimitive r K).re / ((K : ℝ) + 1) +
      (p : ℝ) * (pmRamanujanPrimitive r K).re *
        (1 / (((K : ℝ) + 1) * P) - 1 / (((K : ℝ) + 1) * p)) =
      (p : ℝ) * (pmRamanujanPrimitive r K).re / (((K : ℝ) + 1) * P) := by
    field_simp
    ring
  linarith

/-- The actual packet's finite mean is exactly its primitive endpoint moment. -/
theorem ramanujanGapChainPacket_prefix_mean_eq (r K m offset : ℕ)
    (h : ℕ → ℕ) (a : ℕ → ℝ) :
    let P := pronicGapChainLower K m offset h 0
    (∑ n ∈ range ((K + 1) * P),
      ramanujanGapChainPacket r K m offset h a n / ((n : ℝ) * ((n : ℝ) + 1))) =
      (∑ i ∈ range m, a i * (h i : ℝ)) * (pmRamanujanPrimitive (r + 2) K).re /
        (((K : ℝ) + 1) * P) := by
  let P := pronicGapChainLower K m offset h 0
  let p (i : ℕ) := pronicGapChainLower K m offset h i
  have hP : 0 < P := by simp only [P, pronicGapChainLower]; positivity
  have hb (i : ℕ) (hi : i ∈ range m) :
      P ≤ p i ∧ K * (p i + h i) ≤ (K + 1) * P := by
    have hs : (∑ j ∈ range (i + 1), h j) ≤ ∑ j ∈ range m, h j :=
      sum_le_sum_of_subset (range_mono (mem_range.mp hi))
    rw [Finset.sum_range_succ] at hs
    dsimp only [P, p, pronicGapChainLower]
    simp only [sum_range_zero, add_zero]
    constructor
    · omega
    · nlinarith
  have hd (i : ℕ) (hi : i ∈ range m) :
      (∑ n ∈ range ((K + 1) * P),
        ((p i : ℝ) * (pmRamanujanPrimitive (r + 2) (n / p i)).re -
          ((p i + h i : ℕ) : ℝ) * (pmRamanujanPrimitive (r + 2) (n / (p i + h i))).re) /
            ((n : ℝ) * ((n : ℝ) + 1))) =
        (h i : ℝ) * (pmRamanujanPrimitive (r + 2) K).re / (((K : ℝ) + 1) * P) := by
    simp only [sub_div, sum_sub_distrib]
    rw [scaled_primitive_common_prefix_mean (r + 2) K P (p i) hP (hb i hi).1
        (by nlinarith [(hb i hi).2]),
      scaled_primitive_common_prefix_mean (r + 2) K P (p i + h i) hP
        (by have := (hb i hi).1; omega) (hb i hi).2]
    push_cast
    ring
  change (∑ n ∈ range ((K + 1) * P), _) = _
  simp only [ramanujanGapChainPacket, sum_div]
  rw [sum_comm]
  simp only [sum_mul, sum_div]
  apply sum_congr rfl
  intro i hi
  calc
    _ = a i * (∑ n ∈ range ((K + 1) * P),
        ((p i : ℝ) * (pmRamanujanPrimitive (r + 2) (n / p i)).re -
          ((p i + h i : ℕ) : ℝ) * (pmRamanujanPrimitive (r + 2) (n / (p i + h i))).re) /
            ((n : ℝ) * ((n : ℝ) + 1))) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro n _
      simp only [p]
      ring
    _ = _ := by rw [hd i hi]; ring

private theorem packet_energy_summable (r K m offset : ℕ) (h : ℕ → ℕ) (a : ℕ → ℝ) :
    Summable (fun n : ℕ => (ramanujanGapChainPacket r K m offset h a n) ^ 2 /
      ((n : ℝ) * ((n : ℝ) + 1))) := by
  let p (i : ℕ) := pronicGapChainLower K m offset h i
  let M := pmRamanujanPrimitiveBound (r + 2)
  let C := ∑ i ∈ range m, |a i| * (((p i : ℝ) + ((p i + h i : ℕ) : ℝ)) * M)
  have hb (d n : ℕ) : |(pmRamanujanPrimitive (r + 2) (n / d)).re| ≤ M :=
    (Complex.abs_re_le_norm _).trans (norm_pmRamanujanPrimitive_le (by omega) _)
  have hg (i n : ℕ) :
      |(p i : ℝ) * (pmRamanujanPrimitive (r + 2) (n / p i)).re -
        ((p i + h i : ℕ) : ℝ) * (pmRamanujanPrimitive (r + 2) (n / (p i + h i))).re| ≤
      ((p i : ℝ) + ((p i + h i : ℕ) : ℝ)) * M := by
    calc
      _ ≤ |(p i : ℝ) * (pmRamanujanPrimitive (r + 2) (n / p i)).re| +
          |((p i + h i : ℕ) : ℝ) *
            (pmRamanujanPrimitive (r + 2) (n / (p i + h i))).re| := abs_sub _ _
      _ = (p i : ℝ) * |(pmRamanujanPrimitive (r + 2) (n / p i)).re| +
          ((p i + h i : ℕ) : ℝ) *
            |(pmRamanujanPrimitive (r + 2) (n / (p i + h i))).re| := by
        rw [abs_mul, abs_mul,
          abs_of_nonneg (show (0 : ℝ) ≤ (p i : ℝ) from Nat.cast_nonneg _),
          abs_of_nonneg (show (0 : ℝ) ≤ ((p i + h i : ℕ) : ℝ) from Nat.cast_nonneg _)]
      _ ≤ (p i : ℝ) * M + ((p i + h i : ℕ) : ℝ) * M :=
        add_le_add (mul_le_mul_of_nonneg_left (hb (p i) n) (Nat.cast_nonneg _))
          (mul_le_mul_of_nonneg_left (hb (p i + h i) n) (Nat.cast_nonneg _))
      _ = _ := by ring
  have hF (n : ℕ) : |ramanujanGapChainPacket r K m offset h a n| ≤ C := by
    unfold ramanujanGapChainPacket
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro i _
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hg i n) (abs_nonneg (a i))
  have hs := summable_div_pronicSeq_of_bounded
    (g := fun n => (ramanujanGapChainPacket r K m offset h a n) ^ 2)
    (B := C ^ 2) (fun n => by
      rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hF n) 2)
  simpa only [cast_pronicSeq_eq] using hs

private theorem pronic_tail_hasSum (F : ℕ → ℝ) (N : ℕ)
    (hs : Summable (fun n : ℕ => F n / ((n : ℝ) * ((n : ℝ) + 1)))) :
    HasSum (fun n : ℕ => F (N + n) /
      (((N : ℝ) + n) * ((N : ℝ) + n + 1)))
      ((∑' n : ℕ, F n / ((n : ℝ) * ((n : ℝ) + 1))) -
        ∑ n ∈ range N, F n / ((n : ℝ) * ((n : ℝ) + 1))) := by
  have ht := hs.comp_injective (fun i j h => Nat.add_left_cancel h :
    Function.Injective (fun n : ℕ => N + n))
  have he := hs.sum_add_tsum_nat_add N
  have he' : (∑ n ∈ range N, F n / ((n : ℝ) * ((n : ℝ) + 1))) +
      (∑' n : ℕ, F (N + n) / (((N : ℝ) + n) * ((N : ℝ) + n + 1))) =
      ∑' n : ℕ, F n / ((n : ℝ) * ((n : ℝ) + 1)) := by
    simpa only [Nat.add_comm, Nat.cast_add, add_comm] using he
  have ht' : Summable (fun n : ℕ => F (N + n) /
      (((N : ℝ) + n) * ((N : ℝ) + n + 1))) := by
    simpa only [Function.comp_def, Nat.cast_add] using ht
  convert ht'.hasSum using 1
  linarith

private theorem pronic_conditional_tail_completion (F : ℕ → ℝ) (N : ℕ)
    (hN : 0 < N) (C W : ℝ)
    (hmean : HasSum (fun n : ℕ => F n / ((n : ℝ) * ((n : ℝ) + 1))) 0)
    (hsq : Summable (fun n : ℕ => (F n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))))
    (hheadmean : (∑ n ∈ range N, F n / ((n : ℝ) * ((n : ℝ) + 1))) = C / N)
    (hheadenergy : (∑ n ∈ range N, (F n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) =
      W - C ^ 2 / N) :
    (∑' n : ℕ, (F n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) = W +
      ∑' n : ℕ, (F (N + n) + C) ^ 2 / (((N : ℝ) + n) * ((N : ℝ) + n + 1)) := by
  have htm := pronic_tail_hasSum F N hmean.summable
  rw [hmean.tsum_eq, hheadmean] at htm
  have hte := pronic_tail_hasSum (fun n => (F n) ^ 2) N hsq
  rw [hheadenergy] at hte
  have hmass := GaloisForLFunctions.hasSum_one_div_shift_mul_succ
    (show 0 < (N : ℝ) by exact_mod_cast hN)
  have hs := (hte.add (htm.mul_left (2 * C))).add (hmass.mul_left (C ^ 2))
  have he : (∑' n : ℕ, (F n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) - (W - C ^ 2 / N) +
      2 * C * (0 - C / N) + C ^ 2 * (1 / (N : ℝ)) =
      (∑' n : ℕ, (F n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) - W := by ring
  rw [he] at hs
  have hr : HasSum (fun n : ℕ => (F (N + n) + C) ^ 2 /
      (((N : ℝ) + n) * ((N : ℝ) + n + 1)))
      ((∑' n : ℕ, (F n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) - W) :=
    hs.congr_fun fun n => by ring
  have hx := hr.tsum_eq
  linarith

/-- The forced tail mean cancels the head endpoint loss exactly. -/
theorem ramanujanGapChainPacket_energy_eq_jump_energy_add_conditional_tail
    (r K m offset : ℕ) (h : ℕ → ℕ) (a : ℕ → ℝ) :
    let P := pronicGapChainLower K m offset h 0
    let N := (K + 1) * P
    let C := (∑ i ∈ range m, a i * (h i : ℝ)) * (pmRamanujanPrimitive (r + 2) K).re
    (∑' n : ℕ, (ramanujanGapChainPacket r K m offset h a n) ^ 2 /
      ((n : ℝ) * ((n : ℝ) + 1))) =
      (∑ i ∈ range m, (a i) ^ 2 * (h i : ℝ)) *
        (∑ k ∈ Icc 1 K, (d4BMRamanujanNaturalCoefficient k (r + 2)).re ^ 2 / k) +
      ∑' n : ℕ, (ramanujanGapChainPacket r K m offset h a (N + n) + C) ^ 2 /
        (((N : ℝ) + n) * ((N : ℝ) + n + 1)) := by
  let P := pronicGapChainLower K m offset h 0
  let N := (K + 1) * P
  let B := ∑ i ∈ range m, a i * (h i : ℝ)
  let A := (pmRamanujanPrimitive (r + 2) K).re
  let W := (∑ i ∈ range m, (a i) ^ 2 * (h i : ℝ)) *
    (∑ k ∈ Icc 1 K, (d4BMRamanujanNaturalCoefficient k (r + 2)).re ^ 2 / k)
  have hP : 0 < P := by simp only [P, pronicGapChainLower]; positivity
  have hN : 0 < N := Nat.mul_pos (by omega) hP
  apply pronic_conditional_tail_completion (ramanujanGapChainPacket r K m offset h a)
    N hN (B * A) W (hasSum_ramanujanGapChainPacket_zero r K m offset h a)
    (packet_energy_summable r K m offset h a)
  · have hm := ramanujanGapChainPacket_prefix_mean_eq r K m offset h a
    simpa only [N, Nat.cast_mul, Nat.cast_add, Nat.cast_one] using hm
  · have he := ramanujanGapChainPacket_prefix_energy_eq r K m offset h a
    change (∑ n ∈ range N, _) = W - B ^ 2 / P * A ^ 2 / ((K : ℝ) + 1) at he
    rw [he]
    dsimp only [N]
    push_cast
    have hP0 : (P : ℝ) ≠ 0 := by positivity
    field_simp

/-- Every signed chain pays its full harmonic jump energy in the global actual norm. -/
theorem ramanujanGapChainPacket_jump_energy_le_energy (r K m offset : ℕ)
    (h : ℕ → ℕ) (a : ℕ → ℝ) :
    (∑ i ∈ range m, (a i) ^ 2 * (h i : ℝ)) *
      (∑ k ∈ Icc 1 K, (d4BMRamanujanNaturalCoefficient k (r + 2)).re ^ 2 / k) ≤
      ∑' n : ℕ, (ramanujanGapChainPacket r K m offset h a n) ^ 2 /
        ((n : ℝ) * ((n : ℝ) + 1)) := by
  rw [ramanujanGapChainPacket_energy_eq_jump_energy_add_conditional_tail]
  exact le_add_of_nonneg_right (tsum_nonneg fun n => div_nonneg (sq_nonneg _) (by positivity))

/-- The actual profile distance pays all pre-overlap harmonic jump energy, with no endpoint loss. -/
theorem ramanujanDilationProfile_ge_harmonic_jump_energy (r K : ℕ) (p h : ℕ+) :
    let T := min K ((p : ℕ) / h)
    (h : ℝ) * (∑ k ∈ Icc 1 T, (d4BMRamanujanNaturalCoefficient k (r + 2)).re ^ 2 / k) ≤
      ((p : ℝ) + ((p : ℝ) + h)) * pmRamanujanPrimitiveGram (r + 2) (r + 2) -
        2 * Real.sqrt p * Real.sqrt ((p : ℝ) + h) *
          pmRamanujanDilationProfile (r + 2) (by omega) ((p : ℝ) / ((p : ℝ) + h)) := by
  let T := min K ((p : ℕ) / h)
  let N := (T + 1) * (p : ℕ)
  let q := (p : ℕ) + h
  let F (n : ℕ) := (p : ℝ) * (pmRamanujanPrimitive (r + 2) (n / p)).re -
    (q : ℝ) * (pmRamanujanPrimitive (r + 2) (n / q)).re
  let A := (pmRamanujanPrimitive (r + 2) T).re
  let W := (h : ℝ) *
    (∑ k ∈ Icc 1 T, (d4BMRamanujanNaturalCoefficient k (r + 2)).re ^ 2 / k)
  have hT : T * (h : ℕ) ≤ p :=
    (Nat.mul_le_mul_right (h : ℕ) (min_le_right K _)).trans
      (Nat.div_mul_le_self (p : ℕ) h)
  have hN : 0 < N := by dsimp only [N]; positivity
  have hdist : HasSum (fun n : ℕ => (F n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)))
      (((p : ℝ) + ((p : ℝ) + h)) * pmRamanujanPrimitiveGram (r + 2) (r + 2) -
        2 * Real.sqrt p * Real.sqrt ((p : ℝ) + h) *
          pmRamanujanDilationProfile (r + 2) (by omega) ((p : ℝ) / ((p : ℝ) + h))) := by
    simpa only [F, q, PNat.add_coe, Nat.cast_add] using
      hasSum_scaled_pmRamanujanPrimitive_distance r p (p + h)
  have hmean : HasSum (fun n : ℕ => F n / ((n : ℝ) * ((n : ℝ) + 1))) 0 := by
    have hm := hasSum_ramanujanGapChainPacket_zero r 0 1 ((p : ℕ) - 1)
      (fun _ => (h : ℕ)) (fun _ => (1 : ℝ))
    apply hm.congr_fun
    intro n
    have hp1 : (p : ℕ) - 1 + 1 = p := Nat.sub_add_cancel p.pos
    simp [ramanujanGapChainPacket, pronicGapChainLower, hp1, F, q]
  have hm : (∑ n ∈ range N, F n / ((n : ℝ) * ((n : ℝ) + 1))) = (h : ℝ) * A / N := by
    dsimp only [N, F]
    simp only [sub_div, sum_sub_distrib]
    rw [scaled_primitive_common_prefix_mean (r + 2) T p p p.pos le_rfl (by nlinarith),
      scaled_primitive_common_prefix_mean (r + 2) T p q p.pos
        (by dsimp only [q]; omega) (by dsimp only [q]; nlinarith)]
    dsimp only [q, A]
    push_cast
    ring
  have he : (∑ n ∈ range N, (F n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) =
      W - ((h : ℝ) * A) ^ 2 / N := by
    have hs := ramanujanDilationDistance_prefix_eq (r + 2) K p h
    change (∑ n ∈ range N, (F n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) =
      W - (h : ℝ) ^ 2 / p * A ^ 2 / ((T : ℝ) + 1) at hs
    rw [hs]
    dsimp only [N]
    push_cast
    have hp0 : (p : ℝ) ≠ 0 := by positivity
    field_simp
  have hc := pronic_conditional_tail_completion F N hN ((h : ℝ) * A) W
    hmean hdist.summable hm he
  have hl : W ≤ ∑' n : ℕ, (F n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
    rw [hc]
    exact le_add_of_nonneg_right (tsum_nonneg fun n => div_nonneg (sq_nonneg _) (by positivity))
  rw [hdist.tsum_eq] at hl
  exact hl


private theorem clock_depth_jump_energy_pos (r t : ℕ) :
    0 < ∑ k ∈ Icc 1 (lagVisibilityClock (r + 2) + t),
      (d4BMRamanujanNaturalCoefficient k (r + 2)).re ^ 2 / k := by
  have hC : 0 < lagVisibilityClock (r + 2) := Nat.pos_of_ne_zero
    (fun hz => by have := (lagVisibilityClock_eq_zero_iff (r + 2)).mp hz; omega)
  have hmem : lagVisibilityClock (r + 2) ∈ Icc 1 (lagVisibilityClock (r + 2) + t) :=
    mem_Icc.mpr ⟨hC, by omega⟩
  have hc := (ramanujanNaturalCoefficient_re_ne_zero_iff_clock
    (r + 2) (lagVisibilityClock (r + 2))).mpr ⟨by omega, dvd_refl _⟩
  have hs := single_le_sum
    (fun k (_ : k ∈ Icc 1 (lagVisibilityClock (r + 2) + t)) =>
      div_nonneg (sq_nonneg (d4BMRamanujanNaturalCoefficient k (r + 2)).re)
        (Nat.cast_nonneg k)) hmem
  exact (div_pos (sq_pos_of_ne_zero hc) (by exact_mod_cast hC)).trans_le hs

/-- The endpoint-corrected finite probe recovers each coefficient from the first visible depth. -/
theorem ramanujanGapChainPacket_clock_coefficient_readout
    (r t m offset : ℕ) (h : ℕ → ℕ+) (a : ℕ → ℝ) (j : Fin m) :
    let K := lagVisibilityClock (r + 2) + t
    let hn : ℕ → ℕ := fun i => h i
    let P := pronicGapChainLower K m offset hn 0
    let b : ℕ → ℝ := fun i => if i = (j : ℕ) then 1 else 0
    (∑ n ∈ range ((K + 1) * P),
      ramanujanGapChainPacket r K m offset hn a n *
        (ramanujanGapChainPacket r K m offset hn b n +
          (h j : ℝ) * (pmRamanujanPrimitive (r + 2) K).re) /
        ((n : ℝ) * ((n : ℝ) + 1))) /
      ((h j : ℝ) * (∑ k ∈ Icc 1 K,
        (d4BMRamanujanNaturalCoefficient k (r + 2)).re ^ 2 / k)) = a j := by
  classical
  let K := lagVisibilityClock (r + 2) + t
  let hn : ℕ → ℕ := fun i => h i
  let P := pronicGapChainLower K m offset hn 0
  let b : ℕ → ℝ := fun i => if i = (j : ℕ) then 1 else 0
  let A := (pmRamanujanPrimitive (r + 2) K).re
  let J := ∑ k ∈ Icc 1 K, (d4BMRamanujanNaturalCoefficient k (r + 2)).re ^ 2 / k
  let B := ∑ i ∈ range m, a i * (hn i : ℝ)
  have hj : (j : ℕ) ∈ range m := mem_range.mpr j.isLt
  have hb (f : ℕ → ℝ) : (∑ i ∈ range m, b i * f i) = f j := by
    rw [sum_eq_single (j : ℕ)]
    · simp only [b, if_pos rfl, one_mul]
    · intro i _ hij
      simp only [b, if_neg hij, zero_mul]
    · intro hnot
      exact False.elim (hnot hj)
  have hd : (∑ i ∈ range m, a i * b i * (hn i : ℝ)) = a j * (h j : ℝ) := by
    calc
      _ = ∑ i ∈ range m, b i * (a i * (hn i : ℝ)) := by
        apply sum_congr rfl
        intro i _
        ring
      _ = _ := hb _
  have hB : (∑ i ∈ range m, b i * (hn i : ℝ)) = (h j : ℝ) := hb _
  have he := ramanujanGapChainPacket_bilinear_prefix_eq r K m offset hn a b
  change (∑ n ∈ range ((K + 1) * P),
      ramanujanGapChainPacket r K m offset hn a n * ramanujanGapChainPacket r K m offset hn b n /
        ((n : ℝ) * ((n : ℝ) + 1))) =
      (∑ i ∈ range m, a i * b i * (hn i : ℝ)) * J -
        B * (∑ i ∈ range m, b i * (hn i : ℝ)) / P * A ^ 2 / ((K : ℝ) + 1) at he
  rw [hd, hB] at he
  have hm := ramanujanGapChainPacket_prefix_mean_eq r K m offset hn a
  change (∑ n ∈ range ((K + 1) * P),
      ramanujanGapChainPacket r K m offset hn a n / ((n : ℝ) * ((n : ℝ) + 1))) =
        B * A / (((K : ℝ) + 1) * P) at hm
  have hc : (∑ n ∈ range ((K + 1) * P),
      ramanujanGapChainPacket r K m offset hn a n *
        (ramanujanGapChainPacket r K m offset hn b n + (h j : ℝ) * A) /
        ((n : ℝ) * ((n : ℝ) + 1))) = a j * (h j : ℝ) * J := by
    calc
      _ = (∑ n ∈ range ((K + 1) * P),
          ramanujanGapChainPacket r K m offset hn a n * ramanujanGapChainPacket r K m offset hn b n /
            ((n : ℝ) * ((n : ℝ) + 1))) +
          (h j : ℝ) * A * (∑ n ∈ range ((K + 1) * P),
            ramanujanGapChainPacket r K m offset hn a n / ((n : ℝ) * ((n : ℝ) + 1))) := by
        rw [mul_sum, ← sum_add_distrib]
        apply sum_congr rfl
        intro n _
        ring
      _ = _ := by
        rw [he, hm]
        have hP0 : (P : ℝ) ≠ 0 := by dsimp only [P, pronicGapChainLower]; positivity
        field_simp
        ring
  change (∑ n ∈ range ((K + 1) * P),
      ramanujanGapChainPacket r K m offset hn a n *
        (ramanujanGapChainPacket r K m offset hn b n + (h j : ℝ) * A) /
        ((n : ℝ) * ((n : ℝ) + 1))) / ((h j : ℝ) * J) = a j
  rw [hc]
  have hJ : 0 < J := clock_depth_jump_energy_pos r t
  have hh : 0 < (h j : ℝ) := by exact_mod_cast (h j).pos
  apply (div_eq_iff (ne_of_gt (mul_pos hh hJ))).mpr
  ring

end
end GaloisForLFunctions.BezoutValuationIncidence
