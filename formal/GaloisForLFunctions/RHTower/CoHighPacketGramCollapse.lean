/-
# Co-high packet Gram collapse: the complex Lagrange identity and its equality case

For a finite family of complex points `u i` with real masses `m i` the packet moments are
`p_k = ∑ i, m i · (u i)^k`. This module proves the exact algebra of the Gram expression
`p₀p₂ − p₁²`:

* `packetGram_eq_sum_strictPairs` — the **complex Lagrange identity** (no conjugation):
  `p₀p₂ − p₁² = ∑_{i<j} m i · m j · (u i − u j)²`, over ordered index pairs;
* `packetGram_coHigh_eq_neg_pairEnergy` — **co-high collapse**: on a co-high family
  `u i = g − I·δ i` (common real part `g`, real offsets `δ i`) every pair square is
  `(I·(δ j − δ i))² = −(δ i − δ j)² ≤ 0`, so the Gram expression is real:
  `p₀p₂ − p₁² = −∑_{i<j} m i · m j · (δ i − δ j)²`;
* `packetGram_coHigh_re_nonpos` / `packetGram_coHigh_im` — for nonnegative masses the
  Gram expression is a nonpositive real number;
* `packetGram_coHigh_re_le_neg_pair` — **quantized violation**: any index pair with
  distinct offsets pushes the Gram expression below `−m i₀ · m j₀ · (δ i₀ − δ j₀)²`;
  `packetGram_coHigh_re_neg` — with positive masses at the pair it is strictly negative;
* `packetGram_coHigh_eq_zero_iff` / `packetGram_coHigh_eq_zero_iff_single_point` /
  `packetGram_coHigh_eq_zero_iff_exists_const` — **single-point characterization**: with
  positive masses the Gram expression vanishes iff all offsets agree, iff the co-high
  family is constant on the packet — the Cauchy–Schwarz equality case;
* `packetGram_coHigh_pair` — the two-point packet value `−m i · m j · (δ i − δ j)²`:
  the whole Gram expression of an isolated pair is one explicit number.
-/
import Mathlib

namespace GaloisForLFunctions
namespace RHTower
namespace CoHighPacketGramCollapse

open Finset

noncomputable section

/-! ## Packet moments and the Gram expression -/

/-- The `k`-th signed power moment `p_k = ∑ i, m i · (u i)^k` of a finite weighted
complex packet. -/
def packetMoment {ι : Type*} (s : Finset ι) (m : ι → ℝ) (u : ι → ℂ) (k : ℕ) : ℂ :=
  ∑ i ∈ s, (m i : ℂ) * u i ^ k

/-- The zeroth moment is the total (signed) mass. -/
theorem packetMoment_zero {ι : Type*} (s : Finset ι) (m : ι → ℝ) (u : ι → ℂ) :
    packetMoment s m u 0 = ∑ i ∈ s, (m i : ℂ) := by
  simp [packetMoment]

/-- The packet Gram expression `p₀p₂ − p₁²`. -/
def packetGram {ι : Type*} (s : Finset ι) (m : ι → ℝ) (u : ι → ℂ) : ℂ :=
  packetMoment s m u 0 * packetMoment s m u 2 - packetMoment s m u 1 ^ 2

/-- The ordered index pairs `i < j` of a packet. -/
def strictPairs {ι : Type*} [LinearOrder ι] (s : Finset ι) : Finset (ι × ι) :=
  (s ×ˢ s).filter fun p => p.1 < p.2

/-- Membership in the ordered pair set. -/
theorem mem_strictPairs {ι : Type*} [LinearOrder ι] {s : Finset ι} {p : ι × ι} :
    p ∈ strictPairs s ↔ p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 < p.2 := by
  simp [strictPairs, Finset.mem_filter, Finset.mem_product, and_assoc]

/-! ## The complex Lagrange identity -/

/-- Double-sum expansion: the full symmetric pair-square sum is twice the Gram
expression. -/
theorem sum_sum_pairSquare_eq_two_mul_packetGram {ι : Type*} (s : Finset ι) (m : ι → ℝ) (u : ι → ℂ) :
    ∑ i ∈ s, ∑ j ∈ s, (m i : ℂ) * m j * (u i - u j) ^ 2 = 2 * packetGram s m u := by
  have hexp : ∑ i ∈ s, ∑ j ∈ s, (m i : ℂ) * m j * (u i - u j) ^ 2
      = ∑ i ∈ s, ∑ j ∈ s,
          ((m i : ℂ) * u i ^ 2 * (m j : ℂ)
            - 2 * ((m i : ℂ) * u i) * ((m j : ℂ) * u j)
            + (m i : ℂ) * ((m j : ℂ) * u j ^ 2)) :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hexp]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul_sum s s (fun i => (m i : ℂ) * u i ^ 2) (fun j => (m j : ℂ)),
    ← Finset.sum_mul_sum s s (fun i => 2 * ((m i : ℂ) * u i)) (fun j => (m j : ℂ) * u j),
    ← Finset.sum_mul_sum s s (fun i => (m i : ℂ)) (fun j => (m j : ℂ) * u j ^ 2),
    ← Finset.mul_sum s (fun i => (m i : ℂ) * u i) 2]
  simp only [packetGram, packetMoment, pow_zero, mul_one, pow_one]
  ring

/-- Product-set form of the symmetric pair-square sum. -/
theorem sum_product_pairSquare_eq_two_mul_packetGram {ι : Type*} (s : Finset ι) (m : ι → ℝ)
    (u : ι → ℂ) :
    ∑ p ∈ s ×ˢ s, (m p.1 : ℂ) * m p.2 * (u p.1 - u p.2) ^ 2 = 2 * packetGram s m u := by
  rw [Finset.sum_product]
  exact sum_sum_pairSquare_eq_two_mul_packetGram s m u

/-- A swap-symmetric summand sums equally over the lower and the upper triangle. -/
theorem sum_filter_gt_eq_sum_strictPairs {ι : Type*} [LinearOrder ι] (s : Finset ι) (F : ι × ι → ℂ)
    (hsymm : ∀ p : ι × ι, F p.swap = F p) :
    ∑ p ∈ (s ×ˢ s).filter (fun p => p.2 < p.1), F p = ∑ p ∈ strictPairs s, F p := by
  refine Finset.sum_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_product] at ha
    exact mem_strictPairs.mpr ⟨ha.1.2, ha.1.1, ha.2⟩
  · intro a ha
    rw [mem_strictPairs] at ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha.2.1, ha.1⟩, ha.2.2⟩
  · intro a _
    exact Prod.swap_swap a
  · intro a _
    exact Prod.swap_swap a
  · intro a _
    exact (hsymm a).symm

/-- A swap-symmetric, diagonally vanishing summand over the full product set is twice its
sum over ordered pairs. -/
theorem sum_product_eq_two_mul_sum_strictPairs {ι : Type*} [LinearOrder ι] (s : Finset ι) (F : ι × ι → ℂ)
    (hsymm : ∀ p : ι × ι, F p.swap = F p) (hdiag : ∀ p : ι × ι, p.1 = p.2 → F p = 0) :
    ∑ p ∈ s ×ˢ s, F p = 2 * ∑ p ∈ strictPairs s, F p := by
  have hsplit := Finset.sum_filter_add_sum_filter_not (s ×ˢ s) (fun p => p.1 < p.2) F
  have hsplit2 := Finset.sum_filter_add_sum_filter_not
    ((s ×ˢ s).filter fun p => ¬ p.1 < p.2) (fun p => p.2 < p.1) F
  have hset : ((s ×ˢ s).filter fun p => ¬ p.1 < p.2).filter (fun p => p.2 < p.1)
      = (s ×ˢ s).filter fun p => p.2 < p.1 := by
    rw [Finset.filter_filter]
    exact Finset.filter_congr fun x _ => ⟨fun h => h.2, fun h => ⟨lt_asymm h, h⟩⟩
  have hzero : ∑ p ∈ ((s ×ˢ s).filter fun p => ¬ p.1 < p.2).filter
      (fun p => ¬ p.2 < p.1), F p = 0 := by
    refine Finset.sum_eq_zero fun p hp => ?_
    simp only [Finset.mem_filter] at hp
    exact hdiag p (le_antisymm (not_lt.mp hp.2) (not_lt.mp hp.1.2))
  have hnot : ∑ p ∈ (s ×ˢ s).filter (fun p => ¬ p.1 < p.2), F p
      = ∑ p ∈ strictPairs s, F p := by
    calc ∑ p ∈ (s ×ˢ s).filter (fun p => ¬ p.1 < p.2), F p
        = ∑ p ∈ ((s ×ˢ s).filter fun p => ¬ p.1 < p.2).filter (fun p => p.2 < p.1), F p
          + ∑ p ∈ ((s ×ˢ s).filter fun p => ¬ p.1 < p.2).filter
              (fun p => ¬ p.2 < p.1), F p := hsplit2.symm
      _ = ∑ p ∈ (s ×ˢ s).filter (fun p => p.2 < p.1), F p := by
          rw [hset, hzero, add_zero]
      _ = ∑ p ∈ strictPairs s, F p := sum_filter_gt_eq_sum_strictPairs s F hsymm
  calc ∑ p ∈ s ×ˢ s, F p
      = ∑ p ∈ (s ×ˢ s).filter (fun p => p.1 < p.2), F p
        + ∑ p ∈ (s ×ˢ s).filter (fun p => ¬ p.1 < p.2), F p := hsplit.symm
    _ = ∑ p ∈ strictPairs s, F p
        + ∑ p ∈ (s ×ˢ s).filter (fun p => ¬ p.1 < p.2), F p := rfl
    _ = ∑ p ∈ strictPairs s, F p + ∑ p ∈ strictPairs s, F p := by rw [hnot]
    _ = 2 * ∑ p ∈ strictPairs s, F p := (two_mul _).symm

/-- **Complex Lagrange identity** for finite weighted families, without conjugation:
`p₀p₂ − p₁² = ∑_{i<j} m i · m j · (u i − u j)²`. -/
theorem packetGram_eq_sum_strictPairs {ι : Type*} [LinearOrder ι] (s : Finset ι) (m : ι → ℝ) (u : ι → ℂ) :
    packetGram s m u
      = ∑ p ∈ strictPairs s, (m p.1 : ℂ) * m p.2 * (u p.1 - u p.2) ^ 2 := by
  have h2 := sum_product_eq_two_mul_sum_strictPairs s
    (fun p => (m p.1 : ℂ) * m p.2 * (u p.1 - u p.2) ^ 2)
    (fun p => by
      show (m p.2 : ℂ) * m p.1 * (u p.2 - u p.1) ^ 2
        = (m p.1 : ℂ) * m p.2 * (u p.1 - u p.2) ^ 2
      ring)
    (fun p hp => by
      show (m p.1 : ℂ) * m p.2 * (u p.1 - u p.2) ^ 2 = 0
      rw [hp]
      ring)
  have h3 : (2 : ℂ) * packetGram s m u
      = 2 * ∑ p ∈ strictPairs s, (m p.1 : ℂ) * m p.2 * (u p.1 - u p.2) ^ 2 := by
    rw [← sum_product_pairSquare_eq_two_mul_packetGram s m u]
    exact h2
  exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) h3

/-! ## Co-high specialization: common real part, imaginary pair differences -/

/-- The co-high packet family at common real part `g`: `u i = g − I·δ i`. -/
def coHighFamily {ι : Type*} (g : ℝ) (δ : ι → ℝ) (i : ι) : ℂ := (g : ℂ) - Complex.I * (δ i : ℂ)

/-- Two co-high points agree exactly when their offsets agree. -/
theorem coHighFamily_eq_iff {ι : Type*} (g : ℝ) (δ : ι → ℝ) (i j : ι) :
    coHighFamily g δ i = coHighFamily g δ j ↔ δ i = δ j := by
  unfold coHighFamily
  constructor
  · intro h
    have h1 : Complex.I * (δ i : ℂ) = Complex.I * (δ j : ℂ) := sub_right_inj.mp h
    have h2 : (δ i : ℂ) = (δ j : ℂ) := mul_left_cancel₀ Complex.I_ne_zero h1
    exact_mod_cast h2
  · intro h
    rw [h]

/-- The real pair-interaction energy of a co-high packet:
`∑_{i<j} m i · m j · (δ i − δ j)²`. -/
def coHighPairEnergy {ι : Type*} [LinearOrder ι] (s : Finset ι) (m δ : ι → ℝ) : ℝ :=
  ∑ p ∈ strictPairs s, m p.1 * m p.2 * (δ p.1 - δ p.2) ^ 2

/-- Nonnegative masses give nonnegative pair energy. -/
theorem coHighPairEnergy_nonneg {ι : Type*} [LinearOrder ι] (s : Finset ι) {m : ι → ℝ} (δ : ι → ℝ)
    (hm : ∀ i ∈ s, 0 ≤ m i) : 0 ≤ coHighPairEnergy s m δ := by
  unfold coHighPairEnergy
  refine Finset.sum_nonneg fun p hp => ?_
  rw [mem_strictPairs] at hp
  exact mul_nonneg (mul_nonneg (hm p.1 hp.1) (hm p.2 hp.2.1)) (sq_nonneg _)

/-- **Co-high collapse**: on a co-high family every Lagrange pair square is real and
nonpositive, and the Gram expression is minus the real pair energy. -/
theorem packetGram_coHigh_eq_neg_pairEnergy {ι : Type*} [LinearOrder ι] (s : Finset ι) (m δ : ι → ℝ) (g : ℝ) :
    packetGram s m (coHighFamily g δ) = -((coHighPairEnergy s m δ : ℝ) : ℂ) :=
  calc packetGram s m (coHighFamily g δ)
      = ∑ p ∈ strictPairs s,
          (m p.1 : ℂ) * m p.2 * (coHighFamily g δ p.1 - coHighFamily g δ p.2) ^ 2 :=
        packetGram_eq_sum_strictPairs s m (coHighFamily g δ)
    _ = ∑ p ∈ strictPairs s, -(((m p.1 * m p.2 * (δ p.1 - δ p.2) ^ 2 : ℝ)) : ℂ) :=
        Finset.sum_congr rfl fun p _ => by
          unfold coHighFamily
          push_cast
          linear_combination
            (m p.1 : ℂ) * (m p.2 : ℂ) * ((δ p.1 : ℂ) - (δ p.2 : ℂ)) ^ 2 * Complex.I_sq
    _ = -((coHighPairEnergy s m δ : ℝ) : ℂ) := by
        unfold coHighPairEnergy
        push_cast
        rw [Finset.sum_neg_distrib]

/-- The co-high Gram expression has real part minus the pair energy. -/
theorem packetGram_coHigh_re {ι : Type*} [LinearOrder ι] (s : Finset ι) (m δ : ι → ℝ) (g : ℝ) :
    (packetGram s m (coHighFamily g δ)).re = -coHighPairEnergy s m δ := by
  rw [packetGram_coHigh_eq_neg_pairEnergy]
  simp

/-- The co-high Gram expression is real: its imaginary part vanishes. -/
theorem packetGram_coHigh_im {ι : Type*} [LinearOrder ι] (s : Finset ι) (m δ : ι → ℝ) (g : ℝ) :
    (packetGram s m (coHighFamily g δ)).im = 0 := by
  rw [packetGram_coHigh_eq_neg_pairEnergy]
  simp

/-- With nonnegative masses the co-high Gram expression is a nonpositive real. -/
theorem packetGram_coHigh_re_nonpos {ι : Type*} [LinearOrder ι] (s : Finset ι) {m : ι → ℝ} (δ : ι → ℝ) (g : ℝ)
    (hm : ∀ i ∈ s, 0 ≤ m i) :
    (packetGram s m (coHighFamily g δ)).re ≤ 0 := by
  rw [packetGram_coHigh_re]
  exact neg_nonpos.mpr (coHighPairEnergy_nonneg s δ hm)

/-! ## The equality case and the quantized violation -/

/-- With positive masses the pair energy vanishes iff all offsets agree. -/
theorem coHighPairEnergy_eq_zero_iff {ι : Type*} [LinearOrder ι] (s : Finset ι) {m : ι → ℝ} (δ : ι → ℝ)
    (hm : ∀ i ∈ s, 0 < m i) :
    coHighPairEnergy s m δ = 0 ↔ ∀ i ∈ s, ∀ j ∈ s, δ i = δ j := by
  unfold coHighPairEnergy
  have hterm : ∀ p ∈ strictPairs s, 0 ≤ m p.1 * m p.2 * (δ p.1 - δ p.2) ^ 2 := by
    intro p hp
    rw [mem_strictPairs] at hp
    exact mul_nonneg (mul_nonneg (hm p.1 hp.1).le (hm p.2 hp.2.1).le) (sq_nonneg _)
  rw [Finset.sum_eq_zero_iff_of_nonneg hterm]
  constructor
  · intro h i hi j hj
    rcases lt_trichotomy i j with hij | hij | hij
    · have hz := h (i, j) (mem_strictPairs.mpr ⟨hi, hj, hij⟩)
      have hmm : m i * m j ≠ 0 := ne_of_gt (mul_pos (hm i hi) (hm j hj))
      rcases mul_eq_zero.mp hz with h' | h'
      · exact absurd h' hmm
      · exact sub_eq_zero.mp (sq_eq_zero_iff.mp h')
    · exact congrArg δ hij
    · have hz := h (j, i) (mem_strictPairs.mpr ⟨hj, hi, hij⟩)
      have hmm : m j * m i ≠ 0 := ne_of_gt (mul_pos (hm j hj) (hm i hi))
      rcases mul_eq_zero.mp hz with h' | h'
      · exact absurd h' hmm
      · exact (sub_eq_zero.mp (sq_eq_zero_iff.mp h')).symm
  · intro h p hp
    rw [mem_strictPairs] at hp
    rw [h p.1 hp.1 p.2 hp.2.1]
    ring

/-- Any single ordered pair bounds the pair energy from below. -/
theorem pair_le_coHighPairEnergy {ι : Type*} [LinearOrder ι] (s : Finset ι) {m : ι → ℝ} (δ : ι → ℝ)
    (hm : ∀ i ∈ s, 0 ≤ m i) {i₀ j₀ : ι} (hi : i₀ ∈ s) (hj : j₀ ∈ s) (hne : i₀ ≠ j₀) :
    m i₀ * m j₀ * (δ i₀ - δ j₀) ^ 2 ≤ coHighPairEnergy s m δ := by
  unfold coHighPairEnergy
  have hterm : ∀ p ∈ strictPairs s, 0 ≤ m p.1 * m p.2 * (δ p.1 - δ p.2) ^ 2 := by
    intro p hp
    rw [mem_strictPairs] at hp
    exact mul_nonneg (mul_nonneg (hm p.1 hp.1) (hm p.2 hp.2.1)) (sq_nonneg _)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact Finset.single_le_sum hterm (a := (i₀, j₀)) (mem_strictPairs.mpr ⟨hi, hj, hlt⟩)
  · have h := Finset.single_le_sum hterm (a := (j₀, i₀)) (mem_strictPairs.mpr ⟨hj, hi, hlt⟩)
    calc m i₀ * m j₀ * (δ i₀ - δ j₀) ^ 2
        = m j₀ * m i₀ * (δ j₀ - δ i₀) ^ 2 := by ring
      _ ≤ _ := h

/-- **Quantized violation**: any index pair with distinct members pushes the co-high Gram
expression below minus that pair's energy contribution. -/
theorem packetGram_coHigh_re_le_neg_pair {ι : Type*} [LinearOrder ι] (s : Finset ι) {m : ι → ℝ} (δ : ι → ℝ) (g : ℝ)
    (hm : ∀ i ∈ s, 0 ≤ m i) {i₀ j₀ : ι} (hi : i₀ ∈ s) (hj : j₀ ∈ s) (hne : i₀ ≠ j₀) :
    (packetGram s m (coHighFamily g δ)).re ≤ -(m i₀ * m j₀ * (δ i₀ - δ j₀) ^ 2) := by
  rw [packetGram_coHigh_re]
  exact neg_le_neg (pair_le_coHighPairEnergy s δ hm hi hj hne)

/-- With positive masses at a pair of distinct offsets the co-high Gram expression is
strictly negative. -/
theorem packetGram_coHigh_re_neg {ι : Type*} [LinearOrder ι] (s : Finset ι) {m : ι → ℝ} (δ : ι → ℝ) (g : ℝ)
    (hm : ∀ i ∈ s, 0 ≤ m i) {i₀ j₀ : ι} (hi : i₀ ∈ s) (hj : j₀ ∈ s)
    (hmi : 0 < m i₀) (hmj : 0 < m j₀) (hδ : δ i₀ ≠ δ j₀) :
    (packetGram s m (coHighFamily g δ)).re < 0 := by
  have hne : i₀ ≠ j₀ := fun h => hδ (congrArg δ h)
  have hsub : δ i₀ - δ j₀ ≠ 0 := sub_ne_zero.mpr hδ
  have hq : 0 < m i₀ * m j₀ * (δ i₀ - δ j₀) ^ 2 :=
    mul_pos (mul_pos hmi hmj)
      (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hsub)))
  have hle := packetGram_coHigh_re_le_neg_pair s δ g hm hi hj hne
  linarith

/-- **Single-point characterization, offset form**: with positive masses the co-high Gram
expression vanishes iff all offsets agree on the packet. -/
theorem packetGram_coHigh_eq_zero_iff {ι : Type*} [LinearOrder ι] (s : Finset ι) {m : ι → ℝ} (δ : ι → ℝ) (g : ℝ)
    (hm : ∀ i ∈ s, 0 < m i) :
    packetGram s m (coHighFamily g δ) = 0 ↔ ∀ i ∈ s, ∀ j ∈ s, δ i = δ j := by
  rw [packetGram_coHigh_eq_neg_pairEnergy, neg_eq_zero, Complex.ofReal_eq_zero]
  exact coHighPairEnergy_eq_zero_iff s δ hm

/-- **Single-point characterization, point form**: with positive masses the co-high Gram
expression vanishes iff the packet points all coincide. -/
theorem packetGram_coHigh_eq_zero_iff_single_point {ι : Type*} [LinearOrder ι] (s : Finset ι) {m : ι → ℝ}
    (δ : ι → ℝ) (g : ℝ) (hm : ∀ i ∈ s, 0 < m i) :
    packetGram s m (coHighFamily g δ) = 0
      ↔ ∀ i ∈ s, ∀ j ∈ s, coHighFamily g δ i = coHighFamily g δ j := by
  rw [packetGram_coHigh_eq_zero_iff s δ g hm]
  constructor
  · intro h i hi j hj
    exact (coHighFamily_eq_iff g δ i j).mpr (h i hi j hj)
  · intro h i hi j hj
    exact (coHighFamily_eq_iff g δ i j).mp (h i hi j hj)

/-- **Single-point characterization, constant form**: on a nonempty packet with positive
masses the co-high Gram expression vanishes iff the family is constant. -/
theorem packetGram_coHigh_eq_zero_iff_exists_const {ι : Type*} [LinearOrder ι] (s : Finset ι) {m : ι → ℝ}
    (δ : ι → ℝ) (g : ℝ) (hs : s.Nonempty) (hm : ∀ i ∈ s, 0 < m i) :
    packetGram s m (coHighFamily g δ) = 0
      ↔ ∃ c : ℂ, ∀ i ∈ s, coHighFamily g δ i = c := by
  rw [packetGram_coHigh_eq_zero_iff_single_point s δ g hm]
  constructor
  · intro h
    obtain ⟨i₀, hi₀⟩ := hs
    exact ⟨coHighFamily g δ i₀, fun i hi => h i hi i₀ hi₀⟩
  · rintro ⟨c, hc⟩ i hi j hj
    rw [hc i hi, hc j hj]

/-! ## The isolated pair: one explicit number -/

/-- The ordered pair set of a two-point packet is the single ordered pair. -/
theorem strictPairs_pair {ι : Type*} [LinearOrder ι] {i j : ι} (hij : i < j) :
    strictPairs ({i, j} : Finset ι) = {(i, j)} := by
  ext p
  simp only [mem_strictPairs, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨h1 | h1, h2 | h2, hlt⟩
    · rw [h1, h2] at hlt
      exact absurd hlt (lt_irrefl i)
    · exact Prod.ext h1 h2
    · rw [h1, h2] at hlt
      exact absurd hlt (lt_asymm hij)
    · rw [h1, h2] at hlt
      exact absurd hlt (lt_irrefl j)
  · rintro rfl
    exact ⟨Or.inl rfl, Or.inr rfl, hij⟩

/-- Pair energy of a two-point packet: the single interaction term. -/
theorem coHighPairEnergy_pair {ι : Type*} [LinearOrder ι] {i j : ι} (hij : i < j) (m δ : ι → ℝ) :
    coHighPairEnergy {i, j} m δ = m i * m j * (δ i - δ j) ^ 2 := by
  unfold coHighPairEnergy
  rw [strictPairs_pair hij]
  exact Finset.sum_singleton _ _

/-- **Two-point collapse**: the whole Gram expression of an isolated co-high pair is the
single explicit number `−m i · m j · (δ i − δ j)²`. -/
theorem packetGram_coHigh_pair {ι : Type*} [LinearOrder ι] {i j : ι} (hij : i < j) (m δ : ι → ℝ) (g : ℝ) :
    packetGram {i, j} m (coHighFamily g δ)
      = -((m i * m j * (δ i - δ j) ^ 2 : ℝ) : ℂ) := by
  rw [packetGram_coHigh_eq_neg_pairEnergy, coHighPairEnergy_pair hij]

end

end CoHighPacketGramCollapse
end RHTower
end GaloisForLFunctions
