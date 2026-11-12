import GaloisForLFunctions.WorldsOfTheZeroConfiguration.PrimesRoundAnOscillatingDensity
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# The square target of a half-scale copy of the zeros

The target `sqTarget a` puts the weight `2 Λ(j) j^{2a}` on the square `k = j²` and nothing
elsewhere.

* **Dirichlet series** (`lseriesHasSum_sqTarget`).  `Σ_k sqTarget(k) k^{−s} = 2 Σ_j Λ(j) j^{−(2s−2a)}`,
  that is `−2 ζ′/ζ(2s − 2a)`: the logarithmic derivative of `ζ(2s − 2a)`, whose zeros are the points
  `a + z/2`, `z` a zero of `ζ`.
* **Spikes of an interval** (`sum_Ioc_sqTarget_le`).  The squares in `(b, n]` number at most
  `(n − b)/√n + 1`, and each spike is at most `(2/ε) n^{(2a+ε)/2}`.
-/

open Complex Finset Filter Topology
open ArithmeticFunction (vonMangoldt)

noncomputable section

namespace GaloisForLFunctions.WorldsOfTheZeroConfiguration.SquareTarget

/-- The weight `2 Λ(j) j^{2a}`. -/
def sqWeight (a : ℝ) (j : ℕ) : ℝ := 2 * vonMangoldt j * (j : ℝ) ^ (2 * a)

/-- The square target: `2 Λ(j) j^{2a}` at `k = j²`, zero off the squares. -/
def sqTarget (a : ℝ) (k : ℕ) : ℝ := if Nat.sqrt k ^ 2 = k then sqWeight a (Nat.sqrt k) else 0

theorem sqWeight_nonneg (a : ℝ) (j : ℕ) : 0 ≤ sqWeight a j :=
  mul_nonneg (mul_nonneg (by norm_num) ArithmeticFunction.vonMangoldt_nonneg)
    (Real.rpow_nonneg (Nat.cast_nonneg j) _)

theorem sqWeight_zero (a : ℝ) : sqWeight a 0 = 0 := by simp [sqWeight]

theorem sqTarget_sq (a : ℝ) (j : ℕ) : sqTarget a (j ^ 2) = sqWeight a j := by
  rw [sqTarget, Nat.sqrt_eq', if_pos rfl]

theorem sqTarget_nonneg (a : ℝ) (k : ℕ) : 0 ≤ sqTarget a k := by
  unfold sqTarget
  split_ifs
  · exact sqWeight_nonneg a _
  · exact le_rfl

theorem sqTarget_zero (a : ℝ) : sqTarget a 0 = 0 := by
  have h := sqTarget_sq a 0
  rw [sqWeight_zero] at h
  simpa using h

theorem sqTarget_of_not_sq (a : ℝ) {k : ℕ} (hk : ∀ j : ℕ, j ^ 2 ≠ k) : sqTarget a k = 0 := by
  rw [sqTarget, if_neg (hk _)]

/-- The square target on an interval is the sum of the weights over the roots. -/
theorem sum_Ioc_sqTarget (a : ℝ) (b n : ℕ) :
    ∑ k ∈ Ioc b n, sqTarget a k = ∑ j ∈ Ioc (Nat.sqrt b) (Nat.sqrt n), sqWeight a j := by
  have hinj : ∀ x ∈ Ioc (Nat.sqrt b) (Nat.sqrt n), ∀ y ∈ Ioc (Nat.sqrt b) (Nat.sqrt n),
      x ^ 2 = y ^ 2 → x = y := fun x _ y _ h => Nat.pow_left_injective (by norm_num) h
  have h1 : ∑ j ∈ Ioc (Nat.sqrt b) (Nat.sqrt n), sqWeight a j =
      ∑ j ∈ Ioc (Nat.sqrt b) (Nat.sqrt n), sqTarget a (j ^ 2) :=
    Finset.sum_congr rfl fun j _ => (sqTarget_sq a j).symm
  rw [h1, ← Finset.sum_image hinj]
  refine (Finset.sum_subset (fun k hk => ?_) (fun k hk hnot => ?_)).symm
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨hj1, hj2⟩ := Finset.mem_Ioc.mp hj
    exact Finset.mem_Ioc.mpr ⟨Nat.sqrt_lt'.mp hj1, Nat.le_sqrt'.mp hj2⟩
  · refine sqTarget_of_not_sq a fun j hj => hnot (Finset.mem_image.mpr ⟨j, ?_, hj⟩)
    obtain ⟨hk1, hk2⟩ := Finset.mem_Ioc.mp hk
    exact Finset.mem_Ioc.mpr ⟨Nat.sqrt_lt'.mpr (hj ▸ hk1), Nat.le_sqrt'.mpr (hj ▸ hk2)⟩

/-- A spike is at most `(2/ε) j^{2a+ε}`. -/
theorem sqWeight_le (a : ℝ) {ε : ℝ} (hε : 0 < ε) (j : ℕ) :
    sqWeight a j ≤ 2 / ε * (j : ℝ) ^ (2 * a + ε) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [sqWeight_zero]
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (by simp) _)
  · have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
    have h1 : vonMangoldt j ≤ (j : ℝ) ^ ε / ε :=
      ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_rpow_div hj0.le hε)
    have h2 : (0 : ℝ) ≤ (j : ℝ) ^ (2 * a) := Real.rpow_nonneg hj0.le _
    calc sqWeight a j = 2 * vonMangoldt j * (j : ℝ) ^ (2 * a) := rfl
      _ ≤ 2 * ((j : ℝ) ^ ε / ε) * (j : ℝ) ^ (2 * a) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by norm_num)) h2
      _ = 2 / ε * (j : ℝ) ^ (2 * a + ε) := by
          rw [Real.rpow_add hj0]; ring

/-- The number of squares in `(b, n]` is at most `(n − b)/√n + 1`. -/
theorem card_Ioc_sqrt_le {b n : ℕ} (hbn : b ≤ n) (hn : 0 < n) :
    ((Ioc (Nat.sqrt b) (Nat.sqrt n)).card : ℝ) ≤ ((n : ℝ) - b) / Real.sqrt n + 1 := by
  have hpq : Nat.sqrt b ≤ Nat.sqrt n := Nat.sqrt_le_sqrt hbn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hq : (Nat.sqrt n : ℝ) ≤ Real.sqrt n :=
    (Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mpr
      (by exact_mod_cast Nat.sqrt_le' n)
  have hp : Real.sqrt b < (Nat.sqrt b : ℝ) + 1 :=
    (Real.sqrt_lt' (by positivity)).mpr (by exact_mod_cast Nat.lt_succ_sqrt' b)
  have hyx : Real.sqrt b ≤ Real.sqrt n := Real.sqrt_le_sqrt (by exact_mod_cast hbn)
  have hdiff : Real.sqrt n - Real.sqrt b ≤ ((n : ℝ) - b) / Real.sqrt n := by
    rw [le_div_iff₀ hsn]
    nlinarith [mul_nonneg (Real.sqrt_nonneg b) (sub_nonneg.mpr hyx), Real.mul_self_sqrt hn0.le,
      Real.mul_self_sqrt hb0]
  rw [Nat.card_Ioc, Nat.cast_sub hpq]
  linarith

/-- **The spikes of an interval.** -/
theorem sum_Ioc_sqTarget_le (a : ℝ) {ε : ℝ} (hε : 0 < ε) (hae : 0 ≤ 2 * a + ε) {b n : ℕ}
    (hbn : b ≤ n) (hn : 0 < n) :
    ∑ k ∈ Ioc b n, sqTarget a k ≤
      (((n : ℝ) - b) / Real.sqrt n + 1) * (2 / ε * (n : ℝ) ^ ((2 * a + ε) / 2)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hq : (Nat.sqrt n : ℝ) ≤ Real.sqrt n :=
    (Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mpr
      (by exact_mod_cast Nat.sqrt_le' n)
  have hW : 0 ≤ 2 / ε * (n : ℝ) ^ ((2 * a + ε) / 2) :=
    mul_nonneg (by positivity) (Real.rpow_nonneg hn0.le _)
  have hterm : ∀ j ∈ Ioc (Nat.sqrt b) (Nat.sqrt n),
      sqWeight a j ≤ 2 / ε * (n : ℝ) ^ ((2 * a + ε) / 2) := by
    intro j hj
    have hjq : (j : ℝ) ≤ Real.sqrt n :=
      le_trans (by exact_mod_cast (Finset.mem_Ioc.mp hj).2) hq
    have hpow : (j : ℝ) ^ (2 * a + ε) ≤ (n : ℝ) ^ ((2 * a + ε) / 2) := by
      calc (j : ℝ) ^ (2 * a + ε) ≤ (Real.sqrt n) ^ (2 * a + ε) :=
            Real.rpow_le_rpow (Nat.cast_nonneg j) hjq hae
        _ = (n : ℝ) ^ ((2 * a + ε) / 2) := by
            rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hn0.le]
            congr 1
            ring
    exact (sqWeight_le a hε j).trans (mul_le_mul_of_nonneg_left hpow (by positivity))
  rw [sum_Ioc_sqTarget]
  calc ∑ j ∈ Ioc (Nat.sqrt b) (Nat.sqrt n), sqWeight a j
      ≤ (Ioc (Nat.sqrt b) (Nat.sqrt n)).card • (2 / ε * (n : ℝ) ^ ((2 * a + ε) / 2)) :=
        Finset.sum_le_card_nsmul _ _ _ hterm
    _ = ((Ioc (Nat.sqrt b) (Nat.sqrt n)).card : ℝ) * (2 / ε * (n : ℝ) ^ ((2 * a + ε) / 2)) :=
        nsmul_eq_mul _ _
    _ ≤ (((n : ℝ) - b) / Real.sqrt n + 1) * (2 / ε * (n : ℝ) ^ ((2 * a + ε) / 2)) :=
        mul_le_mul_of_nonneg_right (card_Ioc_sqrt_le hbn hn) hW

/-- **The Dirichlet series of the square target** is `2 Σ_j Λ(j) j^{−(2s−2a)}`. -/
theorem lseriesHasSum_sqTarget {a : ℝ} {s : ℂ} (hs : 1 < (2 * s - 2 * (a : ℂ)).re) :
    LSeriesHasSum (fun k : ℕ => (sqTarget a k : ℂ)) s
      (2 * LSeries (fun n : ℕ => (vonMangoldt n : ℂ)) (2 * s - 2 * (a : ℂ))) := by
  set w : ℂ := 2 * s - 2 * (a : ℂ) with hw
  have hΛ := (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).hasSum.mul_left (2 : ℂ)
  have hterm : ∀ j : ℕ, LSeries.term (fun k : ℕ => (sqTarget a k : ℂ)) s (j ^ 2) =
      2 * LSeries.term (fun n : ℕ => (vonMangoldt n : ℂ)) w j := by
    intro j
    rcases eq_or_ne j 0 with rfl | hj
    · simp
    · have hj0 : (j : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hj
      have hjr : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      have h1 : ((j ^ 2 : ℕ) : ℂ) ^ s = (j : ℂ) ^ (2 * s) := by
        have h := Complex.natCast_cpow_natCast_mul j 2 s
        rw [Nat.cast_pow, ← h]
        norm_num
      have h2 : (((j : ℝ) ^ (2 * a) : ℝ) : ℂ) = (j : ℂ) ^ (2 * (a : ℂ)) := by
        rw [Complex.ofReal_cpow hjr, Complex.ofReal_natCast, Complex.ofReal_mul,
          Complex.ofReal_ofNat]
      have h3 : (j : ℂ) ^ w = (j : ℂ) ^ (2 * s) / (j : ℂ) ^ (2 * (a : ℂ)) := by
        rw [hw, Complex.cpow_sub _ _ hj0]
      have hnum : ((2 * vonMangoldt j * (j : ℝ) ^ (2 * a) : ℝ) : ℂ) =
          2 * (vonMangoldt j : ℂ) * (j : ℂ) ^ (2 * (a : ℂ)) := by
        rw [← h2]
        push_cast
        ring
      rw [LSeries.term_of_ne_zero (pow_ne_zero 2 hj), LSeries.term_of_ne_zero hj, sqTarget_sq,
        sqWeight, hnum, h1, h3, div_div_eq_mul_div]
      ring
  rw [LSeriesHasSum]
  refine (Function.Injective.hasSum_iff (g := fun j : ℕ => j ^ 2)
    (Nat.pow_left_injective (by norm_num)) ?_).mp ?_
  · intro k hk
    have h0 : sqTarget a k = 0 := sqTarget_of_not_sq a fun j hj => hk ⟨j, hj⟩
    rcases eq_or_ne k 0 with rfl | hk0
    · simp
    · rw [LSeries.term_of_ne_zero hk0, h0]
      simp
  · have hcomp : (LSeries.term (fun k : ℕ => (sqTarget a k : ℂ)) s) ∘ (fun j : ℕ => j ^ 2) =
        fun j => 2 * LSeries.term (fun n : ℕ => (vonMangoldt n : ℂ)) w j := funext hterm
    rw [hcomp]
    exact hΛ

end GaloisForLFunctions.WorldsOfTheZeroConfiguration.SquareTarget
