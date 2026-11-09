import GaloisForLFunctions.ArithmeticDiscreteness.TheExceptionalValuesHaveSmallHausdorffDimension
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Dimension zero from linear numbers of exponentially small balls

At each level, linearly many balls of exponentially shrinking radius have summable diameter
costs in every positive dimension. Their limsup therefore has Hausdorff dimension zero.
-/

open Set Metric MeasureTheory MeasureTheory.Measure Filter Topology
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.InfiniteRankWeilTheory

/-- Linear cardinality and exponential radii force every positive-dimensional Hausdorff
measure of the recurrently covered set to vanish. -/
theorem hausdorffMeasure_frequently_eq_zero_of_exponential_covers
    (S : ℕ → Set ℝ) (G : ℕ → Finset ℝ) {M R b s : ℝ}
    (hM : 0 < M) (hR : 0 < R) (hb : 0 < b) (hs : 0 < s)
    (hcard : ∀ n, ((G n).card : ℝ) ≤ M * ((n : ℝ) + 1))
    (hcover : ∀ n, ∀ x ∈ S n, ∃ y ∈ G n, |x - y| ≤ R * Real.exp (-b * n)) :
    μH[s] {x : ℝ | ∃ᶠ n : ℕ in atTop, x ∈ S n} = 0 := by
  let E : Set ℝ := {x | ∃ᶠ n : ℕ in atTop, x ∈ S n}
  let r : ℕ → ℝ := fun n => R * Real.exp (-b * n)
  let w : ℕ → ℝ := fun n =>
    (M * (2 * R) ^ s) * (((n : ℝ) + 1) * Real.exp (-(b * s) * n))
  have hr (n : ℕ) : 0 ≤ r n := by dsimp [r]; positivity
  have hrmono : Antitone r := by
    intro n m hnm
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonpos_left (by exact_mod_cast hnm) (neg_nonpos.mpr hb.le))) hR.le
  have hrlim : Tendsto r atTop (𝓝 0) := by
    have h := ((Real.summable_pow_mul_exp_neg_nat_mul 0 hb).tendsto_atTop_zero).const_mul R
    simpa only [pow_zero, one_mul, mul_zero] using h
  have hw (n : ℕ) : 0 ≤ w n := by dsimp [w]; positivity
  have hwsum : Summable w := by
    have h := ((Real.summable_pow_mul_exp_neg_nat_mul 1 (mul_pos hb hs)).add
      (Real.summable_pow_mul_exp_neg_nat_mul 0 (mul_pos hb hs))).mul_left (M * (2 * R) ^ s)
    refine h.congr fun n => ?_
    dsimp only [w]
    simp only [pow_one, pow_zero]
    ring
  have hcost (n : ℕ) : (G n).card * (2 * r n) ^ s ≤ w n := by
    have hpow : (2 * r n) ^ s = (2 * R) ^ s * Real.exp (-(b * s) * n) := by
      dsimp [r]
      rw [← mul_assoc, Real.mul_rpow (by positivity) (Real.exp_pos _).le, ← Real.exp_mul]
      congr 2
      ring
    rw [hpow]
    calc ((G n).card : ℝ) * ((2 * R) ^ s * Real.exp (-(b * s) * n))
        ≤ (M * ((n : ℝ) + 1)) * ((2 * R) ^ s * Real.exp (-(b * s) * n)) :=
          mul_le_mul_of_nonneg_right (hcard n) (by positivity)
      _ = w n := by dsimp [w]; ring
  have htail (N : ℕ) : Complex.ofReal '' E ⊆
      ⋃ n ≥ N, ⋃ y ∈ G n, closedBall (y : ℂ) (r n) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨n, hn, hxn⟩ := frequently_atTop.mp hx N
    obtain ⟨y, hy, hdist⟩ := hcover n x hxn
    refine mem_iUnion₂.mpr ⟨n, hn, mem_iUnion₂.mpr ⟨y, hy, ?_⟩⟩
    rw [mem_closedBall, Complex.isometry_ofReal.dist_eq, Real.dist_eq]
    exact hdist
  have hzero := ArithmeticDiscreteness.hausdorffMeasure_eq_zero_of_tail_covers
    (Complex.ofReal '' E) G (fun _ y => (y : ℂ)) r w s hs hr hrmono hrlim hw hwsum hcost htail
  rwa [Complex.isometry_ofReal.hausdorffMeasure_image (Or.inl hs.le)] at hzero

/-- The limsup of linearly many exponentially shrinking balls has dimension zero. -/
theorem dimH_frequently_eq_zero_of_exponential_covers
    (S : ℕ → Set ℝ) (G : ℕ → Finset ℝ) {M R b : ℝ}
    (hM : 0 < M) (hR : 0 < R) (hb : 0 < b)
    (hcard : ∀ n, ((G n).card : ℝ) ≤ M * ((n : ℝ) + 1))
    (hcover : ∀ n, ∀ x ∈ S n, ∃ y ∈ G n, |x - y| ≤ R * Real.exp (-b * n)) :
    dimH {x : ℝ | ∃ᶠ n : ℕ in atTop, x ∈ S n} = 0 := by
  apply le_antisymm ?_ bot_le
  apply dimH_le
  intro d hd
  by_contra hle
  have hd0 : 0 < (d : ℝ) := by
    have ht : (0 : ℝ≥0∞) < (d : ℝ≥0∞) := lt_of_not_ge hle
    exact_mod_cast ht
  have hz := hausdorffMeasure_frequently_eq_zero_of_exponential_covers
    S G hM hR hb hd0 hcard hcover
  exact ENNReal.zero_ne_top (hz.symm.trans hd)

#print axioms dimH_frequently_eq_zero_of_exponential_covers

end GaloisForLFunctions.InfiniteRankWeilTheory
