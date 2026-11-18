import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.HorizonCancellation
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.SmoothedLongProducts
import GaloisForLFunctions.BezoutValuationIncidence.IteratedDifferencesAndRisingFactorialPronicWeights
import GaloisForLFunctions.SignedWindowCriticality.TheContinuumCanonicalSystemIsTheJetHankelSystem

/-!
# Arbitrary-order periodic cancellation on quotient blocks

Grouping the spline horizon in blocks of length `q` reduces each product pairing
to a step-`q` sample weighted by `centeredPrimeWeight 1 j` at unit denominator.
Because `centeredPrimeWeight 1` is a fixed linear combination of zero-mean
periodic modular ramps, iterated summation by parts transfers arbitrary smoothness
away from the support endpoints without dependence on `q` in the stencil period.
-/

noncomputable section
open Finset HTGeometry
open GaloisForLFunctions.CountingHolography.Sections
open GaloisForLFunctions.BezoutValuationIncidence
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Horizon pairing of a single product `q` against the unit-stencil prime weight. -/
def unitHorizonPair (n q : ℕ) : ℝ :=
  ∑ k ∈ range (splineHorizon n + 1),
    (sampledSpline n k - sampledSpline n (k + 1)) * centeredPrimeWeight 1 (k / q)

/-- Above the common finite horizon the sampled dyadic spline vanishes. -/
theorem sampledSpline_eq_zero_after {n k : ℕ} (hn : 0 < n) (hk : splineHorizon n < k) :
    sampledSpline n k = 0 := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hscale : 4 * (n : ℝ) ^ 2 ≤ ((2 * n + 1 : ℕ) : ℝ) ^ 2 := by
    push_cast; linarith only [Nat.cast_nonneg (α := ℝ) n]
  have hcap := (mul_le_mul_of_nonneg_left hscale (Real.exp_pos 8).le).trans
    (successorSquareWindowScale_bounds n).2.2
  have htop : Real.exp (8 + Real.log 4) * (n : ℝ) ^ 2 < k := by
    rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    have h : (splineHorizon n : ℝ) < k := by exact_mod_cast hk
    dsimp only [splineHorizon] at h
    push_cast at h
    linarith only [h, hcap, Nat.cast_nonneg (α := ℝ) (windowEnd ((2 * n + 1) ^ 2 + 1))]
  unfold sampledSpline dyadicSpline
  split
  · rename_i hy
    rw [squarePrimeWeight_zero_outside hy (fun hs =>
      htop.not_ge ((div_le_iff₀ (sq_pos_of_pos hn')).mp hs.2)),
      Complex.zero_re, mul_zero, zero_div]
  · exact zero_div _

/-- Below the lower support edge `exp(-8) n²` the sampled dyadic spline vanishes. -/
theorem sampledSpline_eq_zero_before {n k : ℕ} (hn : 0 < n)
    (hk : (k : ℝ) < Real.exp (-8) * (n : ℝ) ^ 2) : sampledSpline n k = 0 := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  unfold sampledSpline dyadicSpline
  split
  · rename_i hy
    rw [squarePrimeWeight_zero_outside hy (fun hs =>
      hk.not_ge ((le_div_iff₀ (sq_pos_of_pos hn')).mp hs.1)),
      Complex.zero_re, mul_zero, zero_div]
  · exact zero_div _

private theorem sum_quotient_blocks {q : ℕ} (hq : 0 < q) (f w : ℕ → ℝ) (b : ℕ) :
    (∑ k ∈ range (q * b), (w k - w (k + 1)) * f (k / q)) =
      ∑ j ∈ range b, (w (q * j) - w (q * (j + 1))) * f j := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    have hb (i : ℕ) (hi : i ∈ range q) : (q * b + i) / q = b := by
      rw [Nat.mul_add_div hq, Nat.div_eq_of_lt (mem_range.mp hi), Nat.add_zero]
    calc (∑ i ∈ range q, (w (q * b + i) - w (q * b + i + 1)) * f ((q * b + i) / q))
        = ∑ i ∈ range q, (w (q * b + i) - w (q * b + i + 1)) * f b :=
          sum_congr rfl fun i hi => by rw [hb i hi]
      _ = (w (q * b) - w (q * (b + 1))) * f b := by
          rw [← sum_mul]
          congr 1
          have ht := sum_range_sub (fun i : ℕ => -w (q * b + i)) q
          simpa only [neg_sub_neg, Nat.add_assoc, Nat.add_zero, Nat.mul_succ] using ht

/-- Grouping modulo `q` collapses the horizon pairing onto step-`q` spline evaluations
against `centeredPrimeWeight 1` at unit denominator. -/
theorem unitHorizonPair_eq_quotient_blocks {n q b : ℕ} (hn : 0 < n) (hq : 0 < q)
    (hb : splineHorizon n < q * b) :
    unitHorizonPair n q =
      ∑ j ∈ range b,
        (sampledSpline n (q * j) - sampledSpline n (q * (j + 1))) * centeredPrimeWeight 1 j := by
  rw [← sum_quotient_blocks hq (centeredPrimeWeight 1) (sampledSpline n) b]
  unfold unitHorizonPair
  apply sum_subset
  · intro k hk
    exact mem_range.mpr (Nat.lt_of_le_of_lt (Nat.le_of_lt_succ (mem_range.mp hk)) hb)
  · intro k _ hk
    have hgt : splineHorizon n < k := by
      by_contra! hle
      exact hk (mem_range.mpr (Nat.lt_succ_of_le hle))
    rw [sampledSpline_eq_zero_after hn hgt,
      sampledSpline_eq_zero_after hn (hgt.trans (Nat.lt_succ_self k)), sub_self, zero_mul]

private theorem unit_quotient_ramp {d : ℕ} (hd : 0 < d) (j : ℕ) :
    centeredQuotient j 1 d = centeredModularRamp d j - (1 / 2 : ℝ) / d := by
  unfold centeredQuotient centeredModularRamp
  have h1 : ((j : ℝ) / d) / (1 : ℕ) = (j : ℝ) / (d : ℕ) := by simp
  rw [h1, Int.fract_div_natCast_eq_div_natCast_mod]
  field_simp
  ring

private theorem abs_centeredModularRamp_le_one (d j : ℕ) : |centeredModularRamp d j| ≤ 1 := by
  by_cases hd : d = 0
  · subst d; simp [centeredModularRamp]
  have hd0 : (0 : ℝ) < d := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hd)
  have hmod : ((j % d : ℕ) : ℝ) < d := by exact_mod_cast Nat.mod_lt j (Nat.pos_of_ne_zero hd)
  have h0 : (0 : ℝ) ≤ (j % d : ℕ) := Nat.cast_nonneg _
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.pos_of_ne_zero hd
  unfold centeredModularRamp
  rw [abs_le]
  constructor
  · rw [sub_eq_add_neg, le_iff_lt_or_eq]
    left
    have : -1 < -(((d : ℝ) - 1) / (2 * d)) := by
      rw [neg_lt_neg_iff, div_lt_one (by positivity)]; linarith
    have : 0 ≤ ((j % d : ℕ) : ℝ) / d := div_nonneg h0 hd0.le
    linarith
  · have hq : ((j % d : ℕ) : ℝ) / d ≤ 1 := (div_le_one hd0).mpr hmod.le
    have hp : 0 ≤ ((d : ℝ) - 1) / (2 * d) := div_nonneg (by linarith) (by positivity)
    linarith

private theorem centeredPrimeWeight_unit_ramps (j : ℕ) :
    centeredPrimeWeight 1 j =
      stencil 1 (fun d => centeredModularRamp d j) -
        momentRatio 1 * parityFunctional 1 (fun d => centeredModularRamp d j) +
        (2 / 63) * primeWeightMean 1 *
          parityFunctional (128 * 1 ^ 2 + 1) (fun d => centeredModularRamp d j) := by
  have he := centeredPrimeWeight_expansion (R := 1) le_rfl j 1
  rw [Nat.div_one] at he
  let f := centeredQuotient j 1
  let g := fun d : ℕ => centeredModularRamp d j
  let r := fun d : ℕ => (1 / 2 : ℝ) / d
  have hfg : ∀ d ∈ Icc 1 (128 * (128 * 1 ^ 2 + 1)), |(f d - (g d - r d))| ≤ 0 := by
    intro d hd
    simp only [f, g, r, unit_quotient_ramp (mem_Icc.mp hd).1, sub_self, abs_zero, le_rfl]
  have hs1 : stencil 1 f = stencil 1 g := by
    have h0 := abs_stencil_le (R := 1) le_rfl (fun d => f d - (g d - r d)) fun d hd =>
      hfg d (mem_Icc.mpr ⟨(mem_Icc.mp hd).1, (mem_Icc.mp hd).2.trans (by decide)⟩)
    rw [mul_zero, abs_nonpos_iff, stencil_sub, stencil_sub,
      stencil_linear_quotient (R := 1) le_rfl, sub_zero, sub_eq_zero] at h0
    exact h0
  have hp (a : ℕ) (ha : 1 ≤ a) (ha' : 128 * a ≤ 128 * (128 * 1 ^ 2 + 1)) :
      parityFunctional a f = parityFunctional a g := by
    have hpar_r : parityFunctional a r = 0 := by
      simp only [parityFunctional, r, Nat.cast_mul, Nat.cast_ofNat, div_mul_eq_div_div]
      ring
    have h0 := parityFunctional_bound (R := a) (f := fun d => f d - (g d - r d)) (M := 0)
      fun d hd => hfg d (mem_Icc.mpr ⟨ha.trans (mem_Icc.mp hd).1, (mem_Icc.mp hd).2.trans ha'⟩)
    have hlin : parityFunctional a (fun d => f d - (g d - r d)) =
        parityFunctional a f - parityFunctional a g + parityFunctional a r := by
      simp only [parityFunctional]; ring
    rw [hlin, hpar_r, add_zero, mul_zero, abs_nonpos_iff, sub_eq_zero] at h0
    exact h0
  rw [he, hs1, hp 1 le_rfl (by decide), hp (128 * 1 ^ 2 + 1) (by decide) le_rfl]

private theorem unit_stencil_ramp_sum (b : ℕ) (x : ℕ → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ d ∈ Icc 1 (128 * (128 * 1 ^ 2 + 1)),
      |∑ j ∈ range b, x j * centeredModularRamp d j| ≤ M) :
    |∑ j ∈ range b, x j * centeredPrimeWeight 1 j| ≤ 1000 * (1 + mass 1) * M := by
  let F (d : ℕ) := ∑ j ∈ range b, x j * centeredModularRamp d j
  have h₁ := abs_stencil_le (R := 1) le_rfl F fun d hd =>
    hf d (mem_Icc.mpr ⟨(mem_Icc.mp hd).1, (mem_Icc.mp hd).2.trans (by decide)⟩)
  have h₂ := parityFunctional_bound (R := 1) (f := F) fun d hd =>
    hf d (mem_Icc.mpr ⟨(mem_Icc.mp hd).1, (mem_Icc.mp hd).2.trans (by decide)⟩)
  have h₃ := parityFunctional_bound (R := 128 * 1 ^ 2 + 1) (f := F) fun d hd =>
    hf d (mem_Icc.mpr ⟨(show 1 ≤ 128 * 1 ^ 2 + 1 by decide).trans (mem_Icc.mp hd).1,
      (mem_Icc.mp hd).2⟩)
  have he : (∑ j ∈ range b, x j * centeredPrimeWeight 1 j) =
      stencil 1 F - momentRatio 1 * parityFunctional 1 F +
        (2 / 63) * primeWeightMean 1 * parityFunctional (128 * 1 ^ 2 + 1) F := by
    simp only [centeredPrimeWeight_unit_ramps, mul_sub, mul_add, sum_add_distrib, sum_sub_distrib,
      mul_left_comm (x _) (momentRatio 1), mul_left_comm (x _) ((2 / 63) * primeWeightMean 1),
      ← mul_sum, stencil_weighted_sum, commute_functional, F]
  rw [he]
  apply (abs_add_le _ _).trans ((add_le_add (abs_sub _ _) le_rfl).trans _)
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 63)]
  have hm := (abs_nonneg _).trans (abs_prefix_le_mass (R := 1) le_rfl 0)
  have h₂' := mul_le_mul (ratio_bound (R := 1) le_rfl) h₂ (abs_nonneg _) (by positivity)
  have h₃' := mul_le_mul
    (mul_le_mul_of_nonneg_left (mean_bound (R := 1) le_rfl) (by norm_num : (0 : ℝ) ≤ 2 / 63))
    h₃ (abs_nonneg _) (by positivity)
  linarith only [h₁, h₂', h₃', mul_nonneg hm hM, hM]

/-- Arbitrary-order summation by parts against `centeredPrimeWeight 1` when the
coefficient sequence vanishes at the first `s + 1` indices and from `b` onward. -/
theorem centeredPrimeWeight_periodic_iter (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : ℕ → ℝ) (b : ℕ),
      (∀ j, j < s + 1 → x j = 0) → (∀ j, b ≤ j → x j = 0) →
      |∑ j ∈ range b, x j * centeredPrimeWeight 1 j| ≤
        C * ∑ j ∈ range b, |bdiff^[s + 1] x j| := by
  let J : ℕ := 128 * (128 * 1 ^ 2 + 1)
  have hm := (abs_nonneg _).trans (abs_prefix_le_mass (R := 1) le_rfl 0)
  refine ⟨1000 * (1 + mass 1) * (2 * (J : ℝ)) ^ (s + 1), by positivity,
    fun x b hx0 hxb => ?_⟩
  let S := ∑ j ∈ range b, |bdiff^[s + 1] x j|
  have hS : 0 ≤ S := sum_nonneg fun _ _ => abs_nonneg _
  let M := (2 * (J : ℝ)) ^ (s + 1) * S
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine (unit_stencil_ramp_sum b x hM fun d hd => ?_).trans_eq (by dsimp only [M, S]; ring)
  obtain ⟨hd1, hdJ⟩ := mem_Icc.mp hd
  have hper : ∀ j, centeredModularRamp d (j + d) = centeredModularRamp d j := fun j => by
    simpa only [mul_one, add_comm] using centeredModularRamp_mul_add d 1 j
  have hzero : ∑ j ∈ range d, centeredModularRamp d j = 0 := by
    rw [sum_centeredModularRamp, centeredModularPrimitive, Nat.mod_self]
    simp
  have hiter := abs_sum_mul_periodic_le_iter hd1 s (centeredModularRamp d) 1
    hper hzero (abs_centeredModularRamp_le_one d) x b hx0 hxb
  refine hiter.trans ?_
  rw [mul_one]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.mul_le_mul_left 2 hdJ) (s + 1)) hS

/-- Iterated backward differences on a step-`h` grid match iterated forward differences
of the underlying real profile up to sign. -/
theorem bdiff_iter_sample_eq (k : ℕ) (g : ℝ → ℝ) (h : ℝ) (j : ℕ) :
    bdiff^[k] (fun i : ℕ => g ((i : ℝ) * h)) j =
      (-1 : ℝ) ^ k * (fwdDiff h)^[k] g ((j : ℝ) * h) := by
  induction k generalizing j with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    dsimp only [bdiff, fwdDiff]
    rw [ih j, ih (j + 1)]
    have he : ((j + 1 : ℕ) : ℝ) * h = (j : ℝ) * h + h := by push_cast; ring
    rw [he, pow_succ]
    ring

/-- Absolute iterated backward differences of a first grid increment equal the
`(k + 1)`-st forward difference of the real profile. -/
theorem abs_bdiff_iter_step_eq (k : ℕ) (g : ℝ → ℝ) (h : ℝ) (j : ℕ) :
    |bdiff^[k] (fun i : ℕ => g ((i : ℝ) * h) - g (((i + 1 : ℕ) : ℝ) * h)) j| =
      |(fwdDiff h)^[k + 1] g ((j : ℝ) * h)| := by
  have h1 : (fun i : ℕ => g ((i : ℝ) * h) - g (((i + 1 : ℕ) : ℝ) * h)) =
      bdiff (fun i : ℕ => g ((i : ℝ) * h)) := rfl
  rw [h1, ← Function.iterate_succ_apply, bdiff_iter_sample_eq, abs_mul, abs_pow, abs_neg,
    abs_one, one_pow, one_mul]

#print axioms unitHorizonPair_eq_quotient_blocks
#print axioms centeredPrimeWeight_periodic_iter
#print axioms abs_bdiff_iter_step_eq
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
