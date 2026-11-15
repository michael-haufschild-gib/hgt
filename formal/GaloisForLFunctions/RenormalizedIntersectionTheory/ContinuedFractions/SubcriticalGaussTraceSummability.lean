import GaloisForLFunctions.RenormalizedIntersectionTheory.ContinuedFractions.WeightedGaussCylinderContraction

/-!
# Bounded-digit Gauss traces below exponent two

Weighted cylinder contraction absorbs a positive loss in the multiplier
exponent. The concrete exponent `2-2β/(n+1)` lies strictly between one and two.
At this exponent the full bounded-digit even-word trace family is absolutely
summable, with geometric decay in word length.
-/

open Filter Topology
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerWords
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerWordProbability
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerBoundedDigits
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerDigitPerturbation
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerWeightedCylinders

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerSubcriticalTraces
noncomputable section

/-- A concrete exponent below two for each bounded digit alphabet. -/
def exponent (n : ℕ) : ℝ := 2 - 2 * eta n

theorem exponent_bounds (n : ℕ) : 1 < exponent n ∧ exponent n < 2 := by
  have h0 := eta_pos n
  have h1 := eta_le_quarter n
  unfold exponent
  constructor <;> linarith only [h0, h1]

private theorem rpow_neg_two {x : ℝ} (hx : 0 < x) :
    x ^ (-(2 : ℝ)) = Real.exp (-(2 * Real.log x)) := by
  rw [Real.rpow_def_of_pos hx]
  congr 1
  ring

/-- The loss below exponent two is paid for by the digit-product perturbation. -/
theorem multiplier_le_weighted_probability (n k : ℕ) (a : Fin (k + 1) → Fin n) :
    wordMultiplier k (word a) ^ (-exponent n) ≤
      2 * probability (k + 1) (word a) * digitProduct n (k + 1) a := by
  have hl : 0 < wordMultiplier k (word a) :=
    zero_lt_one.trans (one_lt_wordMultiplier k (word a))
  have he : 0 ≤ 2 * eta n := mul_nonneg (by norm_num) (eta_pos n).le
  have hb : wordMultiplier k (word a) ^ (-(2 : ℝ)) ≤
      2 * probability (k + 1) (word a) := by
    rw [rpow_neg_two hl]
    simpa only [MayerCylinderEndpoints.endpoint_distance_eq_probability] using
      exp_neg_length_le_endpoint_distance k (word a)
  have hp : wordMultiplier k (word a) ^ (2 * eta n) ≤
      (∏ j : Fin (k + 1), ((a j : ℝ) + 2)) ^ (2 * eta n) :=
    Real.rpow_le_rpow hl.le (MayerWordLengthBounds.wordMultiplier_le_product k (word a)) he
  have hprod : (∏ j : Fin (k + 1), ((a j : ℝ) + 2)) ^ (2 * eta n) =
      digitProduct n (k + 1) a := by
    unfold digitProduct
    exact (Real.finsetProd_rpow _ _ (fun j _ => by positivity) _).symm
  rw [hprod] at hp
  calc
    _ = wordMultiplier k (word a) ^ (-(2 : ℝ)) *
        wordMultiplier k (word a) ^ (2 * eta n) := by
      rw [← Real.rpow_add hl]
      congr 1
      unfold exponent
      ring
    _ ≤ _ := mul_le_mul hb hp (Real.rpow_nonneg hl.le _) (by unfold probability; positivity)

/-- The total subcritical multiplier mass decays geometrically at every positive word length. -/
theorem multiplier_mass_le (n k : ℕ) :
    (∑ a : Fin (k + 1) → Fin n, wordMultiplier k (word a) ^ (-exponent n)) ≤
      2 * cutoffRate n ^ (k + 1) := by
  calc
    _ ≤ ∑ a : Fin (k + 1) → Fin n,
        2 * (probability (k + 1) (word a) * digitProduct n (k + 1) a) :=
      Finset.sum_le_sum (fun a _ => by
        simpa only [mul_assoc] using multiplier_le_weighted_probability n k a)
    _ = 2 * weightedMass n (k + 1) := by rw [← Finset.mul_sum, weightedMass]
    _ ≤ _ := mul_le_mul_of_nonneg_left (weightedMass_le n (k + 1)) (by norm_num)

private theorem multiplier_weight_nonneg (n k : ℕ) (a : Fin (k + 1) → Fin n) :
    0 ≤ wordMultiplier k (word a) ^ (-exponent n) :=
  Real.rpow_nonneg (zero_lt_one.trans (one_lt_wordMultiplier k (word a))).le _

private theorem summable_multiplier_levels (n : ℕ) :
    Summable (fun k : ℕ => ∑ a : Fin (k + 1) → Fin n,
      wordMultiplier k (word a) ^ (-exponent n)) := by
  have hr := cutoffRate_bounds n
  have habs : |cutoffRate n| < 1 := by rw [abs_of_pos hr.1]; exact hr.2
  have hs : Summable (fun k : ℕ => (2 * cutoffRate n) * cutoffRate n ^ k) :=
    (summable_geometric_of_abs_lt_one habs).mul_left (2 * cutoffRate n)
  apply hs.of_nonneg_of_le (fun k => Finset.sum_nonneg
    (fun a _ => multiplier_weight_nonneg n k a))
  intro k
  calc
    _ ≤ 2 * cutoffRate n ^ (k + 1) := multiplier_mass_le n k
    _ = (2 * cutoffRate n) * cutoffRate n ^ k := by rw [pow_succ]; ring

/-- The complete bounded-digit multiplier family is summable below exponent two. -/
theorem summable_multipliers (n : ℕ) :
    Summable (fun p : Σ k : ℕ, Fin (k + 1) → Fin n =>
      wordMultiplier p.1 (word p.2) ^ (-exponent n)) := by
  apply (summable_sigma_of_nonneg
    (f := fun p : Σ k : ℕ, Fin (k + 1) → Fin n =>
      wordMultiplier p.1 (word p.2) ^ (-exponent n))
    (fun p => multiplier_weight_nonneg n p.1 p.2)).mpr
  refine ⟨fun k => (hasSum_fintype
    (fun a : Fin (k + 1) → Fin n => wordMultiplier k (word a) ^ (-exponent n))).summable, ?_⟩
  simpa only [tsum_fintype] using summable_multiplier_levels n

/-- Actual even-word traces retain geometric mass decay at the subcritical exponent. -/
theorem even_trace_mass_le (n k : ℕ) :
    (∑ a : Fin (2 * k + 2) → Fin n,
      ‖wordTrace (exponent n : ℂ) (2 * k + 1) (word a)‖) ≤
        (8 / 3 : ℝ) * cutoffRate n ^ (2 * k + 2) := by
  calc
    _ ≤ ∑ a : Fin (2 * k + 2) → Fin n,
        (4 / 3 : ℝ) * wordMultiplier (2 * k + 1) (word a) ^ (-exponent n) :=
      Finset.sum_le_sum (fun a _ => by
        simpa only [Complex.ofReal_re] using norm_even_wordTrace_le (w := (exponent n : ℂ)) k (word a))
    _ = (4 / 3 : ℝ) * ∑ a : Fin (2 * k + 2) → Fin n,
        wordMultiplier (2 * k + 1) (word a) ^ (-exponent n) := (Finset.mul_sum _ _ _).symm
    _ ≤ (4 / 3 : ℝ) * (2 * cutoffRate n ^ (2 * k + 2)) :=
      mul_le_mul_of_nonneg_left (multiplier_mass_le n (2 * k + 1)) (by norm_num)
    _ = _ := by ring

/-- Absolute summability over both word length and every word in the bounded alphabet. -/
theorem summable_even_traces (n : ℕ) :
    Summable (fun p : Σ k : ℕ, Fin (2 * k + 2) → Fin n =>
      ‖wordTrace (exponent n : ℂ) (2 * p.1 + 1) (word p.2)‖) := by
  have hr := cutoffRate_bounds n
  have hr2 : |cutoffRate n ^ 2| < 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    have hp := mul_pos (sub_pos.mpr hr.2) (add_pos zero_lt_one hr.1)
    nlinarith only [hp]
  have hs := (summable_geometric_of_abs_lt_one hr2).mul_left
    ((8 / 3 : ℝ) * cutoffRate n ^ 2)
  have hlength : Summable (fun k : ℕ =>
      ∑ a : Fin (2 * k + 2) → Fin n, ‖wordTrace (exponent n : ℂ) (2 * k + 1) (word a)‖) := by
    apply hs.of_nonneg_of_le (fun k => Finset.sum_nonneg (fun a _ => norm_nonneg _))
    intro k
    calc
      _ ≤ (8 / 3 : ℝ) * cutoffRate n ^ (2 * k + 2) := even_trace_mass_le n k
      _ = ((8 / 3 : ℝ) * cutoffRate n ^ 2) * (cutoffRate n ^ 2) ^ k := by
        rw [pow_add, pow_mul]
        ring
  apply (summable_sigma_of_nonneg (fun p => norm_nonneg _)).mpr
  refine ⟨fun k => (hasSum_fintype _).summable, ?_⟩
  simpa only [tsum_fintype] using hlength

/-- The actual even-word logarithm at spectral parameter one converges below exponent two
after restricting the digit alphabet. -/
theorem summable_unit_evenWordSeries (n : ℕ) :
    Summable (fun p : Σ k : ℕ, Fin (2 * k + 2) → Fin n =>
      ‖(1 : ℂ) ^ (2 * p.1 + 2) / ((p.1 + 1 : ℕ) : ℂ) *
        wordTrace (exponent n : ℂ) (2 * p.1 + 1) (word p.2)‖) := by
  apply (summable_even_traces n).of_nonneg_of_le (fun p => norm_nonneg _)
  intro p
  have hden : (1 : ℝ) ≤ ((p.1 + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos p.1
  have hcoef : ‖(1 : ℂ) ^ (2 * p.1 + 2) / ((p.1 + 1 : ℕ) : ℂ)‖ ≤ 1 := by
    rw [one_pow, norm_div, norm_one, Complex.norm_natCast]
    exact div_le_self (by norm_num) hden
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) hcoef

/-- Every finite alphabet admits an absolute-convergence exponent strictly between one and two. -/
theorem exists_subcritical_exponent (n : ℕ) : ∃ s : ℝ, 1 < s ∧ s < 2 ∧
    Summable (fun p : Σ k : ℕ, Fin (2 * k + 2) → Fin n =>
      ‖wordTrace (s : ℂ) (2 * p.1 + 1) (word p.2)‖) :=
  ⟨exponent n, (exponent_bounds n).1, (exponent_bounds n).2, summable_even_traces n⟩

/-- The geometric length of an actual expanding Gauss word. -/
def wordLength (k : ℕ) (a : Word (k + 1)) : ℝ := 2 * Real.log (wordMultiplier k a)

theorem wordLength_pos (k : ℕ) (a : Word (k + 1)) : 0 < wordLength k a :=
  mul_pos (by norm_num) (Real.log_pos (one_lt_wordMultiplier k a))

/-- The positive exponent margin absorbs the length factor in the geodesic weight. -/
theorem length_weight_le (n k : ℕ) (a : Word (k + 1)) :
    wordLength k a * Real.exp (-wordLength k a) ≤
      wordMultiplier k a ^ (-exponent n) / eta n := by
  have h := Real.add_one_le_exp (eta n * wordLength k a)
  have hlin : eta n * wordLength k a ≤ Real.exp (eta n * wordLength k a) := by
    linarith only [h]
  have hm := mul_le_mul_of_nonneg_right hlin (Real.exp_pos (-wordLength k a)).le
  have he : Real.exp (eta n * wordLength k a) * Real.exp (-wordLength k a) =
      wordMultiplier k a ^ (-exponent n) := by
    rw [← Real.exp_add, Real.rpow_def_of_pos
      (zero_lt_one.trans (one_lt_wordMultiplier k a))]
    congr 1
    unfold wordLength exponent
    ring
  rw [he] at hm
  apply (le_div_iff₀ (eta_pos n)).mpr
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hm

/-- Length-weighted geodesic mass has the same geometric word-length decay. -/
theorem length_mass_le (n k : ℕ) :
    (∑ a : Fin (k + 1) → Fin n,
      wordLength k (word a) * Real.exp (-wordLength k (word a))) ≤
        (2 / eta n) * cutoffRate n ^ (k + 1) := by
  calc
    _ ≤ ∑ a : Fin (k + 1) → Fin n,
        wordMultiplier k (word a) ^ (-exponent n) / eta n :=
      Finset.sum_le_sum (fun a _ => length_weight_le n k (word a))
    _ = (∑ a : Fin (k + 1) → Fin n,
        wordMultiplier k (word a) ^ (-exponent n)) / eta n := (Finset.sum_div _ _ _).symm
    _ ≤ (2 * cutoffRate n ^ (k + 1)) / eta n :=
      div_le_div_of_nonneg_right (multiplier_mass_le n k) (eta_pos n).le
    _ = _ := by ring

/-- The full bounded-digit family of length-weighted geodesic contributions is summable. -/
theorem summable_length_weights (n : ℕ) :
    Summable (fun p : Σ k : ℕ, Fin (k + 1) → Fin n =>
      wordLength p.1 (word p.2) * Real.exp (-wordLength p.1 (word p.2))) := by
  exact ((summable_multipliers n).div_const (eta n)).of_nonneg_of_le
    (fun p => mul_nonneg (wordLength_pos p.1 (word p.2)).le (Real.exp_pos _).le)
    (fun p => length_weight_le n p.1 (word p.2))

/-- Bounded-digit words of a fixed positive length whose geometric length is at most `T`. -/
def shortWords (n k : ℕ) (T : ℝ) : Finset (Fin (k + 1) → Fin n) := by
  classical
  exact Finset.univ.filter (fun a => wordLength k (word a) ≤ T)

/-- The weighted cylinder estimate bounds the number of short actual Gauss words. -/
theorem card_shortWords_le (n k : ℕ) (T : ℝ) :
    ((shortWords n k T).card : ℝ) ≤
      2 * cutoffRate n ^ (k + 1) * Real.exp ((1 - eta n) * T) := by
  classical
  have hs : 0 ≤ 1 - eta n := by linarith only [eta_le_quarter n]
  have hpoint (a : Fin (k + 1) → Fin n) (ha : a ∈ shortWords n k T) :
      (1 : ℝ) ≤ Real.exp ((1 - eta n) * T) *
        wordMultiplier k (word a) ^ (-exponent n) := by
    have hlen : wordLength k (word a) ≤ T := (Finset.mem_filter.mp ha).2
    have he : wordMultiplier k (word a) ^ (-exponent n) =
        Real.exp (-(1 - eta n) * wordLength k (word a)) := by
      rw [Real.rpow_def_of_pos (zero_lt_one.trans (one_lt_wordMultiplier k (word a)))]
      congr 1
      unfold exponent wordLength
      ring
    rw [he, ← Real.exp_add, Real.one_le_exp_iff]
    have h := mul_nonneg hs (sub_nonneg.mpr hlen)
    nlinarith only [h]
  calc
    _ = ∑ a ∈ shortWords n k T, (1 : ℝ) := by simp
    _ ≤ ∑ a ∈ shortWords n k T, Real.exp ((1 - eta n) * T) *
        wordMultiplier k (word a) ^ (-exponent n) := Finset.sum_le_sum hpoint
    _ ≤ ∑ a : Fin (k + 1) → Fin n, Real.exp ((1 - eta n) * T) *
        wordMultiplier k (word a) ^ (-exponent n) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun a _ _ => mul_nonneg (Real.exp_pos _).le
          (Real.rpow_nonneg (zero_lt_one.trans (one_lt_wordMultiplier k (word a))).le _))
    _ = Real.exp ((1 - eta n) * T) *
        ∑ a : Fin (k + 1) → Fin n, wordMultiplier k (word a) ^ (-exponent n) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ Real.exp ((1 - eta n) * T) * (2 * cutoffRate n ^ (k + 1)) :=
      mul_le_mul_of_nonneg_left (multiplier_mass_le n k) (Real.exp_pos _).le
    _ = _ := by ring

#print axioms multiplier_le_weighted_probability
#print axioms multiplier_mass_le
#print axioms summable_multipliers
#print axioms even_trace_mass_le
#print axioms summable_even_traces
#print axioms summable_unit_evenWordSeries
#print axioms exists_subcritical_exponent
#print axioms length_mass_le
#print axioms summable_length_weights
#print axioms card_shortWords_le

end
end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerSubcriticalTraces
