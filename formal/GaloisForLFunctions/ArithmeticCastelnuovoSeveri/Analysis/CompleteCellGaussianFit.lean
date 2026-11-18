import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.CompleteCellVariancePayment
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.IntervalVarianceRemainder
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.PolePreservingSmoothing

/-!
# Gaussian moment matching for complete Haar pairs

Darijani–Soufian–Beyerer, arXiv:2611.16022, Proposition 2.18, minimize
Gaussian cross entropy by matching moments. Uniform sampling of a complete
logarithmic cell gives a two-point law on its profile values. Its Gaussian
log score has the same optimizer, with an explicit variance in the Haar
coordinates. For zero detail the score is unbounded below.
-/

noncomputable section
open Set MeasureTheory
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
open BiarithmeticGaugeGeometry IntervalVariance

/-- Twice the expected Gaussian negative log likelihood, with the universal
constant log(2π) removed. The second parameter is the logarithm of the variance. -/
def pairScore (q d : ℕ → ℝ) (X a : ℕ) (m l : ℝ) : ℝ :=
  l + Real.exp (-l) *
    intervalMean (Real.log ((2*a : ℕ) : ℝ)) (Real.log ((2*a+2 : ℕ) : ℝ))
      (fun x => (completePairProfile q d X x-m)^2)

/-- Variance under normalized length measure, rather than the integrated variance. -/
def pairVariance (d : ℕ → ℝ) (a : ℕ) : ℝ := haarMass a * d a^2 / logCellWidth a

private theorem score_formula (q d : ℕ → ℝ) {X a : ℕ} (ha : 1 ≤ a) (hX : a ≤ X) (m l : ℝ) :
    pairScore q d X a m l = l + Real.exp (-l)*(pairVariance d a + (q a-m)^2) := by
  have hw := logCellWidth_pos ha
  have hab : Real.log ((2*a:ℕ):ℝ) < Real.log ((2*a+2:ℕ):ℝ) := by
    apply sub_pos.mp
    rwa [haarPairWidth ha]
  have hf := memLp_compact_bv (completePairProfile_bv q d X) (completePairProfile_compact q d X)
  unfold pairScore intervalMean
  rw [integral_sub_const_sq_eq_variance hab (hf.mono_measure Measure.restrict_le_self) m,
    intervalVariance_completePairProfile q d ha hX, intervalMean_completePairProfile q d ha hX,
    haarPairWidth ha, add_div, mul_div_cancel_left₀ _ hw.ne']
  rfl

/-- Exact loss from a displaced mean and a misspecified log variance, for
every complete cell and every independent choice of its two coefficients. -/
theorem pairScore_moments (q d : ℕ → ℝ) (i k : ℕ) (m l : ℝ) :
    pairScore q d (i+1+k) (i+1) m l =
      l + Real.exp (-l)*(pairVariance d (i+1) + (q (i+1)-m)^2) :=
  score_formula q d (by omega) (by omega) m l

/-- Separates the location error and the scale error after moment matching. -/
private theorem score_gap {v : ℝ} (hv : 0 < v) (b m l : ℝ) :
    l + Real.exp (-l)*(v+(b-m)^2) - (Real.log v+1) =
      (Real.exp (Real.log v-l) - 1 - (Real.log v-l)) + Real.exp (-l)*(b-m)^2 := by
  rw [sub_eq_add_neg (Real.log v) l, Real.exp_add, Real.exp_log hv]
  ring

private theorem scale_gap_eq_zero (x : ℝ) : Real.exp x-1-x = 0 ↔ x = 0 := by
  constructor
  · intro h
    by_contra hn
    linarith only [Real.add_one_lt_exp hn,h]
  · rintro rfl
    rw [Real.exp_zero]
    ring

private theorem var_pos_iff (d : ℕ → ℝ) (i : ℕ) :
    0 < pairVariance d (i+1) ↔ d (i+1) ≠ 0 := by
  have hi : 1 ≤ i+1 := by omega
  rw [pairVariance, div_pos_iff_of_pos_right (logCellWidth_pos hi),
    mul_pos_iff_of_pos_left (haarMass_pos hi), sq_pos_iff]

/-- A global score minimum exists exactly on cells with nonzero detail.
The prediction and the variance are uniquely identifiable there. -/
theorem pairScore_minimizer_iff (q d : ℕ → ℝ) (i k : ℕ) (m l : ℝ) :
    (∀ b s, pairScore q d (i+1+k) (i+1) m l ≤ pairScore q d (i+1+k) (i+1) b s) ↔
      d (i+1) ≠ 0 ∧ m = q (i+1) ∧ l = Real.log (pairVariance d (i+1)) := by
  simp only [pairScore_moments]
  let v := pairVariance d (i+1)
  let μ := q (i+1)
  change (∀ b s : ℝ, l + Real.exp (-l)*(v+(μ-m)^2) ≤ s + Real.exp (-s)*(v+(μ-b)^2)) ↔
    d (i+1) ≠ 0 ∧ m = μ ∧ l = Real.log v
  by_cases hd : d (i+1) = 0
  · have hv : v = 0 := by simp [v,pairVariance,hd]
    refine ⟨fun h => ?_, fun h => (h.1 hd).elim⟩
    have h' := h μ (l-1)
    rw [hv,sub_self,zero_pow (by norm_num : 2 ≠ 0),add_zero,mul_zero,add_zero,zero_add] at h'
    linarith only [h', mul_nonneg (Real.exp_pos (-l)).le (sq_nonneg (μ-m))]
  have hv : 0 < v := (var_pos_iff d i).mpr hd
  have hmin (b s : ℝ) : Real.log v+1 ≤ s+Real.exp (-s)*(v+(μ-b)^2) := by
    have h := score_gap hv μ b s
    linarith only [h, Real.add_one_le_exp (Real.log v-s),
      mul_nonneg (Real.exp_pos (-s)).le (sq_nonneg (μ-b))]
  have hbest : Real.log v+Real.exp (-Real.log v)*(v+(μ-μ)^2) = Real.log v+1 := by
    simp [Real.exp_neg,Real.exp_log hv,hv.ne']
  constructor
  · intro h
    have hle := h μ (Real.log v)
    rw [hbest] at hle
    have hg := score_gap hv μ m l
    have he : Real.exp (Real.log v-l)-1-(Real.log v-l) = 0 := by
      linarith only [hg,hle,Real.add_one_le_exp (Real.log v-l),
        mul_nonneg (Real.exp_pos (-l)).le (sq_nonneg (μ-m))]
    have hl := (scale_gap_eq_zero _).mp he
    have hzero : Real.exp (-l)*(μ-m)^2 = 0 := by
      linarith only [hg,he,hle,mul_nonneg (Real.exp_pos (-l)).le (sq_nonneg (μ-m))]
    exact ⟨hd,(sub_eq_zero.mp (sq_eq_zero_iff.mp ((mul_eq_zero.mp hzero).resolve_left
      (Real.exp_ne_zero _)))).symm,(sub_eq_zero.mp hl).symm⟩
  · rintro ⟨_,rfl,rfl⟩ b s
    rw [hbest]
    exact hmin b s

/-- At vanishing detail the correctly centered score takes every real value. -/
theorem constant_pairScore_surjective (q : ℕ → ℝ) (i k : ℕ) :
    Function.Surjective (pairScore q (fun _ => 0) (i+1+k) (i+1) (q (i+1))) := by
  intro y
  exact ⟨y, by simp [pairScore_moments,pairVariance]⟩

/-- Gaussian readouts identify exactly the local mean and squared detail. -/
theorem pairScore_identifies_iff (q d q' d' : ℕ → ℝ) (i k : ℕ) :
    (∀ m l, pairScore q d (i+1+k) (i+1) m l = pairScore q' d' (i+1+k) (i+1) m l) ↔
      q (i+1) = q' (i+1) ∧ d (i+1)^2 = d' (i+1)^2 := by
  simp only [pairScore_moments]
  constructor
  · intro h
    have h0 := h 0 0
    have h1 := h 1 0
    simp only [neg_zero, Real.exp_zero, one_mul, zero_add, sub_zero] at h0 h1
    have he : q (i+1) = q' (i+1) := by linarith only [h0,h1]
    rw [he,add_left_inj] at h0
    have hi : 1 ≤ i+1 := by omega
    unfold pairVariance at h0
    exact ⟨he, mul_left_cancel₀ (haarMass_pos hi).ne'
      ((div_left_inj' (logCellWidth_pos hi).ne').mp h0)⟩
  · rintro ⟨hq,hd⟩ m l
    simp only [pairVariance,hq,hd]

#print axioms pairScore_moments
#print axioms pairScore_minimizer_iff
#print axioms constant_pairScore_surjective
#print axioms pairScore_identifies_iff
end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
