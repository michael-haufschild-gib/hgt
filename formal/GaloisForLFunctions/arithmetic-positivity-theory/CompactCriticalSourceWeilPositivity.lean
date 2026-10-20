import GaloisForLFunctions.«arithmetic-positivity-theory».DoublyCollaredCriticalSourcePositivity
import GaloisForLFunctions.«arithmetic-positivity-theory».CompactFullWeilQuantitativeSmoothing
import GaloisForLFunctions.BiScaleUncertainty.CompactAutocorrelationPolarMoment
import GaloisForLFunctions.RHTower.ArithmeticClockFirstVariation

/-!
# Compact critical sources are Weil-positive for `ζ`

The doubly collared critical sources `g^V = χ(e^{-x}/V) σ(e^{-x} - 1) g_b` are continuous with
support in `[-log(2V), 0]` and Lipschitz. The Lipschitz bound comes from:

* the Bernoulli filter `P₀` is `9/2`-Lipschitz, since the periodic quadratic is `1/2`-Lipschitz;
* `g^V = g^V ∘ proj_{[-log 2V, 0]}`, and each of its four factors is bounded and Lipschitz on that
  interval.

So `g^V` has finite jump energy, and the compact finite-jump explicit formula applies. The real
part of the full Weil functional of `ζ` (von Mangoldt prime side) on `g^V ⋆ g̃^V` splits channel by
channel into the complete critical energy:

`Re W_Λ(g^V) = Lévy(g^V) + Ω(0) ac(0) + 2 R^V E^V - 2 P^V`.

* The prime atoms are `Λ(r) r^{-1/2} ac(log r)`.
* The polar integral `∫_{x≥0} 2cosh(x/2) ac` factors into the two half-exponential moments.
* The Lévy lintegral is the real Lévy integral, because the integrand is nonnegative and
  integrable.

Combined with block positivity of the complete energy uniformly in `V`, this gives unconditional
Weil positivity: for every high dyadic block, every truncation `V ≥ V₀` and every nonzero real
pattern, `Re W_Λ(g^V) > 0`. The supports have arbitrarily large length.
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal CompactlySupported
open _root_.Zeta23 _root_.RHTower _root_.RHTower.ArchimedeanAnomaly _root_.RHTower.ArchimedeanExactForm
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

/-! ### Lipschitz control of doubly collared sources -/

theorem abs_smoothTransition_sub_le (x y : ℝ) :
    |Real.smoothTransition x - Real.smoothTransition y| ≤ smoothTransitionSlope * |x - y| := by
  have hL : LipschitzWith ⟨smoothTransitionSlope, smoothTransitionSlope_nonneg⟩ Real.smoothTransition :=
    lipschitzWith_of_nnnorm_deriv_le ((Real.smoothTransition.contDiff (n := 1)).differentiable (by simp))
      fun x => by
        rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs]
        exact abs_deriv_smoothTransition_le x
  have h := hL.dist_le_mul x y
  rwa [Real.dist_eq, Real.dist_eq] at h

theorem abs_dyadicBernoulliFilter_sub_le (u u' : ℝ) :
    |dyadicBernoulliFilter u - dyadicBernoulliFilter u'| ≤ 9 / 2 * |u - u'| := by
  have hk (x y : ℝ) : |periodicClampedKernel x - periodicClampedKernel y| ≤ |x - y| / 2 := by
    unfold periodicClampedKernel
    rw [show -RHTower.bernoulliPeriodic x - -RHTower.bernoulliPeriodic y =
      -(RHTower.bernoulliPeriodic x - RHTower.bernoulliPeriodic y) by ring, abs_neg]
    exact RHTower.DeletionMixedRefinement.bernoulliPeriodic_lipschitz_bound x y
  unfold dyadicBernoulliFilter
  have h4 := hk (4 * u) (4 * u')
  have h2 := hk (2 * u) (2 * u')
  have h1 := hk u u'
  rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)] at h4
  rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h2
  have e : periodicClampedKernel (4 * u) / 4 - 2 * periodicClampedKernel (2 * u) + 4 * periodicClampedKernel u -
      (periodicClampedKernel (4 * u') / 4 - 2 * periodicClampedKernel (2 * u') + 4 * periodicClampedKernel u') =
      (periodicClampedKernel (4 * u) - periodicClampedKernel (4 * u')) / 4 -
        2 * (periodicClampedKernel (2 * u) - periodicClampedKernel (2 * u')) +
          4 * (periodicClampedKernel u - periodicClampedKernel u') := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  refine (add_le_add (abs_sub _ _) le_rfl).trans ?_
  rw [abs_div, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4),
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

theorem abs_factorialPhaseProfile_sub_le {N : ℕ} (hN : 1 ≤ N) (v v' : ℝ) :
    |factorialPhaseProfile N v - factorialPhaseProfile N v'| ≤
      9 / 2 * (factorialShiftedFreq N + N) * |v - v'| := by
  have hlam : 0 ≤ factorialShiftedFreq N := by
    have := (factorialShiftedFreq_sub_self_bounds hN).1
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  unfold factorialPhaseProfile
  have h1 := abs_dyadicBernoulliFilter_sub_le (factorialShiftedFreq N * v) (factorialShiftedFreq N * v')
  have h2 := abs_dyadicBernoulliFilter_sub_le ((N : ℝ) * v) ((N : ℝ) * v')
  rw [← mul_sub, abs_mul, abs_of_nonneg hlam] at h1
  rw [← mul_sub, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ N from Nat.cast_nonneg N)] at h2
  have e : dyadicBernoulliFilter (factorialShiftedFreq N * v) - dyadicBernoulliFilter (N * v) -
      (dyadicBernoulliFilter (factorialShiftedFreq N * v') - dyadicBernoulliFilter (N * v')) =
      (dyadicBernoulliFilter (factorialShiftedFreq N * v) - dyadicBernoulliFilter (factorialShiftedFreq N * v')) -
        (dyadicBernoulliFilter (N * v) - dyadicBernoulliFilter (N * v')) := by ring
  rw [e]
  refine (abs_sub _ _).trans ?_
  nlinarith

/-- Lipschitz constant `(9/2) ∑ |b_n| (λ_{n+1} + n + 1)` of a real phase combination. -/
def realPhaseLipschitz (S : Finset ℕ) (b : ℕ → ℝ) : ℝ :=
  ∑ n ∈ S, |b n| * (9 / 2 * (factorialShiftedFreq (n + 1) + ((n + 1 : ℕ) : ℝ)))

theorem abs_realPhaseCombination_sub_le (S : Finset ℕ) (b : ℕ → ℝ) (v v' : ℝ) :
    |realPhaseCombination S b v - realPhaseCombination S b v'| ≤ realPhaseLipschitz S b * |v - v'| := by
  unfold realPhaseCombination realPhaseLipschitz
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [← mul_sub, abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (abs_factorialPhaseProfile_sub_le (by omega) v v') (abs_nonneg _)

/-- Products of bounded Lipschitz functions on a set are Lipschitz there. -/
private theorem abs_mul_sub_mul_le {s : Set ℝ} {f g : ℝ → ℝ} {F G Kf Kg : ℝ} (hF : 0 ≤ F)
    (hG : 0 ≤ G) (hf : ∀ x ∈ s, |f x| ≤ F) (hg : ∀ x ∈ s, |g x| ≤ G)
    (hfL : ∀ x ∈ s, ∀ y ∈ s, |f x - f y| ≤ Kf * |x - y|)
    (hgL : ∀ x ∈ s, ∀ y ∈ s, |g x - g y| ≤ Kg * |x - y|) :
    ∀ x ∈ s, ∀ y ∈ s, |f x * g x - f y * g y| ≤ (F * Kg + G * Kf) * |x - y| := by
  intro x hx y hy
  have e : f x * g x - f y * g y = f x * (g x - g y) + g y * (f x - f y) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  calc |f x| * |g x - g y| + |g y| * |f x - f y| ≤ F * (Kg * |x - y|) + G * (Kf * |x - y|) :=
        add_le_add (mul_le_mul (hf x hx) (hgL x hx y hy) (abs_nonneg _) hF)
          (mul_le_mul (hg y hy) (hfL x hx y hy) (abs_nonneg _) hG)
    _ = (F * Kg + G * Kf) * |x - y| := by ring

private theorem abs_mul_le_of_le {s : Set ℝ} {f g : ℝ → ℝ} {F G : ℝ}
    (hf : ∀ x ∈ s, |f x| ≤ F) (hg : ∀ x ∈ s, |g x| ≤ G) : ∀ x ∈ s, |f x * g x| ≤ F * G :=
  fun x hx => by
    rw [abs_mul]
    exact mul_le_mul (hf x hx) (hg x hx) (abs_nonneg _) ((abs_nonneg _).trans (hf x hx))

/-- `|e^{-s} - e^{-t}| ≤ e^{-a} |s - t|` on `[a, ∞)`. -/
private theorem abs_exp_neg_sub_le {a s t : ℝ} (hs : a ≤ s) (ht : a ≤ t) :
    |Real.exp (-s) - Real.exp (-t)| ≤ Real.exp (-a) * |s - t| := by
  wlog hst : s ≤ t generalizing s t
  · rw [abs_sub_comm, abs_sub_comm s]; exact this ht hs (le_of_not_ge hst)
  have h1 : Real.exp (-t) ≤ Real.exp (-s) := Real.exp_le_exp.mpr (by linarith)
  rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
  have h2 : 1 - Real.exp (-(t - s)) ≤ t - s := by linarith [Real.add_one_le_exp (-(t - s))]
  have h3 : Real.exp (-t) = Real.exp (-s) * Real.exp (-(t - s)) := by rw [← Real.exp_add]; ring_nf
  have h4 : Real.exp (-s) ≤ Real.exp (-a) := Real.exp_le_exp.mpr (by linarith)
  rw [h3]
  nlinarith [Real.exp_pos (-s), Real.exp_pos (-(t - s))]

/-- `|e^{s/2} - e^{t/2}| ≤ |s - t|/2` on `(-∞, 0]`. -/
private theorem abs_exp_half_sub_le {s t : ℝ} (hs : s ≤ 0) (ht : t ≤ 0) :
    |Real.exp (s / 2) - Real.exp (t / 2)| ≤ 1 / 2 * |s - t| := by
  have h := abs_exp_neg_sub_le (a := 0) (s := -(s / 2)) (t := -(t / 2)) (by linarith) (by linarith)
  simp only [neg_neg, neg_zero, Real.exp_zero, one_mul] at h
  refine h.trans (le_of_eq ?_)
  rw [show -(s / 2) - -(t / 2) = (t - s) / 2 by ring, abs_div, abs_two, abs_sub_comm]
  ring

/-- Closed form of `g^V`: the lower collar vanishes on `x ≥ 0`, which removes the indicator. -/
theorem criticalTruncatedSource_eq (V : ℝ) (S : Finset ℕ) (b : ℕ → ℝ) (x : ℝ) :
    criticalTruncatedSource V S b x = criticalUpperCutoff (Real.exp (-x) / V) *
      (Real.smoothTransition (Real.exp (-x) - 1) *
        (Real.exp (x / 2) * realPhaseCombination S b (Real.exp (-x)))) := by
  unfold criticalTruncatedSource criticalCollaredSource criticalFactorialSource
  by_cases hx : x ≤ 0
  · rw [indicator_of_mem (show x ∈ Iic (0 : ℝ) from hx), factorialPhaseCombination_re_eq]
  · rw [indicator_of_notMem (show x ∉ Iic (0 : ℝ) from hx),
      Real.smoothTransition.zero_of_nonpos (by
        have := Real.exp_le_exp.mpr (show -x ≤ 0 by simp only [not_le] at hx; linarith)
        rw [Real.exp_zero] at this; linarith)]
    simp

theorem continuous_realPhaseCombination (S : Finset ℕ) (b : ℕ → ℝ) :
    Continuous (realPhaseCombination S b) := by
  unfold realPhaseCombination
  exact continuous_finsetSum _ fun n _ => continuous_const.mul (continuous_factorialPhaseProfile _)

theorem continuous_criticalTruncatedSource (V : ℝ) (S : Finset ℕ) (b : ℕ → ℝ) :
    Continuous (criticalTruncatedSource V S b) := by
  have he : Continuous fun x : ℝ => Real.exp (-x) := Real.continuous_exp.comp continuous_neg
  rw [show criticalTruncatedSource V S b = fun x => _ from funext (criticalTruncatedSource_eq V S b)]
  exact (continuous_criticalUpperCutoff.comp (he.div_const V)).mul
    ((Real.smoothTransition.continuous.comp (he.sub continuous_const)).mul
      ((Real.continuous_exp.comp (continuous_id.div_const 2)).mul
        ((continuous_realPhaseCombination S b).comp he)))

/-- `g^V` vanishes outside `[-log(2V), 0]`. -/
theorem criticalTruncatedSource_eq_zero {V : ℝ} (hV : 0 < V) (S : Finset ℕ) (b : ℕ → ℝ) {x : ℝ}
    (hx : x ∉ Icc (-Real.log (2 * V)) 0) : criticalTruncatedSource V S b x = 0 := by
  rw [criticalTruncatedSource_eq]
  rcases not_and_or.mp hx with h | h
  · rw [not_le] at h
    have h2 : 2 * V < Real.exp (-x) := by
      rw [← Real.exp_log (show 0 < 2 * V by positivity)]; exact Real.exp_lt_exp.mpr (by linarith)
    rw [criticalUpperCutoff_eq_zero (by rw [le_div_iff₀ hV]; linarith), zero_mul]
  · rw [not_le] at h
    rw [Real.smoothTransition.zero_of_nonpos (by
      have := Real.exp_le_exp.mpr (show -x ≤ 0 by linarith)
      rw [Real.exp_zero] at this; linarith), zero_mul, mul_zero]

theorem realPhaseLipschitz_nonneg (S : Finset ℕ) (b : ℕ → ℝ) : 0 ≤ realPhaseLipschitz S b := by
  unfold realPhaseLipschitz
  refine Finset.sum_nonneg fun n _ => mul_nonneg (abs_nonneg _) ?_
  have := (factorialShiftedFreq_sub_self_bounds (N := n + 1) (by omega)).1
  have : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have : 0 ≤ factorialShiftedFreq (n + 1) := by linarith
  positivity

theorem abs_realPhaseCombination_le_two_mul (S : Finset ℕ) (b : ℕ → ℝ) (v : ℝ) :
    |realPhaseCombination S b v| ≤ 2 * ∑ n ∈ S, |b n| := by
  unfold realPhaseCombination
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n _ => ?_
  rw [abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (abs_factorialPhaseProfile_le _ _) (abs_nonneg _)

/-- Lipschitz bound for `g^V`: with `a = -log(2V)`, `g^V = g^V ∘ proj_{[a,0]}`, and each of the four
factors is bounded and Lipschitz on `[a, 0]`. -/
theorem exists_lipschitz_criticalTruncatedSource {V : ℝ} (hV : 0 < V) (S : Finset ℕ) (b : ℕ → ℝ) :
    ∃ K : ℝ, ∀ x y, |criticalTruncatedSource V S b x - criticalTruncatedSource V S b y| ≤
      K * |x - y| := by
  set a := -Real.log (2 * V)
  set g := criticalTruncatedSource V S b
  by_cases ha : a ≤ 0
  swap
  · refine ⟨0, fun x y => ?_⟩
    have hz (z : ℝ) : g z = 0 :=
      criticalTruncatedSource_eq_zero hV S b fun h => ha (h.1.trans h.2)
    rw [hz x, hz y, sub_self, abs_zero, zero_mul]
  set s := Icc a 0
  have hea : Real.exp (-a) = 2 * V := by
    simp only [a, neg_neg]; exact Real.exp_log (by positivity)
  have hE : ∀ x ∈ s, ∀ y ∈ s, |Real.exp (-x) - Real.exp (-y)| ≤ 2 * V * |x - y| := by
    intro x hx y hy
    have := abs_exp_neg_sub_le hx.1 hy.1
    rwa [hea] at this
  have hsl := smoothTransitionSlope_nonneg
  have hA : ∀ x ∈ s, ∀ y ∈ s, |criticalUpperCutoff (Real.exp (-x) / V) -
      criticalUpperCutoff (Real.exp (-y) / V)| ≤ smoothTransitionSlope * 2 * |x - y| := by
    intro x hx y hy
    unfold criticalUpperCutoff
    rw [show 1 - Real.smoothTransition (Real.exp (-x) / V - 1) -
        (1 - Real.smoothTransition (Real.exp (-y) / V - 1)) =
        Real.smoothTransition (Real.exp (-y) / V - 1) - Real.smoothTransition (Real.exp (-x) / V - 1)
        by ring]
    refine (abs_smoothTransition_sub_le _ _).trans ?_
    rw [show Real.exp (-y) / V - 1 - (Real.exp (-x) / V - 1) = (Real.exp (-x) - Real.exp (-y)) / -V
      by field_simp; ring, abs_div, abs_neg, abs_of_pos hV]
    calc smoothTransitionSlope * (|Real.exp (-x) - Real.exp (-y)| / V) ≤
          smoothTransitionSlope * (2 * V * |x - y| / V) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (hE x hx y hy) hV.le) hsl
      _ = smoothTransitionSlope * 2 * |x - y| := by field_simp
  have hA' : ∀ x ∈ s, |criticalUpperCutoff (Real.exp (-x) / V)| ≤ 1 := fun x _ => by
    rw [abs_of_nonneg (criticalUpperCutoff_nonneg _)]; exact criticalUpperCutoff_le_one _
  have hB : ∀ x ∈ s, ∀ y ∈ s, |Real.smoothTransition (Real.exp (-x) - 1) -
      Real.smoothTransition (Real.exp (-y) - 1)| ≤ smoothTransitionSlope * (2 * V) * |x - y| := by
    intro x hx y hy
    refine (abs_smoothTransition_sub_le _ _).trans ?_
    rw [show Real.exp (-x) - 1 - (Real.exp (-y) - 1) = Real.exp (-x) - Real.exp (-y) by ring, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hE x hx y hy) hsl
  have hB' : ∀ x ∈ s, |Real.smoothTransition (Real.exp (-x) - 1)| ≤ 1 := fun x _ => by
    rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]; exact Real.smoothTransition.le_one _
  have hC : ∀ x ∈ s, ∀ y ∈ s, |Real.exp (x / 2) - Real.exp (y / 2)| ≤ 1 / 2 * |x - y| :=
    fun x hx y hy => abs_exp_half_sub_le hx.2 hy.2
  have hC' : ∀ x ∈ s, |Real.exp (x / 2)| ≤ 1 := fun x hx => by
    rw [abs_of_pos (Real.exp_pos _)]
    have := Real.exp_le_exp.mpr (show x / 2 ≤ 0 by linarith [hx.2])
    rwa [Real.exp_zero] at this
  have hD : ∀ x ∈ s, ∀ y ∈ s, |realPhaseCombination S b (Real.exp (-x)) -
      realPhaseCombination S b (Real.exp (-y))| ≤ realPhaseLipschitz S b * (2 * V) * |x - y| := by
    intro x hx y hy
    refine (abs_realPhaseCombination_sub_le S b _ _).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hE x hx y hy) (realPhaseLipschitz_nonneg S b)
  have hD' : ∀ x ∈ s, |realPhaseCombination S b (Real.exp (-x))| ≤ 2 * ∑ n ∈ S, |b n| :=
    fun x _ => abs_realPhaseCombination_le_two_mul S b _
  have hT : (0 : ℝ) ≤ 2 * ∑ n ∈ S, |b n| := by
    have := Finset.sum_nonneg fun n (_ : n ∈ S) => abs_nonneg (b n); positivity
  have hCD := abs_mul_sub_mul_le zero_le_one hT hC' hD' hC hD
  have hCD' := abs_mul_le_of_le hC' hD'
  have hBCD := abs_mul_sub_mul_le zero_le_one (by positivity) hB' hCD' hB hCD
  have hBCD' := abs_mul_le_of_le hB' hCD'
  have hABCD := abs_mul_sub_mul_le zero_le_one (by positivity) hA' hBCD' hA hBCD
  obtain ⟨K, hgs⟩ : ∃ K, ∀ x ∈ s, ∀ y ∈ s, |g x - g y| ≤ K * |x - y| :=
    ⟨_, fun x hx y hy => by simp only [g, criticalTruncatedSource_eq]; exact hABCD x hx y hy⟩
  have hz : ∀ x, x ∉ Ioo a 0 → g x = 0 := by
    intro x hx
    by_cases hxs : x ∈ s
    · rcases (show x = a ∨ x = 0 by
        rcases eq_or_lt_of_le hxs.1 with h | h
        · exact Or.inl h.symm
        · rcases eq_or_lt_of_le hxs.2 with h' | h'
          · exact Or.inr h'
          · exact absurd ⟨h, h'⟩ hx) with rfl | rfl
      · simp only [g, criticalTruncatedSource_eq, hea]
        rw [criticalUpperCutoff_eq_zero (by rw [mul_div_assoc, div_self hV.ne', mul_one]), zero_mul]
      · simp only [g, criticalTruncatedSource_eq, neg_zero, Real.exp_zero, sub_self,
          Real.smoothTransition.zero, zero_mul, mul_zero]
    · exact criticalTruncatedSource_eq_zero hV S b hxs
  have hproj : ∀ x, g x = g (Set.projIcc a 0 ha x) := by
    intro x
    by_cases hx : x ∈ Ioo a 0
    · rw [Set.projIcc_of_mem ha (Ioo_subset_Icc_self hx)]
    · rw [hz x hx, hz]
      rcases le_or_gt x a with h | h
      · rw [Set.projIcc_of_le_left ha h]; exact fun h' => lt_irrefl _ h'.1
      · have h0 : 0 ≤ x := not_lt.mp fun h0 => hx ⟨h, h0⟩
        rw [Set.projIcc_of_right_le ha h0]; exact fun h' => lt_irrefl _ h'.2
  refine ⟨max K 0, fun x y => ?_⟩
  rw [hproj x, hproj y]
  calc _ ≤ K * |(Set.projIcc a 0 ha x : ℝ) - Set.projIcc a 0 ha y| :=
        hgs _ (Set.projIcc a 0 ha x).2 _ (Set.projIcc a 0 ha y).2
    _ ≤ max K 0 * |(Set.projIcc a 0 ha x : ℝ) - Set.projIcc a 0 ha y| :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)
    _ ≤ max K 0 * |x - y| :=
        mul_le_mul_of_nonneg_left (Set.abs_projIcc_sub_projIcc ha) (le_max_right _ _)

theorem hasCompactSupport_criticalTruncatedSource {V : ℝ} (hV : 0 < V) (S : Finset ℕ) (b : ℕ → ℝ) :
    HasCompactSupport (criticalTruncatedSource V S b) :=
  HasCompactSupport.intro isCompact_Icc fun _ hx => criticalTruncatedSource_eq_zero hV S b hx

/-- The doubly collared critical source `g^V` as a compactly supported continuous test. -/
def criticalTruncatedTest {V : ℝ} (hV : 0 < V) (S : Finset ℕ) (b : ℕ → ℝ) : C_c(ℝ, ℝ) :=
  ⟨⟨criticalTruncatedSource V S b, continuous_criticalTruncatedSource V S b⟩,
    hasCompactSupport_criticalTruncatedSource hV S b⟩

theorem criticalTruncatedTest_apply {V : ℝ} (hV : 0 < V) (S : Finset ℕ) (b : ℕ → ℝ) (x : ℝ) :
    criticalTruncatedTest hV S b x = criticalTruncatedSource V S b x := rfl

private theorem sourceAutocorrelation_eq_autocorr (g : ℝ → ℝ) (x : ℝ) :
    sourceAutocorrelation g x = autocorr g x := by
  rw [← autocorr_neg]; unfold sourceAutocorrelation autocorr; simp only [sub_eq_add_neg]

/-- **Receiver identity for compact critical sources.** The real part of the full Weil functional
of `ζ` (von Mangoldt prime side) on `g^V ⋆ g̃^V` equals the complete critical energy of `g^V`:
`Re W_Λ(g^V) = Lévy(g^V) + Ω(0) ac(0) + 2 R^V E^V - 2 P^V`. -/
theorem compactFullWeilEnergy_criticalTruncatedTest {V : ℝ} (hV : 0 < V) (S : Finset ℕ)
    (b : ℕ → ℝ) :
    (compactFullWeilEnergy (criticalTruncatedTest hV S b) : EReal) =
      criticalTruncatedCompleteEnergy V S b := by
  set f := criticalTruncatedTest hV S b
  set g := criticalTruncatedSource V S b
  have hfg : (f : ℝ → ℝ) = g := rfl
  obtain ⟨K, hK⟩ := exists_lipschitz_criticalTruncatedSource hV S b
  have hJ := integrableOn_levy_of_lipschitz f (K := K) (by rw [hfg]; exact hK)
  have hW := re_weilFullFunctional_eq_of_compact_finite_jump f hJ
  have hpol := integral_polar_autocorr_eq_moments f
  have hac : ∀ x, autocorr f x = sourceAutocorrelation g x := fun x => by
    rw [sourceAutocorrelation_eq_autocorr, hfg]
  -- prime channel
  have hprime : (∑' n : ℕ, primeTerm (autocorr f) n) = criticalTruncatedPrimeEnergy V S b := by
    unfold criticalTruncatedPrimeEnergy
    refine tsum_congr fun r => ?_
    unfold primeTerm criticalTruncatedPrimeAtom primeWeight
    split_ifs
    · rw [← autocorr_neg, hfg]; unfold autocorr; simp only [sub_eq_add_neg]; rfl
    · simp
  -- polar channel
  have hR : (∫ u, Real.exp (u / 2) * f u) = criticalTruncatedPolarReadout V S b := by
    unfold criticalTruncatedPolarReadout; rw [hfg]; exact integral_congr_ae (by
      filter_upwards with u; ring)
  have hE : (∫ u, Real.exp (-(u / 2)) * f u) = criticalTruncatedPolarEndpoint V S b := by
    unfold criticalTruncatedPolarEndpoint; rw [hfg]; exact integral_congr_ae (by
      filter_upwards with u; ring)
  -- archimedean (Lévy) channel
  have hnn : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ (autocorr f 0 - autocorr f x) * archLevySinhWeight x := by
    intro x hx
    refine mul_nonneg ?_ (archLevySinhWeight_nonneg (le_of_lt hx))
    have h0 : 0 ≤ ∫ u, (f u - f (u + x)) ^ 2 := integral_nonneg fun u => sq_nonneg _
    rw [integral_sub_shift_sq f.hasCompactSupport f.continuous x] at h0
    linarith
  have hlev : (sourceLevyEnergy g : EReal) = (biScaleLevyEnergy f : ℝ) := by
    unfold sourceLevyEnergy biScaleLevyEnergy
    simp only [← hac]
    rw [← ofReal_integral_eq_lintegral_ofReal hJ
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hnn)),
      EReal.coe_ennreal_ofReal, max_eq_left (setIntegral_nonneg measurableSet_Ioi hnn)]
  unfold compactFullWeilEnergy criticalTruncatedCompleteEnergy
  rw [hW, hlev, ← EReal.coe_add, EReal.coe_eq_coe_iff]
  unfold fullPairing
  rw [hprime, hpol, hR, hE, hac 0]
  ring

/-- **Unconditional Weil positivity of compact critical sources.** There is `M₀` such that for
every `M ≥ M₀`, every truncation `V ≥ V₀`, every dyadic block at `M` and every nonzero real
pattern, the full Weil functional of `ζ` is strictly positive on `g^V ⋆ g̃^V`:
`Re W_Λ(g^V) > 0`. The supports `[-log(2V), 0]` have unbounded length. -/
theorem exists_compactFullWeilEnergy_criticalTruncatedTest_pos :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ V : ℝ, ∀ hV : 0 < V, criticalTruncationThreshold ≤ V →
      ∀ S : Finset ℕ, DyadicScaleBlock S M → ∀ b : ℕ → ℝ, (∃ n ∈ S, b n ≠ 0) →
        0 < compactFullWeilEnergy (criticalTruncatedTest hV S b) := by
  obtain ⟨M₀, h⟩ := exists_criticalTruncatedCompleteEnergy_pos
  refine ⟨M₀, fun M hM V hV hVt S hS b hb => ?_⟩
  have := h M hM V hVt S hS b hb
  rw [← compactFullWeilEnergy_criticalTruncatedTest hV] at this
  exact EReal.coe_pos.mp this

end GaloisForLFunctions.ArithmeticPositivityTheory
