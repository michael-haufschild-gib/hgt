import GaloisForLFunctions.«arithmetic-positivity-theory».CompactFullWeilQuantitativeSmoothing
import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarSourceJumpDomain

/-! Explicit full-form approximation for finite translated factorial tents.
The smoothing index pays for arbitrary simultaneous growth of all pattern parameters. -/

open MeasureTheory Set Filter
open scoped BigOperators Topology CompactlySupported
open _root_.RHTower.WeilMarkovPole
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

/-- The existing arithmetic tent, translated without altering its normalization. -/
def translatedFactorialTent (n : ℕ) (t : ℝ) : C_c(ℝ, ℝ) :=
  ⟨⟨fun x => factorialSourceRight n (x+t),
    (factorialSourceRight n).continuous.comp (continuous_add_const t)⟩,
    hasCompactSupport_comp_add (factorialSourceRight n).hasCompactSupport t⟩

/-- Repeated arithmetic scales are allowed at distinct translation sites. -/
def factorialTentPattern (S : Finset ℕ) (n : ℕ → ℕ) (b t : ℕ → ℝ) : C_c(ℝ, ℝ) :=
  ∑ i ∈ S, b i • translatedFactorialTent (n i) (t i)

@[simp] theorem factorialTentPattern_apply (S : Finset ℕ) (n : ℕ → ℕ)
    (b t : ℕ → ℝ) (x : ℝ) :
    factorialTentPattern S n b t x = ∑ i ∈ S, b i*factorialSourceRight (n i) (x+t i) := by
  simp [factorialTentPattern, translatedFactorialTent]

def factorialTentPatternValueBound (S : Finset ℕ) (n : ℕ → ℕ) (b : ℕ → ℝ) : ℝ :=
  30*∑ i ∈ S, |b i| *((n i+1 : ℕ) : ℝ)

def factorialTentPatternSlopeBound (S : Finset ℕ) (n : ℕ → ℕ) (b : ℕ → ℝ) : ℝ :=
  2000*∑ i ∈ S, |b i| *((n i+1 : ℕ) : ℝ)^2

def factorialTentPatternRadius (S : Finset ℕ) (t : ℕ → ℝ) : ℝ :=
  1+∑ i ∈ S, |t i|

theorem factorialSourceRight_value_bound (n : ℕ) (x : ℝ) :
    |factorialSourceRight n x| ≤ 30*((n+1 : ℕ) : ℝ) := by
  let N := n+1
  let d := sourceFactorialWidth N
  let c := sourceFactorialCollar N
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hd : 0 < d := sourceFactorialWidth_pos hN
  have hc : 0 < c := sourceFactorialCollar_pos hN
  change |exponentialTentSource d x| ≤ 30*(N : ℝ)
  by_cases hx : x ∈ Icc 0 (2*d)
  · have he : Real.exp (3*x/2) ≤ 2 :=
      (Real.exp_le_exp.mpr (by linarith [hx.2])).trans (exp_four_sourceFactorialWidth_le_two hN)
    have ht : causalTent d x ≤ c := (causalTent_le hd.le x).trans (sourceFactorialWidth_le_collar N)
    rw [exponentialTentSource_eq, abs_div, abs_mul,
      abs_of_pos (Real.exp_pos _), abs_of_nonneg (causalTent_nonneg _ _),
      abs_of_nonneg (sq_nonneg _)]
    change Real.exp (3*x/2)*causalTent d x/c^2 ≤ _
    calc
      _ ≤ 2*c/c^2 := div_le_div_of_nonneg_right
        (mul_le_mul he ht (causalTent_nonneg _ _) (by norm_num)) (sq_nonneg c)
      _ = 2*(1/c) := by field_simp
      _ ≤ 2*(15*(N : ℝ)) := mul_le_mul_of_nonneg_left (sourceFactorialCollar_inv_le hN) (by norm_num)
      _ = _ := by ring
  · simp only [exponentialTentSource, exponentialTentDensity_zero_of_not_mem d hx, mul_zero, abs_zero]
    positivity

theorem factorialSourceRight_zero_of_one_lt_abs (n : ℕ) {x : ℝ} (hx : 1 < |x|) :
    factorialSourceRight n x = 0 := by
  have hN : (1 : ℝ) ≤ ((n+1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ n+1 by omega)
  have hd : sourceFactorialWidth (n+1) ≤ 1/2 := by
    refine (sourceFactorialWidth_bounds (by omega : 1 ≤ n+1)).2.trans ?_
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 12*((n+1 : ℕ) : ℝ))).2
    nlinarith
  have hout : x ∉ Icc 0 (2*sourceFactorialWidth (n+1)) := by
    intro hm
    rw [abs_of_nonneg hm.1] at hx
    linarith [hm.2]
  change exponentialTentSource (sourceFactorialWidth (n+1)) x = 0
  simp [exponentialTentSource, exponentialTentDensity_zero_of_not_mem _ hout]

theorem factorialTentPattern_value_bound (S : Finset ℕ) (n : ℕ → ℕ)
    (b t : ℕ → ℝ) (x : ℝ) :
    |factorialTentPattern S n b t x| ≤ factorialTentPatternValueBound S n b := by
  rw [factorialTentPattern_apply]
  calc
    _ ≤ ∑ i ∈ S, |b i*factorialSourceRight (n i) (x+t i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ S, |b i| *(30*((n i+1 : ℕ) : ℝ)) := Finset.sum_le_sum fun i _ => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (factorialSourceRight_value_bound _ _) (abs_nonneg _)
    _ = _ := by
      unfold factorialTentPatternValueBound
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intros
      ring

theorem factorialTentPattern_lipschitz_bound (S : Finset ℕ) (n : ℕ → ℕ)
    (b t : ℕ → ℝ) (x y : ℝ) :
    |factorialTentPattern S n b t x-factorialTentPattern S n b t y| ≤
      factorialTentPatternSlopeBound S n b*|x-y| := by
  rw [factorialTentPattern_apply, factorialTentPattern_apply, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ S, |b i*factorialSourceRight (n i) (x+t i)-
        b i*factorialSourceRight (n i) (y+t i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ S, |b i| *(2000*((n i+1 : ℕ) : ℝ)^2*|x-y|) := Finset.sum_le_sum fun i _ => by
      rw [← mul_sub, abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      simpa only [add_sub_add_right_eq_sub] using factorialSourceRight_abs_sub_le (n i) (x+t i) (y+t i)
    _ = _ := by
      unfold factorialTentPatternSlopeBound
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intros
      ring

theorem factorialTentPattern_zero_of_far (S : Finset ℕ) (n : ℕ → ℕ)
    (b t : ℕ → ℝ) {x : ℝ} (hx : factorialTentPatternRadius S t < |x|) :
    factorialTentPattern S n b t x = 0 := by
  rw [factorialTentPattern_apply]
  apply Finset.sum_eq_zero
  intro i hi
  have hti : |t i| ≤ ∑ j ∈ S, |t j| := Finset.single_le_sum (f := fun j : ℕ => |t j|) (fun j _ => abs_nonneg (t j)) hi
  have hdist : |x| ≤ |x+t i|+|t i| := by
    simpa only [add_sub_cancel_right] using abs_sub (x+t i) (t i)
  have hxi : 1 < |x+t i| := by
    unfold factorialTentPatternRadius at hx
    linarith
  rw [factorialSourceRight_zero_of_one_lt_abs _ hxi, mul_zero]

/-- Full-form approximation for arbitrary finite arithmetic scales, translations, and coefficients. -/
theorem factorialTentPattern_fullWeil_smoothing_error (S : Finset ℕ) (n : ℕ → ℕ)
    (b t : ℕ → ℝ) (k : ℕ) :
    |compactFullWeilEnergy (smoothCompactSource (factorialTentPattern S n b t) k)-
      compactFullWeilEnergy (factorialTentPattern S n b t)| ≤
      compactFullWeilApproximationCost (factorialTentPatternRadius S t)
        (factorialTentPatternValueBound S n b) (factorialTentPatternSlopeBound S n b)/((k : ℝ)+1) :=
  compactFullWeilEnergy_smoothing_error _ (factorialTentPattern_value_bound S n b t)
    (factorialTentPattern_lipschitz_bound S n b t)
    (by unfold factorialTentPatternRadius; positivity) (fun _ => factorialTentPattern_zero_of_far S n b t) k

/-- The accuracy index pays the entire cost, even when every pattern parameter changes. -/
def factorialTentPatternSmoothingIndex (S : Finset ℕ) (n : ℕ → ℕ) (b t : ℕ → ℝ) (q : ℕ) : ℕ :=
  ⌈((q : ℝ)+1)*compactFullWeilApproximationCost (factorialTentPatternRadius S t)
    (factorialTentPatternValueBound S n b) (factorialTentPatternSlopeBound S n b)⌉₊

theorem factorialTentPattern_joint_approximation (S : Finset ℕ) (n : ℕ → ℕ)
    (b t : ℕ → ℝ) (q : ℕ) :
    |compactFullWeilEnergy (smoothCompactSource (factorialTentPattern S n b t)
        (factorialTentPatternSmoothingIndex S n b t q))-
      compactFullWeilEnergy (factorialTentPattern S n b t)| ≤ 1/((q : ℝ)+1) := by
  refine (factorialTentPattern_fullWeil_smoothing_error S n b t _).trans ?_
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  have h := Nat.le_ceil (((q : ℝ)+1)*compactFullWeilApproximationCost (factorialTentPatternRadius S t)
    (factorialTentPatternValueBound S n b) (factorialTentPatternSlopeBound S n b))
  change _ ≤ ((factorialTentPatternSmoothingIndex S n b t q : ℕ) : ℝ) at h
  nlinarith

end GaloisForLFunctions.ArithmeticPositivityTheory
