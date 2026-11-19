import GaloisForLFunctions.ArithmeticPositiveDuality.TheLiouvilleLawForTwoCommutingTranslations
import GaloisForLFunctions.RHTower.TwoDilationDivisorMetric
import GaloisForLFunctions.RHTower.WeilLagFunctionDense
import Mathlib.NumberTheory.Chebyshev

/-!
# The harmonic nullspace of the prime midpoint

Division by scale turns the homogeneous midpoint equation into a two-point
walk of weights 1/3 and 2/3. Its two translations generate the same subgroup
as log 2 and log 3. The only bounded continuous normalized profiles invisible
at every scale are constants.
-/

noncomputable section
open GaloisForLFunctions.ArithmeticPositiveDuality.TranslationLaw
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private def lowStep : ℝ := Real.log 2 - Real.log 3
private def highStep : ℝ := 2*Real.log 2 - Real.log 3

/-- Complete bounded continuous harmonic nullspace on the logarithmic scale. -/
theorem midpoint_harmonic_iff_constant (f : ℝ → ℝ) (hc : Continuous f)
    (hbd : ∃ M : ℝ, ∀ x, f x^2 ≤ M) :
    (∀ x, f x = f (x + (Real.log 2-Real.log 3))/3 +
      2*f (x + (2*Real.log 2-Real.log 3))/3) ↔ ∀ x, f x = f 0 := by
  constructor
  · intro h
    have hh : mean (1/3) lowStep highStep f = f := by
      funext x
      unfold mean lowStep highStep
      linarith only [h x]
    have hw := (bounded_harmonic_iff (1/3) (by constructor <;> norm_num) lowStep highStep f hbd).mp hh
    let F := fun t => (f t : ℂ)
    let P := _root_.RHTower.periodAddSubgroup F
    have ha : lowStep ∈ P := fun x => congrArg Complex.ofReal (hw x).1
    have hb : highStep ∈ P := fun x => congrArg Complex.ofReal (hw x).2
    have h₂ : Real.log 2 ∈ P := by
      have hh := P.sub_mem hb ha
      rwa [show highStep-lowStep=Real.log 2 by unfold highStep lowStep; ring] at hh
    have h₃ : Real.log 3 ∈ P := by
      have hh := P.sub_mem h₂ ha
      rwa [show Real.log 2-lowStep=Real.log 3 by unfold lowStep; ring] at hh
    have hle : AddSubgroup.closure {Real.log (2:ℝ), Real.log 3} ≤ P := by
      rw [AddSubgroup.closure_le]
      intro t ht
      rcases Set.mem_insert_iff.mp ht with rfl | ht
      · exact h₂
      · exact Set.mem_singleton_iff.mp ht ▸ h₃
    have hd := _root_.RHTower.dense_addSubgroup_log_primes Nat.prime_two Nat.prime_three (by norm_num)
    intro x
    exact Complex.ofReal_injective (_root_.RHTower.eq_of_continuous_of_dense_periods
      (Complex.continuous_ofReal.comp hc) (hd.mono hle) x 0)
  · intro h x
    rw [h x, h (x+_), h (x+_)]
    ring

/-- A continuous price bounded by a linear function on the entire positive axis
has zero midpoint at every dilation precisely when it is linear. -/
theorem linear_growth_midpoint_kernel (F : ℝ → ℝ) (hc : ContinuousOn F (Set.Ioi 0))
    (hbd : ∃ M : ℝ, ∀ y : ℝ, 0 < y → (F y/y)^2 ≤ M) :
    (∀ y : ℝ, 0 < y → 2*F (3*y) = F (2*y) + F (4*y)) ↔
      ∀ y : ℝ, 0 < y → F y = y*F 1 := by
  let f := fun x => F (Real.exp x)/Real.exp x
  have hf : Continuous f :=
    (hc.comp_continuous Real.continuous_exp (fun t => Real.exp_pos t)).div
      Real.continuous_exp (fun x => (Real.exp_pos x).ne')
  obtain ⟨M,hM⟩ := hbd
  have hscale (x : ℝ) :
      Real.exp (x+(Real.log 2-Real.log 3)) = 2*Real.exp x/3 ∧
      Real.exp (x+(2*Real.log 2-Real.log 3)) = 4*Real.exp x/3 := by
    rw [show 2*Real.log 2=Real.log 2+Real.log 2 by ring]
    simp only [Real.exp_add, Real.exp_sub, Real.exp_log (by norm_num : (0:ℝ)<2),
      Real.exp_log (by norm_num : (0:ℝ)<3)]
    constructor <;> ring
  constructor
  · intro h
    have hh (x : ℝ) := h (Real.exp x/3) (by positivity)
    have harm (x : ℝ) : f x = f (x + (Real.log 2-Real.log 3))/3 +
        2*f (x + (2*Real.log 2-Real.log 3))/3 := by
      dsimp only [f]
      rw [(hscale x).1,(hscale x).2]
      have he := hh x
      rw [show 3*(Real.exp x/3)=Real.exp x by ring, ← mul_div_assoc, ← mul_div_assoc] at he
      field_simp [(Real.exp_pos x).ne']
      linarith only [he]
    have hz := (midpoint_harmonic_iff_constant f hf ⟨M,fun x => hM _ (Real.exp_pos x)⟩).mp harm
    intro y hy
    have he := hz (Real.log y)
    simp only [f, Real.exp_log hy, Real.exp_zero, div_one] at he
    simpa only [mul_comm] using (div_eq_iff hy.ne').mp he
  · intro h y hy
    rw [h _ (by positivity : 0<3*y), h _ (by positivity : 0<2*y), h _ (by positivity : 0<4*y)]
    ring

/-- Adding the same continuous perturbation to the prime counting price at
every positive scale leaves all real midpoint prices invariant exactly for
linear perturbations. -/
theorem prime_midpoint_invisible_perturbation (F : ℝ → ℝ) (hc : ContinuousOn F (Set.Ioi 0))
    (hbd : ∃ M : ℝ, ∀ y : ℝ, 0 < y → (F y/y)^2 ≤ M) :
    (∀ y : ℝ, 0 < y →
      2*(Chebyshev.theta (3*y)+F (3*y))-(Chebyshev.theta (2*y)+F (2*y))-
        (Chebyshev.theta (4*y)+F (4*y)) =
      2*Chebyshev.theta (3*y)-Chebyshev.theta (2*y)-Chebyshev.theta (4*y)) ↔
      ∀ y : ℝ, 0 < y → F y = y*F 1 := by
  rw [← linear_growth_midpoint_kernel F hc hbd]
  constructor <;> intro h y hy <;> linarith only [h y hy]

/-- Unit tent on a single gap of the integer sampling grid. -/
private def gapTent (j : ℕ) (y : ℝ) : ℝ :=
  2*max 0 (min (y-j) ((j:ℝ)+1-y))

private lemma gapTent_at_integer (j m : ℕ) : gapTent j m = 0 := by
  unfold gapTent
  rw [max_eq_left, mul_zero]
  rcases le_or_gt m j with h | h
  · exact (min_le_left _ _).trans (sub_nonpos.mpr (Nat.cast_le.mpr h))
  · exact (min_le_right _ _).trans (sub_nonpos.mpr (by exact_mod_cast h))

private lemma gapTent_cardinal (j m : ℕ) :
    gapTent j ((m:ℝ)+1/2) = if j=m then 1 else 0 := by
  by_cases h : j=m
  · subst m
    simp [gapTent, show (j:ℝ)+1/2-j=1/2 by ring,
      show (j:ℝ)+1-(j+1/2)=1/2 by ring, max_eq_right (by norm_num : (0:ℝ)≤1/2)]
  · rw [if_neg h, gapTent, max_eq_left, mul_zero]
    rcases lt_or_gt_of_ne h with hl | hl
    · have hd : (j:ℝ)+1 ≤ m := by exact_mod_cast hl
      exact (min_le_right _ _).trans (by linarith only [hd])
    · have hd : (m:ℝ)+1 ≤ j := by exact_mod_cast hl
      exact (min_le_left _ _).trans (by linarith only [hd])

/-- Integer midpoint observations allow arbitrary, independently chosen values
at any finite collection of half-integers, even for a continuous perturbation
vanishing at every integer. -/
theorem integer_midpoint_hidden_interpolation (S : Finset ℕ) (v : ℕ → ℝ) :
    ∃ F : ℝ → ℝ, Continuous F ∧ (∀ m : ℕ, F m=0) ∧
      (∀ j ∈ S, F ((j:ℝ)+1/2)=v j) ∧
      ∀ n : ℕ, 2*F (3*n:ℕ)-F (2*n:ℕ)-F (4*n:ℕ)=0 := by
  let F := fun y : ℝ => ∑ j ∈ S, v j * gapTent j y
  have hgrid (m : ℕ) : F m = 0 := by simp only [F, gapTent_at_integer, mul_zero, Finset.sum_const_zero]
  refine ⟨F, ?_, hgrid, ?_, fun n => by rw [hgrid,hgrid,hgrid]; ring⟩
  · unfold F gapTent
    fun_prop
  · intro j hj
    simp [F, gapTent_cardinal, mul_ite, hj]

#print axioms integer_midpoint_hidden_interpolation
#print axioms midpoint_harmonic_iff_constant
#print axioms linear_growth_midpoint_kernel

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
