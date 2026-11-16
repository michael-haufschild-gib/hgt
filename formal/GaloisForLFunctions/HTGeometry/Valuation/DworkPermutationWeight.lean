import GaloisForLFunctions.HTGeometry.Valuation.ConcaveDworkWeight
import GaloisForLFunctions.HTGeometry.CauchyBinet

/-!
# Dwork weights along determinant permutations

For any nonnegative row labels, every permutation of columns pays at least
the sum of the exact scale increments. Concavity bounds each transition;
column weights then cancel in the permutation sum. This is the weight
inequality behind the row estimate in a Dwork determinant expansion.
-/


noncomputable section
open scoped NNReal BigOperators
namespace GaloisForLFunctions.HTGeometry

/-- Nonnegative transition cost between a dilated row label and a column label. -/
def dworkTransitionWeight (p : ℕ) (x y : ℝ≥0) : ℝ :=
  dworkWeight p (max (((p : ℝ) + 2) * x - y) 0)

/-- A transition pays at least the difference of the endpoint weights. -/
theorem dworkTransitionWeight_add (p : ℕ) (x y : ℝ≥0) :
    dworkWeight p (((p : ℝ) + 2) * x) ≤
      dworkTransitionWeight p x y + dworkWeight p y := by
  have hmax : 0 ≤ max (((p : ℝ) + 2) * x - y) 0 := le_max_right _ _
  have hle : ((p : ℝ) + 2) * x ≤ max (((p : ℝ) + 2) * x - y) 0 + y := by
    linarith only [le_max_left (((p : ℝ) + 2) * x - y) 0]
  have hmono := monotoneOn_dworkWeight p
    (show ((p : ℝ) + 2) * x ∈ Set.Ici 0 from by
      change (0 : ℝ) ≤ ((p : ℝ) + 2) * x
      positivity)
    (show max (((p : ℝ) + 2) * x - y) 0 + y ∈ Set.Ici 0 from by
      change (0 : ℝ) ≤ max (((p : ℝ) + 2) * x - y) 0 + y
      exact add_nonneg hmax y.property) hle
  exact hmono.trans (dworkWeight_subadd p (NNReal.mk _ hmax) y)

/-- Column potentials cancel under every permutation, leaving a uniform row bound. -/
theorem dworkTransitionWeight_perm_sum_lower {ι : Type*} [Fintype ι]
    (p : ℕ) (x : ι → ℝ≥0) (σ : Equiv.Perm ι) :
    (∑ i, min (((p : ℝ) + 1) * x i) 1) ≤
      ∑ i, dworkTransitionWeight p (x i) (x (σ i)) := by
  classical
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => dworkTransitionWeight_add p (x i) (x (σ i)))
  rw [Finset.sum_add_distrib, Equiv.sum_comp σ (fun i => dworkWeight p (x i))] at h
  calc
    _ = ∑ i, (dworkWeight p (((p : ℝ) + 2) * x i) - dworkWeight p (x i)) :=
      Finset.sum_congr rfl fun i _ => (dworkWeight_scale_increment p (x i)).symm
    _ = (∑ i, dworkWeight p (((p : ℝ) + 2) * x i)) -
        ∑ i, dworkWeight p (x i) := Finset.sum_sub_distrib _ _
    _ ≤ _ := by linarith only [h]

/-- Exponential kernel associated with the nonnegative transition cost. -/
def dworkExponentialKernel {ι : Type*} (p : ℕ) (x : ι → ℝ≥0) : Matrix ι ι ℝ :=
  fun i j => Real.exp (-dworkTransitionWeight p (x i) (x j))

/-- The determinant inherits the scale-increment decay from every permutation term. -/
theorem dworkExponentialKernel_abs_det_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℕ) (x : ι → ℝ≥0) :
    |(dworkExponentialKernel p x).det| ≤
      ((Fintype.card ι).factorial : ℝ) *
        Real.exp (-(∑ i, min (((p : ℝ) + 1) * x i) 1)) := by
  rw [GaloisForLFunctions.det_eq_sum_perm_row]
  calc
    _ ≤ ∑ σ : Equiv.Perm ι,
        |(Equiv.Perm.sign σ : ℝ) * ∏ i, dworkExponentialKernel p x i (σ i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _σ : Equiv.Perm ι,
        Real.exp (-(∑ i, min (((p : ℝ) + 1) * x i) 1)) := by
      apply Finset.sum_le_sum
      intro σ _
      have hsign : |(Equiv.Perm.sign σ : ℝ)| = 1 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> norm_num
      rw [abs_mul, hsign, one_mul]
      have hprod : 0 ≤ ∏ i, dworkExponentialKernel p x i (σ i) :=
        Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le
      rw [abs_of_nonneg hprod]
      simp only [dworkExponentialKernel, ← Real.exp_sum, Finset.sum_neg_distrib]
      exact Real.exp_le_exp.mpr (neg_le_neg (dworkTransitionWeight_perm_sum_lower p x σ))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, nsmul_eq_mul]

#print axioms dworkExponentialKernel_abs_det_le
#print axioms dworkTransitionWeight_add
#print axioms dworkTransitionWeight_perm_sum_lower
end GaloisForLFunctions.HTGeometry
