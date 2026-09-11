import GaloisForLFunctions.HTGeometry.FiniteKMSWightman
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Connected Gibbs susceptibility and symmetry sectors

The existing positive finite Gibbs ensemble supplies an exact source-response covariance,
a nonnegative susceptibility form, and a complete classification of its null directions.
A two-sheet parity construction gives an explicit symmetry obstruction to mixed response.

Source: Singh, arXiv:2609.10571, sections 3.3, 5.1 and 5.2.
-/

set_option autoImplicit false

open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry.TraceDynamics
open _root_.HTGeometry
noncomputable section
variable {α ι : Type*} [Fintype α] [Nonempty α] [Fintype ι]

def gibbsMean (β : ℝ) (E f : α → ℝ) : ℝ :=
  ∑ a, finiteGibbsStateWeight β E a * f a

def gibbsCovariance (β : ℝ) (E f g : α → ℝ) : ℝ :=
  ∑ a, finiteGibbsStateWeight β E a *
    (f a - gibbsMean β E f) * (g a - gibbsMean β E g)

theorem gibbsMean_const (β : ℝ) (E : α → ℝ) (c : ℝ) :
    gibbsMean β E (fun _ => c) = c := by
  rw [gibbsMean, ← Finset.sum_mul, sum_finiteGibbsStateWeight_eq_one, one_mul]

theorem gibbsMean_sub_mean (β : ℝ) (E f : α → ℝ) :
    gibbsMean β E (fun a => f a - gibbsMean β E f) = 0 := by
  simp only [gibbsMean, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    sum_finiteGibbsStateWeight_eq_one, one_mul, sub_self]

theorem gibbsCovariance_moment (β : ℝ) (E f g : α → ℝ) :
    gibbsCovariance β E f g = gibbsMean β E (fun a => f a * g a) -
      gibbsMean β E f * gibbsMean β E g := by
  unfold gibbsCovariance
  simp_rw [show ∀ a, finiteGibbsStateWeight β E a *
      (f a - gibbsMean β E f) * (g a - gibbsMean β E g) =
      finiteGibbsStateWeight β E a * (f a*g a) -
      (finiteGibbsStateWeight β E a*f a) * gibbsMean β E g -
      (finiteGibbsStateWeight β E a*g a) * gibbsMean β E f +
      finiteGibbsStateWeight β E a * (gibbsMean β E f * gibbsMean β E g) from fun a => by ring]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    sum_finiteGibbsStateWeight_eq_one, one_mul]
  change gibbsMean β E (fun a => f a*g a) - gibbsMean β E f * gibbsMean β E g -
    gibbsMean β E g * gibbsMean β E f + gibbsMean β E f * gibbsMean β E g = _
  ring

omit [Nonempty α] in
theorem gibbsCovariance_comm (β : ℝ) (E f g : α → ℝ) :
    gibbsCovariance β E f g = gibbsCovariance β E g f := by
  unfold gibbsCovariance
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem gibbsCovariance_self_nonneg (β : ℝ) (E f : α → ℝ) :
    0 ≤ gibbsCovariance β E f f := by
  unfold gibbsCovariance
  exact Finset.sum_nonneg fun a _ => by
    nlinarith [mul_nonneg (finiteGibbsStateWeight_pos β E a).le
      (sq_nonneg (f a - gibbsMean β E f))]

theorem gibbsCovariance_self_eq_zero_iff (β : ℝ) (E f : α → ℝ) :
    gibbsCovariance β E f f = 0 ↔ ∀ a, f a = gibbsMean β E f := by
  have hn a : 0 ≤ finiteGibbsStateWeight β E a *
      (f a - gibbsMean β E f) * (f a - gibbsMean β E f) := by
    nlinarith [mul_nonneg (finiteGibbsStateWeight_pos β E a).le
      (sq_nonneg (f a - gibbsMean β E f))]
  constructor
  · intro hz a
    have h := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hn a)).mp hz a
      (Finset.mem_univ a)
    have hp := finiteGibbsStateWeight_pos β E a
    have hs : (f a - gibbsMean β E f)^2 = 0 := by
      apply (mul_eq_zero.mp (show finiteGibbsStateWeight β E a *
        (f a - gibbsMean β E f)^2 = 0 by nlinarith [h])).resolve_left hp.ne'
    nlinarith [sq_nonneg (f a - gibbsMean β E f)]
  · intro h
    simp [gibbsCovariance, h]

omit [Nonempty α] in
theorem gibbsMean_linearCombination (β : ℝ) (E : α → ℝ)
    (O : ι → α → ℝ) (v : ι → ℝ) :
    gibbsMean β E (fun a => ∑ i, v i * O i a) = ∑ i, v i * gibbsMean β E (O i) := by
  simp only [gibbsMean, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  ring

def susceptibility (β : ℝ) (E : α → ℝ) (O : ι → α → ℝ) : Matrix ι ι ℝ :=
  fun i j => gibbsCovariance β E (O i) (O j)

omit [Nonempty α] in
theorem susceptibility_quadratic (β : ℝ) (E : α → ℝ)
    (O : ι → α → ℝ) (v : ι → ℝ) :
    (∑ i, ∑ j, v i * susceptibility β E O i j * v j) =
      gibbsCovariance β E (fun a => ∑ i, v i * O i a)
        (fun a => ∑ i, v i * O i a) := by
  simp only [susceptibility, gibbsCovariance, gibbsMean_linearCombination]
  simp_rw [← Finset.sum_sub_distrib, ← mul_sub]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  calc
    _ = ∑ a, ∑ i, ∑ j, v i *
        (finiteGibbsStateWeight β E a * (O i a - gibbsMean β E (O i)) *
          (O j a - gibbsMean β E (O j))) * v j := by
      conv_lhs =>
        arg 2
        ext i
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem susceptibility_nonnegative (β : ℝ) (E : α → ℝ)
    (O : ι → α → ℝ) (v : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, v i * susceptibility β E O i j * v j := by
  rw [susceptibility_quadratic]
  exact gibbsCovariance_self_nonneg _ _ _

theorem susceptibility_null_iff_constant (β : ℝ) (E : α → ℝ)
    (O : ι → α → ℝ) (v : ι → ℝ) :
    (∑ i, ∑ j, v i * susceptibility β E O i j * v j) = 0 ↔
      ∀ a, (∑ i, v i * O i a) = ∑ i, v i * gibbsMean β E (O i) := by
  rw [susceptibility_quadratic, gibbsCovariance_self_eq_zero_iff,
    gibbsMean_linearCombination]

/-- Exact response to an arbitrary source equals the connected Gibbs covariance. -/
theorem hasDerivAt_gibbsMean_source (E O f : α → ℝ) (t : ℝ) :
    HasDerivAt (fun s => gibbsMean 1 (fun a => E a - s * O a) f)
      (gibbsCovariance 1 (fun a => E a - t * O a) f O) t := by
  let N : (α → ℝ) → ℝ → ℝ := fun g s =>
    ∑ a, Real.exp (-(E a - s * O a)) * g a
  have hd (g : α → ℝ) : HasDerivAt (N g) (N (fun a => O a * g a) t) t := by
    apply HasDerivAt.fun_sum
    intro a _
    apply (((((hasDerivAt_const t (E a)).sub
      ((hasDerivAt_id t).mul_const (O a))).neg).exp).mul_const (g a)).congr_deriv
    dsimp
    ring
  have hZ (s : ℝ) : N (fun _ => 1) s =
      finiteGibbsPartition 1 (fun a => E a - s * O a) := by
    simp [N, finiteGibbsPartition]
  have hpos : N (fun _ => 1) t ≠ 0 := by
    rw [hZ]
    exact (finiteGibbsPartition_pos _ _).ne'
  have hm (g : α → ℝ) (s : ℝ) :
      gibbsMean 1 (fun a => E a - s * O a) g = N g s / N (fun _ => 1) s := by
    rw [hZ]
    simp only [gibbsMean, finiteGibbsStateWeight, neg_mul, one_mul, N,
      div_mul_eq_mul_div, Finset.sum_div]
  simp_rw [hm]
  apply ((hd f).div (hd (fun _ => 1)) hpos).congr_deriv
  rw [gibbsCovariance_moment, hm, hm, hm]
  have hmul : N (fun a => O a * f a) t = N (fun a => f a * O a) t := by
    congr 1
    funext a
    ring
  have hone : N (fun a => O a * 1) t = N O t := by simp
  rw [hmul, hone]
  field_simp

/-- Finite-source response is differentiable everywhere: no pole is produced by finite sampling. -/
theorem differentiable_gibbsMean_source (E O f : α → ℝ) :
    Differentiable ℝ (fun t => gibbsMean 1 (fun a => E a - t * O a) f) :=
  fun t => (hasDerivAt_gibbsMean_source E O f t).differentiableAt

/-- Duplicating each energy level into two parity sheets halves its probability per sheet. -/
theorem gibbsWeight_parity_sheet (β : ℝ) (E : α → ℝ) (a : α) (b : Bool) :
    finiteGibbsStateWeight β (fun z : α × Bool => E z.1) (a,b) =
      finiteGibbsStateWeight β E a/2 := by
  have hZ : finiteGibbsPartition β (fun z : α × Bool => E z.1) =
      2*finiteGibbsPartition β E := by
    simp only [finiteGibbsPartition, Fintype.sum_prod_type, Fintype.sum_bool,
      Finset.sum_add_distrib]
    ring
  unfold finiteGibbsStateWeight
  rw [hZ]
  field_simp [(finiteGibbsPartition_pos β E).ne']

/-- Every parity-odd one-point function vanishes in the constructed symmetric Gibbs ensemble. -/
theorem gibbsMean_parity_odd (β : ℝ) (E f : α → ℝ) :
    gibbsMean β (fun z : α × Bool => E z.1)
      (fun z => if z.2 then f z.1 else -f z.1) = 0 := by
  simp only [gibbsMean, Fintype.sum_prod_type, Fintype.sum_bool,
    gibbsWeight_parity_sheet, Bool.false_eq_true, ↓reduceIte]
  simp

/-- Even and odd channels have exactly zero connected cross-susceptibility. -/
theorem gibbsCovariance_parity_cross (β : ℝ) (E f g : α → ℝ) :
    gibbsCovariance β (fun z : α × Bool => E z.1)
      (fun z => f z.1) (fun z => if z.2 then g z.1 else -g z.1) = 0 := by
  rw [gibbsCovariance_moment, gibbsMean_parity_odd, mul_zero, sub_zero]
  convert gibbsMean_parity_odd β E (fun a => f a*g a) using 1
  congr 1
  funext z
  cases z.2 <;> simp

/-- At the symmetric phase an odd source has zero linear response in every even channel. -/
theorem gibbs_even_response_to_odd_source (E f g : α → ℝ) :
    HasDerivAt (fun t => gibbsMean 1
      (fun z : α × Bool => E z.1-t*(if z.2 then g z.1 else -g z.1))
      (fun z => f z.1)) 0 0 := by
  have h := hasDerivAt_gibbsMean_source (fun z : α × Bool => E z.1)
    (fun z => if z.2 then g z.1 else -g z.1) (fun z => f z.1) 0
  simpa only [zero_mul, sub_zero, gibbsCovariance_parity_cross] using h

end
end GaloisForLFunctions.HTGeometry.TraceDynamics
