import GaloisForLFunctions.RHTower.XiGaussianHeatRegularKernelBlocks

/-!
# Orthogonal source projections for every canonical singular block

The block Christoffel--Darboux terms are actual mutually orthogonal
reproducing projections for the signed heat moment form. Their exact
composition law survives singular gaps and indefinite sections.
-/

open Polynomial HTGeometry
namespace RHTower
noncomputable section

/-- Kernel at a regular head, including the empty section. -/
def heatRegularSectionKernel (a : {t : ℝ // 0 < t}) : ℕ → ℝ → ℝ[X]
  | 0, _ => 0
  | j + 1, x => heatRegularKernel a j x

theorem heatRegularHead_monotone (a : {t : ℝ // 0 < t}) :
    Monotone (heatRegularHead a) :=
  monotone_nat_of_le_succ fun j => (heatRegularHead_lt_succ a j).le

theorem heatRegularSectionKernel_degree_lt
    (a : {t : ℝ // 0 < t}) (j : ℕ) (x : ℝ) :
    (heatRegularSectionKernel a j x).degree < (heatRegularHead a j : WithBot ℕ) := by
  cases j with
  | zero => simp [heatRegularSectionKernel]
  | succ j => exact heatRegularKernel_degree_lt a j x

theorem heatRegularSectionKernel_reproduces
    (a : {t : ℝ // 0 < t}) (j : ℕ) (x : ℝ)
    (p : ℝ[X]) (hp : p.degree < (heatRegularHead a j : WithBot ℕ)) :
    momentFunctional (heatRealMoments a) (p * heatRegularSectionKernel a j x) =
      p.eval x := by
  cases j with
  | zero =>
    have hp0 : p = 0 := by
      by_contra hne
      rw [heatRegularHead, degree_eq_natDegree hne] at hp
      have : p.natDegree < 0 := by exact_mod_cast hp
      omega
    simp [hp0]
  | succ j =>
    exact momentFunctional_mul_eq_eval_of_monomial
      (fun i hi => hcf_regular_kernel_monomial a j x ⟨i, hi⟩) p hp

/-- A gap contribution is precisely the difference of two consecutive
source section projections. -/
theorem heatRegularKernelBlock_eq_sub
    (a : {t : ℝ // 0 < t}) (j : ℕ) (x : ℝ) :
    heatRegularKernelBlock a j x =
      heatRegularSectionKernel a (j + 1) x - heatRegularSectionKernel a j x := by
  cases j with
  | zero => simpa [heatRegularSectionKernel] using (heatRegularKernel_zero a x).symm
  | succ j =>
    change _ = heatRegularKernel a (j + 1) x - heatRegularKernel a j x
    rw [heatRegularKernel_step]
    ring

theorem heatRegularKernelBlock_degree_lt
    (a : {t : ℝ // 0 < t}) (j : ℕ) (x : ℝ) :
    (heatRegularKernelBlock a j x).degree < (heatRegularHead a (j + 1) : WithBot ℕ) := by
  rw [heatRegularKernelBlock_eq_sub]
  apply lt_of_le_of_lt (degree_sub_le _ _)
  apply max_lt (heatRegularSectionKernel_degree_lt a (j + 1) x)
  exact lt_trans (heatRegularSectionKernel_degree_lt a j x)
    (by exact_mod_cast heatRegularHead_lt_succ a j)

/-- The whole lower polynomial section is annihilated by the new block. -/
theorem heatRegularKernelBlock_annihilates
    (a : {t : ℝ // 0 < t}) (j : ℕ) (x : ℝ)
    (p : ℝ[X]) (hp : p.degree < (heatRegularHead a j : WithBot ℕ)) :
    momentFunctional (heatRealMoments a) (p * heatRegularKernelBlock a j x) = 0 := by
  rw [heatRegularKernelBlock_eq_sub, mul_sub, momentFunctional_sub,
    heatRegularSectionKernel_reproduces a (j + 1) x p
      (lt_trans hp (by exact_mod_cast heatRegularHead_lt_succ a j)),
    heatRegularSectionKernel_reproduces a j x p hp, sub_self]

/-- Each block is a reproducing projection for its own signed source metric. -/
theorem hcf_regular_block_kernel_idempotent
    (a : {t : ℝ // 0 < t}) (j : ℕ) (x y : ℝ) :
    momentFunctional (heatRealMoments a)
      (heatRegularKernelBlock a j x * heatRegularKernelBlock a j y) =
        (heatRegularKernelBlock a j x).eval y := by
  conv_lhs => rw [heatRegularKernelBlock_eq_sub a j y]
  rw [mul_sub, momentFunctional_sub,
    heatRegularSectionKernel_reproduces a (j + 1) y _
      (heatRegularKernelBlock_degree_lt a j x)]
  have hz := heatRegularKernelBlock_annihilates a j x
    (heatRegularSectionKernel a j y) (heatRegularSectionKernel_degree_lt a j y)
  rw [mul_comm] at hz
  rw [hz, sub_zero]

/-- Exact diagonal composition law for all canonical block kernels. This
retains the actual signed moment functional and assumes no positivity. -/
theorem hcf_regular_block_kernel_orthogonal
    (a : {t : ℝ // 0 < t}) (i j : ℕ) (x y : ℝ) :
    momentFunctional (heatRealMoments a)
      (heatRegularKernelBlock a i x * heatRegularKernelBlock a j y) =
        if i = j then (heatRegularKernelBlock a i x).eval y else 0 := by
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    exact hcf_regular_block_kernel_idempotent a i x y
  · rw [if_neg hij]
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · apply heatRegularKernelBlock_annihilates
      exact lt_of_lt_of_le (heatRegularKernelBlock_degree_lt a i x)
        (by exact_mod_cast heatRegularHead_monotone a (show i + 1 ≤ j by omega))
    · rw [mul_comm]
      apply heatRegularKernelBlock_annihilates
      exact lt_of_lt_of_le (heatRegularKernelBlock_degree_lt a j y)
        (by exact_mod_cast heatRegularHead_monotone a (show j + 1 ≤ i by omega))

end
end RHTower
