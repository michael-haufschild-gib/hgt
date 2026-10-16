import GaloisForLFunctions.RHTower.XiGaussianHeatRegularPade
import GaloisForLFunctions.HTGeometry.MomentInverseKernel

/-!
# Exact source reproducing kernels across singular heat-moment gaps

The canonical regular-head transfer frame determines the full inverse
Hankel kernel at every positive time. The source Casoratian supplies its
normalization; extended normal-block orthogonality propagates reproduction
through every row. Positivity and intermediate nonzero pivots are unnecessary.
-/

open Polynomial Matrix HTGeometry
open scoped BigOperators
namespace RHTower
noncomputable section

/-- Source kernel carried by two consecutive canonical regular heads. -/
def heatRegularKernel (a : {t : ℝ // 0 < t}) (j : ℕ) (x : ℝ) : ℝ[X] :=
  (heatRegularCoupling a j)⁻¹ •
    ((heatRegularAdmission a j).eval x •
        momentDividedDifference (heatRegularAdmission a (j + 1)) x -
      (heatRegularAdmission a (j + 1)).eval x •
        momentDividedDifference (heatRegularAdmission a j) x)

theorem heatRegularKernel_degree_lt (a : {t : ℝ // 0 < t}) (j : ℕ) (x : ℝ) :
    (heatRegularKernel a j x).degree < (heatRegularHead a (j + 1) : WithBot ℕ) := by
  have hd (i : ℕ) : (heatRegularAdmission a i).degree =
      (heatRegularHead a i : WithBot ℕ) := by
    rw [heatRegularAdmission,
      degree_eq_natDegree (monicMomentAdmissionPolynomial_monic _ _).ne_zero,
      monicMomentAdmissionPolynomial_natDegree]
  have hn := degree_divByMonic_lt (heatRegularAdmission a (j + 1)) (X - C x)
    (monicMomentAdmissionPolynomial_monic _ _).ne_zero
    (by rw [degree_X_sub_C]; exact_mod_cast Nat.zero_lt_one)
  rw [hd] at hn
  have hp : (momentDividedDifference (heatRegularAdmission a j) x).degree <
      (heatRegularHead a (j + 1) : WithBot ℕ) := by
    apply lt_of_le_of_lt (degree_divByMonic_le _ _)
    rw [hd]
    exact_mod_cast heatRegularHead_lt_succ a j
  exact lt_of_le_of_lt (degree_smul_le _ _)
    (lt_of_le_of_lt (degree_sub_le _ _)
      (max_lt (lt_of_le_of_lt (degree_smul_le _ _) hn)
        (lt_of_le_of_lt (degree_smul_le _ _) hp)))

/-- The source companion fixes the normalization, even when total mass vanishes. -/
theorem heatRegularKernel_moment (a : {t : ℝ // 0 < t}) (j : ℕ) (x : ℝ) :
    momentFunctional (heatRealMoments a) (heatRegularKernel a j x) = 1 := by
  have hw := congrArg (Polynomial.eval x) (hcf_regular_head_casoratian a j)
  simp only [eval_sub, eval_mul, eval_C, hcf_regular_companion_source] at hw
  have hn : (heatRegularAdmission a j).eval x *
        momentFunctional (heatRealMoments a)
          (momentDividedDifference (heatRegularAdmission a (j + 1)) x) -
      (heatRegularAdmission a (j + 1)).eval x *
        momentFunctional (heatRealMoments a)
          (momentDividedDifference (heatRegularAdmission a j) x) =
      heatRegularCoupling a j := by
    dsimp only [momentDividedDifference]
    linear_combination -hw
  rw [heatRegularKernel, momentFunctional_smul, momentFunctional_sub,
    momentFunctional_smul, momentFunctional_smul, hn,
    inv_mul_cancel₀ (heatRegularCoupling_ne_zero a j)]

/-- Division-free displacement identity, valid also on the diagonal. -/
theorem heatRegularKernel_displacement (a : {t : ℝ // 0 < t}) (j : ℕ) (x : ℝ) :
    (X - C x) * heatRegularKernel a j x =
      (heatRegularCoupling a j)⁻¹ •
        ((heatRegularAdmission a j).eval x • heatRegularAdmission a (j + 1) -
          (heatRegularAdmission a (j + 1)).eval x • heatRegularAdmission a j) := by
  have hp := mul_momentDividedDifference (heatRegularAdmission a j) x
  have hq := mul_momentDividedDifference (heatRegularAdmission a (j + 1)) x
  simp only [heatRegularKernel, smul_eq_C_mul]
  linear_combination
    C ((heatRegularCoupling a j)⁻¹) * C ((heatRegularAdmission a j).eval x) * hq -
    C ((heatRegularCoupling a j)⁻¹) * C ((heatRegularAdmission a (j + 1)).eval x) * hp

/-- Every row of the actual finite moment section is reproduced. -/
theorem hcf_regular_kernel_monomial (a : {t : ℝ // 0 < t}) (j : ℕ) (x : ℝ)
    (i : Fin (heatRegularHead a (j + 1))) :
    momentFunctional (heatRealMoments a) (X ^ (i : ℕ) * heatRegularKernel a j x) =
      x ^ (i : ℕ) := by
  apply moment_monomial_of_displacement (heatRegularKernel_moment a j x) ?_ i i.isLt
  intro r hr
  have hp := (heatRegularGap_normalBlock a j).vanishing r (by
    rw [heatRegularHead_add_gap]
    omega)
  have hq := momentFunctional_X_pow_mul_monicMomentAdmissionPolynomial_eq_zero
    (heatRegularHead_det_ne_zero a (j + 1)) (⟨r, by omega⟩ : Fin (heatRegularHead a (j + 1)))
  change momentFunctional (heatRealMoments a) (X ^ r * heatRegularAdmission a j) = 0 at hp
  change momentFunctional (heatRealMoments a) (X ^ r * heatRegularAdmission a (j + 1)) = 0 at hq
  rw [heatRegularKernel_displacement, mul_smul_comm, mul_sub,
    momentFunctional_smul, momentFunctional_sub, mul_smul_comm, mul_smul_comm,
    momentFunctional_smul, momentFunctional_smul, hp, hq]
  ring

/-- The canonical source kernel is exactly the inverse Hankel solve. -/
theorem hcf_regular_kernel_inverse (a : {t : ℝ // 0 < t}) (j : ℕ) (x : ℝ) :
    heatRegularKernel a j x =
      momentInverseKernel (heatRealMoments a) (heatRegularHead a (j + 1)) x :=
  eq_momentInverseKernel_of_monomial (heatRegularHead_det_ne_zero a (j + 1))
    (heatRegularKernel_degree_lt a j x) (fun i hi => hcf_regular_kernel_monomial a j x ⟨i, hi⟩)

/-- Exact source reproduction for every polynomial in the finite section. -/
theorem hcf_regular_kernel_reproduces (a : {t : ℝ // 0 < t}) (j : ℕ) (x : ℝ)
    (c : Fin (heatRegularHead a (j + 1)) → ℝ) :
    momentFunctional (heatRealMoments a)
      (ofFn (heatRegularHead a (j + 1)) c * heatRegularKernel a j x) =
        (ofFn (heatRegularHead a (j + 1)) c).eval x :=
  momentFunctional_mul_eq_eval_of_monomial
    (fun i hi => hcf_regular_kernel_monomial a j x ⟨i, hi⟩) _ (ofFn_degree_lt c)

/-- Pairing two kernels gives their evaluation, with the full source sign retained. -/
theorem hcf_regular_kernel_pairing (a : {t : ℝ // 0 < t}) (j : ℕ) (x y : ℝ) :
    momentFunctional (heatRealMoments a)
      (heatRegularKernel a j y * heatRegularKernel a j x) =
        (heatRegularKernel a j y).eval x :=
  momentFunctional_mul_eq_eval_of_monomial
    (fun i hi => hcf_regular_kernel_monomial a j x ⟨i, hi⟩) _
    (heatRegularKernel_degree_lt a j y)

theorem hcf_regular_kernel_symmetric (a : {t : ℝ // 0 < t}) (j : ℕ) (x y : ℝ) :
    (heatRegularKernel a j x).eval y = (heatRegularKernel a j y).eval x := by
  rw [← hcf_regular_kernel_pairing, mul_comm, hcf_regular_kernel_pairing]

end
end RHTower
