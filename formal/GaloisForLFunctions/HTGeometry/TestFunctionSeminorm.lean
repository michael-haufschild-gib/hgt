import GaloisForLFunctions.HTGeometry.TestFunctionSupNorm
import Mathlib.Analysis.Seminorm

/-!
# The derivative sup-norms as a seminorm family on the test space

The suprema of the iterated derivatives are genuine seminorms on the module of smooth functions
supported in a fixed compact set.  Packaged as a family indexed by the order of differentiation,
they are the defining seminorm family of the test space: the finite suprema that the seminorm
topology uses are exactly the `C^k` norms.

* `deningerTestSupNorm_zero`, `deningerTestSupNorm_neg` : the remaining seminorm laws.
* `deningerTestSeminorm` : the seminorm of a fixed order.
* `deningerTestSeminormFamily` : the family.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

section Seminorms

variable {J : Set ℝ}

theorem deningerTestSupNorm_def (m : ℕ) (phi : ℝ → ℂ) :
    deningerTestSupNorm m phi = sSup (Set.range fun t => ‖iteratedDeriv m phi t‖) := rfl

/-- Every iterated derivative of the zero function is zero. -/
theorem iteratedDeriv_zero_fun (m : ℕ) : iteratedDeriv m (0 : ℝ → ℂ) = 0 := by
  induction m with
  | zero => rw [iteratedDeriv_zero]
  | succ m ih =>
      rw [iteratedDeriv_succ, ih]
      exact deriv_const' 0

theorem deningerTestSupNorm_zero (m : ℕ) : deningerTestSupNorm m (0 : ℝ → ℂ) = 0 := by
  rw [deningerTestSupNorm_def, iteratedDeriv_zero_fun]
  simp

/-- The derivative sup-norms are invariant under negation. -/
theorem deningerTestSupNorm_neg (hJ : IsCompact J) {phi : ℝ → ℂ}
    (hphi : phi ∈ deningerTestSpace J) (m : ℕ) :
    deningerTestSupNorm m (-phi) = deningerTestSupNorm m phi := by
  have h := deningerTestSupNorm_smul hJ hphi (-1) m
  rw [neg_one_smul] at h
  rw [h, abs_neg, abs_one, one_mul]

/-- The sup-norm of the `m`-th derivative, as a seminorm on the test space. -/
noncomputable def deningerTestSeminorm (hJ : IsCompact J) (m : ℕ) :
    Seminorm ℝ (deningerTestSpace J) where
  toFun phi := deningerTestSupNorm m (phi : ℝ → ℂ)
  map_zero' := by
    show deningerTestSupNorm m ((0 : deningerTestSpace J) : ℝ → ℂ) = 0
    rw [Submodule.coe_zero]
    exact deningerTestSupNorm_zero m
  add_le' phi psi := by
    show deningerTestSupNorm m (((phi + psi : deningerTestSpace J) : ℝ → ℂ))
      ≤ deningerTestSupNorm m (phi : ℝ → ℂ) + deningerTestSupNorm m (psi : ℝ → ℂ)
    rw [Submodule.coe_add]
    exact deningerTestSupNorm_add_le hJ phi.2 psi.2 m
  neg' phi := by
    show deningerTestSupNorm m ((-phi : deningerTestSpace J) : ℝ → ℂ)
      = deningerTestSupNorm m (phi : ℝ → ℂ)
    rw [Submodule.coe_neg]
    exact deningerTestSupNorm_neg hJ phi.2 m
  smul' a phi := by
    show deningerTestSupNorm m ((a • phi : deningerTestSpace J) : ℝ → ℂ)
      = ‖a‖ * deningerTestSupNorm m (phi : ℝ → ℂ)
    rw [Submodule.coe_smul, Real.norm_eq_abs]
    exact deningerTestSupNorm_smul hJ phi.2 a m

@[simp] theorem deningerTestSeminorm_apply (hJ : IsCompact J) (m : ℕ)
    (phi : deningerTestSpace J) :
    deningerTestSeminorm hJ m phi = deningerTestSupNorm m (phi : ℝ → ℂ) := rfl

/-- The defining seminorm family of the test space, indexed by the order of differentiation. -/
noncomputable def deningerTestSeminormFamily (hJ : IsCompact J) :
    SeminormFamily ℝ (deningerTestSpace J) ℕ :=
  fun m => deningerTestSeminorm hJ m

@[simp] theorem deningerTestSeminormFamily_apply (hJ : IsCompact J) (m : ℕ)
    (phi : deningerTestSpace J) :
    deningerTestSeminormFamily hJ m phi = deningerTestSupNorm m (phi : ℝ → ℂ) := rfl

/-- The finite supremum of the family up to order `k` dominates every order `m ≤ k`. -/
theorem deningerTestSupNorm_le_finset_sup (hJ : IsCompact J) (k m : ℕ) (hm : m ≤ k)
    (phi : deningerTestSpace J) :
    deningerTestSupNorm m (phi : ℝ → ℂ)
      ≤ ((Finset.range (k + 1)).sup (deningerTestSeminormFamily hJ)) phi := by
  have hmem : m ∈ Finset.range (k + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hm)
  have hle : deningerTestSeminormFamily hJ m
      ≤ (Finset.range (k + 1)).sup (deningerTestSeminormFamily hJ) :=
    Finset.le_sup hmem
  exact hle phi

end Seminorms

end GaloisForLFunctions.HTGeometry
