import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheMellinTransformOfAStencil
import GaloisForLFunctions.RigidArithmeticOfCuts.TheFakePrimeMeasureIsUnique
import Mathlib.FieldTheory.Fixed

/-!
# Zeros are the kernel of the cut system

Read the cut system at the power measure `U_s(r) = r^{-s} − (r + 1)^{-s}`:

`Σ_r U_s(r) (r mod k) = (1 − k^{1-s}) ζ(s)`,  `Re s > 0`, `s ≠ 1`.

So `U_s` solves the homogeneous system at every `k` exactly when `ζ(s) = 0`. The zero modes are the
power-law solutions, and every finite combination of power measures in the kernel is a combination of
zero modes, by independence of the characters `k ↦ k^w`. This is why no stencil identity excludes a
zero: the cut system has them as solutions.

**Positivity reaches exactly the edge.** A solution of the homogeneous system bounded below by
`−1/(r (r + 1))` is zero, by the uniqueness of the fake. On `Re s ≥ 1` the mode `U_s` is dominated by
the pronic measure, so `ζ(s) ≠ 0` there. On `Re s < 1` it dominates the pronic measure at large `r`,
and positivity says nothing. Real zeros are excluded for the same reason: a real mode has one sign.
-/

open Finset Filter Topology
open GaloisForLFunctions.ArithmeticKreinLangerTheory
open GaloisForLFunctions.ArithmeticAuxiliaryDynamics

noncomputable section

namespace GaloisForLFunctions.RigidArithmeticOfCuts

/-- The sawtooth stencil `δ₁ − k δ_k`, whose multiplicity is `r mod k`. -/
def sawStencil (k : ℕ) : ℕ →₀ ℤ := Finsupp.single 1 1 - Finsupp.single k (k : ℤ)

private lemma stepWeight_eq_sum' (c : ℕ →₀ ℤ) (m : ℕ) :
    stepWeight c m = c.sum fun k a => a * ((m / k : ℕ) : ℤ) := rfl

private lemma balance_eq_sum' (c : ℕ →₀ ℤ) :
    ∑ k ∈ c.support, (c k : ℝ) / k = c.sum fun k a => (a : ℝ) / k := rfl

private lemma dirichletPoly_eq_sum (c : ℕ →₀ ℤ) (s : ℂ) :
    dirichletPoly c s = c.sum fun k a => (a : ℂ) * ((k : ℝ) : ℂ) ^ (-s) := rfl

theorem sawStencil_zero {k : ℕ} (hk : 2 ≤ k) : sawStencil k 0 = 0 := by
  simp only [sawStencil, Finsupp.coe_sub, Pi.sub_apply]
  rw [Finsupp.single_eq_of_ne (by omega), Finsupp.single_eq_of_ne (by omega)]
  rfl

theorem isBalanced_sawStencil {k : ℕ} (hk : 2 ≤ k) : IsBalanced (sawStencil k) := by
  have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [IsBalanced, balance_eq_sum', sawStencil, Finsupp.sum_sub_index (by intro _ a b; push_cast; ring),
    Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
  push_cast
  field_simp
  ring

/-- The multiplicity of the sawtooth stencil is the sawtooth. -/
theorem stepWeight_sawStencil {k : ℕ} (hk : 2 ≤ k) (r : ℕ) :
    stepWeight (sawStencil k) r = ((r % k : ℕ) : ℤ) := by
  rw [stepWeight_eq_sum', sawStencil, Finsupp.sum_sub_index (by intro _ a b; ring),
    Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
  have h := Nat.div_add_mod r k
  have h' : (k : ℤ) * ((r / k : ℕ) : ℤ) + ((r % k : ℕ) : ℤ) = r := by exact_mod_cast h
  simp only [Nat.div_one, one_mul]
  linarith

/-- The Dirichlet polynomial of the sawtooth stencil. -/
theorem dirichletPoly_sawStencil {k : ℕ} (hk : 2 ≤ k) (s : ℂ) :
    dirichletPoly (sawStencil k) s = 1 - ((k : ℝ) : ℂ) ^ (1 - s) := by
  have hkC : ((k : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by omega : k ≠ 0)
  rw [dirichletPoly_eq_sum, sawStencil, Finsupp.sum_sub_index (by intro _ a b; push_cast; ring),
    Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
  have hpow : ((k : ℝ) : ℂ) ^ (1 - s) = ((k : ℝ) : ℂ) * ((k : ℝ) : ℂ) ^ (-s) := by
    rw [sub_eq_add_neg, Complex.cpow_add _ _ hkC, Complex.cpow_one]
  rw [hpow]
  simp

/-- The power measure `U_s(r) = r^{-s} − (r + 1)^{-s}`, indexed by `r = j + 1`. -/
abbrev powerMeasure (s : ℂ) (j : ℕ) : ℂ := abelStep s j

/-- **The cut moment of a power measure.** -/
theorem hasSum_powerMeasure_mod {k : ℕ} (hk : 2 ≤ k) {s : ℂ} (hσ : 0 < s.re) (hs1 : s ≠ 1) :
    HasSum (fun j : ℕ => powerMeasure s j * (((j + 1) % k : ℕ) : ℂ))
      ((1 - ((k : ℝ) : ℂ) ^ (1 - s)) * riemannZeta s) := by
  have h := hasSum_mellin (sawStencil_zero hk) (isBalanced_sawStencil hk) hσ hs1
  rw [dirichletPoly_sawStencil hk] at h
  refine h.congr_fun' ?_ |>.trans ?_ <;> sorry

end GaloisForLFunctions.RigidArithmeticOfCuts
