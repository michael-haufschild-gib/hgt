import GaloisForLFunctions.HTGeometry.LaguerreShiftSplits

/-!
# Hermite–Poulain

A constant-coefficient differential operator whose symbol splits over `ℝ` maps real-rooted real
polynomials to real-rooted real polynomials.  The symbol factors into linear terms `X - a`, each of
which acts as the Laguerre shift `p ↦ p' - a·p`.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The constant-coefficient differential operator with symbol `h`, applied to `p`. -/
def diffOpApply (h p : ℝ[X]) : ℝ[X] :=
  (aeval (derivative : Module.End ℝ ℝ[X]) h) p

@[simp] theorem diffOpApply_one (p : ℝ[X]) : diffOpApply 1 p = p := by
  simp [diffOpApply]

theorem diffOpApply_C (c : ℝ) (p : ℝ[X]) : diffOpApply (C c) p = C c * p := by
  simp [diffOpApply, Module.algebraMap_end_apply, Polynomial.smul_eq_C_mul]

theorem diffOpApply_X (p : ℝ[X]) : diffOpApply X p = derivative p := by
  simp [diffOpApply]

theorem diffOpApply_mul (h₁ h₂ p : ℝ[X]) :
    diffOpApply (h₁ * h₂) p = diffOpApply h₁ (diffOpApply h₂ p) := by
  simp [diffOpApply, Module.End.mul_apply]

theorem diffOpApply_X_sub_C (a : ℝ) (p : ℝ[X]) :
    diffOpApply (X - C a) p = laguerreShift a p := by
  have h : diffOpApply (X - C a) p = diffOpApply X p - diffOpApply (C a) p := by
    simp [diffOpApply, map_sub]
  rw [h, diffOpApply_X, diffOpApply_C, laguerreShift]

theorem splits_diffOpApply_multiset_prod (s : Multiset ℝ) {p : ℝ[X]} (hp : p.Splits) :
    (diffOpApply ((s.map fun a => X - C a).prod) p).Splits := by
  classical
  refine Multiset.induction_on s ?_ ?_
  · simpa using hp
  · intro a t ih
    have hprod : (((a ::ₘ t).map fun b => X - C b).prod : ℝ[X])
        = (X - C a) * ((t.map fun b => X - C b).prod) := by
      simp
    rw [hprod, diffOpApply_mul, diffOpApply_X_sub_C]
    exact splits_laguerreShift ih a

/-- **Hermite–Poulain.** -/
theorem splits_diffOpApply {h p : ℝ[X]} (hh : h.Splits) (hp : p.Splits) :
    (diffOpApply h p).Splits := by
  classical
  have hfac := hh.eq_prod_roots
  have hrw : diffOpApply h p
      = C h.leadingCoeff * diffOpApply ((h.roots.map fun a => X - C a).prod) p := by
    conv_lhs => rw [hfac]
    rw [diffOpApply_mul, diffOpApply_C]
  rw [hrw]
  exact (Polynomial.Splits.C _).mul (splits_diffOpApply_multiset_prod _ hp)

end

end GaloisForLFunctions.HTGeometry
