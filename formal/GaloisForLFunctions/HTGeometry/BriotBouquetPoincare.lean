import GaloisForLFunctions.HTGeometry.ExpPolyAllHeights
import GaloisForLFunctions.HTGeometry.PoincareRecession
import GaloisForLFunctions.HTGeometry.PoincareHypertranscendence

/-!
# The Poincaré function of an autonomous first-order map

A transcendental entire solution of an autonomous first-order algebraic differential equation is
`f w = d + c·exp(a w + b)` with `a, c ≠ 0` — the Briot–Bouquet normal form.  That is a
polynomial-coefficient cascade constituent with a linear exponent, so its `n`-th iterate has
differential order exactly `n`, and an invertible affine reparametrisation does not move the minimal
order: the normalized Poincaré approximants have exact orders `1, 2, 3, …`.

Consequently the Poincaré function itself is hypertranscendental: a differentially algebraic
solution of the Schröder equation would force every iterate to satisfy an equation of one bounded
order.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

/-- The general transcendental entire solution of an autonomous first-order equation:
`f w = d + c·exp(a w + b)` with `a, c ≠ 0`. -/
def briotBouquetMap (a b c d : ℂ) : ℂ → ℂ :=
  fun w => d + c * Complex.exp (a * w + b)

theorem briotBouquetMap_eq_expPoly (a b c d : ℂ) :
    briotBouquetMap a b c d
      = expPoly (fun _ => Polynomial.C a * Polynomial.X + Polynomial.C b) (fun _ => c)
          (fun _ => d) 0 := by
  funext w
  rw [briotBouquetMap, expPoly]
  simp

theorem natDegree_linearPoly {a b : ℂ} (ha : a ≠ 0) :
    (Polynomial.C a * Polynomial.X + Polynomial.C b).natDegree = 1 := by
  rw [Polynomial.natDegree_add_C, Polynomial.natDegree_C_mul ha, Polynomial.natDegree_X]

/-- **The unit-cost law for the autonomous first-order class.**  The `n`-th iterate of
`w ↦ d + c·exp(a w + b)` has differential order exactly `n`. -/
theorem exactDifferentialOrder_briotBouquet_iterate {a b c d : ℂ} (ha : a ≠ 0) (hc : c ≠ 0)
    (m : ℕ) :
    ExactDifferentialOrder ((briotBouquetMap a b c d)^[m + 1]) (m + 1) := by
  have hfam : (fun _ : ℕ => briotBouquetMap a b c d)
      = expPoly (fun _ => Polynomial.C a * Polynomial.X + Polynomial.C b) (fun _ => c)
          (fun _ => d) := by
    funext k
    rw [briotBouquetMap_eq_expPoly]
    rfl
  have hcasc : entireCascade (fun _ : ℕ => briotBouquetMap a b c d) (m + 1)
      = (briotBouquetMap a b c d)^[m + 1] := entireCascade_const _ _
  rw [← hcasc, hfam]
  exact exactDifferentialOrder_expPolyCascade_all (fun _ => hc)
    (fun _ => by rw [natDegree_linearPoly ha]) m

theorem differentiable_briotBouquetMap (a b c d : ℂ) :
    Differentiable ℂ (briotBouquetMap a b c d) := by
  intro z
  refine (differentiable_const d).add ?_ z
  exact (differentiable_const c).mul
    (Complex.differentiable_exp.comp ((differentiable_id.const_mul a).add_const b))

theorem differentiable_iterate_of_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f) (k : ℕ) :
    Differentiable ℂ (f^[k]) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ']
      exact hf.comp ih

theorem iterate_conj {f φ : ℂ → ℂ} {lam : ℂ}
    (hconj : ∀ z, f (φ z) = φ (lam * z)) (k : ℕ) (z : ℂ) :
    f^[k] (φ z) = φ (lam ^ k * z) := by
  induction k generalizing z with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply, hconj z, ih (lam * z)]
      congr 1
      ring

/-- **Constraint-order recession for the autonomous first-order class.**  The normalized Poincaré
approximants of `w ↦ d + c·exp(a w + b)` at a repelling fixed point have exact differential orders
`1, 2, 3, …`. -/
theorem exactDifferentialOrder_poincareApprox_briotBouquet {a b c d ζ lam : ℂ}
    (ha : a ≠ 0) (hc : c ≠ 0) (hlam : lam ≠ 0) (m : ℕ) :
    ExactDifferentialOrder
      (fun z => (briotBouquetMap a b c d)^[m + 1] (ζ + z / lam ^ (m + 1))) (m + 1) :=
  exactDifferentialOrder_poincareApprox hlam (exactDifferentialOrder_briotBouquet_iterate ha hc m)

/-- **Bergweiler for the autonomous first-order class.**  Every nonconstant entire solution of the
Schröder equation `f ∘ φ = φ(λ ·)` with `f w = d + c·exp(a w + b)` and nonvanishing realized
derivative is hypertranscendental. -/
theorem not_differentiallyAlgebraicOn_poincare_briotBouquet {a b c d : ℂ} (ha : a ≠ 0) (hc : c ≠ 0)
    {φ : ℂ → ℂ} (hφ : Differentiable ℂ φ) (hnc : ∀ y : ℂ, ∃ z, φ z ≠ y)
    (hφ' : analyticMeroElement (deriv φ)
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr hφ).deriv ≠ 0)
    {lam : ℂ} (hlam : lam ≠ 0)
    (hconj : ∀ z, briotBouquetMap a b c d (φ z) = φ (lam * z)) :
    ¬ DifferentiallyAlgebraicOn φ (Set.univ : Set ℂ) := by
  refine not_differentiallyAlgebraicOn_of_unbounded_conjugates hφ hnc hφ' fun M => ?_
  refine ⟨lam ^ (M + 1), (briotBouquetMap a b c d)^[M + 1], pow_ne_zero _ hlam,
    differentiable_iterate_of_entire (differentiable_briotBouquetMap a b c d) (M + 1),
    fun z => iterate_conj hconj (M + 1) z, ?_⟩
  exact (exactDifferentialOrder_briotBouquet_iterate ha hc M).2 M (Nat.lt_succ_self M)


end GaloisForLFunctions.HTGeometry
