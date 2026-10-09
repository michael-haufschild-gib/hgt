import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.DeterminantIntersection
import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.ObstructionPrincipalization
import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.UnitCocycle
import Mathlib.Algebra.Polynomial.Degree.Units

/-!
# Units in the determinant algebra are exactly scalar units

A unit is constant in the polynomial variable of each determinant chart.
The source's two-chart intersection puts it in the polynomial base ring.
The same argument applies to its inverse, so polynomial-unit rigidity makes
the original unit a scalar. This supplies the global unit calculation needed
to detect line-bundle information lost under the quadric-to-determinant map.
-/

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate DeterminantRing

noncomputable section

variable (k : Type*) [Field k]

/-- Every unit belongs to the actual polynomial base subalgebra. -/
theorem paperDeterminantUnit_mem_baseRange {q : C k} (hq : IsUnit q) :
    q ∈ (baseMap (k := k)).range := by
  letI : IsDomain (BaseAway k 0) :=
    IsLocalization.Away.isDomain _ (MvPolynomial.X_ne_zero (R := k) (0 : Fin 3))
  letI : IsDomain (BaseAway k 1) :=
    IsLocalization.Away.isDomain _ (MvPolynomial.X_ne_zero (R := k) (1 : Fin 3))
  obtain ⟨v, _, hv⟩ := Polynomial.isUnit_iff.mp (hq.map (chartMapA k))
  obtain ⟨w, _, hw⟩ := Polynomial.isUnit_iff.mp (hq.map (chartMapD k))
  exact exists_base_of_constant_charts k hv.symm hw.symm

/-- The only units of the actual determinant quotient come from its coefficient field. -/
theorem paperDeterminantUnit_eq_scalar (u : (C k)ˣ) :
    ∃ c : kˣ, (u : C k) = algebraMap k (C k) (c : k) := by
  obtain ⟨p, hp⟩ := paperDeterminantUnit_mem_baseRange k u.isUnit
  obtain ⟨q, hq⟩ := paperDeterminantUnit_mem_baseRange k (u⁻¹).isUnit
  change baseMap p = (u : C k) at hp
  change baseMap q = ((u⁻¹ : (C k)ˣ) : C k) at hq
  have hpq : p * q = 1 := by
    apply baseMap_injective k
    rw [map_mul, hp, hq, map_one]
    exact u.val_inv
  let v : (Base k)ˣ := ⟨p, q, hpq, by rw [mul_comm]; exact hpq⟩
  let c : kˣ := Units.map (MvPolynomial.eval (fun _ : Fin 3 => (0 : k))).toMonoidHom v
  refine ⟨c, ?_⟩
  have hpC : p = MvPolynomial.C (MvPolynomial.eval (fun _ : Fin 3 => (0 : k)) p) :=
    polynomial_unit_eq_C_eval v.isUnit _
  rw [← hp, hpC]
  change baseMap (MvPolynomial.C (MvPolynomial.eval (fun _ : Fin 3 => (0 : k)) p)) =
    algebraMap k (C k) (MvPolynomial.eval (fun _ : Fin 3 => (0 : k)) p)
  simpa only [MvPolynomial.algebraMap_eq] using
    (baseMap (k := k)).commutes (MvPolynomial.eval (fun _ : Fin 3 => (0 : k)) p)

/-- A complete unit criterion, retaining the scalar unit rather than only its value. -/
theorem paperDeterminant_isUnit_iff_scalar (q : C k) :
    IsUnit q ↔ ∃ c : kˣ, q = algebraMap k (C k) (c : k) := by
  constructor
  · rintro ⟨u, rfl⟩
    exact paperDeterminantUnit_eq_scalar k u
  · rintro ⟨c, rfl⟩
    exact c.isUnit.map (algebraMap k (C k))

/-- Evaluation at the determinant basepoint identifies the full unit group with scalar units. -/
def paperDeterminantUnitsEquiv : (C k)ˣ ≃* kˣ where
  toFun := Units.map (Obstruction.determinantBasepoint k).toMonoidHom
  invFun := Units.map (algebraMap k (C k)).toMonoidHom
  left_inv u := by
    apply Units.ext
    change algebraMap k (C k) (Obstruction.determinantBasepoint k (u : C k)) = u
    obtain ⟨c, hc⟩ := paperDeterminantUnit_eq_scalar k u
    rw [hc]
    have he := (Obstruction.determinantBasepoint k).commutes (c : k)
    change Obstruction.determinantBasepoint k (algebraMap k (C k) (c : k)) = (c : k) at he
    rw [he]
  right_inv u := by
    apply Units.ext
    change Obstruction.determinantBasepoint k (algebraMap k (C k) (u : k)) = u
    exact (Obstruction.determinantBasepoint k).commutes (u : k)
  map_mul' u v := map_mul _ _ _

/-- Adding any family of polynomial parameters introduces no new determinant-ring units. -/
def paperDeterminantPolynomialUnitsEquiv (σ : Type*) :
    (MvPolynomial σ (C k))ˣ ≃* kˣ :=
  (polynomialUnitsEquiv (fun _ : σ => (0 : C k))).trans (paperDeterminantUnitsEquiv k)

end

end GaloisForLFunctions.HTGeometry
