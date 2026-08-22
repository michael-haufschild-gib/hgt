import GaloisForLFunctions.HTGeometry.DirectionDeformationRootFamily
import GaloisForLFunctions.HTGeometry.MvPowerSeriesDirectionSplit
import GaloisForLFunctions.HTGeometry.FractionFieldFunctorial

/-!
# Comparing the canonical family with the deformation of one direction

The canonical labelled root family lives in the power series ring in all couplings; the deformation
of one direction lives in the power series ring in the remaining couplings over that direction's
radical field.  Both embed in the power series ring in the remaining couplings over the Laurent
series field, where they are roots of the same polynomial with the same value at zero coupling —
hence equal, label by label.

## Main results

* `dirCompare`, `dirInclude` — the two embeddings into the comparison ring.
* `dirInclude_comp_dirDeform` — the coefficient rings agree.
* `dirCompare_canonicalRoot` — **the two labelled families agree.**
-/

open Polynomial
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {A : Type} [Field A] {m : ℕ} {d : (Fin (m + 1) → Bool) → A} {i : Fin (m + 1)}

/-- The canonical picture inside the comparison ring of one direction. -/
def dirCompare (A : Type) [Field A] (i : Fin (m + 1)) :
    MvPowerSeries (Fin (m + 1)) A →+*
      MvPowerSeries {j : Fin (m + 1) // j ≠ i} (LaurentSeries A) :=
  (MvPowerSeries.map (algebraMap (PowerSeries A) (LaurentSeries A))).comp
    ((dirSplit A i : MvPowerSeries (Fin (m + 1)) A ≃+*
      MvPowerSeries {j : Fin (m + 1) // j ≠ i} (PowerSeries A)) :
      MvPowerSeries (Fin (m + 1)) A →+* MvPowerSeries {j : Fin (m + 1) // j ≠ i} (PowerSeries A))

theorem dirCompare_injective : Function.Injective (dirCompare A i) :=
  (mvPowerSeries_map_injective (IsFractionRing.injective (PowerSeries A)
    (LaurentSeries A))).comp (dirSplit A i).injective

theorem constantCoeff_dirCompare (f : MvPowerSeries (Fin (m + 1)) A) :
    MvPowerSeries.constantCoeff (dirCompare A i f)
      = algebraMap (PowerSeries A) (LaurentSeries A) (dirRes A i f) := by
  show MvPowerSeries.constantCoeff
    (MvPowerSeries.map (algebraMap (PowerSeries A) (LaurentSeries A)) (dirSplit A i f)) = _
  rw [MvPowerSeries.constantCoeff_map]
  rfl

/-- The deformation ring of one direction inside its comparison ring. -/
def dirInclude (h2 : (2 : A) ≠ 0) (hδ : ∀ z, detuning d i z ≠ 0) :
    MvPowerSeries {j : Fin (m + 1) // j ≠ i} ↥(directionField h2 hδ) →+*
      MvPowerSeries {j : Fin (m + 1) // j ≠ i} (LaurentSeries A) :=
  MvPowerSeries.map ((directionField h2 hδ).val.toRingHom)

theorem dirInclude_injective (h2 : (2 : A) ≠ 0) (hδ : ∀ z, detuning d i z ≠ 0) :
    Function.Injective (dirInclude h2 hδ) :=
  mvPowerSeries_map_injective (fun _ _ h => Subtype.ext h)

theorem constantCoeff_dirInclude (h2 : (2 : A) ≠ 0) (hδ : ∀ z, detuning d i z ≠ 0)
    (g : MvPowerSeries {j : Fin (m + 1) // j ≠ i} ↥(directionField h2 hδ)) :
    MvPowerSeries.constantCoeff (dirInclude h2 hδ g)
      = (directionField h2 hδ).val (MvPowerSeries.constantCoeff g) := by
  show MvPowerSeries.constantCoeff
    (MvPowerSeries.map ((directionField h2 hδ).val.toRingHom) g) = _
  rw [MvPowerSeries.constantCoeff_map]
  rfl

/-- **The two pictures of the coefficient ring agree.** -/
theorem dirInclude_comp_dirDeform (h2 : (2 : A) ≠ 0) (hδ : ∀ z, detuning d i z ≠ 0) :
    (dirInclude h2 hδ).comp (dirDeform h2 hδ)
      = (dirCompare A i).comp
        (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin (m + 1)) (R := A)) := by
  classical
  refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)
  · rw [RingHom.comp_apply, RingHom.comp_apply, dirDeform_C, dirInclude, MvPowerSeries.map_C]
    show MvPowerSeries.C ((directionField h2 hδ).val (dirBase h2 hδ a)) = _
    rw [val_dirBase, dirCompare, RingHom.comp_apply]
    show _ = MvPowerSeries.map _ (dirSplit A i
      (MvPolynomial.coeToMvPowerSeries.ringHom (MvPolynomial.C a)))
    rw [dirSplit_coe_C, MvPowerSeries.map_C]
  · by_cases hj : j = i
    · subst hj
      rw [RingHom.comp_apply, RingHom.comp_apply, dirDeform_X_self, dirInclude,
        MvPowerSeries.map_C]
      show MvPowerSeries.C ((directionField h2 hδ).val (dirVar h2 hδ)) = _
      rw [val_dirVar, dirCompare, RingHom.comp_apply]
      show _ = MvPowerSeries.map _ (dirSplit A j
        (MvPolynomial.coeToMvPowerSeries.ringHom (MvPolynomial.X j)))
      rw [dirSplit_coe_X_self, MvPowerSeries.map_C]
    · rw [RingHom.comp_apply, RingHom.comp_apply, dirDeform_X_ne h2 hδ hj, dirInclude,
        MvPowerSeries.map_X, dirCompare, RingHom.comp_apply]
      show _ = MvPowerSeries.map _ (dirSplit A i
        (MvPolynomial.coeToMvPowerSeries.ringHom (MvPolynomial.X j)))
      rw [dirSplit_coe_X_ne hj, MvPowerSeries.map_X]

theorem dirDeform_injective (h2 : (2 : A) ≠ 0) (hδ : ∀ z, detuning d i z ≠ 0) :
    Function.Injective (dirDeform h2 hδ) := by
  intro p q hpq
  have h := congrArg (dirInclude h2 hδ) hpq
  rw [← RingHom.comp_apply, ← RingHom.comp_apply, dirInclude_comp_dirDeform,
    RingHom.comp_apply, RingHom.comp_apply] at h
  exact MvPolynomial.coe_injective (σ := Fin (m + 1)) (R := A) (dirCompare_injective h)

/-- **The canonical labelled family and the deformed labelled family agree.** -/
theorem dirCompare_canonicalRoot (h2 : (2 : A) ≠ 0) (hδ : ∀ z, detuning d i z ≠ 0)
    (hd : Function.Injective d)
    {Θ : (Fin (m + 1) → Bool) → MvPowerSeries (Fin (m + 1)) A}
    (hΘ : universalCharpolySeries d = ∏ x, (X - C (Θ x)))
    (hconst : ∀ x, MvPowerSeries.constantCoeff (Θ x) = d x)
    {Θ' : (Fin (m + 1) → Bool) →
      MvPowerSeries {j : Fin (m + 1) // j ≠ i} ↥(directionField h2 hδ)}
    (hΘ' : (universalCharpoly A (m + 1) d).map (dirDeform h2 hδ) = ∏ x, (X - C (Θ' x)))
    (hconst' : ∀ x, MvPowerSeries.constantCoeff (Θ' x) = dirRootField h2 hδ x)
    (x : Fin (m + 1) → Bool) :
    dirCompare A i (Θ x) = dirInclude h2 hδ (Θ' x) := by
  classical
  set P : Polynomial (MvPowerSeries {j : Fin (m + 1) // j ≠ i} (LaurentSeries A)) :=
    (universalCharpoly A (m + 1) d).map
      ((dirCompare A i).comp
        (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin (m + 1)) (R := A))) with hP
  have hP1 : P = ∏ y, (X - C (dirCompare A i (Θ y))) := by
    rw [hP, ← Polynomial.map_map,
      show (universalCharpoly A (m + 1) d).map
          (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin (m + 1)) (R := A))
        = universalCharpolySeries d from rfl, hΘ, Polynomial.map_prod]
    exact Finset.prod_congr rfl fun y _ => by
      rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  have hP2 : P = ∏ y, (X - C (dirInclude h2 hδ (Θ' y))) := by
    rw [hP, ← dirInclude_comp_dirDeform h2 hδ, ← Polynomial.map_map, hΘ', Polynomial.map_prod]
    exact Finset.prod_congr rfl fun y _ => by
      rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  have hres : ∀ y, MvPowerSeries.constantCoeff (dirCompare A i (Θ y))
      = (directionField h2 hδ).val (dirRootField h2 hδ y) := by
    intro y
    rw [constantCoeff_dirCompare,
      dirRes_canonicalRoot h2 hd i (fun z => directionRadicalSeries h2 (hδ z))
        (fun z => directionRadicalSeries_sq h2 (hδ z))
        (fun z => constantCoeff_directionRadicalSeries h2 (hδ z)) hΘ hconst y,
      val_dirRootField h2 hδ y]
    rfl
  have hres' : ∀ y, MvPowerSeries.constantCoeff (dirInclude h2 hδ (Θ' y))
      = (directionField h2 hδ).val (dirRootField h2 hδ y) := by
    intro y
    rw [constantCoeff_dirInclude, hconst' y]
  have hvalinj : Function.Injective ((directionField h2 hδ).val) := fun _ _ h => Subtype.ext h
  have hrootinj : Function.Injective
      (fun y => (directionField h2 hδ).val (dirRootField h2 hδ y)) :=
    Function.Injective.comp hvalinj (dirRootField_injective h2 hδ hd)
  have hroot1 : P.IsRoot (dirCompare A i (Θ x)) := by
    rw [hP1]
    show Polynomial.eval (dirCompare A i (Θ x)) (∏ y, (X - C (dirCompare A i (Θ y)))) = 0
    rw [Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ x) (by simp)
  have hroot2 : P.IsRoot (dirInclude h2 hδ (Θ' x)) := by
    rw [hP2]
    show Polynomial.eval (dirInclude h2 hδ (Θ' x)) (∏ y, (X - C (dirInclude h2 hδ (Θ' y)))) = 0
    rw [Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ x) (by simp)
  have hderiv : MvPowerSeries.constantCoeff
      ((Polynomial.derivative P).eval (dirCompare A i (Θ x))) ≠ 0 := by
    rw [hP1, eval_derivative_prod_X_sub_C (fun y => dirCompare A i (Θ y)) x, map_prod]
    refine Finset.prod_ne_zero_iff.mpr fun y hy => ?_
    rw [map_sub, hres x, hres y]
    intro h0
    exact (Finset.mem_erase.mp hy).1 (hrootinj (sub_eq_zero.mp h0)).symm
  exact isRoot_unique_mvPowerSeries hroot1 hroot2 hderiv (by rw [hres x, hres' x])

end

end GaloisForLFunctions.HTGeometry
