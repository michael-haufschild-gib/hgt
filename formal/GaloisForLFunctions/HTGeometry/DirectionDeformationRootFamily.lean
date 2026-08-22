import GaloisForLFunctions.HTGeometry.DirectionCanonicalRootIdentification
import GaloisForLFunctions.HTGeometry.DirectionRootFlipTransfer
import GaloisForLFunctions.HTGeometry.DirectionRadicalField

/-!
# Deforming the remaining couplings around one transverse direction

Over the radical field of one transverse direction the characteristic polynomial of that direction
splits with distinct roots, so turning the remaining couplings back on lifts every root uniquely to
the power series ring in those couplings.  The block flips of the radical field extend
coefficientwise and permute the lifted roots by the hypercube edge swaps of the direction.

## Main results

* `detuning`, `edgeSum`, `edgeProd` — the block data of one direction.
* `dirBase`, `dirVar`, `dirDeform` — the direction's picture of the coefficient ring.
* `dirRootField`, `val_dirRootField`, `dirRootField_injective` — the labelled direction roots.
* `exists_deformationRootFamily` — **the deformed labelled root family.**
* `exists_algEquiv_swap_dirRootField` — every edge swap of the direction is realized on it.
-/

open Polynomial
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {A : Type} [Field A] {m : ℕ}

/-- The detuning across a hypercube edge in the chosen direction. -/
def detuning (d : (Fin (m + 1) → Bool) → A) (i : Fin (m + 1)) (z : Fin m → Bool) : A :=
  cubeSide d i true z - cubeSide d i false z

/-- The trace of the block attached to a hypercube edge. -/
def edgeSum (d : (Fin (m + 1) → Bool) → A) (i : Fin (m + 1)) (z : Fin m → Bool) : A :=
  cubeSide d i false z + cubeSide d i true z

/-- The unperturbed determinant of the block attached to a hypercube edge. -/
def edgeProd (d : (Fin (m + 1) → Bool) → A) (i : Fin (m + 1)) (z : Fin m → Bool) : A :=
  cubeSide d i false z * cubeSide d i true z

variable {d : (Fin (m + 1) → Bool) → A} {i : Fin (m + 1)}

/-- The base field of the direction, inside its radical field. -/
def dirBase (h2 : (2 : A) ≠ 0) (hδ : ∀ z, detuning d i z ≠ 0) :
    A →+* ↥(directionField h2 hδ) :=
  (algebraMap (RatFunc A) ↥(directionField h2 hδ)).comp
    ((algebraMap (Polynomial A) (RatFunc A)).comp (Polynomial.C : A →+* Polynomial A))

/-- The transverse coupling of the direction, inside its radical field. -/
def dirVar (h2 : (2 : A) ≠ 0) (hδ : ∀ z, detuning d i z ≠ 0) : ↥(directionField h2 hδ) :=
  algebraMap (RatFunc A) ↥(directionField h2 hδ)
    (algebraMap (Polynomial A) (RatFunc A) Polynomial.X)

theorem val_algebraMap_ratFunc (h2 : (2 : A) ≠ 0) (hδ : ∀ z, detuning d i z ≠ 0)
    (y : RatFunc A) :
    (directionField h2 hδ).val (algebraMap (RatFunc A) ↥(directionField h2 hδ) y)
      = ratFuncToLaurent A y := by
  rw [(directionField h2 hδ).val.commutes y, algebraMap_ratFunc_laurent]

theorem val_dirBase (h2 : (2 : A) ≠ 0) (hδ : ∀ z, detuning d i z ≠ 0) (a : A) :
    (directionField h2 hδ).val (dirBase h2 hδ a)
      = algebraMap (PowerSeries A) (LaurentSeries A) (PowerSeries.C a) := by
  rw [dirBase, RingHom.comp_apply, RingHom.comp_apply, val_algebraMap_ratFunc,
    ratFuncToLaurent_polynomial]
  congr 1
  exact Polynomial.coe_C a

theorem val_dirVar (h2 : (2 : A) ≠ 0) (hδ : ∀ z, detuning d i z ≠ 0) :
    (directionField h2 hδ).val (dirVar h2 hδ)
      = algebraMap (PowerSeries A) (LaurentSeries A) PowerSeries.X := by
  rw [dirVar, val_algebraMap_ratFunc, ratFuncToLaurent_polynomial]
  congr 1
  exact Polynomial.coe_X

theorem val_directionFieldRadical (h2 : (2 : A) ≠ 0) (hδ : ∀ z, detuning d i z ≠ 0)
    (z : Fin m → Bool) :
    (directionField h2 hδ).val (directionFieldRadical h2 hδ z)
      = algebraMap (PowerSeries A) (LaurentSeries A) (directionRadicalSeries h2 (hδ z)) := rfl

theorem two_ne_zero_directionField (h2 : (2 : A) ≠ 0) (hδ : ∀ z, detuning d i z ≠ 0) :
    (2 : ↥(directionField h2 hδ)) ≠ 0 := by
  intro hcon
  have h1 : (2 : RatFunc A) = 0 :=
    (algebraMap (RatFunc A) ↥(directionField h2 hδ)).injective
      (by rw [map_ofNat, map_zero]; exact hcon)
  have h3 : (2 : Polynomial A) = 0 :=
    (IsFractionRing.injective (Polynomial A) (RatFunc A))
      (by rw [map_ofNat, map_zero]; exact h1)
  exact h2 (Polynomial.C_eq_zero.mp (by rw [map_ofNat]; exact h3))

/-- The labelled roots of the direction, inside its radical field. -/
def dirRootField (h2 : (2 : A) ≠ 0) (hδ : ∀ z, detuning d i z ≠ 0)
    (x : Fin (m + 1) → Bool) : ↥(directionField h2 hδ) :=
  directionRoot (fun z => dirBase h2 hδ (edgeSum d i z)) (directionFieldRadical h2 hδ) i x

theorem val_dirRootField (h2 : (2 : A) ≠ 0) (hδ : ∀ z, detuning d i z ≠ 0)
    (x : Fin (m + 1) → Bool) :
    (directionField h2 hδ).val (dirRootField h2 hδ x)
      = algebraMap (PowerSeries A) (LaurentSeries A)
          (psDirectionRoot (fun z => edgeSum d i z)
            (fun z => directionRadicalSeries h2 (hδ z)) i x) := by
  rw [map_psDirectionRoot (algebraMap (PowerSeries A) (LaurentSeries A)) h2, dirRootField,
    map_directionRoot]
  congr 1
  funext z
  exact val_dirBase h2 hδ (edgeSum d i z)

theorem constantCoeff_psDirectionRoot_edgeSum (h2 : (2 : A) ≠ 0)
    (hδ : ∀ z, detuning d i z ≠ 0) (x : Fin (m + 1) → Bool) :
    PowerSeries.constantCoeff (psDirectionRoot (fun z => edgeSum d i z)
      (fun z => directionRadicalSeries h2 (hδ z)) i x) = d x :=
  constantCoeff_psDirectionRoot h2 d (fun z => edgeSum d i z)
    (fun z => directionRadicalSeries h2 (hδ z)) i (fun _ => rfl)
    (fun z => constantCoeff_directionRadicalSeries h2 (hδ z)) x

theorem dirRootField_injective (h2 : (2 : A) ≠ 0) (hδ : ∀ z, detuning d i z ≠ 0)
    (hd : Function.Injective d) : Function.Injective (dirRootField h2 hδ) := by
  intro x y hxy
  have hval := congrArg (directionField h2 hδ).val hxy
  rw [val_dirRootField, val_dirRootField] at hval
  have hps := (IsFractionRing.injective (PowerSeries A) (LaurentSeries A)) hval
  have := congrArg (PowerSeries.constantCoeff (R := A)) hps
  rw [constantCoeff_psDirectionRoot_edgeSum, constantCoeff_psDirectionRoot_edgeSum] at this
  exact hd this


/-- The direction's picture of the coefficient ring: the chosen coupling stays in the base field of
the radical extension, every other coupling becomes a deformation parameter. -/
def dirDeform (h2 : (2 : A) ≠ 0) (hδ : ∀ z, detuning d i z ≠ 0) :
    MvPolynomial (Fin (m + 1)) A →+*
      MvPowerSeries {j : Fin (m + 1) // j ≠ i} ↥(directionField h2 hδ) :=
  MvPolynomial.eval₂Hom
    ((MvPowerSeries.C : ↥(directionField h2 hδ) →+*
      MvPowerSeries {j : Fin (m + 1) // j ≠ i} ↥(directionField h2 hδ)).comp (dirBase h2 hδ))
    (fun j => if h : j = i then
      (MvPowerSeries.C (dirVar h2 hδ) :
        MvPowerSeries {j : Fin (m + 1) // j ≠ i} ↥(directionField h2 hδ))
      else MvPowerSeries.X ⟨j, h⟩)

theorem dirDeform_C (h2 : (2 : A) ≠ 0) (hδ : ∀ z, detuning d i z ≠ 0) (a : A) :
    dirDeform h2 hδ (MvPolynomial.C a) = MvPowerSeries.C (dirBase h2 hδ a) :=
  MvPolynomial.eval₂Hom_C _ _ a

theorem dirDeform_X_self (h2 : (2 : A) ≠ 0) (hδ : ∀ z, detuning d i z ≠ 0) :
    dirDeform h2 hδ (MvPolynomial.X i) = MvPowerSeries.C (dirVar h2 hδ) := by
  rw [dirDeform, MvPolynomial.eval₂Hom_X']
  exact dif_pos rfl

theorem dirDeform_X_ne (h2 : (2 : A) ≠ 0) (hδ : ∀ z, detuning d i z ≠ 0) {j : Fin (m + 1)}
    (h : j ≠ i) : dirDeform h2 hδ (MvPolynomial.X j) = MvPowerSeries.X ⟨j, h⟩ := by
  rw [dirDeform, MvPolynomial.eval₂Hom_X']
  exact dif_neg h

theorem directionFieldRadical_sq_block (h2 : (2 : A) ≠ 0) (hδ : ∀ z, detuning d i z ≠ 0)
    (z : Fin m → Bool) :
    directionFieldRadical h2 hδ z * directionFieldRadical h2 hδ z
      = (dirBase h2 hδ (cubeSide d i false z) + dirBase h2 hδ (cubeSide d i true z))
        * (dirBase h2 hδ (cubeSide d i false z) + dirBase h2 hδ (cubeSide d i true z))
        - 4 * (dirBase h2 hδ (cubeSide d i false z) * dirBase h2 hδ (cubeSide d i true z)
            - dirVar h2 hδ * dirVar h2 hδ) := by
  have hpoly : (Polynomial.C (detuning d i z * detuning d i z)
        + Polynomial.C (4 : A) * Polynomial.X ^ 2)
      = (Polynomial.C (cubeSide d i false z) + Polynomial.C (cubeSide d i true z))
          * (Polynomial.C (cubeSide d i false z) + Polynomial.C (cubeSide d i true z))
        - 4 * (Polynomial.C (cubeSide d i false z) * Polynomial.C (cubeSide d i true z)
            - Polynomial.X * Polynomial.X) := by
    rw [detuning, map_mul, map_sub, map_ofNat]
    ring
  rw [directionFieldRadical_sq, hpoly]
  simp only [map_sub, map_add, map_mul, map_ofNat]
  rfl

theorem dirBase_mem_baseRange (h2 : (2 : A) ≠ 0) (hδ : ∀ z, detuning d i z ≠ 0) (a : A) :
    dirBase h2 hδ a ∈ baseRange (RatFunc A) ↥(directionField h2 hδ) :=
  ⟨algebraMap (Polynomial A) (RatFunc A) (Polynomial.C a), rfl⟩

/-- **The deformed polynomial reduces to the split direction polynomial.** -/
theorem map_dirDeform_constantCoeff (h2 : (2 : A) ≠ 0) (hδ : ∀ z, detuning d i z ≠ 0) :
    ((universalCharpoly A (m + 1) d).map (dirDeform h2 hδ)).map
        (MvPowerSeries.constantCoeff (σ := {j : Fin (m + 1) // j ≠ i})
          (R := ↥(directionField h2 hδ)))
      = ∏ x, (X - C (dirRootField h2 hδ x)) := by
  classical
  have hsfun : (fun z => cubeSide (fun x => dirBase h2 hδ (d x)) i false z
        + cubeSide (fun x => dirBase h2 hδ (d x)) i true z)
      = fun z => dirBase h2 hδ (edgeSum d i z) := by
    funext z
    rw [edgeSum, map_add]
    rfl
  rw [Polynomial.map_map,
    map_universalCharpoly_of_eval d i
      ((MvPowerSeries.constantCoeff (σ := {j : Fin (m + 1) // j ≠ i})
        (R := ↥(directionField h2 hδ))).comp (dirDeform h2 hδ))
      (dirBase h2 hδ) (dirVar h2 hδ)
      (fun a => by rw [RingHom.comp_apply, dirDeform_C, MvPowerSeries.constantCoeff_C])
      (by rw [RingHom.comp_apply, dirDeform_X_self, MvPowerSeries.constantCoeff_C])
      (fun j hj => by rw [RingHom.comp_apply, dirDeform_X_ne h2 hδ hj,
        MvPowerSeries.constantCoeff_X]),
    charpoly_singleDirectionHam_eq_prod (two_ne_zero_directionField h2 hδ)
      (fun x => dirBase h2 hδ (d x)) (dirVar h2 hδ) i (directionFieldRadical h2 hδ)
      (fun z => directionFieldRadical_sq_block h2 hδ z),
    hsfun]
  rfl

/-- **The deformed labelled root family of one direction.** -/
theorem exists_deformationRootFamily (h2 : (2 : A) ≠ 0) (hδ : ∀ z, detuning d i z ≠ 0)
    (hd : Function.Injective d) :
    ∃ Θ' : (Fin (m + 1) → Bool) →
        MvPowerSeries {j : Fin (m + 1) // j ≠ i} ↥(directionField h2 hδ),
      (universalCharpoly A (m + 1) d).map (dirDeform h2 hδ) = ∏ x, (X - C (Θ' x)) ∧
        ∀ x, MvPowerSeries.constantCoeff (Θ' x) = dirRootField h2 hδ x :=
  exists_mvPowerSeriesRootFamily ↥(directionField h2 hδ) (dirRootField h2 hδ)
    (dirRootField_injective h2 hδ hd) {j : Fin (m + 1) // j ≠ i}
    ((universalCharpoly A (m + 1) d).map (dirDeform h2 hδ))
    ((universalCharpoly_monic A (m + 1) d).map _) (map_dirDeform_constantCoeff h2 hδ)

/-- **Every hypercube edge swap of the direction is realized on its radical field.** -/
theorem exists_algEquiv_swap_dirRootField (h2 : (2 : A) ≠ 0)
    (hδ : ∀ z, detuning d i z ≠ 0) (hδinj : Function.Injective (detuning d i))
    (hδne : ∀ z z', detuning d i z ≠ -detuning d i z') (x : Fin (m + 1) → Bool) :
    ∃ σ : ↥(directionField h2 hδ) ≃ₐ[RatFunc A] ↥(directionField h2 hδ),
      ∀ y, σ (dirRootField h2 hδ y)
        = dirRootField h2 hδ (Equiv.swap x (boolToggle x i) y) :=
  exists_algEquiv_swap_directionRoot (fun z => dirBase h2 hδ (edgeSum d i z))
    (directionFieldRadical h2 hδ) (fun z => dirBase_mem_baseRange h2 hδ (edgeSum d i z))
    (fun z₀ => exists_directionFlip h2 hδ hδinj hδne z₀) i x

theorem map_comp_dirDeform (h2 : (2 : A) ≠ 0) (hδ : ∀ z, detuning d i z ≠ 0)
    (σ : ↥(directionField h2 hδ) ≃ₐ[RatFunc A] ↥(directionField h2 hδ)) :
    (MvPowerSeries.map (σ.toRingEquiv : ↥(directionField h2 hδ) →+*
        ↥(directionField h2 hδ))).comp (dirDeform h2 hδ) = dirDeform h2 hδ := by
  classical
  refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)
  · rw [RingHom.comp_apply, dirDeform_C, MvPowerSeries.map_C, dirBase, RingHom.comp_apply,
      RingHom.comp_apply]
    congr 1
    exact σ.commutes _
  · by_cases hj : j = i
    · subst hj
      rw [RingHom.comp_apply, dirDeform_X_self, MvPowerSeries.map_C, dirVar]
      congr 1
      exact σ.commutes _
    · rw [RingHom.comp_apply, dirDeform_X_ne h2 hδ hj, MvPowerSeries.map_X]

end

end GaloisForLFunctions.HTGeometry
