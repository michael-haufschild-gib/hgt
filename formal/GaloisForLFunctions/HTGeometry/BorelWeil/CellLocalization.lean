import GaloisForLFunctions.HTGeometry.BorelWeil.CellMinors
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Localizing at the cell equations

Sections of `L_λ` over a Bruhat cell, or over an intersection of cells, are regular functions with
denominators a power of the corresponding cell equations.  All of them live inside the localization
of the polynomial ring at the product `totalDenom` of every cell equation — the sections over the
intersection of all the cells.  This file constructs that localization and, using the semi-invariance
of `CellMinors`, extends the right Borel translation to it.

That extension is what makes "the `λ`-semi-invariant elements with denominators from `I`" a
meaningful object for each set `I` of cells, hence what the Čech complex of the Bruhat cover is
assembled from.

## Main definitions

* `GaloisForLFunctions.HTGeometry.BorelWeil.cellChar`, `totalDenom`
* `GaloisForLFunctions.HTGeometry.BorelWeil.FlagLoc` — the ambient localization.
* `GaloisForLFunctions.HTGeometry.BorelWeil.substRightAway` — the Borel action on it.

## Main results

* `substRight_cellDenomPoly`, `substRight_totalDenom` — the cell equations are Borel semi-invariant.
* `substRightAway_algebraMap` — the extension restricts to `substRight` on polynomials.
-/

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k]

/-- The scalar by which right translation by `B` scales the `σ`-cell equation. -/
noncomputable def cellChar (N : ℕ) (k : Type*) [Field k] (σ : Equiv.Perm (Fin N))
    (B : Matrix (Fin N) (Fin N) k) : k :=
  ∏ j : Fin N, ∏ i : Fin N, (if (i : ℕ) < (j : ℕ) + 1 then B i i else 1)

theorem cellChar_ne_zero (σ : Equiv.Perm (Fin N)) {B : Matrix (Fin N) (Fin N) k}
    (hB : IsBorelMat B) : cellChar N k σ B ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun j _ => Finset.prod_ne_zero_iff.mpr fun i _ => ?_
  by_cases h : (i : ℕ) < (j : ℕ) + 1
  · rw [if_pos h]; exact hB.2 i
  · rw [if_neg h]; exact one_ne_zero

theorem substRight_cellDenomPoly [Infinite k] (σ : Equiv.Perm (Fin N))
    {B : Matrix (Fin N) (Fin N) k} (hB : B.BlockTriangular id) :
    substRight B (cellDenomPoly N k σ)
      = MvPolynomial.C (cellChar N k σ B) * cellDenomPoly N k σ := by
  rw [cellDenomPoly, map_prod, cellChar, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [substRight_minorPolyAt σ ((j : ℕ) + 1) hB]

/-- The product of all the cell equations: its nonvanishing locus is the intersection of every
Bruhat cell. -/
noncomputable def totalDenom (N : ℕ) (k : Type*) [Field k] : MvPolynomial (Fin N × Fin N) k :=
  ∏ σ : Equiv.Perm (Fin N), cellDenomPoly N k σ

theorem totalDenom_ne_zero : totalDenom N k ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun σ _ => cellDenomPoly_ne_zero σ

theorem substRight_totalDenom [Infinite k] {B : Matrix (Fin N) (Fin N) k}
    (hB : B.BlockTriangular id) :
    substRight B (totalDenom N k)
      = MvPolynomial.C (∏ σ : Equiv.Perm (Fin N), cellChar N k σ B) * totalDenom N k := by
  rw [totalDenom, map_prod, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun σ _ => ?_
  rw [substRight_cellDenomPoly σ hB]

/-- The ambient localization: regular functions on the intersection of all the Bruhat cells. -/
noncomputable abbrev FlagLoc (N : ℕ) (k : Type*) [Field k] :=
  Localization.Away (totalDenom N k)

theorem isUnit_algebraMap_totalDenom :
    IsUnit (algebraMap (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k) (totalDenom N k)) := by
  exact IsLocalization.map_units (M := Submonoid.powers (totalDenom N k))
    (FlagLoc N k) ⟨totalDenom N k, Submonoid.mem_powers _⟩

/-- Right translation by a Borel element, extended to the localization. -/
noncomputable def substRightAway [Infinite k] {B : Matrix (Fin N) (Fin N) k} (hB : IsBorelMat B) :
    FlagLoc N k →+* FlagLoc N k :=
  IsLocalization.Away.lift (S := FlagLoc N k) (totalDenom N k)
    (g := (algebraMap (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k)).comp
      (substRight B).toRingHom)
    (by
      have hcunit : IsUnit (∏ σ : Equiv.Perm (Fin N), cellChar N k σ B) :=
        (Finset.prod_ne_zero_iff.mpr fun σ _ => cellChar_ne_zero σ hB).isUnit
      have hc : IsUnit ((MvPolynomial.C (∏ σ : Equiv.Perm (Fin N), cellChar N k σ B) :
          MvPolynomial (Fin N × Fin N) k)) :=
        hcunit.map (MvPolynomial.C : k →+* MvPolynomial (Fin N × Fin N) k)
      have hmap : ((algebraMap (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k)).comp
          (substRight B).toRingHom) (totalDenom N k)
          = algebraMap (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k)
              (MvPolynomial.C (∏ σ : Equiv.Perm (Fin N), cellChar N k σ B))
            * algebraMap (MvPolynomial (Fin N × Fin N) k) (FlagLoc N k) (totalDenom N k) := by
        rw [RingHom.comp_apply]
        show algebraMap _ _ (substRight B (totalDenom N k)) = _
        rw [substRight_totalDenom hB.1, map_mul]
      rw [hmap]
      exact (hc.map _).mul isUnit_algebraMap_totalDenom)

theorem substRightAway_algebraMap [Infinite k] {B : Matrix (Fin N) (Fin N) k} (hB : IsBorelMat B)
    (p : MvPolynomial (Fin N × Fin N) k) :
    substRightAway hB (algebraMap _ (FlagLoc N k) p) = algebraMap _ _ (substRight B p) := by
  rw [substRightAway, IsLocalization.Away.lift_eq]
  rfl

end GaloisForLFunctions.HTGeometry.BorelWeil
