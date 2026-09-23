import GaloisForLFunctions.HTGeometry.PowerSeriesDirectionRoot
import GaloisForLFunctions.HTGeometry.TwoLocalGenericFamily

/-!
# The single-direction characteristic polynomial splits over its radical extension

Adjoining the square roots of the block discriminants splits the characteristic polynomial of a
Hamiltonian with one transverse coupling into linear factors, labelled by the hypercube.  The same
factorization holds one level lower, over the power series ring, because the roots are power series
whose images in the field are those linear factors' roots.

## Main results

* `map_singleDirectionHam`, `map_transverseFamilyHam` — the families commute with coefficient maps.
* `charpoly_singleDirectionHam_eq_prod` — the splitting over a field.
* `charpoly_singleDirectionHam_eq_prod_powerSeries` — the splitting over the power series ring.
-/

open Polynomial
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {R S : Type*} [CommRing R] [CommRing S] {m n : ℕ}

theorem map_singleDirectionHam (f : R →+* S) (d : (Fin n → Bool) → R) (u : R) (i : Fin n) :
    (singleDirectionHam d u i).map f = singleDirectionHam (fun x => f (d x)) (f u) i := by
  classical
  ext x y
  rw [Matrix.map_apply, singleDirectionHam, singleDirectionHam]
  by_cases hxy : x = y
  · rw [if_pos hxy, if_pos hxy]
  · rw [if_neg hxy, if_neg hxy]
    by_cases hy : y = boolToggle x i
    · rw [if_pos hy, if_pos hy]
    · rw [if_neg hy, if_neg hy, map_zero]

theorem map_transverseFamilyHam (f : R →+* S) (d : (Fin n → Bool) → R) (u : Fin n → R) :
    (transverseFamilyHam d u).map f = transverseFamilyHam (fun x => f (d x)) (fun j => f (u j)) := by
  classical
  ext x y
  rw [Matrix.map_apply, transverseFamilyHam, transverseFamilyHam]
  by_cases hxy : x = y
  · rw [if_pos hxy, if_pos hxy]
  · rw [if_neg hxy, if_neg hxy, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hy : y = boolToggle x j
    · rw [if_pos hy, if_pos hy]
    · rw [if_neg hy, if_neg hy, map_zero]

variable {K : Type*} [Field K]

/-- **The single-direction characteristic polynomial splits over a field carrying the block
radicals.** -/
theorem charpoly_singleDirectionHam_eq_prod [DecidableEq K] (h2 : (2 : K) ≠ 0)
    (d : (Fin (m + 1) → Bool) → K) (u : K) (i : Fin (m + 1)) (r : (Fin m → Bool) → K)
    (hr : ∀ z, r z * r z
      = (cubeSide d i false z + cubeSide d i true z) * (cubeSide d i false z + cubeSide d i true z)
        - 4 * (cubeSide d i false z * cubeSide d i true z - u * u)) :
    (singleDirectionHam d u i).charpoly
      = ∏ x : Fin (m + 1) → Bool,
          (X - C (directionRoot (fun z => cubeSide d i false z + cubeSide d i true z) r i x)) := by
  classical
  refine (charpoly_singleDirectionHam d u i).trans ?_
  refine (prod_cubeQuadRoot h2 (fun z => cubeSide d i false z + cubeSide d i true z)
    (fun z => cubeSide d i false z * cubeSide d i true z - u * u) r hr).trans ?_
  exact (Fintype.prod_equiv (cubeRelabel (Equiv.swap 0 i)) _ _ fun x => rfl).symm

variable {A : Type} [Field A]

/-- **The same splitting one level lower, over the power series ring.** -/
theorem charpoly_singleDirectionHam_eq_prod_powerSeries (h2 : (2 : A) ≠ 0)
    (d : (Fin (m + 1) → Bool) → A) (i : Fin (m + 1)) (ρ : (Fin m → Bool) → PowerSeries A)
    (hρ : ∀ z, ρ z * ρ z
      = PowerSeries.C ((cubeSide d i true z - cubeSide d i false z)
          * (cubeSide d i true z - cubeSide d i false z))
        + PowerSeries.C (4 : A) * PowerSeries.X ^ (2 : ℕ)) :
    (singleDirectionHam (fun x => PowerSeries.C (d x)) PowerSeries.X i).charpoly
      = ∏ x : Fin (m + 1) → Bool,
          (X - C (psDirectionRoot (fun z => cubeSide d i false z + cubeSide d i true z) ρ i x)) := by
  classical
  set φ : PowerSeries A →+* LaurentSeries A := algebraMap (PowerSeries A) (LaurentSeries A) with hφ
  have hinjφ : Function.Injective φ := IsFractionRing.injective (PowerSeries A) (LaurentSeries A)
  refine Polynomial.map_injective φ hinjφ ?_
  have h2L : (2 : LaurentSeries A) ≠ 0 := by
    intro hcon
    exact h2 (by
      have : φ (PowerSeries.C (2 : A)) = 0 := by rw [map_ofNat, map_ofNat]; exact hcon
      have h1 : PowerSeries.C (2 : A) = 0 := hinjφ (by rw [this, map_zero])
      have := congrArg (PowerSeries.constantCoeff (R := A)) h1
      simpa using this)
  have hsfun : (fun z => cubeSide (fun x => φ (PowerSeries.C (d x))) i false z
        + cubeSide (fun x => φ (PowerSeries.C (d x))) i true z)
      = fun z => φ (PowerSeries.C (cubeSide d i false z + cubeSide d i true z)) := by
    funext z
    rw [map_add, map_add]
    rfl
  rw [← Matrix.charpoly_map, map_singleDirectionHam]
  rw [charpoly_singleDirectionHam_eq_prod h2L (fun x => φ (PowerSeries.C (d x))) (φ PowerSeries.X) i
    (fun z => φ (ρ z)) ?_]
  · rw [Polynomial.map_prod]
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      map_psDirectionRoot φ h2 (fun z => cubeSide d i false z + cubeSide d i true z) ρ i x,
      hsfun]
  · intro z
    have hcs : ∀ b : Bool, cubeSide (fun x => φ (PowerSeries.C (d x))) i b z
        = φ (PowerSeries.C (cubeSide d i b z)) := fun _ => rfl
    rw [hcs, hcs, ← map_mul, hρ z]
    have key : (PowerSeries.C ((cubeSide d i true z - cubeSide d i false z)
          * (cubeSide d i true z - cubeSide d i false z))
        + PowerSeries.C (4 : A) * PowerSeries.X ^ (2 : ℕ))
        = (PowerSeries.C (cubeSide d i false z) + PowerSeries.C (cubeSide d i true z))
            * (PowerSeries.C (cubeSide d i false z) + PowerSeries.C (cubeSide d i true z))
          - 4 * (PowerSeries.C (cubeSide d i false z) * PowerSeries.C (cubeSide d i true z)
              - PowerSeries.X * PowerSeries.X) := by
      rw [map_mul, map_sub, map_ofNat]
      ring
    rw [key]
    simp only [map_sub, map_add, map_mul, map_ofNat]

end
end GaloisForLFunctions.HTGeometry
