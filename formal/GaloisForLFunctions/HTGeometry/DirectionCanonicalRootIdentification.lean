import GaloisForLFunctions.HTGeometry.DirectionCharpolySplit
import GaloisForLFunctions.HTGeometry.MvPowerSeriesDirectionSplit
import GaloisForLFunctions.HTGeometry.TwoLocalCanonicalRoots
import GaloisForLFunctions.HTGeometry.ResidueRootFamilyTransfer

/-!
# The canonical labelled root family, seen in one direction

Reducing every transverse coupling but one leaves the single-direction family, whose roots are the
power series built from the block radicals.  Both families are roots of the same polynomial with the
same value at zero coupling, so a simple root is determined by that value and the two agree.  This
is what makes the labelling of the roots independent of which direction is being analyzed.

## Main results

* `dirRes_universalTransverseHam`, `dirRes_universalCharpoly` — the reduction of the universal
  family to one direction.
* `dirRes_canonicalRoot` — **the canonical root reduces to the direction root of the same label.**
-/

open Polynomial
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {A : Type} [Field A] {m : ℕ}

/-- Evaluating the universal transverse family at a single nonzero coupling. -/
theorem map_universalTransverseHam_of_eval {R : Type*} [CommRing R]
    (d : (Fin (m + 1) → Bool) → A) (i : Fin (m + 1))
    (g : MvPolynomial (Fin (m + 1)) A →+* R) (f : A →+* R) (u : R)
    (hC : ∀ a, g (MvPolynomial.C a) = f a) (hXi : g (MvPolynomial.X i) = u)
    (hXne : ∀ j, j ≠ i → g (MvPolynomial.X j) = 0) :
    (universalTransverseHam A (m + 1) d).map g
      = singleDirectionHam (fun x => f (d x)) u i := by
  classical
  rw [universalTransverseHam, map_transverseFamilyHam]
  have hfun : (fun x => g (MvPolynomial.C (d x))) = fun x => f (d x) :=
    funext fun x => hC (d x)
  rw [hfun, transverseFamilyHam_eq_singleDirection (fun x => f (d x))
    (fun j => g (MvPolynomial.X j)) i hXne, hXi]

theorem map_universalCharpoly_of_eval {R : Type*} [CommRing R]
    (d : (Fin (m + 1) → Bool) → A) (i : Fin (m + 1))
    (g : MvPolynomial (Fin (m + 1)) A →+* R) (f : A →+* R) (u : R)
    (hC : ∀ a, g (MvPolynomial.C a) = f a) (hXi : g (MvPolynomial.X i) = u)
    (hXne : ∀ j, j ≠ i → g (MvPolynomial.X j) = 0) :
    (universalCharpoly A (m + 1) d).map g
      = (singleDirectionHam (fun x => f (d x)) u i).charpoly := by
  rw [universalCharpoly, ← Matrix.charpoly_map,
    map_universalTransverseHam_of_eval d i g f u hC hXi hXne]

theorem dirRes_universalTransverseHam (d : (Fin (m + 1) → Bool) → A) (i : Fin (m + 1)) :
    (universalTransverseHam A (m + 1) d).map
        ((dirRes A i).comp
          (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin (m + 1)) (R := A)))
      = singleDirectionHam (fun x => PowerSeries.C (d x)) PowerSeries.X i := by
  classical
  set ψ : MvPolynomial (Fin (m + 1)) A →+* PowerSeries A :=
    (dirRes A i).comp (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin (m + 1)) (R := A))
    with hψ
  have hC : ∀ a : A, ψ (MvPolynomial.C a) = PowerSeries.C a := fun a => dirRes_coe_C i a
  have hXi : ψ (MvPolynomial.X i) = PowerSeries.X := dirRes_coe_X_self i
  have hXne : ∀ j, j ≠ i → ψ (MvPolynomial.X j) = 0 := fun j hj => dirRes_coe_X_ne hj
  rw [universalTransverseHam, map_transverseFamilyHam]
  have hfun : (fun x => ψ (MvPolynomial.C (d x))) = fun x => PowerSeries.C (d x) :=
    funext fun x => hC (d x)
  rw [hfun, transverseFamilyHam_eq_singleDirection (fun x => PowerSeries.C (d x))
    (fun j => ψ (MvPolynomial.X j)) i hXne, hXi]

theorem dirRes_universalCharpoly (d : (Fin (m + 1) → Bool) → A) (i : Fin (m + 1)) :
    (universalCharpoly A (m + 1) d).map
        ((dirRes A i).comp
          (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin (m + 1)) (R := A)))
      = (singleDirectionHam (fun x => PowerSeries.C (d x)) PowerSeries.X i).charpoly := by
  rw [universalCharpoly, ← Matrix.charpoly_map, dirRes_universalTransverseHam]

/-- **The canonical root of a hypercube point reduces to the direction root of the same point.** -/
theorem dirRes_canonicalRoot (h2 : (2 : A) ≠ 0) {d : (Fin (m + 1) → Bool) → A}
    (hd : Function.Injective d) (i : Fin (m + 1)) (ρ : (Fin m → Bool) → PowerSeries A)
    (hρsq : ∀ z, ρ z * ρ z
      = PowerSeries.C ((cubeSide d i true z - cubeSide d i false z)
          * (cubeSide d i true z - cubeSide d i false z))
        + PowerSeries.C (4 : A) * PowerSeries.X ^ 2)
    (hρconst : ∀ z, PowerSeries.constantCoeff (ρ z)
      = cubeSide d i true z - cubeSide d i false z)
    {Θ : (Fin (m + 1) → Bool) → MvPowerSeries (Fin (m + 1)) A}
    (hΘ : universalCharpolySeries d = ∏ x, (X - C (Θ x)))
    (hconst : ∀ x, MvPowerSeries.constantCoeff (Θ x) = d x) (x : Fin (m + 1) → Bool) :
    dirRes A i (Θ x)
      = psDirectionRoot (fun z => cubeSide d i false z + cubeSide d i true z) ρ i x := by
  classical
  set s : (Fin m → Bool) → A := fun z => cubeSide d i false z + cubeSide d i true z with hs
  set ψ : MvPolynomial (Fin (m + 1)) A →+* PowerSeries A :=
    (dirRes A i).comp (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin (m + 1)) (R := A))
    with hψ
  set F : Polynomial (PowerSeries A) := (universalCharpoly A (m + 1) d).map ψ with hF
  have hcc : ∀ w, PowerSeries.constantCoeff (psDirectionRoot s ρ i w) = d w := fun w =>
    constantCoeff_psDirectionRoot h2 d s ρ i (fun _ => rfl) hρconst w
  have hFprod : F = ∏ w, (X - C (psDirectionRoot s ρ i w)) := by
    rw [hF, dirRes_universalCharpoly, charpoly_singleDirectionHam_eq_prod_powerSeries h2 d i ρ hρsq]
  have hFmap : F = (universalCharpolySeries d).map (dirRes A i) := by
    rw [hF, universalCharpolySeries, Polynomial.map_map]
  have hroot2 : F.IsRoot (dirRes A i (Θ x)) := by
    rw [hFmap]
    show Polynomial.eval (dirRes A i (Θ x)) ((universalCharpolySeries d).map (dirRes A i)) = 0
    rw [Polynomial.eval_map_apply]
    have hzero : Polynomial.eval (Θ x) (universalCharpolySeries d) = 0 := by
      rw [hΘ, Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ x) (by simp)
    rw [hzero, map_zero]
  have hroot1 : F.IsRoot (psDirectionRoot s ρ i x) := by
    rw [hFprod]
    show Polynomial.eval (psDirectionRoot s ρ i x) (∏ w, (X - C (psDirectionRoot s ρ i w))) = 0
    rw [Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ x) (by simp)
  have hderiv : PowerSeries.constantCoeff
      ((Polynomial.derivative F).eval (psDirectionRoot s ρ i x)) ≠ 0 := by
    rw [hFprod, eval_derivative_prod_X_sub_C, map_prod]
    refine Finset.prod_ne_zero_iff.mpr fun w hw => ?_
    rw [map_sub, hcc x, hcc w]
    intro h0
    exact (Finset.mem_erase.mp hw).1 (hd (sub_eq_zero.mp h0)).symm
  have hres : PowerSeries.constantCoeff (psDirectionRoot s ρ i x)
      = PowerSeries.constantCoeff (dirRes A i (Θ x)) := by
    rw [hcc x, constantCoeff_dirRes, hconst x]
  exact (isRoot_unique_mvPowerSeries (σ := Unit) (R := A) hroot1 hroot2 hderiv hres).symm

end

end GaloisForLFunctions.HTGeometry
