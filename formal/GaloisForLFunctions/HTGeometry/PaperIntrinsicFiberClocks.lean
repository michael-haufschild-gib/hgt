import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.AllFibers
import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.CoordinateDerivation
import GaloisForLFunctions.HTGeometry.CoordinateDerivationCommute
import GaloisForLFunctions.HTGeometry.FreeCoordinateConstantKernel

/-!
Every exact fibre of the source polynomial has three independent commuting
locally nilpotent clocks. Their common kernel is exactly ℂ. The fibre coordinates
come from the source's proved affine-three-space equivalences; the constant-kernel
and commutation arguments reuse the native corpus.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate MvPolynomial

/-- The three polynomial coordinates on an actual fibre. -/
def paperIntrinsicFiberCoordinate (t : ℂ) (i : Fin 3) : FiberRing t :=
  (exactFiberEquiv t).symm (X i)

/-- A polynomial clock intrinsic to the level `t`. -/
def paperIntrinsicFiberClock (t : ℂ) (i : Fin 3) :
    Derivation ℂ (FiberRing t) (FiberRing t) :=
  CoordinateDerivation.coordinatePartial (exactFiberEquiv t).symm i

theorem paperIntrinsicFiberClock_apply (t : ℂ) (i : Fin 3) (p : FiberRing t) :
    paperIntrinsicFiberClock t i p =
      (exactFiberEquiv t).symm (pderiv i (exactFiberEquiv t p)) := rfl

/-- Each clock reads one on its own coordinate and zero on the others. -/
theorem paperIntrinsicFiberClock_coordinate (t : ℂ) (i j : Fin 3) :
    paperIntrinsicFiberClock t i (paperIntrinsicFiberCoordinate t j) =
      if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst j
    simp [paperIntrinsicFiberClock, paperIntrinsicFiberCoordinate]
  · simpa [paperIntrinsicFiberClock, paperIntrinsicFiberCoordinate, h] using
      CoordinateDerivation.coordinatePartial_other (exactFiberEquiv t).symm
        (i := i) (j := j) (Ne.symm h)

theorem paperIntrinsicFiberClock_ne_zero (t : ℂ) (i : Fin 3) :
    paperIntrinsicFiberClock t i ≠ 0 := by
  intro h
  have hh := congrArg
    (fun D : Derivation ℂ (FiberRing t) (FiberRing t) =>
      exactFiberEquiv t (D (paperIntrinsicFiberCoordinate t i))) h
  simp [paperIntrinsicFiberClock_coordinate] at hh

theorem paperIntrinsicFiberClock_iterate (t : ℂ) (i : Fin 3)
    (n : ℕ) (p : FiberRing t) :
    ((paperIntrinsicFiberClock t i)^[n]) p =
      (exactFiberEquiv t).symm
        (((pderiv i : Derivation ℂ (R 3) (R 3))^[n]) (exactFiberEquiv t p)) :=
  CoordinateDerivation.transport_iterate (exactFiberEquiv t).symm (pderiv i) n p

/-- Polynomial degree supplies an exact finite stopping bound on each element. -/
theorem paperIntrinsicFiberClock_degree_bound (t : ℂ) (i : Fin 3) (p : FiberRing t) :
    ((paperIntrinsicFiberClock t i)^[degreeOf i (exactFiberEquiv t p) + 1]) p = 0 := by
  rw [paperIntrinsicFiberClock_iterate]
  have hz : ((pderiv i : Derivation ℂ (R 3) (R 3))^[
      degreeOf i (exactFiberEquiv t p) + 1]) (exactFiberEquiv t p) = 0 := by
    apply MvPolynomial.ext
    intro m
    rw [coeff_zero]
    exact CoordinateDerivation.coeff_iterate_pderiv_eq_zero i
      (exactFiberEquiv t p) _ m (by omega)
  rw [hz, map_zero]

theorem paperIntrinsicFiberClock_locallyNilpotent (t : ℂ) (i : Fin 3) :
    ∀ p : FiberRing t, ∃ n : ℕ, ((paperIntrinsicFiberClock t i)^[n]) p = 0 :=
  fun p => ⟨_, paperIntrinsicFiberClock_degree_bound t i p⟩

/-- The intrinsic clocks commute on the whole coordinate algebra. -/
theorem paperIntrinsicFiberClock_commute (t : ℂ) (i j : Fin 3) (p : FiberRing t) :
    paperIntrinsicFiberClock t i (paperIntrinsicFiberClock t j p) =
      paperIntrinsicFiberClock t j (paperIntrinsicFiberClock t i p) := by
  simp only [paperIntrinsicFiberClock_apply, AlgEquiv.apply_symm_apply]
  rw [GaloisForLFunctions.pderiv_comm]

/-- Coordinate evaluation recovers even polynomial-valued clock coefficients. -/
theorem paperIntrinsicFiberClock_sum_coordinate (t : ℂ) (a : Fin 3 → FiberRing t)
    (j : Fin 3) :
    (∑ i : Fin 3, a i • paperIntrinsicFiberClock t i)
      (paperIntrinsicFiberCoordinate t j) = a j := by
  rw [← Derivation.coeFnAddMonoidHom_apply, map_sum, Finset.sum_apply]
  simp [Derivation.smul_apply, paperIntrinsicFiberClock_coordinate]

/-- No polynomial-coefficient linear relation among the three clocks exists. -/
theorem paperIntrinsicFiberClock_independent (t : ℂ) (a : Fin 3 → FiberRing t) :
    (∑ i : Fin 3, a i • paperIntrinsicFiberClock t i) = 0 ↔ ∀ i, a i = 0 := by
  constructor
  · intro h i
    have hi := congrArg (fun D : Derivation ℂ (FiberRing t) (FiberRing t) =>
      D (paperIntrinsicFiberCoordinate t i)) h
    simpa only [paperIntrinsicFiberClock_sum_coordinate, Derivation.zero_apply] using hi
  · intro h
    apply Derivation.ext
    intro p
    rw [← Derivation.coeFnAddMonoidHom_apply, map_sum, Finset.sum_apply]
    simp [Derivation.smul_apply, h]

/-- The three clocks together leave precisely the complex scalars invariant. -/
theorem paperIntrinsicFiberClock_common_kernel (t : ℂ) (p : FiberRing t) :
    (∀ i, paperIntrinsicFiberClock t i p = 0) ↔
      ∃ c : ℂ, p = algebraMap ℂ (FiberRing t) c := by
  constructor
  · intro h
    have hg : ∀ i, pderiv i (exactFiberEquiv t p) = 0 := by
      intro i
      have hi := congrArg (exactFiberEquiv t) (h i)
      simpa only [paperIntrinsicFiberClock_apply, AlgEquiv.apply_symm_apply,
        map_zero] using hi
    obtain ⟨c, hc⟩ := exists_C_of_forall_pderiv_eq_zero hg
    refine ⟨c, (exactFiberEquiv t).injective ?_⟩
    simpa only [AlgEquiv.commutes, MvPolynomial.algebraMap_eq] using hc
  · rintro ⟨c, rfl⟩ i
    exact (paperIntrinsicFiberClock t i).map_algebraMap c

end GaloisForLFunctions.HTGeometry
