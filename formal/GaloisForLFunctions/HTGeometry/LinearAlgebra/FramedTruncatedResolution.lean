import GaloisForLFunctions.HTGeometry.ABHN.CyclicCompanionResolution
import GaloisForLFunctions.RHTower.Deninger.DeningerKerRangeCongr

/-!
# The truncated periodic resolution in an arbitrary frame

Changing coordinates by an invertible matrix preserves both exactness
identities of the nilpotent cyclic companion. The existing three-term
exactness transport handles the coordinate change.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open ABHN Matrix

variable {K : Type*} [Field K]

/-- The nilpotent companion expressed in a prescribed invertible frame. -/
def framedCyclicShift (n : ℕ) (P : (Matrix (Fin (n + 1)) (Fin (n + 1)) K)ˣ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  P.inv * cyclicCompanionMatrix n 0 * P.val

/-- Both alternating maps remain exact in every invertible coordinate frame. -/
theorem framedCyclicShift_periodic_exact (n : ℕ)
    (P : (Matrix (Fin (n + 1)) (Fin (n + 1)) K)ˣ) :
    LinearMap.range (framedCyclicShift n P).mulVecLin =
        LinearMap.ker (framedCyclicShift n P ^ n).mulVecLin ∧
      LinearMap.range (framedCyclicShift n P ^ n).mulVecLin =
        LinearMap.ker (framedCyclicShift n P).mulVecLin := by
  let e := Matrix.toLin'OfInv P.val_inv P.inv_val
  have hsem : SemiconjBy P.inv (cyclicCompanionMatrix n (0 : K)) (framedCyclicShift n P) := by
    change P.inv * cyclicCompanionMatrix n 0 = framedCyclicShift n P * P.inv
    simp only [framedCyclicShift, mul_assoc, P.val_inv, mul_one]
  have hint (q : ℕ) :
      e.toLinearMap ∘ₗ (cyclicCompanionMatrix n (0 : K) ^ q).mulVecLin =
        (framedCyclicShift n P ^ q).mulVecLin ∘ₗ e.toLinearMap := by
    change P.inv.mulVecLin ∘ₗ (cyclicCompanionMatrix n (0 : K) ^ q).mulVecLin =
      (framedCyclicShift n P ^ q).mulVecLin ∘ₗ P.inv.mulVecLin
    rw [← Matrix.mulVecLin_mul, ← Matrix.mulVecLin_mul]
    exact congrArg Matrix.mulVecLin (hsem.pow_right q)
  have hfirst : e.toLinearMap ∘ₗ (cyclicCompanionMatrix n (0 : K)).mulVecLin =
      (framedCyclicShift n P).mulVecLin ∘ₗ e.toLinearMap := by
    simpa only [pow_one] using hint 1
  have h := cyclicCompanionMatrix_zero_periodic_exact (R := K) n
  constructor
  · exact (RHTower.deningerKer_eq_range_congr _ _ _ _ e e e hfirst (hint n) h.1.symm).symm
  · exact (RHTower.deningerKer_eq_range_congr _ _ _ _ e e e (hint n) hfirst h.2.symm).symm

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.framedCyclicShift_periodic_exact
