import GaloisForLFunctions.HTGeometry.BoundedRandomEntireTail
import GaloisForLFunctions.HTGeometry.PacketHermiteSurjectivity

/-!
# The jet packet of the bounded random entire series splits

A finite jet packet of the clamped random series is the Hermite evaluation of its first `N` clamped
coordinates plus a term depending only on the coordinates beyond `N`, where `N` is the size of the
packet.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {H : Type*}

/-- The tail contribution to a jet packet observation. -/
def packetTailObservation (shift : H → ℂ) (p : FiniteMultivariateAffineJetPattern H 1)
    (base : MultivariateAffinePatternRow p → Fin 1 → ℂ) (y : ℕ → ℂ) :
    Fin (affineJetPacketFiniteCoordinateCount p) → ℂ :=
  fun k => iteratedDeriv
    (packetOrder p ((Fintype.equivFin (MultivariateAffinePatternRow p ×
      MultivariateAffinePatternJet p)).symm k))
    (boundedRandomEntireTail (affineJetPacketFiniteCoordinateCount p) y)
    (packetPoint shift p base ((Fintype.equivFin (MultivariateAffinePatternRow p ×
      MultivariateAffinePatternJet p)).symm k))

/-- **The packet split.** -/
theorem finiteAffineJetPacketObservation_split (shift : H → ℂ)
    (p : FiniteMultivariateAffineJetPattern H 1)
    (base : MultivariateAffinePatternRow p → Fin 1 → ℂ) (x : ℕ → ℂ) :
    finiteAffineJetPacketObservation (fun h => oneDimTranslationFrame (shift h)) p base
        (boundedRandomEntireSource x)
      = packetHermiteMap shift p base
          (clampedComplexCoefficientHead (affineJetPacketFiniteCoordinateCount p) x)
        + packetTailObservation shift p base
          (fun k => x (k + affineJetPacketFiniteCoordinateCount p)) := by
  classical
  set N : ℕ := affineJetPacketFiniteCoordinateCount p with hN
  funext k
  set kk := (Fintype.equivFin (MultivariateAffinePatternRow p ×
    MultivariateAffinePatternJet p)).symm k with hkk
  set j : ℕ := packetOrder p kk with hj
  set w : ℂ := packetPoint shift p base kk with hw
  set Pc : Polynomial ℂ :=
    ∑ n : Fin N, C (clampedComplexCoefficientHead N x n / ((4 : ℂ) *
      ((Nat.factorial (n : ℕ)) : ℂ))) * X ^ (n : ℕ) with hPc
  have hpoly : ∀ z : ℂ, Pc.eval z
      = ∑ n ∈ Finset.range N, boundedRandomEntireCoeff x n * z ^ n := by
    intro z
    rw [hPc, Polynomial.eval_finsetSum,
      Finset.sum_range fun n => boundedRandomEntireCoeff x n * z ^ n]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    rfl
  have hsplit : boundedRandomEntireFunction x
      = (fun z => Pc.eval z) + boundedRandomEntireTail N (fun k => x (k + N)) := by
    funext z
    rw [Pi.add_apply, hpoly z]
    exact boundedRandomEntireFunction_split N x z
  have hcd1 : ContDiffAt ℂ (j : WithTop ℕ∞) (fun z : ℂ => Pc.eval z) w :=
    ((Polynomial.differentiable Pc).contDiff.of_le (by exact_mod_cast le_top)).contDiffAt
  have hcd2 : ContDiffAt ℂ (j : WithTop ℕ∞)
      (boundedRandomEntireTail N (fun k => x (k + N))) w :=
    (((differentiable_boundedRandomEntireTail N (fun k => x (k + N))).contDiff).of_le
      (by exact_mod_cast le_top)).contDiffAt
  have hobs : finiteAffineJetPacketObservation (fun h => oneDimTranslationFrame (shift h)) p base
      (boundedRandomEntireSource x) k = iteratedDeriv j (boundedRandomEntireFunction x) w :=
    multivariateAffinePatternObservationCLM_oneDim shift p base
      (boundedRandomEntireFunction x) (differentiable_boundedRandomEntireFunction x) kk
  rw [hobs, hsplit, iteratedDeriv_add hcd1 hcd2, Pi.add_apply, iteratedDeriv_polynomialEval,
    hPc, eval_iterate_derivative_coeffPolynomial, packetHermiteMap_apply]
  rfl

end

end GaloisForLFunctions.HTGeometry
