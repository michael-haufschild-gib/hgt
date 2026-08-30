import GaloisForLFunctions.HTGeometry.RandomEntireJetLawNondegeneracy
import GaloisForLFunctions.HTGeometry.RandomEntirePacketSplit
import GaloisForLFunctions.HTGeometry.RandomEntireTailSource

/-!
# The jet packet of a tail of the random entire series splits

The tail beyond index `L` is again a clamped series, shifted by the monomial `z^L`.  Its jet packets
split into the shifted Hermite evaluation of the next `N` clamped coordinates plus a further tail.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {H : Type*}

/-- The tail contribution to a jet packet observation, at an arbitrary shift index. -/
def packetTailObservationAt (shift : H → ℂ) (p : FiniteMultivariateAffineJetPattern H 1)
    (base : MultivariateAffinePatternRow p → Fin 1 → ℂ) (M : ℕ) (y : ℕ → ℂ) :
    Fin (affineJetPacketFiniteCoordinateCount p) → ℂ :=
  fun k => iteratedDeriv
    (packetOrder p ((Fintype.equivFin (MultivariateAffinePatternRow p ×
      MultivariateAffinePatternJet p)).symm k))
    (boundedRandomEntireTail M y)
    (packetPoint shift p base ((Fintype.equivFin (MultivariateAffinePatternRow p ×
      MultivariateAffinePatternJet p)).symm k))

theorem packetTailObservationAt_eq (shift : H → ℂ) (p : FiniteMultivariateAffineJetPattern H 1)
    (base : MultivariateAffinePatternRow p → Fin 1 → ℂ) (M : ℕ) (y : ℕ → ℂ) :
    packetTailObservationAt shift p base M y
      = finiteAffineJetPacketObservation (fun h => oneDimTranslationFrame (shift h)) p base
        (randomEntireTailSource M y) := by
  funext k
  exact (multivariateAffinePatternObservationCLM_oneDim shift p base _ _ _).symm

theorem measurable_packetTailObservationAt (shift : H → ℂ)
    (p : FiniteMultivariateAffineJetPattern H 1)
    (base : MultivariateAffinePatternRow p → Fin 1 → ℂ) (M : ℕ) :
    Measurable (packetTailObservationAt shift p base M) := by
  rw [funext (packetTailObservationAt_eq shift p base M)]
  exact ((continuous_finiteAffineJetPacketObservation _ p base).comp
    (continuous_randomEntireTailSource M)).measurable

/-- **The tail packet split.** -/
theorem finiteAffineJetPacketObservation_tail_split (shift : H → ℂ)
    (p : FiniteMultivariateAffineJetPattern H 1)
    (base : MultivariateAffinePatternRow p → Fin 1 → ℂ) (L : ℕ) (y : ℕ → ℂ) :
    finiteAffineJetPacketObservation (fun h => oneDimTranslationFrame (shift h)) p base
        (randomEntireTailSource L y)
      = packetShiftedHermiteMap shift p base
          (fun n => ((4 : ℂ) * ((Nat.factorial (n + L)) : ℂ))⁻¹) L
          (clampedComplexCoefficientHead (affineJetPacketFiniteCoordinateCount p) y)
        + packetTailObservationAt shift p base
          (affineJetPacketFiniteCoordinateCount p + L)
          (fun k => y (k + affineJetPacketFiniteCoordinateCount p)) := by
  classical
  set N : ℕ := affineJetPacketFiniteCoordinateCount p with hN
  funext k
  set kk := (Fintype.equivFin (MultivariateAffinePatternRow p ×
    MultivariateAffinePatternJet p)).symm k with hkk
  set j : ℕ := packetOrder p kk with hj
  set w : ℂ := packetPoint shift p base kk with hw
  set Pc : Polynomial ℂ :=
    ∑ n : Fin N, C (clampedComplexCoefficientHead N y n *
      ((4 : ℂ) * ((Nat.factorial ((n : ℕ) + L)) : ℂ))⁻¹) * X ^ ((n : ℕ) + L) with hPc
  have hpoly : ∀ z : ℂ, Pc.eval z = ∑ n ∈ Finset.range N, randomTailCoeff L y n * z ^ (n + L) := by
    intro z
    rw [hPc, Polynomial.eval_finsetSum,
      Finset.sum_range fun n => randomTailCoeff L y n * z ^ (n + L)]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      randomTailCoeff, clampedComplexCoefficientHead, div_eq_mul_inv]
  have hsplit : boundedRandomEntireTail L y
      = (fun z => Pc.eval z) + boundedRandomEntireTail (N + L) (fun k => y (k + N)) := by
    funext z
    rw [Pi.add_apply, hpoly z]
    exact boundedRandomEntireTail_split N L y z
  have hcd1 : ContDiffAt ℂ (j : WithTop ℕ∞) (fun z : ℂ => Pc.eval z) w :=
    ((Polynomial.differentiable Pc).contDiff.of_le (by exact_mod_cast le_top)).contDiffAt
  have hcd2 : ContDiffAt ℂ (j : WithTop ℕ∞)
      (boundedRandomEntireTail (N + L) (fun k => y (k + N))) w :=
    (((differentiable_boundedRandomEntireTail (N + L) (fun k => y (k + N))).contDiff).of_le
      (by exact_mod_cast le_top)).contDiffAt
  have hobs : finiteAffineJetPacketObservation (fun h => oneDimTranslationFrame (shift h)) p base
      (randomEntireTailSource L y) k = iteratedDeriv j (boundedRandomEntireTail L y) w :=
    multivariateAffinePatternObservationCLM_oneDim shift p base
      (boundedRandomEntireTail L y) (differentiable_boundedRandomEntireTail L y) kk
  rw [hobs, hsplit, iteratedDeriv_add hcd1 hcd2, Pi.add_apply, iteratedDeriv_polynomialEval,
    hPc, eval_iterate_derivative_weightedSum, packetShiftedHermiteMap_apply]
  rfl

end

end GaloisForLFunctions.HTGeometry
