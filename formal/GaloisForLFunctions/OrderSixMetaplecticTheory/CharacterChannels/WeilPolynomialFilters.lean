import GaloisForLFunctions.OrderSixMetaplecticTheory.CharacterChannels.WeilCubicProjection
import GaloisForLFunctions.HilbertMetric.QuantumWalk.IdempotentCalculus

/-!
# Polynomial filters of the ramified Weil channel

The actual cubic character projector has two polynomial sectors, evaluated
at one and zero. Its signed Weil-phase pairing sees only the first sector.
Thus every polynomial filter multiplies the actual row pairing by `p(1)`;
Chebyshev filters preserve it at every order.
-/

noncomputable section
open scoped BigOperators Classical
namespace GaloisForLFunctions.OrderSixMetaplecticTheory.RamifiedCharacterChannel
open Polynomial MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein
  MetaplecticMobiusDescent.CubicJacobi MetaplecticMobiusDescent.CubicEisenstein

/-- The existing cubic channel as an endomorphism of residue-class functions. -/
def cubicProjector : Module.End ℂ (ResidueFour → ℂ) where
  toFun := cubicProjection
  map_add' f g := by
    funext c
    simp only [cubicProjection, Pi.add_apply]
    ring
  map_smul' z f := by
    funext c
    simp only [cubicProjection, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem cubicProjector_idempotent : cubicProjector * cubicProjector = cubicProjector := by
  apply LinearMap.ext
  intro f
  exact cubicProjection_idempotent f

/-- Every polynomial filter splits into its retained and discarded cubic components. -/
theorem cubicProjector_polynomial (p : ℂ[X]) (f : ResidueFour → ℂ) :
    aeval cubicProjector p f =
      p.eval 1 • cubicProjection f + p.eval 0 • (f - cubicProjection f) := by
  have h := HilbertMetric.QuantumWalk.aeval_idempotent
    cubicProjector cubicProjector_idempotent p
  exact congrArg (fun A : Module.End ℂ (ResidueFour → ℂ) => A f) h

theorem weightedSum_add (f g : ResidueFour → ℂ) :
    weightedSum (f + g) = weightedSum f + weightedSum g := by
  simp only [weightedSum, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem weightedSum_sub (f g : ResidueFour → ℂ) :
    weightedSum (f - g) = weightedSum f - weightedSum g := by
  simp only [weightedSum, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem weightedSum_smul (a : ℂ) (f : ResidueFour → ℂ) :
    weightedSum (a • f) = a * weightedSum f := by
  simp only [weightedSum, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  ring

/-- The full signed Weil-phase pairing changes by exactly the scalar `p(1)`. -/
theorem weightedSum_polynomial (p : ℂ[X]) (f : ResidueFour → ℂ) :
    weightedSum (aeval cubicProjector p f) = p.eval 1 * weightedSum f := by
  rw [cubicProjector_polynomial, weightedSum_add, weightedSum_smul, weightedSum_smul,
    weightedSum_sub, weightedSum_eq_projected, sub_self, mul_zero, add_zero]

/-- A polynomial filter kills a pairing precisely by its value at one or an already zero pairing. -/
theorem weightedSum_polynomial_eq_zero_iff (p : ℂ[X]) (f : ResidueFour → ℂ) :
    weightedSum (aeval cubicProjector p f) = 0 ↔ p.eval 1 = 0 ∨ weightedSum f = 0 := by
  rw [weightedSum_polynomial, mul_eq_zero]

/-- Every Chebyshev order preserves the actual signed channel. -/
theorem weightedSum_chebyshev (n : ℕ) (f : ResidueFour → ℂ) :
    weightedSum (aeval cubicProjector (Chebyshev.T ℂ (n : ℤ)) f) = weightedSum f := by
  rw [weightedSum_polynomial, Chebyshev.T_eval_one, one_mul]

/-- On actual cubic Gauss class masses, the filtered pairing is the scalar times the row sum. -/
theorem finite_row_sum_polynomial (p : ℂ[X]) (S : Finset O) (w : O → ℂ) :
    weightedSum (aeval cubicProjector p (gaussSquareClassMass S w)) =
      p.eval 1 * ∑ c ∈ S,
        fixedDualAverage c * cubicTwoChar c * normalizedCubicUnitGauss c ^ 2 * w c := by
  rw [weightedSum_polynomial, finite_row_sum_eq_projected, weightedSum_eq_projected]

/-- Chebyshev filtering preserves every finite order-six row sum with arbitrary weights. -/
theorem finite_row_sum_chebyshev (n : ℕ) (S : Finset O) (w : O → ℂ) :
    weightedSum (aeval cubicProjector (Chebyshev.T ℂ (n : ℤ)) (gaussSquareClassMass S w)) =
      ∑ c ∈ S, fixedDualAverage c * cubicTwoChar c * normalizedCubicUnitGauss c ^ 2 * w c := by
  rw [finite_row_sum_polynomial, Chebyshev.T_eval_one, one_mul]

#print axioms cubicProjector_polynomial
#print axioms weightedSum_polynomial_eq_zero_iff
#print axioms finite_row_sum_chebyshev

end GaloisForLFunctions.OrderSixMetaplecticTheory.RamifiedCharacterChannel
