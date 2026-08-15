import GaloisForLFunctions.HTGeometry.MovingCanonicalJetControllability
import GaloisForLFunctions.HTGeometry.MovingDivisorData

/-!
# Finite jet controllability of a moving divisor

Varying finitely many parameters of a moving divisor spans every finite complex jet packet at a
finite family of distinct upper half-plane nodes.  The location-variation columns already span, by
the inverse-square Cauchy rigidity of an injective nonvanishing divisor; multiplying each column by
the positive coordinate speed does not change the span.
-/

open Filter
open scoped Topology

namespace GaloisForLFunctions.HTGeometry

namespace MovingDivisor

noncomputable section

variable (D : MovingDivisor) (θ : ℕ → ℝ)

/-- The exact coordinate speed of the moving divisor at the given parameter. -/
def speed (a : ℕ) : ℝ := D.coordinateSpeed a (θ a)

theorem speed_pos (a : ℕ) : 0 < D.speed θ a := D.coordinate_speed_pos a (θ a)

theorem hasDerivAt_zero_coordinate (a : ℕ) :
    HasDerivAt (fun t : ℝ => D.base a + D.radius a * Real.tanh t) (D.speed θ a) (θ a) :=
  D.coordinate_hasDerivAt a (θ a)

/-- Location-variation jet map on the moving divisor. -/
def locationJet {ι : Type*} (x : ι → ℂ) (n : ι → ℕ) :
    (ℕ →₀ ℝ) →ₗ[ℝ] ((Σ i, Fin (n i)) → ℂ) :=
  movingPoleLocationJetRealLinearCombination x n (D.zero θ)

/-- **The location variations of a moving divisor span every finite complex jet packet.** -/
theorem locationJet_surjective {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℂ) (hx : Function.Injective x) (hupper : ∀ i, 0 < (x i).im) (n : ι → ℕ) :
    Function.Surjective (D.locationJet θ x n) :=
  movingPoleLocationJetRealLinearCombination_surjective x hx hupper n (D.zero θ)
    (D.injective θ) (fun a => ne_of_gt (D.zero_pos θ a))

/-- First-order jet map for variations of the bounded parameter. -/
def parameterJet {ι : Type*} (x : ι → ℂ) (n : ι → ℕ) :
    (ℕ →₀ ℝ) →ₗ[ℝ] ((Σ i, Fin (n i)) → ℂ) :=
  (D.locationJet θ x n).comp (positiveSpeedFinsuppLinearMap (D.speed θ))

theorem parameterJet_single {ι : Type*} (x : ι → ℂ) (n : ι → ℕ) (a : ℕ) :
    D.parameterJet θ x n (Finsupp.single a 1) =
      D.speed θ a • D.locationJet θ x n (Finsupp.single a 1) := by
  rw [parameterJet, LinearMap.comp_apply, positiveSpeedFinsuppLinearMap_single]
  have hsingle : Finsupp.single a (D.speed θ a * 1) =
      D.speed θ a • Finsupp.single a (1 : ℝ) := by
    ext b
    simp [mul_comm]
  rw [hsingle, map_smul]

/-- **The actual parameter derivative of a moving divisor spans every finite complex jet
packet.** -/
theorem parameterJet_surjective {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℂ) (hx : Function.Injective x) (hupper : ∀ i, 0 < (x i).im) (n : ι → ℕ) :
    Function.Surjective (D.parameterJet θ x n) :=
  (D.locationJet_surjective θ x hx hupper n).comp
    (positiveSpeedFinsuppLinearMap_surjective (fun a => ne_of_gt (D.speed_pos θ a)))

end

end MovingDivisor

end GaloisForLFunctions.HTGeometry
