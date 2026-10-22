import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerArithmeticPacketDivision

/-!
# Actual invertible operators through every finite Xi resonance

Replace a generator word by the identity on its complete resonant Xi packet,
and retain the word on the complementary actual source. The resulting operator
is bijective on the whole arithmetic source, with the explicit inverse given
by canonical packet-complement division plus the finite projector.
-/

namespace RHTower
noncomputable section

local notation "V" => DeningerMeyerArithmeticSource
local notation "A" => deningerMeyerArithmeticSourceGenerator

theorem deningerMeyerArithmeticWordDivision_projector_left (L : List ℂ) (u : V) :
    deningerMeyerArithmeticFiniteProjector (deningerMeyerWordXiSupport L)
      (deningerMeyerArithmeticWordDivision L u) = 0 :=
  deningerMeyerArithmeticFiniteProjector_zero_of_packet_zero _ _
    (deningerMeyerArithmeticWordDivision_packet_zero L u)

theorem deningerMeyerArithmeticWordDivision_projector_right (L : List ℂ) (u : V) :
    deningerMeyerArithmeticWordDivision L
      (deningerMeyerArithmeticFiniteProjector (deningerMeyerWordXiSupport L) u) = 0 := by
  apply deningerMeyerArithmeticWord_zero_of_packet_zero L
  · exact deningerMeyerArithmeticWordDivision_packet_zero L _
  · rw [deningerMeyerArithmeticWordDivision_right,
      deningerMeyerArithmeticFiniteProjector_idempotent, sub_self]

def deningerMeyerArithmeticRegularizedWord (L : List ℂ) : Module.End ℂ V :=
  (deningerMeyerGeneratorWord A L).comp
    (LinearMap.id - deningerMeyerArithmeticFiniteProjector (deningerMeyerWordXiSupport L)) +
      deningerMeyerArithmeticFiniteProjector (deningerMeyerWordXiSupport L)

def deningerMeyerArithmeticRegularizedWordInverse (L : List ℂ) : Module.End ℂ V :=
  deningerMeyerArithmeticWordDivision L +
    deningerMeyerArithmeticFiniteProjector (deningerMeyerWordXiSupport L)

theorem deningerMeyerArithmeticRegularizedWord_inverse_right (L : List ℂ) (u : V) :
    deningerMeyerArithmeticRegularizedWord L
      (deningerMeyerArithmeticRegularizedWordInverse L u) = u := by
  let P := deningerMeyerArithmeticFiniteProjector (deningerMeyerWordXiSupport L)
  let D := deningerMeyerArithmeticWordDivision L
  have hP : P (D u + P u) = P u := by
    rw [map_add, deningerMeyerArithmeticWordDivision_projector_left,
      deningerMeyerArithmeticFiniteProjector_idempotent, zero_add]
  have hr : D u + P u - P (D u + P u) = D u := by rw [hP]; module
  change deningerMeyerGeneratorWord A L (D u + P u - P (D u + P u)) + P (D u + P u) = u
  rw [hr, hP, deningerMeyerArithmeticWordDivision_right]
  module

theorem deningerMeyerArithmeticRegularizedWord_inverse_left (L : List ℂ) (u : V) :
    deningerMeyerArithmeticRegularizedWordInverse L
      (deningerMeyerArithmeticRegularizedWord L u) = u := by
  let P := deningerMeyerArithmeticFiniteProjector (deningerMeyerWordXiSupport L)
  let D := deningerMeyerArithmeticWordDivision L
  have hr : P (u - P u) = 0 := by
    rw [map_sub, deningerMeyerArithmeticFiniteProjector_idempotent, sub_self]
  change D (deningerMeyerGeneratorWord A L (u - P u) + P u) +
    P (deningerMeyerGeneratorWord A L (u - P u) + P u) = u
  rw [map_add, map_add, deningerMeyerArithmeticWordDivision_left,
    deningerMeyerArithmeticWordDivision_projector_right,
    deningerMeyerArithmeticFiniteProjector_word,
    deningerMeyerArithmeticFiniteProjector_idempotent, hr, map_zero]
  module

/-- A concrete automorphism of actual arithmetic Meyer cohomology for every
finite word, including arbitrary repeated Xi roots. -/
def deningerMeyerArithmeticRegularizedWordEquiv (L : List ℂ) : V ≃ₗ[ℂ] V :=
  LinearEquiv.ofLinear (deningerMeyerArithmeticRegularizedWord L)
    (deningerMeyerArithmeticRegularizedWordInverse L)
    (LinearMap.ext (deningerMeyerArithmeticRegularizedWord_inverse_right L))
    (LinearMap.ext (deningerMeyerArithmeticRegularizedWord_inverse_left L))

theorem deningerMeyerArithmeticRegularizedWord_bijective (L : List ℂ) :
    Function.Bijective (deningerMeyerArithmeticRegularizedWord L) :=
  (deningerMeyerArithmeticRegularizedWordEquiv L).bijective

end
end RHTower
