import GaloisForLFunctions.HTGeometry.FixedDivisorTranslationFreeness
import GaloisForLFunctions.HTGeometry.SymmetricGaugeSpace
import GaloisForLFunctions.HTGeometry.SymmetricRowPacketAtlas

/-!
# Full complex translation freeness inside the symmetry cage

A gauged source `W·exp(g)` with `g` obeying the functional equation, Schwarz reality, and a
prescribed finite jet passport keeps the divisor of `W`, both symmetries, and the passport.  This
module runs the compact-patch codimension argument inside that constraint space: the symmetric
passport probe is still onto the jets at a node with a free symmetry orbit, so densely many
constrained gauges have full expanded-evaluation rank at every shift of a compact patch.

Baire over a compact exhaustion of the shift configuration space, and then over the countable set of
finite differential patterns, gives one dense residual set of constrained gauges whose entire
uncountable complex translation orbit is differentially algebraically independent.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Topology
open ClassicalAnalyticNevanlinnaCarrierFamily

noncomputable section

variable {row κ ι : Type} [Fintype row] [DecidableEq row] [Fintype κ] [DecidableEq κ]
  [Fintype ι] [DecidableEq ι]

/-- A row packet is admissible in the symmetry cage when its whole node family has a free symmetry
orbit off the origin, the divisor, and the passport set. -/
def symGoodPacket (W : ℂ → ℂ) (A : Finset ℂ) (packet : InjectiveProjectiveRowPacket row)
    (shift : InjectiveShiftConfiguration ι) : Prop :=
  shift.1 ∈ symGoodCombinedRowPacketAmbientSet W A packet

/-- One admissible packet witnesses full coefficient rank in the symmetry cage. -/
def symGaugeExpandedFullRankWitness (W : ℂ → ℂ) (A : Finset ℂ) (degree : ℕ) (orders : ι → ℕ)
    (exponent : κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (g : EntireGauge) (shift : InjectiveShiftConfiguration ι) : Prop :=
  ∃ packet : InjectiveProjectiveRowPacket row,
    symGoodPacket W A packet shift ∧
      Function.Injective
        (expandedDifferentialEvaluationMatrix degree
          (Fintype.card (Σ i, Fin (orders i))) packet.1 exponent
          (gaugeExpandedPacketValue W orders packet g shift)).mulVec

/-- A finite polynomial-coefficient relation on the jets of a caged gauged source. -/
def symGaugeExpandedPatternRelationHolds (W : ℂ → ℂ) (A : Finset ℂ) (degree : ℕ)
    (orders : ι → ℕ) (exponent : κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (g : EntireGauge) (shift : InjectiveShiftConfiguration ι)
    (coeff : κ × Fin (degree + 1) → ℂ) : Prop :=
  ∀ packet : InjectiveProjectiveRowPacket row, symGoodPacket W A packet shift →
    ∀ r, ∑ col, coeff col *
      expandedDifferentialEvaluationMatrix degree
        (Fintype.card (Σ i, Fin (orders i))) packet.1 exponent
        (gaugeExpandedPacketValue W orders packet g shift) r col = 0

omit [DecidableEq row] [DecidableEq κ] [DecidableEq ι] in
theorem symGaugeExpandedPatternRelation_coefficients_eq_zero_of_fullRankWitness
    (W : ℂ → ℂ) (A : Finset ℂ) (degree : ℕ) (orders : ι → ℕ)
    (exponent : κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (g : EntireGauge) (shift : InjectiveShiftConfiguration ι)
    (hwitness : symGaugeExpandedFullRankWitness (row := row) (κ := κ) W A degree orders
      exponent g shift)
    (coeff : κ × Fin (degree + 1) → ℂ)
    (hrelation : symGaugeExpandedPatternRelationHolds (row := row) W A degree orders exponent g
      shift coeff) :
    ∀ col, coeff col = 0 := by
  obtain ⟨packet, hgood, hinjective⟩ := hwitness
  have hmul : (expandedDifferentialEvaluationMatrix degree
      (Fintype.card (Σ i, Fin (orders i))) packet.1 exponent
      (gaugeExpandedPacketValue W orders packet g shift)).mulVec coeff = 0 := by
    funext r
    simpa [Matrix.mulVec, dotProduct, mul_comm] using hrelation packet hgood r
  have hcoeff : coeff = 0 := hinjective (by simpa using hmul)
  intro col
  exact congrFun hcoeff col

end

end GaloisForLFunctions.HTGeometry
