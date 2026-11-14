import GaloisForLFunctions.SignedArithmeticEnergyIncidence.TwoProfileInteraction
import GaloisForLFunctions.SignedArithmeticEnergyIncidence.SignChangesNeedAntiAlignedOverlaps

/-!
# Two-profile witnesses for pole-subtracted incidence energies

Subtracting the square of a pole functional subtracts its rank-one matrix from
the incidence coupling. The exact two-sign threshold therefore uses the mixed
charge `B(f,g) - ℓ(f)ℓ(g)`, with both diagonal pole charges retained.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

variable {ι : Type*} [Fintype ι]

/-- The matrix of the incidence energy after subtracting one pole square. -/
def poleAdjustedCoupling (c : ι → ι → ℝ) (p : ι → ℝ) : ι → ι → ℝ :=
  fun i j => c i j - p i * p j

private theorem rankOne_pairing (p f g : ι → ℝ) :
    (∑ i, ∑ j, p i * p j * f i * g j) = (∑ i, p i * f i) * ∑ j, p j * g j := by
  rw [sum_mul]
  apply sum_congr rfl
  intro i _
  rw [mul_sum]
  exact sum_congr rfl fun j _ => by ring

/-- The concrete polar form is exactly an incidence energy with a rank-one subtraction. -/
theorem incidenceEnergy_poleAdjusted (c : ι → ι → ℝ) (p f : ι → ℝ) :
    incidenceEnergy (poleAdjustedCoupling c p) f = polarForm c p f := by
  unfold incidenceEnergy poleAdjustedCoupling polarForm
  simp only [sub_mul, sum_sub_distrib]
  rw [rankOne_pairing]
  simp only [incidenceEnergy, sq]

/-- The mixed pole charge must be subtracted along with the two diagonal pole squares. -/
theorem incidenceCross_poleAdjusted (c : ι → ι → ℝ) (p f g : ι → ℝ) :
    incidenceCross (poleAdjustedCoupling c p) f g =
      incidenceCross c f g - (∑ i, p i * f i) * ∑ j, p j * g j := by
  unfold incidenceCross poleAdjustedCoupling
  have hp (i j : ι) : p i * p j * (f i * g j + g i * f j) =
      p i * p j * f i * g j + p i * p j * g i * f j := by ring
  simp only [sub_mul, hp, sum_sub_distrib, sum_add_distrib, rankOne_pairing]
  ring

/-- The best relative sign gives the exact pole-subtracted deficit. -/
theorem polarForm_exists_sign_min (c : ι → ι → ℝ) (p f g : ι → ℝ) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      polarForm c p (fun i => f i - ε * g i) =
        polarForm c p f + polarForm c p g -
          2 * |incidenceCross c f g - (∑ i, p i * f i) * ∑ j, p j * g j| := by
  simpa only [incidenceEnergy_poleAdjusted, incidenceCross_poleAdjusted] using
    incidenceEnergy_exists_sign_min (poleAdjustedCoupling c p) f g

/-- The exact two-profile threshold applies to the full polar form, including its pole. -/
theorem polarForm_two_sign_negative_iff (c : ι → ι → ℝ) (p f g : ι → ℝ) :
    (∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ polarForm c p (fun i => f i - ε * g i) < 0) ↔
      polarForm c p f + polarForm c p g <
        2 * |incidenceCross c f g - (∑ i, p i * f i) * ∑ j, p j * g j| := by
  simpa only [incidenceEnergy_poleAdjusted, incidenceCross_poleAdjusted] using
    incidenceEnergy_two_sign_negative_iff (poleAdjustedCoupling c p) f g

end GaloisForLFunctions.SignedArithmeticEnergyIncidence

#print axioms GaloisForLFunctions.SignedArithmeticEnergyIncidence.polarForm_two_sign_negative_iff
#print axioms GaloisForLFunctions.SignedArithmeticEnergyIncidence.polarForm_exists_sign_min
