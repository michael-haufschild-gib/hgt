import GaloisForLFunctions.BezoutValuationIncidence.VaughanPacketsHaveAnExactResidualEnergyDensity
import GaloisForLFunctions.BezoutValuationIncidence.UniformTruncatedMobiusReceiversHaveZeroTrivialDensity

/-!
Finite centering and quadratic-form identities for real superpositions of
Vaughan rows. The smooth direction reads the difference of convolution weights.
-/

open Finset Filter RHTower
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

/-- Centering commutes with every finite real superposition of Vaughan rows. -/
theorem pmPronicVaughanCentredPacket_eq_sum (ε : ℝ) (U V : ℕ) (w : Fin 5 → ℝ) (n : ℕ) :
    pmPronicVaughanCentredPacket ε U V w n =
      ∑ i : Fin 5, w i * pmPronicVaughanCentredPiece ε U V n i := by
  simp only [pmPronicVaughanCentredPacket, pmPronicVaughanPacket,
    pmPronicVaughanCentredPiece, pmPronicVaughanPacketLinearMean,
    mul_sub, sum_sub_distrib, sum_mul, mul_assoc]

/-- The smooth sign vector reads only the difference of the two convolution coefficients. -/
theorem sum_mul_pmPronicVaughanSmoothSigns (w : Fin 5 → ℝ) :
    (∑ i : Fin 5, w i * pmPronicVaughanSmoothSigns i) = w 3 - w 2 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change w 0 * 0 + (w 1 * 0 + (w 2 * (-1) + (w 3 * 1 + w 4 * 0))) = _
  ring

/-- The packet energy is the quadratic form of the actual centered Gram. -/
theorem sq_pronicNorm_pmPronicVaughanCentredPacket_eq_gram
    (ε : ℝ) (U V T : ℕ) (w : Fin 5 → ℝ) :
    pronicNorm (pmPronicVaughanCentredPacket ε U V w) T ^ 2 =
      ∑ i : Fin 5, ∑ j : Fin 5, w i * w j * pmPronicVaughanCentredGram ε U V T i j := by
  rw [pronicNorm, Real.sq_sqrt (sum_nonneg fun n _ => by positivity)]
  simp_rw [pmPronicVaughanCentredPacket_eq_sum]
  have hcell (n : ℕ) :
      (∑ i : Fin 5, w i * pmPronicVaughanCentredPiece ε U V n i) ^ 2 /
          ((n : ℝ) * ((n : ℝ) + 1)) =
        ∑ i : Fin 5, ∑ j : Fin 5, w i * w j *
          (pmPronicVaughanCentredPiece ε U V n i * pmPronicVaughanCentredPiece ε U V n j /
            ((n : ℝ) * ((n : ℝ) + 1))) := by
    rw [pow_two, sum_mul]
    simp_rw [mul_sum, sum_div]
    apply sum_congr rfl
    intro i _
    exact sum_congr rfl fun j _ => by ring
  simp_rw [hcell]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  rw [pmPronicVaughanCentredGram, mul_sum]
  apply sum_congr rfl
  intro n _
  simp only [pronicSeq, Nat.cast_mul, Nat.cast_add, Nat.cast_one]

/-- Each diagonal entry is exactly the squared pronic norm of its centered row. -/
theorem sq_pronicNorm_pmPronicVaughanCentredPiece (ε : ℝ) (U V T : ℕ) (i : Fin 5) :
    pronicNorm (fun n => pmPronicVaughanCentredPiece ε U V n i) T ^ 2 =
      pmPronicVaughanCentredGram ε U V T i i := by
  rw [pronicNorm, Real.sq_sqrt (sum_nonneg fun n _ => by positivity)]
  simp only [pmPronicVaughanCentredGram, pow_two, pronicSeq,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]

#print axioms pmPronicVaughanCentredPacket_eq_sum
#print axioms sum_mul_pmPronicVaughanSmoothSigns
#print axioms sq_pronicNorm_pmPronicVaughanCentredPacket_eq_gram
#print axioms sq_pronicNorm_pmPronicVaughanCentredPiece
end GaloisForLFunctions.BezoutValuationIncidence
