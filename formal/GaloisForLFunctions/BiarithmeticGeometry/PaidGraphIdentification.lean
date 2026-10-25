import GaloisForLFunctions.BiarithmeticGeometry.CofactorGraphDomain
import GaloisForLFunctions.BiarithmeticGeometry.PronicEnergyDomain
import GaloisForLFunctions.ArithmeticOrientationTheory.UnpayabilityIsLocatedOnTheBohrPolydisk

/-!
# The complete cofactor graph realizes the actual paid ideal

The actual centered source prefix supplies the graph's arithmetic row. Its
normalized complex coordinates have finite square energy exactly when both
real cofactor packets have bounded receiver norm, hence exactly on payment.
-/

noncomputable section
open Finset
open GaloisForLFunctions.ArithmeticOrientationTheory
open GaloisForLFunctions.TransHorizonIncidenceMechanics
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- Complexification of the source prefix centered by its actual mean. -/
def actualSourceCofactorRow (c : ℕ → ℝ) (n : ℕ) : ℂ :=
  weightCenteredPrefix c (∑' d : ℕ, c d / d) n

private theorem norm_cofactorPronicCoordinate_sq (v : ℕ → ℂ)
    (k : WienerAlgebraAt (1 / 2)) (n : ℕ) :
    ‖cofactorPronicCoordinate v n k‖ ^ 2 =
      ‖∑ j ∈ Icc 1 (n + 1), k.toFn j * v ((n + 1) / j)‖ ^ 2 /
        (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
  rw [cofactorPronicCoordinate_apply, norm_div, div_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by positivity)]

private theorem actualSourceCofactorRow_packet_re (c : ℕ → ℝ)
    (k : WienerAlgebraAt (1 / 2)) (n : ℕ) :
    (∑ j ∈ Icc 1 n, k.toFn j * actualSourceCofactorRow c (n / j)).re =
      cofactorPrefixAction c (rePart k) n := by
  simp only [Complex.re_sum, actualSourceCofactorRow, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, cofactorPrefixAction, rePart]

private theorem actualSourceCofactorRow_packet_im (c : ℕ → ℝ)
    (k : WienerAlgebraAt (1 / 2)) (n : ℕ) :
    (∑ j ∈ Icc 1 n, k.toFn j * actualSourceCofactorRow c (n / j)).im =
      cofactorPrefixAction c (imPart k) n := by
  simp only [Complex.im_sum, actualSourceCofactorRow, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, cofactorPrefixAction, imPart]

/-- The image of the complete actual-source graph is precisely its arithmetic paid ideal. -/
theorem mem_range_actualSourceCofactorGraphInput_iff (c : ℕ → ℝ)
    (hc : Summable fun d : ℕ => |c d / d|) (k : WienerAlgebraAt (1 / 2)) :
    k ∈ Set.range (cofactorGraphInput (actualSourceCofactorRow c)) ↔ k ∈ paidIdeal c hc := by
  rw [mem_range_cofactorGraphInput_iff]
  simp only [norm_cofactorPronicCoordinate_sq]
  rw [summable_complex_pronicEnergy_iff
    (fun n => ∑ j ∈ Icc 1 n, k.toFn j * actualSourceCofactorRow c (n / j))]
  simp only [actualSourceCofactorRow_packet_re, actualSourceCofactorRow_packet_im]
  rw [← bounded_pronicNorm_iff_summable, ← bounded_pronicNorm_iff_summable,
    ← receiverBounded_dirichletConv_iff_cofactorNorm _ _ hc (criticalWiener_rePart k),
    ← receiverBounded_dirichletConv_iff_cofactorNorm _ _ hc (criticalWiener_imPart k)]
  exact (mem_paidIdeal c hc (k := k)).symm

/-- Every paid kernel has a unique square-summable actual cofactor output. -/
theorem paidIdeal_iff_existsUnique_cofactorGraph (c : ℕ → ℝ)
    (hc : Summable fun d : ℕ => |c d / d|) (k : WienerAlgebraAt (1 / 2)) :
    k ∈ paidIdeal c hc ↔
      ∃! p : cofactorGraphDomain (actualSourceCofactorRow c),
        cofactorGraphInput (actualSourceCofactorRow c) p = k := by
  rw [← mem_range_actualSourceCofactorGraphInput_iff c hc k]
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p, hp, fun q hq => ?_⟩
    exact cofactorGraphInput_injective _ (hq.trans hp.symm)
  · rintro ⟨p, hp, _⟩
    exact ⟨p, hp⟩

end GaloisForLFunctions.BiarithmeticGeometry
