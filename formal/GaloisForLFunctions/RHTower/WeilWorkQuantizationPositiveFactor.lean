import GaloisForLFunctions.RHTower.WeilWorkQuantizationPairing
import GaloisForLFunctions.RHTower.WeilWorkQuantizationCircleCoefficient

/-!
# Actual canonical phases exclude a positive analytic factor

The arithmetic q-chain and the circle-coefficient annihilator contradict one
another whenever an exterior inverse leaves a strictly positive analytic
factor. Every coefficient sum and its exchange is paid by source energy and
analytic coefficient bounds. The remaining L1 obligation is to construct this
factorization from positive winding of the represented periodic phase.
-/

open Complex Set Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace RHTower.WeilSpectral
open GaloisForLFunctions.HTGeometry

/-- A represented canonical phase cannot admit the strictly positive factorization. -/
theorem quantization_phase_no_positive_exterior_factor
    {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {q : ℕ} (hq : 2 ≤ q) {p : ℤ → ℂ}
    (hp : Summable fun k => ‖p k‖ * (q : ℝ) ^ k.natAbs)
    (hphase : ∀ x : ℝ, 0 < x →
      cexp (((2 * Real.pi * quantizationResidualCumulative hW x : ℝ) : ℂ) * I) =
        ∑' k : ℤ, p k * cexp (((2 * (k : ℝ) * Real.log q * x : ℝ) : ℂ) * I))
    {f : ℂ → ℂ} {r M R : ℝ} (hr : 0 < r) (hM : 0 ≤ M)
    (hf : ∀ z ∈ sphere (0 : ℂ) r, ‖f z‖ ≤ M)
    (hR1 : 1 < R) (hR : R < r⁻¹) :
    ¬ ∃ H : ℂ → ℂ, DiffContOnCl ℂ H (ball 0 1) ∧
      ∀ z ∈ sphere (0 : ℂ) 1,
        quantizationExteriorInverse f r z⁻¹ * (∑' k : ℤ, p k * z ^ k) = z * H z := by
  obtain ⟨A, _, hcoef, hsum⟩ := quantizationExteriorInverse_coefficients
    hr hM hf (by linarith) hR
  have hp1 := quantization_firstMoment_of_qWeight hq hp
  have hp0 : Summable fun k => ‖p k‖ := by
    apply hp1.of_nonneg_of_le (fun k => norm_nonneg _)
    intro k
    nlinarith [mul_nonneg (norm_nonneg (p k)) (abs_nonneg (k : ℝ))]
  have hg1 := quantization_firstMoment_of_geometric hR1 hcoef
  have hg0 : Summable fun l => ‖outerCoeff (quantizationExteriorInverse f r) R l‖ := by
    apply hg1.of_nonneg_of_le (fun l => norm_nonneg _)
    intro l
    nlinarith [mul_nonneg (norm_nonneg (outerCoeff (quantizationExteriorInverse f r) R l))
      (Nat.cast_nonneg (α := ℝ) l)]
  have hG (z : ℂ) (hz : z ∈ sphere (0 : ℂ) 1) :
      HasSum (fun l : ℕ => outerCoeff (quantizationExteriorInverse f r) R l * z ^ (-(l : ℤ)))
        (quantizationExteriorInverse f r z⁻¹) := by
    have hn : ‖z‖ = 1 := by simpa only [mem_sphere_iff_norm, sub_zero] using hz
    have hw : ‖z⁻¹‖ < R := by simpa only [norm_inv, hn, inv_one] using hR1
    simpa only [zpow_neg, zpow_natCast, inv_pow] using hsum z⁻¹ hw
  rintro ⟨H, hH, hfactor⟩
  have hann := quantization_annihilator_of_positive_factor hp0 hg0
    (P := fun z => ∑' k : ℤ, p k * z ^ k) (fun _ _ => rfl) hG hH hfactor
  exact quantization_phase_exteriorInverse_not_annihilator hW hq hp hphase
    hr hM hf hR1 hR hann

end RHTower.WeilSpectral
