import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.SplineFiniteCorrection
import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.SplinePolynomialCost

/-!
# Polynomial bounds for exact finite spline interpolation

The explicit parameters retained by finite interpolation satisfy polynomial
bounds in a common envelope for their scalar data. One universal constant
controls the number of nodes, interval span, height threshold, and inverse
residual radius. The constructed nodes retain exact spline coefficients and
unit multiplicity throughout.
-/

open Finset Complex
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

/-- One numerical constant controls all four finite correction costs. -/
def splineCorrectionCostScale : ℝ := 16*(1+Real.pi+1/Real.pi)

def splineCorrectionCostConstant : ℝ :=
  1+96*splineCorrectionCostScale^2+610*splineCorrectionCostScale^3+400000*splineCorrectionCostScale^5

lemma splineCorrectionCostScale_bounds :
    1 ≤ splineCorrectionCostScale ∧ Real.pi ≤ splineCorrectionCostScale ∧
      2/Real.pi ≤ splineCorrectionCostScale ∧ 10+4*Real.pi ≤ splineCorrectionCostScale := by
  have hp := Real.pi_pos
  have hi : 0 < 1/Real.pi := by positivity
  unfold splineCorrectionCostScale
  simp only [div_eq_mul_inv,one_mul] at hi ⊢
  constructor
  · nlinarith only [hp,hi]
  constructor
  · nlinarith only [hp,hi]
  constructor
  · nlinarith only [hp,hi]
  · nlinarith only [hp,hi]

lemma splineCorrectionCostConstant_pos : 0 < splineCorrectionCostConstant := by
  have hK : 0 ≤ splineCorrectionCostScale := le_trans zero_le_one splineCorrectionCostScale_bounds.1
  unfold splineCorrectionCostConstant
  positivity

variable {ι : Type*} [Fintype ι]

/-- Every actual finite correction parameter has polynomial cost in a common
envelope for its explicit scalar data. -/
theorem exists_prescribed_spline_correction_polynomial_bound {δ η X : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hX : 1 ≤ X) {t : ι → ℝ}
    (ht : ∀ i, 0 < t i) (hinj : Function.Injective t)
    (hgap : ∀ i j, η ≤ |t i+splineShift j|)
    (hδX : δ ≤ X) (hηX : 1/η ≤ X) (hLX : ∑ i, |t i| ≤ X)
    (hAX : ∑ i, ∑ j, splineJacobianEntryBound δ (t i) (t j) ≤ X)
    (hJX : ∑ i, ∑ j, splinePairLipschitzBound δ (t i) (t j) ≤ X)
    (hPX : splineHeightCorrectionBound δ t ≤ X)
    (hQX : ∑ i, splineSecondBound δ (t i) ≤ X)
    (hGX : ∑ i, splineSlopeBound δ (t i) ≤ X) (hBX : splineNumeratorBound δ ≤ X) :
    ∃ n : ℕ, ∃ C H₀ ε : ℝ, 0 < n ∧ 0 < C ∧ 0 < H₀ ∧ 0 < ε ∧
      (n : ℝ) ≤ splineCorrectionCostConstant*X^6 ∧
      C ≤ splineCorrectionCostConstant*X^5 ∧
      H₀ ≤ splineCorrectionCostConstant*X^9 ∧ 1/ε ≤ splineCorrectionCostConstant*X^3 ∧
      ∀ H : ℝ, H₀ ≤ H → ∀ r : ι → ℂ, (∀ i, ‖r i‖ ≤ ε*n/H^8) →
      ∃ γ : Fin n → ℝ, Function.Injective γ ∧
        (∀ j, γ j ∈ Set.Icc H (H+C)) ∧
        ∀ i, (∑ j, (Complex.sinh ((δ : ℂ)+(γ j : ℂ)*Complex.I)/
          ((δ : ℂ)+(γ j : ℂ)*Complex.I))^8*phase (t i) (γ j))=r i := by
  classical
  let K := splineCorrectionCostScale
  have hKb := splineCorrectionCostScale_bounds
  have hK : 1 ≤ K := hKb.1
  have hK0 : 0 ≤ K := le_trans zero_le_one hK
  have hX0 : 0 ≤ X := le_trans zero_le_one hX
  have hL0 : 0 ≤ ∑ i, |t i| := sum_nonneg fun _ _ => abs_nonneg _
  have hJ0 : 0 ≤ ∑ i, ∑ j, splinePairLipschitzBound δ (t i) (t j) :=
    sum_nonneg fun i _ => sum_nonneg fun j _ => splinePairLipschitzBound_nonneg hδ (ht j) (t i)
  have hP0 := splineHeightCorrectionBound_nonneg hδ ht
  have hQ0 : 0 ≤ ∑ i, splineSecondBound δ (t i) :=
    sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _
  have hG0 : 0 ≤ ∑ i, splineSlopeBound δ (t i) :=
    sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _
  have hB0 := splineNumeratorBound_nonneg δ
  obtain ⟨Λ,ρ,H₀,n,hΛ,hρ,hH₀,hn,hΛeq,hρeq,hH₀eq,hnUpper,hrealize⟩ :=
    exists_prescribed_spline_finite_correction_data hδ hη ht hinj hgap
  have hΛone : 1 ≤ Λ := by
    rw [hΛeq]
    have hj := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) Real.pi_pos.le) hJ0
    linarith only [hL0,hj]
  have hΛK : Λ ≤ K*X := by
    rw [hΛeq]
    have hj := mul_le_mul_of_nonneg_left hJX
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) Real.pi_pos.le)
    have hk := mul_le_mul_of_nonneg_right hKb.2.2.2 hX0
    change (10+4*Real.pi)*X ≤ K*X at hk
    nlinarith only [hLX,hX,hj,hk]
  have hρX : 1/ρ ≤ 24*K^2*X^3 := by
    rw [hρeq]
    exact inverse_spline_parameter_radius_le hX hK hΛ hΛK hKb.2.2.1 hP0 hPX hQ0 hQX
  obtain ⟨hnX,hCX⟩ := spline_node_count_and_span_le hX hK hΛone hΛK hKb.2.1 hKb.2.2.1
    hAX hB0 hBX hη hηX hρ hρX hnUpper
  have hHX : H₀ ≤ 400000*K^5*X^9 := by
    rw [hH₀eq]
    exact spline_height_threshold_le hX hK hCX hδX hG0 hGX hB0 hBX hP0 hPX hρ hρX
  have hεX : 1/(ρ/4) ≤ 96*K^2*X^3 := by
    have he : 1/(ρ/4)=4*(1/ρ) := by ring
    rw [he]
    exact (mul_le_mul_of_nonneg_left hρX (by norm_num)).trans_eq (by ring)
  have hcn : 400*K^3 ≤ splineCorrectionCostConstant := by
    unfold splineCorrectionCostConstant
    change 400*K^3 ≤ 1+96*K^2+610*K^3+400000*K^5
    nlinarith only [sq_nonneg K,pow_nonneg hK0 3,pow_nonneg hK0 5]
  have hcc : 210*K^3 ≤ splineCorrectionCostConstant := by
    unfold splineCorrectionCostConstant
    change 210*K^3 ≤ 1+96*K^2+610*K^3+400000*K^5
    nlinarith only [sq_nonneg K,pow_nonneg hK0 3,pow_nonneg hK0 5]
  have hch : 400000*K^5 ≤ splineCorrectionCostConstant := by
    unfold splineCorrectionCostConstant
    change 400000*K^5 ≤ 1+96*K^2+610*K^3+400000*K^5
    nlinarith only [sq_nonneg K,pow_nonneg hK0 3]
  have hce : 96*K^2 ≤ splineCorrectionCostConstant := by
    unfold splineCorrectionCostConstant
    change 96*K^2 ≤ 1+96*K^2+610*K^3+400000*K^5
    nlinarith only [pow_nonneg hK0 3,pow_nonneg hK0 5]
  refine ⟨n,((n : ℝ)+1)*(Real.pi/(2*Λ)),H₀,ρ/4,hn,by positivity,hH₀,by positivity,?_,?_,?_,?_,hrealize⟩
  · exact hnX.trans (mul_le_mul_of_nonneg_right hcn (pow_nonneg hX0 6))
  · exact hCX.trans (mul_le_mul_of_nonneg_right hcc (pow_nonneg hX0 5))
  · exact hHX.trans (mul_le_mul_of_nonneg_right hch (pow_nonneg hX0 9))
  · exact hεX.trans (mul_le_mul_of_nonneg_right hce (pow_nonneg hX0 3))

#print axioms exists_prescribed_spline_correction_polynomial_bound
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
