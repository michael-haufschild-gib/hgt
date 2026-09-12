module
public import SQB100CoefficientColumn0
public import SQB100CoefficientColumn1
public import SQB100CoefficientColumn2
public import SQB100CoefficientColumn3
public import SQB100CoefficientColumn4
public import SQB100CoefficientColumn5
public import SQB100CoefficientColumn6
public import SQB100CoefficientColumn7
public import SQB100CoefficientColumn8
public import SQB100RowReconstruction

public section
namespace SQBCompactRow
open Finset
noncomputable section

theorem rowCoefficient_nonneg (a : Fin 9) (b : Fin 13) :
    0 ≤ rowCoefficient a b := by
  fin_cases a
  · exact rowCoefficient_column0_nonneg b
  · exact rowCoefficient_column1_nonneg b
  · exact rowCoefficient_column2_nonneg b
  · exact rowCoefficient_column3_nonneg b
  · exact rowCoefficient_column4_nonneg b
  · exact rowCoefficient_column5_nonneg b
  · exact rowCoefficient_column6_nonneg b
  · exact rowCoefficient_column7_nonneg b
  · exact rowCoefficient_column8_nonneg b

theorem groupedSourceRow_nonneg {t v : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 ≤ groupedSourceRow t v := by
  rw [← rowCoefficient_reconstruction]
  unfold bernsteinTransform
  apply sum_nonneg
  intro a ha
  apply sum_nonneg
  intro b hb
  have hc := rowCoefficient_nonneg ⟨a, mem_range.mp ha⟩ ⟨b, mem_range.mp hb⟩
  have ht : 0 ≤ unscaledBernstein 8 a t :=
    mul_nonneg (pow_nonneg ht0 _) (pow_nonneg (sub_nonneg.mpr ht1) _)
  have hv : 0 ≤ unscaledBernstein 12 b v :=
    mul_nonneg (pow_nonneg hv0 _) (pow_nonneg (sub_nonneg.mpr hv1) _)
  exact mul_nonneg (mul_nonneg hc ht) hv

end
end SQBCompactRow
