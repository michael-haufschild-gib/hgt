module
public import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactBernstein.ColumnZero
public import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactBernstein.ColumnOne
public import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactBernstein.ColumnTwo
public import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactBernstein.ColumnThree
public import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactBernstein.ColumnFour
public import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactBernstein.ColumnFive
public import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactBernstein.ColumnSix
public import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactBernstein.ColumnSeven
public import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactBernstein.ColumnEight
public import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactBernstein.RowReconstruction

/-! Exact coefficient and reconstruction component for the compensated compact last-row margin. -/

public section
namespace HTGeometry.EvenCompactBernstein
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
end HTGeometry.EvenCompactBernstein
