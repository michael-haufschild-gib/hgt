module
public import SQB100CoefficientReconstruction0
public import SQB100CoefficientReconstruction1
public import SQB100CoefficientReconstruction2
public import SQB100CoefficientReconstruction3
public import SQB100CoefficientReconstruction4
public import SQB100CoefficientReconstruction5
public import SQB100CoefficientReconstruction6

@[expose] public section
namespace SQBCompactRow
open Finset
noncomputable section
set_option maxHeartbeats 400000

theorem bernsteinTransform_sub (f g : ℕ → ℕ → ℝ) (t v : ℝ) :
    bernsteinTransform (fun a b => f a b - g a b) t v =
      bernsteinTransform f t v - bernsteinTransform g t v := by
  simp only [bernsteinTransform, sub_mul, sum_sub_distrib]

theorem bernsteinTransform_div (f : ℕ → ℕ → ℝ) (c t v : ℝ) :
    bernsteinTransform (fun a b => f a b / c) t v =
      bernsteinTransform f t v / c := by
  calc
    _ = bernsteinTransform (fun a b => c⁻¹ * f a b) t v := by
      congr 1
      funext a b
      ring
    _ = c⁻¹ * bernsteinTransform f t v := bernsteinTransform_const_mul c⁻¹ f t v
    _ = _ := by ring

theorem tensorRealCoefficient_reconstruction
    (c : ℝ) (j k : ℕ) (hj : j ≤ 8) (hk : k ≤ 12) (t v : ℝ) :
    bernsteinTransform (fun a b => c * degreeElevationCoefficient 8 j a *
      degreeElevationCoefficient 12 k b) t v = c*t^j*v^k := by
  exact tensor_monomial_bernstein_reconstruction 8 12 j k hj hk c t v

def rowCorrection0 : ℝ := (341/480)*(3*(341/480)-6/19)-1/100
def rowCorrection1 : ℝ := (35/480)*(6*(341/480)-6/19)
def rowCorrection2 : ℝ := 3*(35/480)^2

theorem rowCoefficient_eq_split (a b : ℕ) :
    rowCoefficient a b =
      (numeratorCoefficient6 a b : ℝ)/501530650214400000000000000000000 -
      3*(numeratorCoefficient5 a b : ℝ)/13931406950400000000000000000 -
      (numeratorCoefficient4 a b : ℝ)/128994508800000000000000 +
      8*(numeratorCoefficient3 a b : ℝ)/10749542400000000000 -
      (31/8)*(numeratorCoefficient2 a b : ℝ)/298598400000000 -
      (3/8)*(numeratorCoefficient1 a b : ℝ)/8294400000 +
      (15/64)*(numeratorCoefficient0 a b : ℝ)/230400 +
      rowCorrection0 * degreeElevationCoefficient 8 0 a * degreeElevationCoefficient 12 0 b +
      rowCorrection1 * degreeElevationCoefficient 8 1 a * degreeElevationCoefficient 12 0 b +
      rowCorrection2 * degreeElevationCoefficient 8 2 a * degreeElevationCoefficient 12 0 b := by
  by_cases h1 : 1 ≤ a <;> by_cases h2 : 2 ≤ a <;>
    simp [rowCoefficient, rowCorrection0, rowCorrection1, rowCorrection2,
      degreeElevationCoefficient, h1, h2] <;> ring

def groupedSourceRow (t v : ℝ) : ℝ :=
  groupedNumerator6 t v/501530650214400000000000000000000 -
  3*groupedNumerator5 t v/13931406950400000000000000000 -
  groupedNumerator4 t v/128994508800000000000000 +
  8*groupedNumerator3 t v/10749542400000000000 -
  (31/8)*groupedNumerator2 t v/298598400000000 -
  (3/8)*groupedNumerator1 t v/8294400000 +
  (15/64)*groupedNumerator0 t v/230400 +
  ((341+35*t)/480)*(3*((341+35*t)/480)-6/19)-1/100

theorem rowCoefficient_reconstruction (t v : ℝ) :
    bernsteinTransform rowCoefficient t v = groupedSourceRow t v := by
  conv_lhs =>
    arg 1
    ext a b
    rw [rowCoefficient_eq_split]
  simp only [bernsteinTransform_add, bernsteinTransform_sub,
    bernsteinTransform_div, bernsteinTransform_const_mul]
  rw [numeratorCoefficient0_reconstruction, numeratorCoefficient1_reconstruction,
    numeratorCoefficient2_reconstruction, numeratorCoefficient3_reconstruction,
    numeratorCoefficient4_reconstruction, numeratorCoefficient5_reconstruction,
    numeratorCoefficient6_reconstruction,
    tensorRealCoefficient_reconstruction rowCorrection0 0 0 (by omega) (by omega),
    tensorRealCoefficient_reconstruction rowCorrection1 1 0 (by omega) (by omega),
    tensorRealCoefficient_reconstruction rowCorrection2 2 0 (by omega) (by omega)]
  unfold groupedSourceRow rowCorrection0 rowCorrection1 rowCorrection2
  ring

end
end SQBCompactRow
