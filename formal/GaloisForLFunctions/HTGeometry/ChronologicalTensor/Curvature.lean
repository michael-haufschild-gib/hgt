import GaloisForLFunctions.HTGeometry.ChronologicalTensor.SixPoint
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Curved supporting arc of the six-endpoint capacity ball

Every parameter is clamped into the explicitly constructed interval
`[1/3, sqrt 2 - 1]`. This produces nonnegative coefficient rays with an exact
global bound and a unit-cost maximizing probe, without external assumptions.
The actual first and second derivatives of the dual response curve have a
strictly positive turning determinant on the whole supporting arc.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section

def arcEnd : ℝ := Real.sqrt 2 - 1

def arcPosition (s : ℝ) : ℝ := max (1/3) (min s arcEnd)

def weightedSixResponse (A B a b c d e : ℝ) : ℝ :=
  A * separatedThree a b c d e + B * rainbowThree a b c d e

def arcA (s : ℝ) : ℝ := 8 * arcPosition s
def arcB (s : ℝ) : ℝ := (3 * arcPosition s - 1) * (1 - arcPosition s)
def arcCapacity (s : ℝ) : ℝ := (arcPosition s)^(2 : ℕ) * (1 - (arcPosition s)^(2 : ℕ))

theorem arcEnd_bounds : (1/3 : ℝ) ≤ arcEnd ∧ arcEnd ≤ 5/12 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by positivity)
  have hn := Real.sqrt_nonneg (2 : ℝ)
  unfold arcEnd
  constructor <;> nlinarith

theorem arcEnd_relation : 1 - arcEnd^(2 : ℕ) - 2 * arcEnd = 0 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by positivity)
  unfold arcEnd
  nlinarith

theorem arcPosition_bounds (s : ℝ) :
    (1/3 : ℝ) ≤ arcPosition s ∧ arcPosition s ≤ arcEnd :=
  ⟨le_max_left _ _, max_le arcEnd_bounds.1 (min_le_right _ _)⟩

theorem arcPosition_gap_nonneg (s : ℝ) :
    0 ≤ 1 - (arcPosition s)^(2 : ℕ) - 2 * arcPosition s := by
  have hb := arcPosition_bounds s
  have he := arcEnd_bounds
  have hr := arcEnd_relation
  nlinarith [mul_nonneg (sub_nonneg.mpr hb.2)
    (show 0 ≤ arcEnd + arcPosition s + 2 by linarith)]

theorem arc_coefficients_nonneg (s : ℝ) :
    0 ≤ arcA s ∧ 0 ≤ arcB s ∧ 0 ≤ arcCapacity s := by
  have hb := arcPosition_bounds s
  have he := arcEnd_bounds
  have hc : 0 ≤ arcPosition s := by linarith
  have h1 : 0 ≤ 1 - arcPosition s := by linarith
  have h3 : 0 ≤ 3 * arcPosition s - 1 := by linarith
  have hsq : 0 ≤ 1 - (arcPosition s)^(2 : ℕ) := by nlinarith
  exact ⟨mul_nonneg (by positivity) hc, mul_nonneg h3 h1, mul_nonneg (sq_nonneg _) hsq⟩

theorem supporting_gap_identity (q x y : ℝ) :
    q^(2 : ℕ) * (1-q^(2 : ℕ)) * (x+y)^(3 : ℕ) -
        (2*q*x*y^(2 : ℕ) + (3*q-1)*(1-q)*(x+y)*x^(2 : ℕ)) =
      (x-q*(x+y))^(2 : ℕ) * ((1-q^(2 : ℕ))*(x+y)-2*q*x) := by ring

theorem arc_cubic_bound (s x y : ℝ) :
    arcA s / 4 * |x| * |y|^(2 : ℕ) + arcB s * (|x|+|y|) * |x|^(2 : ℕ) ≤
      arcCapacity s * (|x|+|y|)^(3 : ℕ) := by
  have hq := arcPosition_gap_nonneg s
  have hc : 0 ≤ 1 - (arcPosition s)^(2 : ℕ) := by
    have hb := arcPosition_bounds s
    linarith
  have hlast : 0 ≤ (1-(arcPosition s)^(2 : ℕ))*(|x|+|y|)-2*arcPosition s* |x| := by
    nlinarith [mul_nonneg hq (abs_nonneg x), mul_nonneg hc (abs_nonneg y)]
  have hh := mul_nonneg (sq_nonneg (|x|-arcPosition s*(|x|+|y|))) hlast
  rw [← supporting_gap_identity] at hh
  dsimp [arcA, arcB, arcCapacity]
  nlinarith

theorem weightedSix_majorant (A B a b c d e : ℝ) :
    |weightedSixResponse A B a b c d e| ≤
      |A| / 4 * (|b|+|c|+|d|) * (|a|+|e|)^(2 : ℕ) +
        |B| * sixCost a b c d e * (|b|+|c|+|d|)^(2 : ℕ) := by
  let t := sixCost a b c d e
  let x := |b|+|c|+|d|
  let p := |a|+|e|
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have ht : 0 ≤ t := by dsimp [t, sixCost]; positivity
  have hmid : |b+c+d| ≤ x :=
    (abs_add_le (b+c) d).trans (add_le_add (abs_add_le b c) le_rfl)
  have hsum : |a+b+c+d+e| ≤ t := by
    dsimp [t, sixCost]
    calc
      _ ≤ |a+b+c+d| + |e| := abs_add_le _ _
      _ ≤ (|a+b+c| + |d|) + |e| := add_le_add (abs_add_le _ _) le_rfl
      _ ≤ ((|a+b| + |c|) + |d|) + |e| :=
        add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl
      _ ≤ _ := add_le_add (add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl) le_rfl
  have hac : |a| * |e| ≤ p^(2 : ℕ)/4 := by
    dsimp [p]
    nlinarith [sq_nonneg (|a|-|e|)]
  have hcx : |c| ≤ x := by dsimp [x]; linarith [abs_nonneg b, abs_nonneg d]
  calc
    _ ≤ |A| * |a| * |c| * |e| + |B| * t*x* |c| := by
      calc
        _ ≤ |A*separatedThree a b c d e| + |B*rainbowThree a b c d e| := abs_add_le _ _
        _ = |A| * |a| * |c| * |e| + |B| * |a+b+c+d+e| * |b+c+d| * |c| := by
          simp only [separatedThree, rainbowThree, abs_mul]
          ring
        _ ≤ _ := by gcongr
    _ ≤ |A| / 4* |c| * p^(2 : ℕ) + |B| * t*x* |c| := by
      have hh := mul_le_mul_of_nonneg_left hac (mul_nonneg (abs_nonneg A) (abs_nonneg c))
      nlinarith
    _ ≤ |A| / 4*x*p^(2 : ℕ) + |B| * t*x^(2 : ℕ) := by
      have hfirst := mul_le_mul_of_nonneg_right hcx (show 0 ≤ |A| / 4*p^(2 : ℕ) by positivity)
      have hsecond := mul_le_mul_of_nonneg_left hcx (show 0 ≤ |B| * t*x by positivity)
      nlinarith

theorem arc_sharp_bound (s a b c d e : ℝ) :
    |weightedSixResponse (arcA s) (arcB s) a b c d e| ≤
      arcCapacity s * sixCost a b c d e ^ (3 : ℕ) := by
  have h := weightedSix_majorant (arcA s) (arcB s) a b c d e
  have hc := arc_coefficients_nonneg s
  rw [abs_of_nonneg hc.1, abs_of_nonneg hc.2.1] at h
  have hk := arc_cubic_bound s (|b|+|c|+|d|) (|a|+|e|)
  rw [abs_of_nonneg (show 0 ≤ |b|+|c|+|d| by positivity),
    abs_of_nonneg (show 0 ≤ |a|+|e| by positivity)] at hk
  have ht : |b|+|c|+|d|+(|a|+|e|) = sixCost a b c d e := by
    unfold sixCost; ring
  rw [ht] at hk
  exact h.trans hk

theorem arc_attained (s : ℝ) :
    sixCost ((1-arcPosition s)/2) 0 (arcPosition s) 0 ((1-arcPosition s)/2) = 1 ∧
    |weightedSixResponse (arcA s) (arcB s)
      ((1-arcPosition s)/2) 0 (arcPosition s) 0 ((1-arcPosition s)/2)| = arcCapacity s := by
  have hb := arcPosition_bounds s
  have he := arcEnd_bounds
  have hq : 0 ≤ arcPosition s := by linarith
  have hp : 0 ≤ (1-arcPosition s)/2 := by linarith
  constructor
  · simp only [sixCost, abs_of_nonneg hp, abs_of_nonneg hq, abs_zero]
    ring
  · have hr : weightedSixResponse (arcA s) (arcB s)
        ((1-arcPosition s)/2) 0 (arcPosition s) 0 ((1-arcPosition s)/2) = arcCapacity s := by
      unfold weightedSixResponse separatedThree rainbowThree arcA arcB arcCapacity
      ring
    rw [hr, abs_of_nonneg (arc_coefficients_nonneg s).2.2]

def responseX (t : ℝ) : ℝ := t*(1-t)^(2 : ℕ)/4
def responseY (t : ℝ) : ℝ := t^(2 : ℕ)

theorem responseX_hasDerivAt (t : ℝ) :
    HasDerivAt responseX ((1-4*t+3*t^(2 : ℕ))/4) t := by
  convert! ((hasDerivAt_id (𝕜 := ℝ) t).mul (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id (𝕜 := ℝ) t)).pow 2)).div_const 4 using 1
  dsimp [responseX]
  ring

theorem responseY_hasDerivAt (t : ℝ) : HasDerivAt responseY (2*t) t := by
  convert! (hasDerivAt_id (𝕜 := ℝ) t).pow 2 using 1
  dsimp [responseY]
  ring

theorem responseX_deriv_hasDerivAt (t : ℝ) :
    HasDerivAt (deriv responseX) ((-4+6*t)/4) t := by
  have heq : deriv responseX = fun u => (1-4*u+3*u^(2 : ℕ))/4 := by
    funext u
    exact (responseX_hasDerivAt u).deriv
  rw [heq]
  convert! (((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id (𝕜 := ℝ) t).const_mul 4)).add
    (((hasDerivAt_id (𝕜 := ℝ) t).pow 2).const_mul 3)).div_const 4 using 1
  dsimp
  ring

theorem responseY_deriv_hasDerivAt (t : ℝ) :
    HasDerivAt (deriv responseY) 2 t := by
  have heq : deriv responseY = fun u => 2*u := by
    funext u
    exact (responseY_hasDerivAt u).deriv
  rw [heq]
  convert! (hasDerivAt_id (𝕜 := ℝ) t).const_mul 2 using 1
  ring

theorem response_turning_determinant (t : ℝ) :
    deriv responseX t * deriv (deriv responseY) t -
      deriv responseY t * deriv (deriv responseX) t = (1-3*t^(2 : ℕ))/2 := by
  rw [(responseX_hasDerivAt t).deriv, (responseY_hasDerivAt t).deriv,
    (responseX_deriv_hasDerivAt t).deriv, (responseY_deriv_hasDerivAt t).deriv]
  ring

theorem arc_strict_turning (s : ℝ) :
    0 < deriv responseX (arcPosition s) * deriv (deriv responseY) (arcPosition s) -
      deriv responseY (arcPosition s) * deriv (deriv responseX) (arcPosition s) := by
  rw [response_turning_determinant]
  have hb := arcPosition_bounds s
  have he := arcEnd_bounds
  nlinarith

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
