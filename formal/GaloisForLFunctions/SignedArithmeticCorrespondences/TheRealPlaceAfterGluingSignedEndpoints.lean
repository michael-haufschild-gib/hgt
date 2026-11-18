import GaloisForLFunctions.HodgeTheoryOfAFixedPart.WeilsFormInTheGaugeOfTheFlatTail
import GaloisForLFunctions.RHTower.HilbertHankelMomentRepresentation

/-!
# A positive measure for the real-place endpoint correction

In the gauge of a flat divisor, remove the Chebyshev remainder and the diagonal
constant from the row at degree i. At the upper endpoint i+k the residual
archimedean term is a second difference of the harmonic numbers. Its measure
on the unit interval retains the square of every signed endpoint polynomial.
-/

noncomputable section

namespace GaloisForLFunctions.SignedArithmeticCorrespondences
open AbsoluteGeometryOfSpecZ HodgeTheoryOfAFixedPart Finset MeasureTheory

/-- The real-place variation remaining after removing the constant diagonal
and the rational degree minus prime count from the row of the full form. -/
def realEndpoint (i k : ℕ) : ℝ :=
  tailPotential (Icc 1 (i+k)) i -
    ((((i+k : ℕ) : ℝ)/i - chebyshev ((i+k)/i)) + 3/(4*(i : ℝ)) - Real.log (2*Real.pi))

private theorem realEndpoint_harm (i k : ℕ) (hi : 0 < i) :
    2*realEndpoint i k = 2*harm (k+i)-harm k-harm (k+i+i) := by
  rw [realEndpoint,tailPotential_Icc hi (Nat.le_add_right i k),tailRow,Nat.add_sub_cancel_left]
  rw [Nat.add_comm i k]
  ring

private def geom (i : ℕ) (x : ℝ) := ∑ a ∈ range i, x^a

private theorem geom_mul (i : ℕ) (x : ℝ) : geom i x*(1-x) = 1-x^i := by
  induction i with
  | zero => simp [geom]
  | succ i ih =>
    rw [show geom (i+1) x = geom i x + x^i from sum_range_succ .., add_mul, ih, pow_succ]
    ring

private theorem integrated_geom (k i : ℕ) :
    (∫ x in (0:ℝ)..1, x^k * geom i x) = harm (k+i)-harm k := by
  simp only [geom,mul_sum,← pow_add]
  rw [intervalIntegral.integral_finsetSum (fun a _ => (continuous_id.pow _).intervalIntegrable _ _)]
  simp only [hilbertMoment_eq_integral_pow]
  rw [harm, sum_range_add]
  change (∑ a ∈ range i, 1 / (((k+a : ℕ) : ℝ)+1)) =
    _ + _ - ∑ a ∈ range k, 1/((a:ℝ)+1)
  ring

/-- The measure for every offset k is positive on the open unit interval.
Both unregularized harmonic terms use the actual endpoints i+k and 2i+k. -/
theorem realEndpoint_moment (i k : ℕ) (hi : 0 < i) :
    2*realEndpoint i k =
      ∫ x in (0:ℝ)..1, x^k*(1-x)*(∑ a ∈ range i, x^a)^2 := by
  have h (x : ℝ) : x^k*(1-x)*(geom i x)^2 =
      x^k*geom i x - x^(k+i)*geom i x := by
    rw [pow_add, show x^k*(1-x)*(geom i x)^2 = x^k*(geom i x*(1-x))*geom i x by ring,
      geom_mul]
    ring
  change 2*realEndpoint i k = ∫ x in (0:ℝ)..1, x^k*(1-x)*(geom i x)^2
  simp only [h]
  have hc (m : ℕ) : Continuous (fun x : ℝ => x^m*geom i x) := by unfold geom; fun_prop
  rw [intervalIntegral.integral_sub ((hc k).intervalIntegrable _ _) ((hc (k+i)).intervalIntegrable _ _),
    integrated_geom,integrated_geom,realEndpoint_harm _ _ hi]
  ring

/-- The Hankel pairing of two signed endpoint divisors is the integral of
their polynomials against one common real-place measure. -/
theorem realEndpoint_mixed (i L : ℕ) (hi : 0 < i) (S T : Finset ℕ) (u v : ℕ → ℝ) :
    2*(∑ j ∈ S, ∑ k ∈ T, u j*v k*realEndpoint i (L+j+k)) =
      ∫ x in (0:ℝ)..1, (x^L*(1-x)*(∑ a ∈ range i, x^a)^2) *
        (∑ j ∈ S, u j*x^j)*(∑ k ∈ T, v k*x^k) := by
  let w (x : ℝ) := (1-x)*(geom i x)^2
  have hw : Continuous w := by dsimp [w,geom]; fun_prop
  have h (x : ℝ) : (x^L*(1-x)*(∑ a ∈ range i, x^a)^2) *
        (∑ j ∈ S, u j*x^j)*(∑ k ∈ T, v k*x^k) =
      ∑ j ∈ S, ∑ k ∈ T, (u j*v k)*(x^(L+j+k)*w x) := by
    simp only [mul_sum,sum_mul,pow_add,w,geom]
    rw [sum_comm]
    exact sum_congr rfl fun j _ => sum_congr rfl fun k _ => by ring
  simp only [h,mul_sum]
  rw [intervalIntegral.integral_finsetSum (fun j _ => Continuous.intervalIntegrable (by fun_prop) _ _)]
  refine sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_finsetSum (fun k _ => Continuous.intervalIntegrable (by fun_prop) _ _)]
  refine sum_congr rfl fun k _ => ?_
  rw [intervalIntegral.integral_const_mul]
  have hm : (∫ x in (0:ℝ)..1, x^(L+j+k)*w x) = 2*realEndpoint i (L+j+k) := by
    simpa only [w,geom,mul_assoc] using (realEndpoint_moment i (L+j+k) hi).symm
  rw [hm]
  ring

/-- All Hankel matrices of the real-place correction are positive semidefinite,
at every degree and every distance from the collision. -/
theorem realEndpoint_hankel_nonneg (i L : ℕ) (hi : 0 < i) (S : Finset ℕ) (u : ℕ → ℝ) :
    0 ≤ ∑ j ∈ S, ∑ k ∈ S, u j*u k*realEndpoint i (L+j+k) := by
  have h := realEndpoint_mixed i L hi S S u u
  have hp : 0 ≤ 2*(∑ j ∈ S, ∑ k ∈ S, u j*u k*realEndpoint i (L+j+k)) := by
    rw [h]
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x hx
    rw [mul_assoc,← sq]
    exact mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hx.1 _) (sub_nonneg.mpr hx.2))
      (sq_nonneg _)) (sq_nonneg _)
  linarith only [hp]

#print axioms realEndpoint_moment
#print axioms realEndpoint_mixed
#print axioms realEndpoint_hankel_nonneg

end GaloisForLFunctions.SignedArithmeticCorrespondences
