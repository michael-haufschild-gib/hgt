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
  rw [intervalIntegral.integral_finsetSum (f := fun a (x : ℝ) => x^(k+a))
    (fun a _ => Continuous.intervalIntegrable (by fun_prop) _ _)]
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
    rw [mul_assoc, sum_mul_sum]
    simp only [mul_sum,pow_add,w,geom]
    exact sum_congr rfl fun j _ => sum_congr rfl fun k _ => by ring
  rw [intervalIntegral.integral_congr (fun x _ => h x)]
  simp only [mul_sum]
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

/-- The centered real-place polynomial subtracts the monomial at the mean
of the two residue indices. This is the part shared with the finite block. -/
def centeredResiduePolynomial (d : ℕ+) (x : ℝ) : ℝ :=
  (∑ a ∈ range (d:ℕ), x^a)^2 - ((d:ℕ):ℝ)^2*x^((d:ℕ)-1)

/-- Reflection of one residue index turns Cauchy–Schwarz into the sign of the
centered real-place density, including the two collision endpoints. -/
theorem centeredResiduePolynomial_nonneg (d : ℕ+) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ centeredResiduePolynomial d x := by
  let y := Real.sqrt x
  have hy (j : ℕ) : (y^j)^2 = x^j := by
    rw [← pow_mul,Nat.mul_comm,pow_mul,Real.sq_sqrt hx]
  have hm : (∑ a ∈ range (d:ℕ), y^a*y^((d:ℕ)-1-a)) = (d:ℝ)*y^((d:ℕ)-1) := by
    calc _ = ∑ _a ∈ range (d:ℕ), y^((d:ℕ)-1) := by
           refine sum_congr rfl fun a ha => ?_
           rw [← pow_add]
           congr 1
           have := mem_range.mp ha
           omega
         _ = _ := by simp only [sum_const,card_range,nsmul_eq_mul]
  have h := sum_mul_sq_le_sq_mul_sq (range (d:ℕ)) (fun a => y^a) (fun a => y^((d:ℕ)-1-a))
  rw [hm,mul_pow,hy] at h
  simp only [hy,sum_range_reflect (fun a => x^a)] at h
  exact sub_nonneg.mpr (by simpa only [← sq] using h)

/-- Moments after centering the two residue indices. The subtracted rational
term is the exact integral of the central monomial against (1−x)dx. -/
def centeredRealEndpoint (d : ℕ+) (k : ℕ) : ℝ :=
  2*realEndpoint d k - (d:ℝ)^2*(1/((k:ℝ)+(d:ℕ))-1/((k:ℝ)+(d:ℕ)+1))

theorem centeredRealEndpoint_moment (d : ℕ+) (k : ℕ) :
    centeredRealEndpoint d k = ∫ x in (0:ℝ)..1, x^k*(1-x)*centeredResiduePolynomial d x := by
  let m := k+((d:ℕ)-1)
  have hmd : (m:ℝ)+1 = (k:ℝ)+(d:ℕ) := by
    dsimp only [m]
    rw [Nat.cast_add,Nat.cast_sub d.pos,Nat.cast_one]
    ring
  have hsplit (x : ℝ) : x^k*(1-x)*centeredResiduePolynomial d x =
      x^k*(1-x)*(∑ a ∈ range (d:ℕ), x^a)^2 - (d:ℝ)^2*(x^m-x^(m+1)) := by
    rw [centeredResiduePolynomial,pow_succ x m,show x^m = x^k*x^((d:ℕ)-1) from pow_add ..]
    ring
  simp only [hsplit,centeredRealEndpoint]
  rw [intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _),← realEndpoint_moment _ _ d.pos,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_sub
    (f := fun x : ℝ => x^m) (g := fun x : ℝ => x^(m+1))
    (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _),
    hilbertMoment_eq_integral_pow,hilbertMoment_eq_integral_pow,Nat.cast_succ,hmd]

#print axioms centeredResiduePolynomial_nonneg
#print axioms centeredRealEndpoint_moment
#print axioms realEndpoint_moment
#print axioms realEndpoint_mixed
#print axioms realEndpoint_hankel_nonneg

end GaloisForLFunctions.SignedArithmeticCorrespondences
