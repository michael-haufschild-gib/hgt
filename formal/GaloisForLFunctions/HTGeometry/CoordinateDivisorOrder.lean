import GaloisForLFunctions.HTGeometry.TameMonomialEigenvolume
import GaloisForLFunctions.HTGeometry.EigenvolumeUnitInvariance
import Mathlib.Algebra.MvPolynomial.Division

/-!
# Orders along the coordinate divisors

Each coordinate of a polynomial ring over a field generates a height-one prime, so it is a prime
divisor, and the local ring there is a discrete valuation ring with the coordinate as uniformizer.
The order of a monomial along such a divisor is therefore its exponent in that coordinate.

Applied to the toric model this makes the divisor data explicit: the logarithmic volume form has a
simple pole along each coordinate divisor, and the Jacobian determinant of a tame monomial map has
order exactly `e - 1` there.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial IsDiscreteValuationRing

variable {k : Type*} [Field k] {σ : Type*} [Fintype σ] [DecidableEq σ]

omit [Fintype σ] [DecidableEq σ] in
theorem isPrime_span_X (i : σ) : (Ideal.span {(X i : MvPolynomial σ k)}).IsPrime :=
  (Ideal.span_singleton_prime (MvPolynomial.X_prime (R := k) (i := i)).ne_zero).mpr
    MvPolynomial.X_prime

omit [DecidableEq σ] in
theorem height_span_X (i : σ) : (Ideal.span {(X i : MvPolynomial σ k)}).height = 1 :=
  Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero (MvPolynomial.X_prime (R := k) (i := i)).ne_zero)
    (MvPolynomial.X_prime (R := k) (i := i)).not_unit

/-- The prime divisor cut out by a coordinate. -/
noncomputable def coordDivisor (i : σ) : PrimeDivisor (MvPolynomial σ k) :=
  ⟨Ideal.span {X i}, isPrime_span_X i, height_span_X i⟩

omit [DecidableEq σ] in
@[simp] theorem coordDivisor_val (i : σ) :
    (coordDivisor (k := k) i).1 = Ideal.span {(X i : MvPolynomial σ k)} :=
  rfl

omit [DecidableEq σ] in
/-- The coordinate is a uniformizer of the local ring along its own divisor. -/
theorem irreducible_algebraMap_X (i : σ) :
    Irreducible (algebraMap (MvPolynomial σ k)
      (Localization.AtPrime (coordDivisor (k := k) i).1) (X i)) := by
  refine (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr ?_
  have h := IsLocalization.AtPrime.map_eq_maximalIdeal (coordDivisor (k := k) i).1
    (Localization.AtPrime (coordDivisor (k := k) i).1)
  refine h.symm.trans ?_
  show Ideal.map (algebraMap (MvPolynomial σ k)
    (Localization.AtPrime (coordDivisor (k := k) i).1)) (Ideal.span {X i}) = _
  rw [Ideal.map_span, Set.image_singleton]

omit [DecidableEq σ] in
@[simp] theorem orderAt_coordDivisor_X_self (i : σ) :
    orderAt (coordDivisor (k := k) i) (X i) = 1 :=
  addVal_uniformizer (irreducible_algebraMap_X i)

@[simp] theorem orderAt_coordDivisor_X_of_ne {i j : σ} (h : j ≠ i) :
    orderAt (coordDivisor (k := k) i) (X j) = 0 := by
  by_contra hne
  have hmem := (orderAt_ne_zero_iff _ _).mp hne
  rw [coordDivisor_val, Ideal.mem_span_singleton] at hmem
  have hev := map_dvd (MvPolynomial.eval fun l : σ => if l = i then (0 : k) else 1) hmem
  rw [MvPolynomial.eval_X, MvPolynomial.eval_X, if_pos rfl, if_neg h] at hev
  exact one_ne_zero (zero_dvd_iff.mp hev)

theorem orderAt_prod {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [IsIntegrallyClosed B] (P : PrimeDivisor B) {ι : Type*} (s : Finset ι) (f : ι → B) :
    orderAt P (∏ i ∈ s, f i) = ∑ i ∈ s, orderAt P (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [orderAt]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, orderAt_mul, ih]

theorem orderAt_pow {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [IsIntegrallyClosed B] (P : PrimeDivisor B) (a : B) (n : ℕ) :
    orderAt P (a ^ n) = n • orderAt P a := by
  induction n with
  | zero => simp [orderAt]
  | succ n ih => rw [pow_succ, orderAt_mul, ih, succ_nsmul]

/-- **The logarithmic volume form has a simple pole along each coordinate divisor.** -/
theorem orderAt_coordDivisor_prod_X (i : σ) :
    orderAt (coordDivisor (k := k) i) (∏ j : σ, X j) = 1 := by
  rw [orderAt_prod]
  rw [Finset.sum_eq_single i]
  · exact orderAt_coordDivisor_X_self i
  · intro j _ hj
    exact orderAt_coordDivisor_X_of_ne hj
  · intro h
    exact absurd (Finset.mem_univ i) h


/-- **The Jacobian determinant of a tame monomial map has order exactly `e i - 1` along the
`i`-th coordinate divisor.**  This is the shift of the ramification order law, realised. -/
theorem orderAt_coordDivisor_det_jacobian (e : σ → ℕ) (hu : ∀ i, IsUnit ((e i : k))) (i : σ) :
    orderAt (coordDivisor (k := k) i) ((jacobian k σ (monomialMap k σ e)).det) =
      ((e i - 1 : ℕ) : ℕ∞) := by
  obtain ⟨u, hu'⟩ := det_jacobian_monomialMap_eq_unit_mul e hu
  rw [hu', orderAt_mul, orderAt_unit, zero_add, orderAt_prod, Finset.sum_eq_single i]
  · rw [orderAt_pow, orderAt_coordDivisor_X_self]
    simp
  · intro j _ hj
    rw [orderAt_pow, orderAt_coordDivisor_X_of_ne hj]
    simp
  · intro h
    exact absurd (Finset.mem_univ i) h
omit [DecidableEq σ] in
@[simp] theorem orderAt_one {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [IsIntegrallyClosed B] (P : PrimeDivisor B) : orderAt P (1 : B) = 0 := by
  simp [orderAt]

omit [DecidableEq σ] in
/-- **The ramification index of a monomial map along the `i`-th coordinate divisor is `e i`.** -/
theorem orderAt_coordDivisor_monomialMap_X (e : σ → ℕ) (i : σ) :
    orderAt (coordDivisor (k := k) i) (monomialMap k σ e (X i)) = (e i : ℕ∞) := by
  rw [monomialMap_X, orderAt_pow, orderAt_coordDivisor_X_self]
  simp

/-- **The logarithmic volume form has order `-1` along each coordinate divisor.**  In the
vocabulary of the ramification system this is the horizon being a reduced divisor, realised in the
toric model. -/
theorem formOrder_coordDivisor_log (i : σ) :
    formOrder (1 : MvPolynomial σ k) (∏ j : σ, X j) (coordDivisor (k := k) i) = -1 := by
  show ((orderAt (coordDivisor (k := k) i) (1 : MvPolynomial σ k)).toNat : ℤ) -
    ((orderAt (coordDivisor (k := k) i) (∏ j : σ, X j)).toNat : ℤ) = -1
  rw [orderAt_one, orderAt_coordDivisor_prod_X]
  simp

end GaloisForLFunctions.HTGeometry
