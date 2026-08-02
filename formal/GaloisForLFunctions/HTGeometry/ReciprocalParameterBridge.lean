import GaloisForLFunctions.HTGeometry.InverseJetNumerator
import GaloisForLFunctions.HTGeometry.TriangularTailCoefficients

/-!
# The reciprocal jet in the triangular parameters

The tail of a jet carries free parameters, one per coefficient.  Inverting the jet and clearing the
power of the unknown constant term leaves a polynomial in that unknown whose coefficients are, up to
sign, exactly the triangular functions of the parameters.

So the fibre equation of a one-deep observation — the equation satisfied by the unknown constant
term — is the equation whose coefficients are those triangular functions.  That is what turns the
independence and triangularity of the parameter change into a statement about the fibre: the
coefficients of the fibre equation are an algebraically independent, triangular change of the free
parameters of the jet.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

universe u

variable {K : Type u} [CommRing K]

/-- The jet whose `(i+1)`-st coefficient is the `i`-th free parameter, read off the tail. -/
noncomputable def jetParam (K : Type u) [CommRing K] (n : ℕ) : ℕ → MvPolynomial ℕ K :=
  fun i => (triangularTailPoly K n).coeff (i - 1)

theorem jetParam_succ (n i : ℕ) :
    jetParam K n (i + 1) = if i < n then MvPolynomial.X i else 0 := by
  rw [jetParam, Nat.add_sub_cancel, coeff_triangularTailPoly]

/-- **The bridge from the reciprocal jet to the triangular parameters.**  The `j`-th coefficient of
the `n`-th numerator of the inverse jet is, up to sign, the `j`-th triangular function of the free
parameters. -/
theorem coeff_invNumerator_jetParam (n j : ℕ) :
    (invNumerator (jetParam K n) n).coeff j
      = (-1 : MvPolynomial ℕ K) ^ (n - j) * paramCoeff K n j :=
  coeff_invNumerator (triangularTailPoly K n) n j

/-- The top triangular function vanishes: the fibre equation has degree at most `n` in the
coefficients below the horizon. -/
theorem paramCoeff_self {n : ℕ} (hn : n ≠ 0) : paramCoeff K n n = 0 := by
  rw [paramCoeff, Nat.sub_self, pow_zero, Polynomial.coeff_one, if_neg hn]

/-- **The numerator evaluates to the triangular combination.**  Written out, the `n`-th numerator of
the inverse jet is the polynomial `∑_{j < n} (-1)^{n-j} c_j a^j` in the unknown constant term `a`. -/
theorem eval_invNumerator_jetParam {n : ℕ} (hn : n ≠ 0) (a : MvPolynomial ℕ K) :
    (invNumerator (jetParam K n) n).eval a
      = ∑ j ∈ Finset.range n,
          (-1 : MvPolynomial ℕ K) ^ (n - j) * paramCoeff K n j * a ^ j := by
  rw [Polynomial.eval_eq_sum_range'
    (lt_of_le_of_lt (natDegree_invNumerator_le _ n) (Nat.lt_succ_self n)),
    Finset.sum_range_succ]
  have hlast : (invNumerator (jetParam K n) n).coeff n * a ^ n = 0 := by
    rw [coeff_invNumerator_jetParam, paramCoeff_self hn, mul_zero, zero_mul]
  rw [hlast, add_zero]
  exact Finset.sum_congr rfl (fun j _ => by rw [coeff_invNumerator_jetParam])

/-- **The fibre equation in the triangular parameters.**  If a jet `g` inverts the jet whose tail
carries the free parameters, then its `n`-th coefficient satisfies, after clearing the denominator,
the equation of degree `n + 1` in the unknown constant term whose lower coefficients are the
triangular functions of the parameters.

This is the identity that links the fibre of a one-deep observation to the parameter change: the
observed quantity `a^{n+1} g_n` is the value at `a` of a polynomial whose coefficients are an
algebraically independent triangular change of the free jet parameters. -/
theorem pow_mul_eq_paramCoeff_sum {n : ℕ} (hn : n ≠ 0) (g : ℕ → MvPolynomial ℕ K)
    (a : MvPolynomial ℕ K) (h0 : a * g 0 = 1)
    (hrec : ∀ k : ℕ, k + 1 < n + 1 →
      a * g (k + 1) = -∑ j ∈ Finset.range (k + 1), jetParam K n (j + 1) * g (k - j)) :
    a ^ (n + 1) * g n
      = ∑ j ∈ Finset.range n,
          (-1 : MvPolynomial ℕ K) ^ (n - j) * paramCoeff K n j * a ^ j := by
  rw [pow_mul_eq_invNumerator_eval_of_lt (jetParam K n) g a h0 hrec n (Nat.lt_succ_self n),
    eval_invNumerator_jetParam hn]

end GaloisForLFunctions.HTGeometry
