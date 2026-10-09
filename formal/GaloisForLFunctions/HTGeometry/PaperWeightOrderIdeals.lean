import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.NonnegativeWeights
import Mathlib.RingTheory.Ideal.Operations

/-!
# Nonnegative weights control every power of a homogeneous ideal

Apply the paper's nonnegative-monomial theorem to make lower weight bounds
into actual ideals. Products add the bounds, so generators of weight at
least `d` force every element of the `n`th ideal power to have weight at
least `n*d`. Zero-weight variables and arbitrary commutative coefficient
rings are allowed.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

variable {σ R : Type*} [CommRing R]

private theorem weightOrder_mul {w : σ → ℤ} {m n : ℤ} {p q : MvPolynomial σ R}
    (hp : ∀ e, Finsupp.weight w e < m → coeff e p = 0)
    (hq : ∀ e, Finsupp.weight w e < n → coeff e q = 0) :
    ∀ e, Finsupp.weight w e < m + n → coeff e (p * q) = 0 := by
  classical
  intro e he
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨a, b⟩ hab
  have hs : a + b = e := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
  have hw : Finsupp.weight w a + Finsupp.weight w b = Finsupp.weight w e := by
    rw [← map_add, hs]
  by_cases ha : Finsupp.weight w a < m
  · rw [hp a ha, zero_mul]
  · rw [hq b (by omega), mul_zero]

/-- Polynomials with no monomial below the indicated nonnegative-weight order. -/
def paperWeightOrderIdeal (w : σ → ℤ) (hw : ∀ i, 0 ≤ w i) (n : ℤ) :
    Ideal (MvPolynomial σ R) where
  carrier := {p | ∀ e, Finsupp.weight w e < n → coeff e p = 0}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq e he
    rw [coeff_add, hp e he, hq e he, add_zero]
  smul_mem' := by
    intro q p hp
    change ∀ e, Finsupp.weight w e < n → coeff e (q * p) = 0
    have hq : ∀ e, Finsupp.weight w e < (0 : ℤ) → coeff e q = 0 := by
      intro e he
      exact False.elim ((not_lt_of_ge (StableCoordinate.monomial_weight_nonneg w hw e)) he)
    simpa only [zero_add] using weightOrder_mul hq hp

/-- The zero order includes every polynomial, by the source nonnegative-weight theorem. -/
theorem paperWeightOrderIdeal_zero (w : σ → ℤ) (hw : ∀ i, 0 ≤ w i) :
    paperWeightOrderIdeal (R := R) w hw 0 = ⊤ := by
  ext p
  constructor
  · intro _
    trivial
  · intro _ e he
    exact False.elim ((not_lt_of_ge (StableCoordinate.monomial_weight_nonneg w hw e)) he)

/-- Multiplication adds lower weight bounds. -/
theorem paperWeightOrderIdeal_mul_le (w : σ → ℤ) (hw : ∀ i, 0 ≤ w i) (m n : ℤ) :
    paperWeightOrderIdeal (R := R) w hw m * paperWeightOrderIdeal w hw n ≤
      paperWeightOrderIdeal w hw (m + n) := by
  exact Ideal.mul_le.mpr fun _ hp _ hq => weightOrder_mul hp hq

/-- A homogeneous polynomial has no coefficients below its own weight. -/
theorem paperWeightOrderIdeal_mem_of_homogeneous (w : σ → ℤ) (hw : ∀ i, 0 ≤ w i)
    {p : MvPolynomial σ R} {n : ℤ} (hp : p.IsWeightedHomogeneous w n) :
    p ∈ paperWeightOrderIdeal w hw n := by
  intro e he
  exact hp.coeff_eq_zero e (ne_of_lt he)

/-- A nonzero homogeneous polynomial cannot gain a strictly larger weight order. -/
theorem paperWeightOrderIdeal_not_mem_of_homogeneous (w : σ → ℤ) (hw : ∀ i, 0 ≤ w i)
    {p : MvPolynomial σ R} {m n : ℤ} (hp : p.IsWeightedHomogeneous w m)
    (hp0 : p ≠ 0) (hmn : m < n) : p ∉ paperWeightOrderIdeal w hw n := by
  obtain ⟨e, he⟩ := MvPolynomial.ne_zero_iff.mp hp0
  intro h
  exact he (h e (by rw [hp he]; exact hmn))

/-- The lower bound multiplies by the ideal-power exponent. -/
theorem paperWeightOrderIdeal_pow_le (w : σ → ℤ) (hw : ∀ i, 0 ≤ w i)
    (I : Ideal (MvPolynomial σ R)) (d : ℤ)
    (hI : I ≤ paperWeightOrderIdeal w hw d) (n : ℕ) :
    I ^ n ≤ paperWeightOrderIdeal w hw ((n : ℤ) * d) := by
  induction n with
  | zero => simp [paperWeightOrderIdeal_zero]
  | succ n ih =>
    have he : ((n + 1 : ℕ) : ℤ) * d = (n : ℤ) * d + d := by push_cast; ring
    rw [pow_succ, he]
    apply Ideal.mul_le.mpr
    intro p hp q hq
    exact paperWeightOrderIdeal_mul_le w hw _ _ (Ideal.mul_mem_mul (ih hp) (hI hq))

/-- Natural monomial weights agree with their integral casts. -/
theorem paperNatWeight_cast (w : σ → ℕ) (e : σ →₀ ℕ) :
    Finsupp.weight (fun i => (w i : ℤ)) e = (Finsupp.weight w e : ℤ) := by
  classical
  simp only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul, Nat.cast_sum, Nat.cast_mul]
  rfl

/-- A natural weighted homogeneous polynomial is also homogeneous for integral weights. -/
theorem paperIsWeightedHomogeneous_int {w : σ → ℕ} {p : MvPolynomial σ R} {n : ℕ}
    (hp : p.IsWeightedHomogeneous w n) :
    p.IsWeightedHomogeneous (fun i => (w i : ℤ)) (n : ℤ) := by
  intro e he
  rw [paperNatWeight_cast, hp he]

end

end GaloisForLFunctions.HTGeometry
