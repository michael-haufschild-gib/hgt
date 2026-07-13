import GaloisForLFunctions.RHTower.LocalDivisorJetPrimeFrobenius

/-!
# The infinitesimal relative-K1 class of a local divisor jet

For `A_m = R[X]/(X^m)`, the element `1 + X` is a unit because `X` is nilpotent.  Over a
commutative ring this is the elementary relative-`K₁` witness in the kernel of reduction to the
constant fiber.  It is nontrivial exactly when the positive-length jet is nonreduced (`m > 1`).

This provides a positive successor to determinant-line blindness: the regular determinant of this
unipotent class is one, but the unit itself retains the nilpotent thickness.  A source argument must
therefore control the relative unit/regulator, not only its scalar determinant.
-/

namespace RHTower

noncomputable section

/-- The canonical infinitesimal unit represented by the cotangent coordinate. -/
def localDivisorJetInfinitesimalUnit
    (R : Type*) [CommRing R] (m : ℕ) : LocalDivisorJet R m :=
  1 + localDivisorJetVariable R m

/-- The infinitesimal class is always a unit: its nonconstant part is nilpotent. -/
theorem localDivisorJetInfinitesimalUnit_isUnit
    (R : Type*) [CommRing R] (m : ℕ) :
    IsUnit (localDivisorJetInfinitesimalUnit R m) := by
  rw [localDivisorJetInfinitesimalUnit]
  apply IsNilpotent.isUnit_one_add
  exact ⟨m, localDivisorJetVariable_pow_eq_zero R le_rfl⟩

/-- At jet depth at least two, the relative unit is genuinely nontrivial. -/
theorem localDivisorJetInfinitesimalUnit_ne_one
    (R : Type*) [CommRing R] [Nontrivial R] {m : ℕ} (hm : 1 < m) :
    localDivisorJetInfinitesimalUnit R m ≠ 1 := by
  rw [localDivisorJetInfinitesimalUnit]
  intro h
  have hx : localDivisorJetVariable R m = 0 := by simpa using h
  exact localDivisorJetVariable_ne_zero R hm hx

/-- On a positive-length jet, triviality of the canonical relative unit is exactly simplicity. -/
theorem localDivisorJetInfinitesimalUnit_eq_one_iff
    (R : Type*) [CommRing R] [Nontrivial R] {m : ℕ} (hm : 0 < m) :
    localDivisorJetInfinitesimalUnit R m = 1 ↔ m = 1 := by
  constructor
  · intro h
    by_contra hne
    exact localDivisorJetInfinitesimalUnit_ne_one R (by omega) h
  · rintro rfl
    have hx := localDivisorJetVariable_pow_eq_zero R (m := 1) (n := 1) le_rfl
    simpa [localDivisorJetInfinitesimalUnit] using hx

/-- **Relative-K1 local route to RH.**  If the canonical infinitesimal unit vanishes at every
hypothetical right-half divisor point, its order is one; the first ladder rung makes it even. -/
theorem riemannHypothesis_of_rhLadder_one_of_rightInfinitesimalUnitTrivial
    (hladder : RHLadder 1)
    (hunit : ∀ rho ∈ rightHalf, xi rho = 0 →
      localDivisorJetInfinitesimalUnit ℂ (analyticOrderAt xi rho).toNat = 1) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro rho hrho hzero
  have hmpos : 0 < (analyticOrderAt xi rho).toNat :=
    Nat.pos_of_ne_zero (xi_order_toNat_ne_zero hzero)
  have hmone : (analyticOrderAt xi rho).toNat = 1 :=
    (localDivisorJetInfinitesimalUnit_eq_one_iff ℂ hmpos).mp
      (hunit rho hrho hzero)
  have heven : Even (analyticOrderAt xi rho).toNat :=
    rhLadder_one_iff_even_order.mp hladder rho hrho hzero
  rw [hmone] at heven
  exact Nat.not_even_one heven

/-! ## The finite logarithmic regulator -/

/-- The truncated logarithm `log(1+X)` before passage to the local divisor quotient. -/
def localDivisorJetLogUnitPolynomial (m : ℕ) : Polynomial ℂ :=
  ∑ r ∈ Finset.range (m - 1),
    Polynomial.monomial (r + 1) (((-1 : ℂ) ^ r) / (r + 1 : ℕ))

/-- The characteristic-zero logarithmic regulator of the canonical infinitesimal unit. -/
def localDivisorJetLogUnit (m : ℕ) : LocalDivisorJet ℂ m :=
  jetClass ℂ m (localDivisorJetLogUnitPolynomial m)

/-- At depth at least two, the regulator retains its leading cotangent coefficient. -/
theorem localDivisorJetLogUnitPolynomial_coeff_one {m : ℕ} (hm : 1 < m) :
    (localDivisorJetLogUnitPolynomial m).coeff 1 = 1 := by
  simp [localDivisorJetLogUnitPolynomial, Polynomial.coeff_monomial, hm]

/-- **Injectivity on the canonical relative class.**  The truncated logarithm vanishes exactly
when the positive-length local divisor jet is simple. -/
theorem localDivisorJetLogUnit_eq_zero_iff {m : ℕ} (hm : 0 < m) :
    localDivisorJetLogUnit m = 0 ↔ m = 1 := by
  constructor
  · intro h
    by_contra hne
    have hm2 : 1 < m := by omega
    have hjet : jetClass ℂ m (localDivisorJetLogUnitPolynomial m) = 0 := by
      simpa [localDivisorJetLogUnit] using h
    have hall := (jetClass_eq_zero_iff_coeff_lt_eq_zero ℂ m).mp hjet
    have hcoeff := hall 1 hm2
    rw [localDivisorJetLogUnitPolynomial_coeff_one hm2] at hcoeff
    exact one_ne_zero hcoeff
  · rintro rfl
    change jetClass ℂ 1 0 = 0
    exact map_zero (Ideal.Quotient.mk (jetIdeal ℂ 1))

/-- **Logarithmic-regulator route to RH.**  Vanishing of the actual local relative regulator gives
simplicity; the independent first ladder rung gives even multiplicity. -/
theorem riemannHypothesis_of_rhLadder_one_of_rightLogUnitVanishing
    (hladder : RHLadder 1)
    (hlog : ∀ rho ∈ rightHalf, xi rho = 0 →
      localDivisorJetLogUnit (analyticOrderAt xi rho).toNat = 0) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro rho hrho hzero
  have hmpos : 0 < (analyticOrderAt xi rho).toNat :=
    Nat.pos_of_ne_zero (xi_order_toNat_ne_zero hzero)
  have hmone : (analyticOrderAt xi rho).toNat = 1 :=
    (localDivisorJetLogUnit_eq_zero_iff hmpos).mp (hlog rho hrho hzero)
  have heven : Even (analyticOrderAt xi rho).toNat :=
    rhLadder_one_iff_even_order.mp hladder rho hrho hzero
  rw [hmone] at heven
  exact Nat.not_even_one heven

end

end RHTower
