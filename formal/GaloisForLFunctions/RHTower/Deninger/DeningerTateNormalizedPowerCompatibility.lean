import GaloisForLFunctions.RHTower.Deninger.DeningerRationalDivisorSequence

/-!
# Rational powers and the Tate normalization of the Kummer boundary

Taking divisors turns exponentiation into scaling: `div (u ^ n) = n • div u`.  After Kummer
groupification the characteristic group becomes the rational vector space `Nat.Primes →₀ ℚ`, on
which the rational power correspondence `F_q` acts by multiplication by `q`; on residues this is
`F_q^*(ord_p) = q · ord_p`.  The Tate line is the line on which `F_q` acts by `q⁻¹`, so the residue
valued in the Tate-twisted target is invariant under the whole correspondence, and the weight `-1`
is the only twist with that property.

* `deningerDivisor_pow`, `deningerDivisor_zpow` : exponentiation multiplies divisors.
* `deningerRationalPower_zpow_kummer` : the scaling really is exponentiation on integral powers.
* `deningerOrd_rationalPower` : `F_q^*(ord_p) = q · ord_p`.
* `deningerTateResidue_invariant` : the Tate-twisted Kummer boundary is `F`-invariant.
* `deningerTateWeight_unique` : weight `-1` is the only invariance-producing twist.
-/

namespace RHTower

section ScalarEnd

/-- Scalar endomorphisms compose according to multiplication of scalars. -/
theorem deningerScalarEnd_mul {M : Type*} [AddCommGroup M] [Module ℚ M] (c d : ℚ) :
    ((c * d) • LinearMap.id : M →ₗ[ℚ] M) =
      (c • LinearMap.id : M →ₗ[ℚ] M).comp (d • LinearMap.id) :=
  LinearMap.ext fun x => mul_smul c d x

end ScalarEnd

section IntegralPowers

/-- The divisor of the unit `1` vanishes. -/
@[simp]
theorem deningerDivisor_one : deningerDivisor 1 = 0 :=
  (deningerDivisor_eq_zero_iff (by norm_num)).mpr rfl

/-- Taking divisors inverts inverses. -/
@[simp]
theorem deningerDivisor_inv (u : ℚˣ) : deningerDivisor u⁻¹ = -deningerDivisor u := by
  have h := deningerDivisor_mul u u⁻¹
  rw [mul_inv_cancel, deningerDivisor_one] at h
  exact (eq_neg_of_add_eq_zero_right h.symm)

/-- **Exponentiation multiplies divisors**, natural exponents. -/
theorem deningerDivisor_pow (u : ℚˣ) (n : ℕ) :
    deningerDivisor (u ^ n) = n • deningerDivisor u := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, deningerDivisor_mul, ih, succ_nsmul]

/-- **Exponentiation multiplies divisors**, integral exponents.  This is the characteristic-group
form of `F_q^*[β] = [β]^q`. -/
theorem deningerDivisor_zpow (u : ℚˣ) (n : ℤ) :
    deningerDivisor (u ^ n) = n • deningerDivisor u := by
  obtain ⟨k, hk | hk⟩ := Int.eq_nat_or_neg n
  · subst hk
    rw [zpow_natCast, deningerDivisor_pow, natCast_zsmul]
  · subst hk
    rw [zpow_neg, zpow_natCast, deningerDivisor_inv, deningerDivisor_pow, neg_zsmul,
      natCast_zsmul]

end IntegralPowers

section RationalCharacter

/-- The Kummer groupification `M_P^{gp} ⊗ ℚ` of the characteristic group, in prime coordinates. -/
abbrev DeningerRationalCharacter : Type :=
  Nat.Primes →₀ ℚ

/-- The Kummer map from the rational units into the rational characteristic group. -/
noncomputable def deningerRationalDivisor (u : ℚˣ) : DeningerRationalCharacter :=
  (deningerDivisor u).mapRange (fun n : ℤ => (n : ℚ)) (by simp)

@[simp]
theorem deningerRationalDivisor_apply (u : ℚˣ) (p : Nat.Primes) :
    deningerRationalDivisor u p = ((deningerDivisor u p : ℤ) : ℚ) :=
  rfl

/-- The residue `ord_p` on the rational characteristic group. -/
noncomputable def deningerOrd (p : Nat.Primes) : DeningerRationalCharacter →ₗ[ℚ] ℚ :=
  Finsupp.lapply p

@[simp]
theorem deningerOrd_apply (p : Nat.Primes) (f : DeningerRationalCharacter) :
    deningerOrd p f = f p :=
  rfl

/-- Multiplicity one: the residue of a prime at itself is `1`. -/
theorem deningerOrd_rationalDivisor_primeUnit (p : Nat.Primes) :
    deningerOrd p (deningerRationalDivisor (deningerPrimeUnit p)) = 1 := by
  simp [deningerPadicValRat_primeUnit]

/-- The rational power correspondence `F_q` on the characteristic group: multiplication by `q`. -/
noncomputable def deningerRationalPower (q : ℚ) :
    DeningerRationalCharacter →ₗ[ℚ] DeningerRationalCharacter :=
  q • LinearMap.id

@[simp]
theorem deningerRationalPower_apply (q : ℚ) (f : DeningerRationalCharacter) :
    deningerRationalPower q f = q • f :=
  rfl

/-- The power correspondence is multiplicative in the exponent. -/
theorem deningerRationalPower_mul (q r : ℚ) :
    deningerRationalPower (q * r) =
      (deningerRationalPower q).comp (deningerRationalPower r) :=
  deningerScalarEnd_mul q r

/-- The trivial exponent acts trivially. -/
@[simp]
theorem deningerRationalPower_one :
    deningerRationalPower 1 = LinearMap.id :=
  one_smul ℚ _

/-- **The scaling really is exponentiation.**  On an integral exponent the power correspondence
carries the Kummer class of `u` to the Kummer class of `u ^ n`. -/
theorem deningerRationalPower_zpow_kummer (u : ℚˣ) (n : ℤ) :
    deningerRationalPower ((n : ℚ)) (deningerRationalDivisor u) =
      deningerRationalDivisor (u ^ n) := by
  refine Finsupp.ext fun p => ?_
  simp [deningerDivisor_zpow, smul_eq_mul]

/-- **Equation (10).**  The rational power correspondence scales every residue by its exponent. -/
theorem deningerOrd_rationalPower (q : ℚ) (p : Nat.Primes) (f : DeningerRationalCharacter) :
    deningerOrd p (deningerRationalPower q f) = q * deningerOrd p f := by
  simp [smul_eq_mul]

/-- **Equation (10)**, as an identity of functionals: `F_q^*(ord_p) = q · ord_p`. -/
theorem deningerOrd_comp_rationalPower (q : ℚ) (p : Nat.Primes) :
    (deningerOrd p).comp (deningerRationalPower q) = q • deningerOrd p :=
  LinearMap.ext fun f => deningerOrd_rationalPower q p f

end RationalCharacter

section TateNormalization

/-- The Tate line `ℚ(1)`: the rational line on which the power correspondence `F_q` acts by
`q⁻¹`. -/
def deningerTateLineAction (q : ℚ) : ℚ →ₗ[ℚ] ℚ :=
  q⁻¹ • LinearMap.id

@[simp]
theorem deningerTateLineAction_apply (q x : ℚ) :
    deningerTateLineAction q x = q⁻¹ * x :=
  rfl

/-- The Tate action is multiplicative in the exponent. -/
theorem deningerTateLineAction_mul (q r : ℚ) :
    deningerTateLineAction (q * r) =
      (deningerTateLineAction q).comp (deningerTateLineAction r) := by
  show ((q * r)⁻¹ • LinearMap.id : ℚ →ₗ[ℚ] ℚ) = _
  rw [mul_inv]
  exact deningerScalarEnd_mul _ _

/-- The Kummer boundary with values in the Tate-twisted residue target. -/
noncomputable def deningerTateResidue (p : Nat.Primes) : DeningerRationalCharacter →ₗ[ℚ] ℚ :=
  deningerOrd p

/-- **Equation (11).**  Tensoring the residue target with the Tate line makes the Kummer boundary
invariant under the whole rational power correspondence: the weight `+1` of the residue and the
weight `-1` of the Tate line cancel. -/
theorem deningerTateResidue_invariant {q : ℚ} (hq : q ≠ 0) (p : Nat.Primes) :
    (deningerTateLineAction q).comp
        ((deningerTateResidue p).comp (deningerRationalPower q)) =
      deningerTateResidue p := by
  refine LinearMap.ext fun f => ?_
  show q⁻¹ * (deningerOrd p (deningerRationalPower q f)) = deningerOrd p f
  rw [deningerOrd_rationalPower, ← mul_assoc, inv_mul_cancel₀ hq, one_mul]

/-- **Weight rigidity of the Tate normalization.**  A scalar twist `χ` of the residue target makes
the Kummer boundary invariant under every nonzero exponent exactly when `χ` is the Tate weight
`q ↦ q⁻¹`.  Multiplicity one at the prime supplies the test vector that forces the weight. -/
theorem deningerTateWeight_unique (χ : ℚ → ℚ) :
    (∀ q : ℚ, q ≠ 0 → ∀ p : Nat.Primes,
        ((χ q • LinearMap.id : ℚ →ₗ[ℚ] ℚ)).comp
            ((deningerOrd p).comp (deningerRationalPower q)) = deningerOrd p) ↔
      ∀ q : ℚ, q ≠ 0 → χ q = q⁻¹ := by
  constructor
  · intro h q hq
    let p : Nat.Primes := ⟨2, Nat.prime_two⟩
    have key : χ q * q = 1 := by
      have hp := congrArg (fun T : DeningerRationalCharacter →ₗ[ℚ] ℚ =>
        T (Finsupp.single p (1 : ℚ))) (h q hq p)
      simpa [deningerOrd_rationalPower, smul_eq_mul] using hp
    exact eq_inv_of_mul_eq_one_left key
  · intro h q hq p
    refine LinearMap.ext fun f => ?_
    show χ q • (deningerOrd p (deningerRationalPower q f)) = deningerOrd p f
    rw [deningerOrd_rationalPower, h q hq, smul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ hq, one_mul]

end TateNormalization

end RHTower
