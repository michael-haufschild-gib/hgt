import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic

/-!
# Secular weld rigidity: no equivariant retraction onto the tame block

A two-block weld couples a tame (scalar) block to a wild block carried by
nontrivial scaling weights.  Operationally the weld is **rigid** when the
inclusion of the tame block admits no equivariant retraction.  This file
formalizes the shared mechanism and two of its faces.

* `equivariant_linear_kills_scaled` — a linear map intertwining a scaling with
  eigenvalue `a ≠ 1` annihilates every `a`-eigenvector.  This single mechanism
  drives both rigidity instances below.
* On the secular coefficient algebra — the complex group algebra of the
  prime-exponent lattice `⊕_p ℤ`, one invertible generator per prime — the
  prime dilation `σ_p` scales the lane-`p` generator by `p⁻¹`.  The generator
  is a unit, an equivariant algebra retraction onto the scalars would have to
  send it to `0`, and ring maps send units to units:
  `no_equivariant_dilation_retraction`, `secularWeld_nonSplit`.
* On the formal weight ring `ℚ[X]` with the weight shift `X ↦ t·X`, every
  equivariant linear functional kills all positive-weight monomials and hence
  factors through the weight-zero coefficient: the tame projection is the only
  equivariant extraction (`equivariant_functional_eq_constant_coeff`).
-/

open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

/-- **Equivariance kills nontrivial weights.**  A linear map `r` intertwining a
map `σ` (`r ∘ σ = r`) annihilates every `σ`-eigenvector with eigenvalue `a ≠ 1`. -/
theorem equivariant_linear_kills_scaled {K M N : Type*} [Field K]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (r : M →ₗ[K] N) (σ : M → M) (hequi : ∀ x, r (σ x) = r x)
    {x : M} {a : K} (hx : σ x = a • x) (ha : a ≠ 1) : r x = 0 := by
  have h1 : r x = a • r x := by
    conv_lhs => rw [← hequi x, hx]
    exact map_smul r a x
  have hne : a - 1 ≠ 0 := sub_ne_zero.mpr ha
  have h2 : (a - 1) • r x = 0 := by
    rw [sub_smul, one_smul, ← h1, sub_self]
  calc r x = (a - 1)⁻¹ • ((a - 1) • r x) := (inv_smul_smul₀ hne _).symm
    _ = 0 := by rw [h2, smul_zero]

namespace SecularWeld

/-- The exponent lattice of the secular coordinates: one integer lane per prime. -/
abbrev PrimeExponents : Type := Nat.Primes →₀ ℤ

/-- The secular coefficient algebra: the complex group algebra of the
prime-exponent lattice — Laurent polynomials in one invertible generator per
prime, the coordinate ring of the infinite prime torus. -/
abbrev SecularAlgebra : Type := AddMonoidAlgebra ℂ PrimeExponents

/-- The dilation weight of an exponent vector on the prime-`p` lane: `p^{-m_p}`. -/
def dilationWeight (p : Nat.Primes) (m : PrimeExponents) : ℂ :=
  ((p : ℕ) : ℂ) ^ (-(m p))

theorem primeCast_ne_zero (p : Nat.Primes) : ((p : ℕ) : ℂ) ≠ 0 := by
  exact_mod_cast p.2.ne_zero

theorem dilationWeight_zero (p : Nat.Primes) : dilationWeight p 0 = 1 := by
  simp [dilationWeight]

theorem dilationWeight_add (p : Nat.Primes) (m m' : PrimeExponents) :
    dilationWeight p (m + m') = dilationWeight p m * dilationWeight p m' := by
  simp only [dilationWeight, Finsupp.add_apply, neg_add]
  exact zpow_add₀ (primeCast_ne_zero p) _ _

/-- The prime dilation on exponent characters, `χ_m ↦ p^{-m_p}·χ_m`, as a
monoid homomorphism into the secular algebra. -/
def dilationChar (p : Nat.Primes) : Multiplicative PrimeExponents →* SecularAlgebra where
  toFun m := dilationWeight p m.toAdd • AddMonoidAlgebra.of ℂ PrimeExponents m
  map_one' := by
    simp [dilationWeight_zero]
  map_mul' x y := by
    rw [toAdd_mul, dilationWeight_add, map_mul, smul_mul_assoc, mul_smul_comm, smul_smul]

/-- The prime dilation as a `ℂ`-algebra endomorphism of the secular algebra. -/
def dilation (p : Nat.Primes) : SecularAlgebra →ₐ[ℂ] SecularAlgebra :=
  AddMonoidAlgebra.lift ℂ PrimeExponents SecularAlgebra (dilationChar p)

/-- The wild generator on the prime-`p` lane: the exponent character `x_p`. -/
def wildGenerator (p : Nat.Primes) : SecularAlgebra :=
  AddMonoidAlgebra.of ℂ PrimeExponents (Multiplicative.ofAdd (Finsupp.single p 1))

/-- The inverse character `x_p⁻¹`. -/
def wildGeneratorInv (p : Nat.Primes) : SecularAlgebra :=
  AddMonoidAlgebra.of ℂ PrimeExponents (Multiplicative.ofAdd (Finsupp.single p (-1)))

theorem wildGenerator_mul_inv (p : Nat.Primes) :
    wildGenerator p * wildGeneratorInv p = 1 := by
  rw [wildGenerator, wildGeneratorInv, ← map_mul]
  have h : (Multiplicative.ofAdd (Finsupp.single p (1 : ℤ))) *
      (Multiplicative.ofAdd (Finsupp.single p (-1 : ℤ))) = 1 := by
    rw [← ofAdd_add, ← Finsupp.single_add]
    simp
  rw [h, map_one]

/-- The wild generator is a `p⁻¹`-eigenvector of the prime dilation. -/
theorem dilation_wildGenerator (p : Nat.Primes) :
    dilation p (wildGenerator p) = (((p : ℕ) : ℂ))⁻¹ • wildGenerator p := by
  rw [dilation, wildGenerator, AddMonoidAlgebra.lift_of]
  simp [dilationChar, dilationWeight, wildGenerator, Finsupp.single_eq_same,
    zpow_neg, zpow_one]

/-- An equivariant splitting of the secular weld: a `ℂ`-algebra retraction onto
the scalar (tame) block — every `ℂ`-algebra map `𝒪 → ℂ` fixes the scalars, so
it is automatically a retraction of the tame inclusion — commuting with all
prime dilations. -/
def IsEquivariantRetraction (r : SecularAlgebra →ₐ[ℂ] ℂ) : Prop :=
  ∀ p : Nat.Primes, r.comp (dilation p) = r

/-- A retraction equivariant for a single prime dilation already annihilates
that prime's wild generator: the generator has weight `p⁻¹ ≠ 1`. -/
theorem retraction_kills_wildGenerator (r : SecularAlgebra →ₐ[ℂ] ℂ) {p : Nat.Primes}
    (h : r.comp (dilation p) = r) : r (wildGenerator p) = 0 := by
  have hp1 : (((p : ℕ) : ℂ))⁻¹ ≠ 1 := by
    rw [ne_eq, inv_eq_one]
    exact_mod_cast p.2.ne_one
  refine equivariant_linear_kills_scaled r.toLinearMap (dilation p) ?_
    (dilation_wildGenerator p) hp1
  intro x
  simpa using DFunLike.congr_fun h x

/-- **No prime dilation admits an equivariant retraction onto the scalars.**
The wild generator is a unit, and an equivariant retraction would send it to
`0`, while ring maps send units to units. -/
theorem no_equivariant_dilation_retraction (r : SecularAlgebra →ₐ[ℂ] ℂ) (p : Nat.Primes) :
    r.comp (dilation p) ≠ r := by
  intro h
  have h0 : r (wildGenerator p) = 0 := retraction_kills_wildGenerator r h
  have h1 : r (wildGenerator p) * r (wildGeneratorInv p) = 1 := by
    rw [← map_mul, wildGenerator_mul_inv p, map_one]
  rw [h0, zero_mul] at h1
  exact zero_ne_one h1

/-- **The secular weld is rigid**: the tame (scalar) block admits no
equivariant algebra retraction — the operational non-splitting of the
wild/tame extension on the secular coordinates. -/
theorem secularWeld_nonSplit :
    ¬ ∃ r : SecularAlgebra →ₐ[ℂ] ℂ, IsEquivariantRetraction r := by
  rintro ⟨r, hr⟩
  exact no_equivariant_dilation_retraction r ⟨2, Nat.prime_two⟩ (hr _)

end SecularWeld

namespace FormalWeightRing

open Polynomial

/-- The weight shift on the formal secular weight ring `ℚ[X]`: `X ↦ t·X`.  The
weight-`j` monomials are its `t^j`-eigenvectors; weight zero is the tame block. -/
def gradingShift (t : ℚ) : Polynomial ℚ →ₐ[ℚ] Polynomial ℚ :=
  aeval (C t * X)

/-- The weight-`j` monomial is a `t^j`-eigenvector of the weight shift. -/
theorem gradingShift_pow (t : ℚ) (j : ℕ) :
    gradingShift t (X ^ j) = t ^ j • (X ^ j : Polynomial ℚ) := by
  rw [gradingShift, map_pow, aeval_X, mul_pow, ← map_pow C t j, ← smul_eq_C_mul]

/-- **Equivariant functionals are blind to positive weight**: a linear
functional on the formal weight ring equivariant for the weight-two shift
kills every positive-weight monomial. -/
theorem equivariant_functional_kills_positive_weight
    (φ : Polynomial ℚ →ₗ[ℚ] ℚ) (hφ : ∀ f, φ (gradingShift 2 f) = φ f)
    {j : ℕ} (hj : j ≠ 0) : φ (X ^ j) = 0 := by
  refine equivariant_linear_kills_scaled φ (gradingShift 2) hφ (gradingShift_pow 2 j) ?_
  exact ne_of_gt (one_lt_pow₀ (by norm_num) hj)

/-- **The only equivariant extraction is the tame projection**: an equivariant
linear functional on the formal weight ring factors through the weight-zero
coefficient.  This is the formal non-splitting of the weight extension in
positive form. -/
theorem equivariant_functional_eq_constant_coeff
    (φ : Polynomial ℚ →ₗ[ℚ] ℚ) (hφ : ∀ f, φ (gradingShift 2 f) = φ f)
    (f : Polynomial ℚ) : φ f = f.coeff 0 * φ 1 := by
  have hmono : ∀ i : ℕ, φ (monomial i (f.coeff i)) = f.coeff i * φ (X ^ i) := by
    intro i
    rw [← smul_X_eq_monomial, map_smul, smul_eq_mul]
  conv_lhs => rw [f.as_sum_support]
  rw [map_sum, Finset.sum_eq_single 0]
  · rw [hmono 0, pow_zero]
  · intro i _ hi
    rw [hmono i, equivariant_functional_kills_positive_weight φ hφ hi, mul_zero]
  · intro h0
    rw [hmono 0, Polynomial.not_mem_support_iff.mp h0, zero_mul]

end FormalWeightRing

end

end GaloisForLFunctions
