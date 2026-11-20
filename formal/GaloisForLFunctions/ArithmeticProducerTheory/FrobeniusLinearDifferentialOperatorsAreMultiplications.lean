import Mathlib

/-!
# Differential operators linear over the Frobenius image are multiplications

Stepanov's count over `𝔽_q` uses that differentiation is linear over the image of the Frobenius:
`∂(f · g^q) = ∂f · g^q`, so vanishing of an auxiliary `Σ f_i g_i^q` to high order is a condition on
the factors `f_i` alone. On the auxiliaries `R[X_σ]` the Frobenius of degree `a` is the Adams
operation `ψ_a = expand a`. This module decides, for differential operators of every finite order
at once, when that linearity is available.

* `HasOrderLE k P`: differential operators of order `≤ k`, by commutators with multiplications.
  Derivations have order `≤ 1` and orders add under composition, so every polynomial differential
  operator is covered (`hasOrderLE_derivation_iter`).
* `HasOrderLE.linear_of_expand_linear`: if `a` is regular in `R`, an operator of finite order that
  is linear over `ψ_a(R[X_σ])` is linear over `R[X_σ]`; it is multiplication by its value at `1`
  (`HasOrderLE.eq_mul_of_expand_linear`). No order of differentiation sees the Frobenius image as
  constants.
* `derivation_eq_zero_of_expand`: in particular a derivation killing the Frobenius image is zero.
* `pderiv_expand_linear_iff`: `∂_i` is linear over `ψ_a(R[X_σ])` exactly when `a = 0` in `R`.

The mechanism is the weighted Leibniz rule `[P, xⁿ] = n xⁿ⁻¹ [P, x]` for an operator whose
commutator with `x` is a multiplication (`commutator_pow`): linearity over `xᵃ` forces
`a · xᵃ⁻¹ · [P, x] = 0`.
-/

open MvPolynomial

namespace GaloisForLFunctions.ArithmeticProducerTheory

section Order

variable {A : Type*} [CommRing A]

/-- The commutator `[P, f] : g ↦ P (f g) − f P g` of an additive operator with a multiplication. -/
def commutator (P : A →+ A) (f : A) : A →+ A :=
  P.comp (AddMonoidHom.mulLeft f) - (AddMonoidHom.mulLeft f).comp P

@[simp]
theorem commutator_apply (P : A →+ A) (f g : A) : commutator P f g = P (f * g) - f * P g := rfl

/-- Differential operators of order `≤ k`: order `≤ 0` is `A`-linearity, and order `≤ k + 1` means
that every commutator with a multiplication has order `≤ k`. -/
def HasOrderLE : ℕ → (A →+ A) → Prop
  | 0, P => ∀ f g, P (f * g) = f * P g
  | k + 1, P => ∀ f, HasOrderLE k (commutator P f)

theorem hasOrderLE_zero {P : A →+ A} : HasOrderLE 0 P ↔ ∀ f g, P (f * g) = f * P g := Iff.rfl

theorem hasOrderLE_succ {k : ℕ} {P : A →+ A} :
    HasOrderLE (k + 1) P ↔ ∀ f, HasOrderLE k (commutator P f) := Iff.rfl

theorem commutator_add (P Q : A →+ A) (f : A) :
    commutator (P + Q) f = commutator P f + commutator Q f := by
  ext g
  simp only [commutator_apply, AddMonoidHom.add_apply]
  ring

/-- `[P ∘ Q, f] = P ∘ [Q, f] + [P, f] ∘ Q`. -/
theorem commutator_comp (P Q : A →+ A) (f : A) :
    commutator (P.comp Q) f = P.comp (commutator Q f) + (commutator P f).comp Q := by
  ext g
  simp only [commutator_apply, AddMonoidHom.comp_apply, AddMonoidHom.add_apply, map_sub]
  ring

theorem HasOrderLE.add {k : ℕ} {P Q : A →+ A} (hP : HasOrderLE k P) (hQ : HasOrderLE k Q) :
    HasOrderLE k (P + Q) := by
  induction k generalizing P Q with
  | zero =>
    intro f g
    rw [AddMonoidHom.add_apply, AddMonoidHom.add_apply, hP f g, hQ f g, mul_add]
  | succ k ih =>
    intro f
    rw [commutator_add]
    exact ih (hP f) (hQ f)

theorem HasOrderLE.succ {k : ℕ} {P : A →+ A} (hP : HasOrderLE k P) : HasOrderLE (k + 1) P := by
  induction k generalizing P with
  | zero =>
    intro f g h
    simp only [commutator_apply]
    rw [hP g, ← mul_assoc, mul_comm f g, mul_assoc, hP g, hP f]
    ring
  | succ k ih => exact fun f => ih (hP f)

theorem HasOrderLE.mono {k l : ℕ} {P : A →+ A} (hP : HasOrderLE k P) (hkl : k ≤ l) :
    HasOrderLE l P := by
  induction hkl with
  | refl => exact hP
  | step _ ih => exact ih.succ

/-- A derivation has order `≤ 1`: its commutator with `f` is multiplication by `D f`. -/
theorem hasOrderLE_one_of_leibniz {D : A →+ A} (hD : ∀ f g, D (f * g) = f * D g + g * D f) :
    HasOrderLE 1 D := by
  intro f g h
  simp only [commutator_apply]
  rw [hD f (g * h), hD f h]
  ring

/-- Orders add under composition. -/
theorem HasOrderLE.comp {k l : ℕ} {P Q : A →+ A} (hP : HasOrderLE k P) (hQ : HasOrderLE l Q) :
    HasOrderLE (k + l) (P.comp Q) := by
  induction hn : k + l using Nat.strong_induction_on generalizing k l P Q with
  | _ n ih =>
    subst hn
    rcases Nat.eq_zero_or_pos (k + l) with h0 | hpos
    · obtain ⟨rfl, rfl⟩ : k = 0 ∧ l = 0 := by omega
      intro f g
      rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, hQ f g, hP f]
    · obtain ⟨n, hn⟩ : ∃ n, k + l = n + 1 := ⟨k + l - 1, by omega⟩
      rw [hn]
      intro f
      rw [commutator_comp]
      refine HasOrderLE.add ?_ ?_
      · -- `P ∘ [Q, f]`: the second factor loses one order, unless it is already linear
        cases l with
        | zero =>
          have h0 : commutator Q f = 0 := by
            ext g
            simp only [commutator_apply, AddMonoidHom.zero_apply, hQ f g, sub_self]
          rw [h0, AddMonoidHom.comp_zero]
          exact (show HasOrderLE 0 (0 : A →+ A) from fun _ _ => by simp).mono (Nat.zero_le _)
        | succ l =>
          have := ih (k + l) (by omega) hP (hQ f) rfl
          exact this.mono (by omega)
      · cases k with
        | zero =>
          have h0 : commutator P f = 0 := by
            ext g
            simp only [commutator_apply, AddMonoidHom.zero_apply, hP f g, sub_self]
          rw [h0, AddMonoidHom.zero_comp]
          exact (show HasOrderLE 0 (0 : A →+ A) from fun _ _ => by simp).mono (Nat.zero_le _)
        | succ k =>
          have := ih (k + l) (by omega) (hP f) hQ rfl
          exact this.mono (by omega)

/-- **Weighted Leibniz rule.** If `[P, x]` is multiplication by `q`, then `[P, xⁿ]` is
multiplication by `n xⁿ⁻¹ q`. -/
theorem commutator_pow {P : A →+ A} {x q : A} (h : ∀ g, P (x * g) = x * P g + q * g) (n : ℕ)
    (g : A) : P (x ^ n * g) = x ^ n * P g + n • (x ^ (n - 1) * q * g) := by
  induction n generalizing g with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_assoc, ih, h]
    cases n with
    | zero => simp
    | succ n =>
      simp only [Nat.add_sub_cancel, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      ring

/-- The `k`-fold composition `Dᵏ`. -/
def iter (D : A →+ A) : ℕ → (A →+ A)
  | 0 => AddMonoidHom.id A
  | k + 1 => (iter D k).comp D

/-- Iterating an operator of order `≤ 1` `k` times gives order `≤ k`. -/
theorem HasOrderLE.iter {D : A →+ A} (hD : HasOrderLE 1 D) (k : ℕ) : HasOrderLE k (iter D k) := by
  induction k with
  | zero => exact fun f g => rfl
  | succ k ih => exact ih.comp hD

/-- Every power `Dᵏ` of a derivation is a differential operator of order `≤ k`. -/
theorem hasOrderLE_derivation_iter {S : Type*} [CommRing S] [Algebra S A] (D : Derivation S A A)
    (k : ℕ) : HasOrderLE k (iter D.toLinearMap.toAddMonoidHom k) :=
  HasOrderLE.iter (hasOrderLE_one_of_leibniz fun f g => by
    change D (f * g) = f * D g + g * D f
    rw [D.leibniz, smul_eq_mul, smul_eq_mul]) k

end Order

variable {σ R : Type*} [CommRing R]

/-- `a · X_iⁿ` is not a zero divisor of `R[X_σ]` when `a` is regular in `R`. -/
theorem eq_zero_of_nsmul_X_pow_mul {a : ℕ} (ha : IsRegular (a : R)) (i : σ) (n : ℕ)
    {q : MvPolynomial σ R} (h : a • (X i ^ n * q) = 0) : q = 0 := by
  ext m
  have hm := congrArg (coeff (Finsupp.single i n + m)) h
  rw [coeff_smul, X_pow_eq_monomial, coeff_monomial_mul, one_mul, coeff_zero, nsmul_eq_mul] at hm
  exact ha.left (hm.trans (mul_zero _).symm)

/-- **No differential operator is linear over the Frobenius image.** Let `a` be regular in `R`. An
operator of finite order on `R[X_σ]` that is linear over the image of `ψ_a` is linear over
`R[X_σ]`. Induction on the order: the commutator with a coordinate `X_i` is a multiplication by the
inductive hypothesis, and the weighted Leibniz rule at `X_iᵃ = ψ_a(X_i)` kills it. -/
theorem HasOrderLE.linear_of_expand_linear {a : ℕ} (ha : IsRegular (a : R)) :
    ∀ {k : ℕ} {P : MvPolynomial σ R →+ MvPolynomial σ R}, HasOrderLE k P →
      (∀ g f, P (expand a g * f) = expand a g * P f) → ∀ f g, P (f * g) = f * P g := by
  intro k
  induction k with
  | zero => exact fun hP _ => hP
  | succ k ih =>
    intro P hP hlin
    -- the commutator with a coordinate is multiplication by `P X_i − X_i P 1`
    have hq : ∀ i g, P (X i * g) = X i * P g + (P (X i) - X i * P 1) * g := by
      intro i g
      have hQ := ih (hP (X i)) (fun g f => by
        simp only [commutator_apply]
        rw [mul_left_comm, hlin, hlin]
        ring)
      have h1 := hQ g 1
      simp only [commutator_apply, mul_one] at h1
      linear_combination h1
    -- linearity over `X_iᵃ` kills it
    have hX : ∀ i g, P (X i * g) = X i * P g := by
      intro i g
      have h1 := commutator_pow (hq i) a 1
      have h2 := hlin (X i) 1
      rw [expand_X] at h2
      have h3 : a • (X i ^ (a - 1) * (P (X i) - X i * P 1)) = 0 := by
        rw [h2] at h1
        linear_combination -h1
      rw [hq, eq_zero_of_nsmul_X_pow_mul ha i (a - 1) h3, zero_mul, add_zero]
    intro f
    induction f using MvPolynomial.induction_on with
    | C r =>
      intro g
      have := hlin (C r) g
      rwa [expand_C] at this
    | add f₁ f₂ h₁ h₂ =>
      intro g
      rw [add_mul, map_add, h₁, h₂, add_mul]
    | mul_X f i hf =>
      intro g
      rw [mul_assoc, hf, hX, mul_assoc]

/-- A differential operator of finite order that is linear over `ψ_a(R[X_σ])`, with `a` regular in
`R`, is multiplication by its value at `1`. -/
theorem HasOrderLE.eq_mul_of_expand_linear {a : ℕ} (ha : IsRegular (a : R)) {k : ℕ}
    {P : MvPolynomial σ R →+ MvPolynomial σ R} (hP : HasOrderLE k P)
    (hlin : ∀ g f, P (expand a g * f) = expand a g * P f) (f : MvPolynomial σ R) :
    P f = f * P 1 := by
  have := hP.linear_of_expand_linear ha hlin f 1
  rwa [mul_one] at this

/-- A derivation that kills the image of `ψ_a`, with `a` regular in `R`, is zero. -/
theorem derivation_eq_zero_of_expand {a : ℕ} (ha : IsRegular (a : R))
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) (h : ∀ g, D (expand a g) = 0) :
    D = 0 := by
  have hlin : ∀ g f, D.toLinearMap.toAddMonoidHom (expand a g * f) =
      expand a g * D.toLinearMap.toAddMonoidHom f := fun g f => by
    change D (expand a g * f) = expand a g * D f
    rw [D.leibniz, h, smul_zero, add_zero, smul_eq_mul]
  refine Derivation.ext fun f => ?_
  have := (hasOrderLE_derivation_iter D 1).eq_mul_of_expand_linear ha hlin f
  change D f = f * D 1 at this
  rw [this, D.map_one_eq_zero, mul_zero]
  rfl

/-- In characteristic dividing `a` the derivative of every Frobenius pullback vanishes. -/
theorem pderiv_expand_eq_zero {a : ℕ} (ha : (a : R) = 0) (i : σ) (g : MvPolynomial σ R) :
    pderiv i (expand a g) = 0 := by
  induction g using MvPolynomial.induction_on with
  | C r => rw [expand_C, pderiv_C]
  | add g₁ g₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, add_zero]
  | mul_X g j hg =>
    have hC : (a : MvPolynomial σ R) = 0 := by rw [← map_natCast C, ha, map_zero]
    rw [map_mul, expand_X, pderiv_mul, hg, pderiv_pow, hC]
    ring

/-- **The dichotomy.** `∂_i` is linear over the image of `ψ_a` exactly when `a = 0` in `R`: free
multiplicity is the vanishing of the degree of the Frobenius in the ring of coefficients. -/
theorem pderiv_expand_linear_iff (a : ℕ) (i : σ) :
    (∀ g f : MvPolynomial σ R, pderiv i (expand a g * f) = expand a g * pderiv i f) ↔
      (a : R) = 0 := by
  constructor
  · intro h
    have h1 := h (X i) 1
    rw [expand_X, mul_one, pderiv_one, mul_zero, pderiv_pow, pderiv_X_self, mul_one,
      ← map_natCast C, X_pow_eq_monomial, C_mul_monomial, mul_one] at h1
    exact monomial_eq_zero.mp h1
  · intro ha g f
    rw [pderiv_mul, pderiv_expand_eq_zero ha, zero_mul, zero_add]

end GaloisForLFunctions.ArithmeticProducerTheory
