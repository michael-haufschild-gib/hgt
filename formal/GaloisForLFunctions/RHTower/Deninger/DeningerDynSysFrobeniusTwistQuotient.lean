import Mathlib.Algebra.Group.End
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring
import Mathlib.FieldTheory.Finite.Basic

/-!
# The Frobenius-twist quotient

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Lemma 5.3 (`t5`).

For a point `x` of the normalization `X` of an arithmetic scheme, a lift `σ` of a Frobenius
automorphism and coprime `ν ≠ ν'`, the subgroup

`H = {y ^ ν · σ (y) ^ (-ν') | y ∈ κ (x)ˣ}`

has the property that every class of `κ (x)ˣ / H` is represented by a root of unity of order
dividing `ν ^ i - ν' ^ i` for some `i ≥ 1`; in particular `κ (x)ˣ / H` is a torsion group of
exponent prime to `ν ν'`.

The proof is carried out for an arbitrary divisible commutative group `A` with an automorphism all
of whose orbits are finite, which is exactly the structure `κ (x)ˣ` carries.  The mechanism is
Deninger's identity `ν ^ i - ν' ^ i σ ^ i = ω · (ν - ν' σ)` in the group ring `ℤ⟨σ⟩` with
`ω = ∑_{α < i} ν ^ (i - 1 - α) ν' ^ α σ ^ α`; here it appears as the telescoping product
`deningerTwistHom_telescope`.

The two arithmetic facts describing the exponents `ν ^ i - ν' ^ i` — that their prime divisors
avoid `ν ν'`, and that every modulus prime to `ν ν'` divides one of them (take `i = φ (N)`) — are
`deningerPrime_not_dvd_of_dvd_pow_sub` and `deningerExists_pow_sub_dvd`.
-/

namespace RHTower

open Finset

variable {A : Type*} [CommGroup A]

/-- The twist endomorphism `y ↦ y ^ ν · σ (y) ^ (-ν')` of a commutative group. -/
private def deningerTwistHom (σ : MulAut A) (ν ν' : ℕ) : A →* A where
  toFun y := y ^ ν * ((σ y) ^ ν')⁻¹
  map_one' := by simp
  map_mul' a b := by
    rw [map_mul, mul_pow, mul_pow, mul_inv, mul_mul_mul_comm]

@[simp] theorem deningerTwistHom_apply_deningerDynSysFrobeniusTwistQuotient (σ : MulAut A) (ν ν' : ℕ) (y : A) :
    deningerTwistHom σ ν ν' y = y ^ ν * ((σ y) ^ ν')⁻¹ := rfl

section Telescope

variable (σ : MulAut A) {ν ν' : ℕ}

/-- The telescoping identity behind Deninger's group-ring computation `ν^i - ν'^i σ^i =
ω · (ν - ν' σ)`: the element `y = ∏_{α < i} σ^α (z) ^ (ν^{i-1-α} ν'^α)` satisfies
`y^ν σ(y)^{-ν'} = z^{ν^i} σ^i(z)^{-ν'^i}`. -/
theorem deningerTwistHom_telescope (z : A) (i : ℕ) :
    deningerTwistHom σ ν ν'
        (∏ α ∈ Finset.range i, ((σ ^ α) z) ^ (ν ^ (i - 1 - α) * ν' ^ α))
      = z ^ ν ^ i * (((σ ^ i) z) ^ ν' ^ i)⁻¹ := by
  classical
  set g : ℕ → A := fun α => ((σ ^ α) z) ^ (ν ^ (i - α) * ν' ^ α) with hgdef
  have hgval : ∀ α, g α = ((σ ^ α) z) ^ (ν ^ (i - α) * ν' ^ α) := fun _ => rfl
  have hy : (∏ α ∈ Finset.range i, ((σ ^ α) z) ^ (ν ^ (i - 1 - α) * ν' ^ α)) ^ ν
      = ∏ α ∈ Finset.range i, g α := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun α hα => ?_
    have hαi : α < i := Finset.mem_range.mp hα
    rw [← pow_mul, hgval]
    congr 1
    have h1 : ν ^ (i - 1 - α) * ν' ^ α * ν = ν ^ (i - 1 - α) * ν * ν' ^ α := by ring
    rw [h1, ← pow_succ]
    congr 2
    omega
  have hσy : (σ (∏ α ∈ Finset.range i, ((σ ^ α) z) ^ (ν ^ (i - 1 - α) * ν' ^ α))) ^ ν'
      = ∏ α ∈ Finset.range i, g (α + 1) := by
    rw [map_prod, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun α hα => ?_
    have hαi : α < i := Finset.mem_range.mp hα
    have hcomp : σ ((σ ^ α) z) = (σ ^ (α + 1)) z := by
      rw [pow_succ']
      rfl
    rw [map_pow, ← pow_mul, hcomp, hgval]
    congr 1
    have h2 : i - (α + 1) = i - 1 - α := by omega
    rw [h2]
    ring
  have htel : ∏ α ∈ Finset.range i, (g (α + 1) / g α) = g i / g 0 :=
    Finset.prod_range_div g i
  have hsplit : ∏ α ∈ Finset.range i, (g (α + 1) / g α)
      = (∏ α ∈ Finset.range i, g (α + 1)) / ∏ α ∈ Finset.range i, g α :=
    by rw [Finset.prod_div_distrib]
  rw [hsplit] at htel
  have htel' : (∏ α ∈ Finset.range i, g α) / (∏ α ∈ Finset.range i, g (α + 1)) = g 0 / g i := by
    rw [← inv_div, htel, inv_div]
  have hg0 : g 0 = z ^ ν ^ i := by rw [hgval]; simp
  have hgi : g i = ((σ ^ i) z) ^ ν' ^ i := by rw [hgval]; simp
  rw [deningerTwistHom_apply_deningerDynSysFrobeniusTwistQuotient, hy, hσy, ← hg0, ← hgi, ← div_eq_mul_inv, ← div_eq_mul_inv]
  exact htel'

end Telescope

section Surjectivity

variable (σ : MulAut A) {ν ν' : ℕ}

/-- **Deninger, Lemma 5.3 (`t5`).**  Let `σ` be an automorphism of a divisible commutative group
`A` all of whose orbits are finite, and let `ν ≠ ν'` be positive integers.  Then every class of `A`
modulo the twist subgroup `H = {y^ν σ(y)^{-ν'}}` is represented by an element `ζ` with
`ζ ^ (ν^i - ν'^i) = 1` for some `i ≥ 1`. -/
theorem deningerTwistHom_exists_rootOfUnity_repr
    (horb : ∀ c : A, ∃ i : ℕ, 0 < i ∧ (σ ^ i) c = c)
    (hdiv : ∀ (c : A) (n : ℤ), n ≠ 0 → ∃ z : A, z ^ n = c)
    (hne : ν ≠ ν') (c : A) :
    ∃ i : ℕ, 0 < i ∧ ∃ ζ : A,
      ζ ^ ((ν : ℤ) ^ i - (ν' : ℤ) ^ i) = 1 ∧
      c * ζ⁻¹ ∈ MonoidHom.range (deningerTwistHom σ ν ν') := by
  obtain ⟨i, hi, hfix⟩ := horb c
  set d : ℤ := (ν : ℤ) ^ i - (ν' : ℤ) ^ i with hd
  have hdne : d ≠ 0 := by
    rw [hd, sub_ne_zero]
    intro hc
    have hnat : ν ^ i = ν' ^ i := by exact_mod_cast hc
    exact hne (Nat.pow_left_injective hi.ne' hnat)
  obtain ⟨z, hz⟩ := hdiv c d hdne
  set η : A := (σ ^ i) z * z⁻¹ with hη
  have hzd : ((σ ^ i) z) ^ d = z ^ d := by
    rw [← map_zpow, hz, hfix]
  have hηd : η ^ d = 1 := by
    rw [hη, mul_zpow, inv_zpow, hzd, mul_inv_cancel]
  have hσiz : (σ ^ i) z = η * z := by
    rw [hη, inv_mul_cancel_right]
  refine ⟨i, hi, η ^ (ν' ^ i), ?_, ?_⟩
  · rw [← zpow_natCast η (ν' ^ i), ← zpow_mul, mul_comm, zpow_mul, hηd, one_zpow]
  · refine ⟨∏ α ∈ Finset.range i, ((σ ^ α) z) ^ (ν ^ (i - 1 - α) * ν' ^ α), ?_⟩
    rw [deningerTwistHom_telescope σ z i, hσiz, mul_pow, mul_inv, ← hz]
    have hsplit : z ^ d = z ^ ((ν : ℤ) ^ i) * (z ^ ((ν' : ℤ) ^ i))⁻¹ := by
      rw [hd, zpow_sub]
    rw [hsplit]
    have e1 : z ^ ((ν : ℤ) ^ i) = z ^ (ν ^ i) := by
      rw [← zpow_natCast z (ν ^ i)]
      norm_cast
    have e2 : z ^ ((ν' : ℤ) ^ i) = z ^ (ν' ^ i) := by
      rw [← zpow_natCast z (ν' ^ i)]
      norm_cast
    rw [e1, e2]
    simp [mul_comm, mul_assoc]

/-- **Deninger, Lemma 5.3, torsion form.**  Every element of `A` has a power `c ^ (ν^i - ν'^i)`
inside the twist subgroup. -/
theorem deningerTwistHom_zpow_mem
    (horb : ∀ c : A, ∃ i : ℕ, 0 < i ∧ (σ ^ i) c = c)
    (hdiv : ∀ (c : A) (n : ℤ), n ≠ 0 → ∃ z : A, z ^ n = c)
    (hne : ν ≠ ν') (c : A) :
    ∃ i : ℕ, 0 < i ∧ c ^ ((ν : ℤ) ^ i - (ν' : ℤ) ^ i) ∈
      MonoidHom.range (deningerTwistHom σ ν ν') := by
  obtain ⟨i, hi, ζ, hζ, y, hy⟩ :=
    deningerTwistHom_exists_rootOfUnity_repr σ horb hdiv hne c
  refine ⟨i, hi, y ^ ((ν : ℤ) ^ i - (ν' : ℤ) ^ i), ?_⟩
  rw [map_zpow, hy, mul_zpow, inv_zpow, hζ, inv_one, mul_one]

end Surjectivity

/-! ## The exponents `ν^i - ν'^i` for coprime `ν, ν'` -/

/-- Any prime dividing `ν^i - ν'^i` for coprime `ν, ν'` is prime to `ν ν'`. -/
theorem deningerPrime_not_dvd_of_dvd_pow_sub {ν ν' i l : ℕ} (hl : l.Prime)
    (hcop : Nat.Coprime ν ν') (hdvd : (l : ℤ) ∣ (ν : ℤ) ^ i - (ν' : ℤ) ^ i) (hi : 0 < i) :
    ¬ l ∣ ν * ν' := by
  intro hmul
  have key : l ∣ ν ∧ l ∣ ν' := by
    rcases (Nat.Prime.dvd_mul hl).mp hmul with h | h
    · refine ⟨h, ?_⟩
      have h1 : (l : ℤ) ∣ (ν : ℤ) ^ i := dvd_pow (Int.natCast_dvd_natCast.mpr h) hi.ne'
      have h2 : (l : ℤ) ∣ (ν' : ℤ) ^ i := by
        have := dvd_sub h1 hdvd
        simpa using this
      have h3 : l ∣ ν' ^ i := by exact_mod_cast h2
      exact hl.dvd_of_dvd_pow h3
    · refine ⟨?_, h⟩
      have h1 : (l : ℤ) ∣ (ν' : ℤ) ^ i := dvd_pow (Int.natCast_dvd_natCast.mpr h) hi.ne'
      have h2 : (l : ℤ) ∣ (ν : ℤ) ^ i := by
        have := dvd_add hdvd h1
        simpa using this
      have h3 : l ∣ ν ^ i := by exact_mod_cast h2
      exact hl.dvd_of_dvd_pow h3
  have hd1 : l ∣ Nat.gcd ν ν' := Nat.dvd_gcd key.1 key.2
  rw [Nat.Coprime] at hcop
  rw [hcop] at hd1
  exact hl.ne_one (Nat.dvd_one.mp hd1)

/-- Conversely, a root of unity whose order is prime to `ν ν'` is an `(ν^i - ν'^i)`-th root of
unity for a suitable `i ≥ 1`: take `i = φ (N)`. -/
theorem deningerExists_pow_sub_dvd {ν ν' N : ℕ} (hN : 0 < N)
    (hνN : Nat.Coprime ν N) (hν'N : Nat.Coprime ν' N) :
    ∃ i : ℕ, 0 < i ∧ (N : ℤ) ∣ (ν : ℤ) ^ i - (ν' : ℤ) ^ i := by
  refine ⟨Nat.totient N, Nat.totient_pos.mpr hN, ?_⟩
  have h1 : ν ^ Nat.totient N ≡ 1 [MOD N] := Nat.ModEq.pow_totient hνN
  have h2 : ν' ^ Nat.totient N ≡ 1 [MOD N] := Nat.ModEq.pow_totient hν'N
  have : ν ^ Nat.totient N ≡ ν' ^ Nat.totient N [MOD N] := h1.trans h2.symm
  have hint := (Nat.modEq_iff_dvd (n := N)).mp this
  have hneg := (dvd_neg (α := ℤ)).mpr hint
  push_cast at hneg
  simpa [neg_sub] using hneg

end RHTower
