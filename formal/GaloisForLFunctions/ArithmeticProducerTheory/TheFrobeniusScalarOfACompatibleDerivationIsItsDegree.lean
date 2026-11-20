import Mathlib

/-!
# The Frobenius scalar of a compatible derivation is its degree

Over `𝔽_q` the Frobenius kills differentials. On the auxiliaries `R[X_σ]` the Frobenius of degree
`a` is the Adams operation `ψ_a = expand a`. This module classifies every derivation `D` and scalar
`c` with `D ∘ ψ_a = c · ψ_a ∘ D`, for `a ≥ 2` regular in `R`.

* `eulerDerivation r = Σ rᵢ Xᵢ ∂ᵢ`: the torus-invariant derivations. They scale by the degree,
  `D ∘ ψ_a = a · ψ_a ∘ D` (`eulerDerivation_expand`).
* `isCompatible_iff`: `D ∘ ψ_a = c · ψ_a ∘ D` holds iff `D = Σ rᵢ Xᵢ ∂ᵢ` with `c rᵢ = a rᵢ` for
  every `i`.
* `IsCompatible.scalar_eq`: over a domain a nonzero compatible derivation has scalar exactly `a`.
  The scalar is an integer of the base, so it satisfies the product formula: a Frobenius that is
  inseparable to order `pᵏ` at `p` (`pᵏ ∣ a`) scales differentials by at least `pᵏ` at the real
  place.

The proof compares monomials in `a Xᵢᵃ⁻¹ · D Xᵢ = c · ψ_a(D Xᵢ)`: a monomial of degree `d` on the
left is matched with one of degree `d'` on the right, `d − 1 = a (d' − 1)`, so a monomial of degree
`≥ 2` would start an infinite descent, and degree `0` is unmatched.
-/

open MvPolynomial

namespace GaloisForLFunctions.ArithmeticProducerTheory

variable {σ R : Type*} [CommRing R]

/-- `D ∘ ψ_a = c · ψ_a ∘ D`: the derivation `D` is compatible with the Frobenius of degree `a`, with
scalar `c`. -/
def IsCompatible (a : ℕ) (c : R) (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) : Prop :=
  ∀ f, D (expand a f) = c • expand a (D f)

/-- The torus-invariant derivation `Σ rᵢ Xᵢ ∂ᵢ`. -/
noncomputable def eulerDerivation (r : σ → R) :
    Derivation R (MvPolynomial σ R) (MvPolynomial σ R) :=
  mkDerivation R fun i => C (r i) * X i

@[simp]
theorem eulerDerivation_X (r : σ → R) (i : σ) : eulerDerivation r (X i) = C (r i) * X i :=
  mkDerivation_X _ _ _

variable {a : ℕ} {c : R} {D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)}

/-- A derivation with `D Xᵢ = rᵢ Xᵢ` and `c rᵢ = a rᵢ` is compatible with scalar `c`. -/
theorem isCompatible_of_X {r : σ → R} (hD : ∀ i, D (X i) = C (r i) * X i)
    (hc : ∀ i, c * r i = a * r i) : IsCompatible a c D := by
  intro f
  induction f using MvPolynomial.induction_on with
  | C s => rw [expand_C, derivation_C, map_zero, smul_zero]
  | add f g hf hg => rw [map_add, map_add, hf, hg, map_add, map_add, smul_add]
  | mul_X f i hf =>
    have hX : D (X i ^ a) = C (c * r i) * X i ^ a := by
      rw [hc, Derivation.leibniz_pow, hD, smul_eq_mul, nsmul_eq_mul, C_mul, map_natCast]
      cases a with
      | zero => simp
      | succ n =>
        rw [Nat.add_sub_cancel, pow_succ]
        ring
    rw [map_mul, expand_X, Derivation.leibniz, hf, hX, Derivation.leibniz, hD]
    simp only [smul_eq_mul, map_add, map_mul, expand_C, expand_X, smul_eq_C_mul]
    ring

/-- Euler derivations scale by the degree of the Frobenius. -/
theorem eulerDerivation_expand (a : ℕ) (r : σ → R) : IsCompatible a (a : R) (eulerDerivation r) :=
  isCompatible_of_X (fun i => eulerDerivation_X r i) fun _ => rfl

/-- The compatibility identity at a coordinate: `a Xᵢᵃ⁻¹ · D Xᵢ = c · ψ_a(D Xᵢ)`. -/
theorem IsCompatible.at_X (h : IsCompatible a c D) (i : σ) :
    a • (X i ^ (a - 1) * D (X i)) = c • expand a (D (X i)) := by
  have := h (X i)
  rwa [expand_X, Derivation.leibniz_pow, smul_eq_mul] at this

/-- **Matching of monomials.** A monomial `m` of `D Xᵢ` has the form `a m' − (a − 1) eᵢ` for a
monomial `m'` of `D Xᵢ`, with `c · coeff m' = a · coeff m`. -/
theorem IsCompatible.exists_monomial (h : IsCompatible a c D) (ha : IsRegular (a : R))
    (ha0 : a ≠ 0) (i : σ) {m : σ →₀ ℕ} (hm : coeff m (D (X i)) ≠ 0) :
    ∃ m', Finsupp.single i (a - 1) + m = a • m' ∧ coeff m' (D (X i)) ≠ 0 ∧
      c * coeff m' (D (X i)) = a * coeff m (D (X i)) := by
  classical
  have hc := congrArg (coeff (Finsupp.single i (a - 1) + m)) (h.at_X i)
  rw [coeff_smul, X_pow_eq_monomial, coeff_monomial_mul, one_mul, coeff_smul, nsmul_eq_mul,
    smul_eq_mul] at hc
  have hne : coeff (Finsupp.single i (a - 1) + m) (expand a (D (X i))) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hc
    exact hm (ha.left (hc.trans (mul_zero _).symm))
  obtain ⟨m', hm', hEq⟩ :=
    Finset.mem_image.mp (support_expand_subset (D (X i)) (mem_support_iff.mpr hne))
  have hEq' : a • m' = Finsupp.single i (a - 1) + m := hEq
  refine ⟨m', hEq'.symm, mem_support_iff.mp hm', ?_⟩
  rw [← hEq', coeff_expand_smul a ha0] at hc
  exact hc.symm

/-- Every monomial of `D Xᵢ` has degree one: degrees `≥ 2` descend forever under the matching, and
degree `0` is unmatched. -/
theorem IsCompatible.degree_eq_one (h : IsCompatible a c D) (ha : IsRegular (a : R))
    (ha2 : 2 ≤ a) (i : σ) {m : σ →₀ ℕ} (hm : coeff m (D (X i)) ≠ 0) : m.degree = 1 := by
  have key : ∀ d (m : σ →₀ ℕ), m.degree = d → coeff m (D (X i)) ≠ 0 → d ≤ 1 := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro m hd hm
      by_contra hlt
      obtain ⟨m', hEq, hm', -⟩ := h.exists_monomial ha (by omega) i hm
      have hdeg := congrArg Finsupp.degree hEq
      rw [map_add, Finsupp.degree_single, map_nsmul, smul_eq_mul, hd] at hdeg
      have h2 : 2 ≤ m'.degree := by
        by_contra hlt'
        have := Nat.mul_le_mul_left a (show m'.degree ≤ 1 by omega)
        omega
      have h3 := Nat.mul_le_mul_left a h2
      have h4 := Nat.mul_le_mul_right m'.degree ha2
      exact absurd (ih m'.degree (by omega) m' rfl hm') (by omega)
  have h1 := key _ m rfl hm
  obtain ⟨m', hEq, -, -⟩ := h.exists_monomial ha (by omega) i hm
  have hdeg := congrArg Finsupp.degree hEq
  rw [map_add, Finsupp.degree_single, map_nsmul, smul_eq_mul] at hdeg
  by_contra hne
  have h0 : m.degree = 0 := by omega
  rw [h0] at hdeg
  rcases Nat.eq_zero_or_pos m'.degree with h' | h'
  · rw [h'] at hdeg
    omega
  · have := Nat.mul_le_mul_left a h'
    omega

/-- The only monomial of `D Xᵢ` is `Xᵢ`. -/
theorem IsCompatible.eq_single (h : IsCompatible a c D) (ha : IsRegular (a : R)) (ha2 : 2 ≤ a)
    (i : σ) {m : σ →₀ ℕ} (hm : coeff m (D (X i)) ≠ 0) : m = Finsupp.single i 1 := by
  classical
  have hd := h.degree_eq_one ha ha2 i hm
  obtain ⟨m', hEq, hm', -⟩ := h.exists_monomial ha (by omega) i hm
  have hd' := h.degree_eq_one ha ha2 i hm'
  -- the matched monomial has a positive coordinate, which must be `i`
  have hmi : 1 ≤ m i := by
    obtain ⟨k, hk⟩ : ∃ k, m' k ≠ 0 := by
      by_contra hall
      push Not at hall
      rw [Finsupp.ext (g := 0) hall, map_zero] at hd'
      exact zero_ne_one hd'
    have hk' := DFunLike.congr_fun hEq k
    rw [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply] at hk'
    have hge := Nat.mul_le_mul_left a (Nat.one_le_iff_ne_zero.mpr hk)
    by_cases hki : i = k
    · subst hki
      rw [if_pos rfl] at hk'
      omega
    · rw [if_neg hki] at hk'
      have := Finsupp.le_degree k m
      omega
  obtain ⟨m₀, rfl⟩ := exists_add_of_le (Finsupp.single_le_iff.mpr hmi)
  rw [map_add, Finsupp.degree_single] at hd
  rw [(Finsupp.degree_eq_zero_iff m₀).mp (by omega), add_zero]

/-- **Classification at a coordinate.** `D Xᵢ = rᵢ Xᵢ` with `c rᵢ = a rᵢ`. -/
theorem IsCompatible.apply_X (h : IsCompatible a c D) (ha : IsRegular (a : R)) (ha2 : 2 ≤ a)
    (i : σ) :
    D (X i) = C (coeff (Finsupp.single i 1) (D (X i))) * X i ∧
      c * coeff (Finsupp.single i 1) (D (X i)) = a * coeff (Finsupp.single i 1) (D (X i)) := by
  classical
  constructor
  · ext m
    rw [coeff_C_mul, coeff_X]
    by_cases hm : Finsupp.single i 1 = m
    · rw [if_pos hm, mul_one, hm]
    · rw [if_neg hm, mul_zero]
      by_contra hne
      exact hm (h.eq_single ha ha2 i hne).symm
  · by_cases hr : coeff (Finsupp.single i 1) (D (X i)) = 0
    · rw [hr, mul_zero, mul_zero]
    · obtain ⟨m', -, hm', hrel⟩ := h.exists_monomial ha (by omega) i hr
      rwa [h.eq_single ha ha2 i hm'] at hrel

/-- **Classification of compatible derivations.** For `a ≥ 2` regular in `R`,
`D ∘ ψ_a = c · ψ_a ∘ D` iff `D = Σ rᵢ Xᵢ ∂ᵢ` with `c rᵢ = a rᵢ` for every `i`. -/
theorem isCompatible_iff (ha : IsRegular (a : R)) (ha2 : 2 ≤ a) :
    IsCompatible a c D ↔ ∃ r : σ → R, D = eulerDerivation r ∧ ∀ i, c * r i = a * r i := by
  constructor
  · intro h
    refine ⟨fun i => coeff (Finsupp.single i 1) (D (X i)), ?_, fun i => (h.apply_X ha ha2 i).2⟩
    exact derivation_ext fun i => by
      rw [eulerDerivation_X]
      exact (h.apply_X ha ha2 i).1
  · rintro ⟨r, rfl, hc⟩
    exact isCompatible_of_X (fun i => eulerDerivation_X r i) hc

/-- **The scalar is the degree.** Over a domain in which `a ≥ 2` is nonzero, a nonzero derivation
compatible with `ψ_a` has scalar exactly `a`. -/
theorem IsCompatible.scalar_eq [IsDomain R] (h : IsCompatible a c D) (ha : (a : R) ≠ 0)
    (ha2 : 2 ≤ a) (hD : D ≠ 0) : c = a := by
  obtain ⟨r, rfl, hc⟩ := (isCompatible_iff (IsRegular.of_ne_zero ha) ha2).mp h
  by_contra hne
  refine hD (derivation_ext fun i => ?_)
  have h0 : (c - a) * r i = 0 := by rw [sub_mul, hc i, sub_self]
  rw [eulerDerivation_X, (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hne), map_zero,
    zero_mul]
  rfl

end GaloisForLFunctions.ArithmeticProducerTheory
