import GaloisForLFunctions.HTGeometry.ReparametrizationAutomorphism
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Descent of the generic reparametrisation along base automorphisms

An element of the generic reparametrisation invariant under a family of base automorphisms is a
ratio of two jet polynomials whose coefficients are themselves invariant.

The mechanism is the minimal-denominator argument: present the element as `p / q` with `q` of the
fewest monomials, normalised at one of them; for an invariance `e`, the twisted difference
`q - e·q` is again a denominator and has lost that monomial, so minimality forces it to vanish.
The numerator is then invariant because it is the product of the invariant denominator with the
invariant element.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

namespace ReparamField

universe u

variable {K : Type u} [Field K] [Differential K]

@[simp] theorem coeff_polyEquiv (e : K ≃+* K) (m : ℕ →₀ ℕ) (q : ReparamPoly K) :
    MvPolynomial.coeff m (polyEquiv e q) = e (MvPolynomial.coeff m q) := by
  show MvPolynomial.coeff m (MvPolynomial.map (e : K →+* K) q) = e (MvPolynomial.coeff m q)
  rw [MvPolynomial.coeff_map]
  rfl

theorem support_polyEquiv (e : K ≃+* K) (q : ReparamPoly K) :
    (polyEquiv e q).support = q.support := by
  ext m
  simp only [MvPolynomial.mem_support_iff, coeff_polyEquiv, Ne]
  constructor
  · intro h hcon
    exact h (by rw [hcon, map_zero])
  · intro h hcon
    exact h ((EmbeddingLike.map_eq_zero_iff (f := e)).mp hcon)

/-- The denominators of an element of the reparametrisation field. -/
def IsJetDenom (x : ReparamField K) (q : ReparamPoly K) : Prop :=
  ∃ p : ReparamPoly K, algebraMap (ReparamPoly K) (ReparamField K) q * x
    = algebraMap (ReparamPoly K) (ReparamField K) p

theorem exists_nonzero_isJetDenom (x : ReparamField K) :
    ∃ q : ReparamPoly K, q ≠ 0 ∧ IsJetDenom x q := by
  obtain ⟨⟨p, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors (ReparamPoly K)) x
  refine ⟨s.1, ?_, p, ?_⟩
  · exact nonZeroDivisors.ne_zero s.2
  · rw [mul_comm]
    exact hs

theorem isJetDenom_sub {x : ReparamField K} {q₁ q₂ : ReparamPoly K}
    (h₁ : IsJetDenom x q₁) (h₂ : IsJetDenom x q₂) : IsJetDenom x (q₁ - q₂) := by
  obtain ⟨p₁, hp₁⟩ := h₁
  obtain ⟨p₂, hp₂⟩ := h₂
  refine ⟨p₁ - p₂, ?_⟩
  rw [map_sub, map_sub, sub_mul, hp₁, hp₂]

theorem isJetDenom_smul {x : ReparamField K} {q : ReparamPoly K} (h : IsJetDenom x q) (a : K) :
    IsJetDenom x (MvPolynomial.C a * q) := by
  obtain ⟨p, hp⟩ := h
  refine ⟨MvPolynomial.C a * p, ?_⟩
  rw [map_mul, map_mul, mul_assoc, hp]

theorem isJetDenom_polyEquiv {x : ReparamField K} {q : ReparamPoly K} (h : IsJetDenom x q)
    {e : K ≃+* K} (hx : fieldEquiv e x = x) : IsJetDenom x (polyEquiv e q) := by
  obtain ⟨p, hp⟩ := h
  refine ⟨polyEquiv e p, ?_⟩
  have := congrArg (fieldEquiv e) hp
  rw [map_mul, fieldEquiv_algebraMap, fieldEquiv_algebraMap, hx] at this
  exact this

/-- **Descent along base automorphisms.**  An element invariant under a family of base
automorphisms is a ratio of jet polynomials whose coefficients are invariant. -/
theorem exists_invariant_representation (G : Set (K ≃+* K)) (x : ReparamField K)
    (hx : ∀ e ∈ G, fieldEquiv e x = x) :
    ∃ p q : ReparamPoly K, q ≠ 0 ∧ (∀ e ∈ G, polyEquiv e q = q) ∧
      (∀ e ∈ G, polyEquiv e p = p) ∧
      algebraMap (ReparamPoly K) (ReparamField K) q * x
        = algebraMap (ReparamPoly K) (ReparamField K) p := by
  classical
  have hne : ∃ n : ℕ, ∃ q : ReparamPoly K, q ≠ 0 ∧ IsJetDenom x q ∧ q.support.card = n := by
    obtain ⟨q, hq0, hq⟩ := exists_nonzero_isJetDenom x
    exact ⟨q.support.card, q, hq0, hq, rfl⟩
  obtain ⟨q₀, hq₀0, hq₀, hcard⟩ := Nat.find_spec hne
  set N := Nat.find hne with hN
  have hmin : ∀ q : ReparamPoly K, q ≠ 0 → IsJetDenom x q → N ≤ q.support.card := by
    intro q hq0 hq
    exact Nat.find_le ⟨q, hq0, hq, rfl⟩
  obtain ⟨m₀, hm₀⟩ : q₀.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    exact hq₀0 (MvPolynomial.support_eq_empty.mp h)
  have hc0 : MvPolynomial.coeff m₀ q₀ ≠ 0 := MvPolynomial.mem_support_iff.mp hm₀
  set q : ReparamPoly K := MvPolynomial.C (MvPolynomial.coeff m₀ q₀)⁻¹ * q₀ with hqdef
  have hqdenom : IsJetDenom x q := isJetDenom_smul hq₀ _
  have hqcoeff : ∀ m, MvPolynomial.coeff m q
      = (MvPolynomial.coeff m₀ q₀)⁻¹ * MvPolynomial.coeff m q₀ := by
    intro m
    rw [hqdef, MvPolynomial.coeff_C_mul]
  have hqsupp : q.support = q₀.support := by
    ext m
    simp only [MvPolynomial.mem_support_iff, hqcoeff, Ne, mul_eq_zero, not_or]
    constructor
    · intro h
      exact h.2
    · intro h
      exact ⟨inv_ne_zero hc0, h⟩
  have hq0 : q ≠ 0 := by
    intro h
    rw [h] at hqsupp
    simp only [MvPolynomial.support_zero] at hqsupp
    exact absurd (hqsupp ▸ hm₀) (by simp)
  have hqm₀ : MvPolynomial.coeff m₀ q = 1 := by
    rw [hqcoeff, inv_mul_cancel₀ hc0]
  have hqfix : ∀ e ∈ G, polyEquiv e q = q := by
    intro e he
    by_contra hne'
    have hsub : IsJetDenom x (q - polyEquiv e q) :=
      isJetDenom_sub hqdenom (isJetDenom_polyEquiv hqdenom (hx e he))
    have hsub0 : q - polyEquiv e q ≠ 0 := sub_ne_zero_of_ne fun h => hne' h.symm
    have hcardlt : (q - polyEquiv e q).support.card < N := by
      have hsubset : (q - polyEquiv e q).support ⊆ q.support.erase m₀ := by
        intro m hm
        rw [Finset.mem_erase]
        rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub, coeff_polyEquiv] at hm
        constructor
        · intro hcon
          subst hcon
          rw [hqm₀, map_one, sub_self] at hm
          exact hm rfl
        · rw [MvPolynomial.mem_support_iff]
          intro hcon
          rw [hcon, map_zero, sub_zero] at hm
          exact hm rfl
      have h1 := Finset.card_le_card hsubset
      have h2 : (q.support.erase m₀).card < q.support.card :=
        Finset.card_erase_lt_of_mem (hqsupp ▸ hm₀)
      have h3 : q.support.card = N := by rw [hqsupp, hcard]
      omega
    exact absurd (hmin _ hsub0 hsub) (not_le.mpr hcardlt)
  obtain ⟨p, hp⟩ := hqdenom
  refine ⟨p, q, hq0, hqfix, ?_, hp⟩
  intro e he
  have hinj : Function.Injective (algebraMap (ReparamPoly K) (ReparamField K)) :=
    IsFractionRing.injective (ReparamPoly K) (ReparamField K)
  refine hinj ?_
  have hEq := congrArg (fieldEquiv e) hp
  rw [map_mul, fieldEquiv_algebraMap, fieldEquiv_algebraMap, hx e he, hqfix e he, hp] at hEq
  exact hEq.symm

/-- **Descent to a subfield of coefficients.**  If the invariants of the acting family in the base
lie in a subfield, then an invariant element of the reparametrisation is a ratio of jet polynomials
with coefficients in that subfield. -/
theorem exists_representation_coeff_mem (G : Set (K ≃+* K)) (S : Subfield K)
    (hS : ∀ a : K, (∀ e ∈ G, e a = a) → a ∈ S) (x : ReparamField K)
    (hx : ∀ e ∈ G, fieldEquiv e x = x) :
    ∃ p q : ReparamPoly K, q ≠ 0 ∧ (∀ m, MvPolynomial.coeff m p ∈ S) ∧
      (∀ m, MvPolynomial.coeff m q ∈ S) ∧
      algebraMap (ReparamPoly K) (ReparamField K) q * x
        = algebraMap (ReparamPoly K) (ReparamField K) p := by
  obtain ⟨p, q, hq0, hqfix, hpfix, hrep⟩ := exists_invariant_representation G x hx
  refine ⟨p, q, hq0, ?_, ?_, hrep⟩
  · intro m
    refine hS _ fun e he => ?_
    have := congrArg (MvPolynomial.coeff m) (hpfix e he)
    rwa [coeff_polyEquiv] at this
  · intro m
    refine hS _ fun e he => ?_
    have := congrArg (MvPolynomial.coeff m) (hqfix e he)
    rwa [coeff_polyEquiv] at this

end ReparamField

end GaloisForLFunctions.HTGeometry
