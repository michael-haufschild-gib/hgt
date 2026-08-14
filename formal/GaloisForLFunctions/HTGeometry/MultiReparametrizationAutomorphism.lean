import GaloisForLFunctions.HTGeometry.MultiReparametrization
import GaloisForLFunctions.HTGeometry.ReparametrizationAutomorphism
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Base automorphisms and descent for the several-direction reparametrisation

An automorphism of the base commuting with every prescribed derivation extends to the generic
reparametrisation, acting on the coefficients and fixing every jet, and the extension commutes with
the chain-rule derivation.

An element invariant under a family of such automorphisms is a ratio of jet polynomials whose
coefficients are themselves invariant: the minimal-denominator argument is independent of the index
set of the jets.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

namespace MultiReparamField

universe u

variable {K : Type u} [Field K] {n : ℕ}

/-- A base automorphism acts on the jet polynomial ring through its coefficients. -/
noncomputable def polyEquiv (e : K ≃+* K) : MultiReparamPoly K n ≃+* MultiReparamPoly K n :=
  MvPolynomial.mapEquiv (Fin n × ℕ) e

@[simp] theorem polyEquiv_C (e : K ≃+* K) (a : K) :
    polyEquiv (n := n) e (MvPolynomial.C a : MultiReparamPoly K n) = MvPolynomial.C (e a) := by
  simp [polyEquiv]

@[simp] theorem polyEquiv_X (e : K ≃+* K) (p : Fin n × ℕ) :
    polyEquiv (n := n) e (MvPolynomial.X p : MultiReparamPoly K n) = MvPolynomial.X p := by
  simp [polyEquiv]

@[simp] theorem coeff_polyEquiv (e : K ≃+* K) (m : (Fin n × ℕ) →₀ ℕ) (q : MultiReparamPoly K n) :
    MvPolynomial.coeff m (polyEquiv e q) = e (MvPolynomial.coeff m q) := by
  show MvPolynomial.coeff m (MvPolynomial.map (e : K →+* K) q) = e (MvPolynomial.coeff m q)
  rw [MvPolynomial.coeff_map]
  rfl

/-- A base automorphism acts on the generic reparametrisation. -/
noncomputable def fieldEquiv (e : K ≃+* K) : MultiReparamField K n ≃+* MultiReparamField K n :=
  IsFractionRing.ringEquivOfRingEquiv (K := MultiReparamField K n) (L := MultiReparamField K n)
    (polyEquiv (n := n) e)

theorem fieldEquiv_algebraMap (e : K ≃+* K) (q : MultiReparamPoly K n) :
    fieldEquiv (n := n) e (algebraMap (MultiReparamPoly K n) (MultiReparamField K n) q)
      = algebraMap (MultiReparamPoly K n) (MultiReparamField K n) (polyEquiv e q) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap (K := MultiReparamField K n)
    (L := MultiReparamField K n) (polyEquiv (n := n) e) q

@[simp] theorem fieldEquiv_jet (e : K ≃+* K) (p : Fin n × ℕ) :
    fieldEquiv (n := n) e (jet p : MultiReparamField K n) = jet p := by
  rw [jet, fieldEquiv_algebraMap, polyEquiv_X]

theorem algebraMap_base_eq (a : K) :
    (algebraMap K (MultiReparamField K n) a)
      = algebraMap (MultiReparamPoly K n) (MultiReparamField K n) (MvPolynomial.C a) := by
  rw [IsScalarTower.algebraMap_apply K (MultiReparamPoly K n) (MultiReparamField K n)]
  rfl

@[simp] theorem fieldEquiv_base (e : K ≃+* K) (a : K) :
    fieldEquiv (n := n) e (algebraMap K (MultiReparamField K n) a)
      = algebraMap K (MultiReparamField K n) (e a) := by
  rw [algebraMap_base_eq a, fieldEquiv_algebraMap, polyEquiv_C, ← algebraMap_base_eq]

@[simp] theorem fieldEquiv_symm_jet (e : K ≃+* K) (p : Fin n × ℕ) :
    (fieldEquiv (n := n) e).symm (jet p : MultiReparamField K n) = jet p := by
  apply (fieldEquiv (n := n) e).injective
  rw [RingEquiv.apply_symm_apply, fieldEquiv_jet]

theorem fieldEquiv_symm_base (e : K ≃+* K) (a : K) :
    (fieldEquiv (n := n) e).symm (algebraMap K (MultiReparamField K n) (e a))
      = algebraMap K (MultiReparamField K n) a := by
  apply (fieldEquiv (n := n) e).injective
  rw [RingEquiv.apply_symm_apply, fieldEquiv_base]

section

variable (d : Fin n → Derivation ℤ K K)

/-- The conjugate of the chain-rule derivation by a base automorphism. -/
noncomputable def conjDerivation (e : K ≃+* K) :
    Derivation ℤ (MultiReparamField K n) (MultiReparamField K n) := by
  let D : MultiReparamField K n →+ MultiReparamField K n :=
    { toFun := fun z => (fieldEquiv e).symm (fieldDerivation d (fieldEquiv e z))
      map_zero' := by simp
      map_add' := by
        intro x y
        simp }
  refine Derivation.mk' D.toIntLinearMap ?_
  intro x y
  show (fieldEquiv e).symm (fieldDerivation d (fieldEquiv e (x * y)))
    = x • (fieldEquiv e).symm (fieldDerivation d (fieldEquiv e y))
      + y • (fieldEquiv e).symm (fieldDerivation d (fieldEquiv e x))
  rw [map_mul, Derivation.leibniz]
  simp only [smul_eq_mul, map_add, map_mul, RingEquiv.symm_apply_apply]

@[simp] theorem conjDerivation_apply (e : K ≃+* K) (z : MultiReparamField K n) :
    conjDerivation d e z = (fieldEquiv e).symm (fieldDerivation d (fieldEquiv e z)) := rfl

/-- **A base automorphism commuting with every direction extends to one commuting with the
chain-rule derivation.** -/
theorem fieldEquiv_deriv (e : K ≃+* K)
    (he : ∀ (j : Fin n) (a : K), e (d j a) = d j (e a)) (z : MultiReparamField K n) :
    fieldEquiv (n := n) e (fieldDerivation d z) = fieldDerivation d (fieldEquiv e z) := by
  have hjet : ∀ p : Fin n × ℕ, conjDerivation d e (jet p : MultiReparamField K n)
      = fieldDerivation d (jet p) := by
    intro p
    rw [conjDerivation_apply, fieldEquiv_jet, fieldDerivation_jet, fieldEquiv_symm_jet]
  have hbase : ∀ a : K, conjDerivation d e (algebraMap K (MultiReparamField K n) a)
      = fieldDerivation d (algebraMap K (MultiReparamField K n) a) := by
    intro a
    rw [conjDerivation_apply, fieldEquiv_base, fieldDerivation_algebraMap,
      fieldDerivation_algebraMap, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, fieldEquiv_symm_jet, ← he j a, fieldEquiv_symm_base]
  have hconj : conjDerivation d e = fieldDerivation d := by
    refine GaloisForLFunctions.fractionRing_derivation_ext (A := MultiReparamPoly K n)
      (conjDerivation d e) (fieldDerivation d) ?_
    intro q
    induction q using MvPolynomial.induction_on with
    | C a =>
        rw [← algebraMap_base_eq]
        exact hbase a
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p i hp =>
        have hb : (algebraMap (MultiReparamPoly K n) (MultiReparamField K n) (MvPolynomial.X i))
            = (jet i : MultiReparamField K n) := rfl
        rw [map_mul, Derivation.leibniz, Derivation.leibniz, hp, hb, hjet i]
  have hz := congrArg (fun D => D z) hconj
  simp only [conjDerivation_apply] at hz
  rw [← hz]
  exact (fieldEquiv (n := n) e).apply_symm_apply _

end

/-! ### Descent along base automorphisms -/

/-- The denominators of an element of the reparametrisation field. -/
def IsJetDenom (x : MultiReparamField K n) (q : MultiReparamPoly K n) : Prop :=
  ∃ p : MultiReparamPoly K n,
    algebraMap (MultiReparamPoly K n) (MultiReparamField K n) q * x
      = algebraMap (MultiReparamPoly K n) (MultiReparamField K n) p

theorem exists_nonzero_isJetDenom (x : MultiReparamField K n) :
    ∃ q : MultiReparamPoly K n, q ≠ 0 ∧ IsJetDenom x q := by
  obtain ⟨⟨p, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors (MultiReparamPoly K n)) x
  refine ⟨s.1, nonZeroDivisors.ne_zero s.2, p, ?_⟩
  rw [mul_comm]
  exact hs

theorem isJetDenom_sub {x : MultiReparamField K n} {q₁ q₂ : MultiReparamPoly K n}
    (h₁ : IsJetDenom x q₁) (h₂ : IsJetDenom x q₂) : IsJetDenom x (q₁ - q₂) := by
  obtain ⟨p₁, hp₁⟩ := h₁
  obtain ⟨p₂, hp₂⟩ := h₂
  refine ⟨p₁ - p₂, ?_⟩
  rw [map_sub, map_sub, sub_mul, hp₁, hp₂]

theorem isJetDenom_smul {x : MultiReparamField K n} {q : MultiReparamPoly K n}
    (h : IsJetDenom x q) (a : K) : IsJetDenom x (MvPolynomial.C a * q) := by
  obtain ⟨p, hp⟩ := h
  refine ⟨MvPolynomial.C a * p, ?_⟩
  rw [map_mul, map_mul, mul_assoc, hp]

theorem isJetDenom_polyEquiv {x : MultiReparamField K n} {q : MultiReparamPoly K n}
    (h : IsJetDenom x q) {e : K ≃+* K} (hx : fieldEquiv (n := n) e x = x) :
    IsJetDenom x (polyEquiv e q) := by
  obtain ⟨p, hp⟩ := h
  refine ⟨polyEquiv e p, ?_⟩
  have hEq := congrArg (fieldEquiv (n := n) e) hp
  rw [map_mul, fieldEquiv_algebraMap, fieldEquiv_algebraMap, hx] at hEq
  exact hEq

/-- **Descent along base automorphisms.** -/
theorem exists_invariant_representation (G : Set (K ≃+* K)) (x : MultiReparamField K n)
    (hx : ∀ e ∈ G, fieldEquiv (n := n) e x = x) :
    ∃ p q : MultiReparamPoly K n, q ≠ 0 ∧ (∀ e ∈ G, polyEquiv e q = q) ∧
      (∀ e ∈ G, polyEquiv e p = p) ∧
      algebraMap (MultiReparamPoly K n) (MultiReparamField K n) q * x
        = algebraMap (MultiReparamPoly K n) (MultiReparamField K n) p := by
  classical
  have hne : ∃ N : ℕ, ∃ q : MultiReparamPoly K n, q ≠ 0 ∧ IsJetDenom x q ∧ q.support.card = N := by
    obtain ⟨q, hq0, hq⟩ := exists_nonzero_isJetDenom x
    exact ⟨q.support.card, q, hq0, hq, rfl⟩
  obtain ⟨q₀, hq₀0, hq₀, hcard⟩ := Nat.find_spec hne
  set N := Nat.find hne with hN
  have hmin : ∀ q : MultiReparamPoly K n, q ≠ 0 → IsJetDenom x q → N ≤ q.support.card := by
    intro q hq0 hq
    exact Nat.find_le ⟨q, hq0, hq, rfl⟩
  obtain ⟨m₀, hm₀⟩ : q₀.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    exact hq₀0 (MvPolynomial.support_eq_empty.mp h)
  have hc0 : MvPolynomial.coeff m₀ q₀ ≠ 0 := MvPolynomial.mem_support_iff.mp hm₀
  set q : MultiReparamPoly K n := MvPolynomial.C (MvPolynomial.coeff m₀ q₀)⁻¹ * q₀ with hqdef
  have hqdenom : IsJetDenom x q := isJetDenom_smul hq₀ _
  have hqcoeff : ∀ m, MvPolynomial.coeff m q
      = (MvPolynomial.coeff m₀ q₀)⁻¹ * MvPolynomial.coeff m q₀ := by
    intro m
    rw [hqdef, MvPolynomial.coeff_C_mul]
  have hqsupp : q.support = q₀.support := by
    ext m
    simp only [MvPolynomial.mem_support_iff, hqcoeff, Ne, mul_eq_zero, not_or]
    exact ⟨fun h => h.2, fun h => ⟨inv_ne_zero hc0, h⟩⟩
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
  refine IsFractionRing.injective (MultiReparamPoly K n) (MultiReparamField K n) ?_
  have hEq := congrArg (fieldEquiv (n := n) e) hp
  rw [map_mul, fieldEquiv_algebraMap, fieldEquiv_algebraMap, hx e he, hqfix e he, hp] at hEq
  exact hEq.symm

/-- **Descent to a subfield of coefficients.** -/
theorem exists_representation_coeff_mem (G : Set (K ≃+* K)) (S : Subfield K)
    (hS : ∀ a : K, (∀ e ∈ G, e a = a) → a ∈ S) (x : MultiReparamField K n)
    (hx : ∀ e ∈ G, fieldEquiv (n := n) e x = x) :
    ∃ p q : MultiReparamPoly K n, q ≠ 0 ∧ (∀ m, MvPolynomial.coeff m p ∈ S) ∧
      (∀ m, MvPolynomial.coeff m q ∈ S) ∧
      algebraMap (MultiReparamPoly K n) (MultiReparamField K n) q * x
        = algebraMap (MultiReparamPoly K n) (MultiReparamField K n) p := by
  obtain ⟨p, q, hq0, hqfix, hpfix, hrep⟩ := exists_invariant_representation G x hx
  refine ⟨p, q, hq0, ?_, ?_, hrep⟩
  · intro m
    refine hS _ fun e he => ?_
    have hcoe := congrArg (MvPolynomial.coeff m) (hpfix e he)
    rwa [coeff_polyEquiv] at hcoe
  · intro m
    refine hS _ fun e he => ?_
    have hcoe := congrArg (MvPolynomial.coeff m) (hqfix e he)
    rwa [coeff_polyEquiv] at hcoe

end MultiReparamField

end GaloisForLFunctions.HTGeometry
