/-
Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 1.3
(`t26n`), free basis.

The multiplicative monoid of polynomials with constant coefficient one over a field is free
commutative on the irreducible such polynomials: existence of a factorization is an induction on
the degree (divide an irreducible factor by its constant coefficient and multiply it back into the
cofactor), and uniqueness follows from `UniqueFactorizationMonoid.factors_unique` because two
associated normalized polynomials are equal — associates differ by a constant, and comparing
constant coefficients forces that constant to be `1`.

This is the free basis on which the lower isomorphism of Proposition 1.3 is expressed:
`W_rat (κ₀)` is free abelian on the normalized irreducibles of `κ₀[t]`.
-/
import GaloisForLFunctions.RHTower.DeningerDynSysNormalizedIrreducible
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

namespace RHTower

open Polynomial

variable {F : Type*} [Field F]

/-- A polynomial with constant coefficient one is a unit exactly when it is `1`. -/
theorem deningerIsUnit_iff_eq_one {p : Polynomial F} (h : p.coeff 0 = 1) :
    IsUnit p ↔ p = 1 := by
  refine ⟨fun hu => ?_, fun h1 => h1 ▸ isUnit_one⟩
  obtain ⟨c, -, hc⟩ := Polynomial.isUnit_iff.1 hu
  rw [← hc] at h ⊢
  rw [Polynomial.coeff_C_zero] at h
  rw [h, Polynomial.C_1]

/-- Associated normalized polynomials are equal. -/
theorem deningerEq_of_associated {a b : Polynomial F} (ha : a.coeff 0 = 1) (hb : b.coeff 0 = 1)
    (h : Associated a b) : a = b := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨c, -, hc⟩ := Polynomial.isUnit_iff.1 u.isUnit
  have hab : a * Polynomial.C c = b := by rw [hc]; exact hu
  have hcoeff : a.coeff 0 * c = b.coeff 0 := by
    rw [← Polynomial.coeff_C_zero (a := c), ← Polynomial.mul_coeff_zero, hab]
  rw [ha, hb, one_mul] at hcoeff
  rw [← hab, hcoeff, Polynomial.C_1, mul_one]

/-- **Normalized factorization, existence.**  A polynomial with constant coefficient one over a
field is a product of irreducible polynomials with constant coefficient one. -/
theorem deningerExists_normalized_factorization :
    ∀ (n : ℕ) (p : Polynomial F), p.natDegree = n → p.coeff 0 = 1 →
      ∃ S : Multiset (Polynomial F),
        (∀ r ∈ S, r.coeff 0 = 1 ∧ Irreducible r) ∧ S.prod = p := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro p hdeg hp
    have hpne : p ≠ 0 := fun h => by rw [h, Polynomial.coeff_zero] at hp; exact zero_ne_one hp
    by_cases hu : IsUnit p
    · exact ⟨0, by simp, by simpa using ((deningerIsUnit_iff_eq_one hp).1 hu).symm⟩
    · obtain ⟨q, hqirr, r, hr⟩ := WfDvdMonoid.exists_irreducible_factor hu hpne
      have hc : q.coeff 0 * r.coeff 0 = 1 := by
        rw [← Polynomial.mul_coeff_zero, ← hr, hp]
      have hcne : q.coeff 0 ≠ 0 := left_ne_zero_of_mul_eq_one hc
      set c : F := q.coeff 0 with hcdef
      set q' : Polynomial F := Polynomial.C c⁻¹ * q with hq'
      set r' : Polynomial F := Polynomial.C c * r with hr'
      have hq'0 : q'.coeff 0 = 1 := by
        rw [hq', Polynomial.mul_coeff_zero, Polynomial.coeff_C_zero, ← hcdef,
          inv_mul_cancel₀ hcne]
      have hr'0 : r'.coeff 0 = 1 := by
        rw [hr', Polynomial.mul_coeff_zero, Polynomial.coeff_C_zero]
        exact hc
      have hq'irr : Irreducible q' := by
        refine (Associated.irreducible ?_ hqirr)
        exact ⟨(Polynomial.isUnit_C.2 (Ne.isUnit (inv_ne_zero hcne))).unit, by
          rw [hq']
          rw [IsUnit.unit_spec]
          ring⟩
      have hprod : q' * r' = p := by
        rw [hq', hr']
        calc Polynomial.C c⁻¹ * q * (Polynomial.C c * r)
            = (Polynomial.C c⁻¹ * Polynomial.C c) * (q * r) := by ring
          _ = p := by
              rw [← Polynomial.C_mul, inv_mul_cancel₀ hcne, Polynomial.C_1, one_mul, hr]
      have hqdeg : 0 < q.natDegree := by
        rcases Nat.eq_zero_or_pos q.natDegree with h0 | h0
        · exact absurd (Polynomial.isUnit_iff.2 ⟨q.coeff 0, Ne.isUnit hcne,
            (Polynomial.eq_C_of_natDegree_eq_zero h0).symm⟩) hqirr.not_isUnit
        · exact h0
      have hrne : r ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hr
        exact hpne hr
      have hqne : q ≠ 0 := hqirr.ne_zero
      have hdegsum : p.natDegree = q.natDegree + r.natDegree := by
        rw [hr, Polynomial.natDegree_mul hqne hrne]
      have hr'deg : r'.natDegree = r.natDegree := by
        rw [hr', Polynomial.natDegree_C_mul (a := c) hcne]
      have hlt : r'.natDegree < n := by
        rw [hr'deg, ← hdeg, hdegsum]
        omega
      obtain ⟨S, hS, hSprod⟩ := ih r'.natDegree hlt r' rfl hr'0
      refine ⟨q' ::ₘ S, ?_, ?_⟩
      · intro s hs
        rcases Multiset.mem_cons.1 hs with h | h
        · exact h ▸ ⟨hq'0, hq'irr⟩
        · exact hS s h
      · rw [Multiset.prod_cons, hSprod, hprod]

/-- **Normalized factorization, uniqueness.** -/
theorem deningerNormalized_factorization_unique {S T : Multiset (Polynomial F)}
    (hS : ∀ r ∈ S, r.coeff 0 = 1 ∧ Irreducible r)
    (hT : ∀ r ∈ T, r.coeff 0 = 1 ∧ Irreducible r) (h : S.prod = T.prod) : S = T := by
  have hrel : Multiset.Rel Associated S T :=
    UniqueFactorizationMonoid.factors_unique (fun x hx => (hS x hx).2) (fun x hx => (hT x hx).2)
      (h ▸ Associated.refl _)
  refine Multiset.rel_eq.1 (hrel.mono ?_)
  intro a ha b hb hab
  exact deningerEq_of_associated (hS a ha).1 (hT b hb).1 hab

/-- The normalized factorization exists for every normalized polynomial. -/
theorem deningerExists_normalized_factorization' (p : Polynomial F) (hp : p.coeff 0 = 1) :
    ∃ S : Multiset (Polynomial F),
      (∀ r ∈ S, r.coeff 0 = 1 ∧ Irreducible r) ∧ S.prod = p :=
  deningerExists_normalized_factorization p.natDegree p rfl hp

open Classical in
/-- The multiset of normalized irreducible factors of a normalized polynomial (and `0` on
polynomials whose constant coefficient is not one). -/
noncomputable def deningerNormalizedFactors (p : Polynomial F) : Multiset (Polynomial F) :=
  if h : p.coeff 0 = 1 then (deningerExists_normalized_factorization' p h).choose else 0

theorem deningerNormalizedFactors_spec {p : Polynomial F} (hp : p.coeff 0 = 1) :
    (∀ r ∈ deningerNormalizedFactors p, r.coeff 0 = 1 ∧ Irreducible r) ∧
      (deningerNormalizedFactors p).prod = p := by
  classical
  rw [deningerNormalizedFactors, dif_pos hp]
  exact (deningerExists_normalized_factorization' p hp).choose_spec

@[simp] theorem deningerNormalizedFactors_prod {p : Polynomial F} (hp : p.coeff 0 = 1) :
    (deningerNormalizedFactors p).prod = p :=
  (deningerNormalizedFactors_spec hp).2

theorem deningerNormalizedFactors_mem {p : Polynomial F} (hp : p.coeff 0 = 1)
    {r : Polynomial F} (hr : r ∈ deningerNormalizedFactors p) :
    r.coeff 0 = 1 ∧ Irreducible r :=
  (deningerNormalizedFactors_spec hp).1 r hr

/-- The normalized factorization is determined by the polynomial. -/
theorem deningerNormalizedFactors_eq {p : Polynomial F} (hp : p.coeff 0 = 1)
    {S : Multiset (Polynomial F)} (hS : ∀ r ∈ S, r.coeff 0 = 1 ∧ Irreducible r)
    (hprod : S.prod = p) : S = deningerNormalizedFactors p :=
  deningerNormalized_factorization_unique hS (deningerNormalizedFactors_spec hp).1
    (by rw [hprod, deningerNormalizedFactors_prod hp])

theorem deningerMul_coeff_zero {p q : Polynomial F} (hp : p.coeff 0 = 1) (hq : q.coeff 0 = 1) :
    (p * q).coeff 0 = 1 := by
  rw [Polynomial.mul_coeff_zero, hp, hq, one_mul]

theorem deningerPow_coeff_zero {p : Polynomial F} (hp : p.coeff 0 = 1) (n : ℕ) :
    (p ^ n).coeff 0 = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      exact deningerMul_coeff_zero ih hp

/-- **The monoid of normalized polynomials is free commutative on the normalized irreducibles.**
Factorization is additive on products. -/
theorem deningerNormalizedFactors_mul {p q : Polynomial F} (hp : p.coeff 0 = 1)
    (hq : q.coeff 0 = 1) :
    deningerNormalizedFactors (p * q)
      = deningerNormalizedFactors p + deningerNormalizedFactors q := by
  refine (deningerNormalizedFactors_eq (deningerMul_coeff_zero hp hq) ?_ ?_).symm
  · intro r hr
    rcases Multiset.mem_add.1 hr with h | h
    · exact deningerNormalizedFactors_mem hp h
    · exact deningerNormalizedFactors_mem hq h
  · rw [Multiset.prod_add, deningerNormalizedFactors_prod hp, deningerNormalizedFactors_prod hq]

@[simp] theorem deningerNormalizedFactors_one :
    deningerNormalizedFactors (1 : Polynomial F) = 0 :=
  (deningerNormalizedFactors_eq (by simp) (by simp) (by simp)).symm

/-- An irreducible normalized polynomial has itself as its only factor. -/
theorem deningerNormalizedFactors_irreducible {p : Polynomial F} (hp : p.coeff 0 = 1)
    (hirr : Irreducible p) : deningerNormalizedFactors p = {p} :=
  (deningerNormalizedFactors_eq hp (by
    intro r hr
    rw [Multiset.mem_singleton] at hr
    exact hr ▸ ⟨hp, hirr⟩) (by simp)).symm

theorem deningerNormalizedFactors_pow {p : Polynomial F} (hp : p.coeff 0 = 1) (n : ℕ) :
    deningerNormalizedFactors (p ^ n) = n • deningerNormalizedFactors p := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, deningerNormalizedFactors_mul (deningerPow_coeff_zero hp n) hp, ih,
        succ_nsmul]

end RHTower
