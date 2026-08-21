/-
# The Kronecker specialization

`S_d` sends a multivariate polynomial to a two-variable one by `X_{i+1} ↦ Y ^ (d ^ i)`, keeping the
first variable.  It is an algebra map, hence automatically multiplicative; the content is that it is
a *bijection* between the polynomials of degree `< d` in each of `X_1,…,X_{k-1}` and the polynomials
of degree `< d ^ k` in `Y`.  Both directions are base-`d` digit statements.

This is §3 of Coleman--Zwald, and it is what turns Hilbert's irreducibility theorem in one parameter
into the statement for several parameters, with no need for "K(t) is Hilbertian".
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Common
import Mathlib.Tactic.Ring
import Mathlib.Data.Fin.Basic

namespace GaloisForLFunctions.HTGeometry.HilbertIrreducibility

open Finset

/-- The base-`d` digits of `β`, as a function on `Fin r`. -/
def kdigit (d β : ℕ) (i : ℕ) : ℕ := β / d ^ i % d

/-- The value of a digit string in base `d`. -/
def ksum {r : ℕ} (d : ℕ) (a : Fin r → ℕ) : ℕ := ∑ i, a i * d ^ (i : ℕ)

theorem kdigit_lt {d : ℕ} (hd : 1 ≤ d) (β i : ℕ) : kdigit d β i < d :=
  Nat.mod_lt _ hd

theorem ksum_lt {r d : ℕ} {a : Fin r → ℕ} (ha : ∀ i, a i < d) :
    ksum d a < d ^ r := by
  induction r with
  | zero => simp [ksum]
  | succ r ih =>
      have hsplit : ksum d a = a 0 + d * ksum d (fun i : Fin r => a i.succ) := by
        rw [ksum, ksum, Fin.sum_univ_succ, Finset.mul_sum]
        simp only [Fin.val_succ, pow_succ, Fin.val_zero, pow_zero, mul_one]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      have hrec : ksum d (fun i : Fin r => a i.succ) < d ^ r := ih (fun i => ha i.succ)
      have h0 : a 0 < d := ha 0
      calc ksum d a = a 0 + d * ksum d (fun i : Fin r => a i.succ) := hsplit
        _ < d + d * ksum d (fun i : Fin r => a i.succ) := by omega
        _ = d * (ksum d (fun i : Fin r => a i.succ) + 1) := by ring
        _ ≤ d * d ^ r := by
            refine Nat.mul_le_mul_left d ?_
            omega
        _ = d ^ (r + 1) := by rw [pow_succ]; ring

theorem ksum_inj {r d : ℕ} (hd : 1 ≤ d) {a b : Fin r → ℕ}
    (ha : ∀ i, a i < d) (hb : ∀ i, b i < d) (h : ksum d a = ksum d b) : a = b := by
  induction r with
  | zero => funext i; exact absurd i.2 (by omega)
  | succ r ih =>
      have hsplit : ∀ c : Fin (r + 1) → ℕ,
          ksum d c = c 0 + d * ksum d (fun i : Fin r => c i.succ) := by
        intro c
        rw [ksum, ksum, Fin.sum_univ_succ, Finset.mul_sum]
        simp only [Fin.val_succ, pow_succ, Fin.val_zero, pow_zero, mul_one]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      rw [hsplit a, hsplit b] at h
      have h0 : a 0 = b 0 := by
        have hmod := congrArg (· % d) h
        simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (ha 0),
          Nat.mod_eq_of_lt (hb 0)] using hmod
      have hrest : ksum d (fun i : Fin r => a i.succ) = ksum d (fun i : Fin r => b i.succ) := by
        have hdpos : 0 < d := hd
        have := h
        rw [h0] at this
        exact Nat.eq_of_mul_eq_mul_left hdpos (by omega)
      have := ih (fun i => ha i.succ) (fun i => hb i.succ) hrest
      funext i
      refine Fin.cases ?_ ?_ i
      · exact h0
      · intro j
        exact congrFun this j

theorem ksum_kdigit {r d : ℕ} (hd : 1 ≤ d) {β : ℕ} (hβ : β < d ^ r) :
    ksum d (fun i : Fin r => kdigit d β (i : ℕ)) = β := by
  induction r generalizing β with
  | zero =>
      simp only [pow_zero, Nat.lt_one_iff] at hβ
      simp [ksum, hβ]
  | succ r ih =>
      have hsplit : ksum d (fun i : Fin (r + 1) => kdigit d β (i : ℕ))
          = kdigit d β 0 + d * ksum d (fun i : Fin r => kdigit d β (i + 1)) := by
        rw [ksum, ksum, Fin.sum_univ_succ, Finset.mul_sum]
        simp only [Fin.val_succ, pow_succ, Fin.val_zero, pow_zero, mul_one]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      have hstep : ∀ i : ℕ, kdigit d β (i + 1) = kdigit d (β / d) i := by
        intro i
        rw [kdigit, kdigit, pow_succ, Nat.div_div_eq_div_mul, mul_comm]
      have hlt : β / d < d ^ r := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]
        calc β < d ^ (r + 1) := hβ
          _ = d ^ r * d := by rw [pow_succ]
      have hrec := ih hlt
      rw [hsplit]
      simp only [hstep]
      rw [hrec, kdigit, pow_zero, Nat.div_one]
      exact Nat.mod_add_div β d

/-! ### The substitution itself

The variable that will be *specialised* is kept in the **coefficient ring** `R`; the Kronecker map
collapses all the `MvPolynomial` variables into a single one.  With `R = F[X₀]` this is exactly
Coleman--Zwald's `S_d`, and it lands in `F[X₀][Y]`, which is the shape the one-parameter Hilbert
theorem consumes.
-/

open Polynomial MvPolynomial

variable {R : Type*} [CommRing R]

/-- The Kronecker substitution values: `X_j ↦ Y ^ (d ^ j)`. -/
noncomputable def kronVal (R : Type*) [CommRing R] (d k : ℕ) : Fin k → Polynomial R :=
  fun j => (Polynomial.X : Polynomial R) ^ (d ^ (j : ℕ))

/-- The Kronecker specialization `S_d`. -/
noncomputable def kron (R : Type*) [CommRing R] (d k : ℕ) :
    MvPolynomial (Fin k) R →ₐ[R] Polynomial R :=
  MvPolynomial.aeval (kronVal R d k)

/-- The exponent of `Y` attached to a multivariate exponent. -/
def kexp (d : ℕ) {k : ℕ} (a : Fin k →₀ ℕ) : ℕ := ksum d (fun j : Fin k => a j)

theorem kron_monomial (d k : ℕ) (a : Fin k →₀ ℕ) (c : R) :
    kron R d k (MvPolynomial.monomial a c)
      = Polynomial.C c * Polynomial.X ^ (kexp d a) := by
  classical
  rw [kron, MvPolynomial.aeval_monomial]
  have hprod : (a.prod fun i n => kronVal R d k i ^ n)
      = ∏ i : Fin k, kronVal R d k i ^ (a i) := by
    refine Finsupp.prod_of_support_subset a (Finset.subset_univ _) _ ?_
    intro i _
    simp
  rw [hprod, kexp, ksum, ← Finset.prod_pow_eq_pow_sum]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  simp [kronVal, ← pow_mul, mul_comm]

/-- `p` has all its exponents in the Kronecker box. -/
def KBounded (d : ℕ) {k : ℕ} (p : MvPolynomial (Fin k) R) : Prop :=
  ∀ b ∈ p.support, ∀ j : Fin k, b j < d

theorem kexp_inj {d k : ℕ} (hd : 1 ≤ d) {a b : Fin k →₀ ℕ}
    (ha : ∀ j : Fin k, a j < d) (hb : ∀ j : Fin k, b j < d) (he : kexp d a = kexp d b) : a = b :=
  Finsupp.ext (congrFun (ksum_inj hd ha hb he))

theorem coeff_kron (d k : ℕ) (p : MvPolynomial (Fin k) R) (n : ℕ) :
    (kron R d k p).coeff n = ∑ b ∈ p.support, (if n = kexp d b then p.coeff b else 0) := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum p]
  rw [map_sum]
  simp only [kron_monomial]
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  by_cases h : n = kexp d b
  · rw [if_pos h, if_pos h, mul_one]
  · rw [if_neg h, if_neg h, mul_zero]

theorem coeff_kron_eq_coeff {d k : ℕ} (hd : 1 ≤ d) {p : MvPolynomial (Fin k) R}
    (hp : KBounded d p) (a : Fin k →₀ ℕ) (ha : ∀ j : Fin k, a j < d) :
    (kron R d k p).coeff (kexp d a) = p.coeff a := by
  classical
  rw [coeff_kron]
  have hkey : ∀ b ∈ p.support, b ≠ a →
      (if kexp d a = kexp d b then p.coeff b else 0) = 0 := by
    intro b hb hne
    by_cases h1 : kexp d a = kexp d b
    · exact absurd (kexp_inj hd ha (hp b hb) h1).symm hne
    · rw [if_neg h1]
  by_cases hmem : a ∈ p.support
  · rw [Finset.sum_eq_single a hkey (fun h => absurd hmem h)]
    simp
  · have hz : p.coeff a = 0 := by
      simpa [MvPolynomial.notMem_support_iff] using hmem
    rw [hz]
    refine Finset.sum_eq_zero fun b hb => ?_
    exact hkey b hb (fun h => hmem (h ▸ hb))

theorem kron_injOn {d k : ℕ} (hd : 1 ≤ d) {p q : MvPolynomial (Fin k) R}
    (hp : KBounded d p) (hq : KBounded d q) (h : kron R d k p = kron R d k q) : p = q := by
  classical
  refine MvPolynomial.ext p q fun a => ?_
  by_cases ha : ∀ j : Fin k, a j < d
  · rw [← coeff_kron_eq_coeff hd hp a ha, ← coeff_kron_eq_coeff hd hq a ha, h]
  · push_neg at ha
    obtain ⟨j, hj⟩ := ha
    have hpa : p.coeff a = 0 := by
      by_contra hc
      exact absurd (hp a (MvPolynomial.mem_support_iff.mpr hc) j) (not_lt.mpr hj)
    have hqa : q.coeff a = 0 := by
      by_contra hc
      exact absurd (hq a (MvPolynomial.mem_support_iff.mpr hc) j) (not_lt.mpr hj)
    rw [hpa, hqa]

/-! ### The pullback -/

/-- The multivariate exponent whose base-`d` digits are those of `n`. -/
noncomputable def mkExp (d k : ℕ) (n : ℕ) : Fin k →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun j : Fin k => kdigit d n (j : ℕ))

@[simp] theorem mkExp_apply (d k n : ℕ) (j : Fin k) : mkExp d k n j = kdigit d n (j : ℕ) := rfl

theorem mkExp_bounded {d : ℕ} (hd : 1 ≤ d) (k n : ℕ) (j : Fin k) : mkExp d k n j < d :=
  kdigit_lt hd n j

theorem kexp_mkExp {d k : ℕ} (hd : 1 ≤ d) {n : ℕ} (hn : n < d ^ k) :
    kexp d (mkExp d k n) = n := by
  rw [kexp]
  simpa using ksum_kdigit hd hn

/-- **The Kronecker pullback.**  Every one-variable polynomial of degree `< d ^ k` is `S_d` of a
multivariate polynomial inside the Kronecker box. -/
theorem exists_kron_eq {d k : ℕ} (hd : 1 ≤ d) {P : Polynomial R}
    (hP : ∀ n, d ^ k ≤ n → P.coeff n = 0) :
    ∃ p : MvPolynomial (Fin k) R, KBounded d p ∧ kron R d k p = P := by
  classical
  set p : MvPolynomial (Fin k) R :=
    ∑ n ∈ Finset.range (d ^ k), MvPolynomial.monomial (mkExp d k n) (P.coeff n) with hp
  have hcoeff : ∀ a : Fin k →₀ ℕ, p.coeff a
      = ∑ n ∈ Finset.range (d ^ k), (if mkExp d k n = a then P.coeff n else 0) := by
    intro a
    rw [hp]
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  have hbdd : KBounded d p := by
    intro b hb j
    rw [MvPolynomial.mem_support_iff, hcoeff] at hb
    by_contra hcon
    apply hb
    refine Finset.sum_eq_zero fun n _ => ?_
    by_cases h : mkExp d k n = b
    · exact absurd (h ▸ mkExp_bounded hd k n j) hcon
    · rw [if_neg h]
  refine ⟨p, hbdd, ?_⟩
  refine Polynomial.ext fun n => ?_
  by_cases hn : n < d ^ k
  · have ha : ∀ j : Fin k, (mkExp d k n) j < d := mkExp_bounded hd k n
    have hkey := coeff_kron_eq_coeff hd hbdd (mkExp d k n) ha
    rw [kexp_mkExp hd hn] at hkey
    rw [hkey, hcoeff]
    rw [Finset.sum_eq_single n]
    · rw [if_pos rfl]
    · intro n' hn' hne
      by_cases h : mkExp d k n' = mkExp d k n
      · exfalso
        apply hne
        have := congrArg (kexp d) h
        rwa [kexp_mkExp hd (Finset.mem_range.mp hn'), kexp_mkExp hd hn] at this
      · rw [if_neg h]
    · intro hcon
      exact absurd (Finset.mem_range.mpr hn) hcon
  · push_neg at hn
    rw [hP n hn, coeff_kron]
    refine Finset.sum_eq_zero fun b hb => ?_
    have hlt : kexp d b < d ^ k := by
      rw [kexp]
      exact ksum_lt (fun j => hbdd b hb j)
    rw [if_neg (by omega)]

/-- Kronecker commutes with specialising the coefficients. -/
theorem kron_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (d k : ℕ)
    (p : MvPolynomial (Fin k) R) :
    Polynomial.map φ (kron R d k p) = kron S d k (MvPolynomial.map φ p) := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum p]
  rw [map_sum, Polynomial.map_sum]
  conv_rhs => rw [MvPolynomial.as_sum p]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [kron_monomial, MvPolynomial.map_monomial, kron_monomial, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]

theorem coeff_kron_eq_zero_of_le {d k : ℕ} {p : MvPolynomial (Fin k) R} (hp : KBounded d p)
    {n : ℕ} (hn : d ^ k ≤ n) : (kron R d k p).coeff n = 0 := by
  classical
  rw [coeff_kron]
  refine Finset.sum_eq_zero fun b hb => ?_
  have hlt : kexp d b < d ^ k := by
    rw [kexp]
    exact ksum_lt (fun j => hp b hb j)
  rw [if_neg (by omega)]

theorem natDegree_kron_lt {d k : ℕ} (hdk : 0 < d ^ k) {p : MvPolynomial (Fin k) R}
    (hp : KBounded d p) : (kron R d k p).natDegree < d ^ k := by
  have hle : (kron R d k p).natDegree ≤ d ^ k - 1 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    exact coeff_kron_eq_zero_of_le hp (by omega)
  omega

theorem kBounded_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {d k : ℕ}
    {p : MvPolynomial (Fin k) R} (hp : KBounded d p) : KBounded d (MvPolynomial.map φ p) :=
  fun b hb j => hp b (MvPolynomial.support_map_subset φ p hb) j

theorem kBounded_of_degreeOf {d k : ℕ} {p : MvPolynomial (Fin k) R}
    (h : ∀ j : Fin k, MvPolynomial.degreeOf j p < d) : KBounded d p := by
  intro b hb j
  have hb' := (MvPolynomial.degreeOf_le_iff (n := j) (f := p)
    (d := MvPolynomial.degreeOf j p)).mp le_rfl b hb
  have := h j
  omega

end GaloisForLFunctions.HTGeometry.HilbertIrreducibility

