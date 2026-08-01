import GaloisForLFunctions.HTGeometry.LinearIrreducibleCriterion
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid
import GaloisForLFunctions.HTGeometry.DeterminantDegreeOne

/-!
# Irreducibility of a multivariate polynomial linear in one variable

Peeling off the first variable identifies the polynomial ring in `n+1` variables with polynomials in
one variable over the ring in the remaining `n`.  A polynomial that is the first variable times a
cofactor plus a remainder, both in the remaining variables, becomes a linear polynomial there.

So it is irreducible as soon as the cofactor is nonzero and the two have no common factor.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

variable {K : Type*} [Field K] {n : ℕ}

theorem finSuccEquiv_rename_succ (p : MvPolynomial (Fin n) K) :
    MvPolynomial.finSuccEquiv K n (MvPolynomial.rename Fin.succ p) = Polynomial.C p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      rw [MvPolynomial.rename_C]
      have h := RingHom.congr_fun (MvPolynomial.finSuccEquiv_comp_C_eq_C (R := K) n) a
      rw [RingHom.comp_apply, RingHom.comp_apply] at h
      rw [← h]
      exact (MvPolynomial.finSuccEquiv K n).apply_symm_apply _
  | add q r hq hr => rw [map_add, map_add, hq, hr, map_add]
  | mul_X q i hq =>
      rw [map_mul, map_mul, hq, MvPolynomial.rename_X, MvPolynomial.finSuccEquiv_X_succ,
        ← Polynomial.C_mul]

theorem finSuccEquiv_linear (A B : MvPolynomial (Fin n) K) :
    MvPolynomial.finSuccEquiv K n
        (MvPolynomial.X 0 * MvPolynomial.rename Fin.succ A + MvPolynomial.rename Fin.succ B) =
      Polynomial.C A * Polynomial.X + Polynomial.C B := by
  rw [map_add, map_mul, MvPolynomial.finSuccEquiv_X_zero,
    finSuccEquiv_rename_succ, finSuccEquiv_rename_succ, mul_comm]

/-- **A polynomial linear in the first variable is irreducible when its coefficients have no common
factor.** -/
theorem irreducible_linear_in_X_zero {A B : MvPolynomial (Fin n) K} (hA : A ≠ 0)
    (hgcd : ∀ r : MvPolynomial (Fin n) K, r ∣ A → r ∣ B → IsUnit r) :
    Irreducible (MvPolynomial.X 0 * MvPolynomial.rename Fin.succ A +
      MvPolynomial.rename Fin.succ B) := by
  rw [← MulEquiv.irreducible_iff (MvPolynomial.finSuccEquiv K n).toMulEquiv]
  show Irreducible (MvPolynomial.finSuccEquiv K n _)
  rw [finSuccEquiv_linear]
  exact irreducible_linear_of_forall_isUnit hA hgcd

/-! ## Recognising the polynomials free of the first variable -/

/-- **A polynomial of degree zero in the first variable comes from the remaining ones.** -/
theorem exists_rename_succ_of_degreeOf_zero {p : MvPolynomial (Fin (n + 1)) K}
    (h : MvPolynomial.degreeOf 0 p = 0) :
    ∃ q : MvPolynomial (Fin n) K, p = MvPolynomial.rename Fin.succ q := by
  have hdeg : (MvPolynomial.finSuccEquiv K n p).natDegree = 0 := by
    rw [MvPolynomial.natDegree_finSuccEquiv]
    exact h
  obtain ⟨q, hq⟩ := Polynomial.natDegree_eq_zero.1 hdeg
  refine ⟨q, ?_⟩
  have hinj := (MvPolynomial.finSuccEquiv K n).injective
  refine hinj ?_
  rw [finSuccEquiv_rename_succ, hq]

/-! ## The induction step -/

/-- **Irreducibility from a corner expansion with a separating point.**  If the cofactor is
irreducible and some specialisation kills it without killing the remainder, then the polynomial
`X_0 * A + B` is irreducible.  This is the induction step of the rectangular determinant argument. -/
theorem irreducible_linear_of_irreducible_cofactor {S : Type*} [CommRing S]
    {A B : MvPolynomial (Fin n) K} (hA : Irreducible A)
    (φ : MvPolynomial (Fin n) K →+* S) (hA0 : φ A = 0) (hB0 : φ B ≠ 0) :
    Irreducible (MvPolynomial.X 0 * MvPolynomial.rename Fin.succ A +
      MvPolynomial.rename Fin.succ B) := by
  have hAdvd : ¬ A ∣ B := not_dvd_of_map_eq_zero_of_map_ne_zero φ hA0 hB0
  refine irreducible_linear_in_X_zero hA.ne_zero fun r hrA hrB => ?_
  obtain ⟨c, hc⟩ := hrA
  rcases hA.isUnit_or_isUnit hc with hu | hu
  · exact hu
  · exfalso
    obtain ⟨u, hu⟩ := hu
    have hAr : A ∣ r := ⟨(↑u⁻¹ : MvPolynomial (Fin n) K), by
      rw [hc, ← hu]
      rw [mul_assoc, Units.mul_inv, mul_one]⟩
    exact hAdvd (hAr.trans hrB)

/-- **Irreducibility from a corner expansion with a sign.**  The expansion of a determinant along the
column carrying the first variable produces a unit multiple; absorbing it, the same criterion
applies. -/
theorem irreducible_of_corner_expansion {S : Type*} [CommRing S]
    {D : MvPolynomial (Fin (n + 1)) K} {A B : MvPolynomial (Fin n) K}
    {u : (MvPolynomial (Fin (n + 1)) K)ˣ}
    (hD : (u : MvPolynomial (Fin (n + 1)) K) * D =
      MvPolynomial.X 0 * MvPolynomial.rename Fin.succ A + MvPolynomial.rename Fin.succ B)
    (hA : Irreducible A) (φ : MvPolynomial (Fin n) K →+* S) (hA0 : φ A = 0) (hB0 : φ B ≠ 0) :
    Irreducible D := by
  have h := irreducible_linear_of_irreducible_cofactor hA φ hA0 hB0
  rw [← hD] at h
  exact (irreducible_units_mul u).1 h

/-- **Adding a variable preserves irreducibility.**  An irreducible polynomial stays irreducible when
read in one more variable, since it becomes a constant there and a constant is prime exactly when it
was. -/
theorem irreducible_rename_succ {A : MvPolynomial (Fin n) K} (hA : Irreducible A) :
    Irreducible (MvPolynomial.rename Fin.succ A) := by
  have hprime : Prime A := UniqueFactorizationMonoid.irreducible_iff_prime.1 hA
  have hCprime : Prime (Polynomial.C A) := Polynomial.prime_C_iff.2 hprime
  have hmap : (MvPolynomial.finSuccEquiv K n) (MvPolynomial.rename Fin.succ A) =
      Polynomial.C A := finSuccEquiv_rename_succ A
  refine UniqueFactorizationMonoid.irreducible_iff_prime.2 ?_
  refine (MulEquiv.prime_iff (MvPolynomial.finSuccEquiv K n).toMulEquiv).1 ?_
  show Prime (MvPolynomial.finSuccEquiv K n (MvPolynomial.rename Fin.succ A))
  rw [hmap]
  exact hCprime

/-- **Irreducibility is unaffected by a reindexing of the variables.**  In particular by an
arithmetic identity between the numbers of variables, which is what lets an induction whose index
arithmetic is written in different but equal forms be carried out. -/
theorem irreducible_rename_finCongr {L₁ L₂ : ℕ} (h : L₁ = L₂) (p : MvPolynomial (Fin L₁) K) :
    Irreducible (MvPolynomial.rename (finCongr h) p) ↔ Irreducible p := by
  have hmap : MvPolynomial.rename (R := K) (finCongr h) p =
      (MvPolynomial.renameEquiv K (finCongr h)) p := rfl
  rw [hmap]
  exact MulEquiv.irreducible_iff (MvPolynomial.renameEquiv K (finCongr h)).toMulEquiv

/-- **The multivariate form with a unit cofactor.**  When the cofactor is a unit no separating point
is needed. -/
theorem irreducible_linear_in_X_zero_of_isUnit {A B : MvPolynomial (Fin n) K} (hA : IsUnit A) :
    Irreducible (MvPolynomial.X 0 * MvPolynomial.rename Fin.succ A +
      MvPolynomial.rename Fin.succ B) :=
  irreducible_linear_in_X_zero hA.ne_zero fun _ hrA _ => isUnit_of_dvd_unit hrA hA

/-! ## The matrix form -/

/-- **Irreducibility of a determinant from its corner.**  Suppose the first variable occupies one
entry of the first column and no other, the complementary minor is the image of an irreducible
polynomial in the remaining variables, and a specialisation of the ambient ring kills that minor but
not the determinant.  Then the determinant is irreducible. -/
theorem irreducible_det_of_corner_X_zero {S : Type*} [CommRing S] {N : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) (MvPolynomial (Fin (N + 1)) K)) (r₀ : Fin (n + 1))
    (hcorner : M r₀ 0 = MvPolynomial.X 0)
    (hfree : ∀ i j, ¬ (i = r₀ ∧ j = 0) → MvPolynomial.degreeOf 0 (M i j) = 0)
    {A : MvPolynomial (Fin N) K}
    (hminor : (M.submatrix r₀.succAbove Fin.succ).det = MvPolynomial.rename Fin.succ A)
    (hAirr : Irreducible A)
    {φ : MvPolynomial (Fin N) K →+* S} {ψ : MvPolynomial (Fin (N + 1)) K →+* S}
    (hcomp : ∀ p : MvPolynomial (Fin N) K, ψ (MvPolynomial.rename Fin.succ p) = φ p)
    (hA0 : φ A = 0) (hdet0 : ψ M.det ≠ 0) :
    Irreducible M.det := by
  obtain ⟨C, hCdeg, hdet⟩ := det_eq_corner_mul_minor_add M 0 r₀ (by rw [hcorner]) hfree
  obtain ⟨B, hCB⟩ := exists_rename_succ_of_degreeOf_zero hCdeg
  have hB0 : φ B ≠ 0 := by
    intro hcon
    refine hdet0 ?_
    rw [hdet, hminor, hCB, map_add, map_mul, map_mul, hcomp, hA0, mul_zero,
      hcomp, hcon, add_zero]
  rw [hdet, hminor, hCB] at *
  set u : (MvPolynomial (Fin (N + 1)) K)ˣ := (-1 : (MvPolynomial (Fin (N + 1)) K)ˣ) ^ (r₀ : ℕ)
    with hu
  have hucoe : (u : MvPolynomial (Fin (N + 1)) K) =
      (-1 : MvPolynomial (Fin (N + 1)) K) ^ (r₀ : ℕ) := by
    rw [hu, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
  refine irreducible_of_corner_expansion (u := u) ?_ hAirr φ hA0
    (B := (-1 : MvPolynomial (Fin N) K) ^ (r₀ : ℕ) * B) ?_
  · rw [hucoe, map_mul, map_pow, map_neg, map_one]
    ring_nf
    rw [show (r₀ : ℕ) * 2 = 2 * (r₀ : ℕ) from Nat.mul_comm _ _, pow_mul, neg_one_sq, one_pow]
    ring
  · rw [map_mul, map_pow, map_neg, map_one]
    intro hcon
    refine hB0 ?_
    have h2 : ((-1 : S) ^ (r₀ : ℕ)) * ((-1 : S) ^ (r₀ : ℕ) * φ B) = 0 := by
      rw [hcon, mul_zero]
    rwa [← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul] at h2

/-- **Irreducibility of a determinant whose corner minor is a unit.**  No separating point is
needed: a linear polynomial with unit leading coefficient is irreducible. -/
theorem irreducible_det_of_corner_X_zero_of_isUnit {N : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) (MvPolynomial (Fin (N + 1)) K)) (r₀ : Fin (n + 1))
    (hcorner : M r₀ 0 = MvPolynomial.X 0)
    (hfree : ∀ i j, ¬ (i = r₀ ∧ j = 0) → MvPolynomial.degreeOf 0 (M i j) = 0)
    {A : MvPolynomial (Fin N) K}
    (hminor : (M.submatrix r₀.succAbove Fin.succ).det = MvPolynomial.rename Fin.succ A)
    (hAunit : IsUnit A) :
    Irreducible M.det := by
  obtain ⟨C, hCdeg, hdet⟩ := det_eq_corner_mul_minor_add M 0 r₀ (by rw [hcorner]) hfree
  obtain ⟨B, hCB⟩ := exists_rename_succ_of_degreeOf_zero hCdeg
  rw [hdet, hminor, hCB]
  set u : (MvPolynomial (Fin (N + 1)) K)ˣ := (-1 : (MvPolynomial (Fin (N + 1)) K)ˣ) ^ (r₀ : ℕ)
    with hu
  have hucoe : (u : MvPolynomial (Fin (N + 1)) K) =
      (-1 : MvPolynomial (Fin (N + 1)) K) ^ (r₀ : ℕ) := by
    rw [hu, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
  refine (irreducible_units_mul u).1 ?_
  have hEq : (u : MvPolynomial (Fin (N + 1)) K) *
      ((-1 : MvPolynomial (Fin (N + 1)) K) ^ (r₀ : ℕ) * MvPolynomial.X 0 *
        MvPolynomial.rename Fin.succ A + MvPolynomial.rename Fin.succ B) =
      MvPolynomial.X 0 * MvPolynomial.rename Fin.succ A +
        MvPolynomial.rename Fin.succ ((-1 : MvPolynomial (Fin N) K) ^ (r₀ : ℕ) * B) := by
    rw [hucoe, map_mul, map_pow, map_neg, map_one]
    ring_nf
    rw [show (r₀ : ℕ) * 2 = 2 * (r₀ : ℕ) from Nat.mul_comm _ _, pow_mul, neg_one_sq, one_pow]
    ring
  rw [hEq]
  exact irreducible_linear_in_X_zero_of_isUnit hAunit

end GaloisForLFunctions.HTGeometry
