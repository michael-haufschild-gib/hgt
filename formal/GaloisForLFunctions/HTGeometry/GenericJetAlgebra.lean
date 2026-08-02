import GaloisForLFunctions.HTGeometry.TruncatedReciprocalRecurrence
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The generic jet algebra and its specialisations

The generic jet of horizon `N` is the polynomial algebra on the raw coefficients `x_0, …, x_N` with
the constant term inverted.  Its reciprocal coefficients are defined by the inverse recursion, and a
specialisation of the raw coefficients to those of an actual jet — one whose constant term is a unit
— carries the generic reciprocal coefficients to the actual ones.

The point is that both sides satisfy the *same* recursion from the same initial value: the generic
side by definition, the actual side because a product that is one over the horizon has the
convolution identity in every degree below it.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable (K : Type*) [Field K] (N : ℕ)

/-- The polynomial algebra on the raw coefficients of a jet of horizon `N`. -/
abbrev genericJetRing : Type _ := MvPolynomial (Fin (N + 1)) K

/-- The generic jet algebra: the raw coefficients with the constant term inverted. -/
abbrev genericJetAlgebra : Type _ :=
  Localization.Away (MvPolynomial.X (0 : Fin (N + 1)) : genericJetRing K N)

/-- The generic raw coefficients, extended by zero beyond the horizon. -/
noncomputable def genericRaw (j : ℕ) : genericJetAlgebra K N :=
  if h : j < N + 1 then
    algebraMap (genericJetRing K N) (genericJetAlgebra K N) (MvPolynomial.X ⟨j, h⟩)
  else 0

/-- The inverse of the generic constant term. -/
noncomputable def genericInv : genericJetAlgebra K N :=
  IsLocalization.Away.invSelf (MvPolynomial.X (0 : Fin (N + 1)) : genericJetRing K N)

theorem genericRaw_zero_mul_inv : genericRaw K N 0 * genericInv K N = 1 := by
  rw [genericRaw, dif_pos (by omega : 0 < N + 1), genericInv]
  have : (⟨0, by omega⟩ : Fin (N + 1)) = 0 := rfl
  rw [this]
  exact IsLocalization.Away.mul_invSelf _

/-- The generic reciprocal coefficients, by the inverse recursion. -/
noncomputable def genericRecip : ℕ → genericJetAlgebra K N
  | 0 => genericInv K N
  | (k + 1) => -(genericInv K N) * ∑ i ∈ Finset.range (k + 1),
      genericRaw K N (i + 1) * genericRecip (k - i)
  termination_by k => k
  decreasing_by omega

variable {K N}

/-- A specialisation of the generic jet algebra at an actual jet with unit constant term. -/
noncomputable def jetLift {M : Type*} [CommRing M] [Algebra K M] (a : Fin (N + 1) → M)
    (h : IsUnit (a 0)) : genericJetAlgebra K N →+* M :=
  IsLocalization.Away.lift (MvPolynomial.X (0 : Fin (N + 1)) : genericJetRing K N)
    (g := (MvPolynomial.aeval a : genericJetRing K N →ₐ[K] M).toRingHom)
    (by simpa using h)

theorem jetLift_algebraMap {M : Type*} [CommRing M] [Algebra K M] (a : Fin (N + 1) → M)
    (h : IsUnit (a 0)) (p : genericJetRing K N) :
    jetLift a h (algebraMap (genericJetRing K N) (genericJetAlgebra K N) p)
      = MvPolynomial.aeval a p :=
  IsLocalization.Away.lift_eq _ _ p

theorem jetLift_algebraMap_base {M : Type*} [CommRing M] [Algebra K M] (a : Fin (N + 1) → M)
    (h : IsUnit (a 0)) (k : K) :
    jetLift a h (algebraMap K (genericJetAlgebra K N) k) = algebraMap K M k := by
  have hstep : (algebraMap K (genericJetAlgebra K N)) k
      = algebraMap (genericJetRing K N) (genericJetAlgebra K N)
        (algebraMap K (genericJetRing K N) k) := by
    rw [IsScalarTower.algebraMap_apply K (genericJetRing K N) (genericJetAlgebra K N)]
  rw [hstep, jetLift_algebraMap, MvPolynomial.algebraMap_eq, MvPolynomial.aeval_C]

/-- The specialisation as an algebra map over the coefficient field. -/
noncomputable def jetLiftₐ {M : Type*} [CommRing M] [Algebra K M] (a : Fin (N + 1) → M)
    (h : IsUnit (a 0)) : genericJetAlgebra K N →ₐ[K] M :=
  { jetLift a h with commutes' := jetLift_algebraMap_base a h }

@[simp] theorem jetLiftₐ_apply {M : Type*} [CommRing M] [Algebra K M] (a : Fin (N + 1) → M)
    (h : IsUnit (a 0)) (x : genericJetAlgebra K N) : jetLiftₐ a h x = jetLift a h x := rfl

theorem jetLift_genericRaw {M : Type*} [CommRing M] [Algebra K M] (a : Fin (N + 1) → M)
    (h : IsUnit (a 0)) {j : ℕ} (hj : j < N + 1) :
    jetLift a h (genericRaw K N j) = a ⟨j, hj⟩ := by
  rw [genericRaw, dif_pos hj, jetLift_algebraMap, MvPolynomial.aeval_X]

theorem jetLift_genericRaw_of_le {M : Type*} [CommRing M] [Algebra K M] (a : Fin (N + 1) → M)
    (h : IsUnit (a 0)) {j : ℕ} (hj : ¬ j < N + 1) :
    jetLift a h (genericRaw K N j) = 0 := by
  rw [genericRaw, dif_neg hj, map_zero]

theorem jetLift_genericInv_mul {M : Type*} [CommRing M] [Algebra K M] (a : Fin (N + 1) → M)
    (h : IsUnit (a 0)) : jetLift a h (genericInv K N) * a 0 = 1 := by
  have hmul := congrArg (jetLift a h) (genericRaw_zero_mul_inv K N)
  rw [map_mul, map_one, jetLift_genericRaw a h (by omega : 0 < N + 1)] at hmul
  have h0 : (⟨0, by omega⟩ : Fin (N + 1)) = 0 := rfl
  rw [h0] at hmul
  rw [mul_comm]
  exact hmul

/-- **A specialisation carries the generic reciprocal coefficients to the actual ones.** -/
theorem jetLift_genericRecip {M : Type*} [CommRing M] [Algebra K M] {Z W : M[X]}
    (hZW : (X : M[X]) ^ (N + 1) ∣ Z * W - 1) (h : IsUnit (Z.coeff 0)) :
    ∀ k : ℕ, k ≤ N →
      jetLift (K := K) (fun j : Fin (N + 1) => Z.coeff (j : ℕ)) (by simpa using h) (genericRecip K N k)
        = W.coeff k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    set a : Fin (N + 1) → M := fun j => Z.coeff (j : ℕ) with ha
    have ha0 : a 0 = Z.coeff 0 := rfl
    have hu : IsUnit (a 0) := by rw [ha0]; exact h
    match k with
    | 0 =>
        have hinv := jetLift_genericInv_mul (K := K) a hu
        rw [ha0] at hinv
        have hW := coeff_zero_mul_of_dvd hZW
        have : jetLift (K := K) a hu (genericRecip K N 0) * Z.coeff 0 = W.coeff 0 * Z.coeff 0 := by
          rw [genericRecip, hinv, mul_comm (W.coeff 0), hW]
        calc jetLift (K := K) a hu (genericRecip K N 0)
            = jetLift (K := K) a hu (genericRecip K N 0) * (Z.coeff 0 * W.coeff 0) := by
              rw [hW, mul_one]
          _ = (jetLift (K := K) a hu (genericRecip K N 0) * Z.coeff 0) * W.coeff 0 := by ring
          _ = (W.coeff 0 * Z.coeff 0) * W.coeff 0 := by rw [this]
          _ = W.coeff 0 * (Z.coeff 0 * W.coeff 0) := by ring
          _ = W.coeff 0 := by rw [hW, mul_one]
    | (j + 1) =>
        have hterm : ∀ i ∈ Finset.range (j + 1),
            jetLift (K := K) a hu (genericRaw K N (i + 1) * genericRecip K N (j - i))
              = Z.coeff (i + 1) * W.coeff (j - i) := by
          intro i hi
          have hij : i < j + 1 := Finset.mem_range.1 hi
          rw [map_mul, jetLift_genericRaw (K := K) a hu (by omega : i + 1 < N + 1),
            ih (j - i) (by omega) (by omega)]
        have hsum : jetLift (K := K) a hu (genericRecip K N (j + 1))
            = -(jetLift (K := K) a hu (genericInv K N))
              * ∑ i ∈ Finset.range (j + 1), Z.coeff (i + 1) * W.coeff (j - i) := by
          rw [genericRecip, map_mul, map_neg, map_sum, Finset.sum_congr rfl hterm]
        have hrec := coeff_zero_mul_coeff_of_dvd hZW (k := j + 1) hk (by omega)
        have hshift : ∀ i ∈ Finset.range (j + 1),
            Z.coeff (i + 1) * W.coeff (j + 1 - (i + 1)) = Z.coeff (i + 1) * W.coeff (j - i) := by
          intro i _
          congr 2
          omega
        rw [Finset.sum_congr rfl hshift] at hrec
        have hinv := jetLift_genericInv_mul (K := K) a hu
        rw [ha0] at hinv
        calc jetLift (K := K) a hu (genericRecip K N (j + 1))
            = -(jetLift (K := K) a hu (genericInv K N))
              * ∑ i ∈ Finset.range (j + 1), Z.coeff (i + 1) * W.coeff (j - i) := hsum
          _ = jetLift (K := K) a hu (genericInv K N) * (Z.coeff 0 * W.coeff (j + 1)) := by
              rw [hrec]
              ring
          _ = (jetLift (K := K) a hu (genericInv K N) * Z.coeff 0) * W.coeff (j + 1) := by ring
          _ = W.coeff (j + 1) := by rw [hinv, one_mul]

end GaloisForLFunctions.HTGeometry
