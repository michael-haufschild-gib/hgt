import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.IntegralDiagonalJets

/-!
# Euler jets detect integral point-ideal powers

At a coefficient-valued point with nonzero coordinates, multiplication by
each coordinate is regular on the truncated point algebra. Euler jets
therefore detect the same ideal powers as ordinary jets, even when the
coordinates are indeterminates rather than units of the coefficient ring.
-/

open MvPolynomial
noncomputable section
namespace GaloisForLFunctions.ArithmeticLefschetzStepanovTheory

variable {σ R : Type*} [CommRing R]

/-- The coordinate Euler derivation over the coefficient ring. -/
def polynomialEuler (j : σ) : Derivation R (MvPolynomial σ R) (MvPolynomial σ R) :=
  (X j : MvPolynomial σ R) • pderiv j

theorem polynomialEuler_apply (j : σ) (F : MvPolynomial σ R) :
    polynomialEuler j F = X j * pderiv j F := rfl

/-- An ordered word of coefficient-linear Euler derivations. -/
def polynomialEulerWord (L : List σ) : Module.End R (MvPolynomial σ R) :=
  L.foldr (fun j D => (polynomialEuler j).toLinearMap * D) 1

theorem polynomialEulerWord_nil (F : MvPolynomial σ R) : polynomialEulerWord [] F = F := rfl

theorem polynomialEulerWord_cons (j : σ) (L : List σ) (F : MvPolynomial σ R) :
    polynomialEulerWord (j :: L) F = polynomialEuler j (polynomialEulerWord L F) := rfl

theorem polynomialEulerWord_append (L K : List σ) (F : MvPolynomial σ R) :
    polynomialEulerWord (L ++ K) F = polynomialEulerWord L (polynomialEulerWord K F) := by
  induction L with
  | nil => rfl
  | cons j L ih => exact congrArg (polynomialEuler j) ih

theorem polynomialEuler_map {S : Type*} [CommRing S] (φ : R →+* S)
    (j : σ) (F : MvPolynomial σ R) :
    polynomialEuler j (MvPolynomial.map φ F) = MvPolynomial.map φ (polynomialEuler j F) := by
  rw [polynomialEuler_apply, pderiv_map, polynomialEuler_apply, map_mul, MvPolynomial.map_X]

theorem polynomialEulerWord_map {S : Type*} [CommRing S] (φ : R →+* S)
    (L : List σ) (F : MvPolynomial σ R) :
    polynomialEulerWord L (MvPolynomial.map φ F) = MvPolynomial.map φ (polynomialEulerWord L F) := by
  induction L with
  | nil => rfl
  | cons j L ih =>
    rw [polynomialEulerWord_cons, ih, polynomialEuler_map, polynomialEulerWord_cons]

theorem polynomialEulerWord_mul_C (L : List σ) (F : MvPolynomial σ R) (c : R) :
    polynomialEulerWord L (F * C c) = polynomialEulerWord L F * C c := by
  induction L with
  | nil => rfl
  | cons j L ih =>
    rw [polynomialEulerWord_cons, ih, polynomialEuler_apply, pderiv_mul, pderiv_C,
      mul_zero, add_zero, polynomialEulerWord_cons, polynomialEuler_apply]
    exact (mul_assoc _ _ _).symm

/-- Euler jet vanishing with values in the coefficient ring itself. -/
def PolynomialEulerVanishesToOrder (F : MvPolynomial σ R) (u : σ → R) (r : ℕ) : Prop :=
  ∀ L : List σ, L.length < r → eval u (polynomialEulerWord L F) = 0

theorem polynomialEulerVanishesToOrder_succ_iff (F : MvPolynomial σ R) (u : σ → R) (r : ℕ) :
    PolynomialEulerVanishesToOrder F u (r + 1) ↔
      eval u F = 0 ∧ ∀ j, PolynomialEulerVanishesToOrder (polynomialEuler j F) u r := by
  constructor
  · intro h
    refine ⟨h [] (by simp), ?_⟩
    intro j L hL
    have hv := h (L ++ [j]) (by simp only [List.length_append, List.length_singleton]; omega)
    simpa only [polynomialEulerWord_append, polynomialEulerWord_cons, polynomialEulerWord_nil] using hv
  · rintro ⟨h0, hd⟩ L hL
    induction L using List.reverseRecOn with
    | nil => exact h0
    | append_singleton L j _ =>
      rw [polynomialEulerWord_append, polynomialEulerWord_cons, polynomialEulerWord_nil]
      exact hd j L (by simp only [List.length_append, List.length_singleton] at hL; omega)

section Domain

variable [NoZeroDivisors R] [CharZero R]

theorem mem_polynomialPointIdeal_pow_succ_iff (u : σ → R) (F : MvPolynomial σ R) (r : ℕ) :
    F ∈ polynomialPointIdeal u ^ (r + 1) ↔
      eval u F = 0 ∧ ∀ j, pderiv j F ∈ polynomialPointIdeal u ^ r := by
  rw [← polynomialVanishesToOrder_iff_mem_pointIdeal_pow,
    polynomialVanishesToOrder_succ_iff]
  exact and_congr Iff.rfl
    (forall_congr' fun j => polynomialVanishesToOrder_iff_mem_pointIdeal_pow u (pderiv j F) r)

/-- Nonzero coefficient coordinates suffice for Euler jets to detect the full point-ideal power. -/
theorem polynomialEulerVanishesToOrder_iff_mem_pointIdeal_pow (u : σ → R)
    (hu : ∀ j, u j ≠ 0) (F : MvPolynomial σ R) (r : ℕ) :
    PolynomialEulerVanishesToOrder F u r ↔ F ∈ polynomialPointIdeal u ^ r := by
  induction r generalizing F with
  | zero =>
    constructor
    · intro _; simp only [pow_zero, Ideal.one_eq_top, Submodule.mem_top]
    · intro _ L hL; omega
  | succ r ih =>
    rw [polynomialEulerVanishesToOrder_succ_iff, mem_polynomialPointIdeal_pow_succ_iff]
    apply and_congr Iff.rfl
    apply forall_congr'
    intro j
    exact (ih (polynomialEuler j F)).trans
      (X_mul_mem_pointIdeal_pow_iff u j (hu j) (pderiv j F) r)

end Domain

#print axioms polynomialEulerVanishesToOrder_iff_mem_pointIdeal_pow

end GaloisForLFunctions.ArithmeticLefschetzStepanovTheory
