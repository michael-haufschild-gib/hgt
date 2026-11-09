import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Ideal
import GaloisForLFunctions.HTGeometry.DifferentialIndependence

/-!
# Integral polynomial jets and diagonal ideals

Over a characteristic-zero domain, ordinary polynomial jets detect powers
of a point ideal without dividing by factorials. The coefficient recursion
for a partial derivative cancels a positive integer at each step. This
applies when the coefficients themselves are integer polynomials, allowing
the evaluation point to be a tuple of indeterminates.
-/

open MvPolynomial
noncomputable section
namespace GaloisForLFunctions.ArithmeticLefschetzStepanovTheory

variable {σ R : Type*} [CommRing R]

/-- Ordered partial derivatives over an arbitrary coefficient ring. -/
def polynomialJetWord (L : List σ) : Module.End R (MvPolynomial σ R) :=
  L.foldr (fun j D => (pderiv j).toLinearMap * D) 1

theorem polynomialJetWord_nil (F : MvPolynomial σ R) : polynomialJetWord [] F = F := rfl

theorem polynomialJetWord_cons (j : σ) (L : List σ) (F : MvPolynomial σ R) :
    polynomialJetWord (j :: L) F = pderiv j (polynomialJetWord L F) := rfl

theorem polynomialJetWord_append (L K : List σ) (F : MvPolynomial σ R) :
    polynomialJetWord (L ++ K) F = polynomialJetWord L (polynomialJetWord K F) := by
  induction L with
  | nil => rfl
  | cons j L ih => exact congrArg (pderiv j) ih

/-- Vanishing of all polynomial derivatives below an order, with values in the coefficient ring. -/
def PolynomialVanishesToOrder (F : MvPolynomial σ R) (u : σ → R) (r : ℕ) : Prop :=
  ∀ L : List σ, L.length < r → eval u (polynomialJetWord L F) = 0

theorem polynomialVanishesToOrder_succ_iff (F : MvPolynomial σ R) (u : σ → R) (r : ℕ) :
    PolynomialVanishesToOrder F u (r + 1) ↔
      eval u F = 0 ∧ ∀ j, PolynomialVanishesToOrder (pderiv j F) u r := by
  constructor
  · intro h
    refine ⟨h [] (by simp), ?_⟩
    intro j L hL
    have hv := h (L ++ [j]) (by simp only [List.length_append, List.length_singleton]; omega)
    simpa only [polynomialJetWord_append, polynomialJetWord_cons, polynomialJetWord_nil] using hv
  · rintro ⟨h0, hd⟩ L hL
    induction L using List.reverseRecOn with
    | nil => exact h0
    | append_singleton L j _ =>
      rw [polynomialJetWord_append, polynomialJetWord_cons, polynomialJetWord_nil]
      exact hd j L (by simp only [List.length_append, List.length_singleton] at hL; omega)

section Domain

variable [NoZeroDivisors R] [CharZero R]

/-- The origin filtration is detected recursively by evaluation and partial derivatives. -/
theorem mem_originIdeal_pow_succ_iff (F : MvPolynomial σ R) (r : ℕ) :
    F ∈ idealOfVars σ R ^ (r + 1) ↔
      eval (fun _ => 0) F = 0 ∧ ∀ j, pderiv j F ∈ idealOfVars σ R ^ r := by
  rw [mem_pow_idealOfVars_iff']
  constructor
  · intro h
    constructor
    · simpa only [eval_zero', constantCoeff_eq] using h 0 (by simp)
    · intro j
      rw [mem_pow_idealOfVars_iff']
      intro a ha
      rw [coeff_pderiv, h (a + Finsupp.single j 1) (by
        simp only [map_add, Finsupp.degree_single]; omega), zero_mul]
  · rintro ⟨h0, hd⟩ a ha
    by_cases ha0 : a = 0
    · subst a
      simpa only [eval_zero', constantCoeff_eq] using h0
    · obtain ⟨j, hj⟩ : ∃ j, a j ≠ 0 := by
        by_contra h
        push Not at h
        exact ha0 (Finsupp.ext h)
      have hsplit := Finsupp.sub_add_single_one_cancel hj
      have hdeg : Finsupp.degree (a - Finsupp.single j 1) < r := by
        have he := congrArg Finsupp.degree hsplit
        simp only [map_add, Finsupp.degree_single] at he
        omega
      have hc := (mem_pow_idealOfVars_iff' r (pderiv j F)).mp (hd j)
        (a - Finsupp.single j 1) hdeg
      rw [coeff_pderiv, hsplit] at hc
      have hnat : ((a - Finsupp.single j 1) j : R) + 1 ≠ 0 := by
        exact_mod_cast (Nat.succ_ne_zero ((a - Finsupp.single j 1) j))
      exact (mul_eq_zero.mp hc).resolve_right hnat

/-- Integral ordinary jets detect the origin-ideal power exactly, with no denominator inversion. -/
theorem polynomialVanishesToOrder_zero_iff (F : MvPolynomial σ R) (r : ℕ) :
    PolynomialVanishesToOrder F (fun _ => 0) r ↔ F ∈ idealOfVars σ R ^ r := by
  induction r generalizing F with
  | zero =>
    constructor
    · intro _; simp only [pow_zero, Ideal.one_eq_top, Submodule.mem_top]
    · intro _ L hL; omega
  | succ r ih =>
    rw [polynomialVanishesToOrder_succ_iff, mem_originIdeal_pow_succ_iff]
    exact and_congr Iff.rfl (forall_congr' fun j => ih (pderiv j F))

end Domain

end GaloisForLFunctions.ArithmeticLefschetzStepanovTheory
