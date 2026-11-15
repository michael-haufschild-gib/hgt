import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerCartierLowerMonomials
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerDerivationExt

/-!
# Coordinate-free normalization of Frobenius coefficient extraction

The map `t ↦ C(t^(p-1) dt)` satisfies the product rule. Its invariance
under adding one follows by integrating every lower binomial term.
Factoring `a+b=a(1+b/a)` then gives additivity. This is a derivation
agreeing with the universal derivation on the separating coordinate,
so it equals that derivation on the whole field.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ)
local notation "K" => SquareConstantField p s
local notation "L" => SquareKummerField p s c b R
local notation "Ω" => KaehlerDifferential K L
local notation "D" => KaehlerDifferential.D K L
local notation "C" => squareKummerCoordinateCartier p s c b R

private def cartierNormalized (t : L) : Ω := C (t ^ (p - 1) • D t)

private theorem cartierNormalized_mul (a t : L) :
    cartierNormalized p s c b R (a * t) =
      a • cartierNormalized p s c b R t + t • cartierNormalized p s c b R a := by
  have hp : p - 1 + 1 = p := Nat.sub_add_cancel (Fact.out : p.Prime).pos
  have ha : a ^ p = a ^ (p - 1) * a :=
    (congrArg (fun j : ℕ => a ^ j) hp).symm.trans (pow_succ a (p - 1))
  have ht : t ^ p = t ^ (p - 1) * t :=
    (congrArg (fun j : ℕ => t ^ j) hp).symm.trans (pow_succ t (p - 1))
  have hprod : (a * t) ^ (p - 1) • D (a * t) =
      a ^ p • (t ^ (p - 1) • D t) + t ^ p • (a ^ (p - 1) • D a) := by
    simp only [D.leibniz, mul_pow, smul_add, smul_smul, ha, ht]
    congr 1 <;> congr 1 <;> ring
  change C ((a * t) ^ (p - 1) • D (a * t)) = _
  rw [hprod, map_add, squareKummerCoordinateCartier_frobenius_smul,
    squareKummerCoordinateCartier_frobenius_smul]
  rfl

private theorem cartierNormalized_one_add (t : L) :
    cartierNormalized p s c b R (1 + t) = cartierNormalized p s c b R t := by
  classical
  have hsum : cartierNormalized p s c b R (1 + t) =
      ∑ i ∈ Finset.range (p - 1 + 1), (p - 1).choose i • C (t ^ i • D t) := by
    change C ((1 + t) ^ (p - 1) • D (1 + t)) = _
    rw [map_add, D.map_one_eq_zero, zero_add, add_comm (1 : L) t,
      add_pow, Finset.sum_smul, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [one_pow, mul_one, mul_comm (t ^ i) (((p - 1).choose i : ℕ) : L),
      mul_smul, Nat.cast_smul_eq_nsmul, map_nsmul]
  rw [hsum, Finset.sum_eq_single (p - 1)]
  · rw [Nat.choose_self, one_nsmul]
    rfl
  · intro i hi hine
    have hilt : i < p - 1 := by
      have hi' := Finset.mem_range.mp hi
      omega
    rw [squareKummerCoordinateCartier_lower_monomial p s c b R t i hilt, nsmul_zero]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr (Nat.lt_succ_self _))).elim

private theorem cartierNormalized_add (a t : L) :
    cartierNormalized p s c b R (a + t) =
      cartierNormalized p s c b R a + cartierNormalized p s c b R t := by
  by_cases ha : a = 0
  · subst a
    simp only [cartierNormalized, zero_add, map_zero, smul_zero, add_zero]
  · have hdiv : a * (t / a) = t := by
      rw [mul_comm a (t / a), div_mul_cancel₀ _ ha]
    have hone : a * (1 + t / a) = a + t := by rw [mul_add, mul_one, hdiv]
    have h₁ := cartierNormalized_mul p s c b R a (1 + t / a)
    have h₂ := cartierNormalized_mul p s c b R a (t / a)
    rw [hone, cartierNormalized_one_add, add_smul, one_smul] at h₁
    rw [hdiv] at h₂
    calc
      cartierNormalized p s c b R (a + t) =
          a • cartierNormalized p s c b R (t / a) +
            (cartierNormalized p s c b R a + (t / a) • cartierNormalized p s c b R a) := h₁
      _ = cartierNormalized p s c b R a +
          (a • cartierNormalized p s c b R (t / a) +
            (t / a) • cartierNormalized p s c b R a) := by ac_rfl
      _ = cartierNormalized p s c b R a + cartierNormalized p s c b R t := by rw [← h₂]

private theorem cartierNormalized_constant (a : K) :
    cartierNormalized p s c b R (algebraMap K L a) = 0 := by
  rw [cartierNormalized, D.map_algebraMap, smul_zero, map_zero]

private def cartierNormalizedDerivation : Derivation K L Ω where
  toFun := cartierNormalized p s c b R
  map_add' := cartierNormalized_add p s c b R
  map_smul' a t := by
    rw [Algebra.smul_def, cartierNormalized_mul, cartierNormalized_constant,
      smul_zero, add_zero, IsScalarTower.algebraMap_smul]
  map_one_eq_zero' := by
    rw [cartierNormalized, D.map_one_eq_zero, smul_zero, map_zero]
  leibniz' := cartierNormalized_mul p s c b R

/-- Coefficient extraction has the Cartier normalization on every function, independently of coordinates. -/
theorem squareKummerCoordinateCartier_normalization (t : L) :
    squareKummerCoordinateCartier p s c b R (t ^ (p - 1) • D t) = D t := by
  let j : Fin p := ⟨p - 1, Nat.sub_lt (Fact.out : p.Prime).pos Nat.zero_lt_one⟩
  have heq : cartierNormalizedDerivation p s c b R = D := by
    apply squareKummer_derivation_ext p s c b R
    change C ((algebraMap K[X] L X) ^ j.val • D (algebraMap K[X] L X)) =
      D (algebraMap K[X] L X)
    rw [squareKummerCoordinateCartier_power, if_pos (show j.val = p - 1 from rfl)]
  exact Derivation.congr_fun heq t

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
