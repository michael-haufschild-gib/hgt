import GaloisForLFunctions.RHTower.WeilKloostermanDegreeSums

/-!
# Power sums over monic polynomials

Separating a monic polynomial's constant coefficient gives an exact
binomial recurrence. The finite-field moment removes zero exponents and
all exponents not divisible by the multiplicative-group order.
-/

open Finset Polynomial
open GaloisForLFunctions.RHTower.WeilKloosterman
namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

variable (K : Type*) [Field K] [Fintype K]

/-- The moment of one coefficient over the finite field, including exponent zero. -/
def coefficientMoment (n : ℕ) : K :=
  if n = 0 then 0 else if Fintype.card K - 1 ∣ n then -1 else 0

theorem sum_pow_eq_coefficientMoment (n : ℕ) :
    (∑ a : K, a ^ n) = coefficientMoment K n := by
  classical
  by_cases hn : n = 0
  · subst n
    simp only [pow_zero, sum_const, card_univ, nsmul_one, coefficientMoment]
    exact FiniteField.cast_card_eq_zero K
  rw [coefficientMoment, if_neg hn]
  let φ : Kˣ ↪ K := ⟨fun x => x, Units.val_injective⟩
  have he : univ.map φ = univ \ {0} := by
    ext x
    simpa only [mem_map, mem_univ, Function.Embedding.coeFn_mk, true_and, mem_sdiff,
      mem_singleton, φ] using! isUnit_iff_ne_zero
  calc
    (∑ a : K, a ^ n) = ∑ a ∈ univ \ {(0 : K)}, a ^ n := by
      rw [← sum_sdiff ({0} : Finset K).subset_univ, sum_singleton, zero_pow hn, add_zero]
    _ = ∑ a : Kˣ, (a ^ n : K) := by simp only [← he, sum_map, φ, Function.Embedding.coeFn_mk]
    _ = _ := FiniteField.sum_pow_units K n

/-- Summing the constant translates of a polynomial selects the finite-field moments. -/
theorem sum_constant_translate_pow (f : K[X]) (n : ℕ) :
    (∑ a : K, (C a + f) ^ n) = ∑ j ∈ range (n + 1),
      C ((n.choose j : K) * coefficientMoment K j) * f ^ (n - j) := by
  classical
  simp_rw [add_pow]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  have hterm (a : K) : (C a) ^ j * f ^ (n - j) * (n.choose j : K[X]) =
      C (n.choose j : K) * f ^ (n - j) * C (a ^ j) := by
    rw [← C_pow, ← map_natCast (C : K →+* K[X])]
    ring
  simp_rw [hterm]
  rw [← mul_sum, ← map_sum, sum_pow_eq_coefficientMoment, map_mul]
  ring

variable [DecidableEq K]

/-- The actual polynomial power sum over all monic polynomials of degree `d`. -/
noncomputable def monicPowerSum (d n : ℕ) : K[X] := ∑ f ∈ monicDeg d, f ^ n

theorem monicPowerSum_eq_sum (d n : ℕ) :
    monicPowerSum K d n = ∑ a : Fin d → K, monicOf d a ^ n :=
  sum_monicDeg d (fun f => f ^ n)

omit [Fintype K] [DecidableEq K] in
theorem monicOf_cons (d : ℕ) (a : K) (b : Fin d → K) :
    monicOf (d + 1) (Fin.cons a b) = C a + X * monicOf d b := by
  have hsum : (∑ i : Fin d, C (b i) * (X : K[X]) ^ (i.val + 1)) =
      X * ∑ i : Fin d, C (b i) * (X : K[X]) ^ i.val := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    rw [pow_succ]
    ring
  simp only [monicOf, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.val_zero,
    Fin.val_succ, pow_zero, mul_one]
  rw [hsum, pow_succ]
  ring

theorem monicPowerSum_zero (n : ℕ) : monicPowerSum K 0 n = 1 := by
  rw [monicPowerSum_eq_sum]
  simp only [monicOf, pow_zero, Fin.sum_univ_zero, add_zero, one_pow, sum_const,
    card_univ, Fintype.card_fun, Fintype.card_fin, pow_zero, one_smul]

/-- Exact recurrence for the actual monic-polynomial power sums. -/
theorem monicPowerSum_succ (d n : ℕ) :
    monicPowerSum K (d + 1) n = ∑ j ∈ range (n + 1),
      C ((n.choose j : K) * coefficientMoment K j) * X ^ (n - j) *
        monicPowerSum K d (n - j) := by
  classical
  rw [monicPowerSum_eq_sum]
  let e := Fin.consEquiv (fun _ : Fin (d + 1) => K)
  have hsplit : (∑ a : Fin (d + 1) → K, monicOf (d + 1) a ^ n) =
      ∑ b : Fin d → K, ∑ a : K, (C a + X * monicOf d b) ^ n := by
    rw [← e.sum_comp, Fintype.sum_prod_type, sum_comm]
    apply sum_congr rfl
    intro b _
    apply sum_congr rfl
    intro a _
    change monicOf (d + 1) (Fin.cons a b) ^ n = _
    rw [monicOf_cons]
  rw [hsplit]
  simp_rw [sum_constant_translate_pow]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  simp_rw [mul_pow, ← mul_assoc]
  rw [← mul_sum, ← monicPowerSum_eq_sum]

end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.monicPowerSum_succ
