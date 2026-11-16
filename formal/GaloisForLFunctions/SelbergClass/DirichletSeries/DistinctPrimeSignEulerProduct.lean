import GaloisForLFunctions.SelbergClass.DirichletSeries.DistinctPrimeSign
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.Tactic.FieldSimp

/-!
# The Euler product of the distinct-prime sign series

The coefficients have absolute value one at positive integers. Absolute
convergence therefore holds on `Re s > 1`. Every positive prime power has
coefficient minus one, giving the local factor `(1 - 2p⁻ˢ)/(1 - p⁻ˢ)`.
-/

noncomputable section
namespace GaloisForLFunctions.SelbergClass

/-- Distinct-prime signs are uniformly bounded, including the zero convention. -/
theorem norm_distinctPrimeSign_le_one (n : ℕ) : ‖(distinctPrimeSign n : ℂ)‖ ≤ 1 := by
  cases n with
  | zero => simp
  | succ n =>
      rw [distinctPrimeSign_succ]
      simp only [Int.cast_pow, Int.cast_neg, Int.cast_one, norm_pow, norm_neg,
        norm_one, one_pow, le_refl]

/-- Absolute convergence of the actual arithmetic Dirichlet series. -/
theorem lSeriesSummable_distinctPrimeSign {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (distinctPrimeSign n : ℂ)) s := by
  apply LSeriesSummable_of_le_const_mul_rpow (x := 1) hs
  refine ⟨1, fun n _ => ?_⟩
  simpa only [sub_self, Real.rpow_zero, one_mul] using norm_distinctPrimeSign_le_one n

private theorem distinctPrimeSign_prime_pow_succ (p : Nat.Primes) (k : ℕ) :
    distinctPrimeSign ((p : ℕ) ^ (k + 1)) = -1 := by
  rw [distinctPrimeSign, ArithmeticFunction.prodPrimeFactors_apply
    (pow_ne_zero _ p.prop.ne_zero), Nat.primeFactors_prime_pow (by omega) p.prop,
    Finset.prod_singleton]

private theorem natCast_pow_cpow_neg (p k : ℕ) (s : ℂ) :
    (((p ^ k : ℕ) : ℂ) ^ (-s)) = ((p : ℂ) ^ (-s)) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, ih, pow_succ]

/-- The Euler product is obtained from the arithmetic coefficients, with all convergence
conditions discharged by their unit bound. -/
theorem distinctPrimeSign_eulerProduct_hasProd {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes =>
      (1 - 2 * (p : ℂ) ^ (-s)) / (1 - (p : ℂ) ^ (-s)))
      (LSeries (fun n => (distinctPrimeSign n : ℂ)) s) := by
  let f : ℕ → ℂ := LSeries.term (fun n => (distinctPrimeSign n : ℂ)) s
  have hterm (n : ℕ) : f n = (distinctPrimeSign n : ℂ) * (n : ℂ) ^ (-s) :=
    LSeries.term_def₀ (by simp) s n
  have hf1 : f 1 = 1 := by
    rw [hterm, distinctPrimeSign_isMultiplicative.map_one]
    simp
  have hmul : ∀ {m n : ℕ}, m.Coprime n → f (m * n) = f m * f n := by
    intro m n hmn
    simp only [hterm, distinctPrimeSign_isMultiplicative.map_mul_of_coprime hmn,
      Int.cast_mul, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
    ring
  have hsum : Summable fun n => ‖f n‖ :=
    summable_norm_iff.mpr (lSeriesSummable_distinctPrimeSign hs)
  have hf0 : f 0 = 0 := by simp [f]
  apply (EulerProduct.eulerProduct_hasProd hf1 hmul hsum hf0).congr_fun
  intro p
  have hx : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos p.prop.pos, Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast p.prop.one_lt) (by linarith only [hs])
  have hd : 1 - (p : ℂ) ^ (-s) ≠ 0 := by
    intro h
    rw [← sub_eq_zero.mp h, norm_one] at hx
    exact lt_irrefl _ hx
  have hlocal : Summable fun k : ℕ => f ((p : ℕ) ^ k) :=
    (hsum.comp_injective (Nat.pow_right_injective p.prop.two_le)).of_norm
  rw [hlocal.tsum_eq_zero_add, pow_zero, hf1]
  have htail (k : ℕ) : f ((p : ℕ) ^ (k + 1)) =
      -((p : ℂ) ^ (-s)) * ((p : ℂ) ^ (-s)) ^ k := by
    rw [hterm, distinctPrimeSign_prime_pow_succ, natCast_pow_cpow_neg, pow_succ]
    push_cast
    ring
  simp_rw [htail]
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hx]
  field_simp
  ring

#print axioms lSeriesSummable_distinctPrimeSign
#print axioms distinctPrimeSign_eulerProduct_hasProd
end GaloisForLFunctions.SelbergClass
