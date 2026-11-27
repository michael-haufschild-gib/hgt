import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Gibbs

/-! # Prime monomials and the exact Dirichlet certificate of a finite shell spectrum -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet

open Finset Real MvPolynomial

abbrev Exponent := Nat.Primes →₀ ℕ
abbrev PolynomialRing := MvPolynomial Nat.Primes ℤ

def coordinates (t : ℝ) (p : Nat.Primes) : ℝ := (p.val : ℝ)^t

def shellPower (t : ℝ) (n : ℕ+) : ℝ := (n.val : ℝ)^t

def value (t : ℝ) := (MvPolynomial.aeval (coordinates t) : PolynomialRing →ₐ[ℤ] ℝ)

theorem shellPower_exp (t : ℝ) (n : ℕ+) : shellPower t n = exp (t*energy n) := by
  rw [shellPower,rpow_def_of_pos (by exact_mod_cast n.pos),mul_comm]
  rfl

/-- Unique prime factorization identifies evaluation of a monomial with one shell power. -/
theorem monomial_power (v : Exponent) (t : ℝ) :
    v.prod (fun p k => coordinates t p ^ k) = shellPower t (label v) := by
  change (∏ p ∈ v.support, ((p.val : ℝ)^t)^(v p)) =
    ((↑(∏ p ∈ v.support, p.val^(v p) : ℕ) : ℝ)^t)
  rw [Nat.cast_prod,← finsetProd_rpow _ _ (fun _ _ => Nat.cast_nonneg _) t]
  refine prod_congr rfl fun p _ => ?_
  rw [Nat.cast_pow,← rpow_mul_natCast (by positivity),← rpow_natCast_mul (by positivity),mul_comm]

theorem value_sum (P : PolynomialRing) (t : ℝ) :
    value t P = ∑ v ∈ P.support, ((coeff v P : ℤ) : ℝ)*shellPower t (label v) := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  exact sum_congr rfl fun v _ => by rw [value,aeval_monomial,monomial_power]; rfl

/-- Rational Dirichlet linear independence is precisely algebraic independence
of the prime coordinates. The same identification holds over the integers. -/
theorem independent_iff (R : Type*) [CommRing R] [Algebra R ℝ] (t : ℝ) :
    AlgebraicIndependent R (coordinates t) ↔ LinearIndependent R (shellPower t) := by
  classical
  let b := basisMonomials Nat.Primes R
  let ev := (MvPolynomial.aeval (coordinates t) : MvPolynomial Nat.Primes R →ₐ[R] ℝ)
  have eval_basis (v : Exponent) : ev (b v)=shellPower t (label v) := by
    simp only [ev,b,coe_basisMonomials,aeval_monomial,map_one,one_mul,monomial_power]
  rw [← linearIndependent_equiv (R := R) label]
  constructor
  · intro h
    have lin := b.linearIndependent.map' ev.toLinearMap (LinearMap.ker_eq_bot.mpr h)
    simpa only [Function.comp_def,AlgHom.toLinearMap_apply,eval_basis] using lin
  · intro h
    apply algebraicIndependent_iff.mpr
    intro P zero
    have eq := zero
    conv_lhs at eq => rw [P.as_sum]
    simp only [map_sum,aeval_monomial,monomial_power,← Algebra.smul_def] at eq
    have gone := linearIndependent_iff'.mp h P.support (fun v => coeff v P) eq
    ext v
    by_cases hv : v ∈ P.support
    · simpa only [coeff_zero] using gone v hv
    · simpa only [coeff_zero] using not_ne_iff.mp (fun ne => hv (mem_support_iff.mpr ne))

def atom (n : ℕ+) : PolynomialRing := monomial (label.symm n) 1

theorem value_atom (n : ℕ+) (t : ℝ) : value t (atom n)=exp (t*energy n) := by
  simp only [atom,value,aeval_monomial,map_one,one_mul,monomial_power,Equiv.apply_symm_apply,shellPower_exp]

variable {I : Type*} [Fintype I]

/-- The difference left after clearing the fractional mean of the logarithmic energies. -/
def certificate (a : I → ℕ+) : PolynomialRing :=
  (∑ i, Radicals.except (atom ∘ a) i)^(Fintype.card I) -
    (∏ i, atom (a i))^(Fintype.card I-2)*(∑ i, atom (a i))^(Fintype.card I)

theorem certificate_root (a : I → ℕ+) (size : 2 ≤ Fintype.card I) (t : ℝ) :
    value t (certificate a)=0 ↔ agrees (energy ∘ a) t := by
  classical
  rw [agrees,Radicals.thermal_condition_iff _ _ size]
  simp only [certificate,map_sub,map_pow,map_sum,map_prod,map_mul,sub_eq_zero,
    Radicals.condition,Radicals.except,Function.comp_apply,value_atom]

theorem size_of_asymmetric (a : I → ℕ+) (h : ¬Reflects (energy ∘ a)) : 2 ≤ Fintype.card I := by
  by_contra! small
  exact h ((centered_heat_iff_reflects _).mp fun j _ _ => small_packet a (by omega) j)

theorem certificate_ne_zero (a : I → ℕ+) (h : ¬Reflects (energy ∘ a)) : certificate a ≠ 0 := by
  intro zero
  apply h
  apply (centered_heat_iff_reflects _).mp
  intro j _ _
  exact (certificate_root a (size_of_asymmetric a h) j).mp (by rw [zero,map_zero])

#print axioms independent_iff
#print axioms certificate_root
#print axioms certificate_ne_zero

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet
