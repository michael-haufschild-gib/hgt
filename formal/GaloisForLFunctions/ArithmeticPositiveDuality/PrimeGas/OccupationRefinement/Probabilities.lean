import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.Profiles

/-! # Routing prime particles into two channels -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement

open Finset

/-- Classical probability of an ordered factorization of its product. -/
def probability (u v : ℝ) (a b : ℕ) := weight u a * weight v b / weight (u+v) (a*b)

theorem probability_pos {u v : ℝ} (hu : 0<u) (hv : 0<v) (a b : ℕ+) :
    0<probability u v a.val b.val :=
  div_pos (mul_pos (weight_pos u hu a) (weight_pos v hv b)) (weight_pos _ (add_pos hu hv) (a*b))

theorem probability_sum {u v : ℝ} (hu : 0<u) (hv : 0<v) (n : ℕ+) :
    ∑ d ∈ n.val.divisorsAntidiagonal, probability u v d.1 d.2=1 := by
  calc
    _ = (∑ d ∈ n.val.divisorsAntidiagonal, weight u d.1 * weight v d.2)/weight (u+v) n.val := by
      rw [Finset.sum_div]
      exact sum_congr rfl fun d hd => by rw [probability,(Nat.mem_divisorsAntidiagonal.mp hd).1]
    _ = 1 := by
      rw [←ArithmeticFunction.mul_apply,weight_add,div_self (weight_pos _ (add_pos hu hv) n).ne']

/-- Binomial weight for routing a total of j+k copies of one prime. -/
def binomial (u v : ℝ) (j k : ℕ) :=
  ((j+k).choose j : ℝ) * ((u/(u+v))^j * (v/(u+v))^k)

theorem local_probability {u v : ℝ} (hu : 0<u) (hv : 0<v) (j k : ℕ) :
    divided u j * divided v k / divided (u+v) (j+k) = binomial u v j k := by
  have fac (a : ℕ) : (a.factorial:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a)
  have C : ((j+k).choose j : ℝ)=((j+k).factorial:ℝ)/((j.factorial:ℝ)*(k.factorial:ℝ)) := by
    apply (eq_div_iff (mul_ne_zero (fac j) (fac k))).mpr
    rw [←mul_assoc]
    have count : (j+k).choose j * j.factorial * k.factorial = (j+k).factorial := by
      simpa only [Nat.add_sub_cancel_left] using
        Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right j k)
    exact_mod_cast count
  rw [binomial,C]
  simp only [divided,div_pow,pow_add]
  field_simp [fac,(add_pos hu hv).ne']

theorem prime_ray {u v : ℝ} (hu : 0<u) (hv : 0<v) (p : Nat.Primes) (j k : ℕ) :
    probability u v (p.val^j) (p.val^k)=binomial u v j k := by
  rw [probability,←pow_add]
  simp only [weight_prime_pow _ _ _ p.property]
  exact local_probability hu hv j k

private theorem weight_product (u : ℝ) (a : ℕ+) (S : Finset ℕ) (h : a.val.primeFactors ⊆ S) :
    weight u a.val=∏ p ∈ S, divided u (a.val.factorization p) := by
  have hlocal (p k : ℕ) :
      RHTower.Sieve.normalizedPrimePowerValue (fun _ j => divided u j) p k=divided u k := by
    by_cases hk : k=0
    · simp [RHTower.Sieve.normalizedPrimePowerValue,hk,divided]
    · simp [RHTower.Sieve.normalizedPrimePowerValue,hk]
  simpa only [weight,if_neg a.ne_zero,Finset.union_eq_left.mpr h,hlocal] using
    RHTower.Sieve.localEuler_eq_prod_on_union (fun _ j => divided u j) a.val S

/-- All prime species route independently, including repeated particles. -/
theorem prime_factorization {u v : ℝ} (hu : 0<u) (hv : 0<v) (a b : ℕ+) :
    probability u v a.val b.val =
      ∏ p ∈ a.val.primeFactors ∪ b.val.primeFactors,
        binomial u v (a.val.factorization p) (b.val.factorization p) := by
  let S := a.val.primeFactors ∪ b.val.primeFactors
  have factors : (a*b).val.primeFactors=S := Nat.primeFactors_mul a.ne_zero b.ne_zero
  have exps (p) : (a*b).val.factorization p=a.val.factorization p+b.val.factorization p := by
    rw [PNat.mul_coe,Nat.factorization_mul a.ne_zero b.ne_zero,Finsupp.add_apply]
  change weight u a.val * weight v b.val / weight (u+v) (a*b).val = ∏ p ∈ S, _
  rw [weight_product u a S subset_union_left,weight_product v b S subset_union_right,
    weight_product (u+v) (a*b) S factors.le,←prod_mul_distrib,←prod_div_distrib]
  exact prod_congr rfl fun p _ => by rw [exps,local_probability hu hv]

#print axioms probability_sum
#print axioms prime_ray
#print axioms prime_factorization

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement
