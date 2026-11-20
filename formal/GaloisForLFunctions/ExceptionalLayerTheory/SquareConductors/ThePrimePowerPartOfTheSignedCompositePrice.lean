import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheNearDiagonalFactorPairsInTheUnitaryMidpoint
import GaloisForLFunctions.RHTower.MobiusDivisorSectionSignLaw

/-!
# The signed midpoint price on an exact prime-power class

Fix a full block b=p^a. Removing it changes the weighted summatory
problem into two ordinary factor-sign sums on the same coprime region
d < e < b d, with d e bounded by the cofactor cutoff. Opposite signs
cancel within each factorization before any summation over conductors.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Price of an ordered cofactor pair in the fixed prime-power class.
The two signs occur separately, one on each arithmetic variable. -/
def unitaryFactorPairPrice (p b : ℕ) (w : ℕ → ℝ) (d e : ℕ) : ℝ :=
  if ¬p∣d*e ∧ d.Coprime e ∧ d<e ∧ e<b*d then
    w (b*(d*e))*((-1:ℝ)^d.primeFactors.card+(-1:ℝ)^e.primeFactors.card)
  else 0

private theorem ordered_strip_set {n b : ℕ} (hb : 0<b) :
    (nearDiagonalUnitaryFactors b n).filter (fun d => d<n/d)=
      n.divisors.filter (fun d => d.Coprime (n/d) ∧ d<n/d ∧ n/d<b*d) := by
  ext d
  simp only [nearDiagonalUnitaryFactors,mem_filter]
  constructor
  · rintro ⟨⟨div,cop,_,hi⟩,lt⟩
    exact ⟨div,cop,lt,hi⟩
  · rintro ⟨div,cop,lt,hi⟩
    exact ⟨⟨div,cop,lt.trans_le (Nat.le_mul_of_pos_left _ hb),hi⟩,lt⟩

private theorem price_on_cofactor {p a n : ℕ} (hp : p.Prime) (ha : 0<a)
    (hn : 0<n) (w : ℕ → ℝ) :
    (if 1<n ∧ ¬p∣n then w (p^a*n)*(unitaryHalfWeight (p^a*n):ℝ) else 0)=
      ∑ d ∈ n.divisors,unitaryFactorPairPrice p (p^a) w d (n/d) := by
  rcases (show 1≤n from hn).eq_or_lt with h|more
  · rw [←h]
    simp [unitaryFactorPairPrice]
  by_cases divides : p∣n
  · rw [if_neg (fun h => h.2 divides)]
    symm
    apply sum_eq_zero
    intro d hd
    simp only [unitaryFactorPairPrice,Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd),divides,
      not_true_eq_false,false_and,if_false]
  have pos := pow_pos hp.pos a
  have prime : p∈(p^a*n).primeFactors := Nat.mem_primeFactors.mpr ⟨hp,
    (dvd_pow_self p ha.ne').trans (dvd_mul_right _ _),(Nat.mul_pos pos hn).ne'⟩
  have fac : (p^a*n).factorization p=a := by
    rw [Nat.factorization_mul pos.ne' hn.ne',Finsupp.add_apply,Nat.factorization_pow_self hp,
      Nat.factorization_eq_zero_of_not_dvd divides,add_zero]
  have cof := Nat.ordCompl_pow_mul_of_not_dvd a hp divides
  have pair := unitary_midpoint_sum_of_factor_signs prime (cof.symm ▸ more)
  simp only [cof,fac] at pair
  rw [if_pos ⟨more,divides⟩,pair,Int.cast_sum,mul_sum,ordered_strip_set pos,sum_filter]
  refine sum_congr rfl fun d hd => ?_
  have mult := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
  simp only [unitaryFactorPairPrice,mult,divides,not_false_eq_true,true_and,
    Int.cast_add,Int.cast_pow,Int.cast_neg,Int.cast_one]

/-- For any real conductor weight, the complete contribution with exact
p-power p^a and nonunit cofactor up to T is a signed hyperbola sum. The
prime-count signs are separated on its two factors. -/
theorem fixed_prime_power_unitary_price_on_factor_pairs {p a : ℕ} (hp : p.Prime)
    (ha : 0<a) (T : ℕ) (w : ℕ → ℝ) :
    (∑ n ∈ Icc 1 T, if 1<n ∧ ¬p∣n then w (p^a*n)*(unitaryHalfWeight (p^a*n):ℝ) else 0)=
      ∑ d ∈ Icc 1 T, ∑ e ∈ Icc 1 (T/d),unitaryFactorPairPrice p (p^a) w d e := by
  let f := unitaryFactorPairPrice p (p^a) w
  calc _ = ∑ n ∈ Icc 1 T,∑ d ∈ n.divisors, f d (n/d) :=
             sum_congr rfl fun n hn => price_on_cofactor hp ha (mem_Icc.mp hn).1 w
       _ = ∑ d ∈ Icc 1 T,∑ e ∈ Icc 1 (T/d), f d ((d*e)/d) :=
             (_root_.RHTower.sum_Icc_sum_Icc_div_eq_sum_divisors T (fun d n => f d (n/d))).symm
       _ = _ := by
             apply sum_congr rfl
             intro d hd
             apply sum_congr rfl
             intro e _
             rw [Nat.mul_div_cancel_left e (mem_Icc.mp hd).1]

/-- With the larger cofactor as the inner variable the exact upper endpoint
is the smaller of b d − 1 and the hyperbola cutoff. The only inner
arithmetic restriction is coprimality to p d. -/
theorem fixed_prime_power_unitary_price_in_intervals {p a : ℕ} (hp : p.Prime)
    (ha : 0<a) (T : ℕ) (w : ℕ → ℝ) :
    (∑ n ∈ Icc 1 T, if 1<n ∧ ¬p∣n then w (p^a*n)*(unitaryHalfWeight (p^a*n):ℝ) else 0)=
      ∑ d ∈ (Icc 1 T.sqrt).filter (fun d => ¬p∣d),
        ∑ e ∈ (Ioc d (min (p^a*d-1) (T/d))).filter (fun e => (p*d).Coprime e),
          w (p^a*(d*e))*((-1:ℝ)^d.primeFactors.card+(-1:ℝ)^e.primeFactors.card) := by
  let b := p^a
  let D := (Icc 1 T.sqrt).filter (fun d => ¬p∣d)
  have sub : D⊆Icc 1 T := by
    intro d hd
    obtain ⟨lo,hi⟩ := mem_Icc.mp (mem_filter.mp hd).1
    exact mem_Icc.mpr ⟨lo,hi.trans (Nat.sqrt_le_self T)⟩
  rw [fixed_prime_power_unitary_price_on_factor_pairs hp ha]
  calc _ = ∑ d ∈ D,∑ e ∈ Icc 1 (T/d),unitaryFactorPairPrice p b w d e := by
             symm
             apply sum_subset sub
             intro d hd out
             apply sum_eq_zero
             intro e he
             apply if_neg
             rintro ⟨nodiv,_,less,_⟩
             have prime : ¬p∣d := fun h => nodiv (h.trans (dvd_mul_right d e))
             have area := (Nat.mul_le_mul_left d (mem_Icc.mp he).2).trans (Nat.mul_div_le T d)
             have side := Nat.le_sqrt.mpr ((Nat.mul_le_mul_left d less.le).trans area)
             exact out (mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp hd).1,side⟩,prime⟩)
       _ = _ := by
             apply sum_congr rfl
             intro d hd
             obtain ⟨rangeD,prime⟩ := mem_filter.mp hd
             have dp := (mem_Icc.mp rangeD).1
             have bp : 0<b*d := Nat.mul_pos (pow_pos hp.pos a) dp
             have prod (e : ℕ) : (¬p∣d*e) ↔ ¬p∣e := by rw [hp.dvd_mul]; simp only [prime,false_or]
             have inner_factors :
                 (Icc 1 (T/d)).filter (fun e => ¬p∣d*e ∧ d.Coprime e ∧ d<e ∧ e<b*d)=
                 (Ioc d (min (b*d-1) (T/d))).filter (fun e => (p*d).Coprime e) := by
               ext e
               simp only [mem_filter,mem_Icc,mem_Ioc,le_min_iff,Nat.coprime_mul_iff_left,
                 hp.coprime_iff_not_dvd,prod]
               constructor
               · rintro ⟨⟨_,cap⟩,excluded,cop,small,large⟩
                 exact ⟨⟨small,by omega,cap⟩,excluded,cop⟩
               · rintro ⟨⟨small,large,cap⟩,excluded,cop⟩
                 exact ⟨⟨by omega,cap⟩,excluded,cop,small,by omega⟩
             simp only [unitaryFactorPairPrice]
             rw [←sum_filter,inner_factors]

#print axioms fixed_prime_power_unitary_price_in_intervals
#print axioms fixed_prime_power_unitary_price_on_factor_pairs
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
