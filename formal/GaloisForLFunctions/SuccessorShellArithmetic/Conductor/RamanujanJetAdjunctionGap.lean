import GaloisForLFunctions.SuccessorShellArithmetic.TopBand.RamanujanDivisorPlancherel
import GaloisForLFunctions.ArithmeticPositiveDuality.TheCriticalLineIsThePositivityThresholdOfTheIntegerSuccessor

/-!
# The divisor jet is an adjunction-energy gap

A finite real-power deformation of the Ramanujan divisor sum satisfies
an exact Jordan-totient quotient identity. Möbius reindexing separates
precisely the primes absent from the lag quotient; no squarefree-modulus
restriction is needed.

Differentiating at exponent one identifies every logarithmic divisor jet
with its Ramanujan coefficient times the difference of the conductor's
adjunction energy and that of its reduced lag quotient.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta
namespace GaloisForLFunctions.SuccessorShellArithmetic
open BezoutValuationIncidence CriticalArithmeticCorrelationTheory
  ArithmeticIntersectionTheory ArithmeticPositiveDuality
noncomputable section


private theorem moebius_weighted_divisor_sum (f : ArithmeticFunction ℝ)
    (hf : f.IsMultiplicative) {n : ℕ} (hn : n ≠ 0) :
    (∑ d ∈ n.divisors, (moebius d : ℝ) * f d) =
      ∏ p ∈ n.primeFactors, (1 - f p) := by
  let F := (moebius : ArithmeticFunction ℝ).pmul f * (ζ : ArithmeticFunction ℝ)
  have hF : F.IsMultiplicative :=
    (isMultiplicative_moebius.intCast.pmul hf).mul isMultiplicative_zeta.natCast
  have he : F = prodPrimeFactors (fun p => 1 - f p) := by
    refine (IsMultiplicative.eq_iff_eq_on_prime_powers _ hF _
      (IsMultiplicative.prodPrimeFactors _)).mpr ?_
    intro p i hp
    rcases i with _ | i
    · rw [pow_zero, hF.map_one, (IsMultiplicative.prodPrimeFactors _).map_one]
    · change (((moebius : ArithmeticFunction ℝ).pmul f) * (ζ : ArithmeticFunction ℝ))
          (p ^ (i + 1)) = _
      rw [coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp,
        sum_range_succ', sum_range_succ']
      have hz : (∑ j ∈ range i,
          ((moebius : ArithmeticFunction ℝ).pmul f) (p ^ (j + 1 + 1))) = 0 := by
        apply sum_eq_zero
        intro j _
        rw [pmul_apply, intCoe_apply, moebius_apply_prime_pow hp (by omega),
          if_neg (by omega), Int.cast_zero, zero_mul]
      rw [hz, zero_add, pow_zero, pow_one, pmul_apply, pmul_apply,
        intCoe_apply, intCoe_apply, moebius_apply_one, moebius_apply_prime hp,
        hf.map_one, prodPrimeFactors_apply (pow_ne_zero _ hp.ne_zero),
        Nat.primeFactors_prime_pow (by omega) hp, prod_singleton]
      norm_num
      ring
  have h := congrArg (fun a : ArithmeticFunction ℝ => a n) he
  simpa only [F, coe_mul_zeta_apply, pmul_apply, intCoe_apply,
    prodPrimeFactors_apply hn] using h


private def coprimePowerWeight (q : ℕ) (s : ℝ) : ArithmeticFunction ℝ :=
  (RHTower.TotientMulMoebius.chi q : ArithmeticFunction ℝ).pmul (powFun (-s))

private theorem coprimePowerWeight_mult (q : ℕ) (s : ℝ) :
    (coprimePowerWeight q s).IsMultiplicative :=
  (RHTower.TotientMulMoebius.chi_mult q).intCast.pmul (isMultiplicative_powFun (-s))

private theorem coprimePowerWeight_apply (q : ℕ) (s : ℝ) {e : ℕ} (he : e ≠ 0) :
    coprimePowerWeight q s e = if e.Coprime q then (e : ℝ) ^ (-s) else 0 := by
  simp only [coprimePowerWeight, pmul_apply, intCoe_apply,
    RHTower.TotientMulMoebius.chi, ArithmeticFunction.coe_mk, ne_eq, he,
    not_false_eq_true, true_and, powFun_apply he]
  split_ifs <;> simp only [Int.cast_one, Int.cast_zero, one_mul, zero_mul]

/-- The finite power deformation whose first derivative is the divisor jet. -/
def ramanujanPowerDivisor (m n : ℕ) (s : ℝ) : ℝ :=
  ∑ d ∈ m.divisors, if d ∣ n then (moebius (m / d) : ℝ) * (d : ℝ) ^ s else 0

private theorem ramanujanPowerDivisor_eq_gcd_sum {m : ℕ} (hm : 0 < m)
    (n : ℕ) (s : ℝ) :
    ramanujanPowerDivisor m n s =
      ∑ d ∈ (Nat.gcd m n).divisors, (moebius (m / d) : ℝ) * (d : ℝ) ^ s := by
  have hset : m.divisors.filter (fun d => d ∣ n) = (Nat.gcd m n).divisors := by
    ext d
    simp only [mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨⟨hdm, _⟩, hdn⟩
      exact ⟨⟨hdm, hdn⟩, Nat.gcd_ne_zero_left hm.ne'⟩
    · rintro ⟨⟨hdm, hdn⟩, _⟩
      exact ⟨⟨hdm, hm.ne'⟩, hdn⟩
  rw [ramanujanPowerDivisor, ← hset, sum_filter]

private theorem moebius_mul_coprime_indicator (q e : ℕ) :
    (moebius (q * e) : ℝ) =
      if e.Coprime q then (moebius q : ℝ) * (moebius e : ℝ) else 0 := by
  by_cases hc : e.Coprime q
  · simp only [if_pos hc, isMultiplicative_moebius.map_mul_of_coprime hc.symm,
      Int.cast_mul]
  · have hn : ¬Squarefree (q * e) :=
      fun hs => hc (Nat.coprime_of_squarefree_mul hs).symm
    simp only [if_neg hc, moebius_eq_zero_of_not_squarefree hn, Int.cast_zero]

private theorem nat_quotient_rpow {g e : ℕ} (hg : 0 < g) (he : e ∣ g) (s : ℝ) :
    ((g / e : ℕ) : ℝ) ^ s = (g : ℝ) ^ s * (e : ℝ) ^ (-s) := by
  have he0 : 0 < e := Nat.pos_of_dvd_of_pos he hg
  have heR : (e : ℝ) ≠ 0 := by exact_mod_cast he0.ne'
  have hquot : ((g / e : ℕ) : ℝ) = (g : ℝ) / e := by
    apply (eq_div_iff heR).mpr
    exact_mod_cast Nat.div_mul_cancel he
  rw [hquot, Real.div_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _),
    Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv]

private theorem restricted_power_divisor_sum {g : ℕ} (hg : 0 < g) (q : ℕ) (s : ℝ) :
    (∑ e ∈ g.divisors, if e.Coprime q then
      (moebius e : ℝ) * ((g / e : ℕ) : ℝ) ^ s else 0) =
      (g : ℝ) ^ s * ∏ p ∈ g.primeFactors,
        (if p.Coprime q then 1 - (p : ℝ) ^ (-s) else 1) := by
  have h := moebius_weighted_divisor_sum
    (coprimePowerWeight q s) (coprimePowerWeight_mult q s) hg.ne'
  have hprod : (∏ p ∈ g.primeFactors, (1 - coprimePowerWeight q s p)) =
      ∏ p ∈ g.primeFactors, (if p.Coprime q then 1 - (p : ℝ) ^ (-s) else 1) := by
    apply prod_congr rfl
    intro p hp
    rw [coprimePowerWeight_apply q s (Nat.prime_of_mem_primeFactors hp).ne_zero]
    split_ifs <;> simp only [sub_zero]
  rw [← hprod, ← h, mul_sum]
  apply sum_congr rfl
  intro e he
  rw [coprimePowerWeight_apply q s (Nat.pos_of_mem_divisors he).ne',
    nat_quotient_rpow hg (Nat.dvd_of_mem_divisors he)]
  split_ifs <;> ring

/-- Möbius reindexing leaves precisely the primes absent from the lag quotient. -/
theorem ramanujanPowerDivisor_eq_product {m : ℕ} (hm : 0 < m) (n : ℕ) (s : ℝ) :
    ramanujanPowerDivisor m n s =
      (moebius (m / Nat.gcd m n) : ℝ) * (Nat.gcd m n : ℝ) ^ s *
        ∏ p ∈ (Nat.gcd m n).primeFactors,
          (if p.Coprime (m / Nat.gcd m n) then 1 - (p : ℝ) ^ (-s) else 1) := by
  let g := Nat.gcd m n
  let q := m / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left n hm
  have hgd : g ∣ m := Nat.gcd_dvd_left m n
  have hmqg : m = q * g := (Nat.div_mul_cancel hgd).symm
  have hdiv (e : ℕ) (he : e ∈ g.divisors) : m / (g / e) = q * e := by
    have hed := Nat.dvd_of_mem_divisors he
    have hepos := Nat.pos_of_mem_divisors he
    apply Nat.div_eq_of_eq_mul_left (Nat.div_pos (Nat.le_of_dvd hg hed) hepos)
    calc
      m = q * g := hmqg
      _ = (q * e) * (g / e) := by
        conv_lhs => rw [← Nat.div_mul_cancel hed]
        ring
  rw [ramanujanPowerDivisor_eq_gcd_sum hm n s]
  change (∑ d ∈ g.divisors, (moebius (m / d) : ℝ) * (d : ℝ) ^ s) = _
  rw [← Nat.sum_div_divisors g (fun d => (moebius (m / d) : ℝ) * (d : ℝ) ^ s)]
  calc
    _ = (moebius q : ℝ) * ∑ e ∈ g.divisors,
        if e.Coprime q then (moebius e : ℝ) * ((g / e : ℕ) : ℝ) ^ s else 0 := by
      rw [mul_sum]
      apply sum_congr rfl
      intro e he
      rw [hdiv e he, moebius_mul_coprime_indicator]
      split_ifs <;> ring
    _ = _ := by rw [restricted_power_divisor_sum hg q s]; ring

/-- At zero lag the finite power divisor sum is the Jordan Euler product. -/
theorem ramanujanPowerDivisor_zero_eq_product {m : ℕ} (hm : 0 < m) (s : ℝ) :
    ramanujanPowerDivisor m 0 s =
      (m : ℝ) ^ s * ∏ p ∈ m.primeFactors, (1 - (p : ℝ) ^ (-s)) := by
  simpa only [Nat.gcd_zero_right, Nat.div_self hm, moebius_apply_one, Int.cast_one,
    one_mul, Nat.coprime_one_right_eq_true, if_true] using ramanujanPowerDivisor_eq_product hm 0 s

#print axioms ramanujanPowerDivisor_eq_product
#print axioms ramanujanPowerDivisor_zero_eq_product

private theorem prime_product_coprime_partition {q g : ℕ}
    (hq : 0 < q) (hg : 0 < g) (F : ℕ → ℝ) :
    (∏ p ∈ q.primeFactors, F p) *
      (∏ p ∈ g.primeFactors, if p.Coprime q then F p else 1) =
        ∏ p ∈ (q * g).primeFactors, F p := by
  have hfilter : (∏ p ∈ g.primeFactors, if p.Coprime q then F p else 1) =
      ∏ p ∈ g.primeFactors.filter (fun p => p ∉ q.primeFactors), F p := by
    rw [prod_filter]
    apply prod_congr rfl
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    by_cases hc : p.Coprime q
    · have hn : p ∉ q.primeFactors := fun h =>
        ((Nat.Prime.dvd_iff_not_coprime hpp).mp (Nat.mem_primeFactors.mp h).2.1) hc
      rw [if_pos hc, if_pos hn]
    · have hm : p ∈ q.primeFactors := Nat.mem_primeFactors.mpr
        ⟨hpp, (Nat.Prime.dvd_iff_not_coprime hpp).mpr hc, hq.ne'⟩
      rw [if_neg hc, if_neg (not_not.mpr hm)]
  have hd : Disjoint q.primeFactors
      (g.primeFactors.filter (fun p => p ∉ q.primeFactors)) := by
    apply Finset.disjoint_left.mpr
    intro p hp hpg
    exact (mem_filter.mp hpg).2 hp
  have hu : q.primeFactors ∪ g.primeFactors.filter (fun p => p ∉ q.primeFactors) =
      q.primeFactors ∪ g.primeFactors := by
    ext p
    simp only [mem_union, mem_filter]
    tauto
  rw [hfilter, ← prod_union hd, hu, Nat.primeFactors_mul hq.ne' hg.ne']

/-- The generalized Ramanujan quotient is a finite identity even at its zeros. -/
theorem ramanujanPowerDivisor_mul_quotient {m : ℕ} (hm : 0 < m) (n : ℕ) (s : ℝ) :
    ramanujanPowerDivisor m n s * ramanujanPowerDivisor (m / Nat.gcd m n) 0 s =
      (moebius (m / Nat.gcd m n) : ℝ) * ramanujanPowerDivisor m 0 s := by
  let g := Nat.gcd m n
  let q := m / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left n hm
  have hgd : g ∣ m := Nat.gcd_dvd_left m n
  have hq : 0 < q := Nat.div_pos (Nat.le_of_dvd hm hgd) hg
  have hmqg : m = q * g := (Nat.div_mul_cancel hgd).symm
  have hprod := prime_product_coprime_partition hq hg (fun p => 1 - (p : ℝ) ^ (-s))
  rw [← hmqg] at hprod
  have hpow : (m : ℝ) ^ s = (q : ℝ) ^ s * (g : ℝ) ^ s := by
    rw [hmqg, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  rw [ramanujanPowerDivisor_eq_product hm n s,
    ramanujanPowerDivisor_zero_eq_product hq s,
    ramanujanPowerDivisor_zero_eq_product hm s]
  change ((moebius q : ℝ) * (g : ℝ) ^ s *
      ∏ p ∈ g.primeFactors, (if p.Coprime q then 1 - (p : ℝ) ^ (-s) else 1)) *
      ((q : ℝ) ^ s * ∏ p ∈ q.primeFactors, (1 - (p : ℝ) ^ (-s))) = _
  calc
    _ = (moebius q : ℝ) * ((q : ℝ) ^ s * (g : ℝ) ^ s) *
        ((∏ p ∈ q.primeFactors, (1 - (p : ℝ) ^ (-s))) *
          ∏ p ∈ g.primeFactors, (if p.Coprime q then 1 - (p : ℝ) ^ (-s) else 1)) := by ring
    _ = _ := by rw [hprod, ← hpow]; ring

/-- Exponent one recovers the ordinary Ramanujan coefficient. -/
theorem ramanujanPowerDivisor_one (m n : ℕ) :
    ramanujanPowerDivisor m n 1 = ramanujanLagCoefficient m n := by
  unfold ramanujanPowerDivisor ramanujanLagCoefficient
  apply sum_congr rfl
  intro d _
  change (if d ∣ n then (moebius (m / d) : ℝ) * (d : ℝ) ^ (1 : ℝ) else 0) =
    (moebius (m / d) : ℝ) * (if d ∣ n then (d : ℝ) else 0)
  split_ifs <;> simp only [Real.rpow_one, mul_zero]

/-- The power deformation differentiates to the actual logarithmic divisor jet. -/
theorem hasDerivAt_ramanujanPowerDivisor_one (m n : ℕ) :
    HasDerivAt (ramanujanPowerDivisor m n) (ramanujanLogDivisorJet m n) 1 := by
  unfold ramanujanPowerDivisor ramanujanLogDivisorJet
  apply HasDerivAt.fun_sum
  intro d hd
  by_cases hdn : d ∣ n
  · simp only [if_pos hdn]
    have hdR : 0 < (d : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd
    simpa only [Real.rpow_one, mul_assoc] using
      (Real.hasStrictDerivAt_const_rpow hdR (1 : ℝ)).hasDerivAt.const_mul
        (moebius (m / d) : ℝ)
  · simpa only [if_neg hdn] using hasDerivAt_const (1 : ℝ) (0 : ℝ)

/-- Every lag jet is its Ramanujan coefficient times an exact adjunction-energy gap. -/
theorem ramanujanLogDivisorJet_eq_adjunction_gap {m : ℕ} (hm : 0 < m) (n : ℕ) :
    ramanujanLogDivisorJet m n = ramanujanLagCoefficient m n *
      ((Real.log m + tameDifferent m) -
        (Real.log (m / Nat.gcd m n : ℕ) + tameDifferent (m / Nat.gcd m n))) := by
  let q := m / Nat.gcd m n
  have hg : 0 < Nat.gcd m n := Nat.gcd_pos_of_pos_left n hm
  have hq : 0 < q := Nat.div_pos (Nat.le_of_dvd hm (Nat.gcd_dvd_left m n)) hg
  have hfun : (fun s => ramanujanPowerDivisor m n s * ramanujanPowerDivisor q 0 s) =
      (fun s => (moebius q : ℝ) * ramanujanPowerDivisor m 0 s) :=
    funext (ramanujanPowerDivisor_mul_quotient hm n)
  have hl : HasDerivAt
      (fun s => ramanujanPowerDivisor m n s * ramanujanPowerDivisor q 0 s)
      (ramanujanLogDivisorJet m n * ramanujanPowerDivisor q 0 1 +
        ramanujanPowerDivisor m n 1 * ramanujanLogDivisorJet q 0) 1 :=
    (hasDerivAt_ramanujanPowerDivisor_one m n).mul
      (hasDerivAt_ramanujanPowerDivisor_one q 0)
  rw [hfun] at hl
  have hr := (hasDerivAt_ramanujanPowerDivisor_one m 0).const_mul (moebius q : ℝ)
  have he := hl.unique hr
  have hcm : ramanujanLagCoefficient m 0 = (m.totient : ℝ) :=
    BezoutValuationIncidence.ramanujanLagCoefficient_of_dvd (dvd_zero m)
  have hcq : ramanujanLagCoefficient q 0 = (q.totient : ℝ) :=
    BezoutValuationIncidence.ramanujanLagCoefficient_of_dvd (dvd_zero q)
  simp only [ramanujanPowerDivisor_one, hcq,
    ramanujanLogDivisorJet_of_dvd hm (dvd_zero m),
    ramanujanLogDivisorJet_of_dvd hq (dvd_zero q)] at he
  have hc := ramanujanPowerDivisor_mul_quotient hm n 1
  change ramanujanPowerDivisor m n 1 * ramanujanPowerDivisor q 0 1 =
    (moebius q : ℝ) * ramanujanPowerDivisor m 0 1 at hc
  simp only [ramanujanPowerDivisor_one, hcm, hcq] at hc
  have hphi : (q.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hq).ne'
  apply mul_right_cancel₀ hphi
  change ramanujanLogDivisorJet m n * (q.totient : ℝ) =
    (ramanujanLagCoefficient m n *
      ((Real.log m + tameDifferent m) - (Real.log q + tameDifferent q))) * q.totient
  linear_combination he - (Real.log m + tameDifferent m) * hc

#print axioms ramanujanPowerDivisor_mul_quotient
#print axioms ramanujanLogDivisorJet_eq_adjunction_gap

end
end GaloisForLFunctions.SuccessorShellArithmetic
