import GaloisForLFunctions.RHTower.CoprimeBlockMultiplicationFiber

/-!
# Exact stabilization of the dyadic–triadic cancellation count

For the literal weights `(1-2[2|m]) (1-3[3|n])`, a rectangular cutoff contains the complete
multiplication fibre at `k` once both side lengths reach `k`. Opposite-sign unit cancellation
therefore has a canonical eventual count.

That count is exactly a finite integer combination of shifted divisor counts, with shifts
`2, 3, 4, 9, 6, 12, 18, 36`. The proof first classifies the signed convolution on prime powers,
uses multiplicativity to identify its pointwise absolute value, and then recovers cancellation
from the positive and negative source masses. Thus retaining this count does not produce a new
arithmetic constraint beyond an explicit divisor-count combination. This classification concerns
the specified two-source count; it makes no assertion about arbitrary labelled history objects.
-/

open scoped BigOperators

namespace RHTower.CoprimeFiberStabilization

def weight (x : ℕ × ℕ) : ℤ :=
  blockDeletionCoefficient 2 x.1 * blockDeletionCoefficient 3 x.2

def rectangleFiber (M N k : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 N)).filter fun x => x.1 * x.2 = k

theorem rectangleFiber_eq (M N k : ℕ) (hM : k ≤ M) (hN : k ≤ N) :
    rectangleFiber M N k = k.divisorsAntidiagonal := by
  ext x
  simp only [rectangleFiber, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
    Nat.mem_divisorsAntidiagonal]
  constructor
  · rintro ⟨⟨⟨h1, _⟩, ⟨h2, _⟩⟩, rfl⟩
    exact ⟨rfl, Nat.mul_ne_zero (by omega) (by omega)⟩
  · rintro ⟨hx, hk⟩
    have hmem : x ∈ k.divisorsAntidiagonal := Nat.mem_divisorsAntidiagonal.mpr ⟨hx, hk⟩
    have hfst := Nat.fst_mem_divisors_of_mem_antidiagonal hmem
    have hsnd := Nat.snd_mem_divisors_of_mem_antidiagonal hmem
    exact ⟨⟨⟨Nat.pos_of_mem_divisors hfst, (Nat.divisor_le hfst).trans hM⟩,
      ⟨Nat.pos_of_mem_divisors hsnd, (Nat.divisor_le hsnd).trans hN⟩⟩, hx⟩

def positiveMass (k : ℕ) : ℕ := ∑ x ∈ k.divisorsAntidiagonal, (weight x).toNat
def negativeMass (k : ℕ) : ℕ := ∑ x ∈ k.divisorsAntidiagonal, (-weight x).toNat
def signedMass (k : ℕ) : ℤ := ∑ x ∈ k.divisorsAntidiagonal, weight x
def absoluteMass (k : ℕ) : ℤ := ∑ x ∈ k.divisorsAntidiagonal, |weight x|
def cancellation (k : ℕ) : ℕ := min (positiveMass k) (negativeMass k)

theorem mass_difference (k : ℕ) :
    signedMass k = (positiveMass k : ℤ) - negativeMass k := by
  simp only [signedMass, positiveMass, negativeMass, Nat.cast_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  omega

theorem mass_sum (k : ℕ) :
    absoluteMass k = (positiveMass k : ℤ) + negativeMass k := by
  simp only [absoluteMass, positiveMass, negativeMass, Nat.cast_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rcases le_total 0 (weight x) with h | h
  · rw [abs_of_nonneg h]
    omega
  · rw [abs_of_nonpos h]
    omega

theorem cancellation_classification (k : ℕ) :
    2 * (cancellation k : ℤ) = absoluteMass k - |signedMass k| := by
  rw [mass_difference, mass_sum, cancellation]
  rcases le_total (positiveMass k) (negativeMass k) with h | h
  · rw [min_eq_left h, abs_of_nonpos (by omega)]
    omega
  · rw [min_eq_right h, abs_of_nonneg (by omega)]
    omega

def deletion (q : ℕ) : ArithmeticFunction ℤ :=
  ⟨fun n => if n = 0 then 0 else blockDeletionCoefficient q n, by simp⟩

theorem deletion_apply (q n : ℕ) (hn : n ≠ 0) :
    deletion q n = blockDeletionCoefficient q n := by simp [deletion, hn]

theorem signedMass_eq_convolution (k : ℕ) :
    signedMass k = (deletion 2 * deletion 3) k := by
  rw [signedMass, ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro x hx
  rw [deletion_apply _ _ (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hx),
    deletion_apply _ _ (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hx)]
  rfl

theorem deletion_isMultiplicative (q : ℕ) (hq : q.Prime) :
    (deletion q).IsMultiplicative := by
  refine ⟨?_, fun {m n} hmn => ?_⟩
  · simp [deletion, blockDeletionCoefficient, hq.not_dvd_one]
  · by_cases hm : m = 0
    · subst m
      simp
    by_cases hn : n = 0
    · subst n
      simp
    rw [deletion_apply _ _ (Nat.mul_ne_zero hm hn), deletion_apply _ _ hm,
      deletion_apply _ _ hn]
    have hnot : ¬(q ∣ m ∧ q ∣ n) := by
      rintro ⟨hqm, hqn⟩
      exact hq.ne_one (Nat.eq_one_of_dvd_coprimes hmn hqm hqn)
    simp only [blockDeletionCoefficient, hq.dvd_mul]
    by_cases hqm : q ∣ m <;> by_cases hqn : q ∣ n <;> simp_all

def signedFunction : ArithmeticFunction ℤ := deletion 2 * deletion 3
def absoluteSignedFunction : ArithmeticFunction ℤ :=
  ⟨fun n => |signedFunction n|, by simp⟩

theorem signedFunction_isMultiplicative : signedFunction.IsMultiplicative :=
  (deletion_isMultiplicative 2 Nat.prime_two).mul
    (deletion_isMultiplicative 3 Nat.prime_three)

theorem absoluteSignedFunction_isMultiplicative : absoluteSignedFunction.IsMultiplicative := by
  refine ⟨?_, fun {m n} hmn => ?_⟩
  · change |signedFunction 1| = 1
    rw [signedFunction_isMultiplicative.map_one, abs_one]
  · change |signedFunction (m*n)| = |signedFunction m| * |signedFunction n|
    rw [signedFunction_isMultiplicative.map_mul_of_coprime hmn, abs_mul]

theorem convolution_prime_power (f g : ArithmeticFunction ℤ) (p i : ℕ) (hp : p.Prime) :
    (f * g) (p ^ i) = ∑ j ∈ Finset.range (i + 1), f (p ^ j) * g (p ^ (i - j)) := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => f a * g b),
    Nat.sum_divisors_prime_pow hp]
  apply Finset.sum_congr rfl
  intro j hj
  have hji : j ≤ i := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have he : p ^ i = p ^ (i-j) * p ^ j := by rw [← pow_add, Nat.sub_add_cancel hji]
  rw [he, Nat.mul_div_cancel _ (pow_pos hp.pos j)]

theorem deletion_prime_power (q p i : ℕ) (hq : q.Prime) (hp : p.Prime) :
    deletion q (p ^ i) = if i = 0 then 1 else if p = q then 1 - (q : ℤ) else 1 := by
  rw [deletion_apply _ _ (pow_ne_zero _ hp.ne_zero)]
  by_cases hi : i = 0
  · simp [hi, blockDeletionCoefficient, hq.not_dvd_one]
  by_cases hpq : p = q
  · subst p
    have hdiv : q ∣ q ^ i := dvd_pow_self q hi
    simp [blockDeletionCoefficient, hi, hdiv]
  · have hdiv : ¬ q ∣ p ^ i := by
      intro hd
      have hd' := hq.dvd_of_dvd_pow hd
      have heq := (Nat.dvd_prime hp).mp hd'
      rcases heq with h | h
      · exact hq.ne_one h
      · exact hpq h.symm
    simp [blockDeletionCoefficient, hi, hpq, hdiv]

theorem deletion_other_prime (q p i : ℕ) (hq : q.Prime) (hp : p.Prime) (hpq : p ≠ q) :
    deletion q (p ^ i) = 1 := by simp [deletion_prime_power q p i hq hp, hpq]

theorem deletion_convolution_at_left_prime (p q i : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    (deletion p * deletion q) (p ^ i) = 1 + (i : ℤ) * (1 - (p : ℤ)) := by
  rw [convolution_prime_power _ _ p i hp]
  simp_rw [deletion_other_prime q p _ hq hp hpq, mul_one]
  rw [Finset.sum_range_succ']
  have he : ∀ j, deletion p (p ^ (j+1)) = 1 - (p : ℤ) := by
    intro j
    simp [deletion_prime_power p p (j+1) hp hp]
  simp_rw [he]
  simp [deletion, blockDeletionCoefficient, hp.not_dvd_one]
  ring

theorem signedFunction_prime_power (p i : ℕ) (hp : p.Prime) :
    signedFunction (p ^ i) =
      if p = 2 then 1 - (i : ℤ) else if p = 3 then 1 - 2 * (i : ℤ) else (i : ℤ) + 1 := by
  by_cases h2 : p = 2
  · subst p
    simp only [ite_true]
    rw [signedFunction, deletion_convolution_at_left_prime 2 3 i Nat.prime_two Nat.prime_three
      (by omega)]
    ring
  by_cases h3 : p = 3
  · subst p
    simp only [h2, if_false, ite_true]
    rw [signedFunction, mul_comm,
      deletion_convolution_at_left_prime 3 2 i Nat.prime_three Nat.prime_two (by omega)]
    ring
  · rw [signedFunction, convolution_prime_power _ _ p i hp]
    simp_rw [deletion_other_prime 2 p _ Nat.prime_two hp h2,
      deletion_other_prime 3 p _ Nat.prime_three hp h3]
    simp [h2, h3]

def zetaZ : ArithmeticFunction ℤ := (ArithmeticFunction.zeta : ArithmeticFunction ℤ)
def divisorCount : ArithmeticFunction ℤ := zetaZ * zetaZ

theorem zetaZ_prime_power (p i : ℕ) (hp : p.Prime) : zetaZ (p ^ i) = 1 := by
  simp [zetaZ, hp.ne_zero]

theorem divisorCount_prime_power (p i : ℕ) (hp : p.Prime) :
    divisorCount (p ^ i) = (i : ℤ) + 1 := by
  rw [divisorCount, convolution_prime_power _ _ p i hp]
  simp_rw [zetaZ_prime_power p _ hp]
  simp

noncomputable def localPolynomial (q : ℕ) (a b : ℤ) : ArithmeticFunction ℤ :=
  ArithmeticFunction.ofPowerSeries q
    (1 + PowerSeries.C a * PowerSeries.X + PowerSeries.C b * PowerSeries.X ^ 2)

theorem localPolynomial_isMultiplicative (q : ℕ) (hq : q.Prime) (a b : ℤ) :
    (localPolynomial q a b).IsMultiplicative := by
  apply ArithmeticFunction.isMultiplicative_ofPowerSeries_of_isPrimePow q hq.isPrimePow
  simp

theorem localPolynomial_own_prime (q i : ℕ) (hq : q.Prime) (a b : ℤ) :
    localPolynomial q a b (q ^ i) =
      (if i = 0 then 1 else 0) + a * (if i = 1 then 1 else 0) +
        b * (if i = 2 then 1 else 0) := by
  rw [localPolynomial, ArithmeticFunction.ofPowerSeries_apply_pow hq.one_lt]
  simp only [map_add, PowerSeries.coeff_X, PowerSeries.coeff_X_pow, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_one]

theorem localPolynomial_other_prime (q p i : ℕ) (hq : q.Prime) (hp : p.Prime)
    (hpq : p ≠ q) (a b : ℤ) :
    localPolynomial q a b (p ^ i) = if i = 0 then 1 else 0 := by
  by_cases hi : i = 0
  · subst i
    rw [pow_zero, localPolynomial, ArithmeticFunction.ofPowerSeries_apply_one]
    simp
  have hnot : ¬ ∃ j : ℕ, q ^ j = p ^ i := by
    rintro ⟨j, hj⟩
    have hd : p ∣ q ^ j := hj ▸ dvd_pow_self p hi
    exact hpq (Nat.prime_eq_prime_of_dvd_pow hp hq hd)
  rw [localPolynomial, ArithmeticFunction.ofPowerSeries_apply hq.one_lt,
    Function.extend_apply' _ _ _ hnot]
  simp [hi]

theorem localPolynomial_mul_other_prime (q p i : ℕ) (hq : q.Prime) (hp : p.Prime)
    (hpq : p ≠ q) (a b : ℤ) (f : ArithmeticFunction ℤ) :
    (localPolynomial q a b * f) (p ^ i) = f (p ^ i) := by
  rw [convolution_prime_power _ _ p i hp]
  simp_rw [localPolynomial_other_prime q p _ hq hp hpq]
  simp

theorem localPolynomial_mul_own_prime (q i : ℕ) (hq : q.Prime)
    (a b : ℤ) (f : ArithmeticFunction ℤ) :
    (localPolynomial q a b * f) (q ^ i) = f (q ^ i) +
      (if 1 ≤ i then a * f (q ^ (i-1)) else 0) +
      (if 2 ≤ i then b * f (q ^ (i-2)) else 0) := by
  rw [convolution_prime_power _ _ q i hq]
  simp_rw [localPolynomial_own_prime q _ hq a b, add_mul, mul_assoc,
    Finset.sum_add_distrib]
  simp only [mul_ite, ite_mul, mul_zero, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_range, Nat.zero_lt_succ, if_true, Nat.sub_zero]
  simp only [Nat.lt_succ_iff]

noncomputable def absoluteCandidate : ArithmeticFunction ℤ :=
  localPolynomial 2 (-2) 2 * localPolynomial 3 (-1) 2 * divisorCount

theorem divisorCount_isMultiplicative : divisorCount.IsMultiplicative :=
  ArithmeticFunction.isMultiplicative_zeta.natCast.mul
    ArithmeticFunction.isMultiplicative_zeta.natCast

theorem absoluteCandidate_isMultiplicative : absoluteCandidate.IsMultiplicative :=
  ((localPolynomial_isMultiplicative 2 Nat.prime_two (-2) 2).mul
    (localPolynomial_isMultiplicative 3 Nat.prime_three (-1) 2)).mul
      divisorCount_isMultiplicative

theorem absoluteSignedFunction_eq_candidate : absoluteSignedFunction = absoluteCandidate := by
  apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers
    absoluteSignedFunction absoluteSignedFunction_isMultiplicative
    absoluteCandidate absoluteCandidate_isMultiplicative).mpr
  intro p i hp
  change |signedFunction (p ^ i)| = absoluteCandidate (p ^ i)
  rw [signedFunction_prime_power p i hp]
  by_cases h2 : p = 2
  · subst p
    rw [absoluteCandidate, mul_assoc,
      localPolynomial_mul_own_prime 2 i Nat.prime_two]
    simp_rw [localPolynomial_mul_other_prime 3 2 _ Nat.prime_three Nat.prime_two
      (by omega), divisorCount_prime_power 2 _ Nat.prime_two]
    simp only [ite_true]
    cases i with
    | zero => norm_num
    | succ i =>
      rw [abs_of_nonpos (by omega)]
      split_ifs <;> omega
  by_cases h3 : p = 3
  · subst p
    have he : absoluteCandidate = localPolynomial 3 (-1) 2 *
        (localPolynomial 2 (-2) 2 * divisorCount) := by unfold absoluteCandidate; ring
    rw [he, localPolynomial_mul_own_prime 3 i Nat.prime_three]
    simp_rw [localPolynomial_mul_other_prime 2 3 _ Nat.prime_two Nat.prime_three
      (by omega), divisorCount_prime_power 3 _ Nat.prime_three]
    simp only [h2, if_false, ite_true]
    cases i with
    | zero => norm_num
    | succ i =>
      rw [abs_of_nonpos (by omega)]
      split_ifs <;> omega
  · rw [absoluteCandidate, mul_assoc,
      localPolynomial_mul_other_prime 2 p i Nat.prime_two hp h2,
      localPolynomial_mul_other_prime 3 p i Nat.prime_three hp h3,
      divisorCount_prime_power p i hp]
    simp [h2, h3]
    omega

def absoluteFunction (f : ArithmeticFunction ℤ) : ArithmeticFunction ℤ :=
  ⟨fun n => |f n|, by simp⟩

theorem absoluteFunction_isMultiplicative (f : ArithmeticFunction ℤ)
    (hf : f.IsMultiplicative) : (absoluteFunction f).IsMultiplicative := by
  refine ⟨?_, fun {m n} hmn => ?_⟩
  · change |f 1| = 1
    rw [hf.map_one, abs_one]
  · change |f (m*n)| = |f m| * |f n|
    rw [hf.map_mul_of_coprime hmn, abs_mul]

theorem absoluteDeletion_two : absoluteFunction (deletion 2) = zetaZ := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp
  change |deletion 2 n| = zetaZ n
  rw [deletion_apply 2 n hn]
  by_cases hd : 2 ∣ n <;> simp [blockDeletionCoefficient, hd, zetaZ, hn]

theorem absoluteDeletion_three :
    absoluteFunction (deletion 3) = localPolynomial 3 1 0 * zetaZ := by
  apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers
    _ (absoluteFunction_isMultiplicative _ (deletion_isMultiplicative 3 Nat.prime_three))
    _ ((localPolynomial_isMultiplicative 3 Nat.prime_three 1 0).mul
      ArithmeticFunction.isMultiplicative_zeta.natCast)).mpr
  intro p i hp
  change |deletion 3 (p ^ i)| = _
  rw [deletion_prime_power 3 p i Nat.prime_three hp]
  by_cases h3 : p = 3
  · subst p
    rw [localPolynomial_mul_own_prime 3 i Nat.prime_three]
    by_cases hi : i = 0 <;> simp_all [Nat.prime_three.ne_zero]
    all_goals omega
  · rw [localPolynomial_mul_other_prime 3 p i Nat.prime_three hp h3]
    simp [h3, hp.ne_zero]

theorem absoluteMass_eq_candidate (k : ℕ) :
    absoluteMass k = (divisorCount * localPolynomial 3 1 0) k := by
  have he : absoluteMass k =
      (absoluteFunction (deletion 2) * absoluteFunction (deletion 3)) k := by
    rw [absoluteMass, ArithmeticFunction.mul_apply]
    apply Finset.sum_congr rfl
    intro x hx
    change |weight x| = |deletion 2 x.1| * |deletion 3 x.2|
    rw [deletion_apply _ _ (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hx),
      deletion_apply _ _ (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hx)]
    exact abs_mul _ _
  rw [he, absoluteDeletion_two, absoluteDeletion_three]
  congr 1
  unfold divisorCount
  ring

noncomputable def atom (q : ℕ) : ArithmeticFunction ℤ :=
  ArithmeticFunction.ofPowerSeries q PowerSeries.X

theorem localPolynomial_eq_atoms (q : ℕ) (a b : ℤ) :
    localPolynomial q a b = 1 + (a : ArithmeticFunction ℤ) * atom q +
      (b : ArithmeticFunction ℤ) * atom q ^ 2 := by
  simp [localPolynomial, atom]

noncomputable def odometerFactor : ArithmeticFunction ℤ :=
  atom 2 + atom 3 - atom 2 ^ 2 - atom 3 ^ 2 - atom 2 * atom 3 +
    atom 2 ^ 2 * atom 3 + 2 * atom 2 * atom 3 ^ 2 - 2 * atom 2 ^ 2 * atom 3 ^ 2

theorem cancellation_eq_divisorCount_factor (k : ℕ) :
    (cancellation k : ℤ) = (divisorCount * odometerFactor) k := by
  have hc := cancellation_classification k
  rw [absoluteMass_eq_candidate, signedMass_eq_convolution] at hc
  change 2 * (cancellation k : ℤ) =
    (divisorCount * localPolynomial 3 1 0) k - absoluteSignedFunction k at hc
  rw [absoluteSignedFunction_eq_candidate] at hc
  have he : divisorCount * localPolynomial 3 1 0 - absoluteCandidate =
      2 * (divisorCount * odometerFactor) := by
    unfold absoluteCandidate odometerFactor
    simp only [localPolynomial_eq_atoms]
    norm_num
    ring
  have he' := congrArg (fun f : ArithmeticFunction ℤ => f k) he
  change (divisorCount * localPolynomial 3 1 0) k - absoluteCandidate k =
    (2 * (divisorCount * odometerFactor)) k at he'
  simp only [two_mul, ArithmeticFunction.add_apply] at he'
  omega

theorem atom_apply (q n : ℕ) (hq : 1 < q) :
    atom q n = if n = q then 1 else 0 := by
  by_cases hn : n = q
  · subst n
    have he := ArithmeticFunction.ofPowerSeries_apply_pow hq (PowerSeries.X : PowerSeries ℤ) 1
    simpa [atom, PowerSeries.coeff_X] using he
  rw [atom, ArithmeticFunction.ofPowerSeries_apply hq]
  by_cases hh : ∃ i : ℕ, q ^ i = n
  · obtain ⟨i, rfl⟩ := hh
    rw [(Nat.pow_right_injective hq).extend_apply, PowerSeries.coeff_X]
    have hi : i ≠ 1 := by intro hi; simp [hi] at hn
    simp [hi, hn]
  · rw [Function.extend_apply' _ _ _ hh]
    simp [hn]

theorem atom_mul_apply (q k : ℕ) (hq : 1 < q) (f : ArithmeticFunction ℤ) :
    (atom q * f) k = if q ∣ k then f (k / q) else 0 := by
  by_cases hk : k = 0
  · subst k
    simp
  rw [ArithmeticFunction.mul_apply]
  simp_rw [atom_apply q _ hq, ite_mul, one_mul, zero_mul]
  by_cases hd : q ∣ k
  · rw [if_pos hd]
    have hm : (q, k/q) ∈ k.divisorsAntidiagonal :=
      Nat.mem_divisorsAntidiagonal.mpr ⟨Nat.mul_div_cancel' hd, hk⟩
    rw [Finset.sum_eq_single (q, k/q)]
    · simp
    · rintro ⟨a,b⟩ hab hne
      by_cases ha : a = q
      · subst a
        have hab' := (Nat.mem_divisorsAntidiagonal.mp hab).1
        have hb : b = k/q := by rw [← hab', Nat.mul_div_cancel_left _ (by omega : 0 < q)]
        exact (hne (Prod.ext rfl hb)).elim
      · simp [ha]
    · exact fun hn => (hn hm).elim
  · rw [if_neg hd]
    apply Finset.sum_eq_zero
    rintro ⟨a,b⟩ hab
    have hab' := (Nat.mem_divisorsAntidiagonal.mp hab).1
    have ha : a ≠ q := by
      intro he
      subst a
      exact hd ⟨b, hab'.symm⟩
    simp [ha]

theorem atom_mul_atom (q r : ℕ) (hq : 1 < q) (hr : 1 < r) :
    atom q * atom r = atom (q*r) := by
  ext k
  rw [atom_mul_apply q k hq, atom_apply (q*r) k (by nlinarith), atom_apply r _ hr]
  by_cases hd : q ∣ k
  · rw [if_pos hd]
    have he : k / q = r ↔ k = q*r := by
      constructor
      · intro he
        calc k = q*(k/q) := (Nat.mul_div_cancel' hd).symm
          _ = q*r := by rw [he]
      · intro he
        rw [he, Nat.mul_div_cancel_left _ (by omega : 0 < q)]
    simp only [he]
  · have he : k ≠ q*r := by rintro rfl; exact hd (dvd_mul_right q r)
    simp [hd, he]

theorem divisorCount_apply (k : ℕ) : divisorCount k = (k.divisors.card : ℤ) := by
  rw [divisorCount, zetaZ, ArithmeticFunction.coe_zeta_mul_apply]
  calc
    (∑ d ∈ k.divisors, ((ArithmeticFunction.zeta : ArithmeticFunction ℤ) d)) =
        ∑ _d ∈ k.divisors, (1 : ℤ) := by
      apply Finset.sum_congr rfl
      intro d hd
      simp [Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)]
    _ = _ := by simp

def shiftedDivisorCount (q k : ℕ) : ℤ :=
  if q ∣ k then ((k/q).divisors.card : ℤ) else 0

theorem atom_mul_divisorCount (q k : ℕ) (hq : 1 < q) :
    (atom q * divisorCount) k = shiftedDivisorCount q k := by
  rw [atom_mul_apply q k hq]
  simp only [divisorCount_apply, shiftedDivisorCount]

theorem cancellation_eq_shifted_divisors (k : ℕ) :
    (cancellation k : ℤ) =
      shiftedDivisorCount 2 k + shiftedDivisorCount 3 k - shiftedDivisorCount 4 k -
      shiftedDivisorCount 9 k - shiftedDivisorCount 6 k + shiftedDivisorCount 12 k +
      2 * shiftedDivisorCount 18 k - 2 * shiftedDivisorCount 36 k := by
  rw [cancellation_eq_divisorCount_factor]
  have h4 : atom 2 ^ 2 = atom 4 := by rw [pow_two, atom_mul_atom 2 2 (by omega) (by omega)]
  have h9 : atom 3 ^ 2 = atom 9 := by rw [pow_two, atom_mul_atom 3 3 (by omega) (by omega)]
  have h6 : atom 2 * atom 3 = atom 6 := atom_mul_atom 2 3 (by omega) (by omega)
  have h12 : atom 4 * atom 3 = atom 12 := atom_mul_atom 4 3 (by omega) (by omega)
  have h18 : atom 2 * atom 9 = atom 18 := atom_mul_atom 2 9 (by omega) (by omega)
  have h36 : atom 4 * atom 9 = atom 36 := atom_mul_atom 4 9 (by omega) (by omega)
  have he : odometerFactor = atom 2 + atom 3 - atom 4 - atom 9 - atom 6 + atom 12 +
      2 * atom 18 - 2 * atom 36 := by
    unfold odometerFactor
    rw [h4, h9, h6, h12, mul_assoc 2 (atom 2) (atom 9),
      mul_assoc 2 (atom 4) (atom 9), h18, h36]
  rw [he]
  have hexpand : divisorCount *
      (atom 2 + atom 3 - atom 4 - atom 9 - atom 6 + atom 12 + 2*atom 18 - 2*atom 36) =
      atom 2*divisorCount + atom 3*divisorCount - atom 4*divisorCount - atom 9*divisorCount -
      atom 6*divisorCount + atom 12*divisorCount + 2*(atom 18*divisorCount) -
      2*(atom 36*divisorCount) := by ring
  rw [hexpand]
  change _ + _ - _ - _ - _ + _ + (2*(atom 18*divisorCount)) k -
    (2*(atom 36*divisorCount)) k = _
  simp only [two_mul, ArithmeticFunction.add_apply]
  rw [atom_mul_divisorCount 2 k (by omega), atom_mul_divisorCount 3 k (by omega),
    atom_mul_divisorCount 4 k (by omega), atom_mul_divisorCount 9 k (by omega),
    atom_mul_divisorCount 6 k (by omega), atom_mul_divisorCount 12 k (by omega),
    atom_mul_divisorCount 18 k (by omega), atom_mul_divisorCount 36 k (by omega)]

def rectangleCancellation (M N k : ℕ) : ℕ :=
  min (∑ x ∈ rectangleFiber M N k, (weight x).toNat)
    (∑ x ∈ rectangleFiber M N k, (-weight x).toNat)

theorem rectangleCancellation_stabilizes (M N k : ℕ) (hM : k ≤ M) (hN : k ≤ N) :
    rectangleCancellation M N k = cancellation k := by
  simp only [rectangleCancellation, rectangleFiber_eq M N k hM hN,
    cancellation, positiveMass, negativeMass]

theorem coprimeFiberStabilization_closed :
    (∀ k : ℕ, 2 * (cancellation k : ℤ) = absoluteMass k - |signedMass k|) ∧
    (∀ k : ℕ, (cancellation k : ℤ) =
      shiftedDivisorCount 2 k + shiftedDivisorCount 3 k - shiftedDivisorCount 4 k -
      shiftedDivisorCount 9 k - shiftedDivisorCount 6 k + shiftedDivisorCount 12 k +
      2 * shiftedDivisorCount 18 k - 2 * shiftedDivisorCount 36 k) ∧
    (∀ k M N : ℕ, k ≤ M → k ≤ N → rectangleCancellation M N k = cancellation k) :=
  ⟨cancellation_classification, cancellation_eq_shifted_divisors,
    fun k M N hM hN => rectangleCancellation_stabilizes M N k hM hN⟩

end RHTower.CoprimeFiberStabilization
