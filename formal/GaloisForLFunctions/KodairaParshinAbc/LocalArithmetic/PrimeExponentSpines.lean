import GaloisForLFunctions.RHTower.Deninger.DeningerRationalPrimeFactorization
import Mathlib.RingTheory.HahnSeries.Lex

/-!
# The lexicographic spine of rational prime exponents

For the order of Definition 3.1 in Boissonneau–Vogel (arXiv:2512.18349),
the first nonzero coordinate determines the Archimedean class. On rational
factorizations the finite classes are precisely primes. In a power coset
the first exponent not divisible by the power is the last attainable order.
-/

noncomputable section
open HahnSeries RHTower
namespace GaloisForLFunctions.KodairaParshinAbc

/-- The integer prime orders of a rational unit, read from small to large primes. -/
def primeExponentSeries (q : ℚˣ) : HahnSeries ℕ ℤ :=
  HahnSeries.ofFinsuppLinearMap ℤ (deningerRatExp q)

/-- The first nontrivial prime exponent. The two signs of one have order infinity. -/
def firstPrimeExponent (q : ℚˣ) : WithTop ℕ := (primeExponentSeries q).orderTop

private theorem series_mul (q r : ℚˣ) :
    primeExponentSeries (q*r) = primeExponentSeries q + primeExponentSeries r := by
  unfold primeExponentSeries
  rw [Units.val_mul, deningerRatExp_mul q.ne_zero r.ne_zero, map_add]

/-- The exponent order is exactly the natural Archimedean class in the lexicographic group. -/
theorem primeExponent_class_iff (q r : ℚˣ) :
    ArchimedeanClass.mk (toLex (primeExponentSeries q)) =
      ArchimedeanClass.mk (toLex (primeExponentSeries r)) ↔
      firstPrimeExponent q = firstPrimeExponent r := by
  exact ((HahnSeries.archimedeanClassOrderIsoWithTop ℕ ℤ).injective.eq_iff).symm.trans
    (by simp [firstPrimeExponent])

/-- A local characterization independent of signs and of any larger prime. -/
theorem firstPrimeExponent_ge_iff (q : ℚˣ) (k : WithTop ℕ) :
    k ≤ firstPrimeExponent q ↔ ∀ j : ℕ, (j : WithTop ℕ) < k → deningerRatExp q j = 0 :=
  HahnSeries.le_orderTop_iff_forall

/-- A candidate is the leading prime precisely when it occurs and every earlier exponent vanishes. -/
theorem firstPrimeExponent_eq_iff (q : ℚˣ) (j : ℕ) :
    firstPrimeExponent q = j ↔ deningerRatExp q j ≠ 0 ∧ ∀ k < j, deningerRatExp q k = 0 := by
  constructor
  · intro h
    exact ⟨HahnSeries.coeff_orderTop_ne h, fun k hk =>
      (firstPrimeExponent_ge_iff q j).1 h.ge k (WithTop.coe_lt_coe.mpr hk)⟩
  · rintro ⟨hn, he⟩
    apply le_antisymm (HahnSeries.orderTop_le_of_coeff_ne_zero (x := primeExponentSeries q) hn)
    exact (firstPrimeExponent_ge_iff q j).2 fun k hk => he k (WithTop.coe_lt_coe.mp hk)

/-- Exactly the primes occur as finite ranks of rational units. -/
theorem firstPrimeExponent_finite_range (j : ℕ) :
    (∃ q : ℚˣ, firstPrimeExponent q = j) ↔ j.Prime := by
  constructor
  · rintro ⟨q, h⟩
    exact deningerRatExp_support_prime _ (Finsupp.mem_support_iff.mpr ((firstPrimeExponent_eq_iff _ _).1 h).1)
  · intro hj
    let q := Units.mk0 (j : ℚ) (Nat.cast_ne_zero.mpr hj.ne_zero)
    refine ⟨q, (firstPrimeExponent_eq_iff q j).2 ?_⟩
    change deningerRatExp (j : ℚ) j ≠ 0 ∧ _
    have h : deningerRatExp (q : ℚ) = Finsupp.single j 1 := deningerRatExp_natCast_prime hj
    refine ⟨by simp [deningerRatExp_natCast_prime hj], fun k hk => ?_⟩
    simp [h, hk.ne]

/-- Multiplication can cancel the earliest exponent but cannot introduce an earlier one. -/
theorem firstPrimeExponent_mul_ge (q r : ℚˣ) :
    min (firstPrimeExponent q) (firstPrimeExponent r) ≤ firstPrimeExponent (q*r) := by
  unfold firstPrimeExponent
  rw [series_mul]
  exact HahnSeries.min_orderTop_le_orderTop_add

/-- The earlier of two distinct leading primes survives multiplication. -/
theorem firstPrimeExponent_mul_eq (q r : ℚˣ) :
    firstPrimeExponent q < firstPrimeExponent r →
      firstPrimeExponent (q*r) = firstPrimeExponent q := by
  intro h
  unfold firstPrimeExponent
  rw [series_mul]
  exact HahnSeries.orderTop_add_eq_left h

/-- Rank infinity remembers the two signs of one, which share their prime exponents. -/
theorem firstPrimeExponent_top_iff (q : ℚˣ) : firstPrimeExponent q = ⊤ ↔ |(q:ℚ)| = 1 := by
  rw [← top_le_iff, firstPrimeExponent_ge_iff, ← deningerRatExp_eq_zero_iff (abs_pos.mpr q.ne_zero),
    deningerRatExp_abs]
  constructor
  · intro h
    exact Finsupp.ext fun j => h j (WithTop.coe_lt_top j)
  · intro h j _
    rw [h, Finsupp.zero_apply]

/-- With two distinct prime factors, the smaller prime controls the rank despite the larger support index. -/
theorem firstPrimeExponent_two_factors (r t : ℕ) (hr : r.Prime) (ht : t.Prime) (hrt : r < t) :
    ∃ q : ℚˣ, (q:ℚ) = (r:ℚ)*t ∧ firstPrimeExponent q = r ∧ t ∈ (deningerRatExp q).support := by
  let v := Units.mk0 (r:ℚ) (Nat.cast_ne_zero.mpr hr.ne_zero)
  let w := Units.mk0 (t:ℚ) (Nat.cast_ne_zero.mpr ht.ne_zero)
  have he : deningerRatExp (↑(v*w):ℚ) = Finsupp.single r 1 + Finsupp.single t 1 := by
    rw [Units.val_mul, deningerRatExp_mul v.ne_zero w.ne_zero]
    exact congrArg₂ (· + ·) (deningerRatExp_natCast_prime hr) (deningerRatExp_natCast_prime ht)
  refine ⟨v*w,rfl,(firstPrimeExponent_eq_iff _ _).2 ⟨?_,?_⟩,?_⟩
  · rw [he,Finsupp.add_apply,Finsupp.single_eq_same,Finsupp.single_eq_of_ne hrt.ne,add_zero]
    exact one_ne_zero
  · intro i hi
    rw [he,Finsupp.add_apply,Finsupp.single_eq_of_ne hi.ne,Finsupp.single_eq_of_ne (hi.trans hrt).ne,add_zero]
  · rw [Finsupp.mem_support_iff,he,Finsupp.add_apply,Finsupp.single_eq_of_ne hrt.ne',
      Finsupp.single_eq_same,zero_add]
    exact one_ne_zero

/-- The first prime obstructing removal by an n-th power. -/
def primePowerCosetOrder (q : ℚˣ) (n : ℤ) : WithTop ℕ :=
  (HahnSeries.ofFinsupp (deningerRatExp q |>.mapRange (fun a => a % n) (Int.zero_emod _))).orderTop

/-- All exponents below the cut vanish in the power coset precisely when they are n-divisible. -/
theorem primePowerCosetOrder_ge_iff (q : ℚˣ) (n : ℤ) (k : WithTop ℕ) :
    k ≤ primePowerCosetOrder q n ↔ ∀ j : ℕ, (j : WithTop ℕ) < k → n ∣ deningerRatExp q j := by
  unfold primePowerCosetOrder
  rw [HahnSeries.le_orderTop_iff_forall]
  constructor
  · intro h j hj
    exact Int.dvd_iff_emod_eq_zero.mpr (h j hj)
  · intro h j hj
    exact Int.dvd_iff_emod_eq_zero.mp (h j hj)

private theorem unit_mul_power_exponent (q u : ℚˣ) (n : ℤ) (j : ℕ) :
    deningerRatExp (↑(q * u ^ n) : ℚ) j = deningerRatExp q j + n * deningerRatExp u j := by
  rw [Units.val_mul, Units.val_zpow_eq_zpow_val, deningerRatExp_mul q.ne_zero (zpow_ne_zero _ u.ne_zero),
    deningerRatExp_zpow u.ne_zero, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]

/-- The first nondivisible exponent is unchanged by multiplying by an arbitrary n-th power. -/
theorem primePowerCosetOrder_mul_pow (q u : ℚˣ) (n : ℤ) :
    primePowerCosetOrder (q * u^n) n = primePowerCosetOrder q n := by
  unfold primePowerCosetOrder
  congr 2
  ext j
  simp only [Finsupp.mapRange_apply, unit_mul_power_exponent, Int.add_mul_emod_self_left]

/-- Every power twist has leading prime at most the first nondivisible exponent. -/
theorem firstPrimeExponent_twist_le (q u : ℚˣ) (n : ℤ) :
    firstPrimeExponent (q * u^n) ≤ primePowerCosetOrder q n := by
  rw [← primePowerCosetOrder_mul_pow q u, primePowerCosetOrder_ge_iff]
  intro j hj
  rw [(firstPrimeExponent_ge_iff _ _).1 le_rfl j hj]
  exact dvd_zero _

/-- Simultaneous Euclidean division of the prime exponents constructs a positive optimal twist. -/
theorem primePowerCosetOrder_attained (q : ℚˣ) (n : ℤ) :
    ∃ u : ℚˣ, 0 < (u : ℚ) ∧ firstPrimeExponent (q * u^n) = primePowerCosetOrder q n := by
  let f := (deningerRatExp q).mapRange (fun a => -(a / n)) (by simp)
  have hf : ∀ j ∈ f.support, Nat.Prime j := by
    intro j hj
    apply deningerRatExp_support_prime q
    apply Finsupp.mem_support_iff.mpr
    intro hz
    exact (Finsupp.mem_support_iff.mp hj) (by simp [f, hz])
  obtain ⟨r, hr, he⟩ := deningerRatExp_surjective_on_primes f hf
  let u := Units.mk0 r hr.ne'
  refine ⟨u, hr, ?_⟩
  unfold firstPrimeExponent primePowerCosetOrder
  congr 1
  ext j
  change deningerRatExp (↑(q * u^n) : ℚ) j = deningerRatExp q j % n
  rw [unit_mul_power_exponent]
  change _ + n * deningerRatExp r j = _
  rw [he]
  change _ + n * (-(_ / n)) = _
  have := Int.emod_add_mul_ediv (deningerRatExp q j) n
  linarith only [this]

/-- Thus the n-spine is a maximum over rational units, with the sign forgotten at infinity. -/
theorem primePowerCosetOrder_isGreatest (q : ℚˣ) (n : ℤ) :
    IsGreatest (Set.range fun u : ℚˣ => firstPrimeExponent (q * u^n)) (primePowerCosetOrder q n) := by
  obtain ⟨u, _, hu⟩ := primePowerCosetOrder_attained q n
  exact ⟨⟨u, hu⟩, by rintro _ ⟨v, rfl⟩; exact firstPrimeExponent_twist_le q v n⟩

/-- A rational unit is an actual n-th power exactly when the spine is infinite and its sign has an n-th root. -/
theorem rationalUnit_power_iff_infinite_spine (q : ℚˣ) (n : ℕ) :
    (∃ v : ℚˣ, v^n = q) ↔ primePowerCosetOrder q (n:ℤ) = ⊤ ∧ (Odd n ∨ 0 < (q:ℚ)) := by
  constructor
  · rintro ⟨v,rfl⟩
    constructor
    · rw [← top_le_iff, primePowerCosetOrder_ge_iff]
      intro j _
      have he := unit_mul_power_exponent 1 v (n:ℤ) j
      simp only [zpow_natCast, one_mul, Units.val_one, deningerRatExp_one, Finsupp.zero_apply,
        zero_add] at he
      rw [he]
      exact dvd_mul_right _ _
    · rcases n.even_or_odd with ⟨k,hk⟩ | hn
      · right
        rw [Units.val_pow_eq_pow_val, hk, pow_add, ← sq]
        exact sq_pos_of_ne_zero (pow_ne_zero _ v.ne_zero)
      · exact Or.inl hn
  · rintro ⟨hsp,hsign⟩
    obtain ⟨u,hu,he⟩ := primePowerCosetOrder_attained q (n:ℤ)
    rw [hsp, zpow_natCast, firstPrimeExponent_top_iff, Units.val_mul, Units.val_pow_eq_pow_val] at he
    have hn : (u:ℚ)^n ≠ 0 := pow_ne_zero _ u.ne_zero
    rcases le_or_gt 0 ((q:ℚ)*(u:ℚ)^n) with h | h
    · rw [abs_of_nonneg h] at he
      refine ⟨u⁻¹, Units.ext ?_⟩
      rw [Units.val_pow_eq_pow_val,Units.val_inv_eq_inv_val,(eq_div_iff hn).2 he,one_div,inv_pow]
    · have hodd : Odd n := hsign.resolve_right fun hq => (mul_pos hq (pow_pos hu n)).not_gt h
      rw [abs_of_neg h] at he
      have he' : (q:ℚ)*(u:ℚ)^n = -1 := neg_eq_iff_eq_neg.mp he
      refine ⟨-u⁻¹, Units.ext ?_⟩
      rw [Units.val_pow_eq_pow_val,Units.val_neg,Units.val_inv_eq_inv_val,hodd.neg_pow,inv_pow,
        (eq_div_iff hn).2 he',neg_div,one_div]

#print axioms firstPrimeExponent_top_iff
#print axioms firstPrimeExponent_two_factors
#print axioms rationalUnit_power_iff_infinite_spine
#print axioms primeExponent_class_iff
#print axioms firstPrimeExponent_ge_iff
#print axioms firstPrimeExponent_eq_iff
#print axioms firstPrimeExponent_finite_range
#print axioms firstPrimeExponent_mul_ge
#print axioms firstPrimeExponent_mul_eq
#print axioms primePowerCosetOrder_ge_iff
#print axioms primePowerCosetOrder_mul_pow
#print axioms firstPrimeExponent_twist_le
#print axioms primePowerCosetOrder_attained
#print axioms primePowerCosetOrder_isGreatest

end GaloisForLFunctions.KodairaParshinAbc
