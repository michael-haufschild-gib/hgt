import GaloisForLFunctions.RHTower.Sieve.SelbergGcdLogAsymptotic

/-!
# The twisted Selberg coefficient

For coprime `a, b` the twisted coefficient is

`c_{a,b}(m, n) = μ(m)μ(n) (ma, nb) / (mn)`,

so `c_{1,1}` is the original Selberg coefficient. It arises from the resonant terms of the discrete
mollified second moment of `ζ` along a vertical progression, where `a/b` is the resonant fraction.

* **Multiplicativity** (`bivariateMultiplicative_twistedOriginalCoeff`): for pair-coprime splittings
  `(ma, nb)` factors as `(m₁a, n₁b)(m₂a, n₂b)`, prime by prime: the exponent of `p` in `(ma, nb)` is
  `min(v_p m + v_p a, v_p n + v_p b)`, and `min(v_p a, v_p b) = 0`.
* **Local factors.** At `p ∤ ab` the twisted coefficient agrees with the original one; at `p | a`
  (`a` squarefree) its local factor is `(1 − X/p)(1 − Y)`, and at `p | b` it is `(1 − X)(1 − Y/p)`
  (`twistedOriginalCoeff_prime_pow_of_dvd_left`, `…_right`).
-/

open ArithmeticFunction Finset
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHTower.Sieve

noncomputable section

/-- The twisted Selberg coefficient `μ(m)μ(n)(ma, nb)/(mn)`. -/
def twistedOriginalCoeff (a b m n : ℕ) : ℝ :=
  (((ArithmeticFunction.moebius m : ℤ) : ℝ) / (m : ℝ)) *
    (((ArithmeticFunction.moebius n : ℤ) : ℝ) / (n : ℝ)) *
      (Nat.gcd (m * a) (n * b) : ℝ)

theorem twistedOriginalCoeff_one_one : twistedOriginalCoeff 1 1 = selbergOriginalCoeff := by
  funext m n
  simp [twistedOriginalCoeff, selbergOriginalCoeff]

/-- **Prime-by-prime factorization of the twisted gcd.** -/
theorem gcd_mul_twist {a b m₁ n₁ m₂ n₂ : ℕ} (hab : Nat.Coprime a b) (ha : a ≠ 0) (hb : b ≠ 0)
    (hm₁ : m₁ ≠ 0) (hn₁ : n₁ ≠ 0) (hm₂ : m₂ ≠ 0) (hn₂ : n₂ ≠ 0)
    (hcop : Nat.Coprime (m₁ * n₁) (m₂ * n₂)) :
    Nat.gcd (m₁ * m₂ * a) (n₁ * n₂ * b) = Nat.gcd (m₁ * a) (n₁ * b) * Nat.gcd (m₂ * a) (n₂ * b) := by
  have h1 : m₁ * m₂ * a ≠ 0 := by positivity
  have h2 : n₁ * n₂ * b ≠ 0 := by positivity
  have h3 : m₁ * a ≠ 0 := by positivity
  have h4 : n₁ * b ≠ 0 := by positivity
  have h5 : m₂ * a ≠ 0 := by positivity
  have h6 : n₂ * b ≠ 0 := by positivity
  refine Nat.eq_of_factorization_eq (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero h1)).ne'
    (by positivity) fun p => ?_
  rw [Nat.factorization_mul (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero h3)).ne'
      (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero h5)).ne',
    Finsupp.add_apply, Nat.factorization_gcd h1 h2, Nat.factorization_gcd h3 h4,
    Nat.factorization_gcd h5 h6, Finsupp.inf_apply, Finsupp.inf_apply, Finsupp.inf_apply]
  simp only [Nat.factorization_mul (by positivity : m₁ * m₂ ≠ 0) ha,
    Nat.factorization_mul hm₁ hm₂, Nat.factorization_mul (by positivity : n₁ * n₂ ≠ 0) hb,
    Nat.factorization_mul hn₁ hn₂, Nat.factorization_mul hm₁ ha, Nat.factorization_mul hn₁ hb,
    Nat.factorization_mul hm₂ ha, Nat.factorization_mul hn₂ hb, Finsupp.add_apply]
  -- `min(v_p a, v_p b) = 0` and `p` divides at most one side of the pair split
  have hab0 : min (a.factorization p) (b.factorization p) = 0 := by
    by_contra h
    have hpa : 0 < a.factorization p := by omega
    have hpb : 0 < b.factorization p := by omega
    have hp : p.Prime := by
      by_contra hnp
      rw [Nat.factorization_eq_zero_of_not_prime _ hnp] at hpa
      omega
    exact hp.ne_one (Nat.eq_one_of_dvd_coprimes hab (Nat.dvd_of_factorization_pos hpa.ne')
      (Nat.dvd_of_factorization_pos hpb.ne'))
  have hsplit : (m₁.factorization p = 0 ∧ n₁.factorization p = 0) ∨
      (m₂.factorization p = 0 ∧ n₂.factorization p = 0) := by
    by_contra h
    push Not at h
    obtain ⟨h1', h2'⟩ := h
    have hp1 : 0 < (m₁ * n₁).factorization p := by
      rw [Nat.factorization_mul hm₁ hn₁, Finsupp.add_apply]
      by_cases hz : m₁.factorization p = 0
      · have := h1' hz; omega
      · omega
    have hp2 : 0 < (m₂ * n₂).factorization p := by
      rw [Nat.factorization_mul hm₂ hn₂, Finsupp.add_apply]
      by_cases hz : m₂.factorization p = 0
      · have := h2' hz; omega
      · omega
    have hd1 := Nat.dvd_of_factorization_pos hp1.ne'
    have hd2 := Nat.dvd_of_factorization_pos hp2.ne'
    have hp : p.Prime := by
      by_contra hnp
      rw [Nat.factorization_eq_zero_of_not_prime _ hnp] at hp1
      omega
    exact hp.ne_one (Nat.eq_one_of_dvd_coprimes hcop hd1 hd2)
  rcases hsplit with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> simp only [e1, e2] <;> omega

/-- **The twisted coefficient is bivariate multiplicative.** -/
theorem bivariateMultiplicative_twistedOriginalCoeff {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : a ≠ 0) (hb : b ≠ 0) : BivariateMultiplicative (twistedOriginalCoeff a b) := by
  constructor
  · simp [twistedOriginalCoeff, hab.gcd_eq_one]
  · intro m₁ n₁ m₂ n₂ hcop
    by_cases h0 : m₁ = 0 ∨ n₁ = 0 ∨ m₂ = 0 ∨ n₂ = 0
    · rcases h0 with h | h | h | h <;> simp [twistedOriginalCoeff, h]
    push Not at h0
    obtain ⟨hm₁, hn₁, hm₂, hn₂⟩ := h0
    have hcm : Nat.Coprime m₁ m₂ :=
      Nat.Coprime.coprime_dvd_left (dvd_mul_right m₁ n₁)
        (Nat.Coprime.coprime_dvd_right (dvd_mul_right m₂ n₂) hcop)
    have hcn : Nat.Coprime n₁ n₂ :=
      Nat.Coprime.coprime_dvd_left (dvd_mul_left n₁ m₁)
        (Nat.Coprime.coprime_dvd_right (dvd_mul_left n₂ m₂) hcop)
    have hμm : ((μ (m₁ * m₂) : ℤ) : ℝ) = ((μ m₁ : ℤ) : ℝ) * ((μ m₂ : ℤ) : ℝ) := by
      rw [isMultiplicative_moebius.map_mul_of_coprime hcm]; push_cast; ring
    have hμn : ((μ (n₁ * n₂) : ℤ) : ℝ) = ((μ n₁ : ℤ) : ℝ) * ((μ n₂ : ℤ) : ℝ) := by
      rw [isMultiplicative_moebius.map_mul_of_coprime hcn]; push_cast; ring
    have hg := gcd_mul_twist hab ha hb hm₁ hn₁ hm₂ hn₂ hcop
    unfold twistedOriginalCoeff
    rw [hμm, hμn, hg]
    push_cast
    have : (m₁ : ℝ) ≠ 0 := by exact_mod_cast hm₁
    have : (m₂ : ℝ) ≠ 0 := by exact_mod_cast hm₂
    have : (n₁ : ℝ) ≠ 0 := by exact_mod_cast hn₁
    have : (n₂ : ℝ) ≠ 0 := by exact_mod_cast hn₂
    field_simp

/-- At a prime coprime to `ab` the twist does not change the gcd of prime powers. -/
theorem gcd_prime_pow_mul_of_not_dvd {a b p : ℕ} (hab : Nat.Coprime a b) (hp : p.Prime)
    (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b) (i j : ℕ) :
    Nat.gcd (p ^ i * a) (p ^ j * b) = Nat.gcd (p ^ i) (p ^ j) := by
  have hpa' : Nat.Coprime (p ^ i) a := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpa).pow_left i
  have hpb' : Nat.Coprime (p ^ j) b := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpb).pow_left j
  have hpb'' : Nat.Coprime (p ^ i) b := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpb).pow_left i
  have hpa'' : Nat.Coprime a (p ^ j) :=
    (((Nat.Prime.coprime_iff_not_dvd hp).mpr hpa).pow_left j).symm
  rw [Nat.gcd_comm, Nat.Coprime.gcd_mul _ hpa', Nat.gcd_comm, Nat.Coprime.gcd_mul _ hpb',
    Nat.gcd_comm (p ^ j * b) a, Nat.Coprime.gcd_mul _ hpb', hpb''.gcd_eq_one,
    hpa''.gcd_eq_one, hab.gcd_eq_one]
  ring

/-- At a prime coprime to `ab` the twisted coefficient is the original one. -/
theorem twistedOriginalCoeff_prime_pow_of_not_dvd {a b p : ℕ} (hab : Nat.Coprime a b)
    (hp : p.Prime) (hpa : ¬ p ∣ a) (hpb : ¬ p ∣ b) (i j : ℕ) :
    twistedOriginalCoeff a b (p ^ i) (p ^ j) = selbergOriginalCoeff (p ^ i) (p ^ j) := by
  unfold twistedOriginalCoeff selbergOriginalCoeff
  rw [gcd_prime_pow_mul_of_not_dvd hab hp hpa hpb]

/-- The local factor `(1 − X/p)(1 − Y)` of the twisted coefficient at `p | a`. -/
def twistLocal (p i j : ℕ) : ℝ :=
  if i = 0 ∧ j = 0 then 1
  else if i = 1 ∧ j = 0 then -(1 / (p : ℝ))
  else if i = 0 ∧ j = 1 then -1
  else if i = 1 ∧ j = 1 then 1 / (p : ℝ)
  else 0

theorem moebius_prime_pow_real {p i : ℕ} (hp : p.Prime) :
    ((μ (p ^ i) : ℤ) : ℝ) = if i = 0 then 1 else if i = 1 then -1 else 0 :=
  moebius_real_prime_pow hp

/-- **The local factor at `p | a`.** -/
theorem twistedOriginalCoeff_prime_pow_of_dvd_left {a b p : ℕ} (hab : Nat.Coprime a b)
    (ha : Squarefree a) (hp : p.Prime) (hpa : p ∣ a) (i j : ℕ) :
    twistedOriginalCoeff a b (p ^ i) (p ^ j) = twistLocal p i j := by
  obtain ⟨a', rfl⟩ := hpa
  have hpa' : ¬ p ∣ a' := by
    intro h
    obtain ⟨c, rfl⟩ := h
    have := (Nat.squarefree_iff_prime_squarefree.mp ha) p hp
    exact this ⟨c, by ring⟩
  have hpb : ¬ p ∣ b := fun h => hp.ne_one (Nat.eq_one_of_dvd_coprimes hab (dvd_mul_right p a') h)
  have ha'b : Nat.Coprime a' b := Nat.Coprime.coprime_dvd_left (dvd_mul_left a' p) hab
  have hpbC : Nat.Coprime p b := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpb
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  unfold twistedOriginalCoeff twistLocal
  rw [moebius_prime_pow_real hp, moebius_prime_pow_real hp]
  rcases Nat.lt_or_ge i 2 with hi | hi
  · rcases Nat.lt_or_ge j 2 with hj | hj
    · have g01 : Nat.gcd (p ^ 0 * (p * a')) (p ^ 1 * b) = p := by
        rw [pow_zero, one_mul, pow_one, Nat.gcd_mul_left, ha'b.gcd_eq_one, mul_one]
      have g10 : Nat.gcd (p ^ 1 * (p * a')) (p ^ 0 * b) = 1 := by
        rw [pow_zero, one_mul, pow_one]
        exact (Nat.Coprime.mul_left hpbC hab).gcd_eq_one
      have g11 : Nat.gcd (p ^ 1 * (p * a')) (p ^ 1 * b) = p := by
        rw [pow_one, Nat.gcd_mul_left, hab.gcd_eq_one, mul_one]
      have g00 : Nat.gcd (p ^ 0 * (p * a')) (p ^ 0 * b) = 1 := by
        rw [pow_zero, one_mul, one_mul]; exact hab.gcd_eq_one
      interval_cases i <;> interval_cases j
      · rw [g00]; simp
      · rw [g01]; simp; field_simp
      · rw [g10]; simp; ring
      · rw [g11]; simp; field_simp
    · have : ¬ j = 0 := by omega
      have : ¬ j = 1 := by omega
      simp [*]
  · have : ¬ i = 0 := by omega
    have : ¬ i = 1 := by omega
    simp [*]

/-- **The local factor at `p | b`.** -/
theorem twistedOriginalCoeff_prime_pow_of_dvd_right {a b p : ℕ} (hab : Nat.Coprime a b)
    (hb : Squarefree b) (hp : p.Prime) (hpb : p ∣ b) (i j : ℕ) :
    twistedOriginalCoeff a b (p ^ i) (p ^ j) = twistLocal p j i := by
  have hswap : twistedOriginalCoeff a b (p ^ i) (p ^ j) = twistedOriginalCoeff b a (p ^ j) (p ^ i) := by
    unfold twistedOriginalCoeff
    rw [Nat.gcd_comm]
    ring
  rw [hswap]
  exact twistedOriginalCoeff_prime_pow_of_dvd_left hab.symm hb hp hpb j i

end

end RHTower.Sieve
