import GaloisForLFunctions.PNTPlus.Mathlib.NumberTheory.Sieve.SelbergBounds
import GaloisForLFunctions.RHTower.Sieve.SquarefreeDivisorProduct
import GaloisForLFunctions.RHTower.Sieve.PowersetTailBound

/-!
# The two-dimensional sieve of shifted rough pairs

The cost of discarding the integers free of primes in a range `(P₁, h]` is, after the second-moment
reduction, the number of pairs `(m, m+d)` **both** free of such primes.  That is a sieve of
dimension two: for each sifting prime `p` the pair avoids two residue classes, or one when `p ∣ d`.

This file sets up that sieve as a `SelbergSieve` and identifies its sifted sum with the pair count.
The density `ν` is the multiplicative function with `ν p = 2/p` off the shift and `1/p` on it, which
is exactly the proportion of residues the pair must avoid.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- The primes of a range, multiplied together. -/
def rangePrimes (P₁ h : ℕ) : Finset ℕ := (Finset.Icc (P₁ + 1) h).filter Nat.Prime

theorem rangePrimes_prime {P₁ h p : ℕ} (hp : p ∈ rangePrimes P₁ h) : p.Prime :=
  (Finset.mem_filter.1 hp).2

/-- The modulus of the sieve: the product of the sifting primes. -/
def rangePrimorial (P₁ h : ℕ) : ℕ := ∏ p ∈ rangePrimes P₁ h, p

theorem rangePrimorial_squarefree (P₁ h : ℕ) : Squarefree (rangePrimorial P₁ h) :=
  Sieve.prodDistinctPrimes_squarefree _ fun _ hp => rangePrimes_prime hp

/-- The number of residue classes a shifted pair must avoid at a prime: two off the shift, one on
it. -/
def pairClassCount (d p : ℕ) : ℝ := if p ∣ d then 1 else 2

/-- The sieve density of the shifted pair problem. -/
def pairNu (d : ℕ) : ArithmeticFunction ℝ :=
  (ArithmeticFunction.prodPrimeFactors (pairClassCount d)).pdiv .id

theorem pairNu_isMultiplicative (d : ℕ) : (pairNu d).IsMultiplicative := by
  rw [pairNu]
  arith_mult

theorem pairNu_apply_prime {d p : ℕ} (hp : p.Prime) :
    pairNu d p = pairClassCount d p / (p : ℝ) := by
  simp [pairNu, ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero, hp.primeFactors]

theorem pairNu_pos_of_prime {d p : ℕ} (hp : p.Prime) : 0 < pairNu d p := by
  rw [pairNu_apply_prime hp, pairClassCount]
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  split_ifs <;> positivity

/-- Away from the shift the density is `2/p`, so it is below one only above `2`; on the shift it is
`1/p`, below one at every prime. -/
theorem pairNu_lt_one_of_prime {d p : ℕ} (hp : p.Prime) (h3 : 3 ≤ p) : pairNu d p < 1 := by
  rw [pairNu_apply_prime hp, pairClassCount]
  have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h3
  split_ifs with hd
  · rw [div_lt_one (by linarith)]
    linarith
  · rw [div_lt_one (by linarith)]
    linarith

/-! ## The sieve instance -/

/-- A prime dividing a product of distinct primes is one of them. -/
theorem mem_of_prime_dvd_prod {s : Finset ℕ} (hs : ∀ q ∈ s, q.Prime) {p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ ∏ q ∈ s, q) : p ∈ s := by
  obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hp.prime (fun q => q)).1 hdvd
  have := ((Nat.prime_dvd_prime_iff_eq hp (hs q hq)).1 hpq)
  rwa [this]

/-- **The sieve of shifted rough pairs.**  Support `[1, Y]`, sifting primes the range `(P₁, h]`, and
density the shifted-pair density. -/
def roughPairSieve (Y : ℝ) {P₁ : ℕ} (hP₁ : 2 ≤ P₁) (h d : ℕ) {z : ℝ} (hz : 1 ≤ z) :
    SelbergSieve where
  support := (Finset.Icc 1 ⌊Y⌋₊).image (fun m => m * (m + d))
  prodPrimes := rangePrimorial P₁ h
  prodPrimes_squarefree := rangePrimorial_squarefree P₁ h
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := Y
  nu := pairNu d
  nu_mult := pairNu_isMultiplicative d
  nu_pos_of_prime := fun p hp _ => pairNu_pos_of_prime hp
  nu_lt_one_of_prime := fun p hp hdvd => by
    refine pairNu_lt_one_of_prime hp ?_
    have hmem : p ∈ rangePrimes P₁ h :=
      mem_of_prime_dvd_prod (fun q hq => rangePrimes_prime hq) hp hdvd
    rw [rangePrimes, Finset.mem_filter, Finset.mem_Icc] at hmem
    omega
  level := z
  one_le_level := hz

/-- The shift map is injective on the positive integers. -/
theorem shiftMul_injOn (d : ℕ) : Set.InjOn (fun m : ℕ => m * (m + d)) (Set.Ici 1) := by
  intro a ha b hb hab
  simp only [Set.mem_Ici] at ha hb
  simp only at hab
  have hmono : ∀ u v : ℕ, 1 ≤ u → u < v → u * (u + d) < v * (v + d) := by
    intro u v hu huv
    have h1 : u * (u + d) < v * (u + d) :=
      Nat.mul_lt_mul_of_lt_of_le huv (le_refl (u + d)) (by omega)
    have h2 : v * (u + d) ≤ v * (v + d) := Nat.mul_le_mul_left v (by omega)
    omega
  rcases Nat.lt_trichotomy a b with hlt | heq | hgt
  · exact absurd hab (by have := hmono a b ha hlt; omega)
  · exact heq
  · exact absurd hab (by have := hmono b a hb hgt; omega)

/-- **The sifted sum of the pair sieve is the shifted rough pair count.** -/
theorem siftedSum_roughPairSieve (Y : ℝ) {P₁ : ℕ} (hP₁ : 2 ≤ P₁) (h d : ℕ) {z : ℝ} (hz : 1 ≤ z) :
    BoundingSieve.siftedSum (s := (roughPairSieve Y hP₁ h d hz).toBoundingSieve)
      = (((Finset.Icc 1 ⌊Y⌋₊).filter
          (fun m => (∀ p ∈ rangePrimes P₁ h, ¬ p ∣ m)
            ∧ ∀ p ∈ rangePrimes P₁ h, ¬ p ∣ (m + d))).card : ℝ) := by
  classical
  have hiff : ∀ n : ℕ, Nat.Coprime (rangePrimorial P₁ h) n
      ↔ (∀ p ∈ rangePrimes P₁ h, ¬ p ∣ n) := by
    intro n
    constructor
    · intro hc p hp hpn
      have hpP : p ∣ rangePrimorial P₁ h := Finset.dvd_prod_of_mem _ hp
      have hd : p ∣ Nat.gcd (rangePrimorial P₁ h) n := Nat.dvd_gcd hpP hpn
      rw [Nat.Coprime] at hc
      rw [hc] at hd
      exact (Nat.Prime.one_lt (rangePrimes_prime hp)).ne' (Nat.eq_one_of_dvd_one hd)
    · intro hall
      by_contra hne
      obtain ⟨p, hp⟩ := Nat.exists_prime_and_dvd hne
      have hpP : p ∣ rangePrimorial P₁ h := hp.2.trans (Nat.gcd_dvd_left _ _)
      have hpn : p ∣ n := hp.2.trans (Nat.gcd_dvd_right _ _)
      exact hall p (mem_of_prime_dvd_prod (fun q hq => rangePrimes_prime hq) hp.1 hpP) hpn
  have hinj : Set.InjOn (fun m : ℕ => m * (m + d)) ((Finset.Icc 1 ⌊Y⌋₊ : Finset ℕ) : Set ℕ) := by
    refine Set.InjOn.mono ?_ (shiftMul_injOn d)
    intro m hm
    rw [Finset.mem_coe, Finset.mem_Icc] at hm
    exact hm.1
  show (∑ v ∈ (Finset.Icc 1 ⌊Y⌋₊).image (fun m => m * (m + d)),
      if Nat.Coprime (rangePrimorial P₁ h) v then (1 : ℝ) else 0) = _
  rw [Finset.sum_image hinj]
  have hpair : ∀ m : ℕ, Nat.Coprime (rangePrimorial P₁ h) (m * (m + d))
      ↔ ((∀ p ∈ rangePrimes P₁ h, ¬ p ∣ m) ∧ ∀ p ∈ rangePrimes P₁ h, ¬ p ∣ (m + d)) := by
    intro m
    rw [hiff]
    constructor
    · intro hall
      exact ⟨fun p hp hpm => hall p hp (hpm.trans ⟨m + d, rfl⟩),
        fun p hp hpm => hall p hp (Dvd.dvd.mul_left hpm m)⟩
    · rintro ⟨h1, h2⟩ p hp hpv
      rcases (Nat.Prime.dvd_mul (rangePrimes_prime hp)).1 hpv with hc | hc
      · exact h1 p hp hc
      · exact h2 p hp hc
  simp only [hpair]
  rw [Finset.sum_boole]


/-! ## The Selberg terms of the pair sieve -/

/-- **The Selberg terms of the pair sieve are an explicit product.**  For a squarefree divisor of
the modulus, `g(l) = ∏_{p ∣ l} c_p/(p − c_p)`. -/
theorem selbergTerms_roughPairSieve (Y : ℝ) {P₁ : ℕ} (hP₁ : 2 ≤ P₁) (h d : ℕ) {z : ℝ}
    (hz : 1 ≤ z) {l : ℕ} (hl : l ∣ rangePrimorial P₁ h) (hl0 : l ≠ 0) :
    SelbergSieve.selbergTerms (roughPairSieve Y hP₁ h d hz).toBoundingSieve l
      = ∏ p ∈ l.primeFactors, pairClassCount d p / ((p : ℝ) - pairClassCount d p) := by
  classical
  have hsq : Squarefree l :=
    Squarefree.squarefree_of_dvd hl (rangePrimorial_squarefree P₁ h)
  have hprime : ∀ p ∈ l.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hp3 : ∀ p ∈ l.primeFactors, (3 : ℝ) ≤ (p : ℝ) := by
    intro p hp
    have hpl : p ∣ l := Nat.dvd_of_mem_primeFactors hp
    have hpP : p ∣ rangePrimorial P₁ h := hpl.trans hl
    have hmem : p ∈ rangePrimes P₁ h :=
      mem_of_prime_dvd_prod (fun q hq => rangePrimes_prime hq) (hprime p hp) hpP
    rw [rangePrimes, Finset.mem_filter, Finset.mem_Icc] at hmem
    have : 3 ≤ p := by omega
    exact_mod_cast this
  rw [SelbergSieve.selbergTerms_apply]
  have hnu : (roughPairSieve Y hP₁ h d hz).toBoundingSieve.nu l
      = (∏ p ∈ l.primeFactors, pairClassCount d p) / (l : ℝ) := by
    show pairNu d l = _
    simp [pairNu, ArithmeticFunction.prodPrimeFactors_apply hl0]
  rw [hnu]
  have hprod : ∀ p ∈ l.primeFactors,
      1 / (1 - (roughPairSieve Y hP₁ h d hz).toBoundingSieve.nu p)
        = (p : ℝ) / ((p : ℝ) - pairClassCount d p) := by
    intro p hp
    have hval : (roughPairSieve Y hP₁ h d hz).toBoundingSieve.nu p
        = pairClassCount d p / (p : ℝ) := pairNu_apply_prime (hprime p hp)
    rw [hval]
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith [hp3 p hp]
    have hstep : (1 : ℝ) - pairClassCount d p / (p : ℝ)
        = ((p : ℝ) - pairClassCount d p) / (p : ℝ) := by
      field_simp
    rw [hstep, one_div_div]
  rw [Finset.prod_congr rfl hprod]
  have hl_eq : ((∏ p ∈ l.primeFactors, p : ℕ) : ℝ) = (l : ℝ) := by
    rw [Nat.prod_primeFactors_of_squarefree hsq]
  have hsplit : (∏ p ∈ l.primeFactors, pairClassCount d p) / (l : ℝ)
      * ∏ p ∈ l.primeFactors, (p : ℝ) / ((p : ℝ) - pairClassCount d p)
      = ∏ p ∈ l.primeFactors, pairClassCount d p / ((p : ℝ) - pairClassCount d p) := by
    have hlR : (l : ℝ) = ∏ p ∈ l.primeFactors, (p : ℝ) := by
      rw [← hl_eq]
      push_cast
      ring
    rw [hlR, div_mul_eq_mul_div, ← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith [hp3 p hp]
    field_simp
  rw [hsplit]

/-- **The untruncated bounding sum of the pair sieve is an Euler product.** -/
theorem sum_selbergTerms_roughPairSieve (Y : ℝ) {P₁ : ℕ} (hP₁ : 2 ≤ P₁) (h d : ℕ) {z : ℝ}
    (hz : 1 ≤ z) :
    (∑ l ∈ (rangePrimorial P₁ h).divisors,
        SelbergSieve.selbergTerms (roughPairSieve Y hP₁ h d hz).toBoundingSieve l)
      = ∏ p ∈ rangePrimes P₁ h,
          (pairClassCount d p / ((p : ℝ) - pairClassCount d p) + 1) := by
  classical
  have hprime : ∀ p ∈ rangePrimes P₁ h, p.Prime := fun p hp => rangePrimes_prime hp
  have hcongr : ∀ l ∈ (rangePrimorial P₁ h).divisors,
      SelbergSieve.selbergTerms (roughPairSieve Y hP₁ h d hz).toBoundingSieve l
        = ∏ p ∈ l.primeFactors, pairClassCount d p / ((p : ℝ) - pairClassCount d p) := by
    intro l hl
    rw [Nat.mem_divisors] at hl
    have hl0 : l ≠ 0 := by
      intro hc
      exact hl.2 (by rw [hc] at hl; exact zero_dvd_iff.1 hl.1)
    exact selbergTerms_roughPairSieve Y hP₁ h d hz hl.1 hl0
  rw [Finset.sum_congr rfl hcongr, rangePrimorial]
  exact sum_divisors_prod_primes_eq_prod hprime
    (fun p => pairClassCount d p / ((p : ℝ) - pairClassCount d p))

/-- The Selberg terms of the pair sieve are nonnegative on divisors of the modulus. -/
theorem selbergTerms_roughPairSieve_nonneg (Y : ℝ) {P₁ : ℕ} (hP₁ : 2 ≤ P₁) (h d : ℕ) {z : ℝ}
    (hz : 1 ≤ z) {l : ℕ} (hl : l ∣ rangePrimorial P₁ h) (hl0 : l ≠ 0) :
    0 ≤ SelbergSieve.selbergTerms (roughPairSieve Y hP₁ h d hz).toBoundingSieve l := by
  rw [selbergTerms_roughPairSieve Y hP₁ h d hz hl hl0]
  refine Finset.prod_nonneg fun p hp => ?_
  have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpP : p ∣ rangePrimorial P₁ h := (Nat.dvd_of_mem_primeFactors hp).trans hl
  have hmem : p ∈ rangePrimes P₁ h :=
    mem_of_prime_dvd_prod (fun q hq => rangePrimes_prime hq) hprime hpP
  rw [rangePrimes, Finset.mem_filter, Finset.mem_Icc] at hmem
  have h3 : (3 : ℝ) ≤ (p : ℝ) := by
    have : 3 ≤ p := by omega
    exact_mod_cast this
  have hc : pairClassCount d p ≤ 2 ∧ 0 ≤ pairClassCount d p := by
    rw [pairClassCount]; constructor <;> split_ifs <;> norm_num
  have hden : (0 : ℝ) < (p : ℝ) - pairClassCount d p := by linarith [hc.1]
  exact div_nonneg hc.2 hden.le

/-- **The bounding sum of the pair sieve keeps half its Euler product.**  Divisors with at most `k`
prime factors are automatically below the sieve level, and by the powerset tail bound they carry at
least half the product. -/
theorem selbergBoundingSum_roughPairSieve_ge (Y : ℝ) {P₁ : ℕ} (hP₁ : 2 ≤ P₁) {h : ℕ} (d k : ℕ)
    {z : ℝ} (hz : 1 ≤ z) (hh1 : 1 ≤ h) (hlev : ((h : ℝ)) ^ (2 * k) ≤ z)
    (hk : Real.exp 1
        * (∑ p ∈ rangePrimes P₁ h, pairClassCount d p / ((p : ℝ) - pairClassCount d p))
        + Real.log 2 ≤ (k : ℝ)) :
    (1 / 2) * ∏ p ∈ rangePrimes P₁ h,
        (pairClassCount d p / ((p : ℝ) - pairClassCount d p) + 1)
      ≤ SelbergSieve.selbergBoundingSum (roughPairSieve Y hP₁ h d hz) := by
  classical
  set s : Finset ℕ := rangePrimes P₁ h with hs
  set a : ℕ → ℝ := fun p => pairClassCount d p / ((p : ℝ) - pairClassCount d p) with ha
  have hprime : ∀ p ∈ s, p.Prime := fun p hp => rangePrimes_prime hp
  have ha0 : ∀ p ∈ s, 0 ≤ a p := by
    intro p hp
    rw [hs, rangePrimes, Finset.mem_filter, Finset.mem_Icc] at hp
    have h3 : (3 : ℝ) ≤ (p : ℝ) := by
      have : 3 ≤ p := by omega
      exact_mod_cast this
    have hc : pairClassCount d p ≤ 2 ∧ 0 ≤ pairClassCount d p := by
      rw [pairClassCount]; constructor <;> split_ifs <;> norm_num
    rw [ha]
    exact div_nonneg hc.2 (by linarith [hc.1])
  refine le_trans (sum_powerset_card_le_ge ha0 k hk) ?_
  -- reindex the truncated powerset sum back into the bounding sum
  have hinj : Set.InjOn (fun t => ∏ p ∈ t, p)
      ((s.powerset.filter (fun t => t.card ≤ k) : Finset (Finset ℕ)) : Set (Finset ℕ)) := by
    intro t ht u hu hEq
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_powerset] at ht hu
    have h1 : (∏ p ∈ t, p).primeFactors = t :=
      Nat.primeFactors_prod fun p hp => hprime p (ht.1 hp)
    have h2 : (∏ p ∈ u, p).primeFactors = u :=
      Nat.primeFactors_prod fun p hp => hprime p (hu.1 hp)
    rw [← h1, ← h2]
    exact congrArg Nat.primeFactors hEq
  set G : ℕ → ℝ := fun l =>
    if (l : ℝ) ^ 2 ≤ z then
      SelbergSieve.selbergTerms (roughPairSieve Y hP₁ h d hz).toBoundingSieve l else 0 with hG
  have hterm : ∀ t ∈ s.powerset.filter (fun t => t.card ≤ k),
      (∏ p ∈ t, a p) = G (∏ p ∈ t, p) := by
    intro t ht
    rw [Finset.mem_filter, Finset.mem_powerset] at ht
    have hdvd : (∏ p ∈ t, p) ∣ rangePrimorial P₁ h := by
      rw [rangePrimorial, ← hs]
      exact Finset.prod_dvd_prod_of_subset _ _ _ ht.1
    have h0 : (∏ p ∈ t, p) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.2 fun p hp => ?_
      exact (hprime p (ht.1 hp)).ne_zero
    have hsize : (((∏ p ∈ t, p : ℕ)) : ℝ) ^ 2 ≤ z := by
      have hhR : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh1
      have hple : ∀ p ∈ t, p ≤ h := by
        intro p hp
        have := ht.1 hp
        rw [hs, rangePrimes, Finset.mem_filter, Finset.mem_Icc] at this
        exact this.1.2
      have hprod : (∏ p ∈ t, p) ≤ h ^ t.card := by
        calc (∏ p ∈ t, p) ≤ ∏ _p ∈ t, h := Finset.prod_le_prod' hple
          _ = h ^ t.card := by rw [Finset.prod_const]
      have hcast : (((∏ p ∈ t, p : ℕ)) : ℝ) ≤ ((h : ℝ)) ^ t.card := by
        have := hprod
        calc (((∏ p ∈ t, p : ℕ)) : ℝ) ≤ ((h ^ t.card : ℕ) : ℝ) := by exact_mod_cast this
          _ = ((h : ℝ)) ^ t.card := by push_cast; ring
      have hmono : ((h : ℝ)) ^ t.card ≤ ((h : ℝ)) ^ k := pow_le_pow_right₀ hhR ht.2
      have hnn : (0 : ℝ) ≤ (((∏ p ∈ t, p : ℕ)) : ℝ) := Nat.cast_nonneg _
      have hsq : (((∏ p ∈ t, p : ℕ)) : ℝ) ^ 2 ≤ (((h : ℝ)) ^ k) ^ 2 := by
        refine pow_le_pow_left₀ hnn (le_trans hcast hmono) 2
      calc (((∏ p ∈ t, p : ℕ)) : ℝ) ^ 2 ≤ (((h : ℝ)) ^ k) ^ 2 := hsq
        _ = ((h : ℝ)) ^ (2 * k) := by rw [← pow_mul]; ring_nf
        _ ≤ z := hlev
    rw [hG]
    simp only
    rw [if_pos hsize, selbergTerms_roughPairSieve Y hP₁ h d hz hdvd h0,
      Nat.primeFactors_prod fun p hp => hprime p (ht.1 hp)]
  have hkey : ∑ t ∈ s.powerset.filter (fun t => t.card ≤ k), ∏ p ∈ t, a p
      ≤ SelbergSieve.selbergBoundingSum (roughPairSieve Y hP₁ h d hz) := by
    show _ ≤ ∑ l ∈ (rangePrimorial P₁ h).divisors, G l
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_image hinj]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro l hl
      rw [Finset.mem_image] at hl
      obtain ⟨t, ht, rfl⟩ := hl
      rw [Finset.mem_filter, Finset.mem_powerset] at ht
      refine Nat.mem_divisors.2 ⟨?_, ?_⟩
      · rw [rangePrimorial, ← hs]
        exact Finset.prod_dvd_prod_of_subset _ _ _ ht.1
      · refine Finset.prod_ne_zero_iff.2 fun p hp => ?_
        exact (hprime p hp).ne_zero
    · intro l hl _
      rw [Nat.mem_divisors] at hl
      have hl0 : l ≠ 0 := by
        intro hc
        exact hl.2 (by rw [hc] at hl; exact zero_dvd_iff.1 hl.1)
      rw [hG]
      simp only
      split_ifs
      · exact selbergTerms_roughPairSieve_nonneg Y hP₁ h d hz hl.1 hl0
      · exact le_rfl
  exact hkey

end

end RHTower.Sieve
