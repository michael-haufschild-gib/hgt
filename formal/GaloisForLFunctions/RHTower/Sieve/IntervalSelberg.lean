import GaloisForLFunctions.RHTower.Sieve.SelbergCoefficient
import GaloisForLFunctions.RHTower.Sieve.Mertens

/-!
# The Selberg sieve of an integer interval

Sieving `Ioc a b` by the primes up to `z` is the `BoundingSieve` with unit weights, total mass
`b - a`, sifting modulus the primorial `z#`, and density `ν d = 1/d`.  Its remainders are the
interval multiple counts, so `|R_d| < 1` for every `d` — the input `abs_card_filter_dvd_Ioc_sub_lt`
already provides.

For this sieve the Selberg terms are `g_l = ∏_{p ∣ l} 1/(p-1)`, and the truncated Selberg bound
reads

`#{n ∈ (a,b] : P⁻(n) > z} ≤ (b-a)/S_Y + errSum`,

with the error supported on `d ≤ Y²` and each coefficient bounded by one.  Taking `Y` as large as
the interval allows makes `log(Y²) ≍ log(b-a)`, which is the level Brun's pure sieve cannot reach.
-/

namespace RHTower.Sieve

open Finset Nat BoundingSieve

/-- The reciprocal density `d ↦ 1/d`, as an arithmetic function. -/
noncomputable def invNat : ArithmeticFunction ℝ where
  toFun d := if d = 0 then 0 else (d : ℝ)⁻¹
  map_zero' := by simp

theorem invNat_apply {d : ℕ} (hd : d ≠ 0) : invNat d = (d : ℝ)⁻¹ := by
  simp [invNat, hd]

theorem isMultiplicative_invNat : ArithmeticFunction.IsMultiplicative invNat := by
  constructor
  · simp [invNat]
  · intro m n hmn
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have hn : n = 1 := by simpa [Nat.Coprime] using hmn
      subst hn
      simp [invNat]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hm1 : m = 1 := by simpa [Nat.Coprime] using hmn
      subst hm1
      simp [invNat]
    have hm0 : m ≠ 0 := by omega
    have hn0 : n ≠ 0 := by omega
    have hmn0 : m * n ≠ 0 := Nat.mul_ne_zero hm0 hn0
    rw [invNat_apply hmn0, invNat_apply hm0, invNat_apply hn0]
    push_cast
    rw [mul_inv]

/-- The Selberg sieve of the interval `Ioc a b` by the primes up to `z`. -/
noncomputable def intervalSieve (a b z : ℕ) : BoundingSieve where
  support := Finset.Ioc a b
  prodPrimes := primorial z
  prodPrimes_squarefree := squarefree_primorial z
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := (b : ℝ) - a
  nu := invNat
  nu_mult := isMultiplicative_invNat
  nu_pos_of_prime := fun p hp _ => by
    rw [invNat_apply hp.ne_zero]
    have : (0 : ℝ) < p := by exact_mod_cast hp.pos
    positivity
  nu_lt_one_of_prime := fun p hp _ => by
    rw [invNat_apply hp.ne_zero]
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    rw [inv_lt_one_iff₀]
    right
    linarith

@[simp]
theorem intervalSieve_prodPrimes (a b z : ℕ) : (intervalSieve a b z).prodPrimes = primorial z :=
  rfl

@[simp]
theorem intervalSieve_totalMass (a b z : ℕ) :
    (intervalSieve a b z).totalMass = (b : ℝ) - a := rfl

/-- The multiple sums of the interval sieve are the interval multiple counts. -/
theorem intervalSieve_multSum (a b z d : ℕ) :
    (intervalSieve a b z).multSum d = ((#{n ∈ Finset.Ioc a b | d ∣ n} : ℕ) : ℝ) := by
  classical
  rw [multSum]
  exact (Finset.natCast_card_filter (fun n => d ∣ n) (Finset.Ioc a b)).symm

/-- The sifted sum of the interval sieve counts the rough integers. -/
theorem intervalSieve_siftedSum (a b z : ℕ) :
    (intervalSieve a b z).siftedSum
      = ((#{n ∈ Finset.Ioc a b | Nat.Coprime (primorial z) n} : ℕ) : ℝ) := by
  classical
  rw [siftedSum]
  exact (Finset.natCast_card_filter (fun n => Nat.Coprime (primorial z) n)
    (Finset.Ioc a b)).symm

/-- **Unit remainders.**  Every remainder of the interval sieve is bounded by one. -/
theorem abs_intervalSieve_rem_le (a b z : ℕ) {d : ℕ} (hd : 0 < d) (hab : a ≤ b) :
    |(intervalSieve a b z).rem d| ≤ 1 := by
  have hd0 : d ≠ 0 := hd.ne'
  have hrem : (intervalSieve a b z).rem d
      = ((#{n ∈ Finset.Ioc a b | d ∣ n} : ℕ) : ℝ) - ((b : ℝ) - a) / d := by
    rw [rem, intervalSieve_multSum, intervalSieve_totalMass]
    congr 1
    show invNat d * ((b : ℝ) - a) = ((b : ℝ) - a) / d
    rw [invNat_apply hd0]
    ring
  rw [hrem]
  exact (abs_card_filter_dvd_Ioc_sub_lt d a b hd hab).le

/-- The Selberg terms of the interval sieve. -/
theorem intervalSieve_selbergTerms (a b z : ℕ) {d : ℕ} (hd : d ≠ 0) :
    (intervalSieve a b z).selbergTerms d
      = (d : ℝ)⁻¹ * ∏ p ∈ d.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹ := by
  rw [selbergTerms_apply]
  congr 1
  · exact invNat_apply hd
  · refine Finset.prod_congr rfl ?_
    intro p hp
    congr 2
    exact invNat_apply (Nat.prime_of_mem_primeFactors hp).ne_zero

/-- **Selberg sieve for an interval.**  The rough-integer count is bounded by the interval length
over the truncated Selberg mass, plus an error carried by divisors up to `Y²`, each with a
coefficient of absolute value at most one. -/
theorem card_coprime_Ioc_le_selberg (a b z : ℕ) (hab : a ≤ b) {Y : ℕ} (hY : 1 ≤ Y) :
    ((#{n ∈ Finset.Ioc a b | Nat.Coprime (primorial z) n} : ℕ) : ℝ)
      ≤ ((b : ℝ) - a) / selbergMassLE (intervalSieve a b z) Y
        + ∑ d ∈ (primorial z).divisors,
            |lambdaSquared (selbergTruncWeight (intervalSieve a b z) Y) d| := by
  have hbase := siftedSum_le_selbergTrunc (intervalSieve a b z) hY
  rw [intervalSieve_siftedSum, intervalSieve_totalMass] at hbase
  have herr : (intervalSieve a b z).errSum
        (lambdaSquared (selbergTruncWeight (intervalSieve a b z) Y))
      ≤ ∑ d ∈ (primorial z).divisors,
          |lambdaSquared (selbergTruncWeight (intervalSieve a b z) Y) d| := by
    rw [errSum]
    refine Finset.sum_le_sum ?_
    intro d hd
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    have hrem := abs_intervalSieve_rem_le a b z hdpos hab
    have hnn : (0 : ℝ) ≤ |lambdaSquared (selbergTruncWeight (intervalSieve a b z) Y) d| :=
      abs_nonneg _
    nlinarith [hrem, hnn]
  linarith [hbase, herr]

/-- Each Selberg term of the interval sieve dominates the reciprocal. -/
theorem inv_le_intervalSieve_selbergTerms (a b z : ℕ) {l : ℕ} (hl : l ∣ primorial z) :
    (l : ℝ)⁻¹ ≤ (intervalSieve a b z).selbergTerms l := by
  have hl0 : l ≠ 0 := by
    intro h
    exact (squarefree_primorial z).ne_zero (Nat.eq_zero_of_zero_dvd (h ▸ hl))
  have hlpos : (0 : ℝ) < l := by
    have : 0 < l := Nat.pos_of_ne_zero hl0
    exact_mod_cast this
  rw [intervalSieve_selbergTerms a b z hl0]
  have hfac : ∀ p ∈ l.primeFactors, (1 : ℝ) ≤ (1 - (p : ℝ)⁻¹)⁻¹ := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hpinv : (p : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    have hpos : (0 : ℝ) < 1 - (p : ℝ)⁻¹ := by
      have : (0 : ℝ) < (p : ℝ)⁻¹ := by positivity
      linarith
    rw [le_inv_comm₀ (by norm_num) hpos, inv_one]
    have hppos : (0 : ℝ) < (p : ℝ)⁻¹ := by positivity
    linarith
  have hprod : (1 : ℝ) ≤ ∏ p ∈ l.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹ := by
    have h := Finset.prod_le_prod (s := l.primeFactors) (f := fun _ : ℕ => (1 : ℝ))
      (g := fun p : ℕ => (1 - (p : ℝ)⁻¹)⁻¹) (fun i _ => zero_le_one) hfac
    simpa using h
  calc (l : ℝ)⁻¹ = (l : ℝ)⁻¹ * 1 := by ring
    _ ≤ (l : ℝ)⁻¹ * ∏ p ∈ l.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹ := by
        refine mul_le_mul_of_nonneg_left hprod ?_
        positivity

/-- A squarefree number below the sieve cut divides the primorial. -/
theorem dvd_primorial_of_squarefree {l z : ℕ} (hl : Squarefree l) (hlz : l ≤ z) :
    l ∣ primorial z := by
  have hsub : l.primeFactors ⊆ Nat.primesLE z := by
    intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hple : p ≤ l := Nat.le_of_dvd (Nat.pos_of_ne_zero hl.ne_zero)
      (Nat.dvd_of_mem_primeFactors hp)
    exact Nat.mem_primesLE.2 ⟨le_trans hple hlz, hprime⟩
  have hprod : ∏ p ∈ l.primeFactors, p = l := Nat.prod_primeFactors_of_squarefree hl
  rw [primorial_eq_prod_primesLE, ← hprod]
  exact Finset.prod_dvd_prod_of_subset _ _ _ hsub

/-- **Mass lower bound.**  The truncated Selberg mass dominates the reciprocal sum of the
squarefree numbers below the truncation. -/
theorem sum_inv_squarefree_le_selbergMassLE (a b z Y : ℕ) (hYz : Y ≤ z) :
    ∑ l ∈ {l ∈ Finset.Icc 1 Y | Squarefree l}, (l : ℝ)⁻¹
      ≤ selbergMassLE (intervalSieve a b z) Y := by
  classical
  have hsub : {l ∈ Finset.Icc 1 Y | Squarefree l}
      ⊆ {l ∈ (primorial z).divisors | l ≤ Y} := by
    intro l hl
    obtain ⟨hlmem, hlsq⟩ := Finset.mem_filter.1 hl
    obtain ⟨-, hlY⟩ := Finset.mem_Icc.1 hlmem
    exact Finset.mem_filter.2
      ⟨Nat.mem_divisors.2 ⟨dvd_primorial_of_squarefree hlsq (le_trans hlY hYz),
        (squarefree_primorial z).ne_zero⟩, hlY⟩
  have hstep : ∀ l ∈ {l ∈ Finset.Icc 1 Y | Squarefree l},
      (l : ℝ)⁻¹ ≤ (intervalSieve a b z).selbergTerms l := by
    intro l hl
    obtain ⟨hlmem, hlsq⟩ := Finset.mem_filter.1 hl
    obtain ⟨-, hlY⟩ := Finset.mem_Icc.1 hlmem
    exact inv_le_intervalSieve_selbergTerms a b z
      (dvd_primorial_of_squarefree hlsq (le_trans hlY hYz))
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [selbergMassLE]
  refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
  intro l hl _
  exact (selbergTerms_pos (Nat.dvd_of_mem_divisors (Finset.mem_filter.1 hl).1)).le

end RHTower.Sieve
