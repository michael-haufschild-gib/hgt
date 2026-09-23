import GaloisForLFunctions.RHTower.PrimeValuationHellingerReesReflectionFracture
import GaloisForLFunctions.HTGeometry.DyadicReflectionJetLaw

/-!
# The reflected Hellinger sewing cost is a dyadic Euler-log combination

The finite-prime squared Hellinger affinity between the critical valuation law and radial drift `c`
factors through the finite prime partition function

```text
Z_N(s) = ∏_{p < N} (1 - p^(-s))⁻¹,      P_N(s) = log Z_N(s)
```

as `H_N(c) = Z_N(1-c)^(2 : ℕ) / (Z_N(1) Z_N(1-2c))`.  Hence the logarithm of the reflected sewing
multiplier `S_N(c) = H_N(-c)/H_N(c)` is exactly the dyadic reflection combination of `P_N` at the
centre `s = 1`:

```text
log S_N(c) = P_N(1-2c) - P_N(1+2c) - 2 P_N(1-c) + 2 P_N(1+c).
```

The all-orders jet law for that combination therefore applies verbatim: the sewing cost vanishes to
order three at the lossless boundary, its third derivative there is `-12 P_N'''(1)`, all even orders
vanish, and every odd order `n` is `-2(2^n - 2) P_N^(n)(1)`.
-/

open Set

namespace RHTower

noncomputable section

/-! ## Positivity of the finite prime partition -/

/-- On the convergent side each local Euler factor is a proper probability defect. -/
theorem one_sub_rpow_pos {p : ℕ} (hp : p.Prime) {s : ℝ} (hs : 0 < s) :
    0 < 1 - (p : ℝ) ^ (-s) := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hlt : (p : ℝ) ^ (-s) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  linarith

/-- The finite prime partition function is positive on the convergent side. -/
theorem realPrimeEulerPartitionBelow_pos {s : ℝ} (hs : 0 < s) (N : ℕ) :
    0 < realPrimeEulerPartitionBelow s N := by
  rw [realPrimeEulerPartitionBelow]
  refine Finset.prod_pos fun p hp => ?_
  exact inv_pos.mpr (one_sub_rpow_pos (Nat.prime_of_mem_primesBelow hp) hs)

/-! ## The Euler logarithm -/

/-- The finite prime Euler logarithm `P_N(s) = log Z_N(s)`. -/
def primeEulerLogBelow (s : ℝ) (N : ℕ) : ℝ := Real.log (realPrimeEulerPartitionBelow s N)

/-- The Euler logarithm is the finite sum of local defect logarithms. -/
theorem primeEulerLogBelow_eq_sum {s : ℝ} (hs : 0 < s) (N : ℕ) :
    primeEulerLogBelow s N
      = ∑ p ∈ Nat.primesBelow N, -Real.log (1 - (p : ℝ) ^ (-s)) := by
  rw [primeEulerLogBelow, realPrimeEulerPartitionBelow,
    Real.log_prod (fun p hp => inv_ne_zero
      (ne_of_gt (one_sub_rpow_pos (Nat.prime_of_mem_primesBelow hp) hs)))]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Real.log_inv]

/-! ## The Euler factorization of the squared Hellinger affinity -/

/-- **The finite Euler factorization.**  `H_N(c) = Z_N(1-c)^(2 : ℕ) / (Z_N(1) Z_N(1-2c))`. -/
theorem primeValuationSquaredHellingerBelow_eq_partitionRatio {c : ℝ} (h1 : 0 < 1 - 2 * c)
    (h2 : 0 < 1 - c) (N : ℕ) :
    primeValuationSquaredHellingerBelow c N
      = realPrimeEulerPartitionBelow (1 - c) N ^ 2 /
          (realPrimeEulerPartitionBelow 1 N * realPrimeEulerPartitionBelow (1 - 2 * c) N) := by
  rw [primeValuationSquaredHellingerBelow, realPrimeEulerPartitionBelow,
    realPrimeEulerPartitionBelow, realPrimeEulerPartitionBelow, ← Finset.prod_pow,
    ← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hprime := Nat.prime_of_mem_primesBelow hp
  have hA : 0 < 1 - (p : ℝ) ^ (-(1 : ℝ)) := one_sub_rpow_pos hprime one_pos
  have hB : 0 < 1 - (p : ℝ) ^ (-(1 - 2 * c)) := one_sub_rpow_pos hprime h1
  have hC : 0 < 1 - (p : ℝ) ^ (-(1 - c)) := one_sub_rpow_pos hprime h2
  have hinv : (p : ℝ) ^ (-(1 : ℝ)) = ((p : ℝ))⁻¹ := Real.rpow_neg_one _
  rw [primeValuationSquaredHellingerFactorNat_of_prime c hprime]
  simp only [primeValuationSquaredHellingerFactor, squaredHellingerAffinity,
    primeRadialCriticalMass, primeRadialTwistedMass, primeRadialCrossMass]
  rw [← hinv]
  rw [hinv] at hA
  field_simp

/-! ## The reflected sewing cost -/

/-- The reflected squared sewing multiplier `S_N(c) = H_N(-c)/H_N(c)`. -/
def reflectedSewingMultiplierBelow (c : ℝ) (N : ℕ) : ℝ :=
  primeValuationSquaredHellingerBelow (-c) N / primeValuationSquaredHellingerBelow c N

/-- Its logarithm, the reflected Hellinger sewing cost. -/
def logReflectedSewingBelow (c : ℝ) (N : ℕ) : ℝ :=
  Real.log (reflectedSewingMultiplierBelow c N)

/-- **The sewing cost is the dyadic Euler-log combination.** -/
theorem logReflectedSewingBelow_eq {c : ℝ} (hc : |c| < 1 / 2) (N : ℕ) :
    logReflectedSewingBelow c N
      = primeEulerLogBelow (1 - 2 * c) N - primeEulerLogBelow (1 + 2 * c) N
        - 2 * primeEulerLogBelow (1 - c) N + 2 * primeEulerLogBelow (1 + c) N := by
  obtain ⟨hcl, hcu⟩ := abs_lt.mp hc
  have e1 : (1 : ℝ) - -c = 1 + c := by ring
  have e2 : (1 : ℝ) - 2 * -c = 1 + 2 * c := by ring
  have hpos1 : (0 : ℝ) < 1 - 2 * c := by linarith
  have hpos2 : (0 : ℝ) < 1 - c := by linarith
  have hpos3 : (0 : ℝ) < 1 + 2 * c := by linarith
  have hpos4 : (0 : ℝ) < 1 + c := by linarith
  have hZ1 : 0 < realPrimeEulerPartitionBelow 1 N := realPrimeEulerPartitionBelow_pos one_pos N
  have hZ2 : 0 < realPrimeEulerPartitionBelow (1 - c) N :=
    realPrimeEulerPartitionBelow_pos hpos2 N
  have hZ3 : 0 < realPrimeEulerPartitionBelow (1 - 2 * c) N :=
    realPrimeEulerPartitionBelow_pos hpos1 N
  have hZ4 : 0 < realPrimeEulerPartitionBelow (1 + c) N :=
    realPrimeEulerPartitionBelow_pos hpos4 N
  have hZ5 : 0 < realPrimeEulerPartitionBelow (1 + 2 * c) N :=
    realPrimeEulerPartitionBelow_pos hpos3 N
  have hHc := primeValuationSquaredHellingerBelow_eq_partitionRatio hpos1 hpos2 N
  have hHnegc := primeValuationSquaredHellingerBelow_eq_partitionRatio
    (c := -c) (by linarith) (by linarith) N
  rw [e1, e2] at hHnegc
  have hratio : reflectedSewingMultiplierBelow c N
      = realPrimeEulerPartitionBelow (1 + c) N ^ 2 *
          realPrimeEulerPartitionBelow (1 - 2 * c) N /
        (realPrimeEulerPartitionBelow (1 + 2 * c) N *
          realPrimeEulerPartitionBelow (1 - c) N ^ 2) := by
    rw [reflectedSewingMultiplierBelow, hHc, hHnegc]
    field_simp
  rw [logReflectedSewingBelow, hratio, Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow]
  simp only [primeEulerLogBelow, Nat.cast_ofNat]
  ring

/-- **The sewing cost is literally the dyadic reflection combination at the centre `1`.** -/
theorem logReflectedSewingBelow_eq_dyadic {c : ℝ} (hc : |c| < 1 / 2) (N : ℕ) :
    logReflectedSewingBelow c N
      = GaloisForLFunctions.dyadicReflectionCombination
          (fun s => primeEulerLogBelow s N) 1 c := by
  rw [logReflectedSewingBelow_eq hc, GaloisForLFunctions.dyadicReflectionCombination]

/-! ## Smoothness of the Euler logarithm -/

/-- Each local Euler defect logarithm is smooth on the convergent side. -/
theorem contDiffAt_neg_log_one_sub_rpow {p : ℕ} (hp : p.Prime) (n : ℕ) {s : ℝ} (hs : 0 < s) :
    ContDiffAt ℝ n (fun t : ℝ => -Real.log (1 - (p : ℝ) ^ (-t))) s := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast hp.pos
  have hbase : ContDiffAt ℝ n (fun t : ℝ => 1 - (p : ℝ) ^ (-t)) s := by
    have hrw : (fun t : ℝ => 1 - (p : ℝ) ^ (-t))
        = fun t : ℝ => 1 - Real.exp (Real.log (p : ℝ) * -t) := by
      funext t
      rw [Real.rpow_def_of_pos hp0]
    rw [hrw]
    exact contDiffAt_const.sub (by fun_prop)
  exact (hbase.log (ne_of_gt (one_sub_rpow_pos hp hs))).neg

/-- **The Euler logarithm is smooth on the convergent half-line.** -/
theorem contDiffOn_primeEulerLogBelow (n : ℕ) (N : ℕ) :
    ContDiffOn ℝ n (fun s => primeEulerLogBelow s N) (Ioi 0) := by
  intro s hs
  have hs0 : (0 : ℝ) < s := hs
  have hsum : ContDiffAt ℝ n
      (fun t : ℝ => ∑ p ∈ Nat.primesBelow N, -Real.log (1 - (p : ℝ) ^ (-t))) s :=
    ContDiffAt.sum fun p hp =>
      contDiffAt_neg_log_one_sub_rpow (Nat.prime_of_mem_primesBelow hp) n hs0
  have heq : (fun t : ℝ => ∑ p ∈ Nat.primesBelow N, -Real.log (1 - (p : ℝ) ^ (-t)))
      =ᶠ[nhds s] fun t => primeEulerLogBelow t N := by
    refine Filter.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds hs) ?_
    intro t ht
    exact (primeEulerLogBelow_eq_sum ht N).symm
  exact (hsum.congr_of_eventuallyEq heq.symm).contDiffWithinAt

/-! ## The jet tower of the sewing cost -/

/-- The sewing cost agrees with the dyadic combination near the lossless boundary. -/
theorem logReflectedSewing_eventuallyEq_dyadic (N : ℕ) :
    (fun c => logReflectedSewingBelow c N)
      =ᶠ[nhds 0] fun c => GaloisForLFunctions.dyadicReflectionCombination
        (fun s => primeEulerLogBelow s N) 1 c := by
  refine Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds
    (show (0 : ℝ) ∈ Ioo (-(1 / 2) : ℝ) (1 / 2) by constructor <;> norm_num)) ?_
  intro c hc
  refine logReflectedSewingBelow_eq_dyadic ?_ N
  obtain ⟨h1, h2⟩ := hc
  exact abs_lt.mpr ⟨h1, h2⟩

/-- **The all-orders jet law for the reflected sewing cost.** -/
theorem iteratedDeriv_logReflectedSewing (n : ℕ) (N : ℕ) :
    iteratedDeriv n (fun c => logReflectedSewingBelow c N) 0
      = ((-2 : ℝ) ^ n - 2 ^ n - 2 * ((-1 : ℝ) ^ n - 1)) *
        iteratedDeriv n (fun s => primeEulerLogBelow s N) 1 := by
  rw [Filter.EventuallyEq.iteratedDeriv_eq n (logReflectedSewing_eventuallyEq_dyadic N)]
  exact GaloisForLFunctions.iteratedDeriv_dyadicReflectionCombination_of_contDiffOn
    isOpen_Ioi (by norm_num) (contDiffOn_primeEulerLogBelow n N)

/-- Even orders of the sewing cost vanish. -/
theorem iteratedDeriv_logReflectedSewing_even {n : ℕ} (hn : Even n) (N : ℕ) :
    iteratedDeriv n (fun c => logReflectedSewingBelow c N) 0 = 0 := by
  rw [iteratedDeriv_logReflectedSewing n N, hn.neg_pow, hn.neg_one_pow]
  ring

/-- **Odd orders of the sewing cost are `-2(2^n - 2)` times the Euler-log jet at the centre.** -/
theorem iteratedDeriv_logReflectedSewing_odd {n : ℕ} (hn : Odd n) (N : ℕ) :
    iteratedDeriv n (fun c => logReflectedSewingBelow c N) 0
      = -2 * (2 ^ n - 2) * iteratedDeriv n (fun s => primeEulerLogBelow s N) 1 := by
  rw [iteratedDeriv_logReflectedSewing n N, hn.neg_pow, hn.neg_one_pow]
  ring

/-- The sewing cost vanishes at the lossless boundary. -/
theorem logReflectedSewing_zero (N : ℕ) : logReflectedSewingBelow 0 N = 0 := by
  have h := logReflectedSewingBelow_eq_dyadic (c := 0) (by norm_num) N
  rw [h, GaloisForLFunctions.dyadicReflectionCombination_zero]

/-- First and second orders vanish, so the cost has cubic contact at the boundary. -/
theorem iteratedDeriv_one_logReflectedSewing (N : ℕ) :
    iteratedDeriv 1 (fun c => logReflectedSewingBelow c N) 0 = 0 := by
  rw [iteratedDeriv_logReflectedSewing 1 N]
  norm_num

theorem iteratedDeriv_two_logReflectedSewing (N : ℕ) :
    iteratedDeriv 2 (fun c => logReflectedSewingBelow c N) 0 = 0 :=
  iteratedDeriv_logReflectedSewing_even (by decide) N

/-- **Exact cubic confluence.**  The third jet of the sewing cost is `-12 P_N'''(1)`. -/
theorem iteratedDeriv_three_logReflectedSewing (N : ℕ) :
    iteratedDeriv 3 (fun c => logReflectedSewingBelow c N) 0
      = -12 * iteratedDeriv 3 (fun s => primeEulerLogBelow s N) 1 := by
  rw [iteratedDeriv_logReflectedSewing 3 N]
  norm_num

/-! ## Oddness of the sewing cost -/

/-- The squared Hellinger affinity is positive on the strip. -/
theorem primeValuationSquaredHellingerBelow_pos_of_abs_lt {c : ℝ} (hc : |c| < 1 / 2) (N : ℕ) :
    0 < primeValuationSquaredHellingerBelow c N := by
  obtain ⟨hcl, hcu⟩ := abs_lt.mp hc
  have hpos1 : (0 : ℝ) < 1 - 2 * c := by linarith
  have hpos2 : (0 : ℝ) < 1 - c := by linarith
  rw [primeValuationSquaredHellingerBelow_eq_partitionRatio hpos1 hpos2 N]
  have hZ1 : 0 < realPrimeEulerPartitionBelow 1 N := realPrimeEulerPartitionBelow_pos one_pos N
  have hZ2 : 0 < realPrimeEulerPartitionBelow (1 - c) N :=
    realPrimeEulerPartitionBelow_pos hpos2 N
  have hZ3 : 0 < realPrimeEulerPartitionBelow (1 - 2 * c) N :=
    realPrimeEulerPartitionBelow_pos hpos1 N
  positivity

/-- **The sewing cost is odd**: reflecting the drift inverts the sewing multiplier. -/
theorem logReflectedSewingBelow_neg {c : ℝ} (hc : |c| < 1 / 2) (N : ℕ) :
    logReflectedSewingBelow (-c) N = -logReflectedSewingBelow c N := by
  have hcneg : |(-c)| < 1 / 2 := by rwa [abs_neg]
  have hHc : 0 < primeValuationSquaredHellingerBelow c N :=
    primeValuationSquaredHellingerBelow_pos_of_abs_lt hc N
  have hHnegc : 0 < primeValuationSquaredHellingerBelow (-c) N :=
    primeValuationSquaredHellingerBelow_pos_of_abs_lt hcneg N
  have hinv : reflectedSewingMultiplierBelow (-c) N
      = (reflectedSewingMultiplierBelow c N)⁻¹ := by
    rw [reflectedSewingMultiplierBelow, reflectedSewingMultiplierBelow, neg_neg]
    rw [inv_div]
  rw [logReflectedSewingBelow, logReflectedSewingBelow, hinv, Real.log_inv]

end

end RHTower
