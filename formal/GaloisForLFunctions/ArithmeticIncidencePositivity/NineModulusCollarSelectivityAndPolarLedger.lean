import GaloisForLFunctions.ArithmeticIncidencePositivity.TotalAntiDiagonalClassification
import GaloisForLFunctions.ArithmeticIncidencePositivity.ContinuumCrossingRatioBridgeAndMultiAtomWindowLaw
import GaloisForLFunctions.SelectivePositivityAndThresholdLaws.TwoPrimeCatalanSeparationAndContinuumTowerObstruction

/-!
# Nine-Modulus Collar Selectivity, Catalan `(8, 9)` Separation, and the Polar-Paid Ledger

`TotalAntiDiagonalClassification` proved that the total anti-diagonal kernel
`archLevyDensity (log n) + vonMangoldtAtom n - crossingPolarWeight (log n) a` (`n ≥ 2`) fails to be
paid by the `s = 1` pole at its midpoint if and only if `n` belongs to the nine-modulus collar
`totalDominatedModuli = {2, 3, 4, 5, 7, 8, 9, 11, 13}`. On the two-prime sub-window
`[-23/40, 23/40]` (`{2, 3}`), `TwoPrimeCatalanSeparationAndContinuumTowerObstruction` proved smooth
odd Weil selectivity against `liouvilleTwistedVonMangoldt`.

This module extends the selectivity and incidence-ledger theory across the entire nine-modulus
collar:

1. **Exact Identification of the Nine-Modulus Collar Window (`r = 2 * log 2 = (1/2) log 16`):**
   At aperture `r = 2 * log 2`, `2r = log 16`, so `relevantShifts (2 * log 2) = Finset.Icc 2 15`.
   Its prime-power support (`0 < Λ(n)`) is **literally `totalDominatedModuli`**
   (`relevantShifts_two_mul_log_two_filter_vonMangoldt_pos`), while every integer `n ≥ 2` outside
   `totalDominatedModuli` has `totalAntiDiagonalKernel n (log n / 2) ≤ 0`. Consequently, for every
   test `F` supported in `[−2 log 2, 2 log 2]`, both `primeSideCharge F` and the ratio-comb energy
   `combEnergy F (relevantShifts (2 * log 2)) vonMangoldtAtom` reduce with zero error to sums over
   `totalDominatedModuli`.

2. **Archimedean-Free Catalan `(8, 9)` (`2³ + 1 = 3²`) Separation and 7-vs-2 Collar Sign Law:**
   Inside `totalDominatedModuli` sits the Catalan prime-power pair `(8, 9) = (2³, 3²)`. Because
   `Ω(8) = 3` is odd while `Ω(9) = 2` is even, `catalanCubeSquareForm w := w 8 * w (8 + 1)`
   evaluates to `+72^σ (log 2)(log 3) > 0` across every real scale twist `scaleTwistedVonMangoldt σ`
   (`σ ∈ ℝ`) and to `-(log 2)(log 3) < 0` on `liouvilleTwistedVonMangoldt`. Across the entire
   nine-modulus collar, `liouvilleTwistedVonMangoldt` partitions cleanly into `7` strictly negative
   moduli `{2, 3, 5, 7, 8, 11, 13}` and `2` strictly positive squares `{4, 9}`.

3. **Ground-Eigenvalue Antitonicity, Smooth Odd Collar Refutation, and Nine-Modulus Comb Ledger:**
   Support inclusion implies `liouvilleWindowGroundEigenvalue r₂ ≤ liouvilleWindowGroundEigenvalue r₁`
   for `23 / 40 ≤ r₁ ≤ r₂`, certifying `liouvilleWindowGroundEigenvalue r < -3 / 10 < 0` and
   simultaneous smooth odd witnesses `F ∈ C²_c([-r, r])` with `(1 / 25) ∫ F² < Re W_ζ(F ⋆ F̃)` and
   `Re W_{λΛ}(F ⋆ F̃) < -(3 / 10) ∫ F² < 0` across **every** `r ≥ 23 / 40` — in particular at the
   exact nine-modulus collar aperture `r = 2 * log 2` — alongside the nine-modulus ratio-comb
   incidence ledger floor (`fullZeroForm_ge_nineModulusCollar_combLedger`).
-/

open MeasureTheory Set Filter Finset Topology
open scoped BigOperators ArithmeticFunction
open _root_.RHTower _root_.RHTower.CHMDPolar _root_.RHTower.WeilLevyPoleGauss
open _root_.RHTower.ArchimedeanAnomaly
open GaloisForLFunctions.ArithmeticCriticalityTheory
open GaloisForLFunctions.SelectivePositivityAndThresholdLaws

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-! ## §1. Exact Identification of the Nine-Modulus Collar Window `r = 2 * log 2` -/

/-- An integer divisible by two distinct primes is not a prime power. -/
theorem not_isPrimePow_of_dvd_two_primes {n p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hpn : p ∣ n) (hqn : q ∣ n) :
    ¬ IsPrimePow n := by
  intro hpp
  obtain ⟨r, _, hr, _, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
  have h1 := (Nat.prime_dvd_prime_iff_eq hp hr).mp (hp.dvd_of_dvd_pow hpn)
  have h2 := (Nat.prime_dvd_prime_iff_eq hq hr).mp (hq.dvd_of_dvd_pow hqn)
  exact hpq (h1.trans h2.symm)

/-- Positivity of `Λ(n)` characterizes prime powers. -/
theorem vonMangoldt_pos_iff_isPrimePow {n : ℕ} :
    0 < ArithmeticFunction.vonMangoldt n ↔ IsPrimePow n := by
  constructor
  · intro h
    by_contra hnp
    rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hnp] at h
    exact lt_irrefl 0 h
  · intro hpp
    refine lt_of_le_of_ne ArithmeticFunction.vonMangoldt_nonneg (Ne.symm ?_)
    rwa [Ne, ArithmeticFunction.vonMangoldt_eq_zero_iff, not_not]

/-- At the nine-modulus collar aperture `r = 2 * log 2` (`2r = log 16`), the relevant shifts are
precisely `Finset.Icc 2 15`. -/
theorem relevantShifts_two_mul_log_two :
    relevantShifts (2 * Real.log 2) = Finset.Icc 2 15 := by
  have h16 : 2 * (2 * Real.log 2) = Real.log 16 := by
    rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num, Real.log_pow]
    push_cast
    ring
  ext n
  rw [mem_relevantShifts, Finset.mem_Icc, h16]
  constructor
  · rintro ⟨hn2, hlt⟩
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hn16 : (n : ℝ) < 16 := (Real.log_lt_log_iff hn0 (by norm_num)).mp hlt
    have hn16_nat : n < 16 := by exact_mod_cast hn16
    exact ⟨hn2, by omega⟩
  · rintro ⟨hn2, hn15⟩
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hn16 : (n : ℝ) < 16 := by exact_mod_cast (by omega : n < 16)
    exact ⟨hn2, Real.log_lt_log hn0 hn16⟩

/-- Among the relevant shifts of `r = 2 * log 2` (`2 ≤ n ≤ 15`), `0 < Λ(n)` holds if and only if
`n ∈ totalDominatedModuli = {2, 3, 4, 5, 7, 8, 9, 11, 13}`. -/
theorem vonMangoldt_pos_iff_mem_totalDominatedModuli_of_mem_relevantShifts
    {n : ℕ} (hn : n ∈ relevantShifts (2 * Real.log 2)) :
    0 < ArithmeticFunction.vonMangoldt n ↔ n ∈ totalDominatedModuli := by
  rw [relevantShifts_two_mul_log_two, Finset.mem_Icc] at hn
  obtain ⟨hn2, hn15⟩ := hn
  rw [vonMangoldt_pos_iff_isPrimePow]
  simp only [totalDominatedModuli, Finset.mem_insert, Finset.mem_singleton]
  interval_cases n
  · exact iff_of_true (Nat.Prime.isPrimePow Nat.prime_two) (by omega)
  · exact iff_of_true (Nat.Prime.isPrimePow Nat.prime_three) (by omega)
  · exact iff_of_true ((isPrimePow_nat_iff 4).mpr ⟨2, 2, Nat.prime_two, by norm_num, by norm_num⟩)
      (by omega)
  · exact iff_of_true (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 5)) (by omega)
  · exact iff_of_false (not_isPrimePow_of_dvd_two_primes Nat.prime_two Nat.prime_three
      (by norm_num) (by norm_num) (by norm_num)) (by omega)
  · exact iff_of_true (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 7)) (by omega)
  · exact iff_of_true ((isPrimePow_nat_iff 8).mpr ⟨2, 3, Nat.prime_two, by norm_num, by norm_num⟩)
      (by omega)
  · exact iff_of_true ((isPrimePow_nat_iff 9).mpr ⟨3, 2, Nat.prime_three, by norm_num, by norm_num⟩)
      (by omega)
  · exact iff_of_false (not_isPrimePow_of_dvd_two_primes Nat.prime_two
      (by norm_num : Nat.Prime 5) (by norm_num) (by norm_num) (by norm_num)) (by omega)
  · exact iff_of_true (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 11)) (by omega)
  · exact iff_of_false (not_isPrimePow_of_dvd_two_primes Nat.prime_two Nat.prime_three
      (by norm_num) (by norm_num) (by norm_num)) (by omega)
  · exact iff_of_true (Nat.Prime.isPrimePow (by norm_num : Nat.Prime 13)) (by omega)
  · exact iff_of_false (not_isPrimePow_of_dvd_two_primes Nat.prime_two
      (by norm_num : Nat.Prime 7) (by norm_num) (by norm_num) (by norm_num)) (by omega)
  · exact iff_of_false (not_isPrimePow_of_dvd_two_primes Nat.prime_three
      (by norm_num : Nat.Prime 5) (by norm_num) (by norm_num) (by norm_num)) (by omega)

/-- **Exact Prime-Power Collar Identification:**
Filtering `relevantShifts (2 * log 2)` to prime powers (`0 < Λ(n)`) produces literally the
nine-modulus collar `totalDominatedModuli = {2, 3, 4, 5, 7, 8, 9, 11, 13}`. -/
theorem relevantShifts_two_mul_log_two_filter_vonMangoldt_pos :
    (relevantShifts (2 * Real.log 2)).filter (fun n => 0 < ArithmeticFunction.vonMangoldt n) =
      totalDominatedModuli := by
  ext n
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hn, hpos⟩
    exact (vonMangoldt_pos_iff_mem_totalDominatedModuli_of_mem_relevantShifts hn).mp hpos
  · intro hmem
    have hn : n ∈ relevantShifts (2 * Real.log 2) := by
      rw [relevantShifts_two_mul_log_two, Finset.mem_Icc]
      simp only [totalDominatedModuli, Finset.mem_insert, Finset.mem_singleton] at hmem
      omega
    exact ⟨hn, (vonMangoldt_pos_iff_mem_totalDominatedModuli_of_mem_relevantShifts hn).mpr hmem⟩

/-- `totalDominatedModuli` is a subset of `relevantShifts (2 * log 2)`. -/
theorem totalDominatedModuli_subset_relevantShifts_two_mul_log_two :
    totalDominatedModuli ⊆ relevantShifts (2 * Real.log 2) := by
  rw [← relevantShifts_two_mul_log_two_filter_vonMangoldt_pos]
  exact Finset.filter_subset _ _

/-- Every shift in `relevantShifts (2 * log 2)` outside `totalDominatedModuli` carries zero atom. -/
theorem vonMangoldtAtom_eq_zero_of_mem_relevantShifts_not_mem_collar
    {n : ℕ} (hn : n ∈ relevantShifts (2 * Real.log 2)) (hnot : n ∉ totalDominatedModuli) :
    vonMangoldtAtom n = 0 := by
  have hnot_pos : ¬ 0 < ArithmeticFunction.vonMangoldt n :=
    mt (vonMangoldt_pos_iff_mem_totalDominatedModuli_of_mem_relevantShifts hn).mp hnot
  have hΛ0 : ArithmeticFunction.vonMangoldt n = 0 :=
    le_antisymm (not_lt.mp hnot_pos) ArithmeticFunction.vonMangoldt_nonneg
  unfold vonMangoldtAtom
  split_ifs
  · rw [hΛ0, zero_div]
  · rfl

/-- For every test `F` supported in `[−2 log 2, 2 log 2]`, `primeSideCharge F` reduces identically
to the sum over the nine-modulus collar `totalDominatedModuli`. -/
theorem primeSideCharge_eq_sum_totalDominatedModuli {F : ℝ → ℝ}
    (hsupp : ∀ x, 2 * Real.log 2 < |x| → F x = 0) :
    primeSideCharge F =
      ∑ n ∈ totalDominatedModuli, vonMangoldtAtom n * autoCorr F (Real.log n) := by
  have hr : 0 ≤ 2 * Real.log 2 := by positivity
  rw [primeSideCharge_eq_sum_relevantShifts hr hsupp]
  refine (Finset.sum_subset totalDominatedModuli_subset_relevantShifts_two_mul_log_two ?_).symm
  intro n hn hnot
  rw [vonMangoldtAtom_eq_zero_of_mem_relevantShifts_not_mem_collar hn hnot, zero_mul]

/-- At `r = 2 * log 2`, the ratio-comb energy on `relevantShifts (2 * log 2)` reduces identically
to the nine-modulus collar `totalDominatedModuli`. -/
theorem combEnergy_relevantShifts_two_mul_log_two_eq (F : ℝ → ℝ) :
    combEnergy F (relevantShifts (2 * Real.log 2)) vonMangoldtAtom =
      combEnergy F totalDominatedModuli vonMangoldtAtom := by
  unfold combEnergy
  have hsub := totalDominatedModuli_subset_relevantShifts_two_mul_log_two
  have houter : ∑ p ∈ relevantShifts (2 * Real.log 2),
        ∑ q ∈ relevantShifts (2 * Real.log 2),
          vonMangoldtAtom p * vonMangoldtAtom q * autoCorr F (Real.log q - Real.log p) =
      ∑ p ∈ totalDominatedModuli,
        ∑ q ∈ relevantShifts (2 * Real.log 2),
          vonMangoldtAtom p * vonMangoldtAtom q * autoCorr F (Real.log q - Real.log p) := by
    refine (Finset.sum_subset hsub ?_).symm
    intro p hp hnot
    rw [vonMangoldtAtom_eq_zero_of_mem_relevantShifts_not_mem_collar hp hnot]
    simp
  rw [houter]
  refine Finset.sum_congr rfl fun p _ => ?_
  refine (Finset.sum_subset hsub ?_).symm
  intro q hq hnot
  rw [vonMangoldtAtom_eq_zero_of_mem_relevantShifts_not_mem_collar hq hnot]
  simp

/-! ## §2. Catalan `(8, 9)` (`2³ + 1 = 3²`) Separation and 7-vs-2 Collar Sign Partition -/

/-- **Catalan Cube-Square Bilinear Form (`8 + 1 = 9`, i.e. `2³ + 1 = 3²`):**
Evaluates `w` on the Catalan prime-power pair `(8, 9)` inside `totalDominatedModuli`, with zero
archimedean input. -/
def catalanCubeSquareForm (w : ℕ → ℝ) : ℝ :=
  w 8 * w (8 + 1)

theorem liouvilleTwistedVonMangoldt_eight :
    liouvilleTwistedVonMangoldt 8 = -Real.log 2 := by
  have h8 : (8 : ℕ) = 2 ^ 3 := by norm_num
  rw [liouvilleTwistedVonMangoldt, h8,
    ArithmeticFunction.cardFactors_pow, ArithmeticFunction.cardFactors_apply_prime Nat.prime_two,
    ArithmeticFunction.vonMangoldt_apply_pow (by norm_num),
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  norm_num

theorem liouvilleTwistedVonMangoldt_nine :
    liouvilleTwistedVonMangoldt 9 = Real.log 3 := by
  have h9 : (9 : ℕ) = 3 ^ 2 := by norm_num
  rw [liouvilleTwistedVonMangoldt, h9,
    ArithmeticFunction.cardFactors_pow, ArithmeticFunction.cardFactors_apply_prime Nat.prime_three,
    ArithmeticFunction.vonMangoldt_apply_pow (by norm_num),
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three]
  norm_num

/-- **Archimedean-Free Catalan `(8, 9)` Collar Separation:**
Across every real scale twist `scaleTwistedVonMangoldt σ` (`σ ∈ ℝ`), `catalanCubeSquareForm`
equals `+72^σ (log 2)(log 3) > 0`, whereas on `liouvilleTwistedVonMangoldt` it equals
`-(log 2)(log 3) < 0`. -/
theorem catalan_cubeSquare_collar_separation :
    (∀ σ : ℝ, catalanCubeSquareForm (scaleTwistedVonMangoldt σ) =
        (72 : ℝ) ^ σ * (Real.log 2 * Real.log 3) ∧
      0 < catalanCubeSquareForm (scaleTwistedVonMangoldt σ)) ∧
    (catalanCubeSquareForm liouvilleTwistedVonMangoldt = -(Real.log 2 * Real.log 3) ∧
      catalanCubeSquareForm liouvilleTwistedVonMangoldt < 0) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  refine ⟨fun σ => ?_, ?_⟩
  · have hΛ8 : (ArithmeticFunction.vonMangoldt 8 : ℝ) = Real.log 2 := by
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num),
        ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
      norm_num
    have hΛ9 : (ArithmeticFunction.vonMangoldt 9 : ℝ) = Real.log 3 := by
      rw [show (9 : ℕ) = 3 ^ 2 by norm_num, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num),
        ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three]
      norm_num
    have heq : catalanCubeSquareForm (scaleTwistedVonMangoldt σ) =
        (72 : ℝ) ^ σ * (Real.log 2 * Real.log 3) := by
      unfold catalanCubeSquareForm scaleTwistedVonMangoldt
      rw [show (8 + 1 : ℕ) = 9 by norm_num, hΛ8, hΛ9]
      have hmul : (8 : ℝ) ^ σ * (9 : ℝ) ^ σ = (72 : ℝ) ^ σ := by
        rw [← Real.mul_rpow (by norm_num) (by norm_num)]
        norm_num
      calc ((8 : ℕ) : ℝ) ^ σ * Real.log 2 * (((9 : ℕ) : ℝ) ^ σ * Real.log 3)
          = ((8 : ℝ) ^ σ * (9 : ℝ) ^ σ) * (Real.log 2 * Real.log 3) := by norm_num; ring
        _ = (72 : ℝ) ^ σ * (Real.log 2 * Real.log 3) := by rw [hmul]
    exact ⟨heq, heq ▸ mul_pos (Real.rpow_pos_of_pos (by norm_num) σ) (mul_pos hl2 hl3)⟩
  · have heq : catalanCubeSquareForm liouvilleTwistedVonMangoldt =
        -(Real.log 2 * Real.log 3) := by
      unfold catalanCubeSquareForm
      rw [show (8 + 1 : ℕ) = 9 by norm_num, liouvilleTwistedVonMangoldt_eight,
        liouvilleTwistedVonMangoldt_nine]
      ring
    exact ⟨heq, heq ▸ neg_lt_zero.mpr (mul_pos hl2 hl3)⟩

/-- The seven odd-`Ω` moduli in `totalDominatedModuli` where `liouvilleTwistedVonMangoldt < 0`. -/
def collarNegativeLiouvilleModuli : Finset ℕ := {2, 3, 5, 7, 8, 11, 13}

/-- The two even-`Ω` square moduli in `totalDominatedModuli` where `0 < liouvilleTwistedVonMangoldt`. -/
def collarPositiveLiouvilleModuli : Finset ℕ := {4, 9}

/-- **Exact 7-vs-2 Sign Partition of `liouvilleTwistedVonMangoldt` Across the Nine-Modulus Collar.**
`totalDominatedModuli` splits disjointly into `7` moduli `{2, 3, 5, 7, 8, 11, 13}` on which
`liouvilleTwistedVonMangoldt n < 0` and `2` square moduli `{4, 9}` on which
`0 < liouvilleTwistedVonMangoldt n`. -/
theorem collar_liouville_sign_partition :
    totalDominatedModuli = collarNegativeLiouvilleModuli ∪ collarPositiveLiouvilleModuli ∧
    Disjoint collarNegativeLiouvilleModuli collarPositiveLiouvilleModuli ∧
    collarNegativeLiouvilleModuli.card = 7 ∧
    collarPositiveLiouvilleModuli.card = 2 ∧
    (∀ n ∈ collarNegativeLiouvilleModuli, liouvilleTwistedVonMangoldt n < 0) ∧
    (∀ n ∈ collarPositiveLiouvilleModuli, 0 < liouvilleTwistedVonMangoldt n) := by
  have hprime_neg : ∀ {p : ℕ}, p.Prime → liouvilleTwistedVonMangoldt p < 0 := by
    intro p hp
    rw [liouvilleTwistedVonMangoldt, ArithmeticFunction.cardFactors_apply_prime hp,
      ArithmeticFunction.vonMangoldt_apply_prime hp]
    have hlp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
    linarith [show ((-1 : ℝ) ^ 1) = -1 by norm_num]
  refine ⟨by decide, by decide, by decide, by decide, ?_, ?_⟩
  · intro n hn
    simp only [collarNegativeLiouvilleModuli, Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hprime_neg Nat.prime_two
    · exact hprime_neg Nat.prime_three
    · exact hprime_neg (by norm_num : Nat.Prime 5)
    · exact hprime_neg (by norm_num : Nat.Prime 7)
    · rw [liouvilleTwistedVonMangoldt_eight]
      exact neg_lt_zero.mpr (Real.log_pos (by norm_num))
    · exact hprime_neg (by norm_num : Nat.Prime 11)
    · exact hprime_neg (by norm_num : Nat.Prime 13)
  · intro n hn
    simp only [collarPositiveLiouvilleModuli, Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl
    · rw [liouvilleTwistedVonMangoldt_four]
      exact Real.log_pos (by norm_num)
    · rw [liouvilleTwistedVonMangoldt_nine]
      exact Real.log_pos (by norm_num)

/-- Evenness of `autoCorr F`: `autoCorr F (-t) = autoCorr F t` for every `F : ℝ → ℝ`. -/
theorem autoCorr_neg_eq (F : ℝ → ℝ) (t : ℝ) : autoCorr F (-t) = autoCorr F t := by
  unfold autoCorr
  calc (∫ u, F u * F (u + -t))
      = ∫ u, F (u + t) * F (u + t + -t) :=
        (integral_add_right_eq_self (fun u => F u * F (u + -t)) t).symm
    _ = ∫ u, F u * F (u + t) := by
        refine integral_congr_ae (Eventually.of_forall fun u => ?_)
        have h : u + t + -t = u := by ring
        rw [h, mul_comm]

/-- Endpoint-inclusive support vanishing of `autoCorr`: if `F x = 0` for `B < |x|`, then
`autoCorr F t = 0` for every `t` with `2 * B ≤ |t|` (the boundary `x = ±B` has measure zero). -/
theorem autoCorr_eq_zero_of_support_le {F : ℝ → ℝ} {B : ℝ}
    (hsupp : ∀ x, B < |x| → F x = 0) {t : ℝ} (ht : 2 * B ≤ |t|) :
    autoCorr F t = 0 := by
  have hae : ∀ᵐ x : ℝ ∂volume, F x * F (x + t) = 0 := by
    have h1 : ∀ᵐ x : ℝ ∂volume, x ≠ B := ae_iff.mpr (by simp)
    have h2 : ∀ᵐ x : ℝ ∂volume, x ≠ -B := ae_iff.mpr (by simp)
    filter_upwards [h1, h2] with x hxB hxmB
    by_cases hf1 : F x = 0
    · simp [hf1]
    by_cases hf2 : F (x + t) = 0
    · simp [hf2]
    have b1 : |x| ≤ B := not_lt.mp fun h => hf1 (hsupp x h)
    have b2 : |x + t| ≤ B := not_lt.mp fun h => hf2 (hsupp _ h)
    have b1_lt : |x| < B := lt_of_le_of_ne b1 fun heq => by
      rcases (abs_eq (le_trans (abs_nonneg x) b1)).mp heq with rfl | rfl
      · exact hxB rfl
      · exact hxmB rfl
    have h3 : |t| ≤ |x + t| + |x| := by
      have := abs_sub (x + t) x
      rwa [add_sub_cancel_left] at this
    linarith
  exact integral_eq_zero_of_ae hae

/-- Pointwise evaluation of `liouvilleTwistedVonMangoldt` vs `vonMangoldt` across the nine-modulus
collar: on `collarPositiveLiouvilleModuli = {4, 9}` they agree identically, while on
`collarNegativeLiouvilleModuli = {2, 3, 5, 7, 8, 11, 13}` `liouvilleTwistedVonMangoldt = -Λ`. -/
theorem liouvilleTwistedVonMangoldt_collar_cases :
    (∀ n ∈ collarPositiveLiouvilleModuli,
      liouvilleTwistedVonMangoldt n = (ArithmeticFunction.vonMangoldt n : ℝ)) ∧
    (∀ n ∈ collarNegativeLiouvilleModuli,
      liouvilleTwistedVonMangoldt n = -(ArithmeticFunction.vonMangoldt n : ℝ)) := by
  have hprime_eq : ∀ {p : ℕ}, p.Prime →
      liouvilleTwistedVonMangoldt p = -(ArithmeticFunction.vonMangoldt p : ℝ) := by
    intro p hp
    rw [liouvilleTwistedVonMangoldt, ArithmeticFunction.cardFactors_apply_prime hp]
    ring
  refine ⟨?_, ?_⟩
  · intro n hn
    simp only [collarPositiveLiouvilleModuli, Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl
    · rw [liouvilleTwistedVonMangoldt_four, show (4 : ℕ) = 2 ^ 2 by norm_num,
        ArithmeticFunction.vonMangoldt_apply_pow (by norm_num),
        ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    · rw [liouvilleTwistedVonMangoldt_nine, show (9 : ℕ) = 3 ^ 2 by norm_num,
        ArithmeticFunction.vonMangoldt_apply_pow (by norm_num),
        ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three]
  · intro n hn
    simp only [collarNegativeLiouvilleModuli, Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hprime_eq Nat.prime_two
    · exact hprime_eq Nat.prime_three
    · exact hprime_eq (by norm_num : Nat.Prime 5)
    · exact hprime_eq (by norm_num : Nat.Prime 7)
    · rw [liouvilleTwistedVonMangoldt_eight, show (8 : ℕ) = 2 ^ 3 by norm_num,
        ArithmeticFunction.vonMangoldt_apply_pow (by norm_num),
        ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    · exact hprime_eq (by norm_num : Nat.Prime 11)
    · exact hprime_eq (by norm_num : Nat.Prime 13)

/-- **Exact Square-Cancellation and Seven-Atom Collar Difference Law (`r = 2 * log 2`):**
For every real profile `F : ℝ → ℝ` vanishing outside `[−2 log 2, 2 log 2]`, the two even-`Ω`
square moduli `{4, 9}` cancel identically between `W_{λΛ}` and `W_ζ` (along with the pole, Gamma,
and composite shifts `{6, 10, 12, 14, 15}`), leaving purely the `7` odd-`Ω` collar shifts
`collarNegativeLiouvilleModuli = {2, 3, 5, 7, 8, 11, 13}`:
`Re W_{λΛ}(F ⋆ F̃) - Re W_ζ(F ⋆ F̃) = 4 ∑_{n ∈ {2,3,5,7,8,11,13}} vonMangoldtAtom n · autoCorr F (log n)`. -/
theorem re_weilFullFunctional_liouville_sub_vonMangoldt_collar {F : ℝ → ℝ}
    (hsupp : ∀ x, 2 * Real.log 2 < |x| → F x = 0) :
    (weilFullFunctional liouvilleTwistedVonMangoldt
        (EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ)))).re -
      (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ)))).re =
      4 * ∑ n ∈ collarNegativeLiouvilleModuli, vonMangoldtAtom n * autoCorr F (Real.log n) := by
  set k : ℝ → ℂ := EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ))
  have hk_eq : ∀ t : ℝ, k t = ((autoCorr F t : ℝ) : ℂ) := by
    intro t
    have h := _root_.RHTower.ArchimedeanExactForm.autocorr_eq_weilTest F (-t)
    rw [neg_neg] at h
    rw [← h, ← autoCorr_eq_autocorr, autoCorr_neg_eq]
  have hzero_ge16 : ∀ {n : ℕ}, 16 ≤ n → k (Real.log n) = 0 ∧ k (-Real.log n) = 0 := by
    intro n hn16
    have hlog16 : 2 * (2 * Real.log 2) ≤ Real.log n := by
      have h16 : 2 * (2 * Real.log 2) = Real.log 16 := by
        rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num, Real.log_pow]
        push_cast; ring
      rw [h16]
      exact Real.log_le_log (by norm_num) (by exact_mod_cast hn16)
    have hpos : 0 ≤ Real.log n := le_trans (by positivity) hlog16
    have hac1 : autoCorr F (Real.log n) = 0 :=
      autoCorr_eq_zero_of_support_le hsupp (by rwa [abs_of_nonneg hpos])
    have hac2 : autoCorr F (-Real.log n) = 0 := by rw [autoCorr_neg_eq, hac1]
    rw [hk_eq, hk_eq, hac1, hac2, Complex.ofReal_zero]
    exact ⟨rfl, rfl⟩
  have htsum : ∀ w : ℕ → ℝ,
      (∑' n : ℕ, ((if 2 ≤ n then w n / Real.sqrt n else 0 : ℝ) : ℂ) *
        (k (Real.log n) + k (-Real.log n))) =
      (((2 * ∑ n ∈ Finset.Icc 2 15, (w n / Real.sqrt n) * autoCorr F (Real.log n)) : ℝ) : ℂ) := by
    intro w
    rw [tsum_eq_sum (s := Finset.Icc 2 15)]
    · rw [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
      rw [if_pos hn2, hk_eq, hk_eq, autoCorr_neg_eq]
      push_cast
      ring
    · intro n hn
      rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
      rcases hn with hlt | hgt
      · rw [if_neg (by omega : ¬ 2 ≤ n), Complex.ofReal_zero, zero_mul]
      · obtain ⟨hz1, hz2⟩ := hzero_ge16 (by omega : 16 ≤ n)
        rw [hz1, hz2, add_zero, mul_zero]
  have hdiff_c : weilFullFunctional liouvilleTwistedVonMangoldt k -
      weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) k =
      (((2 * ∑ n ∈ Finset.Icc 2 15,
          (((ArithmeticFunction.vonMangoldt n : ℝ) - liouvilleTwistedVonMangoldt n) / Real.sqrt n) *
            autoCorr F (Real.log n)) : ℝ) : ℂ) := by
    unfold weilFullFunctional
    rw [htsum liouvilleTwistedVonMangoldt,
      htsum (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))]
    rw [← Complex.ofReal_sub]
    congr 1
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  have hre := congrArg Complex.re hdiff_c
  rw [Complex.sub_re, Complex.ofReal_re] at hre
  rw [hre]
  obtain ⟨hpos_eq, hneg_eq⟩ := liouvilleTwistedVonMangoldt_collar_cases
  obtain ⟨hpart, hdisj, _, _, _, _⟩ := collar_liouville_sign_partition
  have hsub_collar : Finset.sum (Finset.Icc 2 15)
        (fun n => (((ArithmeticFunction.vonMangoldt n : ℝ) - liouvilleTwistedVonMangoldt n) /
          Real.sqrt n) * autoCorr F (Real.log n)) =
      ∑ n ∈ totalDominatedModuli,
        (((ArithmeticFunction.vonMangoldt n : ℝ) - liouvilleTwistedVonMangoldt n) /
          Real.sqrt n) * autoCorr F (Real.log n) := by
    rw [← relevantShifts_two_mul_log_two]
    refine (Finset.sum_subset totalDominatedModuli_subset_relevantShifts_two_mul_log_two ?_).symm
    intro n hn hnot
    have hnot_pos : ¬ 0 < ArithmeticFunction.vonMangoldt n :=
      mt (vonMangoldt_pos_iff_mem_totalDominatedModuli_of_mem_relevantShifts hn).mp hnot
    have hΛ0 : (ArithmeticFunction.vonMangoldt n : ℝ) = 0 := by
      exact_mod_cast le_antisymm (not_lt.mp hnot_pos) ArithmeticFunction.vonMangoldt_nonneg
    have hL0 : liouvilleTwistedVonMangoldt n = 0 := by
      rw [liouvilleTwistedVonMangoldt, hΛ0, mul_zero]
    rw [hΛ0, hL0]
    ring
  rw [hsub_collar, hpart, Finset.sum_union hdisj]
  have hpos_zero : ∑ n ∈ collarPositiveLiouvilleModuli,
      (((ArithmeticFunction.vonMangoldt n : ℝ) - liouvilleTwistedVonMangoldt n) / Real.sqrt n) *
        autoCorr F (Real.log n) = 0 := by
    refine Finset.sum_eq_zero fun n hn => ?_
    rw [hpos_eq n hn, sub_self, zero_div, zero_mul]
  have hneg_two : ∑ n ∈ collarNegativeLiouvilleModuli,
      (((ArithmeticFunction.vonMangoldt n : ℝ) - liouvilleTwistedVonMangoldt n) / Real.sqrt n) *
        autoCorr F (Real.log n) =
      2 * ∑ n ∈ collarNegativeLiouvilleModuli, vonMangoldtAtom n * autoCorr F (Real.log n) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn2 : 2 ≤ n := by
      simp only [collarNegativeLiouvilleModuli, Finset.mem_insert, Finset.mem_singleton] at hn
      omega
    rw [hneg_eq n hn]
    unfold vonMangoldtAtom
    rw [if_pos hn2]
    ring
  rw [hpos_zero, add_zero, hneg_two]
  ring

/-! ## §3. Ground-Eigenvalue Antitonicity, Smooth Collar Selectivity, and Comb Ledger Floor -/

/-- Support inclusion `C²_c([-r₁, r₁]) ⊆ C²_c([-r₂, r₂])` makes `liouvilleWindowRayleighSet`
monotone in `r`. -/
theorem liouvilleWindowRayleighSet_mono {r₁ r₂ : ℝ} (hle : r₁ ≤ r₂) :
    liouvilleWindowRayleighSet r₁ ⊆ liouvilleWindowRayleighSet r₂ := by
  rintro q ⟨F, hF2, hFc, hsupp, hnorm, hq⟩
  exact ⟨F, hF2, hFc, fun x hx => hsupp x (lt_of_le_of_lt hle hx), hnorm, hq⟩

/-- For every `r ≥ 23 / 40`, `liouvilleWindowRayleighSet r` is nonempty. -/
theorem liouvilleWindowRayleighSet_nonempty {r : ℝ} (hr : 23 / 40 ≤ r) :
    (liouvilleWindowRayleighSet r).Nonempty := by
  obtain ⟨F, hF2, hFc, _, hsupp, hnorm, _, _⟩ :=
    exists_smooth_odd_twentyThreeFortieths_zeta_pos_liouville_neg
  exact ⟨_, liouvilleWindowRayleighSet_mono hr ⟨F, hF2, hFc, hsupp, hnorm, rfl⟩⟩

/-- **Antitonicity of `liouvilleWindowGroundEigenvalue`:**
For `23 / 40 ≤ r₁ ≤ r₂`, `liouvilleWindowGroundEigenvalue r₂ ≤ liouvilleWindowGroundEigenvalue r₁`. -/
theorem liouvilleWindowGroundEigenvalue_antitone_of_ge {r₁ r₂ : ℝ}
    (hr₁ : 23 / 40 ≤ r₁) (hle : r₁ ≤ r₂) :
    liouvilleWindowGroundEigenvalue r₂ ≤ liouvilleWindowGroundEigenvalue r₁ := by
  unfold liouvilleWindowGroundEigenvalue
  exact csInf_le_csInf (bddBelow_liouvilleWindowRayleighSet (by linarith))
    (liouvilleWindowRayleighSet_nonempty hr₁) (liouvilleWindowRayleighSet_mono hle)

/-- **All-Collar Smooth Selective Separation (`r ≥ 23 / 40`):**
For every aperture `r ≥ 23 / 40`, `liouvilleWindowGroundEigenvalue r < -3 / 10 < 0` and there exists
an explicit smooth odd witness `F ∈ C²_c([-r, r])` with `0 < ∫ F²`,
`(1 / 25) ∫ F² < Re W_ζ(F ⋆ F̃)`, and `Re W_{λΛ}(F ⋆ F̃) < -(3 / 10) ∫ F² < 0`. -/
theorem smooth_odd_selectivity_of_ge_twentyThreeFortieths {r : ℝ} (hr : 23 / 40 ≤ r) :
    BddBelow (liouvilleWindowRayleighSet r) ∧
    liouvilleWindowGroundEigenvalue r < -(3 / 10 : ℝ) ∧
    ∃ F : ℝ → ℝ, ContDiff ℝ 2 F ∧ HasCompactSupport F ∧
      (∀ x, F (-x) = -F x) ∧ (∀ x, r < |x| → F x = 0) ∧ 0 < (∫ x, F x ^ 2) ∧
      (1 / 25 : ℝ) * (∫ x, F x ^ 2) <
        (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
          (EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ)))).re ∧
      (weilFullFunctional liouvilleTwistedVonMangoldt
        (EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ)))).re <
        -(3 / 10 : ℝ) * (∫ x, F x ^ 2) := by
  have hbdd := bddBelow_liouvilleWindowRayleighSet (by linarith : 0 < r)
  have hanti := liouvilleWindowGroundEigenvalue_antitone_of_ge le_rfl hr
  have h23 := liouvilleWindowGroundEigenvalue_twentyThreeFortieths_lt_neg_threeTenths.2
  obtain ⟨F, hF2, hFc, hodd, hsupp, hnorm, hzeta, hliouv⟩ :=
    exists_smooth_odd_twentyThreeFortieths_zeta_pos_liouville_neg
  refine ⟨hbdd, lt_of_le_of_lt hanti h23, F, hF2, hFc, hodd,
    fun x hx => hsupp x (lt_of_le_of_lt hr hx), hnorm, hzeta, hliouv⟩

/-- The nine-modulus collar aperture `2 * log 2` strictly exceeds `23 / 40`. -/
theorem twentyThreeFortieths_lt_two_mul_log_two : (23 / 40 : ℝ) < 2 * Real.log 2 := by
  have hl2 := Real.log_two_gt_d9
  linarith

/-- **Nine-Modulus Collar Ratio-Comb Incidence Ledger Floor (`r = 2 * log 2`).**
For every real odd `F ∈ C²_c(ℝ)` supported in `[−2 log 2, 2 log 2]`, every plateau radius
`R > 2 * log 2`, and every `γ > 0`, the entire prime-power crossing charge in `fullZeroForm F` is
priced by the ratio-comb energy on `totalDominatedModuli = {2, 3, 4, 5, 7, 8, 9, 11, 13}`:
`surplusPool + crossingPotentialTerm + gaugeRemainder - poleCharge
  - γ * autoCorr F 0 - γ⁻¹ * combEnergy F totalDominatedModuli vonMangoldtAtom ≤ fullZeroForm F`. -/
theorem fullZeroForm_ge_nineModulusCollar_combLedger {F : ℝ → ℝ} {R γ : ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x)
    (hsupp : ∀ x, 2 * Real.log 2 < |x| → F x = 0) (hrR : 2 * Real.log 2 < R) (hγ : 0 < γ) :
    surplusPool (aperturePlateau (2 * Real.log 2) R) F +
        crossingPotentialTerm (aperturePlateau (2 * Real.log 2) R) F +
        gaugeRemainder (aperturePlateau (2 * Real.log 2) R) F -
        poleCharge F -
        γ * autoCorr F 0 -
        γ⁻¹ * combEnergy F totalDominatedModuli vonMangoldtAtom ≤
      fullZeroForm F := by
  have hr : 0 < 2 * Real.log 2 := by positivity
  have h := fullZeroForm_ge_incidenceBudget_sub_combEnergy hF hFc hodd hr hsupp hrR hγ
  rwa [combEnergy_relevantShifts_two_mul_log_two_eq F] at h

/-- **Complete Nine-Modulus Collar Selectivity and Polar-Ledger Package (`r = 2 * log 2`).**
Packages at the canonical nine-modulus collar aperture `r = 2 * log 2`:
1. Exact prime-power support match `(relevantShifts (2 * log 2)).filter (0 < Λ ·) = totalDominatedModuli`;
2. Midpoint polar payment `totalAntiDiagonalKernel n (log n / 2) ≤ 0` for all `n ≥ 2` outside
   `totalDominatedModuli`;
3. Smooth odd Liouville refutation `liouvilleWindowGroundEigenvalue (2 * log 2) < -3 / 10` with
   simultaneous positive `W_ζ` and negative `W_{λΛ}` witness on `[−2 log 2, 2 log 2]`. -/
theorem nineModulusCollar_selectivity_package :
    ((relevantShifts (2 * Real.log 2)).filter (fun n => 0 < ArithmeticFunction.vonMangoldt n) =
      totalDominatedModuli) ∧
    (∀ n : ℕ, 2 ≤ n → n ∉ totalDominatedModuli →
      totalAntiDiagonalKernel n (Real.log n / 2) ≤ 0) ∧
    liouvilleWindowGroundEigenvalue (2 * Real.log 2) < -(3 / 10 : ℝ) ∧
    (∃ F : ℝ → ℝ, ContDiff ℝ 2 F ∧ HasCompactSupport F ∧
      (∀ x, F (-x) = -F x) ∧ (∀ x, 2 * Real.log 2 < |x| → F x = 0) ∧ 0 < (∫ x, F x ^ 2) ∧
      (1 / 25 : ℝ) * (∫ x, F x ^ 2) <
        (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
          (EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ)))).re ∧
      (weilFullFunctional liouvilleTwistedVonMangoldt
        (EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ)))).re <
        -(3 / 10 : ℝ) * (∫ x, F x ^ 2)) := by
  obtain ⟨_, hlt, hwit⟩ :=
    smooth_odd_selectivity_of_ge_twentyThreeFortieths twentyThreeFortieths_lt_two_mul_log_two.le
  exact ⟨relevantShifts_two_mul_log_two_filter_vonMangoldt_pos,
    fun n hn2 hnot => totalAntiDiagonalKernel_midpoint_nonpos hn2 hnot,
    hlt, hwit⟩

end GaloisForLFunctions.ArithmeticIncidencePositivity
