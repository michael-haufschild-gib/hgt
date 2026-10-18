import GaloisForLFunctions.BezoutValuationIncidence.SharpPrimitiveEnergySuccessorFrontier
import GaloisForLFunctions.BezoutValuationIncidence.GcdOrbitProjectionAndExactTranslationPeriods
import GaloisForLFunctions.BezoutValuationIncidence.PrimeTailCalibrationAndMobiusDefect

/-!
# Sharp Jordan Upper Bounds, Gcd-Orbit Orthogonality, and Stride-Bounded Primitive Energy

In `SharpPrimitiveEnergySuccessorFrontier`, `exists_prime_mode_with_large_primitive_energy` proves
that `sievePrimitiveEnergy N c` has no level-uniform upper bound in terms of `sieveVariance N c`
because prime modes `p` satisfy `J₂(p) / φ(p) = p + 1 → ∞`.

This module establishes the **sharp multiplicative upper bound** complementing
`jordanTotient2_ge_mul_totient` and shows that the **gcd-orbit projection**
`sieveGcdProjection N h c` (`GcdOrbitProjectionAndExactTranslationPeriods`) simultaneously
projects all four spectral observables (`sieveVariance`, `sieveSuccessorCovariance`,
`sieveSuccessorReserve`, `sievePrimitiveEnergy`) orthogonally onto the resonant modes `q ∣ h`,
eliminating prime escape above `h` with a **cutoff-independent** upper bound:

* `jordanTotient2_le_sq_mul_totient` & `four_mul_jordanTotient2_le_three_mul_sq_mul_totient`:
  For every `n : ℕ`, `J₂(n) ≤ n² φ(n)`, and for every `n ≥ 2`:
  `4 * J₂(n) ≤ 3 * n² * φ(n)` (attained with exact equality at `n = 2` where `4 * 3 = 3 * 4 * 1`).
* `sixteen_mul_sievePrimitiveEnergy_le_sq_mul_sieveVariance`:
  For every cutoff `N : ℕ` and every weight `c : ℕ → ℝ`,
  `16 * sievePrimitiveEnergy N c ≤ N² * sieveVariance N c`, with exact equality at `N = 2` for every
  weight `c`.
* `sieveGcdProjection_observables_diagonal` & `sieveGcdProjection_simultaneous_pythagoras`:
  The gcd-orbit projection `Γ_h c = sieveGcdProjection N h c` restricts the Selberg multiples
  diagonals of `sieveVariance`, `sieveSuccessorCovariance`, `sieveSuccessorReserve`, and
  `12 * sievePrimitiveEnergy` to `q ∈ [2, N]` with `q ∣ h`, and satisfies exact simultaneous
  Pythagorean orthogonal decompositions for `sieveVariance`, `sieveSuccessorReserve`, and
  `sievePrimitiveEnergy`.
* `sixteen_mul_sievePrimitiveEnergy_gcdProjection_le_stride_sq`,
  `sieveGcdProjection_two_stride_identities`, &
  `sixteen_mul_sievePrimitiveEnergy_le_leastPeriod_sq`:
  For every positive stride `h ≥ 1`, cutoff `N : ℕ`, and weight `c : ℕ → ℝ`,
  `16 * sievePrimitiveEnergy N (sieveGcdProjection N h c) ≤ h² * sieveVariance N (sieveGcdProjection N h c) ≤ h² * sieveVariance N c`
  (completely independent of `N`). At `h = 2`,
  `4 * sievePrimitiveEnergy N (sieveGcdProjection N 2 c) = sieveVariance N (sieveGcdProjection N 2 c)`
  identically. Consequently, for every finite sieve weight `c`,
  `16 * sievePrimitiveEnergy N c ≤ (sieveLeastPeriod N c)² * sieveVariance N c`.
-/

open Finset ArithmeticFunction GaloisForLFunctions.BiScaleUncertainty RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Sharp Multiplicative Upper Bound on `jordanTotient2` -/

/-- Prime-power evaluation of `jordanTotient2`: `J₂(p^(k+1)) = (p^(k+1))² - (p^k)²`. -/
theorem jordanTotient2_prime_pow_succ {p : ℕ} (hp : p.Prime) (k : ℕ) :
    jordanTotient2 (p ^ (k + 1)) =
      ((p : ℝ) ^ (k + 1)) ^ (2 : ℕ) - ((p : ℝ) ^ k) ^ (2 : ℕ) := by
  rw [jordanTotient2_eq_gcdPowKernel, gcdPowKernel_prime_pow 2 hp (by omega)]
  norm_cast

/-- Multiplicativity of `jordanTotient2` on coprime arguments. -/
theorem jordanTotient2_mul_of_coprime {a b : ℕ} (h : a.Coprime b) :
    jordanTotient2 (a * b) = jordanTotient2 a * jordanTotient2 b := by
  simp_rw [jordanTotient2_eq_gcdPowKernel]
  exact (isMultiplicative_gcdPowKernel 2).map_mul_of_coprime h

/-- `jordanTotient2 n` is non-negative for every `n : ℕ`. -/
theorem jordanTotient2_nonneg (n : ℕ) : 0 ≤ jordanTotient2 n := by
  have h := jordanTotient2_ge_mul_totient n
  have h0 : (0 : ℝ) ≤ (n : ℝ) * (Nat.totient n : ℝ) := by positivity
  linarith

private theorem jordanTotient2_upper_aux (n : ℕ) :
    jordanTotient2 n ≤ (n : ℝ) ^ (2 : ℕ) * (Nat.totient n : ℝ) ∧
      (2 ≤ n → 4 * jordanTotient2 n ≤ 3 * (n : ℝ) ^ (2 : ℕ) * (Nat.totient n : ℝ)) := by
  induction n using Nat.recOnPrimeCoprime with
  | zero =>
    simp [jordanTotient2]
  | prime_pow p k hp =>
    rcases k with _ | k
    · simp
    · rw [jordanTotient2_prime_pow_succ hp, Nat.totient_prime_pow_succ hp]
      push_cast [Nat.cast_sub hp.one_le]
      rw [pow_succ (p : ℝ) k]
      set A : ℝ := (p : ℝ) ^ k
      set P : ℝ := (p : ℝ)
      have hP2 : 2 ≤ P := show (2 : ℝ) ≤ (p : ℝ) by exact_mod_cast hp.two_le
      have hA1 : 1 ≤ A := one_le_pow₀ (by linarith)
      have hid : 3 * (A * P) ^ (2 : ℕ) * (A * (P - 1)) - 4 * ((A * P) ^ (2 : ℕ) - A ^ (2 : ℕ)) =
          A ^ (2 : ℕ) * (P - 1) * (3 * P ^ (2 : ℕ) * (A - 1) + (3 * P + 2) * (P - 2)) := by
        ring
      have hnonneg : 0 ≤ A ^ (2 : ℕ) * (P - 1) *
          (3 * P ^ (2 : ℕ) * (A - 1) + (3 * P + 2) * (P - 2)) := by
        have h1 : 0 ≤ A ^ (2 : ℕ) * (P - 1) := mul_nonneg (sq_nonneg A) (by linarith)
        have h2 : 0 ≤ 3 * P ^ (2 : ℕ) * (A - 1) :=
          mul_nonneg (by positivity) (by linarith)
        have h3 : 0 ≤ (3 * P + 2) * (P - 2) :=
          mul_nonneg (by linarith) (by linarith)
        exact mul_nonneg h1 (add_nonneg h2 h3)
      have h43 : 4 * ((A * P) ^ (2 : ℕ) - A ^ (2 : ℕ)) ≤
          3 * (A * P) ^ (2 : ℕ) * (A * (P - 1)) := by linarith
      have h0 : 0 ≤ (A * P) ^ (2 : ℕ) * (A * (P - 1)) :=
        mul_nonneg (sq_nonneg _) (mul_nonneg (by linarith) (by linarith))
      exact ⟨by linarith, fun _ => h43⟩
  | coprime a b ha1 _ hab ha hb =>
    rw [jordanTotient2_mul_of_coprime hab, Nat.totient_mul hab, Nat.cast_mul, Nat.cast_mul]
    have hja := jordanTotient2_nonneg a
    have hjb := jordanTotient2_nonneg b
    have hba0 : 0 ≤ (b : ℝ) ^ (2 : ℕ) * (Nat.totient b : ℝ) := by positivity
    have hab1 : jordanTotient2 a * jordanTotient2 b ≤
        ((a : ℝ) ^ (2 : ℕ) * (Nat.totient a : ℝ)) *
          ((b : ℝ) ^ (2 : ℕ) * (Nat.totient b : ℝ)) :=
      mul_le_mul ha.1 hb.1 hjb (hja.trans ha.1)
    refine ⟨by nlinarith, fun _ => ?_⟩
    have hm := mul_le_mul (ha.2 ha1) hb.1 hjb (by positivity)
    nlinarith

/-- **Universal Multiplicative Upper Bound (`jordanTotient2_le_sq_mul_totient`):**
For every `n : ℕ`, `jordanTotient2 n ≤ n² * φ(n)`. -/
theorem jordanTotient2_le_sq_mul_totient (n : ℕ) :
    jordanTotient2 n ≤ (n : ℝ) ^ (2 : ℕ) * (Nat.totient n : ℝ) :=
  (jordanTotient2_upper_aux n).1

/-- **Sharp `3/4` Multiplicative Upper Bound on `jordanTotient2`
(`four_mul_jordanTotient2_le_three_mul_sq_mul_totient`):**
For every `n ≥ 2`, `4 * jordanTotient2 n ≤ 3 * n² * φ(n)`, with equality at `n = 2` where
`J₂(2) = 3` and `2² * φ(2) = 4`. -/
theorem four_mul_jordanTotient2_le_three_mul_sq_mul_totient {n : ℕ} (hn : 2 ≤ n) :
    4 * jordanTotient2 n ≤ 3 * (n : ℝ) ^ (2 : ℕ) * (Nat.totient n : ℝ) :=
  (jordanTotient2_upper_aux n).2 hn

/-! ## §2. Sharp Finite-Level Upper Bound on `sievePrimitiveEnergy` -/

/-- **Sharp Finite-Level Upper Bound on `sievePrimitiveEnergy`
(`sixteen_mul_sievePrimitiveEnergy_le_sq_mul_sieveVariance`):**
For every sieve level `N : ℕ` and every weight `c : ℕ → ℝ`:
`16 * sievePrimitiveEnergy N c ≤ N² * sieveVariance N c`,
and at `N = 2` equality holds identically for every weight `c`. -/
theorem sixteen_mul_sievePrimitiveEnergy_le_sq_mul_sieveVariance (N : ℕ) (c : ℕ → ℝ) :
    16 * sievePrimitiveEnergy N c ≤ (N : ℝ) ^ (2 : ℕ) * sieveVariance N c ∧
      16 * sievePrimitiveEnergy 2 c = (2 : ℝ) ^ (2 : ℕ) * sieveVariance 2 c := by
  have h12 := twelve_mul_sievePrimitiveEnergy_eq_jordan_diagonal N c
  have hbound : 4 * (12 * sievePrimitiveEnergy N c) ≤
      3 * (N : ℝ) ^ (2 : ℕ) * sieveVariance N c := by
    rw [h12, sieveVariance, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun q hq => ?_
    obtain ⟨hq2, hqN⟩ := Finset.mem_Icc.mp hq
    have hqR : (q : ℝ) ≤ (N : ℝ) := by exact_mod_cast hqN
    have hq_sq : (q : ℝ) ^ (2 : ℕ) ≤ (N : ℝ) ^ (2 : ℕ) :=
      pow_le_pow_left₀ (Nat.cast_nonneg q) hqR 2
    have hj := four_mul_jordanTotient2_le_three_mul_sq_mul_totient hq2
    have hphi : (0 : ℝ) ≤ (Nat.totient q : ℝ) := Nat.cast_nonneg _
    have hsq : 0 ≤ (selbergMultiplesCoord N c q) ^ (2 : ℕ) := sq_nonneg _
    have hjN : 4 * jordanTotient2 q ≤ 3 * (N : ℝ) ^ (2 : ℕ) * (Nat.totient q : ℝ) :=
      hj.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hq_sq (by norm_num)) hphi)
    have hmul := mul_le_mul_of_nonneg_right hjN hsq
    nlinarith only [hmul]
  refine ⟨by linarith only [hbound], ?_⟩
  have h2 := twelve_mul_sievePrimitiveEnergy_eq_jordan_diagonal 2 c
  unfold sieveVariance
  rw [Finset.Icc_self] at h2 ⊢
  simp only [Finset.sum_singleton, Nat.totient_two, Nat.cast_one, one_mul] at h2 ⊢
  have hj2 : jordanTotient2 2 = 3 := by
    have h := jordanTotient2_prime_pow_succ Nat.prime_two 0
    norm_num at h
    exact h
  rw [hj2] at h2
  linarith only [h2]

/-! ## §3. Gcd-Orbit Projection of All Four Spectral Observables & Simultaneous Pythagoras -/

/-- Weighted Selberg diagonal formula for `sieveGcdProjection N h c`:
for any modal weight `w : ℕ → ℝ`, summing `w q * Y_{N, Γ_h c}(q)²` over `q ∈ [2, N]` filters
the sum to resonant divisors `q ∣ h`. -/
theorem sum_selbergMultiplesCoord_gcdProjection_sq (N h : ℕ) (w c : ℕ → ℝ) :
    (∑ q ∈ Finset.Icc 2 N, w q * (selbergMultiplesCoord N (sieveGcdProjection N h c) q) ^ (2 : ℕ)) =
      ∑ q ∈ (Finset.Icc 2 N).filter (fun q => q ∣ h),
        w q * (selbergMultiplesCoord N c q) ^ (2 : ℕ) := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [selbergMultiplesCoord_gcdProjection]
  by_cases hh : q ∣ h <;> simp [hh]

/-- Weighted Selberg diagonal formula for the orthogonal complement `c - sieveGcdProjection N h c`:
summing `w q * Y_{N, c - Γ_h c}(q)²` over `q ∈ [2, N]` filters the sum to non-resonant modes `¬ q ∣ h`. -/
theorem sum_selbergMultiplesCoord_sub_gcdProjection_sq (N h : ℕ) (w c : ℕ → ℝ) :
    (∑ q ∈ Finset.Icc 2 N,
      w q * (selbergMultiplesCoord N (fun d => c d - sieveGcdProjection N h c d) q) ^ (2 : ℕ)) =
      ∑ q ∈ (Finset.Icc 2 N).filter (fun q => ¬ q ∣ h),
        w q * (selbergMultiplesCoord N c q) ^ (2 : ℕ) := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [selbergMultiplesCoord_sub, selbergMultiplesCoord_gcdProjection]
  by_cases hh : q ∣ h <;> simp [hh]

/-- **Simultaneous Diagonal Evaluation of All Four Observables Under `sieveGcdProjection`
(`sieveGcdProjection_observables_diagonal`):**
For every cutoff `N : ℕ`, stride `h : ℕ`, and weight `c : ℕ → ℝ`:
1. `sieveVariance N (sieveGcdProjection N h c) = ∑_{q ∈ [2, N], q ∣ h} φ(q) Y_{N,c}(q)²`,
2. `sieveSuccessorCovariance N (sieveGcdProjection N h c) = ∑_{q ∈ [2, N], q ∣ h} μ(q) Y_{N,c}(q)²`,
3. `sieveSuccessorReserve N (sieveGcdProjection N h c) = ∑_{q ∈ [2, N], q ∣ h} (φ(q) - μ(q)) Y_{N,c}(q)²`,
4. `12 * sievePrimitiveEnergy N (sieveGcdProjection N h c) = ∑_{q ∈ [2, N], q ∣ h} J₂(q) Y_{N,c}(q)²`. -/
theorem sieveGcdProjection_observables_diagonal (N h : ℕ) (c : ℕ → ℝ) :
    sieveVariance N (sieveGcdProjection N h c) =
      (∑ q ∈ (Finset.Icc 2 N).filter (fun q => q ∣ h),
        (Nat.totient q : ℝ) * (selbergMultiplesCoord N c q) ^ (2 : ℕ)) ∧
    sieveSuccessorCovariance N (sieveGcdProjection N h c) =
      (∑ q ∈ (Finset.Icc 2 N).filter (fun q => q ∣ h),
        moebiusReal q * (selbergMultiplesCoord N c q) ^ (2 : ℕ)) ∧
    sieveSuccessorReserve N (sieveGcdProjection N h c) =
      (∑ q ∈ (Finset.Icc 2 N).filter (fun q => q ∣ h),
        ((Nat.totient q : ℝ) - moebiusReal q) * (selbergMultiplesCoord N c q) ^ (2 : ℕ)) ∧
    12 * sievePrimitiveEnergy N (sieveGcdProjection N h c) =
      (∑ q ∈ (Finset.Icc 2 N).filter (fun q => q ∣ h),
        jordanTotient2 q * (selbergMultiplesCoord N c q) ^ (2 : ℕ)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold sieveVariance
    exact sum_selbergMultiplesCoord_gcdProjection_sq N h (fun q => (Nat.totient q : ℝ)) c
  · rw [sieveSuccessorCovariance_eq_diagonal]
    exact sum_selbergMultiplesCoord_gcdProjection_sq N h moebiusReal c
  · rcases N with _ | N
    · simp [sieveSuccessorReserve, selbergTotientDiagonalForm, bezoutCoprimeQuadraticForm]
    · unfold sieveSuccessorReserve
      rw [selbergSubBezoutQuadraticForm_eq_Icc_two (by omega)]
      exact sum_selbergMultiplesCoord_gcdProjection_sq (N + 1) h
        (fun q => (Nat.totient q : ℝ) - moebiusReal q) c
  · rw [twelve_mul_sievePrimitiveEnergy_eq_jordan_diagonal]
    exact sum_selbergMultiplesCoord_gcdProjection_sq N h jordanTotient2 c

/-- **Simultaneous Pythagorean Decomposition Under `sieveGcdProjection`
(`sieveGcdProjection_simultaneous_pythagoras`):**
For every `N, h : ℕ` and `c : ℕ → ℝ`, the gcd-orbit projection `Γ_h c = sieveGcdProjection N h c`
splits `sieveVariance`, `sieveSuccessorCovariance`, `sieveSuccessorReserve`, and
`sievePrimitiveEnergy` additively into their resonant (`q ∣ h`) and non-resonant (`¬ q ∣ h`)
parts, and contracts `sieveVariance`, `sieveSuccessorReserve`, and `sievePrimitiveEnergy`. -/
theorem sieveGcdProjection_simultaneous_pythagoras (N h : ℕ) (c : ℕ → ℝ) :
    sieveVariance N c =
      sieveVariance N (sieveGcdProjection N h c) +
        sieveVariance N (fun d => c d - sieveGcdProjection N h c d) ∧
    sieveSuccessorReserve N c =
      sieveSuccessorReserve N (sieveGcdProjection N h c) +
        sieveSuccessorReserve N (fun d => c d - sieveGcdProjection N h c d) ∧
    sievePrimitiveEnergy N c =
      sievePrimitiveEnergy N (sieveGcdProjection N h c) +
        sievePrimitiveEnergy N (fun d => c d - sieveGcdProjection N h c d) ∧
    sieveVariance N (sieveGcdProjection N h c) ≤ sieveVariance N c ∧
    sieveSuccessorReserve N (sieveGcdProjection N h c) ≤ sieveSuccessorReserve N c ∧
    sievePrimitiveEnergy N (sieveGcdProjection N h c) ≤ sievePrimitiveEnergy N c := by
  have hsplit_sum : ∀ w : ℕ → ℝ,
      (∑ q ∈ Finset.Icc 2 N, w q * (selbergMultiplesCoord N c q) ^ (2 : ℕ)) =
        (∑ q ∈ Finset.Icc 2 N,
          w q * (selbergMultiplesCoord N (sieveGcdProjection N h c) q) ^ (2 : ℕ)) +
        ∑ q ∈ Finset.Icc 2 N,
          w q * (selbergMultiplesCoord N (fun d => c d - sieveGcdProjection N h c d) q) ^ (2 : ℕ) := by
    intro w
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [selbergMultiplesCoord_sub, selbergMultiplesCoord_gcdProjection]
    by_cases hh : q ∣ h <;> simp [hh]
  have hV : sieveVariance N c =
      sieveVariance N (sieveGcdProjection N h c) +
        sieveVariance N (fun d => c d - sieveGcdProjection N h c d) :=
    hsplit_sum (fun q => (Nat.totient q : ℝ))
  have hR : sieveSuccessorReserve N c =
      sieveSuccessorReserve N (sieveGcdProjection N h c) +
        sieveSuccessorReserve N (fun d => c d - sieveGcdProjection N h c d) := by
    rcases N with _ | N
    · simp [sieveSuccessorReserve, selbergTotientDiagonalForm, bezoutCoprimeQuadraticForm]
    · unfold sieveSuccessorReserve
      rw [selbergSubBezoutQuadraticForm_eq_Icc_two (by omega),
        selbergSubBezoutQuadraticForm_eq_Icc_two (by omega),
        selbergSubBezoutQuadraticForm_eq_Icc_two (by omega)]
      exact hsplit_sum (fun q => (Nat.totient q : ℝ) - moebiusReal q)
  have hE12 : 12 * sievePrimitiveEnergy N c =
      12 * sievePrimitiveEnergy N (sieveGcdProjection N h c) +
        12 * sievePrimitiveEnergy N (fun d => c d - sieveGcdProjection N h c d) := by
    rw [twelve_mul_sievePrimitiveEnergy_eq_jordan_diagonal,
      twelve_mul_sievePrimitiveEnergy_eq_jordan_diagonal,
      twelve_mul_sievePrimitiveEnergy_eq_jordan_diagonal]
    exact hsplit_sum jordanTotient2
  have hE : sievePrimitiveEnergy N c =
      sievePrimitiveEnergy N (sieveGcdProjection N h c) +
        sievePrimitiveEnergy N (fun d => c d - sieveGcdProjection N h c d) := by
    linarith only [hE12]
  have hV_rem : 0 ≤ sieveVariance N (fun d => c d - sieveGcdProjection N h c d) :=
    Finset.sum_nonneg fun q _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have hR_rem : 0 ≤ sieveSuccessorReserve N (fun d => c d - sieveGcdProjection N h c d) := by
    rcases N with _ | N
    · simp [sieveSuccessorReserve, selbergTotientDiagonalForm, bezoutCoprimeQuadraticForm]
    · unfold sieveSuccessorReserve
      exact sub_nonneg.mpr (bezoutCoprimeQuadraticForm_le_selberg (by omega) _)
  have hE_rem : 0 ≤ sievePrimitiveEnergy N (fun d => c d - sieveGcdProjection N h c d) := by
    have h12_nonneg : 0 ≤ 12 * sievePrimitiveEnergy N (fun d => c d - sieveGcdProjection N h c d) := by
      rw [twelve_mul_sievePrimitiveEnergy_eq_jordan_diagonal]
      exact Finset.sum_nonneg fun q _ => mul_nonneg (jordanTotient2_nonneg q) (sq_nonneg _)
    linarith only [h12_nonneg]
  exact ⟨hV, hR, hE, by linarith, by linarith, by linarith⟩

/-! ## §4. Cutoff-Independent Stride Upper Bound & Intrinsic Least-Period Inequality -/

/-- **Cutoff-Independent Stride Upper Bound on Projected Primitive Energy
(`sixteen_mul_sievePrimitiveEnergy_gcdProjection_le_stride_sq`):**
For every positive stride `h ≥ 1`, every sieve cutoff `N : ℕ` (arbitrarily large), and every
weight `c : ℕ → ℝ`, the gcd-orbit projection `sieveGcdProjection N h c` eliminates prime escape
above `h` and satisfies:
`16 * sievePrimitiveEnergy N (sieveGcdProjection N h c) ≤ h² * sieveVariance N (sieveGcdProjection N h c) ≤ h² * sieveVariance N c`. -/
theorem sixteen_mul_sievePrimitiveEnergy_gcdProjection_le_stride_sq
    (N : ℕ) {h : ℕ} (hh : 1 ≤ h) (c : ℕ → ℝ) :
    16 * sievePrimitiveEnergy N (sieveGcdProjection N h c) ≤
      (h : ℝ) ^ (2 : ℕ) * sieveVariance N (sieveGcdProjection N h c) ∧
    (h : ℝ) ^ (2 : ℕ) * sieveVariance N (sieveGcdProjection N h c) ≤
      (h : ℝ) ^ (2 : ℕ) * sieveVariance N c := by
  obtain ⟨hV_diag, _, _, hE_diag⟩ := sieveGcdProjection_observables_diagonal N h c
  obtain ⟨_, _, _, hV_le, _, _⟩ := sieveGcdProjection_simultaneous_pythagoras N h c
  have hbound : 4 * (12 * sievePrimitiveEnergy N (sieveGcdProjection N h c)) ≤
      3 * (h : ℝ) ^ (2 : ℕ) * sieveVariance N (sieveGcdProjection N h c) := by
    rw [hE_diag, hV_diag, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun q hq => ?_
    obtain ⟨hqI, hqdvd⟩ := Finset.mem_filter.mp hq
    have hq2 : 2 ≤ q := (Finset.mem_Icc.mp hqI).1
    have hqh : q ≤ h := Nat.le_of_dvd hh hqdvd
    have hqR : (q : ℝ) ≤ (h : ℝ) := by exact_mod_cast hqh
    have hq_sq : (q : ℝ) ^ (2 : ℕ) ≤ (h : ℝ) ^ (2 : ℕ) :=
      pow_le_pow_left₀ (Nat.cast_nonneg q) hqR 2
    have hj := four_mul_jordanTotient2_le_three_mul_sq_mul_totient hq2
    have hphi : (0 : ℝ) ≤ (Nat.totient q : ℝ) := Nat.cast_nonneg _
    have hsq : 0 ≤ (selbergMultiplesCoord N c q) ^ (2 : ℕ) := sq_nonneg _
    have hjh : 4 * jordanTotient2 q ≤ 3 * (h : ℝ) ^ (2 : ℕ) * (Nat.totient q : ℝ) :=
      hj.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hq_sq (by norm_num)) hphi)
    have hmul := mul_le_mul_of_nonneg_right hjh hsq
    nlinarith only [hmul]
  refine ⟨by linarith only [hbound],
    mul_le_mul_of_nonneg_left hV_le (sq_nonneg (h : ℝ))⟩

/-- **Exact Parity-Orbit (`h = 2`) Spectral Identities (`sieveGcdProjection_two_stride_identities`):**
At stride `h = 2`, for every level `N : ℕ` and every weight `c : ℕ → ℝ`, the parity-orbit
projection `sieveGcdProjection N 2 c` attains the `3/4` Jordan upper bound with exact equality:
1. `4 * sievePrimitiveEnergy N (sieveGcdProjection N 2 c) = sieveVariance N (sieveGcdProjection N 2 c)`,
2. `sieveSuccessorCovariance N (sieveGcdProjection N 2 c) = -sieveVariance N (sieveGcdProjection N 2 c)`,
3. `sieveSuccessorReserve N (sieveGcdProjection N 2 c) = 2 * sieveVariance N (sieveGcdProjection N 2 c)`. -/
theorem sieveGcdProjection_two_stride_identities (N : ℕ) (c : ℕ → ℝ) :
    4 * sievePrimitiveEnergy N (sieveGcdProjection N 2 c) =
      sieveVariance N (sieveGcdProjection N 2 c) ∧
    sieveSuccessorCovariance N (sieveGcdProjection N 2 c) =
      -sieveVariance N (sieveGcdProjection N 2 c) ∧
    sieveSuccessorReserve N (sieveGcdProjection N 2 c) =
      2 * sieveVariance N (sieveGcdProjection N 2 c) := by
  obtain ⟨hV, hC, hR, hE⟩ := sieveGcdProjection_observables_diagonal N 2 c
  have hmem : ∀ q ∈ (Finset.Icc 2 N).filter (fun q => q ∣ 2), q = 2 := by
    intro q hq
    obtain ⟨hqI, hqdvd⟩ := Finset.mem_filter.mp hq
    have hq2 : 2 ≤ q := (Finset.mem_Icc.mp hqI).1
    have hle2 : q ≤ 2 := Nat.le_of_dvd (by decide) hqdvd
    omega
  have hj2 : jordanTotient2 2 = 3 := by
    have h := jordanTotient2_prime_pow_succ Nat.prime_two 0
    norm_num at h
    exact h
  have hm2 : moebiusReal 2 = -1 := by
    simp [moebiusReal, ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  have ht2 : (Nat.totient 2 : ℝ) = 1 := by simp [Nat.totient_two]
  have hE_eq : (∑ q ∈ (Finset.Icc 2 N).filter (fun q => q ∣ 2),
      jordanTotient2 q * (selbergMultiplesCoord N c q) ^ (2 : ℕ)) =
      3 * ∑ q ∈ (Finset.Icc 2 N).filter (fun q => q ∣ 2),
        (Nat.totient q : ℝ) * (selbergMultiplesCoord N c q) ^ (2 : ℕ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [hmem q hq, hj2, ht2]
    ring
  have hC_eq : (∑ q ∈ (Finset.Icc 2 N).filter (fun q => q ∣ 2),
      moebiusReal q * (selbergMultiplesCoord N c q) ^ (2 : ℕ)) =
      -∑ q ∈ (Finset.Icc 2 N).filter (fun q => q ∣ 2),
        (Nat.totient q : ℝ) * (selbergMultiplesCoord N c q) ^ (2 : ℕ) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [hmem q hq, hm2, ht2]
    ring
  have hR_eq : (∑ q ∈ (Finset.Icc 2 N).filter (fun q => q ∣ 2),
      ((Nat.totient q : ℝ) - moebiusReal q) * (selbergMultiplesCoord N c q) ^ (2 : ℕ)) =
      2 * ∑ q ∈ (Finset.Icc 2 N).filter (fun q => q ∣ 2),
        (Nat.totient q : ℝ) * (selbergMultiplesCoord N c q) ^ (2 : ℕ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [hmem q hq, hm2, ht2]
    ring
  rw [hE_eq, ← hV] at hE
  rw [hC_eq, ← hV] at hC
  rw [hR_eq, ← hV] at hR
  exact ⟨by linarith only [hE], hC, hR⟩

/-- At stride `h = 0`, `sieveGcdProjection N 0 c` preserves `sieveVariance` and `sievePrimitiveEnergy`
identically. -/
theorem sieveGcdProjection_zero_stride_observables (N : ℕ) (c : ℕ → ℝ) :
    sieveVariance N (sieveGcdProjection N 0 c) = sieveVariance N c ∧
      sievePrimitiveEnergy N (sieveGcdProjection N 0 c) = sievePrimitiveEnergy N c := by
  have hcoord : ∀ q ∈ Finset.Icc 2 N,
      selbergMultiplesCoord N (sieveGcdProjection N 0 c) q = selbergMultiplesCoord N c q := by
    intro q _
    rw [selbergMultiplesCoord_gcdProjection, if_pos (dvd_zero q)]
  constructor
  · unfold sieveVariance
    refine Finset.sum_congr rfl fun q hq => by rw [hcoord q hq]
  · have h12 := twelve_mul_sievePrimitiveEnergy_eq_jordan_diagonal N (sieveGcdProjection N 0 c)
    have h12' := twelve_mul_sievePrimitiveEnergy_eq_jordan_diagonal N c
    have hsum : (∑ q ∈ Finset.Icc 2 N,
        jordanTotient2 q * (selbergMultiplesCoord N (sieveGcdProjection N 0 c) q) ^ (2 : ℕ)) =
        ∑ q ∈ Finset.Icc 2 N, jordanTotient2 q * (selbergMultiplesCoord N c q) ^ (2 : ℕ) :=
      Finset.sum_congr rfl fun q hq => by rw [hcoord q hq]
    linarith only [h12, h12', hsum]

/-- **Intrinsic Least-Period Upper Bound on `sievePrimitiveEnergy`
(`sixteen_mul_sievePrimitiveEnergy_le_leastPeriod_sq`):**
For every sieve level `N : ℕ` and every weight `c : ℕ → ℝ`, the discrete primitive energy is
bounded above by the square of the exact least positive period `sieveLeastPeriod N c` times
`sieveVariance N c`:
`16 * sievePrimitiveEnergy N c ≤ (sieveLeastPeriod N c)² * sieveVariance N c`. -/
theorem sixteen_mul_sievePrimitiveEnergy_le_leastPeriod_sq (N : ℕ) (c : ℕ → ℝ) :
    16 * sievePrimitiveEnergy N c ≤
      (sieveLeastPeriod N c : ℝ) ^ (2 : ℕ) * sieveVariance N c := by
  obtain ⟨⟨hpos, hper⟩, _⟩ := sieveLeastPeriod_isLeast N c
  have hfix := (sieveGcdProjection_eq_zero_stride_iff N (sieveLeastPeriod N c) c).mpr hper
  obtain ⟨hV0, hE0⟩ := sieveGcdProjection_zero_stride_observables N c
  have hstride := (sixteen_mul_sievePrimitiveEnergy_gcdProjection_le_stride_sq N hpos c).1
  rw [hfix, hV0, hE0] at hstride
  exact hstride

end
end GaloisForLFunctions.BezoutValuationIncidence
