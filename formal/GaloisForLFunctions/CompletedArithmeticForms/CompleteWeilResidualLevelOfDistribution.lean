import GaloisForLFunctions.CompletedArithmeticForms.PrimeResidualLevelOfDistribution
import GaloisForLFunctions.SuccessorShellArithmetic.TopBand.RamanujanDivisorPlancherel
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.CompleteConductorResidualsRetainTheirHorizonDecay
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.CountingActiveShellsMakesTheAffineSourceLinear
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.LogarithmicOverlapOfTheCompleteWeilMatrixIsTheRiemannHypothesis
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheAdjunctionEnergyHasFiniteSublevels

/-!
# Level of Distribution for Complete Weil Matrix Residuals at RH-Complete Overlap

Unconditional affirmative resolution of Question Q3 across all Ramanujan conductors
`1 ≤ m ≤ M = ⌊N^θ⌋₊` for every Bombieri–Vinogradov exponent `0 < θ < 1 / 2` and every
overlap schedule `c : ℕ → ℝ` with `∀ᶠ N, 1 ≤ c N` and `c N ^ 2 / log N → 0` (the sharp
`c_N = o((log N)^{1/2})` boundary of the complete-Weil tower, including the RH-complete
regime `c_N = 2 (log N)^α` for `1 / 4 < α < 1 / 2`):
```
(∑_{m=1}^{⌊N^θ⌋₊} ‖W_{N, c_N} v_m - E_m(c_N) v_m‖²) / (∑_{m=1}^{⌊N^θ⌋₊} E_m(c_N)²) → 0.
```

Starting from the exact eight-piece identity
`completeWeilMatrix_ramanujan_residual_eq_at_every_overlap`, each block is controlled
collectively over `1 ≤ m ≤ M` (`M * M ≤ N`):
1. `fullPrimeMatrix` residual: `O(M log N)` via `exists_fullPrimeMatrix_levelOfDistribution`.
2. Self-energy replacement: `O(M c²)` via `abs_completeWeilSelfError_le_of_width_le_one` and
   the Riesz norm ceiling `‖v_m‖² ≤ 6`.
3. Center matrix residual: `m = 1` via `exists_fullWeilCenter_norm_sq_polynomial_bound`; for
   `m ≥ 2`, dual Bessel Hilbert–Schmidt on the two-pole kernel gives `O(c² log N)` and
   weighted Schur on `archimedeanCenterKernel` gives `O(M c² log N)`.
4. Separated cross replacement: integer-distance Schur test gives `O(M c⁴)`.
5. Two-pole moment replacement: dual Bessel Hilbert–Schmidt gives `O(c⁴ log N / N²)`.
6. Near-Gamma / downward cancellation: sharp quadratic-radius near-row `L²` concentration
   combined with complete-period Plancherel on `ramanujanLogDivisorJet` gives
   `O(M (c⁴ + c² log N))` indoors, while the divisor-totient packet bound
   `sum_normalizedRamanujanMode_sq_le` cancels `1 / ℓ` outdoors to give `O(c³ (log N)⁵)`
   without a factor of `M`.
7. Near-center block: sharp near-row `L²` concentration gives `O(M c⁴)`.
8. Upward prime defect: weighted Schur (`up_row_le` / `down_row_le`) and the linear affine
   shell bound `abs_shellCorrectionOfShift_mean_le_linear` give `O(M c²)`.
-/

noncomputable section

open MeasureTheory Finset Filter Topology ArithmeticFunction
open scoped BigOperators RealInnerProductSpace

namespace GaloisForLFunctions.CompletedArithmeticForms

open SignedArithmeticHodgeTheory RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell
  CriticalArithmeticCorrelationTheory SpacingScaleHarmonicAnalysis
  ArithmeticElectrostatics BezoutValuationIncidence HTGeometry
  SuccessorShellArithmetic

/-! ## Section 1: Weighted Schur, Dual Bessel Hilbert–Schmidt, and Sharp Near-Row `L²` Bounds -/

private theorem norm_add_sq_le_two {E : Type*} [SeminormedAddCommGroup E] (a b : E) :
    ‖a + b‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a b) 2
  nlinarith only [h, sq_nonneg (‖a‖ - ‖b‖)]

private theorem norm_sub_sq_le_two {E : Type*} [SeminormedAddCommGroup E] (a b : E) :
    ‖a - b‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  simpa only [sub_eq_add_neg, norm_neg] using norm_add_sq_le_two a (-b)

private theorem norm_four_sq_le {E : Type*} [SeminormedAddCommGroup E] (a b c d : E) :
    ‖a + b + c + d‖ ^ 2 ≤ 4 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2) := by
  have h := norm_add_sq_le_two (a + b) (c + d)
  rw [← add_assoc] at h
  linarith only [h, norm_add_sq_le_two a b, norm_add_sq_le_two c d]

private theorem norm_eight_signed_sq_le {E : Type*} [SeminormedAddCommGroup E]
    (p s c x q y z u : E) :
    ‖-p + s + c - x + q + (y + z) - u‖ ^ 2 ≤
      8 * (‖p‖ ^ 2 + ‖s‖ ^ 2 + ‖c‖ ^ 2 + ‖x‖ ^ 2 +
        ‖q‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2 + ‖u‖ ^ 2) := by
  have hid : -p + s + c - x + q + (y + z) - u =
      (-p + s + c + -x) + (q + y + z + -u) := by abel
  rw [hid]
  have h := norm_add_sq_le_two (-p + s + c + -x) (q + y + z + -u)
  have h1 := norm_four_sq_le (-p) s c (-x)
  have h2 := norm_four_sq_le q y z (-u)
  rw [norm_neg, norm_neg] at h1
  rw [norm_neg] at h2
  linarith only [h, h1, h2]

/-- Weighted Schur `L²` inequality for finite kernels majorized entrywise by `U ≥ 0`. -/
private theorem sum_sq_abs_majorized_kernel_le {N : ℕ} (K U : ℕ → ℕ → ℝ) (x w u d : ℕ → ℝ)
    (hU : ∀ n ∈ Icc 1 N, ∀ j ∈ Icc 1 N, 0 ≤ U n j)
    (hKU : ∀ n ∈ Icc 1 N, ∀ j ∈ Icc 1 N, |K n j| ≤ U n j)
    (hw : ∀ j ∈ Icc 1 N, 0 < w j)
    (hrow : ∀ n ∈ Icc 1 N, (∑ j ∈ Icc 1 N, U n j * w j) ≤ u n)
    (hcol : ∀ j ∈ Icc 1 N, (∑ n ∈ Icc 1 N, U n j * (u n / w j)) ≤ d j) :
    (∑ n ∈ Icc 1 N, (∑ j ∈ Icc 1 N, K n j * x j) ^ 2) ≤
      ∑ j ∈ Icc 1 N, d j * x j ^ 2 := by
  have hfor_n : ∀ n ∈ Icc 1 N,
      (∑ j ∈ Icc 1 N, K n j * x j) ^ 2 ≤
        ∑ j ∈ Icc 1 N, (U n j * (u n / w j)) * x j ^ 2 := by
    intro n hn
    have habs : |∑ j ∈ Icc 1 N, K n j * x j| ≤
        ∑ j ∈ Icc 1 N, Real.sqrt (U n j * w j) * (Real.sqrt (U n j / w j) * |x j|) := by
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j hj => ?_)
      rw [abs_mul]
      have h1 : |K n j| * |x j| ≤ U n j * |x j| :=
        mul_le_mul_of_nonneg_right (hKU n hn j hj) (abs_nonneg _)
      have hsplit : U n j = Real.sqrt (U n j * w j) * Real.sqrt (U n j / w j) := by
        rw [← Real.sqrt_mul (mul_nonneg (hU n hn j hj) (hw j hj).le)]
        have hmul : (U n j * w j) * (U n j / w j) = U n j ^ 2 := by
          field_simp [(hw j hj).ne']
        rw [hmul, Real.sqrt_sq (hU n hn j hj)]
      exact h1.trans_eq ((congrArg (· * |x j|) hsplit).trans (mul_assoc _ _ _))
    have hsq := mul_self_le_mul_self (abs_nonneg _) habs
    rw [← sq, sq_abs, ← sq] at hsq
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Icc 1 N)
      (fun j => Real.sqrt (U n j * w j))
      (fun j => Real.sqrt (U n j / w j) * |x j|)
    have hcs' : (∑ j ∈ Icc 1 N,
        Real.sqrt (U n j * w j) * (Real.sqrt (U n j / w j) * |x j|)) ^ 2 ≤
        (∑ j ∈ Icc 1 N, U n j * w j) * ∑ j ∈ Icc 1 N, (U n j / w j) * x j ^ 2 := by
      refine hcs.trans_eq ?_
      congr 1
      · exact sum_congr rfl fun j hj => Real.sq_sqrt (mul_nonneg (hU n hn j hj) (hw j hj).le)
      · exact sum_congr rfl fun j hj => by
          rw [mul_pow, Real.sq_sqrt (div_nonneg (hU n hn j hj) (hw j hj).le), sq_abs]
    calc
      (∑ j ∈ Icc 1 N, K n j * x j) ^ 2 ≤
          (∑ j ∈ Icc 1 N, U n j * w j) * ∑ j ∈ Icc 1 N, (U n j / w j) * x j ^ 2 :=
        hsq.trans hcs'
      _ ≤ u n * ∑ j ∈ Icc 1 N, (U n j / w j) * x j ^ 2 :=
        mul_le_mul_of_nonneg_right (hrow n hn)
          (sum_nonneg fun j hj => mul_nonneg (div_nonneg (hU n hn j hj) (hw j hj).le) (sq_nonneg _))
      _ = ∑ j ∈ Icc 1 N, (U n j * (u n / w j)) * x j ^ 2 := by
        rw [mul_sum]
        exact sum_congr rfl fun j _ => by ring
  calc
    (∑ n ∈ Icc 1 N, (∑ j ∈ Icc 1 N, K n j * x j) ^ 2) ≤
        ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, (U n j * (u n / w j)) * x j ^ 2 := sum_le_sum hfor_n
    _ = ∑ j ∈ Icc 1 N, (∑ n ∈ Icc 1 N, U n j * (u n / w j)) * x j ^ 2 := by
      rw [sum_comm]
      exact sum_congr rfl fun j _ => (sum_mul _ _ _).symm
    _ ≤ ∑ j ∈ Icc 1 N, d j * x j ^ 2 :=
      sum_le_sum fun j hj => mul_le_mul_of_nonneg_right (hcol j hj) (sq_nonneg _)

/-- Euclidean squared norm of a horizon matrix acting on `normalizedRamanujanHorizonVector`. -/
private theorem matrix_normalizedRamanujan_norm_sq {N m : ℕ} (K : ℕ → ℕ → ℝ) :
    ‖Matrix.toEuclideanLin (fun n j : PrimeHorizonIndex N => K n j)
      (normalizedRamanujanHorizonVector m N)‖ ^ 2 =
      (∑ n ∈ Icc 1 N,
        (∑ j ∈ Icc 1 N, K n j * (normalizedRamanujanMode m j / Real.sqrt j)) ^ 2) /
        Real.log N := by
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ n : PrimeHorizonIndex N,
    (∑ j : PrimeHorizonIndex N, K n j *
      ((Real.sqrt (Real.log N))⁻¹ * (normalizedRamanujanMode m j / Real.sqrt j))) ^ 2) = _
  have hrow : ∀ n : PrimeHorizonIndex N,
      (∑ j : PrimeHorizonIndex N, K n j *
        ((Real.sqrt (Real.log N))⁻¹ * (normalizedRamanujanMode m j / Real.sqrt j))) ^ 2 =
      (∑ j ∈ Icc 1 N, K n j * (normalizedRamanujanMode m j / Real.sqrt j)) ^ 2 / Real.log N := by
    intro n
    have h1 : (∑ j : PrimeHorizonIndex N, K n j *
        ((Real.sqrt (Real.log N))⁻¹ * (normalizedRamanujanMode m j / Real.sqrt j))) =
        (Real.sqrt (Real.log N))⁻¹ *
          ∑ j ∈ Icc 1 N, K n j * (normalizedRamanujanMode m j / Real.sqrt j) := by
      refine (sum_coe_sort (Icc 1 N)
        (fun j => K n j * ((Real.sqrt (Real.log N))⁻¹ * (normalizedRamanujanMode m j / Real.sqrt j)))).trans ?_
      rw [mul_sum]
      exact sum_congr rfl fun j _ => by ring
    rw [h1, mul_pow, inv_pow, Real.sq_sqrt (Real.log_natCast_nonneg N), div_eq_inv_mul]
  simp_rw [hrow, ← sum_div]
  congr 1
  exact sum_coe_sort (Icc 1 N)
    (fun n => (∑ j ∈ Icc 1 N, K n j * (normalizedRamanujanMode m j / Real.sqrt j)) ^ 2)

/-- Dual Bessel inequality bounds the collective action of any matrix across `1 ≤ m ≤ M`
by `6` times its Hilbert–Schmidt norm squared. -/
private theorem sum_matrix_action_norm_sq_le_six_mul_hs {M N : ℕ} (hMN : M * M ≤ N)
    (hL : 4 * Real.exp 7 ≤ Real.log N)
    (A : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ) :
    (∑ m ∈ Icc 1 M,
      ‖Matrix.toEuclideanLin A (normalizedRamanujanHorizonVector m N)‖ ^ 2) ≤
      6 * ∑ n : PrimeHorizonIndex N, ∑ j : PrimeHorizonIndex N, A n j ^ 2 := by
  have hrow_eq : ∀ (m : ℕ) (n : PrimeHorizonIndex N),
      ((Matrix.toEuclideanLin A (normalizedRamanujanHorizonVector m N)) n) ^ 2 =
        ⟪WithLp.toLp 2 (fun j => A n j), normalizedRamanujanHorizonVector m N⟫ ^ 2 := by
    intro m n
    congr 1
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    change (∑ j : PrimeHorizonIndex N, A n j * normalizedRamanujanHorizonVector m N j) =
      ∑ j : PrimeHorizonIndex N, normalizedRamanujanHorizonVector m N j * A n j
    exact sum_congr rfl fun j _ => mul_comm _ _
  have hnorm_r : ∀ n : PrimeHorizonIndex N,
      ‖WithLp.toLp 2 (fun j : PrimeHorizonIndex N => A n j)‖ ^ 2 =
        ∑ j : PrimeHorizonIndex N, A n j ^ 2 := by
    intro n
    rw [EuclideanSpace.real_norm_sq_eq]
  calc
    (∑ m ∈ Icc 1 M,
        ‖Matrix.toEuclideanLin A (normalizedRamanujanHorizonVector m N)‖ ^ 2) =
        ∑ m ∈ Icc 1 M, ∑ n : PrimeHorizonIndex N,
          ⟪WithLp.toLp 2 (fun j => A n j), normalizedRamanujanHorizonVector m N⟫ ^ 2 := by
      refine sum_congr rfl fun m _ => ?_
      rw [EuclideanSpace.real_norm_sq_eq]
      exact sum_congr rfl fun n _ => hrow_eq m n
    _ = ∑ n : PrimeHorizonIndex N, ∑ m ∈ Icc 1 M,
          ⟪WithLp.toLp 2 (fun j => A n j), normalizedRamanujanHorizonVector m N⟫ ^ 2 := sum_comm
    _ ≤ ∑ n : PrimeHorizonIndex N,
          6 * ‖WithLp.toLp 2 (fun j : PrimeHorizonIndex N => A n j)‖ ^ 2 :=
      sum_le_sum fun n _ => sum_inner_normalizedRamanujanHorizonVector_sq_le hMN hL _
    _ = 6 * ∑ n : PrimeHorizonIndex N, ∑ j : PrimeHorizonIndex N, A n j ^ 2 := by
      rw [← mul_sum]
      congr 1
      exact sum_congr rfl fun n _ => hnorm_r n

/-- Hilbert–Schmidt squared norm bound for `arithmeticPoleKernel` on `Icc 1 N`. -/
private theorem sum_sq_arithmeticPoleKernel_le {N : ℕ} (hlogN : 1 ≤ Real.log N) :
    (∑ n : PrimeHorizonIndex N, ∑ j : PrimeHorizonIndex N,
      arithmeticPoleKernel n j ^ 2) ≤ 8 * (N : ℝ) ^ 2 * Real.log N := by
  have hpoint : ∀ n ∈ Icc 1 N, ∀ j ∈ Icc 1 N,
      arithmeticPoleKernel n j ^ 2 ≤ 2 * ((n : ℝ) / j + (j : ℝ) / n) := by
    intro n hn j hj
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hj0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    unfold arithmeticPoleKernel
    have h2 : (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n) ^ 2 ≤
        2 * ((Real.sqrt n / Real.sqrt j) ^ 2 + (Real.sqrt j / Real.sqrt n) ^ 2) := by
      nlinarith only [sq_nonneg (Real.sqrt n / Real.sqrt j - Real.sqrt j / Real.sqrt n)]
    simpa only [div_pow, Real.sq_sqrt hn0, Real.sq_sqrt hj0] using h2
  have hsum_n : (∑ n ∈ Icc 1 N, (n : ℝ)) ≤ (N : ℝ) ^ 2 := by
    calc
      (∑ n ∈ Icc 1 N, (n : ℝ)) ≤ ∑ _n ∈ Icc 1 N, (N : ℝ) :=
        sum_le_sum fun n hn => by exact_mod_cast (mem_Icc.mp hn).2
      _ = (N : ℝ) ^ 2 := by rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, sq]
  have hsum_inv : (∑ j ∈ Icc 1 N, 1 / (j : ℝ)) ≤ 2 * Real.log N := by
    linarith [_root_.RHTower.Sieve.sum_Icc_one_div_le_one_add_log N, hlogN]
  have hprod : (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, (n : ℝ) / j) ≤ 2 * (N : ℝ) ^ 2 * Real.log N := by
    have hfac : (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, (n : ℝ) / j) =
        (∑ n ∈ Icc 1 N, (n : ℝ)) * ∑ j ∈ Icc 1 N, 1 / (j : ℝ) := by
      rw [sum_mul]
      exact sum_congr rfl fun n _ => by rw [mul_sum]; exact sum_congr rfl fun j _ => by ring
    rw [hfac]
    exact (mul_le_mul hsum_n hsum_inv (sum_nonneg fun _ _ => by positivity) (by positivity)).trans_eq
      (by ring)
  have hcoe : (∑ n : PrimeHorizonIndex N, ∑ j : PrimeHorizonIndex N,
      arithmeticPoleKernel n j ^ 2) =
      ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, arithmeticPoleKernel n j ^ 2 := by
    refine (sum_coe_sort (Icc 1 N)
      (fun n => ∑ j : PrimeHorizonIndex N, arithmeticPoleKernel n j ^ 2)).trans ?_
    exact sum_congr rfl fun n _ => sum_coe_sort (Icc 1 N) (fun j => arithmeticPoleKernel n j ^ 2)
  rw [hcoe]
  calc
    (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, arithmeticPoleKernel n j ^ 2) ≤
        ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, 2 * ((n : ℝ) / j + (j : ℝ) / n) :=
      sum_le_sum fun n hn => sum_le_sum fun j hj => hpoint n hn j hj
    _ = 2 * ((∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, (n : ℝ) / j) +
          ∑ j ∈ Icc 1 N, ∑ n ∈ Icc 1 N, (j : ℝ) / n) := by
      simp_rw [mul_add, sum_add_distrib, ← mul_sum]
      rw [sum_comm (s := Icc 1 N) (t := Icc 1 N) (f := fun n j => (j : ℝ) / n)]
    _ ≤ 2 * (2 * (N : ℝ) ^ 2 * Real.log N + 2 * (N : ℝ) ^ 2 * Real.log N) :=
      mul_le_mul_of_nonneg_left (add_le_add hprod hprod) zero_le_two
    _ = 8 * (N : ℝ) ^ 2 * Real.log N := by ring

/-- Sharp quadratic-radius near-row `L²` concentration: because `|n - j| ≤ j * (R / N)` on
`nearRowIndices c N j`, each column `j` participates in at most `2 j R / N` near rows,
cancelling `1 / j` identically. -/
private theorem sum_near_div_sqrt_sq_le_profile {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N)
    (hw : c / N ≤ 1) (F : ℕ → ℕ → ℝ) (G : ℕ → ℝ) (hG : ∀ j ∈ Icc 1 N, 0 ≤ G j)
    (hFG : ∀ n ∈ Icc 1 N, ∀ j ∈ nearRowIndices c N n, |F n j| ≤ G j) :
    (∑ n ∈ Icc 1 N, (∑ j ∈ nearRowIndices c N n, F n j / Real.sqrt j) ^ 2) ≤
      4 * linearNearRowRadius c ^ 2 / N * ∑ j ∈ Icc 1 N, G j ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hR0 : 0 ≤ linearNearRowRadius c := by unfold linearNearRowRadius; positivity
  -- Column cardinality bound `card (nearRowIndices c N j) ≤ 2 * (j * (R / N))`.
  have hcol_card : ∀ j ∈ Icc 1 N,
      ((nearRowIndices c N j).card : ℝ) ≤ 2 * ((j : ℝ) * (linearNearRowRadius c / N)) := by
    intro j hj
    have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hj).1
    have he : Real.exp (2 * c / N) - 1 ≤ linearNearRowRadius c / N := by
      calc
        _ ≤ 2 * c / N * Real.exp (2 * c / N) := exp_sub_one_le_mul_exp
        _ ≤ 2 * c / N * Real.exp 2 :=
          mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr (by
              have h := mul_le_mul_of_nonneg_left hw zero_le_two
              simpa only [mul_div_assoc, mul_one] using h)) (by positivity)
        _ = _ := by unfold linearNearRowRadius; ring
    have hsub : nearRowIndices c N j ⊆
        (Icc 1 N).filter (fun n => n ≠ j ∧ |(n : ℝ) - j| ≤ (j : ℝ) * (linearNearRowRadius c / N)) := by
      intro n hn
      obtain ⟨hnI, hnj, hlog⟩ := mem_filter.mp hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hnI).1
      have hdist := (abs_sub_le_of_abs_log_le hn0 hj0 hlog).trans
        (mul_le_mul_of_nonneg_left he hj0.le)
      exact mem_filter.mpr ⟨hnI, hnj, hdist⟩
    exact (show ((nearRowIndices c N j).card : ℝ) ≤
        (((Icc 1 N).filter
          (fun n => n ≠ j ∧ |(n : ℝ) - j| ≤ (j : ℝ) * (linearNearRowRadius c / N))).card : ℝ)
        by exact_mod_cast card_le_card hsub).trans
      (card_near_le (Icc 1 N) j (by positivity))
  -- Symmetry of `nearRowIndices`.
  have hsym : ∀ n ∈ Icc 1 N, ∀ j ∈ Icc 1 N,
      (j ∈ nearRowIndices c N n ↔ n ∈ nearRowIndices c N j) := by
    intro n hn j hj
    simp only [nearRowIndices, mem_filter, hn, hj, true_and]
    rw [ne_comm, abs_sub_comm]
  -- Row-by-row Cauchy–Schwarz.
  have hrow : ∀ n ∈ Icc 1 N,
      (∑ j ∈ nearRowIndices c N n, F n j / Real.sqrt j) ^ 2 ≤
        (2 * linearNearRowRadius c) *
          ∑ j ∈ Icc 1 N, if n ∈ nearRowIndices c N j then G j ^ 2 / j else 0 := by
    intro n hn
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (nearRowIndices c N n)
      (fun j => F n j / Real.sqrt j) (fun _ => (1 : ℝ))
    simp only [mul_one, one_pow, sum_const, nsmul_eq_mul] at hcs
    have hcard := card_nearRowIndices_le_small_width hc hn hw
    have hpt : ∀ j ∈ nearRowIndices c N n, (F n j / Real.sqrt j) ^ 2 ≤ G j ^ 2 / j := by
      intro j hj
      have hjI := (mem_filter.mp hj).1
      have hj0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
      have hsq := mul_self_le_mul_self (abs_nonneg _) (hFG n hn j hj)
      rw [← sq, sq_abs, ← sq] at hsq
      rw [div_pow, Real.sq_sqrt hj0]
      exact div_le_div_of_nonneg_right hsq hj0
    have hsum_eq : (∑ j ∈ nearRowIndices c N n, G j ^ 2 / j) =
        ∑ j ∈ Icc 1 N, if n ∈ nearRowIndices c N j then G j ^ 2 / j else 0 := by
      rw [nearRowIndices, sum_filter]
      refine sum_congr rfl fun j hj => ?_
      have hiff : (j ≠ n ∧ |Real.log j - Real.log n| ≤ 2 * c / N) ↔ n ∈ nearRowIndices c N j := by
        rw [← hsym n hn j hj]
        simp only [nearRowIndices, mem_filter, hj, true_and]
      by_cases h : n ∈ nearRowIndices c N j
      · rw [if_pos (hiff.mpr h), if_pos h]
      · rw [if_neg (mt hiff.mp h), if_neg h]
    calc
      (∑ j ∈ nearRowIndices c N n, F n j / Real.sqrt j) ^ 2 ≤
          (∑ j ∈ nearRowIndices c N n, (F n j / Real.sqrt j) ^ 2) *
            (nearRowIndices c N n).card := hcs
      _ ≤ (∑ j ∈ nearRowIndices c N n, G j ^ 2 / j) * (2 * linearNearRowRadius c) :=
        mul_le_mul (sum_le_sum hpt) hcard (Nat.cast_nonneg _)
          (sum_nonneg fun j _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg j))
      _ = (2 * linearNearRowRadius c) *
            ∑ j ∈ Icc 1 N, if n ∈ nearRowIndices c N j then G j ^ 2 / j else 0 := by
        rw [hsum_eq, mul_comm]
  calc
    (∑ n ∈ Icc 1 N, (∑ j ∈ nearRowIndices c N n, F n j / Real.sqrt j) ^ 2) ≤
        ∑ n ∈ Icc 1 N, (2 * linearNearRowRadius c) *
          ∑ j ∈ Icc 1 N, if n ∈ nearRowIndices c N j then G j ^ 2 / j else 0 := sum_le_sum hrow
    _ = (2 * linearNearRowRadius c) * ∑ j ∈ Icc 1 N,
          (G j ^ 2 / j) * ((nearRowIndices c N j).card : ℝ) := by
      rw [← mul_sum, sum_comm]
      congr 1
      refine sum_congr rfl fun j _ => ?_
      have hfilt : (Icc 1 N).filter (· ∈ nearRowIndices c N j) = nearRowIndices c N j :=
        filter_eq_self.mpr fun n hn => (mem_filter.mp hn).1
      rw [← sum_filter, hfilt, sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ (2 * linearNearRowRadius c) * ∑ j ∈ Icc 1 N,
          (G j ^ 2 / j) * (2 * ((j : ℝ) * (linearNearRowRadius c / N))) := by
      refine mul_le_mul_of_nonneg_left (sum_le_sum fun j hj => ?_) (by positivity)
      exact mul_le_mul_of_nonneg_left (hcol_card j hj)
        (div_nonneg (sq_nonneg _) (Nat.cast_nonneg j))
    _ = 4 * linearNearRowRadius c ^ 2 / N * ∑ j ∈ Icc 1 N, G j ^ 2 := by
      rw [mul_sum, mul_sum]
      refine sum_congr rfl fun j hj => ?_
      have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_ne_zero (by have := (mem_Icc.mp hj).1; omega)).ne'
      field_simp [hj0, hN0.ne']
      ring

/-! ## Section 2: Collective Bounds on Replacement, Center, Near, and Upward Blocks -/

/-- Collective self-energy replacement bound across `1 ≤ m ≤ M`. -/
private theorem sum_completeWeilSelfError_norm_sq_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM_int : 0 < ∫ u, φ u ^ 2) {M N : ℕ} (hM : 1 ≤ M) (hMN : M * M ≤ N)
    (hL : 4 * Real.exp 7 ≤ Real.log N) {c : ℝ} (hc0 : 0 < c) (hcN : c ≤ N) :
    (∑ m ∈ Icc 1 M,
      ‖completeWeilSelfError φ c N • normalizedRamanujanHorizonVector m N‖ ^ 2) ≤
      2 * Real.exp 1 * M * c ^ 2 := by
  have hN1 : 1 ≤ N := (Nat.mul_pos hM hM).trans_le hMN
  have hN0 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hs := abs_completeWeilSelfError_le_of_width_le_one hφ hsupp hM_int hc0 hN1 hcN
  have hs_le : |completeWeilSelfError φ c N| ≤ Real.exp (1 / 2) / 2 * c :=
    hs.trans (mul_le_mul_of_nonneg_left (div_le_self hc0.le hN0) (by positivity))
  have hssq : completeWeilSelfError φ c N ^ 2 ≤ Real.exp 1 / 4 * c ^ 2 := by
    have h := mul_self_le_mul_self (abs_nonneg _) hs_le
    rw [← sq, sq_abs, ← sq] at h
    refine h.trans_eq ?_
    have hexp : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
      rw [sq, ← Real.exp_add]; norm_num
    calc
      (Real.exp (1 / 2) / 2 * c) ^ 2 = Real.exp (1 / 2) ^ 2 / 4 * c ^ 2 := by ring
      _ = Real.exp 1 / 4 * c ^ 2 := by rw [hexp]
  have hpt : ∀ m ∈ Icc 1 M,
      ‖completeWeilSelfError φ c N • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
        2 * Real.exp 1 * c ^ 2 := by
    intro m hm
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have hv := normalizedRamanujanHorizonVector_norm_sq_le_six hm hMN hL
    have hmul := mul_le_mul hssq hv (sq_nonneg _) (by positivity)
    have he0 : 0 ≤ Real.exp 1 * c ^ 2 := by positivity
    nlinarith only [hmul, he0]
  calc
    _ ≤ ∑ _m ∈ Icc 1 M, 2 * Real.exp 1 * c ^ 2 := sum_le_sum hpt
    _ = 2 * Real.exp 1 * M * c ^ 2 := by
      rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]; ring

/-- Collective center-matrix residual bound across `1 ≤ m ≤ M`: `O(M * c^2 * log N)`. -/
private theorem exists_sum_fullWeilCenter_norm_sq_le (φ : ℝ → ℝ) :
    ∃ C_c : ℝ, 0 < C_c ∧ ∀ M N : ℕ, 1 ≤ M → M * M ≤ N → 4 * Real.exp 7 ≤ Real.log N →
      ∀ c : ℝ,
        (∑ m ∈ Icc 1 M,
          ‖Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N)
              (normalizedRamanujanHorizonVector m N) -
            (if m = 1 then completeWeilPoleShift φ c else 0) •
              normalizedRamanujanHorizonVector m N‖ ^ 2) ≤
          C_c * M * c ^ 2 * Real.log N := by
  obtain ⟨Cc1, hCc1, hc1⟩ := exists_fullWeilCenter_norm_sq_polynomial_bound φ one_pos
  let q := completeWeilPoleShift φ 1
  refine ⟨Cc1 + 132 * q ^ 2 + 1, by positivity, ?_⟩
  intro M N hM hMN hL c
  have hN1 : 1 ≤ N := (Nat.mul_pos hM hM).trans_le hMN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hlogN : 1 ≤ Real.log N := by linarith [Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 7)]
  have hLN0 : 0 < Real.log N := zero_lt_one.trans_le hlogN
  have hMN_le : M ≤ N := (Nat.le_mul_self M).trans hMN
  let α := completeWeilPoleShift φ c
  have hα : α = c * q := by dsimp only [α, q]; unfold completeWeilPoleShift; ring
  have hα2 : α ^ 2 = c ^ 2 * q ^ 2 := by rw [hα]; ring
  -- Pole part of `fullWeilCenterMatrix α N` via dual Bessel Hilbert–Schmidt.
  let Apole : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ :=
    fun n j => (α / N) * arithmeticPoleKernel n j
  have hpole_sum : (∑ m ∈ Icc 1 M,
      ‖Matrix.toEuclideanLin Apole (normalizedRamanujanHorizonVector m N)‖ ^ 2) ≤
      48 * q ^ 2 * c ^ 2 * Real.log N := by
    have hhs : (∑ n : PrimeHorizonIndex N, ∑ j : PrimeHorizonIndex N, Apole n j ^ 2) ≤
        8 * α ^ 2 * Real.log N := by
      have hfac : (∑ n : PrimeHorizonIndex N, ∑ j : PrimeHorizonIndex N, Apole n j ^ 2) =
          (α / N) ^ 2 *
            ∑ n : PrimeHorizonIndex N, ∑ j : PrimeHorizonIndex N, arithmeticPoleKernel n j ^ 2 := by
        dsimp only [Apole]
        simp_rw [mul_pow, ← mul_sum]
      rw [hfac]
      exact (mul_le_mul_of_nonneg_left (sum_sq_arithmeticPoleKernel_le hlogN) (sq_nonneg _)).trans_eq
        (by field_simp [hN0.ne'])
    exact (sum_matrix_action_norm_sq_le_six_mul_hs hMN hL Apole).trans
      ((mul_le_mul_of_nonneg_left hhs (by norm_num)).trans_eq (by rw [hα2]; ring))
  -- Collar part of `fullWeilCenterMatrix α N` via weighted Schur (`w j = 1 / √j`).
  let Acollar : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ :=
    fun n j => (α / N) * archimedeanCenterKernel n j
  have hH0 : 0 ≤ (harmonic N : ℝ) := by exact_mod_cast harmonic_nonneg N
  have hH1 : 0 ≤ (harmonic N : ℝ) + 1 := by linarith only [hH0]
  have hH_le : (harmonic N : ℝ) + 1 ≤ 3 * Real.log N := by
    linarith [harmonic_le_one_add_log N, hlogN]
  have hcollar_pt : ∀ m ∈ Icc 1 M,
      ‖Matrix.toEuclideanLin Acollar (normalizedRamanujanHorizonVector m N)‖ ^ 2 ≤
        18 * q ^ 2 * c ^ 2 * Real.log N := by
    intro m hm
    obtain ⟨hm1, hmM⟩ := mem_Icc.mp hm
    have hschur := sum_sq_abs_majorized_kernel_le
      (N := N) archimedeanCenterKernel archimedeanCenterKernel
      (fun j => normalizedRamanujanMode m j / Real.sqrt j)
      (fun j => 1 / Real.sqrt j)
      (fun n => (N : ℝ) * ((harmonic N : ℝ) + 1) / Real.sqrt n)
      (fun j => (N : ℝ) * ((harmonic N : ℝ) + 1) ^ 2 * j)
      (fun n _ j _ => archimedeanCenterKernel_nonneg n j)
      (fun n _ j _ => abs_of_nonneg (archimedeanCenterKernel_nonneg n j) |>.le)
      (fun j hj => by
        have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hj).1
        exact one_div_pos.mpr (Real.sqrt_pos.mpr hj0))
      (fun n hn => by
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
        have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
        have hsn : Real.sqrt n ≤ (N : ℝ) / Real.sqrt n := by
          rw [le_div_iff₀ (Real.sqrt_pos.mpr hn0), Real.mul_self_sqrt hn0.le]
          exact hnN
        have h1 : (∑ j ∈ Icc 1 N, archimedeanCenterKernel n j * (1 / Real.sqrt j)) =
            ∑ j ∈ Icc 1 N, archimedeanCenterKernel n j / Real.sqrt j :=
          sum_congr rfl fun j _ => mul_one_div _ _
        rw [h1]
        exact (sum_archimedeanCenterKernel_div_sqrt_le hn).trans
          ((mul_le_mul_of_nonneg_right hsn hH1).trans_eq (by ring)))
      (fun j hj => by
        have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hj).1
        have h1 : (∑ n ∈ Icc 1 N, archimedeanCenterKernel n j *
            (((N : ℝ) * ((harmonic N : ℝ) + 1) / Real.sqrt n) / (1 / Real.sqrt j))) =
            ((N : ℝ) * ((harmonic N : ℝ) + 1) * Real.sqrt j) *
              ∑ n ∈ Icc 1 N, archimedeanCenterKernel j n / Real.sqrt n := by
          rw [mul_sum]
          refine sum_congr rfl fun n _ => ?_
          rw [archimedeanCenterKernel_comm n j]
          field_simp [(Real.sqrt_pos.mpr hj0).ne']
        rw [h1]
        refine (mul_le_mul_of_nonneg_left (sum_archimedeanCenterKernel_div_sqrt_le hj)
          (mul_nonneg (mul_nonneg hN0.le hH1) (Real.sqrt_nonneg j))).trans_eq ?_
        calc
          ((N : ℝ) * ((harmonic N : ℝ) + 1) * Real.sqrt j) * (Real.sqrt j * ((harmonic N : ℝ) + 1)) =
              (N : ℝ) * ((harmonic N : ℝ) + 1) ^ 2 * (Real.sqrt j * Real.sqrt j) := by ring
          _ = (N : ℝ) * ((harmonic N : ℝ) + 1) ^ 2 * j := by rw [Real.mul_self_sqrt hj0.le])
    have hmode_sum : (∑ j ∈ Icc 1 N,
        ((N : ℝ) * ((harmonic N : ℝ) + 1) ^ 2 * j) *
          (normalizedRamanujanMode m j / Real.sqrt j) ^ 2) ≤
        2 * (N : ℝ) ^ 2 * (3 * Real.log N) ^ 2 := by
      have heq : (∑ j ∈ Icc 1 N,
          ((N : ℝ) * ((harmonic N : ℝ) + 1) ^ 2 * j) *
            (normalizedRamanujanMode m j / Real.sqrt j) ^ 2) =
          (N : ℝ) * ((harmonic N : ℝ) + 1) ^ 2 *
            ∑ j ∈ Icc 1 N, normalizedRamanujanMode m j ^ 2 := by
        rw [mul_sum]
        refine sum_congr rfl fun j hj => ?_
        have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hj).1
        rw [div_pow, Real.sq_sqrt hj0.le]
        field_simp [hj0.ne']
      rw [heq]
      have hH2 : ((harmonic N : ℝ) + 1) ^ 2 ≤ (3 * Real.log N) ^ 2 :=
        pow_le_pow_left₀ hH1 hH_le 2
      have hm_sq := sum_Icc_normalizedRamanujanMode_sq_le hm1 (hmM.trans hMN_le)
      calc
        (N : ℝ) * ((harmonic N : ℝ) + 1) ^ 2 * ∑ j ∈ Icc 1 N, normalizedRamanujanMode m j ^ 2 ≤
            (N : ℝ) * (3 * Real.log N) ^ 2 * (2 * N) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hH2 hN0.le) hm_sq
            (sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
        _ = 2 * (N : ℝ) ^ 2 * (3 * Real.log N) ^ 2 := by ring
    have hnorm_eq : ‖Matrix.toEuclideanLin Acollar (normalizedRamanujanHorizonVector m N)‖ ^ 2 =
        (α / N) ^ 2 *
          (∑ n ∈ Icc 1 N,
            (∑ j ∈ Icc 1 N, archimedeanCenterKernel n j *
              (normalizedRamanujanMode m j / Real.sqrt j)) ^ 2) / Real.log N := by
      have hsm : Acollar = (α / N) •
          ((fun n j => archimedeanCenterKernel n j) :
            Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ) := rfl
      rw [hsm, map_smul, LinearMap.smul_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
        matrix_normalizedRamanujan_norm_sq, mul_div_assoc]
    rw [hnorm_eq]
    calc
      (α / N) ^ 2 * (∑ n ∈ Icc 1 N,
          (∑ j ∈ Icc 1 N, archimedeanCenterKernel n j *
            (normalizedRamanujanMode m j / Real.sqrt j)) ^ 2) / Real.log N ≤
          (α / N) ^ 2 * (2 * (N : ℝ) ^ 2 * (3 * Real.log N) ^ 2) / Real.log N :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hschur.trans hmode_sum) (sq_nonneg _))
          hLN0.le
      _ = 18 * q ^ 2 * c ^ 2 * Real.log N := by
        rw [div_pow, hα2]; field_simp [hN0.ne', hLN0.ne']
  -- Split `Icc 1 M = insert 1 (Icc 2 M)`.
  have hunion : Icc 1 M = insert 1 (Icc 2 M) := by
    ext m; simp only [mem_Icc, mem_insert]; omega
  have hnot1 : (1 : ℕ) ∉ Icc 2 M := by simp
  have hdecomp : fullWeilCenterMatrix α N = Apole - Acollar := by
    ext n j
    simp only [fullWeilCenterMatrix, Apole, Acollar, Matrix.sub_apply]
    ring
  have hm1_bound :
      ‖Matrix.toEuclideanLin (fullWeilCenterMatrix α N) (normalizedRamanujanHorizonVector 1 N) -
        (if (1 : ℕ) = 1 then α else 0) • normalizedRamanujanHorizonVector 1 N‖ ^ 2 ≤
        Cc1 * M * c ^ 2 * Real.log N := by
    have hbase := hc1 c N
    have hL2 : 1 ≤ (Real.log N) ^ 2 := by nlinarith only [hlogN]
    have hM1R : (1 : ℝ) ≤ M := by exact_mod_cast hM
    calc
      _ ≤ Cc1 * c ^ 2 / Real.log N := hbase
      _ ≤ Cc1 * c ^ 2 * Real.log N := by
        rw [div_le_iff₀ hLN0]
        nlinarith only [mul_nonneg hCc1 (sq_nonneg c), hL2]
      _ ≤ Cc1 * M * c ^ 2 * Real.log N := by
        have h := mul_le_mul_of_nonneg_right hM1R
          (show 0 ≤ Cc1 * c ^ 2 * Real.log N by positivity)
        nlinarith only [h]
  have hrest_bound :
      (∑ m ∈ Icc 2 M,
        ‖Matrix.toEuclideanLin (fullWeilCenterMatrix α N) (normalizedRamanujanHorizonVector m N) -
          (if m = 1 then α else 0) • normalizedRamanujanHorizonVector m N‖ ^ 2) ≤
        132 * q ^ 2 * M * c ^ 2 * Real.log N := by
    have hsub2 : Icc 2 M ⊆ Icc 1 M := fun m hm =>
      mem_Icc.mpr ⟨by have := (mem_Icc.mp hm).1; omega, (mem_Icc.mp hm).2⟩
    have hpt2 : ∀ m ∈ Icc 2 M,
        ‖Matrix.toEuclideanLin (fullWeilCenterMatrix α N) (normalizedRamanujanHorizonVector m N) -
          (if m = 1 then α else 0) • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
          2 * ‖Matrix.toEuclideanLin Apole (normalizedRamanujanHorizonVector m N)‖ ^ 2 +
            36 * q ^ 2 * c ^ 2 * Real.log N := by
      intro m hm
      have hm_ne : m ≠ 1 := by have := (mem_Icc.mp hm).1; omega
      rw [if_neg hm_ne, zero_smul, sub_zero, hdecomp, map_sub, LinearMap.sub_apply]
      have h2 := norm_sub_sq_le_two
        (Matrix.toEuclideanLin Apole (normalizedRamanujanHorizonVector m N))
        (Matrix.toEuclideanLin Acollar (normalizedRamanujanHorizonVector m N))
      have hc_m := hcollar_pt m (hsub2 hm)
      linarith only [h2, hc_m]
    have hpole2 : (∑ m ∈ Icc 2 M,
        ‖Matrix.toEuclideanLin Apole (normalizedRamanujanHorizonVector m N)‖ ^ 2) ≤
        48 * q ^ 2 * M * c ^ 2 * Real.log N := by
      have hM1R : (1 : ℝ) ≤ M := by exact_mod_cast hM
      calc
        _ ≤ ∑ m ∈ Icc 1 M,
              ‖Matrix.toEuclideanLin Apole (normalizedRamanujanHorizonVector m N)‖ ^ 2 :=
          sum_le_sum_of_subset_of_nonneg hsub2 fun _ _ _ => sq_nonneg _
        _ ≤ 48 * q ^ 2 * c ^ 2 * Real.log N := hpole_sum
        _ ≤ 48 * q ^ 2 * M * c ^ 2 * Real.log N := by
          have h := mul_le_mul_of_nonneg_right hM1R
            (show 0 ≤ 48 * q ^ 2 * c ^ 2 * Real.log N by positivity)
          nlinarith only [h]
    have hcard2 : ((Icc 2 M).card : ℝ) ≤ M := by
      rw [Nat.card_Icc]
      exact_mod_cast (show M + 1 - 2 ≤ M by omega)
    calc
      _ ≤ ∑ m ∈ Icc 2 M,
            (2 * ‖Matrix.toEuclideanLin Apole (normalizedRamanujanHorizonVector m N)‖ ^ 2 +
              36 * q ^ 2 * c ^ 2 * Real.log N) := sum_le_sum hpt2
      _ = 2 * (∑ m ∈ Icc 2 M,
            ‖Matrix.toEuclideanLin Apole (normalizedRamanujanHorizonVector m N)‖ ^ 2) +
          ((Icc 2 M).card : ℝ) * (36 * q ^ 2 * c ^ 2 * Real.log N) := by
        rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
      _ ≤ 2 * (48 * q ^ 2 * M * c ^ 2 * Real.log N) +
            M * (36 * q ^ 2 * c ^ 2 * Real.log N) :=
        add_le_add (mul_le_mul_of_nonneg_left hpole2 zero_le_two)
          (mul_le_mul_of_nonneg_right hcard2 (by positivity))
      _ = 132 * q ^ 2 * M * c ^ 2 * Real.log N := by ring
  rw [hunion, sum_insert hnot1]
  have hextra : 0 ≤ (M : ℝ) * c ^ 2 * Real.log N := by positivity
  nlinarith only [hm1_bound, hrest_bound, hextra]

/-- Collective separated-cross error bound across `1 ≤ m ≤ M`: `O(M * c^4)`. -/
private theorem exists_sum_separatedCrossError_norm_sq_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM_int : 0 < ∫ u, φ u ^ 2) :
    ∃ C_x : ℝ, 0 < C_x ∧ ∀ M N : ℕ, 1 ≤ M → M * M ≤ N → 4 * Real.exp 7 ≤ Real.log N →
      ∀ c : ℝ, 0 < c →
        (∑ m ∈ Icc 1 M,
          ‖Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N)
            (normalizedRamanujanHorizonVector m N)‖ ^ 2) ≤
          C_x * M * c ^ 4 := by
  let K₀ := 152 * (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2)
  have hK₀ : 0 ≤ K₀ := by dsimp only [K₀]; positivity
  refine ⟨96 * K₀ ^ 2 + 1, by positivity, ?_⟩
  intro M N hM hMN hL c hc0
  have hN1 : 1 ≤ N := (Nat.mul_pos hM hM).trans_le hMN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hlogN : 1 ≤ Real.log N := by linarith [Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 7)]
  have hLN0 : 0 < Real.log N := zero_lt_one.trans_le hlogN
  let K : ℕ → ℕ → ℝ := fun n j =>
    if 2 * (c / N) < |Real.log j - Real.log n| then
      atomCrossErrorKernel (atomDilate φ (c / N)) n j else 0
  let U : ℕ → ℕ → ℝ := fun n j =>
    (K₀ * (c / N) ^ 2) * (max (n : ℝ) j) ^ 2 / |(n : ℝ) - j| ^ 2
  have hU_nonneg : ∀ n ∈ Icc 1 N, ∀ j ∈ Icc 1 N, 0 ≤ U n j :=
    fun _ _ _ _ => by dsimp only [U]; positivity
  have hU_symm : ∀ n j, U n j = U j n := fun n j => by
    dsimp only [U]
    rw [max_comm, abs_sub_comm]
  have hU_row : ∀ n ∈ Icc 1 N, (∑ j ∈ Icc 1 N, U n j) ≤ 4 * K₀ * c ^ 2 := by
    intro n hn
    have h1 := sum_abs_kernel_le_of_integer_distance (K := K₀ * (c / N) ^ 2) (E := U)
      (by positivity) (fun a _ b _ => by rw [abs_of_nonneg (by dsimp only [U]; positivity)]) hn
    have hsum : (∑ j ∈ Icc 1 N, U n j) = ∑ j ∈ Icc 1 N, |U n j| :=
      sum_congr rfl fun j hj => (abs_of_nonneg (hU_nonneg n hn j hj)).symm
    rw [hsum]
    exact h1.trans_eq (by field_simp [hN0.ne'])
  have hpt : ∀ m ∈ Icc 1 M,
      ‖Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N)
        (normalizedRamanujanHorizonVector m N)‖ ^ 2 ≤ 96 * K₀ ^ 2 * c ^ 4 := by
    intro m hm
    have hschur := sum_sq_abs_majorized_kernel_le (N := N) K U
      (fun j => normalizedRamanujanMode m j / Real.sqrt j)
      (fun _ => 1) (fun _ => 4 * K₀ * c ^ 2) (fun _ => 16 * K₀ ^ 2 * c ^ 4)
      hU_nonneg
      (fun n hn j hj => abs_separatedCrossError_le hφ hsupp hM_int hc0 hN1 hn hj)
      (fun _ _ => zero_lt_one)
      (fun n hn => by simpa only [mul_one] using hU_row n hn)
      (fun j hj => by
        have h1 : (∑ n ∈ Icc 1 N, U n j * (4 * K₀ * c ^ 2 / 1)) =
            (4 * K₀ * c ^ 2) * ∑ n ∈ Icc 1 N, U j n := by
          rw [mul_sum]; exact sum_congr rfl fun n _ => by rw [hU_symm n j]; ring
        rw [h1]
        exact (mul_le_mul_of_nonneg_left (hU_row j hj) (by positivity)).trans_eq (by ring))
    have hnorm_eq : ‖Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N)
        (normalizedRamanujanHorizonVector m N)‖ ^ 2 =
        (∑ n ∈ Icc 1 N, (∑ j ∈ Icc 1 N, K n j *
          (normalizedRamanujanMode m j / Real.sqrt j)) ^ 2) / Real.log N :=
      matrix_normalizedRamanujan_norm_sq K
    have hv_norm : (∑ j ∈ Icc 1 N, (normalizedRamanujanMode m j / Real.sqrt j) ^ 2) / Real.log N =
        ‖normalizedRamanujanHorizonVector m N‖ ^ 2 := by
      rw [normalizedRamanujanHorizonVector, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
        inv_pow, Real.sq_sqrt hLN0.le, ramanujanHorizonVector_norm_sq, div_eq_inv_mul]
      rfl
    rw [hnorm_eq]
    calc
      _ ≤ (∑ j ∈ Icc 1 N, (16 * K₀ ^ 2 * c ^ 4) *
            (normalizedRamanujanMode m j / Real.sqrt j) ^ 2) / Real.log N :=
        div_le_div_of_nonneg_right hschur hLN0.le
      _ = 16 * K₀ ^ 2 * c ^ 4 * ‖normalizedRamanujanHorizonVector m N‖ ^ 2 := by
        rw [← mul_sum, mul_div_assoc, hv_norm]
      _ ≤ 16 * K₀ ^ 2 * c ^ 4 * 6 :=
        mul_le_mul_of_nonneg_left (normalizedRamanujanHorizonVector_norm_sq_le_six hm hMN hL)
          (by positivity)
      _ = 96 * K₀ ^ 2 * c ^ 4 := by ring
  calc
    _ ≤ ∑ _m ∈ Icc 1 M, 96 * K₀ ^ 2 * c ^ 4 := sum_le_sum hpt
    _ = 96 * K₀ ^ 2 * M * c ^ 4 := by
      rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]; ring
    _ ≤ (96 * K₀ ^ 2 + 1) * M * c ^ 4 := by
      have hextra : 0 ≤ (M : ℝ) * c ^ 4 := by positivity
      nlinarith only [hextra]

/-- Collective two-pole moment replacement bound across `1 ≤ m ≤ M`: `O(M * c^4)`. -/
private theorem exists_sum_fullWeilPoleError_norm_sq_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM_int : 0 < ∫ u, φ u ^ 2) :
    ∃ C_q : ℝ, 0 < C_q ∧ ∀ M N : ℕ, 1 ≤ M → M * M ≤ N → 4 * Real.exp 7 ≤ Real.log N →
      ∀ c : ℝ, 0 < c → c ≤ N →
        (∑ m ∈ Icc 1 M,
          ‖Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N)
            (normalizedRamanujanHorizonVector m N)‖ ^ 2) ≤
          C_q * M * c ^ 4 := by
  let C_pole := atomPoleMomentErrorConstant φ
  refine ⟨48 * C_pole ^ 2 + 1, by positivity, ?_⟩
  intro M N hM hMN hL c hc0 hcN
  have hN1 : 1 ≤ N := (Nat.mul_pos hM hM).trans_le hMN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hlogN : 1 ≤ Real.log N := by linarith [Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 7)]
  have hd := abs_atomPoleErrorCoefficient_le_of_le hφ hsupp hM_int hc0 hN1 hcN
  have hdsq : atomPoleErrorCoefficient φ c N ^ 2 ≤ C_pole ^ 2 * (c / N) ^ 4 := by
    have h := mul_self_le_mul_self (abs_nonneg _) hd
    rw [← sq, sq_abs, ← sq] at h
    exact h.trans_eq (by ring)
  have hhs : (∑ n : PrimeHorizonIndex N, ∑ j : PrimeHorizonIndex N,
      fullWeilPoleErrorMatrix φ c N n j ^ 2) ≤ 8 * C_pole ^ 2 * c ^ 4 * Real.log N / (N : ℝ) ^ 2 := by
    have hfac : (∑ n : PrimeHorizonIndex N, ∑ j : PrimeHorizonIndex N,
        fullWeilPoleErrorMatrix φ c N n j ^ 2) =
        atomPoleErrorCoefficient φ c N ^ 2 *
          ∑ n : PrimeHorizonIndex N, ∑ j : PrimeHorizonIndex N, arithmeticPoleKernel n j ^ 2 := by
      unfold fullWeilPoleErrorMatrix
      simp_rw [mul_pow, ← mul_sum]
    rw [hfac]
    calc
      _ ≤ (C_pole ^ 2 * (c / N) ^ 4) * (8 * (N : ℝ) ^ 2 * Real.log N) :=
        mul_le_mul hdsq (sum_sq_arithmeticPoleKernel_le hlogN)
          (sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
      _ = 8 * C_pole ^ 2 * c ^ 4 * Real.log N / (N : ℝ) ^ 2 := by
        field_simp [hN0.ne']
  have hlog_div : Real.log N / (N : ℝ) ^ 2 ≤ 1 := by
    rw [div_le_one (sq_pos_of_pos hN0)]
    have h1 : Real.log N ≤ N := (Real.log_le_sub_one_of_pos hN0).trans (by linarith)
    have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    nlinarith only [h1, hN1R]
  have hM1R : (1 : ℝ) ≤ M := by exact_mod_cast hM
  calc
    (∑ m ∈ Icc 1 M,
        ‖Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N)
          (normalizedRamanujanHorizonVector m N)‖ ^ 2) ≤
        6 * (8 * C_pole ^ 2 * c ^ 4 * Real.log N / (N : ℝ) ^ 2) :=
      (sum_matrix_action_norm_sq_le_six_mul_hs hMN hL _).trans
        (mul_le_mul_of_nonneg_left hhs (by norm_num))
    _ = 48 * C_pole ^ 2 * c ^ 4 * (Real.log N / (N : ℝ) ^ 2) := by ring
    _ ≤ 48 * C_pole ^ 2 * c ^ 4 * 1 :=
      mul_le_mul_of_nonneg_left hlog_div (by positivity)
    _ ≤ (48 * C_pole ^ 2 + 1) * M * c ^ 4 := by
      have h1 := mul_le_mul_of_nonneg_right hM1R (show 0 ≤ 48 * C_pole ^ 2 * c ^ 4 by positivity)
      have hextra : 0 ≤ (M : ℝ) * c ^ 4 := by positivity
      nlinarith only [h1, hextra]

/-- Prefix `L²` bound on the normalized logarithmic divisor jet via Plancherel periodicity. -/
private theorem sum_Icc_ramanujanLogDivisorJet_div_totient_sq_le {m N : ℕ}
    (hm : 0 < m) (hmN : m ≤ N) :
    (∑ j ∈ Icc 1 N, (ramanujanLogDivisorJet m j / Real.sqrt (m.totient : ℝ)) ^ 2) ≤
      4 * (N : ℝ) * (Real.log m) ^ 2 := by
  have hφm : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  let f : ℕ → ℝ := fun j => (ramanujanLogDivisorJet m j / Real.sqrt (m.totient : ℝ)) ^ 2
  have hf_per : Function.Periodic f m := fun j => by
    dsimp only [f]
    rw [ramanujanLogDivisorJet_periodic m j]
  have hrng : (∑ r ∈ range m, f r) ≤ 2 * (m : ℝ) * (Real.log m) ^ 2 := by
    have hfac : (∑ r ∈ range m, f r) =
        (∑ r ∈ range m, ramanujanLogDivisorJet m r ^ 2) / (m.totient : ℝ) := by
      dsimp only [f]
      simp_rw [div_pow, Real.sq_sqrt hφm.le, ← sum_div]
    rw [hfac, sum_range_ramanujanLogDivisorJet_sq hm]
    have hv := sum_vonMangoldt_sq_mul_totient_le hm
    rw [div_le_iff₀ hφm]
    nlinarith only [mul_le_mul_of_nonneg_left hv (Nat.cast_nonneg (α := ℝ) m)]
  have hIcc_m : (∑ j ∈ Icc 1 m, f j) = ∑ r ∈ range m, f r := by
    have h0 : Icc 1 m = Ioc 0 (0 + m) := by ext x; simp only [mem_Icc, mem_Ioc]; omega
    rw [h0, sum_Ioc_periodic_eq hm hf_per 0]
  have h0N : Icc 1 N = Ioc 0 N := by ext x; simp only [mem_Icc, mem_Ioc]; omega
  rw [h0N]
  calc
    (∑ j ∈ Ioc 0 N, f j) ≤ (((N - 0) / m + 1 : ℕ) : ℝ) * ∑ j ∈ Icc 1 m, f j :=
      sum_Ioc_le_mul_sum_Icc_of_periodic_pos hm (fun _ _ => sq_nonneg _)
        (fun j _ => hf_per j) 0 N
    _ ≤ (((N / m + 1 : ℕ) : ℝ)) * (2 * (m : ℝ) * (Real.log m) ^ 2) := by
      rw [Nat.sub_zero, hIcc_m]
      exact mul_le_mul_of_nonneg_left hrng (Nat.cast_nonneg _)
    _ = 2 * (((N / m : ℕ) : ℝ) * m + m) * (Real.log m) ^ 2 := by push_cast; ring
    _ ≤ 4 * (N : ℝ) * (Real.log m) ^ 2 := by
      have hdiv : ((N / m : ℕ) : ℝ) * m ≤ N := by exact_mod_cast Nat.div_mul_le_self N m
      have hmNR : (m : ℝ) ≤ N := by exact_mod_cast hmN
      exact mul_le_mul_of_nonneg_right (by linarith only [hdiv, hmNR]) (sq_nonneg _)

/-- Collective interior near-Gamma / downward cancellation bound across `1 ≤ m ≤ M`. -/
private theorem exists_sum_interiorNearGammaDownward_norm_sq_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM_int : 0 < ∫ u, φ u ^ 2) :
    ∃ C_in : ℝ, 0 < C_in ∧ ∀ M N : ℕ, 1 ≤ M → M * M ≤ N → 1 ≤ Real.log N →
      ∀ c : ℝ, 1 ≤ c → c / N ≤ 1 / 3 →
        (∑ m ∈ Icc 1 M,
          ‖(Real.sqrt (m.totient : ℝ))⁻¹ • normalizedNearGammaDownwardVector φ c N m‖ ^ 2) ≤
          C_in * M * (c ^ 4 + c ^ 2 * Real.log N) := by
  obtain ⟨Cp, hCp, hpair⟩ := exists_abs_atomArchPair_near_sub_le hφ hsupp hM_int
  let A₀ := Cp + 2 * Real.exp 2 + 1
  have hA₀ : 0 ≤ A₀ := by dsimp only [A₀]; positivity
  let R₀ := 2 * Real.exp 2
  refine ⟨16 * R₀ ^ 2 * (A₀ ^ 2 + 2) + 1, by positivity, ?_⟩
  intro M N hM hMN hlogN c hc1 hw1
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hw : c / N ≤ 1 := hw1.trans (by norm_num)
  have hN1 : 1 ≤ N := (Nat.mul_pos hM hM).trans_le hMN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hLN0 : 0 < Real.log N := zero_lt_one.trans_le hlogN
  have hMN_le : M ≤ N := (Nat.le_mul_self M).trans hMN
  have hlogc : |Real.log c| ≤ c := by
    rw [abs_of_nonneg (Real.log_nonneg hc1)]
    exact (Real.log_le_sub_one_of_pos hc0).trans (by linarith only [hc0])
  have hR_eq : linearNearRowRadius c = R₀ * c := by unfold linearNearRowRadius; dsimp only [R₀]; ring
  have hpt : ∀ m ∈ Icc 1 M,
      ‖(Real.sqrt (m.totient : ℝ))⁻¹ • normalizedNearGammaDownwardVector φ c N m‖ ^ 2 ≤
        16 * R₀ ^ 2 * (A₀ ^ 2 + 2) * (c ^ 4 + c ^ 2 * Real.log N) := by
    intro m hm
    obtain ⟨hm1, hmM⟩ := mem_Icc.mp hm
    have hmN : m ≤ N := hmM.trans hMN_le
    have hφm : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm1
    have hsm : 0 < Real.sqrt (m.totient : ℝ) := Real.sqrt_pos.mpr hφm
    let G : ℕ → ℝ := fun j =>
      A₀ * c * |normalizedRamanujanMode m j| +
        |ramanujanLogDivisorJet m j| / Real.sqrt (m.totient : ℝ)
    have hG0 : ∀ j ∈ Icc 1 N, 0 ≤ G j := fun j _ => by dsimp only [G]; positivity
    have hFG : ∀ n ∈ Icc 1 N, ∀ j ∈ nearRowIndices c N n,
        |nearGammaDownwardCoefficient φ c N m n j / Real.sqrt (m.totient : ℝ)| ≤ G j := by
      intro n hn j hj
      have hjN := (mem_filter.mp hj).1
      have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hjN).1
      have hs : |Real.log j - Real.log n| ≤ 2 * (c / N) := by
        have h := (mem_filter.mp hj).2.2
        change |Real.log j - Real.log n| ≤ 2 * c / N at h
        simpa only [mul_div_assoc] using h
      let q := shellAutocorr φ (|Real.log j - Real.log n| / (c / N)) / (∫ u, φ u ^ 2)
      let a := atomArchPair (atomDilate φ (c / N)) n j / (∫ u, atomDilate φ (c / N) u ^ 2)
      have hrem : |a - Real.log (1 / (c / N)) * q| ≤ Cp := by
        dsimp only [a, q]
        rw [← mul_div_assoc]
        exact hpair (c / N) (div_pos hc0 hN0) hw1 n j hs
      have hq : |q| ≤ 1 := by
        have h := abs_bumpCorr_le hφ.continuous (hasCompactSupport_profile hsupp)
          (|Real.log j - Real.log n| / (c / N))
        change |shellAutocorr φ (|Real.log j - Real.log n| / (c / N))| ≤ ∫ u, φ u ^ 2 at h
        dsimp only [q]
        rw [abs_div, abs_of_pos hM_int, div_le_one hM_int]
        exact h
      have hquot : (N : ℝ) / j ≤ linearNearRowRadius c :=
        (div_le_iff₀ hj0).mpr (nearRow_geometry_small_width hc0 hn hj hw).2.2
      have hloglow : 0 ≤ Real.log N - Real.log j := sub_nonneg.mpr
        (Real.log_le_log hj0 (by exact_mod_cast (mem_Icc.mp hjN).2))
      have hloghigh : Real.log N - Real.log j ≤ linearNearRowRadius c := by
        have h := Real.log_le_sub_one_of_pos (div_pos hN0 hj0)
        rw [Real.log_div hN0.ne' hj0.ne'] at h
        linarith only [h, hquot]
      have hlog : |Real.log (1 / (c / N)) - Real.log j| ≤ linearNearRowRadius c + |Real.log c| := by
        have hlogeq : Real.log (1 / (c / N)) = Real.log N - Real.log c := by
          rw [one_div, Real.log_inv, Real.log_div hc0.ne' hN0.ne']; ring
        rw [hlogeq, show Real.log N - Real.log c - Real.log j =
          (Real.log N - Real.log j) - Real.log c by ring]
        exact (abs_sub _ _).trans (by rw [abs_of_nonneg hloglow]; linarith only [hloghigh])
      have heq : nearGammaDownwardCoefficient φ c N m n j / Real.sqrt (m.totient : ℝ) =
          (a - Real.log (1 / (c / N)) * q) * normalizedRamanujanMode m j +
          (Real.log (1 / (c / N)) - Real.log j) * q * normalizedRamanujanMode m j +
          q * (ramanujanLogDivisorJet m j / Real.sqrt (m.totient : ℝ)) := by
        rw [nearGammaDownwardCoefficient, sum_vonMangoldt_mul_ramanujan_eq_log_sub_jet m
          (mem_Icc.mp hjN).1, normalizedRamanujanMode_eq_coefficient hm1]
        dsimp only [a, q]
        ring
      rw [heq]
      have hcoef_le : Cp + (linearNearRowRadius c + |Real.log c|) ≤ A₀ * c := by
        rw [hR_eq]
        dsimp only [A₀, R₀]
        nlinarith only [hCp, hc1, hlogc]
      calc
        _ ≤ |(a - Real.log (1 / (c / N)) * q) * normalizedRamanujanMode m j| +
            |(Real.log (1 / (c / N)) - Real.log j) * q * normalizedRamanujanMode m j| +
            |q * (ramanujanLogDivisorJet m j / Real.sqrt (m.totient : ℝ))| := abs_add_three _ _ _
        _ ≤ (Cp + (linearNearRowRadius c + |Real.log c|)) * |normalizedRamanujanMode m j| +
              |ramanujanLogDivisorJet m j| / Real.sqrt (m.totient : ℝ) := by
          simp only [abs_mul, abs_div, abs_of_pos hsm]
          have h1 := mul_le_mul_of_nonneg_right hrem (abs_nonneg (normalizedRamanujanMode m j))
          have h2 := mul_le_mul_of_nonneg_right
            (mul_le_mul hlog hq (abs_nonneg _)
              (add_nonneg (by unfold linearNearRowRadius; positivity) (abs_nonneg _)))
            (abs_nonneg (normalizedRamanujanMode m j))
          have h3 := mul_le_mul_of_nonneg_right hq
            (div_nonneg (abs_nonneg (ramanujanLogDivisorJet m j)) hsm.le)
          nlinarith only [h1, h2, h3]
        _ ≤ G j := add_le_add
          (mul_le_mul_of_nonneg_right hcoef_le (abs_nonneg _)) le_rfl
    have hsum_G2 : (∑ j ∈ Icc 1 N, G j ^ 2) ≤
        (N : ℝ) * (4 * A₀ ^ 2 * c ^ 2 + 8 * (Real.log N) ^ 2) := by
      have hpt_G : ∀ j ∈ Icc 1 N, G j ^ 2 ≤
          2 * A₀ ^ 2 * c ^ 2 * normalizedRamanujanMode m j ^ 2 +
            2 * (ramanujanLogDivisorJet m j / Real.sqrt (m.totient : ℝ)) ^ 2 := by
        intro j _
        dsimp only [G]
        calc
          (A₀ * c * |normalizedRamanujanMode m j| +
              |ramanujanLogDivisorJet m j| / Real.sqrt (m.totient : ℝ)) ^ 2 ≤
            2 * (A₀ * c * |normalizedRamanujanMode m j|) ^ 2 +
              2 * (|ramanujanLogDivisorJet m j| / Real.sqrt (m.totient : ℝ)) ^ 2 := by
            nlinarith only [sq_nonneg (A₀ * c * |normalizedRamanujanMode m j| -
              |ramanujanLogDivisorJet m j| / Real.sqrt (m.totient : ℝ))]
          _ = 2 * A₀ ^ 2 * c ^ 2 * normalizedRamanujanMode m j ^ 2 +
              2 * (ramanujanLogDivisorJet m j / Real.sqrt (m.totient : ℝ)) ^ 2 := by
            rw [mul_pow, sq_abs, div_pow, div_pow, sq_abs]; ring
      have hlogm2 : (Real.log m) ^ 2 ≤ (Real.log N) ^ 2 :=
        pow_le_pow_left₀ (Real.log_natCast_nonneg m)
          (Real.log_le_log (by exact_mod_cast hm1) (by exact_mod_cast hmN)) 2
      have hjet_N : (∑ j ∈ Icc 1 N,
          (ramanujanLogDivisorJet m j / Real.sqrt (m.totient : ℝ)) ^ 2) ≤
          4 * (N : ℝ) * (Real.log N) ^ 2 :=
        (sum_Icc_ramanujanLogDivisorJet_div_totient_sq_le hm1 hmN).trans
          (mul_le_mul_of_nonneg_left hlogm2 (by positivity))
      calc
        (∑ j ∈ Icc 1 N, G j ^ 2) ≤
            ∑ j ∈ Icc 1 N, (2 * A₀ ^ 2 * c ^ 2 * normalizedRamanujanMode m j ^ 2 +
              2 * (ramanujanLogDivisorJet m j / Real.sqrt (m.totient : ℝ)) ^ 2) :=
          sum_le_sum hpt_G
        _ = 2 * A₀ ^ 2 * c ^ 2 * (∑ j ∈ Icc 1 N, normalizedRamanujanMode m j ^ 2) +
              2 * ∑ j ∈ Icc 1 N, (ramanujanLogDivisorJet m j / Real.sqrt (m.totient : ℝ)) ^ 2 := by
          rw [sum_add_distrib, ← mul_sum, ← mul_sum]
        _ ≤ 2 * A₀ ^ 2 * c ^ 2 * (2 * N) + 2 * (4 * (N : ℝ) * (Real.log N) ^ 2) :=
          add_le_add (mul_le_mul_of_nonneg_left (sum_Icc_normalizedRamanujanMode_sq_le hm1 hmN)
            (by positivity)) (mul_le_mul_of_nonneg_left hjet_N zero_le_two)
        _ = (N : ℝ) * (4 * A₀ ^ 2 * c ^ 2 + 8 * (Real.log N) ^ 2) := by ring
    have hnorm_eq :
        ‖(Real.sqrt (m.totient : ℝ))⁻¹ • normalizedNearGammaDownwardVector φ c N m‖ ^ 2 =
          (∑ n ∈ Icc 1 N,
            (∑ j ∈ nearRowIndices c N n,
              (nearGammaDownwardCoefficient φ c N m n j / Real.sqrt (m.totient : ℝ)) /
                Real.sqrt j) ^ 2) / Real.log N := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
        normalizedNearGammaDownwardVector_norm_sq, ← mul_div_assoc, mul_sum]
      congr 1
      refine sum_congr rfl fun n _ => ?_
      rw [← mul_pow]
      congr 1
      unfold nearGammaDownwardRow
      rw [mul_sum]
      exact sum_congr rfl fun j _ => by ring
    have hnear := sum_near_div_sqrt_sq_le_profile hc0 hN1 hw
      (fun n j => nearGammaDownwardCoefficient φ c N m n j / Real.sqrt (m.totient : ℝ))
      G hG0 hFG
    rw [hnorm_eq]
    have hc4_div : c ^ 4 / Real.log N ≤ c ^ 4 := div_le_self (by positivity) hlogN
    calc
      _ ≤ (4 * linearNearRowRadius c ^ 2 / N *
            ((N : ℝ) * (4 * A₀ ^ 2 * c ^ 2 + 8 * (Real.log N) ^ 2))) / Real.log N :=
        div_le_div_of_nonneg_right
          (hnear.trans (mul_le_mul_of_nonneg_left hsum_G2 (by positivity))) hLN0.le
      _ = 16 * R₀ ^ 2 * A₀ ^ 2 * (c ^ 4 / Real.log N) + 32 * R₀ ^ 2 * c ^ 2 * Real.log N := by
        rw [hR_eq]; field_simp [hN0.ne', hLN0.ne']; ring
      _ ≤ 16 * R₀ ^ 2 * A₀ ^ 2 * c ^ 4 + 32 * R₀ ^ 2 * c ^ 2 * Real.log N :=
        add_le_add (mul_le_mul_of_nonneg_left hc4_div (by positivity)) le_rfl
      _ ≤ 16 * R₀ ^ 2 * (A₀ ^ 2 + 2) * (c ^ 4 + c ^ 2 * Real.log N) := by
        have hR2 : 0 ≤ R₀ ^ 2 := sq_nonneg _
        have h1 : 0 ≤ R₀ ^ 2 * c ^ 4 := by positivity
        have h2 : 0 ≤ R₀ ^ 2 * A₀ ^ 2 * c ^ 2 * Real.log N := by positivity
        nlinarith only [h1, h2]
  calc
    _ ≤ ∑ _m ∈ Icc 1 M, 16 * R₀ ^ 2 * (A₀ ^ 2 + 2) * (c ^ 4 + c ^ 2 * Real.log N) :=
      sum_le_sum hpt
    _ = 16 * R₀ ^ 2 * (A₀ ^ 2 + 2) * M * (c ^ 4 + c ^ 2 * Real.log N) := by
      rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]; ring
    _ ≤ (16 * R₀ ^ 2 * (A₀ ^ 2 + 2) + 1) * M * (c ^ 4 + c ^ 2 * Real.log N) := by
      have hextra : 0 ≤ (M : ℝ) * (c ^ 4 + c ^ 2 * Real.log N) := by positivity
      nlinarith only [hextra]

/-- Collective exterior downward bound across `1 ≤ m ≤ M`: `O(c^3 * (log N)^5)` with no factor `M`. -/
private theorem exists_sum_exteriorDownward_norm_sq_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM_int : 0 < ∫ u, φ u ^ 2) :
    ∃ C_ex : ℝ, 0 < C_ex ∧ ∀ M N : ℕ, 1 ≤ M → M * M ≤ N → 1 ≤ Real.log N →
      ∀ c : ℝ, 1 ≤ c → c / N ≤ 1 / 3 →
        (∑ m ∈ Icc 1 M,
          ‖(Real.sqrt (m.totient : ℝ))⁻¹ • normalizedExteriorDownwardVector φ c N m‖ ^ 2) ≤
          C_ex * c ^ 3 * (Real.log N) ^ 5 := by
  let S₀ := (Real.exp 1 + 2) * (Real.exp 1 + 1) ^ 2
  refine ⟨144 * S₀ + 1, by positivity, ?_⟩
  intro M N hM hMN hlogN c hc1 hw1
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hw : c / N ≤ 1 := hw1.trans (by norm_num)
  have hN1 : 1 ≤ N := (Nat.mul_pos hM hM).trans_le hMN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hLN0 : 0 < Real.log N := zero_lt_one.trans_le hlogN
  obtain ⟨hg, hgsupp, -⟩ := atomDilate_facts hφ hsupp (div_pos hc0 hN0)
  let g := atomDilate φ (c / N)
  have hG : 0 < ∫ u, g u ^ 2 := by
    dsimp only [g]
    rw [integral_atomDilate_sq (div_pos hc0 hN0)]
    exact mul_pos (div_pos hc0 hN0) hM_int
  have hgc : HasCompactSupport g := HasCompactSupport.intro isCompact_Icc hgsupp
  let S_row := (Icc 1 N).filter (fun n => N - linearPrimeStrip c ≤ n)
  let L_ext := Ioc N (exteriorPrimeCutoff c N)
  have hB_le : (linearPrimeStrip c : ℝ) ≤ (Real.exp 1 + 1) * c := linearPrimeStrip_le hc1
  have hS_card : (S_row.card : ℝ) ≤ (Real.exp 1 + 2) * c := by
    have hcontain : S_row ⊆ Icc (N - linearPrimeStrip c) N := fun n hn =>
      mem_Icc.mpr ⟨(mem_filter.mp hn).2, (mem_Icc.mp (mem_filter.mp hn).1).2⟩
    have hnat : S_row.card ≤ linearPrimeStrip c + 1 := by
      have h := card_le_card hcontain; rw [Nat.card_Icc] at h; omega
    have hR : (S_row.card : ℝ) ≤ (linearPrimeStrip c : ℝ) + 1 := by exact_mod_cast hnat
    nlinarith only [hR, hB_le, hc1]
  have hL_card : (L_ext.card : ℝ) ≤ (Real.exp 1 + 1) * c := by
    have hbound := (exteriorPrimeCutoff_bounds_small_width hc0 hN1 hw).2
    have hR : (L_ext.card : ℝ) ≤ linearPrimeStrip c := by
      dsimp only [L_ext]
      rw [Nat.card_Ioc]
      exact_mod_cast (show exteriorPrimeCutoff c N - N ≤ linearPrimeStrip c by omega)
    exact hR.trans hB_le
  -- Bound each `m`'s row sum by `(S_row.card * L_ext.card) * ∑_{ℓ ∈ L_ext} (H_m(ℓ)/√φ(m))^2 / ℓ`.
  have hfor_m : ∀ m ∈ Icc 1 M,
      ‖(Real.sqrt (m.totient : ℝ))⁻¹ • normalizedExteriorDownwardVector φ c N m‖ ^ 2 ≤
        ((Real.exp 1 + 2) * (Real.exp 1 + 1) * c ^ 2 / Real.log N) *
          ∑ ℓ ∈ L_ext, (horizonRamanujanMangoldt m N ℓ / Real.sqrt (m.totient : ℝ)) ^ 2 / ℓ := by
    intro m hm
    have hm1 := (mem_Icc.mp hm).1
    have hφm : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm1
    have hsm : 0 < Real.sqrt (m.totient : ℝ) := Real.sqrt_pos.mpr hφm
    have hrestrict : (∑ n ∈ Icc 1 N, regroupedExteriorDownwardPrimeRow g c N m n ^ 2) =
        ∑ n ∈ S_row, regroupedExteriorDownwardPrimeRow g c N m n ^ 2 := by
      symm
      refine sum_subset (filter_subset _ _) fun n hn hnS => ?_
      have hout : n < N - linearPrimeStrip c := lt_of_not_ge fun h => hnS (mem_filter.mpr ⟨hn, h⟩)
      rw [regroupedExteriorDownwardPrimeRow_eq_zero_small_width hc0 hn hgsupp hw hout m,
        zero_pow (by decide)]
    have hrow_n : ∀ n ∈ S_row,
        (m.totient : ℝ)⁻¹ * regroupedExteriorDownwardPrimeRow g c N m n ^ 2 ≤
          ((Real.exp 1 + 1) * c) *
            ∑ ℓ ∈ L_ext, (horizonRamanujanMangoldt m N ℓ / Real.sqrt (m.totient : ℝ)) ^ 2 / ℓ := by
      intro n _
      have heq_row : (Real.sqrt (m.totient : ℝ))⁻¹ * regroupedExteriorDownwardPrimeRow g c N m n =
          ∑ ℓ ∈ L_ext, (horizonRamanujanMangoldt m N ℓ / Real.sqrt (m.totient : ℝ) / Real.sqrt ℓ) *
            (bumpCorr g (Real.log ℓ - Real.log n) / (∫ u, g u ^ 2)) := by
        unfold regroupedExteriorDownwardPrimeRow
        rw [mul_sum]
        exact sum_congr rfl fun ℓ _ => by ring
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq L_ext
        (fun ℓ => (horizonRamanujanMangoldt m N ℓ / Real.sqrt (m.totient : ℝ) / Real.sqrt ℓ) *
          (bumpCorr g (Real.log ℓ - Real.log n) / (∫ u, g u ^ 2)))
        (fun _ => (1 : ℝ))
      simp only [mul_one, one_pow, sum_const, nsmul_eq_mul] at hcs
      have hterm_le : ∀ ℓ ∈ L_ext,
          ((horizonRamanujanMangoldt m N ℓ / Real.sqrt (m.totient : ℝ) / Real.sqrt ℓ) *
            (bumpCorr g (Real.log ℓ - Real.log n) / (∫ u, g u ^ 2))) ^ 2 ≤
            (horizonRamanujanMangoldt m N ℓ / Real.sqrt (m.totient : ℝ)) ^ 2 / ℓ := by
        intro ℓ _
        have hcorr : |bumpCorr g (Real.log ℓ - Real.log n) / (∫ u, g u ^ 2)| ≤ 1 := by
          rw [abs_div, abs_of_pos hG, div_le_one hG]
          exact abs_bumpCorr_le hg.continuous hgc _
        have hcorr_sq : (bumpCorr g (Real.log ℓ - Real.log n) / (∫ u, g u ^ 2)) ^ 2 ≤ 1 := by
          have h := mul_self_le_mul_self (abs_nonneg _) hcorr
          simpa only [← sq, sq_abs, one_pow] using h
        rw [mul_pow, div_pow, Real.sq_sqrt (Nat.cast_nonneg ℓ)]
        exact (mul_le_mul_of_nonneg_left hcorr_sq (by positivity)).trans_eq (mul_one _)
      have hlhs : (m.totient : ℝ)⁻¹ * regroupedExteriorDownwardPrimeRow g c N m n ^ 2 =
          ((Real.sqrt (m.totient : ℝ))⁻¹ * regroupedExteriorDownwardPrimeRow g c N m n) ^ 2 := by
        rw [mul_pow, inv_pow, Real.sq_sqrt hφm.le]
      rw [hlhs, heq_row]
      calc
        _ ≤ (∑ ℓ ∈ L_ext,
              ((horizonRamanujanMangoldt m N ℓ / Real.sqrt (m.totient : ℝ) / Real.sqrt ℓ) *
                (bumpCorr g (Real.log ℓ - Real.log n) / (∫ u, g u ^ 2))) ^ 2) * L_ext.card := hcs
        _ ≤ (∑ ℓ ∈ L_ext, (horizonRamanujanMangoldt m N ℓ / Real.sqrt (m.totient : ℝ)) ^ 2 / ℓ) *
              ((Real.exp 1 + 1) * c) :=
          mul_le_mul (sum_le_sum hterm_le) hL_card (Nat.cast_nonneg _)
            (sum_nonneg fun _ _ => by positivity)
        _ = _ := mul_comm _ _
    have hact_eq : (∑ n ∈ Icc 1 N, actualExteriorDownwardRow (atomDilate φ (c / N)) N m n ^ 2) =
        ∑ n ∈ Icc 1 N, regroupedExteriorDownwardPrimeRow g c N m n ^ 2 :=
      sum_congr rfl fun n hn =>
        congrArg (fun t : ℝ => t ^ 2) (downwardRamanujanRow_sub_interior_eq hc0 hn hgsupp m)
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt hφm.le,
      normalizedExteriorDownwardVector_norm_sq, hact_eq,
      hrestrict, mul_div_assoc, mul_sum]
    refine (div_le_div_of_nonneg_right (sum_le_sum hrow_n) hLN0.le).trans ?_
    rw [sum_const, nsmul_eq_mul]
    exact (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hS_card
        (mul_nonneg (by positivity) (sum_nonneg fun _ _ => by positivity))) hLN0.le).trans_eq
      (by ring)
  -- Packet sum over `m ∈ Icc 1 M` at each `ℓ ∈ L_ext`.
  have hlogM4 : (1 + Real.log M) ^ 4 ≤ 6 * (Real.log N) ^ 4 := by
    have hMR : (0 : ℝ) < M := by exact_mod_cast hM
    have hsq : (M : ℝ) ^ 2 ≤ N := by rw [sq]; exact_mod_cast hMN
    have h2 : 2 * Real.log M ≤ Real.log N := by
      have h := Real.log_le_log (sq_pos_of_pos hMR) hsq
      rwa [Real.log_pow, Nat.cast_ofNat] at h
    have hlogM : 1 + Real.log M ≤ (3 / 2) * Real.log N := by linarith only [h2, hlogN]
    calc
      (1 + Real.log M) ^ 4 ≤ ((3 / 2) * Real.log N) ^ 4 :=
        pow_le_pow_left₀ (by linarith [Real.log_natCast_nonneg M]) hlogM 4
      _ = (81 / 16) * (Real.log N) ^ 4 := by ring
      _ ≤ 6 * (Real.log N) ^ 4 := mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg hLN0.le 4)
  have hfor_ℓ : ∀ ℓ ∈ L_ext,
      (∑ m ∈ Icc 1 M,
        (horizonRamanujanMangoldt m N ℓ / Real.sqrt (m.totient : ℝ)) ^ 2 / ℓ) ≤
        144 * (Real.log N) ^ 6 := by
    intro ℓ hℓ
    obtain ⟨hℓ_gt, hℓ_hi⟩ := mem_Ioc.mp hℓ
    have hℓ0 : 0 < ℓ := (Nat.zero_le N).trans_lt hℓ_gt
    have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓ0
    let D_ℓ := ℓ.divisors.filter (fun d => ℓ / d ≤ N)
    have hsum_Λ : (∑ d ∈ D_ℓ, (Λ d : ℝ)) ≤ Real.log ℓ :=
      (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => vonMangoldt_nonneg).trans_eq
        ArithmeticFunction.vonMangoldt_sum
    have hcs_m : ∀ m ∈ Icc 1 M,
        (horizonRamanujanMangoldt m N ℓ / Real.sqrt (m.totient : ℝ)) ^ 2 ≤
          Real.log ℓ * ∑ d ∈ D_ℓ, (Λ d : ℝ) * normalizedRamanujanMode m (ℓ / d) ^ 2 := by
      intro m hm
      have hm1 := (mem_Icc.mp hm).1
      have heq_H : horizonRamanujanMangoldt m N ℓ / Real.sqrt (m.totient : ℝ) =
          ∑ d ∈ D_ℓ, Real.sqrt (Λ d) * (Real.sqrt (Λ d) * normalizedRamanujanMode m (ℓ / d)) := by
        unfold horizonRamanujanMangoldt
        rw [sum_div]
        refine sum_congr rfl fun d _ => ?_
        rw [normalizedRamanujanMode_eq_coefficient hm1, ← mul_assoc,
          Real.mul_self_sqrt vonMangoldt_nonneg]
        ring
      rw [heq_H]
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq D_ℓ
        (fun d => Real.sqrt (Λ d))
        (fun d => Real.sqrt (Λ d) * normalizedRamanujanMode m (ℓ / d))
      refine hcs.trans ?_
      have h1 : (∑ d ∈ D_ℓ, Real.sqrt (Λ d) ^ 2) = ∑ d ∈ D_ℓ, (Λ d : ℝ) :=
        sum_congr rfl fun d _ => Real.sq_sqrt vonMangoldt_nonneg
      have h2 : (∑ d ∈ D_ℓ, (Real.sqrt (Λ d) * normalizedRamanujanMode m (ℓ / d)) ^ 2) =
          ∑ d ∈ D_ℓ, (Λ d : ℝ) * normalizedRamanujanMode m (ℓ / d) ^ 2 :=
        sum_congr rfl fun d _ => by rw [mul_pow, Real.sq_sqrt vonMangoldt_nonneg]
      rw [h1, h2]
      exact mul_le_mul_of_nonneg_right hsum_Λ
        (sum_nonneg fun d _ => mul_nonneg vonMangoldt_nonneg (sq_nonneg _))
    -- Bound `log ℓ ≤ 3 * log N`: `ℓ ≤ N + linearPrimeStrip c ≤ 5 * N` since `c ≤ N / 3`.
    have hlogℓ_sq : (Real.log ℓ) ^ 2 ≤ 24 * (Real.log N) ^ 2 := by
      have hcut := (exteriorPrimeCutoff_bounds_small_width hc0 hN1 hw).2
      have hℓ_bound : (ℓ : ℝ) ≤ 5 * N := by
        have h1 : (ℓ : ℝ) ≤ (N : ℝ) + linearPrimeStrip c := by exact_mod_cast (hℓ_hi.trans hcut)
        have hc_le : c ≤ (N : ℝ) / 3 := (div_le_iff₀ hN0).mp hw1 |>.trans_eq (by ring)
        have he1 : Real.exp 1 ≤ 3 := Real.exp_one_lt_d9.le.trans (by norm_num)
        have hB4 : (linearPrimeStrip c : ℝ) ≤ 4 * c :=
          hB_le.trans (mul_le_mul_of_nonneg_right (by linarith only [he1]) hc0.le)
        linarith only [h1, hB4, hc_le, hN0]
      have hlog5 : Real.log 5 ≤ 4 := by
        linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5)]
      have hlogℓ : Real.log ℓ ≤ 5 * Real.log N := by
        have h := Real.log_le_log hℓR hℓ_bound
        rw [Real.log_mul (by norm_num) hN0.ne'] at h
        linarith only [h, hlog5, hlogN]
      -- Note `5^2 = 25`: refine `hlog5` using `5 = 2 * (5 / 2)` so `log 5 ≤ 1 + 3/2 = 5/2 < 3`!
      have hlog2 : Real.log 2 ≤ 1 := by
        linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
      have hlog25 : Real.log (5 / 2) ≤ 3 / 2 := by
        linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5 / 2)]
      have hlog5_sharp : Real.log 5 ≤ 3 := by
        have h5 : (5 : ℝ) = 2 * (5 / 2) := by norm_num
        rw [h5, Real.log_mul (by norm_num) (by norm_num)]
        linarith only [hlog2, hlog25]
      have hlogℓ4 : Real.log ℓ ≤ 4 * Real.log N := by
        have h := Real.log_le_log hℓR hℓ_bound
        rw [Real.log_mul (by norm_num) hN0.ne'] at h
        linarith only [h, hlog5_sharp, hlogN]
      exact (pow_le_pow_left₀ (Real.log_natCast_nonneg ℓ) hlogℓ4 2).trans
        (by nlinarith only [sq_nonneg (Real.log N)])
    have hinner_m : (∑ m ∈ Icc 1 M, ∑ d ∈ D_ℓ, (Λ d : ℝ) * normalizedRamanujanMode m (ℓ / d) ^ 2) ≤
        Real.log ℓ * ℓ * (1 + Real.log M) ^ 4 := by
      rw [sum_comm]
      have hfor_d : ∀ d ∈ D_ℓ,
          (∑ m ∈ Icc 1 M, (Λ d : ℝ) * normalizedRamanujanMode m (ℓ / d) ^ 2) ≤
            (Λ d : ℝ) * ((ℓ : ℝ) * (1 + Real.log M) ^ 4) := by
        intro d hd
        have hd_mem := (mem_filter.mp hd).1
        have hd0 : 0 < d := Nat.pos_of_mem_divisors hd_mem
        have hq1 : 1 ≤ ℓ / d := Nat.div_pos (Nat.divisor_le hd_mem) hd0
        have hq_le : ((ℓ / d : ℕ) : ℝ) ≤ ℓ := by exact_mod_cast Nat.div_le_self ℓ d
        rw [← mul_sum]
        exact mul_le_mul_of_nonneg_left
          ((sum_normalizedRamanujanMode_sq_le M hq1).trans
            (mul_le_mul_of_nonneg_right hq_le (by positivity)))
          vonMangoldt_nonneg
      calc
        _ ≤ ∑ d ∈ D_ℓ, (Λ d : ℝ) * ((ℓ : ℝ) * (1 + Real.log M) ^ 4) := sum_le_sum hfor_d
        _ = (∑ d ∈ D_ℓ, (Λ d : ℝ)) * ((ℓ : ℝ) * (1 + Real.log M) ^ 4) := (sum_mul _ _ _).symm
        _ ≤ Real.log ℓ * ((ℓ : ℝ) * (1 + Real.log M) ^ 4) :=
          mul_le_mul_of_nonneg_right hsum_Λ (by positivity)
        _ = Real.log ℓ * ℓ * (1 + Real.log M) ^ 4 := by ring
    rw [← sum_div]
    calc
      (∑ m ∈ Icc 1 M, (horizonRamanujanMangoldt m N ℓ / Real.sqrt (m.totient : ℝ)) ^ 2) / ℓ ≤
          (Real.log ℓ * (Real.log ℓ * ℓ * (1 + Real.log M) ^ 4)) / ℓ := by
        refine div_le_div_of_nonneg_right ?_ hℓR.le
        calc
          _ ≤ ∑ m ∈ Icc 1 M, Real.log ℓ *
                ∑ d ∈ D_ℓ, (Λ d : ℝ) * normalizedRamanujanMode m (ℓ / d) ^ 2 :=
            sum_le_sum hcs_m
          _ = Real.log ℓ * ∑ m ∈ Icc 1 M,
                ∑ d ∈ D_ℓ, (Λ d : ℝ) * normalizedRamanujanMode m (ℓ / d) ^ 2 := (mul_sum _ _ _).symm
          _ ≤ Real.log ℓ * (Real.log ℓ * ℓ * (1 + Real.log M) ^ 4) :=
            mul_le_mul_of_nonneg_left hinner_m (Real.log_natCast_nonneg ℓ)
      _ = (Real.log ℓ) ^ 2 * (1 + Real.log M) ^ 4 := by field_simp [hℓR.ne']
      _ ≤ (24 * (Real.log N) ^ 2) * (6 * (Real.log N) ^ 4) :=
        mul_le_mul hlogℓ_sq hlogM4 (by positivity) (by positivity)
      _ = 144 * (Real.log N) ^ 6 := by ring
  calc
    (∑ m ∈ Icc 1 M,
        ‖(Real.sqrt (m.totient : ℝ))⁻¹ • normalizedExteriorDownwardVector φ c N m‖ ^ 2) ≤
        ∑ m ∈ Icc 1 M, ((Real.exp 1 + 2) * (Real.exp 1 + 1) * c ^ 2 / Real.log N) *
          ∑ ℓ ∈ L_ext, (horizonRamanujanMangoldt m N ℓ / Real.sqrt (m.totient : ℝ)) ^ 2 / ℓ :=
      sum_le_sum hfor_m
    _ = ((Real.exp 1 + 2) * (Real.exp 1 + 1) * c ^ 2 / Real.log N) *
          ∑ ℓ ∈ L_ext, ∑ m ∈ Icc 1 M,
            (horizonRamanujanMangoldt m N ℓ / Real.sqrt (m.totient : ℝ)) ^ 2 / ℓ := by
      rw [← mul_sum, sum_comm]
    _ ≤ ((Real.exp 1 + 2) * (Real.exp 1 + 1) * c ^ 2 / Real.log N) *
          (L_ext.card * (144 * (Real.log N) ^ 6)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact (sum_le_sum hfor_ℓ).trans_eq (by rw [sum_const, nsmul_eq_mul])
    _ ≤ ((Real.exp 1 + 2) * (Real.exp 1 + 1) * c ^ 2 / Real.log N) *
          (((Real.exp 1 + 1) * c) * (144 * (Real.log N) ^ 6)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hL_card (by positivity)) (by positivity)
    _ = 144 * S₀ * c ^ 3 * (Real.log N) ^ 5 := by
      dsimp only [S₀]; field_simp [hLN0.ne']
    _ ≤ (144 * S₀ + 1) * c ^ 3 * (Real.log N) ^ 5 := by
      have hextra : 0 ≤ c ^ 3 * (Real.log N) ^ 5 := by positivity
      nlinarith only [hextra]

/-- Collective near-center bound across `1 ≤ m ≤ M`: `O(M * c^4)` via `sum_near_div_sqrt_sq_le_profile`. -/
private theorem exists_sum_nearCenterVector_norm_sq_le (φ : ℝ → ℝ) :
    ∃ C_nc : ℝ, 0 < C_nc ∧ ∀ M N : ℕ, 1 ≤ M → M * M ≤ N → 1 ≤ Real.log N →
      ∀ c : ℝ, 0 < c → 2 * c ≤ N →
        (∑ m ∈ Icc 1 M, ‖nearCenterVector φ c N m‖ ^ 2) ≤ C_nc * M * c ^ 4 := by
  let q := |completeWeilPoleShift φ 1| * (1 + Real.exp (1 / 2))
  let R₀ := 2 * Real.exp 2
  refine ⟨8 * R₀ ^ 2 * q ^ 2 + 1, by positivity, ?_⟩
  intro M N hM hMN hlogN c hc0 hcN2
  have hN1 : 1 ≤ N := (Nat.mul_pos hM hM).trans_le hMN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hLN0 : 0 < Real.log N := zero_lt_one.trans_le hlogN
  have hw : c / N ≤ 1 := (div_le_one hN0).mpr (by linarith only [hcN2, hc0])
  have hMN_le : M ≤ N := (Nat.le_mul_self M).trans hMN
  have hR_eq : linearNearRowRadius c = R₀ * c := by unfold linearNearRowRadius; dsimp only [R₀]; ring
  have hα : |completeWeilPoleShift φ c| = c * |completeWeilPoleShift φ 1| := by
    have h1 : completeWeilPoleShift φ c = c * completeWeilPoleShift φ 1 := by
      unfold completeWeilPoleShift; ring
    rw [h1, abs_mul, abs_of_pos hc0]
  -- Pointwise entry bound `|...| ≤ q * c * |c̃_m(j)|` on `nearRowIndices c N n`.
  have hentry : ∀ m n : ℕ, n ∈ Icc 1 N → ∀ j ∈ nearRowIndices c N n,
      |completeWeilPoleShift φ c / N * archimedeanCenterKernel n j * normalizedRamanujanMode m j| ≤
        q * c * |normalizedRamanujanMode m j| := by
    intro m n hn j hj
    obtain ⟨hjN, hjn, hlog⟩ := mem_filter.mp hj
    have hn1 := (mem_Icc.mp hn).1
    have hj1 := (mem_Icc.mp hjN).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
    let y := |Real.log j - Real.log n|
    have hkernel : archimedeanCenterKernel n j = _root_.RHTower.archLevyDensity y := by
      unfold archimedeanCenterKernel
      rw [if_neg (by push Not; exact ⟨Ne.symm hjn, by omega, by omega⟩)]
    have hgap : 1 / (N : ℝ) ≤ y := by
      have h := gap_div_le_abs_log_div hj1 hn1 hjn
      rw [Real.log_div hj0.ne' hn0.ne'] at h
      have hd : (1 : ℝ) ≤ |(j : ℝ) - n| := by
        rcases lt_or_gt_of_ne hjn with h' | h'
        · have hR : (j : ℝ) + 1 ≤ n := by exact_mod_cast (Nat.succ_le_iff.mpr h')
          rw [abs_of_neg (by linarith only [hR])]; linarith only [hR]
        · have hR : (n : ℝ) + 1 ≤ j := by exact_mod_cast (Nat.succ_le_iff.mpr h')
          rw [abs_of_pos (by linarith only [hR])]; linarith only [hR]
      have hmax0 : 0 < max (j : ℝ) n := hj0.trans_le (le_max_left _ _)
      have hmaxN : max (j : ℝ) n ≤ N :=
        max_le (by exact_mod_cast (mem_Icc.mp hjN).2) (by exact_mod_cast (mem_Icc.mp hn).2)
      calc
        1 / (N : ℝ) ≤ 1 / max (j : ℝ) n := one_div_le_one_div_of_le hmax0 hmaxN
        _ ≤ |(j : ℝ) - n| / max (j : ℝ) n := div_le_div_of_nonneg_right hd hmax0.le
        _ ≤ y := h
    have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hgap
    have hy1 : y ≤ 1 := hlog.trans ((div_le_one hN0).mpr hcN2)
    have hD0 : 0 < _root_.RHTower.archLevyDensity y := RHTower.archLevyDensity_pos hy0
    have hD : _root_.RHTower.archLevyDensity y ≤ N / 2 + Real.exp (1 / 2) / 4 := by
      refine (archLevyDensity_le_inv_two_mul_add hy0 hy1).trans ?_
      have : 1 / (2 * y) ≤ N / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        have := (div_le_iff₀ hN0).mp hgap
        linarith
      linarith
    have hcoef : |completeWeilPoleShift φ c| / N * _root_.RHTower.archLevyDensity y ≤ q * c := by
      rw [hα, div_mul_eq_mul_div, div_le_iff₀ hN0]
      dsimp only [q]
      have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN1
      have he0 := Real.exp_pos (1 / 2)
      have ha0 := abs_nonneg (completeWeilPoleShift φ 1)
      have hD_N : _root_.RHTower.archLevyDensity y ≤ N + Real.exp (1 / 2) * N := by
        have heN : Real.exp (1 / 2) ≤ Real.exp (1 / 2) * N :=
          le_mul_of_one_le_right he0.le hN1R
        linarith only [hD, hN1R, he0, heN]
      exact (mul_le_mul_of_nonneg_left hD_N (mul_nonneg hc0.le ha0)).trans_eq (by ring)
    rw [hkernel, abs_mul, abs_mul, abs_div, abs_of_pos hN0, abs_of_pos hD0]
    exact mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)
  have hpt : ∀ m ∈ Icc 1 M, ‖nearCenterVector φ c N m‖ ^ 2 ≤ 8 * R₀ ^ 2 * q ^ 2 * c ^ 4 := by
    intro m hm
    obtain ⟨hm1, hmM⟩ := mem_Icc.mp hm
    rw [nearCenterVector_norm_sq]
    have hnear := sum_near_div_sqrt_sq_le_profile hc0 hN1 hw
      (fun n j => completeWeilPoleShift φ c / N * archimedeanCenterKernel n j *
        normalizedRamanujanMode m j)
      (fun j => q * c * |normalizedRamanujanMode m j|)
      (fun j _ => by dsimp only [q]; positivity)
      (fun n hn j hj => hentry m n hn j hj)
    have hsum_G2 : (∑ j ∈ Icc 1 N, (q * c * |normalizedRamanujanMode m j|) ^ 2) ≤
        2 * q ^ 2 * c ^ 2 * N := by
      have heq : (∑ j ∈ Icc 1 N, (q * c * |normalizedRamanujanMode m j|) ^ 2) =
          q ^ 2 * c ^ 2 * ∑ j ∈ Icc 1 N, normalizedRamanujanMode m j ^ 2 := by
        rw [mul_sum]
        exact sum_congr rfl fun j _ => by rw [mul_pow, mul_pow, sq_abs]
      rw [heq]
      exact (mul_le_mul_of_nonneg_left (sum_Icc_normalizedRamanujanMode_sq_le hm1 (hmM.trans hMN_le))
        (by positivity)).trans_eq (by ring)
    have hc4_div : c ^ 4 / Real.log N ≤ c ^ 4 := div_le_self (by positivity) hlogN
    calc
      _ ≤ (4 * linearNearRowRadius c ^ 2 / N * (2 * q ^ 2 * c ^ 2 * N)) / Real.log N :=
        div_le_div_of_nonneg_right
          (hnear.trans (mul_le_mul_of_nonneg_left hsum_G2 (by positivity))) hLN0.le
      _ = 8 * R₀ ^ 2 * q ^ 2 * (c ^ 4 / Real.log N) := by
        rw [hR_eq]; field_simp [hN0.ne']; ring
      _ ≤ 8 * R₀ ^ 2 * q ^ 2 * c ^ 4 :=
        mul_le_mul_of_nonneg_left hc4_div (by positivity)
  calc
    _ ≤ ∑ _m ∈ Icc 1 M, 8 * R₀ ^ 2 * q ^ 2 * c ^ 4 := sum_le_sum hpt
    _ = 8 * R₀ ^ 2 * q ^ 2 * M * c ^ 4 := by
      rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]; ring
    _ ≤ (8 * R₀ ^ 2 * q ^ 2 + 1) * M * c ^ 4 := by
      have hextra : 0 ≤ (M : ℝ) * c ^ 4 := by positivity
      nlinarith only [hextra]

/-- Uniform linear overlap bound on `shellCorrection`, independent of the conductor `m`. -/
theorem abs_shellCorrection_le_linear {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM_int : 0 < ∫ u, φ u ^ 2) {m : ℕ} (hm : 0 < m) {c : ℝ} (hc : 0 < c) :
    |shellCorrection φ c m| ≤ 2 * (Real.log 4 + 4) * c := by
  have h := abs_shellCorrectionOfShift_mean_le_linear hm hφ hsupp hM_int 0 id hc
  have hφm : 0 < (m.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hm
  rw [ramanujanLagCoefficient_of_dvd (dvd_zero m), abs_mul, abs_of_pos hφm] at h
  change (m.totient : ℝ) * |shellCorrection φ c m| ≤ _ at h
  have hscaled : (m.totient : ℝ) * |shellCorrection φ c m| ≤
      (m.totient : ℝ) * (2 * (Real.log 4 + 4) * c) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h
  by_contra hbad
  exact (not_lt_of_ge hscaled) (mul_lt_mul_of_pos_left (lt_of_not_ge hbad) hφm)

/-- Collective upward prime defect bound across `1 ≤ m ≤ M`: `O(M * c^2)`. -/
private theorem exists_sum_upwardPrimeDefect_norm_sq_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM_int : 0 < ∫ u, φ u ^ 2) :
    ∃ C_u : ℝ, 0 < C_u ∧ ∀ M N : ℕ, 1 ≤ M → M * M ≤ N → 4 * Real.exp 7 ≤ Real.log N →
      ∀ c : ℝ, 0 < c → c ≤ N →
        (∑ m ∈ Icc 1 M,
          ‖upwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N) -
            shellCorrection φ c m • normalizedRamanujanHorizonVector m N‖ ^ 2) ≤
          C_u * M * c ^ 2 := by
  let L₄ := Real.log 4 + 4
  have hL₄ : 0 < L₄ := by
    dsimp only [L₄]
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    linarith
  refine ⟨32 * L₄ * Real.exp 5 + 48 * L₄ ^ 2 + 1, by positivity, ?_⟩
  intro M N hM hMN hL c hc0 hcN
  have hN1 : 1 ≤ N := (Nat.mul_pos hM hM).trans_le hMN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hlogN : 1 ≤ Real.log N := by linarith [Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 7)]
  have hLN0 : 0 < Real.log N := zero_lt_one.trans_le hlogN
  have hMN_le : M ≤ N := (Nat.le_mul_self M).trans hMN
  let w := c / N
  have hw0 : 0 < w := div_pos hc0 hN0
  have hw1 : w ≤ 1 := (div_le_one hN0).mpr hcN
  obtain ⟨hg, hgsupp, -⟩ := atomDilate_facts hφ hsupp hw0
  let g := atomDilate φ w
  have hG : 0 < ∫ u, g u ^ 2 := by
    dsimp only [g]
    rw [integral_atomDilate_sq hw0]
    exact mul_pos hw0 hM_int
  have hgc : HasCompactSupport g := HasCompactSupport.intro isCompact_Icc hgsupp
  -- Exponential width bounds for `0 < w ≤ 1`.
  have hew : Real.exp w - 1 ≤ w * Real.exp 1 := by
    calc
      Real.exp w - 1 ≤ w * Real.exp w := exp_sub_one_le_mul_exp
      _ ≤ w * Real.exp 1 := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hw1) hw0.le
  have hew_nonneg : 0 ≤ Real.exp w - 1 := by linarith [Real.add_one_le_exp w]
  let K_lag := SpacingScaleHarmonicAnalysis.lagRange (Real.log N + w + 1)
  let K_mat : ℕ → ℕ → ℝ := fun n j =>
    ∑ k ∈ range K_lag, _root_.RHTower.vonMangoldtAtom k *
      ((if j = k * n then 0 else bumpCorr g (Real.log k - (Real.log j - Real.log n))) /
        (∫ u, g u ^ 2))
  let U_mat : ℕ → ℕ → ℝ := fun n j =>
    ∑ k ∈ range K_lag, _root_.RHTower.vonMangoldtAtom k * upInd w k n j
  have hU_nonneg : ∀ n ∈ Icc 1 N, ∀ j ∈ Icc 1 N, 0 ≤ U_mat n j :=
    fun _ _ _ _ => sum_nonneg fun k _ =>
      mul_nonneg (vonMangoldtAtom_nonneg' k) (upInd_nonneg w k _ _)
  have hKU : ∀ n ∈ Icc 1 N, ∀ j ∈ Icc 1 N, |K_mat n j| ≤ U_mat n j := by
    intro n _ j _
    dsimp only [K_mat, U_mat]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _ => ?_)
    rw [abs_mul, abs_of_nonneg (vonMangoldtAtom_nonneg' k)]
    refine mul_le_mul_of_nonneg_left ?_ (vonMangoldtAtom_nonneg' k)
    rw [abs_div, abs_of_pos hG, div_le_iff₀ hG]
    simpa only [mul_comm] using abs_nonRatio_term_le hg.continuous hgc hgsupp k n j
  let R_up := 2 * L₄ * Real.exp 3 * c
  have hR_up0 : 0 ≤ R_up := by dsimp only [R_up]; positivity
  have hrow_U : ∀ n ∈ Icc 1 N, (∑ j ∈ Icc 1 N, U_mat n j * (1 / Real.sqrt j)) ≤
      R_up / Real.sqrt n := by
    intro n hn
    have hn1 := (mem_Icc.mp hn).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
    have heq : (∑ j ∈ Icc 1 N, U_mat n j * (1 / Real.sqrt j)) =
        (∑ k ∈ range K_lag, _root_.RHTower.vonMangoldtAtom k *
          ∑ j ∈ Icc 1 N, Real.sqrt ((n : ℝ) / j) * upInd w k n j) / Real.sqrt n := by
      dsimp only [U_mat]
      simp_rw [sum_mul]
      rw [sum_comm, sum_div]
      refine sum_congr rfl fun k _ => ?_
      simp_rw [mul_assoc]
      rw [← mul_sum, mul_div_assoc]
      congr 1
      rw [sum_div]
      refine sum_congr rfl fun j hj => ?_
      have hsj : Real.sqrt j ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast (mem_Icc.mp hj).1)).ne'
      rw [Real.sqrt_div hn0.le]
      field_simp [hsn.ne', hsj]
    rw [heq]
    refine div_le_div_of_nonneg_right ?_ hsn.le
    have hup := up_row_le hw0.le hn1 K_lag
    have hexp32 : Real.exp (3 * w / 2) ≤ Real.exp 2 :=
      Real.exp_le_exp.mpr (by linarith only [hw1])
    calc
      _ ≤ 2 * L₄ * Real.exp (3 * w / 2) * (Real.exp w - 1) * N := hup
      _ ≤ 2 * L₄ * Real.exp 2 * (w * Real.exp 1) * N := by
        refine mul_le_mul_of_nonneg_right ?_ hN0.le
        exact mul_le_mul (mul_le_mul_of_nonneg_left hexp32 (by positivity)) hew hew_nonneg
          (by positivity)
      _ = R_up := by
        dsimp only [R_up, w]
        rw [show Real.exp 3 = Real.exp 2 * Real.exp 1 by rw [← Real.exp_add]; norm_num]
        field_simp [hN0.ne']; ring
  have hcol_U : ∀ j ∈ Icc 1 N,
      (∑ n ∈ Icc 1 N, U_mat n j * ((R_up / Real.sqrt n) / (1 / Real.sqrt j))) ≤
        4 * R_up * Real.exp 2 * w * Real.log N * j := by
    intro j hj
    obtain ⟨hj1, hjN⟩ := mem_Icc.mp hj
    have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
    have hsj : 0 < Real.sqrt j := Real.sqrt_pos.mpr hj0
    have heq : (∑ n ∈ Icc 1 N, U_mat n j * ((R_up / Real.sqrt n) / (1 / Real.sqrt j))) =
        R_up * ∑ k ∈ range K_lag, _root_.RHTower.vonMangoldtAtom k *
          ∑ n ∈ Icc 1 N, Real.sqrt ((j : ℝ) / n) * upInd w k n j := by
      dsimp only [U_mat]
      simp_rw [sum_mul]
      rw [sum_comm, mul_sum]
      refine sum_congr rfl fun k _ => ?_
      simp_rw [mul_assoc]
      rw [← mul_sum, mul_left_comm R_up]
      congr 1
      rw [mul_sum]
      refine sum_congr rfl fun n hn => ?_
      have hsn : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast (mem_Icc.mp hn).1)).ne'
      rw [Real.sqrt_div hj0.le]
      field_simp [hsn, hsj.ne']
    rw [heq]
    have hdown := down_row_le hw0.le hj1 K_lag
    have hexp12 : Real.exp (w / 2) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by linarith only [hw1])
    have hlogj : Real.log j + w ≤ 2 * Real.log N := by
      have h1 : Real.log j ≤ Real.log N := Real.log_le_log hj0 (by exact_mod_cast hjN)
      linarith only [h1, hw1, hlogN]
    refine mul_le_mul_of_nonneg_left (hdown.trans ?_) hR_up0 |>.trans_eq (by ring)
    calc
      2 * Real.exp (w / 2) * j * (Real.exp w - 1) * (Real.log j + w) ≤
          2 * Real.exp 1 * j * (w * Real.exp 1) * (2 * Real.log N) := by
        refine mul_le_mul ?_ hlogj (by linarith [Real.log_natCast_nonneg j]) (by positivity)
        refine mul_le_mul ?_ hew hew_nonneg (by positivity)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp12 zero_le_two) hj0.le
      _ = 4 * Real.exp 2 * w * Real.log N * j := by
        rw [show Real.exp 2 = Real.exp 1 * Real.exp 1 by rw [← Real.exp_add]; norm_num]; ring
  have hpt : ∀ m ∈ Icc 1 M,
      ‖upwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N) -
        shellCorrection φ c m • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
        (32 * L₄ * Real.exp 5 + 48 * L₄ ^ 2) * c ^ 2 := by
    intro m hm
    obtain ⟨hm1, hmM⟩ := mem_Icc.mp hm
    have hup_norm : ‖upwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N)‖ ^ 2 ≤
        16 * L₄ * Real.exp 5 * c ^ 2 := by
      have hrow_eq : ∀ n ∈ Icc 1 N,
          (upwardPrimeRow g N (primeHorizonExtension (normalizedRamanujanHorizonVector m N)) n /
            (∫ u, g u ^ 2)) ^ 2 =
          (∑ j ∈ Icc 1 N, K_mat n j * (normalizedRamanujanMode m j / Real.sqrt j)) ^ 2 /
            Real.log N := by
        intro n hn
        have heq1 : upwardPrimeRow g N
            (primeHorizonExtension (normalizedRamanujanHorizonVector m N)) n / (∫ u, g u ^ 2) =
            (Real.sqrt (Real.log N))⁻¹ *
              ∑ j ∈ Icc 1 N, K_mat n j * (normalizedRamanujanMode m j / Real.sqrt j) := by
          rw [upwardPrimeRow_eq_sum hgsupp hw0.le hn, sum_div]
          dsimp only [K_mat]
          simp_rw [sum_mul]
          rw [sum_comm (s := Icc 1 N) (t := range K_lag), mul_sum]
          refine sum_congr rfl fun k _ => ?_
          rw [mul_sum, mul_sum, sum_div]
          refine sum_congr rfl fun j hj => ?_
          rw [primeHorizonExtension, dif_pos hj]
          change (_root_.RHTower.vonMangoldtAtom k *
              (((Real.sqrt (Real.log N))⁻¹ * (normalizedRamanujanMode m j / Real.sqrt j)) *
                if j = k * n then 0 else bumpCorr g (Real.log k - (Real.log j - Real.log n)))) /
              (∫ u, g u ^ 2) = _
          ring
        rw [heq1, mul_pow, inv_pow, Real.sq_sqrt hLN0.le, div_eq_inv_mul]
      have hvec_sq : ‖upwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N)‖ ^ 2 =
          (∑ n ∈ Icc 1 N,
            (∑ j ∈ Icc 1 N, K_mat n j * (normalizedRamanujanMode m j / Real.sqrt j)) ^ 2) /
            Real.log N := by
        rw [EuclideanSpace.real_norm_sq_eq]
        change (∑ n : PrimeHorizonIndex N,
          (upwardPrimeRow g N (primeHorizonExtension (normalizedRamanujanHorizonVector m N)) n /
            (∫ u, g u ^ 2)) ^ 2) = _
        refine (sum_coe_sort (Icc 1 N)
          (fun n => (upwardPrimeRow g N
            (primeHorizonExtension (normalizedRamanujanHorizonVector m N)) n /
            (∫ u, g u ^ 2)) ^ 2)).trans ?_
        rw [sum_congr rfl hrow_eq, ← sum_div]
      have hschur := sum_sq_abs_majorized_kernel_le (N := N) K_mat U_mat
        (fun j => normalizedRamanujanMode m j / Real.sqrt j)
        (fun j => 1 / Real.sqrt j)
        (fun n => R_up / Real.sqrt n)
        (fun j => 4 * R_up * Real.exp 2 * w * Real.log N * j)
        hU_nonneg hKU
        (fun j hj => one_div_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast (mem_Icc.mp hj).1)))
        hrow_U hcol_U
      have hmode_sum : (∑ j ∈ Icc 1 N,
          (4 * R_up * Real.exp 2 * w * Real.log N * j) *
            (normalizedRamanujanMode m j / Real.sqrt j) ^ 2) ≤
          8 * R_up * Real.exp 2 * c * Real.log N := by
        have heq : (∑ j ∈ Icc 1 N,
            (4 * R_up * Real.exp 2 * w * Real.log N * j) *
              (normalizedRamanujanMode m j / Real.sqrt j) ^ 2) =
            (4 * R_up * Real.exp 2 * w * Real.log N) *
              ∑ j ∈ Icc 1 N, normalizedRamanujanMode m j ^ 2 := by
          rw [mul_sum]
          refine sum_congr rfl fun j hj => ?_
          have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hj).1
          rw [div_pow, Real.sq_sqrt hj0.le]
          field_simp [hj0.ne']
        rw [heq]
        calc
          _ ≤ (4 * R_up * Real.exp 2 * w * Real.log N) * (2 * N) :=
            mul_le_mul_of_nonneg_left
              (sum_Icc_normalizedRamanujanMode_sq_le hm1 (hmM.trans hMN_le)) (by positivity)
          _ = 8 * R_up * Real.exp 2 * c * Real.log N := by dsimp only [w]; field_simp [hN0.ne']; ring
      rw [hvec_sq]
      calc
        _ ≤ (8 * R_up * Real.exp 2 * c * Real.log N) / Real.log N :=
          div_le_div_of_nonneg_right (hschur.trans hmode_sum) hLN0.le
        _ = 16 * L₄ * (Real.exp 3 * Real.exp 2) * c ^ 2 := by
          dsimp only [R_up]; field_simp [hLN0.ne']; ring
        _ = 16 * L₄ * Real.exp 5 * c ^ 2 := by
          rw [← Real.exp_add]; norm_num
    have hshell_norm : ‖shellCorrection φ c m • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
        24 * L₄ ^ 2 * c ^ 2 := by
      have hsc := abs_shellCorrection_le_linear hφ hsupp hM_int hm1 hc0
      change |shellCorrection φ c m| ≤ 2 * L₄ * c at hsc
      have hsc_sq : shellCorrection φ c m ^ 2 ≤ 4 * L₄ ^ 2 * c ^ 2 := by
        have h := mul_self_le_mul_self (abs_nonneg _) hsc
        rw [← sq, sq_abs, ← sq] at h
        exact h.trans_eq (by ring)
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      exact (mul_le_mul hsc_sq (normalizedRamanujanHorizonVector_norm_sq_le_six hm hMN hL)
        (sq_nonneg _) (by positivity)).trans_eq (by ring)
    have hsub := norm_sub_sq_le_two
      (upwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N))
      (shellCorrection φ c m • normalizedRamanujanHorizonVector m N)
    linarith only [hsub, hup_norm, hshell_norm]
  calc
    _ ≤ ∑ _m ∈ Icc 1 M, (32 * L₄ * Real.exp 5 + 48 * L₄ ^ 2) * c ^ 2 := sum_le_sum hpt
    _ = (32 * L₄ * Real.exp 5 + 48 * L₄ ^ 2) * M * c ^ 2 := by
      rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]; ring
    _ ≤ (32 * L₄ * Real.exp 5 + 48 * L₄ ^ 2 + 1) * M * c ^ 2 := by
      have hextra : 0 ≤ (M : ℝ) * c ^ 2 := by positivity
      nlinarith only [hextra]

/-! ## Section 3: Complete Collective Residual Theorem and Question Q3 Resolution -/

/-- Collective eight-piece complete-Weil residual bound across `1 ≤ m ≤ M` (`M * M ≤ N`):
every block of `W_{N, c} v_m - E_m(c) v_m` is bounded simultaneously in `L²`. -/
theorem exists_completeWeil_collective_residual_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM_int : 0 < ∫ u, φ u ^ 2) :
    ∃ K_φ : ℝ, 0 < K_φ ∧ ∀ M N : ℕ, 1 ≤ M → M * M ≤ N → 4 * Real.exp 7 ≤ Real.log N →
      ∀ c : ℝ, 1 ≤ c → c / N ≤ 1 / 3 →
        (∑ m ∈ Icc 1 M,
          ‖Matrix.toEuclideanLin (completeWeilMatrix φ c N)
              (normalizedRamanujanHorizonVector m N) -
            completedConductorEnergy φ c m • normalizedRamanujanHorizonVector m N‖ ^ 2) ≤
          K_φ * ((M : ℝ) * (Real.log N + c ^ 2 * Real.log N + c ^ 4) +
            c ^ 3 * (Real.log N) ^ 5) := by
  obtain ⟨C_p, hCp, hp⟩ := exists_fullPrimeMatrix_levelOfDistribution
  obtain ⟨C_c, hCc, hc_mat⟩ := exists_sum_fullWeilCenter_norm_sq_le φ
  obtain ⟨C_x, hCx, hx⟩ := exists_sum_separatedCrossError_norm_sq_le hφ hsupp hM_int
  obtain ⟨C_q, hCq, hq⟩ := exists_sum_fullWeilPoleError_norm_sq_le hφ hsupp hM_int
  obtain ⟨C_in, hCin, hin⟩ := exists_sum_interiorNearGammaDownward_norm_sq_le hφ hsupp hM_int
  obtain ⟨C_ex, hCex, hex⟩ := exists_sum_exteriorDownward_norm_sq_le hφ hsupp hM_int
  obtain ⟨C_nc, hCnc, hnc⟩ := exists_sum_nearCenterVector_norm_sq_le φ
  obtain ⟨C_u, hCu, hu⟩ := exists_sum_upwardPrimeDefect_norm_sq_le hφ hsupp hM_int
  let K_φ := 8 * (C_p + C_c + C_x + C_q + 2 * C_in + 2 * C_ex + C_nc + C_u + 2 * Real.exp 1) + 1
  refine ⟨K_φ, by dsimp only [K_φ]; positivity, ?_⟩
  intro M N hM hMN hL c hc1 hw3
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN1 : 1 ≤ N := (Nat.mul_pos hM hM).trans_le hMN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hlogN : 1 ≤ Real.log N := by linarith [Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 7)]
  have hc3N : 3 * c ≤ N := by
    have h := (div_le_iff₀ hN0).mp hw3
    linarith only [h]
  have hc2N : 2 * c ≤ N := by linarith only [hc3N, hc0]
  have hcN : c ≤ N := by linarith only [hc3N, hc0]
  have hc2_le_c4 : c ^ 2 ≤ c ^ 4 := pow_le_pow_right₀ hc1 (by decide)
  -- Pointwise 8-piece norm square bound for each `m ∈ Icc 1 M`.
  have hpt8 : ∀ m ∈ Icc 1 M,
      ‖Matrix.toEuclideanLin (completeWeilMatrix φ c N)
          (normalizedRamanujanHorizonVector m N) -
        completedConductorEnergy φ c m • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
      8 * (‖Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector m N) -
            (Real.log N - ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m N‖ ^ 2 +
          ‖completeWeilSelfError φ c N • normalizedRamanujanHorizonVector m N‖ ^ 2 +
          ‖Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N)
              (normalizedRamanujanHorizonVector m N) -
            (if m = 1 then completeWeilPoleShift φ c else 0) •
              normalizedRamanujanHorizonVector m N‖ ^ 2 +
          ‖Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N)
            (normalizedRamanujanHorizonVector m N)‖ ^ 2 +
          ‖Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N)
            (normalizedRamanujanHorizonVector m N)‖ ^ 2 +
          (2 * ‖(Real.sqrt (m.totient : ℝ))⁻¹ • normalizedNearGammaDownwardVector φ c N m‖ ^ 2 +
            2 * ‖(Real.sqrt (m.totient : ℝ))⁻¹ • normalizedExteriorDownwardVector φ c N m‖ ^ 2) +
          ‖nearCenterVector φ c N m‖ ^ 2 +
          ‖upwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N) -
            shellCorrection φ c m • normalizedRamanujanHorizonVector m N‖ ^ 2) := by
    intro m hm
    have hm1 := (mem_Icc.mp hm).1
    rw [completeWeilMatrix_ramanujan_residual_eq_at_every_overlap hφ hsupp hM_int hc0 hN1 hm1]
    have h8 := norm_eight_signed_sq_le
      (Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector m N) -
        (Real.log N - ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m N)
      (completeWeilSelfError φ c N • normalizedRamanujanHorizonVector m N)
      (Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N)
          (normalizedRamanujanHorizonVector m N) -
        (if m = 1 then completeWeilPoleShift φ c else 0) •
          normalizedRamanujanHorizonVector m N)
      (Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N)
        (normalizedRamanujanHorizonVector m N))
      (Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N)
        (normalizedRamanujanHorizonVector m N))
      ((Real.sqrt (m.totient : ℝ))⁻¹ • normalizedFullNearGammaDownwardVector φ c N m)
      (nearCenterVector φ c N m)
      (upwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N) -
        shellCorrection φ c m • normalizedRamanujanHorizonVector m N)
    have hdown_split :
        ‖(Real.sqrt (m.totient : ℝ))⁻¹ • normalizedFullNearGammaDownwardVector φ c N m‖ ^ 2 ≤
          2 * ‖(Real.sqrt (m.totient : ℝ))⁻¹ • normalizedNearGammaDownwardVector φ c N m‖ ^ 2 +
            2 * ‖(Real.sqrt (m.totient : ℝ))⁻¹ • normalizedExteriorDownwardVector φ c N m‖ ^ 2 := by
      rw [normalizedFullNearGammaDownwardVector_eq_sub hφ hsupp hc0 N m, smul_sub]
      have h2 := norm_sub_sq_le_two
        ((Real.sqrt (m.totient : ℝ))⁻¹ • normalizedNearGammaDownwardVector φ c N m)
        ((Real.sqrt (m.totient : ℝ))⁻¹ • normalizedExteriorDownwardVector φ c N m)
      linarith only [h2]
    linarith only [h8, hdown_split]
  have hB_p := hp M N hM hMN hlogN
  have hB_s : (∑ m ∈ Icc 1 M,
      ‖completeWeilSelfError φ c N • normalizedRamanujanHorizonVector m N‖ ^ 2) ≤
      2 * Real.exp 1 * M * c ^ 4 :=
    (sum_completeWeilSelfError_norm_sq_le hφ hsupp hM_int hM hMN hL hc0 hcN).trans
      (mul_le_mul_of_nonneg_left hc2_le_c4 (by positivity))
  have hB_c := hc_mat M N hM hMN hL c
  have hB_x := hx M N hM hMN hL c hc0
  have hB_q := hq M N hM hMN hL c hc0 hcN
  have hB_in := hin M N hM hMN hlogN c hc1 hw3
  have hB_ex := hex M N hM hMN hlogN c hc1 hw3
  have hB_nc := hnc M N hM hMN hlogN c hc0 hc2N
  have hB_u : (∑ m ∈ Icc 1 M,
      ‖upwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N) -
        shellCorrection φ c m • normalizedRamanujanHorizonVector m N‖ ^ 2) ≤
      C_u * M * c ^ 4 :=
    (hu M N hM hMN hL c hc0 hcN).trans
      (mul_le_mul_of_nonneg_left hc2_le_c4 (by positivity))
  have hsum := sum_le_sum hpt8
  simp_rw [← mul_sum, sum_add_distrib, ← mul_sum] at hsum
  have hMR : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hpos_L : 0 ≤ (M : ℝ) * Real.log N := by positivity
  have hpos_cL : 0 ≤ (M : ℝ) * (c ^ 2 * Real.log N) := by positivity
  have hpos_c4 : 0 ≤ (M : ℝ) * c ^ 4 := by positivity
  have hpos_ex : 0 ≤ c ^ 3 * (Real.log N) ^ 5 := by positivity
  dsimp only [K_φ]
  linarith only [hsum, hB_p, hB_s, hB_c, hB_x, hB_q, hB_in, hB_ex, hB_nc, hB_u,
    mul_nonneg (by positivity : (0 : ℝ) ≤ C_c + C_x + C_q + 2 * C_in + 2 * C_ex + C_nc + C_u + 2 * Real.exp 1) hpos_L,
    mul_nonneg (by positivity : (0 : ℝ) ≤ C_p + C_x + C_q + 2 * C_ex + C_nc + C_u + 2 * Real.exp 1) hpos_cL,
    mul_nonneg (by positivity : (0 : ℝ) ≤ C_p + C_c + 2 * C_ex) hpos_c4,
    mul_nonneg (by positivity : (0 : ℝ) ≤ C_p + C_c + C_x + C_q + 2 * C_in + C_nc + C_u + 2 * Real.exp 1) hpos_ex,
    hpos_L, hpos_cL, hpos_c4, hpos_ex]

/-- Uniform linear-in-overlap logarithmic lower bound on `completedConductorEnergy`:
for every `c ≥ 1` and `m ≥ 1`, `log m - C_E * c ≤ completedConductorEnergy φ c m`. -/
theorem exists_completedConductorEnergy_ge_log_sub_linear {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM_int : 0 < ∫ u, φ u ^ 2) :
    ∃ C_E : ℝ, 0 < C_E ∧ ∀ c : ℝ, 1 ≤ c → ∀ m : ℕ, 1 ≤ m →
      Real.log m - C_E * c ≤ completedConductorEnergy φ c m := by
  let C_E := |completeWeilSelfFinitePart φ 1| + 2 * (Real.log 4 + 4) + 2
  refine ⟨C_E, by dsimp only [C_E]; positivity, ?_⟩
  intro c hc1 m hm
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  rw [completedConductorEnergy_eq_sub_shellCorrection hc0 hm, completeWeilAdjunctionEnergy,
    completeWeilSelfFinitePart_eq_at_one_sub_log φ hc0]
  have hlogm := log_le_ramanujanAdjunctionEnergy_sub m
  have hlogc : Real.log c ≤ c := (Real.log_le_sub_one_of_pos hc0).trans (by linarith only [hc0])
  have hself : -(|completeWeilSelfFinitePart φ 1| * c) ≤ completeWeilSelfFinitePart φ 1 := by
    have h1 : -|completeWeilSelfFinitePart φ 1| ≤ completeWeilSelfFinitePart φ 1 :=
      neg_abs_le _
    have h2 : |completeWeilSelfFinitePart φ 1| ≤ |completeWeilSelfFinitePart φ 1| * c :=
      le_mul_of_one_le_right (abs_nonneg _) hc1
    linarith only [h1, h2]
  have hpole : 0 ≤ (if m = 1 then completeWeilPoleShift φ c else 0) := by
    split_ifs
    · exact completeWeilPoleShift_nonneg φ hc0.le
    · exact le_rfl
  have hshell : -(2 * (Real.log 4 + 4) * c) ≤ -shellCorrection φ c m :=
    neg_le_neg ((le_abs_self _).trans (abs_shellCorrection_le_linear hφ hsupp hM_int hm hc0))
  have hCE_expand : C_E * c =
      |completeWeilSelfFinitePart φ 1| * c + (2 * (Real.log 4 + 4) * c) + 2 * c := by
    dsimp only [C_E]; ring
  rw [hCE_expand]
  linarith only [hlogm, hlogc, hself, hpole, hshell, hc0]

/-- Eventual Bombieri–Vinogradov conductor cutoff bounds for `M = ⌊N^θ⌋₊` (`0 < θ < 1 / 2`). -/
theorem eventually_conductorCutoff_bounds {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 1 / 2) :
    ∀ᶠ N : ℕ in atTop,
      2 ≤ ⌊(N : ℝ) ^ θ⌋₊ ∧
      ⌊(N : ℝ) ^ θ⌋₊ * ⌊(N : ℝ) ^ θ⌋₊ ≤ N ∧
      (N : ℝ) ^ θ / 2 ≤ (⌊(N : ℝ) ^ θ⌋₊ : ℝ) ∧
      (⌊(N : ℝ) ^ θ⌋₊ : ℝ) ≤ (N : ℝ) ^ θ ∧
      4 * Real.exp 7 ≤ Real.log N := by
  have hrpow : Tendsto (fun N : ℕ => (N : ℝ) ^ θ) atTop atTop :=
    (tendsto_rpow_atTop hθ0).comp tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hrpow.eventually_ge_atTop 2, hlog.eventually_ge_atTop (4 * Real.exp 7),
    eventually_ge_atTop 1] with N hNθ hLN hN1
  have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have h0 : 0 ≤ (N : ℝ) ^ θ := by positivity
  have hfl_ge2 : 2 ≤ ⌊(N : ℝ) ^ θ⌋₊ := Nat.le_floor hNθ
  have hfl_le : (⌊(N : ℝ) ^ θ⌋₊ : ℝ) ≤ (N : ℝ) ^ θ := Nat.floor_le h0
  have hfl_half : (N : ℝ) ^ θ / 2 ≤ (⌊(N : ℝ) ^ θ⌋₊ : ℝ) := by
    have hsub := (Nat.sub_one_lt_floor ((N : ℝ) ^ θ)).le
    linarith only [hsub, hNθ]
  have hsq : ⌊(N : ℝ) ^ θ⌋₊ * ⌊(N : ℝ) ^ θ⌋₊ ≤ N := by
    have hR : ((⌊(N : ℝ) ^ θ⌋₊ * ⌊(N : ℝ) ^ θ⌋₊ : ℕ) : ℝ) ≤ N := by
      push_cast
      calc
        (⌊(N : ℝ) ^ θ⌋₊ : ℝ) * (⌊(N : ℝ) ^ θ⌋₊ : ℝ) ≤ (N : ℝ) ^ θ * (N : ℝ) ^ θ :=
          mul_le_mul hfl_le hfl_le (Nat.cast_nonneg _) h0
        _ = (N : ℝ) ^ (θ + θ) := (Real.rpow_add (by positivity) θ θ).symm
        _ ≤ (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1R (by linarith only [hθ])
        _ = N := Real.rpow_one _
    exact_mod_cast hR
  exact ⟨hfl_ge2, hsq, hfl_half, hfl_le, hLN⟩

/-- Uniform eventual lower bound `(θ / 2) * log N ≤ completedConductorEnergy φ (c N) m`
across every top conductor slice `m ∈ Ioc ⌊δ * ⌊N^θ⌋₊⌋₊ ⌊N^θ⌋₊` (`0 < δ < 1`). -/
theorem eventually_completedConductorEnergy_ge_on_Ioc {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM_int : 0 < ∫ u, φ u ^ 2) {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 1 / 2)
    {c : ℕ → ℝ} (hc1 : ∀ᶠ N in atTop, 1 ≤ c N)
    (hc_lim : Tendsto (fun N => c N ^ 2 / Real.log N) atTop (𝓝 0))
    {δ : ℝ} (hδ0 : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ∀ m ∈ Ioc ⌊δ * (⌊(N : ℝ) ^ θ⌋₊ : ℝ)⌋₊ ⌊(N : ℝ) ^ θ⌋₊,
      (θ / 2) * Real.log N ≤ completedConductorEnergy φ (c N) m := by
  obtain ⟨C_E, hCE, hE_lb⟩ := exists_completedConductorEnergy_ge_log_sub_linear hφ hsupp hM_int
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hc_small := hc_lim.eventually (ge_mem_nhds (show 0 < θ / (4 * C_E) by positivity))
  have hL_large := hlog.eventually_ge_atTop (max 1 ((4 / θ) * |Real.log (δ / 2)|))
  filter_upwards [eventually_conductorCutoff_bounds hθ0 hθ, hc1, hc_small, hL_large,
    eventually_ge_atTop 2] with N hcut hcN1 hcN_sm hLN hN2
  obtain ⟨_, _, hfl_half, _, _⟩ := hcut
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hLN1 : 1 ≤ Real.log N := (le_max_left _ _).trans hLN
  have hLN0 : 0 < Real.log N := zero_lt_one.trans_le hLN1
  intro m hm
  obtain ⟨hm_gt, _⟩ := mem_Ioc.mp hm
  have hm1 : 1 ≤ m := (Nat.zero_le _).trans_lt hm_gt
  have hmR_gt : δ * (⌊(N : ℝ) ^ θ⌋₊ : ℝ) < m := Nat.lt_of_floor_lt hm_gt
  have hm_rpow : (δ / 2) * (N : ℝ) ^ θ ≤ m := by
    nlinarith only [hmR_gt, hfl_half, hδ0]
  have hlog_m : Real.log (δ / 2) + θ * Real.log N ≤ Real.log m := by
    have h := Real.log_le_log (by positivity) hm_rpow
    rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hN0] at h
    linarith only [h]
  have hc_le_c2 : c N ≤ c N ^ 2 := by nlinarith only [hcN1]
  have hCE_c : C_E * c N ≤ (θ / 4) * Real.log N := by
    have h1 : c N / Real.log N ≤ θ / (4 * C_E) :=
      (div_le_div_of_nonneg_right hc_le_c2 hLN0.le).trans hcN_sm
    have h2 := (div_le_iff₀ hLN0).mp h1
    have h3 := mul_le_mul_of_nonneg_left h2 hCE.le
    have hCE_ne : C_E ≠ 0 := hCE.ne'
    calc
      C_E * c N ≤ C_E * (θ / (4 * C_E) * Real.log N) := h3
      _ = (θ / 4) * Real.log N := by field_simp [hCE_ne]
  have hδ_bound : -(θ / 4) * Real.log N ≤ Real.log (δ / 2) := by
    have h1 : (4 / θ) * |Real.log (δ / 2)| ≤ Real.log N := (le_max_right _ _).trans hLN
    have h2 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ θ / 4 by positivity)
    have h3 : |Real.log (δ / 2)| ≤ (θ / 4) * Real.log N := by
      calc
        |Real.log (δ / 2)| = (θ / 4) * ((4 / θ) * |Real.log (δ / 2)|) := by
          field_simp [hθ0.ne']
        _ ≤ (θ / 4) * Real.log N := h2
    linarith only [neg_abs_le (Real.log (δ / 2)), h3]
  have hbase := hE_lb (c N) hcN1 m hm1
  linarith only [hbase, hlog_m, hCE_c, hδ_bound]

/-- Normalized collective residual decay relative to the natural arithmetic energy scale
`⌊N^θ⌋₊ * (log N)²` for every `0 < θ < 1 / 2` and `c N ^ 2 / log N → 0`. -/
theorem tendsto_completeWeil_residual_div_mul_log_sq_zero {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM_int : 0 < ∫ u, φ u ^ 2) {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 1 / 2)
    {c : ℕ → ℝ} (hc1 : ∀ᶠ N in atTop, 1 ≤ c N)
    (hc_lim : Tendsto (fun N => c N ^ 2 / Real.log N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ =>
      (∑ m ∈ Icc 1 ⌊(N : ℝ) ^ θ⌋₊,
        ‖Matrix.toEuclideanLin (completeWeilMatrix φ (c N) N)
            (normalizedRamanujanHorizonVector m N) -
          completedConductorEnergy φ (c N) m •
            normalizedRamanujanHorizonVector m N‖ ^ 2) /
      ((⌊(N : ℝ) ^ θ⌋₊ : ℝ) * (Real.log N) ^ 2)) atTop (𝓝 0) := by
  obtain ⟨K_φ, hKφ, hcoll⟩ := exists_completeWeil_collective_residual_bound hφ hsupp hM_int
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv_log : Tendsto (fun N : ℕ => 1 / Real.log (N : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hlog
  have hmaj : Tendsto (fun N : ℕ =>
      K_φ * ((1 + 1440 / θ ^ 6) * (1 / Real.log (N : ℝ)) +
        (c N ^ 2 / Real.log (N : ℝ)) + (c N ^ 2 / Real.log (N : ℝ)) ^ 2)) atTop (𝓝 0) := by
    have h1 := ((hinv_log.const_mul (1 + 1440 / θ ^ 6)).add hc_lim).add (hc_lim.pow 2)
    simpa only [mul_zero, add_zero] using h1.const_mul K_φ
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [eventually_conductorCutoff_bounds hθ0 hθ, hc1,
    hc_lim.eventually (ge_mem_nhds zero_lt_one),
    hlog.eventually_ge_atTop 6, eventually_ge_atTop 2] with N hcut hcN1 hc_le1 hLN6 hN2
  obtain ⟨hM2, hMN, hfl_half, _, hLN_exp⟩ := hcut
  have hM1 : 1 ≤ ⌊(N : ℝ) ^ θ⌋₊ := by omega
  have hMR0 : (0 : ℝ) < ⌊(N : ℝ) ^ θ⌋₊ := by exact_mod_cast hM1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hLN0 : 0 < Real.log N := by linarith only [hLN6]
  have hc2_le_L : c N ^ 2 ≤ Real.log N := (div_le_one hLN0).mp hc_le1
  have hc_le_L : c N ≤ Real.log N := (by nlinarith only [hcN1] : c N ≤ c N ^ 2).trans hc2_le_L
  -- Verify `c N / N ≤ 1 / 3` via `log N ^ 2 / 2 ≤ exp (log N) = N` and `6 ≤ log N`.
  have hw3 : c N / N ≤ 1 / 3 := by
    have hexp2 := Real.pow_div_factorial_le_exp (Real.log N) hLN0.le 2
    rw [Real.exp_log hN0, show (Nat.factorial 2 : ℝ) = 2 by norm_num] at hexp2
    rw [div_le_iff₀ hN0]
    nlinarith only [hc_le_L, hexp2, hLN6]
  -- Bound `(log N)^5 / ⌊N^θ⌋₊ ≤ (1440 / θ^6) * (1 / log N)` via `(θ log N)^6 / 720 ≤ N^θ`.
  have hlog5_div_M : (Real.log N) ^ 5 / (⌊(N : ℝ) ^ θ⌋₊ : ℝ) ≤
      (1440 / θ ^ 6) * (1 / Real.log N) := by
    have hexp6 := Real.pow_div_factorial_le_exp (θ * Real.log N) (by positivity) 6
    have hrpow_eq : Real.exp (θ * Real.log N) = (N : ℝ) ^ θ := by
      rw [Real.rpow_def_of_pos hN0, mul_comm]
    rw [hrpow_eq, show (Nat.factorial 6 : ℝ) = 720 by norm_num] at hexp6
    have hM_lb : (θ * Real.log N) ^ 6 / 1440 ≤ (⌊(N : ℝ) ^ θ⌋₊ : ℝ) := by
      linarith only [hexp6, hfl_half]
    have hden0 : 0 < (θ * Real.log N) ^ 6 / 1440 := by positivity
    calc
      (Real.log N) ^ 5 / (⌊(N : ℝ) ^ θ⌋₊ : ℝ) ≤
          (Real.log N) ^ 5 / ((θ * Real.log N) ^ 6 / 1440) :=
        div_le_div_of_nonneg_left (by positivity) hden0 hM_lb
      _ = (1440 / θ ^ 6) * (1 / Real.log N) := by
        field_simp [hθ0.ne', hLN0.ne']
  -- Bound `c^3 ≤ (log N)^2` since `1 ≤ c` and `c^2 ≤ log N`.
  have hc3_le_L2 : c N ^ 3 ≤ (Real.log N) ^ 2 := by
    have hc34 : c N ^ 3 ≤ c N ^ 4 := pow_le_pow_right₀ hcN1 (by decide)
    have hc4L2 : c N ^ 4 ≤ (Real.log N) ^ 2 := by
      have h := pow_le_pow_left₀ (sq_nonneg _) hc2_le_L 2
      simpa only [← pow_mul] using h
    exact hc34.trans hc4L2
  have hnum := hcoll ⌊(N : ℝ) ^ θ⌋₊ N hM1 hMN hLN_exp (c N) hcN1 hw3
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sum_nonneg fun _ _ => sq_nonneg _) (by positivity))]
  calc
    _ ≤ (K_φ * ((⌊(N : ℝ) ^ θ⌋₊ : ℝ) * (Real.log N + c N ^ 2 * Real.log N + c N ^ 4) +
          c N ^ 3 * (Real.log N) ^ 5)) /
        ((⌊(N : ℝ) ^ θ⌋₊ : ℝ) * (Real.log N) ^ 2) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ (K_φ * ((⌊(N : ℝ) ^ θ⌋₊ : ℝ) * (Real.log N + c N ^ 2 * Real.log N + c N ^ 4) +
          (Real.log N) ^ 2 * (Real.log N) ^ 5)) /
        ((⌊(N : ℝ) ^ θ⌋₊ : ℝ) * (Real.log N) ^ 2) := by
      refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hKφ.le) (by positivity)
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hc3_le_L2 (by positivity))
    _ = K_φ * ((1 / Real.log N + (Real.log N) ^ 5 / (⌊(N : ℝ) ^ θ⌋₊ : ℝ)) +
          c N ^ 2 / Real.log N + (c N ^ 2 / Real.log N) ^ 2) := by
      field_simp [hMR0.ne', hLN0.ne']; ring
    _ ≤ K_φ * ((1 + 1440 / θ ^ 6) * (1 / Real.log N) +
          (c N ^ 2 / Real.log N) + (c N ^ 2 / Real.log N) ^ 2) := by
      refine mul_le_mul_of_nonneg_left ?_ hKφ.le
      linarith only [hlog5_div_M]

/-- **Unconditional affirmative resolution of Question Q3 (Level of Distribution for Complete
Weil Residuals).** For every `C²` profile `φ` supported in `[0, 1]` with `0 < ∫ φ²`, every
Bombieri–Vinogradov exponent `0 < θ < 1 / 2`, and every overlap schedule `c : ℕ → ℝ` with
`∀ᶠ N, 1 ≤ c N` and `c N ^ 2 / log N → 0` (covering the entire RH-complete window
`c N = 2 * (log N)^α`, `1 / 4 < α < 1 / 2`), the collective complete-Weil residual energy across
all conductors `1 ≤ m ≤ ⌊N^θ⌋₊` vanishes relative to the collective completed conductor energy:
```
(∑_{m=1}^{⌊N^θ⌋₊} ‖W_{N, c_N} v_m - E_m(c_N) v_m‖²) / (∑_{m=1}^{⌊N^θ⌋₊} E_m(c_N)²) → 0.
```
-/
theorem tendsto_completeWeil_residual_levelOfDistribution {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM_int : 0 < ∫ u, φ u ^ 2) {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 1 / 2)
    {c : ℕ → ℝ} (hc1 : ∀ᶠ N in atTop, 1 ≤ c N)
    (hc_lim : Tendsto (fun N => c N ^ 2 / Real.log N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ =>
      (∑ m ∈ Icc 1 ⌊(N : ℝ) ^ θ⌋₊,
        ‖Matrix.toEuclideanLin (completeWeilMatrix φ (c N) N)
            (normalizedRamanujanHorizonVector m N) -
          completedConductorEnergy φ (c N) m •
            normalizedRamanujanHorizonVector m N‖ ^ 2) /
      (∑ m ∈ Icc 1 ⌊(N : ℝ) ^ θ⌋₊, completedConductorEnergy φ (c N) m ^ 2))
      atTop (𝓝 0) := by
  have hres := tendsto_completeWeil_residual_div_mul_log_sq_zero hφ hsupp hM_int hθ0 hθ hc1 hc_lim
  have hmaj := hres.const_mul (8 / θ ^ 2)
  simp only [mul_zero] at hmaj
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [eventually_conductorCutoff_bounds hθ0 hθ,
    eventually_completedConductorEnergy_ge_on_Ioc hφ hsupp hM_int hθ0 hθ hc1 hc_lim
      (by norm_num : (0 : ℝ) < 1 / 2)] with N hcut hE_top
  obtain ⟨hM2, _, _, _, hLN_exp⟩ := hcut
  have hLN0 : 0 < Real.log N := by linarith [Real.exp_pos 7]
  let M := ⌊(N : ℝ) ^ θ⌋₊
  let S_top := Ioc ⌊(1 / 2 : ℝ) * (M : ℝ)⌋₊ M
  have hsub : S_top ⊆ Icc 1 M := fun m hm =>
    mem_Icc.mpr ⟨(Nat.zero_le _).trans_lt (mem_Ioc.mp hm).1, (mem_Ioc.mp hm).2⟩
  have hcard_top : (M : ℝ) / 2 ≤ S_top.card := by
    have hfl : (⌊(1 / 2 : ℝ) * (M : ℝ)⌋₊ : ℝ) ≤ (1 / 2 : ℝ) * (M : ℝ) :=
      Nat.floor_le (by positivity)
    have hle_M : ⌊(1 / 2 : ℝ) * (M : ℝ)⌋₊ ≤ M := by
      have hR : (⌊(1 / 2 : ℝ) * (M : ℝ)⌋₊ : ℝ) ≤ (M : ℝ) :=
        hfl.trans (by linarith [Nat.cast_nonneg (α := ℝ) M])
      exact_mod_cast hR
    dsimp only [S_top]
    rw [Nat.card_Ioc, Nat.cast_sub hle_M]
    linarith only [hfl]
  have hden_lb : (θ ^ 2 / 8) * (M : ℝ) * (Real.log N) ^ 2 ≤
      ∑ m ∈ Icc 1 M, completedConductorEnergy φ (c N) m ^ 2 := by
    calc
      (θ ^ 2 / 8) * (M : ℝ) * (Real.log N) ^ 2 =
          ((M : ℝ) / 2) * ((θ / 2) * Real.log N) ^ 2 := by ring
      _ ≤ (S_top.card : ℝ) * ((θ / 2) * Real.log N) ^ 2 :=
        mul_le_mul_of_nonneg_right hcard_top (sq_nonneg _)
      _ = ∑ _m ∈ S_top, ((θ / 2) * Real.log N) ^ 2 := by rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ m ∈ S_top, completedConductorEnergy φ (c N) m ^ 2 :=
        sum_le_sum fun m hm => pow_le_pow_left₀ (by positivity) (hE_top m hm) 2
      _ ≤ ∑ m ∈ Icc 1 M, completedConductorEnergy φ (c N) m ^ 2 :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _
  have hden_pos : 0 < (θ ^ 2 / 8) * (M : ℝ) * (Real.log N) ^ 2 := by
    have hMR : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sum_nonneg fun _ _ => sq_nonneg _)
    (sum_nonneg fun _ _ => sq_nonneg _))]
  calc
    _ ≤ (∑ m ∈ Icc 1 M,
          ‖Matrix.toEuclideanLin (completeWeilMatrix φ (c N) N)
              (normalizedRamanujanHorizonVector m N) -
            completedConductorEnergy φ (c N) m •
              normalizedRamanujanHorizonVector m N‖ ^ 2) /
        ((θ ^ 2 / 8) * (M : ℝ) * (Real.log N) ^ 2) :=
      div_le_div_of_nonneg_left (sum_nonneg fun _ _ => sq_nonneg _) hden_pos hden_lb
    _ = (8 / θ ^ 2) * ((∑ m ∈ Icc 1 M,
          ‖Matrix.toEuclideanLin (completeWeilMatrix φ (c N) N)
              (normalizedRamanujanHorizonVector m N) -
            completedConductorEnergy φ (c N) m •
              normalizedRamanujanHorizonVector m N‖ ^ 2) /
          ((M : ℝ) * (Real.log N) ^ 2)) := by
      field_simp [hθ0.ne']

/-- Schedule helper: for `0 < α < 1 / 2`, the RH-complete logarithmic overlap
`2 * (log N)^α` eventually satisfies `1 ≤ 2 * (log N)^α` and `(2 * (log N)^α)^2 / log N → 0`. -/
theorem logarithmic_rhComplete_overlap_facts {α : ℝ} (hα0 : 0 < α) (hα : α < 1 / 2) :
    (∀ᶠ N : ℕ in atTop, 1 ≤ 2 * Real.log (N : ℝ) ^ α) ∧
    Tendsto (fun N : ℕ => (2 * Real.log (N : ℝ) ^ α) ^ 2 / Real.log (N : ℝ)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨?_, ?_⟩
  · filter_upwards [hlog.eventually_ge_atTop 1] with N hLN
    have hrpow : 1 ≤ Real.log (N : ℝ) ^ α := Real.one_le_rpow hLN hα0.le
    linarith only [hrpow]
  · have hlim : Tendsto (fun N : ℕ => 4 * (Real.log (N : ℝ) ^ (1 - 2 * α))⁻¹) atTop (𝓝 0) := by
      have hpos : 0 < 1 - 2 * α := by linarith only [hα]
      have h1 := tendsto_inv_atTop_zero.comp ((tendsto_rpow_atTop hpos).comp hlog)
      simpa only [mul_zero, Function.comp_def] using h1.const_mul 4
    refine hlim.congr' ?_
    filter_upwards [hlog.eventually_gt_atTop 0] with N hLN0
    have hpow2 : (Real.log (N : ℝ) ^ α) ^ 2 = Real.log (N : ℝ) ^ (2 * α) := by
      rw [← Real.rpow_natCast (Real.log (N : ℝ) ^ α) 2,
        ← Real.rpow_mul hLN0.le, Nat.cast_ofNat]
      ring_nf
    calc
      4 * (Real.log (N : ℝ) ^ (1 - 2 * α))⁻¹ =
          4 * Real.log (N : ℝ) ^ (-(1 - 2 * α)) := by rw [Real.rpow_neg hLN0.le]
      _ = 4 * Real.log (N : ℝ) ^ (2 * α - 1) := by ring_nf
      _ = 4 * (Real.log (N : ℝ) ^ (2 * α) / Real.log (N : ℝ) ^ (1 : ℝ)) := by
        rw [Real.rpow_sub hLN0]
      _ = (2 * Real.log (N : ℝ) ^ α) ^ 2 / Real.log (N : ℝ) := by
        rw [Real.rpow_one, ← hpow2]; ring

/-- **RH-Complete Specialization of Question Q3 (`tiltedUnitSpline`).** Along every overlap
schedule `c_N = 2 * (log N)^α` (`0 < α < 1 / 2`, covering the entire RH-complete regime
`1 / 4 < α < 1 / 2` of `riemannHypothesis_iff_tiltedUnitSpline_completeWeil_nonneg_log`),
and for every Bombieri–Vinogradov exponent `0 < θ < 1 / 2`, the `tiltedUnitSpline` complete-Weil
residuals satisfy level of distribution `θ`. -/
theorem tendsto_tiltedUnitSpline_completeWeil_residual_rhComplete
    {α θ : ℝ} (hα0 : 0 < α) (hα : α < 1 / 2) (hθ0 : 0 < θ) (hθ : θ < 1 / 2) :
    Tendsto (fun N : ℕ =>
      (∑ m ∈ Icc 1 ⌊(N : ℝ) ^ θ⌋₊,
        ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (2 * Real.log N ^ α) N)
            (normalizedRamanujanHorizonVector m N) -
          completedConductorEnergy tiltedUnitSpline (2 * Real.log N ^ α) m •
            normalizedRamanujanHorizonVector m N‖ ^ 2) /
      (∑ m ∈ Icc 1 ⌊(N : ℝ) ^ θ⌋₊,
        completedConductorEnergy tiltedUnitSpline (2 * Real.log N ^ α) m ^ 2))
      atTop (𝓝 0) := by
  obtain ⟨hc1, hc_lim⟩ := logarithmic_rhComplete_overlap_facts hα0 hα
  exact tendsto_completeWeil_residual_levelOfDistribution
    contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
    hθ0 hθ hc1 hc_lim

#print axioms exists_completeWeil_collective_residual_bound
#print axioms tendsto_completeWeil_residual_levelOfDistribution
#print axioms tendsto_tiltedUnitSpline_completeWeil_residual_rhComplete

end GaloisForLFunctions.CompletedArithmeticForms
