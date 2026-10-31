import GaloisForLFunctions.CompletedArithmeticForms.ConductorBandTopTailBounds
import GaloisForLFunctions.CompletedArithmeticForms.PrimeResidualLevelOfDistribution
import GaloisForLFunctions.SuccessorShellArithmetic.Conductor.PrimeConductorHeadNorm
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCenterCorrectionRetainsThePrimeDefect
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheMeanZeroCenterRowsAreUniformlyBounded
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheReplacementErrorsVanishAtEveryOverlap
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCompleteWeilMatrixDecomposesAtEveryOverlap

/-!
# Conductor-band bounds for the prime, center, pole, and separated-error operators

This module proves uniform norm and bilinear estimates on finite Ramanujan conductor subspaces
`conductorSubspace M N` below small powers of the horizon (`M ^ 6 ≤ N`):

* **Discrete `L²` packet orthogonality and `log log N`-free linear moment.** Pairwise period
  cancellation over `m * l ≤ R ^ 2` gives `∑_{j=1}^N (∑_{m=1}^R a_m g_m(j))^2 ≤ (N + R^4) ∑ a_m^2`,
  eliminating `log log N` from `∑_{j=1}^N (j / N) u_j^2 ≤ (4 / log N) ‖u‖^2`.
* **Pole annihilation and center-collar decay.** On `(conductorSubspace 1 N)ᗮ`, the harmonic sum
  vanishes identically, annihilating `fullWeilPoleErrorMatrix` and reducing `fullWeilCenterMatrix`
  to the negative archimedean collar. Splitting the collar into its pole leak, reciprocal-sum half,
  near-difference band (`|n - j| ≤ R^4`), and far-difference Abel tail (`|n - j| > R^4`) yields an
  `O(|α| (1 + log R) / √(log N))` bilinear bound.
* **Separated cross-error bounds.** Weighted integer-distance Schur bounds give both an `O(c^2)`
  whole-space operator norm bound and an `O(c^2 / log N)` quadratic bound on `conductorSubspace R N`.
* **Orthogonal prime cross-pairing without unsuppressed `log M`.** Subtracting the adjunction-energy
  diagonal `∑ a_m (log m + tameDifferent m) v_m ∈ conductorSubspace M N` leaves a uniform Mertens
  term of `O(1)` norm, a deep-quotient tail (`n ≤ N / M^4`) of `O(1 / M^2)` norm, and a top-strip
  term (`n > N / M^4`) whose reduced-dilation Plancherel expansion has norm
  `O((1 + log M)^2 / √(log N))`.
-/

noncomputable section

open MeasureTheory Finset Filter Topology ArithmeticFunction
open scoped BigOperators RealInnerProductSpace Classical

namespace GaloisForLFunctions.CompletedArithmeticForms

open SignedArithmeticHodgeTheory RenormalizedArithmeticPotentialTheory
  CriticalArithmeticCorrelationTheory SuccessorShellArithmetic
  ArithmeticIntersectionTheory ArithmeticEffectivityTheory ArithmeticElectrostatics
  BezoutValuationIncidence HTGeometry
  RenormalizedBiarithmeticGeometry SpacingScaleHarmonicAnalysis

/-! ### 1. Discrete `L²` packet bound and `log log N`-free linear moment -/

private theorem sum_Ioc_mul_periodic_eq {f : ℕ → ℝ} {q : ℕ} (hq : 0 < q)
    (hf : Function.Periodic f q) (B : ℕ) :
    (∑ j ∈ Ioc 0 (B * q), f j) = (B : ℝ) * ∑ r ∈ range q, f r := by
  induction B with
  | zero => simp
  | succ B ih =>
    have hunion : Ioc 0 ((B + 1) * q) = Ioc 0 (B * q) ∪ Ioc (B * q) (B * q + q) := by
      have hmul : (B + 1) * q = B * q + q := Nat.succ_mul B q
      ext j; simp only [mem_Ioc, mem_union, hmul]; omega
    have hdisj : Disjoint (Ioc 0 (B * q)) (Ioc (B * q) (B * q + q)) := by
      rw [Finset.disjoint_left]
      intro j hj1 hj2
      simp only [mem_Ioc] at hj1 hj2
      omega
    rw [hunion, sum_union hdisj, ih, sum_Ioc_periodic_eq hq hf (B * q), Nat.cast_add, Nat.cast_one]
    ring

private theorem sum_Icc_normalizedRamanujanMode_mul_le {m l R N : ℕ}
    (hm : m ∈ Icc 1 R) (hl : l ∈ Icc 1 R) (a : ℕ → ℝ) :
    a m * a l * (∑ j ∈ Icc 1 N, normalizedRamanujanMode m j * normalizedRamanujanMode l j) ≤
      (if m = l then (N : ℝ) * a m ^ 2 else 0) + |a m| * |a l| * (R : ℝ) ^ 3 := by
  obtain ⟨hm1, hmR⟩ := mem_Icc.mp hm
  obtain ⟨hl1, hlR⟩ := mem_Icc.mp hl
  have hm0 : 0 < m := hm1
  have hl0 : 0 < l := hl1
  let q := m * l
  have hq0 : 0 < q := Nat.mul_pos hm0 hl0
  have hqR2 : (q : ℝ) ≤ (R : ℝ) ^ 2 := by
    have hnat : m * l ≤ R * R := Nat.mul_le_mul hmR hlR
    have hcast : ((m * l : ℕ) : ℝ) ≤ ((R * R : ℕ) : ℝ) := by exact_mod_cast hnat
    simpa only [q, Nat.cast_mul, sq] using hcast
  let f : ℕ → ℝ := fun j => normalizedRamanujanMode m j * normalizedRamanujanMode l j
  have hpm : Function.Periodic (normalizedRamanujanMode m) q := by
    simpa only [q, Nat.cast_id, Nat.mul_comm] using (normalizedRamanujanMode_periodic hm0).nat_mul l
  have hpl : Function.Periodic (normalizedRamanujanMode l) q := by
    simpa only [q, Nat.cast_id] using (normalizedRamanujanMode_periodic hl0).nat_mul m
  have hper : Function.Periodic f q := fun j => congrArg₂ (· * ·) (hpm j) (hpl j)
  have hmean : (∑ r ∈ range q, f r) = (q : ℝ) * (if m = l then 1 else 0) := by
    have hp := periodMean_normalizedRamanujanMode_mul hm0 hl0 (dvd_mul_right m l)
      (dvd_mul_left l m) hq0
    have hqR0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq0.ne'
    unfold periodMean at hp
    rw [div_eq_iff hqR0] at hp
    linarith only [hp, mul_comm (if m = l then (1 : ℝ) else 0) (q : ℝ)]
  let B := N / q
  have hBq_le : B * q ≤ N := Nat.div_mul_le_self N q
  have hrem_lt : N - B * q < q := by
    have h1 : q * B + N % q = N := Nat.div_add_mod N q
    have h2 : N % q < q := Nat.mod_lt N hq0
    have hmul : q * B = B * q := Nat.mul_comm q B
    omega
  have hsplit : Icc 1 N = Ioc 0 (B * q) ∪ Ioc (B * q) N := by
    ext j; simp only [mem_Icc, mem_union, mem_Ioc]; omega
  have hdisj : Disjoint (Ioc 0 (B * q)) (Ioc (B * q) N) := by
    rw [Finset.disjoint_left]; intro j hj1 hj2; simp only [mem_Ioc] at hj1 hj2; omega
  have hsum_eq : (∑ j ∈ Icc 1 N, f j) =
      (B : ℝ) * ((q : ℝ) * (if m = l then 1 else 0)) + ∑ j ∈ Ioc (B * q) N, f j := by
    rw [hsplit, sum_union hdisj, sum_Ioc_mul_periodic_eq hq0 hper B, hmean]
  have hf_abs : ∀ j, |f j| ≤ R := by
    intro j
    dsimp only [f]
    rw [abs_mul]
    have h1 := abs_normalizedRamanujanMode_le_sqrt_totient hm0 j
    have h2 := abs_normalizedRamanujanMode_le_sqrt_totient hl0 j
    have hφm : (m.totient : ℝ) ≤ R := by exact_mod_cast (Nat.totient_le m).trans hmR
    have hφl : (l.totient : ℝ) ≤ R := by exact_mod_cast (Nat.totient_le l).trans hlR
    calc
      |normalizedRamanujanMode m j| * |normalizedRamanujanMode l j| ≤
          Real.sqrt m.totient * Real.sqrt l.totient :=
        mul_le_mul h1 h2 (abs_nonneg _) (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt R * Real.sqrt R :=
        mul_le_mul (Real.sqrt_le_sqrt hφm) (Real.sqrt_le_sqrt hφl)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = R := Real.mul_self_sqrt (Nat.cast_nonneg R)
  have htail_abs : |∑ j ∈ Ioc (B * q) N, f j| ≤ (R : ℝ) ^ 3 := by
    calc
      |∑ j ∈ Ioc (B * q) N, f j| ≤ ∑ j ∈ Ioc (B * q) N, |f j| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ Ioc (B * q) N, (R : ℝ) := sum_le_sum fun j _ => hf_abs j
      _ = ((N - B * q : ℕ) : ℝ) * R := by rw [sum_const, Nat.card_Ioc, nsmul_eq_mul]
      _ ≤ (q : ℝ) * R :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hrem_lt.le) (Nat.cast_nonneg R)
      _ ≤ (R : ℝ) ^ 2 * R := mul_le_mul_of_nonneg_right hqR2 (Nat.cast_nonneg R)
      _ = (R : ℝ) ^ 3 := by ring
  have htail_prod : a m * a l * (∑ j ∈ Ioc (B * q) N, f j) ≤ |a m| * |a l| * (R : ℝ) ^ 3 := by
    calc
      a m * a l * (∑ j ∈ Ioc (B * q) N, f j) ≤ |a m * a l * ∑ j ∈ Ioc (B * q) N, f j| :=
        le_abs_self _
      _ = |a m| * |a l| * |∑ j ∈ Ioc (B * q) N, f j| := by rw [abs_mul, abs_mul]
      _ ≤ |a m| * |a l| * (R : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_left htail_abs (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  change a m * a l * (∑ j ∈ Icc 1 N, f j) ≤ _
  rw [hsum_eq, mul_add]
  refine add_le_add ?_ htail_prod
  by_cases hml : m = l
  · subst l
    rw [if_pos rfl, if_pos rfl, mul_one]
    have hBqR : (B : ℝ) * q ≤ N := by exact_mod_cast hBq_le
    have hsq : 0 ≤ a m ^ 2 := sq_nonneg (a m)
    nlinarith only [hBqR, hsq, (by ring : a m * a m = a m ^ 2)]
  · rw [if_neg hml, if_neg hml]
    ring_nf
    exact le_rfl

/-- Discrete `L²` Plancherel bound on `[1, N]` for any conductor packet supported on `Icc 1 R`. -/
theorem sum_Icc_packet_mode_sq_le (R N : ℕ) (a : ℕ → ℝ) :
    (∑ j ∈ Icc 1 N, (∑ m ∈ Icc 1 R, a m * normalizedRamanujanMode m j) ^ 2) ≤
      ((N : ℝ) + (R : ℝ) ^ 4) * ∑ m ∈ Icc 1 R, a m ^ 2 := by
  have hexp : (∑ j ∈ Icc 1 N, (∑ m ∈ Icc 1 R, a m * normalizedRamanujanMode m j) ^ 2) =
      ∑ m ∈ Icc 1 R, ∑ l ∈ Icc 1 R,
        a m * a l * ∑ j ∈ Icc 1 N, normalizedRamanujanMode m j * normalizedRamanujanMode l j := by
    calc
      _ = ∑ j ∈ Icc 1 N, ∑ m ∈ Icc 1 R, ∑ l ∈ Icc 1 R,
            a m * a l * (normalizedRamanujanMode m j * normalizedRamanujanMode l j) := by
        refine sum_congr rfl fun j _ => ?_
        rw [pow_two, sum_mul]
        refine sum_congr rfl fun m _ => ?_
        rw [mul_sum]
        exact sum_congr rfl fun l _ => by ring
      _ = ∑ m ∈ Icc 1 R, ∑ l ∈ Icc 1 R, ∑ j ∈ Icc 1 N,
            a m * a l * (normalizedRamanujanMode m j * normalizedRamanujanMode l j) := by
        rw [sum_comm]
        exact sum_congr rfl fun _ _ => sum_comm
      _ = _ := sum_congr rfl fun m _ => sum_congr rfl fun l _ => (mul_sum ..).symm
  rw [hexp]
  have hsum_le :
      (∑ m ∈ Icc 1 R, ∑ l ∈ Icc 1 R,
        a m * a l * ∑ j ∈ Icc 1 N, normalizedRamanujanMode m j * normalizedRamanujanMode l j) ≤
      (∑ m ∈ Icc 1 R, ∑ l ∈ Icc 1 R, if m = l then (N : ℝ) * a m ^ 2 else 0) +
        ∑ m ∈ Icc 1 R, ∑ l ∈ Icc 1 R, |a m| * |a l| * (R : ℝ) ^ 3 := by
    rw [← sum_add_distrib]
    refine sum_le_sum fun m hm => ?_
    rw [← sum_add_distrib]
    exact sum_le_sum fun l hl => sum_Icc_normalizedRamanujanMode_mul_le hm hl a
  have hdiag : (∑ m ∈ Icc 1 R, ∑ l ∈ Icc 1 R, if m = l then (N : ℝ) * a m ^ 2 else 0) =
      (N : ℝ) * ∑ m ∈ Icc 1 R, a m ^ 2 := by
    rw [mul_sum]
    refine sum_congr rfl fun m hm => ?_
    rw [sum_ite_eq, if_pos hm]
  have hoff : (∑ m ∈ Icc 1 R, ∑ l ∈ Icc 1 R, |a m| * |a l| * (R : ℝ) ^ 3) ≤
      (R : ℝ) ^ 4 * ∑ m ∈ Icc 1 R, a m ^ 2 := by
    have hfact : (∑ m ∈ Icc 1 R, ∑ l ∈ Icc 1 R, |a m| * |a l| * (R : ℝ) ^ 3) =
        (R : ℝ) ^ 3 * (∑ m ∈ Icc 1 R, |a m|) ^ 2 := by
      rw [pow_two, sum_mul]
      simp only [mul_sum]
      refine (sum_congr rfl fun m _ => sum_congr rfl fun l _ => by ring)
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Icc 1 R) (fun m => |a m|) (fun _ => (1 : ℝ))
    simp only [mul_one, sq_abs, one_pow, sum_const, Nat.card_Icc, Nat.add_sub_cancel,
      nsmul_eq_mul] at hcs
    rw [hfact]
    calc
      (R : ℝ) ^ 3 * (∑ m ∈ Icc 1 R, |a m|) ^ 2 ≤
          (R : ℝ) ^ 3 * ((∑ m ∈ Icc 1 R, a m ^ 2) * R) :=
        mul_le_mul_of_nonneg_left hcs (by positivity)
      _ = (R : ℝ) ^ 4 * ∑ m ∈ Icc 1 R, a m ^ 2 := by ring
  calc
    _ ≤ (∑ m ∈ Icc 1 R, ∑ l ∈ Icc 1 R, if m = l then (N : ℝ) * a m ^ 2 else 0) +
          ∑ m ∈ Icc 1 R, ∑ l ∈ Icc 1 R, |a m| * |a l| * (R : ℝ) ^ 3 := hsum_le
    _ ≤ (N : ℝ) * (∑ m ∈ Icc 1 R, a m ^ 2) + (R : ℝ) ^ 4 * ∑ m ∈ Icc 1 R, a m ^ 2 := by
      rw [hdiag]; exact add_le_add le_rfl hoff
    _ = ((N : ℝ) + (R : ℝ) ^ 4) * ∑ m ∈ Icc 1 R, a m ^ 2 := by ring

/-- `log log N`-free linear-moment bound `∑_{j=1}^N (j / N) u_j^2 ≤ (4 / log N) ‖u‖^2` on
`conductorSubspace R N` whenever `R ^ 4 ≤ N`. -/
theorem sum_linear_moment_sq_le_four_div_log {R N : ℕ} (hR : 2 ≤ R) (hRN4 : R ^ 4 ≤ N)
    (hlog : 18 * (1 + Real.log R) ≤ Real.log N)
    {u : EuclideanSpace ℝ (PrimeHorizonIndex N)} (hu : u ∈ conductorSubspace R N) :
    Real.log N * (∑ j ∈ Icc 1 N, ((j : ℝ) / N) * primeHorizonExtension u j ^ 2) ≤
      4 * ‖u‖ ^ 2 := by
  obtain ⟨a, -, rfl⟩ := (mem_conductorSubspace_iff (M := R) (N := N) (x := u)).mp hu
  have hRN2 : R * R ≤ N := by
    have h4 : R * R ≤ R ^ 4 := by
      have : 1 ≤ R * R := Nat.mul_pos (by omega) (by omega)
      nlinarith [show R ^ 4 = (R * R) * (R * R) by ring]
    exact h4.trans hRN4
  have hN1 : 1 ≤ N := (Nat.mul_pos (by omega : 0 < R) (by omega : 0 < R)).trans_le hRN2
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hL : 0 < Real.log N := by
    have hR0 := Real.log_natCast_nonneg R
    linarith only [hlog, hR0]
  have hterm (j : ℕ) (hj : j ∈ Icc 1 N) :
      Real.log N * (((j : ℝ) / N) * primeHorizonExtension
        (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N) j ^ 2) =
      (1 / (N : ℝ)) * (∑ m ∈ Icc 1 R, a m * normalizedRamanujanMode m j) ^ 2 := by
    have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hj).1
    rw [primeHorizonExtension_coe _ ⟨j, hj⟩]
    have hp : (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N) ⟨j, hj⟩ =
        (Real.sqrt (Real.log N))⁻¹ *
          ((∑ m ∈ Icc 1 R, a m * normalizedRamanujanMode m j) / Real.sqrt j) := by
      change (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : PrimeHorizonIndex N => ℝ) ⟨j, hj⟩)
        (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N) = _
      rw [map_sum, sum_div, mul_sum]
      refine sum_congr rfl fun m _ => ?_
      change a m * ((Real.sqrt (Real.log N))⁻¹ * (normalizedRamanujanMode m j / Real.sqrt j)) = _
      ring
    rw [hp, mul_pow, inv_pow, div_pow, Real.sq_sqrt hL.le, Real.sq_sqrt hj0.le]
    field_simp [hL.ne', hj0.ne', hN0.ne']
  rw [mul_sum, sum_congr rfl hterm, ← mul_sum]
  have hpack := sum_Icc_packet_mode_sq_le R N a
  have hRN4R : (R : ℝ) ^ 4 ≤ N := by exact_mod_cast hRN4
  have hriesz := (half_and_three_halves_riesz_of_log_le hR hRN2 hlog a).1
  have hsum0 : 0 ≤ ∑ m ∈ Icc 1 R, a m ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  calc
    (1 / (N : ℝ)) * (∑ j ∈ Icc 1 N, (∑ m ∈ Icc 1 R, a m * normalizedRamanujanMode m j) ^ 2) ≤
        (1 / (N : ℝ)) * (((N : ℝ) + (R : ℝ) ^ 4) * ∑ m ∈ Icc 1 R, a m ^ 2) :=
      mul_le_mul_of_nonneg_left hpack (by positivity)
    _ ≤ (1 / (N : ℝ)) * ((2 * (N : ℝ)) * ∑ m ∈ Icc 1 R, a m ^ 2) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (by linarith only [hRN4R]) hsum0) (by positivity)
    _ = 2 * ∑ m ∈ Icc 1 R, a m ^ 2 := by field_simp [hN0.ne']
    _ ≤ 4 * ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 := by
      linarith only [hriesz]

/-! ### 2. Pole annihilation and center-matrix bilinear bound -/

/-- Bilinear identity for `horizonKernelMatrix` on `EuclideanSpace ℝ (PrimeHorizonIndex N)`. -/
theorem horizonKernelMatrix_bilinear (K : ℕ → ℕ → ℝ) (N : ℕ)
    (x y : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ⟪Matrix.toEuclideanLin (horizonKernelMatrix K N) x, y⟫ =
      ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
        primeHorizonExtension y n * primeHorizonExtension x j * K n j := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ n : PrimeHorizonIndex N, y n * ∑ j : PrimeHorizonIndex N, K n j * x j) = _
  simp only [mul_sum]
  rw [← sum_coe_sort (Icc 1 N) (fun n => ∑ j ∈ Icc 1 N,
    primeHorizonExtension y n * primeHorizonExtension x j * K n j)]
  refine sum_congr rfl fun n _ => ?_
  rw [← sum_coe_sort (Icc 1 N)
    (fun j => primeHorizonExtension y n * primeHorizonExtension x j * K n j)]
  refine sum_congr rfl fun j _ => ?_
  rw [primeHorizonExtension_coe, primeHorizonExtension_coe]
  ring

/-- Orthogonality to `conductorSubspace 1 N` annihilates `harmonicSum`. -/
theorem harmonicSum_eq_zero_of_mem_orthog_one {N : ℕ} (hN : 2 ≤ N)
    {x : EuclideanSpace ℝ (PrimeHorizonIndex N)} (hx : x ∈ (conductorSubspace 1 N)ᗮ) :
    SelectiveMultiscaleArithmeticPositivity.harmonicSum N (primeHorizonExtension x) = 0 := by
  have hv1 : normalizedRamanujanHorizonVector 1 N ∈ conductorSubspace 1 N :=
    mem_conductorSubspace_normalizedRamanujanHorizonVector (mem_Icc.mpr ⟨le_rfl, le_rfl⟩)
  have horth : ⟪normalizedRamanujanHorizonVector 1 N, x⟫ = 0 :=
    (Submodule.mem_orthogonal _ _).mp hx _ hv1
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hsinv : (Real.sqrt (Real.log N))⁻¹ ≠ 0 := inv_ne_zero (Real.sqrt_pos.mpr hlog).ne'
  have hmode1 : ∀ n : ℕ, normalizedRamanujanMode 1 n = 1 := by
    intro n
    rw [normalizedRamanujanMode, ramanujanMode_one, Nat.totient_one, Nat.cast_one,
      Real.sqrt_one, div_one]
  have hinner : ⟪normalizedRamanujanHorizonVector 1 N, x⟫ =
      (Real.sqrt (Real.log N))⁻¹ *
        SelectiveMultiscaleArithmeticPositivity.harmonicSum N (primeHorizonExtension x) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    change (∑ n : PrimeHorizonIndex N,
      x n * ((Real.sqrt (Real.log N))⁻¹ * (normalizedRamanujanMode 1 n / Real.sqrt (n : ℕ)))) = _
    rw [SelectiveMultiscaleArithmeticPositivity.harmonicSum, mul_sum,
      ← sum_coe_sort (Icc 1 N) (fun n =>
        (Real.sqrt (Real.log N))⁻¹ * (primeHorizonExtension x n / Real.sqrt n))]
    refine sum_congr rfl fun n _ => ?_
    rw [hmode1 n, primeHorizonExtension_coe]
    ring
  rw [hinner, mul_eq_zero] at horth
  exact horth.resolve_left hsinv

private theorem arithmeticPoleKernel_bilinear_eq_zero {N : ℕ} {a b : ℕ → ℝ}
    (ha : SelectiveMultiscaleArithmeticPositivity.harmonicSum N a = 0)
    (hb : SelectiveMultiscaleArithmeticPositivity.harmonicSum N b = 0) :
    (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, b n * a j * arithmeticPoleKernel n j) = 0 := by
  unfold SelectiveMultiscaleArithmeticPositivity.harmonicSum at ha hb
  have hterm (n j : ℕ) : b n * a j * arithmeticPoleKernel n j =
      (b n * Real.sqrt n) * (a j / Real.sqrt j) +
        (b n / Real.sqrt n) * (a j * Real.sqrt j) := by
    unfold arithmeticPoleKernel
    ring
  simp only [hterm, sum_add_distrib, ← mul_sum, ← sum_mul]
  rw [ha, hb]
  ring

/-- `fullWeilPoleErrorMatrix` vanishes identically on `(conductorSubspace 1 N)ᗮ`. -/
theorem fullWeilPoleErrorMatrix_inner_eq_zero_of_orthog_one (φ : ℝ → ℝ) (c : ℝ)
    {N : ℕ} (hN : 2 ≤ N)
    {x y : EuclideanSpace ℝ (PrimeHorizonIndex N)}
    (hx : x ∈ (conductorSubspace 1 N)ᗮ) (hy : y ∈ (conductorSubspace 1 N)ᗮ) :
    ⟪Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N) x, y⟫ = 0 := by
  change ⟪Matrix.toEuclideanLin
    (horizonKernelMatrix (fun n j => atomPoleErrorCoefficient φ c N * arithmeticPoleKernel n j) N)
    x, y⟫ = 0
  rw [horizonKernelMatrix_bilinear]
  have hfactor : (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
      primeHorizonExtension y n * primeHorizonExtension x j *
        (atomPoleErrorCoefficient φ c N * arithmeticPoleKernel n j)) =
      atomPoleErrorCoefficient φ c N *
        ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
          primeHorizonExtension y n * primeHorizonExtension x j * arithmeticPoleKernel n j := by
    rw [mul_sum]
    refine sum_congr rfl fun n _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun j _ => by ring
  rw [hfactor, arithmeticPoleKernel_bilinear_eq_zero
    (harmonicSum_eq_zero_of_mem_orthog_one hN hx)
    (harmonicSum_eq_zero_of_mem_orthog_one hN hy), mul_zero]

private theorem sum_inv_add_sq_le {n N : ℕ} (hn : 1 ≤ n) :
    (∑ j ∈ Icc 1 N, 1 / ((n : ℝ) + j) ^ 2) ≤ 1 / (n : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hstep : ∀ k : ℕ, 1 / ((n : ℝ) + (k + 1 : ℕ)) ^ 2 ≤
      1 / ((n : ℝ) + k) - 1 / ((n : ℝ) + (k + 1 : ℕ)) := by
    intro k
    have ha : 0 < (n : ℝ) + k := by positivity
    have hb : 0 < (n : ℝ) + (k + 1 : ℕ) := by positivity
    have hdiff : 1 / ((n : ℝ) + k) - 1 / ((n : ℝ) + (k + 1 : ℕ)) =
        1 / (((n : ℝ) + k) * ((n : ℝ) + (k + 1 : ℕ))) := by
      field_simp [ha.ne', hb.ne']
      push_cast
      ring
    rw [hdiff, div_le_div_iff₀ (sq_pos_of_pos hb) (mul_pos ha hb)]
    push_cast
    nlinarith only [ha]
  have hreindex : (∑ j ∈ Icc 1 N, 1 / ((n : ℝ) + j) ^ 2) =
      ∑ k ∈ range N, 1 / ((n : ℝ) + (k + 1 : ℕ)) ^ 2 := by
    refine sum_bij (fun j _ => j - 1) ?_ ?_ ?_ ?_
    · intro j hj; obtain ⟨h1, h2⟩ := mem_Icc.mp hj; exact mem_range.mpr (by omega)
    · intro i hi j hj hij
      obtain ⟨hi1, _⟩ := mem_Icc.mp hi; obtain ⟨hj1, _⟩ := mem_Icc.mp hj
      change i - 1 = j - 1 at hij; omega
    · intro k hk; refine ⟨k + 1, mem_Icc.mpr ⟨by omega, by have := mem_range.mp hk; omega⟩, by omega⟩
    · intro j hj; obtain ⟨hj1, _⟩ := mem_Icc.mp hj; rw [Nat.sub_add_cancel hj1]
  rw [hreindex]
  calc
    (∑ k ∈ range N, 1 / ((n : ℝ) + (k + 1 : ℕ)) ^ 2) ≤
        ∑ k ∈ range N, (1 / ((n : ℝ) + k) - 1 / ((n : ℝ) + (k + 1 : ℕ))) :=
      sum_le_sum fun k _ => hstep k
    _ = 1 / ((n : ℝ) + (0 : ℕ)) - 1 / ((n : ℝ) + N) :=
      sum_range_sub' (fun k : ℕ => 1 / ((n : ℝ) + k)) N
    _ ≤ 1 / (n : ℝ) := by
      simp only [Nat.cast_zero, add_zero]
      have : 0 ≤ 1 / ((n : ℝ) + N) := by positivity
      linarith only [this]

private theorem sum_range_normalizedRamanujanMode_eq_zero_of_two_le {m : ℕ} (hm : 2 ≤ m) :
    (∑ j ∈ range m, normalizedRamanujanMode m j) = 0 := by
  have hm0 : 0 < m := by omega
  have hp := periodMean_normalizedRamanujanMode_mul hm0 one_pos dvd_rfl (one_dvd m) hm0
  rw [if_neg (by omega : m ≠ 1)] at hp
  unfold periodMean at hp
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm0.ne'
  have hsum0 : (∑ j ∈ range m, normalizedRamanujanMode m j * normalizedRamanujanMode 1 j) = 0 :=
    (div_eq_zero_iff.mp hp).resolve_right hmR
  have hmode1 : ∀ j, normalizedRamanujanMode 1 j = 1 := fun j => by
    rw [normalizedRamanujanMode, ramanujanMode_one, Nat.totient_one, Nat.cast_one,
      Real.sqrt_one, div_one]
  simpa only [hmode1, mul_one] using hsum0

private theorem abs_sum_far_lower_div_sub_le {g : ℕ → ℝ} {B : ℝ} {n D : ℕ}
    (hB : ∀ l k : ℕ, l ≤ k → |∑ j ∈ Ico l k, g j| ≤ B) (hB0 : 0 ≤ B)
    (hD : 0 < D) (hn : D + 1 < n) :
    |∑ j ∈ Icc 1 (n - D - 1), g j / ((n : ℝ) - j)| ≤ B / (D : ℝ) := by
  let L := n - D - 1
  have hL1 : 1 ≤ L := by dsimp only [L]; omega
  have hpartial (k : ℕ) (hk : k ≤ L) : |∑ i ∈ range k, g (L - i)| ≤ B := by
    rw [← Nat.Ico_zero_eq_range, sum_Ico_reflect g 0 (show k ≤ L + 1 by omega), Nat.sub_zero]
    exact hB (L + 1 - k) (L + 1) (Nat.sub_le _ _)
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have h := abs_sum_mul_le_of_finite_partial
    (g := fun i => g (L - i)) (w := fun i => 1 / ((D : ℝ) + 1 + i))
    L hpartial (fun i => by positivity)
    (fun i => by apply one_div_le_one_div_of_le (by positivity); push_cast; linarith)
  have heq : (∑ i ∈ range L, 1 / ((D : ℝ) + 1 + i) * g (L - i)) =
      ∑ j ∈ Icc 1 L, g j / ((n : ℝ) - j) := by
    refine sum_bij (fun i _ => L - i) ?_ ?_ ?_ ?_
    · intro i hi; have := mem_range.mp hi; exact mem_Icc.mpr ⟨by omega, by omega⟩
    · intro i hi j hj hij
      have := mem_range.mp hi; have := mem_range.mp hj
      change L - i = L - j at hij; omega
    · intro j hj; obtain ⟨h1, h2⟩ := mem_Icc.mp hj
      refine ⟨L - j, mem_range.mpr (by omega), by omega⟩
    · intro i hi
      have hi' := mem_range.mp hi
      have hnat : n - (L - i) = D + 1 + i := by dsimp only [L]; omega
      have hsub : (n : ℝ) - ((L - i : ℕ) : ℝ) = (D : ℝ) + 1 + i := by
        rw [← Nat.cast_sub (show L - i ≤ n by dsimp only [L]; omega), hnat]
        push_cast; ring
      rw [hsub]; ring
  rw [heq, Nat.cast_zero, add_zero] at h
  exact h.trans (by
    rw [mul_one_div]
    exact div_le_div_of_nonneg_left hB0 hD0 (by linarith))

private theorem abs_sum_far_erase_div_abs_sub_le {g : ℕ → ℝ} {B : ℝ} {n D N : ℕ}
    (hn : n ∈ Icc 1 N) (hD : 0 < D) (hB0 : 0 ≤ B)
    (hB : ∀ l k : ℕ, l ≤ k → |∑ j ∈ Ico l k, g j| ≤ B) :
    |∑ j ∈ (Icc 1 N).filter (fun j : ℕ => (D : ℝ) < |(n : ℝ) - j|),
      g j / |(n : ℝ) - j| | ≤ 2 * B / (D : ℝ) := by
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  let S_lo := (Icc 1 N).filter (fun j : ℕ => j + D < n)
  let S_hi := (Icc 1 N).filter (fun j : ℕ => n + D < j)
  have hpart : (Icc 1 N).filter (fun j : ℕ => (D : ℝ) < |(n : ℝ) - j|) = S_lo ∪ S_hi := by
    ext j
    simp only [S_lo, S_hi, mem_filter, mem_union]
    constructor
    · rintro ⟨hj, hgt⟩
      rcases lt_or_ge j n with hlt | hge
      · left
        refine ⟨hj, ?_⟩
        have habs : |(n : ℝ) - j| = (n : ℝ) - j :=
          abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hlt.le))
        rw [habs] at hgt
        have hcast : ((j + D : ℕ) : ℝ) < n := by push_cast; linarith only [hgt]
        exact_mod_cast hcast
      · right
        refine ⟨hj, ?_⟩
        have habs : |(n : ℝ) - j| = (j : ℝ) - n := by
          rw [abs_sub_comm]; exact abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hge))
        rw [habs] at hgt
        have hcast : ((n + D : ℕ) : ℝ) < j := by push_cast; linarith only [hgt]
        exact_mod_cast hcast
    · rintro (⟨hj, hlo⟩ | ⟨hj, hhi⟩)
      · refine ⟨hj, ?_⟩
        have hcast : ((j + D : ℕ) : ℝ) < n := by exact_mod_cast hlo
        have habs : |(n : ℝ) - j| = (n : ℝ) - j :=
          abs_of_nonneg (sub_nonneg.mpr (by push_cast at hcast; linarith))
        rw [habs]; push_cast at hcast; linarith
      · refine ⟨hj, ?_⟩
        have hcast : ((n + D : ℕ) : ℝ) < j := by exact_mod_cast hhi
        have habs : |(n : ℝ) - j| = (j : ℝ) - n := by
          rw [abs_sub_comm]; exact abs_of_nonneg (sub_nonneg.mpr (by push_cast at hcast; linarith))
        rw [habs]; push_cast at hcast; linarith
  have hdisj : Disjoint S_lo S_hi := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    simp only [S_lo, S_hi, mem_filter] at hj1 hj2
    omega
  have hlo_bound : |∑ j ∈ S_lo, g j / |(n : ℝ) - j| | ≤ B / (D : ℝ) := by
    by_cases hbig : D + 1 < n
    · have hS_lo : S_lo = Icc 1 (n - D - 1) := by
        have hnN := (mem_Icc.mp hn).2
        ext j; simp only [S_lo, mem_filter, mem_Icc]; omega
      rw [hS_lo]
      have hcongr : (∑ j ∈ Icc 1 (n - D - 1), g j / |(n : ℝ) - j|) =
          ∑ j ∈ Icc 1 (n - D - 1), g j / ((n : ℝ) - j) :=
        sum_congr rfl fun j hj => by
          rw [abs_of_nonneg (sub_nonneg.mpr (by
            have := (mem_Icc.mp hj).2; exact_mod_cast (show j ≤ n by omega)))]
      rw [hcongr]
      exact abs_sum_far_lower_div_sub_le hB hB0 hD hbig
    · have hempty : S_lo = ∅ := by
        ext j; simp only [S_lo, mem_filter, mem_Icc, notMem_empty, iff_false]; omega
      rw [hempty, sum_empty, abs_zero]
      exact div_nonneg hB0 hD0.le
  have hhi_bound : |∑ j ∈ S_hi, g j / |(n : ℝ) - j| | ≤ B / (D : ℝ) := by
    have hS_hi : S_hi = Ico (n + D + 1) (N + 1) := by
      ext j; simp only [S_hi, mem_filter, mem_Icc, mem_Ico]; omega
    rw [hS_hi]
    have hcongr : (∑ j ∈ Ico (n + D + 1) (N + 1), g j / |(n : ℝ) - j|) =
        ∑ j ∈ Ico (n + D + 1) (N + 1), g j / (-(n : ℝ) + j) :=
      sum_congr rfl fun j hj => by
        have hjlo := (mem_Ico.mp hj).1
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast (show n ≤ j by omega)))]
        congr 1; ring
    rw [hcongr]
    have hab := abs_sum_Ico_div_add_le (r := -(n : ℝ)) hB (n + D + 1) (N + 1)
      (by push_cast; positivity)
    have hden : -(n : ℝ) + (n + D + 1 : ℕ) = (D : ℝ) + 1 := by push_cast; ring
    rw [hden] at hab
    exact hab.trans (div_le_div_of_nonneg_left hB0 hD0 (by linarith))
  rw [hpart, sum_union hdisj]
  calc
    |∑ j ∈ S_lo, g j / |(n : ℝ) - j| + ∑ j ∈ S_hi, g j / |(n : ℝ) - j| | ≤
        |∑ j ∈ S_lo, g j / |(n : ℝ) - j| | + |∑ j ∈ S_hi, g j / |(n : ℝ) - j| | := abs_add_le _ _
    _ ≤ B / D + B / D := add_le_add hlo_bound hhi_bound
    _ = 2 * B / D := by ring

/-- Weighted Schur `L²` inequality for finite kernels majorized entrywise by `U ≥ 0`. -/
theorem sum_sq_abs_majorized_kernel_le' {N : ℕ} (K U : ℕ → ℕ → ℝ) (x w u d : ℕ → ℝ)
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
      · exact sum_congr rfl fun j hj =>
          Real.sq_sqrt (mul_nonneg (hU n hn j hj) (hw j hj).le)
      · refine sum_congr rfl fun j hj => ?_
        rw [mul_pow, Real.sq_sqrt (div_nonneg (hU n hn j hj) (hw j hj).le), sq_abs]
    calc
      (∑ j ∈ Icc 1 N, K n j * x j) ^ 2 ≤
          (∑ j ∈ Icc 1 N, U n j * w j) * ∑ j ∈ Icc 1 N, (U n j / w j) * x j ^ 2 :=
        hsq.trans hcs'
      _ ≤ u n * ∑ j ∈ Icc 1 N, (U n j / w j) * x j ^ 2 :=
        mul_le_mul_of_nonneg_right (hrow n hn)
          (sum_nonneg fun j hj => mul_nonneg (div_nonneg (hU n hn j hj) (hw j hj).le) (sq_nonneg _))
      _ = ∑ j ∈ Icc 1 N, (U n j * (u n / w j)) * x j ^ 2 := by
        rw [mul_sum]; exact sum_congr rfl fun j _ => by ring
  calc
    (∑ n ∈ Icc 1 N, (∑ j ∈ Icc 1 N, K n j * x j) ^ 2) ≤
        ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, (U n j * (u n / w j)) * x j ^ 2 := sum_le_sum hfor_n
    _ = ∑ j ∈ Icc 1 N, (∑ n ∈ Icc 1 N, U n j * (u n / w j)) * x j ^ 2 := by
      rw [sum_comm]; exact sum_congr rfl fun j _ => (sum_mul ..).symm
    _ ≤ ∑ j ∈ Icc 1 N, d j * x j ^ 2 :=
      sum_le_sum fun j hj => mul_le_mul_of_nonneg_right (hcol j hj) (sq_nonneg _)

/-- Uniform `o(1)` bilinear bound on `fullWeilCenterMatrix α N` for `u ∈ conductorSubspace R N`
orthogonal to `conductorSubspace 1 N` and any `y ∈ (conductorSubspace 1 N)ᗮ`. -/
theorem abs_fullWeilCenterMatrix_inner_le_of_mem_conductorSubspace (α : ℝ)
    {R N : ℕ} (hR : 2 ≤ R) (hRN6 : R ^ 6 ≤ N)
    (hlog : 18 * (1 + Real.log R) ≤ Real.log N)
    {u y : EuclideanSpace ℝ (PrimeHorizonIndex N)}
    (hu : u ∈ conductorSubspace R N)
    (hu1 : u ∈ (conductorSubspace 1 N)ᗮ) (hy1 : y ∈ (conductorSubspace 1 N)ᗮ) :
    |⟪Matrix.toEuclideanLin (fullWeilCenterMatrix α N) u, y⟫| ≤
      144 * |α| * (1 + Real.log R) / Real.sqrt (Real.log N) * ‖u‖ * ‖y‖ := by
  have hRN4 : R ^ 4 ≤ N :=
    (Nat.pow_le_pow_right (by omega : 0 < R) (by omega : 4 ≤ 6)).trans hRN6
  have hRN2 : R * R ≤ N := by
    have : R ^ 2 ≤ R ^ 6 := Nat.pow_le_pow_right (by omega : 0 < R) (by omega : 2 ≤ 6)
    simpa only [sq] using this.trans hRN6
  have hN2 : 2 ≤ N := by
    have : 4 ≤ R * R := Nat.mul_le_mul hR hR
    omega
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hL1 : 1 ≤ Real.log N := by
    have hR0 := Real.log_natCast_nonneg R
    linarith only [hlog, hR0]
  have hL : 0 < Real.log N := zero_lt_one.trans_le hL1
  have hsL : 0 < Real.sqrt (Real.log N) := Real.sqrt_pos.mpr hL
  -- Reduce `fullWeilCenterMatrix` to `-α • collarMatrix`.
  let K_col : ℕ → ℕ → ℝ := fun n j => (1 / (N : ℝ)) * archimedeanCenterKernel n j
  have hinner_eq : ⟪Matrix.toEuclideanLin (fullWeilCenterMatrix α N) u, y⟫ =
      -α * ⟪Matrix.toEuclideanLin (horizonKernelMatrix K_col N) u, y⟫ := by
    change ⟪Matrix.toEuclideanLin
      (horizonKernelMatrix (fun n j =>
        (α / N) * (arithmeticPoleKernel n j - archimedeanCenterKernel n j)) N) u, y⟫ = _
    rw [horizonKernelMatrix_bilinear, horizonKernelMatrix_bilinear]
    have hterm (n j : ℕ) :
        primeHorizonExtension y n * primeHorizonExtension u j *
            ((α / N) * (arithmeticPoleKernel n j - archimedeanCenterKernel n j)) =
          (α / N) * (primeHorizonExtension y n * primeHorizonExtension u j *
            arithmeticPoleKernel n j) -
          α * (primeHorizonExtension y n * primeHorizonExtension u j * K_col n j) := by
      dsimp only [K_col]; ring
    simp only [hterm, sum_sub_distrib, ← mul_sum]
    rw [arithmeticPoleKernel_bilinear_eq_zero
      (harmonicSum_eq_zero_of_mem_orthog_one hN2 hu1)
      (harmonicSum_eq_zero_of_mem_orthog_one hN2 hy1)]
    ring
  -- It suffices to bound `‖collarLin u‖ ≤ 144 * (1 + log R) / √(log N) * ‖u‖`.
  let collarLin := Matrix.toEuclideanLin (horizonKernelMatrix K_col N)
  suffices hcol_norm : ‖collarLin u‖ ≤
      144 * (1 + Real.log R) / Real.sqrt (Real.log N) * ‖u‖ by
    rw [hinner_eq, abs_mul, abs_neg]
    calc
      |α| * |⟪collarLin u, y⟫| ≤ |α| * (‖collarLin u‖ * ‖y‖) :=
        mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (abs_nonneg _)
      _ ≤ |α| * ((144 * (1 + Real.log R) / Real.sqrt (Real.log N) * ‖u‖) * ‖y‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hcol_norm (norm_nonneg y)) (abs_nonneg _)
      _ = 144 * |α| * (1 + Real.log R) / Real.sqrt (Real.log N) * ‖u‖ * ‖y‖ := by ring
  -- Split `u = a 1 • v_1 + uTilde`.
  obtain ⟨a, -, hu_eq⟩ := (mem_conductorSubspace_iff (M := R) (N := N) (x := u)).mp hu
  let aTilde : ℕ → ℝ := fun m => if m = 1 then 0 else a m
  let uTilde := ∑ m ∈ Icc 1 R, aTilde m • normalizedRamanujanHorizonVector m N
  have hu_split : u = a 1 • normalizedRamanujanHorizonVector 1 N + uTilde := by
    rw [hu_eq]
    have h1mem : (1 : ℕ) ∈ Icc 1 R := mem_Icc.mpr ⟨le_rfl, by omega⟩
    rw [← add_sum_erase _ _ h1mem]
    congr 1
    dsimp only [uTilde]
    rw [← add_sum_erase _ _ h1mem]
    have hz : aTilde 1 • normalizedRamanujanHorizonVector 1 N = 0 := by simp [aTilde]
    rw [hz, zero_add]
    refine sum_congr rfl fun m hm => ?_
    have hm1 : m ≠ 1 := (mem_erase.mp hm).1
    simp [aTilde, hm1]
  -- Piece 1: `a 1 • v_1`.
  have ha1_le : |a 1| ≤ 36 * (1 + Real.log R) / Real.log N * ‖u‖ := by
    have hlow := (low_band_norm_le_of_mem_orthogonal (by omega : 1 ≤ 1) (by omega : 1 ≤ R)
      hR hRN2 hlog (hu_eq ▸ hu1)).1
    rw [← hu_eq] at hlow
    have h1sq : Real.sqrt (∑ m ∈ Icc 1 1, a m ^ 2) = |a 1| := by
      rw [Icc_self, sum_singleton, Real.sqrt_sq_eq_abs]
    rwa [h1sq] at hlow
  have hv1_col : ‖collarLin (normalizedRamanujanHorizonVector 1 N)‖ ≤
      3 * Real.sqrt (Real.log N) := by
    have hsq : ‖collarLin (normalizedRamanujanHorizonVector 1 N)‖ ^ 2 ≤
        (3 * Real.sqrt (Real.log N)) ^ 2 := by
      rw [← horizonProfileVector_extension (normalizedRamanujanHorizonVector 1 N),
        horizonKernelMatrix_profile_norm_sq]
      have hrow_le : ∀ n ∈ Icc 1 N,
          (∑ j ∈ Icc 1 N, K_col n j *
            primeHorizonExtension (normalizedRamanujanHorizonVector 1 N) j) ^ 2 ≤
          9 * Real.log N / N := by
        intro n hn
        have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
        have hnonneg : 0 ≤ ∑ j ∈ Icc 1 N, K_col n j *
            primeHorizonExtension (normalizedRamanujanHorizonVector 1 N) j :=
          sum_nonneg fun j hj => by
            rw [primeHorizonExtension_coe _ ⟨j, hj⟩]
            change 0 ≤ (1 / (N : ℝ)) * archimedeanCenterKernel n j *
              ((Real.sqrt (Real.log N))⁻¹ * (normalizedRamanujanMode 1 j / Real.sqrt j))
            have hm1 : normalizedRamanujanMode 1 j = 1 := by
              rw [normalizedRamanujanMode, ramanujanMode_one, Nat.totient_one, Nat.cast_one,
                Real.sqrt_one, div_one]
            rw [hm1]
            exact mul_nonneg (mul_nonneg (by positivity) (archimedeanCenterKernel_nonneg n j))
              (by positivity)
        have hrow : (∑ j ∈ Icc 1 N, K_col n j *
            primeHorizonExtension (normalizedRamanujanHorizonVector 1 N) j) ≤
            3 * Real.sqrt (Real.log N) * Real.sqrt n / N := by
          have heq : (∑ j ∈ Icc 1 N, K_col n j *
              primeHorizonExtension (normalizedRamanujanHorizonVector 1 N) j) =
              (1 / (N : ℝ)) * (Real.sqrt (Real.log N))⁻¹ *
                ∑ j ∈ Icc 1 N, archimedeanCenterKernel n j / Real.sqrt j := by
            rw [mul_sum]
            refine sum_congr rfl fun j hj => ?_
            rw [primeHorizonExtension_coe _ ⟨j, hj⟩]
            change (1 / (N : ℝ)) * archimedeanCenterKernel n j *
              ((Real.sqrt (Real.log N))⁻¹ * (normalizedRamanujanMode 1 j / Real.sqrt j)) = _
            have hm1 : normalizedRamanujanMode 1 j = 1 := by
              rw [normalizedRamanujanMode, ramanujanMode_one, Nat.totient_one, Nat.cast_one,
                Real.sqrt_one, div_one]
            rw [hm1]; ring
          rw [heq]
          have hH := sum_archimedeanCenterKernel_div_sqrt_le hn
          have hHN : (harmonic N : ℝ) + 1 ≤ 3 * Real.log N := by
            have hh := harmonic_le_one_add_log N
            linarith only [hh, hL1]
          calc
            (1 / (N : ℝ)) * (Real.sqrt (Real.log N))⁻¹ *
                (∑ j ∈ Icc 1 N, archimedeanCenterKernel n j / Real.sqrt j) ≤
                (1 / (N : ℝ)) * (Real.sqrt (Real.log N))⁻¹ *
                  (Real.sqrt n * (3 * Real.log N)) :=
              mul_le_mul_of_nonneg_left
                (hH.trans (mul_le_mul_of_nonneg_left hHN (Real.sqrt_nonneg _))) (by positivity)
            _ = 3 * Real.sqrt (Real.log N) * Real.sqrt n / N := by
              field_simp [hN0.ne', hsL.ne']
              rw [Real.sq_sqrt hL.le]
              ring
        have hsqn := pow_le_pow_left₀ hnonneg hrow 2
        calc
          _ ≤ (3 * Real.sqrt (Real.log N) * Real.sqrt n / N) ^ 2 := hsqn
          _ = 9 * Real.log N * n / (N : ℝ) ^ 2 := by
            rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hL.le, Real.sq_sqrt (Nat.cast_nonneg n)]
            ring
          _ ≤ 9 * Real.log N * N / (N : ℝ) ^ 2 :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hnN (by positivity)) (sq_nonneg _)
          _ = 9 * Real.log N / N := by field_simp [hN0.ne']
      calc
        (∑ n ∈ Icc 1 N, (∑ j ∈ Icc 1 N, K_col n j *
            primeHorizonExtension (normalizedRamanujanHorizonVector 1 N) j) ^ 2) ≤
            ∑ _n ∈ Icc 1 N, 9 * Real.log N / N := sum_le_sum hrow_le
        _ = (N : ℝ) * (9 * Real.log N / N) := by
          rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        _ = (3 * Real.sqrt (Real.log N)) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hL.le]; field_simp [hN0.ne']; ring
    nlinarith only [hsq, norm_nonneg (collarLin (normalizedRamanujanHorizonVector 1 N)), hsL]
  have hpiece1 : ‖collarLin (a 1 • normalizedRamanujanHorizonVector 1 N)‖ ≤
      108 * (1 + Real.log R) / Real.sqrt (Real.log N) * ‖u‖ := by
    rw [map_smul, norm_smul, Real.norm_eq_abs]
    calc
      |a 1| * ‖collarLin (normalizedRamanujanHorizonVector 1 N)‖ ≤
          (36 * (1 + Real.log R) / Real.log N * ‖u‖) * (3 * Real.sqrt (Real.log N)) :=
        mul_le_mul ha1_le hv1_col (norm_nonneg _) (by
          have := Real.log_natCast_nonneg R; positivity)
      _ = 108 * (1 + Real.log R) / Real.sqrt (Real.log N) * ‖u‖ := by
        field_simp [hL.ne', hsL.ne']
        rw [Real.sq_sqrt hL.le]
        ring
  -- Bounds on `uTilde`.
  have ha_sq : (∑ m ∈ Icc 1 R, aTilde m ^ 2) ≤ 2 * ‖u‖ ^ 2 := by
    have hle : (∑ m ∈ Icc 1 R, aTilde m ^ 2) ≤ ∑ m ∈ Icc 1 R, a m ^ 2 :=
      sum_le_sum fun m _ => by dsimp only [aTilde]; split_ifs <;> simp [sq_nonneg]
    have hr := (half_and_three_halves_riesz_of_log_le hR hRN2 hlog a).1
    rw [← hu_eq] at hr
    linarith only [hle, hr]
  have huTilde_mem : uTilde ∈ conductorSubspace R N :=
    sum_normalizedRamanujanHorizonVector_mem_conductorSubspace R N aTilde
  have huTilde_norm : ‖uTilde‖ ≤ 2 * ‖u‖ := by
    have hr := (half_and_three_halves_riesz_of_log_le hR hRN2 hlog aTilde).2
    have hsq : ‖uTilde‖ ^ 2 ≤ (2 * ‖u‖) ^ 2 := by
      calc
        ‖uTilde‖ ^ 2 ≤ (3 / 2 : ℝ) * ∑ m ∈ Icc 1 R, aTilde m ^ 2 := hr
        _ ≤ (3 / 2 : ℝ) * (2 * ‖u‖ ^ 2) := mul_le_mul_of_nonneg_left ha_sq (by norm_num)
        _ ≤ (2 * ‖u‖) ^ 2 := by nlinarith only [sq_nonneg ‖u‖]
    nlinarith only [hsq, norm_nonneg uTilde, norm_nonneg u]
  have hlin_uTilde : (∑ j ∈ Icc 1 N, ((j : ℝ) / N) * primeHorizonExtension uTilde j ^ 2) ≤
      16 / Real.log N * ‖u‖ ^ 2 := by
    have hm := sum_linear_moment_sq_le_four_div_log hR hRN4 hlog huTilde_mem
    have h4 : ‖uTilde‖ ^ 2 ≤ 4 * ‖u‖ ^ 2 := by
      nlinarith only [huTilde_norm, norm_nonneg uTilde, norm_nonneg u]
    rw [div_mul_eq_mul_div, le_div_iff₀' hL]
    linarith only [hm, h4]
  -- Decompose each row `(collarLin uTilde) n` into sum-half, near-diff (`≤ R^4`), far-diff (`> R^4`).
  let gTilde : ℕ → ℝ := fun j => ∑ m ∈ Icc 1 R, aTilde m * normalizedRamanujanMode m j
  have huTilde_ext : ∀ j ∈ Icc 1 N, primeHorizonExtension uTilde j =
      (Real.sqrt (Real.log N))⁻¹ * (gTilde j / Real.sqrt j) := by
    intro j hj
    rw [primeHorizonExtension_coe _ ⟨j, hj⟩]
    change (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : PrimeHorizonIndex N => ℝ) ⟨j, hj⟩) uTilde = _
    dsimp only [uTilde, gTilde]
    rw [map_sum, sum_div, mul_sum]
    refine sum_congr rfl fun m _ => ?_
    change aTilde m * ((Real.sqrt (Real.log N))⁻¹ * (normalizedRamanujanMode m j / Real.sqrt j)) = _
    ring
  let D := R ^ 4
  have hD0 : 0 < D := pow_pos (by omega : 0 < R) 4
  let y_lin : ℕ → ℝ := fun j => Real.sqrt ((j : ℝ) / N) * |primeHorizonExtension uTilde j|
  have hy_lin_sq : (∑ j ∈ Icc 1 N, y_lin j ^ 2) ≤ 16 / Real.log N * ‖u‖ ^ 2 := by
    have heq : (∑ j ∈ Icc 1 N, y_lin j ^ 2) =
        ∑ j ∈ Icc 1 N, ((j : ℝ) / N) * primeHorizonExtension uTilde j ^ 2 :=
      sum_congr rfl fun j _ => by
        dsimp only [y_lin]
        rw [mul_pow, Real.sq_sqrt (by positivity), sq_abs]
    rw [heq]; exact hlin_uTilde
  -- Row decomposition of `collarLin uTilde`.
  let rowSumHalf : ℕ → ℝ := fun n =>
    ∑ j ∈ (Icc 1 N).erase n,
      (Real.sqrt n * Real.sqrt j / (2 * (N : ℝ) * ((n : ℝ) + j))) * primeHorizonExtension uTilde j
  let K_near : ℕ → ℕ → ℝ := fun n j =>
    if n ≠ j ∧ |(n : ℝ) - j| ≤ D then (1 / 2 : ℝ) / |(n : ℝ) - j| else 0
  let rowNear : ℕ → ℝ := fun n =>
    Real.sqrt ((n : ℝ) / N) * ∑ j ∈ Icc 1 N, K_near n j *
      (Real.sqrt ((j : ℝ) / N) * primeHorizonExtension uTilde j)
  let rowFar : ℕ → ℝ := fun n =>
    (Real.sqrt n / (2 * (N : ℝ) * Real.sqrt (Real.log N))) *
      ∑ j ∈ (Icc 1 N).filter (fun j : ℕ => (D : ℝ) < |(n : ℝ) - j|), gTilde j / |(n : ℝ) - j|
  have hrow_split : ∀ n ∈ Icc 1 N,
      (∑ j ∈ Icc 1 N, K_col n j * primeHorizonExtension uTilde j) =
        rowSumHalf n + rowNear n + rowFar n := by
    intro n hn
    rw [← sum_erase_add (Icc 1 N) (fun j => K_col n j * primeHorizonExtension uTilde j) hn]
    have hdiag : K_col n n * primeHorizonExtension uTilde n = 0 := by
      dsimp only [K_col]; rw [archimedeanCenterKernel_self, mul_zero, zero_mul]
    rw [hdiag, add_zero]
    have hterm_erase : ∀ j ∈ (Icc 1 N).erase n,
        K_col n j * primeHorizonExtension uTilde j =
          (Real.sqrt n * Real.sqrt j / (2 * (N : ℝ) * ((n : ℝ) + j))) *
            primeHorizonExtension uTilde j +
          (Real.sqrt n * Real.sqrt j / (2 * (N : ℝ) * |(n : ℝ) - j|)) *
            primeHorizonExtension uTilde j := by
      intro j hj
      obtain ⟨hjn, hjI⟩ := mem_erase.mp hj
      have h := archimedeanCenterKernel_div_sqrt_mul (mem_Icc.mp hn).1
        (mem_Icc.mp hjI).1 (Ne.symm hjn)
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
      have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hjI).1
      have hsn := (Real.sqrt_pos.mpr hn0).ne'
      have hsj := (Real.sqrt_pos.mpr hj0).ne'
      dsimp only [K_col]
      have hker : archimedeanCenterKernel n j =
          (1 / 2 : ℝ) * (1 / |(n : ℝ) - j| + 1 / ((n : ℝ) + j)) *
            (Real.sqrt n * Real.sqrt j) :=
        (div_eq_iff (mul_ne_zero hsn hsj)).mp h
      have hadd_ne : (n : ℝ) + j ≠ 0 := by positivity
      have hsub_ne : |(n : ℝ) - j| ≠ 0 :=
        abs_ne_zero.mpr (sub_ne_zero.mpr (by exact_mod_cast Ne.symm hjn))
      rw [hker]
      field_simp [hN0.ne', hadd_ne, hsub_ne]
      ring
    rw [sum_congr rfl hterm_erase, sum_add_distrib]
    change rowSumHalf n + _ = rowSumHalf n + rowNear n + rowFar n
    rw [add_assoc]
    congr 1
    -- Split `(Icc 1 N).erase n` into `|(n : ℝ) - j| ≤ D` and `(D : ℝ) < |(n : ℝ) - j|`.
    have near_eq : rowNear n =
        ∑ j ∈ ((Icc 1 N).erase n).filter (fun j : ℕ => |(n : ℝ) - j| ≤ D),
          (Real.sqrt n * Real.sqrt j / (2 * (N : ℝ) * |(n : ℝ) - j|)) *
            primeHorizonExtension uTilde j := by
      dsimp only [rowNear, K_near]
      rw [mul_sum]
      have hsub : ((Icc 1 N).erase n).filter (fun j : ℕ => |(n : ℝ) - j| ≤ D) ⊆ Icc 1 N :=
        fun j hj => (mem_erase.mp (mem_filter.mp hj).1).2
      rw [← sum_subset hsub]
      · refine sum_congr rfl fun j hj => ?_
        obtain ⟨hje, hle⟩ := mem_filter.mp hj
        have hne : n ≠ j := Ne.symm (mem_erase.mp hje).1
        rw [if_pos ⟨hne, hle⟩, Real.sqrt_div (Nat.cast_nonneg n),
          Real.sqrt_div (Nat.cast_nonneg j)]
        field_simp [hN0.ne', (Real.sqrt_pos.mpr hN0).ne']
        rw [Real.sq_sqrt hN0.le]; ring
      · intro j hjI hnot
        have hfalse : ¬(n ≠ j ∧ |(n : ℝ) - j| ≤ D) := by
          rintro ⟨hne, hle⟩
          exact hnot (mem_filter.mpr ⟨mem_erase.mpr ⟨hne.symm, hjI⟩, hle⟩)
        rw [if_neg hfalse, zero_mul, mul_zero]
    have far_eq : rowFar n =
        ∑ j ∈ ((Icc 1 N).erase n).filter (fun j : ℕ => ¬|(n : ℝ) - j| ≤ D),
          (Real.sqrt n * Real.sqrt j / (2 * (N : ℝ) * |(n : ℝ) - j|)) *
            primeHorizonExtension uTilde j := by
      dsimp only [rowFar]
      have hf_eq : ((Icc 1 N).erase n).filter (fun j : ℕ => ¬|(n : ℝ) - j| ≤ D) =
          (Icc 1 N).filter (fun j : ℕ => (D : ℝ) < |(n : ℝ) - j|) := by
        ext j; simp only [mem_filter, mem_erase, not_le]
        constructor
        · rintro ⟨⟨_, hj⟩, hlt⟩; exact ⟨hj, hlt⟩
        · rintro ⟨hj, hlt⟩
          refine ⟨⟨?_, hj⟩, hlt⟩
          intro h; subst h; simp only [sub_self, abs_zero] at hlt
          linarith [show (0 : ℝ) < D by exact_mod_cast hD0]
      rw [hf_eq, mul_sum]
      refine sum_congr rfl fun j hj => ?_
      have hjI := (mem_filter.mp hj).1
      have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hjI).1
      have hsj := (Real.sqrt_pos.mpr hj0).ne'
      rw [huTilde_ext j hjI]
      field_simp [hN0.ne', hsL.ne', hsj]
    rw [near_eq, far_eq, sum_filter_add_sum_filter_not]
  -- Bound 1: `∑ (rowSumHalf n)^2 ≤ 4 / log N * ‖u‖^2`.
  have hsumHalf_sq : (∑ n ∈ Icc 1 N, rowSumHalf n ^ 2) ≤ 4 / Real.log N * ‖u‖ ^ 2 := by
    have hpt : ∀ n ∈ Icc 1 N, rowSumHalf n ^ 2 ≤ (1 / (4 * (N : ℝ))) * ∑ j ∈ Icc 1 N, y_lin j ^ 2 := by
      intro n hn
      have hn1 := (mem_Icc.mp hn).1
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      have habs : |rowSumHalf n| ≤
          (Real.sqrt n / (2 * Real.sqrt N)) * ∑ j ∈ Icc 1 N, (1 / ((n : ℝ) + j)) * y_lin j := by
        dsimp only [rowSumHalf]
        rw [mul_sum]
        have hsub : (Icc 1 N).erase n ⊆ Icc 1 N := erase_subset _ _
        refine (abs_sum_le_sum_abs _ _).trans
          ((sum_le_sum fun j hj => ?_).trans
            (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity))
        dsimp only [y_lin]
        rw [abs_mul, abs_of_nonneg (by positivity :
          0 ≤ Real.sqrt n * Real.sqrt j / (2 * (N : ℝ) * ((n : ℝ) + j))),
          Real.sqrt_div (Nat.cast_nonneg j)]
        have hadd_ne : (n : ℝ) + j ≠ 0 := by positivity
        have hident :
            Real.sqrt n * Real.sqrt j / (2 * (N : ℝ) * ((n : ℝ) + j)) *
                |primeHorizonExtension uTilde j| =
              Real.sqrt n / (2 * Real.sqrt N) *
                (1 / ((n : ℝ) + j) *
                  (Real.sqrt j / Real.sqrt N * |primeHorizonExtension uTilde j|)) := by
          field_simp [hN0.ne', (Real.sqrt_pos.mpr hN0).ne', hadd_ne]
          rw [Real.sq_sqrt hN0.le]; ring
        exact le_of_eq hident
      have hsq := pow_le_pow_left₀ (abs_nonneg _) habs 2
      have h22 : (2 : ℝ) ^ 2 = 4 := by norm_num
      rw [sq_abs, mul_pow, div_pow, mul_pow, Real.sq_sqrt hn0.le, Real.sq_sqrt hN0.le, h22] at hsq
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Icc 1 N)
        (fun j => 1 / ((n : ℝ) + j)) y_lin
      calc
        rowSumHalf n ^ 2 ≤ ((n : ℝ) / (4 * N)) *
            ((∑ j ∈ Icc 1 N, (1 / ((n : ℝ) + j)) ^ 2) * ∑ j ∈ Icc 1 N, y_lin j ^ 2) :=
          hsq.trans (mul_le_mul_of_nonneg_left hcs (by positivity))
        _ ≤ ((n : ℝ) / (4 * N)) * ((1 / (n : ℝ)) * ∑ j ∈ Icc 1 N, y_lin j ^ 2) := by
          refine mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right ?_ (sum_nonneg fun _ _ => sq_nonneg _)) (by positivity)
          simpa only [one_div_pow] using sum_inv_add_sq_le hn1
        _ = (1 / (4 * (N : ℝ))) * ∑ j ∈ Icc 1 N, y_lin j ^ 2 := by
          field_simp [hn0.ne', hN0.ne']
    calc
      (∑ n ∈ Icc 1 N, rowSumHalf n ^ 2) ≤
          ∑ _n ∈ Icc 1 N, (1 / (4 * (N : ℝ))) * ∑ j ∈ Icc 1 N, y_lin j ^ 2 := sum_le_sum hpt
      _ = (1 / 4 : ℝ) * ∑ j ∈ Icc 1 N, y_lin j ^ 2 := by
        rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        field_simp [hN0.ne']
      _ ≤ (1 / 4 : ℝ) * (16 / Real.log N * ‖u‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hy_lin_sq (by norm_num)
      _ = 4 / Real.log N * ‖u‖ ^ 2 := by ring
  -- Bound 2: `∑ (rowNear n)^2 ≤ (20 * (1 + log R))^2 / log N * ‖u‖^2`.
  have hnear_sq : (∑ n ∈ Icc 1 N, rowNear n ^ 2) ≤
      (20 * (1 + Real.log R)) ^ 2 / Real.log N * ‖u‖ ^ 2 := by
    have hK_nonneg : ∀ n ∈ Icc 1 N, ∀ j ∈ Icc 1 N, 0 ≤ K_near n j :=
      fun _ _ _ _ => by dsimp only [K_near]; split_ifs <;> positivity
    have hK_symm : ∀ n j, K_near n j = K_near j n := fun n j => by
      dsimp only [K_near]
      by_cases hne : n = j
      · subst hne; simp
      · have hne' : j ≠ n := Ne.symm hne
        rw [abs_sub_comm (n : ℝ) j]
        simp [hne, hne']
    have hK_row : ∀ n ∈ Icc 1 N, (∑ j ∈ Icc 1 N, K_near n j) ≤ 5 * (1 + Real.log R) := by
      intro n _
      let S_lo := (Icc 1 N).filter (fun j : ℕ => j < n ∧ n - j ≤ D)
      let S_hi := (Icc 1 N).filter (fun j : ℕ => n < j ∧ j - n ≤ D)
      have hsupp : ∀ j ∈ Icc 1 N, j ∉ S_lo ∪ S_hi → K_near n j = 0 := by
        intro j hjI hnot
        dsimp only [K_near]
        rw [if_neg]
        rintro ⟨hne, hle⟩
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · apply hnot; refine mem_union.mpr (Or.inr (mem_filter.mpr ⟨hjI, hlt, ?_⟩))
          rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hlt.le))] at hle
          have hc : ((j - n : ℕ) : ℝ) ≤ D := by
            rw [Nat.cast_sub hlt.le]; exact hle
          exact_mod_cast hc
        · apply hnot; refine mem_union.mpr (Or.inl (mem_filter.mpr ⟨hjI, hgt, ?_⟩))
          rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hgt.le))] at hle
          have hc : ((n - j : ℕ) : ℝ) ≤ D := by
            rw [Nat.cast_sub hgt.le]; exact hle
          exact_mod_cast hc
      have hdisj : Disjoint S_lo S_hi := by
        rw [Finset.disjoint_left]; intro j hj1 hj2
        simp only [S_lo, S_hi, mem_filter] at hj1 hj2; omega
      have hsub : S_lo ∪ S_hi ⊆ Icc 1 N := union_subset (filter_subset _ _) (filter_subset _ _)
      rw [← sum_subset hsub hsupp, sum_union hdisj]
      have hlo : (∑ j ∈ S_lo, K_near n j) ≤ (1 / 2 : ℝ) * (harmonic D : ℝ) := by
        have hinj : ∀ j ∈ S_lo, n - j ∈ Icc 1 D := fun j hj => by
          obtain ⟨_, hlt, hle⟩ := mem_filter.mp hj; exact mem_Icc.mpr ⟨by omega, hle⟩
        calc
          (∑ j ∈ S_lo, K_near n j) = ∑ j ∈ S_lo, (1 / 2 : ℝ) * (1 / ((n - j : ℕ) : ℝ)) := by
            refine sum_congr rfl fun j hj => ?_
            obtain ⟨_, hlt, hle⟩ := mem_filter.mp hj
            have habs : |(n : ℝ) - j| = ((n - j : ℕ) : ℝ) := by
              rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hlt.le)), Nat.cast_sub hlt.le]
            dsimp only [K_near]
            rw [if_pos ⟨by omega, by rw [habs]; exact_mod_cast hle⟩, habs]; ring
          _ = ∑ h ∈ S_lo.image (fun j => n - j), (1 / 2 : ℝ) * (1 / (h : ℝ)) := by
            rw [sum_image]; intro a ha b hb hab
            dsimp only at hab
            obtain ⟨_, hal, _⟩ := mem_filter.mp ha; obtain ⟨_, hbl, _⟩ := mem_filter.mp hb
            omega
          _ ≤ ∑ h ∈ Icc 1 D, (1 / 2 : ℝ) * (1 / (h : ℝ)) :=
            sum_le_sum_of_subset_of_nonneg (image_subset_iff.mpr hinj) fun _ _ _ => by positivity
          _ = (1 / 2 : ℝ) * (harmonic D : ℝ) := by
            rw [← mul_sum, harmonic_eq_sum_Icc]
            congr 1; push_cast; exact sum_congr rfl fun h _ => by simp [one_div]
      have hhi : (∑ j ∈ S_hi, K_near n j) ≤ (1 / 2 : ℝ) * (harmonic D : ℝ) := by
        have hinj : ∀ j ∈ S_hi, j - n ∈ Icc 1 D := fun j hj => by
          obtain ⟨_, hlt, hle⟩ := mem_filter.mp hj; exact mem_Icc.mpr ⟨by omega, hle⟩
        calc
          (∑ j ∈ S_hi, K_near n j) = ∑ j ∈ S_hi, (1 / 2 : ℝ) * (1 / ((j - n : ℕ) : ℝ)) := by
            refine sum_congr rfl fun j hj => ?_
            obtain ⟨_, hlt, hle⟩ := mem_filter.mp hj
            have habs : |(n : ℝ) - j| = ((j - n : ℕ) : ℝ) := by
              rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hlt.le)),
                Nat.cast_sub hlt.le]
            dsimp only [K_near]
            rw [if_pos ⟨by omega, by rw [habs]; exact_mod_cast hle⟩, habs]; ring
          _ = ∑ h ∈ S_hi.image (fun j => j - n), (1 / 2 : ℝ) * (1 / (h : ℝ)) := by
            rw [sum_image]; intro a ha b hb hab
            dsimp only at hab
            obtain ⟨_, hal, _⟩ := mem_filter.mp ha; obtain ⟨_, hbl, _⟩ := mem_filter.mp hb
            omega
          _ ≤ ∑ h ∈ Icc 1 D, (1 / 2 : ℝ) * (1 / (h : ℝ)) :=
            sum_le_sum_of_subset_of_nonneg (image_subset_iff.mpr hinj) fun _ _ _ => by positivity
          _ = (1 / 2 : ℝ) * (harmonic D : ℝ) := by
            rw [← mul_sum, harmonic_eq_sum_Icc]
            congr 1; push_cast; exact sum_congr rfl fun h _ => by simp [one_div]
      have hHD : (harmonic D : ℝ) ≤ 5 * (1 + Real.log R) := by
        have hh := harmonic_le_one_add_log D
        have hlogD : Real.log (D : ℝ) = 4 * Real.log R := by
          dsimp only [D]; rw [Nat.cast_pow, Real.log_pow]; ring
        have hR0 := Real.log_natCast_nonneg R
        linarith only [hh, hlogD, hR0]
      linarith only [hlo, hhi, hHD]
    let M_row := 5 * (1 + Real.log R)
    have hM0 : 0 ≤ M_row := by
      have := Real.log_natCast_nonneg R; dsimp only [M_row]; positivity
    have hschur := sum_sq_abs_majorized_kernel_le' (N := N) K_near K_near
      (fun j => Real.sqrt ((j : ℝ) / N) * primeHorizonExtension uTilde j)
      (fun _ => 1) (fun _ => M_row) (fun _ => M_row ^ 2)
      hK_nonneg
      (fun n hn j hj => le_of_eq (abs_of_nonneg (hK_nonneg n hn j hj)))
      (fun _ _ => zero_lt_one)
      (fun n hn => by simpa only [mul_one] using hK_row n hn)
      (fun j hj => by
        have heq : (∑ n ∈ Icc 1 N, K_near n j * (M_row / 1)) = M_row * ∑ n ∈ Icc 1 N, K_near j n := by
          rw [mul_sum]; exact sum_congr rfl fun n _ => by rw [hK_symm n j]; ring
        rw [heq]
        exact (mul_le_mul_of_nonneg_left (hK_row j hj) hM0).trans_eq (by ring))
    have hpt : ∀ n ∈ Icc 1 N, rowNear n ^ 2 ≤
        (∑ j ∈ Icc 1 N, K_near n j *
          (Real.sqrt ((j : ℝ) / N) * primeHorizonExtension uTilde j)) ^ 2 := by
      intro n hn
      dsimp only [rowNear]
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      have hnN : (n : ℝ) / N ≤ 1 := (div_le_one hN0).mpr (by exact_mod_cast (mem_Icc.mp hn).2)
      exact (mul_le_mul_of_nonneg_right hnN (sq_nonneg _)).trans_eq (one_mul _)
    have hsq_eq : ∀ j : ℕ,
        (Real.sqrt ((j : ℝ) / N) * primeHorizonExtension uTilde j) ^ 2 = y_lin j ^ 2 :=
      fun j => by dsimp only [y_lin]; rw [mul_pow, mul_pow, sq_abs]
    calc
      (∑ n ∈ Icc 1 N, rowNear n ^ 2) ≤
          ∑ j ∈ Icc 1 N, M_row ^ 2 * y_lin j ^ 2 := by
        refine (sum_le_sum hpt).trans (hschur.trans_eq ?_)
        exact sum_congr rfl fun j _ => by rw [hsq_eq]
      _ = M_row ^ 2 * ∑ j ∈ Icc 1 N, y_lin j ^ 2 := (mul_sum ..).symm
      _ ≤ M_row ^ 2 * (16 / Real.log N * ‖u‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hy_lin_sq (sq_nonneg _)
      _ = (20 * (1 + Real.log R)) ^ 2 / Real.log N * ‖u‖ ^ 2 := by
        dsimp only [M_row]; ring
  -- Bound 3: `∑ (rowFar n)^2 ≤ 4 / log N * ‖u‖^2`.
  have hfar_sq : (∑ n ∈ Icc 1 N, rowFar n ^ 2) ≤ 4 / Real.log N * ‖u‖ ^ 2 := by
    let B' := 2 * (R : ℝ) ^ 2 * Real.sqrt (∑ m ∈ Icc 1 R, aTilde m ^ 2)
    have hB'0 : 0 ≤ B' := by dsimp only [B']; positivity
    have hg_Ico : ∀ l k : ℕ, l ≤ k → |∑ j ∈ Ico l k, gTilde j| ≤ B' := by
      intro l k hlk
      have hswap : (∑ j ∈ Ico l k, gTilde j) =
          ∑ m ∈ Icc 1 R, aTilde m * ∑ j ∈ Ico l k, normalizedRamanujanMode m j := by
        dsimp only [gTilde]
        rw [sum_comm]
        exact sum_congr rfl fun m _ => (mul_sum ..).symm
      have hm_bound : ∀ m ∈ Icc 1 R,
          |aTilde m * ∑ j ∈ Ico l k, normalizedRamanujanMode m j| ≤ |aTilde m| * (2 * R) := by
        intro m hm
        obtain ⟨hm1, hmR⟩ := mem_Icc.mp hm
        rcases eq_or_lt_of_le hm1 with rfl | hm2
        · simp [aTilde]
        · rw [abs_mul]
          have hm0 : 0 < m := by omega
          have hper_le := abs_sum_Ico_le_of_periodic hm0 (normalizedRamanujanMode_periodic hm0)
            (sum_range_normalizedRamanujanMode_eq_zero_of_two_le hm2) l k hlk
          have hL1_m := sum_range_abs_normalizedRamanujanMode_le hm0
          have hmR_cast : (m : ℝ) ≤ R := by exact_mod_cast hmR
          exact mul_le_mul_of_nonneg_left (by linarith only [hper_le, hL1_m, hmR_cast]) (abs_nonneg _)
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Icc 1 R) (fun m => |aTilde m|) (fun _ => (1 : ℝ))
      simp only [mul_one, sq_abs, one_pow, sum_const, Nat.card_Icc, Nat.add_sub_cancel,
        nsmul_eq_mul] at hcs
      have hsum_abs : (∑ m ∈ Icc 1 R, |aTilde m|) ≤
          (R : ℝ) * Real.sqrt (∑ m ∈ Icc 1 R, aTilde m ^ 2) := by
        have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast (show 1 ≤ R by omega)
        have hsq : (∑ m ∈ Icc 1 R, |aTilde m|) ^ 2 ≤
            ((R : ℝ) * Real.sqrt (∑ m ∈ Icc 1 R, aTilde m ^ 2)) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _)]
          have hRR : (R : ℝ) ≤ (R : ℝ) ^ 2 := by nlinarith only [hR1]
          exact hcs.trans ((mul_comm _ _).trans_le
            (mul_le_mul_of_nonneg_right hRR (sum_nonneg fun _ _ => sq_nonneg _)))
        have hrhs0 : 0 ≤ (R : ℝ) * Real.sqrt (∑ m ∈ Icc 1 R, aTilde m ^ 2) := by positivity
        nlinarith only [hsq, hrhs0]
      rw [hswap]
      calc
        |∑ m ∈ Icc 1 R, aTilde m * ∑ j ∈ Ico l k, normalizedRamanujanMode m j| ≤
            ∑ m ∈ Icc 1 R, |aTilde m| * (2 * R) :=
          (abs_sum_le_sum_abs _ _).trans (sum_le_sum hm_bound)
        _ = (2 * (R : ℝ)) * ∑ m ∈ Icc 1 R, |aTilde m| := by rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
        _ ≤ (2 * (R : ℝ)) * ((R : ℝ) * Real.sqrt (∑ m ∈ Icc 1 R, aTilde m ^ 2)) :=
          mul_le_mul_of_nonneg_left hsum_abs (by positivity)
        _ = B' := by dsimp only [B']; ring
    have h2BD : 2 * B' / (D : ℝ) ≤ 2 * ‖u‖ := by
      have hR2 : (2 : ℝ) ≤ R := by exact_mod_cast hR
      have hR0 : (0 : ℝ) < R := by positivity
      have hsqrt_le : Real.sqrt (∑ m ∈ Icc 1 R, aTilde m ^ 2) ≤ 2 * ‖u‖ := by
        have h4 : (∑ m ∈ Icc 1 R, aTilde m ^ 2) ≤ (2 * ‖u‖) ^ 2 := by
          nlinarith only [ha_sq, sq_nonneg ‖u‖]
        exact (Real.sqrt_le_sqrt h4).trans_eq (Real.sqrt_sq (by positivity))
      have hquot : 2 * B' / (D : ℝ) = (4 / (R : ℝ) ^ 2) * Real.sqrt (∑ m ∈ Icc 1 R, aTilde m ^ 2) := by
        dsimp only [B', D]; rw [Nat.cast_pow]; field_simp [hR0.ne']; ring
      have hfrac1 : 4 / (R : ℝ) ^ 2 ≤ 1 := by
        rw [div_le_one (sq_pos_of_pos hR0)]; nlinarith only [hR2]
      rw [hquot]
      calc
        (4 / (R : ℝ) ^ 2) * Real.sqrt (∑ m ∈ Icc 1 R, aTilde m ^ 2) ≤
            1 * (2 * ‖u‖) :=
          mul_le_mul hfrac1 hsqrt_le (Real.sqrt_nonneg _) zero_le_one
        _ = 2 * ‖u‖ := one_mul _
    have hpt : ∀ n ∈ Icc 1 N, rowFar n ^ 2 ≤ (1 / ((N : ℝ) * Real.log N)) * ‖u‖ ^ 2 := by
      intro n hn
      have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
      have habs : |rowFar n| ≤ (Real.sqrt n / (2 * (N : ℝ) * Real.sqrt (Real.log N))) * (2 * ‖u‖) := by
        dsimp only [rowFar]
        rw [abs_mul, abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left
          ((abs_sum_far_erase_div_abs_sub_le hn hD0 hB'0 hg_Ico).trans h2BD) (by positivity)
      have hsq := pow_le_pow_left₀ (abs_nonneg _) habs 2
      rw [sq_abs] at hsq
      calc
        rowFar n ^ 2 ≤ ((Real.sqrt n / (2 * (N : ℝ) * Real.sqrt (Real.log N))) * (2 * ‖u‖)) ^ 2 := hsq
        _ = ((n : ℝ) / ((N : ℝ) ^ 2 * Real.log N)) * ‖u‖ ^ 2 := by
          rw [mul_pow, div_pow, mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n),
            Real.sq_sqrt hL.le]
          field_simp [hN0.ne', hL.ne']
        _ ≤ ((N : ℝ) / ((N : ℝ) ^ 2 * Real.log N)) * ‖u‖ ^ 2 :=
          mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_right hnN (by positivity)) (sq_nonneg _)
        _ = (1 / ((N : ℝ) * Real.log N)) * ‖u‖ ^ 2 := by field_simp [hN0.ne', hL.ne']
    calc
      (∑ n ∈ Icc 1 N, rowFar n ^ 2) ≤
          ∑ _n ∈ Icc 1 N, (1 / ((N : ℝ) * Real.log N)) * ‖u‖ ^ 2 := sum_le_sum hpt
      _ = (1 / Real.log N) * ‖u‖ ^ 2 := by
        rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        field_simp [hN0.ne', hL.ne']
      _ ≤ 4 / Real.log N * ‖u‖ ^ 2 := by
        have hpos : 0 ≤ 1 / Real.log N * ‖u‖ ^ 2 := by positivity
        nlinarith only [hpos, (by ring :
          4 / Real.log N * ‖u‖ ^ 2 = 4 * (1 / Real.log N * ‖u‖ ^ 2))]
  -- Combine the 3 row pieces of `collarLin uTilde`.
  have huTilde_col : ‖collarLin uTilde‖ ≤
      36 * (1 + Real.log R) / Real.sqrt (Real.log N) * ‖u‖ := by
    have hrhs0 : 0 ≤ 36 * (1 + Real.log R) / Real.sqrt (Real.log N) * ‖u‖ := by
      have := Real.log_natCast_nonneg R; positivity
    have hsq : ‖collarLin uTilde‖ ^ 2 ≤
        (36 * (1 + Real.log R) / Real.sqrt (Real.log N) * ‖u‖) ^ 2 := by
      rw [← horizonProfileVector_extension uTilde, horizonKernelMatrix_profile_norm_sq]
      have h3 : ∀ a b c : ℝ, (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := fun a b c => by
        nlinarith only [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
      have hpt : ∀ n ∈ Icc 1 N,
          (∑ j ∈ Icc 1 N, K_col n j * primeHorizonExtension uTilde j) ^ 2 ≤
            3 * (rowSumHalf n ^ 2 + rowNear n ^ 2 + rowFar n ^ 2) := by
        intro n hn; rw [hrow_split n hn]; exact h3 _ _ _
      have h1R : 1 ≤ 1 + Real.log R := by
        have := Real.log_natCast_nonneg R; linarith
      have h1R_sq : 1 ≤ (1 + Real.log R) ^ 2 := by nlinarith only [h1R]
      calc
        (∑ n ∈ Icc 1 N, (∑ j ∈ Icc 1 N, K_col n j * primeHorizonExtension uTilde j) ^ 2) ≤
            3 * ((∑ n ∈ Icc 1 N, rowSumHalf n ^ 2) +
              (∑ n ∈ Icc 1 N, rowNear n ^ 2) + (∑ n ∈ Icc 1 N, rowFar n ^ 2)) := by
          refine (sum_le_sum hpt).trans_eq ?_
          rw [← mul_sum, sum_add_distrib, sum_add_distrib]
        _ ≤ 3 * (4 / Real.log N * ‖u‖ ^ 2 +
              (20 * (1 + Real.log R)) ^ 2 / Real.log N * ‖u‖ ^ 2 +
              4 / Real.log N * ‖u‖ ^ 2) := by
          linarith only [hsumHalf_sq, hnear_sq, hfar_sq]
        _ = (24 + 1200 * (1 + Real.log R) ^ 2) / Real.log N * ‖u‖ ^ 2 := by ring
        _ ≤ (1296 * (1 + Real.log R) ^ 2) / Real.log N * ‖u‖ ^ 2 := by
          refine mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right ?_ hL.le) (sq_nonneg _)
          linarith only [h1R_sq]
        _ = (36 * (1 + Real.log R) / Real.sqrt (Real.log N) * ‖u‖) ^ 2 := by
          rw [mul_pow, div_pow, mul_pow, Real.sq_sqrt hL.le]; ring
    nlinarith only [hsq, norm_nonneg (collarLin uTilde), hrhs0]
  -- Combine `a 1 • v_1` and `uTilde`.
  conv_lhs => rw [hu_split, map_add]
  calc
    ‖collarLin (a 1 • normalizedRamanujanHorizonVector 1 N) + collarLin uTilde‖ ≤
        ‖collarLin (a 1 • normalizedRamanujanHorizonVector 1 N)‖ + ‖collarLin uTilde‖ :=
      norm_add_le _ _
    _ ≤ 108 * (1 + Real.log R) / Real.sqrt (Real.log N) * ‖u‖ +
          36 * (1 + Real.log R) / Real.sqrt (Real.log N) * ‖u‖ :=
      add_le_add hpiece1 huTilde_col
    _ = 144 * (1 + Real.log R) / Real.sqrt (Real.log N) * ‖u‖ := by ring

/-! ### 3. Separated cross-error matrix bounds -/

/-- Whole-space operator norm bound for `separatedCrossErrorMatrix φ c N` at every overlap `c > 0`. -/
theorem norm_separatedCrossErrorMatrix_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM_int : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc0 : 0 < c) {N : ℕ} (hN : 1 ≤ N)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ‖Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) x‖ ≤
      4 * (152 * (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2)) * c ^ 2 * ‖x‖ := by
  let K₀ := 152 * (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2)
  have hK₀ : 0 ≤ K₀ := by dsimp only [K₀]; positivity
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  let K : ℕ → ℕ → ℝ := fun n j =>
    if 2 * (c / N) < |Real.log j - Real.log n| then
      atomCrossErrorKernel (atomDilate φ (c / N)) n j else 0
  let U : ℕ → ℕ → ℝ := fun n j =>
    (K₀ * (c / N) ^ 2) * (max (n : ℝ) j) ^ 2 / |(n : ℝ) - j| ^ 2
  have hU_nonneg : ∀ n ∈ Icc 1 N, ∀ j ∈ Icc 1 N, 0 ≤ U n j :=
    fun _ _ _ _ => by dsimp only [U]; positivity
  have hU_symm : ∀ n j, U n j = U j n := fun n j => by
    dsimp only [U]; rw [max_comm, abs_sub_comm]
  have hU_row : ∀ n ∈ Icc 1 N, (∑ j ∈ Icc 1 N, U n j) ≤ 4 * K₀ * c ^ 2 := by
    intro n hn
    have h1 := sum_abs_kernel_le_of_integer_distance (K := K₀ * (c / N) ^ 2) (E := U)
      (by positivity) (fun a _ b _ => by rw [abs_of_nonneg (by dsimp only [U]; positivity)]) hn
    have hsum : (∑ j ∈ Icc 1 N, U n j) = ∑ j ∈ Icc 1 N, |U n j| :=
      sum_congr rfl fun j hj => (abs_of_nonneg (hU_nonneg n hn j hj)).symm
    rw [hsum]
    exact h1.trans_eq (by field_simp [hN0.ne'])
  have hschur := sum_sq_abs_majorized_kernel_le' (N := N) K U
    (primeHorizonExtension x)
    (fun _ => 1) (fun _ => 4 * K₀ * c ^ 2) (fun _ => (4 * K₀ * c ^ 2) ^ 2)
    hU_nonneg
    (fun n hn j hj => abs_separatedCrossError_le hφ hsupp hM_int hc0 hN hn hj)
    (fun _ _ => zero_lt_one)
    (fun n hn => by simpa only [mul_one] using hU_row n hn)
    (fun j hj => by
      have h1 : (∑ n ∈ Icc 1 N, U n j * (4 * K₀ * c ^ 2 / 1)) =
          (4 * K₀ * c ^ 2) * ∑ n ∈ Icc 1 N, U j n := by
        rw [mul_sum]; exact sum_congr rfl fun n _ => by rw [hU_symm n j]; ring
      rw [h1]
      exact (mul_le_mul_of_nonneg_left (hU_row j hj) (by positivity)).trans_eq (by ring))
  have hnorm_sq : ‖Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) x‖ ^ 2 ≤
      (4 * K₀ * c ^ 2 * ‖x‖) ^ 2 := by
    change ‖Matrix.toEuclideanLin (horizonKernelMatrix K N) x‖ ^ 2 ≤ _
    rw [← horizonProfileVector_extension x, horizonKernelMatrix_profile_norm_sq,
      horizonProfileVector_extension]
    calc
      (∑ n ∈ Icc 1 N, (∑ j ∈ Icc 1 N, K n j * primeHorizonExtension x j) ^ 2) ≤
          ∑ j ∈ Icc 1 N, (4 * K₀ * c ^ 2) ^ 2 * primeHorizonExtension x j ^ 2 := hschur
      _ = (4 * K₀ * c ^ 2) ^ 2 * ∑ j ∈ Icc 1 N, primeHorizonExtension x j ^ 2 := (mul_sum ..).symm
      _ = (4 * K₀ * c ^ 2 * ‖x‖) ^ 2 := by rw [sum_primeHorizonExtension_sq, mul_pow]
  have hrhs0 : 0 ≤ 4 * K₀ * c ^ 2 * ‖x‖ := by positivity
  nlinarith only [hnorm_sq, norm_nonneg (Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) x),
    hrhs0]

/-- Subspace `O(c^2 / log N)` quadratic bound for `separatedCrossErrorMatrix φ c N` on
`conductorSubspace R N` (`R ^ 4 ≤ N`). -/
theorem abs_separatedCrossErrorMatrix_inner_le_of_mem_conductorSubspace {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ t, t ∉ Set.Icc 0 1 → φ t = 0)
    (hM_int : 0 < ∫ t, φ t ^ 2) {c : ℝ} (hc0 : 0 < c)
    {R N : ℕ} (hR : 2 ≤ R) (hRN4 : R ^ 4 ≤ N)
    (hlog : 18 * (1 + Real.log R) ≤ Real.log N)
    {u : EuclideanSpace ℝ (PrimeHorizonIndex N)} (hu : u ∈ conductorSubspace R N) :
    |⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) u, u⟫| ≤
      36 * (152 * (∫ t, |φ t|) ^ 2 / (∫ t, φ t ^ 2)) * c ^ 2 / Real.log N * ‖u‖ ^ 2 := by
  let K₀ := 152 * (∫ t, |φ t|) ^ 2 / (∫ t, φ t ^ 2)
  have hK₀ : 0 ≤ K₀ := by dsimp only [K₀]; positivity
  have hN1 : 1 ≤ N := (pow_pos (by omega : 0 < R) 4).trans_le hRN4
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hL : 0 < Real.log N := by
    have hR0 := Real.log_natCast_nonneg R
    linarith only [hlog, hR0]
  let K : ℕ → ℕ → ℝ := fun n j =>
    if 2 * (c / N) < |Real.log j - Real.log n| then
      atomCrossErrorKernel (atomDilate φ (c / N)) n j else 0
  have hmax_sq : ∀ x y : ℝ, (max x y) ^ 2 ≤ 2 * x * y + 2 * |x - y| ^ 2 := by
    intro x y
    rw [sq_abs]
    rcases le_total x y with hxy | hyx
    · rw [max_eq_right hxy]
      nlinarith only [sq_nonneg (x - y), sq_nonneg x]
    · rw [max_eq_left hyx]
      nlinarith only [sq_nonneg (x - y), sq_nonneg y]
  have hK_entry : ∀ n ∈ Icc 1 N, ∀ j ∈ Icc 1 N,
      |K n j| ≤ 2 * K₀ * c ^ 2 *
          (((n : ℝ) / N) * ((j : ℝ) / N) / |(n : ℝ) - j| ^ 2) +
        2 * K₀ * (c / N) ^ 2 := by
    intro n hn j hj
    by_cases hnj : n = j
    · subst j
      have hnot : ¬(2 * (c / N) < |Real.log n - Real.log n|) := by
        rw [sub_self, abs_zero]; exact not_lt.mpr (by positivity)
      dsimp only [K]
      rw [if_neg hnot, abs_zero]
      positivity
    · have hd_ne : |(n : ℝ) - j| ≠ 0 :=
        abs_ne_zero.mpr (sub_ne_zero.mpr (by exact_mod_cast hnj))
      have hd0 : 0 < |(n : ℝ) - j| ^ 2 := sq_pos_of_ne_zero hd_ne
      have hb := abs_separatedCrossError_le hφ hsupp hM_int hc0 hN1 hn hj
      calc
        |K n j| ≤ (K₀ * (c / N) ^ 2) * (max (n : ℝ) j) ^ 2 / |(n : ℝ) - j| ^ 2 := hb
        _ ≤ (K₀ * (c / N) ^ 2) * (2 * (n : ℝ) * j + 2 * |(n : ℝ) - j| ^ 2) / |(n : ℝ) - j| ^ 2 :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hmax_sq n j) (by positivity)) hd0.le
        _ = 2 * K₀ * c ^ 2 *
              (((n : ℝ) / N) * ((j : ℝ) / N) / |(n : ℝ) - j| ^ 2) +
            2 * K₀ * (c / N) ^ 2 := by
          field_simp [hN0.ne', hd_ne]; ring
  change |⟪Matrix.toEuclideanLin (horizonKernelMatrix K N) u, u⟫| ≤ _
  rw [horizonKernelMatrix_inner]
  let y : ℕ → ℝ := fun n => ((n : ℝ) / N) * |primeHorizonExtension u n|
  have hy_sq : (∑ n ∈ Icc 1 N, y n ^ 2) ≤ 4 / Real.log N * ‖u‖ ^ 2 := by
    have hpt : ∀ n ∈ Icc 1 N, y n ^ 2 ≤ ((n : ℝ) / N) * primeHorizonExtension u n ^ 2 := by
      intro n hn
      have hnN : (n : ℝ) / N ≤ 1 := (div_le_one hN0).mpr (by exact_mod_cast (mem_Icc.mp hn).2)
      have hn0 : 0 ≤ (n : ℝ) / N := by positivity
      dsimp only [y]
      rw [mul_pow, sq_abs]
      have hsq : ((n : ℝ) / N) ^ 2 ≤ (n : ℝ) / N := by nlinarith only [hnN, hn0]
      exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    have hm := sum_linear_moment_sq_le_four_div_log hR hRN4 hlog hu
    rw [le_div_iff₀' hL]
    exact (mul_le_mul_of_nonneg_left (sum_le_sum hpt) hL.le).trans hm
  have hpart1 :
      (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, y n * y j * (1 / |(n : ℝ) - j| ^ 2)) ≤
        4 * ∑ n ∈ Icc 1 N, y n ^ 2 := by
    have hschur := finite_weighted_schur_row_potential (Icc 1 N) y (fun _ => (1 : ℝ))
      (fun n j => 1 / |(n : ℝ) - j| ^ 2) (fun _ _ => zero_lt_one)
      (fun _ _ _ _ => by positivity)
      (fun n _ j _ => by rw [abs_sub_comm])
    simp only [div_one, mul_one] at hschur
    calc
      (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, y n * y j * (1 / |(n : ℝ) - j| ^ 2)) ≤
          ∑ n ∈ Icc 1 N, y n ^ 2 * ∑ j ∈ Icc 1 N, 1 / |(n : ℝ) - j| ^ 2 := hschur
      _ ≤ ∑ n ∈ Icc 1 N, y n ^ 2 * 4 :=
        sum_le_sum fun n _ =>
          mul_le_mul_of_nonneg_left (sum_inv_sq_integer_distance_le_four N n) (sq_nonneg _)
      _ = 4 * ∑ n ∈ Icc 1 N, y n ^ 2 := by rw [← sum_mul]; ring
  have hpart2 : (∑ n ∈ Icc 1 N, |primeHorizonExtension u n|) ^ 2 ≤ (N : ℝ) * ‖u‖ ^ 2 := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Icc 1 N)
      (fun n => |primeHorizonExtension u n|) (fun _ => (1 : ℝ))
    simp only [mul_one, sq_abs, one_pow, sum_const, Nat.card_Icc, Nat.add_sub_cancel,
      nsmul_eq_mul, sum_primeHorizonExtension_sq] at hcs
    linarith only [hcs]
  have hlog_le_N : Real.log N ≤ N := by
    linarith only [Real.log_le_sub_one_of_pos hN0]
  have hinv_N : 1 / (N : ℝ) ≤ 1 / Real.log N :=
    one_div_le_one_div_of_le hL hlog_le_N
  calc
    |∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, primeHorizonExtension u n * primeHorizonExtension u j * K n j| ≤
        ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
          |primeHorizonExtension u n| * |primeHorizonExtension u j| * |K n j| := by
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n _ => ?_)
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
      rw [abs_mul, abs_mul]
    _ ≤ ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
          |primeHorizonExtension u n| * |primeHorizonExtension u j| *
            (2 * K₀ * c ^ 2 * (((n : ℝ) / N) * ((j : ℝ) / N) / |(n : ℝ) - j| ^ 2) +
              2 * K₀ * (c / N) ^ 2) :=
      sum_le_sum fun n hn => sum_le_sum fun j hj =>
        mul_le_mul_of_nonneg_left (hK_entry n hn j hj) (by positivity)
    _ = 2 * K₀ * c ^ 2 * (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, y n * y j * (1 / |(n : ℝ) - j| ^ 2)) +
          2 * K₀ * (c / N) ^ 2 * (∑ n ∈ Icc 1 N, |primeHorizonExtension u n|) ^ 2 := by
      have hterm_eq : ∀ n j,
          |primeHorizonExtension u n| * |primeHorizonExtension u j| *
              (2 * K₀ * c ^ 2 * (((n : ℝ) / N) * ((j : ℝ) / N) / |(n : ℝ) - j| ^ 2) +
                2 * K₀ * (c / N) ^ 2) =
            2 * K₀ * c ^ 2 * (y n * y j * (1 / |(n : ℝ) - j| ^ 2)) +
              2 * K₀ * (c / N) ^ 2 *
                (|primeHorizonExtension u n| * |primeHorizonExtension u j|) := by
        intro n j; dsimp only [y]; ring
      simp_rw [hterm_eq, sum_add_distrib, ← mul_sum]
      congr 2
      rw [pow_two, sum_mul]
      exact sum_congr rfl fun n _ => (mul_sum ..).symm
    _ ≤ 2 * K₀ * c ^ 2 * (4 * (4 / Real.log N * ‖u‖ ^ 2)) +
          2 * K₀ * (c / N) ^ 2 * ((N : ℝ) * ‖u‖ ^ 2) :=
      add_le_add
        (mul_le_mul_of_nonneg_left
          (hpart1.trans (mul_le_mul_of_nonneg_left hy_sq (by norm_num))) (by positivity))
        (mul_le_mul_of_nonneg_left hpart2 (by positivity))
    _ = 32 * K₀ * c ^ 2 / Real.log N * ‖u‖ ^ 2 +
          2 * K₀ * c ^ 2 * (1 / (N : ℝ)) * ‖u‖ ^ 2 := by
      field_simp [hN0.ne', hL.ne']; ring
    _ ≤ 32 * K₀ * c ^ 2 / Real.log N * ‖u‖ ^ 2 +
          2 * K₀ * c ^ 2 * (1 / Real.log N) * ‖u‖ ^ 2 :=
      add_le_add le_rfl
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hinv_N (by positivity)) (sq_nonneg _))
    _ ≤ 36 * K₀ * c ^ 2 / Real.log N * ‖u‖ ^ 2 := by
      have : 0 ≤ K₀ * c ^ 2 / Real.log N * ‖u‖ ^ 2 := by positivity
      linarith only [this, (by ring : 2 * K₀ * c ^ 2 * (1 / Real.log N) * ‖u‖ ^ 2 =
        2 * (K₀ * c ^ 2 / Real.log N * ‖u‖ ^ 2)),
        (by ring : 32 * K₀ * c ^ 2 / Real.log N * ‖u‖ ^ 2 =
          32 * (K₀ * c ^ 2 / Real.log N * ‖u‖ ^ 2)),
        (by ring : 36 * K₀ * c ^ 2 / Real.log N * ‖u‖ ^ 2 =
          36 * (K₀ * c ^ 2 / Real.log N * ‖u‖ ^ 2))]

/-! ### 4. Logarithmic divisor-jet packet and orthogonal prime cross-pairing -/

/-- Conductor coefficient of `k ∈ Icc 1 M` in the collective logarithmic divisor jet of `a`. -/
def divisorJetCoeff (M : ℕ) (a : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ m ∈ Icc 1 M, if k ∈ m.divisors then
    a m * (ramanujanJetConductorWeight m k * Real.sqrt (k.totient : ℝ) / Real.sqrt (m.totient : ℝ))
  else 0

/-- Horizon vector representing `(log N)^{-1/2} n^{-1/2} ∑_{m=1}^M a_m ramanujanLogDivisorJet m n / √φ(m)`
inside `conductorSubspace M N`. -/
def divisorJetHorizonVector (M N : ℕ) (a : ℕ → ℝ) : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  ∑ k ∈ Icc 1 M, divisorJetCoeff M a k • normalizedRamanujanHorizonVector k N

theorem divisorJetHorizonVector_mem_conductorSubspace (M N : ℕ) (a : ℕ → ℝ) :
    divisorJetHorizonVector M N a ∈ conductorSubspace M N :=
  sum_normalizedRamanujanHorizonVector_mem_conductorSubspace M N _

/-- Exact coordinate evaluation of `divisorJetHorizonVector`. -/
theorem divisorJetHorizonVector_apply (M N : ℕ) (a : ℕ → ℝ) (n : PrimeHorizonIndex N) :
    divisorJetHorizonVector M N a n =
      (Real.sqrt (Real.log N))⁻¹ * poleVector n *
        ∑ m ∈ Icc 1 M, a m * (ramanujanLogDivisorJet m n / Real.sqrt (m.totient : ℝ)) := by
  change (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : PrimeHorizonIndex N => ℝ) n)
    (divisorJetHorizonVector M N a) = _
  dsimp only [divisorJetHorizonVector]
  rw [map_sum]
  have hproj : ∀ k ∈ Icc 1 M,
      (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : PrimeHorizonIndex N => ℝ) n)
          (divisorJetCoeff M a k • normalizedRamanujanHorizonVector k N) =
        (Real.sqrt (Real.log N))⁻¹ * poleVector n *
          (divisorJetCoeff M a k * normalizedRamanujanMode k n) := by
    intro k _
    change divisorJetCoeff M a k *
      ((Real.sqrt (Real.log N))⁻¹ * (normalizedRamanujanMode k n / Real.sqrt (n : ℕ))) = _
    unfold poleVector
    ring
  rw [sum_congr rfl hproj, ← mul_sum]
  congr 1
  dsimp only [divisorJetCoeff]
  simp_rw [sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun m hm => ?_
  obtain ⟨hm1, hmM⟩ := mem_Icc.mp hm
  have hm0 : 0 < m := hm1
  have hdiv_sub : m.divisors ⊆ Icc 1 M := fun k hk =>
    mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hk,
      (Nat.le_of_dvd hm0 (Nat.dvd_of_mem_divisors hk)).trans hmM⟩
  have hsum_k :
      (∑ k ∈ Icc 1 M,
        (if k ∈ m.divisors then
          a m * (ramanujanJetConductorWeight m k * Real.sqrt (k.totient : ℝ) /
            Real.sqrt (m.totient : ℝ))
        else 0) * normalizedRamanujanMode k n) =
      ∑ k ∈ m.divisors,
        a m * (ramanujanJetConductorWeight m k * Real.sqrt (k.totient : ℝ) /
          Real.sqrt (m.totient : ℝ)) * normalizedRamanujanMode k n := by
    rw [← sum_subset hdiv_sub]
    · exact sum_congr rfl fun k hk => by rw [if_pos hk]
    · intro k _ hk; rw [if_neg hk, zero_mul]
  rw [hsum_k, ramanujanLogDivisorJet_eq_weighted_conductors hm0, sum_div, mul_sum]
  refine sum_congr rfl fun k hk => ?_
  have hk0 : 0 < k := Nat.pos_of_mem_divisors hk
  have hsφk : Real.sqrt (k.totient : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr hk0)).ne'
  rw [normalizedRamanujanMode_eq_coefficient hk0]
  field_simp [hsφk]

/-- Uniform `O(1 + log M)` `L²` norm bound on `divisorJetHorizonVector M N a`. -/
theorem exists_divisorJetHorizonVector_norm_le :
    ∃ C_jet : ℝ, 0 < C_jet ∧
      ∀ {M N : ℕ}, 2 ≤ M → M * M ≤ N → 18 * (1 + Real.log M) ≤ Real.log N →
      ∀ a : ℕ → ℝ,
        ‖divisorJetHorizonVector M N a‖ ≤
          C_jet * (1 + Real.log M) * Real.sqrt (∑ m ∈ Icc 1 M, a m ^ 2) := by
  obtain ⟨C_env, hC_env_pos, hC_env⟩ := exists_primeMertensRemainder_log_envelope
  let C_mert := C_env + |Real.eulerMascheroniConstant| + 1
  have hC_mert_pos : 1 ≤ C_mert := by
    dsimp only [C_mert]
    have := abs_nonneg Real.eulerMascheroniConstant
    linarith only [hC_env_pos, this]
  let C_jet := 4 * C_mert + 4
  refine ⟨C_jet, by dsimp only [C_jet]; positivity, ?_⟩
  intro M N hM hMN hlog a
  have hmert_le : ∀ y : ℕ, 1 ≤ y → mertensSum y ≤ Real.log y + C_mert := by
    intro y hy
    have hprof := hC_env y hy
    have hden : 1 ≤ 1 + Real.log y := by have := Real.log_natCast_nonneg y; linarith
    have hle : primeMertensRemainderProfile y ≤ C_env :=
      hprof.trans (div_le_self hC_env_pos.le hden)
    unfold primeMertensRemainderProfile at hle
    have h1y : 0 ≤ 1 / (y : ℝ) := by positivity
    have habs : |mertensSum y - Real.log y + Real.eulerMascheroniConstant| ≤ C_env := by
      linarith only [hle, h1y]
    have hup := (le_abs_self _).trans habs
    have hγ := neg_abs_le Real.eulerMascheroniConstant
    dsimp only [C_mert]
    linarith only [hup, hγ]
  -- Bound `∑_{k=1}^M (divisorJetCoeff M a k)^2`.
  have hcoeff_sq : (∑ k ∈ Icc 1 M, divisorJetCoeff M a k ^ 2) ≤
      (2 + 4 * C_mert + 4) * (1 + Real.log M) ^ 2 * ∑ m ∈ Icc 1 M, a m ^ 2 := by
    let offCoeff : ℕ → ℝ := fun k =>
      ∑ m ∈ (Icc 1 M).filter (fun m => k ∈ m.divisors),
        a m * (Λ (m / k) * Real.sqrt (k.totient : ℝ) / Real.sqrt (m.totient : ℝ))
    have hsplit_k : ∀ k ∈ Icc 1 M,
        divisorJetCoeff M a k = a k * Real.log k + offCoeff k := by
      intro k hk
      obtain ⟨hk1, _⟩ := mem_Icc.mp hk
      have hk_div : k ∈ k.divisors := Nat.mem_divisors.mpr ⟨dvd_rfl, by omega⟩
      have hsφk : Real.sqrt (k.totient : ℝ) ≠ 0 :=
        (Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr hk1)).ne'
      dsimp only [divisorJetCoeff, offCoeff, ramanujanJetConductorWeight]
      rw [← sum_filter]
      have hterm : ∀ m ∈ (Icc 1 M).filter (fun m => k ∈ m.divisors),
          a m * (((if k = m then Real.log m else 0) + Λ (m / k)) *
            Real.sqrt (k.totient : ℝ) / Real.sqrt (m.totient : ℝ)) =
          (if m = k then a k * Real.log k else 0) +
            a m * (Λ (m / k) * Real.sqrt (k.totient : ℝ) / Real.sqrt (m.totient : ℝ)) := by
        intro m _
        by_cases hmk : m = k
        · subst m
          rw [if_pos rfl, if_pos rfl]
          field_simp [hsφk]
        · rw [if_neg (Ne.symm hmk), if_neg hmk, zero_add, zero_add]
      rw [sum_congr rfl hterm, sum_add_distrib, sum_ite_eq']
      simp only [mem_filter, hk, hk_div, and_self, ↓reduceIte]
    have hpt_sq : ∀ k ∈ Icc 1 M,
        divisorJetCoeff M a k ^ 2 ≤ 2 * (a k * Real.log k) ^ 2 + 2 * offCoeff k ^ 2 := by
      intro k hk
      rw [hsplit_k k hk]
      nlinarith only [sq_nonneg (a k * Real.log k - offCoeff k)]
    have hdiag_sum : (∑ k ∈ Icc 1 M, 2 * (a k * Real.log k) ^ 2) ≤
        2 * (1 + Real.log M) ^ 2 * ∑ m ∈ Icc 1 M, a m ^ 2 := by
      rw [mul_sum]
      refine sum_le_sum fun k hk => ?_
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (mem_Icc.mp hk).1
      have hkM : (k : ℝ) ≤ M := by exact_mod_cast (mem_Icc.mp hk).2
      have hlk : Real.log k ≤ 1 + Real.log M := by
        have := Real.log_le_log (by positivity) hkM; linarith
      have hlk0 : 0 ≤ Real.log k := Real.log_nonneg hk1
      have hsq : (Real.log k) ^ 2 ≤ (1 + Real.log M) ^ 2 := pow_le_pow_left₀ hlk0 hlk 2
      calc
        2 * (a k * Real.log k) ^ 2 = 2 * (Real.log k) ^ 2 * a k ^ 2 := by ring
        _ ≤ 2 * (1 + Real.log M) ^ 2 * a k ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq zero_le_two) (sq_nonneg _)
    -- Bound `∑_{k=1}^M offCoeff k ^ 2`.
    have hoff_k : ∀ k ∈ Icc 1 M,
        offCoeff k ^ 2 ≤ (2 * mertensSum M) *
          ∑ m ∈ (Icc 1 M).filter (fun m => k ∈ m.divisors), Λ (m / k) * a m ^ 2 := by
      intro k hk
      obtain ⟨hk1, _⟩ := mem_Icc.mp hk
      let S_k := (Icc 1 M).filter (fun m => k ∈ m.divisors)
      have hterm_le : ∀ m ∈ S_k,
          |a m * (Λ (m / k) * Real.sqrt (k.totient : ℝ) / Real.sqrt (m.totient : ℝ))| ≤
            Real.sqrt (2 * Λ (m / k) / ((m / k : ℕ) : ℝ)) * (Real.sqrt (Λ (m / k)) * |a m|) := by
        intro m hmS
        obtain ⟨hmI, hkdiv⟩ := mem_filter.mp hmS
        have hm0 : 0 < m := (mem_Icc.mp hmI).1
        have hkdvd : k ∣ m := Nat.dvd_of_mem_divisors hkdiv
        have hq0 : 0 < m / k := Nat.div_pos (Nat.le_of_dvd hm0 hkdvd) hk1
        have hqR : (0 : ℝ) < (m / k : ℕ) := by exact_mod_cast hq0
        have hφmR : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm0
        have hΛ0 : 0 ≤ Λ (m / k) := vonMangoldt_nonneg
        have htot := totient_mul_quot_le hkdvd
        -- `(k.totient : ℝ) * (m / k) * Λ (m / k) ≤ 2 * m.totient * Λ (m / k)`
        have hrat_sq : (Λ (m / k) * Real.sqrt (k.totient : ℝ) / Real.sqrt (m.totient : ℝ)) ^ 2 ≤
            (2 * Λ (m / k) / ((m / k : ℕ) : ℝ)) * Λ (m / k) := by
          rw [div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg k.totient),
            Real.sq_sqrt (Nat.cast_nonneg m.totient), div_mul_eq_mul_div,
            div_le_div_iff₀ hφmR hqR]
          have hmul := mul_le_mul_of_nonneg_right htot hΛ0
          linarith only [hmul, (by ring :
            Λ (m / k) ^ 2 * (k.totient : ℝ) * ((m / k : ℕ) : ℝ) =
              ((k.totient : ℝ) * ((m / k : ℕ) : ℝ) * Λ (m / k)) * Λ (m / k)),
            (by ring : 2 * Λ (m / k) * Λ (m / k) * (m.totient : ℝ) =
              (2 * (m.totient : ℝ) * Λ (m / k)) * Λ (m / k))]
        have hrat_le : Λ (m / k) * Real.sqrt (k.totient : ℝ) / Real.sqrt (m.totient : ℝ) ≤
            Real.sqrt (2 * Λ (m / k) / ((m / k : ℕ) : ℝ)) * Real.sqrt (Λ (m / k)) := by
          rw [← Real.sqrt_mul (by positivity)]
          exact (Real.le_sqrt_of_sq_le hrat_sq)
        rw [abs_mul, abs_of_nonneg
          (div_nonneg (mul_nonneg hΛ0 (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))]
        calc
          |a m| * (Λ (m / k) * Real.sqrt (k.totient : ℝ) / Real.sqrt (m.totient : ℝ)) ≤
              |a m| * (Real.sqrt (2 * Λ (m / k) / ((m / k : ℕ) : ℝ)) * Real.sqrt (Λ (m / k))) :=
            mul_le_mul_of_nonneg_left hrat_le (abs_nonneg _)
          _ = Real.sqrt (2 * Λ (m / k) / ((m / k : ℕ) : ℝ)) * (Real.sqrt (Λ (m / k)) * |a m|) := by
            ring
      have habs_off : |offCoeff k| ≤
          ∑ m ∈ S_k, Real.sqrt (2 * Λ (m / k) / ((m / k : ℕ) : ℝ)) *
            (Real.sqrt (Λ (m / k)) * |a m|) :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum hterm_le)
      have hsq := pow_le_pow_left₀ (abs_nonneg _) habs_off 2
      rw [sq_abs] at hsq
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq S_k
        (fun m => Real.sqrt (2 * Λ (m / k) / ((m / k : ℕ) : ℝ)))
        (fun m => Real.sqrt (Λ (m / k)) * |a m|)
      have h1_le : (∑ m ∈ S_k, Real.sqrt (2 * Λ (m / k) / ((m / k : ℕ) : ℝ)) ^ 2) ≤
          2 * mertensSum M := by
        have hsq1 : ∀ m ∈ S_k,
            Real.sqrt (2 * Λ (m / k) / ((m / k : ℕ) : ℝ)) ^ 2 =
              2 * (Λ (m / k) / ((m / k : ℕ) : ℝ)) := fun m _ => by
          rw [Real.sq_sqrt (div_nonneg (mul_nonneg zero_le_two vonMangoldt_nonneg) (Nat.cast_nonneg _))]
          ring
        rw [sum_congr rfl hsq1, ← mul_sum]
        refine mul_le_mul_of_nonneg_left ?_ zero_le_two
        have hinj : ∀ m₁ ∈ S_k, ∀ m₂ ∈ S_k, m₁ / k = m₂ / k → m₁ = m₂ := by
          intro m₁ hm₁ m₂ hm₂ heq
          have hd1 := Nat.dvd_of_mem_divisors (mem_filter.mp hm₁).2
          have hd2 := Nat.dvd_of_mem_divisors (mem_filter.mp hm₂).2
          rw [← Nat.div_mul_cancel hd1, ← Nat.div_mul_cancel hd2, heq]
        have hsub : S_k.image (fun m => m / k) ⊆ Icc 1 M := by
          intro d hd
          obtain ⟨m, hmS, rfl⟩ := mem_image.mp hd
          obtain ⟨hmI, hkdiv⟩ := mem_filter.mp hmS
          exact mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd (mem_Icc.mp hmI).1
            (Nat.dvd_of_mem_divisors hkdiv)) hk1, (Nat.div_le_self m k).trans (mem_Icc.mp hmI).2⟩
        calc
          (∑ m ∈ S_k, Λ (m / k) / ((m / k : ℕ) : ℝ)) =
              ∑ d ∈ S_k.image (fun m => m / k), Λ d / (d : ℝ) :=
            (sum_image (f := fun d : ℕ => Λ d / (d : ℝ)) hinj).symm
          _ ≤ ∑ d ∈ Icc 1 M, Λ d / (d : ℝ) :=
            sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ =>
              div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _)
          _ = mertensSum M := rfl
      have h2_eq : (∑ m ∈ S_k, (Real.sqrt (Λ (m / k)) * |a m|) ^ 2) =
          ∑ m ∈ S_k, Λ (m / k) * a m ^ 2 :=
        sum_congr rfl fun m _ => by
          rw [mul_pow, Real.sq_sqrt vonMangoldt_nonneg, sq_abs]
      calc
        offCoeff k ^ 2 ≤ (∑ m ∈ S_k, Real.sqrt (2 * Λ (m / k) / ((m / k : ℕ) : ℝ)) ^ 2) *
            ∑ m ∈ S_k, (Real.sqrt (Λ (m / k)) * |a m|) ^ 2 := hsq.trans hcs
        _ ≤ (2 * mertensSum M) * ∑ m ∈ S_k, Λ (m / k) * a m ^ 2 := by
          rw [h2_eq]
          exact mul_le_mul_of_nonneg_right h1_le
            (sum_nonneg fun _ _ => mul_nonneg vonMangoldt_nonneg (sq_nonneg _))
    have hoff_sum : (∑ k ∈ Icc 1 M, 2 * offCoeff k ^ 2) ≤
        4 * (C_mert + 1) * (1 + Real.log M) ^ 2 * ∑ m ∈ Icc 1 M, a m ^ 2 := by
      have hmertM : 2 * mertensSum M ≤ 2 * (C_mert + 1) * (1 + Real.log M) := by
        have hm := hmert_le M (by omega)
        have hLM0 := Real.log_natCast_nonneg M
        nlinarith only [hm, hLM0, hC_mert_pos]
      have hswap_sum :
          (∑ k ∈ Icc 1 M, ∑ m ∈ (Icc 1 M).filter (fun m => k ∈ m.divisors),
            Λ (m / k) * a m ^ 2) ≤ Real.log M * ∑ m ∈ Icc 1 M, a m ^ 2 := by
        have hrew : (∑ k ∈ Icc 1 M, ∑ m ∈ (Icc 1 M).filter (fun m => k ∈ m.divisors),
            Λ (m / k) * a m ^ 2) =
            ∑ m ∈ Icc 1 M, a m ^ 2 * ∑ k ∈ m.divisors, Λ (m / k) := by
          simp_rw [sum_filter]
          rw [sum_comm]
          refine sum_congr rfl fun m hm => ?_
          obtain ⟨hm1, hmM⟩ := mem_Icc.mp hm
          have hsub : m.divisors ⊆ Icc 1 M := fun k hk =>
            mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hk,
              (Nat.le_of_dvd hm1 (Nat.dvd_of_mem_divisors hk)).trans hmM⟩
          have hk_eq : (∑ x ∈ Icc 1 M, if x ∈ m.divisors then Λ (m / x) * a m ^ 2 else 0) =
              ∑ x ∈ m.divisors, Λ (m / x) * a m ^ 2 := by
            rw [← sum_subset hsub]
            · exact sum_congr rfl fun x hx => if_pos hx
            · intro x _ hx; exact if_neg hx
          rw [hk_eq, mul_sum]
          exact sum_congr rfl fun x _ => mul_comm _ _
        rw [hrew, mul_sum]
        refine sum_le_sum fun m hm => ?_
        have hmM : (m : ℝ) ≤ M := by exact_mod_cast (mem_Icc.mp hm).2
        have hm1 : 0 < m := (mem_Icc.mp hm).1
        have hdiv_log : (∑ k ∈ m.divisors, Λ (m / k)) = Real.log m := by
          rw [Nat.sum_div_divisors m (fun d => Λ d), vonMangoldt_sum]
        rw [hdiv_log, mul_comm (a m ^ 2)]
        exact mul_le_mul_of_nonneg_right
          (Real.log_le_log (by exact_mod_cast hm1) hmM) (sq_nonneg _)
      have hmert0 : 0 ≤ 2 * mertensSum M :=
        mul_nonneg zero_le_two
          (sum_nonneg fun _ _ => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _))
      have h1 : (∑ k ∈ Icc 1 M, 2 * offCoeff k ^ 2) ≤
          2 * (2 * mertensSum M) *
            ∑ k ∈ Icc 1 M, ∑ m ∈ (Icc 1 M).filter (fun m => k ∈ m.divisors),
              Λ (m / k) * a m ^ 2 := by
        calc
          (∑ k ∈ Icc 1 M, 2 * offCoeff k ^ 2) = 2 * ∑ k ∈ Icc 1 M, offCoeff k ^ 2 :=
            (mul_sum _ _ _).symm
          _ ≤ 2 * ∑ k ∈ Icc 1 M, (2 * mertensSum M) *
              ∑ m ∈ (Icc 1 M).filter (fun m => k ∈ m.divisors), Λ (m / k) * a m ^ 2 :=
            mul_le_mul_of_nonneg_left (sum_le_sum hoff_k) zero_le_two
          _ = _ := by rw [← mul_sum, mul_assoc]
      have hLM_le : Real.log M ≤ 1 + Real.log M := by linarith
      calc
        (∑ k ∈ Icc 1 M, 2 * offCoeff k ^ 2) ≤
            2 * (2 * mertensSum M) * (Real.log M * ∑ m ∈ Icc 1 M, a m ^ 2) :=
          h1.trans (mul_le_mul_of_nonneg_left hswap_sum (mul_nonneg zero_le_two hmert0))
        _ ≤ 2 * (2 * (C_mert + 1) * (1 + Real.log M)) *
            ((1 + Real.log M) * ∑ m ∈ Icc 1 M, a m ^ 2) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hmertM zero_le_two)
            (mul_le_mul_of_nonneg_right hLM_le (sum_nonneg fun _ _ => sq_nonneg _))
            (mul_nonneg (Real.log_natCast_nonneg M) (sum_nonneg fun _ _ => sq_nonneg _)) ?_
          have := Real.log_natCast_nonneg M; positivity
        _ = 4 * (C_mert + 1) * (1 + Real.log M) ^ 2 * ∑ m ∈ Icc 1 M, a m ^ 2 := by ring
    calc
      (∑ k ∈ Icc 1 M, divisorJetCoeff M a k ^ 2) ≤
          (∑ k ∈ Icc 1 M, 2 * (a k * Real.log k) ^ 2) + ∑ k ∈ Icc 1 M, 2 * offCoeff k ^ 2 := by
        rw [← sum_add_distrib]; exact sum_le_sum hpt_sq
      _ ≤ 2 * (1 + Real.log M) ^ 2 * (∑ m ∈ Icc 1 M, a m ^ 2) +
          4 * (C_mert + 1) * (1 + Real.log M) ^ 2 * ∑ m ∈ Icc 1 M, a m ^ 2 :=
        add_le_add hdiag_sum hoff_sum
      _ = (2 + 4 * C_mert + 4) * (1 + Real.log M) ^ 2 * ∑ m ∈ Icc 1 M, a m ^ 2 := by ring
  have hriesz := (half_and_three_halves_riesz_of_log_le hM hMN hlog (divisorJetCoeff M a)).2
  have hSa0 : 0 ≤ ∑ m ∈ Icc 1 M, a m ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hLM1 : 0 ≤ 1 + Real.log M := by have := Real.log_natCast_nonneg M; linarith
  have hconst_le : (3 / 2 : ℝ) * (2 + 4 * C_mert + 4) ≤ C_jet ^ 2 := by
    dsimp only [C_jet]
    nlinarith only [hC_mert_pos]
  have hnorm_sq : ‖divisorJetHorizonVector M N a‖ ^ 2 ≤
      (C_jet * (1 + Real.log M) * Real.sqrt (∑ m ∈ Icc 1 M, a m ^ 2)) ^ 2 := by
    calc
      ‖divisorJetHorizonVector M N a‖ ^ 2 ≤
          (3 / 2 : ℝ) * ∑ k ∈ Icc 1 M, divisorJetCoeff M a k ^ 2 := hriesz
      _ ≤ (3 / 2 : ℝ) * ((2 + 4 * C_mert + 4) * (1 + Real.log M) ^ 2 *
          ∑ m ∈ Icc 1 M, a m ^ 2) :=
        mul_le_mul_of_nonneg_left hcoeff_sq (by norm_num)
      _ = ((3 / 2 : ℝ) * (2 + 4 * C_mert + 4)) *
          ((1 + Real.log M) ^ 2 * ∑ m ∈ Icc 1 M, a m ^ 2) := by ring
      _ ≤ C_jet ^ 2 * ((1 + Real.log M) ^ 2 * ∑ m ∈ Icc 1 M, a m ^ 2) :=
        mul_le_mul_of_nonneg_right hconst_le (mul_nonneg (sq_nonneg _) hSa0)
      _ = (C_jet * (1 + Real.log M) * Real.sqrt (∑ m ∈ Icc 1 M, a m ^ 2)) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hSa0]; ring
  have hrhs0 : 0 ≤ C_jet * (1 + Real.log M) * Real.sqrt (∑ m ∈ Icc 1 M, a m ^ 2) := by
    dsimp only [C_jet]; positivity
  nlinarith only [hnorm_sq, norm_nonneg (divisorJetHorizonVector M N a), hrhs0]

private theorem sum_Icc_dvd_vonMangoldt_mul_le {g : ℕ} (hg : 2 ≤ g) (B : ℕ) :
    (∑ t ∈ Icc 2 B, if g ∣ t then (Λ t / (t : ℝ)) * (g : ℝ) else 0) ≤ 2 * Λ g := by
  by_cases hgpp : IsPrimePow g
  · obtain ⟨p, r, hp, hr, rfl⟩ := (isPrimePow_nat_iff g).mp hgpp
    have hΛpr : Λ (p ^ r) = Real.log p := by
      rw [vonMangoldt_apply_pow hr.ne', vonMangoldt_apply_prime hp]
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hlogp0 : 0 ≤ Real.log p := Real.log_nonneg (by linarith only [hp2])
    let S := (Icc 2 B).filter (fun t => p ^ r ∣ t ∧ Λ t ≠ 0)
    have hrew : (∑ t ∈ Icc 2 B, if p ^ r ∣ t then (Λ t / (t : ℝ)) * ((p ^ r : ℕ) : ℝ) else 0) =
        ∑ t ∈ S, (Λ t / (t : ℝ)) * ((p ^ r : ℕ) : ℝ) := by
      rw [sum_filter]
      refine sum_congr rfl fun t _ => ?_
      by_cases hdvd : p ^ r ∣ t
      · by_cases hΛ0 : Λ t = 0
        · rw [if_pos hdvd, if_neg (fun h => h.2 hΛ0), hΛ0, zero_div, zero_mul]
        · rw [if_pos hdvd, if_pos ⟨hdvd, hΛ0⟩]
      · rw [if_neg hdvd, if_neg (fun h => hdvd h.1)]
    rw [hrew, hΛpr]
    -- Every `t ∈ S` has the form `p ^ (r + j)` with `j ∈ range B`.
    have hmem_im : S ⊆ (range B).image (fun j => p ^ (r + j)) := by
      intro t ht
      obtain ⟨htI, hdvd, hΛt⟩ := mem_filter.mp ht
      obtain ⟨q, k, hq, hk, rfl⟩ := (isPrimePow_nat_iff t).mp (vonMangoldt_ne_zero_iff.mp hΛt)
      have hp_dvd_qk : p ∣ q ^ k := (dvd_pow_self p hr.ne').trans hdvd
      have hpq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hp_dvd_qk)
      subst q
      have hrk : r ≤ k := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hdvd
      have hkB : k < B := (Nat.lt_pow_self hp.one_lt).trans_le (mem_Icc.mp htI).2
      refine mem_image.mpr ⟨k - r, mem_range.mpr (by omega), ?_⟩
      rw [Nat.add_sub_of_le hrk]
    have hinj : ∀ j₁ ∈ range B, ∀ j₂ ∈ range B,
        p ^ (r + j₁) = p ^ (r + j₂) → j₁ = j₂ := by
      intro j₁ _ j₂ _ heq
      have h := (Nat.pow_right_inj hp.one_lt).mp heq
      omega
    have hval : ∀ j ∈ range B,
        (Λ (p ^ (r + j)) / ((p ^ (r + j) : ℕ) : ℝ)) * ((p ^ r : ℕ) : ℝ) =
          Real.log p * ((p : ℝ)⁻¹) ^ j := by
      intro j _
      have hrj : r + j ≠ 0 := by omega
      rw [vonMangoldt_apply_pow hrj, vonMangoldt_apply_prime hp, Nat.cast_pow, Nat.cast_pow,
        pow_add, inv_pow]
      have hp_ne : (p : ℝ) ^ r ≠ 0 := pow_ne_zero r hp0.ne'
      have hpj_ne : (p : ℝ) ^ j ≠ 0 := pow_ne_zero j hp0.ne'
      field_simp [hp_ne, hpj_ne]
    have hgeom : ∀ K : ℕ,
        (1 - (p : ℝ)⁻¹) * (∑ j ∈ range K, ((p : ℝ)⁻¹) ^ j) = 1 - ((p : ℝ)⁻¹) ^ K := by
      intro K
      induction K with
      | zero => simp
      | succ K ih =>
        rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
        ring
    have hsum_inv_le : (∑ j ∈ range B, ((p : ℝ)⁻¹) ^ j) ≤ 2 := by
      have hp_inv_le : (p : ℝ)⁻¹ ≤ 1 / 2 := by
        rw [inv_eq_one_div]
        exact one_div_le_one_div_of_le (by norm_num) hp2
      have hhalf : (1 / 2 : ℝ) ≤ 1 - (p : ℝ)⁻¹ := by linarith only [hp_inv_le]
      have hS0 : 0 ≤ ∑ j ∈ range B, ((p : ℝ)⁻¹) ^ j :=
        sum_nonneg fun _ _ => pow_nonneg (inv_nonneg.mpr hp0.le) _
      have hpow0 : 0 ≤ ((p : ℝ)⁻¹) ^ B := pow_nonneg (inv_nonneg.mpr hp0.le) B
      have h1 := mul_le_mul_of_nonneg_right hhalf hS0
      have h2 := hgeom B
      linarith only [h1, h2, hpow0]
    calc
      (∑ t ∈ S, (Λ t / (t : ℝ)) * ((p ^ r : ℕ) : ℝ)) ≤
          ∑ t ∈ (range B).image (fun j => p ^ (r + j)),
            (Λ t / (t : ℝ)) * ((p ^ r : ℕ) : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hmem_im fun _ _ _ =>
          mul_nonneg (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
      _ = ∑ j ∈ range B, Real.log p * ((p : ℝ)⁻¹) ^ j := by
        rw [sum_image hinj]
        exact sum_congr rfl hval
      _ = Real.log p * ∑ j ∈ range B, ((p : ℝ)⁻¹) ^ j := (mul_sum _ _ _).symm
      _ ≤ Real.log p * 2 := mul_le_mul_of_nonneg_left hsum_inv_le hlogp0
      _ = 2 * Real.log p := by ring
  · have hzero : ∀ t ∈ Icc 2 B,
        (if g ∣ t then (Λ t / (t : ℝ)) * (g : ℝ) else 0) = 0 := by
      intro t _
      by_cases hdvd : g ∣ t
      · rw [if_pos hdvd]
        have hΛ0 : Λ t = 0 := by
          by_contra hne
          obtain ⟨p, k, hp, _, rfl⟩ := (isPrimePow_nat_iff t).mp (vonMangoldt_ne_zero_iff.mp hne)
          obtain ⟨r, _, rfl⟩ := (Nat.dvd_prime_pow hp).mp hdvd
          have hr0 : r ≠ 0 := by rintro rfl; simp at hg
          exact hgpp (hp.isPrimePow.pow hr0)
        rw [hΛ0, zero_div, zero_mul]
      · exact if_neg hdvd
    rw [sum_eq_zero hzero]
    exact mul_nonneg zero_le_two vonMangoldt_nonneg

private theorem nat_log_two_le_two_mul_log {M : ℕ} (hM : 1 ≤ M) :
    (Nat.log 2 M : ℝ) ≤ 2 * Real.log M := by
  let L := Nat.log 2 M
  have hpow : ((2 : ℝ) ^ L) ≤ (M : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : M ≠ 0)
  have hlog : (L : ℝ) * Real.log 2 ≤ Real.log M := by
    have h := Real.log_le_log (by positivity) hpow
    simpa only [Real.log_pow] using h
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (2 : ℝ)⁻¹ by norm_num)
    rw [Real.log_inv] at h
    linarith only [h]
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  nlinarith only [hlog, hlog2, hL0]

/-- Reduced-dilation coefficient `c_{t, d}` in `G(t * n) = ∑_{d=1}^M c_{t, d} g_d(n)`. -/
private def reducedDilationCoeff (M : ℕ) (a : ℕ → ℝ) (t d : ℕ) : ℝ :=
  ∑ m ∈ (Icc 1 M).filter (fun m => m / Nat.gcd m t = d),
    a m * (Real.sqrt (m.totient : ℝ) / Real.sqrt (d.totient : ℝ))

private theorem sum_normalizedRamanujanMode_dilate_eq_reduced (M t n : ℕ) (a : ℕ → ℝ) :
    (∑ m ∈ Icc 1 M, a m * normalizedRamanujanMode m (t * n)) =
      ∑ d ∈ Icc 1 M, reducedDilationCoeff M a t d * normalizedRamanujanMode d n := by
  have hmaps : ∀ m ∈ Icc 1 M, m / Nat.gcd m t ∈ Icc 1 M := fun m hm => by
    obtain ⟨hm1, hmM⟩ := mem_Icc.mp hm
    exact mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hm1 (Nat.gcd_dvd_left m t))
      (Nat.gcd_pos_of_pos_left t hm1), (Nat.div_le_self m _).trans hmM⟩
  have hterm : ∀ m ∈ Icc 1 M, a m * normalizedRamanujanMode m (t * n) =
      (a m * (Real.sqrt (m.totient : ℝ) / Real.sqrt ((m / Nat.gcd m t).totient : ℝ))) *
        normalizedRamanujanMode (m / Nat.gcd m t) n := fun m hm => by
    rw [normalizedRamanujanMode_dilate_reduced (mem_Icc.mp hm).1 t n]
    ring
  rw [sum_congr rfl hterm, ← sum_fiberwise_of_maps_to hmaps]
  refine sum_congr rfl fun d _ => ?_
  dsimp only [reducedDilationCoeff]
  rw [sum_mul]
  refine sum_congr rfl fun m hm => ?_
  rw [(mem_filter.mp hm).2]

private theorem sum_reducedDilationCoeff_sq_le {M t : ℕ} (hM : 2 ≤ M) (ht : IsPrimePow t)
    (a : ℕ → ℝ) :
    (∑ d ∈ Icc 1 M, reducedDilationCoeff M a t d ^ 2) ≤
      2 * (∑ m ∈ Icc 1 M, a m ^ 2) +
        4 * Real.log M * ∑ m ∈ Icc 1 M, a m ^ 2 *
          ∑ g ∈ m.divisors.filter (2 ≤ ·), if g ∣ t then (g : ℝ) else 0 := by
  obtain ⟨p, k, hp, _, rfl⟩ := (isPrimePow_nat_iff t).mp ht
  let Big2 := (Icc 1 M).filter (fun m => 2 ≤ Nat.gcd m (p ^ k))
  have hpt : ∀ d ∈ Icc 1 M,
      reducedDilationCoeff M a (p ^ k) d ^ 2 ≤
        2 * a d ^ 2 +
          4 * Real.log M * ∑ m ∈ Big2.filter (fun m => m / Nat.gcd m (p ^ k) = d),
            a m ^ 2 * ∑ g ∈ m.divisors.filter (2 ≤ ·), if g ∣ p ^ k then (g : ℝ) else 0 := by
    intro d hd
    obtain ⟨hd1, _⟩ := mem_Icc.mp hd
    let F_d := (Icc 1 M).filter (fun m => m / Nat.gcd m (p ^ k) = d)
    let F1_d := F_d.filter (fun m => Nat.gcd m (p ^ k) = 1)
    let S_d := Big2.filter (fun m => m / Nat.gcd m (p ^ k) = d)
    have hpart : F_d = F1_d ∪ S_d := by
      ext m
      simp only [F_d, F1_d, S_d, Big2, mem_filter, mem_union, mem_Icc]
      constructor
      · rintro ⟨⟨hm1, hmM⟩, hdiv⟩
        have hg0 : 0 < Nat.gcd m (p ^ k) := Nat.gcd_pos_of_pos_left _ hm1
        rcases eq_or_ne (Nat.gcd m (p ^ k)) 1 with hg1 | hg_ne
        · exact Or.inl ⟨⟨⟨hm1, hmM⟩, hdiv⟩, hg1⟩
        · exact Or.inr ⟨⟨⟨hm1, hmM⟩, by omega⟩, hdiv⟩
      · rintro (⟨hF, _⟩ | ⟨⟨hI, _⟩, hdiv⟩)
        · exact hF
        · exact ⟨hI, hdiv⟩
    have hdisj : Disjoint F1_d S_d := by
      rw [Finset.disjoint_left]
      intro m hm1 hm2
      have h1 := (mem_filter.mp hm1).2
      have h2 := (mem_filter.mp (mem_filter.mp hm2).1).2
      omega
    have hsplit : reducedDilationCoeff M a (p ^ k) d =
        (∑ m ∈ F1_d, a m * (Real.sqrt (m.totient : ℝ) / Real.sqrt (d.totient : ℝ))) +
          ∑ m ∈ S_d, a m * (Real.sqrt (m.totient : ℝ) / Real.sqrt (d.totient : ℝ)) := by
      dsimp only [reducedDilationCoeff]
      change (∑ m ∈ F_d, _) = _
      rw [hpart, sum_union hdisj]
    have hF1_sq :
        (∑ m ∈ F1_d, a m * (Real.sqrt (m.totient : ℝ) / Real.sqrt (d.totient : ℝ))) ^ 2 ≤
          a d ^ 2 := by
      have hsub1 : F1_d ⊆ {d} := by
        intro m hm
        have hm1 := mem_filter.mp hm
        have hm2 := mem_filter.mp hm1.1
        have hdiv := hm2.2
        rw [hm1.2, Nat.div_one] at hdiv
        exact mem_singleton.mpr hdiv
      rcases Finset.subset_singleton_iff.mp hsub1 with hemp | hsing
      · rw [hemp, sum_empty, zero_pow (by norm_num)]
        exact sq_nonneg _
      · rw [hsing, sum_singleton]
        have hsφd : Real.sqrt (d.totient : ℝ) ≠ 0 :=
          (Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr hd1)).ne'
        rw [div_self hsφd, mul_one]
    -- Bound `S_d.card ≤ Nat.log 2 M`.
    have hcard_Sd : (S_d.card : ℝ) ≤ 2 * Real.log M := by
      let e : ℕ → ℕ := fun m => Nat.log p (Nat.gcd m (p ^ k))
      have hm_eq : ∀ m ∈ S_d, Nat.gcd m (p ^ k) = p ^ e m ∧ m = d * p ^ e m := by
        intro m hmS
        obtain ⟨hmBig, hdiv⟩ := mem_filter.mp hmS
        obtain ⟨r, _, hg_eq⟩ := (Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_right m (p ^ k))
        have her : e m = r := by
          dsimp only [e]; rw [hg_eq, Nat.log_pow hp.one_lt r]
        have hg_pow : Nat.gcd m (p ^ k) = p ^ e m := by rw [her, hg_eq]
        refine ⟨hg_pow, ?_⟩
        have hmul := Nat.div_mul_cancel (Nat.gcd_dvd_left m (p ^ k))
        rw [hdiv, hg_pow] at hmul
        exact hmul.symm
      have hinj : Set.InjOn e S_d := by
        intro m₁ hm₁ m₂ hm₂ heq
        rw [(hm_eq m₁ hm₁).2, (hm_eq m₂ hm₂).2, heq]
      have him_sub : S_d.image e ⊆ Icc 1 (Nat.log 2 M) := by
        intro r hr
        obtain ⟨m, hmS, rfl⟩ := mem_image.mp hr
        obtain ⟨hmBig, _⟩ := mem_filter.mp hmS
        obtain ⟨hmI, hg2⟩ := mem_filter.mp hmBig
        obtain ⟨hm1, hmM⟩ := mem_Icc.mp hmI
        have hg_pow := (hm_eq m hmS).1
        have he1 : 1 ≤ e m := by
          by_contra hlt
          have hz : e m = 0 := by omega
          rw [hz, pow_zero] at hg_pow
          omega
        have h2pow : 2 ^ e m ≤ M :=
          (Nat.pow_le_pow_left hp.two_le (e m)).trans
            (hg_pow ▸ (Nat.le_of_dvd hm1 (Nat.gcd_dvd_left m (p ^ k))).trans hmM)
        have heM : e m ≤ Nat.log 2 M := by
          rw [← Nat.log_pow Nat.one_lt_two (e m)]
          exact Nat.log_mono_right h2pow
        exact mem_Icc.mpr ⟨he1, heM⟩
      have hcard_nat : S_d.card ≤ Nat.log 2 M := by
        calc
          S_d.card = (S_d.image e).card := (card_image_of_injOn hinj).symm
          _ ≤ (Icc 1 (Nat.log 2 M)).card := card_le_card him_sub
          _ = Nat.log 2 M := by simp
      exact (show (S_d.card : ℝ) ≤ (Nat.log 2 M : ℝ) by exact_mod_cast hcard_nat).trans
        (nat_log_two_le_two_mul_log (by omega))
    -- Apply Cauchy–Schwarz on `S_d`.
    have hSd_sq :
        (∑ m ∈ S_d, a m * (Real.sqrt (m.totient : ℝ) / Real.sqrt (d.totient : ℝ))) ^ 2 ≤
          2 * Real.log M * ∑ m ∈ S_d,
            a m ^ 2 * ∑ g ∈ m.divisors.filter (2 ≤ ·), if g ∣ p ^ k then (g : ℝ) else 0 := by
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq S_d (fun _ => (1 : ℝ))
        (fun m => a m * (Real.sqrt (m.totient : ℝ) / Real.sqrt (d.totient : ℝ)))
      simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one] at hcs
      have hterm_Sd : ∀ m ∈ S_d,
          (a m * (Real.sqrt (m.totient : ℝ) / Real.sqrt (d.totient : ℝ))) ^ 2 ≤
            a m ^ 2 * ∑ g ∈ m.divisors.filter (2 ≤ ·), if g ∣ p ^ k then (g : ℝ) else 0 := by
        intro m hmS
        obtain ⟨hmBig, hdiv⟩ := mem_filter.mp hmS
        obtain ⟨hmI, hg2⟩ := mem_filter.mp hmBig
        have hm1 : 0 < m := (mem_Icc.mp hmI).1
        let g := Nat.gcd m (p ^ k)
        have hmdg : m = d * g := by
          have hmul := Nat.div_mul_cancel (Nat.gcd_dvd_left m (p ^ k))
          change (m / g) * g = m at hmul
          rw [hdiv] at hmul
          exact hmul.symm
        have htot : (m.totient : ℝ) ≤ (g : ℝ) * d.totient := by
          rw [hmdg]; exact_mod_cast totient_mul_le d g
        have hdφ0 : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr hd1
        have hrat : (Real.sqrt (m.totient : ℝ) / Real.sqrt (d.totient : ℝ)) ^ 2 ≤ (g : ℝ) := by
          rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _),
            div_le_iff₀ hdφ0]
          exact htot
        have hg_mem : g ∈ m.divisors.filter (2 ≤ ·) :=
          mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left _ _, hm1.ne'⟩, hg2⟩
        have hg_le_sum : (g : ℝ) ≤
            ∑ g' ∈ m.divisors.filter (2 ≤ ·), if g' ∣ p ^ k then (g' : ℝ) else 0 := by
          have hs := single_le_sum (f := fun g' : ℕ => if g' ∣ p ^ k then (g' : ℝ) else 0)
            (fun g' _ => by split_ifs <;> positivity) hg_mem
          simpa only [if_pos (Nat.gcd_dvd_right m (p ^ k))] using hs
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_left (hrat.trans hg_le_sum) (sq_nonneg _)
      exact hcs.trans (mul_le_mul hcard_Sd (sum_le_sum hterm_Sd)
        (sum_nonneg fun _ _ => sq_nonneg _)
        (mul_nonneg zero_le_two (Real.log_natCast_nonneg M)))
    have h2sq : reducedDilationCoeff M a (p ^ k) d ^ 2 ≤
        2 * (∑ m ∈ F1_d, a m * (Real.sqrt (m.totient : ℝ) / Real.sqrt (d.totient : ℝ))) ^ 2 +
          2 * (∑ m ∈ S_d, a m * (Real.sqrt (m.totient : ℝ) / Real.sqrt (d.totient : ℝ))) ^ 2 := by
      rw [hsplit]
      nlinarith only [sq_nonneg
        ((∑ m ∈ F1_d, a m * (Real.sqrt (m.totient : ℝ) / Real.sqrt (d.totient : ℝ))) -
          ∑ m ∈ S_d, a m * (Real.sqrt (m.totient : ℝ) / Real.sqrt (d.totient : ℝ)))]
    calc
      reducedDilationCoeff M a (p ^ k) d ^ 2 ≤
          2 * a d ^ 2 + 2 * (2 * Real.log M * ∑ m ∈ S_d,
            a m ^ 2 * ∑ g ∈ m.divisors.filter (2 ≤ ·), if g ∣ p ^ k then (g : ℝ) else 0) :=
        h2sq.trans (add_le_add (mul_le_mul_of_nonneg_left hF1_sq zero_le_two)
          (mul_le_mul_of_nonneg_left hSd_sq zero_le_two))
      _ = 2 * a d ^ 2 + 4 * Real.log M * ∑ m ∈ S_d,
            a m ^ 2 * ∑ g ∈ m.divisors.filter (2 ≤ ·), if g ∣ p ^ k then (g : ℝ) else 0 := by
        ring
  have hmaps_Big2 : ∀ m ∈ Big2, m / Nat.gcd m (p ^ k) ∈ Icc 1 M := fun m hm => by
    obtain ⟨hm1, hmM⟩ := mem_Icc.mp (mem_filter.mp hm).1
    exact mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hm1 (Nat.gcd_dvd_left m _))
      (Nat.gcd_pos_of_pos_left _ hm1), (Nat.div_le_self m _).trans hmM⟩
  have hfib :
      (∑ d ∈ Icc 1 M, ∑ m ∈ Big2.filter (fun m => m / Nat.gcd m (p ^ k) = d),
        a m ^ 2 * ∑ g ∈ m.divisors.filter (2 ≤ ·), if g ∣ p ^ k then (g : ℝ) else 0) =
      ∑ m ∈ Big2, a m ^ 2 *
        ∑ g ∈ m.divisors.filter (2 ≤ ·), if g ∣ p ^ k then (g : ℝ) else 0 :=
    sum_fiberwise_of_maps_to hmaps_Big2 _
  have hBig2_le :
      (∑ m ∈ Big2, a m ^ 2 *
        ∑ g ∈ m.divisors.filter (2 ≤ ·), if g ∣ p ^ k then (g : ℝ) else 0) ≤
      ∑ m ∈ Icc 1 M, a m ^ 2 *
        ∑ g ∈ m.divisors.filter (2 ≤ ·), if g ∣ p ^ k then (g : ℝ) else 0 :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ =>
      mul_nonneg (sq_nonneg _)
        (sum_nonneg fun _ _ => by split_ifs <;> positivity)
  calc
    (∑ d ∈ Icc 1 M, reducedDilationCoeff M a (p ^ k) d ^ 2) ≤
        (∑ d ∈ Icc 1 M, 2 * a d ^ 2) +
          ∑ d ∈ Icc 1 M, 4 * Real.log M * ∑ m ∈ Big2.filter (fun m => m / Nat.gcd m (p ^ k) = d),
            a m ^ 2 * ∑ g ∈ m.divisors.filter (2 ≤ ·), if g ∣ p ^ k then (g : ℝ) else 0 := by
      rw [← sum_add_distrib]
      exact sum_le_sum hpt
    _ = 2 * (∑ m ∈ Icc 1 M, a m ^ 2) +
          4 * Real.log M * ∑ m ∈ Big2,
            a m ^ 2 * ∑ g ∈ m.divisors.filter (2 ≤ ·), if g ∣ p ^ k then (g : ℝ) else 0 := by
      rw [← mul_sum, ← mul_sum, hfib]
    _ ≤ 2 * (∑ m ∈ Icc 1 M, a m ^ 2) +
          4 * Real.log M * ∑ m ∈ Icc 1 M,
            a m ^ 2 * ∑ g ∈ m.divisors.filter (2 ≤ ·), if g ∣ p ^ k then (g : ℝ) else 0 :=
      add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hBig2_le (mul_nonneg (by norm_num) (Real.log_natCast_nonneg M)))

/-- Pointwise non-Mertens prime-profile correction on a Ramanujan packet. -/
private def packetPrimeCorrTerm (M N : ℕ) (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  poleVector n * ∑ m ∈ Icc 1 M, a m *
    (poleProfileCorrection (normalizedRamanujanMode m) (N / n) n +
      (Real.log m + tameDifferent m) * normalizedRamanujanMode m n)

/-- Deep quotient strip `1 ≤ n ≤ N / M ^ 4` bound for `packetPrimeCorrTerm`:
each quotient satisfies `N / n ≥ M ^ 4`, giving `O(1 / M)` pointwise cancellation per mode and
total `L²` mass `≤ 32 * (log N) * ∑ a_m^2` without any factor of `M` or `log M`. -/
private theorem sum_deep_packetPrimeCorrTerm_sq_le
    {M N : ℕ} (hM : 2 ≤ M) (hM6N : M ^ 6 ≤ N) (hL1 : 1 ≤ Real.log N) (a : ℕ → ℝ) :
    (Real.log N)⁻¹ * (∑ n ∈ Icc 1 (N / M ^ 4), packetPrimeCorrTerm M N a n ^ 2) ≤
      32 * ∑ m ∈ Icc 1 M, a m ^ 2 := by
  have hM4_pos : 0 < M ^ 4 := pow_pos (by omega) 4
  have hKN : N / M ^ 4 ≤ N := Nat.div_le_self N (M ^ 4)
  have hL0 : 0 < Real.log N := zero_lt_one.trans_le hL1
  have hcorr_deep : ∀ n ∈ Icc 1 (N / M ^ 4),
      packetPrimeCorrTerm M N a n ^ 2 ≤ (16 / (n : ℝ)) * ∑ m ∈ Icc 1 M, a m ^ 2 := by
    intro n hn
    obtain ⟨hn0, hnK⟩ := mem_Icc.mp hn
    have hy_ge : M ^ 4 ≤ N / n := by
      refine (Nat.le_div_iff_mul_le hn0).mpr ?_
      rw [Nat.mul_comm]
      exact (Nat.mul_le_mul_right (M ^ 4) hnK).trans (Nat.div_mul_le_self N (M ^ 4))
    have hy0 : 0 < N / n := lt_of_lt_of_le hM4_pos hy_ge
    have hterm_m : ∀ m ∈ Icc 1 M,
        |a m * (poleProfileCorrection (normalizedRamanujanMode m) (N / n) n +
            (Real.log m + tameDifferent m) * normalizedRamanujanMode m n)| ≤
          |a m| * (4 / (M : ℝ)) := by
      intro m hm
      obtain ⟨hm1, hmM⟩ := mem_Icc.mp hm
      have hcor := abs_normalizedRamanujan_correction_le hm1 hn0 hy0
      have hφm : Real.sqrt (m.totient : ℝ) ≤ Real.sqrt M :=
        Real.sqrt_le_sqrt (by exact_mod_cast (Nat.totient_le m).trans hmM)
      have hlogm : Real.log m ≤ M := by
        have h1 : Real.log m ≤ (m : ℝ) := by
          linarith only [Real.log_le_sub_one_of_pos (show (0 : ℝ) < m by exact_mod_cast hm1)]
        exact h1.trans (by exact_mod_cast hmM)
      have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
      have hsM_le : Real.sqrt M ≤ M := by
        have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (by omega : 1 ≤ M)
        nlinarith only [Real.sq_sqrt hM0.le, Real.sqrt_nonneg M, hM1,
          sq_nonneg (Real.sqrt M - 1)]
      have hnum : 4 * Real.sqrt (m.totient : ℝ) * Real.log m ≤ 4 * (M : ℝ) ^ 2 := by
        have hmul : Real.sqrt (m.totient : ℝ) * Real.log m ≤ (M : ℝ) * M :=
          mul_le_mul (hφm.trans hsM_le) hlogm (Real.log_natCast_nonneg m) hM0.le
        nlinarith only [hmul]
      have hden : (M : ℝ) ^ 3 ≤ ((N / n : ℕ) : ℝ) := by
        have hM34 : M ^ 3 ≤ M ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
        exact_mod_cast hM34.trans hy_ge
      have hquot : 4 * Real.sqrt (m.totient : ℝ) * Real.log m / ((N / n : ℕ) : ℝ) ≤
          4 / (M : ℝ) := by
        rw [div_le_div_iff₀ (by exact_mod_cast hy0) hM0]
        nlinarith only [hnum, hden, hM0]
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hcor.trans hquot) (abs_nonneg _)
    have habs_sum :
        |∑ m ∈ Icc 1 M, a m * (poleProfileCorrection (normalizedRamanujanMode m) (N / n) n +
            (Real.log m + tameDifferent m) * normalizedRamanujanMode m n)| ≤
          (4 / (M : ℝ)) * ∑ m ∈ Icc 1 M, |a m| := by
      calc
        _ ≤ ∑ m ∈ Icc 1 M, |a m| * (4 / (M : ℝ)) :=
          (abs_sum_le_sum_abs _ _).trans (sum_le_sum hterm_m)
        _ = (4 / (M : ℝ)) * ∑ m ∈ Icc 1 M, |a m| := by
          rw [mul_sum]
          exact sum_congr rfl fun _ _ => mul_comm _ _
    have hcs_a : (∑ m ∈ Icc 1 M, |a m|) ^ 2 ≤ (M : ℝ) * ∑ m ∈ Icc 1 M, a m ^ 2 := by
      have h := Finset.sum_mul_sq_le_sq_mul_sq (Icc 1 M) (fun _ => (1 : ℝ)) (fun m => |a m|)
      simpa only [one_mul, one_pow, sum_const, Nat.card_Icc, Nat.add_sub_cancel,
        nsmul_eq_mul, mul_one, sq_abs] using h
    have hsq_sum :
        (∑ m ∈ Icc 1 M, a m * (poleProfileCorrection (normalizedRamanujanMode m) (N / n) n +
            (Real.log m + tameDifferent m) * normalizedRamanujanMode m n)) ^ 2 ≤
          16 * ∑ m ∈ Icc 1 M, a m ^ 2 := by
      have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (by omega : 1 ≤ M)
      have hM0 : (0 : ℝ) < M := zero_lt_one.trans_le hM1
      have h1 := pow_le_pow_left₀ (abs_nonneg _) habs_sum 2
      rw [sq_abs, mul_pow] at h1
      calc
        _ ≤ (4 / (M : ℝ)) ^ 2 * ((M : ℝ) * ∑ m ∈ Icc 1 M, a m ^ 2) :=
          h1.trans (mul_le_mul_of_nonneg_left hcs_a (sq_nonneg _))
        _ = (16 / (M : ℝ)) * ∑ m ∈ Icc 1 M, a m ^ 2 := by field_simp [hM0.ne']; ring
        _ ≤ 16 * ∑ m ∈ Icc 1 M, a m ^ 2 :=
          mul_le_mul_of_nonneg_right (div_le_self (by norm_num) hM1)
            (sum_nonneg fun _ _ => sq_nonneg _)
    unfold packetPrimeCorrTerm
    rw [mul_pow, poleVector_sq]
    calc
      1 / (n : ℝ) * (∑ m ∈ Icc 1 M, a m * _) ^ 2 ≤
          1 / (n : ℝ) * (16 * ∑ m ∈ Icc 1 M, a m ^ 2) :=
        mul_le_mul_of_nonneg_left hsq_sum (by positivity)
      _ = (16 / (n : ℝ)) * ∑ m ∈ Icc 1 M, a m ^ 2 := by ring
  have hhar_K : (∑ n ∈ Icc 1 (N / M ^ 4), (1 / (n : ℝ))) ≤ 2 * Real.log N := by
    have hsub : Icc 1 (N / M ^ 4) ⊆ Icc 1 N := Icc_subset_Icc_right hKN
    have h1 : (∑ n ∈ Icc 1 (N / M ^ 4), (1 / (n : ℝ))) ≤
        RenormalizedArithmeticPotentialTheory.harmonicSum N :=
      sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    have h2 := RenormalizedArithmeticPotentialTheory.harmonicSum_le_one_add_log N
    linarith only [h1, h2, hL1]
  have hSa0 : 0 ≤ ∑ m ∈ Icc 1 M, a m ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  calc
    (Real.log N)⁻¹ * (∑ n ∈ Icc 1 (N / M ^ 4), packetPrimeCorrTerm M N a n ^ 2) ≤
        (Real.log N)⁻¹ * ∑ n ∈ Icc 1 (N / M ^ 4), (16 / (n : ℝ)) * ∑ m ∈ Icc 1 M, a m ^ 2 :=
      mul_le_mul_of_nonneg_left (sum_le_sum hcorr_deep) (inv_nonneg.mpr hL0.le)
    _ = (Real.log N)⁻¹ *
          ((16 * ∑ n ∈ Icc 1 (N / M ^ 4), (1 / (n : ℝ))) * ∑ m ∈ Icc 1 M, a m ^ 2) := by
      congr 1
      rw [← sum_mul]
      congr 1
      rw [mul_sum]
      exact sum_congr rfl fun _ _ => by ring
    _ ≤ (Real.log N)⁻¹ * ((16 * (2 * Real.log N)) * ∑ m ∈ Icc 1 M, a m ^ 2) := by
      refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hL0.le)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hhar_K (by norm_num)) hSa0
    _ = 32 * ∑ m ∈ Icc 1 M, a m ^ 2 := by field_simp [hL0.ne']; ring

/-- Top-strip upward prime-jump Plancherel bound on `Ioc (N / M ^ 4) N` via reduced Ramanujan
dilations, incurring only `(1 + log M) ^ 4 * ∑ a_m^2`. -/
private theorem sum_top_upJump_sq_le
    {M N : ℕ} (hM : 2 ≤ M) (hMK : M * M ≤ N / M ^ 4) (hKN : N / M ^ 4 ≤ N)
    (hhar_NK : (harmonic N : ℝ) - harmonic (N / M ^ 4) + 2 ≤ 4 * (1 + Real.log M))
    {C_mert : ℝ} (hC_mert1 : 1 ≤ C_mert)
    (hmert_M4 : mertensSum (M ^ 4) ≤ (C_mert + 4) * (1 + Real.log M))
    (a : ℕ → ℝ) :
    (∑ n ∈ Ioc (N / M ^ 4) N,
        (poleVector n * ∑ t ∈ Icc 1 (N / n),
          (∑ m ∈ Icc 1 M, a m * normalizedRamanujanMode m (n * t)) * Λ t / (t : ℝ)) ^ 2) ≤
      (8 * (C_mert + 4) ^ 2 + 32 * (C_mert + 4)) * (1 + Real.log M) ^ 4 *
        ∑ m ∈ Icc 1 M, a m ^ 2 := by
  have hM4_pos : 0 < M ^ 4 := pow_pos (by omega) 4
  have hquot_lt_M4 : ∀ n ∈ Ioc (N / M ^ 4) N, N / n ≤ M ^ 4 := by
    intro n hn
    obtain ⟨hKn, _⟩ := mem_Ioc.mp hn
    have hn0 : 0 < n := by omega
    have hlt_mul : N < M ^ 4 * n := by
      rw [Nat.mul_comm]
      exact (Nat.div_lt_iff_lt_mul hM4_pos).mp hKn
    exact ((Nat.div_lt_iff_lt_mul hn0).mpr hlt_mul).le
  let G : ℕ → ℝ := fun j => ∑ m ∈ Icc 1 M, a m * normalizedRamanujanMode m j
  have hup_cs : ∀ n ∈ Ioc (N / M ^ 4) N,
      (poleVector n * ∑ t ∈ Icc 1 (N / n), G (n * t) * Λ t / (t : ℝ)) ^ 2 ≤
        mertensSum (M ^ 4) *
          ∑ t ∈ Icc 2 (M ^ 4), (Λ t / (t : ℝ)) * (G (t * n) * poleVector n) ^ 2 := by
    intro n hn
    have hquot := hquot_lt_M4 n hn
    have ht_sum_eq :
        (∑ t ∈ Icc 1 (N / n), G (n * t) * Λ t / (t : ℝ)) =
          ∑ t ∈ Icc 2 (M ^ 4),
            Real.sqrt (Λ t / (t : ℝ)) *
              (Real.sqrt (Λ t / (t : ℝ)) * (if t ≤ N / n then G (t * n) else 0)) := by
      have hsub_t : Icc 2 (N / n) ⊆ Icc 2 (M ^ 4) := Icc_subset_Icc_right hquot
      have h1_split :
          (∑ t ∈ Icc 1 (N / n), G (n * t) * Λ t / (t : ℝ)) =
            ∑ t ∈ Icc 2 (N / n), G (t * n) * (Λ t / (t : ℝ)) := by
        rcases lt_or_ge (N / n) 1 with hlt1 | hge1
        · have he1 : Icc 1 (N / n) = ∅ := Icc_eq_empty (by omega)
          have he2 : Icc 2 (N / n) = ∅ := Icc_eq_empty (by omega)
          rw [he1, he2, sum_empty, sum_empty]
        · have hunion : Icc 1 (N / n) = {1} ∪ Icc 2 (N / n) := by
            ext t; simp only [mem_Icc, mem_union, mem_singleton]; omega
          have hdisj : Disjoint ({1} : Finset ℕ) (Icc 2 (N / n)) := by
            rw [Finset.disjoint_singleton_left, mem_Icc]; omega
          rw [hunion, sum_union hdisj, sum_singleton, vonMangoldt_apply_one,
            mul_zero, zero_div, zero_add]
          exact sum_congr rfl fun t _ => by rw [Nat.mul_comm]; ring
      rw [h1_split, ← sum_subset hsub_t]
      · refine sum_congr rfl fun t ht => ?_
        rw [if_pos (mem_Icc.mp ht).2, ← mul_assoc,
          Real.mul_self_sqrt (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _)), mul_comm]
      · intro t htI hnot
        have hnle : ¬ t ≤ N / n := fun hle => hnot (mem_Icc.mpr ⟨(mem_Icc.mp htI).1, hle⟩)
        rw [if_neg hnle, mul_zero, mul_zero]
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Icc 2 (M ^ 4))
      (fun t => Real.sqrt (Λ t / (t : ℝ)))
      (fun t => Real.sqrt (Λ t / (t : ℝ)) * (if t ≤ N / n then G (t * n) else 0))
    have h1_mert :
        (∑ t ∈ Icc 2 (M ^ 4), Real.sqrt (Λ t / (t : ℝ)) ^ 2) ≤ mertensSum (M ^ 4) := by
      have hsq : ∀ t ∈ Icc 2 (M ^ 4), Real.sqrt (Λ t / (t : ℝ)) ^ 2 = Λ t / (t : ℝ) :=
        fun t _ => Real.sq_sqrt (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _))
      rw [sum_congr rfl hsq]
      exact sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_left (by omega))
        fun _ _ _ => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _)
    have h2_le :
        (∑ t ∈ Icc 2 (M ^ 4),
            (Real.sqrt (Λ t / (t : ℝ)) * (if t ≤ N / n then G (t * n) else 0)) ^ 2) ≤
          ∑ t ∈ Icc 2 (M ^ 4), (Λ t / (t : ℝ)) * G (t * n) ^ 2 := by
      refine sum_le_sum fun t _ => ?_
      rw [mul_pow, Real.sq_sqrt (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _))]
      refine mul_le_mul_of_nonneg_left ?_ (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _))
      split_ifs
      · exact le_rfl
      · rw [zero_pow (by norm_num)]; exact sq_nonneg _
    rw [mul_pow, ht_sum_eq]
    calc
      poleVector n ^ 2 * (∑ t ∈ Icc 2 (M ^ 4), _) ^ 2 ≤
          poleVector n ^ 2 * (mertensSum (M ^ 4) *
            ∑ t ∈ Icc 2 (M ^ 4), (Λ t / (t : ℝ)) * G (t * n) ^ 2) := by
        refine mul_le_mul_of_nonneg_left (hcs.trans ?_) (sq_nonneg _)
        exact mul_le_mul h1_mert h2_le
          (sum_nonneg fun _ _ => sq_nonneg _)
          (sum_nonneg fun _ _ => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _))
      _ = mertensSum (M ^ 4) *
            ∑ t ∈ Icc 2 (M ^ 4), (Λ t / (t : ℝ)) * (G (t * n) * poleVector n) ^ 2 := by
        rw [← mul_assoc, mul_comm (poleVector n ^ 2), mul_assoc, mul_sum]
        congr 1; exact sum_congr rfl fun t _ => by ring
  have hfor_t : ∀ t ∈ Icc 2 (M ^ 4),
      (Λ t / (t : ℝ)) * (∑ n ∈ Ioc (N / M ^ 4) N, (G (t * n) * poleVector n) ^ 2) ≤
        4 * (1 + Real.log M) * (Λ t / (t : ℝ)) *
          (2 * (∑ m ∈ Icc 1 M, a m ^ 2) +
            4 * Real.log M * ∑ m ∈ Icc 1 M, a m ^ 2 *
              ∑ g ∈ m.divisors.filter (2 ≤ ·), if g ∣ t then (g : ℝ) else 0) := by
    intro t _
    by_cases hΛt : Λ t = 0
    · simp [hΛt]
    · have htpp : IsPrimePow t := vonMangoldt_ne_zero_iff.mp hΛt
      have hred_n : ∀ n ∈ Ioc (N / M ^ 4) N,
          (G (t * n) * poleVector n) ^ 2 =
            (∑ d ∈ Icc 1 M, reducedDilationCoeff M a t d * ramanujanPoleProfile d n) ^ 2 := by
        intro n _
        congr 1
        dsimp only [G]
        rw [sum_normalizedRamanujanMode_dilate_eq_reduced, sum_mul]
        exact sum_congr rfl fun d _ => by
          rw [ramanujanPoleProfile_eq_mul_poleVector, mul_assoc]
      have hpack_t :
          (∑ n ∈ Ioc (N / M ^ 4) N, (G (t * n) * poleVector n) ^ 2) ≤
            4 * (1 + Real.log M) * ∑ d ∈ Icc 1 M, reducedDilationCoeff M a t d ^ 2 := by
        rw [sum_congr rfl hred_n]
        exact (sum_Ioc_packet_sq_le hM hMK hKN _).trans
          (mul_le_mul_of_nonneg_right hhar_NK (sum_nonneg fun _ _ => sq_nonneg _))
      have hdil := sum_reducedDilationCoeff_sq_le hM htpp a
      have hΛ_div0 : 0 ≤ Λ t / (t : ℝ) := div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _)
      have hLM4_0 : 0 ≤ 4 * (1 + Real.log M) := by
        have := Real.log_natCast_nonneg M; positivity
      calc
        (Λ t / (t : ℝ)) * (∑ n ∈ Ioc (N / M ^ 4) N, (G (t * n) * poleVector n) ^ 2) ≤
            (Λ t / (t : ℝ)) *
              (4 * (1 + Real.log M) * ∑ d ∈ Icc 1 M, reducedDilationCoeff M a t d ^ 2) :=
          mul_le_mul_of_nonneg_left hpack_t hΛ_div0
        _ ≤ (Λ t / (t : ℝ)) *
              (4 * (1 + Real.log M) *
                (2 * (∑ m ∈ Icc 1 M, a m ^ 2) +
                  4 * Real.log M * ∑ m ∈ Icc 1 M, a m ^ 2 *
                    ∑ g ∈ m.divisors.filter (2 ≤ ·), if g ∣ t then (g : ℝ) else 0)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdil hLM4_0) hΛ_div0
        _ = _ := by ring
  have hdiv_t_sum :
      (∑ t ∈ Icc 2 (M ^ 4), (Λ t / (t : ℝ)) *
          ∑ m ∈ Icc 1 M, a m ^ 2 *
            ∑ g ∈ m.divisors.filter (2 ≤ ·), if g ∣ t then (g : ℝ) else 0) ≤
        2 * Real.log M * ∑ m ∈ Icc 1 M, a m ^ 2 := by
    have hswap1 :
        (∑ t ∈ Icc 2 (M ^ 4), (Λ t / (t : ℝ)) *
            ∑ m ∈ Icc 1 M, a m ^ 2 *
              ∑ g ∈ m.divisors.filter (2 ≤ ·), if g ∣ t then (g : ℝ) else 0) =
          ∑ m ∈ Icc 1 M, a m ^ 2 *
            ∑ g ∈ m.divisors.filter (2 ≤ ·),
              ∑ t ∈ Icc 2 (M ^ 4), if g ∣ t then (Λ t / (t : ℝ)) * (g : ℝ) else 0 := by
      simp_rw [mul_sum]
      rw [sum_comm]
      refine sum_congr rfl fun m _ => ?_
      rw [sum_comm]
      refine sum_congr rfl fun g _ => ?_
      exact sum_congr rfl fun t _ => by split_ifs <;> ring
    rw [hswap1, mul_sum]
    refine sum_le_sum fun m hm => ?_
    obtain ⟨hm1, hmM⟩ := mem_Icc.mp hm
    have hg_sum :
        (∑ g ∈ m.divisors.filter (2 ≤ ·),
            ∑ t ∈ Icc 2 (M ^ 4), if g ∣ t then (Λ t / (t : ℝ)) * (g : ℝ) else 0) ≤
          2 * Real.log M := by
      calc
        _ ≤ ∑ g ∈ m.divisors.filter (2 ≤ ·), 2 * Λ g :=
          sum_le_sum fun g hg => sum_Icc_dvd_vonMangoldt_mul_le (mem_filter.mp hg).2 (M ^ 4)
        _ ≤ ∑ g ∈ m.divisors, 2 * Λ g :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
            fun _ _ _ => mul_nonneg zero_le_two vonMangoldt_nonneg
        _ = 2 * Real.log m := by rw [← mul_sum, vonMangoldt_sum]
        _ ≤ 2 * Real.log M := mul_le_mul_of_nonneg_left
          (Real.log_le_log (by exact_mod_cast hm1) (by exact_mod_cast hmM)) zero_le_two
    rw [mul_comm (2 * Real.log M)]
    exact mul_le_mul_of_nonneg_left hg_sum (sq_nonneg _)
  have hmert_Icc2 : (∑ t ∈ Icc 2 (M ^ 4), Λ t / (t : ℝ)) ≤ mertensSum (M ^ 4) :=
    sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_left (by omega))
      fun _ _ _ => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _)
  have hSa0 : 0 ≤ ∑ m ∈ Icc 1 M, a m ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hinner_t_sum :
      (∑ t ∈ Icc 2 (M ^ 4),
          (Λ t / (t : ℝ)) * ∑ n ∈ Ioc (N / M ^ 4) N, (G (t * n) * poleVector n) ^ 2) ≤
        (8 * (C_mert + 4) + 32) * (1 + Real.log M) ^ 3 * ∑ m ∈ Icc 1 M, a m ^ 2 := by
    have hstep1 := sum_le_sum hfor_t
    have hterm_rew : ∀ t ∈ Icc 2 (M ^ 4),
        4 * (1 + Real.log M) * (Λ t / (t : ℝ)) *
            (2 * (∑ m ∈ Icc 1 M, a m ^ 2) +
              4 * Real.log M * ∑ m ∈ Icc 1 M, a m ^ 2 *
                ∑ g ∈ m.divisors.filter (2 ≤ ·), if g ∣ t then (g : ℝ) else 0) =
          (8 * (1 + Real.log M) * (∑ m ∈ Icc 1 M, a m ^ 2)) * (Λ t / (t : ℝ)) +
            (16 * (1 + Real.log M) * Real.log M) *
              ((Λ t / (t : ℝ)) * ∑ m ∈ Icc 1 M, a m ^ 2 *
                ∑ g ∈ m.divisors.filter (2 ≤ ·), if g ∣ t then (g : ℝ) else 0) :=
      fun _ _ => by ring
    have hrew_rhs :
        (∑ t ∈ Icc 2 (M ^ 4),
            4 * (1 + Real.log M) * (Λ t / (t : ℝ)) *
              (2 * (∑ m ∈ Icc 1 M, a m ^ 2) +
                4 * Real.log M * ∑ m ∈ Icc 1 M, a m ^ 2 *
                  ∑ g ∈ m.divisors.filter (2 ≤ ·), if g ∣ t then (g : ℝ) else 0)) =
          8 * (1 + Real.log M) * (∑ t ∈ Icc 2 (M ^ 4), Λ t / (t : ℝ)) *
              (∑ m ∈ Icc 1 M, a m ^ 2) +
            16 * (1 + Real.log M) * Real.log M *
              (∑ t ∈ Icc 2 (M ^ 4), (Λ t / (t : ℝ)) *
                ∑ m ∈ Icc 1 M, a m ^ 2 *
                  ∑ g ∈ m.divisors.filter (2 ≤ ·), if g ∣ t then (g : ℝ) else 0) := by
      rw [sum_congr rfl hterm_rew, sum_add_distrib, ← mul_sum, ← mul_sum]
      ring
    rw [hrew_rhs] at hstep1
    have hLM0 := Real.log_natCast_nonneg M
    have hLM_le : Real.log M ≤ 1 + Real.log M := by linarith only []
    have hpart1 :
        8 * (1 + Real.log M) * (∑ t ∈ Icc 2 (M ^ 4), Λ t / (t : ℝ)) *
            (∑ m ∈ Icc 1 M, a m ^ 2) ≤
          8 * (C_mert + 4) * (1 + Real.log M) ^ 3 * ∑ m ∈ Icc 1 M, a m ^ 2 := by
      have hm1 : (∑ t ∈ Icc 2 (M ^ 4), Λ t / (t : ℝ)) ≤ (C_mert + 4) * (1 + Real.log M) :=
        hmert_Icc2.trans hmert_M4
      have hp1 : 8 * (1 + Real.log M) * (∑ t ∈ Icc 2 (M ^ 4), Λ t / (t : ℝ)) *
            (∑ m ∈ Icc 1 M, a m ^ 2) ≤
          8 * (1 + Real.log M) * ((C_mert + 4) * (1 + Real.log M)) * ∑ m ∈ Icc 1 M, a m ^ 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hm1 (by positivity)) hSa0
      have hpow23 : (1 + Real.log M) ^ 2 ≤ (1 + Real.log M) ^ 3 := by
        nlinarith only [hLM0, sq_nonneg (1 + Real.log M)]
      calc
        _ ≤ 8 * (C_mert + 4) * (1 + Real.log M) ^ 2 * ∑ m ∈ Icc 1 M, a m ^ 2 := by
          linarith only [hp1, (by ring :
            8 * (1 + Real.log M) * ((C_mert + 4) * (1 + Real.log M)) * ∑ m ∈ Icc 1 M, a m ^ 2 =
              8 * (C_mert + 4) * (1 + Real.log M) ^ 2 * ∑ m ∈ Icc 1 M, a m ^ 2)]
        _ ≤ 8 * (C_mert + 4) * (1 + Real.log M) ^ 3 * ∑ m ∈ Icc 1 M, a m ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpow23 (by positivity)) hSa0
    have hpart2 :
        16 * (1 + Real.log M) * Real.log M *
            (∑ t ∈ Icc 2 (M ^ 4), (Λ t / (t : ℝ)) *
              ∑ m ∈ Icc 1 M, a m ^ 2 *
                ∑ g ∈ m.divisors.filter (2 ≤ ·), if g ∣ t then (g : ℝ) else 0) ≤
          32 * (1 + Real.log M) ^ 3 * ∑ m ∈ Icc 1 M, a m ^ 2 := by
      have hnonneg_div : 0 ≤ ∑ t ∈ Icc 2 (M ^ 4), (Λ t / (t : ℝ)) *
          ∑ m ∈ Icc 1 M, a m ^ 2 *
            ∑ g ∈ m.divisors.filter (2 ≤ ·), if g ∣ t then (g : ℝ) else 0 :=
        sum_nonneg fun _ _ => mul_nonneg (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _))
          (sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _)
            (sum_nonneg fun g _ => by
              by_cases h : g ∣ _
              · simp [h]
              · simp [h]))
      have hp2 :
          16 * (1 + Real.log M) * Real.log M *
              (∑ t ∈ Icc 2 (M ^ 4), (Λ t / (t : ℝ)) *
                ∑ m ∈ Icc 1 M, a m ^ 2 *
                  ∑ g ∈ m.divisors.filter (2 ≤ ·), if g ∣ t then (g : ℝ) else 0) ≤
            16 * (1 + Real.log M) * (1 + Real.log M) *
              (2 * (1 + Real.log M) * ∑ m ∈ Icc 1 M, a m ^ 2) :=
        mul_le_mul
          (mul_le_mul_of_nonneg_left hLM_le (by positivity))
          (hdiv_t_sum.trans
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLM_le zero_le_two) hSa0))
          hnonneg_div (by positivity)
      linarith only [hp2, (by ring :
        16 * (1 + Real.log M) * (1 + Real.log M) *
          (2 * (1 + Real.log M) * ∑ m ∈ Icc 1 M, a m ^ 2) =
          32 * (1 + Real.log M) ^ 3 * ∑ m ∈ Icc 1 M, a m ^ 2)]
    linarith only [hstep1, hpart1, hpart2]
  calc
    (∑ n ∈ Ioc (N / M ^ 4) N,
        (poleVector n * ∑ t ∈ Icc 1 (N / n), G (n * t) * Λ t / (t : ℝ)) ^ 2) ≤
        mertensSum (M ^ 4) *
          ∑ n ∈ Ioc (N / M ^ 4) N, ∑ t ∈ Icc 2 (M ^ 4),
            (Λ t / (t : ℝ)) * (G (t * n) * poleVector n) ^ 2 := by
      rw [mul_sum]; exact sum_le_sum hup_cs
    _ = mertensSum (M ^ 4) *
          ∑ t ∈ Icc 2 (M ^ 4),
            (Λ t / (t : ℝ)) * ∑ n ∈ Ioc (N / M ^ 4) N, (G (t * n) * poleVector n) ^ 2 := by
      congr 1; rw [sum_comm]; exact sum_congr rfl fun _ _ => (mul_sum _ _ _).symm
    _ ≤ ((C_mert + 4) * (1 + Real.log M)) *
          ((8 * (C_mert + 4) + 32) * (1 + Real.log M) ^ 3 * ∑ m ∈ Icc 1 M, a m ^ 2) :=
      mul_le_mul hmert_M4 hinner_t_sum
        (sum_nonneg fun _ _ => mul_nonneg (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _))
          (sum_nonneg fun _ _ => sq_nonneg _))
        (by have := Real.log_natCast_nonneg M; positivity)
    _ = (8 * (C_mert + 4) ^ 2 + 32 * (C_mert + 4)) * (1 + Real.log M) ^ 4 *
          ∑ m ∈ Icc 1 M, a m ^ 2 := by ring

/-- Top-strip bound on `Ioc (N / M ^ 4) N` combining upward prime jumps, Mertens diagonal,
downward divisor jet, and adjunction energy. -/
private theorem sum_top_packetPrimeCorrTerm_sq_le
    {M N : ℕ} (hM : 2 ≤ M) (hM6N : M ^ 6 ≤ N) (hlog : 18 * (1 + Real.log M) ≤ Real.log N)
    {C_mert C_jet : ℝ} (hC_mert1 : 1 ≤ C_mert) (hC_jet_pos : 0 < C_jet)
    (hmert_le : ∀ y : ℕ, 1 ≤ y → mertensSum y ≤ Real.log y + C_mert)
    (hC_jet : ∀ {M N : ℕ}, 2 ≤ M → M * M ≤ N → 18 * (1 + Real.log M) ≤ Real.log N →
      ∀ a : ℕ → ℝ, ‖divisorJetHorizonVector M N a‖ ≤
        C_jet * (1 + Real.log M) * Real.sqrt (∑ m ∈ Icc 1 M, a m ^ 2))
    (a : ℕ → ℝ) :
    (Real.log N)⁻¹ * (∑ n ∈ Ioc (N / M ^ 4) N, packetPrimeCorrTerm M N a n ^ 2) ≤
      (80 * (C_mert + 4) ^ 2 + 32 * C_jet ^ 2 + 64) *
        ((1 + Real.log M) ^ 4 / Real.log N) * ∑ m ∈ Icc 1 M, a m ^ 2 := by
  have hM4_pos : 0 < M ^ 4 := pow_pos (by omega) 4
  have hMM_le_N : M * M ≤ N := by
    have hpow : M * M ≤ M ^ 6 := by
      calc
        M * M = M ^ 2 := (sq M).symm
        _ ≤ M ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
    exact hpow.trans hM6N
  have hMK : M * M ≤ N / M ^ 4 := by
    refine (Nat.le_div_iff_mul_le hM4_pos).mpr ?_
    calc
      M * M * M ^ 4 = M ^ 6 := by ring
      _ ≤ N := hM6N
  have hKN : N / M ^ 4 ≤ N := Nat.div_le_self N (M ^ 4)
  have hK1 : 1 ≤ N / M ^ 4 := (Nat.mul_le_mul hM hM).trans hMK |>.trans' (by omega)
  have hL0 : 0 < Real.log N := by
    have := Real.log_natCast_nonneg M; linarith only [hlog, this]
  have hsL0 : 0 < Real.sqrt (Real.log N) := Real.sqrt_pos.mpr hL0
  have hhar_NK : (harmonic N : ℝ) - harmonic (N / M ^ 4) + 2 ≤ 4 * (1 + Real.log M) := by
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (hK1.trans hKN)
    have hK0 : (0 : ℝ) < (N / M ^ 4 : ℕ) := by exact_mod_cast hK1
    have hNK_nat : N < (N / M ^ 4 + 1) * M ^ 4 := by
      have h1 : M ^ 4 * (N / M ^ 4) + N % M ^ 4 = N := Nat.div_add_mod N (M ^ 4)
      have h2 : N % M ^ 4 < M ^ 4 := Nat.mod_lt N hM4_pos
      calc
        N = M ^ 4 * (N / M ^ 4) + N % M ^ 4 := h1.symm
        _ < M ^ 4 * (N / M ^ 4) + M ^ 4 := Nat.add_lt_add_left h2 _
        _ = (N / M ^ 4 + 1) * M ^ 4 := by ring
    have hNK_le : (N : ℝ) / ((N / M ^ 4 : ℕ) : ℝ) ≤ 2 * (M : ℝ) ^ 4 := by
      rw [div_le_iff₀ hK0]
      have hcast : (N : ℝ) ≤ (((N / M ^ 4 : ℕ) : ℝ) + 1) * (M : ℝ) ^ 4 := by
        exact_mod_cast hNK_nat.le
      have hK1R : (1 : ℝ) ≤ (N / M ^ 4 : ℕ) := by exact_mod_cast hK1
      nlinarith only [hcast, hK1R, show (0 : ℝ) ≤ (M : ℝ) ^ 4 by positivity]
    have hHN : (harmonic N : ℝ) ≤ 1 + Real.log N := harmonic_le_one_add_log N
    have hHK : Real.log ((N / M ^ 4 : ℕ) : ℝ) ≤ (harmonic (N / M ^ 4) : ℝ) :=
      (Real.log_le_log hK0 (by exact_mod_cast Nat.le_succ (N / M ^ 4))).trans
        (log_add_one_le_harmonic (N / M ^ 4))
    have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
      linarith only [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
    have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
    have hlog_NK : Real.log ((N : ℝ) / ((N / M ^ 4 : ℕ) : ℝ)) ≤ 1 + 4 * Real.log M := by
      calc
        Real.log ((N : ℝ) / ((N / M ^ 4 : ℕ) : ℝ)) ≤ Real.log (2 * (M : ℝ) ^ 4) :=
          Real.log_le_log (div_pos hN0 hK0) hNK_le
        _ = Real.log 2 + 4 * Real.log M := by
          rw [Real.log_mul (by norm_num) (pow_ne_zero 4 hM0.ne'), Real.log_pow]; ring
        _ ≤ 1 + 4 * Real.log M := by linarith only [hlog2]
    rw [Real.log_div hN0.ne' hK0.ne'] at hlog_NK
    linarith only [hHN, hHK, hlog_NK]
  have hmert_M4 : mertensSum (M ^ 4) ≤ (C_mert + 4) * (1 + Real.log M) := by
    have hm := hmert_le (M ^ 4) (by omega)
    rw [Nat.cast_pow, Real.log_pow] at hm
    push_cast at hm
    have hLM0 := Real.log_natCast_nonneg M
    nlinarith only [hm, hLM0, hC_mert1]
  have hquot_lt_M4 : ∀ n ∈ Ioc (N / M ^ 4) N, N / n ≤ M ^ 4 := by
    intro n hn
    obtain ⟨hKn, _⟩ := mem_Ioc.mp hn
    have hn0 : 0 < n := by omega
    have hlt_mul : N < M ^ 4 * n := by
      rw [Nat.mul_comm]
      exact (Nat.div_lt_iff_lt_mul hM4_pos).mp hKn
    exact ((Nat.div_lt_iff_lt_mul hn0).mpr hlt_mul).le
  let G : ℕ → ℝ := fun j => ∑ m ∈ Icc 1 M, a m * normalizedRamanujanMode m j
  let upJump : ℕ → ℝ := fun n =>
    poleVector n * ∑ t ∈ Icc 1 (N / n), G (n * t) * Λ t / (t : ℝ)
  let mertTop : ℕ → ℝ := fun n => mertensSum (N / n) * (poleVector n * G n)
  let jetTop : ℕ → ℝ := fun n =>
    poleVector n * ∑ m ∈ Icc 1 M, a m * (ramanujanLogDivisorJet m n / Real.sqrt (m.totient : ℝ))
  let energyTop : ℕ → ℝ := fun n =>
    poleVector n * ∑ m ∈ Icc 1 M,
      (a m * (Real.log m + tameDifferent m)) * normalizedRamanujanMode m n
  have hcorr_top_eq : ∀ n ∈ Ioc (N / M ^ 4) N,
      packetPrimeCorrTerm M N a n = upJump n - mertTop n - jetTop n + energyTop n := by
    intro n hn
    have hn0 : 0 < n := by have := (mem_Ioc.mp hn).1; omega
    unfold packetPrimeCorrTerm
    dsimp only [upJump, mertTop, jetTop, energyTop, G]
    have hterm_m : ∀ m ∈ Icc 1 M,
        a m * (poleProfileCorrection (normalizedRamanujanMode m) (N / n) n +
            (Real.log m + tameDifferent m) * normalizedRamanujanMode m n) =
          (∑ t ∈ Icc 1 (N / n), a m * normalizedRamanujanMode m (n * t) * Λ t / (t : ℝ)) -
            mertensSum (N / n) * (a m * normalizedRamanujanMode m n) -
            a m * (ramanujanLogDivisorJet m n / Real.sqrt (m.totient : ℝ)) +
            (a m * (Real.log m + tameDifferent m)) * normalizedRamanujanMode m n := by
      intro m hm
      have hm0 : 0 < m := (mem_Icc.mp hm).1
      have hdown :
          (∑ d ∈ n.divisors,
              (normalizedRamanujanMode m (n / d) - normalizedRamanujanMode m n) * Λ d) =
            -(ramanujanLogDivisorJet m n / Real.sqrt (m.totient : ℝ)) := by
        simp_rw [normalizedRamanujanMode_eq_coefficient hm0]
        have hsub_d : ∀ d ∈ n.divisors,
            (ramanujanLagCoefficient m (n / d) / Real.sqrt (m.totient : ℝ) -
                ramanujanLagCoefficient m n / Real.sqrt (m.totient : ℝ)) * Λ d =
              ((ramanujanLagCoefficient m (n / d) - ramanujanLagCoefficient m n) * Λ d) /
                Real.sqrt (m.totient : ℝ) := fun _ _ => by ring
        rw [sum_congr rfl hsub_d, ← sum_div, ← ramanujanDownCorrection,
          ramanujanDownCorrection_eq_neg_logDivisorJet m hn0, neg_div]
      have hup :
          (∑ t ∈ Icc 1 (N / n),
              (normalizedRamanujanMode m (n * t) - normalizedRamanujanMode m n) * Λ t / (t : ℝ)) =
            (∑ t ∈ Icc 1 (N / n), normalizedRamanujanMode m (n * t) * Λ t / (t : ℝ)) -
              mertensSum (N / n) * normalizedRamanujanMode m n := by
        unfold mertensSum
        rw [mul_comm _ (normalizedRamanujanMode m n), mul_sum, ← sum_sub_distrib]
        exact sum_congr rfl fun t _ => by ring
      have hsum_t : a m * (∑ t ∈ Icc 1 (N / n),
          normalizedRamanujanMode m (n * t) * Λ t / (t : ℝ)) =
          ∑ t ∈ Icc 1 (N / n), a m * normalizedRamanujanMode m (n * t) * Λ t / (t : ℝ) := by
        rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
      rw [poleProfileCorrection_eq_divisor_jumps, hup, hdown]
      linear_combination hsum_t
    rw [sum_congr rfl hterm_m]
    simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum]
    have hswap_t :
        (∑ m ∈ Icc 1 M, ∑ t ∈ Icc 1 (N / n),
            a m * normalizedRamanujanMode m (n * t) * Λ t / (t : ℝ)) =
          ∑ t ∈ Icc 1 (N / n),
            (∑ m ∈ Icc 1 M, a m * normalizedRamanujanMode m (n * t)) * Λ t / (t : ℝ) := by
      rw [sum_comm]
      refine sum_congr rfl fun t _ => ?_
      rw [sum_mul, sum_div]
    rw [hswap_t]
    ring
  have h4sq : ∀ n ∈ Ioc (N / M ^ 4) N,
      packetPrimeCorrTerm M N a n ^ 2 ≤
        4 * upJump n ^ 2 + 4 * mertTop n ^ 2 + 4 * jetTop n ^ 2 + 4 * energyTop n ^ 2 := by
    intro n hn
    rw [hcorr_top_eq n hn]
    nlinarith only [sq_nonneg (upJump n + mertTop n), sq_nonneg (upJump n + jetTop n),
      sq_nonneg (upJump n - energyTop n), sq_nonneg (mertTop n - jetTop n),
      sq_nonneg (mertTop n + energyTop n), sq_nonneg (jetTop n + energyTop n)]
  have hSa0 : 0 ≤ ∑ m ∈ Icc 1 M, a m ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  -- Sub-bound (i): `mertTop`.
  have hmertTop_sum :
      (∑ n ∈ Ioc (N / M ^ 4) N, mertTop n ^ 2) ≤
        4 * (C_mert + 4) ^ 2 * (1 + Real.log M) ^ 3 * ∑ m ∈ Icc 1 M, a m ^ 2 := by
    have hpt : ∀ n ∈ Ioc (N / M ^ 4) N,
        mertTop n ^ 2 ≤ ((C_mert + 4) * (1 + Real.log M)) ^ 2 * (poleVector n * G n) ^ 2 := by
      intro n hn
      have hmono : mertensSum (N / n) ≤ mertensSum (M ^ 4) :=
        sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right (hquot_lt_M4 n hn))
          fun _ _ _ => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _)
      have hm0 : 0 ≤ mertensSum (N / n) :=
        sum_nonneg fun _ _ => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _)
      dsimp only [mertTop]
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hm0 (hmono.trans hmert_M4) 2) (sq_nonneg _)
    have hpack_G : (∑ n ∈ Ioc (N / M ^ 4) N, (poleVector n * G n) ^ 2) ≤
        4 * (1 + Real.log M) * ∑ m ∈ Icc 1 M, a m ^ 2 := by
      have heq_G : ∀ n ∈ Ioc (N / M ^ 4) N,
          (poleVector n * G n) ^ 2 = (∑ m ∈ Icc 1 M, a m * ramanujanPoleProfile m n) ^ 2 := by
        intro n _; congr 1; dsimp only [G]; rw [mul_sum]
        exact sum_congr rfl fun m _ => by rw [ramanujanPoleProfile_eq_mul_poleVector]; ring
      rw [sum_congr rfl heq_G]
      exact (sum_Ioc_packet_sq_le hM hMK hKN a).trans
        (mul_le_mul_of_nonneg_right hhar_NK hSa0)
    calc
      (∑ n ∈ Ioc (N / M ^ 4) N, mertTop n ^ 2) ≤
          ((C_mert + 4) * (1 + Real.log M)) ^ 2 *
            ∑ n ∈ Ioc (N / M ^ 4) N, (poleVector n * G n) ^ 2 := by
        rw [mul_sum]; exact sum_le_sum hpt
      _ ≤ ((C_mert + 4) * (1 + Real.log M)) ^ 2 *
            (4 * (1 + Real.log M) * ∑ m ∈ Icc 1 M, a m ^ 2) :=
        mul_le_mul_of_nonneg_left hpack_G (sq_nonneg _)
      _ = 4 * (C_mert + 4) ^ 2 * (1 + Real.log M) ^ 3 * ∑ m ∈ Icc 1 M, a m ^ 2 := by ring
  -- Sub-bound (ii): `jetTop`.
  have hjetTop_sum :
      (∑ n ∈ Ioc (N / M ^ 4) N, jetTop n ^ 2) ≤
        8 * C_jet ^ 2 * (1 + Real.log M) ^ 3 * ∑ m ∈ Icc 1 M, a m ^ 2 := by
    have hjet_eq : ∀ n ∈ Ioc (N / M ^ 4) N,
        jetTop n ^ 2 =
          (∑ k ∈ Icc 1 M, divisorJetCoeff M a k * ramanujanPoleProfile k n) ^ 2 := by
      intro n hn
      have hnI : n ∈ Icc 1 N := mem_Icc.mpr
        ⟨by have := (mem_Ioc.mp hn).1; omega, (mem_Ioc.mp hn).2⟩
      have happ := divisorJetHorizonVector_apply M N a ⟨n, hnI⟩
      have hproj : divisorJetHorizonVector M N a ⟨n, hnI⟩ =
          (Real.sqrt (Real.log N))⁻¹ *
            ∑ k ∈ Icc 1 M, divisorJetCoeff M a k * ramanujanPoleProfile k n := by
        change (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : PrimeHorizonIndex N => ℝ) ⟨n, hnI⟩)
          (divisorJetHorizonVector M N a) = _
        dsimp only [divisorJetHorizonVector]
        rw [map_sum, mul_sum]
        refine sum_congr rfl fun k _ => ?_
        change divisorJetCoeff M a k *
          ((Real.sqrt (Real.log N))⁻¹ * ramanujanPoleProfile k n) = _
        ring
      rw [hproj] at happ
      have hcancel := mul_left_cancel₀ (inv_ne_zero hsL0.ne')
        (by simpa only [mul_assoc] using happ)
      dsimp only [jetTop]
      rw [← hcancel]
    rw [sum_congr rfl hjet_eq]
    have hriesz_jet := (half_and_three_halves_riesz_of_log_le hM hMM_le_N hlog
      (divisorJetCoeff M a)).1
    change 1 / 2 * (∑ k ∈ Icc 1 M, divisorJetCoeff M a k ^ 2) ≤
      ‖divisorJetHorizonVector M N a‖ ^ 2 at hriesz_jet
    have hjet_norm := hC_jet hM hMM_le_N hlog a
    have hjet_coeff_sq : (∑ k ∈ Icc 1 M, divisorJetCoeff M a k ^ 2) ≤
        2 * C_jet ^ 2 * (1 + Real.log M) ^ 2 * ∑ m ∈ Icc 1 M, a m ^ 2 := by
      have hsq := pow_le_pow_left₀ (norm_nonneg _) hjet_norm 2
      rw [mul_pow, mul_pow, Real.sq_sqrt hSa0] at hsq
      have h1 : (∑ k ∈ Icc 1 M, divisorJetCoeff M a k ^ 2) ≤
          2 * ‖divisorJetHorizonVector M N a‖ ^ 2 := by linarith only [hriesz_jet]
      calc
        _ ≤ 2 * (C_jet ^ 2 * (1 + Real.log M) ^ 2 * ∑ m ∈ Icc 1 M, a m ^ 2) :=
          h1.trans (mul_le_mul_of_nonneg_left hsq zero_le_two)
        _ = 2 * C_jet ^ 2 * (1 + Real.log M) ^ 2 * ∑ m ∈ Icc 1 M, a m ^ 2 := by ring
    calc
      (∑ n ∈ Ioc (N / M ^ 4) N,
          (∑ k ∈ Icc 1 M, divisorJetCoeff M a k * ramanujanPoleProfile k n) ^ 2) ≤
          4 * (1 + Real.log M) * ∑ k ∈ Icc 1 M, divisorJetCoeff M a k ^ 2 :=
        (sum_Ioc_packet_sq_le hM hMK hKN _).trans
          (mul_le_mul_of_nonneg_right hhar_NK (sum_nonneg fun _ _ => sq_nonneg _))
      _ ≤ 4 * (1 + Real.log M) *
            (2 * C_jet ^ 2 * (1 + Real.log M) ^ 2 * ∑ m ∈ Icc 1 M, a m ^ 2) :=
        mul_le_mul_of_nonneg_left hjet_coeff_sq
          (by have := Real.log_natCast_nonneg M; positivity)
      _ = 8 * C_jet ^ 2 * (1 + Real.log M) ^ 3 * ∑ m ∈ Icc 1 M, a m ^ 2 := by ring
  -- Sub-bound (iii): `energyTop`.
  have henergyTop_sum :
      (∑ n ∈ Ioc (N / M ^ 4) N, energyTop n ^ 2) ≤
        16 * (1 + Real.log M) ^ 3 * ∑ m ∈ Icc 1 M, a m ^ 2 := by
    let b : ℕ → ℝ := fun m => a m * (Real.log m + tameDifferent m)
    have heq_b : ∀ n ∈ Ioc (N / M ^ 4) N,
        energyTop n ^ 2 = (∑ m ∈ Icc 1 M, b m * ramanujanPoleProfile m n) ^ 2 := by
      intro n _; congr 1; dsimp only [energyTop, b]; rw [mul_sum]
      exact sum_congr rfl fun m _ => by rw [ramanujanPoleProfile_eq_mul_poleVector]; ring
    have hb_sq : (∑ m ∈ Icc 1 M, b m ^ 2) ≤
        4 * (1 + Real.log M) ^ 2 * ∑ m ∈ Icc 1 M, a m ^ 2 := by
      have hpt_b : ∀ m ∈ Icc 1 M, b m ^ 2 ≤ 4 * (1 + Real.log M) ^ 2 * a m ^ 2 := by
        intro m hm
        obtain ⟨hm1, hmM⟩ := mem_Icc.mp hm
        have htame0 : 0 ≤ tameDifferent m := by
          unfold tameDifferent
          refine sum_nonneg fun p hp => ?_
          have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
          exact div_nonneg (Real.log_nonneg (by linarith only [hp2])) (by linarith only [hp2])
        have htame_le : tameDifferent m ≤ Real.log m := by
          have hsi0 := selfIntersection_nonneg hm1
          rw [selfIntersection_eq hm1] at hsi0
          linarith only [hsi0]
        have hlogm_le : Real.log m ≤ 1 + Real.log M := by
          have := Real.log_le_log (by exact_mod_cast hm1) (show (m : ℝ) ≤ M by exact_mod_cast hmM)
          linarith only [this]
        have hlogm0 : 0 ≤ Real.log m + tameDifferent m :=
          add_nonneg (Real.log_natCast_nonneg m) htame0
        have hle2 : Real.log m + tameDifferent m ≤ 2 * (1 + Real.log M) := by
          linarith only [htame_le, hlogm_le]
        have hsq2 : (Real.log m + tameDifferent m) ^ 2 ≤ (2 * (1 + Real.log M)) ^ 2 :=
          pow_le_pow_left₀ hlogm0 hle2 2
        dsimp only [b]
        calc
          (a m * (Real.log m + tameDifferent m)) ^ 2 =
              (Real.log m + tameDifferent m) ^ 2 * a m ^ 2 := by ring
          _ ≤ (2 * (1 + Real.log M)) ^ 2 * a m ^ 2 :=
            mul_le_mul_of_nonneg_right hsq2 (sq_nonneg _)
          _ = 4 * (1 + Real.log M) ^ 2 * a m ^ 2 := by ring
      rw [mul_sum]; exact sum_le_sum hpt_b
    rw [sum_congr rfl heq_b]
    calc
      (∑ n ∈ Ioc (N / M ^ 4) N, (∑ m ∈ Icc 1 M, b m * ramanujanPoleProfile m n) ^ 2) ≤
          4 * (1 + Real.log M) * ∑ m ∈ Icc 1 M, b m ^ 2 :=
        (sum_Ioc_packet_sq_le hM hMK hKN b).trans
          (mul_le_mul_of_nonneg_right hhar_NK (sum_nonneg fun _ _ => sq_nonneg _))
      _ ≤ 4 * (1 + Real.log M) * (4 * (1 + Real.log M) ^ 2 * ∑ m ∈ Icc 1 M, a m ^ 2) :=
        mul_le_mul_of_nonneg_left hb_sq (by have := Real.log_natCast_nonneg M; positivity)
      _ = 16 * (1 + Real.log M) ^ 3 * ∑ m ∈ Icc 1 M, a m ^ 2 := by ring
  -- Sub-bound (iv): `upJump`.
  have hupJump_sum :
      (∑ n ∈ Ioc (N / M ^ 4) N, upJump n ^ 2) ≤
        (8 * (C_mert + 4) ^ 2 + 32 * (C_mert + 4)) * (1 + Real.log M) ^ 4 *
          ∑ m ∈ Icc 1 M, a m ^ 2 :=
    sum_top_upJump_sq_le hM hMK hKN hhar_NK hC_mert1 hmert_M4 a
  -- Combine the four top-strip pieces.
  have hLM0 := Real.log_natCast_nonneg M
  have hpow34 : (1 + Real.log M) ^ 3 ≤ (1 + Real.log M) ^ 4 :=
    pow_le_pow_right₀ (by linarith only [hLM0]) (by norm_num)
  have hcorr_Ioc_sum :
      (∑ n ∈ Ioc (N / M ^ 4) N, packetPrimeCorrTerm M N a n ^ 2) ≤
        (80 * (C_mert + 4) ^ 2 + 32 * C_jet ^ 2 + 64) * (1 + Real.log M) ^ 4 *
          ∑ m ∈ Icc 1 M, a m ^ 2 := by
    have hsum4 :
        (∑ n ∈ Ioc (N / M ^ 4) N, packetPrimeCorrTerm M N a n ^ 2) ≤
          4 * (∑ n ∈ Ioc (N / M ^ 4) N, upJump n ^ 2) +
            4 * (∑ n ∈ Ioc (N / M ^ 4) N, mertTop n ^ 2) +
            4 * (∑ n ∈ Ioc (N / M ^ 4) N, jetTop n ^ 2) +
            4 * (∑ n ∈ Ioc (N / M ^ 4) N, energyTop n ^ 2) := by
      calc
        _ ≤ ∑ n ∈ Ioc (N / M ^ 4) N,
            (4 * upJump n ^ 2 + 4 * mertTop n ^ 2 + 4 * jetTop n ^ 2 + 4 * energyTop n ^ 2) :=
          sum_le_sum h4sq
        _ = _ := by simp only [sum_add_distrib, ← mul_sum]
    have hm_le : 4 * (∑ n ∈ Ioc (N / M ^ 4) N, mertTop n ^ 2) ≤
        16 * (C_mert + 4) ^ 2 * (1 + Real.log M) ^ 4 * ∑ m ∈ Icc 1 M, a m ^ 2 := by
      calc
        _ ≤ 4 * (4 * (C_mert + 4) ^ 2 * (1 + Real.log M) ^ 3 * ∑ m ∈ Icc 1 M, a m ^ 2) :=
          mul_le_mul_of_nonneg_left hmertTop_sum (by norm_num)
        _ = 16 * (C_mert + 4) ^ 2 * (1 + Real.log M) ^ 3 * ∑ m ∈ Icc 1 M, a m ^ 2 := by ring
        _ ≤ 16 * (C_mert + 4) ^ 2 * (1 + Real.log M) ^ 4 * ∑ m ∈ Icc 1 M, a m ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpow34 (by positivity)) hSa0
    have hj_le : 4 * (∑ n ∈ Ioc (N / M ^ 4) N, jetTop n ^ 2) ≤
        32 * C_jet ^ 2 * (1 + Real.log M) ^ 4 * ∑ m ∈ Icc 1 M, a m ^ 2 := by
      calc
        _ ≤ 4 * (8 * C_jet ^ 2 * (1 + Real.log M) ^ 3 * ∑ m ∈ Icc 1 M, a m ^ 2) :=
          mul_le_mul_of_nonneg_left hjetTop_sum (by norm_num)
        _ = 32 * C_jet ^ 2 * (1 + Real.log M) ^ 3 * ∑ m ∈ Icc 1 M, a m ^ 2 := by ring
        _ ≤ 32 * C_jet ^ 2 * (1 + Real.log M) ^ 4 * ∑ m ∈ Icc 1 M, a m ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpow34 (by positivity)) hSa0
    have he_le : 4 * (∑ n ∈ Ioc (N / M ^ 4) N, energyTop n ^ 2) ≤
        64 * (1 + Real.log M) ^ 4 * ∑ m ∈ Icc 1 M, a m ^ 2 := by
      calc
        _ ≤ 4 * (16 * (1 + Real.log M) ^ 3 * ∑ m ∈ Icc 1 M, a m ^ 2) :=
          mul_le_mul_of_nonneg_left henergyTop_sum (by norm_num)
        _ = 64 * (1 + Real.log M) ^ 3 * ∑ m ∈ Icc 1 M, a m ^ 2 := by ring
        _ ≤ 64 * (1 + Real.log M) ^ 4 * ∑ m ∈ Icc 1 M, a m ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpow34 (by norm_num)) hSa0
    have hu_le : 4 * (∑ n ∈ Ioc (N / M ^ 4) N, upJump n ^ 2) ≤
        64 * (C_mert + 4) ^ 2 * (1 + Real.log M) ^ 4 * ∑ m ∈ Icc 1 M, a m ^ 2 := by
      have hcoef : 4 * (8 * (C_mert + 4) ^ 2 + 32 * (C_mert + 4)) ≤
          64 * (C_mert + 4) ^ 2 := by nlinarith only [hC_mert1]
      calc
        _ ≤ 4 * ((8 * (C_mert + 4) ^ 2 + 32 * (C_mert + 4)) * (1 + Real.log M) ^ 4 *
              ∑ m ∈ Icc 1 M, a m ^ 2) :=
          mul_le_mul_of_nonneg_left hupJump_sum (by norm_num)
        _ = 4 * (8 * (C_mert + 4) ^ 2 + 32 * (C_mert + 4)) *
            ((1 + Real.log M) ^ 4 * ∑ m ∈ Icc 1 M, a m ^ 2) := by ring
        _ ≤ 64 * (C_mert + 4) ^ 2 * ((1 + Real.log M) ^ 4 * ∑ m ∈ Icc 1 M, a m ^ 2) :=
          mul_le_mul_of_nonneg_right hcoef (mul_nonneg (by positivity) hSa0)
        _ = 64 * (C_mert + 4) ^ 2 * (1 + Real.log M) ^ 4 * ∑ m ∈ Icc 1 M, a m ^ 2 := by ring
    linarith only [hsum4, hu_le, hm_le, hj_le, he_le, (by ring :
      64 * (C_mert + 4) ^ 2 * (1 + Real.log M) ^ 4 * ∑ m ∈ Icc 1 M, a m ^ 2 +
        16 * (C_mert + 4) ^ 2 * (1 + Real.log M) ^ 4 * ∑ m ∈ Icc 1 M, a m ^ 2 +
        32 * C_jet ^ 2 * (1 + Real.log M) ^ 4 * ∑ m ∈ Icc 1 M, a m ^ 2 +
        64 * (1 + Real.log M) ^ 4 * ∑ m ∈ Icc 1 M, a m ^ 2 =
      (80 * (C_mert + 4) ^ 2 + 32 * C_jet ^ 2 + 64) * (1 + Real.log M) ^ 4 *
        ∑ m ∈ Icc 1 M, a m ^ 2)]
  calc
    (Real.log N)⁻¹ * (∑ n ∈ Ioc (N / M ^ 4) N, packetPrimeCorrTerm M N a n ^ 2) ≤
        (Real.log N)⁻¹ * ((80 * (C_mert + 4) ^ 2 + 32 * C_jet ^ 2 + 64) *
          (1 + Real.log M) ^ 4 * ∑ m ∈ Icc 1 M, a m ^ 2) :=
      mul_le_mul_of_nonneg_left hcorr_Ioc_sum (inv_nonneg.mpr hL0.le)
    _ = (80 * (C_mert + 4) ^ 2 + 32 * C_jet ^ 2 + 64) *
          ((1 + Real.log M) ^ 4 / Real.log N) * ∑ m ∈ Icc 1 M, a m ^ 2 := by ring

/-- Uniform `L²` residual norm bound on `conductorSubspace M N` (`M ^ 6 ≤ N`) without any
unsuppressed factor of `M` or `log M`:
`‖P_N u - ∑ a_m (log N - E(m)) v_m‖ ≤ C_res * (1 + (1 + log M)^2 / √(log N)) * ‖u‖`. -/
theorem exists_fullPrimeMatrix_packet_residual_norm_le :
    ∃ C_res : ℝ, 0 < C_res ∧
      ∀ {M N : ℕ}, 2 ≤ M → M ^ 6 ≤ N → 18 * (1 + Real.log M) ≤ Real.log N →
      ∀ a : ℕ → ℝ,
        ‖Matrix.toEuclideanLin (fullPrimeMatrix N)
            (∑ m ∈ Icc 1 M, a m • normalizedRamanujanHorizonVector m N) -
          ∑ m ∈ Icc 1 M, (a m * (Real.log N - ramanujanAdjunctionEnergy m)) •
            normalizedRamanujanHorizonVector m N‖ ≤
          C_res * (1 + (1 + Real.log M) ^ 2 / Real.sqrt (Real.log N)) *
            ‖∑ m ∈ Icc 1 M, a m • normalizedRamanujanHorizonVector m N‖ := by
  obtain ⟨C_env, hC_env_pos, hC_env⟩ := exists_primeMertensRemainder_log_envelope
  obtain ⟨C_jet, hC_jet_pos, hC_jet⟩ := exists_divisorJetHorizonVector_norm_le
  have hC_mert1 : 1 ≤ C_env + |Real.eulerMascheroniConstant| + 1 := by positivity
  have hC_top_pos : 0 < 160 * (C_env + |Real.eulerMascheroniConstant| + 1 + 4) ^ 2 +
      64 * C_jet ^ 2 + 128 := by positivity
  refine ⟨2 * C_env + 16 + 4 * Real.sqrt
      (160 * (C_env + |Real.eulerMascheroniConstant| + 1 + 4) ^ 2 + 64 * C_jet ^ 2 + 128),
    by positivity, ?_⟩
  intro M N hM hM6N hlog a
  set u := ∑ m ∈ Icc 1 M, a m • normalizedRamanujanHorizonVector m N
  set diagVec := ∑ m ∈ Icc 1 M,
    (a m * (Real.log N - ramanujanAdjunctionEnergy m)) • normalizedRamanujanHorizonVector m N
  set C_mert := C_env + |Real.eulerMascheroniConstant| + 1
  set C_top := 160 * (C_mert + 4) ^ 2 + 64 * C_jet ^ 2 + 128
  set C_res := 2 * C_env + 16 + 4 * Real.sqrt C_top
  have hMM_le_N : M * M ≤ N := by
    have hpow : M * M ≤ M ^ 6 := by
      calc
        M * M = M ^ 2 := (sq M).symm
        _ ≤ M ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
    exact hpow.trans hM6N
  have hL1 : 1 ≤ Real.log N := by
    have := Real.log_natCast_nonneg M; linarith only [hlog, this]
  have hL0 : 0 < Real.log N := zero_lt_one.trans_le hL1
  have hriesz_a : (∑ m ∈ Icc 1 M, a m ^ 2) ≤ 2 * ‖u‖ ^ 2 := by
    have h := (half_and_three_halves_riesz_of_log_le hM hMM_le_N hlog a).1
    linarith only [h]
  have hSa0 : 0 ≤ ∑ m ∈ Icc 1 M, a m ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hnorm_res_eq : ‖Matrix.toEuclideanLin (fullPrimeMatrix N) u - diagVec‖ ^ 2 =
      ∑ n ∈ Icc 1 N,
        ((Real.sqrt (Real.log N))⁻¹ * ∑ m ∈ Icc 1 M, a m * ramanujanPrimeResidual m N n) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    have hcoord : ∀ idx : PrimeHorizonIndex N,
        (Matrix.toEuclideanLin (fullPrimeMatrix N) u - diagVec) idx =
          (Real.sqrt (Real.log N))⁻¹ *
            ∑ m ∈ Icc 1 M, a m * ramanujanPrimeResidual m N idx.1 := by
      intro idx
      change (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : PrimeHorizonIndex N => ℝ) idx)
        (Matrix.toEuclideanLin (fullPrimeMatrix N) u - diagVec) = _
      rw [map_sub, map_sum, map_sum, ← sum_sub_distrib, mul_sum]
      refine sum_congr rfl fun m _ => ?_
      rw [map_smul, map_smul, map_smul]
      change a m * (Matrix.toEuclideanLin (fullPrimeMatrix N)
          (normalizedRamanujanHorizonVector m N) idx) -
        a m * (Real.log N - ramanujanAdjunctionEnergy m) *
          normalizedRamanujanHorizonVector m N idx = _
      dsimp only [normalizedRamanujanHorizonVector]
      rw [map_smul]
      change a m * ((Real.sqrt (Real.log N))⁻¹ *
          Matrix.toEuclideanLin (fullPrimeMatrix N) (ramanujanHorizonVector m N) idx) -
        a m * (Real.log N - ramanujanAdjunctionEnergy m) *
          ((Real.sqrt (Real.log N))⁻¹ * ramanujanPoleProfile m idx.1) = _
      rw [fullPrimeMatrix_apply_ramanujanHorizonVector, ramanujanPrimeResidual]
      ring
    trans ∑ idx : PrimeHorizonIndex N,
      ((Real.sqrt (Real.log N))⁻¹ *
        ∑ m ∈ Icc 1 M, a m * ramanujanPrimeResidual m N idx.1) ^ 2
    · exact sum_congr rfl fun idx _ => by rw [hcoord idx]
    · exact Finset.sum_coe_sort (Icc 1 N) (fun n =>
        ((Real.sqrt (Real.log N))⁻¹ *
          ∑ m ∈ Icc 1 M, a m * ramanujanPrimeResidual m N n) ^ 2)
  let e : ℕ → ℝ := fun y => mertensSum y - Real.log y + Real.eulerMascheroniConstant
  let r : ℕ → ℝ := fun n => Real.log N - Real.log ((N / n : ℕ) : ℝ) - Real.log n
  have hu_apply : ∀ n ∈ Icc 1 N,
      (Real.sqrt (Real.log N))⁻¹ * poleVector n *
          (∑ m ∈ Icc 1 M, a m * normalizedRamanujanMode m n) =
        primeHorizonExtension u n := by
    intro n hn
    rw [primeHorizonExtension_coe u ⟨n, hn⟩]
    change _ = (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : PrimeHorizonIndex N => ℝ) ⟨n, hn⟩) u
    rw [map_sum, mul_sum]
    refine sum_congr rfl fun m _ => ?_
    change (Real.sqrt (Real.log N))⁻¹ * poleVector n * (a m * normalizedRamanujanMode m n) =
      a m * ((Real.sqrt (Real.log N))⁻¹ * ramanujanPoleProfile m n)
    rw [ramanujanPoleProfile_eq_mul_poleVector]
    ring
  have hres_pt : ∀ n ∈ Icc 1 N,
      (Real.sqrt (Real.log N))⁻¹ * (∑ m ∈ Icc 1 M, a m * ramanujanPrimeResidual m N n) =
        (e (N / n) - r n) * primeHorizonExtension u n +
          (Real.sqrt (Real.log N))⁻¹ * packetPrimeCorrTerm M N a n := by
    intro n hn
    obtain ⟨hn0, hnN⟩ := mem_Icc.mp hn
    have hid_m : ∀ m ∈ Icc 1 M, ramanujanPrimeResidual m N n =
        ((e (N / n) - r n) * normalizedRamanujanMode m n +
          (poleProfileCorrection (normalizedRamanujanMode m) (N / n) n +
            (Real.log m + tameDifferent m) * normalizedRamanujanMode m n)) * poleVector n := by
      intro m _
      rw [ramanujanPrimeResidual]
      simp only [ramanujanPoleProfile_eq_mul_poleVector]
      rw [sum_weilPrimeKernel_poleProfile_eq_correction (normalizedRamanujanMode m) hn0 hnN]
      dsimp only [e, r, ramanujanAdjunctionEnergy]
      ring
    have hsum_m : (∑ m ∈ Icc 1 M, a m * ramanujanPrimeResidual m N n) =
        (e (N / n) - r n) * poleVector n * (∑ m ∈ Icc 1 M, a m * normalizedRamanujanMode m n) +
          packetPrimeCorrTerm M N a n := by
      rw [sum_congr rfl (fun m hm => by rw [hid_m m hm])]
      unfold packetPrimeCorrTerm
      rw [mul_sum, mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun m _ => by ring
    rw [hsum_m, mul_add, ← hu_apply n hn]
    ring
  have hmert_piece :
      (∑ n ∈ Icc 1 N, ((e (N / n) - r n) * primeHorizonExtension u n) ^ 2) ≤
        C_env ^ 2 * ‖u‖ ^ 2 := by
    have hpt : ∀ n ∈ Icc 1 N,
        ((e (N / n) - r n) * primeHorizonExtension u n) ^ 2 ≤
          C_env ^ 2 * primeHorizonExtension u n ^ 2 := by
      intro n hn
      obtain ⟨hn0, hnN⟩ := mem_Icc.mp hn
      have hy1 : 1 ≤ N / n := Nat.div_pos hnN hn0
      have hr_bd := roundoff_le hn0 hnN
      have her_abs : |e (N / n) - r n| ≤ C_env := by
        have h1 : |e (N / n) - r n| ≤ primeMertensRemainderProfile (N / n) := by
          unfold primeMertensRemainderProfile
          calc
            |e (N / n) - r n| ≤ |e (N / n)| + |r n| := abs_sub _ _
            _ ≤ |e (N / n)| + 1 / ((N / n : ℕ) : ℝ) := by
              rw [abs_of_nonneg hr_bd.1]; exact add_le_add le_rfl hr_bd.2
        have hden : 1 ≤ 1 + Real.log ((N / n : ℕ) : ℝ) := by
          have := Real.log_natCast_nonneg (N / n); linarith
        exact h1.trans ((hC_env (N / n) hy1).trans (div_le_self hC_env_pos.le hden))
      have her_sq : (e (N / n) - r n) ^ 2 ≤ C_env ^ 2 := by
        have h := pow_le_pow_left₀ (abs_nonneg _) her_abs 2
        simpa only [sq_abs] using h
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right her_sq (sq_nonneg _)
    calc
      (∑ n ∈ Icc 1 N, ((e (N / n) - r n) * primeHorizonExtension u n) ^ 2) ≤
          ∑ n ∈ Icc 1 N, C_env ^ 2 * primeHorizonExtension u n ^ 2 := sum_le_sum hpt
      _ = C_env ^ 2 * ‖u‖ ^ 2 := by rw [← mul_sum, sum_primeHorizonExtension_sq]
  have hmert_le : ∀ y : ℕ, 1 ≤ y → mertensSum y ≤ Real.log y + C_mert := by
    intro y hy
    have hden : 1 ≤ 1 + Real.log y := by have := Real.log_natCast_nonneg y; linarith
    have hle : primeMertensRemainderProfile y ≤ C_env :=
      (hC_env y hy).trans (div_le_self hC_env_pos.le hden)
    unfold primeMertensRemainderProfile at hle
    have h1y : 0 ≤ 1 / (y : ℝ) := by positivity
    have habs : |mertensSum y - Real.log y + Real.eulerMascheroniConstant| ≤ C_env := by
      linarith only [hle, h1y]
    have hup := (le_abs_self _).trans habs
    have hγ := neg_abs_le Real.eulerMascheroniConstant
    linarith only [hup, hγ]
  have hdeep_piece :
      (Real.log N)⁻¹ * (∑ n ∈ Icc 1 (N / M ^ 4), packetPrimeCorrTerm M N a n ^ 2) ≤
        64 * ‖u‖ ^ 2 := by
    calc
      _ ≤ 32 * ∑ m ∈ Icc 1 M, a m ^ 2 := sum_deep_packetPrimeCorrTerm_sq_le hM hM6N hL1 a
      _ ≤ 32 * (2 * ‖u‖ ^ 2) := mul_le_mul_of_nonneg_left hriesz_a (by norm_num)
      _ = 64 * ‖u‖ ^ 2 := by ring
  have htop_piece :
      (Real.log N)⁻¹ * (∑ n ∈ Ioc (N / M ^ 4) N, packetPrimeCorrTerm M N a n ^ 2) ≤
        C_top * ((1 + Real.log M) ^ 4 / Real.log N) * ‖u‖ ^ 2 := by
    have htop_raw := sum_top_packetPrimeCorrTerm_sq_le hM hM6N hlog hC_mert1 hC_jet_pos
      hmert_le hC_jet a
    calc
      _ ≤ (80 * (C_mert + 4) ^ 2 + 32 * C_jet ^ 2 + 64) *
            ((1 + Real.log M) ^ 4 / Real.log N) * (2 * ‖u‖ ^ 2) :=
        htop_raw.trans (mul_le_mul_of_nonneg_left hriesz_a
          (mul_nonneg (by positivity) (div_nonneg (by positivity) hL0.le)))
      _ = C_top * ((1 + Real.log M) ^ 4 / Real.log N) * ‖u‖ ^ 2 := by
        dsimp only [C_top]; ring
  have hsplit_Icc : Icc 1 N = Icc 1 (N / M ^ 4) ∪ Ioc (N / M ^ 4) N := by
    have hM4_pos : 0 < M ^ 4 := pow_pos (by omega) 4
    have hMK : M * M ≤ N / M ^ 4 := (Nat.le_div_iff_mul_le hM4_pos).mpr
      (by calc M * M * M ^ 4 = M ^ 6 := by ring
               _ ≤ N := hM6N)
    have hK1 : 1 ≤ N / M ^ 4 := (Nat.mul_le_mul hM hM).trans hMK |>.trans' (by omega)
    have hKN : N / M ^ 4 ≤ N := Nat.div_le_self N (M ^ 4)
    ext n; simp only [mem_Icc, mem_union, mem_Ioc]; omega
  have hdisj_Icc : Disjoint (Icc 1 (N / M ^ 4)) (Ioc (N / M ^ 4) N) := by
    rw [Finset.disjoint_left]; intro n hn1 hn2; simp only [mem_Icc, mem_Ioc] at hn1 hn2; omega
  have htotal_sq :
      ‖Matrix.toEuclideanLin (fullPrimeMatrix N) u - diagVec‖ ^ 2 ≤
        (2 * C_env ^ 2 + 128 + 2 * C_top * ((1 + Real.log M) ^ 4 / Real.log N)) * ‖u‖ ^ 2 := by
    have hpt_2sq : ∀ n ∈ Icc 1 N,
        ((Real.sqrt (Real.log N))⁻¹ * ∑ m ∈ Icc 1 M, a m * ramanujanPrimeResidual m N n) ^ 2 ≤
          2 * ((e (N / n) - r n) * primeHorizonExtension u n) ^ 2 +
            2 * ((Real.log N)⁻¹ * packetPrimeCorrTerm M N a n ^ 2) := by
      intro n hn
      rw [hres_pt n hn]
      have hsq : ((Real.sqrt (Real.log N))⁻¹ * packetPrimeCorrTerm M N a n) ^ 2 =
          (Real.log N)⁻¹ * packetPrimeCorrTerm M N a n ^ 2 := by
        rw [mul_pow, inv_pow, Real.sq_sqrt hL0.le]
      nlinarith only [hsq,
        sq_nonneg ((e (N / n) - r n) * primeHorizonExtension u n -
          (Real.sqrt (Real.log N))⁻¹ * packetPrimeCorrTerm M N a n)]
    have hcorr_split :
        (Real.log N)⁻¹ * (∑ n ∈ Icc 1 N, packetPrimeCorrTerm M N a n ^ 2) =
          (Real.log N)⁻¹ * (∑ n ∈ Icc 1 (N / M ^ 4), packetPrimeCorrTerm M N a n ^ 2) +
            (Real.log N)⁻¹ * (∑ n ∈ Ioc (N / M ^ 4) N, packetPrimeCorrTerm M N a n ^ 2) := by
      rw [hsplit_Icc, sum_union hdisj_Icc, mul_add]
    rw [hnorm_res_eq]
    calc
      (∑ n ∈ Icc 1 N, ((Real.sqrt (Real.log N))⁻¹ *
          ∑ m ∈ Icc 1 M, a m * ramanujanPrimeResidual m N n) ^ 2) ≤
          2 * (∑ n ∈ Icc 1 N, ((e (N / n) - r n) * primeHorizonExtension u n) ^ 2) +
            2 * ((Real.log N)⁻¹ * ∑ n ∈ Icc 1 N, packetPrimeCorrTerm M N a n ^ 2) := by
        calc
          _ ≤ ∑ n ∈ Icc 1 N, (2 * ((e (N / n) - r n) * primeHorizonExtension u n) ^ 2 +
              2 * ((Real.log N)⁻¹ * packetPrimeCorrTerm M N a n ^ 2)) := sum_le_sum hpt_2sq
          _ = _ := by simp only [sum_add_distrib, ← mul_sum]
      _ ≤ 2 * (C_env ^ 2 * ‖u‖ ^ 2) +
            2 * (64 * ‖u‖ ^ 2 + C_top * ((1 + Real.log M) ^ 4 / Real.log N) * ‖u‖ ^ 2) := by
        rw [hcorr_split]
        exact add_le_add (mul_le_mul_of_nonneg_left hmert_piece zero_le_two)
          (mul_le_mul_of_nonneg_left (add_le_add hdeep_piece htop_piece) zero_le_two)
      _ = (2 * C_env ^ 2 + 128 + 2 * C_top * ((1 + Real.log M) ^ 4 / Real.log N)) * ‖u‖ ^ 2 := by
        ring
  set X := (1 + Real.log M) ^ 2 / Real.sqrt (Real.log N)
  have hX0 : 0 ≤ X := by positivity
  have hX_sq : X ^ 2 = (1 + Real.log M) ^ 4 / Real.log N := by
    dsimp only [X]; rw [div_pow, Real.sq_sqrt hL0.le]; ring
  have hCres_sq :
      2 * C_env ^ 2 + 128 + 2 * C_top * X ^ 2 ≤ (C_res * (1 + X)) ^ 2 := by
    have hsCtop_sq : Real.sqrt C_top ^ 2 = C_top := Real.sq_sqrt hC_top_pos.le
    have hsCtop0 : 0 ≤ Real.sqrt C_top := Real.sqrt_nonneg C_top
    dsimp only [C_res]
    nlinarith only [hC_env_pos, hsCtop_sq, hsCtop0, hX0, sq_nonneg C_env, sq_nonneg X,
      mul_nonneg hC_env_pos.le hsCtop0, mul_nonneg hX0 hC_env_pos.le, mul_nonneg hX0 hsCtop0]
  have hrhs_sq :
      ‖Matrix.toEuclideanLin (fullPrimeMatrix N) u - diagVec‖ ^ 2 ≤
        (C_res * (1 + X) * ‖u‖) ^ 2 := by
    rw [← hX_sq] at htotal_sq
    calc
      ‖Matrix.toEuclideanLin (fullPrimeMatrix N) u - diagVec‖ ^ 2 ≤
          (2 * C_env ^ 2 + 128 + 2 * C_top * X ^ 2) * ‖u‖ ^ 2 := htotal_sq
      _ ≤ (C_res * (1 + X)) ^ 2 * ‖u‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hCres_sq (sq_nonneg _)
      _ = (C_res * (1 + X) * ‖u‖) ^ 2 := by ring
  have hrhs0 : 0 ≤ C_res * (1 + X) * ‖u‖ := by
    have hCr0 : 0 < C_res := by dsimp only [C_res]; positivity
    positivity
  nlinarith only [hrhs_sq, norm_nonneg (Matrix.toEuclideanLin (fullPrimeMatrix N) u - diagVec),
    hrhs0]

/-- Orthogonal cross-pairing bound for `fullPrimeMatrix N` between `u ∈ conductorSubspace M N`
and `w ∈ (conductorSubspace M N)ᗮ`, free of any unsuppressed `log M` factor:
`|⟪P_N u, w⟫| ≤ C_res * (1 + (1 + log M)^2 / √(log N)) * ‖u‖ * ‖w‖`. -/
theorem exists_fullPrimeMatrix_orthog_inner_le :
    ∃ C_res : ℝ, 0 < C_res ∧
      ∀ {M N : ℕ}, 2 ≤ M → M ^ 6 ≤ N → 18 * (1 + Real.log M) ≤ Real.log N →
      ∀ {u w : EuclideanSpace ℝ (PrimeHorizonIndex N)},
        u ∈ conductorSubspace M N →
        w ∈ (conductorSubspace M N)ᗮ →
        |⟪Matrix.toEuclideanLin (fullPrimeMatrix N) u, w⟫| ≤
          C_res * (1 + (1 + Real.log M) ^ 2 / Real.sqrt (Real.log N)) * ‖u‖ * ‖w‖ := by
  obtain ⟨C_res, hC_res_pos, hC_res⟩ := exists_fullPrimeMatrix_packet_residual_norm_le
  refine ⟨C_res, hC_res_pos, ?_⟩
  intro M N hM hM6N hlog u w hu hw
  obtain ⟨a, -, rfl⟩ := (mem_conductorSubspace_iff (M := M) (N := N) (x := u)).mp hu
  let diagVec := ∑ m ∈ Icc 1 M,
    (a m * (Real.log N - ramanujanAdjunctionEnergy m)) • normalizedRamanujanHorizonVector m N
  have hdiag_mem : diagVec ∈ conductorSubspace M N :=
    sum_normalizedRamanujanHorizonVector_mem_conductorSubspace M N _
  have horth : ⟪diagVec, w⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hdiag_mem hw
  have hinner_eq :
      ⟪Matrix.toEuclideanLin (fullPrimeMatrix N)
          (∑ m ∈ Icc 1 M, a m • normalizedRamanujanHorizonVector m N), w⟫ =
        ⟪Matrix.toEuclideanLin (fullPrimeMatrix N)
            (∑ m ∈ Icc 1 M, a m • normalizedRamanujanHorizonVector m N) - diagVec, w⟫ := by
    rw [inner_sub_left, horth, sub_zero]
  rw [hinner_eq]
  calc
    |⟪Matrix.toEuclideanLin (fullPrimeMatrix N)
        (∑ m ∈ Icc 1 M, a m • normalizedRamanujanHorizonVector m N) - diagVec, w⟫| ≤
        ‖Matrix.toEuclideanLin (fullPrimeMatrix N)
          (∑ m ∈ Icc 1 M, a m • normalizedRamanujanHorizonVector m N) - diagVec‖ * ‖w‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ (C_res * (1 + (1 + Real.log M) ^ 2 / Real.sqrt (Real.log N)) *
          ‖∑ m ∈ Icc 1 M, a m • normalizedRamanujanHorizonVector m N‖) * ‖w‖ :=
      mul_le_mul_of_nonneg_right (hC_res hM hM6N hlog a) (norm_nonneg w)
    _ = C_res * (1 + (1 + Real.log M) ^ 2 / Real.sqrt (Real.log N)) *
          ‖∑ m ∈ Icc 1 M, a m • normalizedRamanujanHorizonVector m N‖ * ‖w‖ := by ring

#print axioms sum_linear_moment_sq_le_four_div_log
#print axioms fullWeilPoleErrorMatrix_inner_eq_zero_of_orthog_one
#print axioms abs_fullWeilCenterMatrix_inner_le_of_mem_conductorSubspace
#print axioms norm_separatedCrossErrorMatrix_le
#print axioms abs_separatedCrossErrorMatrix_inner_le_of_mem_conductorSubspace
#print axioms exists_divisorJetHorizonVector_norm_le
#print axioms exists_fullPrimeMatrix_packet_residual_norm_le
#print axioms exists_fullPrimeMatrix_orthog_inner_le

end GaloisForLFunctions.CompletedArithmeticForms


