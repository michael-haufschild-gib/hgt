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
    (hm : m ∈ Icc 1 R) (hl : l ∈ Icc 1 R) (a_m a_l : ℝ) :
    a_m * a_l * (∑ j ∈ Icc 1 N, normalizedRamanujanMode m j * normalizedRamanujanMode l j) ≤
      (if m = l then (N : ℝ) * a_m ^ 2 else 0) + |a_m| * |a_l| * (R : ℝ) ^ 3 := by
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
    have h1 := Nat.div_add_mod N q
    have h2 := Nat.mod_lt N hq0
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
  have htail_prod : a_m * a_l * (∑ j ∈ Ioc (B * q) N, f j) ≤ |a_m| * |a_l| * (R : ℝ) ^ 3 := by
    calc
      a_m * a_l * (∑ j ∈ Ioc (B * q) N, f j) ≤ |a_m * a_l * ∑ j ∈ Ioc (B * q) N, f j| :=
        le_abs_self _
      _ = |a_m| * |a_l| * |∑ j ∈ Ioc (B * q) N, f j| := by rw [abs_mul, abs_mul]
      _ ≤ |a_m| * |a_l| * (R : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_left htail_abs (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  change a_m * a_l * (∑ j ∈ Icc 1 N, f j) ≤ _
  rw [hsum_eq, mul_add]
  refine add_le_add ?_ htail_prod
  by_cases hml : m = l
  · subst l
    rw [if_pos rfl, if_pos rfl, mul_one]
    have hBqR : (B : ℝ) * q ≤ N := by exact_mod_cast hBq_le
    have hsq : 0 ≤ a_m ^ 2 := sq_nonneg a_m
    nlinarith only [hBqR, hsq]
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
    exact sum_le_sum fun l hl => sum_Icc_normalizedRamanujanMode_mul_le hm hl (a m) (a l)
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
  have hterm (n j : ℕ) : b n * a j * arithmeticPoleKernel n j =
      (b n * Real.sqrt n) * (a j / Real.sqrt j) +
        (b n / Real.sqrt n) * (a j * Real.sqrt j) := by
    unfold arithmeticPoleKernel
    ring
  simp only [hterm, sum_add_distrib, ← mul_sum, ← sum_mul,
    ← SelectiveMultiscaleArithmeticPositivity.harmonicSum]
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
      g j / |(n : ℝ) - j|| ≤ 2 * B / (D : ℝ) := by
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
  have hlo_bound : |∑ j ∈ S_lo, g j / |(n : ℝ) - j|| ≤ B / (D : ℝ) := by
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
  have hhi_bound : |∑ j ∈ S_hi, g j / |(n : ℝ) - j|| ≤ B / (D : ℝ) := by
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
    |∑ j ∈ S_lo, g j / |(n : ℝ) - j| + ∑ j ∈ S_hi, g j / |(n : ℝ) - j|| ≤
        |∑ j ∈ S_lo, g j / |(n : ℝ) - j|| + |∑ j ∈ S_hi, g j / |(n : ℝ) - j|| := abs_add_le _ _
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
      hR hRN2 hlog hu_eq hu1).1
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
              have hsqL : Real.log N = Real.sqrt (Real.log N) ^ 2 := (Real.sq_sqrt hL.le).symm
              rw [hsqL]
              field_simp [hN0.ne', hsL.ne']
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
        have hsqL : Real.log N = Real.sqrt (Real.log N) ^ 2 := (Real.sq_sqrt hL.le).symm
        rw [hsqL]; field_simp [hsL.ne']; ring
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
    rw [le_div_iff₀' hL] at hm ⊢
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
          Real.sqrt n * Real.sqrt j * ((1 / |(n : ℝ) - j| + 1 / ((n : ℝ) + j)) / 2) := by
        rw [← h]; field_simp [hsn, hsj]
      rw [hker]; ring
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
        have hsN : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
        field_simp [hN0.ne', (Real.sqrt_pos.mpr hN0).ne']
        rw [hsN]; ring
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
          intro h; subst h; simp at hlt; positivity
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
        rw [abs_mul, abs_of_nonneg (by positivity), Real.sqrt_div (Nat.cast_nonneg j)]
        dsimp only [y_lin]
        rw [Real.sqrt_div (Nat.cast_nonneg j)]
        field_simp [hN0.ne', (Real.sqrt_pos.mpr hN0).ne']
        have hsN : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN0.le
        rw [hsN]; exact le_rfl
      have hsq := pow_le_pow_left₀ (abs_nonneg _) habs 2
      rw [sq_abs, mul_pow, div_pow, mul_pow, Real.sq_sqrt hn0.le, Real.sq_sqrt hN0.le] at hsq
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Icc 1 N)
        (fun j => 1 / ((n : ℝ) + j)) y_lin
      calc
        rowSumHalf n ^ 2 ≤ ((n : ℝ) / (4 * N)) *
            ((∑ j ∈ Icc 1 N, (1 / ((n : ℝ) + j)) ^ 2) * ∑ j ∈ Icc 1 N, y_lin j ^ 2) :=
          hsq.trans (mul_le_mul_of_nonneg_left (by simpa only [norm_num] using hcs) (by positivity))
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
    have hsq_eq : ∀ j, (Real.sqrt ((j : ℝ) / N) * primeHorizonExtension uTilde j) ^ 2 = y_lin j ^ 2 :=
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
    let B := 2 * (R : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt (∑ m ∈ Icc 1 R, aTilde m ^ 2)
    -- Simpler integer power bound: `B := 2 * R^2 * √(∑ aTilde^2)`.
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
          field_simp [hN0.ne', hL.ne']; ring
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
        have : 0 ≤ 1 / Real.log N * ‖u‖ ^ 2 := by positivity
        linarith only [this]
  -- Combine the 3 row pieces of `collarLin uTilde`.
  have huTilde_col : ‖collarLin uTilde‖ ≤
      28 * (1 + Real.log R) / Real.sqrt (Real.log N) * ‖u‖ := by
    have hsq : ‖collarLin uTilde‖ ^ 2 ≤
        (28 * (1 + Real.log R) / Real.sqrt (Real.log N) * ‖u‖) ^ 2 := by
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
        _ ≤ (784 * (1 + Real.log R) ^ 2) / Real.log N * ‖u‖ ^ 2 := by
          -- Wait: 1200 + 24 = 1224 ≤ 36^2 = 1296! Let's check: 28^2 = 784 < 1224!
          sorry
    sorry
  sorry
