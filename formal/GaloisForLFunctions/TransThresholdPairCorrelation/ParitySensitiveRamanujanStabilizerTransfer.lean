import GaloisForLFunctions.TransThresholdPairCorrelation.CoalescentPrimeReductionAndParitySieve
import GaloisForLFunctions.TransThresholdPairCorrelation.RamanujanDirichletCoalescentTransfer
import GaloisForLFunctions.RHTower.Zeta23OffLineMultipleExclusion
import GaloisForLFunctions.RHTower.ZetaThreeQuartersReduction
import GaloisForLFunctions.RenormalizedBiarithmeticGeometry.TheSurvivalConeOfAPeriodicGermIsItsModuleOfRelations

/-!
# Parity-Sensitive Ramanujan Stabilizer Transfer on Even Coalescent Shifts

For coalescent aperture `θ₀ < 1 / 3`, `primeCoalSum` collapses identically to the odd-prime
even-shift sum `oddEvenShiftPrimeCoalSum`, in which every lag `|p - q| = 2r` is strictly even.
On unrestricted integer shifts, `RamanujanDirichletCoalescentTransfer` established Ward–Mertens
transfer for individual moduli `q ≥ 2` via `∑_{d ∣ q} μ(q / d) = 0`. Restricting to even shifts
`h = 2r` transforms the Hardy–Littlewood singular series, the `RenormalizedBiarithmeticGeometry`
periodic Ramanujan germ, and the zero-side smooth-weighted coalescent certificate in six exact ways
proved unconditionally in this module:

1. **Parity Lock at `q = 2` and Odd-Modulus 2-Isomorphism (`ramanujanLagCoefficient_two_even`,
   `ramanujanLagCoefficient_odd_two_mul`, `ramanujanLagCoefficient_two_mul_odd_two_mul`):**
   At `q = 2`, `c_2(2r) = +1` for every `r : ℕ`, merging with `c_1(2r) = +1` into the doubled
   Poisson-parity baseline `2`. For every odd modulus `q` (`q % 2 = 1`) and every `r : ℕ`, both
   `c_q(2r) = c_q(r)` and `c_{2q}(2r) = c_q(r)` hold identically, while `4 ∣ n` forces
   `sqfreeTotientInv n = 0`.

2. **Exact Modulo-`4` Singular-Series Pairing and Ward–Mertens Top-Octave Identity
   (`sum_singularSeries_evenShift_eq_odd_split`, `sum_sqfreeTotientInv_eq_odd_add_half_odd`,
   `two_mul_sum_odd_sqfreeTotientInv_eq_add_topOctave`):**
   On any cutoff `N : ℕ`, splitting modulo `4` yields
   `∑_{n=1}^N (sqfreeTotientInv n / φ(n)) c_n(2r)
     = 2 ∑_{1≤q≤N/2, q odd} (sqfreeTotientInv q / φ(q)) c_q(r)
       + ∑_{N/2<q≤N, q odd} (sqfreeTotientInv q / φ(q)) c_q(r)`,
   and for the Ward–Mertens sum,
   `2 ∑_{1≤q≤Q, q odd} sqfreeTotientInv q
     = ∑_{n=1}^Q sqfreeTotientInv n + ∑_{Q/2<q≤Q, q odd} sqfreeTotientInv q`.
   Thus parity-locking onto even shifts doubles each odd-modulus stabilizer weight while preserving
   the full Ward–Mertens repulsion slope with an explicit nonnegative top-octave bonus.

3. **Even-Shift Poisson-Parity (`q = 1, 2`) and Multi-Modulus Ramanujan Coalescent Transfer
   (`abs_poisson_evenShift_cosTransform_add_le`,
   `abs_sum_odd_singularSeries_evenShift_cosTransform_add_le`,
   `abs_sum_full_evenShift_singularSeries_cosTransform_add_le`):**
   Because `Ω` is supported in `[a, b]` with `0 < a ≤ b ≤ m`, the `q = 1, 2` cotangent pole `m / τ`
   is smooth away from `0` and integrates by parts at rate `O(m² / (R a²))`, transferring the
   doubled `q = 1, 2` baseline `2 ∑_{r=1}^R Ω̂(2r / m)` to `-Ω̂(0)`. Simultaneously, half-scale
   substitution `m / 2` transfers the odd-modulus singular series `3 ≤ q ≤ Q` (`q % 2 = 1`) on
   even shifts `2r` to `-Ω̂(0) ∑_{3≤q≤Q, q odd} sqfreeTotientInv q`, so the complete parity-locked
   singular series transfers unconditionally to `-Ω̂(0) ∑_{1≤q≤Q, q odd} sqfreeTotientInv q`.

4. **Stabilizer-Centered Decomposition and Actual Prime-Pair Parity Lock
   (`oddEvenShiftPrimeCoalSum_eq_stabilizerModel_add_discrepancy`,
   `primeCoalSum_ramanujan_two_eq`, `primeCoalSum_ramanujan_two_mul_odd_eq`):**
   Decomposes `oddEvenShiftPrimeCoalSum` around any parity-sensitive `Q`-modulus Ramanujan
   stabilizer model into its singular-series baseline plus centered discrepancy
   `stabilizerDiscrepancyOddCoalSum`, and proves unconditionally that for `θ₀ < 1/3` the `q = 2`
   Ramanujan projection on actual coalescent prime pairs equals `primeCoalSum` identically while
   every doubled odd modulus `2q` agrees identically with `q`.

5. **Dynamic Poisson-Horizon Transfer and `RBG` Cross-Order Parity-Twin Survival
   (`abs_sum_dynamic_poissonHorizon_singularSeries_add_le`,
   `ramanujanMode_eq_ramanujanLagCoefficient`, `evenShift_ramanujanParityTwin_survival`):**
   Setting the scale-adaptive Poisson horizon `Q(m) = ⌊m / b⌋₊` (`0 < a ≤ b ≤ m`) discharges
   `Q(m) b ≤ m` automatically; identifying `RenormalizedBiarithmeticGeometry.ramanujanMode` with
   `ramanujanLagCoefficient` shows that on even lags `2r`, every singular-series torsion order
   `ord α` (`0 < ord α`, `¬ 4 ∣ ord α`) collapses onto its odd core `oddCore (ord α)`, so the
   renormalized periodic germ survives unconditionally across mixed `{q, 2q}` parity-twin orbits.

6. **Multiplicity-Refined Weighted Seam and Simple-Critical Coalescent Certificates
   (`weighted_rank_certificate_mult2_offLineMultiple`, `seamA_weighted_mult2_offLineMultiple`,
   `zeta_coalescent_certificate_simple_and_offLineMultiple`,
   `zeta_primeCoalescent_certificate_simple_and_offLineMultiple`,
   `offLineSimple_add_two_offLineMultiple_le_seven_thirtySixths_add_primeCoalescentSurplus`):**
   Retains the multiplicity excess `N - (s₁ + 2s₂ + 2p)` in the `c = 2` rank–trace inequality for
   smoothly weighted Gram matrices `wmat w (Z.Gz P T)`, sharpening the bandwidth-`4/3` coalescent
   certificate unconditionally from `N₀*` to simple critical zeros minus off-line multiple mass
   `N₀ˢ(T, 2T) - M_off(T, 2T)` and bounding `S_off(T, 2T) + 2 M_off(T, 2T)` by
   `(7/36 + ε) N(T, 2T) + primeCoalescentSurplus u η T`.
-/

open MeasureTheory Real Set Finset Filter Topology ArithmeticFunction
open scoped BigOperators ArithmeticFunction.Moebius

open Zeta23 Zeta23.PrimeSide RHTower RHTower.Sieve
open GaloisForLFunctions.BezoutValuationIncidence

noncomputable section

namespace GaloisForLFunctions.TransThresholdPairCorrelation

/-! ## §1. Parity Lock at `q = 2` and Odd-Modulus 2-Isomorphism on Even Shifts -/

/-- At modulus `q = 1`, the Ramanujan lag coefficient is identically `1`. -/
theorem ramanujanLagCoefficient_one (h : ℕ) : ramanujanLagCoefficient 1 h = 1 := by
  simp [ramanujanLagCoefficient, moebiusReal]

/-- Every odd integer is coprime to `2`. -/
theorem coprime_two_of_odd {q : ℕ} (hq : q % 2 = 1) : Nat.Coprime 2 q := by
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
  omega

/-- **Odd-Modulus 2-Isomorphism of `ramanujanLagCoefficient`.**
For every odd modulus `q` (`q % 2 = 1`) and every `r : ℕ`, multiplication by `2` preserves
divisor compatibility modulo `q`, so `c_q(2r) = c_q(r)` identically. -/
theorem ramanujanLagCoefficient_odd_two_mul {q : ℕ} (hq : q % 2 = 1) (r : ℕ) :
    ramanujanLagCoefficient q (2 * r) = ramanujanLagCoefficient q r := by
  unfold ramanujanLagCoefficient
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdq : d ∣ q := Nat.dvd_of_mem_divisors hd
  have hd_odd : d % 2 = 1 := by
    by_contra hd_even
    have h2d : 2 ∣ d := by omega
    have h2q : 2 ∣ q := dvd_trans h2d hdq
    omega
  have hcop : Nat.Coprime d 2 := (coprime_two_of_odd hd_odd).symm
  have hdvd : (d ∣ 2 * r) ↔ (d ∣ r) :=
    ⟨fun h => hcop.dvd_of_dvd_mul_left h, fun h => dvd_mul_of_dvd_right h 2⟩
  by_cases h : d ∣ r
  · rw [if_pos (hdvd.mpr h), if_pos h]
  · rw [if_neg (mt hdvd.mp h), if_neg h]

/-- For every odd `q`, `Nat.totient (2 * q) = Nat.totient q`. -/
theorem totient_two_mul_of_odd {q : ℕ} (hq : q % 2 = 1) :
    (2 * q).totient = q.totient := by
  rw [Nat.totient_mul (coprime_two_of_odd hq), Nat.totient_two, one_mul]

/-- **Even-Twin Stabilizer Identity (`c_{2q}(2r) = c_q(r)`).**
For every odd `q` (`q % 2 = 1`) and every `r : ℕ`, the modulus-`2q` Ramanujan lag coefficient at
even shift `2r` equals the modulus-`q` coefficient at `r`. -/
theorem ramanujanLagCoefficient_two_mul_odd_two_mul {q : ℕ} (hq : q % 2 = 1) (r : ℕ) :
    ramanujanLagCoefficient (2 * q) (2 * r) = ramanujanLagCoefficient q r := by
  have hq0 : 0 < q := by omega
  have hφq : (q.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hq0).ne'
  have hsieve : sieveLagMultiplier (2 * q) (2 * r) = sieveLagMultiplier q r := by
    rw [sieveLagMultiplier_eq_moebius_totient_quotient,
      sieveLagMultiplier_eq_moebius_totient_quotient,
      Nat.gcd_mul_left 2 q r, Nat.mul_div_mul_left q (Nat.gcd q r) two_pos]
  unfold sieveLagMultiplier at hsieve
  rw [totient_two_mul_of_odd hq] at hsieve
  exact (div_left_inj' hφq).mp hsieve

/-- **Parity Lock at `q = 2`:** `c_2(2r) = 1` for every `r : ℕ`. -/
theorem ramanujanLagCoefficient_two_even (r : ℕ) :
    ramanujanLagCoefficient 2 (2 * r) = 1 := by
  have h := ramanujanLagCoefficient_two_mul_odd_two_mul (q := 1) (by norm_num) r
  simpa [ramanujanLagCoefficient_one] using h

/-- On odd shifts `2r + 1`, `c_2(2r + 1) = -1`. -/
theorem ramanujanLagCoefficient_two_odd (r : ℕ) :
    ramanujanLagCoefficient 2 (2 * r + 1) = -1 := by
  have hdiv : (2 : ℕ).divisors = {1, 2} := Nat.Prime.divisors Nat.prime_two
  unfold ramanujanLagCoefficient
  rw [hdiv, Finset.sum_pair (by norm_num)]
  have hnd : ¬ (2 ∣ 2 * r + 1) := by omega
  rw [if_pos (one_dvd _), if_neg hnd]
  have hμ2 : moebiusReal (2 / 1) = -1 := by
    change ((μ (2 : ℕ) : ℤ) : ℝ) = -1
    rw [ArithmeticFunction.moebius_apply_prime Nat.prime_two]
    norm_num
  rw [hμ2]
  norm_num

/-! ## §2. Exact Modulo-`4` Singular-Series Pairing and Ward–Mertens Bijection Law -/

/-- `sqfreeTotientInv 1 = 1`. -/
theorem sqfreeTotientInv_one : RHTower.Sieve.sqfreeTotientInv 1 = 1 := by
  rw [RHTower.Sieve.sqfreeTotientInv_apply, if_pos squarefree_one, Nat.totient_one]
  norm_num

/-- `sqfreeTotientInv 2 = 1`. -/
theorem sqfreeTotientInv_two : RHTower.Sieve.sqfreeTotientInv 2 = 1 := by
  rw [RHTower.Sieve.sqfreeTotientInv_apply, if_pos Nat.prime_two.squarefree, Nat.totient_two]
  norm_num

/-- For every odd `q`, `sqfreeTotientInv (2 * q) = sqfreeTotientInv q`. -/
theorem sqfreeTotientInv_two_mul_of_odd {q : ℕ} (hq : q % 2 = 1) :
    RHTower.Sieve.sqfreeTotientInv (2 * q) = RHTower.Sieve.sqfreeTotientInv q := by
  rw [RHTower.Sieve.isMultiplicative_sqfreeTotientInv.map_mul_of_coprime (coprime_two_of_odd hq),
    sqfreeTotientInv_two, one_mul]

/-- Every multiple of `4` is non-squarefree, so `sqfreeTotientInv n = 0` whenever `4 ∣ n`. -/
theorem sqfreeTotientInv_of_four_dvd {n : ℕ} (h4 : 4 ∣ n) :
    RHTower.Sieve.sqfreeTotientInv n = 0 := by
  have hns : ¬ Squarefree n := by
    intro hs
    rcases h4 with ⟨k, rfl⟩
    have hu : IsUnit (2 : ℕ) := hs 2 ⟨k, by ring⟩
    simp at hu
  rw [RHTower.Sieve.sqfreeTotientInv_apply, if_neg hns]

/-- General modulo-`4` decomposition of any sum over `Finset.Icc 1 N` when multiples of `4` vanish:
`∑_{n=1}^N f(n) = ∑_{1≤q≤N, q odd} f(q) + ∑_{1≤q≤N/2, q odd} f(2q)`. -/
theorem sum_Icc_eq_odd_add_two_mul_odd (N : ℕ) (f : ℕ → ℝ)
    (h4 : ∀ n ∈ Finset.Icc 1 N, 4 ∣ n → f n = 0) :
    ∑ n ∈ Finset.Icc 1 N, f n =
      (∑ q ∈ (Finset.Icc 1 N).filter (fun q => q % 2 = 1), f q) +
      (∑ q ∈ (Finset.Icc 1 (N / 2)).filter (fun q => q % 2 = 1), f (2 * q)) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 N) (fun n => n % 2 = 1) f]
  congr 1
  rw [← Finset.sum_filter_add_sum_filter_not
    ((Finset.Icc 1 N).filter (fun n => ¬ n % 2 = 1)) (fun n => n % 4 = 2) f]
  have hzero : ∑ n ∈ ((Finset.Icc 1 N).filter (fun n => ¬ n % 2 = 1)).filter
      (fun n => ¬ n % 4 = 2), f n = 0 := by
    refine Finset.sum_eq_zero fun n hn => ?_
    simp only [Finset.mem_filter] at hn
    exact h4 n hn.1.1 (by omega)
  rw [hzero, add_zero]
  refine (Finset.sum_nbij (fun q => 2 * q) ?_ ?_ ?_ (fun _ _ => rfl)).symm
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_Icc] at hq ⊢
    omega
  · intro q₁ _ q₂ _ h
    dsimp at h
    omega
  · intro n hn
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hn
    refine ⟨n / 2, ?_, by dsimp; omega⟩
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
    omega

/-- Splitting `(Finset.Icc 1 N).filter odd` into `Icc 1 (N / 2)` and the top octave `Ioc (N / 2) N`. -/
theorem sum_Icc_odd_eq_half_add_topOctave (N : ℕ) (g : ℕ → ℝ) :
    ∑ q ∈ (Finset.Icc 1 N).filter (fun q => q % 2 = 1), g q =
      (∑ q ∈ (Finset.Icc 1 (N / 2)).filter (fun q => q % 2 = 1), g q) +
      (∑ q ∈ (Finset.Ioc (N / 2) N).filter (fun q => q % 2 = 1), g q) := by
  have hsub : (Finset.Icc 1 (N / 2)).filter (fun q => q % 2 = 1) ⊆
      (Finset.Icc 1 N).filter (fun q => q % 2 = 1) := by
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_Icc] at hq ⊢
    exact ⟨⟨hq.1.1, hq.1.2.trans (Nat.div_le_self N 2)⟩, hq.2⟩
  have hsdiff : ((Finset.Icc 1 N).filter (fun q => q % 2 = 1)) \
      ((Finset.Icc 1 (N / 2)).filter (fun q => q % 2 = 1)) =
      (Finset.Ioc (N / 2) N).filter (fun q => q % 2 = 1) := by
    ext q
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have h := Finset.sum_sdiff (f := g) hsub
  rw [hsdiff] at h
  linarith

/-- **Exact Modulo-`4` Singular-Series Pairing Law on Even Shifts (`2r`).**
For every cutoff `N : ℕ` and every `r : ℕ`, each odd modulus `q ≤ N / 2` pairs with its even twin
`2q ≤ N` to double its singular-series weight on `2r`, while odd moduli in `(N / 2, N]` appear
once:
`∑_{n=1}^N (sqfreeTotientInv n / φ(n)) c_n(2r)
  = 2 ∑_{1≤q≤N/2, q odd} (sqfreeTotientInv q / φ(q)) c_q(r)
    + ∑_{N/2<q≤N, q odd} (sqfreeTotientInv q / φ(q)) c_q(r)`. -/
theorem sum_singularSeries_evenShift_eq_odd_split (N r : ℕ) :
    ∑ n ∈ Finset.Icc 1 N,
        (RHTower.Sieve.sqfreeTotientInv n / (n.totient : ℝ)) *
          ramanujanLagCoefficient n (2 * r) =
      2 * (∑ q ∈ (Finset.Icc 1 (N / 2)).filter (fun q => q % 2 = 1),
            (RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ)) *
              ramanujanLagCoefficient q r) +
      (∑ q ∈ (Finset.Ioc (N / 2) N).filter (fun q => q % 2 = 1),
        (RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ)) *
          ramanujanLagCoefficient q r) := by
  let f : ℕ → ℝ := fun n =>
    (RHTower.Sieve.sqfreeTotientInv n / (n.totient : ℝ)) *
      ramanujanLagCoefficient n (2 * r)
  let g : ℕ → ℝ := fun q =>
    (RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ)) *
      ramanujanLagCoefficient q r
  change ∑ n ∈ Finset.Icc 1 N, f n = _
  rw [sum_Icc_eq_odd_add_two_mul_odd N f (fun n _ hn4 => by
    dsimp [f]; rw [sqfreeTotientInv_of_four_dvd hn4, zero_div, zero_mul])]
  have hodd1 : ∑ q ∈ (Finset.Icc 1 N).filter (fun q => q % 2 = 1), f q =
      ∑ q ∈ (Finset.Icc 1 N).filter (fun q => q % 2 = 1), g q := by
    refine Finset.sum_congr rfl fun q hq => ?_
    have hq_odd : q % 2 = 1 := (Finset.mem_filter.mp hq).2
    dsimp [f, g]
    rw [ramanujanLagCoefficient_odd_two_mul hq_odd r]
  have hodd2 : ∑ q ∈ (Finset.Icc 1 (N / 2)).filter (fun q => q % 2 = 1), f (2 * q) =
      ∑ q ∈ (Finset.Icc 1 (N / 2)).filter (fun q => q % 2 = 1), g q := by
    refine Finset.sum_congr rfl fun q hq => ?_
    have hq_odd : q % 2 = 1 := (Finset.mem_filter.mp hq).2
    dsimp [f, g]
    rw [sqfreeTotientInv_two_mul_of_odd hq_odd, totient_two_mul_of_odd hq_odd,
      ramanujanLagCoefficient_two_mul_odd_two_mul hq_odd r]
  rw [hodd1, hodd2, sum_Icc_odd_eq_half_add_topOctave N g]
  ring

/-- **Exact Parity-Halving Ward–Mertens Identity.**
For every `Q : ℕ`,
`∑_{n=1}^Q sqfreeTotientInv n
  = ∑_{1≤q≤Q, q odd} sqfreeTotientInv q + ∑_{1≤q≤Q/2, q odd} sqfreeTotientInv q`. -/
theorem sum_sqfreeTotientInv_eq_odd_add_half_odd (Q : ℕ) :
    ∑ n ∈ Finset.Icc 1 Q, RHTower.Sieve.sqfreeTotientInv n =
      (∑ q ∈ (Finset.Icc 1 Q).filter (fun q => q % 2 = 1), RHTower.Sieve.sqfreeTotientInv q) +
      (∑ q ∈ (Finset.Icc 1 (Q / 2)).filter (fun q => q % 2 = 1),
        RHTower.Sieve.sqfreeTotientInv q) := by
  rw [sum_Icc_eq_odd_add_two_mul_odd Q (fun n => RHTower.Sieve.sqfreeTotientInv n)
    (fun _ _ hn4 => sqfreeTotientInv_of_four_dvd hn4)]
  congr 1
  refine Finset.sum_congr rfl fun q hq => ?_
  exact sqfreeTotientInv_two_mul_of_odd (Finset.mem_filter.mp hq).2

/-- **Ward–Mertens Top-Octave Bonus Identity.**
Doubling the odd-modulus reciprocal-totient sum up to `Q` exceeds the full Ward–Mertens sum up to
`Q` by the exact nonnegative top-octave odd sum over `(Q / 2, Q]`:
`2 ∑_{1≤q≤Q, q odd} sqfreeTotientInv q
  = ∑_{n=1}^Q sqfreeTotientInv n + ∑_{Q/2<q≤Q, q odd} sqfreeTotientInv q`. -/
theorem two_mul_sum_odd_sqfreeTotientInv_eq_add_topOctave (Q : ℕ) :
    2 * (∑ q ∈ (Finset.Icc 1 Q).filter (fun q => q % 2 = 1), RHTower.Sieve.sqfreeTotientInv q) =
      (∑ n ∈ Finset.Icc 1 Q, RHTower.Sieve.sqfreeTotientInv n) +
      (∑ q ∈ (Finset.Ioc (Q / 2) Q).filter (fun q => q % 2 = 1),
        RHTower.Sieve.sqfreeTotientInv q) := by
  rw [sum_sqfreeTotientInv_eq_odd_add_half_odd Q,
    sum_Icc_odd_eq_half_add_topOctave Q (fun q => RHTower.Sieve.sqfreeTotientInv q)]
  ring

/-- `2 ∑_{1≤q≤Q, q odd} sqfreeTotientInv q ≥ ∑_{n=1}^Q sqfreeTotientInv n`. -/
theorem sum_sqfreeTotientInv_le_two_mul_sum_odd (Q : ℕ) :
    (∑ n ∈ Finset.Icc 1 Q, RHTower.Sieve.sqfreeTotientInv n) ≤
      2 * (∑ q ∈ (Finset.Icc 1 Q).filter (fun q => q % 2 = 1),
        RHTower.Sieve.sqfreeTotientInv q) := by
  rw [two_mul_sum_odd_sqfreeTotientInv_eq_add_topOctave Q]
  have hnn : 0 ≤ ∑ q ∈ (Finset.Ioc (Q / 2) Q).filter (fun q => q % 2 = 1),
      RHTower.Sieve.sqfreeTotientInv q :=
    Finset.sum_nonneg fun q _ => RHTower.Sieve.sqfreeTotientInv_nonneg q
  linarith

/-! ## §3. Even-Shift Poisson-Parity (`q = 1, 2`) and Odd-Modulus Coalescent Transfer -/

/-- A continuous function vanishing outside `[a, b]` vanishes at both endpoints `a` and `b`. -/
private theorem eq_zero_endpoints_of_supp {Ω : ℝ → ℝ} {a b : ℝ}
    (hcont : Continuous Ω) (hsupp : ∀ τ, τ ∉ Icc a b → Ω τ = 0) :
    Ω a = 0 ∧ Ω b = 0 := by
  have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  constructor
  · have hseq : Tendsto (fun n : ℕ => a - 1 / ((n : ℝ) + 1)) atTop (𝓝 a) := by
      simpa using tendsto_const_nhds.sub h1
    have hlim := hcont.continuousAt.tendsto.comp hseq
    have hzero : (fun n : ℕ => Ω (a - 1 / ((n : ℝ) + 1))) = fun _ => 0 := by
      funext n
      apply hsupp
      rw [Set.mem_Icc, not_and_or, not_le]
      left
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    rw [Function.comp_def, hzero] at hlim
    exact tendsto_nhds_unique hlim tendsto_const_nhds
  · have hseq : Tendsto (fun n : ℕ => b + 1 / ((n : ℝ) + 1)) atTop (𝓝 b) := by
      simpa using tendsto_const_nhds.add h1
    have hlim := hcont.continuousAt.tendsto.comp hseq
    have hzero : (fun n : ℕ => Ω (b + 1 / ((n : ℝ) + 1))) = fun _ => 0 := by
      funext n
      apply hsupp
      rw [Set.mem_Icc, not_and_or, not_le]
      right
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    rw [Function.comp_def, hzero] at hlim
    exact tendsto_nhds_unique hlim tendsto_const_nhds

/-- **Even-Shift Poisson-Parity Baseline Transfer (`q = 1, 2`).**
For any `C¹` non-negative window `Ω` supported in `[a, b]` with `0 < a ≤ b ≤ m` (`0 < m`) and any
`R ≥ 1`, the doubled Poisson-parity baseline `2 ∑_{r=1}^R cosTransform Ω (2r / m)` transfers to
`-cosTransform Ω 0` up to the endpoint transform, the cotangent residual `(b / m) cosTransform Ω 0`,
and the integrated-by-parts `1 / τ` oscillation `O(m² / (2 R a²))`:
`|(2 ∑_{r=1}^R cosTransform Ω (2r / m)) + cosTransform Ω 0|
  ≤ |cosTransform Ω (2R / m)| + (b / m) cosTransform Ω 0
    + (m² / (2 R a²)) ∫ τ in a..b, (a |deriv Ω τ| + Ω τ)`. -/
theorem abs_poisson_evenShift_cosTransform_add_le
    {Ω : ℝ → ℝ} {a b m : ℝ} {R : ℕ}
    (ha : 0 < a) (hab : a ≤ b) (hbm : b ≤ m) (hR : 1 ≤ R)
    (hΩ1 : ContDiff ℝ 1 Ω) (hΩ0 : ∀ τ, 0 ≤ Ω τ)
    (hsupp : ∀ τ, τ ∉ Icc a b → Ω τ = 0) :
    |(2 * ∑ r ∈ Finset.Icc 1 R, cosTransform Ω (((2 * r : ℕ) : ℝ) / m)) + cosTransform Ω 0| ≤
      |cosTransform Ω (((2 * R : ℕ) : ℝ) / m)| +
        (b / m) * cosTransform Ω 0 +
        (m ^ 2 / (2 * (R : ℝ) * a ^ 2)) * ∫ τ in a..b, (a * |deriv Ω τ| + Ω τ) := by
  have hb : 0 < b := ha.trans_le hab
  have hm : 0 < m := hb.trans_le hbm
  have hR_pos : (0 : ℝ) < R := by exact_mod_cast hR
  have hcont : Continuous Ω := hΩ1.continuous
  have hdcont : Continuous (deriv Ω) := hΩ1.continuous_deriv le_rfl
  have hInt : Integrable Ω := by
    have hcpt : HasCompactSupport Ω := HasCompactSupport.of_support_subset_isCompact
      isCompact_Icc (fun τ hτ => by
        by_contra hnot
        exact hτ (hsupp τ hnot))
    exact hcont.integrable_of_hasCompactSupport hcpt
  obtain ⟨hΩa, hΩb⟩ := eq_zero_endpoints_of_supp hcont hsupp
  set S1 := (2 * ∑ r ∈ Finset.Icc 1 R, cosTransform Ω (((2 * r : ℕ) : ℝ) / m)) +
    (cosTransform Ω 0 - cosTransform Ω (((2 * R : ℕ) : ℝ) / m))
  have htri : |(2 * ∑ r ∈ Finset.Icc 1 R, cosTransform Ω (((2 * r : ℕ) : ℝ) / m)) +
        cosTransform Ω 0| ≤
      |cosTransform Ω (((2 * R : ℕ) : ℝ) / m)| + |S1| := by
    have hid : (2 * ∑ r ∈ Finset.Icc 1 R, cosTransform Ω (((2 * r : ℕ) : ℝ) / m)) +
        cosTransform Ω 0 = cosTransform Ω (((2 * R : ℕ) : ℝ) / m) + S1 := by
      unfold S1; ring
    rw [hid]
    exact abs_add_le _ _
  refine htri.trans ?_
  rw [add_assoc]
  refine add_le_add le_rfl ?_
  -- Express `S1` as an integral over `a..b`
  have hS1_int : S1 = ∫ τ in a..b, Ω τ *
      ((2 * ∑ r ∈ Finset.Icc 1 R, Real.cos (((2 * r : ℕ) : ℝ) * (τ / m))) +
        (1 - Real.cos (((2 * R : ℕ) : ℝ) * (τ / m)))) := by
    unfold S1 cosTransform
    rw [Finset.mul_sum]
    simp_rw [← integral_const_mul]
    rw [← integral_finsetSum (Finset.Icc 1 R)
      (fun r _ => (integrable_window_mul_cos hInt (((2 * r : ℕ) : ℝ) / m)).const_mul 2)]
    rw [← integral_sub (integrable_window_mul_cos hInt 0)
      (integrable_window_mul_cos hInt (((2 * R : ℕ) : ℝ) / m))]
    have hsub_int : Integrable (fun τ =>
        Ω τ * Real.cos (τ * 0) - Ω τ * Real.cos (τ * (((2 * R : ℕ) : ℝ) / m))) :=
      ((integrable_window_mul_cos hInt 0).sub
        (integrable_window_mul_cos hInt (((2 * R : ℕ) : ℝ) / m))).congr
          (Eventually.of_forall fun _ => rfl)
    rw [← integral_add
      (integrable_finsetSum _ fun r _ =>
        (integrable_window_mul_cos hInt (((2 * r : ℕ) : ℝ) / m)).const_mul 2)
      hsub_int]
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
      setIntegral_eq_integral_of_forall_compl_eq_zero]
    · refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
      dsimp only
      simp only [mul_zero, Real.cos_zero]
      rw [mul_add, Finset.mul_sum]
      have hsum_eq : (∑ r ∈ Finset.Icc 1 R,
            2 * (Ω τ * Real.cos (τ * (((2 * r : ℕ) : ℝ) / m)))) =
          ∑ r ∈ Finset.Icc 1 R,
            Ω τ * (2 * Real.cos (((2 * r : ℕ) : ℝ) * (τ / m))) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [show τ * (((2 * r : ℕ) : ℝ) / m) = ((2 * r : ℕ) : ℝ) * (τ / m) by ring]
        ring
      rw [hsum_eq, ← Finset.mul_sum,
        show τ * (((2 * R : ℕ) : ℝ) / m) = ((2 * R : ℕ) : ℝ) * (τ / m) by ring]
      ring
    · intro τ hτ
      rw [hsupp τ hτ]
      simp
  -- On `[a, b]`, rewrite the Dirichlet sum via `cot(τ / m) = (cot(τ / m) - m / τ) + m / τ`
  let F_cot : ℝ → ℝ := fun τ =>
    Ω τ * (Real.sin (((2 * R : ℕ) : ℝ) * (τ / m)) *
      (Real.cos (τ / m) / Real.sin (τ / m) - 1 / (τ / m)))
  let F_pole : ℝ → ℝ := fun τ =>
    m * ((Ω τ / τ) * Real.sin ((2 * (R : ℝ) / m) * τ))
  have hcongr_ab : EqOn
      (fun τ => Ω τ * ((2 * ∑ r ∈ Finset.Icc 1 R, Real.cos (((2 * r : ℕ) : ℝ) * (τ / m))) +
        (1 - Real.cos (((2 * R : ℕ) : ℝ) * (τ / m)))))
      (fun τ => F_cot τ + F_pole τ) (Set.uIcc a b) := by
    intro τ hτ
    rw [Set.uIcc_of_le hab] at hτ
    have hτ0 : 0 < τ := ha.trans_le hτ.1
    set θ := τ / m
    have hθ0 : 0 < θ := div_pos hτ0 hm
    have hθ1 : θ ≤ 1 := (div_le_one hm).mpr (hτ.2.trans hbm)
    have hθ_pi : θ < π := hθ1.trans_lt (by linarith [Real.pi_gt_three])
    have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 hθ_pi
    have htrap := trapezoidal_sum_cos_eq_div hR (ϕ := 2 * θ)
      (by rw [show 2 * θ / 2 = θ by ring]; exact hsin.ne')
    rw [show 2 * θ / 2 = θ by ring] at htrap
    have htop := Finset.sum_Icc_succ_top (a := 1) (b := R - 1) (by omega)
      (fun r => Real.cos ((r : ℝ) * (2 * θ)))
    rw [show R - 1 + 1 = R by omega] at htop
    have hsum_cast : ∑ r ∈ Finset.Icc 1 R, Real.cos (((2 * r : ℕ) : ℝ) * θ) =
        ∑ r ∈ Finset.Icc 1 R, Real.cos ((r : ℝ) * (2 * θ)) := by
      refine Finset.sum_congr rfl fun r _ => ?_
      congr 1; push_cast; ring
    have hR_cast : ((2 * R : ℕ) : ℝ) * θ = (R : ℝ) * (2 * θ) := by push_cast; ring
    have hdir : (2 * ∑ r ∈ Finset.Icc 1 R, Real.cos (((2 * r : ℕ) : ℝ) * θ)) +
        (1 - Real.cos (((2 * R : ℕ) : ℝ) * θ)) =
        Real.sin (((2 * R : ℕ) : ℝ) * θ) * (Real.cos θ / Real.sin θ) := by
      rw [hsum_cast, hR_cast, htop]
      have h2 := congrArg (fun x => 2 * x) htrap
      have hrhs : 2 * (Real.sin ((R : ℝ) * (2 * θ)) * Real.cos θ / (2 * Real.sin θ)) =
          Real.sin ((R : ℝ) * (2 * θ)) * (Real.cos θ / Real.sin θ) := by
        field_simp [hsin.ne']
      linarith
    dsimp only [F_cot, F_pole]
    rw [hdir]
    have harg : ((2 * R : ℕ) : ℝ) * (τ / m) = (2 * (R : ℝ) / m) * τ := by
      push_cast; ring
    rw [harg]
    have hinv : 1 / (τ / m) = m / τ := one_div_div τ m
    rw [hinv]
    ring
  have hInt_cot : IntervalIntegrable F_cot volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hab]
    refine hcont.continuousOn.mul (ContinuousOn.mul (by fun_prop) ?_)
    refine ContinuousOn.sub ?_ ?_
    · refine ContinuousOn.div (by fun_prop) (by fun_prop) fun τ hτ => ?_
      have hτ0 : 0 < τ := ha.trans_le hτ.1
      have hθ1 : τ / m ≤ 1 := (div_le_one hm).mpr (hτ.2.trans hbm)
      exact (Real.sin_pos_of_pos_of_lt_pi (div_pos hτ0 hm)
        (hθ1.trans_lt (by linarith [Real.pi_gt_three]))).ne'
    · refine ContinuousOn.div continuousOn_const (continuousOn_id.div_const m) fun τ hτ => ?_
      exact (div_pos (ha.trans_le hτ.1) hm).ne'
  have hInt_pole : IntervalIntegrable F_pole volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hab]
    refine continuousOn_const.mul (ContinuousOn.mul ?_ (by fun_prop))
    exact hcont.continuousOn.div continuousOn_id fun τ hτ => (ha.trans_le hτ.1).ne'
  rw [hS1_int, intervalIntegral.integral_congr hcongr_ab,
    intervalIntegral.integral_add hInt_cot hInt_pole]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · -- Cotangent residual bound: `|∫ F_cot| ≤ (b / m) * cosTransform Ω 0`
    have hcos0_ab : cosTransform Ω 0 = ∫ τ in a..b, Ω τ := by
      rw [cosTransform_zero_eq_integral, intervalIntegral.integral_of_le hab,
        ← integral_Icc_eq_integral_Ioc,
        setIntegral_eq_integral_of_forall_compl_eq_zero (fun τ hτ => hsupp τ hτ)]
    rw [hcos0_ab, ← intervalIntegral.integral_const_mul]
    refine (intervalIntegral.abs_integral_le_integral_abs hab).trans ?_
    refine intervalIntegral.integral_mono_on hab hInt_cot.abs
      ((hcont.const_mul (b / m)).intervalIntegrable a b) fun τ hτ => ?_
    dsimp only [F_cot]
    have hτ0 : 0 < τ := ha.trans_le hτ.1
    have hθ0 : 0 < τ / m := div_pos hτ0 hm
    have hθ1 : τ / m ≤ 1 := (div_le_one hm).mpr (hτ.2.trans hbm)
    rw [abs_mul, abs_mul, abs_of_nonneg (hΩ0 τ)]
    have hcot := abs_cos_div_sin_sub_inv_le hθ0 hθ1
    have hsin1 : |Real.sin (((2 * R : ℕ) : ℝ) * (τ / m))| ≤ 1 := Real.abs_sin_le_one _
    have hτb : τ / m ≤ b / m := div_le_div_of_nonneg_right hτ.2 hm.le
    calc Ω τ * (|Real.sin (((2 * R : ℕ) : ℝ) * (τ / m))| *
          |Real.cos (τ / m) / Real.sin (τ / m) - 1 / (τ / m)|)
        ≤ Ω τ * (1 * (τ / m)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hsin1 hcot (abs_nonneg _) zero_le_one) (hΩ0 τ)
      _ ≤ Ω τ * (b / m) := mul_le_mul_of_nonneg_left (by linarith) (hΩ0 τ)
      _ = b / m * Ω τ := mul_comm _ _
  · -- Integration by parts on `F_pole`
    dsimp only [F_pole]
    rw [intervalIntegral.integral_const_mul, abs_mul, abs_of_pos hm]
    let u_fn : ℝ → ℝ := fun τ => Ω τ / τ
    let u'_fn : ℝ → ℝ := fun τ => (deriv Ω τ * τ - Ω τ) / τ ^ 2
    let v_fn : ℝ → ℝ := fun τ => -(m / (2 * (R : ℝ))) * Real.cos ((2 * (R : ℝ) / m) * τ)
    let v'_fn : ℝ → ℝ := fun τ => Real.sin ((2 * (R : ℝ) / m) * τ)
    have hu_deriv : ∀ τ ∈ Set.uIcc a b, HasDerivAt u_fn (u'_fn τ) τ := by
      intro τ hτ
      rw [Set.uIcc_of_le hab] at hτ
      have hτ0 : τ ≠ 0 := (ha.trans_le hτ.1).ne'
      have hdΩ : HasDerivAt Ω (deriv Ω τ) τ :=
        ((hΩ1.differentiable one_ne_zero).differentiableAt).hasDerivAt
      exact (hdΩ.div (hasDerivAt_id τ) hτ0).congr_of_eventuallyEq
        (Eventually.of_forall fun _ => rfl) |>.congr_deriv (by dsimp [u'_fn]; ring)
    have hv_deriv : ∀ τ ∈ Set.uIcc a b, HasDerivAt v_fn (v'_fn τ) τ := by
      intro τ _
      have h1 : HasDerivAt (fun x : ℝ => (2 * (R : ℝ) / m) * x) (2 * (R : ℝ) / m) τ := by
        simpa using (hasDerivAt_id τ).const_mul (2 * (R : ℝ) / m)
      refine (h1.cos.const_mul (-(m / (2 * (R : ℝ))))).congr_deriv ?_
      dsimp [v'_fn]
      have hR0 : (R : ℝ) ≠ 0 := hR_pos.ne'
      field_simp [hm.ne', hR0]
    have hu'_int : IntervalIntegrable u'_fn volume a b := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hab]
      refine ((hdcont.continuousOn.mul continuousOn_id).sub hcont.continuousOn).div
        (continuousOn_id.pow 2) fun τ hτ => pow_ne_zero 2 (ha.trans_le hτ.1).ne'
    have hv'_int : IntervalIntegrable v'_fn volume a b :=
      (by fun_prop : Continuous v'_fn).intervalIntegrable _ _
    have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu_deriv hv_deriv hu'_int hv'_int
    have hbdry : u_fn b * v_fn b - u_fn a * v_fn a = 0 := by
      dsimp [u_fn]
      rw [hΩa, hΩb, zero_div, zero_div, zero_mul, zero_mul, sub_self]
    rw [hibp, hbdry, zero_sub, abs_neg]
    have hpull : ∫ τ in a..b, u'_fn τ * v_fn τ =
        -(m / (2 * (R : ℝ))) * ∫ τ in a..b, u'_fn τ * Real.cos ((2 * (R : ℝ) / m) * τ) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun τ _ => ?_
      dsimp [v_fn]; ring
    rw [hpull, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < m / (2 * (R : ℝ)))]
    have hmaj_int : IntervalIntegrable (fun τ => (a * |deriv Ω τ| + Ω τ) / a ^ 2) volume a b :=
      (((hdcont.abs.const_mul a).add hcont).div_const (a ^ 2)).intervalIntegrable _ _
    have hint_le : |∫ τ in a..b, u'_fn τ * Real.cos ((2 * (R : ℝ) / m) * τ)| ≤
        ∫ τ in a..b, (a * |deriv Ω τ| + Ω τ) / a ^ 2 := by
      refine (intervalIntegral.abs_integral_le_integral_abs hab).trans ?_
      refine intervalIntegral.integral_mono_on hab
        (hu'_int.mul_continuousOn (by fun_prop)).abs hmaj_int fun τ hτ => ?_
      dsimp only [u'_fn]
      have hτa : a ≤ τ := hτ.1
      have hτ0 : 0 < τ := ha.trans_le hτa
      rw [abs_mul]
      have hcos1 : |Real.cos ((2 * (R : ℝ) / m) * τ)| ≤ 1 := Real.abs_cos_le_one _
      have hu'_le : |(deriv Ω τ * τ - Ω τ) / τ ^ 2| ≤ (a * |deriv Ω τ| + Ω τ) / a ^ 2 := by
        rw [abs_div, abs_of_pos (sq_pos_of_pos hτ0)]
        have hnum : |deriv Ω τ * τ - Ω τ| ≤ |deriv Ω τ| * τ + Ω τ := by
          refine (abs_sub _ _).trans ?_
          rw [abs_mul, abs_of_pos hτ0, abs_of_nonneg (hΩ0 τ)]
        calc |deriv Ω τ * τ - Ω τ| / τ ^ 2
            ≤ (|deriv Ω τ| * τ + Ω τ) / τ ^ 2 :=
              div_le_div_of_nonneg_right hnum (sq_nonneg τ)
          _ = |deriv Ω τ| / τ + Ω τ / τ ^ 2 := by field_simp [hτ0.ne']
          _ ≤ |deriv Ω τ| / a + Ω τ / a ^ 2 :=
              add_le_add (div_le_div_of_nonneg_left (abs_nonneg _) ha hτa)
                (div_le_div_of_nonneg_left (hΩ0 τ) (sq_pos_of_pos ha)
                  (pow_le_pow_left₀ ha.le hτa 2))
          _ = (a * |deriv Ω τ| + Ω τ) / a ^ 2 := by field_simp [ha.ne']
      calc |(deriv Ω τ * τ - Ω τ) / τ ^ 2| * |Real.cos ((2 * (R : ℝ) / m) * τ)|
          ≤ ((a * |deriv Ω τ| + Ω τ) / a ^ 2) * 1 :=
            mul_le_mul hu'_le hcos1 (abs_nonneg _) (by have := hΩ0 τ; positivity)
        _ = (a * |deriv Ω τ| + Ω τ) / a ^ 2 := mul_one _
    have hdiv_out : ∫ τ in a..b, (a * |deriv Ω τ| + Ω τ) / a ^ 2 =
        (1 / a ^ 2) * ∫ τ in a..b, (a * |deriv Ω τ| + Ω τ) := by
      have hfn : (fun τ => (a * |deriv Ω τ| + Ω τ) / a ^ 2) =
          fun τ => (1 / a ^ 2) * (a * |deriv Ω τ| + Ω τ) := funext fun τ => by ring
      rw [hfn]
      exact intervalIntegral.integral_const_mul _ _
    calc m * (m / (2 * (R : ℝ)) * |∫ τ in a..b, u'_fn τ * Real.cos ((2 * (R : ℝ) / m) * τ)|)
        ≤ m * (m / (2 * (R : ℝ)) * ∫ τ in a..b, (a * |deriv Ω τ| + Ω τ) / a ^ 2) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hint_le (by positivity)) hm.le
      _ = (m ^ 2 / (2 * (R : ℝ) * a ^ 2)) * ∫ τ in a..b, (a * |deriv Ω τ| + Ω τ) := by
          rw [hdiv_out]
          field_simp [hR_pos.ne', ha.ne']

/-- **Parity-Sensitive Odd-Modulus Singular-Series Coalescent Transfer on Even Shifts (`2r`).**
For any non-negative integrable window `Ω` supported in `[a, b]` (`0 ≤ a ≤ b`, `0 < b`), any scale
`m > 0`, and any cutoff `Q` with `Q b ≤ m` (`q ≥ 3` odd, `1 ≤ R q`), substituting half-scale `m / 2`
transfers the parity-doubled odd-modulus singular series over even shifts `2r` (`1 ≤ r ≤ q R_q`)
unconditionally to `-cosTransform Ω 0 * ∑_{3≤q≤Q, q odd} sqfreeTotientInv q`:
`|(2 ∑_{3≤q≤Q, q odd} (sqfreeTotientInv q / φ(q)) ∑_{r=1}^{q R_q} c_q(2r) cosTransform Ω (2r / m))
    + cosTransform Ω 0 ∑_{3≤q≤Q, q odd} sqfreeTotientInv q|
  ≤ ∑_{3≤q≤Q, q odd} sqfreeTotientInv q |cosTransform Ω (2 q R_q / m)|
    + (b / m) cosTransform Ω 0 ∑_{3≤q≤Q, q odd} (sqfreeTotientInv q / φ(q)) ∑_{d ∣ q} d²`. -/
theorem abs_sum_odd_singularSeries_evenShift_cosTransform_add_le
    {Ω : ℝ → ℝ} {a b m : ℝ} {Q : ℕ} {R : ℕ → ℕ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : 0 < b) (hm : 0 < m)
    (hR : ∀ q ∈ (Finset.Icc 3 Q).filter (fun q => q % 2 = 1), 1 ≤ R q)
    (hQm : (Q : ℝ) * b ≤ m)
    (hInt : Integrable Ω) (hΩ0 : ∀ τ, 0 ≤ Ω τ)
    (hsupp : ∀ τ, τ ∉ Icc a b → Ω τ = 0) :
    |(2 * ∑ q ∈ (Finset.Icc 3 Q).filter (fun q => q % 2 = 1),
          (RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ)) *
            ∑ r ∈ Finset.Icc 1 (q * R q),
              ramanujanLagCoefficient q (2 * r) * cosTransform Ω (((2 * r : ℕ) : ℝ) / m)) +
        cosTransform Ω 0 *
          ∑ q ∈ (Finset.Icc 3 Q).filter (fun q => q % 2 = 1), RHTower.Sieve.sqfreeTotientInv q| ≤
      (∑ q ∈ (Finset.Icc 3 Q).filter (fun q => q % 2 = 1),
        RHTower.Sieve.sqfreeTotientInv q * |cosTransform Ω (((2 * (q * R q) : ℕ) : ℝ) / m)|) +
      (b / m) * cosTransform Ω 0 *
        ∑ q ∈ (Finset.Icc 3 Q).filter (fun q => q % 2 = 1),
          (RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ)) *
            (∑ d ∈ q.divisors, (d : ℝ) ^ 2) := by
  set oddSet := (Finset.Icc 3 Q).filter (fun q => q % 2 = 1)
  have hm2 : 0 < m / 2 := by linarith
  have hrew : (2 * ∑ q ∈ oddSet,
          (RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ)) *
            ∑ r ∈ Finset.Icc 1 (q * R q),
              ramanujanLagCoefficient q (2 * r) * cosTransform Ω (((2 * r : ℕ) : ℝ) / m)) +
        cosTransform Ω 0 * ∑ q ∈ oddSet, RHTower.Sieve.sqfreeTotientInv q =
      ∑ q ∈ oddSet,
        (2 * (RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ))) *
          ((∑ r ∈ Finset.Icc 1 (q * R q),
              ramanujanLagCoefficient q r * cosTransform Ω ((r : ℝ) / (m / 2))) +
            (q.totient : ℝ) / 2 * cosTransform Ω 0) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q hq => ?_
    obtain ⟨hq_icc, hq_odd⟩ := Finset.mem_filter.mp hq
    have hq3 : 3 ≤ q := (Finset.mem_Icc.mp hq_icc).1
    have hφ0 : (q.totient : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr (by omega : 0 < q)).ne'
    have hinner : ∑ r ∈ Finset.Icc 1 (q * R q),
        ramanujanLagCoefficient q (2 * r) * cosTransform Ω (((2 * r : ℕ) : ℝ) / m) =
        ∑ r ∈ Finset.Icc 1 (q * R q),
          ramanujanLagCoefficient q r * cosTransform Ω ((r : ℝ) / (m / 2)) := by
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [ramanujanLagCoefficient_odd_two_mul hq_odd r]
      congr 2
      push_cast
      field_simp [hm.ne']
    rw [hinner]
    field_simp [hφ0]
  rw [hrew]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ q ∈ oddSet,
      |(2 * (RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ))) *
        ((∑ r ∈ Finset.Icc 1 (q * R q),
            ramanujanLagCoefficient q r * cosTransform Ω ((r : ℝ) / (m / 2))) +
          (q.totient : ℝ) / 2 * cosTransform Ω 0)| ≤
      RHTower.Sieve.sqfreeTotientInv q * |cosTransform Ω (((2 * (q * R q) : ℕ) : ℝ) / m)| +
      (b / m) * cosTransform Ω 0 *
        ((RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ)) *
          (∑ d ∈ q.divisors, (d : ℝ) ^ 2)) := by
    intro q hq
    obtain ⟨hq_icc, _⟩ := Finset.mem_filter.mp hq
    obtain ⟨hq3, hqQ⟩ := Finset.mem_Icc.mp hq_icc
    have hq2 : 2 ≤ q := by omega
    have hq_real : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
    have hqm2 : (q : ℝ) * b ≤ 2 * (m / 2) := by
      have h1 : (q : ℝ) * b ≤ m := (mul_le_mul_of_nonneg_right hq_real hb.le).trans hQm
      linarith
    have hφ0 : (q.totient : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr (by omega : 0 < q)).ne'
    have hnn : 0 ≤ 2 * (RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ)) :=
      mul_nonneg zero_le_two
        (div_nonneg (RHTower.Sieve.sqfreeTotientInv_nonneg q) (Nat.cast_nonneg _))
    rw [abs_mul, abs_of_nonneg hnn]
    have hmod := abs_sum_ramanujanLagCoefficient_mul_cosTransform_add_le ha hab hb hm2
      hq2 (hR q hq) hqm2 hInt hΩ0 hsupp
    have harg_eq : (((q * R q : ℕ) : ℝ) / (m / 2)) = (((2 * (q * R q) : ℕ) : ℝ) / m) := by
      push_cast
      field_simp [hm.ne']
    rw [harg_eq, show b / (4 * (m / 2)) = b / (2 * m) by field_simp [hm.ne']; ring] at hmod
    calc (2 * (RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ))) *
          |(∑ r ∈ Finset.Icc 1 (q * R q),
              ramanujanLagCoefficient q r * cosTransform Ω ((r : ℝ) / (m / 2))) +
            (q.totient : ℝ) / 2 * cosTransform Ω 0|
        ≤ (2 * (RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ))) *
          ((q.totient : ℝ) / 2 * |cosTransform Ω (((2 * (q * R q) : ℕ) : ℝ) / m)| +
            (∑ d ∈ q.divisors, (d : ℝ) ^ 2) * (b / (2 * m)) * cosTransform Ω 0) :=
          mul_le_mul_of_nonneg_left hmod hnn
      _ = RHTower.Sieve.sqfreeTotientInv q * |cosTransform Ω (((2 * (q * R q) : ℕ) : ℝ) / m)| +
          (b / m) * cosTransform Ω 0 *
            ((RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ)) *
              (∑ d ∈ q.divisors, (d : ℝ) ^ 2)) := by
          field_simp [hφ0, hm.ne']
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]

/-- **Complete Parity-Locked Singular-Series Coalescent Transfer (`1 ≤ q ≤ Q`, `q` odd).**
Combining the `q = 1, 2` Poisson-parity baseline (`2 ∑_{r=1}^{R 1} Ω̂(2r / m)`) with all odd moduli
`3 ≤ q ≤ Q` (`2 (sqfreeTotientInv q / φ(q)) ∑_{r=1}^{q R_q} c_q(2r) Ω̂(2r / m)`) transfers the
entire parity-locked singular series up to `Q` (`1 ≤ Q`, `Q b ≤ m`, `0 < a ≤ b`) to the negative
Ward–Mertens sum `-cosTransform Ω 0 * ∑_{1≤q≤Q, q odd} sqfreeTotientInv q` (which has magnitude at
least `(1 / 2) cosTransform Ω 0 * ∑_{n=1}^Q sqfreeTotientInv n`). -/
theorem abs_sum_full_evenShift_singularSeries_cosTransform_add_le
    {Ω : ℝ → ℝ} {a b m : ℝ} {Q : ℕ} {R : ℕ → ℕ}
    (ha : 0 < a) (hab : a ≤ b) (hQ1 : 1 ≤ Q)
    (hR : ∀ q ∈ (Finset.Icc 1 Q).filter (fun q => q % 2 = 1), 1 ≤ R q)
    (hQm : (Q : ℝ) * b ≤ m)
    (hΩ1 : ContDiff ℝ 1 Ω) (hΩ0 : ∀ τ, 0 ≤ Ω τ)
    (hsupp : ∀ τ, τ ∉ Icc a b → Ω τ = 0) :
    |(2 * ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => q % 2 = 1),
          (RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ)) *
            ∑ r ∈ Finset.Icc 1 (q * R q),
              ramanujanLagCoefficient q (2 * r) * cosTransform Ω (((2 * r : ℕ) : ℝ) / m)) +
        cosTransform Ω 0 *
          ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => q % 2 = 1), RHTower.Sieve.sqfreeTotientInv q| ≤
      (∑ q ∈ (Finset.Icc 1 Q).filter (fun q => q % 2 = 1),
        RHTower.Sieve.sqfreeTotientInv q * |cosTransform Ω (((2 * (q * R q) : ℕ) : ℝ) / m)|) +
      (b / m) * cosTransform Ω 0 *
        (1 + ∑ q ∈ (Finset.Icc 3 Q).filter (fun q => q % 2 = 1),
          (RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ)) *
            (∑ d ∈ q.divisors, (d : ℝ) ^ 2)) +
      (m ^ 2 / (2 * (R 1 : ℝ) * a ^ 2)) * ∫ τ in a..b, (a * |deriv Ω τ| + Ω τ) := by
  have hb : 0 < b := ha.trans_le hab
  have hQ_ge1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ1
  have hbm : b ≤ m := by
    calc b = 1 * b := (one_mul b).symm
      _ ≤ (Q : ℝ) * b := mul_le_mul_of_nonneg_right hQ_ge1 hb.le
      _ ≤ m := hQm
  have hm : 0 < m := hb.trans_le hbm
  have hInt : Integrable Ω := by
    have hcpt : HasCompactSupport Ω := HasCompactSupport.of_support_subset_isCompact
      isCompact_Icc (fun τ hτ => by
        by_contra hnot
        exact hτ (hsupp τ hnot))
    exact hΩ1.continuous.integrable_of_hasCompactSupport hcpt
  have h1_mem : 1 ∈ (Finset.Icc 1 Q).filter (fun q => q % 2 = 1) :=
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, hQ1⟩, by norm_num⟩
  have herase : ((Finset.Icc 1 Q).filter (fun q => q % 2 = 1)).erase 1 =
      (Finset.Icc 3 Q).filter (fun q => q % 2 = 1) := by
    ext q
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_Icc]
    omega
  have hsplit_sum : ∀ g : ℕ → ℝ,
      ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => q % 2 = 1), g q =
        g 1 + ∑ q ∈ (Finset.Icc 3 Q).filter (fun q => q % 2 = 1), g q := by
    intro g
    rw [← Finset.add_sum_erase _ g h1_mem, herase]
  rw [hsplit_sum, hsplit_sum, hsplit_sum]
  simp only [sqfreeTotientInv_one, Nat.totient_one, Nat.cast_one, div_one, one_mul,
    ramanujanLagCoefficient_one]
  have hbase := abs_poisson_evenShift_cosTransform_add_le ha hab hbm (hR 1 h1_mem) hΩ1 hΩ0 hsupp
  have hodd := abs_sum_odd_singularSeries_evenShift_cosTransform_add_le ha.le hab hb hm
    (fun q hq => hR q (by rw [← herase] at hq; exact Finset.mem_of_mem_erase hq))
    hQm hInt hΩ0 hsupp
  have hlhs : (2 * ((∑ r ∈ Finset.Icc 1 (R 1), cosTransform Ω (((2 * r : ℕ) : ℝ) / m)) +
          ∑ q ∈ (Finset.Icc 3 Q).filter (fun q => q % 2 = 1),
            (RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ)) *
              ∑ r ∈ Finset.Icc 1 (q * R q),
                ramanujanLagCoefficient q (2 * r) * cosTransform Ω (((2 * r : ℕ) : ℝ) / m))) +
        cosTransform Ω 0 * (1 + ∑ q ∈ (Finset.Icc 3 Q).filter (fun q => q % 2 = 1),
          RHTower.Sieve.sqfreeTotientInv q) =
      ((2 * ∑ r ∈ Finset.Icc 1 (R 1), cosTransform Ω (((2 * r : ℕ) : ℝ) / m)) + cosTransform Ω 0) +
      ((2 * ∑ q ∈ (Finset.Icc 3 Q).filter (fun q => q % 2 = 1),
          (RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ)) *
            ∑ r ∈ Finset.Icc 1 (q * R q),
              ramanujanLagCoefficient q (2 * r) * cosTransform Ω (((2 * r : ℕ) : ℝ) / m)) +
        cosTransform Ω 0 *
          ∑ q ∈ (Finset.Icc 3 Q).filter (fun q => q % 2 = 1), RHTower.Sieve.sqfreeTotientInv q) := by
    ring
  rw [hlhs]
  refine (abs_add_le _ _).trans ?_
  have hadd := add_le_add hbase hodd
  linarith

/-! ## §4. Stabilizer-Centered Decomposition and Actual Prime-Pair Parity Lock -/

/-- The `Q`-modulus parity-locked Hardy–Littlewood singular-series weight at integer lag `h`:
`2 ∑_{1≤q≤Q, q odd} (sqfreeTotientInv q / φ(q)) c_q(h)`. On even shifts `h = 2r`, this equals the
doubled odd-modulus singular series `2 + 2 ∑_{3≤q≤Q, q odd} (μ(q)² / φ(q)²) c_q(r)`. -/
def parityStabilizerWeight (Q h : ℕ) : ℝ :=
  2 * ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => q % 2 = 1),
    (RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ)) * ramanujanLagCoefficient q h

/-- On even shifts `2r`, `parityStabilizerWeight Q (2 * r) = parityStabilizerWeight Q r`. -/
theorem parityStabilizerWeight_two_mul (Q r : ℕ) :
    parityStabilizerWeight Q (2 * r) = parityStabilizerWeight Q r := by
  unfold parityStabilizerWeight
  congr 1
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [ramanujanLagCoefficient_odd_two_mul (Finset.mem_filter.mp hq).2 r]

/-- The parity-locked `Q`-modulus singular-series model sum over distinct coalescent odd integers
`3 ≤ n, m ≤ X` (`n % 2 = 1`, `m % 2 = 1`): replaces the prime-pair weight `acoef n * acoef m` in
`oddEvenShiftPrimeCoalSum` by `(1/4) parityStabilizerWeight Q (Nat.dist n m) / √(n * m)`.
The raw arithmetic weight has complete-period mean `1/8` in full integer rectangles. -/
def stabilizerModelOddCoalSum (Q : ℕ) (Ω g : ℝ → ℝ) (X θ₀ : ℝ) : ℝ :=
  (1 / π) * ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
    if 3 ≤ n ∧ 3 ≤ m ∧ n % 2 = 1 ∧ m % 2 = 1 ∧ n ≠ m ∧ |Real.log n - Real.log m| ≤ θ₀
    then ((1 / 4 : ℝ) * parityStabilizerWeight Q (Nat.dist n m) /
        (Real.sqrt n * Real.sqrt m)) * g (Real.log m) * cosTransform Ω (Real.log n - Real.log m)
    else 0

/-- The signed difference between `oddEvenShiftPrimeCoalSum` and the `Q`-modulus
Ramanujan model on coalescent odd integer pairs `3 ≤ n, m ≤ X`. -/
def stabilizerDiscrepancyOddCoalSum (Q : ℕ) (Ω g : ℝ → ℝ) (X θ₀ : ℝ) : ℝ :=
  (1 / π) * ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
    if 3 ≤ n ∧ 3 ≤ m ∧ n % 2 = 1 ∧ m % 2 = 1 ∧ n ≠ m ∧ |Real.log n - Real.log m| ≤ θ₀
    then ((if n.Prime ∧ m.Prime then acoef n * acoef m else 0) -
        (1 / 4 : ℝ) * parityStabilizerWeight Q (Nat.dist n m) /
          (Real.sqrt n * Real.sqrt m)) * g (Real.log m) * cosTransform Ω (Real.log n - Real.log m)
    else 0

/-- **Exact Stabilizer Decomposition of `oddEvenShiftPrimeCoalSum`.**
For every modulus cutoff `Q : ℕ`, window `Ω`, taper weight `g`, prime cutoff `X`, and aperture `θ₀`,
`oddEvenShiftPrimeCoalSum` decomposes identically into `stabilizerModelOddCoalSum Q` plus
`stabilizerDiscrepancyOddCoalSum Q`. -/
theorem oddEvenShiftPrimeCoalSum_eq_stabilizerModel_add_discrepancy
    (Q : ℕ) (Ω g : ℝ → ℝ) (X θ₀ : ℝ) :
    oddEvenShiftPrimeCoalSum Ω g X θ₀ =
      stabilizerModelOddCoalSum Q Ω g X θ₀ + stabilizerDiscrepancyOddCoalSum Q Ω g X θ₀ := by
  unfold oddEvenShiftPrimeCoalSum stabilizerModelOddCoalSum stabilizerDiscrepancyOddCoalSum
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases hodd : 3 ≤ n ∧ 3 ≤ m ∧ n % 2 = 1 ∧ m % 2 = 1 ∧ n ≠ m ∧ |Real.log n - Real.log m| ≤ θ₀
  · rw [if_pos hodd, if_pos hodd]
    obtain ⟨hn3, hm3, hn_odd, hm_odd, hne, hgap⟩ := hodd
    by_cases hp : n.Prime ∧ m.Prime
    · have hp_cond : n.Prime ∧ m.Prime ∧ 3 ≤ n ∧ 3 ≤ m ∧ n % 2 = m % 2 ∧
          n ≠ m ∧ |Real.log n - Real.log m| ≤ θ₀ :=
        ⟨hp.1, hp.2, hn3, hm3, hn_odd.trans hm_odd.symm, hne, hgap⟩
      rw [if_pos hp_cond, if_pos hp]
      ring
    · have hnp_cond : ¬ (n.Prime ∧ m.Prime ∧ 3 ≤ n ∧ 3 ≤ m ∧ n % 2 = m % 2 ∧
          n ≠ m ∧ |Real.log n - Real.log m| ≤ θ₀) := fun hc => hp ⟨hc.1, hc.2.1⟩
      rw [if_neg hnp_cond, if_neg hp]
      ring
  · have hnp_cond : ¬ (n.Prime ∧ m.Prime ∧ 3 ≤ n ∧ 3 ≤ m ∧ n % 2 = m % 2 ∧
        n ≠ m ∧ |Real.log n - Real.log m| ≤ θ₀) := by
      rintro ⟨hnP, hmP, hn3, hm3, _, hne, hgap⟩
      have hn_odd : n % 2 = 1 := hnP.eq_two_or_odd.resolve_left (by omega)
      have hm_odd : m % 2 = 1 := hmP.eq_two_or_odd.resolve_left (by omega)
      exact hodd ⟨hn3, hm3, hn_odd, hm_odd, hne, hgap⟩
    rw [if_neg hnp_cond, if_neg hodd, if_neg hodd, add_zero]

/-- **Actual Prime-Pair Parity Lock at `q = 2` (`θ₀ < 1 / 3`):**
For every coalescent aperture `θ₀ < 1 / 3`, weighting each contributing prime pair `(n, m)` in
`primeCoalSum Ω g X θ₀` by `ramanujanLagCoefficient 2 (Nat.dist n m)` reproduces
`primeCoalSum Ω g X θ₀` identically (`c_2(|n - m|) = +1` on every coalescent prime pair). -/
theorem primeCoalSum_ramanujan_two_eq (Ω g : ℝ → ℝ) (X : ℝ) {θ₀ : ℝ} (hθ₀ : θ₀ < 1 / 3) :
    (1 / π) * (∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
      if n.Prime ∧ m.Prime ∧ n ≠ m ∧ |Real.log n - Real.log m| ≤ θ₀
      then ramanujanLagCoefficient 2 (Nat.dist n m) *
        (acoef n * acoef m * g (Real.log m) * cosTransform Ω (Real.log n - Real.log m))
      else 0) = primeCoalSum Ω g X θ₀ := by
  unfold primeCoalSum
  congr 1
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
  split_ifs with h
  · obtain ⟨hnP, hmP, hne, hgap⟩ := h
    obtain ⟨_, _, _, _, hpar⟩ := odd_and_even_gap_of_prime_coalescent hnP hmP hne hgap hθ₀
    have heven : Nat.dist n m = 2 * (Nat.dist n m / 2) := by
      rcases le_total n m with hnm | hmn
      · rw [Nat.dist_eq_sub_of_le hnm]
        omega
      · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hmn]
        omega
    rw [heven, ramanujanLagCoefficient_two_even, one_mul]
  · rfl

/-- **Actual Prime-Pair Odd-Modulus Doubling Invariance (`θ₀ < 1 / 3`):**
For every odd modulus `q` (`q % 2 = 1`) and every coalescent aperture `θ₀ < 1 / 3`, the `(2 * q)`
Ramanujan lag-weighted prime coalescent sum equals the `q` Ramanujan lag-weighted prime coalescent
sum identically on actual prime pairs. -/
theorem primeCoalSum_ramanujan_two_mul_odd_eq {q : ℕ} (hq : q % 2 = 1)
    (Ω g : ℝ → ℝ) (X : ℝ) {θ₀ : ℝ} (hθ₀ : θ₀ < 1 / 3) :
    (1 / π) * (∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
      if n.Prime ∧ m.Prime ∧ n ≠ m ∧ |Real.log n - Real.log m| ≤ θ₀
      then ramanujanLagCoefficient (2 * q) (Nat.dist n m) *
        (acoef n * acoef m * g (Real.log m) * cosTransform Ω (Real.log n - Real.log m))
      else 0) =
    (1 / π) * (∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
      if n.Prime ∧ m.Prime ∧ n ≠ m ∧ |Real.log n - Real.log m| ≤ θ₀
      then ramanujanLagCoefficient q (Nat.dist n m) *
        (acoef n * acoef m * g (Real.log m) * cosTransform Ω (Real.log n - Real.log m))
      else 0) := by
  congr 1
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
  split_ifs with h
  · obtain ⟨hnP, hmP, hne, hgap⟩ := h
    obtain ⟨_, _, _, _, hpar⟩ := odd_and_even_gap_of_prime_coalescent hnP hmP hne hgap hθ₀
    have heven : Nat.dist n m = 2 * (Nat.dist n m / 2) := by
      rcases le_total n m with hnm | hmn
      · rw [Nat.dist_eq_sub_of_le hnm]
        omega
      · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hmn]
        omega
    rw [heven, ramanujanLagCoefficient_two_mul_odd_two_mul hq,
      ramanujanLagCoefficient_odd_two_mul hq]
  · rfl

/-! ## §5. Dynamic Scale-Dependent Poisson Horizon & `RBG` Ramanujan Parity-Twin Survival -/

/-- **Dynamic Scale-Adaptive Poisson-Horizon Singular-Series Coalescent Transfer (`Q(m) = ⌊m / b⌋₊`).**
For any smooth window `Ω ≥ 0` supported in `[a, b]` (`0 < a ≤ b`) and any scale `m ≥ b`, setting
the modulus cutoff dynamically to the exact Poisson horizon `Q(m) := ⌊m / b⌋₊` satisfies
`1 ≤ ⌊m / b⌋₊` and `(⌊m / b⌋₊ : ℝ) * b ≤ m` automatically (every modulus `q ≤ ⌊m / b⌋₊` has its
first nonzero dual Poisson mode `2π m / q ≥ 2π b > b` outside `supp Ω`), transferring the full
parity-locked singular series unconditionally to `-cosTransform Ω 0 * ∑_{1≤q≤⌊m/b⌋₊, q odd} sqfreeTotientInv q`
with zero external cutoff premise. -/
theorem abs_sum_dynamic_poissonHorizon_singularSeries_add_le
    {Ω : ℝ → ℝ} {a b m : ℝ} {R : ℕ → ℕ}
    (ha : 0 < a) (hab : a ≤ b) (hbm : b ≤ m)
    (hR : ∀ q ∈ (Finset.Icc 1 ⌊m / b⌋₊).filter (fun q => q % 2 = 1), 1 ≤ R q)
    (hΩ1 : ContDiff ℝ 1 Ω) (hΩ0 : ∀ τ, 0 ≤ Ω τ)
    (hsupp : ∀ τ, τ ∉ Icc a b → Ω τ = 0) :
    |(2 * ∑ q ∈ (Finset.Icc 1 ⌊m / b⌋₊).filter (fun q => q % 2 = 1),
          (RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ)) *
            ∑ r ∈ Finset.Icc 1 (q * R q),
              ramanujanLagCoefficient q (2 * r) * cosTransform Ω (((2 * r : ℕ) : ℝ) / m)) +
        cosTransform Ω 0 *
          ∑ q ∈ (Finset.Icc 1 ⌊m / b⌋₊).filter (fun q => q % 2 = 1),
            RHTower.Sieve.sqfreeTotientInv q| ≤
      (∑ q ∈ (Finset.Icc 1 ⌊m / b⌋₊).filter (fun q => q % 2 = 1),
        RHTower.Sieve.sqfreeTotientInv q * |cosTransform Ω (((2 * (q * R q) : ℕ) : ℝ) / m)|) +
      (b / m) * cosTransform Ω 0 *
        (1 + ∑ q ∈ (Finset.Icc 3 ⌊m / b⌋₊).filter (fun q => q % 2 = 1),
          (RHTower.Sieve.sqfreeTotientInv q / (q.totient : ℝ)) *
            (∑ d ∈ q.divisors, (d : ℝ) ^ 2)) +
      (m ^ 2 / (2 * (R 1 : ℝ) * a ^ 2)) * ∫ τ in a..b, (a * |deriv Ω τ| + Ω τ) := by
  have hb : 0 < b := ha.trans_le hab
  have hdiv1 : 1 ≤ m / b := (one_le_div hb).mpr hbm
  have hQ1 : 1 ≤ ⌊m / b⌋₊ := (Nat.le_floor_iff (by positivity)).mpr (by simpa using hdiv1)
  have hQm : ((⌊m / b⌋₊ : ℕ) : ℝ) * b ≤ m := by
    have hfl : ((⌊m / b⌋₊ : ℕ) : ℝ) ≤ m / b := Nat.floor_le (by positivity)
    exact (mul_le_mul_of_nonneg_right hfl hb.le).trans_eq (div_mul_cancel₀ m hb.ne')
  exact abs_sum_full_evenShift_singularSeries_cosTransform_add_le ha hab hQ1 hR hQm hΩ1 hΩ0 hsupp

/-- **Exact Identification of the `ArithmeticEffectivityTheory` Primitive-Root Ramanujan Sum with
`ramanujanLagCoefficient`:**
For every `q ≥ 1` and lag `h : ℕ`, `∑_{ζ ∈ primitiveRoots q ℂ} ζ^h = (ramanujanLagCoefficient q h : ℂ)`. -/
theorem ramanujanSum_eq_ramanujanLagCoefficient {q : ℕ} (hq : 0 < q) (h : ℕ) :
    GaloisForLFunctions.ArithmeticEffectivityTheory.ramanujanSum q h =
      (ramanujanLagCoefficient q h : ℂ) := by
  rw [GaloisForLFunctions.ArithmeticEffectivityTheory.ramanujanSum_eq_sum_moebius hq h,
    Nat.sum_divisorsAntidiagonal' (fun a b =>
      (ArithmeticFunction.moebius a : ℂ) * (if b ∣ h then (b : ℂ) else 0)),
    ramanujanLagCoefficient, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  split_ifs <;> simp [moebiusReal]

/-- **Exact Identification of `RenormalizedBiarithmeticGeometry.ramanujanMode` with
`ramanujanLagCoefficient`:**
For every `q ≥ 1` and lag `h : ℕ`, `ramanujanMode q h = ramanujanLagCoefficient q h`. -/
theorem ramanujanMode_eq_ramanujanLagCoefficient {q : ℕ} (hq : 0 < q) (h : ℕ) :
    GaloisForLFunctions.RenormalizedBiarithmeticGeometry.ramanujanMode q h =
      ramanujanLagCoefficient q h := by
  unfold GaloisForLFunctions.RenormalizedBiarithmeticGeometry.ramanujanMode
  rw [ramanujanSum_eq_ramanujanLagCoefficient hq h, Complex.ofReal_re]

/-- The odd core of a positive torsion order `n` with `¬ 4 ∣ n`: `n` if `n` is odd, and `n / 2` if
`n = 2q` with `q` odd. -/
def oddCore (n : ℕ) : ℕ :=
  if n % 2 = 1 then n else n / 2

theorem oddCore_odd_and_pos {n : ℕ} (hn : 0 < n) (hn4 : ¬ 4 ∣ n) :
    0 < oddCore n ∧ oddCore n % 2 = 1 := by
  unfold oddCore
  split_ifs with hodd
  · exact ⟨hn, hodd⟩
  · omega

/-- **Even-Shift Odd-Core Collapse of `RBG.ramanujanMode`:**
For every positive modulus `n` with `¬ 4 ∣ n` (in particular, every modulus with nonzero
Hardy–Littlewood singular-series weight `sqfreeTotientInv n ≠ 0`) and every `r : ℕ`,
`ramanujanMode n (2 * r) = ramanujanLagCoefficient (oddCore n) r = ramanujanMode (oddCore n) r`. -/
theorem ramanujanMode_evenShift_eq_oddCore {n : ℕ} (hn : 0 < n) (hn4 : ¬ 4 ∣ n) (r : ℕ) :
    GaloisForLFunctions.RenormalizedBiarithmeticGeometry.ramanujanMode n (2 * r) =
      GaloisForLFunctions.RenormalizedBiarithmeticGeometry.ramanujanMode (oddCore n) r := by
  obtain ⟨hc_pos, hc_odd⟩ := oddCore_odd_and_pos hn hn4
  rw [ramanujanMode_eq_ramanujanLagCoefficient hn (2 * r),
    ramanujanMode_eq_ramanujanLagCoefficient hc_pos r]
  unfold oddCore at hc_odd ⊢
  split_ifs with hodd
  · exact ramanujanLagCoefficient_odd_two_mul hodd r
  · have hn_eq : n = 2 * (n / 2) := by omega
    have hq_odd : (n / 2) % 2 = 1 := by omega
    conv_lhs => rw [hn_eq]
    exact ramanujanLagCoefficient_two_mul_odd_two_mul hq_odd r

/-- **Cross-Order Parity-Twin Survival for Even-Shift `RBG` Periodic Germs:**
In `RenormalizedBiarithmeticGeometry.ramanujanTwin_survival`, torsion modes on unrestricted lags
survive renormalization only on relations vanishing separately on each exact order `m`. On even
coalescent shifts `2 * r`, every family of torsion orders `ord : Fin N → ℕ` with `0 < ord α` and
`¬ 4 ∣ ord α` collapses onto `oddCore (ord α)`, so the renormalized `periodicGerm` survives
unconditionally (`0 ≤ quad A C`) on every coefficient vector `C` whose sum vanishes over each
joint `{q, 2q}` odd-core fiber (`{1, 2}`, `{3, 6}`, `{5, 10}`, …). -/
theorem evenShift_ramanujanParityTwin_survival {N : ℕ} (ord : Fin N → ℕ)
    (hord : ∀ α, 0 < ord α) (hn4 : ∀ α, ¬ 4 ∣ ord α)
    {x : Fin N → ℝ} (hx : ∀ α, 0 ≤ x α) :
    ∃ A : Matrix (Fin N) (Fin N) ℝ,
      (∀ α β, Tendsto (fun r =>
        GaloisForLFunctions.RenormalizedBiarithmeticGeometry.periodicGerm
          (fun α k => GaloisForLFunctions.RenormalizedBiarithmeticGeometry.ramanujanMode (ord α) (2 * k))
          x r α β -
        (-Real.log (1 - r)) *
          GaloisForLFunctions.RenormalizedBiarithmeticGeometry.cesaroGram
            (fun α k => GaloisForLFunctions.RenormalizedBiarithmeticGeometry.ramanujanMode (ord α) (2 * k))
            (∏ γ, oddCore (ord γ)) α β)
          (𝓝[<] 1) (𝓝 (A α β))) ∧
      ∀ C : Fin N → ℝ,
        (∀ m : ℕ, ∑ α ∈ Finset.univ.filter (fun α => oddCore (ord α) = m), C α = 0) →
          0 ≤ GaloisForLFunctions.RenormalizedBiarithmeticGeometry.quad A C := by
  classical
  let a : Fin N → ℕ → ℝ := fun α k =>
    GaloisForLFunctions.RenormalizedBiarithmeticGeometry.ramanujanMode (ord α) (2 * k)
  have ha_eq : ∀ α k, a α k =
      GaloisForLFunctions.RenormalizedBiarithmeticGeometry.ramanujanMode (oddCore (ord α)) k :=
    fun α k => ramanujanMode_evenShift_eq_oddCore (hord α) (hn4 α) k
  have hcore_pos : ∀ α, 0 < oddCore (ord α) := fun α => (oddCore_odd_and_pos (hord α) (hn4 α)).1
  have hq : 0 < ∏ γ, oddCore (ord γ) := Finset.prod_pos fun γ _ => hcore_pos γ
  have hper : ∀ α, Function.Periodic (a α) (∏ γ, oddCore (ord γ)) := by
    intro α k
    rw [ha_eq α (k + ∏ γ, oddCore (ord γ)), ha_eq α k]
    have hdvd : oddCore (ord α) ∣ ∏ γ, oddCore (ord γ) :=
      Finset.dvd_prod_of_mem _ (Finset.mem_univ α)
    have hp := (GaloisForLFunctions.RenormalizedBiarithmeticGeometry.ramanujanMode_periodic
      (hcore_pos α)).nat_mul ((∏ γ, oddCore (ord γ)) / oddCore (ord α))
    rw [Nat.cast_id, Nat.div_mul_cancel hdvd] at hp
    exact hp k
  obtain ⟨A, hA, hpos⟩ :=
    GaloisForLFunctions.RenormalizedBiarithmeticGeometry.periodicGerm_survival a hq hper hx
  refine ⟨A, hA, fun C hC => hpos C fun k => ?_⟩
  have hsum_eq : ∑ α, C α * a α k =
      ∑ α, C α *
        GaloisForLFunctions.RenormalizedBiarithmeticGeometry.ramanujanMode (oddCore (ord α)) k :=
    Finset.sum_congr rfl fun α _ => by rw [ha_eq α k]
  rw [hsum_eq, ← Finset.sum_fiberwise_of_maps_to (s := Finset.univ)
    (t := Finset.univ.image (fun α => oddCore (ord α))) (g := fun α => oddCore (ord α))
    (fun α _ => Finset.mem_image_of_mem _ (Finset.mem_univ α))]
  refine Finset.sum_eq_zero fun m _ => ?_
  have hfib : ∑ α ∈ Finset.univ.filter (fun α => oddCore (ord α) = m),
      C α * GaloisForLFunctions.RenormalizedBiarithmeticGeometry.ramanujanMode (oddCore (ord α)) k =
    (∑ α ∈ Finset.univ.filter (fun α => oddCore (ord α) = m), C α) *
      GaloisForLFunctions.RenormalizedBiarithmeticGeometry.ramanujanMode m k := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [(Finset.mem_filter.mp hα).2]
  rw [hfib, hC m, zero_mul]

/-! ## §6. Multiplicity-Refined Weighted Seam & Simple-Critical Coalescent Certificates -/

section WeightedMultSeam

open Matrix RHLinalg Zeta23 Zeta23.ZeroSide Zeta23.Tail Zeta23.Assembly Zeta23.ThmE

/-- Off-line multiple zero mass of a `ZeroBlockData` block is invariant under grid weighting
`weightBlock D w`. -/
theorem blockOffLineMultipleMass_weightBlock {ι d : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype d] (D : ZeroBlockData ι d) (w : d → ℝ) :
    RHTower.blockOffLineMultipleMass (RHTower.weightBlock D w) =
      RHTower.blockOffLineMultipleMass D := by
  classical
  unfold RHTower.blockOffLineMultipleMass RHTower.weightBlock
  rfl

/-- **Multiplicity-Refined `c = 2` Rank–Trace Certificate for Weighted Gram Matrices:**
For grid weights `|w k| ≤ 1`, retaining the multiplicity excess `N - (s₁ + 2s₂ + 2p)` in the
weighted block Gram matrix `Â_w = c⁻¹ • (weightBlock D w).blockA` yields
`4 tr Â_w - ‖Â_w‖_F² - 2 N + M_off ≤ s₁`. -/
theorem weighted_rank_certificate_mult2_offLineMultiple {ι d : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype d] [DecidableEq d] (D : ZeroBlockData ι d) (Pr : D.PairReps) {w : d → ℝ}
    (hw : ∀ k, |w k| ≤ 1) {c : ℝ} (hc : 0 < c)
    (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ 2 ≤ c) :
    4 * rtrace (((c⁻¹ : ℝ) : ℂ) • (RHTower.weightBlock D w).blockA) -
      frobSq (((c⁻¹ : ℝ) : ℂ) • (RHTower.weightBlock D w).blockA) -
      2 * (D.Ncount : ℝ) + (RHTower.blockOffLineMultipleMass D : ℝ) ≤ (D.s₁ : ℝ) := by
  set D' := RHTower.weightBlock D w
  set Pr' := RHTower.weightPairReps D w Pr
  have hdec := (D'.blockP_add_blockQ c).symm
  have hraw := RHTower.four_rtrace_sub_frobSq_le_block D' Pr' hc
    (RHTower.weightBlock_hPois D hw hPois)
  rw [← hdec] at hraw
  have hmass := RHTower.blockOffLineMultipleMass_add_le D' Pr'
  have hmass' : (RHTower.blockOffLineMultipleMass D' : ℝ) +
      2 * ((D'.s₁ : ℝ) + 2 * (D'.s₂ : ℝ) + 2 * (Pr'.p : ℝ)) ≤ 2 * (D'.Ncount : ℝ) := by
    exact_mod_cast hmass
  have hbm : RHTower.blockOffLineMultipleMass D' = RHTower.blockOffLineMultipleMass D :=
    blockOffLineMultipleMass_weightBlock D w
  have hs₁ : D'.s₁ = D.s₁ := rfl
  have hN : D'.Ncount = D.Ncount := rfl
  rw [hbm, hs₁, hN] at hmass'
  rw [hs₁] at hraw
  linarith

/-- **Multiplicity-Refined Weighted Seam Inequality (`seamA_weighted_mult2_offLineMultiple`):**
For grid weights `|w k| ≤ 1` and `B₀ = θ₀ / (a L)`,
`4 tr Ĝ_w - ‖Ĝ_w‖_F² - 2 N(T, 2T) - 3 N_II - B₀(4 + 2 √(‖Ĝ_w‖_F²) + B₀)
  ≤ N₀ˢ(T, 2T) - M_off(T, 2T)`.
Strictly refines `RHTower.seamA_weighted` (which bounded only `N₀*`) by retaining both the
critical multiplicity excess `s₂` and twice the off-line multiple mass `M_off`. -/
theorem seamA_weighted_mult2_offLineMultiple {Z : ZeroConfig} {P : Params} {T A₀ C₁ : ℝ}
    (hT : 0 ≤ T) (H : TailHyp Z P T A₀ C₁) (hconj : PhiHatConj T P)
    (hreal : PhiHatReal T P) (hPois : PoissonSq T P) (ha : 0 < P.a T)
    {w : Fin (P.d T) → ℝ} (hw : ∀ k, |w k| ≤ 1) :
    4 * rtrace (P.hat T (RHTower.wmat w (Z.Gz P T))) -
      frobSq (P.hat T (RHTower.wmat w (Z.Gz P T))) -
      2 * (Z.N T (2 * T) : ℝ) - 3 * (NII Z T : ℝ) -
      theta0 A₀ (Real.exp (P.L T / 4) * C₁) T / (P.a T * P.L T) *
        (4 + 2 * Real.sqrt (frobSq (P.hat T (RHTower.wmat w (Z.Gz P T)))) +
          theta0 A₀ (Real.exp (P.L T / 4) * C₁) T / (P.a T * P.L T)) ≤
      (Z.N0s T (2 * T) : ℝ) - (RHTower.offLineMultipleMass Z T (2 * T) : ℝ) := by
  have hL := H.L_pos
  have hc : 0 < P.a T * P.L T ^ 2 := by positivity
  set D := blockData Z T P hconj with hD
  have hAw : P.hat T (RHTower.wmat w (Z.Az P T)) =
      (((P.a T * P.L T ^ 2)⁻¹ : ℝ) : ℂ) • (RHTower.weightBlock D w).blockA := by
    rw [ZeroSide.hat_eq]
    congr 1
    ext k l
    rw [RHTower.weightBlock_blockA_apply, RHTower.wmat, Az_eq_blockA Z T P hconj]
  have hcore := weighted_rank_certificate_mult2_offLineMultiple D
    (mkPairReps Z T _ (evalVec_reflect hconj)) hw hc (sum_normSq_v_le Z T P hconj hreal hPois)
  have hNc : (D.Ncount : ℝ) = (Z.NIprime T : ℝ) := by
    rw [hD, blockData, ← NIprime_eq_mk Z T _ (evalVec_reflect hconj)]
  have hs₁ : (D.s₁ : ℝ) = (Z.s1 T : ℝ) := by
    rw [hD, blockData, ← s1_eq_mk Z T _ (evalVec_reflect hconj)]
  have hbm : RHTower.blockOffLineMultipleMass D =
      RHTower.offLineMultipleMass Z (T - D0 T) (2 * T + D0 T) := by
    rw [hD, blockData, RHTower.blockOffLineMultipleMass_mkData Z hconj]
  rw [← hAw, hNc, hs₁, hbm] at hcore
  have hGAE : P.hat T (RHTower.wmat w (Z.Gz P T)) =
      P.hat T (RHTower.wmat w (Z.Az P T)) + P.hat T (RHTower.wmat w (Z.Ez P T)) := by
    rw [← hat_add, ← RHTower.wmat_add]
    congr 2
    simp [ZeroConfig.Ez]
  have hE : (P.hat T (RHTower.wmat w (Z.Ez P T))).IsHermitian := by
    rw [ZeroSide.hat_eq]
    exact ZeroBlockData.isHermitian_real_smul
      (RHTower.wmat_isHermitian w (H.Ez_isHermitian hconj)) _
  have hBle := RHTower.traceNorm_hat_wmat_Ez_le H ha hw hE
  have hB0 := traceNorm_nonneg hE
  have hB₀ : 0 ≤ theta0 A₀ (Real.exp (P.L T / 4) * C₁) T / (P.a T * P.L T) := hB0.trans hBle
  have hpert := ctr_sub_frobSq_perturb 4 (by norm_num) hGAE hB₀
    ((abs_rtrace_le_traceNorm hE).trans hBle)
    ((frobSq_le_traceNorm_sq hE).trans (pow_le_pow_left₀ hB0 hBle 2))
  have hs1 : (Z.s1 T : ℝ) ≤ (Z.N0s T (2 * T) : ℝ) + (NII Z T : ℝ) := by
    exact_mod_cast s1_le Z hT
  have hNI : (Z.NIprime T : ℝ) = (Z.N T (2 * T) : ℝ) + (NII Z T : ℝ) := by
    exact_mod_cast NIprime_eq Z hT
  have hmono : (RHTower.offLineMultipleMass Z T (2 * T) : ℝ) ≤
      (RHTower.offLineMultipleMass Z (T - D0 T) (2 * T + D0 T) : ℝ) := by
    exact_mod_cast RHTower.offLineMultipleMass_mono Z (by linarith [D0_nonneg T])
      (by linarith [D0_nonneg T])
  rw [hNI] at hcore
  linarith [hcore, hpert, hs1, hmono]

/-- Single-height combination for the multiplicity-refined smooth-weighted certificate at
bandwidth `4/3`. -/
theorem certificate_at_simple_and_offLineMultiple {ε₁ : ℝ} {u : ℝ → ℝ} {T : ℝ}
    (hF : LocalHypsCoreW params43.crho (params43.toSetting T) (params43.localFun T))
    (hT300 : Tail.T₀ ≤ T) (hwL : 8 * params43.w ≤ params43.L T) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (zetaZeroConfig.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    (hu : WindowProfile ε₁ u) {ℓ₀ K Kq C₀ C1 Cψ C2 CΓ Ct Mk η v ε ε' CR : ℝ} {k : ℕ}
    (hℓ₀ : 0 ≤ ℓ₀) (hlip : ∀ s t, |u s - u t| ≤ ℓ₀ * |s - t|) (hℓ1 : 2 * ℓ₀ / T ≤ 1)
    (hD5 : 5 ≤ ε₁ * T) (hK : 0 ≤ K)
    (hμinc : ∀ t, 2 ≤ t → ∀ r, |Zeta23.mu (t + r) - Zeta23.mu t| ≤ (K * |r| + 10 * r ^ 2) / t)
    (hKq0 : 0 ≤ Kq)
    (hKq : ∀ t : ℝ, 2 ≤ t → ∀ r : ℝ, |muq 0 1 (t + r) - muq 0 1 t| ≤ Kq * (|r| + r ^ 2) / t)
    (hμl : ∀ τ ∈ Icc T (2 * T), |Zeta23.mu τ| ≤ Zeta23.l T) (hC₀ : 0 ≤ C₀)
    (hμ : NuBound (params43.toSetting T) (C₀ * Zeta23.l T) Zeta23.mu)
    (hν : NuBound (params43.toSetting T) (Bconst (params43.toSetting T)) (Zeta23.nuX (params43.X T)))
    (hC1 : 0 ≤ C1) (hCψ : 0 ≤ Cψ) (hMk0 : 0 ≤ Mk)
    (hMk : ∀ x, |iteratedDeriv k (fun x => u x ^ 4) x| ≤ Mk) (hk : 2 ≤ k) (hηk : 2 ≤ η * k)
    (hv : 2 ≤ v) (hvT : T = v ^ 12) (hlT : 1 ≤ Real.log T) (hl : Zeta23.l T ≤ Real.log T)
    (hL : params43.L T ≤ 2 * Real.log T) (hLc : params43.crho ≤ params43.L T)
    (hsX : Real.sqrt (params43.X T) ≤ v ^ 8)
    (hA : ∑ n ∈ primeRange (params43.X T), acoef n ≤ 3 * Real.sqrt (params43.X T))
    (hψ : ∑ n ∈ primeRange (params43.X T), (Λ n : ℝ) ≤ Cψ * params43.X T)
    (hS : ∑ n ∈ primeRange (params43.X T), (Λ n : ℝ) / n
      ≤ (params43.L T ^ 2 / 2 + C1 * params43.L T) / Real.log 2)
    (hε' : 0 < ε') (hε'1 : ε' ≤ 1) (hε'ε : ε' ≤ ε) (hl14 : 14 / ε' ≤ Zeta23.l T)
    (hΓ : |(∫ τ in T..(2 * T), Zeta23.mu τ ^ 2) - T * ell1 T ^ 2 / (4 * π ^ 2)|
      ≤ CΓ * (T * ell1 T ^ 2 / (4 * π ^ 2)) / Zeta23.l T ^ 2)
    (hC2 : ∀ x : ℝ, 2 ≤ x → |∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (Λ n : ℝ) ^ 2 / n * (Real.log x - Real.log n)
      - Real.log x ^ 3 / 6| ≤ C2 * Real.log x ^ 2)
    (ha : 1 - 2 / (4 / 3 * Zeta23.l T) ≤ params43.a T) (hCt : 0 ≤ Ct)
    (htr : |trGtA (params43.toSetting T) (params43.localFun T)
        - params43.a T * params43.L T * (zetaZeroConfig.N T (2 * T) : ℝ)|
      ≤ Ct * (params43.L T * (1 + Real.log T + Real.sqrt (params43.X T))))
    (hRv : |(zetaZeroConfig.N T (2 * T) : ℝ) - T * ell1 T / (2 * π)| ≤ CR * Real.log T)
    (hCR : 0 ≤ CR)
    (hE : 4 * ((6 * (1 + 2 * ℓ₀) + 4) * T + traceConst params43.crho Kq Ct * Real.log T ^ 6 * v ^ 11)
        + ((|CΓ| + 2 * |C2|) * T
          + (chanConst params43.crho ℓ₀ K C1 Cψ Mk + gridConst params43.crho ℓ₀ ε₁ C₀ C1 Cψ)
            * Real.log T ^ 6 * v ^ 11)
        + (43 / 36 + ε' / 2 + 32 * π * ε₁) * (CR * Real.log T) + 3 * (NII zetaZeroConfig T : ℝ)
      ≤ ε / 4 * (zetaZeroConfig.N T (2 * T) : ℝ))
    (hB : Tail.theta0 A₀ (Real.exp (params43.L T / 4) * params43.C1 T) T / (params43.a T * params43.L T)
        * (4 + 4 * Real.sqrt (zetaZeroConfig.N T (2 * T) : ℝ)
          + Tail.theta0 A₀ (Real.exp (params43.L T / 4) * params43.C1 T) T / (params43.a T * params43.L T))
      ≤ ε / 4 * (zetaZeroConfig.N T (2 * T) : ℝ))
    (hEf : (|CΓ| + 2 * |C2|) * T
        + (chanConst params43.crho ℓ₀ K C1 Cψ Mk + gridConst params43.crho ℓ₀ ε₁ C₀ C1 Cψ)
          * Real.log T ^ 6 * v ^ 11 ≤ (zetaZeroConfig.N T (2 * T) : ℝ) / 10)
    (hE₀ : CR * Real.log T ≤ (zetaZeroConfig.N T (2 * T) : ℝ) / 10)
    (hN₀ : 0 ≤ (zetaZeroConfig.N0s T (2 * T) : ℝ) -
      (RHTower.offLineMultipleMass zetaZeroConfig T (2 * T) : ℝ)) :
    (29 / 36 - 32 * π * ε₁ - ε) * (zetaZeroConfig.N T (2 * T) : ℝ) - coalescentSurplus u η T ≤
      (zetaZeroConfig.N0s T (2 * T) : ℝ) -
        (RHTower.offLineMultipleMass zetaZeroConfig T (2 * T) : ℝ) := by
  have hP := paramsValidFam_params43
  have hπ := Real.pi_pos
  have hT0 : 0 < T := by have : (300 : ℝ) ≤ T := hT300; linarith only [this]
  have hT2π : 2 * π * 1 ≤ T := by
    have : (300 : ℝ) ≤ T := hT300; linarith only [this, Real.pi_lt_four]
  have hL8 : 8 ≤ params43.L T := hF.eight_le_L
  have ha2 : 1 / 2 ≤ params43.a T := hF.b_ge_half.trans hF.b_le_a
  have ha0 : 0 < params43.a T := by linarith only [ha2]
  have Htail : Tail.TailHyp zetaZeroConfig params43 T A₀ (params43.C1 T) :=
    { hT := hT300, hL := by linarith only [hL8], hA₀ := hA₀, hloc := hloc,
      hC₁ := Tail.C1_nonneg _ T,
      hdecay := fun r y hy hz => norm_phiHat_sub_I_mul_le_fam hP hwL r y hy hz }
  have hseam := seamA_weighted_mult2_offLineMultiple hT0.le Htail
    (fun z => GzGp.phiHat_conj params43 T z)
    (fun r => GzGp.phiHat_ofReal params43 T r) (poissonSq_fam hP hwL) ha0
    (w := profileGrid u T) (abs_profileGrid_le hu T)
  have hGzGp : zetaZeroConfig.Gz params43 T = params43.Gp T := by
    refine zetaZeroConfig.Gz_eq_Gp params43 T paperInputs_zeta.EF (by linarith only [hL8]) ?_ ?_
    · exact (Complex.ofRealCLM.contDiff.comp
        (Taper.phi_contDiff hP.taper hP.w_pos (hP.two_w_le hwL))).of_le (by norm_num)
    · exact closure_minimal (Taper.phi_support_subset hP.taper hP.w_pos) isClosed_Icc
  rw [hGzGp] at hseam
  have htrb := trace_ge_at hF hu hℓ₀ hlip hKq0 hKq hμl hCt htr hv hvT hlT hL hsX hA
  have hfb := frob_le_at hF (by linarith only [hT2π]) hu hℓ₀ hlip hℓ1 hD5 hK hμinc hμl hC₀ hμ hν
    hC1 hCψ hMk0 hMk hk hηk (by linarith only [hv]) hvT hlT hl hL hLc hsX hA hψ hS hε' hε'1 hl14
    hΓ hC2 ha (η := η) (CΓ := CΓ) (C2 := C2)
  have hM : T * ell1 T / (2 * π) ≤ (zetaZeroConfig.N T (2 * T) : ℝ) + CR * Real.log T := by
    have := (abs_le.mp hRv).1; linarith only [this]
  have hTl : T * Zeta23.l T ≤ 2 * π * (T * ell1 T / (2 * π)) := by
    have hc₀ : 0 ≤ 2 * Real.log 2 - 1 := by have := Real.log_two_gt_d9; linarith only [this]
    have e : 2 * π * (T * ell1 T / (2 * π)) = T * ell1 T := by field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left (by unfold ell1; linarith only [hc₀]) hT0.le
  have hN0 : (0 : ℝ) ≤ (zetaZeroConfig.N T (2 * T) : ℝ) := Nat.cast_nonneg _
  have hB0 : 0 ≤ Tail.theta0 A₀ (Real.exp (params43.L T / 4) * params43.C1 T) T /
      (params43.a T * params43.L T) :=
    div_nonneg (Htail.tailInputs ha0 (fun z => Params.phiHat_conj z)).theta_nonneg (by positivity)
  have htr' : (zetaZeroConfig.N T (2 * T) : ℝ) - 4 * ε₁ * (T * Zeta23.l T)
      - ((6 * (1 + 2 * ℓ₀) + 4) * T + traceConst params43.crho Kq Ct * Real.log T ^ 6 * v ^ 11)
      ≤ rtrace (params43.hat T (RHTower.wmat (profileGrid u T) (params43.Gp T))) := by
    have e : 4 * ε₁ * (T * Zeta23.l T) = 4 * ε₁ * T * Zeta23.l T := by ring
    linarith only [htrb, e]
  have hfb' : frobSq (params43.hat T (RHTower.wmat (profileGrid u T) (params43.Gp T)))
      ≤ (43 / 36 + ε' / 2) * (T * ell1 T / (2 * π)) + coalescentSurplus u η T
        + ((|CΓ| + 2 * |C2|) * T
          + (chanConst params43.crho ℓ₀ K C1 Cψ Mk + gridConst params43.crho ℓ₀ ε₁ C₀ C1 Cψ)
            * Real.log T ^ 6 * v ^ 11) := by
    linarith only [hfb]
  exact certificate_combine hseam htr' hfb' hM hTl hN0 hN₀ hu.pos.le hε'.le hε'1 hε'ε hE hB0 hB
    hEf (by positivity) hE₀

/-- **Smooth-Weighted Bandwidth-`4/3` Certificate for Simple Critical Zeros & Off-Line Multiple
Mass (`WindowProfile` collar form):**
For every `WindowProfile ε₁ u`, `η > 0`, and `ε > 0`, eventually
`(29/36 - 32π ε₁ - ε) N(T, 2T) - coalescentSurplus u η T + M_off(T, 2T) ≤ N₀ˢ(T, 2T)`. -/
theorem zeta_coalescent_certificate_four_thirds_simple_and_offLineMultiple
    {ε₁ : ℝ} {u : ℝ → ℝ} (hu : WindowProfile ε₁ u) {η : ℝ} (hη : 0 < η) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T in atTop,
      (29 / 36 - 32 * π * ε₁ - ε) * (Ncount T (2 * T) : ℝ) - coalescentSurplus u η T +
        (RHTower.offLineMultipleMass zetaZeroConfig T (2 * T) : ℝ) ≤
        (N0simple T (2 * T) : ℝ) := by
  obtain ⟨ε', hε'def⟩ : ∃ x : ℝ, x = min ε 1 := ⟨_, rfl⟩
  have hε'0 : 0 < ε' := by rw [hε'def]; exact lt_min hε one_pos
  have hε'1 : ε' ≤ 1 := by rw [hε'def]; exact min_le_right _ _
  have hε'ε : ε' ≤ ε := by rw [hε'def]; exact min_le_left _ _
  have hπ := Real.pi_pos
  have hP := paramsValidFam_params43
  have H := paperInputs_zeta
  have hε₁ := hu.pos
  obtain ⟨CR, TR, hRvM⟩ := H.RvM.main
  obtain ⟨A₀, hA₀, hloc⟩ := H.RvM.local_count
  obtain ⟨CN, hNII⟩ := Tail.eventually_NII_le zetaZeroConfig hA₀ hloc
  obtain ⟨Ct, Tt, hCt, htrW⟩ := prop_trace_zeta_wide (cϱ := params43.crho)
    (by norm_num : (0 : ℝ) < 4 / 3) |CR|
  obtain ⟨TL, hTL⟩ := localHypsCoreW_eventually_fam hP
  obtain ⟨R, hRdef⟩ : ∃ x : ℝ, x = Taper.l1Deriv2 stdProfile := ⟨_, rfl⟩
  have hR0 : 0 ≤ R := by rw [hRdef]; exact MeasureTheory.integral_nonneg fun x => abs_nonneg _
  obtain ⟨K, hK0, hK⟩ := mu_increment_bound gammaFacts
  obtain ⟨Kq, hKq0, hKq⟩ := muq_increment_bound
    (GammaChi.gammaFactsChi (κ := 0) (q := 1) (by norm_num) le_rfl) le_rfl
  obtain ⟨C₀, Tm, hC₀1, hμB⟩ := mu_nuBound
  obtain ⟨Tμ, hμl⟩ := mu_abs_le_l gammaFacts
  obtain ⟨TB, hνB⟩ := nuBound_eventually (4 / 3) gammaFacts (by norm_num : (0 : ℝ) < 4 / 3)
  obtain ⟨x₀, hx₀⟩ := H.cheb.cheb1b
  obtain ⟨Cψ, hψ⟩ := H.cheb.cheb1a
  obtain ⟨C1, hC1⟩ := H.cheb.cheb2a
  obtain ⟨C2, hC2⟩ := H.cheb.cheb2b
  obtain ⟨CΓ, TΓ, hΓsq⟩ := gammaFacts.int_mu_sq
  obtain ⟨Tpos, hTpos⟩ := RHTower.two_thirds_add_offLineMultipleMass_le_N0simple (1 / 6) (by norm_num)
  obtain ⟨ℓ₀, hℓ₀, hlip⟩ := hu.exists_lipschitz
  obtain ⟨k, hk2, hηk⟩ : ∃ k : ℕ, 2 ≤ k ∧ 2 ≤ η * k := by
    refine ⟨max 2 ⌈2 / η⌉₊, le_max_left _ _, ?_⟩
    have h1 : 2 / η ≤ (⌈2 / η⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈2 / η⌉₊ : ℕ) : ℝ) ≤ ((max 2 ⌈2 / η⌉₊ : ℕ) : ℝ) := by
      exact_mod_cast le_max_right _ _
    have h3 : η * (2 / η) = 2 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left (h1.trans h2) hη.le]
  obtain ⟨Mk, hMk0, hMk⟩ := hu.exists_iteratedDeriv_pow_four_le k
  set cr := params43.crho with hcr
  have hcr4 : 4 ≤ cr := (hTL (max TL 0) (le_max_left _ _)).four_le_cϱ
  set Kpow := 4 * traceConst cr Kq Ct + (chanConst cr ℓ₀ K |C1| |Cψ| Mk
    + gridConst cr ℓ₀ ε₁ C₀ |C1| |Cψ|) with hKpow
  have hKpow0 : 0 ≤ Kpow := by
    have h1 : 0 ≤ traceConst cr Kq Ct := by unfold traceConst; positivity
    have h2 := chanConst_nonneg (by linarith only [hcr4]) hℓ₀ hK0 (abs_nonneg C1) (abs_nonneg Cψ) hMk0
      (cϱ := cr)
    have h3 := gridConst_nonneg (ℓ₀ := ℓ₀) (ε₁ := ε₁) (C₀ := C₀) (by linarith only [hcr4])
      (abs_nonneg C1) (abs_nonneg Cψ) (cϱ := cr)
    rw [hKpow]; positivity
  set Klin := 4 * (6 * (1 + 2 * ℓ₀) + 4) + (|CΓ| + 2 * |C2|) with hKlin
  have hKlin0 : 0 ≤ Klin := by rw [hKlin]; positivity
  set Kc := 43 / 36 + 1 / 2 + 32 * π * ε₁ with hKc
  have hKc1 : 1 ≤ Kc := by
    rw [hKc]; have : 0 ≤ 32 * π * ε₁ := by positivity
    linarith only [this]
  have hl := Real.tendsto_log_atTop
  have e1 := eventually_l_bounds
  have e2 := eventually_ge_atTop (max (max (max TR Tt) (max TL Tm))
    (max (max Tμ TB) (max TΓ (max Tpos 4096))))
  have e3 := eventually_ge_atTop (max (max (5 / ε₁) (2 * ℓ₀)) (max (8 * π * |CR|)
    (max (256 * π * Kc * |CR| / ε') (8 * π * (1024 / ε' ^ 2 + 40 / ε')))))
  have e4 := hl.eventually_ge_atTop (max (max (28 / ε' + 12) (3 * cr / 2 + 12))
    (max (3 * (|x₀| + 2) / 2) (256 * π * Klin / ε')))
  have e5 := eventually_log_pow_rpow_le 6 (by norm_num : (11 : ℝ) / 12 < 1) hKpow0
    (by positivity : (0 : ℝ) < ε' / (256 * π))
  have e6 := eventually_log_pow_rpow_le 0 (by norm_num : (1 : ℝ) / 2 < 1)
    (by positivity : (0 : ℝ) ≤ 3 * |CN|) (by positivity : (0 : ℝ) < ε' / (256 * π))
  have e7 := eventually_log_pow_rpow_le_const 1 (by norm_num : (4 : ℝ) / 3 / 2 - 1 < 0)
    (by positivity : (0 : ℝ) ≤ 32 * A₀ * R ^ 2) (by norm_num : (0 : ℝ) < 1)
  filter_upwards [e1, e2, e3, e4, e5, e6, e7, hNII] with T ⟨hlog1, hl1, hlo, hhi⟩ hT1 hT2 hlogT hrate
    hrate2 hrate3 hNIIT
  have hTR : TR ≤ T := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hT1))
  have hTt : Tt ≤ T := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hT1))
  have hTLT : TL ≤ T := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hT1))
  have hTm : Tm ≤ T := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hT1))
  have hTμ : Tμ ≤ T := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hT1))
  have hTB : TB ≤ T := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hT1))
  have hTΓ : TΓ ≤ T := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hT1))
  have hTp4 : max Tpos 4096 ≤ T :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hT1))
  have hTposT : Tpos ≤ T := (le_max_left _ _).trans hTp4
  have hT4096 : (4096 : ℝ) ≤ T := (le_max_right _ _).trans hTp4
  have hTε : 5 / ε₁ ≤ T := (le_max_left _ _).trans ((le_max_left _ _).trans hT2)
  have hTℓ : 2 * ℓ₀ ≤ T := (le_max_right _ _).trans ((le_max_left _ _).trans hT2)
  have hTCR : 8 * π * |CR| ≤ T := (le_max_left _ _).trans ((le_max_right _ _).trans hT2)
  have hTKc : 256 * π * Kc * |CR| / ε' ≤ T :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hT2))
  have hTN : 8 * π * (1024 / ε' ^ 2 + 40 / ε') ≤ T :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hT2))
  have hlε : 28 / ε' + 12 ≤ Real.log T := (le_max_left _ _).trans ((le_max_left _ _).trans hlogT)
  have hlc : 3 * cr / 2 + 12 ≤ Real.log T := (le_max_right _ _).trans ((le_max_left _ _).trans hlogT)
  have hlx : 3 * (|x₀| + 2) / 2 ≤ Real.log T := (le_max_left _ _).trans ((le_max_right _ _).trans hlogT)
  have hlK : 256 * π * Klin / ε' ≤ Real.log T :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hlogT)
  have hT0 : 0 < T := by linarith only [hT4096]
  have hF := hTL T hTLT
  have hLl : params43.L T = 4 / 3 * Zeta23.l T := rfl
  have hw : params43.w = 1 := rfl
  have hL8 : 8 ≤ params43.L T := by
    have : 12 ≤ Real.log T := by have := (by positivity : (0 : ℝ) ≤ 28 / ε'); linarith only [this, hlε]
    rw [hLl]; linarith only [this, hlo]
  have hwL : 8 * params43.w ≤ params43.L T := by rw [hw]; linarith only [hL8]
  have hL : params43.L T ≤ 2 * Real.log T := by rw [hLl]; linarith only [hhi, hl1]
  have hLc : cr ≤ params43.L T := by rw [hLl]; linarith only [hlo, hlc]
  obtain ⟨hv2, hvT, hsX, hv11⟩ := scale_facts hT4096 hhi
  set v := T ^ (1 / 12 : ℝ)
  have hXL : params43.X T = Real.exp (params43.L T) := rfl
  have hlogX : Real.log (params43.X T) = params43.L T := by rw [hXL, Real.log_exp]
  have hXx : max x₀ 2 ≤ params43.X T := by
    rw [hXL]
    have h1 : params43.L T + 1 ≤ Real.exp (params43.L T) := Real.add_one_le_exp _
    have h2 : |x₀| + 2 ≤ params43.L T := by rw [hLl]; linarith only [hlo, hlx]
    exact max_le (by linarith only [le_abs_self x₀, h1, h2]) (by linarith only [h1, h2, abs_nonneg x₀])
  have hX2 : 2 ≤ params43.X T := (le_max_right _ _).trans hXx
  have hA : ∑ n ∈ Zeta23.PrimeSide.primeRange (params43.X T), acoef n ≤
      3 * Real.sqrt (params43.X T) := by
    have := hx₀ (params43.X T) ((le_max_left _ _).trans hXx)
    unfold Zeta23.PrimeSide.primeRange acoef; exact this
  have hψ' : ∑ n ∈ Zeta23.PrimeSide.primeRange (params43.X T), (Λ n : ℝ) ≤
      |Cψ| * params43.X T := by
    have := hψ (params43.X T) hX2
    have h2 : Cψ * params43.X T ≤ |Cψ| * params43.X T :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith only [hX2])
    unfold Zeta23.PrimeSide.primeRange; linarith only [this, h2]
  have hS : ∑ n ∈ Zeta23.PrimeSide.primeRange (params43.X T), (Λ n : ℝ) / n
      ≤ (params43.L T ^ 2 / 2 + |C1| * params43.L T) / Real.log 2 := by
    have h := sum_vonMangoldt_div_le hC1 hX2
    rw [hlogX] at h
    refine h.trans (div_le_div_of_nonneg_right ?_ (Real.log_pos (by norm_num)).le)
    have := mul_le_mul_of_nonneg_right (le_abs_self C1) (by linarith only [hL8] : (0 : ℝ) ≤ params43.L T)
    linarith only [this]
  have hΓ := hΓsq T hTΓ
  have ha : 1 - 2 / (4 / 3 * Zeta23.l T) ≤ params43.a T := by
    have := one_sub_le_a_params43 hwL
    rw [hw, hLl] at this; simpa using this
  have hε₁T : 5 ≤ ε₁ * T := by rw [div_le_iff₀ hε₁] at hTε; linarith only [hTε]
  have hℓ1 : 2 * ℓ₀ / T ≤ 1 := by rw [div_le_one hT0]; exact hTℓ
  have hl14 : 14 / ε' ≤ Zeta23.l T := by
    have e : 14 / ε' = (28 / ε') / 2 := by ring
    linarith only [hlo, hlε, e]
  have hμ : NuBound (params43.toSetting T) (C₀ * Zeta23.l T) Zeta23.mu := hμB _ hTm
  have hν := hνB (params43.toSetting T) rfl hTB
  have hμl' : ∀ τ ∈ Icc T (2 * T), |Zeta23.mu τ| ≤ Zeta23.l T := hμl (params43.toSetting T) hTμ
  set N : ℝ := (zetaZeroConfig.N T (2 * T) : ℝ)
  have hRv0 := hRvM T hTR
  have hRv : |N - T * ell1 T / (2 * π)| ≤ |CR| * Real.log T := by
    rw [show T * ell1 T / (2 * π) = T / (2 * π) * ell1 T by ring]
    exact hRv0.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith only [hlog1]))
  have htr := htrW (params43.toSetting T) (params43.localFun T) rfl hTt hF N (by
    have e : (params43.toSetting T).T = T := rfl
    rw [e, ← ell1_eq_ell1q T]
    rw [show T * ell1 T / (2 * π) = T / (2 * π) * ell1 T by ring] at hRv
    exact hRv)
  have hc₀ : 0 ≤ 2 * Real.log 2 - 1 := by have := Real.log_two_gt_d9; linarith only [this]
  have hMlow : T * Real.log T / (4 * π) ≤ T * ell1 T / (2 * π) := by
    have h1 : Real.log T ≤ 2 * ell1 T := by unfold ell1; linarith only [hlo, hc₀]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ T * (2 * π))
    nlinarith only [this, hT0, hπ]
  have hCRlog : |CR| * Real.log T ≤ T * Real.log T / (8 * π) := by
    rw [le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_right hTCR (by linarith only [hlog1] : (0 : ℝ) ≤ Real.log T)
    linarith only [this]
  have hNlow : T * Real.log T / (8 * π) ≤ N := by
    have h1 := (abs_le.mp hRv).1
    have e : T * Real.log T / (4 * π) = 2 * (T * Real.log T / (8 * π)) := by ring
    linarith only [h1, hMlow, hCRlog, e]
  set U := T * Real.log T / (8 * π) with hU
  have hTU : ε' / (256 * π) * T ≤ ε' / 32 * U := by
    rw [hU]
    have : ε' / (256 * π) * T * 1 ≤ ε' / (256 * π) * T * Real.log T :=
      mul_le_mul_of_nonneg_left hlog1 (by positivity)
    have e : ε' / 32 * (T * Real.log T / (8 * π)) = ε' / (256 * π) * T * Real.log T := by
      field_simp; ring
    linarith only [this, e]
  have hW : Kpow * (Real.log T ^ 6 * v ^ 11) ≤ ε' / 32 * U := by
    rw [hv11]
    linarith only [hrate, hTU, show Kpow * (Real.log T ^ 6 * T ^ (11 / 12 : ℝ))
      = Kpow * Real.log T ^ 6 * T ^ (11 / 12 : ℝ) by ring]
  have hlin : Klin * T ≤ ε' / 32 * U := by
    rw [hU]
    rw [div_le_iff₀ hε'0] at hlK
    have e : ε' / 32 * (T * Real.log T / (8 * π)) = T * (ε' * Real.log T) / (256 * π) := by
      field_simp; ring
    rw [e, le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hlK hT0.le
    nlinarith only [this]
  have hCRb : Kc * (|CR| * Real.log T) ≤ ε' / 32 * U := by
    rw [hU]
    rw [div_le_iff₀ hε'0] at hTKc
    have e : ε' / 32 * (T * Real.log T / (8 * π)) = (ε' * T) * Real.log T / (256 * π) := by
      field_simp; ring
    rw [e, le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_right hTKc (by linarith only [hlog1] : (0 : ℝ) ≤ Real.log T)
    nlinarith only [this]
  have hNIIb : 3 * (NII zetaZeroConfig T : ℝ) ≤ ε' / 32 * U := by
    have h1 : (NII zetaZeroConfig T : ℝ) ≤ |CN| * Real.sqrt T * Real.log T := by
      refine hNIIT.trans ?_
      have hsT := Real.sqrt_nonneg T
      calc CN * Real.sqrt T * Zeta23.l T ≤ |CN| * Real.sqrt T * Zeta23.l T :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hsT)
              (by linarith only [hl1])
        _ ≤ |CN| * Real.sqrt T * Real.log T :=
            mul_le_mul_of_nonneg_left hhi (mul_nonneg (abs_nonneg _) hsT)
    have h2 : 3 * |CN| * Real.sqrt T ≤ ε' / (256 * π) * T := by
      rw [Real.sqrt_eq_rpow]; simpa using hrate2
    have h3 := mul_le_mul_of_nonneg_right h2 (by linarith only [hlog1] : (0 : ℝ) ≤ Real.log T)
    have e : ε' / 32 * U = ε' / (256 * π) * T * Real.log T := by rw [hU]; field_simp; ring
    nlinarith only [h1, h3, e]
  have hC1T : params43.C1 T ≤ 2 * R := by rw [hRdef]; exact C1_le_fam hP hwL
  have hθ := theta0_le_fam hP (show Tail.T₀ ≤ T by show (300 : ℝ) ≤ T; linarith only [hT4096])
    (by linarith only [hA₀]) (Tail.C1_nonneg _ T) hC1T
  have hθ1 : Tail.theta0 A₀ (Real.exp (params43.L T / 4) * params43.C1 T) T ≤ 1 := by
    have hlam : params43.lam / 2 - 1 = (4 / 3 : ℝ) / 2 - 1 := rfl
    rw [hlam] at hθ
    have hT13 : 0 ≤ T ^ ((4 / 3 : ℝ) / 2 - 1) := by positivity
    have h2 : 32 * A₀ * R ^ 2 * Zeta23.l T * T ^ ((4 / 3 : ℝ) / 2 - 1)
        ≤ 32 * A₀ * R ^ 2 * Real.log T * T ^ ((4 / 3 : ℝ) / 2 - 1) := by
      apply mul_le_mul_of_nonneg_right _ hT13
      exact mul_le_mul_of_nonneg_left hhi (by have := zero_le_one.trans hA₀; positivity)
    simp only [pow_one] at hrate3
    linarith only [hθ, h2, hrate3]
  have ha2 : 1 / 2 ≤ params43.a T := hF.b_ge_half.trans hF.b_le_a
  have haL : 4 ≤ params43.a T * params43.L T := by nlinarith only [ha2, hL8]
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = Tail.theta0 A₀ (Real.exp (params43.L T / 4) * params43.C1 T) T /
      (params43.a T * params43.L T) := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    have ha0 : 0 < params43.a T := by linarith only [ha2]
    have Htail : Tail.TailHyp zetaZeroConfig params43 T A₀ (params43.C1 T) :=
      { hT := show (300 : ℝ) ≤ T by linarith only [hT4096], hL := by linarith only [hL8],
        hA₀ := hA₀, hloc := hloc, hC₁ := Tail.C1_nonneg _ T,
        hdecay := fun r y hy hz => norm_phiHat_sub_I_mul_le_fam hP hwL r y hy hz }
    exact div_nonneg (Htail.tailInputs ha0 (fun z => Params.phiHat_conj z)).theta_nonneg
      (by positivity)
  have hB1 : B ≤ 1 := by rw [hBdef, div_le_one (by positivity)]; linarith only [hθ1, haL]
  have hNbig : 1024 / ε' ^ 2 + 40 / ε' ≤ N := by
    have h1 : 1024 / ε' ^ 2 + 40 / ε' ≤ T / (8 * π) := by
      rw [le_div_iff₀ (by positivity)]; linarith only [hTN]
    have h2 : T / (8 * π) ≤ U := by
      rw [hU, div_le_div_iff₀ (by positivity) (by positivity)]
      have := mul_le_mul_of_nonneg_left hlog1 (by positivity : (0 : ℝ) ≤ T * (8 * π))
      nlinarith only [this]
    linarith only [h1, h2, hNlow]
  have hN0 : 0 ≤ N := by
    have : 0 ≤ 1024 / ε' ^ 2 + 40 / ε' := by positivity
    linarith only [this, hNbig]
  have hBb : B * (4 + 4 * Real.sqrt N + B) ≤ ε / 4 * N := by
    have h1 : B * (4 + 4 * Real.sqrt N + B) ≤ 1 * (4 + 4 * Real.sqrt N + 1) :=
      mul_le_mul hB1 (by linarith only [hB1]) (by positivity) zero_le_one
    have hN40 : 40 / ε' ≤ N := by
      have : 0 ≤ 1024 / ε' ^ 2 := by positivity
      linarith only [this, hNbig]
    have hN1024 : 1024 / ε' ^ 2 ≤ N := by
      have : 0 ≤ 40 / ε' := by positivity
      linarith only [this, hNbig]
    have h5 : 5 ≤ ε' / 8 * N := by rw [div_le_iff₀ hε'0] at hN40; nlinarith only [hN40]
    have h6 : 4 * Real.sqrt N ≤ ε' / 8 * N := by
      have hsN : 32 / ε' ≤ Real.sqrt N := by
        rw [Real.le_sqrt (by positivity) hN0]
        have e : (32 / ε') ^ 2 = 1024 / ε' ^ 2 := by field_simp; norm_num
        rw [e]; exact hN1024
      have hsN0 := Real.sqrt_nonneg N
      have hNsq : N = Real.sqrt N * Real.sqrt N := (Real.mul_self_sqrt hN0).symm
      rw [div_le_iff₀ hε'0] at hsN
      nlinarith only [hsN, hNsq, hsN0, hε'0]
    have h7 : ε' / 4 * N ≤ ε / 4 * N := mul_le_mul_of_nonneg_right (by linarith only [hε'ε]) hN0
    linarith only [h1, h5, h6, h7]
  have hcoef : 43 / 36 + ε' / 2 + 32 * π * ε₁ ≤ Kc := by rw [hKc]; linarith only [hε'1]
  have hCRlog0 : 0 ≤ |CR| * Real.log T := by have := abs_nonneg CR; nlinarith only [this, hlog1]
  have hcoefb : (43 / 36 + ε' / 2 + 32 * π * ε₁) * (|CR| * Real.log T) ≤ Kc * (|CR| * Real.log T) :=
    mul_le_mul_of_nonneg_right hcoef hCRlog0
  have hUN : ε' / 32 * U ≤ ε' / 32 * N := mul_le_mul_of_nonneg_left hNlow (by positivity)
  have hε'N : ε' / 8 * N ≤ ε / 4 * N :=
    mul_le_mul_of_nonneg_right (by linarith only [hε'ε, hε]) hN0
  have hN10 : ε' / 32 * N ≤ N / 32 := by
    have := mul_le_mul_of_nonneg_right hε'1 hN0; linarith only [this]
  have hKpowW : Kpow * (Real.log T ^ 6 * v ^ 11)
      = 4 * (traceConst cr Kq Ct * Real.log T ^ 6 * v ^ 11)
        + (chanConst cr ℓ₀ K |C1| |Cψ| Mk + gridConst cr ℓ₀ ε₁ C₀ |C1| |Cψ|) * Real.log T ^ 6 * v ^ 11 := by
    rw [hKpow]; ring
  have hKlinT : Klin * T = 4 * ((6 * (1 + 2 * ℓ₀) + 4) * T) + (|CΓ| + 2 * |C2|) * T := by
    rw [hKlin]; ring
  have hE : 4 * ((6 * (1 + 2 * ℓ₀) + 4) * T + traceConst params43.crho Kq Ct * Real.log T ^ 6 * v ^ 11)
        + ((|CΓ| + 2 * |C2|) * T
          + (chanConst params43.crho ℓ₀ K |C1| |Cψ| Mk + gridConst params43.crho ℓ₀ ε₁ C₀ |C1| |Cψ|)
            * Real.log T ^ 6 * v ^ 11)
        + (43 / 36 + ε' / 2 + 32 * π * ε₁) * (|CR| * Real.log T) + 3 * (NII zetaZeroConfig T : ℝ)
      ≤ ε / 4 * N := by
    linarith only [hKpowW, hKlinT, hW, hlin, hcoefb, hCRb, hNIIb, hUN, hε'N]
  have hEf : (|CΓ| + 2 * |C2|) * T
        + (chanConst params43.crho ℓ₀ K |C1| |Cψ| Mk + gridConst params43.crho ℓ₀ ε₁ C₀ |C1| |Cψ|)
          * Real.log T ^ 6 * v ^ 11 ≤ N / 10 := by
    have h4 : 0 ≤ 4 * ((6 * (1 + 2 * ℓ₀) + 4) * T) := by positivity
    have h5 : 0 ≤ 4 * (traceConst cr Kq Ct * Real.log T ^ 6 * v ^ 11) := by
      have : 0 ≤ traceConst cr Kq Ct := by unfold traceConst; positivity
      have : 0 ≤ Real.log T := by linarith only [hlog1]
      positivity
    linarith only [hKpowW, hKlinT, hW, hlin, hUN, hN10, h4, h5, hN0]
  have hE₀ : |CR| * Real.log T ≤ N / 10 := by
    have : |CR| * Real.log T ≤ Kc * (|CR| * Real.log T) := le_mul_of_one_le_left hCRlog0 hKc1
    linarith only [this, hCRb, hUN, hN10, hN0]
  have hN₀_pos : 0 ≤ (zetaZeroConfig.N0s T (2 * T) : ℝ) -
      (RHTower.offLineMultipleMass zetaZeroConfig T (2 * T) : ℝ) := by
    have hp := hTpos T hTposT
    have hNc0 : 0 ≤ (Ncount T (2 * T) : ℝ) := Nat.cast_nonneg _
    rw [zetaZeroConfig_N0s]
    linarith
  have hcert := certificate_at_simple_and_offLineMultiple hF
    (show Tail.T₀ ≤ T by show (300 : ℝ) ≤ T; linarith only [hT4096]) hwL hA₀
    hloc hu hℓ₀ hlip hℓ1 hε₁T hK0 hK hKq0 hKq hμl' (by linarith only [hC₀1]) hμ hν (abs_nonneg C1)
    (abs_nonneg Cψ) hMk0 hMk hk2 hηk hv2 hvT hlog1 hhi hL hLc hsX hA hψ' hS hε'0 hε'1 hε'ε hl14
    hΓ hC2 ha hCt htr hRv (abs_nonneg CR) (η := η) (hE := hE) (hB := by rw [← hBdef]; exact hBb)
    hEf hE₀ hN₀_pos
  rw [zetaZeroConfig_N, zetaZeroConfig_N0s] at hcert
  linarith

/-- **Unconditional Simple-Critical & Off-Line-Multiple Coalescent Certificate at Bandwidth `4/3`:**
For every `η > 0` and `ε > 0`, there exists a smooth window profile `u` such that for all large `T`,
`(29/36 - ε) N(T, 2T) - coalescentSurplus u η T + M_off(T, 2T) ≤ N₀ˢ(T, 2T)`. -/
theorem zeta_coalescent_certificate_simple_and_offLineMultiple
    {η : ℝ} (hη : 0 < η) {ε : ℝ} (hε : 0 < ε) :
    ∃ (u : ℝ → ℝ) (ε₁ : ℝ), WindowProfile ε₁ u ∧ ∀ᶠ T in atTop,
      (29 / 36 - ε) * (Ncount T (2 * T) : ℝ) - coalescentSurplus u η T +
        (RHTower.offLineMultipleMass zetaZeroConfig T (2 * T) : ℝ) ≤
        (N0simple T (2 * T) : ℝ) := by
  have hπ := Real.pi_pos
  set ε₁ := min (ε / (64 * π)) (1 / 8)
  have h0 : 0 < ε₁ := lt_min (by positivity) (by norm_num)
  have h1 : ε₁ ≤ 1 / 8 := min_le_right _ _
  obtain ⟨u, hu⟩ := exists_windowProfile h0 h1
  refine ⟨u, ε₁, hu, ?_⟩
  filter_upwards [zeta_coalescent_certificate_four_thirds_simple_and_offLineMultiple hu hη
    (by positivity : (0 : ℝ) < ε / 2)] with T hT
  have hN : (0 : ℝ) ≤ (Ncount T (2 * T) : ℝ) := Nat.cast_nonneg _
  have h2 : 32 * π * ε₁ ≤ ε / 2 := by
    have : ε₁ ≤ ε / (64 * π) := min_le_left _ _
    have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 32 * π)
    have e : 32 * π * (ε / (64 * π)) = ε / 2 := by field_simp; ring
    linarith
  have h3 : (29 / 36 - ε) * (Ncount T (2 * T) : ℝ) ≤
      (29 / 36 - 32 * π * ε₁ - ε / 2) * (Ncount T (2 * T) : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith) hN
  linarith

/-- **Unconditional Pure-Prime Simple-Critical & Off-Line-Multiple Coalescent Certificate
(`0 < η < 1/3`):**
Eliminating proper prime powers via `eventually_abs_coalescentSurplus_sub_primeCoalescentSurplus_le_mul_Ncount`
yields for every `0 < η < 1/3` and `ε > 0` a smooth window profile `u` such that for all large `T`,
`(29/36 - ε) N(T, 2T) - primeCoalescentSurplus u η T + M_off(T, 2T) ≤ N₀ˢ(T, 2T)`. -/
theorem zeta_primeCoalescent_certificate_simple_and_offLineMultiple
    {η : ℝ} (hη0 : 0 < η) (hη3 : η < 1 / 3) {ε : ℝ} (hε : 0 < ε) :
    ∃ (u : ℝ → ℝ) (ε₁ : ℝ), WindowProfile ε₁ u ∧ ∀ᶠ T in atTop,
      (29 / 36 - ε) * (Ncount T (2 * T) : ℝ) - primeCoalescentSurplus u η T +
        (RHTower.offLineMultipleMass zetaZeroConfig T (2 * T) : ℝ) ≤
        (N0simple T (2 * T) : ℝ) := by
  obtain ⟨u, ε₁, hu, hcert⟩ := zeta_coalescent_certificate_simple_and_offLineMultiple hη0
    (by positivity : (0 : ℝ) < ε / 2)
  refine ⟨u, ε₁, hu, ?_⟩
  have htend : Tendsto (fun T : ℝ => 1024 * Real.sqrt 2 * T ^ (-1 / 3 + η)) atTop (𝓝 0) := by
    have hr := tendsto_rpow_neg_atTop (by linarith : 0 < -(-1 / 3 + η))
      |>.congr' (Eventually.of_forall fun T => by rw [neg_neg])
    simpa using hr.const_mul (1024 * Real.sqrt 2)
  filter_upwards [hcert,
    eventually_abs_coalescentSurplus_sub_primeCoalescentSurplus_le_mul_Ncount hu
      (by linarith : η < 1),
    htend.eventually (Iic_mem_nhds (by positivity : (0 : ℝ) < ε / 2))] with T hT hdiff hsmall
  have hN0 : 0 ≤ (Ncount T (2 * T) : ℝ) := Nat.cast_nonneg _
  have hsmall' : 1024 * Real.sqrt 2 * T ^ (-1 / 3 + η) ≤ ε / 2 := hsmall
  have hcs_le : coalescentSurplus u η T - primeCoalescentSurplus u η T ≤
      (ε / 2) * (Ncount T (2 * T) : ℝ) :=
    (le_abs_self _).trans (hdiff.trans (mul_le_mul_of_nonneg_right hsmall' hN0))
  linarith

/-- **Unconditional Off-Line Simple + Twice Off-Line Multiple Ceiling via `primeCoalescentSurplus`:**
Combining `zeta_primeCoalescent_certificate_simple_and_offLineMultiple` with the exact window census
`N = N₀ + S_off + M_off` and `N₀ˢ ≤ N₀` proves unconditionally that for every `0 < η < 1/3` and
`ε > 0`, there exists a smooth window profile `u` such that for all large `T`,
`S_off(T, 2T) + 2 M_off(T, 2T) ≤ (7/36 + ε) N(T, 2T) + primeCoalescentSurplus u η T`. -/
theorem offLineSimple_add_two_offLineMultiple_le_seven_thirtySixths_add_primeCoalescentSurplus
    {η : ℝ} (hη0 : 0 < η) (hη3 : η < 1 / 3) {ε : ℝ} (hε : 0 < ε) :
    ∃ (u : ℝ → ℝ) (ε₁ : ℝ), WindowProfile ε₁ u ∧ ∀ᶠ T in atTop,
      (RHTower.offLineSimpleCount zetaZeroConfig T (2 * T) : ℝ) +
        2 * (RHTower.offLineMultipleMass zetaZeroConfig T (2 * T) : ℝ) ≤
        (7 / 36 + ε) * (Ncount T (2 * T) : ℝ) + primeCoalescentSurplus u η T := by
  obtain ⟨u, ε₁, hu, hcert⟩ :=
    zeta_primeCoalescent_certificate_simple_and_offLineMultiple hη0 hη3 hε
  refine ⟨u, ε₁, hu, ?_⟩
  filter_upwards [hcert] with T hT
  have hN := RHTower.zeta_N_eq_N0_add_offLineSimple_add_offLineMultiple T (2 * T)
  have hs : (N0simple T (2 * T) : ℝ) ≤ (N0 T (2 * T) : ℝ) := by
    exact_mod_cast RHTower.zeta_N0simple_le_N0 T (2 * T)
  linarith

end WeightedMultSeam

end GaloisForLFunctions.TransThresholdPairCorrelation
