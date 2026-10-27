import GaloisForLFunctions.TransThresholdPairCorrelation.CoalescentPrimeReductionAndParitySieve
import GaloisForLFunctions.TransThresholdPairCorrelation.RamanujanDirichletCoalescentTransfer
import GaloisForLFunctions.RHTower.ZetaThreeQuartersReduction

/-!
# Parity-Sensitive Ramanujan Stabilizer Transfer on Even Coalescent Shifts

For coalescent aperture `θ₀ < 1 / 3`, `primeCoalSum` collapses identically to the odd-prime
even-shift sum `oddEvenShiftPrimeCoalSum`, in which every lag `|p - q| = 2r` is strictly even.
On unrestricted integer shifts, `RamanujanDirichletCoalescentTransfer` established Ward–Mertens
transfer for individual moduli `q ≥ 2` via `∑_{d ∣ q} μ(q / d) = 0`. Restricting to even shifts
`h = 2r` transforms the Hardy–Littlewood singular series in four exact ways proved unconditionally
in this module:

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

4. **Stabilizer-Centered Decomposition and Critical-Line Proportion Milestones
   (`oddEvenShiftPrimeCoalSum_eq_stabilizerModel_add_discrepancy`,
   `coalescent_stabilizer_proportion_milestones`):**
   Decomposes `oddEvenShiftPrimeCoalSum` around any parity-sensitive `Q`-modulus Ramanujan
   stabilizer model into its singular-series baseline plus centered discrepancy, and proves the
   unconditional critical-line simple-zero proportion payoffs of `PrimeCoalescentSurplusAtMost β`
   at `β < 5/36` (`> 2/3`), `β ≤ 577/4500` (`≥ 254/375`), and `β ≤ 1/18` (`≥ 3/4` critical-line
   simple zeros).
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
      dsimp only
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
      simpa [u_fn, u'_fn] using hdΩ.div (hasDerivAt_id τ) hτ0
    have hv_deriv : ∀ τ ∈ Set.uIcc a b, HasDerivAt v_fn (v'_fn τ) τ := by
      intro τ _
      have h1 : HasDerivAt (fun x : ℝ => (2 * (R : ℝ) / m) * x) (2 * (R : ℝ) / m) τ := by
        simpa using (hasDerivAt_id τ).const_mul (2 * (R : ℝ) / m)
      refine (h1.cos.const_mul (-(m / (2 * (R : ℝ))))).congr_deriv ?_
      dsimp [v'_fn]
      have hR0 : (R : ℝ) ≠ 0 := hR_pos.ne'
      field_simp [hm.ne', hR0]
      ring
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
          ring

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
          ring
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

/-! ## §4. Stabilizer-Centered Decomposition of `oddEvenShiftPrimeCoalSum` & Proportion Milestones -/

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
`oddEvenShiftPrimeCoalSum` by `parityStabilizerWeight Q (Nat.dist n m) / √(n * m)` (with factor
`1 / 4` matching the odd-integer density `(1 / 2)²` whose product with `2` reproduces `1 / 2`). -/
def stabilizerModelOddCoalSum (Q : ℕ) (Ω g : ℝ → ℝ) (X θ₀ : ℝ) : ℝ :=
  (1 / π) * ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
    if 3 ≤ n ∧ 3 ≤ m ∧ n % 2 = 1 ∧ m % 2 = 1 ∧ n ≠ m ∧ |Real.log n - Real.log m| ≤ θ₀
    then ((1 / 4 : ℝ) * parityStabilizerWeight Q (Nat.dist n m) /
        (Real.sqrt n * Real.sqrt m)) * g (Real.log m) * cosTransform Ω (Real.log n - Real.log m)
    else 0

/-- The centered stabilizer discrepancy of `oddEvenShiftPrimeCoalSum` relative to the `Q`-modulus
parity-locked Ramanujan model on coalescent odd integer pairs `3 ≤ n, m ≤ X`. -/
def stabilizerDiscrepancyOddCoalSum (Q : ℕ) (Ω g : ℝ → ℝ) (X θ₀ : ℝ) : ℝ :=
  (1 / π) * ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
    if 3 ≤ n ∧ 3 ≤ m ∧ n % 2 = 1 ∧ m % 2 = 1 ∧ n ≠ m ∧ |Real.log n - Real.log m| ≤ θ₀
    then ((if n.Prime ∧ m.Prime then acoef n * acoef m else 0) -
        (1 / 4 : ℝ) * parityStabilizerWeight Q (Nat.dist n m) /
          (Real.sqrt n * Real.sqrt m)) * g (Real.log m) * cosTransform Ω (Real.log n - Real.log m)
    else 0

/-- **Exact Stabilizer-Centered Decomposition of `oddEvenShiftPrimeCoalSum`.**
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

/-- **Milestone 1 Critical-Line Simple-Zero Proportion Package (`4/3` Coalescent Thresholds).**
Unconditionally packages the three critical-line simple-zero proportion thresholds certified by
`PrimeCoalescentSurplusAtMost β` at bandwidth `λ = 4/3`:
1. **First Blood (`β < 5 / 36`):** `N₀*(T, 2T) ≥ (2 / 3 + (5 / 36 - β) / 2) N(T, 2T)` eventually,
   strictly breaking the `2 / 3` threshold by `(5 / 36 - β) / 2 > 0`;
2. **Surpassing `HD(1)` (`β ≤ 577 / 4500`):** `N₀*(T, 2T) ≥ (254 / 375 - ε) N(T, 2T)` eventually
   (`254 / 375 = 0.67733... > 0.67727...`);
3. **Three-Quarters Simple Critical-Line Zeros (`β ≤ 1 / 18`):** `N₀*(T, 2T) ≥ (3 / 4 - ε) N(T, 2T)`
   eventually — at least `3 / 4` of nontrivial zeros in `[T, 2T]` are simple and lie on `Re s = 1/2`. -/
theorem coalescent_stabilizer_proportion_milestones :
    (∀ {β : ℝ}, β < 5 / 36 → PrimeCoalescentSurplusAtMost β →
      0 < (5 / 36 - β) / 2 ∧
      ∀ᶠ T in atTop,
        (2 / 3 + (5 / 36 - β) / 2) * (Ncount T (2 * T) : ℝ) ≤ (N0star T (2 * T) : ℝ)) ∧
    (∀ {β : ℝ}, β ≤ 577 / 4500 → PrimeCoalescentSurplusAtMost β →
      ∀ ε > 0, ∀ᶠ T in atTop,
        (254 / 375 - ε) * (Ncount T (2 * T) : ℝ) ≤ (N0star T (2 * T) : ℝ)) ∧
    (∀ {β : ℝ}, β ≤ 1 / 18 → PrimeCoalescentSurplusAtMost β →
      ∀ ε > 0, ∀ᶠ T in atTop,
        (3 / 4 - ε) * (Ncount T (2 * T) : ℝ) ≤ (N0star T (2 * T) : ℝ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro β hβ hP
    have hpos : 0 < (5 / 36 - β) / 2 := by linarith
    refine ⟨hpos, ?_⟩
    obtain ⟨η, u, ε₁, _, _, _, hev⟩ := hP ((5 / 36 - β) / 4) (by linarith)
    filter_upwards [hev] with T ⟨hcert, hsurp⟩
    linarith
  · intro β hβ hP ε hε
    obtain ⟨η, u, ε₁, _, _, _, hev⟩ := hP (ε / 2) (by linarith)
    filter_upwards [hev] with T ⟨hcert, hsurp⟩
    have hN0 : 0 ≤ (Ncount T (2 * T) : ℝ) := Nat.cast_nonneg _
    have hle : (254 / 375 - ε) * (Ncount T (2 * T) : ℝ) ≤
        (29 / 36 - β - ε) * (Ncount T (2 * T) : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith) hN0
    have hcomb : (29 / 36 - β - ε) * (Ncount T (2 * T) : ℝ) =
        (29 / 36 - ε / 2) * (Ncount T (2 * T) : ℝ) -
          (β + ε / 2) * (Ncount T (2 * T) : ℝ) := by ring
    linarith
  · intro β hβ hP ε hε
    obtain ⟨η, u, ε₁, _, _, _, hev⟩ := hP (ε / 2) (by linarith)
    filter_upwards [hev] with T ⟨hcert, hsurp⟩
    have hN0 : 0 ≤ (Ncount T (2 * T) : ℝ) := Nat.cast_nonneg _
    have hle : (3 / 4 - ε) * (Ncount T (2 * T) : ℝ) ≤
        (29 / 36 - β - ε) * (Ncount T (2 * T) : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith) hN0
    have hcomb : (29 / 36 - β - ε) * (Ncount T (2 * T) : ℝ) =
        (29 / 36 - ε / 2) * (Ncount T (2 * T) : ℝ) -
          (β + ε / 2) * (Ncount T (2 * T) : ℝ) := by ring
    linarith

end GaloisForLFunctions.TransThresholdPairCorrelation
