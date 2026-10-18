import GaloisForLFunctions.BezoutValuationIncidence.ExactFinitePrefixDiscrepancyDualityAndReturnTimes
import GaloisForLFunctions.BezoutValuationIncidence.ArithmeticLagSchedulesAndSharpRecoveryHorizon
import GaloisForLFunctions.BezoutValuationIncidence.PostStepInactiveEnergyAndPronicGradientConservation
import GaloisForLFunctions.RHTower.PMPairedRamanujanGram

/-!
# Short-Horizon Pronic Discrepancy Energy and Von Mangoldt Duality (Period-Free Calculus)

A central structural question for finite divisor sieves is how the finite-prefix discrepancy
`sievePrefixDiscrepancy N M c = ∑_{k=1}^M sieveSeq N c k - M * finiteHarmonicSum N c`
behaves on short intervals `M ∈ [1, H]` (such as the sharp observability horizon `H = N - 1`) and
under the non-periodic Bézout pronic measure `1 / pronicSeq M = 1 / (M * (M + 1))`, **without**
embedding into the artificial full period `N!`.

Because each dual Ramanujan primitive `pmRamanujanPrimitive e M` is periodic with its own individual
modulus `e ≤ N` (rather than `N!`), this module establishes a completely period-free short-horizon
and pronic-weighted discrepancy calculus:

1. **The Pronic-Weighted Discrepancy Von Mangoldt Duality Theorem
   (`hasSum_sievePrefixDiscrepancy_div_pronicSeq`, `tsum_sievePrefixDiscrepancy_div_pronicSeq`,
   `tsum_sievePrefixDiscrepancy_mode_probe_div_pronicSeq`):**
   Integrating `sievePrefixDiscrepancy N M c` against the Bézout pronic weight `1 / pronicSeq M`
   over all natural horizons `M ≥ 1` transforms the Selberg multiples coordinates
   `selbergMultiplesCoord N c e` into the **von Mangoldt prime-power functional**:
   $$\sum_{M=1}^\infty \frac{\operatorname{sievePrefixDiscrepancy}\,N\,M\,c}{\operatorname{pronicSeq}\,M}
     = -\sum_{e=2}^N \Lambda(e)\,\operatorname{selbergMultiplesCoord}\,N\,c\,e.$$
   In particular, for a pure Selberg mode `sieveModeWeight N q` (`2 ≤ q ≤ N`), the pronic
   discrepancy series equals `-vonMangoldt q`, which vanishes identically at every composite
   non-prime-power mode `q` (such as `q = 6`) and equals `-log p` at every prime power `q = p^a`.

2. **Period-Free Uniform Dual-Energy Ceiling & Short-Horizon `L²` Discrepancy Bounds
   (`pmRamanujanPrimitive_re_prime_sq_div_totient_le`,
   `sievePrefixDualEnergy_le_periodFreeDualCeiling`,
   `sum_Icc_sievePrefixDiscrepancy_sq_le`,
   `sum_Icc_sievePrefixDiscrepancy_sq_div_pronicSeq_le`):**
   - At every prime mode `p` and every horizon `M`, `(pmRamanujanPrimitive p M).re = -(M % p)` and
     `(pmRamanujanPrimitive p M).re ^ 2 / φ(p) ≤ φ(p) = p - 1`.
   - For every level `N` and every horizon `M`, `sievePrefixDualEnergy N M` is bounded uniformly in
     `M` (with no reference to `N!`) by `sievePeriodFreeDualCeiling N`.
   - Over any short horizon `H` (e.g., `H = N - 1`), the cumulative squared discrepancy is bounded
     by `H * sieveVariance N c * sievePeriodFreeDualCeiling N`, and the pronic-weighted squared
     discrepancy sum over `1 ≤ M ≤ H` is bounded uniformly for all `H` by
     `(1 - 1 / (H + 1)) * sieveVariance N c * sievePeriodFreeDualCeiling N`.

3. **Exact Non-Periodic Pronic Discrepancy Gram Quadratic Form
   (`hasSum_sievePrefixDiscrepancy_sq_div_pronicSeq`, `tsum_sievePrefixDiscrepancy_sq_div_pronicSeq`):**
   For every cutoff `N` and every sieve weight `c`, the infinite-horizon pronic-weighted squared
   discrepancy series converges unconditionally to the quadratic form defined by the non-periodic
   Ramanujan Gram matrix `pmRamanujanPrimitiveGram p q` on the Selberg coordinates `Y_N(c, e)`.
-/

open Complex MeasureTheory Set Filter Topology Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Pronic-Weighted Discrepancy Von Mangoldt Duality -/

/-- Real cast of `pronicSeq M` as `(M : ℝ) * ((M : ℝ) + 1)`. -/
theorem cast_pronicSeq_eq (M : ℕ) :
    (pronicSeq M : ℝ) = (M : ℝ) * ((M : ℝ) + 1) := by
  unfold pronicSeq
  push_cast
  ring

/-- **The Pronic-Weighted Discrepancy Von Mangoldt Duality Theorem
(`hasSum_sievePrefixDiscrepancy_div_pronicSeq`):**
For every cutoff `N : ℕ` and every sieve weight `c : ℕ → ℝ`, the pronic-weighted discrepancy series
`M ↦ sievePrefixDiscrepancy N M c / pronicSeq M` is unconditionally summable on `ℕ` with exact sum
`-∑_{e ∈ Icc 2 N} vonMangoldt e * selbergMultiplesCoord N c e`. -/
theorem hasSum_sievePrefixDiscrepancy_div_pronicSeq (N : ℕ) (c : ℕ → ℝ) :
    HasSum (fun M : ℕ => sievePrefixDiscrepancy N M c / (pronicSeq M : ℝ))
      (-∑ e ∈ Finset.Icc 2 N, vonMangoldt e * selbergMultiplesCoord N c e) := by
  have hsum : HasSum
      (fun M : ℕ => ∑ e ∈ Finset.Icc 2 N,
        ((pmRamanujanPrimitive e M).re / ((M : ℝ) * ((M : ℝ) + 1))) *
          selbergMultiplesCoord N c e)
      (∑ e ∈ Finset.Icc 2 N, (-vonMangoldt e) * selbergMultiplesCoord N c e) := by
    apply hasSum_sum
    intro e he
    have he1 : 1 < e := by have := (Finset.mem_Icc.mp he).1; omega
    exact (hasSum_pmRamanujanPrimitive_reciprocal he1).mul_right (selbergMultiplesCoord N c e)
  simp_rw [neg_mul] at hsum
  rw [Finset.sum_neg_distrib] at hsum
  refine hsum.congr_fun ?_
  intro M
  rw [cast_pronicSeq_eq M, sievePrefixDiscrepancy_eq_ramanujan_diagonal N M c, Finset.sum_div]
  refine Finset.sum_congr rfl fun e _ => ?_
  ring

/-- **Infinite Series Formula for the Pronic-Weighted Discrepancy
(`tsum_sievePrefixDiscrepancy_div_pronicSeq`):**
For every `N : ℕ` and `c : ℕ → ℝ`:
`∑' M : ℕ, sievePrefixDiscrepancy N M c / pronicSeq M = -∑ e ∈ Icc 2 N, vonMangoldt e * selbergMultiplesCoord N c e`. -/
theorem tsum_sievePrefixDiscrepancy_div_pronicSeq (N : ℕ) (c : ℕ → ℝ) :
    (∑' M : ℕ, sievePrefixDiscrepancy N M c / (pronicSeq M : ℝ)) =
      -∑ e ∈ Finset.Icc 2 N, vonMangoldt e * selbergMultiplesCoord N c e :=
  (hasSum_sievePrefixDiscrepancy_div_pronicSeq N c).tsum_eq

/-- **Pure-Mode Pronic Discrepancy Evaluation (`tsum_sievePrefixDiscrepancy_mode_probe_div_pronicSeq`):**
For every cutoff `N : ℕ` and every mode `q ∈ Icc 2 N`, probing the pronic-weighted discrepancy
series with the pure Selberg mode `sieveModeWeight N q` extracts `-vonMangoldt q`. -/
theorem tsum_sievePrefixDiscrepancy_mode_probe_div_pronicSeq {N q : ℕ}
    (hq : q ∈ Finset.Icc 2 N) :
    (∑' M : ℕ, sievePrefixDiscrepancy N M (sieveModeWeight N q) / (pronicSeq M : ℝ)) =
      -vonMangoldt q := by
  rw [tsum_sievePrefixDiscrepancy_div_pronicSeq]
  have hsum :
      (∑ e ∈ Finset.Icc 2 N,
        vonMangoldt e * selbergMultiplesCoord N (sieveModeWeight N q) e) =
      vonMangoldt q := by
    calc
      _ = ∑ e ∈ Finset.Icc 2 N, if e = q then vonMangoldt e else 0 := by
        refine Finset.sum_congr rfl fun e he => ?_
        have heI : e ∈ Finset.Icc 1 N :=
          Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp he).1; omega, (Finset.mem_Icc.mp he).2⟩
        rw [sieveModeWeight, selbergMultiplesCoord_ramanujan_inverse, if_pos heI]
        split_ifs <;> ring
      _ = vonMangoldt q := by simp [hq]
  rw [hsum]

/-- **Composite Non-Prime-Power Cancellation in Pronic Discrepancy
(`tsum_sievePrefixDiscrepancy_mode_probe_eq_zero_of_not_isPrimePow`):**
For every composite non-prime-power mode `q ∈ Icc 2 N` (i.e. `¬ IsPrimePow q`, such as `q = 6`),
the pronic-weighted discrepancy series of `sieveModeWeight N q` vanishes identically. -/
theorem tsum_sievePrefixDiscrepancy_mode_probe_eq_zero_of_not_isPrimePow {N q : ℕ}
    (hq : q ∈ Finset.Icc 2 N) (hnp : ¬ IsPrimePow q) :
    (∑' M : ℕ, sievePrefixDiscrepancy N M (sieveModeWeight N q) / (pronicSeq M : ℝ)) = 0 := by
  rw [tsum_sievePrefixDiscrepancy_mode_probe_div_pronicSeq hq,
    ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hnp, neg_zero]

/-! ## §2. Period-Free Uniform Dual-Energy Ceiling & Short-Horizon `L²` Bounds -/

/-- **Prime-Mode Dual Energy Bound (`pmRamanujanPrimitive_re_prime_sq_div_totient_le`):**
For every prime `p` and every horizon `M : ℕ`, the single-mode dual energy contribution of `p` is
`((M % p : ℕ) : ℝ) ^ 2 / (p - 1)` and is bounded above by `φ(p) = p - 1`. -/
theorem pmRamanujanPrimitive_re_prime_sq_div_totient_le {p : ℕ}
    (hp : p.Prime) (M : ℕ) :
    (pmRamanujanPrimitive p M).re ^ (2 : ℕ) / (Nat.totient p : ℝ) ≤ (Nat.totient p : ℝ) := by
  have hre : (pmRamanujanPrimitive p M).re = -((M % p : ℕ) : ℝ) := by
    rw [pmRamanujanPrimitive_prime hp M]
    simp
  have hmod_lt : M % p < p := Nat.mod_lt M hp.pos
  have hmod_le : M % p ≤ p.totient := by
    rw [Nat.totient_prime hp]
    omega
  have hmodR : ((M % p : ℕ) : ℝ) ≤ (p.totient : ℝ) := by exact_mod_cast hmod_le
  have htot_pos : (0 : ℝ) < (p.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hp.pos
  rw [hre, neg_sq, div_le_iff₀ htot_pos, ← sq]
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) hmodR 2

/-- **The Period-Free Dual-Energy Ceiling (`sievePeriodFreeDualCeiling`):**
An explicit finite-level bound on `sievePrefixDualEnergy N M` depending only on the individual
moduli `2 ≤ e ≤ N` (and never on `M` or `N!`). -/
def sievePeriodFreeDualCeiling (N : ℕ) : ℝ :=
  ∑ e ∈ Finset.Icc 2 N, (pmRamanujanPrimitiveBound e) ^ (2 : ℕ) / (Nat.totient e : ℝ)

/-- `sievePeriodFreeDualCeiling N` is non-negative for every `N : ℕ`. -/
theorem sievePeriodFreeDualCeiling_nonneg (N : ℕ) :
    0 ≤ sievePeriodFreeDualCeiling N :=
  Finset.sum_nonneg fun _ _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

/-- **Uniform Period-Free Upper Bound on `sievePrefixDualEnergy N M`
(`sievePrefixDualEnergy_le_periodFreeDualCeiling`):**
For every level `N : ℕ` and every horizon `M : ℕ`,
`sievePrefixDualEnergy N M ≤ sievePeriodFreeDualCeiling N`. -/
theorem sievePrefixDualEnergy_le_periodFreeDualCeiling (N M : ℕ) :
    sievePrefixDualEnergy N M ≤ sievePeriodFreeDualCeiling N := by
  unfold sievePrefixDualEnergy sievePeriodFreeDualCeiling
  refine Finset.sum_le_sum fun e he => ?_
  have he1 : 1 < e := by have := (Finset.mem_Icc.mp he).1; omega
  have habs : |(pmRamanujanPrimitive e M).re| ≤ pmRamanujanPrimitiveBound e :=
    (Complex.abs_re_le_norm (pmRamanujanPrimitive e M)).trans (norm_pmRamanujanPrimitive_le he1 M)
  have hB0 : 0 ≤ pmRamanujanPrimitiveBound e :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hsq : (pmRamanujanPrimitive e M).re ^ (2 : ℕ) ≤ (pmRamanujanPrimitiveBound e) ^ (2 : ℕ) := by
    rw [← sq_abs (pmRamanujanPrimitive e M).re]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  exact div_le_div_of_nonneg_right hsq (Nat.cast_nonneg _)

/-- **Pointwise Period-Free Discrepancy Bound (`sievePrefixDiscrepancy_sq_le_periodFree`):**
For every `N, M : ℕ` and `c : ℕ → ℝ`,
`(sievePrefixDiscrepancy N M c) ^ 2 ≤ sieveVariance N c * sievePeriodFreeDualCeiling N`. -/
theorem sievePrefixDiscrepancy_sq_le_periodFree (N M : ℕ) (c : ℕ → ℝ) :
    (sievePrefixDiscrepancy N M c) ^ (2 : ℕ) ≤
      sieveVariance N c * sievePeriodFreeDualCeiling N := by
  have h1 := sievePrefixDiscrepancy_sq_le_variance_mul_dualEnergy N M c
  have h2 := sievePrefixDualEnergy_le_periodFreeDualCeiling N M
  have hv : 0 ≤ sieveVariance N c :=
    Finset.sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  exact h1.trans (mul_le_mul_of_nonneg_left h2 hv)

/-- **Short-Horizon Cumulative Squared Discrepancy Bound (`sum_Icc_sievePrefixDiscrepancy_sq_le`):**
For every cutoff `N : ℕ`, short horizon `H : ℕ` (such as `H = N - 1`), and sieve weight `c : ℕ → ℝ`:
`∑_{M=1}^H (sievePrefixDiscrepancy N M c)² ≤ H * sieveVariance N c * sievePeriodFreeDualCeiling N`. -/
theorem sum_Icc_sievePrefixDiscrepancy_sq_le (N H : ℕ) (c : ℕ → ℝ) :
    (∑ M ∈ Finset.Icc 1 H, (sievePrefixDiscrepancy N M c) ^ (2 : ℕ)) ≤
      (H : ℝ) * sieveVariance N c * sievePeriodFreeDualCeiling N := by
  calc
    (∑ M ∈ Finset.Icc 1 H, (sievePrefixDiscrepancy N M c) ^ (2 : ℕ))
      ≤ ∑ _M ∈ Finset.Icc 1 H, (sieveVariance N c * sievePeriodFreeDualCeiling N) :=
        Finset.sum_le_sum fun M _ => sievePrefixDiscrepancy_sq_le_periodFree N M c
    _ = (H : ℝ) * sieveVariance N c * sievePeriodFreeDualCeiling N := by
        simp [mul_assoc]

/-- **Horizon-Uniform Pronic-Weighted Squared Discrepancy Bound
(`sum_Icc_sievePrefixDiscrepancy_sq_div_pronicSeq_le`):**
For every cutoff `N : ℕ`, horizon `H ≥ 1`, and weight `c : ℕ → ℝ`, the pronic-weighted squared
discrepancy sum over `1 ≤ M ≤ H` is bounded above by
`(1 - 1 / (H + 1)) * sieveVariance N c * sievePeriodFreeDualCeiling N`. -/
theorem sum_Icc_sievePrefixDiscrepancy_sq_div_pronicSeq_le
    (N : ℕ) {H : ℕ} (hH : 1 ≤ H) (c : ℕ → ℝ) :
    (∑ M ∈ Finset.Icc 1 H,
      (sievePrefixDiscrepancy N M c) ^ (2 : ℕ) / (pronicSeq M : ℝ)) ≤
      (1 - 1 / ((H : ℝ) + 1)) * sieveVariance N c * sievePeriodFreeDualCeiling N := by
  calc
    (∑ M ∈ Finset.Icc 1 H,
      (sievePrefixDiscrepancy N M c) ^ (2 : ℕ) / (pronicSeq M : ℝ))
      ≤ ∑ M ∈ Finset.Icc 1 H,
          (sieveVariance N c * sievePeriodFreeDualCeiling N) * ((1 : ℝ) / (pronicSeq M : ℝ)) := by
        refine Finset.sum_le_sum fun M _ => ?_
        rw [← div_eq_mul_one_div]
        exact div_le_div_of_nonneg_right
          (sievePrefixDiscrepancy_sq_le_periodFree N M c) (Nat.cast_nonneg _)
    _ = (sieveVariance N c * sievePeriodFreeDualCeiling N) *
          ∑ M ∈ Finset.Icc 1 H, (1 : ℝ) / (pronicSeq M : ℝ) := by
        rw [← Finset.mul_sum]
    _ = (1 - 1 / ((H : ℝ) + 1)) * sieveVariance N c * sievePeriodFreeDualCeiling N := by
        rw [sum_one_div_pronicSeq_eq hH]
        ring

/-! ## §3. Exact Non-Periodic Pronic Discrepancy Gram Quadratic Form -/

/-- **The Non-Periodic Pronic Discrepancy Gram Quadratic Form (`sievePronicDiscrepancyGramForm`):**
The quadratic form on Selberg multiples coordinates `selbergMultiplesCoord N c` induced by the
non-periodic Ramanujan primitive Gram matrix `pmRamanujanPrimitiveGram p q`. -/
def sievePronicDiscrepancyGramForm (N : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ p ∈ Finset.Icc 2 N, ∑ q ∈ Finset.Icc 2 N,
    selbergMultiplesCoord N c p * selbergMultiplesCoord N c q *
      pmRamanujanPrimitiveGram p q

/-- **Pointwise Gram Expansion of Pronic-Weighted Squared Discrepancy
(`sievePrefixDiscrepancy_sq_div_pronicSeq_eq_gramTerm`):**
For every `N, M : ℕ` and `c : ℕ → ℝ`, `(sievePrefixDiscrepancy N M c)² / pronicSeq M` expands into
the bilinear sum of `pmRamanujanPrimitiveGramTerm p q M` over `p, q ∈ Icc 2 N`. -/
theorem sievePrefixDiscrepancy_sq_div_pronicSeq_eq_gramTerm
    (N M : ℕ) (c : ℕ → ℝ) :
    (sievePrefixDiscrepancy N M c) ^ (2 : ℕ) / (pronicSeq M : ℝ) =
      ∑ p ∈ Finset.Icc 2 N, ∑ q ∈ Finset.Icc 2 N,
        selbergMultiplesCoord N c p * selbergMultiplesCoord N c q *
          pmRamanujanPrimitiveGramTerm p q M := by
  rw [cast_pronicSeq_eq M, sievePrefixDiscrepancy_eq_ramanujan_diagonal N M c,
    sq, Finset.sum_mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun q _ => ?_
  unfold pmRamanujanPrimitiveGramTerm
  ring

/-- **Exact Infinite-Horizon Pronic Discrepancy Gram Identity
(`hasSum_sievePrefixDiscrepancy_sq_div_pronicSeq`):**
For every cutoff `N : ℕ` and every sieve weight `c : ℕ → ℝ`, the pronic-weighted squared
discrepancy series `M ↦ (sievePrefixDiscrepancy N M c)² / pronicSeq M` converges unconditionally
on `ℕ` to `sievePronicDiscrepancyGramForm N c`. -/
theorem hasSum_sievePrefixDiscrepancy_sq_div_pronicSeq (N : ℕ) (c : ℕ → ℝ) :
    HasSum (fun M : ℕ => (sievePrefixDiscrepancy N M c) ^ (2 : ℕ) / (pronicSeq M : ℝ))
      (sievePronicDiscrepancyGramForm N c) := by
  have hs : HasSum
      (fun M : ℕ => ∑ p ∈ Finset.Icc 2 N, ∑ q ∈ Finset.Icc 2 N,
        selbergMultiplesCoord N c p * selbergMultiplesCoord N c q *
          pmRamanujanPrimitiveGramTerm p q M)
      (sievePronicDiscrepancyGramForm N c) := by
    unfold sievePronicDiscrepancyGramForm
    apply hasSum_sum
    intro p hp
    apply hasSum_sum
    intro q hq
    have hp1 : 1 < p := by have := (Finset.mem_Icc.mp hp).1; omega
    have hq1 : 1 < q := by have := (Finset.mem_Icc.mp hq).1; omega
    exact (summable_pmRamanujanPrimitiveGramTerm hp1 hq1).hasSum.mul_left _
  exact hs.congr_fun fun M => sievePrefixDiscrepancy_sq_div_pronicSeq_eq_gramTerm N M c

/-- **Infinite Series Formula for the Pronic-Weighted Squared Discrepancy
(`tsum_sievePrefixDiscrepancy_sq_div_pronicSeq`):**
For every `N : ℕ` and `c : ℕ → ℝ`:
`∑' M : ℕ, (sievePrefixDiscrepancy N M c)² / pronicSeq M = sievePronicDiscrepancyGramForm N c`. -/
theorem tsum_sievePrefixDiscrepancy_sq_div_pronicSeq (N : ℕ) (c : ℕ → ℝ) :
    (∑' M : ℕ, (sievePrefixDiscrepancy N M c) ^ (2 : ℕ) / (pronicSeq M : ℝ)) =
      sievePronicDiscrepancyGramForm N c :=
  (hasSum_sievePrefixDiscrepancy_sq_div_pronicSeq N c).tsum_eq

/-- Symmetry of the non-periodic Ramanujan primitive Gram matrix `pmRamanujanPrimitiveGram`. -/
theorem pmRamanujanPrimitiveGram_symm (p q : ℕ) :
    pmRamanujanPrimitiveGram p q = pmRamanujanPrimitiveGram q p := by
  unfold pmRamanujanPrimitiveGram pmRamanujanPrimitiveGramTerm
  congr 1
  ext N
  ring

/-- **Prime-Dilated Diagonal Gram Recurrence (`pmRamanujanPrimitiveGram_prime_mul_diag`):**
For every prime `p` and modulus `q > 1` with `¬ p ∣ q`:
`pmRamanujanPrimitiveGram (p * q) (p * q) = (p - 1) * pmRamanujanPrimitiveGram q q - 2 * pmRamanujanPrimitiveGram (p * q) q`. -/
theorem pmRamanujanPrimitiveGram_prime_mul_diag {p q : ℕ}
    (hp : p.Prime) (hq : 1 < q) (hpq : ¬ p ∣ q) :
    pmRamanujanPrimitiveGram (p * q) (p * q) =
      ((p : ℝ) - 1) * pmRamanujanPrimitiveGram q q -
        2 * pmRamanujanPrimitiveGram (p * q) q := by
  have hpair := pmRamanujanPrimitiveGram_prime_pair hp hq hq hpq hpq
  have hsymm := pmRamanujanPrimitiveGram_symm q (p * q)
  linarith

/-- **Two-Mode Prime-Dilation Quadratic Decomposition
(`pmRamanujanPrimitiveGram_two_mode_dilation_identity`):**
For every prime `p`, modulus `q > 1` with `¬ p ∣ q`, and Selberg mode amplitudes `u, v : ℝ` on the
dilated pair `{q, p * q}`, the non-periodic Gram quadratic form decomposes into the variance-proportional
diagonal `(u² + (p - 1) * v²) * pmRamanujanPrimitiveGram q q` minus the dilation shear
`2 * v * (v - u) * pmRamanujanPrimitiveGram (p * q) q`. -/
theorem pmRamanujanPrimitiveGram_two_mode_dilation_identity {p q : ℕ}
    (hp : p.Prime) (hq : 1 < q) (hpq : ¬ p ∣ q) (u v : ℝ) :
    u ^ (2 : ℕ) * pmRamanujanPrimitiveGram q q +
      2 * u * v * pmRamanujanPrimitiveGram (p * q) q +
      v ^ (2 : ℕ) * pmRamanujanPrimitiveGram (p * q) (p * q) =
      (u ^ (2 : ℕ) + ((p : ℝ) - 1) * v ^ (2 : ℕ)) * pmRamanujanPrimitiveGram q q -
        2 * v * (v - u) * pmRamanujanPrimitiveGram (p * q) q := by
  rw [pmRamanujanPrimitiveGram_prime_mul_diag hp hq hpq]
  ring

/-- **Exact Cancellation of Off-Diagonal Gram Coupling on Dilation-Flat Probes
(`pmRamanujanPrimitiveGram_two_mode_flat_eq`):**
When `v = u` on the prime-dilated pair `{q, p * q}` (`¬ p ∣ q`), the off-diagonal Gram coupling
cancels the diagonal prime-dilation defect identically, yielding `p * u² * pmRamanujanPrimitiveGram q q`. -/
theorem pmRamanujanPrimitiveGram_two_mode_flat_eq {p q : ℕ}
    (hp : p.Prime) (hq : 1 < q) (hpq : ¬ p ∣ q) (u : ℝ) :
    u ^ (2 : ℕ) * pmRamanujanPrimitiveGram q q +
      2 * u * u * pmRamanujanPrimitiveGram (p * q) q +
      u ^ (2 : ℕ) * pmRamanujanPrimitiveGram (p * q) (p * q) =
      (p : ℝ) * u ^ (2 : ℕ) * pmRamanujanPrimitiveGram q q := by
  have h := pmRamanujanPrimitiveGram_two_mode_dilation_identity hp hq hpq u u
  linarith

/-- **Asymptotic Negative Self-Energy Dilation Limit at Non-Prime-Power Modes
(`tendsto_pmRamanujanPrimitiveGram_prime_mul_not_isPrimePow`):**
For every composite non-prime-power mode `q > 1` (`¬ IsPrimePow q`, such as `q = 6`), as `p → ∞`
through primes, the prime-dilated Gram covariance `pmRamanujanPrimitiveGram (p * q) q` converges to
`-pmRamanujanPrimitiveGram q q < 0`. -/
theorem tendsto_pmRamanujanPrimitiveGram_prime_mul_not_isPrimePow {q : ℕ}
    (hq : 1 < q) (hnp : ¬ IsPrimePow q) :
    Tendsto (fun p : {p : ℕ // p.Prime} => pmRamanujanPrimitiveGram ((p : ℕ) * q) q)
      atTop (𝓝 (-pmRamanujanPrimitiveGram q q)) := by
  have h := tendsto_pmRamanujanPrimitiveGram_prime_mul hq hq
  rwa [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hnp, mul_zero, zero_div, zero_sub] at h

end

end GaloisForLFunctions.BezoutValuationIncidence
