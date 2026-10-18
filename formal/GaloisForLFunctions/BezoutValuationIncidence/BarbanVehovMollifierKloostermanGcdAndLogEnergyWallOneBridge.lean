import GaloisForLFunctions.BezoutValuationIncidence.NaturalCutoffMultiDepthCofactorAndConditionalTailBridge
import GaloisForLFunctions.BezoutValuationIncidence.CompensatedHarmonicPredecessorPeakDriftAndDiagonalBudget
import GaloisForLFunctions.BiScaleUncertainty.KerPCenteredSieveAndFirstSecondMomentReciprocity
import GaloisForLFunctions.BiScaleUncertainty.VasyuninReciprocityAndExactTailGramProducer
import GaloisForLFunctions.RHTower.Sieve.BarbanVehovGcdFormSharp
import GaloisForLFunctions.RHTower.Sieve.KloostermanProductFrequencyGcdBound
import GaloisForLFunctions.RHTower.Sieve.KloostermanSharedHybridCollapse
import GaloisForLFunctions.RHTower.Sieve.StadlmannReciprocalPhaseApplications
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusLogConvolution
import GaloisForLFunctions.RHTower.EulerDeletionAveragedDivisorCovariance
import GaloisForLFunctions.TransHorizonIncidenceMechanics.DivisorIncidencePerturbationAndLogarithmicDamping

/-!
# Barban–Vehov Mollifier Annihilation, Kloosterman Shared-GCD Dispersion, Vasyunin Pronic Cells, and Logarithmic Energy Balance (`BarbanVehovMollifierKloostermanGcdAndLogEnergyWallOneBridge`)

This module integrates existing corpus infrastructure from `BiScaleUncertainty`, `RHTower`,
`RHTower.Sieve`, and `TransHorizonIncidenceMechanics` into `BezoutValuationIncidence` to provide
unconditional tools for the four obstructions of the Wall 1 programme:

1. **Barban–Vehov / Levinson GCD-Power & `ker P` Mollifier Annihilation in BVI (§1)**:
   - Connects the BVI complete-period variance `sieveVariance`, Bézout coprime successor form
     `bezoutCoprimeQuadraticForm`, and finite-prefix discrepancy `sievePrefixDiscrepancy` to the
     Barban–Vehov logarithmic mollifier `barbanVehovWeight X`, its unit-normalized counterpart
     `normalizedBarbanVehovWeight X`, the endpoint-centered `ker P` projection
     `kerPEndpointWeight N c`, and the logarithmic cutoff-averaged source
     `DeletionAveragedDivisor.arithmeticCoeff X M`.
   - Proves that `selbergMultiplesCoord N (barbanVehovWeight X) e` vanishes identically beyond the
     mollifier length (`X < e ≤ N`), bounds both `sieveVariance N (barbanVehovWeight X)` and
     `|bezoutCoprimeQuadraticForm N (barbanVehovWeight X)|` by `4 A² (1 + log X)`, bounds the
     normalized Barban–Vehov variance and Bézout form by `O(1 / log X)`, and bounds the periodic
     Franel GCD-square form `franelGcdQuadraticForm N (barbanVehovWeight N)` directly by
     `N² · barbanVehovSelbergDiagonal N` and `64 A² N (1 + log N)`.

2. **Vasyunin Reciprocal-Cell Partition & Pronic Origin-Tail Gram Bridge (§2)**:
   - Rewrites the `BiScaleUncertainty` bulk-head and small-`t` origin-tail Fermi–Nyman Gram
     identities (`fermiHeadGram`, `fermiTailGram`) and Kronecker single-cell combinator energies
     (`singleCellFermiCombinator`) in terms of the BVI pronic sequence `pronicSeq n = n (n + 1)`
     with zero truncation remainder.

3. **Distinct-Modulus Kloosterman Terminal-Block, Shared-GCD Multiplicity & Stadlmann Reciprocal-Phase Bridge (§3)**:
   - Bridges the `RHTower.Sieve` distinct-modulus Kloosterman terminal-block reduction (`M % lcm(q, r)`),
     product-frequency shared-GCD fibre bound (`card ≤ gcd(q, r)`), two-sided shared hybrid
     inverse-residue collapse, and Stadlmann reciprocal-phase / Chen–Gupta–Li Ramanujan duality into
     `BezoutValuationIncidence`, giving a simultaneous minimum bound on distinct-modulus correlations
     combining residual-length and horizon-independent shared-GCD budgets.

4. **Pronic Logarithmic-Convolution Energy Sandwich & Divisor-Incidence Damping Stability (§4)**:
   - Connects `RHTower.pmPowerDampedDivisor_log_energy_balance` to `pmPowerDampedDivisorDiscreteEnergy`
     and BVI's canonical renormalized interior martingale decomposition, proving that the signed sum
     of the logarithmic dilation, prefix, and forcing covariances is unconditionally sandwiched
     between `0` and `log N · pmPowerDampedDivisorDiscreteEnergy ε N`, with an explicit non-negative
     pronic log-deficit identity.
   - Couples this with the `TransHorizonIncidenceMechanics` divisor-incidence damping radius
     `incidenceDampingRadius N = 1 / (96 (N + 1) (log N)²)` for `sieveRenormalizedPrefixDefect`.
-/

open Complex MeasureTheory Set Filter Topology Finset ArithmeticFunction
open GaloisForLFunctions.NymanMellin GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

noncomputable section

namespace GaloisForLFunctions.BezoutValuationIncidence

set_option autoImplicit false

/-! ## §1. Barban–Vehov / Levinson GCD-Power & `ker P` Mollifier Annihilation in BVI -/

/-- **High-Frequency Selberg Coordinate Annihilation for `barbanVehovWeight X`**:
For `1 ≤ X ≤ N` and every modulus `e > X`, the BVI Selberg multiples-coordinate
`selbergMultiplesCoord N (barbanVehovWeight X) e` vanishes identically. -/
theorem selbergMultiplesCoord_barbanVehovWeight_eq_zero_of_lt
    {X N e : ℕ} (hXN : X ≤ N) (hXe : X < e) :
    selbergMultiplesCoord N (barbanVehovWeight X) e = 0 := by
  have he : 0 < e := by omega
  exact barbanVehov_inner_eq_zero he hXN hXe

/-- **Uniform Reciprocal-Totient Bound on Selberg Coordinates of `barbanVehovWeight X`**:
For `X ≤ N` and `e > 0`, `|selbergMultiplesCoord N (barbanVehovWeight X) e| ≤ A / φ(e)` (and
vanishes off squarefree `e`). -/
theorem abs_selbergMultiplesCoord_barbanVehovWeight_le
    {X N e : ℕ} (he : 0 < e) (hXN : X ≤ N) :
    |selbergMultiplesCoord N (barbanVehovWeight X) e| ≤
      coprimeLogMoebiusConst / (Nat.totient e : ℝ) :=
  abs_barbanVehov_inner_le he hXN

/-- **Exact `ker P` Variance-to-Selberg Identity (`kerPEndpointWeight`)**:
For `N ≥ 1` and any sieve weight `c : ℕ → ℝ`, projecting `c` onto `ker P` via `kerPEndpointWeight N c`
eliminates the `e = 1` harmonic shadow, so `sieveVariance` equals `selbergTotientDiagonalForm`
and `2 * bezoutCoprimeQuadraticForm ≤ sieveVariance`. -/
theorem sieveVariance_kerPEndpointWeight_eq_selberg_and_bezout_le
    {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) :
    sieveVariance N (kerPEndpointWeight N c) =
        selbergTotientDiagonalForm N (kerPEndpointWeight N c) ∧
      2 * bezoutCoprimeQuadraticForm N (kerPEndpointWeight N c) ≤
        sieveVariance N (kerPEndpointWeight N c) := by
  have hker : finiteHarmonicSum N (kerPEndpointWeight N c) = 0 :=
    finiteHarmonicSum_kerPEndpointWeight_eq_zero hN c
  have hvar := selberg_eq_harmonic_sq_add_variance N (kerPEndpointWeight N c)
  rw [hker, zero_pow (by norm_num), zero_add] at hvar
  refine ⟨hvar.symm, ?_⟩
  rw [← hvar]
  exact (two_mul_bezoutCoprimeQuadraticForm_le_selberg_of_harmonic_eq_zero hN
    (kerPEndpointWeight N c) hker).1

/-- **Exact Drift-Free Prefix Discrepancy & Uniform `ℓ¹` Bound on `kerPEndpointWeight`**:
For `N ≥ 1`, any weight `c : ℕ → ℝ`, and any horizon `M : ℕ`, the BVI prefix discrepancy of
`kerPEndpointWeight N c` equals the uncentered cumulative sieved divisor sum and is bounded
uniformly in `M` by `∑_{d=1}^N |kerPEndpointWeight N c d|`. -/
theorem sievePrefixDiscrepancy_kerPEndpointWeight_eq_sum_and_le
    {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) (M : ℕ) :
    sievePrefixDiscrepancy N M (kerPEndpointWeight N c) =
        (∑ k ∈ Finset.Icc 1 M, sievedDivisorSum N (kerPEndpointWeight N c) k) ∧
      |sievePrefixDiscrepancy N M (kerPEndpointWeight N c)| ≤
        ∑ d ∈ Finset.Icc 1 N, |kerPEndpointWeight N c d| := by
  have hker : finiteHarmonicSum N (kerPEndpointWeight N c) = 0 :=
    finiteHarmonicSum_kerPEndpointWeight_eq_zero hN c
  have hsum : sievePrefixDiscrepancy N M (kerPEndpointWeight N c) =
      ∑ k ∈ Finset.Icc 1 M, sievedDivisorSum N (kerPEndpointWeight N c) k := by
    rw [sievePrefixDiscrepancy_eq_sum_sub_drift, hker, mul_zero, sub_zero]
  refine ⟨hsum, ?_⟩
  rw [hsum]
  exact abs_sum_sievedDivisorSum_le_of_harmonic_eq_zero N (kerPEndpointWeight N c) hker M

/-- **General Magnitude Bound `|bezoutCoprimeQuadraticForm N c| ≤ selbergTotientDiagonalForm N c`**:
Because `|μ(e)| ≤ 1 ≤ φ(e)` for every `e ≥ 1`, the Bézout coprime quadratic form is bounded in
absolute value by the Selberg totient diagonal form for every `N : ℕ` and every `c : ℕ → ℝ`. -/
theorem abs_bezoutCoprimeQuadraticForm_le_selbergTotientDiagonalForm
    (N : ℕ) (c : ℕ → ℝ) :
    |bezoutCoprimeQuadraticForm N c| ≤ selbergTotientDiagonalForm N c := by
  rw [bezoutCoprimeQuadraticForm_eq_moebius_diagonal, selbergTotientDiagonalForm]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun e he => ?_)
  have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
  have hphi : (1 : ℝ) ≤ (Nat.totient e : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr he1
  have hmu : |moebiusReal e| ≤ 1 := by
    unfold moebiusReal
    exact abs_moebius_le_one e
  rw [abs_mul, abs_of_nonneg (sq_nonneg (selbergMultiplesCoord N c e))]
  exact mul_le_mul_of_nonneg_right (hmu.trans hphi) (sq_nonneg _)

/-- **Logarithmic Bound on BVI Variance and Bézout Coprime Form for `barbanVehovWeight X`**:
For `X ≤ N`, both `sieveVariance N (barbanVehovWeight X)` and
`|bezoutCoprimeQuadraticForm N (barbanVehovWeight X)|` are bounded above by
`4 * coprimeLogMoebiusConst ^ 2 * (1 + Real.log X)`. -/
theorem sieveVariance_and_bezout_barbanVehovWeight_le_log
    {X N : ℕ} (hXN : X ≤ N) :
    sieveVariance N (barbanVehovWeight X) ≤
        4 * coprimeLogMoebiusConst ^ (2 : ℕ) * (1 + Real.log (X : ℝ)) ∧
      |bezoutCoprimeQuadraticForm N (barbanVehovWeight X)| ≤
        4 * coprimeLogMoebiusConst ^ (2 : ℕ) * (1 + Real.log (X : ℝ)) := by
  have hsel := barbanVehov_totient_diagonal_le hXN
  have hvar := selberg_eq_harmonic_sq_add_variance N (barbanVehovWeight X)
  have hle_var : sieveVariance N (barbanVehovWeight X) ≤
      selbergTotientDiagonalForm N (barbanVehovWeight X) := by
    linarith [sq_nonneg (finiteHarmonicSum N (barbanVehovWeight X))]
  exact ⟨hle_var.trans hsel,
    (abs_bezoutCoprimeQuadraticForm_le_selbergTotientDiagonalForm N (barbanVehovWeight X)).trans hsel⟩

/-- **`O(1 / log X)` Decay of BVI Variance and Bézout Coprime Form for `normalizedBarbanVehovWeight X`**:
For `2 ≤ X ≤ N`, the unit-normalized Barban–Vehov weight (`normalizedBarbanVehovWeight X 1 = 1`)
has both complete-period variance `sieveVariance` and Bézout coprime form bounded by
`4 A² (1 + log X) / (log X)²`. -/
theorem sieveVariance_and_bezout_normalizedBarbanVehovWeight_le_inv_log
    {X N : ℕ} (hX : 2 ≤ X) (hXN : X ≤ N) :
    sieveVariance N (normalizedBarbanVehovWeight X) ≤
        4 * coprimeLogMoebiusConst ^ (2 : ℕ) * (1 + Real.log (X : ℝ)) /
          (Real.log (X : ℝ)) ^ (2 : ℕ) ∧
      |bezoutCoprimeQuadraticForm N (normalizedBarbanVehovWeight X)| ≤
        4 * coprimeLogMoebiusConst ^ (2 : ℕ) * (1 + Real.log (X : ℝ)) /
          (Real.log (X : ℝ)) ^ (2 : ℕ) := by
  have hsel := (selbergTotientDiagonalForm_normalizedBarbanVehovWeight_pinch hX hXN).2
  have hvar := selberg_eq_harmonic_sq_add_variance N (normalizedBarbanVehovWeight X)
  have hle_var : sieveVariance N (normalizedBarbanVehovWeight X) ≤
      selbergTotientDiagonalForm N (normalizedBarbanVehovWeight X) := by
    linarith [sq_nonneg (finiteHarmonicSum N (normalizedBarbanVehovWeight X))]
  exact ⟨hle_var.trans hsel,
    (abs_bezoutCoprimeQuadraticForm_le_selbergTotientDiagonalForm N
      (normalizedBarbanVehovWeight X)).trans hsel⟩

/-- **Sharp Diagonal & Logarithmic Bounds on `franelGcdQuadraticForm N (barbanVehovWeight N)`**:
Specializing the Levinson GCD-power bounds `sum_barbanVehov_gcd_rpow_div_le_diagonal` and
`sum_barbanVehov_gcd_rpow_div_le` to `s = 2` bounds the periodic Franel GCD-square form
`franelGcdQuadraticForm N (barbanVehovWeight N)` both by `N² · barbanVehovSelbergDiagonal N` and by
`64 A² N (1 + log N)`. -/
theorem franelGcdQuadraticForm_barbanVehovWeight_le_diagonal_and_log (N : ℕ) :
    franelGcdQuadraticForm N (barbanVehovWeight N) ≤
        ((N : ℝ) ^ (2 : ℕ)) * barbanVehovSelbergDiagonal N ∧
      franelGcdQuadraticForm N (barbanVehovWeight N) ≤
        coprimeLogMoebiusConst ^ (2 : ℕ) * (N : ℝ) * (64 * (1 + Real.log (N : ℝ))) := by
  have hrew : franelGcdQuadraticForm N (barbanVehovWeight N) =
      ∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
        barbanVehovWeight N p.1 * barbanVehovWeight N p.2 *
          (Nat.gcd p.1 p.2 : ℝ) ^ (2 : ℝ) / ((p.1 : ℝ) * (p.2 : ℝ)) := by
    unfold franelGcdQuadraticForm
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Real.rpow_two]
    ring
  rw [hrew]
  have hs : (1 : ℝ) ≤ 2 := by norm_num
  have hdiag := sum_barbanVehov_gcd_rpow_div_le_diagonal N hs
  have hlog := sum_barbanVehov_gcd_rpow_div_le N hs
  rw [show (2 : ℝ) * (2 - 1) = (2 : ℝ) by ring, Real.rpow_two] at hdiag
  rw [show (2 : ℝ) - 1 = 1 by ring, Real.rpow_one] at hlog
  exact ⟨hdiag, hlog⟩

/-- **Logarithmic Cutoff-Averaged Divisor Source Annihilation on `[2, X]` (`DeletionAveragedDivisor`)**:
For `1 ≤ X < M`, the tapered difference of Barban–Vehov sources `DeletionAveragedDivisor.divisorSource X M`
has unit value at `k = 1`, vanishes identically across the entire initial window `2 ≤ k ≤ X`, and
equals `(Λ(k) - b_X(k)) / (log M - log X)` on `X < k ≤ M`. -/
theorem deletionAveragedDivisor_window_annihilation_and_vonMangoldt_exposure
    {X M : ℕ} (hX : 1 ≤ X) (hXM : X < M) :
    DeletionAveragedDivisor.divisorSource X M 1 = 1 ∧
      (∀ k : ℕ, 1 < k → k ≤ X → DeletionAveragedDivisor.divisorSource X M k = 0) ∧
      (∀ k : ℕ, 1 < k → k ≤ M →
        DeletionAveragedDivisor.divisorSource X M k =
          (vonMangoldt k - barbanVehovCoeff X k) / (Real.log (M : ℝ) - Real.log (X : ℝ))) :=
  ⟨DeletionAveragedDivisor.divisorSource_one hX hXM,
    fun _ hk hkX => DeletionAveragedDivisor.divisorSource_initial_zero hX hXM hk hkX,
    fun _ hk hkM => DeletionAveragedDivisor.divisorSource_eq_vonMangoldt_sub hX hXM hk hkM⟩

/-! ## §2. Vasyunin Reciprocal-Cell Partition & Pronic Origin-Tail Gram Bridge -/

/-- Helper: `(pronicSeq n : ℝ) = (n : ℝ) * ((n : ℝ) + 1)`. -/
theorem cast_pronicSeq_eq_mul_succ (n : ℕ) :
    (pronicSeq n : ℝ) = (n : ℝ) * ((n : ℝ) + 1) := by
  unfold pronicSeq
  push_cast
  ring

/-- **Exact Pronic-Cell Formula for the Bulk-Head and Origin-Tail Fermi–Nyman Gram Matrices**:
For every cutoff `N : ℕ` and scales `d₁, d₂ : ℕ`, the bulk-head Gram entry `fermiHeadGram N d₁ d₂`
on `(1/(N+1), 1]` equals the finite sum over `1 ≤ n ≤ N` weighted by `1 / pronicSeq n`, and the
small-`t` origin-tail Gram entry `fermiTailGram N d₁ d₂` on `(0, 1/(N+1)]` equals
`fermiGlobalGram d₁ d₂` minus that exact finite pronic sum (with zero truncation remainder). -/
theorem fermiHead_and_tailGram_eq_pronicSeq_sum (N d₁ d₂ : ℕ) :
    fermiHeadGram N d₁ d₂ =
        ((∑ n ∈ Finset.Icc 1 N,
          (fermiCellMatrix (d₁ + 1) n * fermiCellMatrix (d₂ + 1) n) /
            (pronicSeq n : ℝ) : ℝ) : ℂ) ∧
      fermiTailGram N d₁ d₂ =
        fermiGlobalGram d₁ d₂ -
          ((∑ n ∈ Finset.Icc 1 N,
            (fermiCellMatrix (d₁ + 1) n * fermiCellMatrix (d₂ + 1) n) /
              (pronicSeq n : ℝ) : ℝ) : ℂ) := by
  have hsum :
      (∑ n ∈ Finset.Icc 1 N,
        (fermiCellMatrix (d₁ + 1) n * fermiCellMatrix (d₂ + 1) n) /
          ((n : ℝ) * ((n : ℝ) + 1))) =
      ∑ n ∈ Finset.Icc 1 N,
        (fermiCellMatrix (d₁ + 1) n * fermiCellMatrix (d₂ + 1) n) /
          (pronicSeq n : ℝ) := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [cast_pronicSeq_eq_mul_succ]
  refine ⟨?_, ?_⟩
  · rw [fermiHeadGram_eq_sum_cellMatrix, hsum]
  · rw [fermiTailGram_eq_global_sub_sum_cellMatrix, hsum]

/-- **Exact Pronic-Cell Bulk-Head and Origin-Tail Energy of `singleCellFermiCombinator`**:
For every `k N : ℕ`, the bulk-head `L²` energy of `singleCellFermiCombinator (k + 1) N` on
`(1/(N+1), 1]` equals `1 / pronicSeq (k + 1)` if `k + 1 ≤ N` (and `0` otherwise), while its
origin-tail `L²` energy on `(0, 1/(N+1)]` equals its global `L²(0, 1]` energy minus
`if k + 1 ≤ N then 1 / pronicSeq (k + 1) else 0`. -/
theorem singleCellFermiCombinator_pronicSeq_head_and_tail_energy (k N : ℕ) :
    (∫ t in Ioc (1 / ((N : ℝ) + 1)) 1,
        ‖singleCellFermiCombinator (k + 1) N t‖ ^ 2) =
        (if k + 1 ≤ N then 1 / (pronicSeq (k + 1) : ℝ) else 0) ∧
      (∫ t in Ioc (0 : ℝ) (1 / ((N : ℝ) + 1)),
        ‖singleCellFermiCombinator (k + 1) N t‖ ^ 2) =
        (∫ t in Ioc (0 : ℝ) 1, ‖singleCellFermiCombinator (k + 1) N t‖ ^ 2) -
          (if k + 1 ≤ N then 1 / (pronicSeq (k + 1) : ℝ) else 0) := by
  rw [integral_normSq_singleCellFermiCombinator_head_eq,
    integral_normSq_singleCellFermiCombinator_tail_eq_global_sub_cell,
    cast_pronicSeq_eq_mul_succ (k + 1)]
  exact ⟨rfl, rfl⟩

/-! ## §3. Distinct-Modulus Kloosterman Terminal-Block, Shared-GCD Multiplicity & Stadlmann Reciprocal-Phase Bridge -/

/-- **Simultaneous Residual-Length and Shared-GCD Product-Harmonic Bound on Distinct-Modulus Kloosterman Correlations**:
For any unequal stored moduli `q ≠ r`, interval horizon `M : ℕ`, and frequencies `n, k : ℤ`:
1. Every complete `lcm(q + 1, r + 1)` period block in `[1, M]` vanishes identically, reducing
   `kloostermanCrossModulusCorrelation (Finset.Icc 1 M) q r n k` to the terminal block of length
   `M % lcm(q + 1, r + 1)`.
2. Every two-coordinate cross-frequency fibre over `ZMod ((q + 1) * (r + 1))` has cardinality at
   most `gcd(q + 1, r + 1)`.
3. The correlation norm is simultaneously bounded by the minimum of the residual-length budget
   `(M % lcm(q + 1, r + 1)) φ(q + 1) φ(r + 1)` and the horizon-independent shared-GCD budget
   `kloostermanProductGcdHarmonicPairBudget q r`. -/
theorem kloosterman_distinct_modulus_terminal_and_gcd_fibre_bridge
    (M q r : ℕ) (hqr : q ≠ r) (n k : ℤ) (z : ZMod ((q + 1) * (r + 1))) :
    kloostermanCrossModulusCorrelation (Finset.Icc 1 M) q r n k =
        kloostermanNaturalCrossIntervalTerminalBlock M (q + 1) (r + 1)
          (Int.cast n) (Int.cast k) ∧
      Fintype.card (kloostermanProductCrossPhaseFrequencyFibre (q + 1) (r + 1) z) ≤
        (q + 1).gcd (r + 1) ∧
      ‖kloostermanCrossModulusCorrelation (Finset.Icc 1 M) q r n k‖ ≤
        min
          (((M % Nat.lcm (q + 1) (r + 1) : ℕ) : ℝ) *
            Nat.totient (q + 1) * Nat.totient (r + 1))
          (kloostermanProductGcdHarmonicPairBudget q r) := by
  refine ⟨kloostermanCrossModulusCorrelation_Icc_eq_terminalBlock_of_ne M q r hqr n k,
    card_kloostermanProductCrossPhaseFrequencyFibre_le_gcd (q + 1) (r + 1) z,
    le_min (norm_kloostermanCrossModulusCorrelation_Icc_le_terminal_of_ne M q r hqr n k) ?_⟩
  unfold kloostermanProductGcdHarmonicPairBudget
  exact norm_kloostermanCrossModulusCorrelation_Icc_le_productHarmonic_gcd M q r hqr n k

/-- **Stadlmann Reciprocal-Phase / Ramanujan Duality and Shared Hybrid Kloosterman Collapse**:
For any positive modulus `q` (`[NeZero q]`), finite index type `ι`, and frequency family `c : ι → ZMod q`:
1. The multi-factor reciprocal-phase correlation `stadlmannReciprocalPhaseFamilySum q c` collapses
   to the single zero-frequency Kloosterman sum `kloostermanSum q 0 (∑ i, c i)` and to the
   Chen–Gupta–Li Ramanujan sum `cglRamanujanAdditiveSum ⟨q, _⟩ (∑ i, c i)`.
2. The complete frequency second moment of `stadlmannReciprocalPhaseSum q` equals `q · φ(q)`.
3. On any modulus set `Q`, the two-sided shared hybrid Kloosterman bilinear form collapses
   identically by character orthogonality to the inverse-residue correlation
   `∑ q' ∈ Q, w q' * (q' + 1)² * inverseResidueHybridCorrelation q' N M a b t`. -/
theorem stadlmann_reciprocal_phase_and_hybrid_collapse_bridge
    (q : ℕ) [NeZero q] {ι : Type*} [Fintype ι] (c : ι → ZMod q)
    (Q : Finset ℕ) (w : ℕ → ℂ) (N M : ℕ) (a b : ℕ → ℂ) (t : ℝ) :
    stadlmannReciprocalPhaseFamilySum q c = kloostermanSum q 0 (∑ i, c i) ∧
      stadlmannReciprocalPhaseFamilySum q c =
        RHTower.cglRamanujanAdditiveSum ⟨q, Nat.pos_of_ne_zero (NeZero.ne q)⟩ (∑ i, c i) ∧
      (∑ x : ZMod q, Complex.normSq (stadlmannReciprocalPhaseSum q x)) =
        (q : ℝ) * Nat.totient q ∧
      kloostermanSharedHybridModulusBilinear Q w N M a b t =
        ∑ q' ∈ Q, w q' * (((q' + 1 : ℕ) : ℂ) ^ 2) *
          inverseResidueHybridCorrelation q' N M a b t :=
  ⟨stadlmannReciprocalPhaseFamilySum_eq_kloosterman q c,
    stadlmannReciprocalPhaseFamilySum_eq_cglRamanujan q c,
    sum_normSq_stadlmannReciprocalPhaseSum q,
    kloostermanSharedHybridModulusBilinear_eq_inverseResidueCorrelation Q w N M a b t⟩

/-! ## §4. Pronic Logarithmic-Convolution Energy Sandwich & Divisor-Incidence Damping Stability -/

/-- The **Pronic Logarithmic Deficit** of the centered power-damped divisor prefix at horizon `N`:
$$\operatorname{pmPronicLogDeficit}(\varepsilon, N)
  := \sum_{n=1}^N \frac{(\log N - \log n)\,\bigl(\operatorname{pmPowerDampedCenteredDivisorPrefix}(\varepsilon, n)\bigr)^2}{n(n + 1)}.$$ -/
def pmPronicLogDeficit (ε : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N,
    (Real.log (N : ℝ) - Real.log (n : ℝ)) *
      pmPowerDampedCenteredDivisorPrefix ε n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))

/-- **Non-Negativity of `pmPronicLogDeficit`**:
Because `1 ≤ n ≤ N` implies `log n ≤ log N`, `pmPronicLogDeficit ε N ≥ 0` for all `ε : ℝ` and `N : ℕ`. -/
theorem pmPronicLogDeficit_nonneg (ε : ℝ) (N : ℕ) :
    0 ≤ pmPronicLogDeficit ε N := by
  unfold pmPronicLogDeficit
  refine Finset.sum_nonneg fun n hn => ?_
  obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
  have hlog : Real.log (n : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by exact_mod_cast hn1) (by exact_mod_cast hnN)
  have hsub : 0 ≤ Real.log (N : ℝ) - Real.log (n : ℝ) := sub_nonneg.mpr hlog
  positivity

/-- **Exact Pronic Logarithmic-Deficit Decomposition**:
For every `ε : ℝ` and `N : ℕ`, `Real.log N * pmPowerDampedDivisorDiscreteEnergy ε N` splits into the
exact logarithmic covariance combination (`pmPowerDampedDivisor_log_energy_balance`) plus the
non-negative deficit `pmPronicLogDeficit ε N`. -/
theorem log_mul_pmPowerDampedDivisorDiscreteEnergy_eq_covariances_add_deficit
    (ε : ℝ) (N : ℕ) :
    Real.log (N : ℝ) * pmPowerDampedDivisorDiscreteEnergy ε N =
      (pmPowerDampedLogDilationCovariance ε N +
        pmPowerDampedLogPrefixCovariance ε N -
        (pmPowerDampedDivisorDensity ε).re * pmPowerDampedLogForcingCovariance ε N) +
      pmPronicLogDeficit ε N := by
  rw [← pmPowerDampedDivisor_log_energy_balance ε N]
  unfold pmPowerDampedDivisorDiscreteEnergy pmPronicLogDeficit
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

/-- **Two-Sided Pronic Sandwich for the Logarithmic Dilation–Prefix–Forcing Covariance Combination**:
For every `ε : ℝ` and `N : ℕ`, the signed combination of the three logarithmic covariances is
non-negative and bounded above by `Real.log N * pmPowerDampedDivisorDiscreteEnergy ε N`. -/
theorem pmPowerDamped_log_covariances_sandwich (ε : ℝ) (N : ℕ) :
    0 ≤ pmPowerDampedLogDilationCovariance ε N +
          pmPowerDampedLogPrefixCovariance ε N -
          (pmPowerDampedDivisorDensity ε).re * pmPowerDampedLogForcingCovariance ε N ∧
      pmPowerDampedLogDilationCovariance ε N +
          pmPowerDampedLogPrefixCovariance ε N -
          (pmPowerDampedDivisorDensity ε).re * pmPowerDampedLogForcingCovariance ε N ≤
        Real.log (N : ℝ) * pmPowerDampedDivisorDiscreteEnergy ε N := by
  constructor
  · rw [← pmPowerDampedDivisor_log_energy_balance ε N]
    refine Finset.sum_nonneg fun n hn => ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
    positivity
  · rw [log_mul_pmPowerDampedDivisorDiscreteEnergy_eq_covariances_add_deficit ε N]
    exact le_add_of_nonneg_right (pmPronicLogDeficit_nonneg ε N)

/-- **Unified Wall 1 Cross-Module Synthesis (`wall1_corpus_reuse_master_bridge`)**:
Packages the four cross-module Wall 1 tools into a single unconditional theorem:
1. **Barban–Vehov / `ker P` Sieve Annihilation**: For `2 ≤ X ≤ N`, `normalizedBarbanVehovWeight X`
   satisfies `w_X(1) = 1`, vanishes in Selberg coordinates for `e > X`, and has both BVI
   `sieveVariance` and `|bezoutCoprimeQuadraticForm|` bounded by `4 A² (1 + log X) / (log X)²`.
2. **Vasyunin Pronic-Cell Tail Gram Identity**: `fermiTailGram N d₁ d₂` equals `fermiGlobalGram d₁ d₂`
   minus the finite pronic-cell sum over `1 ≤ n ≤ N` with zero truncation remainder.
3. **Kloosterman Shared-GCD & Terminal-Block Bound**: For `q ≠ r`, `kloostermanCrossModulusCorrelation`
   is bounded by the minimum of the terminal-block length bound and `kloostermanProductGcdHarmonicPairBudget q r`.
4. **Pronic Log-Energy Sandwich & Divisor-Incidence Damping Radius**: The logarithmic covariance
   combination is sandwiched in `[0, log N · pmPowerDampedDivisorDiscreteEnergy ε N]`, and within the
   `(log N)²` divisor-incidence damping radius `incidenceDampingRadius N`, every nonempty six-horizon
   prefix defect satisfies `sieveRenormalizedPrefixDefect N M (pmPowerDampedRealWeight ε) ≤ -1/2`. -/
theorem wall1_corpus_reuse_master_bridge :
    (∀ {X N : ℕ}, 2 ≤ X → X ≤ N →
      normalizedBarbanVehovWeight X 1 = 1 ∧
      sieveVariance N (normalizedBarbanVehovWeight X) ≤
        4 * coprimeLogMoebiusConst ^ (2 : ℕ) * (1 + Real.log (X : ℝ)) /
          (Real.log (X : ℝ)) ^ (2 : ℕ)) ∧
    (∀ N d₁ d₂ : ℕ,
      fermiTailGram N d₁ d₂ =
        fermiGlobalGram d₁ d₂ -
          ((∑ n ∈ Finset.Icc 1 N,
            (fermiCellMatrix (d₁ + 1) n * fermiCellMatrix (d₂ + 1) n) /
              (pronicSeq n : ℝ) : ℝ) : ℂ)) ∧
    (∀ M q r : ℕ, q ≠ r → ∀ n k : ℤ,
      ‖kloostermanCrossModulusCorrelation (Finset.Icc 1 M) q r n k‖ ≤
        min
          (((M % Nat.lcm (q + 1) (r + 1) : ℕ) : ℝ) *
            Nat.totient (q + 1) * Nat.totient (r + 1))
          (kloostermanProductGcdHarmonicPairBudget q r)) ∧
    (∀ (ε : ℝ) (N : ℕ),
      0 ≤ pmPowerDampedLogDilationCovariance ε N +
            pmPowerDampedLogPrefixCovariance ε N -
            (pmPowerDampedDivisorDensity ε).re * pmPowerDampedLogForcingCovariance ε N ∧
        pmPowerDampedLogDilationCovariance ε N +
            pmPowerDampedLogPrefixCovariance ε N -
            (pmPowerDampedDivisorDensity ε).re * pmPowerDampedLogForcingCovariance ε N ≤
          Real.log (N : ℝ) * pmPowerDampedDivisorDiscreteEnergy ε N) ∧
    (∀ {N M : ℕ}, 2 ≤ N → 1 ≤ M → M + 1 < 6 * (N + 1) →
      ∀ {ε : ℝ}, 0 ≤ ε → ε ≤ incidenceDampingRadius N →
        sieveRenormalizedPrefixDefect N M (pmPowerDampedRealWeight ε) ≤ -(1 / 2 : ℝ)) := by
  refine ⟨?_, ?_, ?_, pmPowerDamped_log_covariances_sandwich, ?_⟩
  · intro X N hX hXN
    exact ⟨normalizedBarbanVehovWeight_one hX,
      (sieveVariance_and_bezout_normalizedBarbanVehovWeight_le_inv_log hX hXN).1⟩
  · intro N d₁ d₂
    exact (fermiHead_and_tailGram_eq_pronicSeq_sum N d₁ d₂).2
  · intro M q r hqr n k
    exact (kloosterman_distinct_modulus_terminal_and_gcd_fibre_bridge M q r hqr n k 0).2.2
  · intro N M hN hM hhi ε hε hεhi
    exact prefix_defect_le_neg_half_of_incidence_radius hN hM hhi hε hεhi

end GaloisForLFunctions.BezoutValuationIncidence

end
