import GaloisForLFunctions.BezoutValuationIncidence.TupleAdmissibilityCollisionEnergyAndHardyLittlewoodCoercivity
import GaloisForLFunctions.BezoutValuationIncidence.SharpPrimitiveEnergySuccessorFrontier
import GaloisForLFunctions.BiScaleUncertainty.TwoLagMomentCone
import GaloisForLFunctions.BiScaleUncertainty.SixthSievePhaseRecovery
import GaloisForLFunctions.TransHorizonIncidenceMechanics.TotientObservabilityThresholdAndValuationFiberCollision
import GaloisForLFunctions.TransHorizonIncidenceMechanics.ActiveSawtoothInterpolationAndSharpConditioning

/-!
# Two-Lag Five-Mode Polytope, Higher-Moment Phase Recovery, and Sub-Horizon Observability Bridge

This module unifies deep results formalized across `BiScaleUncertainty` and
`TransHorizonIncidenceMechanics` with `BezoutValuationIncidence`, resolving several structural
problems and strengthening the BVI flagship theorems (independent of Wall 1):

1. **Resolution of the Diameter-$D = 2$ Three-Tuple ($H_3 = (0, 1, 2)$) Spectral Polytope &
   Five-Mode Realizability (Addressing BVI Open Problem 3):**
   - For the consecutive 3-tuple $H_3 = (0, 1, 2)$ of diameter $D = 2$, the centered 3-tuple
     variance functional over a complete period $1 \dots N!$ is
     $$\mathcal{V}_{H_3}(N, c) := 3\,\operatorname{Cov}_0(N, c) + 4\,\operatorname{Cov}_1(N, c)
       + 2\,\operatorname{Cov}_2(N, c).$$
   - By the five-facet two-lag cone (`TwoLagSieve.MomentCone`) of `BiScaleUncertainty`, every
     divisor mode $e \ge 2$ has non-negative 3-tuple eigenvalue
     $$\Lambda_{H_3}(e) := 3\,\varphi(e) + 4\,\mu(e) + 2\,\lambda_2(e)
       = \bigl(2\varphi(e) + 3\mu(e) + \lambda_2(e)\bigr) + \bigl(\varphi(e) + \mu(e) + \lambda_2(e)\bigr) \ge 0,$$
     which vanishes at $e = 3$ ($\Lambda_{H_3}(3) = 0$, matching `tuplePrimeStructureFactor H_3 3 = 0`
     since $(0, 1, 2)$ covers all residue classes mod $3$) and attains $6\,\varphi(e)$ at $e = 6$
     ($\Lambda_{H_3}(6) = 12 = 6\,\varphi(6)$).
   - Consequently, every finite sieve weight $c : \mathbb{N} \to \mathbb{R}$ satisfies the sharp
     universal two-sided envelope
     $$0 \le \mathcal{V}_{H_3}(N, c) \le 6\,\operatorname{Var}(N, c),$$
     and at every cutoff $N + 12 \ge 12$, the five extreme modes $\{2, 3, 4, 6, 12\}$ (`fiveModeWeight`)
     exhaust the entire joint two-lag moment cone while simultaneously realizing the closed-form
     primitive energy
     $$12\,\mathcal{E}_{\mathrm{prim}}(N + 12) = 3 a^2 + 8 b^2 + 12 c^2 + 24 d^2 + 96 e^2$$
     and centered 3-tuple variance
     $$\mathcal{V}_{H_3}(N + 12) = a^2 + 2 c^2 + 12 d^2 + 16 e^2.$$

2. **Higher-Moment Signed Selberg Coordinate Recovery vs. Quadratic Sign Ambiguity:**
   - Whereas BVI's 2-point lag schedules recover only the unsigned squares $Y_{N,c}(q)^2$,
     3-point translated moments (`tripleMoment`) uniquely recover the **signed** Selberg coordinate
     $Y_{N,c}(q)$ for every odd divisor mode $q \in [1, N]$ (`bvi_tripleMoment_recovers_signed_odd_modes`).
   - On the even-mode pair $q \in \{6, 10\}$ (`evenPairReal a b`), all affine 2-point moments and
     all translated $m$-point moments of degree $m \le 5$ are invariant under $(a, b) \mapsto (a, -b)$,
     whereas adding the single zero-lag 6th moment uniquely recovers $(a, b)$ up to a single global
     sign $\pm(a, b)$ with exact flip gap $960 a^3 b^3$ (`bvi_evenPair_sixth_moment_sign_hierarchy`).

3. **Sub-Horizon Totient Phase Observability ($\Phi_{\max}(N) < N$) & Sharp Active-Sawtooth Conditioning:**
   - Upgrading BVI's $N$-step observability horizon, the prime-power totient threshold
     $\Phi_{\max}(N) = \max_{p^a \le N} \varphi(p^a)$ satisfies $\Phi_{\max}(N) < N$ for all $N \ge 1$
     and uniquely determines the full residue phase $k \bmod L_N$ from $W \ge \Phi_{\max}(N)$
     consecutive observations (`bvi_subhorizon_totient_observability_and_sharp_collision`).
   - Upgrading BVI's prefix conditioning bound $2\tau(d)$, active sawtooth sampling at arbitrary
     common powers $j^m$ ($m \ge 1$, arbitrarily far beyond any scale $B$) reconstructs every
     squarefree coefficient $c(d)$ ($d \in [2, N]$) with the **exact, attained** amplification constant
     $\mathcal{A}(d) = \frac{2d}{d - 1}(\tau(d) - 1)$ (`bvi_active_power_sampling_sharp_conditioning`).
-/

open Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.BiScaleUncertainty.TwoLagSieve
open GaloisForLFunctions.BiScaleUncertainty.SieveMoments
open GaloisForLFunctions.BiScaleUncertainty.AffineSieve
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-!
## §1. The Diameter-$D = 2$ Three-Tuple ($H_3 = (0, 1, 2)$) Spectral Polytope and Five-Mode Synthesis
-/

/-- The canonical consecutive 3-tuple $H_3 = (0, 1, 2)$ of diameter $D = 2$. -/
def consecutiveThreeTuple (i : Fin 3) : ℕ := i.val

/-- The consecutive 3-tuple $H_3 = (0, 1, 2)$ is equidistributed modulo $3$, so its prime
Ramanujan structure factor at $p = 3$ vanishes identically: $S_3(H_3) = 0$. -/
theorem consecutiveThreeTuple_primeStructureFactor_three_eq_zero :
    tuplePrimeStructureFactor consecutiveThreeTuple 3 = 0 := by
  rw [tuplePrimeStructureFactor_eq_zero_iff consecutiveThreeTuple 3 (by omega)]
  intro r hr
  fin_cases hr <;> decide

/-- At $p = 2$, the consecutive 3-tuple $H_3 = (0, 1, 2)$ has occupancy counts $\nu(2, 0) = 2$
and $\nu(2, 1) = 1$, so its prime structure factor is $S_2(H_3) = 2(2^2 + 1^2) - 3^2 = 1$. -/
theorem consecutiveThreeTuple_primeStructureFactor_two_eq_one :
    tuplePrimeStructureFactor consecutiveThreeTuple 2 = 1 := by
  have hcol : tupleModCollisionEnergy consecutiveThreeTuple 2 = 5 := by decide
  unfold tuplePrimeStructureFactor
  rw [hcol]
  norm_num

/-- The divisor-mode eigenvalue for the centered 3-tuple variance on $H_3 = (0, 1, 2)$:
$$\Lambda_{H_3}(e) = 3\,\varphi(e) + 4\,\mu(e) + 2\,\lambda_2(e).$$ -/
def threeTupleModeEigenvalue (e : ℕ) : ℝ :=
  3 * (Nat.totient e : ℝ) + 4 * (μ e : ℝ) + 2 * lagTwoEigenvalue e

/-- Exact algebraic decomposition of the 3-tuple mode eigenvalue into the first two facets of
`MomentCone` and into its upper-bound complement relative to $6\,\varphi(e)$. -/
theorem threeTupleModeEigenvalue_cone_identities (e : ℕ) :
    threeTupleModeEigenvalue e =
      (2 * (Nat.totient e : ℝ) + 3 * (μ e : ℝ) + lagTwoEigenvalue e) +
        ((Nat.totient e : ℝ) + (μ e : ℝ) + lagTwoEigenvalue e) ∧
    6 * (Nat.totient e : ℝ) - threeTupleModeEigenvalue e =
      ((Nat.totient e : ℝ) - 4 * (μ e : ℝ) - 2 * lagTwoEigenvalue e) +
        2 * (Nat.totient e : ℝ) := by
  unfold threeTupleModeEigenvalue
  constructor <;> ring

/-- Every divisor mode $e \ge 2$ satisfies the two-sided spectral enclosure
$$0 \le \Lambda_{H_3}(e) \le 6\,\varphi(e).$$ -/
theorem threeTupleModeEigenvalue_bounds {e : ℕ} (he : 2 ≤ e) :
    0 ≤ threeTupleModeEigenvalue e ∧
      threeTupleModeEigenvalue e ≤ 6 * (Nat.totient e : ℝ) := by
  obtain ⟨h1, h2, _, h4, _⟩ := arithmetic_momentCone he
  have hphi : (0 : ℝ) ≤ (Nat.totient e : ℝ) := Nat.cast_nonneg _
  obtain ⟨hid1, hid2⟩ := threeTupleModeEigenvalue_cone_identities e
  constructor <;> linarith

/-- Exact values of the 3-tuple mode eigenvalue $\Lambda_{H_3}(e)$ on the five extreme modes
$e \in \{2, 3, 4, 6, 12\}$:
- $\Lambda_{H_3}(2) = 1 = S_2(H_3)$,
- $\Lambda_{H_3}(3) = 0 = S_3(H_3)$ (complete modular cancellation at $p = 3$),
- $\Lambda_{H_3}(4) = 2$,
- $\Lambda_{H_3}(6) = 12 = 6\,\varphi(6)$ (attaining the upper bound $6\,\varphi(e)$),
- $\Lambda_{H_3}(12) = 16$. -/
theorem threeTupleModeEigenvalue_five_modes :
    threeTupleModeEigenvalue 2 = 1 ∧
    threeTupleModeEigenvalue 3 = 0 ∧
    threeTupleModeEigenvalue 4 = 2 ∧
    threeTupleModeEigenvalue 6 = 12 ∧
    threeTupleModeEigenvalue 12 = 16 := by
  have hm2 : μ 2 = -1 := ArithmeticFunction.moebius_apply_prime Nat.prime_two
  have hm3 : μ 3 = -1 := ArithmeticFunction.moebius_apply_prime Nat.prime_three
  have hm4 : μ 4 = 0 := by
    apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
    intro hs
    exact (Nat.squarefree_iff_prime_squarefree.mp hs) 2 Nat.prime_two ⟨1, by ring⟩
  have hm6 : μ 6 = 1 := by
    have h := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
      (show Nat.Coprime 2 3 by decide)
    simpa [hm2, hm3] using h
  have hm12 : μ 12 = 0 := by
    apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
    intro hs
    exact (Nat.squarefree_iff_prime_squarefree.mp hs) 2 Nat.prime_two ⟨3, by ring⟩
  have hphi : Nat.totient 2 = 1 ∧ Nat.totient 3 = 2 ∧ Nat.totient 4 = 2 ∧
      Nat.totient 6 = 2 ∧ Nat.totient 12 = 4 := by decide
  obtain ⟨hf2, hf3, hf4, hf6, hf12⟩ := hphi
  unfold threeTupleModeEigenvalue lagTwoEigenvalue
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [hf2, hf3, hf4, hf6, hf12, hm2, hm3, hm4, hm6, hm12]

/-- The centered 3-tuple period variance for $H_3 = (0, 1, 2)$:
$$\mathcal{V}_{H_3}(N, c) = 3\,\operatorname{Cov}_0(N, c) + 4\,\operatorname{Cov}_1(N, c)
  + 2\,\operatorname{Cov}_2(N, c).$$ -/
def threeTupleCenteredVariance (N : ℕ) (c : ℕ → ℝ) : ℝ :=
  3 * periodCovariance N c 0 + 4 * periodCovariance N c 1 + 2 * periodCovariance N c 2

/-- Exact Selberg-coordinate diagonalization of the centered 3-tuple period variance:
$$\mathcal{V}_{H_3}(N, c) = \sum_{e=2}^N \Lambda_{H_3}(e)\,Y_{N,c}(e)^2.$$ -/
theorem threeTupleCenteredVariance_eq_diagonal (N : ℕ) (c : ℕ → ℝ) :
    threeTupleCenteredVariance N c =
      ∑ e ∈ Finset.Icc 2 N, threeTupleModeEigenvalue e * (selbergMultiplesCoord N c e) ^ 2 := by
  unfold threeTupleCenteredVariance
  rw [periodCovariance_zero, periodCovariance_one, bezout_sub_harmonic_sq_eq, periodCovariance_two]
  unfold sieveVariance threeTupleModeEigenvalue moebiusReal
  simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  ring

/-- **Sharp Two-Sided Spectral Enclosure for the Centered 3-Tuple Variance:**
For every horizon $N$ and every real sieve weight $c : \mathbb{N} \to \mathbb{R}$,
$$0 \le \mathcal{V}_{H_3}(N, c) \le 6\,\operatorname{Var}(N, c).$$ -/
theorem threeTupleCenteredVariance_bounds (N : ℕ) (c : ℕ → ℝ) :
    0 ≤ threeTupleCenteredVariance N c ∧
      threeTupleCenteredVariance N c ≤ 6 * sieveVariance N c := by
  have hcone := period_momentCone N c
  rw [periodCovariance_zero] at hcone
  obtain ⟨h1, h2, _, h4, _⟩ := hcone
  have hvar : 0 ≤ sieveVariance N c := sieveVariance_nonneg N c
  unfold threeTupleCenteredVariance
  rw [periodCovariance_zero]
  constructor <;> linarith

/-- **Exact Jordan Primitive Energy and 3-Tuple Variance of the Five-Mode Generating Family:**
At every cutoff $N + 12 \ge 12$, the five-mode weight `fiveModeWeight N H a b c d e` supported on
modes $\{1, 2, 3, 4, 6, 12\}$ simultaneously realizes:
- harmonic mean $\mathcal{H}_{N+12} = H$,
- lag-0 variance $\operatorname{Cov}_0 = a^2 + 2 b^2 + 2 c^2 + 2 d^2 + 4 e^2$,
- lag-1 covariance $\operatorname{Cov}_1 = -a^2 - b^2 + d^2$,
- lag-2 covariance $\operatorname{Cov}_2 = a^2 - b^2 - 2 c^2 - d^2 + 2 e^2$,
- centered 3-tuple variance $\mathcal{V}_{H_3} = a^2 + 2 c^2 + 12 d^2 + 16 e^2$ (with mode $3$
  completely annihilated), and
- primitive energy $12\,\mathcal{E}_{\mathrm{prim}} = 3 a^2 + 8 b^2 + 12 c^2 + 24 d^2 + 96 e^2$. -/
theorem fiveModeWeight_full_spectral_synthesis (N : ℕ) (H a b c d e : ℝ) :
    finiteHarmonicSum (N + 12) (fiveModeWeight N H a b c d e) = H ∧
    periodCovariance (N + 12) (fiveModeWeight N H a b c d e) 0 =
      a ^ 2 + 2 * b ^ 2 + 2 * c ^ 2 + 2 * d ^ 2 + 4 * e ^ 2 ∧
    periodCovariance (N + 12) (fiveModeWeight N H a b c d e) 1 =
      -a ^ 2 - b ^ 2 + d ^ 2 ∧
    periodCovariance (N + 12) (fiveModeWeight N H a b c d e) 2 =
      a ^ 2 - b ^ 2 - 2 * c ^ 2 - d ^ 2 + 2 * e ^ 2 ∧
    threeTupleCenteredVariance (N + 12) (fiveModeWeight N H a b c d e) =
      a ^ 2 + 2 * c ^ 2 + 12 * d ^ 2 + 16 * e ^ 2 ∧
    12 * sievePrimitiveEnergy (N + 12) (fiveModeWeight N H a b c d e) =
      3 * a ^ 2 + 8 * b ^ 2 + 12 * c ^ 2 + 24 * d ^ 2 + 96 * e ^ 2 := by
  obtain ⟨hH, h0, h1, h2⟩ := fiveModeWeight_moments N H a b c d e
  have h3tup : threeTupleCenteredVariance (N + 12) (fiveModeWeight N H a b c d e) =
      a ^ 2 + 2 * c ^ 2 + 12 * d ^ 2 + 16 * e ^ 2 := by
    unfold threeTupleCenteredVariance
    rw [h0, h1, h2]
    ring
  refine ⟨hH, h0, h1, h2, h3tup, ?_⟩
  rw [twelve_mul_sievePrimitiveEnergy_eq_jordan_diagonal]
  have htail : (∑ q ∈ Finset.Icc 2 (N + 12), jordanTotient2 q *
      (selbergMultiplesCoord (N + 12) (fiveModeWeight N H a b c d e) q) ^ 2) =
      ∑ q ∈ Finset.Icc 2 (N + 12), jordanTotient2 q * (fiveModeProfile H a b c d e q) ^ 2 := by
    apply Finset.sum_congr rfl
    intro q hq
    unfold fiveModeWeight
    rw [selbergMultiplesCoord_ramanujan_inverse, if_pos]
    obtain ⟨hq2, hqN⟩ := Finset.mem_Icc.mp hq
    exact Finset.mem_Icc.mpr ⟨by omega, hqN⟩
  rw [htail]
  have hfull := sum_fiveModeProfile_sq N jordanTotient2 H a b c d e
  have hI : Finset.Icc 1 (N + 12) = insert 1 (Finset.Icc 2 (N + 12)) := by
    ext q
    simp only [Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hI, Finset.sum_insert (by simp)] at hfull
  have hp1 : fiveModeProfile H a b c d e 1 = H := by simp [fiveModeProfile]
  rw [hp1] at hfull
  have hj2 : jordanTotient2 2 = 3 :=
    (jordanTotient2_sharp_successor_facets 0).1.2.mpr (Or.inl rfl)
  have hj3 : jordanTotient2 3 = 8 :=
    (jordanTotient2_sharp_successor_facets 1).1.2.mpr (Or.inr rfl)
  have hj4 : jordanTotient2 4 = 12 :=
    (jordanTotient2_sharp_successor_facets 2).2.1.2.mpr (Or.inr rfl)
  have hj6 : jordanTotient2 6 = 24 :=
    (jordanTotient2_sharp_successor_facets 4).2.2.2.mpr (Or.inr rfl)
  have hj12 : jordanTotient2 12 = 96 := by
    have hcop : Nat.Coprime 4 3 := by decide
    have hmul : jordanTotient2 (4 * 3) = jordanTotient2 4 * jordanTotient2 3 := by
      simp_rw [jordanTotient2_eq_gcdPowKernel]
      exact (isMultiplicative_gcdPowKernel 2).map_mul_of_coprime hcop
    norm_num [hj4, hj3] at hmul
    exact hmul
  have ht3 : Nat.totient 3 = 2 := Nat.totient_prime Nat.prime_three
  have ht4 := wall11_totient_degeneracy_broken_by_bezout.1
  have ht6 := wall11_totient_degeneracy_broken_by_bezout.2.1
  have hm2 : moebiusReal 2 = -1 := by
    simp [moebiusReal, ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  have hm3 : moebiusReal 3 = -1 := by
    simp [moebiusReal, ArithmeticFunction.moebius_apply_prime Nat.prime_three]
  have hg4 := wall11_totient_degeneracy_broken_by_bezout.2.2.1
  have hg6 := wall11_totient_degeneracy_broken_by_bezout.2.2.2
  rw [ht4] at hg4
  rw [ht6] at hg6
  have hm4 : moebiusReal 4 = 0 := by norm_num at hg4; linarith
  have hm6 : moebiusReal 6 = 1 := by norm_num at hg6; linarith
  norm_num [ht3, ht4, ht6, hm2, hm3, hm4, hm6] at hj2 hj3 hj4 hj6
  rw [hj2, hj3, hj4, hj6, hj12] at hfull
  linarith

/-!
## §2. Higher-Moment Signed Selberg Coordinate Recovery vs. Quadratic Sign Ambiguity
-/

/-- **Signed Odd-Mode Selberg Coordinate Recovery from 3-Point Moments
(`bvi_tripleMoment_recovers_signed_odd_modes`):**
Whereas 2-point lag correlations depend only on $Y_{N,c}(q)^2$ (leaving a $2^{N-1}$ sign ambiguity),
the 3-point translated moments `tripleMoment N c h k` uniquely determine the **signed** Selberg
coordinate $Y_{N,c}(q)$ for every odd divisor mode $q \in [1, N]$, as well as the harmonic mean
$\mathcal{H}_N(c) = Y_{N,c}(1)$. -/
theorem bvi_tripleMoment_recovers_signed_odd_modes (N : ℕ) (c e : ℕ → ℝ)
    (htriple : ∀ h k : ℕ, tripleMoment N c h k = tripleMoment N e h k) :
    (∀ q ∈ Finset.Icc 1 N, Odd q →
      selbergMultiplesCoord N c q = selbergMultiplesCoord N e q) ∧
    (1 ≤ N → finiteHarmonicSum N c = finiteHarmonicSum N e) := by
  have hodd := tripleMoment_recovers_odd_coordinates N c e htriple
  refine ⟨hodd, fun hN => ?_⟩
  rw [← selbergMultiplesCoord_one_eq_finiteHarmonicSum,
    ← selbergMultiplesCoord_one_eq_finiteHarmonicSum]
  exact hodd 1 (Finset.mem_Icc.mpr ⟨le_rfl, hN⟩) odd_one

/-- **Sharp 6th-Order Even-Mode Phase Recovery Hierarchy
(`bvi_evenPair_sixth_moment_sign_hierarchy`):**
On the even-mode pair $q \in \{6, 10\}$ (`evenPairReal a b`):
1. Every translated moment of degree $m \le 5$ is invariant under flipping the relative sign
   $(a, b) \mapsto (a, -b)$,
2. The single zero-lag 6th moment separates $(a, b)$ from $(a, -b)$ by the exact cubic cross term
   $960 a^3 b^3$, and
3. The affine 2-point moments together with the zero-lag 6th moment uniquely determine $(a, b)$
   up to a single global sign $\pm(a, b)$. -/
theorem bvi_evenPair_sixth_moment_sign_hierarchy (N : ℕ) (a b c d : ℝ) :
    (∀ (m : ℕ), m ≤ 5 → ∀ h : Fin m → ℕ,
      translatedMoment (N + 10) (evenPairReal a b) h =
        translatedMoment (N + 10) (evenPairReal a (-b)) h) ∧
    translatedMoment (N + 10) (evenPairReal a b) (fun _ : Fin 6 => 0) -
      translatedMoment (N + 10) (evenPairReal a (-b)) (fun _ : Fin 6 => 0) =
      960 * a ^ 3 * b ^ 3 ∧
    (((∀ u v, affineMoment (N + 10) (evenPairReal a b) u v =
          affineMoment (N + 10) (evenPairReal c d) u v) ∧
        translatedMoment (N + 10) (evenPairReal a b) (fun _ : Fin 6 => 0) =
          translatedMoment (N + 10) (evenPairReal c d) (fun _ : Fin 6 => 0)) ↔
      (c = a ∧ d = b) ∨ (c = -a ∧ d = -b)) :=
  ⟨evenPair_through_five_flip N a b,
    evenPair_sixth_flip_difference N a b,
    evenPair_recovery_iff N a b c d⟩

/-!
## §3. Sub-Horizon Totient Phase Observability and Sharp Active-Sawtooth Conditioning
-/

/-- **Sub-Horizon Totient Phase Observability and Valuation-Clock Collision Bridge
(`bvi_subhorizon_totient_observability_and_sharp_collision`):**
For every cutoff $N \ge 1$:
1. The prime-power totient threshold $\Phi_{\max}(N) = \operatorname{horizonTotientThreshold}(N)$
   is strictly smaller than $N$ ($\Phi_{\max}(N) < N$),
2. Observing $s_{N,c}(k + t)$ for $0 \le t < \Phi_{\max}(N)$ uniquely determines the entire
   infinite future trajectory $t \mapsto s_{N,c}(k + t)$ ($t \in \mathbb{N}$), and
3. For every prime power $p^a$ ($a \ge 1$), any window of length $W < \varphi(p^a)$ fails to
   separate $k = 1$ from the valuation-clock shift $\ell = 1 + p^{a-1}$. -/
theorem bvi_subhorizon_totient_observability_and_sharp_collision {N : ℕ} (hN : 1 ≤ N) :
    horizonTotientThreshold N < N ∧
    (∀ k l : ℕ,
      (∀ t < horizonTotientThreshold N, ∀ c : ℕ → ℝ,
        sieveSeq N c (k + t) = sieveSeq N c (l + t)) ↔
      (∀ t : ℕ, ∀ c : ℕ → ℝ, sieveSeq N c (k + t) = sieveSeq N c (l + t))) ∧
    (∀ {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) (W : ℕ),
      (∀ k l : ℕ,
        (∀ t < W, Nat.gcd (k + t) (p ^ a) = Nat.gcd (l + t) (p ^ a)) →
        Nat.ModEq (p ^ a) k l) ↔
      (p ^ a).totient ≤ W) := by
  refine ⟨horizonTotientThreshold_lt_self hN, fun k l => ?_,
    fun hp ha W => prime_pow_trace_injective_iff_totient_le hp ha W⟩
  rw [← horizonObservationPhase_eq_iff_totient_trace N le_rfl k l,
    horizonObservationPhase_eq_iff_all_future N k l]

/-- **Sharp Active-Sawtooth Conditioning and Arbitrary-Scale Power Recovery Bridge
(`bvi_active_power_sampling_sharp_conditioning`):**
For squarefree-supported weights at cutoff $N$:
1. Every coefficient error $|c(d) - b(d)|$ ($d \in [2, N]$ squarefree) is bounded by
   $\operatorname{activeSampleAmplification}(d) \cdot E = \frac{2d}{d - 1}(\tau(d) - 1)\,E$
   in terms of the sup-norm error $E$ of power samples $j^m$ ($m \ge 1$),
2. This constant $\frac{2d}{d - 1}(\tau(d) - 1)$ is **attained** by an explicit squarefree weight
   with prescribed harmonic mean $H$, and
3. Arbitrary squarefree sample data and harmonic mean $H$ can be realized by power samples $j^m$
   placed strictly above any prescribed observation scale $B$. -/
theorem bvi_active_power_sampling_sharp_conditioning (N : ℕ) (H : ℝ)
    {m d : ℕ} (hm : 1 ≤ m) (hd : 2 ≤ d) (hdN : d ≤ N) (hs : Squarefree d) :
    (∀ {c b : ℕ → ℝ} (hc : ∀ j : ℕ, ¬ Squarefree j → c j = 0)
        (hb : ∀ j : ℕ, ¬ Squarefree j → b j = 0) (E : ℝ),
      (∀ j ∈ Finset.Icc 2 N, Squarefree j →
        |activeCenteredSawtoothSum N c (j ^ m) (j ^ m) -
          activeCenteredSawtoothSum N b (j ^ m) (j ^ m)| ≤ E) →
      |c d - b d| ≤ activeSampleAmplification d * E) ∧
    (∃ c : ℕ → ℝ, (∀ j : ℕ, ¬ Squarefree j → c j = 0) ∧
      finiteHarmonicSum N c = H ∧
      (∀ j ∈ Finset.Icc 2 N, Squarefree j →
        |activeCenteredSawtoothSum N c (j ^ m) (j ^ m)| ≤ 1) ∧
      c d = activeSampleAmplification d) ∧
    (∀ (B : ℕ) (a : ℕ → ℝ),
      ∃ m' : ℕ, ∃ c : ℕ → ℝ, 1 ≤ m' ∧
        (∀ j ∈ Finset.Icc 2 N, B < j ^ m') ∧
        (∀ j : ℕ, ¬ Squarefree j → c j = 0) ∧
        finiteHarmonicSum N c = H ∧
        ∀ j ∈ Finset.Icc 2 N, Squarefree j →
          activeCenteredSawtoothSum N c (j ^ m') (j ^ m') = a j) := by
  have hN : 1 ≤ N := by omega
  refine ⟨fun hc hb E hobs =>
      active_power_samples_coefficient_error_le N hc hb hm hd hdN hs E hobs,
    exists_active_power_samples_amplification_attainer N H hm hd hdN hs,
    fun B a => exists_distant_calibrated_active_interpolant hN B H a⟩

end

end GaloisForLFunctions.BezoutValuationIncidence
