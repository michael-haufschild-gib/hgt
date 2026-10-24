import GaloisForLFunctions.BezoutValuationIncidence.AllDampingVinogradovKorobovBandAndInteriorGrowth
import GaloisForLFunctions.BezoutValuationIncidence.CompletePeriodQuadraticFormsSignInvarianceAndTransHorizonSeparation
import GaloisForLFunctions.BezoutValuationIncidence.MultiplicativeWeightsAreDecidedAtThePrimesOnTheBand
import GaloisForLFunctions.RHTower.AdmixturesAndTheShiftedPairLeaveTheWeilCone

/-!
# The Parity Pair and Selectivity Against Shifted-Pair and Beurling Countermodels

This module resolves Topics 4 and 5 of the Research Topics (§7.8) for the Bézout–Valuation
Incidence programme:

1. **The parity pair with Trans-Horizon Incidence Mechanics: complete-period and diagonal Gram
   blindness versus linear prime-readout anti-symmetry (§1):**
   For any damping $\varepsilon > 0$ and cutoff $N \ge 1$, the finite Ramanujan reconstructions
   `dampedFiniteRamanujanRow ε N` and `parityTwinFiniteRamanujanRow ε N` of `pmPowerDampedRealWeight ε`
   and `parityTwinWeight ε` have Selberg coordinates $W_{c_\varepsilon}(q)$ and
   $W_{c'_\varepsilon}(q) = \mu(q) W_{c_\varepsilon}(q)$ on $[1, N]$.
   - Because $|W_{c'_\varepsilon}(q)| = |W_{c_\varepsilon}(q)|$ for all $q \ge 1$, the two rows have
     **identical complete-period mean**, **identical centered and uncentered complete-period
     quadratic forms** (`selbergTotientDiagonalForm`, `sieveVariance`, `bezoutCoprimeQuadraticForm`,
     `sieveSuccessorCovariance`, `sieveSuccessorReserve`, `successorPhaseLoss`,
     `sievePrimitiveEnergy`, `franelGcdQuadraticForm`, `sieveVarianceAboveParity`,
     `TwoLagSieve.periodCovariance` at all lags, `tupleVariance` at all shift tuples), and
     **identical diagonal pronic Gram energies** in $\mathcal G$, $\mathcal G^{\mathrm{ec}}$, and
     $\mathcal G^{\mathrm{mc}}$ (`parityPair_finiteRamanujanRow_completePeriod_and_diagGram_eq`).
   - Because $\Lambda(e)$ is supported on prime powers and $W_{c_\varepsilon}(e)$ is supported on
     squarefree moduli, their product is supported purely on the primes $e = p$, where $\mu(p) = -1$.
     Consequently $\Lambda(e) W_{c'_\varepsilon}(e) = -\Lambda(e) W_{c_\varepsilon}(e)$ for every
     $e \ge 2$ (`vonMangoldt_mul_weightRamanujanCoeff_parityTwin`), so the von Mangoldt pronic
     readouts of the two reconstructions are **exact opposites** at every cutoff $N$ and have
     strictly opposite signs for all $N \ge 2$
     (`vonMangoldtReadout_parityPair_finiteRamanujanRow_eq_neg`,
     `vonMangoldtReadout_parityPair_finiteRamanujanRow_opposite_signs`).

2. **All-damping Vinogradov–Korobov band separation of multiplicative weights and the parity pair (§2):**
   Extending `MultiplicativeWeightsAreDecidedAtThePrimesOnTheBand` from $[1/4, 1/2]$ to
   $[\varepsilon_0, 1/2]$ for **every** damping floor $\varepsilon_0 \in (0, 1/2]$:
   - Every multiplicative weight $f$ with $|f| \le 1$ and $f(p) = -1$ at all primes (Möbius,
     Liouville, etc.) has bounded receiver $E_T(f d^{-\varepsilon}) \le E_f$ uniformly across all
     $T \in \mathbb N$ and all $\varepsilon \in [\varepsilon_0, 1/2]$ on the Vinogradov–Korobov
     band $\varepsilon \ge \frac{1}{2} - \frac{\kappa\sigma(T)}{480\log T}$
     (`exists_receiver_le_on_vinogradovKorobovBand_of_primes_neg_one_of_pos`), whereas every
     nonnegative multiplicative weight with $f(p) = +1$ at primes and the parity twin $c'_\varepsilon$
     grow at least like $c_{\varepsilon_0}(\log(T + 1) - \log 100)$
     (`prime_sign_dichotomy_on_vinogradovKorobovBand_of_pos`).

3. **Selectivity against the shifted pair $\zeta(s - a)\zeta(s + a)$ and Beurling systems (§3):**
   - For the shifted-pair weight $\Lambda_a(n) = \Lambda(n)(n^a + n^{-a})$ of
     $F_a(s) = \zeta(s - a)\zeta(s + a)$, the exact square identity
     $$\Lambda_a(n) - 2\Lambda(n) = \Lambda(n)\bigl(n^{a/2} - n^{-a/2}\bigr)^2 \ge 0$$
     (`shiftedPairVonMangoldt_sub_two_mul_eq_sq`) forces strict pointwise excess
     $\Lambda_a(q) > 2\Lambda(q) > \Lambda(q)$ at every prime power $q \ge 2$ whenever $a \ne 0$
     (`two_mul_vonMangoldt_lt_shiftedPairVonMangoldt_of_isPrimePow`).
   - Consequently, the shifted-pair pronic readout $\mathcal R_{N, a}(c) = \sum_{e=2}^N \Lambda_a(e) Y_{N, c}(e)$
     strictly exceeds $2\mathcal R_N(c)$ for every nonnegative-coordinate row with $Y_{N, c}(2) > 0$
     whenever $a \ne 0$ (`two_mul_vonMangoldtReadout_lt_shiftedPairReadout_of_pos_at_two`), and
     equals $2\mathcal R_N(c)$ if and only if $a = 0$ (`shiftedPairReadout_eq_two_mul_iff_eq_zero`).
   - Packaging the Weil-cone, Ramanujan, and zero-free band selectivity laws
     (`shiftedPair_and_vkBand_selectivity`): $\Lambda_a$ never lies in `WeilPositiveFull`, lies in
     `WeilPositiveDegree 2` iff `RiemannHypothesis ∧ a = 0`, violates the Ramanujan bound for
     $\varepsilon < |a|$, and the ratio of the Vinogradov–Korobov scale $\sigma(x)$ to the sharp
     Beurling de la Vallée Poussin scale $\sqrt{\log x}$ satisfies
     $$\frac{\sigma(x)}{\sqrt{\log x}} = (\log x)^{1/10} (\log\log x)^{-5/3} \longrightarrow +\infty$$
     (`tendsto_vkScale_div_sqrt_log_atTop`).
-/

open Finset Filter Topology RHTower RHTower.Sieve RHTower.WeilSpectral
open ArithmeticFunction GaloisForLFunctions.TransHorizonIncidenceMechanics
open GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Finite-Horizon Ramanujan Reconstructions of the Parity Pair -/

/-- The finite divisor row on `[1, N]` whose Selberg coordinates are `W_{c_ε}(q)`. -/
def dampedFiniteRamanujanRow (ε : ℝ) (N : ℕ) : ℕ → ℝ :=
  RHTower.pmRamanujanResidueCoeff (weightRamanujanCoeff (pmPowerDampedRealWeight ε)) N

/-- The finite divisor row on `[1, N]` whose Selberg coordinates are `W_{c'_ε}(q) = μ(q) W_{c_ε}(q)`. -/
def parityTwinFiniteRamanujanRow (ε : ℝ) (N : ℕ) : ℕ → ℝ :=
  RHTower.pmRamanujanResidueCoeff (weightRamanujanCoeff (parityTwinWeight ε)) N

theorem selbergMultiplesCoord_dampedFiniteRamanujanRow (ε : ℝ) {N q : ℕ} (hq : q ∈ Icc 1 N) :
    selbergMultiplesCoord N (dampedFiniteRamanujanRow ε N) q =
      weightRamanujanCoeff (pmPowerDampedRealWeight ε) q :=
  RHTower.pmRamanujanResidueCoeff_multiples _ (mem_Icc.mp hq).1 (mem_Icc.mp hq).2

theorem selbergMultiplesCoord_parityTwinFiniteRamanujanRow (ε : ℝ) {N q : ℕ} (hq : q ∈ Icc 1 N) :
    selbergMultiplesCoord N (parityTwinFiniteRamanujanRow ε N) q =
      weightRamanujanCoeff (parityTwinWeight ε) q :=
  RHTower.pmRamanujanResidueCoeff_multiples _ (mem_Icc.mp hq).1 (mem_Icc.mp hq).2

theorem sq_selbergMultiplesCoord_parityPair_finiteRamanujanRow {ε : ℝ} (hε : 0 < ε)
    {N q : ℕ} (hq : q ∈ Icc 1 N) :
    (selbergMultiplesCoord N (parityTwinFiniteRamanujanRow ε N) q) ^ 2 =
      (selbergMultiplesCoord N (dampedFiniteRamanujanRow ε N) q) ^ 2 := by
  rw [selbergMultiplesCoord_parityTwinFiniteRamanujanRow ε hq,
    selbergMultiplesCoord_dampedFiniteRamanujanRow ε hq,
    ← sq_abs (weightRamanujanCoeff (parityTwinWeight ε) q),
    abs_weightRamanujanCoeff_parityTwin hε (mem_Icc.mp hq).1, sq_abs]

/-- **Complete-period and diagonal pronic Gram blindness of the parity pair:**
At every cutoff `N ≥ 1` and damping `ε > 0`, the finite Ramanujan reconstructions of `c_ε` and `c'_ε`
have the exact same complete-period mean, the exact same centered and uncentered complete-period
quadratic forms (Selberg totient form, Selberg variance, Bézout coprime form, successor covariance,
successor reserve, phase loss, primitive energy, Franel gcd form, above-parity variance, all-lag
covariances, and all-tuple variances), and the exact same diagonal pronic Gram energies in `𝒢`,
`𝒢^{ec}`, and `𝒢^{mc}`. -/
theorem parityPair_finiteRamanujanRow_completePeriod_and_diagGram_eq
    {ε : ℝ} (hε : 0 < ε) {N : ℕ} (hN : 1 ≤ N) :
    let c₁ := dampedFiniteRamanujanRow ε N
    let c₂ := parityTwinFiniteRamanujanRow ε N
    finiteHarmonicSum N c₂ = finiteHarmonicSum N c₁ ∧
      selbergTotientDiagonalForm N c₂ = selbergTotientDiagonalForm N c₁ ∧
      sieveVariance N c₂ = sieveVariance N c₁ ∧
      bezoutCoprimeQuadraticForm N c₂ = bezoutCoprimeQuadraticForm N c₁ ∧
      sieveSuccessorCovariance N c₂ = sieveSuccessorCovariance N c₁ ∧
      sieveSuccessorReserve N c₂ = sieveSuccessorReserve N c₁ ∧
      successorPhaseLoss N c₂ = successorPhaseLoss N c₁ ∧
      sievePrimitiveEnergy N c₂ = sievePrimitiveEnergy N c₁ ∧
      franelGcdQuadraticForm N c₂ = franelGcdQuadraticForm N c₁ ∧
      sieveVarianceAboveParity N c₂ = sieveVarianceAboveParity N c₁ ∧
      (∀ h : ℕ, TwoLagSieve.periodCovariance N c₂ h = TwoLagSieve.periodCovariance N c₁ h) ∧
      (∀ H : Finset ℕ, tupleVariance N c₂ H = tupleVariance N c₁ H) ∧
      (∑ e ∈ Icc 2 N, (selbergMultiplesCoord N c₂ e) ^ 2 * pmRamanujanGram e e =
        ∑ e ∈ Icc 2 N, (selbergMultiplesCoord N c₁ e) ^ 2 * pmRamanujanGram e e) ∧
      (∑ e ∈ Icc 2 N, (selbergMultiplesCoord N c₂ e) ^ 2 * pmRamanujanEnergyCenteredGram e e =
        ∑ e ∈ Icc 2 N, (selbergMultiplesCoord N c₁ e) ^ 2 * pmRamanujanEnergyCenteredGram e e) ∧
      (∑ e ∈ Icc 2 N, (selbergMultiplesCoord N c₂ e) ^ 2 * pmRamanujanMeanCenteredGram e e =
        ∑ e ∈ Icc 2 N, (selbergMultiplesCoord N c₁ e) ^ 2 * pmRamanujanMeanCenteredGram e e) := by
  dsimp only
  have hsq1 : ∀ q ∈ Icc 1 N,
      (selbergMultiplesCoord N (parityTwinFiniteRamanujanRow ε N) q) ^ 2 =
        (selbergMultiplesCoord N (dampedFiniteRamanujanRow ε N) q) ^ 2 :=
    fun q hq => sq_selbergMultiplesCoord_parityPair_finiteRamanujanRow hε hq
  have hsq2 : ∀ q ∈ Icc 2 N,
      (selbergMultiplesCoord N (parityTwinFiniteRamanujanRow ε N) q) ^ 2 =
        (selbergMultiplesCoord N (dampedFiniteRamanujanRow ε N) q) ^ 2 :=
    fun q hq => hsq1 q (mem_Icc.mpr ⟨by have := (mem_Icc.mp hq).1; omega, (mem_Icc.mp hq).2⟩)
  obtain ⟨hV, hC, hR, hL, hE, hA, hcov, htup⟩ := completePeriodCenteredForms_eq_of_sq_eq hN hsq2
  obtain ⟨hSel, hBez, hFr⟩ := completePeriodUncenteredForms_eq_of_sq_eq N hsq1
  have hmean : finiteHarmonicSum N (parityTwinFiniteRamanujanRow ε N) =
      finiteHarmonicSum N (dampedFiniteRamanujanRow ε N) := by
    rw [← selbergMultiplesCoord_one_eq_finiteHarmonicSum,
      ← selbergMultiplesCoord_one_eq_finiteHarmonicSum,
      selbergMultiplesCoord_parityTwinFiniteRamanujanRow ε (mem_Icc.mpr ⟨le_rfl, hN⟩),
      selbergMultiplesCoord_dampedFiniteRamanujanRow ε (mem_Icc.mpr ⟨le_rfl, hN⟩),
      weightRamanujanCoeff_parityTwin hε 1, weightRamanujanCoeff_pmPowerDamped hε one_pos,
      ArithmeticFunction.moebius_apply_one, Int.cast_one, one_mul]
  refine ⟨hmean, hSel, hV, hBez, hC, hR, hL, hE, hFr, hA, hcov, htup, ?_, ?_, ?_⟩
  · exact sum_congr rfl fun e he => by rw [hsq2 e he]
  · exact sum_congr rfl fun e he => by rw [hsq2 e he]
  · exact sum_congr rfl fun e he => by rw [hsq2 e he]

/-- **Prime-power vs. squarefree intersection law for the parity pair:**
For every `e ≥ 2` and `ε > 0`, `Λ(e) W_{c'_ε}(e) = -Λ(e) W_{c_ε}(e)`. -/
theorem vonMangoldt_mul_weightRamanujanCoeff_parityTwin {ε : ℝ} (hε : 0 < ε) {e : ℕ}
    (he : 2 ≤ e) :
    vonMangoldt e * weightRamanujanCoeff (parityTwinWeight ε) e =
      -(vonMangoldt e * weightRamanujanCoeff (pmPowerDampedRealWeight ε) e) := by
  have he0 : 0 < e := by omega
  rw [weightRamanujanCoeff_parityTwin hε e, weightRamanujanCoeff_pmPowerDamped hε he0]
  by_cases hpp : IsPrimePow e
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff e).mp hpp
    rcases eq_or_ne k 1 with rfl | hk1
    · rw [pow_one, ArithmeticFunction.moebius_apply_prime hp]
      push_cast; ring
    · have hnsq : ¬ Squarefree (p ^ k) := by
        rw [Nat.squarefree_pow_iff hp.ne_one hk.ne']
        omega
      rw [dampedRamanujanCoeff_eq_closed hε, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsq]
      simp
  · rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp]
    ring

/-- **Exact anti-symmetry of the von Mangoldt pronic readout for the parity pair:**
At every finite cutoff `N`, the von Mangoldt readouts of `parityTwinFiniteRamanujanRow ε N` and
`dampedFiniteRamanujanRow ε N` are exact negatives of each other. -/
theorem vonMangoldtReadout_parityPair_finiteRamanujanRow_eq_neg {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    vonMangoldtReadout N (parityTwinFiniteRamanujanRow ε N) =
      -vonMangoldtReadout N (dampedFiniteRamanujanRow ε N) := by
  unfold vonMangoldtReadout
  rw [← sum_neg_distrib]
  refine sum_congr rfl fun e he => ?_
  have he1 : e ∈ Icc 1 N := mem_Icc.mpr ⟨by have := (mem_Icc.mp he).1; omega, (mem_Icc.mp he).2⟩
  rw [selbergMultiplesCoord_parityTwinFiniteRamanujanRow ε he1,
    selbergMultiplesCoord_dampedFiniteRamanujanRow ε he1,
    vonMangoldt_mul_weightRamanujanCoeff_parityTwin hε (mem_Icc.mp he).1]

/-- **Strict sign opposition of the von Mangoldt readouts of the parity pair:**
For every cutoff `N ≥ 2` and damping `ε > 0`,
`vonMangoldtReadout N (dampedFiniteRamanujanRow ε N) < 0 < vonMangoldtReadout N (parityTwinFiniteRamanujanRow ε N)`. -/
theorem vonMangoldtReadout_parityPair_finiteRamanujanRow_opposite_signs {ε : ℝ} (hε : 0 < ε)
    {N : ℕ} (hN : 2 ≤ N) :
    vonMangoldtReadout N (dampedFiniteRamanujanRow ε N) < 0 ∧
      0 < vonMangoldtReadout N (parityTwinFiniteRamanujanRow ε N) := by
  have hpos : 0 < vonMangoldtReadout N (parityTwinFiniteRamanujanRow ε N) := by
    unfold vonMangoldtReadout
    have hnn : ∀ e ∈ Icc 2 N,
        0 ≤ vonMangoldt e * selbergMultiplesCoord N (parityTwinFiniteRamanujanRow ε N) e := by
      intro e he
      have he1 : e ∈ Icc 1 N := mem_Icc.mpr ⟨by have := (mem_Icc.mp he).1; omega, (mem_Icc.mp he).2⟩
      rw [selbergMultiplesCoord_parityTwinFiniteRamanujanRow ε he1,
        weightRamanujanCoeff_parityTwin hε e, dampedRamanujanCoeff_eq_closed hε e]
      have hρ : 0 < dampedDensity ε := RHTower.pmPowerDampedDivisorDensity_re_pos hε
      have hD : 0 < RHTower.pmPowerDampedRamanujanDenominator ε e :=
        RHTower.pmPowerDampedRamanujanDenominator_pos hε e
      have hmu : 0 ≤ (moebius e : ℝ) * (moebius e : ℝ) := mul_self_nonneg _
      have hw : 0 ≤ (moebius e : ℝ) * (dampedDensity ε * (moebius e : ℝ) /
          RHTower.pmPowerDampedRamanujanDenominator ε e) := by
        rw [show (moebius e : ℝ) * (dampedDensity ε * (moebius e : ℝ) /
            RHTower.pmPowerDampedRamanujanDenominator ε e) =
          dampedDensity ε * ((moebius e : ℝ) * (moebius e : ℝ)) /
            RHTower.pmPowerDampedRamanujanDenominator ε e by ring]
        positivity
      exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg hw
    have h2 : 0 < vonMangoldt 2 * selbergMultiplesCoord N (parityTwinFiniteRamanujanRow ε N) 2 := by
      rw [selbergMultiplesCoord_parityTwinFiniteRamanujanRow ε (mem_Icc.mpr ⟨by omega, hN⟩),
        weightRamanujanCoeff_parityTwin hε 2, dampedRamanujanCoeff_eq_closed hε 2,
        ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two,
        ArithmeticFunction.moebius_apply_prime Nat.prime_two]
      have hρ : 0 < dampedDensity ε := RHTower.pmPowerDampedDivisorDensity_re_pos hε
      have hD : 0 < RHTower.pmPowerDampedRamanujanDenominator ε 2 :=
        RHTower.pmPowerDampedRamanujanDenominator_pos hε 2
      have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
      push_cast
      rw [show (-1 : ℝ) * (dampedDensity ε * -1 / RHTower.pmPowerDampedRamanujanDenominator ε 2) =
        dampedDensity ε / RHTower.pmPowerDampedRamanujanDenominator ε 2 by ring]
      positivity
    exact lt_of_lt_of_le h2 (single_le_sum hnn (mem_Icc.mpr ⟨le_rfl, hN⟩))
  refine ⟨?_, hpos⟩
  have hneg := vonMangoldtReadout_parityPair_finiteRamanujanRow_eq_neg hε N
  linarith

/-! ## §2. All-Damping Vinogradov–Korobov Band Separation for Multiplicative Weights -/

/-- The critical Wiener mass of `(f ⋆ 1)(q) q^{-ε}` decreases in `ε` above any positive floor `ε₀ > 0`. -/
theorem criticalMass_le_of_pos {f : ArithmeticFunction ℝ} (hf : f.IsMultiplicative)
    (hfp : ∀ p : ℕ, p.Prime → f p = -1) (hbd : ∀ n, |f n| ≤ 1)
    {ε₀ ε : ℝ} (hε₀ : 0 < ε₀) (hε_ge : ε₀ ≤ ε) :
    ∑' q : ℕ, |dampedSignWeight ⇑(f * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) ε q| *
        (q : ℝ) ^ (-(1 / 2 : ℝ)) ≤
      ∑' q : ℕ, |dampedSignWeight ⇑(f * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) ε₀ q| *
        (q : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hε : 0 < ε := hε₀.trans_le hε_ge
  have h0 := criticalWiener_mul_zeta hf hfp hbd hε₀
  refine (criticalWiener_mul_zeta hf hfp hbd hε).tsum_le_tsum (fun q => ?_) h0
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (Nat.cast_nonneg q) _)
  unfold dampedSignWeight
  rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg q) _),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg q) _)]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp [Real.zero_rpow (show -ε ≠ 0 by linarith), Real.zero_rpow (show -ε₀ ≠ 0 by linarith)]
  · exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hq) (by linarith)

/-- **All-damping Vinogradov–Korobov band bound for multiplicative weights with `f(p) = -1`:**
For any damping floor `ε₀ > 0` and any multiplicative `f` with `|f| ≤ 1` and `f(p) = -1` at all
primes, there exists `E` such that `E_T(f d^{-ε}) ≤ E` uniformly for all `T` and all `ε ∈ [ε₀, 1/2]`
on the Vinogradov–Korobov band `ε ≥ 1/2 - κ σ(T)/(480 log T)`. -/
theorem exists_receiver_le_on_vinogradovKorobovBand_of_primes_neg_one_of_pos
    {f : ArithmeticFunction ℝ} (hf : f.IsMultiplicative)
    (hfp : ∀ p : ℕ, p.Prime → f p = -1) (hbd : ∀ n, |f n| ≤ 1)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ E : ℝ, ∀ (T : ℕ) (ε : ℝ), ε₀ ≤ ε → ε ≤ 1 / 2 →
      1 / 2 - vkKappa * vkScale T / (480 * Real.log T) ≤ ε →
        weightPronicEnergy (dampedSignWeight ⇑f ε) (∑' d : ℕ, dampedSignWeight ⇑f ε d / d) T ≤ E := by
  obtain ⟨E, _, hE⟩ := exists_receiver_le_on_vinogradovKorobovBand_of_pos hε₀
  set Gq := ∑' q : ℕ,
    |dampedSignWeight ⇑(f * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) ε₀ q| *
      (q : ℝ) ^ (-(1 / 2 : ℝ))
  have hG0 : 0 ≤ Gq := tsum_nonneg fun q =>
    mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg q) _)
  refine ⟨(Gq * Real.sqrt (max E 0) + (Real.sqrt 2 + 1) * Gq) ^ 2,
    fun T ε hε_ge hε2 hband => ?_⟩
  have hε : 0 < ε := hε₀.trans_le hε_ge
  set g := dampedSignWeight ⇑(f * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) ε
  set c := pmPowerDampedRealWeight ε
  have hg := criticalWiener_mul_zeta hf hfp hbd hε
  have hc := summable_abs_pmPowerDamped_div hε
  have hconv : dampedSignWeight ⇑f ε = RHTower.dirichletConv g c :=
    funext (dampedMultiplicative_eq_dirichletConv f ε)
  have hmc : ∑' d : ℕ, c d / d = dampedDensity ε := (hasSum_pmPowerDampedRealWeight_div hε).tsum_eq
  have hmean : ∑' d : ℕ, dampedSignWeight ⇑f ε d / d = (∑' q : ℕ, g q / q) * dampedDensity ε := by
    rw [hconv, ← hmc]
    exact (hasSum_dirichletConv_div hg.summable_abs_div.of_abs.hasSum hc.of_abs.hasSum
      hg.summable_abs_div hc).tsum_eq
  have hGε := criticalMass_le_of_pos hf hfp hbd hε₀ hε_ge
  have hρ0 : 0 < dampedDensity ε := RHTower.pmPowerDampedDivisorDensity_re_pos hε
  have hρ1 := dampedDensity_le_one hε
  have hEc : pronicNorm (weightCenteredPrefix c (dampedDensity ε)) T ≤ Real.sqrt (max E 0) := by
    rw [← Real.sqrt_sq (pronicNorm_nonneg _ T), ← weightPronicEnergy_eq_sq_pronicNorm]
    refine Real.sqrt_le_sqrt ((?_ : _ ≤ E).trans (le_max_left _ _))
    rw [weightPronicEnergy_pmPowerDamped]
    exact hE T ε hε_ge hε2 hband
  have hlaw := pronicNorm_dirichletConv_le (c := c) hg (dampedDensity ε) T
  rw [hmean, weightPronicEnergy_eq_sq_pronicNorm, hconv]
  refine pow_le_pow_left₀ (pronicNorm_nonneg _ T) (hlaw.trans ?_) 2
  rw [abs_of_pos hρ0]
  have hs2 : 0 ≤ Real.sqrt 2 + 1 := by positivity
  calc (∑' q : ℕ, |g q| * (q : ℝ) ^ (-(1 / 2 : ℝ))) *
        pronicNorm (weightCenteredPrefix c (dampedDensity ε)) T +
        dampedDensity ε * ((Real.sqrt 2 + 1) * ∑' q : ℕ, |g q| * (q : ℝ) ^ (-(1 / 2 : ℝ)))
      ≤ Gq * Real.sqrt (max E 0) + 1 * ((Real.sqrt 2 + 1) * Gq) := by
        refine add_le_add (mul_le_mul hGε hEc (pronicNorm_nonneg _ T) hG0) ?_
        exact mul_le_mul hρ1 (mul_le_mul_of_nonneg_left hGε hs2) (by positivity) zero_le_one
    _ = Gq * Real.sqrt (max E 0) + (Real.sqrt 2 + 1) * Gq := by ring

/-- **Unified prime-sign dichotomy on the Vinogradov–Korobov band across `[ε₀, 1/2]`:**
For every `ε₀ ∈ (0, 1/2]`, multiplicative weights with `f(p) = -1` are uniformly bounded on the
band while nonnegative multiplicative weights with `f(p) = +1` grow at least logarithmically. -/
theorem prime_sign_dichotomy_on_vinogradovKorobovBand_of_pos
    {f_neg f_pos : ArithmeticFunction ℝ}
    (hf_neg : f_neg.IsMultiplicative) (hfp_neg : ∀ p : ℕ, p.Prime → f_neg p = -1)
    (hbd_neg : ∀ n, |f_neg n| ≤ 1)
    (hf_pos : f_pos.IsMultiplicative) (hfp_pos : ∀ p : ℕ, p.Prime → f_pos p = 1)
    (h0_pos : ∀ n, 0 ≤ f_pos n) (hbd_pos : ∀ n, |f_pos n| ≤ 1)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ E : ℝ, ∀ (T : ℕ) (ε : ℝ), ε₀ ≤ ε → ε ≤ 1 / 2 →
      1 / 2 - vkKappa * vkScale T / (480 * Real.log T) ≤ ε →
        weightPronicEnergy (dampedSignWeight ⇑f_neg ε)
          (∑' d : ℕ, dampedSignWeight ⇑f_neg ε d / d) T ≤ E ∧
        (Real.log ((T : ℝ) + 1) - Real.log 100) / 1024 ≤
          weightPronicEnergy (dampedSignWeight ⇑f_pos ε)
            (∑' d : ℕ, dampedSignWeight ⇑f_pos ε d / d) T := by
  obtain ⟨E, hE⟩ := exists_receiver_le_on_vinogradovKorobovBand_of_primes_neg_one_of_pos
    hf_neg hfp_neg hbd_neg hε₀
  exact ⟨E, fun T ε hε_ge hε2 hband =>
    ⟨hE T ε hε_ge hε2 hband,
      receiver_ge_log_of_primes_one hf_pos hfp_pos h0_pos hbd_pos (hε₀.trans_le hε_ge) hε2 T⟩⟩

/-! ## §3. Selectivity Against the Shifted Pair `ζ(s - a)ζ(s + a)` and Beurling Systems -/

/-- **Exact quadratic excess of the shifted-pair von Mangoldt weight:**
For every `a ∈ ℝ` and `n ≥ 1`, `Λ_a(n) - 2 Λ(n) = Λ(n) (n^{a/2} - n^{-a/2})² ≥ 0`. -/
theorem shiftedPairVonMangoldt_sub_two_mul_eq_sq (a : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    shiftedPairVonMangoldt a n - 2 * vonMangoldt n =
      vonMangoldt n * ((n : ℝ) ^ (a / 2) - (n : ℝ) ^ (-(a / 2))) ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold shiftedPairVonMangoldt
  have hpos : ((n : ℝ) ^ (a / 2)) ^ (2 : ℕ) = (n : ℝ) ^ a := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; ring_nf
  have hneg : ((n : ℝ) ^ (-(a / 2))) ^ (2 : ℕ) = (n : ℝ) ^ (-a) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; ring_nf
  have hprod : (n : ℝ) ^ (a / 2) * (n : ℝ) ^ (-(a / 2)) = 1 := by
    rw [← Real.rpow_add hn0, add_neg_cancel, Real.rpow_zero]
  calc vonMangoldt n * ((n : ℝ) ^ a + (n : ℝ) ^ (-a)) - 2 * vonMangoldt n
      = vonMangoldt n * (((n : ℝ) ^ (a / 2)) ^ (2 : ℕ) + ((n : ℝ) ^ (-(a / 2))) ^ (2 : ℕ) -
          2 * ((n : ℝ) ^ (a / 2) * (n : ℝ) ^ (-(a / 2)))) := by
        rw [hpos, hneg, hprod]; ring
    _ = vonMangoldt n * ((n : ℝ) ^ (a / 2) - (n : ℝ) ^ (-(a / 2))) ^ 2 := by ring

/-- **Strict excess of `Λ_a(q)` at every prime power for `a ≠ 0`:**
For any prime power `q` and `a ≠ 0`, `2 Λ(q) < Λ_a(q)`. -/
theorem two_mul_vonMangoldt_lt_shiftedPairVonMangoldt_of_isPrimePow
    {a : ℝ} (ha : a ≠ 0) {q : ℕ} (hq : IsPrimePow q) :
    2 * vonMangoldt q < shiftedPairVonMangoldt a q := by
  have hq2 : 2 ≤ q := hq.two_le
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  have hΛ : 0 < vonMangoldt q :=
    lt_of_le_of_ne ArithmeticFunction.vonMangoldt_nonneg
      (Ne.symm (ArithmeticFunction.vonMangoldt_ne_zero_iff.mpr hq))
  have hne : (q : ℝ) ^ (a / 2) - (q : ℝ) ^ (-(a / 2)) ≠ 0 := by
    intro hsub
    have heq : (q : ℝ) ^ (a / 2) = (q : ℝ) ^ (-(a / 2)) := sub_eq_zero.mp hsub
    have hlog := congrArg Real.log heq
    rw [Real.log_rpow hq0, Real.log_rpow hq0] at hlog
    have hlogq : Real.log q ≠ 0 := (Real.log_pos hq1).ne'
    have : a / 2 = -(a / 2) := mul_right_cancel₀ hlogq hlog
    exact ha (by linarith)
  have hsq : 0 < ((q : ℝ) ^ (a / 2) - (q : ℝ) ^ (-(a / 2))) ^ 2 := sq_pos_of_ne_zero hne
  have hid := shiftedPairVonMangoldt_sub_two_mul_eq_sq a (by omega : 1 ≤ q)
  linarith [mul_pos hΛ hsq]

/-- The shifted-pair pronic readout `R_{N, a}(c) = Σ_{e=2}^N Λ_a(e) Y_{N, c}(e)`. -/
def shiftedPairReadout (N : ℕ) (a : ℝ) (c : ℕ → ℝ) : ℝ :=
  ∑ e ∈ Icc 2 N, shiftedPairVonMangoldt a e * selbergMultiplesCoord N c e

theorem shiftedPairReadout_zero (N : ℕ) (c : ℕ → ℝ) :
    shiftedPairReadout N 0 c = 2 * vonMangoldtReadout N c := by
  unfold shiftedPairReadout vonMangoldtReadout
  rw [mul_sum]
  refine sum_congr rfl fun e _ => ?_
  simp only [shiftedPairVonMangoldt, neg_zero, Real.rpow_zero]
  ring

/-- **Shifted-pair readout decomposition:**
For any row `c`, `R_{N, a}(c) - 2 R_N(c) = Σ_{e=2}^N Λ(e) (e^{a/2} - e^{-a/2})² Y_{N, c}(e)`. -/
theorem shiftedPairReadout_sub_two_mul_vonMangoldtReadout (N : ℕ) (a : ℝ) (c : ℕ → ℝ) :
    shiftedPairReadout N a c - 2 * vonMangoldtReadout N c =
      ∑ e ∈ Icc 2 N,
        vonMangoldt e * ((e : ℝ) ^ (a / 2) - (e : ℝ) ^ (-(a / 2))) ^ 2 *
          selbergMultiplesCoord N c e := by
  unfold shiftedPairReadout vonMangoldtReadout
  rw [mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun e he => ?_
  have he1 : 1 ≤ e := by have := (mem_Icc.mp he).1; omega
  rw [← shiftedPairVonMangoldt_sub_two_mul_eq_sq a he1]
  ring

/-- **Strict separation of the shifted-pair readout for nonnegative Selberg rows:**
If `N ≥ 2`, `Y_{N, c}(e) ≥ 0` on `[2, N]`, and `Y_{N, c}(2) > 0`, then for every `a : ℝ`,
`2 R_N(c) ≤ R_{N, a}(c)`, with equality if and only if `a = 0`. -/
theorem shiftedPairReadout_eq_two_mul_iff_eq_zero {N : ℕ} (hN : 2 ≤ N) {c : ℕ → ℝ}
    (hY : ∀ e ∈ Icc 2 N, 0 ≤ selbergMultiplesCoord N c e)
    (hY2 : 0 < selbergMultiplesCoord N c 2) (a : ℝ) :
    2 * vonMangoldtReadout N c ≤ shiftedPairReadout N a c ∧
      (shiftedPairReadout N a c = 2 * vonMangoldtReadout N c ↔ a = 0) := by
  have hdiff := shiftedPairReadout_sub_two_mul_vonMangoldtReadout N a c
  have hnn : ∀ e ∈ Icc 2 N,
      0 ≤ vonMangoldt e * ((e : ℝ) ^ (a / 2) - (e : ℝ) ^ (-(a / 2))) ^ 2 *
        selbergMultiplesCoord N c e :=
    fun e he => mul_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (sq_nonneg _)) (hY e he)
  refine ⟨by linarith [sum_nonneg hnn], ⟨fun heq => ?_, fun ha => by rw [ha, shiftedPairReadout_zero]⟩⟩
  by_contra ha
  have hlt2 := two_mul_vonMangoldt_lt_shiftedPairVonMangoldt_of_isPrimePow ha Nat.prime_two.isPrimePow
  have hid2 := shiftedPairVonMangoldt_sub_two_mul_eq_sq a (by norm_num : 1 ≤ 2)
  have hpos2 : 0 < vonMangoldt 2 * ((2 : ℝ) ^ (a / 2) - (2 : ℝ) ^ (-(a / 2))) ^ 2 *
      selbergMultiplesCoord N c 2 := mul_pos (by linarith) hY2
  have hle := single_le_sum hnn (mem_Icc.mpr ⟨le_rfl, hN⟩)
  linarith

/-- **Selectivity of the Vinogradov–Korobov scale over the Beurling de la Vallée Poussin scale:**
As `x → ∞`, the ratio `vkScale x / √(log x) = (log x)^{1/10} (log log x)^{-5/3}` tends to `+∞`. -/
theorem tendsto_vkScale_div_sqrt_log_atTop :
    Tendsto (fun x : ℝ => vkScale x / Real.sqrt (Real.log x)) atTop atTop := by
  have hL : Tendsto (fun x : ℝ => Real.log x) atTop atTop := Real.tendsto_log_atTop
  have hY : Tendsto (fun x : ℝ => Real.log x ^ ((1 : ℝ) / 20)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp hL
  have hlog_div : Tendsto (fun y : ℝ => Real.log y / y) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hcomp := ((hlog_div.comp hY).pow 2).const_mul 400
  simp only [ zero_pow (by norm_num : 2 ≠ 0), mul_zero] at hcomp
  set invRatio : ℝ → ℝ := fun x => Real.sqrt (Real.log x) / vkScale x
  have hinv_zero : Tendsto invRatio atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ hcomp
    · filter_upwards [hL.eventually_gt_atTop 1] with x hx
      have h1 : 0 ≤ Real.sqrt (Real.log x) := Real.sqrt_nonneg _
      have h2 : 0 ≤ vkScale x := vkScale_nonneg hx.le
      exact div_nonneg h1 h2
    · filter_upwards [hL.eventually_gt_atTop (Real.exp 1)] with x hx
      have hL1 : 1 < Real.log x := lt_trans (by linarith [Real.one_lt_exp_iff.mpr one_pos]) hx
      have hL0 : 0 < Real.log x := by linarith
      have hLL1 : 1 < Real.log (Real.log x) := by
        rw [← Real.log_exp 1]
        exact Real.log_lt_log (Real.exp_pos 1) hx
      have hLL0 : 0 < Real.log (Real.log x) := by linarith
      simp only [invRatio, Function.comp_apply, vkScale]
      rw [Real.sqrt_eq_rpow]
      have hpow_le : Real.log (Real.log x) ^ ((5 : ℝ) / 3) ≤ Real.log (Real.log x) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hLL1.le (by norm_num)
      have hlog_rpow : Real.log (Real.log x ^ ((1 : ℝ) / 20)) = 1 / 20 * Real.log (Real.log x) :=
        Real.log_rpow hL0 (1 / 20)
      have hrpow_sq : (Real.log x ^ ((1 : ℝ) / 20)) ^ (2 : ℕ) = Real.log x ^ ((1 : ℝ) / 10) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; ring_nf
      have hden : Real.log x ^ ((1 : ℝ) / 2) /
          (Real.log x ^ ((3 : ℝ) / 5) * Real.log (Real.log x) ^ (-(5 / 3 : ℝ))) =
          Real.log (Real.log x) ^ ((5 : ℝ) / 3) / Real.log x ^ ((1 : ℝ) / 10) := by
        rw [← div_div, ← Real.rpow_sub hL0, show (1 : ℝ) / 2 - 3 / 5 = -(1 / 10) by norm_num,
          Real.rpow_neg hL0.le, Real.rpow_neg hLL0.le]
        field_simp
      rw [hden, hlog_rpow, div_pow, hrpow_sq]
      calc Real.log (Real.log x) ^ ((5 : ℝ) / 3) / Real.log x ^ ((1 : ℝ) / 10)
          ≤ Real.log (Real.log x) ^ (2 : ℝ) / Real.log x ^ ((1 : ℝ) / 10) :=
            div_le_div_of_nonneg_right hpow_le (Real.rpow_nonneg hL0.le _)
        _ = 400 * ((1 / 20 * Real.log (Real.log x)) ^ 2 / Real.log x ^ ((1 : ℝ) / 10)) := by
            rw [Real.rpow_two]; ring
  have hinv_pos : ∀ᶠ x : ℝ in atTop, 0 < invRatio x := by
    filter_upwards [(Real.tendsto_log_atTop.comp hL).eventually_gt_atTop 0,
      hL.eventually_gt_atTop 0] with x hLL0 hL0
    simp only [invRatio, vkScale]
    exact div_pos (Real.sqrt_pos.mpr hL0)
      (mul_pos (Real.rpow_pos_of_pos hL0 _) (Real.rpow_pos_of_pos hLL0 _))
  have ht := Tendsto.inv_tendsto_nhdsGT_zero (tendsto_nhdsWithin_iff.mpr ⟨hinv_zero, hinv_pos⟩)
  refine ht.congr' (Eventually.of_forall fun x => ?_)
  change (Real.sqrt (Real.log x) / vkScale x)⁻¹ = _
  exact inv_div (Real.sqrt (Real.log x)) (vkScale x)

/-- **Unified selectivity theorem against shifted-pair and Beurling countermodels:**
1. For every shift `a`, `shiftedPairVonMangoldt a` lies outside `WeilPositiveFull`.
2. `shiftedPairVonMangoldt a` lies in `WeilPositiveDegree 2` iff `RiemannHypothesis ∧ a = 0`.
3. For `a ≠ 0` and `ε < |a|`, `shiftedPairCoeff a` violates the Ramanujan bound `O(n^ε)`.
4. The Vinogradov–Korobov scale `vkScale x` exceeds the Beurling de la Vallée Poussin scale
   `√(log x)` by an unbounded factor `vkScale x / √(log x) → +∞`. -/
theorem shiftedPair_and_vkBand_selectivity :
    (∀ a : ℝ, ¬ WeilPositiveFull (shiftedPairVonMangoldt a)) ∧
      (∀ a : ℝ, WeilPositiveDegree 2 (shiftedPairVonMangoldt a) ↔ RiemannHypothesis ∧ a = 0) ∧
      (∀ a ε : ℝ, ε < |a| → ¬ ∃ C : ℝ, ∀ n : ℕ, n ≠ 0 → shiftedPairCoeff a n ≤ C * (n : ℝ) ^ ε) ∧
      Tendsto (fun x : ℝ => vkScale x / Real.sqrt (Real.log x)) atTop atTop :=
  ⟨not_weilPositiveFull_shiftedPairVonMangoldt,
    weilPositiveDegree_two_shiftedPairVonMangoldt_iff,
    fun _ _ hε => not_ramanujan_shiftedPairCoeff hε,
    tendsto_vkScale_div_sqrt_log_atTop⟩

#print axioms parityPair_finiteRamanujanRow_completePeriod_and_diagGram_eq
#print axioms vonMangoldt_mul_weightRamanujanCoeff_parityTwin
#print axioms vonMangoldtReadout_parityPair_finiteRamanujanRow_eq_neg
#print axioms vonMangoldtReadout_parityPair_finiteRamanujanRow_opposite_signs
#print axioms criticalMass_le_of_pos
#print axioms exists_receiver_le_on_vinogradovKorobovBand_of_primes_neg_one_of_pos
#print axioms prime_sign_dichotomy_on_vinogradovKorobovBand_of_pos
#print axioms shiftedPairVonMangoldt_sub_two_mul_eq_sq
#print axioms two_mul_vonMangoldt_lt_shiftedPairVonMangoldt_of_isPrimePow
#print axioms shiftedPairReadout_sub_two_mul_vonMangoldtReadout
#print axioms shiftedPairReadout_eq_two_mul_iff_eq_zero
#print axioms tendsto_vkScale_div_sqrt_log_atTop
#print axioms shiftedPair_and_vkBand_selectivity

end

end GaloisForLFunctions.BezoutValuationIncidence
