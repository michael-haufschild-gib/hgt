import GaloisForLFunctions.BezoutValuationIncidence.DedekindPsiJordanTotientAndFiveFormSpectralSynthesis
import GaloisForLFunctions.BezoutValuationIncidence.SharpPrimitiveEnergySuccessorFrontier
import GaloisForLFunctions.BezoutValuationIncidence.MomentSignVisibilityAndZeroProductRelations
import GaloisForLFunctions.BezoutValuationIncidence.TupleStructureFactorsAtSquarefreeModuli
import GaloisForLFunctions.BezoutValuationIncidence.VonMangoldtReadoutFormOfTheBaezDuarteCriterion
import GaloisForLFunctions.BezoutValuationIncidence.UniformLagWindowCovarianceAtQuadraticOrder
import GaloisForLFunctions.BezoutValuationIncidence.RenormalizedMobiusDefectAndFirstOctaveCancellation

/-!
# Complete-period quadratic forms: Selberg coordinate parity invariance and trans-horizon separation

Every complete-period quadratic form of the finite divisor-sieve theory is simultaneously
diagonalized in the Selberg multiples coordinates
`Y_{N,c}(q) = selbergMultiplesCoord N c q = ∑_{d ≤ N, q ∣ d} c(d)/d`:

* Centered complete-period quadratic forms (`sieveVariance`, `sieveSuccessorCovariance`,
  `sieveSuccessorReserve`, `successorPhaseLoss`, `sievePrimitiveEnergy`,
  `sieveVarianceAboveParity`, `TwoLagSieve.periodCovariance N c h` at every lag `h` including the
  two-lag covariances `h = 1, 2`, and `tupleVariance N c H` for every shift tuple `H`) depend only
  on the non-constant squared coordinates `(Y_{N,c}(2)², …, Y_{N,c}(N)²)`.
* Uncentered complete-period quadratic forms (`selbergTotientDiagonalForm`,
  `bezoutCoprimeQuadraticForm`, `franelGcdQuadraticForm`, and `SieveMoments.translatedMoment N c v`
  for `v : Fin 2 → ℕ`) depend only on the full vector of squared coordinates
  `(Y_{N,c}(1)², …, Y_{N,c}(N)²)`.

Consequently:

1. **Universal `(ℤ/2ℤ)^N` sign-character invariance (`completePeriodCenteredForms_eq_of_sq_eq`,
   `completePeriodQuadraticForms_scaledSelbergRow`):**
   Every complete-period quadratic form of the sieve theory is an even function of each Selberg
   coordinate individually, hence invariant under `scaledSelbergRow N c ε` for every sign pattern
   `ε : ℕ → ℝ` with `ε(q)² = 1`.
2. **Bidirectional orbit characterization (`sq_selbergMultiplesCoord_eq_iff_periodCovariance_eq`,
   `exists_sign_character_scaledSelbergRow_iff`):**
   Conversely, by lag-spectrum Möbius inversion (`lagSpectrumReadout_periodCovariance`), two rows
   with the same complete-period mean have the same complete-period lag covariances on `1, …, N`
   (or the same complete-period quadratic bundle) **if and only if** they lie in the same
   `(ℤ/2ℤ)^{N-1}` sign-character orbit `c₂ = scaledSelbergRow N c₁ ε` on `[1, N]`.
3. **Trans-horizon linearity and single-mode flip formulas
   (`sieveSeq_scaledSelbergRow_singleModeSignFlip_sub`,
   `sievePrefixDiscrepancy_scaledSelbergRow_singleModeSignFlip_sub`,
   `vonMangoldtReadout_scaledSelbergRow_singleModeSignFlip_sub`):**
   The pointwise response `sieveSeq N c k`, the finite-prefix discrepancy
   `sievePrefixDiscrepancy N M c`, and the von Mangoldt pronic readout `vonMangoldtReadout N c`
   are linear in the signed Selberg coordinates `Y_{N,c}(q)`. Flipping a single coordinate `q₀`
   via `singleModeSignFlip q₀` shifts `sieveSeq N c k` by `-2 Y_{N,c}(q₀) c_{q₀}(k)`, shifts
   `sievePrefixDiscrepancy N M c` by `-2 Re(R_{q₀}(M)) Y_{N,c}(q₀)`, and shifts
   `vonMangoldtReadout N c` by `-2 Λ(q₀) Y_{N,c}(q₀)`.
4. **Explicit finite prime-pair rows separated by the trans-horizon response
   (`primePairPlusWeight`, `primePairMinusWeight`,
   `primePairWeights_completePeriod_coincide`, `primePairWeights_transHorizon_separated`):**
   The two rows `primePairPlusWeight N` (`Y = δ₂ + δ₃`) and `primePairMinusWeight N`
   (`Y = δ₂ - δ₃`) on `[1, N]` (`N ≥ 3`) have identical complete-period mean (`0`), Selberg
   variance (`3`), Bézout coprime successor form (`-2`), successor covariance (`-2`), successor
   reserve (`5`), phase loss (`3/2`), primitive energy (`11/12`), all-lag covariances
   (`periodCovariance N _ 1 = -2`, `periodCovariance N _ 2 = 0`), and all-tuple variances, while
   their pointwise responses `sieveSeq N _ k` differ by `2 c₃(k) ≠ 0` at **every** `k ∈ ℕ`
   (in particular at the trans-horizon point `k = N + 1`), their prefix discrepancies
   `sievePrefixDiscrepancy N M` differ by `-2` at `M = 1` and at the trans-horizon point
   `M = 3N + 1`, their von Mangoldt readouts are `log 2 + log 3` vs. `log 2 - log 3`, and their
   renormalized prefix defects `sieveRenormalizedPrefixDefect N 1` are `-4` vs. `0`.
-/

open Finset ArithmeticFunction GaloisForLFunctions.BiScaleUncertainty RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Universal Sign-Character Invariance of Complete-Period Quadratic Forms -/

/-- Rescaling Selberg coordinates by any sign pattern `ε` with `ε(q)² = 1` preserves every
squared Selberg coordinate on `[1, N]`. -/
theorem sq_selbergMultiplesCoord_scaledSelbergRow {N q : ℕ} (c : ℕ → ℝ) {ε : ℕ → ℝ}
    (hq : q ∈ Icc 1 N) (hε : ε q ^ 2 = 1) :
    (selbergMultiplesCoord N (scaledSelbergRow N c ε) q) ^ 2 =
      (selbergMultiplesCoord N c q) ^ 2 := by
  rw [selbergMultiplesCoord_scaledSelbergRow c ε hq, mul_pow, hε, one_mul]

/-- If `ε(1) = 1`, `scaledSelbergRow N c ε` preserves the complete-period mean
`finiteHarmonicSum N c`. -/
theorem finiteHarmonicSum_scaledSelbergRow {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) {ε : ℕ → ℝ}
    (hε1 : ε 1 = 1) :
    finiteHarmonicSum N (scaledSelbergRow N c ε) = finiteHarmonicSum N c := by
  rw [← selbergMultiplesCoord_one_eq_finiteHarmonicSum,
    ← selbergMultiplesCoord_one_eq_finiteHarmonicSum,
    selbergMultiplesCoord_scaledSelbergRow c ε (mem_Icc.mpr ⟨le_rfl, hN⟩), hε1, one_mul]

/-- The `q = 1` term of `successorPhaseLoss` vanishes identically, so `successorPhaseLoss N c`
depends only on the non-constant Selberg coordinates `q ∈ Icc 2 N`. -/
theorem successorPhaseLoss_eq_sum_Icc_two (N : ℕ) (c : ℕ → ℝ) :
    successorPhaseLoss N c =
      ∑ q ∈ Icc 2 N,
        ((Nat.totient q : ℝ) - moebiusReal q ^ 2 / (Nat.totient q : ℝ)) *
          (selbergMultiplesCoord N c q) ^ 2 := by
  unfold successorPhaseLoss
  symm
  apply Finset.sum_subset
  · intro q hq
    exact mem_Icc.mpr ⟨by have := (mem_Icc.mp hq).1; omega, (mem_Icc.mp hq).2⟩
  · intro q hq hn
    have hq1 : q = 1 := by simp only [mem_Icc] at hq hn; omega
    subst hq1
    norm_num [moebiusReal]

/-- **Simultaneous evenness of all centered complete-period quadratic forms:**
Whenever two sieve rows `c₁, c₂` have equal squared non-constant Selberg coordinates
`Y(q)²` for all `q ∈ Icc 2 N`, they have identical Selberg variance, Bézout successor covariance,
Bézout successor reserve, one-step successor phase loss, discrete sawtooth primitive energy,
above-parity variance, complete-period lag covariance at every lag `h` (in particular two-lag
covariances `h = 1, 2`), and complete-period tuple variance for every shift tuple `H`. -/
theorem completePeriodCenteredForms_eq_of_sq_eq {N : ℕ} (hN : 1 ≤ N) {c₁ c₂ : ℕ → ℝ}
    (hsq : ∀ q ∈ Icc 2 N,
      (selbergMultiplesCoord N c₁ q) ^ 2 = (selbergMultiplesCoord N c₂ q) ^ 2) :
    sieveVariance N c₁ = sieveVariance N c₂ ∧
      sieveSuccessorCovariance N c₁ = sieveSuccessorCovariance N c₂ ∧
      sieveSuccessorReserve N c₁ = sieveSuccessorReserve N c₂ ∧
      successorPhaseLoss N c₁ = successorPhaseLoss N c₂ ∧
      sievePrimitiveEnergy N c₁ = sievePrimitiveEnergy N c₂ ∧
      sieveVarianceAboveParity N c₁ = sieveVarianceAboveParity N c₂ ∧
      (∀ h : ℕ, TwoLagSieve.periodCovariance N c₁ h = TwoLagSieve.periodCovariance N c₂ h) ∧
      (∀ H : Finset ℕ, tupleVariance N c₁ H = tupleVariance N c₂ H) := by
  have hsum : ∀ w : ℕ → ℝ,
      (∑ q ∈ Icc 2 N, w q * (selbergMultiplesCoord N c₁ q) ^ 2) =
        ∑ q ∈ Icc 2 N, w q * (selbergMultiplesCoord N c₂ q) ^ 2 :=
    fun w => sum_congr rfl fun q hq => by rw [hsq q hq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold sieveVariance
    exact hsum _
  · rw [sieveSuccessorCovariance_eq_diagonal, sieveSuccessorCovariance_eq_diagonal]
    exact hsum _
  · unfold sieveSuccessorReserve
    rw [selbergSubBezoutQuadraticForm_eq_Icc_two hN, selbergSubBezoutQuadraticForm_eq_Icc_two hN]
    exact hsum _
  · rw [successorPhaseLoss_eq_sum_Icc_two, successorPhaseLoss_eq_sum_Icc_two]
    exact hsum _
  · have h12 : 12 * sievePrimitiveEnergy N c₁ = 12 * sievePrimitiveEnergy N c₂ := by
      rw [twelve_mul_sievePrimitiveEnergy_eq_jordan_diagonal,
        twelve_mul_sievePrimitiveEnergy_eq_jordan_diagonal]
      exact hsum _
    linarith
  · unfold sieveVarianceAboveParity
    refine sum_congr rfl fun q hq => ?_
    have hq2 : q ∈ Icc 2 N :=
      mem_Icc.mpr ⟨by have := (mem_Icc.mp hq).1; omega, (mem_Icc.mp hq).2⟩
    rw [hsq q hq2]
  · intro h
    rw [periodCovariance_eq_ramanujanLagWeight_diagonal,
      periodCovariance_eq_ramanujanLagWeight_diagonal]
    exact hsum _
  · intro H
    rw [tupleVariance_eq_sum_structureFactor hN, tupleVariance_eq_sum_structureFactor hN]
    exact sum_congr rfl fun q hq => by rw [hsq q hq]

/-- **Simultaneous evenness of all uncentered complete-period quadratic forms:**
Whenever two sieve rows `c₁, c₂` have equal squared Selberg coordinates `Y(q)²` for all
`q ∈ Icc 1 N`, they also have identical Selberg totient diagonal form, Bézout coprime successor
form, and Franel gcd-square form. -/
theorem completePeriodUncenteredForms_eq_of_sq_eq (N : ℕ) {c₁ c₂ : ℕ → ℝ}
    (hsq : ∀ q ∈ Icc 1 N,
      (selbergMultiplesCoord N c₁ q) ^ 2 = (selbergMultiplesCoord N c₂ q) ^ 2) :
    selbergTotientDiagonalForm N c₁ = selbergTotientDiagonalForm N c₂ ∧
      bezoutCoprimeQuadraticForm N c₁ = bezoutCoprimeQuadraticForm N c₂ ∧
      franelGcdQuadraticForm N c₁ = franelGcdQuadraticForm N c₂ := by
  have hsum : ∀ w : ℕ → ℝ,
      (∑ q ∈ Icc 1 N, w q * (selbergMultiplesCoord N c₁ q) ^ 2) =
        ∑ q ∈ Icc 1 N, w q * (selbergMultiplesCoord N c₂ q) ^ 2 :=
    fun w => sum_congr rfl fun q hq => by rw [hsq q hq]
  refine ⟨?_, ?_, ?_⟩
  · unfold selbergTotientDiagonalForm
    exact hsum _
  · rw [bezoutCoprimeQuadraticForm_eq_moebius_diagonal,
      bezoutCoprimeQuadraticForm_eq_moebius_diagonal]
    exact hsum _
  · rw [franelGcdQuadraticForm_eq_jordanTotient2_diagonal,
      franelGcdQuadraticForm_eq_jordanTotient2_diagonal]
    exact hsum _

/-- **Universal sign-character invariance of the complete-period quadratic bundle:**
For every cutoff `N ≥ 1`, every row `c : ℕ → ℝ`, and every sign character `ε : ℕ → ℝ` with
`∀ q ∈ Icc 1 N, ε q ^ 2 = 1`, the coordinate-twisted row `scaledSelbergRow N c ε` has the exact
same Selberg totient form, Selberg variance, Bézout coprime successor form, Bézout successor
covariance, successor reserve, one-step phase loss, sawtooth primitive energy, Franel gcd form,
above-parity variance, complete-period lag covariance at every lag `h`, and tuple variance for
every shift tuple `H`. -/
theorem completePeriodQuadraticForms_scaledSelbergRow {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ)
    {ε : ℕ → ℝ} (hε : ∀ q ∈ Icc 1 N, ε q ^ 2 = 1) :
    selbergTotientDiagonalForm N (scaledSelbergRow N c ε) = selbergTotientDiagonalForm N c ∧
      sieveVariance N (scaledSelbergRow N c ε) = sieveVariance N c ∧
      bezoutCoprimeQuadraticForm N (scaledSelbergRow N c ε) = bezoutCoprimeQuadraticForm N c ∧
      sieveSuccessorCovariance N (scaledSelbergRow N c ε) = sieveSuccessorCovariance N c ∧
      sieveSuccessorReserve N (scaledSelbergRow N c ε) = sieveSuccessorReserve N c ∧
      successorPhaseLoss N (scaledSelbergRow N c ε) = successorPhaseLoss N c ∧
      sievePrimitiveEnergy N (scaledSelbergRow N c ε) = sievePrimitiveEnergy N c ∧
      franelGcdQuadraticForm N (scaledSelbergRow N c ε) = franelGcdQuadraticForm N c ∧
      sieveVarianceAboveParity N (scaledSelbergRow N c ε) = sieveVarianceAboveParity N c ∧
      (∀ h : ℕ, TwoLagSieve.periodCovariance N (scaledSelbergRow N c ε) h =
        TwoLagSieve.periodCovariance N c h) ∧
      (∀ H : Finset ℕ, tupleVariance N (scaledSelbergRow N c ε) H = tupleVariance N c H) := by
  have hsq1 : ∀ q ∈ Icc 1 N,
      (selbergMultiplesCoord N (scaledSelbergRow N c ε) q) ^ 2 =
        (selbergMultiplesCoord N c q) ^ 2 :=
    fun q hq => sq_selbergMultiplesCoord_scaledSelbergRow c hq (hε q hq)
  have hsq2 : ∀ q ∈ Icc 2 N,
      (selbergMultiplesCoord N (scaledSelbergRow N c ε) q) ^ 2 =
        (selbergMultiplesCoord N c q) ^ 2 :=
    fun q hq => hsq1 q (mem_Icc.mpr ⟨by have := (mem_Icc.mp hq).1; omega, (mem_Icc.mp hq).2⟩)
  obtain ⟨hV, hC, hR, hL, hE, hA, hcov, htup⟩ := completePeriodCenteredForms_eq_of_sq_eq hN hsq2
  obtain ⟨hSel, hBez, hFr⟩ := completePeriodUncenteredForms_eq_of_sq_eq N hsq1
  exact ⟨hSel, hV, hBez, hC, hR, hL, hE, hFr, hA, hcov, htup⟩

/-! ## §2. Bidirectional Orbit Classification via Complete-Period Lag Covariances -/

/-- **Lag-covariance characterization of the squared Selberg spectrum:**
Two rows `c₁, c₂` at cutoff `N` have the same squared non-constant Selberg coordinates `Y(q)²`
on `Icc 2 N` **if and only if** their complete-period lag covariances agree at lags `1, …, N`. -/
theorem sq_selbergMultiplesCoord_eq_iff_periodCovariance_eq (N : ℕ) (c₁ c₂ : ℕ → ℝ) :
    (∀ q ∈ Icc 2 N,
      (selbergMultiplesCoord N c₁ q) ^ 2 = (selbergMultiplesCoord N c₂ q) ^ 2) ↔
      (∀ g ∈ Icc 1 N,
        TwoLagSieve.periodCovariance N c₁ g = TwoLagSieve.periodCovariance N c₂ g) := by
  constructor
  · intro hsq g _
    rw [periodCovariance_eq_ramanujanLagWeight_diagonal,
      periodCovariance_eq_ramanujanLagWeight_diagonal]
    exact sum_congr rfl fun q hq => by rw [hsq q hq]
  · intro hcov q hq
    rw [← lagSpectrumReadout_periodCovariance hq c₁,
      ← lagSpectrumReadout_periodCovariance hq c₂]
    unfold lagSpectrumReadout
    refine sum_congr rfl fun u hu => ?_
    congr 1
    refine sum_congr rfl fun x hx => ?_
    have hqu : q * u ≤ N := by
      have := (Nat.le_div_iff_mul_le (by have := (mem_Icc.mp hq).1; omega)).mp (mem_Icc.mp hu).2
      linarith [Nat.mul_comm u q]
    have hx_eq := (Nat.mem_divisorsAntidiagonal.mp hx).1
    have hx2 : x.2 ∈ Icc 1 N := by
      refine mem_Icc.mpr ⟨Nat.pos_of_ne_zero fun h0 => ?_, ?_⟩
      · rw [h0, mul_zero] at hx_eq
        have hq2 := (mem_Icc.mp hq).1
        have hu1 := (mem_Icc.mp hu).1
        nlinarith
      · exact (Nat.le_of_dvd (by have := (mem_Icc.mp hq).1; have := (mem_Icc.mp hu).1; nlinarith)
          ⟨x.1, by rw [← hx_eq]; ring⟩).trans hqu
    rw [hcov x.2 hx2]

/-- Canonical relative sign pattern between the Selberg coordinates of `c₁` and `c₂`. -/
def relativeSelbergSign (N : ℕ) (c₁ c₂ : ℕ → ℝ) (q : ℕ) : ℝ :=
  if selbergMultiplesCoord N c₂ q = -selbergMultiplesCoord N c₁ q ∧
      selbergMultiplesCoord N c₁ q ≠ 0 then -1 else 1

theorem relativeSelbergSign_sq (N : ℕ) (c₁ c₂ : ℕ → ℝ) (q : ℕ) :
    (relativeSelbergSign N c₁ c₂ q) ^ 2 = 1 := by
  unfold relativeSelbergSign
  split_ifs <;> norm_num

/-- **Complete-period lag covariances determine the row up to a Selberg coordinate sign character:**
For any two rows `c₁, c₂` at cutoff `N ≥ 1` with the same complete-period mean
`finiteHarmonicSum N c₁ = finiteHarmonicSum N c₂`, the complete-period lag covariances on `Icc 1 N`
agree **if and only if** there exists a sign pattern `ε : ℕ → ℝ` with `ε 1 = 1`, `∀ q, ε q ^ 2 = 1`,
and `c₂ d = scaledSelbergRow N c₁ ε d` for every active divisor `d ∈ Icc 1 N`. -/
theorem periodCovariance_eq_iff_exists_scaledSelbergRow {N : ℕ} {c₁ c₂ : ℕ → ℝ}
    (hmean : finiteHarmonicSum N c₁ = finiteHarmonicSum N c₂) :
    (∀ g ∈ Icc 1 N,
      TwoLagSieve.periodCovariance N c₁ g = TwoLagSieve.periodCovariance N c₂ g) ↔
      ∃ ε : ℕ → ℝ, ε 1 = 1 ∧ (∀ q, ε q ^ 2 = 1) ∧
        ∀ d ∈ Icc 1 N, c₂ d = scaledSelbergRow N c₁ ε d := by
  rw [← sq_selbergMultiplesCoord_eq_iff_periodCovariance_eq]
  constructor
  · intro hsq
    refine ⟨relativeSelbergSign N c₁ c₂, ?_, relativeSelbergSign_sq N c₁ c₂, ?_⟩
    · unfold relativeSelbergSign
      rw [selbergMultiplesCoord_one_eq_finiteHarmonicSum,
        selbergMultiplesCoord_one_eq_finiteHarmonicSum, hmean]
      split_ifs with h
      · exfalso; exact h.2 (by linarith [h.1])
      · rfl
    · intro d hd
      rw [← ramanujan_inverse_selbergCoords_eq N c₂ d hd, scaledSelbergRow]
      have hcoord : ∀ q ∈ Icc 1 N,
          selbergMultiplesCoord N c₂ q =
            relativeSelbergSign N c₁ c₂ q * selbergMultiplesCoord N c₁ q := by
        intro q hq
        by_cases hq1 : q = 1
        · subst hq1
          unfold relativeSelbergSign
          rw [selbergMultiplesCoord_one_eq_finiteHarmonicSum,
            selbergMultiplesCoord_one_eq_finiteHarmonicSum, hmean]
          split_ifs with h
          · exfalso; exact h.2 (by linarith [h.1])
          · ring
        · have hq2 : q ∈ Icc 2 N :=
            mem_Icc.mpr ⟨by have := (mem_Icc.mp hq).1; omega, (mem_Icc.mp hq).2⟩
          have h := sq_eq_sq_iff_eq_or_eq_neg.mp (hsq q hq2).symm
          unfold relativeSelbergSign
          rcases h with heq | hneg
          · split_ifs with h'
            · linarith [h'.1]
            · linarith
          · by_cases hz : selbergMultiplesCoord N c₁ q = 0
            · rw [hz] at hneg ⊢
              simp [hneg]
            · rw [if_pos ⟨hneg, hz⟩]
              linarith
      have hdiff : ∀ q ∈ Icc 1 N,
          selbergMultiplesCoord N
            (fun j => pmRamanujanResidueCoeff (selbergMultiplesCoord N c₂) N j -
              pmRamanujanResidueCoeff
                (fun r => relativeSelbergSign N c₁ c₂ r * selbergMultiplesCoord N c₁ r) N j) q = 0 := by
        intro q hq
        rw [selbergMultiplesCoord_sub, selbergMultiplesCoord_ramanujan_inverse,
          selbergMultiplesCoord_ramanujan_inverse, if_pos hq, if_pos hq, hcoord q hq, sub_self]
      exact sub_eq_zero.mp ((selbergMultiplesCoord_tail_zero_iff N 0 _).mp hdiff d hd)
  · rintro ⟨ε, _, hε, hc⟩ q hq
    have hq1 : q ∈ Icc 1 N :=
      mem_Icc.mpr ⟨by have := (mem_Icc.mp hq).1; omega, (mem_Icc.mp hq).2⟩
    have hY : selbergMultiplesCoord N c₂ q =
        selbergMultiplesCoord N (scaledSelbergRow N c₁ ε) q := by
      unfold selbergMultiplesCoord
      refine sum_congr rfl fun d hd => ?_
      rw [hc d (mem_filter.mp hd).1]
    rw [hY, sq_selbergMultiplesCoord_scaledSelbergRow c₁ hq1 (hε q)]

/-! ## §3. Single-Mode Sign Flips and Exact Trans-Horizon Linearity -/

/-- The sign character on Selberg coordinates that flips the single mode `q₀` and fixes all
other modes. -/
def singleModeSignFlip (q₀ q : ℕ) : ℝ :=
  if q = q₀ then -1 else 1

theorem singleModeSignFlip_sq (q₀ q : ℕ) :
    (singleModeSignFlip q₀ q) ^ 2 = 1 := by
  unfold singleModeSignFlip
  split_ifs <;> norm_num

theorem singleModeSignFlip_sub_one (q₀ q : ℕ) :
    singleModeSignFlip q₀ q - 1 = if q = q₀ then -2 else 0 := by
  unfold singleModeSignFlip
  split_ifs <;> norm_num

/-- **Pointwise response difference under an arbitrary Selberg coordinate rescaling:**
`s_{N, c^ε}(k) - s_{N,c}(k) = ∑_{q=1}^N (ε(q) - 1) Y_{N,c}(q) c_q(k)`. -/
theorem sieveSeq_scaledSelbergRow_sub (N : ℕ) (c : ℕ → ℝ) (ε : ℕ → ℝ) (k : ℕ) :
    sieveSeq N (scaledSelbergRow N c ε) k - sieveSeq N c k =
      ∑ q ∈ Icc 1 N,
        (ε q - 1) * selbergMultiplesCoord N c q * ramanujanLagCoefficient q k := by
  rw [SieveMoments.sieveSeq_ramanujan_expansion N (scaledSelbergRow N c ε) k,
    SieveMoments.sieveSeq_ramanujan_expansion N c k, ← sum_sub_distrib]
  refine sum_congr rfl fun q hq => ?_
  rw [selbergMultiplesCoord_scaledSelbergRow c ε hq]
  ring

/-- **Single-mode sign flip on the pointwise sieve response:**
Flipping mode `q₀ ∈ Icc 1 N` shifts `sieveSeq N c k` by `-2 Y_{N,c}(q₀) c_{q₀}(k)`. -/
theorem sieveSeq_scaledSelbergRow_singleModeSignFlip_sub {N q₀ : ℕ} (hq₀ : q₀ ∈ Icc 1 N)
    (c : ℕ → ℝ) (k : ℕ) :
    sieveSeq N (scaledSelbergRow N c (singleModeSignFlip q₀)) k - sieveSeq N c k =
      -2 * selbergMultiplesCoord N c q₀ * ramanujanLagCoefficient q₀ k := by
  rw [sieveSeq_scaledSelbergRow_sub]
  calc
    (∑ q ∈ Icc 1 N,
        (singleModeSignFlip q₀ q - 1) * selbergMultiplesCoord N c q *
          ramanujanLagCoefficient q k)
      = ∑ q ∈ Icc 1 N,
          if q = q₀ then -2 * selbergMultiplesCoord N c q * ramanujanLagCoefficient q k else 0 := by
        refine sum_congr rfl fun q _ => ?_
        rw [singleModeSignFlip_sub_one]
        split_ifs <;> ring
    _ = -2 * selbergMultiplesCoord N c q₀ * ramanujanLagCoefficient q₀ k := by
        simp [hq₀]

/-- **Prefix discrepancy difference under an arbitrary Selberg coordinate rescaling:**
`L_N(M, c^ε) - L_N(M, c) = ∑_{q=2}^N (ε(q) - 1) Re(R_q(M)) Y_{N,c}(q)`. -/
theorem sievePrefixDiscrepancy_scaledSelbergRow_sub (N M : ℕ) (c : ℕ → ℝ) (ε : ℕ → ℝ) :
    sievePrefixDiscrepancy N M (scaledSelbergRow N c ε) - sievePrefixDiscrepancy N M c =
      ∑ q ∈ Icc 2 N,
        (ε q - 1) * (pmRamanujanPrimitive q M).re * selbergMultiplesCoord N c q := by
  rw [sievePrefixDiscrepancy_eq_ramanujan_diagonal N M (scaledSelbergRow N c ε),
    sievePrefixDiscrepancy_eq_ramanujan_diagonal N M c, ← sum_sub_distrib]
  refine sum_congr rfl fun q hq => ?_
  have hq1 : q ∈ Icc 1 N :=
    mem_Icc.mpr ⟨by have := (mem_Icc.mp hq).1; omega, (mem_Icc.mp hq).2⟩
  rw [selbergMultiplesCoord_scaledSelbergRow c ε hq1]
  ring

/-- **Single-mode sign flip on the finite-prefix discrepancy:**
Flipping mode `q₀ ∈ Icc 2 N` shifts `sievePrefixDiscrepancy N M c` by
`-2 Re(R_{q₀}(M)) Y_{N,c}(q₀)`. -/
theorem sievePrefixDiscrepancy_scaledSelbergRow_singleModeSignFlip_sub {N q₀ : ℕ}
    (hq₀ : q₀ ∈ Icc 2 N) (M : ℕ) (c : ℕ → ℝ) :
    sievePrefixDiscrepancy N M (scaledSelbergRow N c (singleModeSignFlip q₀)) -
        sievePrefixDiscrepancy N M c =
      -2 * (pmRamanujanPrimitive q₀ M).re * selbergMultiplesCoord N c q₀ := by
  rw [sievePrefixDiscrepancy_scaledSelbergRow_sub]
  calc
    (∑ q ∈ Icc 2 N,
        (singleModeSignFlip q₀ q - 1) * (pmRamanujanPrimitive q M).re *
          selbergMultiplesCoord N c q)
      = ∑ q ∈ Icc 2 N,
          if q = q₀ then -2 * (pmRamanujanPrimitive q M).re * selbergMultiplesCoord N c q
          else 0 := by
        refine sum_congr rfl fun q _ => ?_
        rw [singleModeSignFlip_sub_one]
        split_ifs <;> ring
    _ = -2 * (pmRamanujanPrimitive q₀ M).re * selbergMultiplesCoord N c q₀ := by
        simp [hq₀]

/-- **Von Mangoldt pronic readout difference under an arbitrary Selberg coordinate rescaling:**
`vonMangoldtReadout N (c^ε) - vonMangoldtReadout N c = ∑_{q=2}^N (ε(q) - 1) Λ(q) Y_{N,c}(q)`. -/
theorem vonMangoldtReadout_scaledSelbergRow_sub (N : ℕ) (c : ℕ → ℝ) (ε : ℕ → ℝ) :
    vonMangoldtReadout N (scaledSelbergRow N c ε) - vonMangoldtReadout N c =
      ∑ q ∈ Icc 2 N,
        (ε q - 1) * vonMangoldt q * selbergMultiplesCoord N c q := by
  unfold vonMangoldtReadout
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun q hq => ?_
  have hq1 : q ∈ Icc 1 N :=
    mem_Icc.mpr ⟨by have := (mem_Icc.mp hq).1; omega, (mem_Icc.mp hq).2⟩
  rw [selbergMultiplesCoord_scaledSelbergRow c ε hq1]
  ring

/-- **Single-mode sign flip on the von Mangoldt pronic readout:**
Flipping mode `q₀ ∈ Icc 2 N` shifts `vonMangoldtReadout N c` by `-2 Λ(q₀) Y_{N,c}(q₀)`. -/
theorem vonMangoldtReadout_scaledSelbergRow_singleModeSignFlip_sub {N q₀ : ℕ}
    (hq₀ : q₀ ∈ Icc 2 N) (c : ℕ → ℝ) :
    vonMangoldtReadout N (scaledSelbergRow N c (singleModeSignFlip q₀)) -
        vonMangoldtReadout N c =
      -2 * vonMangoldt q₀ * selbergMultiplesCoord N c q₀ := by
  rw [vonMangoldtReadout_scaledSelbergRow_sub]
  calc
    (∑ q ∈ Icc 2 N,
        (singleModeSignFlip q₀ q - 1) * vonMangoldt q * selbergMultiplesCoord N c q)
      = ∑ q ∈ Icc 2 N,
          if q = q₀ then -2 * vonMangoldt q * selbergMultiplesCoord N c q else 0 := by
        refine sum_congr rfl fun q _ => ?_
        rw [singleModeSignFlip_sub_one]
        split_ifs <;> ring
    _ = -2 * vonMangoldt q₀ * selbergMultiplesCoord N c q₀ := by
        simp [hq₀]

/-- **Exact faithfulness of the sieve response on the `(ℤ/2ℤ)^N` sign-character orbit:**
The response sequence of `scaledSelbergRow N c ε` agrees with that of `c` at all integer points
if and only if `ε q = 1` at every active Selberg mode `q ∈ Icc 1 N` (`Y_{N,c}(q) ≠ 0`). -/
theorem sieveSeq_scaledSelbergRow_eq_iff (N : ℕ) (c : ℕ → ℝ) (ε : ℕ → ℝ) :
    (∀ k : ℕ, sieveSeq N (scaledSelbergRow N c ε) k = sieveSeq N c k) ↔
      ∀ q ∈ Icc 1 N, selbergMultiplesCoord N c q ≠ 0 → ε q = 1 := by
  constructor
  · intro hall q hq hY
    have hdiff : sieveSeq N (fun d => scaledSelbergRow N c ε d - c d) = fun _ => 0 := by
      funext k
      have hk := hall k
      unfold sieveSeq at hk ⊢
      rw [sum_sub_distrib, hk, sub_self]
    have hsum_sq : (∑ k ∈ Ioc 0 N.factorial,
        (sieveSeq N (fun d => scaledSelbergRow N c ε d - c d) k) ^ 2) / (N.factorial : ℝ) =
        selbergTotientDiagonalForm N (fun d => scaledSelbergRow N c ε d - c d) := by
      simpa only [pow_two, selbergTotientDiagonalForm, mul_assoc] using
        mean_sieveSeq_mul_eq_totient_pairing N
          (fun d => scaledSelbergRow N c ε d - c d)
          (fun d => scaledSelbergRow N c ε d - c d)
    rw [hdiff] at hsum_sq
    simp only [zero_pow two_ne_zero, sum_const_zero, zero_div] at hsum_sq
    have hphi : 0 < (Nat.totient q : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr (mem_Icc.mp hq).1
    have hterm_zero : (Nat.totient q : ℝ) *
        (selbergMultiplesCoord N (fun d => scaledSelbergRow N c ε d - c d) q) ^ 2 = 0 := by
      have htot := hsum_sq.symm
      unfold selbergTotientDiagonalForm at htot
      exact (sum_eq_zero_iff_of_nonneg
        (fun r _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))).mp htot q hq
    have hcoord_zero := sq_eq_zero_iff.mp ((mul_eq_zero.mp hterm_zero).resolve_left hphi.ne')
    rw [selbergMultiplesCoord_sub, selbergMultiplesCoord_scaledSelbergRow c ε hq] at hcoord_zero
    have hfac : (ε q - 1) * selbergMultiplesCoord N c q = 0 := by linarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hfac).resolve_right hY)
  · intro hact k
    have h := sieveSeq_scaledSelbergRow_sub N c ε k
    have hsum0 : (∑ q ∈ Icc 1 N,
        (ε q - 1) * selbergMultiplesCoord N c q * ramanujanLagCoefficient q k) = 0 := by
      refine sum_eq_zero fun q hq => ?_
      by_cases hY : selbergMultiplesCoord N c q = 0
      · simp [hY]
      · rw [hact q hq hY, sub_self, zero_mul, zero_mul]
    linarith

/-! ## §4. Explicit Finite Prime-Pair Witness Separated by the Trans-Horizon Response -/

/-- Selberg coordinate profile supported on the first two primes `{2, 3}` with signs `(+1, +1)`. -/
def primePairPlusProfile (q : ℕ) : ℝ :=
  if q = 2 then 1 else if q = 3 then 1 else 0

/-- Selberg coordinate profile supported on the first two primes `{2, 3}` with signs `(+1, -1)`. -/
def primePairMinusProfile (q : ℕ) : ℝ :=
  if q = 2 then 1 else if q = 3 then -1 else 0

/-- The finite divisor-sieve weight at cutoff `N` with Selberg coordinates `δ₂ + δ₃`. -/
def primePairPlusWeight (N : ℕ) : ℕ → ℝ :=
  pmRamanujanResidueCoeff primePairPlusProfile N

/-- The finite divisor-sieve weight at cutoff `N` with Selberg coordinates `δ₂ - δ₃`. -/
def primePairMinusWeight (N : ℕ) : ℕ → ℝ :=
  pmRamanujanResidueCoeff primePairMinusProfile N

theorem selbergMultiplesCoord_primePairPlusWeight {N q : ℕ} (hq : q ∈ Icc 1 N) :
    selbergMultiplesCoord N (primePairPlusWeight N) q = primePairPlusProfile q := by
  unfold primePairPlusWeight
  rw [selbergMultiplesCoord_ramanujan_inverse, if_pos hq]

theorem selbergMultiplesCoord_primePairMinusWeight {N q : ℕ} (hq : q ∈ Icc 1 N) :
    selbergMultiplesCoord N (primePairMinusWeight N) q = primePairMinusProfile q := by
  unfold primePairMinusWeight
  rw [selbergMultiplesCoord_ramanujan_inverse, if_pos hq]

theorem primePairMinusProfile_eq_singleModeSignFlip (q : ℕ) :
    primePairMinusProfile q = singleModeSignFlip 3 q * primePairPlusProfile q := by
  unfold primePairMinusProfile primePairPlusProfile singleModeSignFlip
  by_cases h2 : q = 2
  · subst h2; norm_num
  by_cases h3 : q = 3
  · subst h3; norm_num
  simp [h2, h3]

/-- `primePairMinusWeight N` is the Selberg coordinate sign twist of `primePairPlusWeight N` by
`singleModeSignFlip 3`. -/
theorem selbergMultiplesCoord_primePairMinusWeight_eq_scaled {N q : ℕ} (hq : q ∈ Icc 1 N) :
    selbergMultiplesCoord N (primePairMinusWeight N) q =
      selbergMultiplesCoord N
        (scaledSelbergRow N (primePairPlusWeight N) (singleModeSignFlip 3)) q := by
  rw [selbergMultiplesCoord_primePairMinusWeight hq,
    selbergMultiplesCoord_scaledSelbergRow _ _ hq,
    selbergMultiplesCoord_primePairPlusWeight hq,
    primePairMinusProfile_eq_singleModeSignFlip]

theorem sq_primePairMinusProfile (q : ℕ) :
    (primePairMinusProfile q) ^ 2 = (primePairPlusProfile q) ^ 2 := by
  rw [primePairMinusProfile_eq_singleModeSignFlip, mul_pow, singleModeSignFlip_sq, one_mul]

private theorem sum_Icc_two_primePairPlusProfile_sq {N : ℕ} (hN : 3 ≤ N) (w : ℕ → ℝ) :
    (∑ q ∈ Icc 2 N, w q * (primePairPlusProfile q) ^ 2) = w 2 + w 3 := by
  have hterm : ∀ q ∈ Icc 2 N,
      w q * (primePairPlusProfile q) ^ 2 =
        (if q = 2 then w 2 else 0) + (if q = 3 then w 3 else 0) := by
    intro q _
    unfold primePairPlusProfile
    by_cases h2 : q = 2
    · subst h2; norm_num
    by_cases h3 : q = 3
    · subst h3; norm_num
    simp [h2, h3]
  rw [sum_congr rfl hterm, sum_add_distrib]
  have h2 : 2 ∈ Icc 2 N := mem_Icc.mpr ⟨le_rfl, by omega⟩
  have h3 : 3 ∈ Icc 2 N := mem_Icc.mpr ⟨by omega, hN⟩
  simp [h2, h3]

/-- **All complete-period quadratic forms coincide on `primePairPlusWeight N` and
`primePairMinusWeight N` (`N ≥ 3`):**
Both weights have zero complete-period mean (`ker P`), Selberg variance `3`, Bézout coprime
successor form `-2`, centered successor covariance `-2`, successor reserve `5`, one-step phase
loss `3/2`, sawtooth primitive energy `11/12`, identical complete-period lag covariances at
every lag `h` (with `periodCovariance = -2` at `h = 1` and `0` at `h = 2`), and identical
tuple variances for every shift tuple `H`. -/
theorem primePairWeights_completePeriod_coincide {N : ℕ} (hN : 3 ≤ N) :
    (finiteHarmonicSum N (primePairPlusWeight N) = 0 ∧
      finiteHarmonicSum N (primePairMinusWeight N) = 0) ∧
    (sieveVariance N (primePairPlusWeight N) = 3 ∧
      sieveVariance N (primePairMinusWeight N) = 3) ∧
    (bezoutCoprimeQuadraticForm N (primePairPlusWeight N) = -2 ∧
      bezoutCoprimeQuadraticForm N (primePairMinusWeight N) = -2) ∧
    (sieveSuccessorCovariance N (primePairPlusWeight N) = -2 ∧
      sieveSuccessorCovariance N (primePairMinusWeight N) = -2) ∧
    (sieveSuccessorReserve N (primePairPlusWeight N) = 5 ∧
      sieveSuccessorReserve N (primePairMinusWeight N) = 5) ∧
    (successorPhaseLoss N (primePairPlusWeight N) = 3 / 2 ∧
      successorPhaseLoss N (primePairMinusWeight N) = 3 / 2) ∧
    (12 * sievePrimitiveEnergy N (primePairPlusWeight N) = 11 ∧
      12 * sievePrimitiveEnergy N (primePairMinusWeight N) = 11) ∧
    (TwoLagSieve.periodCovariance N (primePairPlusWeight N) 1 = -2 ∧
      TwoLagSieve.periodCovariance N (primePairMinusWeight N) 1 = -2 ∧
      TwoLagSieve.periodCovariance N (primePairPlusWeight N) 2 = 0 ∧
      TwoLagSieve.periodCovariance N (primePairMinusWeight N) 2 = 0 ∧
      ∀ h : ℕ, TwoLagSieve.periodCovariance N (primePairPlusWeight N) h =
        TwoLagSieve.periodCovariance N (primePairMinusWeight N) h) ∧
    (∀ H : Finset ℕ, tupleVariance N (primePairPlusWeight N) H =
      tupleVariance N (primePairMinusWeight N) H) := by
  have hN1 : 1 ≤ N := by omega
  have hsq1 : ∀ q ∈ Icc 1 N,
      (selbergMultiplesCoord N (primePairPlusWeight N) q) ^ 2 =
        (selbergMultiplesCoord N (primePairMinusWeight N) q) ^ 2 := by
    intro q hq
    rw [selbergMultiplesCoord_primePairPlusWeight hq,
      selbergMultiplesCoord_primePairMinusWeight hq, sq_primePairMinusProfile]
  have hsq2 : ∀ q ∈ Icc 2 N,
      (selbergMultiplesCoord N (primePairPlusWeight N) q) ^ 2 =
        (selbergMultiplesCoord N (primePairMinusWeight N) q) ^ 2 :=
    fun q hq => hsq1 q (mem_Icc.mpr ⟨by have := (mem_Icc.mp hq).1; omega, (mem_Icc.mp hq).2⟩)
  obtain ⟨hV_eq, hC_eq, hR_eq, hL_eq, hE_eq, _, hcov_eq, htup_eq⟩ :=
    completePeriodCenteredForms_eq_of_sq_eq hN1 hsq2
  obtain ⟨_, hBez_eq, _⟩ := completePeriodUncenteredForms_eq_of_sq_eq N hsq1
  have heval : ∀ w : ℕ → ℝ,
      (∑ q ∈ Icc 2 N, w q * (selbergMultiplesCoord N (primePairPlusWeight N) q) ^ 2) =
        w 2 + w 3 := by
    intro w
    calc
      _ = ∑ q ∈ Icc 2 N, w q * (primePairPlusProfile q) ^ 2 := by
        refine sum_congr rfl fun q hq => ?_
        rw [selbergMultiplesCoord_primePairPlusWeight
          (mem_Icc.mpr ⟨by have := (mem_Icc.mp hq).1; omega, (mem_Icc.mp hq).2⟩)]
      _ = w 2 + w 3 := sum_Icc_two_primePairPlusProfile_sq hN w
  have hmean_plus : finiteHarmonicSum N (primePairPlusWeight N) = 0 := by
    rw [← selbergMultiplesCoord_one_eq_finiteHarmonicSum,
      selbergMultiplesCoord_primePairPlusWeight (mem_Icc.mpr ⟨le_rfl, hN1⟩)]
    simp [primePairPlusProfile]
  have hmean_minus : finiteHarmonicSum N (primePairMinusWeight N) = 0 := by
    rw [← selbergMultiplesCoord_one_eq_finiteHarmonicSum,
      selbergMultiplesCoord_primePairMinusWeight (mem_Icc.mpr ⟨le_rfl, hN1⟩)]
    simp [primePairMinusProfile]
  have hmu2 : moebiusReal 2 = -1 := by
    unfold moebiusReal; rw [ArithmeticFunction.moebius_apply_prime Nat.prime_two]; norm_num
  have hmu3 : moebiusReal 3 = -1 := by
    unfold moebiusReal; rw [ArithmeticFunction.moebius_apply_prime Nat.prime_three]; norm_num
  have hj2 : jordanTotient2 2 = 3 := by
    have h := jordanTotient2_prime_pow_succ Nat.prime_two 0; norm_num at h; exact h
  have hj3 : jordanTotient2 3 = 8 := by
    have h := jordanTotient2_prime_pow_succ Nat.prime_three 0; norm_num at h; exact h
  have hV_plus : sieveVariance N (primePairPlusWeight N) = 3 := by
    unfold sieveVariance
    rw [heval, Nat.totient_two, Nat.totient_prime Nat.prime_three]
    norm_num
  have hC_plus : sieveSuccessorCovariance N (primePairPlusWeight N) = -2 := by
    rw [sieveSuccessorCovariance_eq_diagonal, heval, hmu2, hmu3]
    norm_num
  have hBez_plus : bezoutCoprimeQuadraticForm N (primePairPlusWeight N) = -2 := by
    have hC := hC_plus
    unfold sieveSuccessorCovariance at hC
    rw [hmean_plus] at hC
    linarith
  have hR_plus : sieveSuccessorReserve N (primePairPlusWeight N) = 5 := by
    unfold sieveSuccessorReserve
    rw [selbergSubBezoutQuadraticForm_eq_Icc_two hN1, heval,
      Nat.totient_two, Nat.totient_prime Nat.prime_three, hmu2, hmu3]
    norm_num
  have hL_plus : successorPhaseLoss N (primePairPlusWeight N) = 3 / 2 := by
    rw [successorPhaseLoss_eq_sum_Icc_two, heval,
      Nat.totient_two, Nat.totient_prime Nat.prime_three, hmu2, hmu3]
    norm_num
  have hE_plus : 12 * sievePrimitiveEnergy N (primePairPlusWeight N) = 11 := by
    rw [twelve_mul_sievePrimitiveEnergy_eq_jordan_diagonal, heval, hj2, hj3]
    norm_num
  have hcov1_plus : TwoLagSieve.periodCovariance N (primePairPlusWeight N) 1 = -2 := by
    rw [TwoLagSieve.periodCovariance_one, hBez_plus, hmean_plus]
    norm_num
  have hcov2_plus : TwoLagSieve.periodCovariance N (primePairPlusWeight N) 2 = 0 := by
    rw [periodCovariance_eq_ramanujanLagWeight_diagonal, heval]
    have hr2 : ramanujanLagWeight 2 2 = 1 := by
      rw [ramanujanLagWeight_eq_sum_divisors]
      have hdiv2 : (2 : ℕ).divisors = {1, 2} := by decide
      rw [hdiv2, sum_insert (by decide), sum_singleton]
      simp [ArithmeticFunction.moebius_apply_prime Nat.prime_two]; norm_num
    have hr3 : ramanujanLagWeight 2 3 = -1 := by
      rw [ramanujanLagWeight_eq_sum_divisors]
      have hdiv3 : (3 : ℕ).divisors = {1, 3} := by decide
      rw [hdiv3, sum_insert (by decide), sum_singleton]
      have hndvd : ¬ (3 ∣ 2) := by decide
      simp [hndvd, ArithmeticFunction.moebius_apply_prime Nat.prime_three]
    rw [hr2, hr3]
    ring
  exact ⟨⟨hmean_plus, hmean_minus⟩,
    ⟨hV_plus, hV_eq ▸ hV_plus⟩,
    ⟨hBez_plus, hBez_eq ▸ hBez_plus⟩,
    ⟨hC_plus, hC_eq ▸ hC_plus⟩,
    ⟨hR_plus, hR_eq ▸ hR_plus⟩,
    ⟨hL_plus, hL_eq ▸ hL_plus⟩,
    ⟨hE_plus, by rw [← hE_eq, hE_plus]⟩,
    ⟨hcov1_plus, hcov_eq 1 ▸ hcov1_plus, hcov2_plus, hcov_eq 2 ▸ hcov2_plus, hcov_eq⟩,
    htup_eq⟩

/-- Explicit Ramanujan formula for the response of `primePairPlusWeight N` and
`primePairMinusWeight N` at any integer `k`:
`s_{N, c^+}(k) = c_2(k) + c_3(k)` and `s_{N, c^-}(k) = c_2(k) - c_3(k)`. -/
theorem sieveSeq_primePairWeights_eq {N : ℕ} (hN : 3 ≤ N) (k : ℕ) :
    sieveSeq N (primePairPlusWeight N) k =
        ramanujanLagCoefficient 2 k + ramanujanLagCoefficient 3 k ∧
      sieveSeq N (primePairMinusWeight N) k =
        ramanujanLagCoefficient 2 k - ramanujanLagCoefficient 3 k ∧
      sieveSeq N (primePairPlusWeight N) k - sieveSeq N (primePairMinusWeight N) k =
        2 * ramanujanLagCoefficient 3 k := by
  have h1 : 1 ∈ Icc 2 N → False := fun h => by have := (mem_Icc.mp h).1; omega
  have hIcc : Icc 1 N = insert 1 (Icc 2 N) := by
    ext q; simp only [mem_Icc, mem_insert]; omega
  have hplus : sieveSeq N (primePairPlusWeight N) k =
      ramanujanLagCoefficient 2 k + ramanujanLagCoefficient 3 k := by
    rw [SieveMoments.sieveSeq_ramanujan_expansion, hIcc, sum_insert h1]
    have hY1 : selbergMultiplesCoord N (primePairPlusWeight N) 1 = 0 := by
      rw [selbergMultiplesCoord_primePairPlusWeight (mem_Icc.mpr ⟨le_rfl, by omega⟩)]
      simp [primePairPlusProfile]
    rw [hY1, zero_mul, zero_add]
    have hterm : ∀ q ∈ Icc 2 N,
        selbergMultiplesCoord N (primePairPlusWeight N) q * ramanujanLagCoefficient q k =
          (if q = 2 then ramanujanLagCoefficient 2 k else 0) +
            (if q = 3 then ramanujanLagCoefficient 3 k else 0) := by
      intro q hq
      rw [selbergMultiplesCoord_primePairPlusWeight
        (mem_Icc.mpr ⟨by have := (mem_Icc.mp hq).1; omega, (mem_Icc.mp hq).2⟩)]
      unfold primePairPlusProfile
      by_cases h2 : q = 2
      · subst h2; simp
      by_cases h3 : q = 3
      · subst h3; simp
      simp [h2, h3]
    rw [sum_congr rfl hterm, sum_add_distrib]
    have h2 : 2 ∈ Icc 2 N := mem_Icc.mpr ⟨le_rfl, by omega⟩
    have h3 : 3 ∈ Icc 2 N := mem_Icc.mpr ⟨by omega, hN⟩
    simp [h2, h3]
  have hminus : sieveSeq N (primePairMinusWeight N) k =
      ramanujanLagCoefficient 2 k - ramanujanLagCoefficient 3 k := by
    rw [SieveMoments.sieveSeq_ramanujan_expansion, hIcc, sum_insert h1]
    have hY1 : selbergMultiplesCoord N (primePairMinusWeight N) 1 = 0 := by
      rw [selbergMultiplesCoord_primePairMinusWeight (mem_Icc.mpr ⟨le_rfl, by omega⟩)]
      simp [primePairMinusProfile]
    rw [hY1, zero_mul, zero_add]
    have hterm : ∀ q ∈ Icc 2 N,
        selbergMultiplesCoord N (primePairMinusWeight N) q * ramanujanLagCoefficient q k =
          (if q = 2 then ramanujanLagCoefficient 2 k else 0) -
            (if q = 3 then ramanujanLagCoefficient 3 k else 0) := by
      intro q hq
      rw [selbergMultiplesCoord_primePairMinusWeight
        (mem_Icc.mpr ⟨by have := (mem_Icc.mp hq).1; omega, (mem_Icc.mp hq).2⟩)]
      unfold primePairMinusProfile
      by_cases h2 : q = 2
      · subst h2; simp
      by_cases h3 : q = 3
      · subst h3; simp
      simp [h2, h3]
    rw [sum_congr rfl hterm, sum_sub_distrib]
    have h2 : 2 ∈ Icc 2 N := mem_Icc.mpr ⟨le_rfl, by omega⟩
    have h3 : 3 ∈ Icc 2 N := mem_Icc.mpr ⟨by omega, hN⟩
    simp [h2, h3]
  exact ⟨hplus, hminus, by linarith⟩

/-- At every integer `k`, the Ramanujan sum `c_3(k) = ramanujanLagCoefficient 3 k` is either
`2` (when `3 ∣ k`) or `-1` (when `¬ 3 ∣ k`), and in particular never vanishes. -/
theorem ramanujanLagCoefficient_three_eq_ite (k : ℕ) :
    ramanujanLagCoefficient 3 k = (if 3 ∣ k then 2 else -1) ∧
      ramanujanLagCoefficient 3 k ≠ 0 := by
  have heq : ramanujanLagCoefficient 3 k = if 3 ∣ k then 2 else -1 := by
    rw [← ramanujanLagWeight_eq_ramanujanLagCoefficient, ramanujanLagWeight_eq_sum_divisors]
    have hdiv3 : (3 : ℕ).divisors = {1, 3} := by decide
    rw [hdiv3, sum_insert (by decide), sum_singleton]
    have hmu3 : (μ 3 : ℝ) = -1 := by
      rw [ArithmeticFunction.moebius_apply_prime Nat.prime_three]; norm_num
    have hmu1 : (μ (3 / 3) : ℝ) = 1 := by norm_num
    have h1 : 1 ∣ k := one_dvd k
    rw [if_pos h1, show 3 / 1 = 3 by rfl, hmu3, hmu1]
    by_cases h3 : 3 ∣ k <;> simp [h3]; norm_num
  refine ⟨heq, ?_⟩
  rw [heq]
  split_ifs <;> norm_num

/-- **Trans-horizon separation of `primePairPlusWeight N` and `primePairMinusWeight N` (`N ≥ 3`):**
Although `primePairPlusWeight N` and `primePairMinusWeight N` have identical complete-period
quadratic forms:
1. Their pointwise responses `sieveSeq N _ k` are strictly unequal at **every** `k ∈ ℕ` (and in
   particular at the first trans-horizon point `k = N + 1 > N`).
2. Their prefix discrepancies satisfy
   `sievePrefixDiscrepancy N M (primePairPlusWeight N) - sievePrefixDiscrepancy N M (primePairMinusWeight N) = -2 * ((M % 3 : ℕ) : ℝ)`
   for every `M`, which equals `-2 ≠ 0` at `M = 1` and at the trans-horizon point `M = 3 * N + 1 > N`.
3. Their von Mangoldt pronic readouts are `log 2 + log 3` vs. `log 2 - log 3`, hence strictly
   unequal (`vonMangoldtReadout N (primePairPlusWeight N) - vonMangoldtReadout N (primePairMinusWeight N) = 2 * log 3 > 0`).
4. Their first pronic discrepancy energy terms `(sievePrefixDiscrepancy N 1 _)^2 / pronicSeq 1` are
   `2` vs. `0`, and their first renormalized prefix defects `sieveRenormalizedPrefixDefect N 1`
   are `-4` vs. `0`. -/
theorem primePairWeights_transHorizon_separated {N : ℕ} (hN : 3 ≤ N) :
    (∀ k : ℕ, sieveSeq N (primePairPlusWeight N) k ≠ sieveSeq N (primePairMinusWeight N) k) ∧
    sieveSeq N (primePairPlusWeight N) (N + 1) ≠ sieveSeq N (primePairMinusWeight N) (N + 1) ∧
    (∀ M : ℕ, sievePrefixDiscrepancy N M (primePairPlusWeight N) -
        sievePrefixDiscrepancy N M (primePairMinusWeight N) = -2 * ((M % 3 : ℕ) : ℝ)) ∧
    sievePrefixDiscrepancy N (3 * N + 1) (primePairPlusWeight N) -
        sievePrefixDiscrepancy N (3 * N + 1) (primePairMinusWeight N) = -2 ∧
    vonMangoldtReadout N (primePairPlusWeight N) = Real.log 2 + Real.log 3 ∧
    vonMangoldtReadout N (primePairMinusWeight N) = Real.log 2 - Real.log 3 ∧
    vonMangoldtReadout N (primePairPlusWeight N) ≠ vonMangoldtReadout N (primePairMinusWeight N) ∧
    (sievePrefixDiscrepancy N 1 (primePairPlusWeight N)) ^ 2 / (pronicSeq 1 : ℝ) = 2 ∧
    (sievePrefixDiscrepancy N 1 (primePairMinusWeight N)) ^ 2 / (pronicSeq 1 : ℝ) = 0 ∧
    sieveRenormalizedPrefixDefect N 1 (primePairPlusWeight N) = -4 ∧
    sieveRenormalizedPrefixDefect N 1 (primePairMinusWeight N) = 0 := by
  have hseq_ne : ∀ k : ℕ,
      sieveSeq N (primePairPlusWeight N) k ≠ sieveSeq N (primePairMinusWeight N) k := by
    intro k heq
    have hdiff := (sieveSeq_primePairWeights_eq hN k).2.2
    rw [heq, sub_self] at hdiff
    exact (ramanujanLagCoefficient_three_eq_ite k).2 (by linarith)
  have hdisc_plus : ∀ M : ℕ,
      sievePrefixDiscrepancy N M (primePairPlusWeight N) =
        -((M % 2 : ℕ) : ℝ) - ((M % 3 : ℕ) : ℝ) := by
    intro M
    rw [sievePrefixDiscrepancy_eq_ramanujan_diagonal]
    have hterm : ∀ q ∈ Icc 2 N,
        (pmRamanujanPrimitive q M).re * selbergMultiplesCoord N (primePairPlusWeight N) q =
          (if q = 2 then (pmRamanujanPrimitive 2 M).re else 0) +
            (if q = 3 then (pmRamanujanPrimitive 3 M).re else 0) := by
      intro q hq
      rw [selbergMultiplesCoord_primePairPlusWeight
        (mem_Icc.mpr ⟨by have := (mem_Icc.mp hq).1; omega, (mem_Icc.mp hq).2⟩)]
      unfold primePairPlusProfile
      by_cases h2 : q = 2
      · subst h2; simp
      by_cases h3 : q = 3
      · subst h3; simp
      simp [h2, h3]
    rw [sum_congr rfl hterm, sum_add_distrib]
    have h2 : 2 ∈ Icc 2 N := mem_Icc.mpr ⟨le_rfl, by omega⟩
    have h3 : 3 ∈ Icc 2 N := mem_Icc.mpr ⟨by omega, hN⟩
    simp only [sum_ite_eq', h2, h3, if_true]
    rw [pmRamanujanPrimitive_prime Nat.prime_two M, pmRamanujanPrimitive_prime Nat.prime_three M]
    simp [sub_eq_add_neg]
  have hdisc_minus : ∀ M : ℕ,
      sievePrefixDiscrepancy N M (primePairMinusWeight N) =
        -((M % 2 : ℕ) : ℝ) + ((M % 3 : ℕ) : ℝ) := by
    intro M
    rw [sievePrefixDiscrepancy_eq_ramanujan_diagonal]
    have hterm : ∀ q ∈ Icc 2 N,
        (pmRamanujanPrimitive q M).re * selbergMultiplesCoord N (primePairMinusWeight N) q =
          (if q = 2 then (pmRamanujanPrimitive 2 M).re else 0) -
            (if q = 3 then (pmRamanujanPrimitive 3 M).re else 0) := by
      intro q hq
      rw [selbergMultiplesCoord_primePairMinusWeight
        (mem_Icc.mpr ⟨by have := (mem_Icc.mp hq).1; omega, (mem_Icc.mp hq).2⟩)]
      unfold primePairMinusProfile
      by_cases h2 : q = 2
      · subst h2; simp
      by_cases h3 : q = 3
      · subst h3; simp
      simp [h2, h3]
    rw [sum_congr rfl hterm, sum_sub_distrib]
    have h2 : 2 ∈ Icc 2 N := mem_Icc.mpr ⟨le_rfl, by omega⟩
    have h3 : 3 ∈ Icc 2 N := mem_Icc.mpr ⟨by omega, hN⟩
    simp only [sum_ite_eq', h2, h3, if_true]
    rw [pmRamanujanPrimitive_prime Nat.prime_two M, pmRamanujanPrimitive_prime Nat.prime_three M]
    simp [sub_eq_add_neg]
  have hdisc_sub : ∀ M : ℕ,
      sievePrefixDiscrepancy N M (primePairPlusWeight N) -
        sievePrefixDiscrepancy N M (primePairMinusWeight N) = -2 * ((M % 3 : ℕ) : ℝ) := by
    intro M
    rw [hdisc_plus M, hdisc_minus M]
    ring
  have hvm_plus : vonMangoldtReadout N (primePairPlusWeight N) = Real.log 2 + Real.log 3 := by
    unfold vonMangoldtReadout
    have hterm : ∀ q ∈ Icc 2 N,
        vonMangoldt q * selbergMultiplesCoord N (primePairPlusWeight N) q =
          (if q = 2 then vonMangoldt 2 else 0) + (if q = 3 then vonMangoldt 3 else 0) := by
      intro q hq
      rw [selbergMultiplesCoord_primePairPlusWeight
        (mem_Icc.mpr ⟨by have := (mem_Icc.mp hq).1; omega, (mem_Icc.mp hq).2⟩)]
      unfold primePairPlusProfile
      by_cases h2 : q = 2
      · subst h2; simp
      by_cases h3 : q = 3
      · subst h3; simp
      simp [h2, h3]
    rw [sum_congr rfl hterm, sum_add_distrib]
    have h2 : 2 ∈ Icc 2 N := mem_Icc.mpr ⟨le_rfl, by omega⟩
    have h3 : 3 ∈ Icc 2 N := mem_Icc.mpr ⟨by omega, hN⟩
    simp [h2, h3, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two,
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three]
  have hvm_minus : vonMangoldtReadout N (primePairMinusWeight N) = Real.log 2 - Real.log 3 := by
    unfold vonMangoldtReadout
    have hterm : ∀ q ∈ Icc 2 N,
        vonMangoldt q * selbergMultiplesCoord N (primePairMinusWeight N) q =
          (if q = 2 then vonMangoldt 2 else 0) - (if q = 3 then vonMangoldt 3 else 0) := by
      intro q hq
      rw [selbergMultiplesCoord_primePairMinusWeight
        (mem_Icc.mpr ⟨by have := (mem_Icc.mp hq).1; omega, (mem_Icc.mp hq).2⟩)]
      unfold primePairMinusProfile
      by_cases h2 : q = 2
      · subst h2; simp
      by_cases h3 : q = 3
      · subst h3; simp
      simp [h2, h3]
    rw [sum_congr rfl hterm, sum_sub_distrib]
    have h2 : 2 ∈ Icc 2 N := mem_Icc.mpr ⟨le_rfl, by omega⟩
    have h3 : 3 ∈ Icc 2 N := mem_Icc.mpr ⟨by omega, hN⟩
    simp [h2, h3, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two,
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three]
  have hvm_ne : vonMangoldtReadout N (primePairPlusWeight N) ≠
      vonMangoldtReadout N (primePairMinusWeight N) := by
    rw [hvm_plus, hvm_minus]
    have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    linarith
  have hc2_1 : ramanujanLagCoefficient 2 1 = -1 := by
    rw [← ramanujanLagWeight_eq_ramanujanLagCoefficient, ramanujanLagWeight_one_left]
    simp [ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  have hc2_2 : ramanujanLagCoefficient 2 2 = 1 := by
    rw [← ramanujanLagWeight_eq_ramanujanLagCoefficient, ramanujanLagWeight_eq_sum_divisors]
    have hdiv2 : (2 : ℕ).divisors = {1, 2} := by decide
    rw [hdiv2, sum_insert (by decide), sum_singleton]
    simp [ArithmeticFunction.moebius_apply_prime Nat.prime_two]; norm_num
  have hc3_1 : ramanujanLagCoefficient 3 1 = -1 := by
    rw [(ramanujanLagCoefficient_three_eq_ite 1).1, if_neg (by decide)]
  have hc3_2 : ramanujanLagCoefficient 3 2 = -1 := by
    rw [(ramanujanLagCoefficient_three_eq_ite 2).1, if_neg (by decide)]
  have hren_plus : sieveRenormalizedPrefixDefect N 1 (primePairPlusWeight N) = -4 := by
    rw [sieveRenormalizedPrefixDefect_eq_succ_sub_sq, Icc_self, sum_singleton, sum_singleton,
      (sieveSeq_primePairWeights_eq hN 1).1, (sieveSeq_primePairWeights_eq hN 2).1,
      hc2_1, hc2_2, hc3_1, hc3_2]
    norm_num
  have hren_minus : sieveRenormalizedPrefixDefect N 1 (primePairMinusWeight N) = 0 := by
    rw [sieveRenormalizedPrefixDefect_eq_succ_sub_sq, Icc_self, sum_singleton, sum_singleton,
      (sieveSeq_primePairWeights_eq hN 1).2.1, (sieveSeq_primePairWeights_eq hN 2).2.1,
      hc2_1, hc2_2, hc3_1, hc3_2]
    norm_num
  refine ⟨hseq_ne, hseq_ne (N + 1), hdisc_sub, ?_, hvm_plus, hvm_minus, hvm_ne, ?_, ?_,
    hren_plus, hren_minus⟩
  · rw [hdisc_sub (3 * N + 1)]
    have hmod : (3 * N + 1) % 3 = 1 := by omega
    rw [hmod]
    norm_num
  · rw [hdisc_plus 1, cast_pronicSeq_eq 1]
    norm_num
  · rw [hdisc_minus 1, cast_pronicSeq_eq 1]
    norm_num

end
end GaloisForLFunctions.BezoutValuationIncidence
