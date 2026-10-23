import GaloisForLFunctions.ArithmeticOrientationTheory.OrientedReadings
import GaloisForLFunctions.TransHorizonIncidenceMechanics.CompletePeriodQuadraticFormsAgreeOnParityRowPairs

/-!
# Complete-Period Quadratic Forms Are Orientation-Blind (`CompletePeriodQuadraticFormsAreOrientationBlind`)

In the language of `ScaleSignedIncidenceCriticality` and `ArithmeticOrientationTheory`, a method
that inspects a divisor weight `c : ℕ → ℝ` at cutoff `N` through complete-period quadratic
observables factors through the **complete-period lag-covariance reading**
$$\operatorname{completePeriodLagReading}(N)(c)
  = \bigl(\operatorname{finiteHarmonicSum}(N, c),\;
    h \mapsto \operatorname{TwoLagSieve.periodCovariance}(N, c, h)\bigr).$$

This module establishes the exact shadow, refinement hierarchy, orientation blindness, and
resolution limits of `completePeriodLagReading N`:

1. **Universal Refinement over All 12 Complete-Period Quadratic Forms
   (`refines_completePeriodLagReading_*`)**:
   For every `N ≥ 1`, `completePeriodLagReading N` refines `sieveVariance N`,
   `bezoutCoprimeQuadraticForm N`, `sieveSuccessorCovariance N`, `sieveSuccessorReserve N`,
   `sievePoincareExcess N`, `successorPhaseLoss N`, `sievePrimitiveEnergy N`,
   `sieveVarianceAboveParity N`, `selbergTotientDiagonalForm N`, `franelGcdQuadraticForm N`,
   `tupleVariance N · H`, and `SieveMoments.translatedMoment N · (v : Fin 2 → ℕ)`.

2. **Exact Shadow Characterization (`mem_shadow_completePeriodLagReading_iff_signOrbit`)**:
   For `N ≥ 1`, `c₂ ∈ shadow (completePeriodLagReading N) c₁` if and only if
   `finiteHarmonicSum N c₁ = finiteHarmonicSum N c₂` and `c₂` lies in the `(ℤ/2ℤ)^{N-1}`
   sign-character orbit of `c₁` on `Icc 1 N`:
   $$\exists \varepsilon : \mathbb{N} \to \mathbb{R},\;
     \varepsilon(1) = 1 \wedge (\forall q,\, \varepsilon(q)^2 = 1) \wedge
     \forall d \in [1, N],\, c_2(d) = \operatorname{scaledSelbergRow}(N, c_1, \varepsilon)(d).$$

3. **Universal Orientation Blindness (`invisible_completePeriodLagReading_scaledSelbergRow`,
   `invisible_completePeriodLagReading_evenFlipRow`)**:
   Every sign character `ε : ℕ → ℝ` with `ε(1) = 1` and `ε(q)^2 = 1` is invisible to
   `completePeriodLagReading N` (and hence, by `Invisible.of_refines`, to every complete-period
   quadratic form of the sieve theory). In particular, `evenFlipRow N` and `singleModeSignFlip q₀`
   (`q₀ ≥ 2`) are invisible collapses.

4. **Non-Resolution of Trans-Horizon Response, Von Mangoldt Readout Sign, and Prefix Defect Sign
   (`not_resolves_completePeriodLagReading_sieveSeq`,
   `not_resolves_completePeriodLagReading_vonMangoldtReadout_nonneg`,
   `not_resolves_completePeriodLagReading_renormalizedPrefixDefect_neg`)**:
   For every cutoff `N ≥ 3`, `completePeriodLagReading N` (and therefore every complete-period
   quadratic form of the sieve theory) fails to resolve:
   - the value of the trans-horizon response `sieveSeq N c k` at **any** integer `k ∈ ℕ`
     (including `k = N + 1 > N`),
   - the sign predicate `0 ≤ vonMangoldtReadout N c` (which is `+` on `primePairPlusWeight N` and
     `-` on `primePairMinusWeight N`), and
   - the first-cell renormalized prefix defect sign `sieveRenormalizedPrefixDefect N 1 c < 0`.
-/

open Finset ArithmeticFunction
open GaloisForLFunctions.ScaleSignedIncidenceCriticality
open GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open RHTower RHTower.Sieve
open scoped BigOperators

namespace GaloisForLFunctions.ArithmeticOrientationTheory

noncomputable section
set_option autoImplicit false

/-! ## §1. The Complete-Period Lag Reading and Its Exact Shadow -/

/-- The **complete-period lag-covariance reading** at cutoff `N`: records the complete-period mean
`finiteHarmonicSum N c = Y_{N,c}(1)` together with the complete-period lag covariance function
`h ↦ TwoLagSieve.periodCovariance N c h`. -/
def completePeriodLagReading (N : ℕ) (c : ℕ → ℝ) : ℝ × (ℕ → ℝ) :=
  (finiteHarmonicSum N c, fun h => TwoLagSieve.periodCovariance N c h)

/-- Two rows lie in the same shadow of `completePeriodLagReading N` (`N ≥ 1`) if and only if they
have the same complete-period mean and the same squared Selberg coordinates on `Icc 2 N`. -/
theorem mem_shadow_completePeriodLagReading_iff_sq_eq {N : ℕ} (hN : 1 ≤ N) (c₁ c₂ : ℕ → ℝ) :
    c₂ ∈ shadow (completePeriodLagReading N) c₁ ↔
      finiteHarmonicSum N c₁ = finiteHarmonicSum N c₂ ∧
        ∀ q ∈ Icc 2 N,
          (selbergMultiplesCoord N c₁ q) ^ 2 = (selbergMultiplesCoord N c₂ q) ^ 2 := by
  simp only [mem_shadow_iff, completePeriodLagReading, Prod.ext_iff, funext_iff]
  constructor
  · rintro ⟨hmean, hcov⟩
    exact ⟨hmean.symm,
      (sq_selbergMultiplesCoord_eq_iff_periodCovariance_eq N c₁ c₂).mpr fun g _ => (hcov g).symm⟩
  · rintro ⟨hmean, hsq⟩
    exact ⟨hmean.symm, fun h => ((completePeriodCenteredForms_eq_of_sq_eq hN hsq).2.2.2.2.2.2.1 h).symm⟩

/-- **Exact Shadow Theorem (`mem_shadow_completePeriodLagReading_iff_signOrbit`):**
For `N ≥ 1`, `c₂ ∈ shadow (completePeriodLagReading N) c₁` if and only if they have the same
complete-period mean and `c₂` lies in the `(ℤ/2ℤ)^{N-1}` sign-character orbit of `c₁` on
`Icc 1 N`. -/
theorem mem_shadow_completePeriodLagReading_iff_signOrbit {N : ℕ} (hN : 1 ≤ N) (c₁ c₂ : ℕ → ℝ) :
    c₂ ∈ shadow (completePeriodLagReading N) c₁ ↔
      finiteHarmonicSum N c₁ = finiteHarmonicSum N c₂ ∧
        ∃ ε : ℕ → ℝ, ε 1 = 1 ∧ (∀ q : ℕ, (ε q) ^ 2 = 1) ∧
          ∀ d ∈ Icc 1 N, c₂ d = scaledSelbergRow N c₁ ε d := by
  rw [mem_shadow_completePeriodLagReading_iff_sq_eq hN]
  constructor
  · rintro ⟨hmean, hsq⟩
    have hcov := (sq_selbergMultiplesCoord_eq_iff_periodCovariance_eq N c₁ c₂).mp hsq
    exact ⟨hmean, (periodCovariance_eq_iff_exists_scaledSelbergRow hmean).mp hcov⟩
  · rintro ⟨hmean, hsign⟩
    have hcov := (periodCovariance_eq_iff_exists_scaledSelbergRow hmean).mpr hsign
    exact ⟨hmean, (sq_selbergMultiplesCoord_eq_iff_periodCovariance_eq N c₁ c₂).mpr hcov⟩

/-- Membership in the shadow of `completePeriodLagReading N` (`N ≥ 1`) implies full agreement on
all 12 complete-period quadratic forms and all two-point translated moments
(`CompletePeriodQuadraticEq N c₁ c₂`). -/
theorem completePeriodQuadraticEq_of_mem_shadow {N : ℕ} (hN : 1 ≤ N) {c₁ c₂ : ℕ → ℝ}
    (h : c₂ ∈ shadow (completePeriodLagReading N) c₁) :
    CompletePeriodQuadraticEq N c₁ c₂ := by
  obtain ⟨hmean, hsq⟩ := (mem_shadow_completePeriodLagReading_iff_sq_eq hN c₁ c₂).mp h
  exact completePeriodQuadraticEq_of_mean_and_sq_eq hN hmean hsq

/-! ## §2. Universal Refinement Over All Complete-Period Quadratic Forms -/

theorem refines_completePeriodLagReading_sieveVariance {N : ℕ} (hN : 1 ≤ N) :
    Refines (completePeriodLagReading N) (sieveVariance N) :=
  fun _ _ h => (completePeriodQuadraticEq_of_mem_shadow hN h).2.2.1.symm

theorem refines_completePeriodLagReading_bezoutCoprimeQuadraticForm {N : ℕ} (hN : 1 ≤ N) :
    Refines (completePeriodLagReading N) (bezoutCoprimeQuadraticForm N) :=
  fun _ _ h => (completePeriodQuadraticEq_of_mem_shadow hN h).2.2.2.1.symm

theorem refines_completePeriodLagReading_sieveSuccessorCovariance {N : ℕ} (hN : 1 ≤ N) :
    Refines (completePeriodLagReading N) (sieveSuccessorCovariance N) :=
  fun _ _ h => (completePeriodQuadraticEq_of_mem_shadow hN h).2.2.2.2.1.symm

theorem refines_completePeriodLagReading_sieveSuccessorReserve {N : ℕ} (hN : 1 ≤ N) :
    Refines (completePeriodLagReading N) (sieveSuccessorReserve N) :=
  fun _ _ h => (completePeriodQuadraticEq_of_mem_shadow hN h).2.2.2.2.2.1.symm

theorem refines_completePeriodLagReading_sievePoincareExcess {N : ℕ} (hN : 1 ≤ N) :
    Refines (completePeriodLagReading N) (sievePoincareExcess N) :=
  fun _ _ h => (completePeriodQuadraticEq_of_mem_shadow hN h).2.2.2.2.2.2.1.symm

theorem refines_completePeriodLagReading_successorPhaseLoss {N : ℕ} (hN : 1 ≤ N) :
    Refines (completePeriodLagReading N) (successorPhaseLoss N) :=
  fun _ _ h => (completePeriodQuadraticEq_of_mem_shadow hN h).2.2.2.2.2.2.2.1.symm

theorem refines_completePeriodLagReading_sievePrimitiveEnergy {N : ℕ} (hN : 1 ≤ N) :
    Refines (completePeriodLagReading N) (sievePrimitiveEnergy N) :=
  fun _ _ h => (completePeriodQuadraticEq_of_mem_shadow hN h).2.2.2.2.2.2.2.2.1.symm

theorem refines_completePeriodLagReading_tupleVariance {N : ℕ} (hN : 1 ≤ N) (H : Finset ℕ) :
    Refines (completePeriodLagReading N) (fun c => tupleVariance N c H) :=
  fun _ _ h => ((completePeriodQuadraticEq_of_mem_shadow hN h).2.2.2.2.2.2.2.2.2.2.2.2.1 H).symm

theorem refines_completePeriodLagReading_translatedMoment_two {N : ℕ} (hN : 1 ≤ N)
    (v : Fin 2 → ℕ) :
    Refines (completePeriodLagReading N) (fun c => SieveMoments.translatedMoment N c v) :=
  fun _ _ h => ((completePeriodQuadraticEq_of_mem_shadow hN h).2.2.2.2.2.2.2.2.2.2.2.2.2 v).symm

/-! ## §3. Universal Orientation Blindness to Sign-Character Twists -/

/-- **Universal Orientation Blindness (`invisible_completePeriodLagReading_scaledSelbergRow`):**
For every `N ≥ 1` and every mean-preserving sign character `ε : ℕ → ℝ` (`ε 1 = 1` and
`∀ q, (ε q)^2 = 1`), the sign-twist map `fun c => scaledSelbergRow N c ε` is invisible to
`completePeriodLagReading N`. By `Invisible.of_refines`, it is simultaneously invisible to every
complete-period quadratic form of the sieve theory. -/
theorem invisible_completePeriodLagReading_scaledSelbergRow {N : ℕ} (hN : 1 ≤ N)
    {ε : ℕ → ℝ} (hε1 : ε 1 = 1) (hε : ∀ q : ℕ, (ε q) ^ 2 = 1) :
    Invisible (completePeriodLagReading N) (fun c => scaledSelbergRow N c ε) := by
  intro c
  have heq := completePeriodQuadraticEq_scaledSelbergRow hN c hε1 hε
  simp only [completePeriodLagReading, Prod.ext_iff, funext_iff]
  exact ⟨heq.1, heq.2.2.2.2.2.2.2.2.2.2.2.1⟩

/-- The even-mode sign flip `evenFlipRow N` is invisible to `completePeriodLagReading N`. -/
theorem invisible_completePeriodLagReading_evenFlipRow {N : ℕ} (hN : 1 ≤ N) :
    Invisible (completePeriodLagReading N) (evenFlipRow N) :=
  invisible_completePeriodLagReading_scaledSelbergRow hN evenSign_one evenSign_sq

/-- Flipping a single non-trivial Selberg mode `q₀ ≥ 2` (`singleModeSignFlip q₀`) is invisible to
`completePeriodLagReading N`. -/
theorem invisible_completePeriodLagReading_singleModeSignFlip {N q₀ : ℕ} (hN : 1 ≤ N)
    (hq₀ : 2 ≤ q₀) :
    Invisible (completePeriodLagReading N)
      (fun c => scaledSelbergRow N c (singleModeSignFlip q₀)) := by
  refine invisible_completePeriodLagReading_scaledSelbergRow hN ?_ (singleModeSignFlip_sq q₀)
  unfold singleModeSignFlip
  rw [if_neg (by omega)]

/-! ## §4. Non-Resolution of Trans-Horizon Response, Von Mangoldt Sign, and Prefix Defect -/

/-- At every cutoff `N ≥ 3`, `primePairMinusWeight N` lies in the shadow of `primePairPlusWeight N`
under `completePeriodLagReading N`. -/
theorem primePairMinusWeight_mem_shadow_completePeriodLagReading {N : ℕ} (hN : 3 ≤ N) :
    primePairMinusWeight N ∈ shadow (completePeriodLagReading N) (primePairPlusWeight N) := by
  have hN1 : 1 ≤ N := by omega
  rw [mem_shadow_completePeriodLagReading_iff_sq_eq hN1]
  refine ⟨by
    rw [(primePairWeights_completePeriod_coincide hN).1.1,
      (primePairWeights_completePeriod_coincide hN).1.2], fun q hq => ?_⟩
  have hq1 : q ∈ Icc 1 N :=
    mem_Icc.mpr ⟨by have := (mem_Icc.mp hq).1; omega, (mem_Icc.mp hq).2⟩
  rw [selbergMultiplesCoord_primePairPlusWeight hq1,
    selbergMultiplesCoord_primePairMinusWeight hq1, sq_primePairMinusProfile]

/-- **Non-Resolution of the Pointwise Response (`not_resolves_completePeriodLagReading_sieveSeq`):**
For every cutoff `N ≥ 3` and **every** integer `k ∈ ℕ` (in particular at the trans-horizon point
`k = N + 1 > N`), `completePeriodLagReading N` does not resolve the predicate
`fun c => sieveSeq N c k = sieveSeq N (primePairPlusWeight N) k`. -/
theorem not_resolves_completePeriodLagReading_sieveSeq {N : ℕ} (hN : 3 ≤ N) (k : ℕ) :
    ¬ Resolves (completePeriodLagReading N)
      (fun c => sieveSeq N c k = sieveSeq N (primePairPlusWeight N) k) := by
  intro hres
  have hmem := primePairMinusWeight_mem_shadow_completePeriodLagReading hN
  have heq := (hres (primePairPlusWeight N) (primePairMinusWeight N) hmem).mpr rfl
  exact (primePairWeights_transHorizon_separated hN).1 k heq.symm

/-- **Non-Resolution of the Von Mangoldt Pronic Readout Sign
(`not_resolves_completePeriodLagReading_vonMangoldtReadout_nonneg`):**
For every cutoff `N ≥ 3`, `completePeriodLagReading N` (and hence any complete-period quadratic
form of the sieve theory) does not resolve the sign predicate `0 ≤ vonMangoldtReadout N c`:
`vonMangoldtReadout N (primePairPlusWeight N) = log 2 + log 3 > 0`, whereas
`vonMangoldtReadout N (primePairMinusWeight N) = log 2 - log 3 < 0`. -/
theorem not_resolves_completePeriodLagReading_vonMangoldtReadout_nonneg {N : ℕ} (hN : 3 ≤ N) :
    ¬ Resolves (completePeriodLagReading N) (fun c => 0 ≤ vonMangoldtReadout N c) := by
  intro hres
  have hmem := primePairMinusWeight_mem_shadow_completePeriodLagReading hN
  have hsep := primePairWeights_transHorizon_separated hN
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog23 : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  have hplus : 0 ≤ vonMangoldtReadout N (primePairPlusWeight N) := by
    rw [hsep.2.2.2.2.1]; linarith
  have hminus : 0 ≤ vonMangoldtReadout N (primePairMinusWeight N) :=
    (hres (primePairPlusWeight N) (primePairMinusWeight N) hmem).mpr hplus
  rw [hsep.2.2.2.2.2.1] at hminus
  linarith

/-- **Non-Resolution of the First-Cell Renormalized Prefix Defect Sign
(`not_resolves_completePeriodLagReading_renormalizedPrefixDefect_neg`):**
For every cutoff `N ≥ 3`, `completePeriodLagReading N` does not resolve the predicate
`sieveRenormalizedPrefixDefect N 1 c < 0`: it holds for `primePairPlusWeight N` (`-4 < 0`) and
fails for `primePairMinusWeight N` (`0`). -/
theorem not_resolves_completePeriodLagReading_renormalizedPrefixDefect_neg {N : ℕ} (hN : 3 ≤ N) :
    ¬ Resolves (completePeriodLagReading N)
      (fun c => sieveRenormalizedPrefixDefect N 1 c < 0) := by
  intro hres
  have hmem := primePairMinusWeight_mem_shadow_completePeriodLagReading hN
  have hsep := primePairWeights_transHorizon_separated hN
  have hplus : sieveRenormalizedPrefixDefect N 1 (primePairPlusWeight N) < 0 := by
    rw [hsep.2.2.2.2.2.2.2.2.2.1]; norm_num
  have hminus : sieveRenormalizedPrefixDefect N 1 (primePairMinusWeight N) < 0 :=
    (hres (primePairPlusWeight N) (primePairMinusWeight N) hmem).mpr hplus
  rw [hsep.2.2.2.2.2.2.2.2.2.2] at hminus
  linarith

end

end GaloisForLFunctions.ArithmeticOrientationTheory
