import GaloisForLFunctions.ArithmeticIncidencePositivity.FirstOpenWindowTwoAtomLaw
import GaloisForLFunctions.ArithmeticIncidencePositivity.PrimeCombEnergyReduction
import GaloisForLFunctions.ArithmeticOrientationTheory.CompletePeriodQuadraticFormsAreOrientationBlind

/-!
# Complete-Period Quadratic Parity, the Ratio-Lag Comb Energy, and Trans-Horizon Separation (`CompletePeriodQuadraticParityAndTransHorizonSeparation`)

This module resolves Open Problem §7.5 (**Parity**) of `ArithmeticIncidencePositivity` and connects
the complete-period `(ℤ/2ℤ)^N` sign-invariance classification to the prime-comb energy
`combEnergy` of `PrimeCombEnergyReduction` and the two-atom law of `FirstOpenWindowTwoAtomLaw`:

1. **The Parity-Twisted Two-Atom Law (`sq_two_atom_sub_le`, `sq_two_atom_add_sq_sub_le`)**:
   Evaluating the three-shift Gram inequality `three_shift_gram` along the anti-diagonal parity
   ray `λ = θ, μ = -θ` yields the **parity-twisted two-atom law**
   $$\bigl(A_F(a) - A_F(b)\bigr)^2 \le 2 A_F(0)\bigl(A_F(0) - A_F(b - a)\bigr).$$
   Combining `sq_two_atom_le` (the `(+1, +1)` ray `primePairPlusProfile`) with `sq_two_atom_sub_le`
   (the `(+1, -1)` ray `primePairMinusProfile`) eliminates the ratio-lag coupling `A_F(b - a)` by
   `(ℤ/2ℤ)` sign averaging and yields the unconditional Bessel bound
   $$A_F(a)^2 + A_F(b)^2 \le A_F(0)^2.$$

2. **Single-Mode Sign Flip of the Prime-Comb Energy (`combEnergy_singleModeSignFlip_sub`)**:
   Whereas every complete-period quadratic form of the sieve theory is diagonal in the Selberg
   coordinates `Y_{N,c}(q)` and therefore invariant under `singleModeSignFlip p₀`, the Archimedean
   prime-comb energy `combEnergy F s w = ∑_{p,q ∈ s} w(p) w(q) A_F(log q - log p)` transforms
   under a single-mode sign flip at `p₀ ∈ s` by
   $$E_{\sigma_{p_0} w}(F) - E_w(F)
     = -4 w(p_0) \sum_{q \in s \setminus \{p_0\}} w(q)\, A_F(\log q - \log p_0).$$

3. **Evaluating `combEnergy` on the Separated Pair `primePairPlusWeight N` vs.
   `primePairMinusWeight N` (`combEnergy_primePairWeights_eq`)**:
   For every cutoff `N ≥ 3` and every continuous compactly supported test `F : ℝ → ℝ`, feeding the
   Selberg coordinate profiles `selbergMultiplesCoord N (primePairPlusWeight N)` and
   `selbergMultiplesCoord N (primePairMinusWeight N)` into `combEnergy F (Icc 2 N)` gives:
   - $E_{Y^+}(F) = 2 A_F(0) + 2 A_F(\log 3 - \log 2)$,
   - $E_{Y^-}(F) = 2 A_F(0) - 2 A_F(\log 3 - \log 2)$,
   - $E_{Y^+}(F) + E_{Y^-}(F) = 4 A_F(0)$ (the sign-invariant diagonal part),
   - $E_{Y^+}(F) - E_{Y^-}(F) = 4 A_F(\log 3 - \log 2)$ (the exact ratio-lag coupling of the first
     open window `r ∈ (221/400, log 2)`).

4. **Definitive Resolution of §7.5 (`completePeriod_parity_and_transHorizon_separation`)**:
   Complete-period quadratic forms of the sieve theory (variance, Bézout coprime successor form,
   centered successor covariance, successor reserve, torus Poincaré excess, one-step phase loss,
   sawtooth primitive energy, two-lag and all-lag complete-period covariances, tuple variances, and
   two-point translated moments) are **all** even functions of the Selberg coordinates and hence
   invariant under every sign character on `Y_{N,c}`, with bidirectional orbit characterization
   `completePeriodQuadraticForms_eq_iff_signOrbit`; whereas the pointwise trans-horizon response
   `sieveSeq N c k`, the prefix discrepancy `sievePrefixDiscrepancy N M c`, the von Mangoldt
   pronic readout `vonMangoldtReadout N c`, the trans-horizon pronic receiver `horizonPronicEnergy`,
   and the Archimedean prime-comb energy `combEnergy` are **not** sign-invariant, separated
   explicitly by `(primePairPlusWeight N, primePairMinusWeight N)` at every finite cutoff `N ≥ 3`
   and by `(chiFourRow ε N, chiFourTwinRow ε N)` and `(fermiRow ε N, evenFlipRow N (fermiRow ε N))`
   across all horizons.
-/

open Finset MeasureTheory ArithmeticFunction
open GaloisForLFunctions.ArithmeticCriticalityTheory
open GaloisForLFunctions.ScaleSignedIncidenceCriticality
open GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open GaloisForLFunctions.ArithmeticOrientationTheory
open RHTower RHTower.Sieve
open scoped BigOperators

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

set_option autoImplicit false

variable {F : ℝ → ℝ}

/-! ## §1. The Parity-Twisted Two-Atom Law and `(ℤ/2ℤ)` Polarization -/

/-- **The parity-twisted two-atom law (`sq_two_atom_sub_le`):**
For every continuous compactly supported test `F : ℝ → ℝ` and all shifts `a, b : ℝ`,
`(autoCorr F a - autoCorr F b)^2 ≤ 2 * autoCorr F 0 * (autoCorr F 0 - autoCorr F (b - a))`.
Obtained by evaluating `three_shift_gram` along the anti-diagonal parity ray `(λ, μ) = (θ, -θ)`. -/
theorem sq_two_atom_sub_le (hF : Continuous F) (hFc : HasCompactSupport F) (a b : ℝ) :
    (autoCorr F a - autoCorr F b) ^ 2
      ≤ 2 * autoCorr F 0 * (autoCorr F 0 - autoCorr F (b - a)) := by
  have hquad : ∀ θ : ℝ, 0 ≤ (2 * autoCorr F 0 - 2 * autoCorr F (b - a)) * (θ * θ)
      + (-2 * (autoCorr F a - autoCorr F b)) * θ + autoCorr F 0 := by
    intro θ
    have h := three_shift_gram hF hFc θ (-θ) a b
    nlinarith [h]
  have hdisc := discrim_le_zero hquad
  rw [discrim] at hdisc
  nlinarith [hdisc]

/-- **Sign-averaged two-atom Bessel inequality (`sq_two_atom_add_sq_sub_le`):**
Averaging the symmetric two-atom law `sq_two_atom_le` (`(+1, +1)`Selberg signs) and the
parity-twisted two-atom law `sq_two_atom_sub_le` (`(+1, -1)` Selberg signs) cancels the ratio-lag
term `autoCorr F (b - a)` and gives `(autoCorr F a)^2 + (autoCorr F b)^2 ≤ (autoCorr F 0)^2`. -/
theorem sq_two_atom_add_sq_sub_le (hF : Continuous F) (hFc : HasCompactSupport F) (a b : ℝ) :
    autoCorr F a ^ 2 + autoCorr F b ^ 2 ≤ autoCorr F 0 ^ 2 := by
  have hplus := sq_two_atom_le hF hFc a b
  have hminus := sq_two_atom_sub_le hF hFc a b
  nlinarith [hplus, hminus]

/-! ## §2. Single-Mode Sign Flip of the Prime-Comb Energy -/

/-- **Single-mode sign flip of `combEnergy` (`combEnergy_singleModeSignFlip_sub`):**
Flipping the sign of `w` at a single modulus `p₀ ∈ s` leaves the diagonal energy
`(∑ p ∈ s, w p ^ 2) * autoCorr F 0` invariant and shifts `combEnergy F s w` by
`-4 * w p₀ * ∑ q ∈ s.erase p₀, w q * autoCorr F (Real.log q - Real.log p₀)`. -/
theorem combEnergy_singleModeSignFlip_sub {s : Finset ℕ} {p₀ : ℕ} (hp₀ : p₀ ∈ s) (w : ℕ → ℝ) :
    combEnergy F s (fun p => singleModeSignFlip p₀ p * w p) - combEnergy F s w =
      -4 * w p₀ * ∑ q ∈ s.erase p₀, w q * autoCorr F (Real.log q - Real.log p₀) := by
  unfold combEnergy
  rw [← add_sum_erase _ _ hp₀, ← add_sum_erase _ (fun p => ∑ q ∈ s, w p * w q * _) hp₀]
  have hrow_p₀ :
      (∑ q ∈ s,
          (singleModeSignFlip p₀ p₀ * w p₀) * (singleModeSignFlip p₀ q * w q) *
            autoCorr F (Real.log q - Real.log p₀)) -
        (∑ q ∈ s, w p₀ * w q * autoCorr F (Real.log q - Real.log p₀)) =
      -2 * w p₀ * ∑ q ∈ s.erase p₀, w q * autoCorr F (Real.log q - Real.log p₀) := by
    rw [← add_sum_erase _ _ hp₀, ← add_sum_erase _ (fun q => w p₀ * w q * _) hp₀]
    have hp₀_flip : singleModeSignFlip p₀ p₀ = -1 := by simp [singleModeSignFlip]
    rw [hp₀_flip, mul_sum, ← sum_sub_distrib]
    have hdiag : ((-1 * w p₀) * (-1 * w p₀) * autoCorr F (Real.log p₀ - Real.log p₀) +
        ∑ x ∈ s.erase p₀,
          (-1 * w p₀) * (singleModeSignFlip p₀ x * w x) * autoCorr F (Real.log x - Real.log p₀)) -
        (w p₀ * w p₀ * autoCorr F (Real.log p₀ - Real.log p₀) +
          ∑ x ∈ s.erase p₀, w p₀ * w x * autoCorr F (Real.log x - Real.log p₀)) =
        ∑ x ∈ s.erase p₀,
          ((-1 * w p₀) * (singleModeSignFlip p₀ x * w x) * autoCorr F (Real.log x - Real.log p₀) -
            w p₀ * w x * autoCorr F (Real.log x - Real.log p₀)) := by
      rw [← sum_sub_distrib]; ring
    rw [hdiag, ← sum_sub_distrib]
    have hzero : ∀ x ∈ s.erase p₀,
        ((-1 * w p₀) * (singleModeSignFlip p₀ x * w x) * autoCorr F (Real.log x - Real.log p₀) -
          w p₀ * w x * autoCorr F (Real.log x - Real.log p₀)) -
        (-2 * w p₀ * (w x * autoCorr F (Real.log x - Real.log p₀))) = 0 := by
      intro x hx
      have hx_ne : x ≠ p₀ := (mem_erase.mp hx).1
      have hx_flip : singleModeSignFlip p₀ x = 1 := by simp [singleModeSignFlip, hx_ne]
      rw [hx_flip]; ring
    exact sub_eq_zero.mp (by rw [← sum_sub_distrib]; exact sum_eq_zero hzero)
  have hcol_p₀ :
      (∑ p ∈ s.erase p₀,
          ∑ q ∈ s,
            (singleModeSignFlip p₀ p * w p) * (singleModeSignFlip p₀ q * w q) *
              autoCorr F (Real.log q - Real.log p)) -
        (∑ p ∈ s.erase p₀, ∑ q ∈ s, w p * w q * autoCorr F (Real.log q - Real.log p)) =
      -2 * w p₀ * ∑ p ∈ s.erase p₀, w p * autoCorr F (Real.log p - Real.log p₀) := by
    rw [← sum_sub_distrib, mul_sum]
    refine sum_congr rfl fun p hp => ?_
    have hp_ne : p ≠ p₀ := (mem_erase.mp hp).1
    have hp_flip : singleModeSignFlip p₀ p = 1 := by simp [singleModeSignFlip, hp_ne]
    rw [← add_sum_erase _ _ hp₀, ← add_sum_erase _ (fun q => w p * w q * _) hp₀]
    have hp₀_flip : singleModeSignFlip p₀ p₀ = -1 := by simp [singleModeSignFlip]
    have hrest :
        (∑ x ∈ s.erase p₀,
            (singleModeSignFlip p₀ p * w p) * (singleModeSignFlip p₀ x * w x) *
              autoCorr F (Real.log x - Real.log p)) =
          ∑ x ∈ s.erase p₀, w p * w x * autoCorr F (Real.log x - Real.log p) := by
      refine sum_congr rfl fun x hx => ?_
      have hx_ne : x ≠ p₀ := (mem_erase.mp hx).1
      have hx_flip : singleModeSignFlip p₀ x = 1 := by simp [singleModeSignFlip, hx_ne]
      rw [hp_flip, hx_flip, one_mul, one_mul]
    rw [hrest, hp_flip, hp₀_flip,
      show Real.log p₀ - Real.log p = -(Real.log p - Real.log p₀) by ring, autoCorr_neg]
    ring
  linarith [hrow_p₀, hcol_p₀]

/-! ## §3. Comb Energy on `primePairPlusWeight N` vs. `primePairMinusWeight N` -/

/-- **Prime-comb energy of the separated pair (`combEnergy_primePairWeights_eq`):**
For every cutoff `N ≥ 3`, evaluating `combEnergy F (Icc 2 N)` on the Selberg coordinate profiles
of `primePairPlusWeight N` and `primePairMinusWeight N` gives:
- `combEnergy F (Icc 2 N) (selbergMultiplesCoord N (primePairPlusWeight N)) = 2 * autoCorr F 0 + 2 * autoCorr F (Real.log 3 - Real.log 2)`,
- `combEnergy F (Icc 2 N) (selbergMultiplesCoord N (primePairMinusWeight N)) = 2 * autoCorr F 0 - 2 * autoCorr F (Real.log 3 - Real.log 2)`,
- their difference is `4 * autoCorr F (Real.log 3 - Real.log 2)`, isolating the ratio-lag
  correlation of the first open window `FirstOpenWindowTwoAtomLaw`. -/
theorem combEnergy_primePairWeights_eq {N : ℕ} (hN : 3 ≤ N) :
    combEnergy F (Icc 2 N) (selbergMultiplesCoord N (primePairPlusWeight N)) =
        2 * autoCorr F 0 + 2 * autoCorr F (Real.log 3 - Real.log 2) ∧
      combEnergy F (Icc 2 N) (selbergMultiplesCoord N (primePairMinusWeight N)) =
        2 * autoCorr F 0 - 2 * autoCorr F (Real.log 3 - Real.log 2) ∧
      combEnergy F (Icc 2 N) (selbergMultiplesCoord N (primePairPlusWeight N)) -
          combEnergy F (Icc 2 N) (selbergMultiplesCoord N (primePairMinusWeight N)) =
        4 * autoCorr F (Real.log 3 - Real.log 2) := by
  have hsub : ({2, 3} : Finset ℕ) ⊆ Icc 2 N := by
    intro q hq
    simp only [mem_insert, mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact mem_Icc.mpr ⟨le_rfl, by omega⟩
    · exact mem_Icc.mpr ⟨by omega, hN⟩
  have hplus_supp : ∀ q ∈ Icc 2 N, q ∉ ({2, 3} : Finset ℕ) →
      selbergMultiplesCoord N (primePairPlusWeight N) q = 0 := by
    intro q hq hnot
    rw [selbergMultiplesCoord_primePairPlusWeight
      (mem_Icc.mpr ⟨by have := (mem_Icc.mp hq).1; omega, (mem_Icc.mp hq).2⟩)]
    simp only [mem_insert, mem_singleton, not_or] at hnot
    simp [primePairPlusProfile, hnot.1, hnot.2]
  have hminus_supp : ∀ q ∈ Icc 2 N, q ∉ ({2, 3} : Finset ℕ) →
      selbergMultiplesCoord N (primePairMinusWeight N) q = 0 := by
    intro q hq hnot
    rw [selbergMultiplesCoord_primePairMinusWeight
      (mem_Icc.mpr ⟨by have := (mem_Icc.mp hq).1; omega, (mem_Icc.mp hq).2⟩)]
    simp only [mem_insert, mem_singleton, not_or] at hnot
    simp [primePairMinusProfile, hnot.1, hnot.2]
  have h2_mem : (2 : ℕ) ∈ Icc 1 N := mem_Icc.mpr ⟨by omega, by omega⟩
  have h3_mem : (3 : ℕ) ∈ Icc 1 N := mem_Icc.mpr ⟨by omega, hN⟩
  have hY2_plus : selbergMultiplesCoord N (primePairPlusWeight N) 2 = 1 := by
    rw [selbergMultiplesCoord_primePairPlusWeight h2_mem]; simp [primePairPlusProfile]
  have hY3_plus : selbergMultiplesCoord N (primePairPlusWeight N) 3 = 1 := by
    rw [selbergMultiplesCoord_primePairPlusWeight h3_mem]; simp [primePairPlusProfile]
  have hY2_minus : selbergMultiplesCoord N (primePairMinusWeight N) 2 = 1 := by
    rw [selbergMultiplesCoord_primePairMinusWeight h2_mem]; simp [primePairMinusProfile]
  have hY3_minus : selbergMultiplesCoord N (primePairMinusWeight N) 3 = -1 := by
    rw [selbergMultiplesCoord_primePairMinusWeight h3_mem]; simp [primePairMinusProfile]
  have hplus_eq : combEnergy F (Icc 2 N) (selbergMultiplesCoord N (primePairPlusWeight N)) =
      2 * autoCorr F 0 + 2 * autoCorr F (Real.log 3 - Real.log 2) := by
    unfold combEnergy
    rw [← sum_subset hsub (fun p hp hnot => by
      rw [hplus_supp p hp hnot]; simp)]
    have hinner : ∀ p ∈ ({2, 3} : Finset ℕ),
        (∑ q ∈ Icc 2 N,
            selbergMultiplesCoord N (primePairPlusWeight N) p *
              selbergMultiplesCoord N (primePairPlusWeight N) q *
              autoCorr F (Real.log q - Real.log p)) =
          ∑ q ∈ ({2, 3} : Finset ℕ),
            selbergMultiplesCoord N (primePairPlusWeight N) p *
              selbergMultiplesCoord N (primePairPlusWeight N) q *
              autoCorr F (Real.log q - Real.log p) :=
      fun p _ => (sum_subset hsub fun q hq hnot => by rw [hplus_supp q hq hnot]; ring).symm
    rw [sum_congr rfl hinner, sum_pair (by decide), sum_pair (by decide), sum_pair (by decide),
      hY2_plus, hY3_plus, sub_self, sub_self,
      show Real.log 2 - Real.log 3 = -(Real.log 3 - Real.log 2) by ring, autoCorr_neg]
    ring
  have hminus_eq : combEnergy F (Icc 2 N) (selbergMultiplesCoord N (primePairMinusWeight N)) =
      2 * autoCorr F 0 - 2 * autoCorr F (Real.log 3 - Real.log 2) := by
    unfold combEnergy
    rw [← sum_subset hsub (fun p hp hnot => by
      rw [hminus_supp p hp hnot]; simp)]
    have hinner : ∀ p ∈ ({2, 3} : Finset ℕ),
        (∑ q ∈ Icc 2 N,
            selbergMultiplesCoord N (primePairMinusWeight N) p *
              selbergMultiplesCoord N (primePairMinusWeight N) q *
              autoCorr F (Real.log q - Real.log p)) =
          ∑ q ∈ ({2, 3} : Finset ℕ),
            selbergMultiplesCoord N (primePairMinusWeight N) p *
              selbergMultiplesCoord N (primePairMinusWeight N) q *
              autoCorr F (Real.log q - Real.log p) :=
      fun p _ => (sum_subset hsub fun q hq hnot => by rw [hminus_supp q hq hnot]; ring).symm
    rw [sum_congr rfl hinner, sum_pair (by decide), sum_pair (by decide), sum_pair (by decide),
      hY2_minus, hY3_minus, sub_self, sub_self,
      show Real.log 2 - Real.log 3 = -(Real.log 3 - Real.log 2) by ring, autoCorr_neg]
    ring
  exact ⟨hplus_eq, hminus_eq, by linarith⟩

/-! ## §4. Master Synthesis Closing Open Problem §7.5 (Parity) -/

/-- **Definitive Resolution of Open Problem §7.5 (`completePeriod_parity_and_transHorizon_separation`):**
1. **Universal Sign-Character Invariance of Complete-Period Quadratic Forms:**
   For every cutoff `N ≥ 1`, two rows `c₁, c₂ : ℕ → ℝ` with equal complete-period mean
   `finiteHarmonicSum N c₁ = finiteHarmonicSum N c₂` agree on all complete-period quadratic forms
   (`CompletePeriodQuadraticEq N c₁ c₂`: `selbergTotientDiagonalForm`, `sieveVariance`,
   `bezoutCoprimeQuadraticForm`, `sieveSuccessorCovariance`, `sieveSuccessorReserve`,
   `sievePoincareExcess`, `successorPhaseLoss`, `sievePrimitiveEnergy`, `sieveVarianceAboveParity`,
   `franelGcdQuadraticForm`, `TwoLagSieve.periodCovariance N · h` at every lag `h`,
   `tupleVariance N · H` at every shift tuple `H`, and all two-point translated moments) if and
   only if `c₂` lies in the `(ℤ/2ℤ)^{N-1}` sign-character orbit of `c₁` on `Icc 1 N`.
2. **Explicit Finite Separated Pair (`primePairPlusWeight N` vs. `primePairMinusWeight N`):**
   For every `N ≥ 3`, `primePairPlusWeight N` and `primePairMinusWeight N` satisfy
   `CompletePeriodQuadraticEq N` (with mean `0`, variance `3`, Bézout successor form `-2`,
   reserve `5`, phase loss `3/2`, primitive energy `11/12`), yet:
   - their pointwise responses `sieveSeq N _ k` disagree at **every** `k ∈ ℕ` (including the first
     trans-horizon point `k = N + 1 > N`),
   - their prefix discrepancies at `M = 3 * N + 1 > N` differ by `-2`,
   - their von Mangoldt pronic readouts are `log 2 + log 3` vs. `log 2 - log 3`,
   - their first-cell renormalized prefix defects are `-4` vs. `0`, and
   - their Archimedean prime-comb energies `combEnergy F (Icc 2 N)` differ by
     `4 * autoCorr F (Real.log 3 - Real.log 2)`. -/
theorem completePeriod_parity_and_transHorizon_separation {N : ℕ} (hN : 3 ≤ N) :
    (∀ c₁ c₂ : ℕ → ℝ,
      CompletePeriodQuadraticEq N c₁ c₂ ↔
        finiteHarmonicSum N c₁ = finiteHarmonicSum N c₂ ∧
          ∃ ε : ℕ → ℝ, ε 1 = 1 ∧ (∀ q : ℕ, (ε q) ^ 2 = 1) ∧
            ∀ d ∈ Icc 1 N, c₂ d = scaledSelbergRow N c₁ ε d) ∧
    CompletePeriodQuadraticEq N (primePairPlusWeight N) (primePairMinusWeight N) ∧
    (∀ k : ℕ, sieveSeq N (primePairPlusWeight N) k ≠ sieveSeq N (primePairMinusWeight N) k) ∧
    sieveSeq N (primePairPlusWeight N) (N + 1) ≠
      sieveSeq N (primePairMinusWeight N) (N + 1) ∧
    sievePrefixDiscrepancy N (3 * N + 1) (primePairPlusWeight N) -
        sievePrefixDiscrepancy N (3 * N + 1) (primePairMinusWeight N) = -2 ∧
    vonMangoldtReadout N (primePairPlusWeight N) = Real.log 2 + Real.log 3 ∧
    vonMangoldtReadout N (primePairMinusWeight N) = Real.log 2 - Real.log 3 ∧
    sieveRenormalizedPrefixDefect N 1 (primePairPlusWeight N) = -4 ∧
    sieveRenormalizedPrefixDefect N 1 (primePairMinusWeight N) = 0 ∧
    (∀ F : ℝ → ℝ,
      combEnergy F (Icc 2 N) (selbergMultiplesCoord N (primePairPlusWeight N)) -
          combEnergy F (Icc 2 N) (selbergMultiplesCoord N (primePairMinusWeight N)) =
        4 * autoCorr F (Real.log 3 - Real.log 2)) := by
  have hN1 : 1 ≤ N := by omega
  have hiff : ∀ c₁ c₂ : ℕ → ℝ,
      CompletePeriodQuadraticEq N c₁ c₂ ↔
        finiteHarmonicSum N c₁ = finiteHarmonicSum N c₂ ∧
          ∃ ε : ℕ → ℝ, ε 1 = 1 ∧ (∀ q : ℕ, (ε q) ^ 2 = 1) ∧
            ∀ d ∈ Icc 1 N, c₂ d = scaledSelbergRow N c₁ ε d := by
    intro c₁ c₂
    constructor
    · intro h
      have hcov : ∀ g ∈ Icc 1 N,
          TwoLagSieve.periodCovariance N c₁ g = TwoLagSieve.periodCovariance N c₂ g :=
        fun g _ => h.2.2.2.2.2.2.2.2.2.2.2.1 g
      exact ⟨h.1, (periodCovariance_eq_iff_exists_scaledSelbergRow h.1).mp hcov⟩
    · rintro ⟨hmean, hsign⟩
      have hcov := (periodCovariance_eq_iff_exists_scaledSelbergRow hmean).mpr hsign
      have hsq := (sq_selbergMultiplesCoord_eq_iff_periodCovariance_eq N c₁ c₂).mpr hcov
      exact completePeriodQuadraticEq_of_mean_and_sq_eq hN1 hmean hsq
  have hpair_eq : CompletePeriodQuadraticEq N (primePairPlusWeight N) (primePairMinusWeight N) :=
    completePeriodQuadraticEq_of_mem_shadow hN1
      (primePairMinusWeight_mem_shadow_completePeriodLagReading hN)
  have hsep := primePairWeights_transHorizon_separated hN
  exact ⟨hiff, hpair_eq, hsep.1, hsep.2.1, hsep.2.2.2.1, hsep.2.2.2.2.1,
    hsep.2.2.2.2.2.1, hsep.2.2.2.2.2.2.2.2.2.1, hsep.2.2.2.2.2.2.2.2.2.2,
    fun F => (combEnergy_primePairWeights_eq (F := F) hN).2.2⟩

end GaloisForLFunctions.ArithmeticIncidencePositivity
