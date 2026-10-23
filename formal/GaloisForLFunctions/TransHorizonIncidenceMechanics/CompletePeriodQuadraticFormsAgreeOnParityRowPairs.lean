import GaloisForLFunctions.BezoutValuationIncidence.CompletePeriodQuadraticFormsSignInvarianceAndTransHorizonSeparation
import GaloisForLFunctions.TransHorizonIncidenceMechanics.SlidingPeriodPoincareCoercivityAndHarmonicDecomposition
import GaloisForLFunctions.TransHorizonIncidenceMechanics.RealCharacterParityRowsAtEveryHorizon
import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiRowsAgreeInEveryTranslatedMomentAndSplitTheReceiver

/-!
# Complete-Period Quadratic Forms Agree on All Parity Row Pairs While the Trans-Horizon Receiver Splits (`CompletePeriodQuadraticFormsAgreeOnParityRowPairs`)

This module bridges the complete-period quadratic sign-invariance classification of
`BezoutValuationIncidence.CompletePeriodQuadraticFormsSignInvarianceAndTransHorizonSeparation` with
the cofinal parity row pairs of `TransHorizonIncidenceMechanics`:

1. **Invariance of `sievePoincareExcess` (`sievePoincareExcess_eq_of_sq_eq`,
   `sievePoincareExcess_scaledSelbergRow_eq`)**:
   The harmonic-subtracted unit-step torus Poincaré excess
   $$\operatorname{sievePoincareExcess}(N, c)
     = \sum_{e=2}^N \bigl(\varphi(e) - 2\mu(e)\bigr) Y_{N,c}(e)^2$$
   depends only on the squared Selberg coordinates `(Y_{N,c}(2)^2, ..., Y_{N,c}(N)^2)` and is
   therefore invariant under every sign character `ε : ℕ → ℝ` (`ε(e)^2 = 1`) on the Selberg
   coordinates.

2. **Universal Complete-Period Blindness to the Even-Mode Sign Flip (`evenFlipRow_completePeriod_eq`,
   `sieveSeq_evenFlipRow_sub`)**:
   For every cutoff `N ≥ 1` and every row `c : ℕ → ℝ`, the even-mode sign flip
   `evenFlipRow N c = scaledSelbergRow N c evenSign` (which negates `Y_{N,c}(q)` on even `q` and
   preserves `Y_{N,c}(1)`) has the **exact same** complete-period mean `finiteHarmonicSum`,
   `selbergTotientDiagonalForm`, `sieveVariance`, `bezoutCoprimeQuadraticForm`,
   `sieveSuccessorCovariance`, `sieveSuccessorReserve`, `sievePoincareExcess`,
   `successorPhaseLoss`, `sievePrimitiveEnergy`, `sieveVarianceAboveParity`,
   `franelGcdQuadraticForm`, `TwoLagSieve.periodCovariance` at every lag `h`, and `tupleVariance`
   for every shift tuple `H` as `c`, while shifting the pointwise response by
   $$s_{N, c^\flat}(k) - s_{N, c}(k)
     = -2 \sum_{\substack{1 \le q \le N \\ 2 \mid q}} Y_{N,c}(q)\, c_q(k).$$

3. **Cofinal Separation Across the Three Canonical Parity Families
   (`chiFour_parityRows_completePeriod_and_receiver_split`,
   `realCharacter_parityRows_completePeriod_and_receiver_split`,
   `fermi_parityRows_completePeriod_and_receiver_split`)**:
   For every damping `0 < ε ≤ 1 / 2`:
   - `chiFourRow ε N` and `chiFourTwinRow ε N` have identical complete-period mean and identical
     values for all 12 complete-period quadratic forms at every horizon `N ≥ 1`, yet their
     pointwise responses `sieveSeq N _ k` and cubic moments disagree at every `N ≥ 3`, and their
     trans-horizon pronic receivers `horizonPronicEnergy` split into uniformly bounded vs.
     unbounded as `N → ∞`.
   - `charRow χ ε N` and `charTwinRow χ ε N` (for any non-principal real character `χ` mod `q`)
     have identical complete-period mean and identical values for all 12 complete-period quadratic
     forms at every horizon `N ≥ 1`, while their cubic moments, pointwise responses, and
     trans-horizon pronic receivers split for all large `N`.
   - `fermiRow ε N` and `evenFlipRow N (fermiRow ε N)` have identical complete-period mean,
     identical values for all 12 complete-period quadratic forms, **and** identical translated
     moments of **every** degree `m` at every horizon `N ≥ 1`, yet their trans-horizon pronic
     receivers split into bounded vs. unbounded as `N → ∞`.
-/

open Finset Filter Topology ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.BezoutValuationIncidence
open RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ## §1. Sign-Character Invariance of the Torus Poincaré Excess -/

/-- The harmonic-subtracted unit-step torus Poincaré excess `sievePoincareExcess N c` depends only
on the squared non-trivial Selberg coordinates `(Y_{N,c}(2)^2, ..., Y_{N,c}(N)^2)`. -/
theorem sievePoincareExcess_eq_of_sq_eq (N : ℕ) {c₁ c₂ : ℕ → ℝ}
    (hsq : ∀ q ∈ Icc 2 N,
      (selbergMultiplesCoord N c₁ q) ^ 2 = (selbergMultiplesCoord N c₂ q) ^ 2) :
    sievePoincareExcess N c₁ = sievePoincareExcess N c₂ := by
  unfold sievePoincareExcess
  refine sum_congr rfl fun e he => ?_
  rw [hsq e he]

/-- `sievePoincareExcess N c` is invariant under every sign character `ε` (`ε(q)^2 = 1` for
`q ∈ Icc 2 N`) on the Selberg coordinates. -/
theorem sievePoincareExcess_scaledSelbergRow_eq (N : ℕ) (c : ℕ → ℝ) {ε : ℕ → ℝ}
    (hε : ∀ q ∈ Icc 2 N, (ε q) ^ 2 = 1) :
    sievePoincareExcess N (scaledSelbergRow N c ε) = sievePoincareExcess N c :=
  sievePoincareExcess_eq_of_sq_eq N fun q hq =>
    sq_selbergMultiplesCoord_scaledSelbergRow c
      (mem_Icc.mpr ⟨by have := (mem_Icc.mp hq).1; omega, (mem_Icc.mp hq).2⟩) (hε q hq)

/-! ## §2. Bundled Complete-Period Agreement Predicate and General Sign-Twist Law -/

/-- Two divisor weights `c₁, c₂ : ℕ → ℝ` at cutoff `N` are **complete-period quadratically
indistinguishable** (`CompletePeriodQuadraticEq N c₁ c₂`) if they have the same complete-period
mean `finiteHarmonicSum N` and the exact same values on all 12 complete-period quadratic forms of
the sieve theory:
`selbergTotientDiagonalForm`, `sieveVariance`, `bezoutCoprimeQuadraticForm`,
`sieveSuccessorCovariance`, `sieveSuccessorReserve`, `sievePoincareExcess`,
`successorPhaseLoss`, `sievePrimitiveEnergy`, `sieveVarianceAboveParity`,
`franelGcdQuadraticForm`, `TwoLagSieve.periodCovariance` at every lag `h`, and `tupleVariance`
for every shift tuple `H`, as well as all two-point translated moments. -/
def CompletePeriodQuadraticEq (N : ℕ) (c₁ c₂ : ℕ → ℝ) : Prop :=
  finiteHarmonicSum N c₁ = finiteHarmonicSum N c₂ ∧
  selbergTotientDiagonalForm N c₁ = selbergTotientDiagonalForm N c₂ ∧
  sieveVariance N c₁ = sieveVariance N c₂ ∧
  bezoutCoprimeQuadraticForm N c₁ = bezoutCoprimeQuadraticForm N c₂ ∧
  sieveSuccessorCovariance N c₁ = sieveSuccessorCovariance N c₂ ∧
  sieveSuccessorReserve N c₁ = sieveSuccessorReserve N c₂ ∧
  sievePoincareExcess N c₁ = sievePoincareExcess N c₂ ∧
  successorPhaseLoss N c₁ = successorPhaseLoss N c₂ ∧
  sievePrimitiveEnergy N c₁ = sievePrimitiveEnergy N c₂ ∧
  sieveVarianceAboveParity N c₁ = sieveVarianceAboveParity N c₂ ∧
  franelGcdQuadraticForm N c₁ = franelGcdQuadraticForm N c₂ ∧
  (∀ h : ℕ, TwoLagSieve.periodCovariance N c₁ h = TwoLagSieve.periodCovariance N c₂ h) ∧
  (∀ H : Finset ℕ, tupleVariance N c₁ H = tupleVariance N c₂ H) ∧
  (∀ v : Fin 2 → ℕ, SieveMoments.translatedMoment N c₁ v = SieveMoments.translatedMoment N c₂ v)

/-- Whenever `c₁` and `c₂` have equal complete-period mean `finiteHarmonicSum N` and equal squared
Selberg coordinates on `Icc 2 N` (`N ≥ 1`), they satisfy `CompletePeriodQuadraticEq N c₁ c₂`. -/
theorem completePeriodQuadraticEq_of_mean_and_sq_eq {N : ℕ} (hN : 1 ≤ N) {c₁ c₂ : ℕ → ℝ}
    (hmean : finiteHarmonicSum N c₁ = finiteHarmonicSum N c₂)
    (hsq2 : ∀ q ∈ Icc 2 N,
      (selbergMultiplesCoord N c₁ q) ^ 2 = (selbergMultiplesCoord N c₂ q) ^ 2) :
    CompletePeriodQuadraticEq N c₁ c₂ := by
  have hsq1 : ∀ q ∈ Icc 1 N,
      (selbergMultiplesCoord N c₁ q) ^ 2 = (selbergMultiplesCoord N c₂ q) ^ 2 := by
    intro q hq
    by_cases hq1 : q = 1
    · subst hq1
      rw [selbergMultiplesCoord_one_eq_finiteHarmonicSum,
        selbergMultiplesCoord_one_eq_finiteHarmonicSum, hmean]
    · exact hsq2 q (mem_Icc.mpr ⟨by have := (mem_Icc.mp hq).1; omega, (mem_Icc.mp hq).2⟩)
  obtain ⟨hV, hC, hR, hL, hE, hP, hcov, htup⟩ := completePeriodCenteredForms_eq_of_sq_eq hN hsq2
  obtain ⟨hSel, hBez, hFran⟩ := completePeriodUncenteredForms_eq_of_sq_eq N hsq1
  obtain ⟨ε, _, hε, hc⟩ :=
    (periodCovariance_eq_iff_exists_scaledSelbergRow hmean).mp fun g _ => hcov g
  have hmom : ∀ v : Fin 2 → ℕ,
      SieveMoments.translatedMoment N c₁ v = SieveMoments.translatedMoment N c₂ v := by
    intro v
    have h2 : SieveMoments.translatedMoment N c₂ v =
        SieveMoments.translatedMoment N (scaledSelbergRow N c₁ ε) v := by
      unfold SieveMoments.translatedMoment
      congr 1
      refine sum_congr rfl fun n _ => prod_congr rfl fun i _ => ?_
      unfold sieveSeq
      refine sum_congr rfl fun d hd => hc d (mem_filter.mp hd).1
    rw [h2, translatedMoment_two_scaled_eq N c₁ (fun q => by simpa [sq] using hε q) v]
  exact ⟨hmean, hSel, hV, hBez, hC, hR, sievePoincareExcess_eq_of_sq_eq N hsq2,
    hL, hE, hP, hFran, hcov, htup, hmom⟩

/-- Every mean-preserving sign character `ε` (`ε 1 = 1` and `∀ q, (ε q)^2 = 1`) produces a row
`scaledSelbergRow N c ε` that is complete-period quadratically indistinguishable from `c`. -/
theorem completePeriodQuadraticEq_scaledSelbergRow {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ)
    {ε : ℕ → ℝ} (hε1 : ε 1 = 1) (hε : ∀ q : ℕ, (ε q) ^ 2 = 1) :
    CompletePeriodQuadraticEq N (scaledSelbergRow N c ε) c := by
  have hmean : finiteHarmonicSum N (scaledSelbergRow N c ε) = finiteHarmonicSum N c := by
    rw [← selbergMultiplesCoord_one_eq_finiteHarmonicSum,
      ← selbergMultiplesCoord_one_eq_finiteHarmonicSum,
      selbergMultiplesCoord_scaledSelbergRow c ε (mem_Icc.mpr ⟨le_rfl, hN⟩), hε1, one_mul]
  refine completePeriodQuadraticEq_of_mean_and_sq_eq hN hmean fun q hq => ?_
  exact sq_selbergMultiplesCoord_scaledSelbergRow c
    (mem_Icc.mpr ⟨by have := (mem_Icc.mp hq).1; omega, (mem_Icc.mp hq).2⟩) (hε q)

/-! ## §3. Universal Complete-Period Blindness to `evenFlipRow` and Trans-Horizon Shift -/

theorem evenSign_one : evenSign 1 = 1 := by
  simp [evenSign]

theorem evenSign_sq (q : ℕ) : (evenSign q) ^ 2 = 1 := by
  rw [sq, evenSign_mul_self]

/-- **Universal complete-period blindness to the even-mode sign flip (`evenFlipRow_completePeriod_eq`):**
For every cutoff `N ≥ 1` and every row `c : ℕ → ℝ`, `evenFlipRow N c` and `c` have identical
complete-period mean and identical values on all 12 complete-period quadratic forms and all
two-point translated moments. -/
theorem evenFlipRow_completePeriod_eq {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) :
    CompletePeriodQuadraticEq N (evenFlipRow N c) c :=
  completePeriodQuadraticEq_scaledSelbergRow hN c evenSign_one evenSign_sq

/-- **Pointwise response shift under `evenFlipRow`:**
Flipping the sign of all even Selberg coordinates shifts the sieve response `sieveSeq N c k` by
`-2 ∑_{q ∈ [1, N], 2 ∣ q} Y_{N,c}(q) c_q(k)`. -/
theorem sieveSeq_evenFlipRow_sub (N : ℕ) (c : ℕ → ℝ) (k : ℕ) :
    sieveSeq N (evenFlipRow N c) k - sieveSeq N c k =
      -2 * ∑ q ∈ (Icc 1 N).filter (fun q => 2 ∣ q),
        selbergMultiplesCoord N c q * ramanujanLagCoefficient q k := by
  rw [evenFlipRow, sieveSeq_scaledSelbergRow_sub, mul_sum, sum_filter]
  refine sum_congr rfl fun q _ => ?_
  unfold evenSign
  split_ifs <;> ring

/-! ## §4. Cofinal Parity Row Pairs: Complete-Period Agreement vs. Trans-Horizon Separation -/

theorem chiFourSign_one : chiFourSign 1 = 1 := by
  simp [chiFourSign, chiFour_eq]

theorem chiFourSign_sq (q : ℕ) : (chiFourSign q) ^ 2 = 1 := by
  rw [sq, chiFourSign_mul_self]

/-- At every cutoff `N ≥ 1` and every damping `ε : ℝ`, `chiFourTwinRow ε N` and `chiFourRow ε N`
are complete-period quadratically indistinguishable (`CompletePeriodQuadraticEq N`). -/
theorem chiFourTwinRow_completePeriod_eq (ε : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    CompletePeriodQuadraticEq N (chiFourTwinRow ε N) (chiFourRow ε N) :=
  completePeriodQuadraticEq_scaledSelbergRow hN (chiFourRow ε N) chiFourSign_one chiFourSign_sq

/-- At every horizon `N ≥ 3` and damping `ε > 0`, the pointwise responses `sieveSeq N` of
`chiFourTwinRow ε N` and `chiFourRow ε N` disagree at some integer point `k`. -/
theorem exists_sieveSeq_chiFourTwinRow_ne {ε : ℝ} (hε : 0 < ε) {N : ℕ} (hN : 3 ≤ N) :
    ∃ k : ℕ, sieveSeq N (chiFourTwinRow ε N) k ≠ sieveSeq N (chiFourRow ε N) k := by
  by_contra hall
  push Not at hall
  have hact := (sieveSeq_scaledSelbergRow_eq_iff N (chiFourRow ε N) chiFourSign).mp hall
  have h3 : (3 : ℕ) ∈ Icc 1 N := mem_Icc.mpr ⟨by omega, hN⟩
  have hY3 : selbergMultiplesCoord N (chiFourRow ε N) 3 ≠ 0 := by
    rw [selbergMultiplesCoord_chiFourRow ε (by norm_num)]
    have hpos := chiFourPartialMass_pos hε (X := N / 3) (by omega)
    have hc : dampedSignWeight chiFour ε 3 / (3 : ℕ) ≠ 0 := by
      have : (3 : ℝ) ^ (-ε) ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
      simp [dampedSignWeight, chiFour_eq, this]
    exact mul_ne_zero hc hpos.ne'
  have hs3 := hact 3 h3 hY3
  have hneg : chiFourSign 3 = -1 := by simp [chiFourSign, chiFour_eq]
  linarith

/-- **Complete-Period Agreement and Trans-Horizon Receiver Split for the `χ₄` Parity Rows
(`chiFour_parityRows_completePeriod_and_receiver_split`):**
For every `0 < ε ≤ 1 / 2`:
1. At every horizon `N ≥ 1`, `chiFourTwinRow ε N` and `chiFourRow ε N` agree on the complete-period
   mean `finiteHarmonicSum N`, all 12 complete-period quadratic forms, and all two-point translated
   moments (`CompletePeriodQuadraticEq N`).
2. At every horizon `N ≥ 3`, their pointwise responses `sieveSeq N _ k` disagree at some `k` and
   their cubic translated moments disagree.
3. The pronic discrepancy energy `horizonPronicEnergy N (chiFourRow ε N) T` is uniformly bounded
   in `(N, T)`, whereas `horizonPronicEnergy N (chiFourTwinRow ε N) T` is unbounded as `N → ∞`. -/
theorem chiFour_parityRows_completePeriod_and_receiver_split {ε : ℝ} (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) :
    (∀ N : ℕ, 1 ≤ N → CompletePeriodQuadraticEq N (chiFourTwinRow ε N) (chiFourRow ε N)) ∧
    (∀ N : ℕ, 3 ≤ N → ∃ k : ℕ,
      sieveSeq N (chiFourTwinRow ε N) k ≠ sieveSeq N (chiFourRow ε N) k) ∧
    (∀ N : ℕ, 3 ≤ N → ∃ v : Fin 3 → ℕ,
      SieveMoments.translatedMoment N (chiFourTwinRow ε N) v ≠
        SieveMoments.translatedMoment N (chiFourRow ε N) v) ∧
    (∃ C : ℝ, ∀ N T : ℕ, horizonPronicEnergy N (chiFourRow ε N) T ≤ C) ∧
    (∀ C : ℝ, ∀ᶠ N in atTop, ∃ T : ℕ, C < horizonPronicEnergy N (chiFourTwinRow ε N) T) :=
  ⟨fun _ hN => chiFourTwinRow_completePeriod_eq ε hN,
    fun _ hN => exists_sieveSeq_chiFourTwinRow_ne hε hN,
    fun _ hN => exists_translatedMoment_three_chiFourTwinRow_ne hε hN,
    ⟨_, horizonPronicEnergy_chiFourRow_le hε⟩,
    eventually_lt_horizonPronicEnergy_chiFourTwinRow hε hε2⟩

variable {q : ℕ} [NeZero q]

theorem completedValue_one (χ : MulChar (ZMod q) ℤ) : completedValue χ 1 = 1 := by
  simp [completedValue, charSign_one]

theorem completedValue_sq (χ : MulChar (ZMod q) ℤ) (e : ℕ) : (completedValue χ e) ^ 2 = 1 := by
  rw [sq, completedValue_mul_self]

/-- At every cutoff `N ≥ 1`, every real character `χ` mod `q`, and every damping `ε : ℝ`,
`charTwinRow χ ε N` and `charRow χ ε N` are complete-period quadratically indistinguishable
(`CompletePeriodQuadraticEq N`). -/
theorem charTwinRow_completePeriod_eq (χ : MulChar (ZMod q) ℤ) (ε : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    CompletePeriodQuadraticEq N (charTwinRow χ ε N) (charRow χ ε N) :=
  completePeriodQuadraticEq_scaledSelbergRow hN (charRow χ ε N)
    (completedValue_one χ) (completedValue_sq χ)

/-- **Complete-Period Agreement and Trans-Horizon Receiver Split for Every Real Character
(`realCharacter_parityRows_completePeriod_and_receiver_split`):**
For every non-principal real character `χ` mod `q` and every `0 < ε ≤ 1 / 2`:
1. At every horizon `N ≥ 1`, `charTwinRow χ ε N` and `charRow χ ε N` satisfy
   `CompletePeriodQuadraticEq N` (identical complete-period mean, all 12 complete-period quadratic
   forms, and all two-point translated moments).
2. At all large horizons `N`, their cubic translated moments and pointwise responses disagree.
3. The pronic discrepancy energy of `charRow χ ε N` is uniformly bounded in `(N, T)`, whereas that
   of `charTwinRow χ ε N` tends to infinity with `N`. -/
theorem realCharacter_parityRows_completePeriod_and_receiver_split
    {χ : MulChar (ZMod q) ℤ} (hχ : χ ≠ 1) {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    (∀ N : ℕ, 1 ≤ N → CompletePeriodQuadraticEq N (charTwinRow χ ε N) (charRow χ ε N)) ∧
    (∀ᶠ N in atTop, ∃ v : Fin 3 → ℕ,
      SieveMoments.translatedMoment N (charTwinRow χ ε N) v ≠
        SieveMoments.translatedMoment N (charRow χ ε N) v) ∧
    (∃ C : ℝ, ∀ N T : ℕ, horizonPronicEnergy N (charRow χ ε N) T ≤ C) ∧
    (∀ C : ℝ, ∀ᶠ N in atTop, ∃ T : ℕ, C < horizonPronicEnergy N (charTwinRow χ ε N) T) :=
  ⟨fun _ hN => charTwinRow_completePeriod_eq χ ε hN,
    eventually_exists_translatedMoment_three_charTwinRow_ne hχ hε,
    ⟨_, horizonPronicEnergy_charRow_le hχ hε⟩,
    eventually_lt_horizonPronicEnergy_charTwinRow hχ hε hε2⟩

/-- **Complete-Period and All-Degree Moment Agreement vs. Trans-Horizon Receiver Split for the
Fermi Parity Rows (`fermi_parityRows_completePeriod_and_receiver_split`):**
For every `0 < ε ≤ 1 / 2`:
1. At every horizon `N ≥ 1`, `evenFlipRow N (fermiRow ε N)` and `fermiRow ε N` satisfy
   `CompletePeriodQuadraticEq N` (identical complete-period mean and all 12 complete-period
   quadratic forms).
2. At every horizon `N`, every degree `m`, and every shift tuple `v : Fin m → ℕ`, their
   complete-period translated moments `SieveMoments.translatedMoment` coincide.
3. Yet the trans-horizon pronic receiver separates them: `horizonPronicEnergy N (fermiRow ε N) T`
   stays below a uniform bound `E` for all large `N`, whereas
   `horizonPronicEnergy N (evenFlipRow N (fermiRow ε N)) T` exceeds any given `C` for all large `N`. -/
theorem fermi_parityRows_completePeriod_and_receiver_split {ε : ℝ} (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) :
    (∀ N : ℕ, 1 ≤ N → CompletePeriodQuadraticEq N (evenFlipRow N (fermiRow ε N)) (fermiRow ε N)) ∧
    (∀ N m (v : Fin m → ℕ),
      SieveMoments.translatedMoment N (evenFlipRow N (fermiRow ε N)) v =
        SieveMoments.translatedMoment N (fermiRow ε N) v) ∧
    (∃ E : ℝ, ∀ T : ℕ, ∀ᶠ N in atTop, horizonPronicEnergy N (fermiRow ε N) T ≤ E) ∧
    (∀ C : ℝ, ∀ᶠ N in atTop, ∃ T : ℕ,
      C < horizonPronicEnergy N (evenFlipRow N (fermiRow ε N)) T) :=
  ⟨fun _ hN => evenFlipRow_completePeriod_eq hN (fermiRow ε N),
    (fermi_parityRows hε hε2).1,
    (fermi_parityRows hε hε2).2.1,
    (fermi_parityRows hε hε2).2.2⟩

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
