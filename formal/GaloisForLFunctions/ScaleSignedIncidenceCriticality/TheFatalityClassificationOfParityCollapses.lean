import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheResolutionLimitOfAReading
import GaloisForLFunctions.ArithmeticOrientationTheory.OrientedReadings
import GaloisForLFunctions.ArithmeticOrientationTheory.CompletePeriodQuadraticFormsAreOrientationBlind
import GaloisForLFunctions.ArithmeticOrientationTheory.TheEvenFlipIsReadAtThePrimeTwo
import GaloisForLFunctions.ArithmeticOrientationTheory.AnOrientationFaithfulNormOverTheOddSquarefreeWeight
import GaloisForLFunctions.TransHorizonIncidenceMechanics.CompletePeriodQuadraticFormsAgreeOnParityRowPairs
import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheEvenFlipShiftsThePoleValueByTheEvenPartOfTheKernel
import GaloisForLFunctions.TransHorizonIncidenceMechanics.EvenFlipPairsOverTheOddSquarefreeWeightAreClassifiedAtThePole
import GaloisForLFunctions.TransHorizonIncidenceMechanics.CubicMomentsPinTheParityOfOddRows
import GaloisForLFunctions.TransHorizonIncidenceMechanics.CubicMomentsPinSquarefreeRowsUpToTheEvenFlip
import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheQuarterLawOfResidueFlips
import GaloisForLFunctions.TransHorizonIncidenceMechanics.SubgroupFlipsArePaidAtHalfDamping
import GaloisForLFunctions.SmoothBernoulliPoleCalibration.EvenPoleCalibrationAndLogMomentPinning

/-!
# The Fatality Classification of Parity Collapses

A collapse `κ : D → D` is *invisible* to a reading `r` when `r (κ d) = r d` for all `d`. By the
collapse–resolution dichotomy (`not_resolves_of_separating_collapse`), an invisible collapse
forbids `r` from resolving a property `P` as soon as `κ` is **strictly fatal** at some paid datum
`d` (`P d ∧ ¬ P (κ d)`), and is harmless at `d` when `κ` is **neutral** (`P (κ d) ↔ P d`).

This module gives the complete fatality and neutrality classification across the three families of
parity collapses in the corpus, together with the exact faithful completions that kill the fatal
collapses:

1. **General SSIC Fatality–Neutrality Calculus for Collapses (§1).**
   At any paid datum `d` (`P d`), strict fatality (`P d ∧ ¬ P (κ d)`), pair-fatality
   (`¬ (P d ∧ P (κ d))`), and failure of neutrality (`¬ (P (κ d) ↔ P d)`) are equivalent
   (`strictlyFatalAt_iff_pairFatalAt_of_paid`, `strictlyFatalAt_iff_not_neutralAt_of_paid`).
   Whenever `r` is blind to `κ`, any strictly fatal datum destroys resolution of `P` and forces the
   resolution limit of any real invariant `I` to reach at least `max (I d) (I (κ d))`.

2. **Family I: The Even-Multiplier Flip (`evenFlip`) on Four-Free Convolutions (§2).**
   For a four-free convolution weight `c = k ⋆ o_ε` (`0 < ε ≤ 1/2`, `k` supported on `[1, J]` and
   vanishing on multiples of `4`), `evenFlip c = k^♭ ⋆ o_ε` is strictly fatal for `ReceiverBounded`
   at `c` **if and only if** `poleValue k J ε = 0 ∧ poleValue (evenPartWeight k) J ε ≠ 0`
   (`strictlyFatalAt_evenFlip_iff_pole_and_evenPart`). It is paid and neutral (`P c ∧ P (evenFlip c)`)
   **if and only if** both `oddPartKernel k` and `evenPartWeight k` vanish independently at `1 - ε`
   (`evenFlip_paid_and_neutral_iff_odd_and_even_pole`).
   In the two-point family `k = α δ_1 + β δ_2`, the even flip is strictly fatal iff
   `α + β 2^{ε - 1} = 0 ∧ β ≠ 0`, and neutral only at the zero kernel (`α = β = 0`).
   In the infinite-support `OrientAdmissible ε k` class, strict fatality holds iff
   `polePairing ε k = 0 ∧ polePairing ε (evenPartWeight k) ≠ 0`.
   Adjoining the first pronic moment (`firstPronicMoment`) expels `evenFlip c` from the shadow of any
   blind reading iff `weightRamanujanCoeff c 2 ≠ 0` (`not_mem_shadow_joinReading_firstPronicMoment_iff`),
   and adjoining the logarithmic pronic moments `logPowWeight c m` separates every generalized Fermi
   even-flip pair (`exists_logMoment_ne_of_strictlyFatalAt_evenFlip`).

3. **Family II: Selberg Sign-Character Orbits and Cubic-Moment Reduction (§3).**
   Under the complete-period lag reading `completePeriodLagReading N`, the shadow of `c` is the
   entire `2^{N-1}` sign-character orbit `scaledSelbergRow N c σ`, within which `chiFourSign`,
   every real character `completedValue χ`, and `evenSign` are cofinally fatal for bounded pronic
   horizon energy. Refining by the complete-period cubic moments (`cubicMomentReading N`) expels
   `chiFourTwinRow ε N` from the shadow at every `N ≥ 3` while leaving `evenFlipRow N (fermiRow ε N)`
   inside the shadow at every `N`; in general, cubic moments collapse the entire `2^{N-1}` sign
   orbit to a singleton on odd-supported rows (`cubicMomentReading_pins_odd_signOrbit`) and to at
   most the two-element even-flip pair `{c, evenFlipRow N c}` on squarefree-supported rows
   (`cubicMomentReading_reduces_squarefree_signOrbit_to_evenFlip`), reducing all surviving
   sign-character fatality to the prime-`2` even flip of Family I.

4. **Family III: Residue-Class Prime Flips and the `(1/4, 3/4)` Complementation Law (§4).**
   At half damping `ε = 1/2`, the residue-class flip `residueFlip q S` is paid iff
   `q.totient < 4 * (S.filter IsUnit).card`, and its complement `Sᶜ` is paid iff
   `4 * (S.filter IsUnit).card < 3 * q.totient` (`receiverBounded_residueFlip_compl_half_iff`).
   Every complement pair `{S, Sᶜ}` has at least one paid member (`receiverBounded_residueFlip_or_compl_half`),
   complementation is paid and neutral (both paid) iff the flipped unit density lies strictly in
   `(1/4, 3/4)` (`both_residueFlip_and_compl_paid_iff`), and complementation is strictly fatal at `S`
   iff `3 * q.totient ≤ 4 * (S.filter IsUnit).card` (`strictlyFatalAt_compl_residueFlip_half_iff`).
   For a subgroup flip `subgroupFlipSet H` (`H ≤ (ZMod q)ˣ`), complementation is neutral at index
   `2` and `3` and strictly fatal iff the index is at least `4`
   (`strictlyFatalAt_compl_subgroupFlipSet_iff`).
-/

open Finset Set Filter Topology BigOperators
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.ArithmeticOrientationTheory
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open GaloisForLFunctions.SmoothBernoulliPoleCalibration

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

noncomputable section
set_option autoImplicit false

variable {D O O' : Type*}

/-! ### 1. General SSIC Fatality and Neutrality Calculus for Collapses -/

/-- A collapse `κ : D → D` is **strictly fatal** for a property `P` at `d` when `d` satisfies `P`
and its collapsed partner `κ d` fails `P`. -/
def StrictlyFatalAt (P : D → Prop) (κ : D → D) (d : D) : Prop :=
  P d ∧ ¬ P (κ d)

/-- A collapse `κ : D → D` is **pair-fatal** for `P` at `d` when `d` and `κ d` cannot both
satisfy `P`. -/
def PairFatalAt (P : D → Prop) (κ : D → D) (d : D) : Prop :=
  ¬ (P d ∧ P (κ d))

/-- A collapse `κ : D → D` is **neutral** for `P` at `d` when `κ` preserves the truth value of `P`
at `d`. -/
def NeutralAt (P : D → Prop) (κ : D → D) (d : D) : Prop :=
  P (κ d) ↔ P d

theorem strictlyFatalAt_iff_pairFatalAt_of_paid {P : D → Prop} {κ : D → D} {d : D} (hd : P d) :
    StrictlyFatalAt P κ d ↔ PairFatalAt P κ d := by
  simp [StrictlyFatalAt, PairFatalAt, hd]

theorem strictlyFatalAt_iff_not_neutralAt_of_paid {P : D → Prop} {κ : D → D} {d : D} (hd : P d) :
    StrictlyFatalAt P κ d ↔ ¬ NeutralAt P κ d := by
  simp [StrictlyFatalAt, NeutralAt, hd]

theorem neutralAt_and_paid_iff_both_paid {P : D → Prop} {κ : D → D} {d : D} :
    (P d ∧ NeutralAt P κ d) ↔ (P d ∧ P (κ d)) := by
  simp only [NeutralAt]
  exact ⟨fun ⟨hd, h⟩ => ⟨hd, h.mpr hd⟩, fun ⟨hd, hκ⟩ => ⟨hd, ⟨fun _ => hd, fun _ => hκ⟩⟩⟩

/-- **Trichotomy of a collapse at any datum.** Either `d` is unpaid, `κ` is strictly fatal at `d`,
or both `d` and `κ d` are paid (so `κ` is neutral at `d`). -/
theorem collapse_trichotomy (P : D → Prop) (κ : D → D) (d : D) :
    ¬ P d ∨ StrictlyFatalAt P κ d ∨ (P d ∧ P (κ d)) := by
  by_cases hd : P d
  · by_cases hκ : P (κ d)
    · exact Or.inr (Or.inr ⟨hd, hκ⟩)
    · exact Or.inr (Or.inl ⟨hd, hκ⟩)
  · exact Or.inl hd

/-- **Strict fatality destroys resolution of any blind reading.** -/
theorem not_resolves_of_invisible_of_strictlyFatalAt {r : D → O} {P : D → Prop} {κ : D → D}
    (hinv : Invisible r κ) {d : D} (hfat : StrictlyFatalAt P κ d) :
    ¬ Resolves r P :=
  not_resolves_of_separating_collapse hinv hfat.1 hfat.2

/-- **Resolution under an invisible collapse forces neutrality everywhere.** -/
theorem neutralAt_of_resolves_of_invisible {r : D → O} {P : D → Prop} {κ : D → D}
    (hres : Resolves r P) (hinv : Invisible r κ) (d : D) :
    NeutralAt P κ d :=
  hres d (κ d) (collapse_mem_shadow hinv d)

/-- **Two-point collapse lower bound on the resolution limit.** An invisible collapse floors the
resolution limit of any real invariant `I` by `max (I d) (I (κ d))`. -/
theorem max_le_resolutionLimit_of_invisible {I : D → ℝ} {r : D → O} {κ : D → D}
    (hinv : Invisible r κ) {d : D} (hbdd : BddAbove (I '' shadow r d)) :
    max (I d) (I (κ d)) ≤ resolutionLimit I r d :=
  max_le (le_resolutionLimit hbdd)
    (by simpa [Function.iterate_one] using iterate_le_resolutionLimit (I := I) hinv hbdd 1)

/-! ### 2. Family I: The Even-Multiplier Flip on Four-Free Convolutions -/

/-- **Exact fatality criterion for the even flip on a four-free convolution.**
Let `k` be a kernel supported on `[1, J]` and vanishing on multiples of `4`, and let `0 < ε ≤ 1/2`.
Then `evenFlip` is strictly fatal for `ReceiverBounded` at `c = k ⋆ o_ε` if and only if `k` vanishes
at the pole `1 - ε` (`poleValue k J ε = 0`) while its even part does not
(`poleValue (evenPartWeight k) J ε ≠ 0`). -/
theorem strictlyFatalAt_evenFlip_iff_pole_and_evenPart
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) {k : ℕ → ℝ}
    (hk4 : ∀ m, 4 ∣ m → k m = 0) {J : ℕ} (hkJ : ∀ j, J < j → k j = 0) :
    StrictlyFatalAt ReceiverBounded evenFlip (RHTower.dirichletConv k (oddSqfWeight ε)) ↔
      (poleValue k J ε = 0 ∧ poleValue (evenPartWeight k) J ε ≠ 0) := by
  simp only [StrictlyFatalAt, evenFlip_dirichletConv_oddSqf hk4]
  obtain ⟨_, _, _, hiff, _, hpres, hnot⟩ := evenFlip_exactLoss hε hε2 hk4 hkJ
  constructor
  · rintro ⟨hc, hnotflip⟩
    refine ⟨hiff.mp hc, fun he0 => hnotflip ((hpres he0).mp hc)⟩
  · rintro ⟨hk0, he_ne⟩
    have hc : ReceiverBounded (RHTower.dirichletConv k (oddSqfWeight ε)) := hiff.mpr hk0
    exact ⟨hc, fun hflip => hnot he_ne ⟨hc, hflip⟩⟩

/-- **Exact neutrality criterion for a paid four-free convolution pair.**
Both `c = k ⋆ o_ε` and `evenFlip c` are paid (so `evenFlip` is paid and neutral at `c`) if and only
if both `oddPartKernel k` and `evenPartWeight k` vanish independently at the pole `1 - ε`. -/
theorem evenFlip_paid_and_neutral_iff_odd_and_even_pole
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) {k : ℕ → ℝ}
    (hk4 : ∀ m, 4 ∣ m → k m = 0) {J : ℕ} (hkJ : ∀ j, J < j → k j = 0) :
    (ReceiverBounded (RHTower.dirichletConv k (oddSqfWeight ε)) ∧
      NeutralAt ReceiverBounded evenFlip (RHTower.dirichletConv k (oddSqfWeight ε))) ↔
      (poleValue (oddPartKernel k) J ε = 0 ∧ poleValue (evenPartWeight k) J ε = 0) := by
  rw [neutralAt_and_paid_iff_both_paid, evenFlip_dirichletConv_oddSqf hk4]
  exact both_evenFlip_pair_receiverBounded_iff_odd_and_even_pole hε hε2 hk4 hkJ

/-- **Complete fatality law in the two-point family `k = α δ_1 + β δ_2`.**
In the two-point family over the odd squarefree weight (`0 < ε ≤ 1/2`), `evenFlip` is strictly
fatal at `(α δ_1 + β δ_2) ⋆ o_ε` if and only if `α + β 2^{ε - 1} = 0` and `β ≠ 0`, and is paid and
neutral only at the zero kernel `α = 0 ∧ β = 0`. -/
theorem strictlyFatalAt_evenFlip_twoPoint_iff
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (α β : ℝ) :
    StrictlyFatalAt ReceiverBounded evenFlip
      (RHTower.dirichletConv (twoPointKernel α β) (oddSqfWeight ε)) ↔
      (α + β * (2 : ℝ) ^ (ε - 1) = 0 ∧ β ≠ 0) := by
  obtain ⟨hflip, _, hiff, hiff', hboth0⟩ := twoPoint_evenFlip_classification hε hε2 α β
  have hev : evenFlip (RHTower.dirichletConv (twoPointKernel α β) (oddSqfWeight ε)) =
      RHTower.dirichletConv (twoPointKernel (α + β) (-β)) (oddSqfWeight ε) := hflip.symm
  simp only [StrictlyFatalAt, hev]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨hiff.mp h1, fun hβ => h2 ?_⟩
    have hα : α = 0 := by have := hiff.mp h1; rw [hβ] at this; linarith
    exact hiff'.mpr (by rw [hα, hβ]; ring)
  · rintro ⟨hpole, hβ⟩
    have h1 : ReceiverBounded (RHTower.dirichletConv (twoPointKernel α β) (oddSqfWeight ε)) :=
      hiff.mpr hpole
    exact ⟨h1, fun h2 => hβ (hboth0 h1 h2).2⟩

/-- **Infinite-support orientation-admissible classification.**
For an `OrientAdmissible ε k` kernel vanishing on multiples of `4` (`0 < ε ≤ 1/2`), `evenFlip` is
strictly fatal at `k ⋆ o_ε` if and only if `polePairing ε k = 0` and
`polePairing ε (evenPartWeight k) ≠ 0`, and is paid and neutral if and only if both pole pairings
vanish. -/
theorem strictlyFatalAt_evenFlip_orientAdmissible_iff
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) {k : ℕ → ℝ}
    (hk4 : ∀ m, 4 ∣ m → k m = 0) (hk : OrientAdmissible ε k) :
    StrictlyFatalAt ReceiverBounded evenFlip (RHTower.dirichletConv k (oddSqfWeight ε)) ↔
      (polePairing ε k = 0 ∧ polePairing ε (evenPartWeight k) ≠ 0) := by
  have hpaid_iff := receiverBounded_dirichletConv_oddSqf_iff_admissible hε hε2 hk
  have hboth_iff := receiverBounded_and_evenFlip_iff hε hε2 hk4 hk
  simp only [StrictlyFatalAt]
  constructor
  · rintro ⟨hc, hnot⟩
    have hp0 : polePairing ε k = 0 := hpaid_iff.mp hc
    exact ⟨hp0, fun he0 => hnot (hboth_iff.mpr ⟨hp0, he0⟩).2⟩
  · rintro ⟨hp0, he_ne⟩
    have hc : ReceiverBounded (RHTower.dirichletConv k (oddSqfWeight ε)) := hpaid_iff.mpr hp0
    exact ⟨hc, fun hflip => he_ne (hboth_iff.mp ⟨hc, hflip⟩).2⟩

/-- **Exact faithful completion of the even-flip shadow by the first pronic moment.**
For any four-free damped weight `c` (`DampedClass K ε c`, `0 < ε`) and any reading `r` invisible to
`evenFlip` (such as `amplitudeReading`), adjoining `firstPronicMoment` expels `evenFlip c` from the
shadow of `c` if and only if the prime-`2` Ramanujan coefficient `weightRamanujanCoeff c 2` is
non-zero. -/
theorem not_mem_shadow_joinReading_firstPronicMoment_iff
    {K ε : ℝ} (hε : 0 < ε) {c : ℕ → ℝ} (hc : DampedClass K ε c)
    (h4 : ∀ m, 4 ∣ m → c m = 0) {r : (ℕ → ℝ) → O} (hinv : Invisible r evenFlip) :
    evenFlip c ∉ shadow (joinReading r firstPronicMoment) c ↔
      weightRamanujanCoeff c 2 ≠ 0 := by
  simp only [shadow_joinReading, Set.mem_inter_iff, mem_shadow_iff, hinv c, true_and]
  exact firstPronicMoment_separates_evenFlip_iff hε hc h4

/-- **Logarithmic-moment completion kills every strictly fatal even-flip pair.**
Whenever `evenFlip` is strictly fatal at `c = k ⋆ o_ε` (`0 < ε ≤ 1/2`, `k` on `[1, J]` vanishing
on multiples of `4`), `c` and `evenFlip c` share all Ramanujan amplitude moduli, yet there exists a
logarithmic moment order `m : ℕ` such that `firstPronicMoment (logPowWeight · m)` strictly
separates them. -/
theorem exists_logMoment_ne_of_strictlyFatalAt_evenFlip
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) {k : ℕ → ℝ}
    (hk4 : ∀ m, 4 ∣ m → k m = 0) {J : ℕ} (hkJ : ∀ j, J < j → k j = 0)
    (hfat : StrictlyFatalAt ReceiverBounded evenFlip (RHTower.dirichletConv k (oddSqfWeight ε))) :
    (∀ e, |weightRamanujanCoeff (evenFlip (RHTower.dirichletConv k (oddSqfWeight ε))) e| =
      |weightRamanujanCoeff (RHTower.dirichletConv k (oddSqfWeight ε)) e|) ∧
      ∃ m : ℕ,
        firstPronicMoment (logPowWeight (RHTower.dirichletConv k (oddSqfWeight ε)) m) ≠
          firstPronicMoment (logPowWeight (evenFlip (RHTower.dirichletConv k (oddSqfWeight ε))) m) := by
  obtain ⟨hk0, he_ne⟩ := (strictlyFatalAt_evenFlip_iff_pole_and_evenPart hε hε2 hk4 hkJ).mp hfat
  obtain ⟨hram, _, _, hlog⟩ := exists_logMoment_ne_of_fermi_evenFlip hε hε2 hk4 hkJ hk0 he_ne
  rw [evenFlip_dirichletConv_oddSqf hk4]
  exact ⟨hram, hlog⟩

/-! ### 3. Family II: Selberg Sign-Character Orbits and Cubic-Moment Reduction -/

/-- The complete-period **cubic-moment reading** at horizon `N`: the family of all translated
cubic moments `SieveMoments.translatedMoment N c v` (`v : Fin 3 → ℕ`). -/
def cubicMomentReading (N : ℕ) (c : ℕ → ℝ) : (Fin 3 → ℕ) → ℝ :=
  fun v => SieveMoments.translatedMoment N c v

/-- **Cofinal fatality of sign-character collapses vs. cubic-moment separation.**
At every damping `0 < ε ≤ 1/2`:
1. Both `chiFourTwinRow ε N` and `evenFlipRow N (fermiRow ε N)` lie in the complete-period
   quadratic lag shadow `shadow (completePeriodLagReading N)` of their paid base rows at every
   `N ≥ 1`, while their pronic horizon energies grow unboundedly as `N → ∞`.
2. Refining by `cubicMomentReading N` expels `chiFourTwinRow ε N` from the shadow of
   `chiFourRow ε N` at every `N ≥ 3`, whereas `evenFlipRow N (fermiRow ε N)` remains inside the
   shadow of `fermiRow ε N` under `cubicMomentReading N` at every horizon `N`. -/
theorem signCharacter_fatality_and_cubic_moment_split
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    (∀ N : ℕ, 1 ≤ N →
      chiFourTwinRow ε N ∈ shadow (completePeriodLagReading N) (chiFourRow ε N)) ∧
    (∀ N : ℕ, 3 ≤ N →
      chiFourTwinRow ε N ∉ shadow (cubicMomentReading N) (chiFourRow ε N)) ∧
    (∃ C : ℝ, ∀ N T : ℕ, horizonPronicEnergy N (chiFourRow ε N) T ≤ C) ∧
    (∀ C : ℝ, ∀ᶠ N in atTop, ∃ T : ℕ, C < horizonPronicEnergy N (chiFourTwinRow ε N) T) ∧
    (∀ N : ℕ, 1 ≤ N →
      evenFlipRow N (fermiRow ε N) ∈ shadow (completePeriodLagReading N) (fermiRow ε N)) ∧
    (∀ N : ℕ,
      evenFlipRow N (fermiRow ε N) ∈ shadow (cubicMomentReading N) (fermiRow ε N)) ∧
    (∃ E : ℝ, ∀ T : ℕ, ∀ᶠ N in atTop, horizonPronicEnergy N (fermiRow ε N) T ≤ E) ∧
    (∀ C : ℝ, ∀ᶠ N in atTop, ∃ T : ℕ,
      C < horizonPronicEnergy N (evenFlipRow N (fermiRow ε N)) T) := by
  obtain ⟨_, _, hchi_cub, hchi_bdd, hchi_unbdd⟩ :=
    chiFour_parityRows_completePeriod_and_receiver_split hε hε2
  obtain ⟨_, hfermi_mom, hfermi_bdd, hfermi_unbdd⟩ :=
    fermi_parityRows_completePeriod_and_receiver_split hε hε2
  refine ⟨fun N hN => ?_, fun N hN hmem => ?_, hchi_bdd, hchi_unbdd,
    fun N hN => invisible_completePeriodLagReading_evenFlipRow hN (fermiRow ε N),
    fun N => funext fun v => hfermi_mom N 3 v,
    hfermi_bdd, hfermi_unbdd⟩
  ·exact invisible_completePeriodLagReading_scaledSelbergRow hN chiFourSign_one chiFourSign_sq
      (chiFourRow ε N)
  · obtain ⟨v, hv⟩ := hchi_cub N hN
    exact hv (congr_fun hmem v)

/-- **Cubic moments eliminate all sign-character collapses on odd-supported rows.**
If `c` is supported on the odd Selberg moduli at horizon `N` (`Y_N(q) = 0` on even `q`,
`Y_N(q) ≠ 0` on odd `q`) and `scaledSelbergRow N c σ` lies in the cubic-moment shadow of `c`,
then `scaledSelbergRow N c σ` coincides with `c` on `[1, N]`: no non-trivial sign twist survives. -/
theorem cubicMomentReading_pins_odd_signOrbit
    {N : ℕ} (c : ℕ → ℝ) (σ : ℕ → ℝ) (hσ : ∀ q, σ q * σ q = 1)
    (heven : ∀ q ∈ Finset.Icc 1 N, Even q → selbergMultiplesCoord N c q = 0)
    (hodd : ∀ q ∈ Finset.Icc 1 N, Odd q → selbergMultiplesCoord N c q ≠ 0)
    (hmem : scaledSelbergRow N c σ ∈ shadow (cubicMomentReading N) c) :
    ∀ d ∈ Finset.Icc 1 N, scaledSelbergRow N c σ d = c d :=
  scaledSelbergRow_eq_of_translatedMoment_three c σ hσ heven hodd (congr_fun hmem)

/-- **Cubic moments reduce the squarefree sign-character orbit to the two-element even-flip pair.**
If the Selberg coordinates of `c` vanish off the squarefree moduli and are non-zero at every
squarefree modulus `≤ N` (as holds for every PM cofactor row `pmCofactorDivisorWeight ε Q`), then
any sign twist `scaledSelbergRow N c σ` in the cubic-moment shadow of `c` coincides on `[1, N]`
with either `c` or its prime-`2` even flip `evenFlipRow N c`. -/
theorem cubicMomentReading_reduces_squarefree_signOrbit_to_evenFlip
    {N : ℕ} (c : ℕ → ℝ) (σ : ℕ → ℝ) (hσ : ∀ q, σ q * σ q = 1)
    (hns : ∀ q ∈ Finset.Icc 1 N, ¬ Squarefree q → selbergMultiplesCoord N c q = 0)
    (hsq : ∀ q ∈ Finset.Icc 1 N, Squarefree q → selbergMultiplesCoord N c q ≠ 0)
    (hmem : scaledSelbergRow N c σ ∈ shadow (cubicMomentReading N) c) :
    (∀ d ∈ Finset.Icc 1 N, scaledSelbergRow N c σ d = c d) ∨
      (∀ d ∈ Finset.Icc 1 N, scaledSelbergRow N c σ d = evenFlipRow N c d) :=
  scaledSelbergRow_eq_or_evenFlip_of_translatedMoment_three c σ hσ hns hsq (congr_fun hmem)

/-! ### 4. Family III: Residue-Class Prime Flips and the `(1/4, 3/4)` Complementation Law -/

/-- The half-damped weight `f_{q,S}(d) d^{-1/2}` associated to a residue-class prime flip `S ⊆ ZMod q`. -/
def residueFlipHalfWeight (q : ℕ) (S : Finset (ZMod q)) : ℕ → ℝ :=
  fun d => residueFlip q S d * (d : ℝ) ^ (-(1 / 2 : ℝ))

/-- The number of units in `ZMod q` is `φ(q) = q.totient`. -/
theorem card_univ_filter_isUnit (q : ℕ) [NeZero q] :
    ((Finset.univ : Finset (ZMod q)).filter IsUnit).card = q.totient := by
  have heq : ((Finset.univ : Finset (ZMod q)).filter IsUnit) =
      (Finset.univ : Finset (ZMod q)ˣ).map ⟨Units.val, Units.val_injective⟩ := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.coeFn_mk, IsUnit]
  rw [heq, Finset.card_map, Finset.card_univ, ZMod.card_units_eq_totient]

/-- For every `S ⊆ ZMod q`, the unit counts of `S` and its complement `Sᶜ` sum to `q.totient`. -/
theorem card_filter_isUnit_add_compl {q : ℕ} [NeZero q] (S : Finset (ZMod q)) :
    (S.filter IsUnit).card + (Sᶜ.filter IsUnit).card = q.totient := by
  have hdisj : Disjoint (S.filter IsUnit) (Sᶜ.filter IsUnit) :=
    Finset.disjoint_filter_filter disjoint_compl_right
  have hunion : S.filter IsUnit ∪ Sᶜ.filter IsUnit =
      (Finset.univ : Finset (ZMod q)).filter IsUnit := by
    ext a
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_compl, Finset.mem_univ, true_and]
    by_cases h : a ∈ S <;> simp [h]
  rw [← Finset.card_union_of_disjoint hdisj, hunion, card_univ_filter_isUnit]

theorem card_filter_isUnit_le_totient {q : ℕ} [NeZero q] (S : Finset (ZMod q)) :
    (S.filter IsUnit).card ≤ q.totient := by
  have h := card_filter_isUnit_add_compl S
  omega

theorem card_compl_filter_isUnit {q : ℕ} [NeZero q] (S : Finset (ZMod q)) :
    (Sᶜ.filter IsUnit).card = q.totient - (S.filter IsUnit).card := by
  have h := card_filter_isUnit_add_compl S
  omega

/-- **The three-quarters law for the complement of a residue-class flip.**
At half damping `ε = 1/2`, the complementary flip `Sᶜ` is paid if and only if `S` flips strictly
less than three quarters of the unit residue classes (`4 * #(S ∩ (ZMod q)ˣ) < 3 * φ(q)`). -/
theorem receiverBounded_residueFlip_compl_half_iff {q : ℕ} [NeZero q] (S : Finset (ZMod q)) :
    ReceiverBounded (residueFlipHalfWeight q Sᶜ) ↔
      4 * (S.filter IsUnit).card < 3 * q.totient := by
  unfold residueFlipHalfWeight
  rw [receiverBounded_residueFlip_half_iff_general, card_compl_filter_isUnit]
  have hle := card_filter_isUnit_le_totient S
  omega

/-- **Every residue-class flip pair `{S, Sᶜ}` has at least one paid member at half damping.**
Because `(0, 1/4]` and `[3/4, 1]` are disjoint, `S` and `Sᶜ` can never both fail the quarter law. -/
theorem receiverBounded_residueFlip_or_compl_half {q : ℕ} [NeZero q] (S : Finset (ZMod q)) :
    ReceiverBounded (residueFlipHalfWeight q S) ∨
      ReceiverBounded (residueFlipHalfWeight q Sᶜ) := by
  rw [receiverBounded_residueFlip_compl_half_iff]
  unfold residueFlipHalfWeight
  rw [receiverBounded_residueFlip_half_iff_general]
  have hφ : 0 < q.totient := Nat.totient_pos.mpr (NeZero.pos q)
  omega

/-- **The `(1/4, 3/4)` neutrality window for residue-class complementation.**
Both `S` and `Sᶜ` are paid at half damping (so the complement involution `S ↦ Sᶜ` is paid and
neutral at `S`) if and only if the flipped unit count lies strictly between `φ(q)/4` and `3φ(q)/4`. -/
theorem both_residueFlip_and_compl_paid_iff {q : ℕ} [NeZero q] (S : Finset (ZMod q)) :
    (ReceiverBounded (residueFlipHalfWeight q S) ∧
      ReceiverBounded (residueFlipHalfWeight q Sᶜ)) ↔
      (q.totient < 4 * (S.filter IsUnit).card ∧ 4 * (S.filter IsUnit).card < 3 * q.totient) := by
  rw [receiverBounded_residueFlip_compl_half_iff]
  unfold residueFlipHalfWeight
  rw [receiverBounded_residueFlip_half_iff_general]

/-- **Exact fatality classification of residue-class complementation.**
The complement involution `S ↦ Sᶜ` is strictly fatal at `S` for `ReceiverBounded ∘ residueFlipHalfWeight q`
if and only if `S` flips at least three quarters of the unit residue classes
(`3 * φ(q) ≤ 4 * #(S ∩ (ZMod q)ˣ)`). -/
theorem strictlyFatalAt_compl_residueFlip_half_iff {q : ℕ} [NeZero q] (S : Finset (ZMod q)) :
    StrictlyFatalAt (fun T => ReceiverBounded (residueFlipHalfWeight q T)) compl S ↔
      3 * q.totient ≤ 4 * (S.filter IsUnit).card := by
  simp only [StrictlyFatalAt]
  rw [receiverBounded_residueFlip_compl_half_iff]
  unfold residueFlipHalfWeight
  rw [receiverBounded_residueFlip_half_iff_general]
  have hφ : 0 < q.totient := Nat.totient_pos.mpr (NeZero.pos q)
  omega

open Classical in
/-- **Subgroup-flip complementation law: index `2` and `3` are neutral; index `≥ 4` is fatal.**
For a subgroup `H ≤ (ZMod q)ˣ`, the subgroup flip `subgroupFlipSet H` flips the `φ(q) - |H|` units
outside `H`, and its complement `(subgroupFlipSet H)ᶜ` flips the `|H|` units inside `H`.
Consequently:
* `(subgroupFlipSet H)ᶜ` is paid at half damping iff `φ(q) < 4 |H|` (index at most `3`);
* when `subgroupFlipSet H` is paid (`4 |H| < 3 φ(q)`), complementation is **strictly fatal** at
  `subgroupFlipSet H` if and only if `4 |H| ≤ φ(q)` (index at least `4`), and **neutral** (both
  paid) if and only if `φ(q) < 4 |H| < 3 φ(q)` (index `2` or `3`). -/
theorem strictlyFatalAt_compl_subgroupFlipSet_iff {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ) :
    StrictlyFatalAt (fun T => ReceiverBounded (residueFlipHalfWeight q T)) compl
      (subgroupFlipSet H) ↔
      4 * Nat.card H ≤ q.totient := by
  rw [strictlyFatalAt_compl_residueFlip_half_iff, card_filter_isUnit_subgroupFlipSet]
  have hH : Nat.card H ≤ q.totient := by
    have h1 := Subgroup.card_dvd_of_le (le_top : H ≤ ⊤)
    have h2 : Nat.card (⊤ : Subgroup (ZMod q)ˣ) = q.totient := by
      rw [Subgroup.card_top, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    rw [h2] at h1
    exact Nat.le_of_dvd (Nat.totient_pos.mpr (NeZero.pos q)) h1
  omega

open Classical in
/-- **Subgroup-flip neutrality window: both `subgroupFlipSet H` and its complement are paid iff
`φ(q) < 4 |H| < 3 φ(q)` (index `2` or `3`).** -/
theorem both_subgroupFlipSet_and_compl_paid_iff {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ) :
    (ReceiverBounded (residueFlipHalfWeight q (subgroupFlipSet H)) ∧
      ReceiverBounded (residueFlipHalfWeight q (subgroupFlipSet H)ᶜ)) ↔
      (q.totient < 4 * Nat.card H ∧ 4 * Nat.card H < 3 * q.totient) := by
  rw [both_residueFlip_and_compl_paid_iff, card_filter_isUnit_subgroupFlipSet]
  have hH : Nat.card H ≤ q.totient := by
    have h1 := Subgroup.card_dvd_of_le (le_top : H ≤ ⊤)
    have h2 : Nat.card (⊤ : Subgroup (ZMod q)ˣ) = q.totient := by
      rw [Subgroup.card_top, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    rw [h2] at h1
    exact Nat.le_of_dvd (Nat.totient_pos.mpr (NeZero.pos q)) h1
  omega

end

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
