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

1. **General SSIC Fatality–Neutrality Calculus for Involutive Collapses (§1).**
   For an involution `κ` and a paid datum `d` (`P d`), strict fatality (`P d ∧ ¬ P (κ d)`),
   pair-fatality (`¬ (P d ∧ P (κ d))`), and failure of neutrality (`¬ (P (κ d) ↔ P d)`) are
   equivalent (`strictlyFatalAt_iff_pairFatalAt_of_paid`, `strictlyFatalAt_iff_not_neutralAt_of_paid`).
   Whenever `r` is blind to `κ`, any strictly fatal datum destroys resolution of `P` and forces the
   resolution limit of any non-negative energy invariant to reach at least `max (I d) (I (κ d))`.

2. **Family I: The Even-Multiplier Flip (`evenFlip`) on Four-Free Convolutions (§2).**
   For a paid four-free convolution weight `c = k ⋆ o_ε` (`0 < ε ≤ 1/2`, `k` on `[1, J]` vanishing
   on multiples of `4`, `poleValue k J ε = 0`), the even flip `c^♭ = k^♭ ⋆ o_ε` is strictly fatal
   for `ReceiverBounded` **if and only if** the even part of the kernel fails to vanish at the pole:
   `poleValue (evenPartWeight k) J ε ≠ 0` (`strictlyFatalAt_evenFlip_iff_evenPart_poleValue_ne_zero`).
   It is neutral on the paid pair `{c, c^♭}` **if and only if** both the odd and even parts of `k`
   vanish independently at `1 - ε` (`neutralAt_evenFlip_paid_iff_odd_and_even_pole`).
   In the two-point family `k = α δ_1 + β δ_2`, the even flip is strictly fatal for every non-zero
   paid kernel (`strictlyFatalAt_evenFlip_twoPoint_iff`). In the infinite-support `OrientAdmissible ε k`
   class, neutrality on the pair holds iff `polePairing ε k = 0 ∧ polePairing ε (evenPartWeight k) = 0`.
   Adjoining the first pronic moment (`firstPronicMoment`) kills the even-flip collapse whenever
   the prime-`2` Ramanujan coefficient is non-zero (`not_mem_shadow_joinReading_firstPronicMoment_iff`),
   and adjoining the logarithmic pronic moments separates every paid Fermi-flipped weight.

3. **Family II: Selberg Sign-Character Orbits and Cubic-Moment Reduction (§3).**
   Under the complete-period lag reading `completePeriodLagReading N`, the shadow of `c` is the
   entire `2^{N-1}` sign-character orbit `scaledSelbergRow N c σ`, within which `chiFourSign`,
   every real character `completedValue χ`, and `evenSign` are cofinally fatal for bounded pronic
   horizon energy. Refining by the complete-period cubic moments (`translatedMoment N · v` for
   `v : Fin 3 → ℕ`) collapses the entire `2^{N-1}` sign orbit to a singleton on odd-supported rows
   (`shadow_cubicMomentReading_odd_singleton`) and to at most the two-element even-flip pair
   `{c, evenFlipRow N c}` on squarefree-supported rows (`shadow_cubicMomentReading_squarefree_pair`),
   reducing all surviving sign-character fatality to the prime-`2` even flip of Family I.

4. **Family III: Residue-Class Prime Flips and the `(1/4, 3/4)` Complementation Law (§4).**
   At half damping `ε = 1/2`, the residue-class flip `residueFlip q S` is paid iff
   `q.totient < 4 * (S.filter IsUnit).card`, and its complement `Sᶜ` is paid iff
   `4 * (S.filter IsUnit).card < 3 * q.totient` (`receiverBounded_residueFlip_compl_half_iff`).
   Every complement pair `{S, Sᶜ}` has at least one paid member (`receiverBounded_residueFlip_or_compl_half`),
   complementation is neutral (both paid) iff the flipped unit density lies strictly in `(1/4, 3/4)`
   (`both_residueFlip_and_compl_paid_iff`), and complementation is strictly fatal at `S` iff
   `3 * q.totient ≤ 4 * (S.filter IsUnit).card` (`strictlyFatalAt_compl_residueFlip_half_iff`).
   For a subgroup flip `subgroupFlipSet H` (`H ≤ (ZMod q)ˣ`), complementation is neutral at index
   `2` and `3` and strictly fatal iff the index is at least `4`
   (`strictlyFatalAt_compl_subgroupFlipSet_iff`).
-/

open Set Filter Topology BigOperators
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

/-- **Resolution of a paid datum under an invisible collapse forces neutrality.** -/
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

/-- **Exact fatality criterion for the even flip on a paid four-free convolution.**
Let `k` be a kernel supported on `[1, J]` and vanishing on multiples of `4`, let `0 < ε ≤ 1/2`,
and assume `c = k ⋆ o_ε` is paid (`poleValue k J ε = 0`). Then the even flip `c^♭ = k^♭ ⋆ o_ε` is
strictly fatal for `ReceiverBounded` if and only if the even part of the kernel has a non-zero
pole value at `1 - ε`: `poleValue (evenPartWeight k) J ε ≠ 0`. -/
theorem strictlyFatalAt_evenFlip_iff_evenPart_poleValue_ne_zero
    {k : ℕ → ℝ} {J : ℕ} (hJ : 1 ≤ J) (hk : SupportedOn k J)
    (h4 : ∀ j, 4 ∣ j → k j = 0) {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hpole : poleValue k J ε = 0) :
    (ReceiverBounded (convWeight k (oddSquarefreeDamped ε)) ∧
      ¬ ReceiverBounded (convWeight (flipKernelOf k) (oddSquarefreeDamped ε))) ↔
      poleValue (evenPartWeight k) J ε ≠ 0 := by
  have hpaid : ReceiverBounded (convWeight k (oddSquarefreeDamped ε)) :=
    (receiverBounded_fourFree_iff hJ hk h4 hε hε2).mpr hpole
  have hshift := poleValue_flipKernelOf_eq_sub_two_evenPart k J ε
  have hk' : SupportedOn (flipKernelOf k) J := supportedOn_flipKernelOf hk
  have h4' : ∀ j, 4 ∣ j → flipKernelOf k j = 0 := flipKernelOf_eq_zero_of_four_dvd h4
  have hflip_iff := receiverBounded_fourFree_iff hJ hk' h4' hε hε2
  rw [hshift, hpole, zero_sub, neg_eq_zero, mul_eq_zero, OfNat.ofNat_ne_zero, false_or] at hflip_iff
  simp [hpaid, hflip_iff]

/-- **Exact neutrality criterion for the even flip on a four-free convolution pair.**
Both members `{k ⋆ o_ε, k^♭ ⋆ o_ε}` of the even-flip pair are paid (so the even flip is paid and
neutral) if and only if both `oddPartKernel k` and `evenPartWeight k` vanish independently at the
pole `1 - ε`. -/
theorem evenFlip_pair_paid_and_neutral_iff_odd_and_even_pole
    {k : ℕ → ℝ} {J : ℕ} (hJ : 1 ≤ J) (hk : SupportedOn k J)
    (h4 : ∀ j, 4 ∣ j → k j = 0) {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    (ReceiverBounded (convWeight k (oddSquarefreeDamped ε)) ∧
      NeutralAt ReceiverBounded
        (fun w => if w = convWeight k (oddSquarefreeDamped ε)
          then convWeight (flipKernelOf k) (oddSquarefreeDamped ε) else w)
        (convWeight k (oddSquarefreeDamped ε))) ↔
      (poleValue (oddPartKernel k) J ε = 0 ∧ poleValue (evenPartWeight k) J ε = 0) := by
  rw [neutralAt_and_paid_iff_both_paid]
  simp only [ ↓reduceIte]
  exact both_evenFlip_pair_receiverBounded_iff_odd_and_even_pole hJ hk h4 hε hε2

/-- **Complete fatality law in the two-point family `k = α δ_1 + β δ_2`.**
Every non-zero paid two-point kernel over the odd squarefree weight has `β ≠ 0`, and its even flip
is strictly fatal (`¬ ReceiverBounded (twoPointKernel α (-β) ⋆ o_ε)`). Neutrality holds in the
paid two-point family only at the trivial kernel `α = β = 0`. -/
theorem strictlyFatalAt_evenFlip_twoPoint_iff
    {α β ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hpaid : α + β * (2 : ℝ) ^ (ε - 1) = 0) :
    (ReceiverBounded (convWeight (twoPointKernel α β) (oddSquarefreeDamped ε)) ∧
      ¬ ReceiverBounded (convWeight (twoPointKernel α (-β)) (oddSquarefreeDamped ε))) ↔
      β ≠ 0 := by
  have h1 := twoPoint_evenFlip_classification hε hε2
  constructor
  · rintro ⟨_, hnot⟩ hβ0
    subst hβ0
    simp only [zero_mul, add_zero] at hpaid
    subst hpaid
    simp only [neg_zero] at hnot
    exact hnot (h1.mpr (by ring)).1
  · intro hβ
    exact (h1.mpr ⟨hpaid, hβ⟩)

/-- **Infinite-support orientation-admissible classification.**
For an `OrientAdmissible ε k` kernel (`0 < ε ≤ 1/2`), the even flip `evenFlip (k ⋆ o_ε)` is paid
and neutral on `{k ⋆ o_ε, evenFlip (k ⋆ o_ε)}` iff both `polePairing ε k = 0` and
`polePairing ε (evenPartWeight k) = 0`, and is strictly fatal at a paid `k ⋆ o_ε` iff
`polePairing ε (evenPartWeight k) ≠ 0`. -/
theorem strictlyFatalAt_evenFlip_orientAdmissible_iff
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) {k : ℕ → ℝ} (hk : OrientAdmissible ε k)
    (hpole : polePairing ε k = 0) :
    StrictlyFatalAt ReceiverBounded evenFlip (convWeight k (oddSquarefreeDamped ε)) ↔
      polePairing ε (evenPartWeight k) ≠ 0 := by
  have hpaid : ReceiverBounded (convWeight k (oddSquarefreeDamped ε)) :=
    (receiverBounded_conv_oddSquarefree_iff hε hε2 hk).mpr hpole
  have hboth := receiverBounded_and_evenFlip_iff hε hε2 hk
  simp only [StrictlyFatalAt, hpaid, true_and, hpole, ne_eq] at hboth ⊢
  exact not_iff_not.mpr ⟨fun h => (hboth.mp ⟨hpaid, h⟩).2, fun h => (hboth.mpr ⟨hpole, h⟩).2⟩

/-- **Exact faithful completion of the even-flip shadow by the first pronic moment.**
For any complete-period reading `r` invisible to `evenFlip` (such as `completePeriodLagReading N`),
adjoining `firstPronicMoment` expels `evenFlip c` from the shadow of `c` if and only if the
prime-`2` Ramanujan coefficient `weightRamanujanCoeff c 2 = c 2 - c 1` is non-zero. -/
theorem not_mem_shadow_joinReading_firstPronicMoment_iff
    {r : (ℕ → ℝ) → O} (hinv : Invisible r evenFlip) (c : ℕ → ℝ) :
    evenFlip c ∉ shadow (joinReading r firstPronicMoment) c ↔
      weightRamanujanCoeff c 2 ≠ 0 := by
  rw [shadow_joinReading, Set.mem_inter_iff, mem_shadow_iff, hinv c, true_and, mem_shadow_iff,
    ne_eq, firstPronicMoment_evenFlip_eq_iff, weightRamanujanCoeff_two, sub_eq_zero, eq_comm]

/-- **Logarithmic-moment completion kills the Fermi even-flip fatality.**
At every damping `0 < ε ≤ 1/2`, the Fermi weight `fermiDamped ε` and its even flip share the entire
complete-period lag reading (`completePeriodLagReading N`), `evenFlip` is strictly fatal at
`fermiDamped ε`, and there exists a logarithmic pronic moment `logPowWeight m` (`m = 1` or `m = 2`)
that separates them. -/
theorem fermi_evenFlip_fatality_resolved_by_logMoments
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    StrictlyFatalAt ReceiverBounded evenFlip (fermiDamped ε) ∧
      (∀ N : ℕ, Invisible (completePeriodLagReading N) evenFlip) ∧
      ∃ m ∈ ({1, 2} : Finset ℕ),
        firstPronicMoment (logPowWeight m (evenFlip (fermiDamped ε))) ≠
          firstPronicMoment (logPowWeight m (fermiDamped ε)) := by
  refine ⟨⟨fermiDamped_receiverBounded hε, evenFlip_fermiDamped_not_receiverBounded hε hε2⟩,
    fun N => invisible_completePeriodLagReading_evenFlip N, ?_⟩
  obtain ⟨m, hm, hne⟩ := exists_logMoment_ne_of_fermi_evenFlip ε
  exact ⟨m, hm, hne.symm⟩

/-! ### 3. Family II: Selberg Sign-Character Orbits and Cubic-Moment Reduction -/

/-- The complete-period **cubic-moment reading** at horizon `N`: the family of all translated
cubic moments `SieveMoments.translatedMoment N c (v 0) (v 1) (v 2)` together with the scale value
`c 1`. -/
def cubicMomentReading (N : ℕ) (c : ℕ → ℝ) : ((Fin 3 → ℕ) → ℝ) × ℝ :=
  (fun v => SieveMoments.translatedMoment N c (v 0) (v 1) (v 2), c 1)

/-- **Cofinal fatality of sign-character collapses inside the quadratic lag shadow.**
At every damping `0 < ε ≤ 1/2`, the quadratic complete-period lag reading `completePeriodLagReading N`
is blind to `scaledSelbergRow N · (chiFourSign ·)`, `scaledSelbergRow N · (completedValue χ ·)`,
and `scaledSelbergRow N · (evenSign ·)`, while each of these collapses sends the paid Fermi row to a
sequence of rows with unbounded pronic horizon energy (`horizonPronicEnergy`). -/
theorem signCharacter_collapses_cofinally_fatal_in_lag_shadow
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    (∃ B : ℝ, ∀ N : ℕ, horizonPronicEnergy N (fermiDamped ε) ≤ B) ∧
      (∀ N : ℕ, scaledSelbergRow N (fermiDamped ε) (fun d => (chiFourSign d : ℝ)) ∈
        shadow (completePeriodLagReading N) (fermiDamped ε)) ∧
      (∀ M : ℝ, ∃ N : ℕ,
        M < horizonPronicEnergy N (scaledSelbergRow N (fermiDamped ε) (fun d => (chiFourSign d : ℝ)))) ∧
      (∀ N : ℕ, scaledSelbergRow N (fermiDamped ε) (fun d => (evenSign d : ℝ)) ∈
        shadow (completePeriodLagReading N) (fermiDamped ε)) ∧
      (∀ M : ℝ, ∃ N : ℕ,
        M < horizonPronicEnergy N (scaledSelbergRow N (fermiDamped ε) (fun d => (evenSign d : ℝ)))) := by
  obtain ⟨hchi_eq, hfermi_bdd, hchi_unbdd⟩ := chiFour_parityRows_completePeriod_and_receiver_split hε hε2
  obtain ⟨heven_eq, _, heven_unbdd⟩ := fermi_parityRows_completePeriod_and_receiver_split hε hε2
  refine ⟨hfermi_bdd,
    fun N => funext fun h => (hchi_eq N h).symm,
    hchi_unbdd,
    fun N => funext fun h => (heven_eq N h).symm,
    heven_unbdd⟩

/-- **Cubic moments eliminate all sign-character collapses on odd-supported rows.**
Within the `2^{N-1}` sign-character orbit `scaledSelbergRow N c σ` of an odd-supported row `c`
with `c 1 ≠ 0` and non-vanishing prime values on `[1, N]`, the cubic-moment reading pins `c`
uniquely on `[1, N]`: no non-trivial sign flip survives. -/
theorem cubicMomentReading_pins_odd_signOrbit
    {N : ℕ} {c : ℕ → ℝ} (hc1 : c 1 ≠ 0)
    (hodd : ∀ d, 1 ≤ d → d ≤ N → Even d → c d = 0)
    (hprime : ∀ p, Nat.Prime p → Odd p → p ≤ N → c p ≠ 0)
    {σ : ℕ → ℝ} (hσ1 : σ 1 = 1) (hσm : ∀ m n, σ (m * n) = σ m * σ n)
    (hσs : ∀ d, 1 ≤ d → d ≤ N → σ d ^ 2 = 1)
    (hread : cubicMomentReading N (scaledSelbergRow N c σ) = cubicMomentReading N c) :
    ∀ d, d ≤ N → scaledSelbergRow N c σ d = c d := by
  have hcub : ∀ v : Fin 3 → ℕ,
      SieveMoments.translatedMoment N (scaledSelbergRow N c σ) (v 0) (v 1) (v 2) =
        SieveMoments.translatedMoment N c (v 0) (v 1) (v 2) :=
    fun v => (congr_arg Prod.fst hread).symm ▸ rfl
  exact fun d hd => scaledSelbergRow_eq_of_translatedMoment_three hc1 hodd hprime hσ1 hσm hσs
    (fun v => (congr_fun (congr_arg Prod.fst hread) v).symm) d hd

/-- **Cubic moments reduce the squarefree sign-character orbit to the two-element even-flip pair.**
Within the `2^{N-1}` sign-character orbit `scaledSelbergRow N c σ` of a squarefree-supported row `c`
with `c 1 ≠ 0` and non-vanishing prime values on `[1, N]`, the cubic-moment reading pins the row on
`[1, N]` up to at most the prime-`2` even flip `evenFlipRow N c`. -/
theorem cubicMomentReading_reduces_squarefree_signOrbit_to_evenFlip
    {N : ℕ} {c : ℕ → ℝ} (hc1 : c 1 ≠ 0)
    (hsq : ∀ d, 1 ≤ d → d ≤ N → ¬ Squarefree d → c d = 0)
    (hprime : ∀ p, Nat.Prime p → Odd p → p ≤ N → c p ≠ 0)
    {σ : ℕ → ℝ} (hσ1 : σ 1 = 1) (hσm : ∀ m n, σ (m * n) = σ m * σ n)
    (hσs : ∀ d, 1 ≤ d → d ≤ N → σ d ^ 2 = 1)
    (hread : cubicMomentReading N (scaledSelbergRow N c σ) = cubicMomentReading N c) :
    (∀ d, d ≤ N → scaledSelbergRow N c σ d = c d) ∨
      (∀ d, d ≤ N → scaledSelbergRow N c σ d = evenFlipRow N c d) :=
  scaledSelbergRow_eq_or_evenFlip_of_translatedMoment_three hc1 hsq hprime hσ1 hσm hσs
    (fun v => (congr_fun (congr_arg Prod.fst hread) v).symm)

/-! ### 4. Family III: Residue-Class Prime Flips and the `(1/4, 3/4)` Complementation Law -/

/-- The half-damped weight `f_{q,S}(d) d^{-1/2}` associated to a residue-class prime flip `S ⊆ ZMod q`. -/
def residueFlipHalfWeight (q : ℕ) (S : Finset (ZMod q)) (d : ℕ) : ℝ :=
  residueFlip q S d * (d : ℝ) ^ (-(1 / 2 : ℝ))

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
  rw [residueFlipHalfWeight, receiverBounded_residueFlip_half_iff_general, card_compl_filter_isUnit]
  have hle := card_filter_isUnit_le_totient S
  omega

/-- **Every residue-class flip pair `{S, Sᶜ}` has at least one paid member at half damping.**
Because `(0, 1/4]` and `[3/4, 1]` are disjoint, `S` and `Sᶜ` can never both fail the quarter law. -/
theorem receiverBounded_residueFlip_or_compl_half {q : ℕ} [NeZero q] (S : Finset (ZMod q)) :
    ReceiverBounded (residueFlipHalfWeight q S) ∨
      ReceiverBounded (residueFlipHalfWeight q Sᶜ) := by
  rw [residueFlipHalfWeight, receiverBounded_residueFlip_half_iff_general,
    receiverBounded_residueFlip_compl_half_iff]
  have hφ : 0 < q.totient := Nat.totient_pos.mpr (NeZero.pos q)
  omega

/-- **The `(1/4, 3/4)` neutrality window for residue-class complementation.**
Both `S` and `Sᶜ` are paid at half damping (so the complement involution `S ↦ Sᶜ` is paid and
neutral at `S`) if and only if the flipped unit count lies strictly between `φ(q)/4` and `3φ(q)/4`. -/
theorem both_residueFlip_and_compl_paid_iff {q : ℕ} [NeZero q] (S : Finset (ZMod q)) :
    (ReceiverBounded (residueFlipHalfWeight q S) ∧
      ReceiverBounded (residueFlipHalfWeight q Sᶜ)) ↔
      (q.totient < 4 * (S.filter IsUnit).card ∧ 4 * (S.filter IsUnit).card < 3 * q.totient) := by
  rw [residueFlipHalfWeight, receiverBounded_residueFlip_half_iff_general,
    receiverBounded_residueFlip_compl_half_iff]

/-- **Exact fatality classification of residue-class complementation.**
The complement involution `S ↦ Sᶜ` is strictly fatal at `S` for `ReceiverBounded ∘ residueFlipHalfWeight q`
if and only if `S` flips at least three quarters of the unit residue classes
(`3 * φ(q) ≤ 4 * #(S ∩ (ZMod q)ˣ)`). -/
theorem strictlyFatalAt_compl_residueFlip_half_iff {q : ℕ} [NeZero q] (S : Finset (ZMod q)) :
    StrictlyFatalAt (fun T => ReceiverBounded (residueFlipHalfWeight q T)) compl S ↔
      3 * q.totient ≤ 4 * (S.filter IsUnit).card := by
  simp only [StrictlyFatalAt, compl_eq_univ_sdiff]
  change (ReceiverBounded (residueFlipHalfWeight q S) ∧
    ¬ ReceiverBounded (residueFlipHalfWeight q Sᶜ)) ↔ _
  rw [residueFlipHalfWeight, receiverBounded_residueFlip_half_iff_general,
    receiverBounded_residueFlip_compl_half_iff]
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
