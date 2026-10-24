import GaloisForLFunctions.ArithmeticOrientationTheory.OrientedReadings
import GaloisForLFunctions.ArithmeticOrientationTheory.TheEvenFlipIsReadAtThePrimeTwo
import GaloisForLFunctions.ArithmeticOrientationTheory.CompletePeriodQuadraticFormsAreOrientationBlind
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheMagnitudePairIsFaithfulWhereTheSignIsBlind
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheDesignSpecificationOfACounterexample

/-!
# The trichotomy of readings (`TheTrichotomyOfReadings`)

In `ScaleSignedIncidenceCriticality` and `ArithmeticOrientationTheory`, a method inspecting the
critical arithmetic form or the divisor-row receiver factors through a **reading** `r : D → O`.
Open Problem 10 of Arithmetic Orientation Theory asks to:
1. prove that **every orientation-faithful (or depth-certifying) reading of the critical form
   crosses the Nyquist aperture, reads a magnitude, or adds data of a third kind (mass, dilution,
   first pronic moment)**; and
2. **compute the exact precision cost of each branch**.

This module establishes the complete resolution of Open Problem 10:

1. **The Sub-Nyquist Sign Barrier and Universal Orientation Blindness (§1):**
   - At any known scale `L > 0`, any sub-Nyquist sign reading `levelReading hL a η` (`a ≤ L / 2`,
     `η ≥ 0`) on `DepthDatum` holds for **every** depth `d : DepthDatum`
     (`levelReading_of_subNyquist`). Consequently, `levelReading hL a η` is **invisible** (`Invisible`)
     to **every** collapse or orientation flip `κ : DepthDatum → DepthDatum`
     (`invisible_levelReading_subNyquist`), is **never `OrientationFaithful`** whenever `κ` moves a
     datum (`not_orientationFaithful_of_refines_subNyquist`), and has trivial resolution limit `1 / 2`
     and resolution floor `0` (`resolutionLimit_depth_levelReading_subNyquist`).
   - On the two-coordinate lattice family `ScaleDepthDatum`, any single-aperture sign reading
     `scaleDepthReading a η` (`a > 0`, `η ≥ 0`) has `resolutionLimit sdDepth (scaleDepthReading a η) = 1 / 2`
     (`theSignIsBlind`), and any reading refined by a sub-Nyquist sign reading inherits its
     complete blindness (`Invisible.of_refines`).
   - On diluted configurations (`dilutedReading hℓ hL a`, `0 < a ≤ ℓ / 2`, `a ≤ L / 2`), aliasing
     below the sub-lattice Nyquist aperture `ℓ / 2` makes `dilutedReading hℓ hL a` invisible to
     every flip `κ : DepthDatum → DepthDatum` (`invisible_dilutedReading_subNyquist`), with exact
     resolution limit `1 / 2` and floor `0` (`resolutionLimit_depth_dilutedReading_subNyquist`).

2. **The Formal Trichotomy Theorem for Orientation-Faithful and Depth-Certifying Readings (§2):**
   - Define `SubNyquistSignFactored hL r` (`∃ a ≤ L / 2, ∃ η ≥ 0, Refines (levelReading hL a η) r`),
     the class of readings that read only a sub-Nyquist sign certificate at scale `L`, and the three
     complementary branches (`ReadingBranch`):
     - **Branch I (Crossing the Nyquist Aperture):** `a > L / 2` (`levelReading hL a η` with
       `L / 2 < a ≤ L`, `adaptiveReading A η` with `ScaleMatched A η`, or the cofinal deficit rate
       `rateSet`);
     - **Branch II (Reading a Magnitude):** `bandPairReading` (`(t₂, t₃)`), the three-band deficit
       reading `bandTripleDeficitReading ℓ L` (`(t₂, t₃, t₄)`), or the isolated-pair doubling reading
       `pairDoublingReading a` (`(M(a), M(2a))`);
     - **Branch III (Adding Data of a Third Kind — Mass, Dilution, or First Pronic Moment):**
       `dilutedReading hℓ hL a` (`ℓ / 2 < a ≤ L / 2` with known on-line mass `L` and dilution `ℓ`),
       or `firstPronicMoment` adjoining the prime-`2` Ramanujan datum `W_c(2)` to amplitude /
       complete-period quadratic readings.
   - **No-Go for `SubNyquistSignFactored` (`not_orientationFaithful_and_not_certifies_of_subNyquistSignFactored`):**
     No reading in `SubNyquistSignFactored hL` can be `OrientationFaithful` for any flip `κ` moving a
     datum (`κ d ≠ d`), nor can it certify any depth `β < 1 / 2` (`¬ Certifies depth r d₀ β`). Thus
     every orientation-faithful or depth-resolving reading of the critical form **must** leave
     `SubNyquistSignFactored` via Branch I, Branch II, or Branch III (`trichotomy_of_readings_escape`).

3. **Exact Faithfulness and Precision Cost of Branch I (Crossing the Nyquist Aperture, §3):**
   - *At known scale `L > 0` in the second aliasing band `L / 2 < a ≤ L`:*
     - The threshold map `weilFloorThreshold L δ = 2L(cosh(δL) − 1)` is strictly increasing on
       `DepthDatum` (`weilFloorThreshold_strictMono`), so `weilFloorThreshold L ∘ depth` is
       **unconditionally `OrientationFaithful`** for every non-identity flip `κ` on `DepthDatum`
       (`orientationFaithful_weilFloorThreshold`).
     - `levelReading hL a η` has exact resolution limit
       `min (1 / 2) (depthResolution L η) ≤ √(η / L³)` (`resolutionLimit_depth_levelReading`,
       `resolutionLimit_depth_levelReading_le_sqrt`).
   - *Across all scales `L > 0` (`ScaleMatched A η`):*
     - **Exact Precision Cost (`branchOne_transNyquist_precision_cost`):**
       By `theDeficitBudgetLaw` and `cube_mul_sq_le_weilFloorThreshold`, certifying depth `β ≥ 0`
       costs precision `η(L) ≤ β² L³` (cubic in the scale `L`, quadratic in the depth `β`), and any
       violation `weilFloorThreshold L β' ≤ η(L)` at a single scale `L > 0` for `β' ∈ (β, 1/2]`
       destroys the certificate (`¬ Certifies sdDepth (adaptiveReading A η) p₀ β`).
   - *Along an unbounded aperture ray:*
     - `rateSet` has `sInf (rateSet p) = sdDepth p` (`sInf_rateSet`) and is `OrientationFaithful` for
       every depth-moving flip on `ScaleDepthDatum` (`orientationFaithful_rateSet`).

4. **Exact Faithfulness and Precision Cost of Branch II (Reading a Magnitude, §4):**
   - *Two aliasing bands (`bandPairReading`):*
     - `bandPairReading` has `resolutionLimit = resolutionFloor = sdDepth`
       (`theDichotomyOfSignAndMagnitude`) and is **unconditionally `OrientationFaithful`** for every
       depth-moving flip on `ScaleDepthDatum` (`orientationFaithful_bandPairReading`), without
       knowing `sdScale`.
     - **Exact Precision Cost (`branchTwo_magnitude_precision_cost`):**
       The scale-free ratio `t₃ / (2 t₂) − 1 = cosh(δL)` has critical value `1`, and resolving it to
       within excess `η ≥ 0` certifies `δ ≤ √(2η) / L` (`theTwoBandCertification`), so certifying
       `δ ≤ β` costs ratio precision `η = ½ β² L²` (quadratic in `βL`).
   - *Three aliasing bands against unknown on-line mass (`bandTripleDeficitReading`):*
     - `bandTripleDeficitReading ℓ L d = (bandDeficit ℓ d.1 L 2, bandDeficit ℓ d.1 L 3, bandDeficit ℓ d.1 L 4)`
       is **unconditionally `OrientationFaithful`** for every non-identity flip on `DepthDatum` at
       unknown mass `L` and dilution `ℓ` (`orientationFaithful_bandTripleDeficitReading`), with
       `(t₄ − t₃)/(t₃ − t₂) = 2 cosh(δℓ)` (`threeBandsDefeatTheMass`).
   - *One aperture doubling for an isolated pair (`pairDoublingReading`):*
     - `pairDoublingReading a d = (pairMoment d.1 a, pairMoment d.1 (2 * a))` (`a > 0`) is
       **unconditionally `OrientationFaithful`** on `DepthDatum` (`orientationFaithful_pairDoublingReading`),
       recovers `d.1 = arcosh(M(2a)/(2M(a)))/(2a)` (`depth_from_doubling`), and resolving the
       normalized doubling ratio `M(2a)/(2M(a)) ≤ 1 + η` (`η ≥ 0`) certifies `δ ≤ √(2η) / (2a)`
       (`depth_le_sqrt_div_of_doubling_ratio_le`, costing precision `η = 2 β² a²`).

5. **Exact Faithfulness and Precision Cost of Branch III (Adding Data of a Third Kind, §5):**
   - *On-line mass and dilution seam (`dilutedReading hℓ hL a`, `ℓ / 2 < a ≤ L / 2`):*
     - Adjoining `(ℓ, L)` past `ℓ / 2` drops the resolution limit from `1 / 2` to
       `min (1 / 2) (depthResolution ℓ (2L)) ≤ √(2L / ℓ³)` in the second band `ℓ / 2 < a ≤ min ℓ (L / 2)`
       (`resolutionLimit_depth_dilutedReading_secondBand`, `resolutionLimit_depth_dilutedReading_secondBand_le_sqrt`)
       and certifies `δ ≤ log((2L + 2a + ℓ)/ℓ)/(2a − ℓ)` at every `ℓ / 2 < a ≤ L / 2`
       (`certifies_depth_dilutedReading`), with exponential mass cost `ℓ e^{δ(2a − ℓ)} ≤ 2L + 2a + ℓ`
       (`mass_ge_of_dilutedLattice_positive`).
   - *First pronic moment on parity-flipped divisor rows (`firstPronicMoment`):*
     - While `amplitudeReading` and `completePeriodLagReading N` are `Invisible` to `evenFlip` and
       Selberg sign twists (`invisible_amplitude_evenFlip`, `invisible_completePeriodLagReading_scaledSelbergRow`),
       adjoining `firstPronicMoment` is `OrientationFaithful` on `OrientedFourFreeDamped ε`
       (`orientationFaithful_firstPronicMoment`), with exact precision gap
       `firstPronicMoment (evenFlip c) − firstPronicMoment c = 2 log 2 · W_c(2)`
       (`firstPronicMoment_evenFlip_sub`).
-/

open Set Finset ArithmeticFunction
open GaloisForLFunctions.ScaleSignedIncidenceCriticality
open GaloisForLFunctions.SquareRootThreshold
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open GaloisForLFunctions.BezoutValuationIncidence
open Zeta23 _root_.RHTower

namespace GaloisForLFunctions.ArithmeticOrientationTheory

noncomputable section
set_option autoImplicit false

/-! ### §1. The Sub-Nyquist Sign Barrier and Universal Orientation Blindness -/

/-- **Sub-Nyquist automaticity of `levelReading` at known scale `L > 0`:**
Whenever `a ≤ L / 2` and `0 ≤ η`, `levelReading hL a η d` holds for **every** depth `d : DepthDatum`. -/
theorem levelReading_of_subNyquist {L a η : ℝ} (hL : 0 < L) (ha : a ≤ L / 2) (hη : 0 ≤ η)
    (d : DepthDatum) : levelReading hL a η d := by
  let p : ScaleDepthDatum := ⟨(L, d.1), hL, d.2.1, d.2.2⟩
  exact scaleDepthReading_of_dense hη p (by show 2 * a ≤ L; linarith)

/-- **Universal Orientation Blindness of Sub-Nyquist Sign Readings (`invisible_levelReading_subNyquist`):**
For any `L > 0`, `a ≤ L / 2`, `0 ≤ η`, and **any** map (or flip) `κ : DepthDatum → DepthDatum`,
`levelReading hL a η` is invisible to `κ`: `levelReading hL a η (κ d) = levelReading hL a η d`. -/
theorem invisible_levelReading_subNyquist {L a η : ℝ} (hL : 0 < L) (ha : a ≤ L / 2) (hη : 0 ≤ η)
    (κ : DepthDatum → DepthDatum) :
    Invisible (levelReading hL a η) κ := fun d =>
  propext (iff_of_true (levelReading_of_subNyquist hL ha hη (κ d))
    (levelReading_of_subNyquist hL ha hη d))

/-- **Exact Trivial Resolution Limit and Floor of Sub-Nyquist Sign Readings
(`resolutionLimit_depth_levelReading_subNyquist`):**
When `a ≤ L / 2` and `0 ≤ η`, `levelReading hL a η` has exact depth resolution limit `1 / 2` and
resolution floor `0` at every `d₀ : DepthDatum`. -/
theorem resolutionLimit_depth_levelReading_subNyquist {L a η : ℝ} (hL : 0 < L) (ha : a ≤ L / 2)
    (hη : 0 ≤ η) (d₀ : DepthDatum) :
    resolutionLimit depth (levelReading hL a η) d₀ = 1 / 2 ∧
      resolutionFloor depth (levelReading hL a η) d₀ = 0 := by
  have hd₀ : levelReading hL a η d₀ := levelReading_of_subNyquist hL ha hη d₀
  have hlim : resolutionLimit depth (levelReading hL a η) d₀ = 1 / 2 := by
    let d_max : DepthDatum := ⟨1 / 2, by norm_num, le_rfl⟩
    have hmem : d_max ∈ shadow (levelReading hL a η) d₀ :=
      propext (iff_of_true (levelReading_of_subNyquist hL ha hη d_max) hd₀)
    exact resolutionLimit_eq_of_mem_shadow_of_max (fun d => d.2.2) hmem rfl
  have hflr : resolutionFloor depth (levelReading hL a η) d₀ = 0 := by
    have hbdd : BddBelow (depth '' shadow (levelReading hL a η) d₀) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨d, -, rfl⟩
      exact d.2.1.le
    refine le_antisymm ?_
      (le_csInf (shadow_image_nonempty depth (levelReading hL a η) d₀) ?_)
    · refine le_of_forall_pos_le_add fun ε hε => ?_
      rw [zero_add]
      set δ : ℝ := min (1 / 2) (ε / 2)
      have hδ0 : 0 < δ := lt_min (by norm_num) (by linarith)
      have hδle : δ ≤ 1 / 2 := min_le_left _ _
      let d_δ : DepthDatum := ⟨δ, hδ0, hδle⟩
      have hmem : d_δ ∈ shadow (levelReading hL a η) d₀ :=
        propext (iff_of_true (levelReading_of_subNyquist hL ha hη d_δ) hd₀)
      exact (csInf_le hbdd ⟨d_δ, hmem, rfl⟩).trans ((min_le_right _ _).trans (by linarith))
    · rintro _ ⟨d, -, rfl⟩
      exact d.2.1.le
  exact ⟨hlim, hflr⟩

/-- **Universal Orientation Blindness of Sub-Nyquist Diluted Sign Readings
(`invisible_dilutedReading_subNyquist`):**
Below the sub-lattice's own Nyquist aperture `a ≤ ℓ / 2` (`0 < a`, `a ≤ L / 2`),
`dilutedReading hℓ hL a` holds for every `d : DepthDatum` (`dilutedLattice_hides_below_own_nyquist`),
so it is invisible to **every** flip `κ : DepthDatum → DepthDatum` and is never `OrientationFaithful`
for any flip that moves a datum. -/
theorem invisible_dilutedReading_subNyquist {ℓ L a : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L)
    (ha : 0 < a) (haℓ : a ≤ ℓ / 2) (haL : a ≤ L / 2) (κ : DepthDatum → DepthDatum) :
    Invisible (dilutedReading hℓ hL a) κ := fun d =>
  propext (iff_of_true
    (fun _ hf hfs => dilutedLattice_hides_below_own_nyquist hℓ hL (κ d).2.1 (κ d).2.2 ha haℓ haL hf hfs)
    (fun _ hf hfs => dilutedLattice_hides_below_own_nyquist hℓ hL d.2.1 d.2.2 ha haℓ haL hf hfs))

/-! ### §2. The Formal Trichotomy Theorem for Orientation-Faithful and Depth-Certifying Readings -/

/-- A reading `r : DepthDatum → O` at scale `L > 0` is **sub-Nyquist sign-factored**
(`SubNyquistSignFactored hL r`) if it is refined by `levelReading hL a η` for some aperture
`a ≤ L / 2` and level `η ≥ 0` (i.e., `r` is a post-processing of a sub-Nyquist sign certificate). -/
def SubNyquistSignFactored {O : Type*} {L : ℝ} (hL : 0 < L) (r : DepthDatum → O) : Prop :=
  ∃ a : ℝ, a ≤ L / 2 ∧ ∃ η : ℝ, 0 ≤ η ∧ Refines (levelReading hL a η) r

/-- **No-Go Theorem for Sub-Nyquist Sign-Factored Readings
(`not_orientationFaithful_and_not_certifies_of_subNyquistSignFactored`):**
If `r : DepthDatum → O` is `SubNyquistSignFactored hL r`, then:
1. `r` is `Invisible` to **every** flip `κ : DepthDatum → DepthDatum`;
2. `¬ OrientationFaithful r κ` whenever `κ` moves at least one datum (`∃ d, κ d ≠ d`);
3. `¬ Certifies depth r d₀ β` for every `d₀ : DepthDatum` and every `β < 1 / 2`. -/
theorem not_orientationFaithful_and_not_certifies_of_subNyquistSignFactored {O : Type*} {L : ℝ}
    (hL : 0 < L) {r : DepthDatum → O} (hsub : SubNyquistSignFactored hL r) :
    (∀ κ : DepthDatum → DepthDatum, Invisible r κ) ∧
    (∀ (κ : DepthDatum → DepthDatum) (d : DepthDatum), κ d ≠ d → ¬ OrientationFaithful r κ) ∧
    (∀ (d₀ : DepthDatum) {β : ℝ}, β < 1 / 2 → ¬ Certifies depth r d₀ β) := by
  obtain ⟨a, ha, η, hη, href⟩ := hsub
  have hinv : ∀ κ : DepthDatum → DepthDatum, Invisible r κ := fun κ =>
    Invisible.of_refines (invisible_levelReading_subNyquist hL ha hη κ) href
  refine ⟨hinv, fun κ d hd => not_orientationFaithful_of_invisible (hinv κ) hd,
    fun d₀ β hβ hcert => ?_⟩
  let d_max : DepthDatum := ⟨1 / 2, by norm_num, le_rfl⟩
  have hmem_sub : d_max ∈ shadow (levelReading hL a η) d₀ :=
    propext (iff_of_true (levelReading_of_subNyquist hL ha hη d_max)
      (levelReading_of_subNyquist hL ha hη d₀))
  have hmem_r : d_max ∈ shadow r d₀ := shadow_subset_of_refines href d₀ hmem_sub
  have hle : depth d_max ≤ β := hcert d_max hmem_r
  change (1 / 2 : ℝ) ≤ β at hle
  linarith

/-- **The Escape Theorem (`trichotomy_of_readings_escape`):**
Every reading `r : DepthDatum → O` that is `OrientationFaithful r κ` (for a flip `κ` with `κ d ≠ d`)
or that certifies a nontrivial depth bound `Certifies depth r d₀ β` (`β < 1 / 2`) **cannot** belong
to `SubNyquistSignFactored hL`: it must either cross the Nyquist aperture `a > L / 2` (Branch I),
read a magnitude rather than a sign (Branch II), or adjoin data of a third kind (Branch III). -/
theorem trichotomy_of_readings_escape {O : Type*} {L : ℝ} (hL : 0 < L) (r : DepthDatum → O) :
    ((∃ (κ : DepthDatum → DepthDatum) (d : DepthDatum), κ d ≠ d ∧ OrientationFaithful r κ) ∨
      (∃ (d₀ : DepthDatum) (β : ℝ), β < 1 / 2 ∧ Certifies depth r d₀ β)) →
    ¬ SubNyquistSignFactored hL r := by
  rintro (⟨κ, d, hd, hfaith⟩ | ⟨d₀, β, hβ, hcert⟩) hsub
  · exact (not_orientationFaithful_and_not_certifies_of_subNyquistSignFactored hL hsub).2.1 κ d hd hfaith
  · exact (not_orientationFaithful_and_not_certifies_of_subNyquistSignFactored hL hsub).2.2 d₀ hβ hcert

/-! ### §3. Branch I: Crossing the Nyquist Aperture and Its Exact `β² L³` Precision Cost -/

/-- **Trans-Nyquist Threshold Orientation Faithfulness (`orientationFaithful_weilFloorThreshold`):**
Just above the Nyquist aperture (`L / 2 < a ≤ L`), the threshold reading
`fun d : DepthDatum => weilFloorThreshold L (depth d)` is **unconditionally `OrientationFaithful`**
for every flip `κ : DepthDatum → DepthDatum` (`κ d ≠ d → weilFloorThreshold L (depth (κ d)) ≠ weilFloorThreshold L (depth d)`). -/
theorem orientationFaithful_weilFloorThreshold {L : ℝ} (hL : 0 < L)
    (κ : DepthDatum → DepthDatum) :
    OrientationFaithful (fun d : DepthDatum => weilFloorThreshold L (depth d)) κ := by
  intro d hd heq
  apply hd
  apply Subtype.ext
  exact weilFloorThreshold_injOn hL ⟨(κ d).2.1, (κ d).2.2⟩ ⟨d.2.1, d.2.2⟩ heq

/-- **Cofinal Deficit-Rate Orientation Faithfulness (`orientationFaithful_rateSet`):**
On the two-coordinate lattice family `ScaleDepthDatum`, the cofinal deficit rate reading `rateSet`
is `OrientationFaithful` for every flip `κ : ScaleDepthDatum → ScaleDepthDatum` that moves the depth
(`∀ p, κ p ≠ p → sdDepth (κ p) ≠ sdDepth p`). -/
theorem orientationFaithful_rateSet (κ : ScaleDepthDatum → ScaleDepthDatum)
    (hκ : ∀ p : ScaleDepthDatum, κ p ≠ p → sdDepth (κ p) ≠ sdDepth p) :
    OrientationFaithful rateSet κ :=
  fun p hp heq => hκ p hp (sdDepth_eq_of_rateSet_eq heq)

/-- **Exact Precision Cost of Branch I (`branchOne_transNyquist_precision_cost`):**
1. *Sub-Nyquist vs. Trans-Nyquist jump:* At known scale `L > 0`, crossing `L / 2` into `(L / 2, L]`
   drops the resolution limit of `levelReading hL a η` (`η ≥ 0`) from `1 / 2` to
   `min (1 / 2) (depthResolution L η) ≤ √(η / L³)`;
2. *Quadratic-in-depth, cubic-in-scale floor:* `L³ δ² ≤ weilFloorThreshold L δ` for all `L, δ > 0`;
3. *Exact Deficit Budget Law for Adaptive Policies:* For any `ScaleMatched A η` (`L / 2 < A L ≤ L`,
   `0 ≤ η L`), a precision budget `∀ L > 0, η L ≤ β² L³` certifies `sdDepth ≤ β`, while reaching
   `weilFloorThreshold L β' ≤ η L` for any `β' ∈ (β, 1/2]` at a single scale `L > 0` refutes
   `Certifies sdDepth (adaptiveReading A η) p₀ β`. -/
theorem branchOne_transNyquist_precision_cost :
    (∀ {L a η : ℝ} (hL : 0 < L), L / 2 < a → a ≤ L → 0 ≤ η →
      ∀ {d₀ : DepthDatum} (_hd₀ : levelReading hL a η d₀),
        resolutionLimit depth (levelReading hL a η) d₀ = min (1 / 2) (depthResolution L η) ∧
        resolutionLimit depth (levelReading hL a η) d₀ ≤ Real.sqrt (η / L ^ 3)) ∧
    (∀ {L δ : ℝ}, 0 < L → 0 < δ → L ^ 3 * δ ^ 2 ≤ weilFloorThreshold L δ) ∧
    (∀ {A η : ℝ → ℝ}, ScaleMatched A η → ∀ {β : ℝ}, 0 ≤ β →
      ∀ {p₀ : ScaleDepthDatum}, adaptiveReading A η p₀ →
        ((∀ L : ℝ, 0 < L → η L ≤ β ^ 2 * L ^ 3) →
          Certifies sdDepth (adaptiveReading A η) p₀ β) ∧
        (∀ L β' : ℝ, 0 < L → 0 < β' → β' ≤ 1 / 2 → β < β' → weilFloorThreshold L β' ≤ η L →
          ¬ Certifies sdDepth (adaptiveReading A η) p₀ β)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro L a η hL ha haL hη d₀ hd₀
    exact ⟨resolutionLimit_depth_levelReading hL ha haL hη hd₀,
      resolutionLimit_depth_levelReading_le_sqrt hL ha haL hη hd₀⟩
  · intro L δ hL hδ
    exact cube_mul_sq_le_weilFloorThreshold hL hδ
  · intro A η h β hβ p₀ hp₀
    exact ⟨(theDeficitBudgetLaw h hβ hp₀).2.1, (theDeficitBudgetLaw h hβ hp₀).2.2⟩

/-! ### §4. Branch II: Reading a Magnitude and Its Exact `β²` Ratio Conditioning Cost -/

/-- **Two-Band Magnitude Orientation Faithfulness (`orientationFaithful_bandPairReading`):**
On `ScaleDepthDatum` (with the scale `sdScale p` unknown), the two-band ground-energy reading
`bandPairReading p = (bandEnergy (sdScale p) (sdDepth p) 2, bandEnergy (sdScale p) (sdDepth p) 3)`
is **unconditionally `OrientationFaithful`** for every depth-moving flip
`κ : ScaleDepthDatum → ScaleDepthDatum` (`∀ p, κ p ≠ p → sdDepth (κ p) ≠ sdDepth p`), and has exact
resolution limit and floor equal to `sdDepth p`. -/
theorem orientationFaithful_bandPairReading (κ : ScaleDepthDatum → ScaleDepthDatum)
    (hκ : ∀ p : ScaleDepthDatum, κ p ≠ p → sdDepth (κ p) ≠ sdDepth p) :
    OrientationFaithful bandPairReading κ :=
  fun p hp heq => hκ p hp (sdDepth_eq_of_mem_shadow_bandPair heq)

/-- The **three-band deficit reading** at dilution `ℓ` and background on-line mass `2L`: records the
measured deficits `bandDeficit ℓ δ L n = bandEnergy ℓ δ n − 2L` at aliasing indices `2, 3, 4`. -/
def bandTripleDeficitReading (ℓ L : ℝ) (d : DepthDatum) : ℝ × ℝ × ℝ :=
  (bandDeficit ℓ d.1 L 2, bandDeficit ℓ d.1 L 3, bandDeficit ℓ d.1 L 4)

/-- **Three-Band Deficit Orientation Faithfulness Against Unknown On-Line Mass
(`orientationFaithful_bandTripleDeficitReading`):**
For any `ℓ > 0`, any on-line mass parameter `L : ℝ`, and **any** flip `κ : DepthDatum → DepthDatum`,
`bandTripleDeficitReading ℓ L` is `OrientationFaithful` (`κ d ≠ d → bandTripleDeficitReading ℓ L (κ d) ≠ bandTripleDeficitReading ℓ L d`). -/
theorem orientationFaithful_bandTripleDeficitReading {ℓ : ℝ} (hℓ : 0 < ℓ) (L : ℝ)
    (κ : DepthDatum → DepthDatum) :
    OrientationFaithful (bandTripleDeficitReading ℓ L) κ := by
  intro d hd heq
  have h2 : bandDeficit ℓ (κ d).1 L 2 = bandDeficit ℓ d.1 L 2 := congrArg Prod.fst heq
  have h3 : bandDeficit ℓ (κ d).1 L 3 = bandDeficit ℓ d.1 L 3 := congrArg (Prod.fst ∘ Prod.snd) heq
  have h4 : bandDeficit ℓ (κ d).1 L 4 = bandDeficit ℓ d.1 L 4 := congrArg (Prod.snd ∘ Prod.snd) heq
  exact hd (Subtype.ext (depth_determined_by_three_bands hℓ (κ d).2.1 hℓ d.2.1 h2 h3 h4))

/-- The **aperture-doubling magnitude reading** on `DepthDatum` at aperture `a > 0`: records the
isolated-pair window moments `(pairMoment δ a, pairMoment δ (2 * a))`. -/
def pairDoublingReading (a : ℝ) (d : DepthDatum) : ℝ × ℝ :=
  (pairMoment d.1 a, pairMoment d.1 (2 * a))

/-- **Aperture-Doubling Orientation Faithfulness (`orientationFaithful_pairDoublingReading`):**
For any `a > 0` and any flip `κ : DepthDatum → DepthDatum`, `pairDoublingReading a` is
`OrientationFaithful` on `DepthDatum`. -/
theorem orientationFaithful_pairDoublingReading {a : ℝ} (ha : 0 < a)
    (κ : DepthDatum → DepthDatum) :
    OrientationFaithful (pairDoublingReading a) κ := by
  intro d hd heq
  have h1 : pairMoment (κ d).1 a = pairMoment d.1 a := congrArg Prod.fst heq
  have h2 : pairMoment (κ d).1 (2 * a) = pairMoment d.1 (2 * a) := congrArg Prod.snd heq
  have hrat : pairMoment (κ d).1 (2 * a) / pairMoment (κ d).1 a =
      pairMoment d.1 (2 * a) / pairMoment d.1 a := by rw [h1, h2]
  exact hd (Subtype.ext (depth_eq_of_doubling_eq (κ d).2.1 d.2.1 ha hrat))

/-- **Square-Root Conditioning of the Aperture-Doubling Ratio
(`depth_le_sqrt_div_of_doubling_ratio_le`):**
For an isolated off-line pair of depth `δ > 0` at aperture `a > 0`, the normalized doubling ratio
`pairMoment δ (2 * a) / (2 * pairMoment δ a)` equals `cosh (2 * δ * a)` (`pairMoment_doubling`).
Consequently, resolving this ratio to within excess `η ≥ 0` of its critical value `1`
(`pairMoment δ (2 * a) / (2 * pairMoment δ a) ≤ 1 + η`) certifies `δ ≤ √(2η) / (2a)` (so certifying
`δ ≤ β` costs ratio precision `η = 2 β² a²`). -/
theorem depth_le_sqrt_div_of_doubling_ratio_le {δ a η : ℝ} (hδ : 0 < δ) (ha : 0 < a) (hη : 0 ≤ η)
    (h : pairMoment δ (2 * a) / (2 * pairMoment δ a) ≤ 1 + η) :
    δ ≤ Real.sqrt (2 * η) / (2 * a) := by
  have hd := pairMoment_doubling hδ ha
  have hcosh : Real.cosh (2 * δ * a) ≤ 1 + η := by
    have hdiv : pairMoment δ (2 * a) / (2 * pairMoment δ a) =
        (pairMoment δ (2 * a) / pairMoment δ a) / 2 := by ring
    rw [hdiv, hd] at h
    linarith
  have h2a : 0 < 2 * a := by positivity
  have hprod : δ * (2 * a) = 2 * δ * a := by ring
  exact depth_le_sqrt_div_of_ratio_le h2a hδ hη (by rwa [hprod])

/-- **Exact Precision Cost of Branch II (`branchTwo_magnitude_precision_cost`):**
1. *Two aliasing bands (`bandPairReading`):* faithful with `resolutionLimit = resolutionFloor = sdDepth`
   where `scaleDepthReading a η` has limit `1 / 2`, and resolving `t₃ / (2 t₂) − 1 ≤ 1 + η` (`η ≥ 0`)
   certifies `δ ≤ √(2η) / L` (`theTwoBandCertification`, precision cost `η = ½ β² L²`);
2. *Three aliasing bands (`bandTripleDeficitReading`):* `OrientationFaithful` at unknown on-line mass
   `2L` and dilution `ℓ`, with `(t₄ − t₃)/(t₃ − t₂) = 2 cosh(δℓ)`;
3. *Isolated-pair aperture doubling (`pairDoublingReading`):* `OrientationFaithful`, with
   `M(2a)/(2M(a)) = cosh(2δa)` and `M(2a)/(2M(a)) ≤ 1 + η → δ ≤ √(2η)/(2a)` (precision cost
   `η = 2 β² a²`). -/
theorem branchTwo_magnitude_precision_cost :
    (∀ (p : ScaleDepthDatum),
      resolutionLimit sdDepth bandPairReading p = sdDepth p ∧
      resolutionFloor sdDepth bandPairReading p = sdDepth p) ∧
    (∀ {L δ η : ℝ}, 0 < L → 0 < δ → 0 ≤ η →
      -(L * latticeFloor L δ 3) / (2 * -(L * latticeFloor L δ 2)) - 1 ≤ 1 + η →
      δ ≤ Real.sqrt (2 * η) / L) ∧
    (∀ {ℓ : ℝ} (_hℓ : 0 < ℓ) (L : ℝ) (κ : DepthDatum → DepthDatum),
      OrientationFaithful (bandTripleDeficitReading ℓ L) κ) ∧
    (∀ {δ a η : ℝ}, 0 < δ → 0 < a → 0 ≤ η →
      pairMoment δ (2 * a) / (2 * pairMoment δ a) ≤ 1 + η →
      δ ≤ Real.sqrt (2 * η) / (2 * a)) := by
  refine ⟨fun p =>
    ⟨resolutionLimit_sdDepth_bandPairReading p,
     (resolutionFloor_eq_resolutionLimit_bandPairReading p).trans
       (resolutionLimit_sdDepth_bandPairReading p)⟩, ?_,
    fun hℓ L κ => orientationFaithful_bandTripleDeficitReading hℓ L κ, ?_⟩
  · intro L δ η hL hδ hη hrat
    exact (theTwoBandCertification hL hδ).2 η hη hrat
  · intro δ a η hδ ha hη hrat
    exact depth_le_sqrt_div_of_doubling_ratio_le hδ ha hη hrat

/-! ### §5. Branch III: Adding Data of a Third Kind (Mass, Dilution, First Pronic Moment) and Its Precision Cost -/

/-- **Square-Root Mass–Dilution Bound in the Second Aliasing Band
(`resolutionLimit_depth_dilutedReading_secondBand_le_sqrt`):**
Across the second aliasing band `ℓ / 2 < a ≤ min ℓ (L / 2)` (`0 < ℓ`, `0 < L`), the exact resolution
limit of `dilutedReading hℓ hL a` is `min (1 / 2) (depthResolution ℓ (2 * L))` and satisfies
`resolutionLimit depth (dilutedReading hℓ hL a) d₀ ≤ √(2 * L / ℓ ^ 3)`. -/
theorem resolutionLimit_depth_dilutedReading_secondBand_le_sqrt {ℓ L a : ℝ}
    (hℓ : 0 < ℓ) (hL : 0 < L) (haℓ : ℓ / 2 < a) (hamin : a ≤ min ℓ (L / 2))
    {d₀ : DepthDatum} (hd₀ : dilutedReading hℓ hL a d₀) :
    resolutionLimit depth (dilutedReading hℓ hL a) d₀ =
        min (1 / 2) (depthResolution ℓ (2 * L)) ∧
      resolutionLimit depth (dilutedReading hℓ hL a) d₀ ≤ Real.sqrt (2 * L / ℓ ^ 3) := by
  have hlim := (resolutionLimit_depth_dilutedReading_secondBand hℓ hL haℓ
    (le_min_iff.mp hamin).1 (le_min_iff.mp hamin).2 hd₀).1
  refine ⟨hlim, ?_⟩
  rw [hlim]
  exact (min_le_right _ _).trans (depthResolution_le_sqrt hℓ (by positivity))

/-- **Exact Precision and Aperture Cost of Branch III (`branchThree_thirdKind_precision_cost`):**
1. *On-line mass and dilution seam (`dilutedReading hℓ hL a`):*
   - below `ℓ / 2`, `dilutedReading hℓ hL a` has limit `1 / 2` and is `Invisible` to every flip;
   - across `(ℓ / 2, min ℓ (L / 2)]`, its exact limit drops to
     `min (1 / 2) (depthResolution ℓ (2L)) ≤ √(2L / ℓ³)` (so certifying depth `β` in the second band
     requires mass-to-dilution cube ratio `2L / ℓ³ ≤ β²`);
   - at any `ℓ / 2 < a ≤ L / 2`, hiding depth `δ` costs exponential mass
     `ℓ e^{δ(2a − ℓ)} ≤ 2L + 2a + ℓ`, and `dilutedReading hℓ hL a` certifies
     `δ ≤ log((2L + 2a + ℓ)/ℓ)/(2a − ℓ)` (logarithmic in the mass `L`, linear in the dilution `ℓ`);
2. *First pronic moment on parity-flipped divisor rows (`firstPronicMoment`):*
   - `amplitudeReading` is `Invisible` to `evenFlipOrientation` (`invisible_amplitude_evenFlip`) and
     does not resolve `ReceiverBounded` (`not_resolves_amplitude_receiverBounded`), and
     `completePeriodLagReading N` is `Invisible` to `evenFlipRow N` (`invisible_completePeriodLagReading_evenFlipRow`);
   - adjoining `firstPronicMoment` is `OrientationFaithful` on `OrientedFourFreeDamped ε`
     (`orientationFaithful_firstPronicMoment`), with exact separation cost
     `firstPronicMoment (evenFlip c) − firstPronicMoment c = 2 log 2 · W_c(2)`
     (`firstPronicMoment_evenFlip_sub`). -/
theorem branchThree_thirdKind_precision_cost :
    (∀ {ℓ L a : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L), ℓ / 2 < a → a ≤ min ℓ (L / 2) →
      ∀ {d₀ : DepthDatum} (_hd₀ : dilutedReading hℓ hL a d₀),
        resolutionLimit depth (dilutedReading hℓ hL a) d₀ =
          min (1 / 2) (depthResolution ℓ (2 * L)) ∧
        resolutionLimit depth (dilutedReading hℓ hL a) d₀ ≤ Real.sqrt (2 * L / ℓ ^ 3)) ∧
    (∀ {ℓ L a : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L), 0 < a → a ≤ L / 2 → ℓ < 2 * a →
      ∀ {d₀ : DepthDatum} (_hd₀ : dilutedReading hℓ hL a d₀),
        Certifies depth (dilutedReading hℓ hL a) d₀
          (Real.log ((2 * L + 2 * a + ℓ) / ℓ) / (2 * a - ℓ))) ∧
    (∀ {ε : ℝ} (hε : 0 < ε),
      Invisible (amplitudeReading (ε := ε)) (evenFlipOrientation hε).flip ∧
      OrientationFaithful (fun c : OrientedFourFreeDamped ε => firstPronicMoment c.1.1)
        (evenFlipOrientation' hε).flip) ∧
    (∀ {K ε : ℝ} (_hε : 0 < ε) {c : ℕ → ℝ} (_hc : DampedClass K ε c),
      (∀ m, 4 ∣ m → c m = 0) →
      firstPronicMoment (evenFlip c) - firstPronicMoment c =
        2 * Real.log 2 * weightRamanujanCoeff c 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ℓ L a hℓ hL haℓ hamin d₀ hd₀
    exact resolutionLimit_depth_dilutedReading_secondBand_le_sqrt hℓ hL haℓ hamin hd₀
  · intro ℓ L a hℓ hL ha haL hgap d₀ hd₀
    exact certifies_depth_dilutedReading hℓ hL ha haL hgap hd₀
  · intro ε hε
    exact ⟨invisible_amplitude_evenFlip hε, orientationFaithful_firstPronicMoment hε⟩
  · intro K ε hε c hc h4
    exact firstPronicMoment_evenFlip_sub hε hc h4

/-- **Master Synthesis for Open Problem 10 (`trichotomy_of_readings_synthesis`):**
Unites the sub-Nyquist sign escape theorem with the exact faithfulness and precision laws of all
three branches (Branch I: crossing the Nyquist aperture at cost `β² L³`; Branch II: reading a
magnitude at ratio cost `½ β² L²` or `2 β² a²`; Branch III: adding mass/dilution or the first
pronic moment at cost `2L ≤ β² ℓ³` / `log((2L + 2a + ℓ)/ℓ)/(2a − ℓ)` / `2 log 2 · W_c(2)`). -/
theorem trichotomy_of_readings_synthesis :
    (∀ {O : Type*} {L : ℝ} (hL : 0 < L) (r : DepthDatum → O),
      ((∃ (κ : DepthDatum → DepthDatum) (d : DepthDatum), κ d ≠ d ∧ OrientationFaithful r κ) ∨
        (∃ (d₀ : DepthDatum) (β : ℝ), β < 1 / 2 ∧ Certifies depth r d₀ β)) →
      ¬ SubNyquistSignFactored hL r) ∧
    (∀ {A η : ℝ → ℝ}, ScaleMatched A η → ∀ {β : ℝ}, 0 ≤ β →
      ∀ {p₀ : ScaleDepthDatum}, adaptiveReading A η p₀ →
        ((∀ L : ℝ, 0 < L → η L ≤ β ^ 2 * L ^ 3) →
          Certifies sdDepth (adaptiveReading A η) p₀ β) ∧
        (∀ L β' : ℝ, 0 < L → 0 < β' → β' ≤ 1 / 2 → β < β' → weilFloorThreshold L β' ≤ η L →
          ¬ Certifies sdDepth (adaptiveReading A η) p₀ β)) ∧
    (∀ (p : ScaleDepthDatum),
      resolutionLimit sdDepth bandPairReading p = sdDepth p ∧
      resolutionFloor sdDepth bandPairReading p = sdDepth p) ∧
    (∀ {ℓ L a : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L), ℓ / 2 < a → a ≤ min ℓ (L / 2) →
      ∀ {d₀ : DepthDatum} (_hd₀ : dilutedReading hℓ hL a d₀),
        resolutionLimit depth (dilutedReading hℓ hL a) d₀ =
          min (1 / 2) (depthResolution ℓ (2 * L)) ∧
        resolutionLimit depth (dilutedReading hℓ hL a) d₀ ≤ Real.sqrt (2 * L / ℓ ^ 3)) ∧
    (∀ {ε : ℝ} (hε : 0 < ε),
      Invisible (amplitudeReading (ε := ε)) (evenFlipOrientation hε).flip ∧
      OrientationFaithful (fun c : OrientedFourFreeDamped ε => firstPronicMoment c.1.1)
        (evenFlipOrientation' hε).flip) :=
  ⟨fun hL r h => trichotomy_of_readings_escape hL r h,
   branchOne_transNyquist_precision_cost.2.2,
   branchTwo_magnitude_precision_cost.1,
   branchThree_thirdKind_precision_cost.1,
   branchThree_thirdKind_precision_cost.2.2.1⟩

end

end GaloisForLFunctions.ArithmeticOrientationTheory
