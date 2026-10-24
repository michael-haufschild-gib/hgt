import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheResolutionLimitOfAReading
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheBoundedApertureRateCertifiesNothing
import GaloisForLFunctions.SquareRootThreshold.TheIncidenceLedgerGradedByTheZeroWidth
import GaloisForLFunctions.ArithmeticIncidencePositivity.PrimeTowerLedgerReduction
import GaloisForLFunctions.ArithmeticCompensationTheory.ThePrimeCombIsATranslation
import GaloisForLFunctions.ArithmeticCompensationTheory.CompensationCoordinates
import GaloisForLFunctions.ArithmeticCompensationTheory.ThePrimePolarResidualHasTheDeLaValleePoussinSaving

/-!
# The Numerical Unit for the Incidence Ledger

This module resolves **Open Problem 7** of `ScaleSignedIncidenceCriticality`:
computing the numerical admissibility unit of the incidence ledger of
`ArithmeticIncidencePositivity`, exhibiting explicit witness pairs that prove the
information loss of the unsigned scalar prime-comb second moment, and identifying the
exact signed pairings and coherent residuals that complete the scalar reading into a
faithful one.

## Mathematical Architecture

1. **§1. The Admissibility Unit of the Incidence Ledger**:
   - The odd incidence ledger (`fullZeroForm_eq_incidenceLedger`) expresses `Ẑ(F)` as the negative
     of the net allocation deficit `ledgerDeficit F r R` (`fullZeroForm_eq_neg_ledgerDeficit`),
     which equals `2 * primeSideCharge F + poleCharge F` minus the archimedean surplus pool,
     crossing potential, and gauge remainder (`ledgerDeficit_eq_primeSideCharge`).
   - By the prime-tower reduction (`primeSideCharge_le_sum_primes`), the entire prime-power side is
     dominated by the subcritical Euler-tower diagonal `combSubcriticalHorizonMass r * autoCorr F 0`
     plus the **first-power prime-comb charge** `combCharge F r`
     (`primeSideCharge_le_combSubcritical_add_combCharge`, `fullZeroForm_ge_combCharge_ledger`).
   - Consequently, the graded allocation condition `GradedIncidenceAllocation σ C` is equivalent to
     an exponential rate bound `C e^{2σr} ∫ F²` on `ledgerDeficit` (`gradedIncidenceAllocation_iff_ledgerDeficit_le`),
     and any graded bound on `2 * combCharge F r` against the archimedean/gauge pool at rate `2σ`
     certifies the zero-free strip `zetaZeroWidth ≤ σ` (`zetaZeroWidth_le_of_combCharge_graded_bound`).
   - In the rate-reading calculus on `GrowthProfile`, the admissibility unit of the ledger is the
     **cofinal exponential rate**: `rateBoundsOn S_cof` recovers `profileRate` on any cofinal
     aperture set (`sInf_rateBoundsOn`), whereas any reading of the ledger deficit restricted to
     bounded apertures `S_bdd : BoundedApertures` leaves the shadow rates unbounded above and
     certifies no rate bound whatever (`ledgerRateDichotomy`).

2. **§2. Explicit Witness Pairs for Scalar Comb-Energy Information Loss**:
   - At any fixed aperture, Cauchy–Schwarz (`sq_cost_le_mass_mul_combEnergy`) maps every positive-mass
     test `F` and finite comb `(s, w)` into `CombPairingDatum`: triples `(mass, energy, charge)` with
     `0 < mass`, `0 ≤ energy`, and `charge ^ 2 ≤ mass * energy` (`mkCombPairingDatum`).
   - The **unsigned scalar comb-energy reading** `scalarCombEnergyReading` observes only
     `(mass, energy) = (‖F‖², ‖C_r F‖²)` and discards the signed pairing `⟪F, C_r F⟫`.
   - For every `d₀ : CombPairingDatum`, three canonical admissible witnesses — `coherentWitness d₀`
     (`charge = +√(mass · energy)`), `orthogonalWitness d₀` (`charge = 0`), and
     `antiCoherentWitness d₀` (`charge = −√(mass · energy)`) — share the **exact same scalar reading**
     and attain the extremes of the Cauchy–Schwarz range (`exists_witness_pair_scalarCombEnergyReading`).
   - Consequently, under `scalarCombEnergyReading`:
     - `combChargeVal` has exact resolution limit `√(mass · energy)`, floor `−√(mass · energy)`, and
       interval `[−√(mass · energy), √(mass · energy)]`
       (`resolutionLimit_combChargeVal_scalarCombEnergyReading`,
       `resolutionFloor_combChargeVal_scalarCombEnergyReading`,
       `resolutionInterval_combChargeVal_scalarCombEnergyReading`);
     - the complete compensated energy `completeCombEnergy d = mass + energy + 2 * charge` has exact
       resolution limit `(√mass + √energy)²`, floor `(√mass − √energy)²`, and interval
       `[(√mass − √energy)², (√mass + √energy)²]`
       (`resolutionInterval_completeCombEnergy_scalarCombEnergyReading`), collapsing on the balanced
       locus `mass = energy` to `[0, 4 * mass]` (`resolutionFloor_completeCombEnergy_eq_zero_of_balanced`).
   - Across actual smooth odd compactly supported test profiles on `ℝ`, the dilated family
     `dilatedUnitOddBump c = rescaledTest unitOddBump c` (`c > 0`) shares with `unitOddBump` the
     **exact same** unit mass `A(0) = 1`, asymptotic normalized comb energy `lim E_r / S_r² = 1`,
     asymptotic exponential comb energy `lim E_r / e^{2r} = 4`, and cross-prime energy
     `lim combCross / e^{2r} = 4`, while its asymptotic normalized first-power charge
     `lim combCharge / S_r = autoCorr unitOddBump (2 / c)` realizes **every** target ratio
     `θ ∈ [0, 1)` (`dilatedUnitOddBump_same_scalar_comb_reading`,
     `exists_dilatedUnitOddBump_witness_for_every_charge_ratio`).

3. **§3. Faithful Completions by Signed Pairing and Coherent Residual**:
   - Adjoining the signed amplitude ratio `amplitudeReading d = gramAmplitude d.mass d.charge` to
     `scalarCombEnergyReading` produces `completedCombReading`, which is **faithful** (`Faithful`)
     for both `combChargeVal` (`faithful_combChargeVal_completedCombReading`) and
     `completeCombEnergy` (`faithful_completeCombEnergy_completedCombReading`), decomposing the
     complete energy via the Pythagorean law (`completeCombEnergy_eq_pythagorean`).
   - On concrete continuous compactly supported tests `F`, subtracting any reference profile `T`
     (in particular the horizon translate `T_r(x) = S_r · F(x + 2r)`) from `primeComb F (combPrimes r) combWeight`
     splits the first-power charge into the signed translate pairing `testPairing F T` plus a
     residual bounded by the **coherent translation-residual energy** `‖C_r F − T‖²`
     (`sq_combCharge_sub_translatePairing_le`, `sq_combCharge_sub_horizonTranslate_le`).
   - When `F` is supported in `[−r, r]`, `autoCorr F (2r) = 0`, so `combCharge F r` is controlled
     purely by the coherent translation-residual energy (`sq_combCharge_le_mass_mul_horizonResidualEnergy`),
     which vanishes asymptotically relative to `S_r²` on the slowly varying family
     (`tendsto_testPairing_normalizedComb_sub_translate`), while pairing the prime shift against its
     polar counterpart before squaring yields the unconditional de la Vallée Poussin saving
     `exp(−c√S)` (`exists_abs_primeShift_sub_polar_le`).
-/

open MeasureTheory Set Filter Topology
open scoped Real
open GaloisForLFunctions.ArithmeticCriticalityTheory
open GaloisForLFunctions.ArithmeticIncidencePositivity
open GaloisForLFunctions.ArithmeticCompensationTheory
open GaloisForLFunctions.SquareRootThreshold

noncomputable section

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

/-! ## §1. The Admissibility Unit of the Incidence Ledger -/

/-- The net allocation deficit of the odd incidence ledger at aperture `r` and plateau radius `R`:
the odd strip costs plus the pole charge, minus the archimedean surplus pool, crossing potential,
even strip gains, and gauge remainder. -/
def ledgerDeficit (F : ℝ → ℝ) (r R : ℝ) : ℝ :=
  (∑ n ∈ relevantShifts r, oddStripCost F r n) + poleCharge F -
    (surplusPool (aperturePlateau r R) F + crossingPotentialTerm (aperturePlateau r R) F +
      (∑ n ∈ relevantShifts r, evenStripGain F r n) +
      gaugeRemainder (aperturePlateau r R) F)

/-- On an odd `C²` compactly supported test supported in `[−r, r]` (`0 < r < R`), the full zero form
is the exact negative of the incidence ledger deficit. -/
theorem fullZeroForm_eq_neg_ledgerDeficit {F : ℝ → ℝ} {r R : ℝ} (hF : ContDiff ℝ 2 F)
    (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x) (hr : 0 < r)
    (hsupp : ∀ x, r < |x| → F x = 0) (hrR : r < R) :
    fullZeroForm F = -ledgerDeficit F r R := by
  rw [fullZeroForm_eq_incidenceLedger hF hFc hodd hr hsupp hrR, ledgerDeficit]
  ring

/-- By the even–odd shift identity (`sum_evenStripGain_sub_sum_oddStripCost`), the net prime-power
cost in `ledgerDeficit` equals `2 * primeSideCharge F`. -/
theorem ledgerDeficit_eq_primeSideCharge {F : ℝ → ℝ} {r R : ℝ} (hF : Continuous F)
    (hodd : ∀ x, F (-x) = -F x) (hr : 0 ≤ r) (hsupp : ∀ x, r < |x| → F x = 0) :
    ledgerDeficit F r R =
      2 * primeSideCharge F + poleCharge F -
        (surplusPool (aperturePlateau r R) F + crossingPotentialTerm (aperturePlateau r R) F +
          gaugeRemainder (aperturePlateau r R) F) := by
  have hnet := sum_evenStripGain_sub_sum_oddStripCost hF hodd hr hsupp
  rw [ledgerDeficit]
  linarith

/-- `GradedIncidenceAllocation σ C` holds if and only if `ledgerDeficit F r R ≤ C e^{2σr} ∫ F²`
at every aperture `0 < r < R` and every odd `C²` test supported in `[−r, r]`. -/
theorem gradedIncidenceAllocation_iff_ledgerDeficit_le (σ C : ℝ) :
    GradedIncidenceAllocation σ C ↔
      ∀ (r R : ℝ) (F : ℝ → ℝ), 0 < r → r < R → ContDiff ℝ 2 F → HasCompactSupport F →
        (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) →
        ledgerDeficit F r R ≤ C * Real.exp (2 * σ * r) * ∫ x, F x ^ 2 := by
  constructor
  · intro h r R F hr hrR hF hFc hodd hsupp
    have hal := h r R F hr hrR hF hFc hodd hsupp
    rw [ledgerDeficit]
    linarith
  · intro h r R F hr hrR hF hFc hodd hsupp
    have hal := h r R F hr hrR hF hFc hodd hsupp
    rw [ledgerDeficit] at hal
    linarith

/-- `GradedIncidenceAllocation σ C` is equivalent to bounding `2 * primeSideCharge F + poleCharge F`
against the archimedean pool, crossing potential, gauge remainder, and `C e^{2σr} ∫ F²`. -/
theorem gradedIncidenceAllocation_iff_primeSideCharge_le (σ C : ℝ) :
    GradedIncidenceAllocation σ C ↔
      ∀ (r R : ℝ) (F : ℝ → ℝ), 0 < r → r < R → ContDiff ℝ 2 F → HasCompactSupport F →
        (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) →
        2 * primeSideCharge F + poleCharge F ≤
          surplusPool (aperturePlateau r R) F + crossingPotentialTerm (aperturePlateau r R) F +
            gaugeRemainder (aperturePlateau r R) F + C * Real.exp (2 * σ * r) * ∫ x, F x ^ 2 := by
  rw [gradedIncidenceAllocation_iff_ledgerDeficit_le]
  constructor
  · intro h r R F hr hrR hF hFc hodd hsupp
    have hal := h r R F hr hrR hF hFc hodd hsupp
    rw [ledgerDeficit_eq_primeSideCharge hF.continuous hodd hr.le hsupp] at hal
    linarith
  · intro h r R F hr hrR hF hFc hodd hsupp
    have hal := h r R F hr hrR hF hFc hodd hsupp
    rw [ledgerDeficit_eq_primeSideCharge hF.continuous hodd hr.le hsupp]
    linarith

/-- The subcritical Euler-tower diagonal sum `Σ_{p ≤ e^{2r}} log p / (p − 1)` at aperture `r`. -/
def combSubcriticalHorizonMass (r : ℝ) : ℝ :=
  ∑ p ∈ combPrimes r, Real.log p / ((p : ℝ) - 1)

theorem combSubcriticalHorizonMass_nonneg (r : ℝ) : 0 ≤ combSubcriticalHorizonMass r := by
  refine Finset.sum_nonneg fun p hp => ?_
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_combPrimes.mp hp).1.two_le
  exact div_nonneg (Real.log_nonneg (by linarith)) (by linarith)

/-- **The prime-power side is bounded by the subcritical diagonal plus the first-power comb charge.**
For every continuous test `F` supported in `[−r, r]` (`r ≥ 0`), eliminating all proper prime powers
via `primeSideCharge_le_sum_primes` expresses the prime-tower upper bound directly in terms of
`combSubcriticalHorizonMass r * autoCorr F 0` and `combCharge F r`. -/
theorem primeSideCharge_le_combSubcritical_add_combCharge {F : ℝ → ℝ} {r : ℝ}
    (hF : Continuous F) (hr : 0 ≤ r) (hsupp : ∀ x, r < |x| → F x = 0) :
    primeSideCharge F ≤ combSubcriticalHorizonMass r * autoCorr F 0 + combCharge F r := by
  classical
  let f : ℕ → ℝ := fun n => Real.log n / ((n : ℝ) - 1) *
    (autoCorr F 0 + Real.sqrt n * autoCorr F (Real.log n))
  let T : Finset {p : ℕ // p.Prime} := (combPrimes r).subtype Nat.Prime
  have hT : ∀ p : {p : ℕ // p.Prime}, Real.log (p : ℕ) ≤ 2 * r → p ∈ T := by
    intro p hp
    rw [Finset.mem_subtype, mem_combPrimes]
    refine ⟨p.2, ?_⟩
    have hp0 : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.pos
    calc ((p : ℕ) : ℝ) = Real.exp (Real.log (p : ℕ)) := (Real.exp_log hp0).symm
      _ ≤ Real.exp (2 * r) := Real.exp_le_exp.mpr hp
  have hbd : primeSideCharge F ≤ ∑ p ∈ T, f (p : ℕ) :=
    primeSideCharge_le_sum_primes (T := T) hF hr hsupp hT
  have hsub : ∑ p ∈ T, f (p : ℕ) = ∑ n ∈ combPrimes r, f n :=
    Finset.sum_subtype_of_mem f fun n hn => (mem_combPrimes.mp hn).1
  have hsplit : ∑ n ∈ combPrimes r, f n =
      combSubcriticalHorizonMass r * autoCorr F 0 + combCharge F r := by
    rw [combSubcriticalHorizonMass, combCharge, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    dsimp only [f]
    rw [combWeight]
    ring
  linarith

/-- **The incidence ledger reduced to the first-power prime-comb charge.** For every odd `F ∈ C²_c`
supported in `[−r, r]` and `0 < r < R`, the full zero form is bounded below by the archimedean/gauge
pool minus `2 * combSubcriticalHorizonMass r * autoCorr F 0` and `2 * combCharge F r`. -/
theorem fullZeroForm_ge_combCharge_ledger {F : ℝ → ℝ} {r R : ℝ} (hF : ContDiff ℝ 2 F)
    (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x) (hr : 0 < r)
    (hsupp : ∀ x, r < |x| → F x = 0) (hrR : r < R) :
    surplusPool (aperturePlateau r R) F + crossingPotentialTerm (aperturePlateau r R) F +
        gaugeRemainder (aperturePlateau r R) F - poleCharge F -
        2 * combSubcriticalHorizonMass r * autoCorr F 0 - 2 * combCharge F r ≤
      fullZeroForm F := by
  have hled := fullZeroForm_eq_neg_ledgerDeficit hF hFc hodd hr hsupp hrR
  have hps := ledgerDeficit_eq_primeSideCharge hF.continuous hodd hr.le hsupp (R := R)
  have hcb := primeSideCharge_le_combSubcritical_add_combCharge hF.continuous hr.le hsupp
  linarith

/-- **Graded allocation of the first-power comb charge certifies a zero-free strip.** If at every
aperture `r > 0`, `2 * combCharge F r + 2 * combSubcriticalHorizonMass r * autoCorr F 0 + poleCharge F`
exceeds the archimedean/gauge pool at plateau `r + 1` by at most `C e^{2σr} ∫ F²`, then
`zetaZeroWidth ≤ σ`. -/
theorem zetaZeroWidth_le_of_combCharge_graded_bound {σ C : ℝ} (hσ : 0 ≤ σ)
    (hbound : ∀ r : ℝ, 0 < r → ∀ F : ℝ → ℝ, ContDiff ℝ 2 F → HasCompactSupport F →
      (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) →
      2 * combCharge F r + 2 * combSubcriticalHorizonMass r * autoCorr F 0 + poleCharge F ≤
        surplusPool (aperturePlateau r (r + 1)) F +
          crossingPotentialTerm (aperturePlateau r (r + 1)) F +
          gaugeRemainder (aperturePlateau r (r + 1)) F +
          C * Real.exp (2 * σ * r) * ∫ x, F x ^ 2) :
    zetaZeroWidth ≤ σ := by
  refine zetaZeroWidth_le_of_graded_odd_fullZeroForm_floor (C := C) hσ ?_
  intro r hr F hF hFc hodd hsupp
  have hled := fullZeroForm_ge_combCharge_ledger hF hFc hodd hr hsupp (lt_add_one r)
  have hb := hbound r hr F hF hFc hodd hsupp
  linarith

/-- **The admissibility unit of the ledger on `GrowthProfile`.** While reading a convex ledger
deficit on any cofinal set of apertures `S_cof` recovers the exact rate `profileRate g`
(`sInf_rateBoundsOn`), any reading `rateBoundsBelow S_bdd` restricted to bounded apertures leaves
the shadow rates unbounded above and certifies no rate bound whatever (`theRateDichotomyIsSharp`). -/
theorem ledgerRateDichotomy (S_cof : CofinalApertures) (S_bdd : BoundedApertures)
    (g : GrowthProfile) :
    sInf (rateBoundsOn S_cof g) = profileRate g ∧
      (¬ BddAbove (profileRate '' shadow (rateBoundsBelow S_bdd) flatProfile)) ∧
      ∀ β : ℝ, ¬ Certifies profileRate (rateBoundsBelow S_bdd) flatProfile β :=
  ⟨sInf_rateBoundsOn S_cof g, theRateDichotomyIsSharp S_bdd⟩

/-! ## §2. Explicit Witness Pairs for Scalar Comb-Energy Information Loss -/

/-- The space of Cauchy–Schwarz comb-pairing data `(mass, energy, charge)` representing the test
mass `‖F‖² > 0`, the raw comb second moment `‖C_r F‖² ≥ 0`, and the signed first-power pairing
`⟪F, C_r F⟫`, subject to the Cauchy–Schwarz inequality `charge ^ 2 ≤ mass * energy`. -/
def CombPairingDatum : Type :=
  { p : ℝ × ℝ × ℝ // 0 < p.1 ∧ 0 ≤ p.2.1 ∧ p.2.2 ^ 2 ≤ p.1 * p.2.1 }

/-- The test mass `A_F(0) = ‖F‖² > 0` of a comb-pairing datum. -/
def combMassVal (d : CombPairingDatum) : ℝ := d.1.1

/-- The raw comb energy `E_w(F) = ‖C_r F‖² ≥ 0` of a comb-pairing datum. -/
def combEnergyVal (d : CombPairingDatum) : ℝ := d.1.2.1

/-- The signed first-power comb charge `⟪F, C_r F⟫ = Σ_p w_p A_F(log p)` of a comb-pairing datum. -/
def combChargeVal (d : CombPairingDatum) : ℝ := d.1.2.2

/-- The complete compensated energy `‖L + C‖² = mass + energy + 2 * charge` in the sense of
`CompensationCoordinates`. -/
def completeCombEnergy (d : CombPairingDatum) : ℝ :=
  combMassVal d + combEnergyVal d + 2 * combChargeVal d

theorem combMassVal_pos (d : CombPairingDatum) : 0 < combMassVal d := d.2.1

theorem combEnergyVal_nonneg (d : CombPairingDatum) : 0 ≤ combEnergyVal d := d.2.2.1

theorem combChargeVal_sq_le (d : CombPairingDatum) :
    combChargeVal d ^ 2 ≤ combMassVal d * combEnergyVal d := d.2.2.2

/-- Every continuous compactly supported test `F` with `autoCorr F 0 > 0` and finite comb `(s, w)`
canonically defines a `CombPairingDatum` by `sq_cost_le_mass_mul_combEnergy`. -/
def mkCombPairingDatum {F : ℝ → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F)
    (h0 : 0 < autoCorr F 0) (s : Finset ℕ) (w : ℕ → ℝ) : CombPairingDatum :=
  ⟨(autoCorr F 0, combEnergy F s w, ∑ p ∈ s, w p * autoCorr F (Real.log p)),
    h0,
    by rw [combEnergy_eq_testPairing ⟨hF, hFc⟩]; exact testPairing_self_nonneg _,
    sq_cost_le_mass_mul_combEnergy hF hFc s w⟩

/-- The Cauchy–Schwarz bound on the signed charge of any `CombPairingDatum`. -/
theorem abs_combChargeVal_le_sqrt (d : CombPairingDatum) :
    |combChargeVal d| ≤ Real.sqrt (combMassVal d * combEnergyVal d) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (combChargeVal_sq_le d)

theorem combChargeVal_le_sqrt (d : CombPairingDatum) :
    combChargeVal d ≤ Real.sqrt (combMassVal d * combEnergyVal d) :=
  (le_abs_self _).trans (abs_combChargeVal_le_sqrt d)

theorem neg_sqrt_le_combChargeVal (d : CombPairingDatum) :
    -Real.sqrt (combMassVal d * combEnergyVal d) ≤ combChargeVal d :=
  neg_le_of_abs_le (abs_combChargeVal_le_sqrt d)

/-- The **unsigned scalar comb-energy reading**: observes only the test mass `‖F‖²` and the raw comb
second moment `‖C_r F‖²`, discarding the signed pairing `⟪F, C_r F⟫`. -/
def scalarCombEnergyReading : CombPairingDatum → ℝ × ℝ :=
  fun d => (combMassVal d, combEnergyVal d)

/-- The **coherent witness** for `d₀`: has the exact same `(mass, energy)` as `d₀` and maximal
positive charge `+√(mass · energy)`. -/
def coherentWitness (d₀ : CombPairingDatum) : CombPairingDatum :=
  ⟨(combMassVal d₀, combEnergyVal d₀, Real.sqrt (combMassVal d₀ * combEnergyVal d₀)),
    combMassVal_pos d₀,
    combEnergyVal_nonneg d₀,
    (Real.sq_sqrt (mul_nonneg (combMassVal_pos d₀).le (combEnergyVal_nonneg d₀))).le⟩

/-- The **orthogonal (translation) witness** for `d₀`: has the exact same `(mass, energy)` as `d₀`
and zero first-power charge `0`. -/
def orthogonalWitness (d₀ : CombPairingDatum) : CombPairingDatum :=
  ⟨(combMassVal d₀, combEnergyVal d₀, 0),
    combMassVal_pos d₀,
    combEnergyVal_nonneg d₀,
    by simp [mul_nonneg (combMassVal_pos d₀).le (combEnergyVal_nonneg d₀)]⟩

/-- The **anti-coherent (compensated) witness** for `d₀`: has the exact same `(mass, energy)` as `d₀`
and maximal negative charge `−√(mass · energy)`. -/
def antiCoherentWitness (d₀ : CombPairingDatum) : CombPairingDatum :=
  ⟨(combMassVal d₀, combEnergyVal d₀, -Real.sqrt (combMassVal d₀ * combEnergyVal d₀)),
    combMassVal_pos d₀,
    combEnergyVal_nonneg d₀,
    by rw [neg_sq]; exact (Real.sq_sqrt (mul_nonneg (combMassVal_pos d₀).le (combEnergyVal_nonneg d₀))).le⟩

theorem coherentWitness_mem_shadow (d₀ : CombPairingDatum) :
    coherentWitness d₀ ∈ shadow scalarCombEnergyReading d₀ := rfl

theorem orthogonalWitness_mem_shadow (d₀ : CombPairingDatum) :
    orthogonalWitness d₀ ∈ shadow scalarCombEnergyReading d₀ := rfl

theorem antiCoherentWitness_mem_shadow (d₀ : CombPairingDatum) :
    antiCoherentWitness d₀ ∈ shadow scalarCombEnergyReading d₀ := rfl

theorem mem_shadow_scalarCombEnergyReading_iff {d d₀ : CombPairingDatum}
    (hd : d ∈ shadow scalarCombEnergyReading d₀) :
    combMassVal d = combMassVal d₀ ∧ combEnergyVal d = combEnergyVal d₀ :=
  Prod.mk.inj hd

/-- **Explicit Witness-Pair Information-Loss Theorem for the Scalar Comb Energy.**
Whenever `0 < combEnergyVal d₀`, the three admissible sources `antiCoherentWitness d₀`,
`orthogonalWitness d₀`, and `coherentWitness d₀` have the **exact same scalar comb-energy reading**
`scalarCombEnergyReading` (`= (combMassVal d₀, combEnergyVal d₀)`) and strictly different target
charges `−√(M E) < 0 < +√(M E)`. Consequently, `scalarCombEnergyReading` cannot resolve any charge
bound `combChargeVal d ≤ β` for `−√(M E) ≤ β < √(M E)`. -/
theorem exists_witness_pair_scalarCombEnergyReading (d₀ : CombPairingDatum)
    (hE : 0 < combEnergyVal d₀) :
    scalarCombEnergyReading (coherentWitness d₀) = scalarCombEnergyReading (orthogonalWitness d₀) ∧
      scalarCombEnergyReading (antiCoherentWitness d₀) =
        scalarCombEnergyReading (orthogonalWitness d₀) ∧
      combChargeVal (antiCoherentWitness d₀) < combChargeVal (orthogonalWitness d₀) ∧
      combChargeVal (orthogonalWitness d₀) < combChargeVal (coherentWitness d₀) ∧
      ∀ β : ℝ, -Real.sqrt (combMassVal d₀ * combEnergyVal d₀) ≤ β →
        β < Real.sqrt (combMassVal d₀ * combEnergyVal d₀) →
        ¬ Resolves scalarCombEnergyReading (fun d => combChargeVal d ≤ β) := by
  have hpos : 0 < Real.sqrt (combMassVal d₀ * combEnergyVal d₀) :=
    Real.sqrt_pos.mpr (mul_pos (combMassVal_pos d₀) hE)
  refine ⟨rfl, rfl, ?_, ?_, fun β hβ0 hβ => ?_⟩
  · show -Real.sqrt (combMassVal d₀ * combEnergyVal d₀) < 0
    linarith
  · show 0 < Real.sqrt (combMassVal d₀ * combEnergyVal d₀)
    exact hpos
  · refine not_resolves_of_pair (d := antiCoherentWitness d₀) (e := coherentWitness d₀) rfl hβ0 ?_
    show ¬ Real.sqrt (combMassVal d₀ * combEnergyVal d₀) ≤ β
    linarith

/-- **Exact resolution limit of `combChargeVal` under `scalarCombEnergyReading`.** -/
theorem resolutionLimit_combChargeVal_scalarCombEnergyReading (d₀ : CombPairingDatum) :
    resolutionLimit combChargeVal scalarCombEnergyReading d₀ =
      Real.sqrt (combMassVal d₀ * combEnergyVal d₀) := by
  rw [resolutionLimit]
  refine le_antisymm
    (csSup_le (shadow_image_nonempty combChargeVal scalarCombEnergyReading d₀) ?_) ?_
  · rintro _ ⟨d, hd, rfl⟩
    obtain ⟨h1, h2⟩ := mem_shadow_scalarCombEnergyReading_iff hd
    rw [← h1, ← h2]
    exact combChargeVal_le_sqrt d
  · have hbdd : BddAbove (combChargeVal '' shadow scalarCombEnergyReading d₀) := by
      refine ⟨Real.sqrt (combMassVal d₀ * combEnergyVal d₀), ?_⟩
      rintro _ ⟨d, hd, rfl⟩
      obtain ⟨h1, h2⟩ := mem_shadow_scalarCombEnergyReading_iff hd
      rw [← h1, ← h2]
      exact combChargeVal_le_sqrt d
    exact le_csSup hbdd ⟨coherentWitness d₀, coherentWitness_mem_shadow d₀, rfl⟩

/-- **Exact resolution floor of `combChargeVal` under `scalarCombEnergyReading`.** -/
theorem resolutionFloor_combChargeVal_scalarCombEnergyReading (d₀ : CombPairingDatum) :
    resolutionFloor combChargeVal scalarCombEnergyReading d₀ =
      -Real.sqrt (combMassVal d₀ * combEnergyVal d₀) := by
  rw [resolutionFloor]
  refine le_antisymm ?_
    (le_csInf (shadow_image_nonempty combChargeVal scalarCombEnergyReading d₀) ?_)
  · have hbdd : BddBelow (combChargeVal '' shadow scalarCombEnergyReading d₀) := by
      refine ⟨-Real.sqrt (combMassVal d₀ * combEnergyVal d₀), ?_⟩
      rintro _ ⟨d, hd, rfl⟩
      obtain ⟨h1, h2⟩ := mem_shadow_scalarCombEnergyReading_iff hd
      rw [← h1, ← h2]
      exact neg_sqrt_le_combChargeVal d
    exact csInf_le hbdd ⟨antiCoherentWitness d₀, antiCoherentWitness_mem_shadow d₀, rfl⟩
  · rintro _ ⟨d, hd, rfl⟩
    obtain ⟨h1, h2⟩ := mem_shadow_scalarCombEnergyReading_iff hd
    rw [← h1, ← h2]
    exact neg_sqrt_le_combChargeVal d

/-- **Exact resolution interval of `combChargeVal` under `scalarCombEnergyReading`.** -/
theorem resolutionInterval_combChargeVal_scalarCombEnergyReading (d₀ : CombPairingDatum) :
    resolutionInterval combChargeVal scalarCombEnergyReading d₀ =
      Icc (-Real.sqrt (combMassVal d₀ * combEnergyVal d₀))
        (Real.sqrt (combMassVal d₀ * combEnergyVal d₀)) := by
  rw [resolutionInterval, resolutionFloor_combChargeVal_scalarCombEnergyReading,
    resolutionLimit_combChargeVal_scalarCombEnergyReading]

/-- Lower and upper bounds on `completeCombEnergy` in terms of `√mass ± √energy`. -/
theorem completeCombEnergy_bounds (d : CombPairingDatum) :
    (Real.sqrt (combMassVal d) - Real.sqrt (combEnergyVal d)) ^ 2 ≤ completeCombEnergy d ∧
      completeCombEnergy d ≤ (Real.sqrt (combMassVal d) + Real.sqrt (combEnergyVal d)) ^ 2 := by
  have hM : 0 ≤ combMassVal d := (combMassVal_pos d).le
  have hE : 0 ≤ combEnergyVal d := combEnergyVal_nonneg d
  have hsqM : Real.sqrt (combMassVal d) ^ 2 = combMassVal d := Real.sq_sqrt hM
  have hsqE : Real.sqrt (combEnergyVal d) ^ 2 = combEnergyVal d := Real.sq_sqrt hE
  have hmul : Real.sqrt (combMassVal d) * Real.sqrt (combEnergyVal d) =
      Real.sqrt (combMassVal d * combEnergyVal d) := (Real.sqrt_mul hM _).symm
  have hlow : (Real.sqrt (combMassVal d) - Real.sqrt (combEnergyVal d)) ^ 2 =
      combMassVal d + combEnergyVal d - 2 * Real.sqrt (combMassVal d * combEnergyVal d) := by
    calc (Real.sqrt (combMassVal d) - Real.sqrt (combEnergyVal d)) ^ 2
        = Real.sqrt (combMassVal d) ^ 2 + Real.sqrt (combEnergyVal d) ^ 2 -
            2 * (Real.sqrt (combMassVal d) * Real.sqrt (combEnergyVal d)) := by ring
      _ = combMassVal d + combEnergyVal d - 2 * Real.sqrt (combMassVal d * combEnergyVal d) := by
          rw [hsqM, hsqE, hmul]
  have hhigh : (Real.sqrt (combMassVal d) + Real.sqrt (combEnergyVal d)) ^ 2 =
      combMassVal d + combEnergyVal d + 2 * Real.sqrt (combMassVal d * combEnergyVal d) := by
    calc (Real.sqrt (combMassVal d) + Real.sqrt (combEnergyVal d)) ^ 2
        = Real.sqrt (combMassVal d) ^ 2 + Real.sqrt (combEnergyVal d) ^ 2 +
            2 * (Real.sqrt (combMassVal d) * Real.sqrt (combEnergyVal d)) := by ring
      _ = combMassVal d + combEnergyVal d + 2 * Real.sqrt (combMassVal d * combEnergyVal d) := by
          rw [hsqM, hsqE, hmul]
  rw [hlow, hhigh, completeCombEnergy]
  exact ⟨by linarith [neg_sqrt_le_combChargeVal d], by linarith [combChargeVal_le_sqrt d]⟩

/-- **Exact resolution limit of `completeCombEnergy` under `scalarCombEnergyReading`.** -/
theorem resolutionLimit_completeCombEnergy_scalarCombEnergyReading (d₀ : CombPairingDatum) :
    resolutionLimit completeCombEnergy scalarCombEnergyReading d₀ =
      (Real.sqrt (combMassVal d₀) + Real.sqrt (combEnergyVal d₀)) ^ 2 := by
  have hM : 0 ≤ combMassVal d₀ := (combMassVal_pos d₀).le
  have hE : 0 ≤ combEnergyVal d₀ := combEnergyVal_nonneg d₀
  have hcoh : completeCombEnergy (coherentWitness d₀) =
      (Real.sqrt (combMassVal d₀) + Real.sqrt (combEnergyVal d₀)) ^ 2 := by
    calc completeCombEnergy (coherentWitness d₀)
        = combMassVal d₀ + combEnergyVal d₀ + 2 * Real.sqrt (combMassVal d₀ * combEnergyVal d₀) := rfl
      _ = Real.sqrt (combMassVal d₀) ^ 2 + Real.sqrt (combEnergyVal d₀) ^ 2 +
            2 * (Real.sqrt (combMassVal d₀) * Real.sqrt (combEnergyVal d₀)) := by
          rw [Real.sq_sqrt hM, Real.sq_sqrt hE, ← Real.sqrt_mul hM]
      _ = (Real.sqrt (combMassVal d₀) + Real.sqrt (combEnergyVal d₀)) ^ 2 := by ring
  rw [resolutionLimit]
  refine le_antisymm
    (csSup_le (shadow_image_nonempty completeCombEnergy scalarCombEnergyReading d₀) ?_) ?_
  · rintro _ ⟨d, hd, rfl⟩
    obtain ⟨h1, h2⟩ := mem_shadow_scalarCombEnergyReading_iff hd
    rw [← h1, ← h2]
    exact (completeCombEnergy_bounds d).2
  · have hbdd : BddAbove (completeCombEnergy '' shadow scalarCombEnergyReading d₀) := by
      refine ⟨(Real.sqrt (combMassVal d₀) + Real.sqrt (combEnergyVal d₀)) ^ 2, ?_⟩
      rintro _ ⟨d, hd, rfl⟩
      obtain ⟨h1, h2⟩ := mem_shadow_scalarCombEnergyReading_iff hd
      rw [← h1, ← h2]
      exact (completeCombEnergy_bounds d).2
    rw [← hcoh]
    exact le_csSup hbdd ⟨coherentWitness d₀, coherentWitness_mem_shadow d₀, rfl⟩

/-- **Exact resolution floor of `completeCombEnergy` under `scalarCombEnergyReading`.** -/
theorem resolutionFloor_completeCombEnergy_scalarCombEnergyReading (d₀ : CombPairingDatum) :
    resolutionFloor completeCombEnergy scalarCombEnergyReading d₀ =
      (Real.sqrt (combMassVal d₀) - Real.sqrt (combEnergyVal d₀)) ^ 2 := by
  have hM : 0 ≤ combMassVal d₀ := (combMassVal_pos d₀).le
  have hE : 0 ≤ combEnergyVal d₀ := combEnergyVal_nonneg d₀
  have hanti : completeCombEnergy (antiCoherentWitness d₀) =
      (Real.sqrt (combMassVal d₀) - Real.sqrt (combEnergyVal d₀)) ^ 2 := by
    calc completeCombEnergy (antiCoherentWitness d₀)
        = combMassVal d₀ + combEnergyVal d₀ +
            2 * (-Real.sqrt (combMassVal d₀ * combEnergyVal d₀)) := rfl
      _ = Real.sqrt (combMassVal d₀) ^ 2 + Real.sqrt (combEnergyVal d₀) ^ 2 -
            2 * (Real.sqrt (combMassVal d₀) * Real.sqrt (combEnergyVal d₀)) := by
          rw [Real.sq_sqrt hM, Real.sq_sqrt hE, ← Real.sqrt_mul hM]; ring
      _ = (Real.sqrt (combMassVal d₀) - Real.sqrt (combEnergyVal d₀)) ^ 2 := by ring
  rw [resolutionFloor]
  refine le_antisymm ?_
    (le_csInf (shadow_image_nonempty completeCombEnergy scalarCombEnergyReading d₀) ?_)
  · have hbdd : BddBelow (completeCombEnergy '' shadow scalarCombEnergyReading d₀) := by
      refine ⟨(Real.sqrt (combMassVal d₀) - Real.sqrt (combEnergyVal d₀)) ^ 2, ?_⟩
      rintro _ ⟨d, hd, rfl⟩
      obtain ⟨h1, h2⟩ := mem_shadow_scalarCombEnergyReading_iff hd
      rw [← h1, ← h2]
      exact (completeCombEnergy_bounds d).1
    rw [← hanti]
    exact csInf_le hbdd ⟨antiCoherentWitness d₀, antiCoherentWitness_mem_shadow d₀, rfl⟩
  · rintro _ ⟨d, hd, rfl⟩
    obtain ⟨h1, h2⟩ := mem_shadow_scalarCombEnergyReading_iff hd
    rw [← h1, ← h2]
    exact (completeCombEnergy_bounds d).1

/-- **Exact resolution interval of `completeCombEnergy` under `scalarCombEnergyReading`.** -/
theorem resolutionInterval_completeCombEnergy_scalarCombEnergyReading (d₀ : CombPairingDatum) :
    resolutionInterval completeCombEnergy scalarCombEnergyReading d₀ =
      Icc ((Real.sqrt (combMassVal d₀) - Real.sqrt (combEnergyVal d₀)) ^ 2)
        ((Real.sqrt (combMassVal d₀) + Real.sqrt (combEnergyVal d₀)) ^ 2) := by
  rw [resolutionInterval, resolutionFloor_completeCombEnergy_scalarCombEnergyReading,
    resolutionLimit_completeCombEnergy_scalarCombEnergyReading]

/-- On the balanced locus `combMassVal d₀ = combEnergyVal d₀` (`‖L‖² = ‖C‖²`), the resolution
interval of `completeCombEnergy` under `scalarCombEnergyReading` is `[0, 4 * combMassVal d₀]`. -/
theorem resolutionInterval_completeCombEnergy_of_balanced (d₀ : CombPairingDatum)
    (hbal : combEnergyVal d₀ = combMassVal d₀) :
    resolutionFloor completeCombEnergy scalarCombEnergyReading d₀ = 0 ∧
      resolutionLimit completeCombEnergy scalarCombEnergyReading d₀ = 4 * combMassVal d₀ := by
  rw [resolutionFloor_completeCombEnergy_scalarCombEnergyReading,
    resolutionLimit_completeCombEnergy_scalarCombEnergyReading, hbal]
  have hM : 0 ≤ combMassVal d₀ := (combMassVal_pos d₀).le
  refine ⟨by ring, ?_⟩
  calc (Real.sqrt (combMassVal d₀) + Real.sqrt (combMassVal d₀)) ^ 2
      = 4 * Real.sqrt (combMassVal d₀) ^ 2 := by ring
    _ = 4 * combMassVal d₀ := by rw [Real.sq_sqrt hM]

/-- **Explicit Smooth Odd Profile Witness Family on `ℝ`.**
For any dilation parameter `c > 0`, `dilatedUnitOddBump c := rescaledTest unitOddBump c` is a
smooth, odd, compactly supported profile on `ℝ`. -/
def dilatedUnitOddBump (c : ℝ) : ℝ → ℝ := rescaledTest unitOddBump c

/-- **Every `dilatedUnitOddBump c` (`c > 0`) has the exact same scalar comb-energy reading as
`unitOddBump` while having asymptotic first-power charge ratio `autoCorr unitOddBump (2 / c)`.**
Specifically, for every `c > 0`, `g = dilatedUnitOddBump c` satisfies:
1. `g` is `C^∞`, odd, and compactly supported;
2. `autoCorr g 0 = 1 = autoCorr unitOddBump 0`;
3. `combEnergy (rescaledTest g r) (combPrimes r) combWeight / combMass r ^ 2 → 1`;
4. `combEnergy (rescaledTest g r) (combPrimes r) combWeight / e^{2r} → 4`;
5. `combCross (rescaledTest g r) r / e^{2r} → 4`;
6. `combCharge (rescaledTest g r) r / combMass r → autoCorr unitOddBump (2 / c)`. -/
theorem dilatedUnitOddBump_same_scalar_comb_reading {c : ℝ} (hc : 0 < c) :
    (∀ n : ℕ, ContDiff ℝ n (dilatedUnitOddBump c)) ∧
      HasCompactSupport (dilatedUnitOddBump c) ∧
      (∀ x, dilatedUnitOddBump c (-x) = -dilatedUnitOddBump c x) ∧
      autoCorr (dilatedUnitOddBump c) 0 = 1 ∧
      Tendsto (fun r => combEnergy (rescaledTest (dilatedUnitOddBump c) r) (combPrimes r) combWeight /
        combMass r ^ 2) atTop (𝓝 1) ∧
      Tendsto (fun r => combEnergy (rescaledTest (dilatedUnitOddBump c) r) (combPrimes r) combWeight /
        Real.exp (2 * r)) atTop (𝓝 4) ∧
      Tendsto (fun r => combCross (rescaledTest (dilatedUnitOddBump c) r) r /
        Real.exp (2 * r)) atTop (𝓝 4) ∧
      Tendsto (fun r => combCharge (rescaledTest (dilatedUnitOddBump c) r) r /
        combMass r) atTop (𝓝 (autoCorr unitOddBump (2 / c))) := by
  have hsmooth : ∀ n : ℕ, ContDiff ℝ n (dilatedUnitOddBump c) := fun n =>
    contDiff_const.mul (contDiff_const.mul ((contDiff_oddBump n).comp (contDiff_id.div_const c)))
  have hcont : Continuous (dilatedUnitOddBump c) := (hsmooth 0).continuous
  have hcs : HasCompactSupport (dilatedUnitOddBump c) :=
    hasCompactSupport_rescaledTest hc hasCompactSupport_unitOddBump
  have hodd : ∀ x, dilatedUnitOddBump c (-x) = -dilatedUnitOddBump c x := fun x => by
    simp only [dilatedUnitOddBump, rescaledTest, unitOddBump, neg_div, oddBump_neg]; ring
  have h0 : autoCorr (dilatedUnitOddBump c) 0 = 1 := by
    rw [dilatedUnitOddBump, autoCorr_rescaledTest hc, zero_div, autoCorr_unitOddBump_zero]
  have h2 : autoCorr (dilatedUnitOddBump c) 2 = autoCorr unitOddBump (2 / c) :=
    autoCorr_rescaledTest hc 2
  have h4 : 4 * autoCorr (dilatedUnitOddBump c) 0 = 4 := by rw [h0, mul_one]
  refine ⟨hsmooth, hcs, hodd, h0, ?_, ?_, ?_, ?_⟩
  · simpa [h0] using tendsto_combEnergy_rescaledTest_div_combMass_sq hcont hcs
  · simpa [h4] using tendsto_combEnergy_rescaledTest_div_exp hcont hcs
  · simpa [h4] using tendsto_combCross_rescaledTest_div_exp hcont hcs
  · simpa [h2] using tendsto_combCharge_rescaledTest_div_combMass hcont hcs

/-- **Continuum of Smooth Odd Profile Witnesses Sharing the Exact Scalar Comb-Energy Reading.**
For every target asymptotic first-power charge ratio `θ ∈ [0, 1)`, there exists a dilation scale
`c ≥ 1` such that `dilatedUnitOddBump c` has the **exact same** unit mass `1`, asymptotic normalized
comb energy `1`, asymptotic exponential comb energy `4`, and cross-prime energy `4` as
`unitOddBump` (whose asymptotic charge ratio is `0`), while achieving asymptotic first-power charge
ratio `lim_{r → ∞} combCharge (rescaledTest (dilatedUnitOddBump c) r) r / combMass r = θ`. -/
theorem exists_dilatedUnitOddBump_witness_for_every_charge_ratio {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    ∃ c : ℝ, 1 ≤ c ∧
      autoCorr (dilatedUnitOddBump c) 0 = autoCorr unitOddBump 0 ∧
      Tendsto (fun r => combEnergy (rescaledTest (dilatedUnitOddBump c) r) (combPrimes r) combWeight /
        combMass r ^ 2) atTop (𝓝 1) ∧
      Tendsto (fun r => combEnergy (rescaledTest (dilatedUnitOddBump c) r) (combPrimes r) combWeight /
        Real.exp (2 * r)) atTop (𝓝 4) ∧
      Tendsto (fun r => combCharge (rescaledTest (dilatedUnitOddBump c) r) r /
        combMass r) atTop (𝓝 θ) := by
  have hcontA : Continuous (autoCorr unitOddBump) :=
    continuous_autoCorr continuous_unitOddBump hasCompactSupport_unitOddBump
  have hA0 : autoCorr unitOddBump 0 = 1 := autoCorr_unitOddBump_zero
  have hsupp : ∀ x, 1 < |x| → unitOddBump x = 0 := fun x hx => by
    simp [unitOddBump, oddBump_eq_zero hx]
  have hA2 : autoCorr unitOddBump 2 = 0 :=
    autoCorr_eq_zero_of_support_le hsupp (by norm_num : (2 : ℝ) * 1 ≤ |(2 : ℝ)|)
  have hmem : θ ∈ Icc (autoCorr unitOddBump 2) (autoCorr unitOddBump 0) := by
    rw [hA2, hA0]; exact ⟨hθ0, hθ1.le⟩
  obtain ⟨t, htIcc, ht_eq⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 2)
    hcontA.continuousOn hmem
  have ht_pos : 0 < t := by
    rcases htIcc.1.eq_or_lt with rfl | hlt
    · rw [hA0] at ht_eq; linarith
    · exact hlt
  set c := 2 / t with hcdef
  have hc1 : 1 ≤ c := by
    rw [hcdef, le_div_iff₀ ht_pos]; linarith [htIcc.2]
  have hc0 : 0 < c := by linarith
  have htc : 2 / c = t := by
    rw [hcdef, div_div_cancel₀ (by norm_num)]
  obtain ⟨_, _, _, h0, hE1, hE4, _, hQ⟩ := dilatedUnitOddBump_same_scalar_comb_reading hc0
  refine ⟨c, hc1, h0.trans hA0.symm, hE1, hE4, ?_⟩
  rwa [htc, ht_eq] at hQ

/-! ## §3. Faithful Completions by Signed Pairing and Coherent Residual -/

/-- The signed compensation amplitude reading `α = −charge / mass` (`gramAmplitude`) on
`CombPairingDatum`. -/
def amplitudeReading : CombPairingDatum → ℝ :=
  fun d => gramAmplitude (combMassVal d) (combChargeVal d)

/-- The **completed comb reading**: adjoins the signed amplitude ratio `amplitudeReading` to the
unsigned scalar comb-energy reading `scalarCombEnergyReading`. -/
def completedCombReading : CombPairingDatum → (ℝ × ℝ) × ℝ :=
  joinReading scalarCombEnergyReading amplitudeReading

/-- The signed charge is recovered algebraically from `combMassVal` and `amplitudeReading`:
`combChargeVal d = −amplitudeReading d * combMassVal d`. -/
theorem combChargeVal_eq_neg_amplitude_mul_mass (d : CombPairingDatum) :
    combChargeVal d = -amplitudeReading d * combMassVal d := by
  have hM : combMassVal d ≠ 0 := (combMassVal_pos d).ne'
  rw [amplitudeReading, gramAmplitude]
  field_simp

/-- **Pythagorean decomposition of `completeCombEnergy` on `CombPairingDatum`.**
`completeCombEnergy d = (1 − α)² · mass + gramTransverse mass energy charge`, with nonnegative
transverse energy. -/
theorem completeCombEnergy_eq_pythagorean (d : CombPairingDatum) :
    completeCombEnergy d =
        (1 - amplitudeReading d) ^ 2 * combMassVal d +
          gramTransverse (combMassVal d) (combEnergyVal d) (combChargeVal d) ∧
      0 ≤ gramTransverse (combMassVal d) (combEnergyVal d) (combChargeVal d) := by
  refine ⟨?_, gramTransverse_nonneg (combMassVal_pos d) (combChargeVal_sq_le d)⟩
  rw [completeCombEnergy, amplitudeReading]
  exact gram_add_eq_compensation (combMassVal_pos d).ne' (combEnergyVal d) (combChargeVal d)

/-- Whenever an invariant `I` is constant on the shadow of `r`, `r` is faithful for `I` and its
resolution floor also equals `I`. -/
theorem faithful_and_floor_eq_of_eq_on_shadow {D O : Type*} {I : D → ℝ} {r : D → O}
    (heq : ∀ d e : D, e ∈ shadow r d → I e = I d) :
    Faithful I r ∧ ∀ d : D, resolutionFloor I r d = I d := by
  have himg : ∀ d : D, I '' shadow r d = {I d} := fun d => by
    ext x
    simp only [mem_image, mem_singleton_iff]
    exact ⟨by rintro ⟨e, he, rfl⟩; exact heq d e he, fun hx => ⟨d, rfl, hx.symm⟩⟩
  refine ⟨fun d => by rw [resolutionLimit, himg d, csSup_singleton],
    fun d => by rw [resolutionFloor, himg d, csInf_singleton]⟩

/-- Equal `completedCombReading` values force equal signed charges `combChargeVal`. -/
theorem combChargeVal_eq_of_completedCombReading_eq {d₁ d₂ : CombPairingDatum}
    (h : completedCombReading d₁ = completedCombReading d₂) :
    combChargeVal d₁ = combChargeVal d₂ := by
  have hM : combMassVal d₁ = combMassVal d₂ := congrArg (Prod.fst ∘ Prod.fst) h
  have hA : amplitudeReading d₁ = amplitudeReading d₂ := congrArg Prod.snd h
  rw [combChargeVal_eq_neg_amplitude_mul_mass d₁, combChargeVal_eq_neg_amplitude_mul_mass d₂,
    hM, hA]

/-- Equal `completedCombReading` values force equal complete compensated energies
`completeCombEnergy`. -/
theorem completeCombEnergy_eq_of_completedCombReading_eq {d₁ d₂ : CombPairingDatum}
    (h : completedCombReading d₁ = completedCombReading d₂) :
    completeCombEnergy d₁ = completeCombEnergy d₂ := by
  have hM : combMassVal d₁ = combMassVal d₂ := congrArg (Prod.fst ∘ Prod.fst) h
  have hE : combEnergyVal d₁ = combEnergyVal d₂ := congrArg (Prod.snd ∘ Prod.fst) h
  have hQ : combChargeVal d₁ = combChargeVal d₂ :=
    combChargeVal_eq_of_completedCombReading_eq h
  simp only [completeCombEnergy, hM, hE, hQ]

/-- **Adjoining the signed amplitude ratio makes the comb reading faithful for `combChargeVal`.** -/
theorem faithful_combChargeVal_completedCombReading :
    Faithful combChargeVal completedCombReading :=
  (faithful_and_floor_eq_of_eq_on_shadow fun _ _ he =>
    combChargeVal_eq_of_completedCombReading_eq he).1

/-- **Adjoining the signed amplitude ratio makes the comb reading faithful for
`completeCombEnergy`.** -/
theorem faithful_completeCombEnergy_completedCombReading :
    Faithful completeCombEnergy completedCombReading :=
  (faithful_and_floor_eq_of_eq_on_shadow fun _ _ he =>
    completeCombEnergy_eq_of_completedCombReading_eq he).1

/-- Consequently, `completedCombReading` collapses the resolution interval of both `combChargeVal`
and `completeCombEnergy` to singletons. -/
theorem resolutionLimit_and_floor_completedCombReading (d₀ : CombPairingDatum) :
    resolutionLimit combChargeVal completedCombReading d₀ = combChargeVal d₀ ∧
      resolutionFloor combChargeVal completedCombReading d₀ = combChargeVal d₀ ∧
      resolutionLimit completeCombEnergy completedCombReading d₀ = completeCombEnergy d₀ ∧
      resolutionFloor completeCombEnergy completedCombReading d₀ = completeCombEnergy d₀ :=
  ⟨faithful_combChargeVal_completedCombReading d₀,
    (faithful_and_floor_eq_of_eq_on_shadow fun _ _ he =>
      combChargeVal_eq_of_completedCombReading_eq he).2 d₀,
    faithful_completeCombEnergy_completedCombReading d₀,
    (faithful_and_floor_eq_of_eq_on_shadow fun _ _ he =>
      completeCombEnergy_eq_of_completedCombReading_eq he).2 d₀⟩

/-- **Coherent-Residual Cauchy–Schwarz Bound for the First-Power Comb Charge.**
For any continuous compactly supported test `F`, any continuous compactly supported reference
profile `T`, and any aperture `r`, subtracting `T` from the prime comb
`primeComb F (combPrimes r) combWeight` splits the first-power charge into the signed reference
pairing `testPairing F T` plus a remainder controlled by the coherent residual energy `‖C_r F − T‖²`:
`(combCharge F r − ⟪F, T⟫)² ≤ A_F(0) · ‖C_r F − T‖²`. -/
theorem sq_combCharge_sub_translatePairing_le {F T : ℝ → ℝ} (hF : Continuous F)
    (hFc : HasCompactSupport F) (hT : Continuous T) (hTc : HasCompactSupport T) (r : ℝ) :
    (combCharge F r - testPairing F T) ^ 2 ≤
      autoCorr F 0 *
        testPairing (fun x => primeComb F (combPrimes r) combWeight x - T x)
          (fun x => primeComb F (combPrimes r) combWeight x - T x) := by
  have hFn : ContCompact F := ⟨hF, hFc⟩
  have hTn : ContCompact T := ⟨hT, hTc⟩
  have hCn : ContCompact (primeComb F (combPrimes r) combWeight) := by
    rw [primeComb]; exact contCompact_finsetComb hFn (combPrimes r) combWeight (fun p => Real.log p)
  have hRn : ContCompact (fun x => primeComb F (combPrimes r) combWeight x - T x) :=
    hCn.sub_nice hTn
  have hcs := testPairing_cauchy_schwarz hFn hRn
  rw [testPairing_sub_right hFn hCn hTn, testPairing_primeComb hFn,
    testPairing_self_eq_autoCorr_zero] at hcs
  exact hcs

/-- **Horizon-Translate Coherent-Residual Bound.**
Taking the reference profile `T_r(x) = combMass r * F (x + 2 * r)` (the horizon translate of `F`
scaled by the comb mass `S_r`), the first-power charge satisfies
`(combCharge F r − S_r · A_F(2r))² ≤ A_F(0) · ‖C_r F − S_r F(· + 2r)‖²`. -/
theorem sq_combCharge_sub_horizonTranslate_le {F : ℝ → ℝ} (hF : Continuous F)
    (hFc : HasCompactSupport F) (r : ℝ) :
    (combCharge F r - combMass r * autoCorr F (2 * r)) ^ 2 ≤
      autoCorr F 0 *
        testPairing (fun x => primeComb F (combPrimes r) combWeight x - combMass r * F (x + 2 * r))
          (fun x => primeComb F (combPrimes r) combWeight x - combMass r * F (x + 2 * r)) := by
  have hFn : ContCompact F := ⟨hF, hFc⟩
  have hTn : ContCompact (fun x => combMass r * F (x + 2 * r)) :=
    ContCompact.const_mul_nice (combMass r) (hFn.translate (2 * r))
  have hpair : testPairing F (fun x => combMass r * F (x + 2 * r)) =
      combMass r * autoCorr F (2 * r) := by
    rw [testPairing_const_mul_right, ← autoCorr_eq_testPairing]
  rw [← hpair]
  exact sq_combCharge_sub_translatePairing_le hF hFc hTn.1 hTn.2 r

/-- **Pure Translation-Residual Bound on `[−r, r]`-Supported Tests.**
When `F` is supported in `[−r, r]` (`0 ≤ r`), the horizon autocorrelation `A_F(2r)` vanishes by
`autoCorr_eq_zero_of_support_le`, so the signed pairing with the coherent translate is identically
zero and the first-power comb charge is bounded purely by the **coherent translation-residual
energy** `‖C_r F − S_r F(· + 2r)‖²`:
`combCharge F r ^ 2 ≤ A_F(0) · ‖C_r F − S_r F(· + 2r)‖²`. -/
theorem sq_combCharge_le_mass_mul_horizonResidualEnergy {F : ℝ → ℝ} {r : ℝ}
    (hF : Continuous F) (hFc : HasCompactSupport F) (hr : 0 ≤ r)
    (hsupp : ∀ x, r < |x| → F x = 0) :
    combCharge F r ^ 2 ≤
      autoCorr F 0 *
        testPairing (fun x => primeComb F (combPrimes r) combWeight x - combMass r * F (x + 2 * r))
          (fun x => primeComb F (combPrimes r) combWeight x - combMass r * F (x + 2 * r)) := by
  have hA2 : autoCorr F (2 * r) = 0 := by
    refine autoCorr_eq_zero_of_support_le hsupp ?_
    rw [abs_of_nonneg (by linarith)]
  have h := sq_combCharge_sub_horizonTranslate_le hF hFc r
  rwa [hA2, mul_zero, sub_zero] at h

/-- **Joint Summary of Coherent Residuals on the Incidence Ledger.**
1. On the slowly varying family `F_r = rescaledTest f r` (`f` continuous and supported in `[−1, 1]`),
   the normalized coherent translation-residual energy
   `testPairing (normalizedComb f r − f(· + 2)) (normalizedComb f r − f(· + 2))` tends to `0`,
   forcing `combCharge (rescaledTest f r) r / combMass r → 0` despite `combEnergy / S_r² → A_f(0)`;
2. Before squaring, pairing the prime shift `Σ Λ(n) 2n^{−1/2} F(x + log n)` against its polar
   counterpart `∫ 4 cosh(s/2) F(x + s) ds` yields the compensated residual bounded unconditionally
   by `K e^{S/2} exp(−c√S) (2‖F'‖₁ + ‖F‖₁)` with the de la Vallée Poussin saving `exp(−c√S)`. -/
theorem coherent_residual_and_polar_compensation_summary :
    (∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f → (∀ x, 1 < |x| → f x = 0) →
      Tendsto (fun r => testPairing (fun x => normalizedComb f r x - f (x + 2))
        (fun x => normalizedComb f r x - f (x + 2))) atTop (𝓝 0) ∧
      Tendsto (fun r => combCharge (rescaledTest f r) r / combMass r) atTop (𝓝 0)) ∧
    (∃ c > 0, ∃ K : ℝ, 0 ≤ K ∧ ∃ S₀ : ℝ, 0 < S₀ ∧ ∀ F : ℝ → ℝ, ContDiff ℝ 1 F →
      ∀ r : ℝ, 0 < r → (∀ y, r < |y| → F y = 0) → ∀ x : ℝ, S₀ ≤ 2 * r + |x| → ∀ N : ℕ,
      Real.exp (2 * r + |x|) ≤ N →
      |(∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.vonMangoldt n : ℝ) *
            (2 * (Real.sqrt n)⁻¹ * F (x + Real.log n))) -
          ∫ s in Ioi (0 : ℝ), 4 * Real.cosh (s / 2) * F (x + s)| ≤
        K * Real.exp ((2 * r + |x|) / 2) * Real.exp (-c * Real.sqrt (2 * r + |x|)) *
          (2 * (∫ y, |deriv F y|) + ∫ y, |F y|)) :=
  ⟨fun _ hf hfc hsupp => ⟨tendsto_testPairing_normalizedComb_sub_translate hf hfc,
    tendsto_combCharge_rescaledTest_div_combMass_zero hf hfc hsupp⟩,
   exists_abs_primeShift_sub_polar_le⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality

end
