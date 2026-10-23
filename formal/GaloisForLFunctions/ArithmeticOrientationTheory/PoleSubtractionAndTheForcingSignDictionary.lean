import GaloisForLFunctions.ArithmeticOrientationTheory.OrientedReadings
import GaloisForLFunctions.ArithmeticOrientationTheory.TheWidthDictionary
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.WhichArithmeticDataForceTheSign
import GaloisForLFunctions.BiScaleUncertainty.PrimeWindowCeilingRHCriterion

/-!
# Pole subtraction and the forcing sign dictionary

Why do span identities, Witt integrality, the functional equation, and positive Euler/Beurling
orbit counts fail to force the sign of the Weil form (`goldenDatum`), and which arithmetic data
force it across the corpus?

In the language of `OrientedReadings` and `TheResolutionLimitOfAReading`, the unsubtracted
arithmetic reading of a curve datum — recording `(q, g)`, trace integrality, and raw point-count
nonnegativity `∀ k ≥ 1, 0 ≤ N_k` — is **blind** to the collapse from a unitary curve datum to
`goldenDatum`: the polar `H⁰ ⊕ H²` contribution `q^k + 1` dominates the primitive `H¹` trace as
soon as every Frobenius eigenvalue lies in the critical strip `|β_i| ≤ √q`
(`CurveDatum.pointCount_nonneg_iff_trace_le_pole`). By the collapse–resolution dichotomy, this
unsubtracted reading cannot resolve `CurveDatum.Unitary` (`not_resolves_unsubtractedReading_unitary`).

By contrast, the lag-1 Frobenius reflection defect reading `D ↦ D.frobReflectionDefect {1} 1 =
(1/2) Σ_i (‖β_i‖ − ‖β_i‖⁻¹)²` and the pole-subtracted Hasse–Weil reading resolve `CurveDatum.Unitary`
on every `CurveDatum ι` (`resolves_frobReflectionDefect_unitary`,
`orientationFaithful_frobReflectionDefect_of_flips`), separating every unitary datum (`= 0`) from
`goldenDatum` (`= 1`) and `hidingDatum N` (`= 9/4`).

Over `ℤ`, the same pole subtraction happens in two places:
1. **In the odd reflection sector of `scalingSurface`**: the `e^r` main terms of the prime comb and
   the pole charge `2 A(F)²` cancel identically, leaving the two-pole Chebyshev remainder
   `E(s) = e^s + s − 1 − ψ(e^s)` on `(0, 2r]`. This links the geometric and spectral units of
   `TheWidthDictionary` to the forward light-cone Bézout unit, the coupled odd-cone Bézout unit, the
   all-aperture two-pole Chebyshev defect unit, and the subexponential Castelnuovo–Severi odd-defect
   floor unit in one 13-way equivalence (`forcingSignAndWidthDictionary_tfae`).
2. **In the one-sided prime window ceiling of `BiScaleUncertainty`**: on windows of length `L`,
   the prime-to-mass ratio `windowCeiling L` has polar main term `e^{L/2}`. Subtracting that pole,
   a one-sided bound `windowCeiling L ≤ e^{L/2} + B(1 + L)` forces every unit of the width and
   forcing-sign dictionary (`scalingSurface_hodgeIndex_of_windowCeiling_le`,
   `positiveCone_bezout_of_windowCeiling_le`, `cofinal_budget_of_windowCeiling_le`).
-/

open Set Complex Filter MeasureTheory
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
open GaloisForLFunctions.ScaleSignedIncidenceCriticality
open GaloisForLFunctions.HTGeometry
open RHTower
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.ArithmeticOrientationTheory

set_option autoImplicit false

/-! ## 1. Faithfulness of the Rosati reflection reading vs. blindness of unsubtracted positivity -/

/-- The lag-1 Frobenius reflection defect reading `D ↦ D.frobReflectionDefect {1} 1`. -/
noncomputable def frobReflectionReading {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : CurveDatum ι) : ℝ :=
  D.frobReflectionDefect ({1} : Finset ℕ) 1

/-- **The lag-1 Frobenius reflection reading resolves unitarity** on every `CurveDatum ι`. -/
theorem resolves_frobReflectionReading_unitary {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Resolves (frobReflectionReading (ι := ι)) CurveDatum.Unitary := by
  intro D₁ D₂ hshadow
  rw [mem_shadow_iff, frobReflectionReading, frobReflectionReading] at hshadow
  rw [← D₂.frobReflectionDefect_singleton_one_eq_zero_iff_unitary,
    ← D₁.frobReflectionDefect_singleton_one_eq_zero_iff_unitary, hshadow]

/-- **Faithfulness under any unitarity-flipping involution.** Any involutive flip `κ` on
`CurveDatum ι` that changes unitarity wherever it moves is separated by `frobReflectionReading`. -/
theorem orientationFaithful_frobReflectionReading_of_flips {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : CurveDatum ι → CurveDatum ι}
    (hflip : ∀ D : CurveDatum ι, κ D ≠ D → ¬ (CurveDatum.Unitary (κ D) ↔ CurveDatum.Unitary D)) :
    OrientationFaithful (frobReflectionReading (ι := ι)) κ :=
  orientationFaithful_of_resolves_of_flips resolves_frobReflectionReading_unitary hflip

/-- A unitary calibration curve datum with `q = 5`, `g = 1`, and `β = ![1, 1]`, matching the base
field and genus of `goldenDatum`. -/
def unitaryCalibrationDatum : CurveDatum (Fin 2) where
  q := 5
  g := 1
  hq := by norm_num
  hcard := by norm_num
  β := ![1, 1]
  β_ne_zero i := by fin_cases i <;> norm_num
  conjPerm := Equiv.refl (Fin 2)
  conjPerm_involutive i := rfl
  β_conjPerm i := by fin_cases i <;> simp
  fePerm := Equiv.refl (Fin 2)
  fePerm_involutive i := rfl
  β_fePerm i := by fin_cases i <;> simp

/-- `unitaryCalibrationDatum` is unitary (`‖β_i‖ = 1`). -/
theorem unitaryCalibrationDatum_unitary : unitaryCalibrationDatum.Unitary := by
  intro i; fin_cases i <;> simp [unitaryCalibrationDatum]

/-- Every trace of `unitaryCalibrationDatum` is `2`, hence an integer. -/
theorem unitaryCalibrationDatum_trace (k : ℕ) : unitaryCalibrationDatum.trace k = 2 := by
  simp only [CurveDatum.trace, CurveDatum.powerSum, unitaryCalibrationDatum,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_pow]
  norm_num

/-- Every point count of `unitaryCalibrationDatum` is `(5^(k/2) − 1)² ≥ 0`. -/
theorem unitaryCalibrationDatum_pointCount_nonneg (k : ℕ) :
    0 ≤ unitaryCalibrationDatum.pointCount k := by
  rw [CurveDatum.pointCount, unitaryCalibrationDatum_trace]
  change 0 ≤ (5 : ℝ) ^ k + 1 - 2 * (5 : ℝ) ^ ((k : ℝ) / 2)
  have hsq : ((5 : ℝ) ^ ((k : ℝ) / 2)) ^ 2 = (5 : ℝ) ^ k := by
    rw [← Real.rpow_natCast 5 k, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 5)]
    congr 1; ring
  have : (5 : ℝ) ^ k + 1 - 2 * (5 : ℝ) ^ ((k : ℝ) / 2) =
      ((5 : ℝ) ^ ((k : ℝ) / 2) - 1) ^ 2 := by linear_combination -hsq
  rw [this]
  exact sq_nonneg _

/-- The unsubtracted arithmetic reading of a curve datum: its `(q, g)` parameters, integrality of
all traces, and nonnegativity of all raw point counts `N_k` (`k ≥ 1`). -/
def unsubtractedCurveReading {ι : Type*} [Fintype ι] (D : CurveDatum ι) :
    ℕ × ℕ × Prop × Prop :=
  (D.q, D.g, (∀ k : ℕ, ∃ m : ℤ, D.trace k = m), (∀ k : ℕ, 1 ≤ k → 0 ≤ D.pointCount k))

/-- The collapse sending every datum in `CurveDatum (Fin 2)` to `goldenDatum`. -/
noncomputable def goldenCollapse : CurveDatum (Fin 2) → CurveDatum (Fin 2) :=
  fun _ => goldenDatum

/-- `unitaryCalibrationDatum` and `goldenDatum` have the exact same unsubtracted arithmetic
reading: `(q, g) = (5, 1)`, integral traces, and nonnegative point counts `N_k ≥ 0` for all
`k ≥ 1`. -/
theorem unsubtractedCurveReading_goldenDatum_eq_unitaryCalibrationDatum :
    unsubtractedCurveReading goldenDatum = unsubtractedCurveReading unitaryCalibrationDatum := by
  unfold unsubtractedCurveReading
  refine Prod.ext rfl (Prod.ext rfl (Prod.ext (propext ⟨fun _ k => ⟨2, unitaryCalibrationDatum_trace k⟩,
    fun _ => goldenDatum_trace_int⟩) (propext ⟨fun _ k _ => unitaryCalibrationDatum_pointCount_nonneg k,
      fun _ k hk => (goldenDatum_pointCount_pos hk).le⟩)))

/-- **Blindness of the unsubtracted arithmetic reading.** The reading recording `(q, g)`, trace
integrality, and raw point-count nonnegativity `∀ k ≥ 1, 0 ≤ N_k` cannot resolve `CurveDatum.Unitary`
on `CurveDatum (Fin 2)`, because `unitaryCalibrationDatum` and `goldenDatum` lie in the same
shadow while one is unitary and the other is not. -/
theorem not_resolves_unsubtractedCurveReading_unitary :
    ¬ Resolves (unsubtractedCurveReading (ι := Fin 2)) CurveDatum.Unitary := by
  intro hres
  have hmem : goldenDatum ∈ shadow unsubtractedCurveReading unitaryCalibrationDatum :=
    unsubtractedCurveReading_goldenDatum_eq_unitaryCalibrationDatum
  exact goldenDatum_not_unitary ((hres unitaryCalibrationDatum goldenDatum hmem).mpr
    unitaryCalibrationDatum_unitary)

/-- By contrast, `frobReflectionReading` separates `unitaryCalibrationDatum` (`= 0`),
`goldenDatum` (`= 1`), and `hidingDatum N` (`= 9/4`). -/
theorem frobReflectionReading_selectivity_battery (N : ℕ) [NeZero N] :
    frobReflectionReading unitaryCalibrationDatum = 0 ∧
      frobReflectionReading goldenDatum = 1 ∧
      frobReflectionReading (hidingDatum N) = 9 / 4 :=
  ⟨(unitaryCalibrationDatum.frobReflectionDefect_singleton_one_eq_zero_iff_unitary).mpr
      unitaryCalibrationDatum_unitary,
    goldenDatum_frobReflectionDefect_singleton_one,
    hidingDatum_frobReflectionDefect_singleton_one N⟩

/-! ## 2. The master forcing-sign and width dictionary over `ℤ` -/

/-- **The forcing-sign and width dictionary (`forcingSignAndWidthDictionary_tfae`)**:
unites the eight units of `widthDictionary_tfae` with the pole-subtracted forcing units of
`WhichArithmeticDataForceTheSign`:
1. `RiemannHypothesis` (spectral unit),
2. `scalingSurface.HodgeIndex` (intersection-form unit),
3. `∃ E, RiemannRochAxiom E ∧ AmpleAxiom E` (effectivity unit),
4. `scalingSurface.BezoutAxiom scalingSurface.positiveCone` (forward light-cone Bézout unit),
5. `scalingSurface.BezoutAxiom scalingSurface.openPositiveCone` (open forward light-cone Bézout unit),
6. `∀ r > 0, (scalingSubsurface (oddRealTestsAt r)).HodgeIndex` (odd reflection-sector unit),
7. `∀ r > 0, (scalingSubsurface (oddRealTestsAt r)).BezoutAxiom (coupledArithmeticCone (oddRealTestsAt r))`
   (coupled odd-cone Bézout unit),
8. all-aperture two-pole Chebyshev defect allocation on `(0, 2r]` (pole-subtracted prime/polar ledger unit),
9. subexponential Castelnuovo–Severi odd-defect floor (degree-floor unit),
10. one positive square in every intersection Gram (signature unit),
11. cofinal admission of the damped Möbius receiver (damping unit),
12. arbitrarily small pronic prefix energy (Báez-Duarte unit),
13. linear mean-square band of the Chebyshev error (growth unit),
14. absence of a finite-radius refutation of full Weil positivity (reading unit). -/
theorem forcingSignAndWidthDictionary_tfae : List.TFAE [
    RiemannHypothesis,
    scalingSurface.HodgeIndex,
    ∃ E : Set ScalingCycle, scalingSurface.RiemannRochAxiom E ∧ scalingSurface.AmpleAxiom E,
    scalingSurface.BezoutAxiom scalingSurface.positiveCone,
    scalingSurface.BezoutAxiom scalingSurface.openPositiveCone,
    ∀ r : ℝ, 0 < r → (scalingSubsurface (oddRealTestsAt r)).HodgeIndex,
    ∀ r : ℝ, 0 < r →
      (scalingSubsurface (oddRealTestsAt r)).BezoutAxiom (coupledArithmeticCone (oddRealTestsAt r)),
    ∀ (r R : ℝ), 0 < r → r < R → ∀ x : ScalingSubcycle (oddRealTestsAt r),
      chebyshevTwoPoleDefect (x.val.test.1 : ℝ → ℝ) r ≤
        oddReflectedPlateauMain x.val.test R + oddReflectedArchTail x.val.test R,
    ∀ σ : ℝ, 0 < σ → ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r →
      ∀ x : ScalingSubcycle (oddRealTestsAt r),
        -(C * Real.exp (2 * σ * r) * ∫ u : ℝ, ((x.val.test.1 : ℝ → ℝ) u) ^ 2) ≤
          (scalingSubsurface (oddRealTestsAt r)).defect x x,
    ∀ (n : ℕ) (f : Fin n → ℝ → ℂ), (∀ i, ContDiff ℝ 2 (f i)) → (∀ i, HasCompactSupport (f i)) →
      hermPosIndex (intersectionGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) f) = 1,
    ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧
      ∃ B : ℝ, ∀ T : ℕ, pmPowerDampedDivisorDiscreteEnergy ε T ≤ B,
    ∀ ε : ℝ, 0 < ε → ∃ (N : ℕ) (c : ℕ → ℝ),
      ∑' M : ℕ, (1 + sievePrefixDiscrepancy N M c) ^ 2 / ((M : ℝ) * ((M : ℝ) + 1)) < ε,
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 0 ≤ L → ∫ t in Icc 0 L, normalizedLogError t ^ 2 ≤ C * (1 + L),
    ¬ ∃ R : ℝ, Refutes (radiusReading R) WeilPositiveFull
      (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))] := by
  tfae_have 1 ↔ 2 := scalingSurface_hodgeIndex_iff.symm
  tfae_have 1 ↔ 3 := riemannHypothesis_iff_exists_effectivity
  tfae_have 2 ↔ 4 := scalingSurface.hodgeIndex_iff_positiveCone_bezout
  tfae_have 2 ↔ 5 := scalingSurface.hodgeIndex_iff_openPositiveCone_bezout
  tfae_have 1 ↔ 6 := (scalingSurface_forcing_tfae.out 0 4)
  tfae_have 1 ↔ 7 := (scalingSurface_forcing_tfae.out 0 5)
  tfae_have 1 ↔ 8 := (scalingSurface_forcing_tfae.out 0 7)
  tfae_have 1 ↔ 9 := (scalingSurface_forcing_tfae.out 0 8)
  tfae_have 1 ↔ 10 := riemannHypothesis_iff_one_positive_square
  tfae_have 1 ↔ 11 := riemannHypothesis_iff_cofinal_budget
  tfae_have 1 ↔ 12 := riemannHypothesis_iff_pronic_prefix_energy
  tfae_have 1 ↔ 13 := riemannHypothesis_iff_meanSquare_band
  tfae_have 1 ↔ 14 := riemannHypothesis_iff_no_radiusReading_refutes
  tfae_finish

/-- Direct dictionary entry: forward light-cone Bézout on `scalingSurface` is equivalent to
cofinal admission of the damped Möbius receiver. -/
theorem positiveCone_bezout_iff_cofinal_budget :
    scalingSurface.BezoutAxiom scalingSurface.positiveCone ↔
      ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧
        ∃ B : ℝ, ∀ T : ℕ, pmPowerDampedDivisorDiscreteEnergy ε T ≤ B :=
  (forcingSignAndWidthDictionary_tfae.out 3 10)

/-- Direct dictionary entry: all-aperture payment of the two-pole Chebyshev defect on `(0, 2r]` is
equivalent to the linear mean-square Chebyshev band. -/
theorem chebyshevTwoPoleDefect_paid_iff_meanSquare_band :
    (∀ (r R : ℝ), 0 < r → r < R → ∀ x : ScalingSubcycle (oddRealTestsAt r),
      chebyshevTwoPoleDefect (x.val.test.1 : ℝ → ℝ) r ≤
        oddReflectedPlateauMain x.val.test R + oddReflectedArchTail x.val.test R) ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 0 ≤ L → ∫ t in Icc 0 L, normalizedLogError t ^ 2 ≤ C * (1 + L) :=
  (forcingSignAndWidthDictionary_tfae.out 7 12)

/-! ## 3. The one-sided pole-subtracted window ceiling forces every unit in the dictionary -/

/-- **One-sided pole-subtracted window ceiling forces the Hodge index of `scalingSurface`.**
On windows of length `L`, `windowCeiling L` has polar main term `e^{L/2}`. If the pole-subtracted
excess `windowCeiling L − e^{L/2}` is eventually bounded above by `B(1 + L)`, then
`scalingSurface.HodgeIndex` holds. -/
theorem scalingSurface_hodgeIndex_of_windowCeiling_le {B : ℝ}
    (h : ∀ᶠ L in atTop, windowCeiling L ≤ Real.exp (L / 2) + B * (1 + L)) :
    scalingSurface.HodgeIndex :=
  scalingSurface_hodgeIndex_iff.mpr (riemannHypothesis_of_windowCeiling_le h)

/-- **One-sided pole-subtracted window ceiling forces forward light-cone Bézout.** -/
theorem positiveCone_bezout_of_windowCeiling_le {B : ℝ}
    (h : ∀ᶠ L in atTop, windowCeiling L ≤ Real.exp (L / 2) + B * (1 + L)) :
    scalingSurface.BezoutAxiom scalingSurface.positiveCone :=
  scalingSurface.hodgeIndex_iff_positiveCone_bezout.mp
    (scalingSurface_hodgeIndex_of_windowCeiling_le h)

/-- **One-sided pole-subtracted window ceiling forces all-aperture payment of the two-pole
Chebyshev defect.** -/
theorem chebyshevTwoPoleDefect_paid_of_windowCeiling_le {B : ℝ}
    (h : ∀ᶠ L in atTop, windowCeiling L ≤ Real.exp (L / 2) + B * (1 + L)) :
    ∀ (r R : ℝ), 0 < r → r < R → ∀ x : ScalingSubcycle (oddRealTestsAt r),
      chebyshevTwoPoleDefect (x.val.test.1 : ℝ → ℝ) r ≤
        oddReflectedPlateauMain x.val.test R + oddReflectedArchTail x.val.test R :=
  (forcingSignAndWidthDictionary_tfae.out 0 7).mp (riemannHypothesis_of_windowCeiling_le h)

/-- **One-sided pole-subtracted window ceiling forces cofinal admission of the damped Möbius
receiver.** -/
theorem cofinal_budget_of_windowCeiling_le {B : ℝ}
    (h : ∀ᶠ L in atTop, windowCeiling L ≤ Real.exp (L / 2) + B * (1 + L)) :
    ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧
      ∃ B' : ℝ, ∀ T : ℕ, pmPowerDampedDivisorDiscreteEnergy ε T ≤ B' :=
  riemannHypothesis_iff_cofinal_budget.mp (riemannHypothesis_of_windowCeiling_le h)

end GaloisForLFunctions.ArithmeticOrientationTheory
