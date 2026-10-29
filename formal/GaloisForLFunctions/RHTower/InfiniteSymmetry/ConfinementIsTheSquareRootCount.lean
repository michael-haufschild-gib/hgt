import GaloisForLFunctions.RHTower.InfiniteSymmetry.ThePolarDivisorIsTheZeroSet
import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheTrickleDownInequalityIsTheSquareRootCount
import GaloisForLFunctions.ArithmeticOfSquareRootPrecision.CurvesCalibrateThePrecisionExponent

/-!
# Confinement of the affine polar divisor is the lower square-root count

**Polar confinement** of a curve datum means that every pole of its continued affine `A₁` Weyl sum
lies on the critical hyperplane `Re s = −1/2`. For data with zeros in the open strip:

* confinement is equivalent to the **lower square-root point count**
  `N_k ≥ q^k + 1 − C q^{k/2}` for all `k` (`polarConfinement_iff_lowerCount`), and so is eventual
  holomorphy of the continuation off the critical hyperplane
  (`eventuallyAnalytic_off_critical_iff_lowerCount`);
* the golden datum has an integral zeta series, positive integral point counts, the functional
  equation, the upper square-root count, the strip condition and the exact pole calculus, and it is
  not confined (`golden_passes_every_test_but_the_lower_count`).

Any arithmetic input that confines the polar divisor is therefore exactly the lower half of the
square-root count of the datum; nothing in the infinite-symmetry calculus, and none of the arithmetic
properties above, supplies it. Over `𝔽_q` the count is produced by geometry (Weil, Stepanov); over
`ℤ` the lower half of the count for `Λ` is the Riemann hypothesis (`lowerCount_vonMangoldt_iff`).
-/

open Filter PowerSeries

namespace GaloisForLFunctions.RHTower.InfiniteSymmetry

open ArithmeticCastelnuovoSeveri HTGeometry.LoopEisenstein.AffineA1 CurveDatum

variable {ι : Type*} [Fintype ι] (D : ArithmeticCastelnuovoSeveri.CurveDatum ι)

/-- Every pole of the continued affine Weyl sum lies on the critical hyperplane. -/
def PolarConfinement : Prop :=
  ∀ s : ℂ, (numeratorPoly D).eval (zetaCoord D (s + 1)) = 0 → s.re = -(1 / 2 : ℝ)

/-- **Confinement is the lower square-root count.** -/
theorem polarConfinement_iff_lowerCount (hD : StripCondition D) :
    PolarConfinement D ↔ ∃ C : ℝ, ∀ k, D.q ^ k + 1 - C * D.sqrtq ^ k ≤ D.pointCount k :=
  (unitary_iff_poles_on_critical_hyperplane D hD).symm.trans
    (ArithmeticLorentzianGeometry.unitary_iff_exists_pointCount_ge D)

/-- The receiver form: holomorphy of the continuation off the critical hyperplane is the lower count. -/
theorem eventuallyAnalytic_off_critical_iff_lowerCount (hD : StripCondition D) :
    (∀ s : ℂ, -1 < s.re → s.re < 0 → s.re ≠ -(1 / 2 : ℝ) →
        ∀ᶠ R : ℝ in atTop, AnalyticAt ℂ (continuedWeylSum D R) s) ↔
      ∃ C : ℝ, ∀ k, D.q ^ k + 1 - C * D.sqrtq ^ k ≤ D.pointCount k :=
  (unitary_iff_eventually_analytic_off_critical D hD).symm.trans
    (ArithmeticLorentzianGeometry.unitary_iff_exists_pointCount_ge D)

/-- **The golden datum passes every arithmetic test but the lower count.** It has an integral zeta
series, positive integral point counts, the functional equation, the upper square-root count, the
strip condition and the exact pole calculus of its affine Weyl sum, and it is neither confined nor
does it satisfy the lower square-root count. -/
theorem golden_passes_every_test_but_the_lower_count :
    (∃ Zℤ : ℤ⟦X⟧, constantCoeff Zℤ = 1 ∧
      PowerSeries.map (Int.castRingHom ℂ) Zℤ = goldenDatum.zetaSeries) ∧
    (∀ j, ∃ n : ℤ, goldenDatum.pointCount j = n) ∧
    (∀ j, 1 ≤ j → 1 ≤ goldenDatum.pointCount j) ∧
    (∀ i, goldenDatum.β (goldenDatum.fePerm i) * goldenDatum.β i = 1) ∧
    ArithmeticOfSquareRootPrecision.UpperCountAtPrecision goldenDatum (1 / 2) ∧
    StripCondition goldenDatum ∧
    (∀ s : ℂ, (numeratorPoly goldenDatum).eval (zetaCoord goldenDatum (s + 1)) = 0 →
      ∀ᶠ R : ℝ in atTop, 0 < R ∧
        meromorphicOrderAt (fun z => weylSum goldenDatum (levelFourParameter z) 0 0 (Real.log R))
          s = -(((numeratorPoly goldenDatum).rootMultiplicity
            (zetaCoord goldenDatum (s + 1)) : ℤ) : WithTop ℤ)) ∧
    ¬ PolarConfinement goldenDatum ∧
    ¬ ∃ C : ℝ, ∀ k, goldenDatum.q ^ k + 1 - C * goldenDatum.sqrtq ^ k ≤ goldenDatum.pointCount k := by
  obtain ⟨hZ, hN, hfe, -⟩ := witt_integral_not_pure
  have hconf : ¬ PolarConfinement goldenDatum := fun h =>
    golden_not_unitary ((unitary_iff_poles_on_critical_hyperplane _ golden_stripCondition).mpr h)
  exact ⟨hZ, hN, fun j hj => one_le_goldenDatum_pointCount hj, hfe,
    (ArithmeticOfSquareRootPrecision.golden_upperCount_and_not_lowerCount (1 / 2)).1,
    golden_stripCondition, fun s hs => weylSum_eventual_order goldenDatum golden_stripCondition s hs,
    hconf, fun h => hconf ((polarConfinement_iff_lowerCount _ golden_stripCondition).mpr h)⟩

end GaloisForLFunctions.RHTower.InfiniteSymmetry
