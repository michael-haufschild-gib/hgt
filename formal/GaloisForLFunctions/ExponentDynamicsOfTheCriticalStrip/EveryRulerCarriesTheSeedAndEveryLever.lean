import GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.MixedTowersOfLeversStayAboveTheBestCentre
import GaloisForLFunctions.SquareRootThreshold.TheSevenEighthsStripBoundsTheZeroWidth
import GaloisForLFunctions.SquareRootThreshold.TheWallsMeasureOneZeroWidth
import GaloisForLFunctions.RHTower.DeBruijnCollisionMassAndCriticalHeat
import GaloisForLFunctions.BezoutValuationIncidence.TheVaughanEmptyLegReadsTheZeroAbscissa
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheWidthIsReadInOneWindow
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheZerosOfTheMollifierCondense
import GaloisForLFunctions.FamilyContinuationTheory.TheSignalExponentIsTheZeroAbscissa
import GaloisForLFunctions.FamilyContinuationTheory.TheReturnTransferIsTheRiemannHypothesisUnderAStrip
import GaloisForLFunctions.RHTower.JointAncestryAbscissaGap
import GaloisForLFunctions.MixingArithmeticOfTheFloorTrees.TheAntisymmetricStateOfTheTwoEndsIsBoundedBelowIffTheRiemannHypothesis
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.LongMoebiusSecondMomentRigidity

/-!
# Every ruler carries the seed and every lever

A **ruler** for a number `w` on a domain `D` is a family of statements `P β` with
`w ≤ β ↔ P β` for `β ∈ D`. One half is a *transmitter* (`w ≤ β → P β`), the other a *receiver*
(`P β → w ≤ β`).

* **Measuring is not moving.** The readings of a ruler are exactly the bounds of `w`
  (`IsRuler.setOf_eq`); two rulers of one number agree reading by reading (`IsRuler.congr`); a
  map improves every reading of a ruler iff it improves every bound of `w`
  (`IsRuler.forall_reading_iff`), so a lever stated on one ruler is the same lever on every other
  (`IsRuler.lever_transport`), and a monotone lever is one reading at the number itself
  (`IsRuler.le_apply_self_iff`).
* **The rulers of the zero width.** The zero abscissa, the Möbius polynomial at one height, one
  window of the mollified zeta function, the zeros of the Möbius polynomials, the signal of the
  zeta kernel and the antisymmetric state of the two ends are rulers of `zetaZeroWidth`.
* **The seed on every ruler.** The bound `zetaZeroWidth ≤ 3/8` gives, with no hypothesis:
  `Λ ≤ 9/128` for the de Bruijn–Newman constant and `3/64` for the slice heat threshold;
  `M(n) = O(n^β)` for every `β > 7/8`; `|M_X(½ + it₀)| = O(X^{3/8+ε})`;
  `∫₀¹|ζ M_X|² = O(X^{3/4+2ε})`; the long moments `T^{4+3θ/4}` and `T^{6+3θ/4}`; no zeros of
  `M_X` on compacts right of `7/8` for large `X`; the signal exponent `7/8`; the depth rate
  `e^{3v/8}` of the antisymmetric state; the gap law of the joint-ancestry abscissa; and the
  equivalence of the return transfer with the Riemann hypothesis.
-/

open Complex MeasureTheory Set Filter

namespace GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip

open GaloisForLFunctions.SquareRootThreshold
  (zetaZeroWidth zetaZeroWidth_nonneg zetaZeroWidth_le_three_eighths)

/-! ### 1. Rulers -/

/-- `P` **transmits** `w` on `D`: a bound `w ≤ β` gives the statement `P β`. -/
def Transmits (w : ℝ) (D : Set ℝ) (P : ℝ → Prop) : Prop := ∀ β ∈ D, w ≤ β → P β

/-- `P` **receives** `w` on `D`: the statement `P β` gives the bound `w ≤ β`. -/
def Receives (w : ℝ) (D : Set ℝ) (P : ℝ → Prop) : Prop := ∀ β ∈ D, P β → w ≤ β

/-- A **ruler** for `w` on `D`: `P β` holds exactly when `w ≤ β`. -/
def IsRuler (w : ℝ) (D : Set ℝ) (P : ℝ → Prop) : Prop := ∀ β ∈ D, w ≤ β ↔ P β

variable {w : ℝ} {D : Set ℝ} {P Q : ℝ → Prop}

theorem isRuler_iff : IsRuler w D P ↔ Transmits w D P ∧ Receives w D P :=
  ⟨fun h => ⟨fun β hβ => (h β hβ).1, fun β hβ => (h β hβ).2⟩,
    fun h β hβ => ⟨h.1 β hβ, h.2 β hβ⟩⟩

/-- A transmitter holds at every seed. -/
theorem Transmits.of_seed (h : Transmits w D P) {s : ℝ} (hs : s ∈ D) (hw : w ≤ s) : P s :=
  h s hs hw

/-- The readings of a ruler are the bounds of `w`: none holds below `w`. -/
theorem IsRuler.setOf_eq (h : IsRuler w D P) : {β ∈ D | P β} = D ∩ Ici w := by
  ext β
  exact ⟨fun hβ => ⟨hβ.1, (h β hβ.1).2 hβ.2⟩, fun hβ => ⟨hβ.1, (h β hβ.1).1 hβ.2⟩⟩

/-- Two rulers of one number agree reading by reading. -/
theorem IsRuler.congr (hP : IsRuler w D P) (hQ : IsRuler w D Q) {β : ℝ} (hβ : β ∈ D) :
    P β ↔ Q β :=
  (hP β hβ).symm.trans (hQ β hβ)

/-- **Measuring is not moving.** A map preserving the domain improves every reading of a ruler iff
it improves every bound of `w`. -/
theorem IsRuler.forall_reading_iff (h : IsRuler w D P) {T : ℝ → ℝ} (hT : ∀ b ∈ D, T b ∈ D) :
    (∀ b ∈ D, P b → P (T b)) ↔ ∀ b ∈ D, w ≤ b → w ≤ T b :=
  ⟨fun hP b hb hw => (h (T b) (hT b hb)).2 (hP b hb ((h b hb).1 hw)),
    fun hw b hb hP => (h (T b) (hT b hb)).1 (hw b hb ((h b hb).2 hP))⟩

/-- A lever stated on one ruler is the same lever on every other ruler of the number. -/
theorem IsRuler.lever_transport (hP : IsRuler w D P) (hQ : IsRuler w D Q) {T : ℝ → ℝ}
    (hT : ∀ b ∈ D, T b ∈ D) :
    (∀ b ∈ D, P b → P (T b)) ↔ ∀ b ∈ D, Q b → Q (T b) :=
  (hP.forall_reading_iff hT).trans (hQ.forall_reading_iff hT).symm

/-- A lever on the whole line improves every reading of every ruler. -/
theorem IsLever.reading {T : ℝ → ℝ} (hT : IsLever w T) (h : IsRuler w D P) {b : ℝ} (hb : b ∈ D)
    (hTb : T b ∈ D) (hP : P b) : P (T b) :=
  (h (T b) hTb).1 (hT b ((h b hb).2 hP))

/-- For a monotone map a lever is one reading: the reading at the image of the number. -/
theorem IsRuler.le_apply_self_iff (h : IsRuler w D P) {T : ℝ → ℝ} (hTw : T w ∈ D) :
    w ≤ T w ↔ P (T w) :=
  h (T w) hTw

/-! ### 2. The rulers of the zero width -/

/-- The zero abscissa, measured from the critical line. -/
theorem isRuler_zetaZeroAbscissa :
    IsRuler zetaZeroWidth (Ici 0) fun β => _root_.RHTower.zetaZeroAbscissa ≤ 1 / 2 + β :=
  fun _ hβ => SquareRootThreshold.zetaZeroWidth_le_iff_zetaZeroAbscissa_le hβ

/-- The Möbius polynomial at one height `t₀` of the critical line. -/
theorem isRuler_moebiusPoly_pointwise (t₀ : ℝ) :
    IsRuler zetaZeroWidth (Ici 0) fun β => ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 1 ≤ X →
      ‖MultiscaleMollifiedZetaField.moebiusPoly X (MultiscaleMollifiedZetaField.linePoint t₀)‖ ≤
        C * (X : ℝ) ^ (β + ε) :=
  fun _ hβ => MultiscaleMollifiedZetaField.zetaZeroWidth_le_iff_pointwise hβ t₀

/-- One unit window of the mollified zeta function. -/
theorem isRuler_unit_window :
    IsRuler zetaZeroWidth (Ici 0) fun β => ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ X : ℕ, 1 ≤ X →
      ∫ u in (0 : ℝ)..1, ‖riemannZeta (MultiscaleMollifiedZetaField.linePoint u) *
        MultiscaleMollifiedZetaField.moebiusPoly X (MultiscaleMollifiedZetaField.linePoint u)‖ ^ 2 ≤
          B * (X : ℝ) ^ (2 * (β + ε)) :=
  fun _ hβ => MultiscaleMollifiedZetaField.zetaZeroWidth_le_iff_unit_window hβ

/-- The zeros of the Möbius polynomials. -/
theorem isRuler_moebiusPoly_zero_free :
    IsRuler zetaZeroWidth univ fun β => ∀ K : Set ℂ, IsCompact K → (∀ z ∈ K, 1 / 2 + β < z.re) →
      (1 : ℂ) ∉ K → ∀ᶠ X : ℕ in atTop, ∀ z ∈ K, MultiscaleMollifiedZetaField.moebiusPoly X z ≠ 0 :=
  fun _ _ => MultiscaleMollifiedZetaField.zetaZeroWidth_le_iff_moebiusPoly_zero_free

/-- The signal of the zeta kernel. -/
theorem isRuler_signal :
    IsRuler zetaZeroWidth (Ico 0 (1 / 2)) fun β => ∀ b' : ℝ, 1 / 2 + β < b' → b' ≤ 1 →
      ∃ K : ℝ, ∀ Z : ℝ, 0 < Z →
        ‖FamilyContinuationTheory.signal (FamilyContinuationTheory.zetaKernel 0) 2 Z‖ ≤ K * Z ^ b' :=
  fun β hβ => (SquareRootThreshold.zetaZeroWidth_le_iff_zetaZeroAbscissa_le hβ.1).trans
    (FamilyContinuationTheory.zetaZeroAbscissa_le_iff_forall_signal_le
      (by linarith [hβ.1]) (by linarith [hβ.2]))

/-- The depth of the antisymmetric state of the two ends of a window. -/
theorem isRuler_twoEndOdd :
    IsRuler zetaZeroWidth (Ico 0 (1 / 2)) fun θ => ∃ C : ℝ, ∀ v : ℝ, 0 ≤ v → ∀ Q : ℕ,
      (∀ n : ℕ, Q < n → AbsoluteGeometryOfSpecZ.packetAutocorr
        (MixingArithmeticOfTheFloorTrees.twoEndOdd v) (Real.log n) = 0) →
        -(C * Real.exp (θ * v)) ≤
          AbsoluteGeometryOfSpecZ.neutralForm Q (MixingArithmeticOfTheFloorTrees.twoEndOdd v) :=
  fun _ hθ => MixingArithmeticOfTheFloorTrees.zetaZeroWidth_le_iff_twoEndOdd_rate hθ.1 hθ.2

/-! ### 3. The seed on every ruler -/

/-- The seed on the abscissa: no zero right of `7/8`. -/
theorem zetaZeroAbscissa_le_seven_eighths : _root_.RHTower.zetaZeroAbscissa ≤ 7 / 8 := by
  have h := (isRuler_zetaZeroAbscissa (3 / 8) (mem_Ici.2 (by norm_num))).1
    zetaZeroWidth_le_three_eighths
  linarith only [h]

/-- **The de Bruijn–Newman constant is at most `9/128`.** -/
theorem newmanConstant_le_nine_div_128 : _root_.RHTower.DeBruijn.newmanConstant ≤ 9 / 128 := by
  have hsq : zetaZeroWidth ^ 2 ≤ (3 / 8 : ℝ) ^ 2 :=
    pow_le_pow_left₀ zetaZeroWidth_nonneg zetaZeroWidth_le_three_eighths 2
  have h := SquareRootThreshold.newmanConstant_le_half_sq_zetaZeroWidth
  linarith only [h, hsq]

/-- **The slice heat threshold is at most `3/64`.** -/
theorem wdHeatThreshold_le_three_div_64 : _root_.RHTower.DeBruijn.wdHeatThreshold ≤ 3 / 64 := by
  have hsq : zetaZeroWidth ^ 2 ≤ (3 / 8 : ℝ) ^ 2 :=
    pow_le_pow_left₀ zetaZeroWidth_nonneg zetaZeroWidth_le_three_eighths 2
  have h := _root_.RHTower.DeBruijn.wdHeatThreshold_le_third_sq_zetaZeroWidth
  linarith only [h, hsq]

/-- **The Mertens function is `O(n^β)` for every `β > 7/8`.** -/
theorem exists_mertens_le_of_seven_eighths_lt {β : ℝ} (hβ : 7 / 8 < β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
      |∑ d ∈ Finset.Icc 1 n, BezoutValuationIncidence.moebiusReal d| ≤ C * (n : ℝ) ^ β :=
  BezoutValuationIncidence.exists_moebius_power_bound_of_abscissa_lt
    (lt_of_le_of_lt zetaZeroAbscissa_le_seven_eighths hβ)

/-- **The Möbius polynomials on the critical line are `O(X^{3/8+ε})`** at every height. -/
theorem exists_norm_moebiusPoly_le_three_eighths (t₀ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 1 ≤ X →
      ‖MultiscaleMollifiedZetaField.moebiusPoly X (MultiscaleMollifiedZetaField.linePoint t₀)‖ ≤
        C * (X : ℝ) ^ (3 / 8 + ε) :=
  (isRuler_moebiusPoly_pointwise t₀ (3 / 8) (mem_Ici.2 (by norm_num))).1
    zetaZeroWidth_le_three_eighths ε hε

/-- **One window of the mollified zeta function is `O(X^{3/4+2ε})` in mean square.** -/
theorem exists_unit_window_le_three_eighths {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ X : ℕ, 1 ≤ X →
      ∫ u in (0 : ℝ)..1, ‖riemannZeta (MultiscaleMollifiedZetaField.linePoint u) *
        MultiscaleMollifiedZetaField.moebiusPoly X (MultiscaleMollifiedZetaField.linePoint u)‖ ^ 2 ≤
          B * (X : ℝ) ^ (2 * (3 / 8 + ε)) :=
  (isRuler_unit_window (3 / 8) (mem_Ici.2 (by norm_num))).1 zetaZeroWidth_le_three_eighths ε hε

/-- **The Möbius polynomials have no zeros on a compact set right of `7/8`**, for large `X`. -/
theorem eventually_moebiusPoly_ne_zero_right_of_seven_eighths {K : Set ℂ} (hK : IsCompact K)
    (hre : ∀ z ∈ K, 7 / 8 < z.re) (h1 : (1 : ℂ) ∉ K) :
    ∀ᶠ X : ℕ in atTop, ∀ z ∈ K, MultiscaleMollifiedZetaField.moebiusPoly X z ≠ 0 :=
  (isRuler_moebiusPoly_zero_free (3 / 8) (mem_univ _)).1 zetaZeroWidth_le_three_eighths K hK
    (fun z hz => by linarith only [hre z hz]) h1

/-- **The signal of the zeta kernel is `O(Z^{b'})` for every `b' > 7/8`.** -/
theorem exists_signal_le_of_seven_eighths_lt {b' : ℝ} (hb' : 7 / 8 < b') (hb'1 : b' ≤ 1) :
    ∃ K : ℝ, ∀ Z : ℝ, 0 < Z →
      ‖FamilyContinuationTheory.signal (FamilyContinuationTheory.zetaKernel 0) 2 Z‖ ≤ K * Z ^ b' :=
  (isRuler_signal (3 / 8) ⟨by norm_num, by norm_num⟩).1 zetaZeroWidth_le_three_eighths b'
    (by linarith only [hb']) hb'1

/-- **The antisymmetric state of the two ends has depth `O(e^{3v/8})`.** -/
theorem exists_twoEndOdd_rate_three_eighths :
    ∃ C : ℝ, ∀ v : ℝ, 0 ≤ v → ∀ Q : ℕ,
      (∀ n : ℕ, Q < n → AbsoluteGeometryOfSpecZ.packetAutocorr
        (MixingArithmeticOfTheFloorTrees.twoEndOdd v) (Real.log n) = 0) →
        -(C * Real.exp (3 / 8 * v)) ≤
          AbsoluteGeometryOfSpecZ.neutralForm Q (MixingArithmeticOfTheFloorTrees.twoEndOdd v) :=
  (isRuler_twoEndOdd (3 / 8) ⟨by norm_num, by norm_num⟩).1 zetaZeroWidth_le_three_eighths

/-- **The long second moment of the Möbius polynomials is `O(T^{4+3θ/4})`.** -/
theorem exists_pure_moebius_moment_le_seed {θ : ℝ} (hθ : 0 < θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
      (∫ t in (1 : ℝ)..T,
        ‖RHTower.edPoly ConjugateDiagonalGeometry.NearLineLogMean.moebiusMollifierCoeff
          (Finset.Icc 1 ⌊T ^ θ⌋₊) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
        C * T ^ (4 + 3 / 4 * θ) := by
  obtain ⟨C, hC, h⟩ :=
    ConjugateDiagonalGeometry.NearLineLogMean.exists_pure_moebius_moment_le_zetaZeroWidth hθ
  refine ⟨C, hC, fun T hT => (h T hT).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hT ?_) hC)⟩
  have := mul_le_mul_of_nonneg_right zetaZeroWidth_le_three_eighths hθ.le
  linarith only [this]

/-- **The long second moment of the mollified zeta function is `O(T^{6+3θ/4})`.** -/
theorem exists_moebius_mollifier_moment_le_seed {θ : ℝ} (hθ : 0 < θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
      (∫ t in (1 : ℝ)..T,
        ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          RHTower.edPoly ConjugateDiagonalGeometry.NearLineLogMean.moebiusMollifierCoeff
            (Finset.Icc 1 ⌊T ^ θ⌋₊) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
        C * T ^ (6 + 3 / 4 * θ) := by
  obtain ⟨C, hC, h⟩ :=
    ConjugateDiagonalGeometry.NearLineLogMean.exists_moebius_mollifier_moment_le_zetaZeroWidth hθ
  refine ⟨C, hC, fun T hT => (h T hT).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hT ?_) hC)⟩
  have := mul_le_mul_of_nonneg_right zetaZeroWidth_le_three_eighths hθ.le
  linarith only [this]

/-- **The gap law of the joint-ancestry abscissa, with no hypothesis**: it vanishes or it is at
least one plus the largest depth of a zero. -/
theorem jasAbscissa_eq_zero_or_one_add_sSup_le :
    _root_.RHTower.jasAbscissa = 0 ∨
      1 + sSup (Set.range fun q : _root_.RHTower.XiZeroCopy => |(q.1 : ℂ).re - 1 / 2|) ≤
        _root_.RHTower.jasAbscissa :=
  _root_.RHTower.jasAbscissa_eq_zero_or_one_add_sSup_le zetaZeroWidth_nonneg
    (lt_of_le_of_lt zetaZeroWidth_le_three_eighths (by norm_num))
    SquareRootThreshold.xiZeroHalfPlaneBound_zetaZeroWidth

/-- **The return transfer is the Riemann hypothesis, with no premise.** -/
theorem homogeneousReturnWindowTransfer_iff_riemannHypothesis :
    SignFreePurityMechanisms.HomogeneousReturnWindowTransfer ↔ RiemannHypothesis :=
  FamilyContinuationTheory.homogeneousReturnWindowTransfer_iff_riemannHypothesis
    (lt_of_le_of_lt zetaZeroAbscissa_le_seven_eighths (by norm_num))

#print axioms newmanConstant_le_nine_div_128
#print axioms exists_mertens_le_of_seven_eighths_lt
#print axioms homogeneousReturnWindowTransfer_iff_riemannHypothesis

end GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip
