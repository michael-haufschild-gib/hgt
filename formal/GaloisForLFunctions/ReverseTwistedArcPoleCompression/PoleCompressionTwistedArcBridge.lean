import GaloisForLFunctions.ReverseTwistedArcPoleCompression.ParitySplitNullPoleDuality
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPoleCompressionRHCriterion
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPoleTracePositivity
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPoleParityCurvature

/-!
# Bridge Between the `2 × 2` Pole-Compression Matrix, Twisted-Arc Cone Rigidity, and Opposite Parity Curvatures

This module formalizes the third leg of **Mechanism 4 (Reverse Twisted-Arc Duality on the
`2 × 2` Pole-Compression Matrix)**:

1. **Twisted-Arc Singleton Cone Criterion via `2 × 2` Pole Compression (`weilPositiveFull_iff_weilPoleCompression_and_eq_vonMangoldt`):**
   Coupling the unconditional twisted-arc cone uniqueness theorem
   (`weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt`) with the `2 × 2` pole-compression
   criterion (`riemannHypothesis_iff_weilPoleCompression_nonneg`), a sequence `lam : ℕ → ℝ` lies in
   the full Weil positivity cone `WeilPositiveFull lam` if and only if
   `|ccmWeilPoleCross a| ≤ ccmWeilPoleDiagonal a` for every positive aperture `a` **and**
   `lam n = Λ(n)` for every `n ≥ 2`.
2. **Five-Way Equivalence of `2 × 2` Pole Compression (`poleCompression_five_way_equivalence`):**
   Establishes the unconditional equivalence between:
   - the `2 × 2` pole-compression inequality `∀ a, |ccmWeilPoleCross a| ≤ ccmWeilPoleDiagonal a`,
   - nonnegativity of the two literal parity pole vectors `ccmPolarParityFormVector a (±1)`,
   - the explicit prime–Gamma pole inequality across all apertures `a`,
   - the square-root logarithmic Chebyshev deficit primitive bound
     `|ccmLogChebyshevDeficitPrimitive t| ≤ B e^{t/2}`,
   - nonemptiness of the full Weil positivity cone `∃ lam, WeilPositiveFull lam`, and
   - one-sided prime-blind positivity `WeilOneSided.PrimeBlindPositive`.
3. **Positive-Trace & Opposite-Curvature Wall-Crossing Dichotomy (`exists_threshold_poleCompression_trace_pos_and_opposite_curvatures`):**
   Above an explicit threshold `A₀ ≥ 2`, the `2 × 2` pole matrix has strictly positive trace
   (`0 < ccmWeilPoleDiagonal a`), the odd and even pole chambers have strictly opposite second
   derivatives (`deriv^[2] Odd < 0 < deriv^[2] Even`), and any hypothetical violation
   `ccmWeilPoleDiagonal a < |ccmWeilPoleCross a|` can flip the sign of **at most one** parity
   pole vector while the opposite parity pole vector remains strictly positive.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Nat
open Zeta23 RHTower RHTower.WeilSpectral RHTower.WeilPoleWeight

noncomputable section

namespace GaloisForLFunctions.ReverseTwistedArcPoleCompression

/-! ### Twisted-arc cone uniqueness coupled to the `2 × 2` pole-compression matrix -/

/-- **Twisted-Arc Singleton Cone Criterion via `2 × 2` Pole Compression:**
A weight sequence `lam : ℕ → ℝ` is full-cone Weil-positive (`WeilPositiveFull lam`) if and only if
the `2 × 2` pole-compression inequality `|ccmWeilPoleCross a| ≤ ccmWeilPoleDiagonal a` holds at
every positive aperture `a` and `lam n = Λ(n)` for every `n ≥ 2`. -/
theorem weilPositiveFull_iff_weilPoleCompression_and_eq_vonMangoldt {lam : ℕ → ℝ} :
    WeilPositiveFull lam ↔
      (∀ a : SuzukiPositiveAperture, |ccmWeilPoleCross a| ≤ ccmWeilPoleDiagonal a) ∧
        ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  rw [weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt,
    riemannHypothesis_iff_weilPoleCompression_nonneg]

/-- **Nonemptiness of the Full Weil Cone ↔ `2 × 2` Pole Compression:**
The full Weil positivity cone is nonempty (`∃ lam, WeilPositiveFull lam`) if and only if
`|ccmWeilPoleCross a| ≤ ccmWeilPoleDiagonal a` holds at every positive aperture `a`. -/
theorem exists_weilPositiveFull_iff_weilPoleCompression_nonneg :
    (∃ lam : ℕ → ℝ, WeilPositiveFull lam) ↔
      ∀ a : SuzukiPositiveAperture, |ccmWeilPoleCross a| ≤ ccmWeilPoleDiagonal a := by
  constructor
  · rintro ⟨lam, hW⟩
    exact (weilPositiveFull_iff_weilPoleCompression_and_eq_vonMangoldt.mp hW).1
  · intro h
    refine ⟨fun n => ArithmeticFunction.vonMangoldt n, ?_⟩
    exact weilPositiveFull_iff_weilPoleCompression_and_eq_vonMangoldt.mpr ⟨h, fun _ _ => rfl⟩

/-- **One-Sided Prime-Blind Positivity ↔ `2 × 2` Pole Compression:**
`WeilOneSided.PrimeBlindPositive` holds if and only if
`|ccmWeilPoleCross a| ≤ ccmWeilPoleDiagonal a` holds at every positive aperture `a`. -/
theorem primeBlindPositive_iff_weilPoleCompression_nonneg :
    WeilOneSided.PrimeBlindPositive ↔
      ∀ a : SuzukiPositiveAperture, |ccmWeilPoleCross a| ≤ ccmWeilPoleDiagonal a :=
  WeilOneSided.exists_weilPositiveFull_iff_primeBlindPositive.symm.trans
    exists_weilPositiveFull_iff_weilPoleCompression_nonneg

/-- **Five-Way Equivalence of `2 × 2` Pole Compression:**
The `2 × 2` pole-compression inequality `∀ a, |ccmWeilPoleCross a| ≤ ccmWeilPoleDiagonal a` is
unconditionally equivalent to:
1. literal parity-pole nonnegativity `0 ≤ Q_a(e_+) ∧ 0 ≤ Q_a(e_-)` at every aperture `a`,
2. the explicit prime–Gamma pole inequality across all apertures `a`,
3. the square-root bound `|ccmLogChebyshevDeficitPrimitive t| ≤ B e^{t/2}` on the logarithmic
   Chebyshev deficit primitive,
4. nonemptiness of the full Weil positivity cone `∃ lam, WeilPositiveFull lam` (whose unique
   element on `n ≥ 2`, when nonempty, is `Λ`), and
5. one-sided prime-blind positivity `WeilOneSided.PrimeBlindPositive`. -/
theorem poleCompression_five_way_equivalence :
    ((∀ a : SuzukiPositiveAperture, |ccmWeilPoleCross a| ≤ ccmWeilPoleDiagonal a) ↔
      (∀ a : SuzukiPositiveAperture,
        0 ≤ ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a 1) ∧
        0 ≤ ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a (-1)))) ∧
    ((∀ a : SuzukiPositiveAperture, |ccmWeilPoleCross a| ≤ ccmWeilPoleDiagonal a) ↔
      (∀ a : SuzukiPositiveAperture,
        |(-Real.eulerMascheroniConstant - Real.log (2 * Real.pi)) * (2 * a.1) +
          2 * a.1 ^ (2 : ℕ) + (2 * Real.sinh a.1) ^ (2 : ℕ) +
          ccmGammaPoleCrossBoundaryMass a - ccmPolarPrimeTent a| ≤
        (-Real.eulerMascheroniConstant - Real.log (2 * Real.pi)) * (2 * Real.sinh a.1) -
          Real.exp a.1 + (1 - 2 * a.1) * Real.exp (-a.1) + ccmGammaPoleSelfBoundaryMass a -
          2 * Real.exp a.1 * ccmReciprocalMangoldtError (2 * a.1) +
          2 * Real.exp (-a.1) * Chebyshev.psi (Real.exp (2 * a.1)))) ∧
    ((∀ a : SuzukiPositiveAperture, |ccmWeilPoleCross a| ≤ ccmWeilPoleDiagonal a) ↔
      (∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, 0 ≤ t →
        |ccmLogChebyshevDeficitPrimitive t| ≤ B * Real.exp (t / 2))) ∧
    ((∀ a : SuzukiPositiveAperture, |ccmWeilPoleCross a| ≤ ccmWeilPoleDiagonal a) ↔
      (∃ lam : ℕ → ℝ, WeilPositiveFull lam)) ∧
    ((∀ a : SuzukiPositiveAperture, |ccmWeilPoleCross a| ≤ ccmWeilPoleDiagonal a) ↔
      WeilOneSided.PrimeBlindPositive) :=
  ⟨riemannHypothesis_iff_weilPoleCompression_nonneg.symm.trans
    riemannHypothesis_iff_parityPole_nonneg,
   riemannHypothesis_iff_weilPoleCompression_nonneg.symm.trans
    riemannHypothesis_iff_primeGammaPoleInequality,
   riemannHypothesis_iff_weilPoleCompression_nonneg.symm.trans
    riemannHypothesis_iff_logChebyshevDeficitPrimitive_bound,
   exists_weilPositiveFull_iff_weilPoleCompression_nonneg.symm,
   primeBlindPositive_iff_weilPoleCompression_nonneg.symm⟩

/-! ### Positive-trace and opposite-curvature wall-crossing dichotomy -/

/-- **Positive-Trace & Opposite-Curvature Wall-Crossing Dichotomy:**
There exists an unconditional aperture threshold `A₀ ≥ 2` such that for every aperture
`a : SuzukiPositiveAperture` with `A₀ ≤ a.1`:
1. the diagonal entry (half-trace) of the `2 × 2` pole matrix is strictly positive:
   `0 < ccmWeilPoleDiagonal a`,
2. the odd pole chamber has strictly negative second derivative while the even pole chamber has
   strictly positive second derivative:
   `deriv (deriv (ccmWeilOddPoleChamber a)) a.1 < 0 ∧ 0 < deriv (deriv (ccmWeilEvenPoleChamber a)) a.1`,
3. if the off-diagonal cross entry exceeds the diagonal (`ccmWeilPoleDiagonal a < |ccmWeilPoleCross a|`),
   then **at most one** parity pole channel is negative while the opposite parity pole channel
   remains strictly positive. -/
theorem exists_threshold_poleCompression_trace_pos_and_opposite_curvatures :
    ∃ A₀ : ℝ, 2 ≤ A₀ ∧ ∀ a : SuzukiPositiveAperture, A₀ ≤ a.1 →
      0 < ccmWeilPoleDiagonal a ∧
      deriv (deriv (ccmWeilOddPoleChamber a)) a.1 < 0 ∧
      0 < deriv (deriv (ccmWeilEvenPoleChamber a)) a.1 ∧
      (ccmWeilPoleDiagonal a < |ccmWeilPoleCross a| →
        (ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a 1) < 0 ∧
          0 < ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a (-1))) ∨
        (0 < ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a 1) ∧
          ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a (-1)) < 0)) := by
  obtain ⟨A_tr, hA_tr⟩ := exists_eventually_ccmWeilPoleDiagonal_pos
  refine ⟨max A_tr ccmWeilPoleCurvatureThreshold, ?_, fun a ha => ?_⟩
  · exact (le_max_left 2 (Real.log (ccmWeilPoleUniformDiagonalBound + 17))).trans
      (le_max_right A_tr ccmWeilPoleCurvatureThreshold)
  · have htr : A_tr ≤ a.1 := (le_max_left A_tr ccmWeilPoleCurvatureThreshold).trans ha
    have hcurv : ccmWeilPoleCurvatureThreshold ≤ a.1 :=
      (le_max_right A_tr ccmWeilPoleCurvatureThreshold).trans ha
    have hdiag : 0 < ccmWeilPoleDiagonal a := hA_tr a htr
    exact ⟨hdiag,
      ccmWeilOddPoleChamber_second_neg a a rfl hcurv,
      ccmWeilEvenPoleChamber_second_pos a a rfl hcurv,
      fun hcross =>
        ccmWeilPoleCompression_parity_opposite_sign_of_diagonal_pos_of_cross_exceeds a hdiag hcross⟩

end GaloisForLFunctions.ReverseTwistedArcPoleCompression
