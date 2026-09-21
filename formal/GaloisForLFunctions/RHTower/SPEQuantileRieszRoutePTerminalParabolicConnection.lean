import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePFiveChannelKreinFactorization

/-!
# Source-forced parabolic connection for the Route-P terminal coordinate

The Route-P terminal coordinate is not stationary at zero prime-power admissions:
the physical square-root wall produces a nonzero lightlike translation.  A bare
translation fails P-Julia invariance.  This leaf gives the exact finite remedy:
homogenize the literal terminal Lorentz pair by one hyperbolic connection pair.

Every literal terminal update then acts by a parabolic isometry of the homogeneous
form.  Its affine section is exactly the terminal update; its central height is
forced by preservation, not selected from the target.  On the terminal locus the
Lorentz component is precisely the actual P Julia quadratic, so the extended P
signature is cutoff-independent.

This constructs a finite source-faithful connection seed.  It does not provide
the still-required unbounded joint Route-P graph estimate, ordered-history
intertwiner, divisor landing, or RH consequence.
-/

namespace RHTower

noncomputable section

open Filter

/-- Lorentz form of the homogeneous terminal connection: the terminal source pair and a
hyperbolic connection pair. -/
def routePTerminalHomogeneousForm (u : Fin 4 → ℝ) : ℝ :=
  u 0 ^ 2 - u 1 ^ 2 + 2 * u 2 * u 3

/-- Parabolic transport forced by one boundary/displacement increment.  On the affine section
`u 3 = 1`, its first two coordinates are the literal terminal update. -/
def routePTerminalParabolicConnection (b d : ℝ) (u : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![u 0 + b * u 3,
    u 1 + d * u 3,
    u 2 - b * u 0 + d * u 1 - (b ^ 2 - d ^ 2) * u 3 / 2,
    u 3]

/-- The source-forced parabolic connection preserves the homogeneous Lorentz form exactly. -/
theorem routePTerminalParabolicConnection_preserves_homogeneousForm
    (b d : ℝ) (u : Fin 4 → ℝ) :
    routePTerminalHomogeneousForm (routePTerminalParabolicConnection b d u) =
      routePTerminalHomogeneousForm u := by
  simp [routePTerminalHomogeneousForm, routePTerminalParabolicConnection]
  ring

/-- The two literal source coordinates carried by the terminal P Julia point. -/
def routePTerminalBoundary (K : ℕ) : ℝ :=
  ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary K (Real.log (K + 3)) 0

def routePTerminalDisplacement (K : ℕ) : ℝ :=
  speQuantileRieszTerminalErrorDisplacement K

/-- Literal cutoff increment of the terminal Lorentz pair: prime-power admission plus the
physical square-root wall. -/
def routePTerminalBoundaryIncrement (K : ℕ) : ℝ :=
  criticalMellinAtomWeight (K + 3) +
    2 * (Real.sqrt ((K + 4 : ℕ) : ℝ) - Real.sqrt ((K + 3 : ℕ) : ℝ))

def routePTerminalDisplacementIncrement (K : ℕ) : ℝ :=
  2 * (Real.sqrt ((K + 4 : ℕ) : ℝ) - Real.sqrt ((K + 3 : ℕ) : ℝ)) -
    criticalMellinAtomWeight (K + 3)

theorem routePTerminalBoundary_succ_sub (K : ℕ) :
    routePTerminalBoundary (K + 1) - routePTerminalBoundary K =
      routePTerminalBoundaryIncrement K := by
  unfold routePTerminalBoundary routePTerminalBoundaryIncrement
  rw [show ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary (K + 1)
        (Real.log ((K + 1 : ℕ) + 3)) 0 =
      ccmActualHeadParabolicMass (K + 1) +
        2 * (Real.sqrt ((K + 1 + 3 : ℕ) : ℝ) - 1) by
      simpa using
        ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary_terminal_eq_headMass_add_threshold
          (K + 1),
    ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary_terminal_eq_headMass_add_threshold K]
  unfold ccmActualHeadParabolicMass
  rw [Finset.sum_range_succ]
  norm_num
  ring

theorem routePTerminalDisplacement_succ_sub (K : ℕ) :
    routePTerminalDisplacement (K + 1) - routePTerminalDisplacement K =
      routePTerminalDisplacementIncrement K := by
  unfold routePTerminalDisplacement routePTerminalDisplacementIncrement
  rw [speQuantileRieszTerminalErrorDisplacement_eq_threshold_sub_headMass,
    speQuantileRieszTerminalErrorDisplacement_eq_threshold_sub_headMass]
  unfold ccmActualHeadParabolicMass
  rw [Finset.sum_range_succ]
  norm_num
  ring

/-- Central height forced by homogeneous preservation of the terminal Lorentz square. -/
def routePTerminalConnectionHeight (K : ℕ) : ℝ :=
  (routePTerminalBoundary 0 ^ 2 - routePTerminalDisplacement 0 ^ 2 -
    (routePTerminalBoundary K ^ 2 - routePTerminalDisplacement K ^ 2)) / 2

/-- Source-defined homogeneous terminal point.  Its last two coordinates are the connection's
hyperbolic pair; its affine terminal P point lies in the section with final coordinate one. -/
def routePTerminalHomogeneousLift (K : ℕ) : Fin 4 → ℝ :=
  ![routePTerminalBoundary K, routePTerminalDisplacement K,
    routePTerminalConnectionHeight K, 1]

theorem routePTerminalHomogeneousLift_form_eq_initial (K : ℕ) :
    routePTerminalHomogeneousForm (routePTerminalHomogeneousLift K) =
      routePTerminalBoundary 0 ^ 2 - routePTerminalDisplacement 0 ^ 2 := by
  simp [routePTerminalHomogeneousForm, routePTerminalHomogeneousLift,
    routePTerminalConnectionHeight]
  ring

/-- The source-defined homogeneous lift is transported exactly by the literal terminal
parabolic connection at every cutoff. -/
theorem routePTerminalHomogeneousLift_succ_eq_parabolicConnection (K : ℕ) :
    routePTerminalHomogeneousLift (K + 1) =
      routePTerminalParabolicConnection
        (routePTerminalBoundaryIncrement K)
        (routePTerminalDisplacementIncrement K)
        (routePTerminalHomogeneousLift K) := by
  have hB := routePTerminalBoundary_succ_sub K
  have hD := routePTerminalDisplacement_succ_sub K
  funext i
  fin_cases i
  · simp [routePTerminalHomogeneousLift, routePTerminalParabolicConnection]
    linarith
  · simp [routePTerminalHomogeneousLift, routePTerminalParabolicConnection]
    linarith
  · have hB' : routePTerminalBoundary (K + 1) =
      routePTerminalBoundary K + routePTerminalBoundaryIncrement K := by linarith
    have hD' : routePTerminalDisplacement (K + 1) =
      routePTerminalDisplacement K + routePTerminalDisplacementIncrement K := by linarith
    simp [routePTerminalHomogeneousLift, routePTerminalParabolicConnection,
      routePTerminalConnectionHeight]
    rw [hB', hD']
    ring
  · rfl

/-- At a literal zero atom, the terminal increment is lightlike.  The connection therefore
absorbs the wall translation without introducing a new quadratic source term. -/
theorem routePTerminalIncrement_lightlike_of_not_isPrimePow
    (K : ℕ) (hK : ¬ IsPrimePow (K + 3)) :
    routePTerminalBoundaryIncrement K ^ 2 -
      routePTerminalDisplacementIncrement K ^ 2 = 0 := by
  unfold routePTerminalBoundaryIncrement routePTerminalDisplacementIncrement
  rw [criticalMellinAtomWeight_eq_zero_of_not_isPrimePow hK]
  ring

/-- The connection transport preserves the source terminal form at every literal step. -/
theorem routePTerminalParabolicConnection_preserves_lift_form (K : ℕ) :
    routePTerminalHomogeneousForm
        (routePTerminalParabolicConnection
          (routePTerminalBoundaryIncrement K)
          (routePTerminalDisplacementIncrement K)
          (routePTerminalHomogeneousLift K)) =
      routePTerminalBoundary 0 ^ 2 - routePTerminalDisplacement 0 ^ 2 := by
  rw [← routePTerminalHomogeneousLift_succ_eq_parabolicConnection,
    routePTerminalHomogeneousLift_form_eq_initial]

/-- On the literal terminal locus, P's Julia form is exactly the Lorentz component of the
homogeneous connection. -/
theorem speQuantileRieszTerminalPJuliaQuadratic_eq_routePTerminalLorentzSquare (K : ℕ) :
    speQuantileRieszTerminalPJuliaQuadratic (speQuantileRieszTerminalPJuliaCoordinates K) =
      ((routePTerminalBoundary K ^ 2 - routePTerminalDisplacement K ^ 2 : ℝ) : ℂ) := by
  simpa [routePTerminalBoundary, routePTerminalDisplacement] using
    speQuantileRieszTerminalPJuliaQuadratic_eq_terminalLorentzSquare K

/-- **Extended P-signature conservation.** The literal terminal P Julia coordinate together
with its forced central connection height has cutoff-independent signature. -/
theorem speQuantileRieszTerminalPJuliaQuadratic_add_connectionHeight_eq_initial (K : ℕ) :
    speQuantileRieszTerminalPJuliaQuadratic (speQuantileRieszTerminalPJuliaCoordinates K) +
        ((2 * routePTerminalConnectionHeight K : ℝ) : ℂ) =
      ((routePTerminalBoundary 0 ^ 2 - routePTerminalDisplacement 0 ^ 2 : ℝ) : ℂ) := by
  rw [speQuantileRieszTerminalPJuliaQuadratic_eq_routePTerminalLorentzSquare]
  unfold routePTerminalConnectionHeight
  push_cast
  ring

/-- The literal terminal Lorentz square escapes along the physical square-root wall.  The lower
bound uses only the permanently retained prime-`2` mass, so it does not invoke any prime-density
or zero-distribution input. -/
theorem routePTerminalLorentzSquare_tendsto_atTop :
    Tendsto (fun K : ℕ =>
      routePTerminalBoundary K ^ 2 - routePTerminalDisplacement K ^ 2) atTop atTop := by
  have htwo : 0 < criticalMellinAtomWeight 2 := by
    exact criticalMellinAtomWeight_pos Nat.prime_two.isPrimePow
  have hmass (K : ℕ) : criticalMellinAtomWeight 2 ≤ ccmActualHeadParabolicMass K := by
    unfold ccmActualHeadParabolicMass
    have hmem : 0 ∈ Finset.range (K + 1) := Finset.mem_range.mpr (by omega)
    simpa using Finset.single_le_sum
      (s := Finset.range (K + 1)) (f := fun n => criticalMellinAtomWeight (n + 2))
      (fun n _ => criticalMellinAtomWeight_nonneg (n + 2)) hmem
  have hwall_nonneg (K : ℕ) :
      0 ≤ Real.sqrt ((K + 3 : ℕ) : ℝ) - 1 := by
    have hN : (1 : ℝ) < ((K + 3 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 < K + 3 by omega)
    have hsquare : 1 < (Real.sqrt ((K + 3 : ℕ) : ℝ)) ^ 2 := by
      rw [Real.sq_sqrt (by positivity)]
      exact hN
    have hsqrt_nonneg : 0 ≤ Real.sqrt ((K + 3 : ℕ) : ℝ) := Real.sqrt_nonneg _
    nlinarith
  have hformula (K : ℕ) :
      routePTerminalBoundary K ^ 2 - routePTerminalDisplacement K ^ 2 =
        8 * ccmActualHeadParabolicMass K *
          (Real.sqrt ((K + 3 : ℕ) : ℝ) - 1) := by
    simpa [routePTerminalBoundary, routePTerminalDisplacement] using
      ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary_terminal_sq_sub_errorDisplacement_sq K
  have hle (K : ℕ) :
      8 * criticalMellinAtomWeight 2 *
          (Real.sqrt ((K + 3 : ℕ) : ℝ) - 1) ≤
        routePTerminalBoundary K ^ 2 - routePTerminalDisplacement K ^ 2 := by
    rw [hformula]
    have hmul := mul_le_mul_of_nonneg_right (hmass K) (hwall_nonneg K)
    nlinarith
  have hcast : Tendsto (fun K : ℕ => ((K + 3 : ℕ) : ℝ)) atTop atTop := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      (tendsto_atTop_add_const_right atTop (3 : ℝ) tendsto_natCast_atTop_atTop)
  have hsqrt : Tendsto (fun K : ℕ => Real.sqrt ((K + 3 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hcast
  have hshift : Tendsto
      (fun K : ℕ => Real.sqrt ((K + 3 : ℕ) : ℝ) - 1) atTop atTop := by
    convert tendsto_atTop_add_const_right atTop (-1 : ℝ) hsqrt using 1
    ring
  have hscale : 0 < 8 * criticalMellinAtomWeight 2 := by positivity
  have hbase : Tendsto
      (fun K : ℕ => 8 * criticalMellinAtomWeight 2 *
        (Real.sqrt ((K + 3 : ℕ) : ℝ) - 1)) atTop atTop :=
    Tendsto.const_mul_atTop hscale hshift
  exact tendsto_atTop_mono hle hbase

/-- The forced central connection coordinate escapes to negative infinity.  Hence adding the
correct terminal connection does not restore a bounded Route-P carrier; a valid completion must
use a genuinely unbounded graph domain. -/
theorem routePTerminalConnectionHeight_tendsto_atBot :
    Tendsto routePTerminalConnectionHeight atTop atBot := by
  have hsquare := routePTerminalLorentzSquare_tendsto_atTop
  have hhalf : Tendsto (fun K : ℕ =>
      (routePTerminalBoundary K ^ 2 - routePTerminalDisplacement K ^ 2) / 2) atTop atTop :=
    hsquare.atTop_div_const (by norm_num)
  have hneg : Tendsto (fun K : ℕ => -
      ((routePTerminalBoundary K ^ 2 - routePTerminalDisplacement K ^ 2) / 2)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hhalf
  have hshift := tendsto_atBot_add_const_right atTop
    ((routePTerminalBoundary 0 ^ 2 - routePTerminalDisplacement 0 ^ 2) / 2) hneg
  convert hshift using 1
  funext K
  unfold routePTerminalConnectionHeight
  ring

/-- The homogeneous terminal transports form an abelian parabolic action.  Thus the terminal
connection has no residual finite-step holonomy: consecutive source increments compose by
addition. -/
theorem routePTerminalParabolicConnection_comp
    (b₂ d₂ b₁ d₁ : ℝ) (u : Fin 4 → ℝ) :
    routePTerminalParabolicConnection b₂ d₂
        (routePTerminalParabolicConnection b₁ d₁ u) =
      routePTerminalParabolicConnection (b₁ + b₂) (d₁ + d₂) u := by
  funext i
  fin_cases i <;>
    simp [routePTerminalParabolicConnection] <;>
    ring

/-- Every literal terminal point is the single parabolic orbit of the initial point under its
total source increment.  Terminal path coherence is therefore closed before the unresolved
ordered-history coupling is imposed. -/
theorem routePTerminalHomogeneousLift_eq_parabolicConnection_from_zero (K : ℕ) :
    routePTerminalHomogeneousLift K =
      routePTerminalParabolicConnection
        (routePTerminalBoundary K - routePTerminalBoundary 0)
        (routePTerminalDisplacement K - routePTerminalDisplacement 0)
        (routePTerminalHomogeneousLift 0) := by
  funext i
  fin_cases i
  · simp [routePTerminalHomogeneousLift, routePTerminalParabolicConnection,
      routePTerminalConnectionHeight]
  · simp [routePTerminalHomogeneousLift, routePTerminalParabolicConnection,
      routePTerminalConnectionHeight]
  · simp [routePTerminalHomogeneousLift, routePTerminalParabolicConnection,
      routePTerminalConnectionHeight]
    ring
  · simp [routePTerminalHomogeneousLift, routePTerminalParabolicConnection,
      routePTerminalConnectionHeight]

end

end RHTower
