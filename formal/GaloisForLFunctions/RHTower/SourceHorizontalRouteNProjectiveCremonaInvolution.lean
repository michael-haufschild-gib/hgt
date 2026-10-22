import GaloisForLFunctions.RHTower.SourceHorizontalAdaptiveVacuumFusion
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmGammaSewnProjectiveParityLeakageBridge
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaRoutePProjectiveDualityAdjunctionFracture
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaMobiusHyperbolicRapidity

/-!
# Route-N projective Cremona involution of the horizontal source

The Route-N critical/twisted parity doublet already contains both retained horizontal
orientations.  This module identifies the operation separating them.  At critical odds `C`, it is
the nonlinear projective reflection

`x ↦ C² / x`.

It preserves the critical reservoir product, is an involution, and negates the exact Route-P
Julia/Cayley coordinate.  On the residue projective clock, inward and outward odds are the marked
odds of the same natural-cone carrier at opposite weights.  Thus Route N, Route P, and Route R are
not merely analogous: they are three coordinates of one reciprocal-odds reflection.

This also gives a sharp source-law classification.  Ordinary residue-Weyl adjunction preserves
projective weight, whereas functional-equation duality negates it; their states collide exactly at
neutral grade.  Therefore a producer cannot be a permutation/Weyl transport.  It must realize the
coefficient-faithful Cremona polarity on the literal completed source.
-/

namespace RHTower

noncomputable section

/-! ## Universal reciprocal-odds geometry -/

/-- Critical-reservoir reflection on positive odds. -/
def sourceHorizontalCriticalOddsReflection (critical odds : ℝ) : ℝ :=
  critical ^ 2 / odds

/-- Bounded Julia/Cayley coordinate of odds relative to critical odds. -/
def sourceHorizontalCriticalOddsCayley (critical odds : ℝ) : ℝ :=
  (odds - critical) / (odds + critical)

/-- Reciprocal-odds reflection is literally an involution. -/
theorem sourceHorizontalCriticalOddsReflection_involutive
    {critical odds : ℝ} (hc : critical ≠ 0) (ho : odds ≠ 0) :
    sourceHorizontalCriticalOddsReflection critical
        (sourceHorizontalCriticalOddsReflection critical odds) = odds := by
  unfold sourceHorizontalCriticalOddsReflection
  field_simp [hc, ho]

/-- Reciprocal-odds reflection reverses the bounded Julia/Cayley orientation. -/
theorem sourceHorizontalCriticalOddsCayley_reflection
    {critical odds : ℝ} (hc : 0 < critical) (ho : 0 < odds) :
    sourceHorizontalCriticalOddsCayley critical
        (sourceHorizontalCriticalOddsReflection critical odds) =
      -sourceHorizontalCriticalOddsCayley critical odds := by
  unfold sourceHorizontalCriticalOddsCayley sourceHorizontalCriticalOddsReflection
  field_simp [hc.ne', ho.ne']
  ring

/-- Positive reciprocal odds are fixed exactly at the critical reservoir. -/
theorem sourceHorizontalCriticalOddsReflection_eq_self_iff
    {critical odds : ℝ} (hc : 0 < critical) (ho : 0 < odds) :
    sourceHorizontalCriticalOddsReflection critical odds = odds ↔
      odds = critical := by
  unfold sourceHorizontalCriticalOddsReflection
  constructor
  · intro h
    have hsquare : critical ^ 2 = odds * odds :=
      (div_eq_iff ho.ne').mp h
    nlinarith
  · rintro rfl
    field_simp [hc.ne']

/-- The invariant product and positivity uniquely classify a reciprocal reflection pair. -/
theorem sourceHorizontalCriticalReservoir_pair_eq_iff
    {critical outward inward : ℝ}
    (hc : 0 < critical) (hout : 0 < outward) (hin : 0 < inward)
    (hreservoir : outward * inward = critical ^ 2) :
    outward = inward ↔ outward = critical := by
  constructor
  · intro h
    rw [h] at hreservoir
    nlinarith
  · intro h
    subst outward
    have hmul : critical * inward = critical * critical := by
      simpa only [pow_two] using hreservoir
    have hi : inward = critical := mul_left_cancel₀ hc.ne' hmul
    exact hi.symm

/-- Half-density aperture coordinates turn the odds Cayley coordinate into the corpus's literal
Route-P source Julia coordinate. -/
theorem sourceHorizontalCriticalOddsCayley_eq_sourceJulia
    (critical odds : ℝ) :
    sourceHorizontalCriticalOddsCayley critical odds =
      HedenmalmThetaSource.mobiusCriticalTwoSidedCayleyDiscrepancy
        ((odds - 1) / 2) ((critical - 1) / 2) := by
  rw [sourceHorizontalCriticalOddsCayley,
    HedenmalmThetaSource.mobiusCriticalTwoSidedCayleyDiscrepancy]
  ring

/-! ## Route-N parity doublet as one projective polarity -/

/-- Reflected projective weight on the same residue clock. -/
def routeNGammaSewnProjectiveReflectedWeight
    (t : ℝ) (p : Nat.Primes) : ℝ :=
  -routeNGammaSewnProjectiveWeight t p

/-- Marked odds of the reflected projective natural-cone state. -/
def routeNGammaSewnProjectiveReflectedMarkedOdds
    (t : ℝ) (p : Nat.Primes) : ℝ :=
  projNaturalMarkedOdds (Option (ZMod (p : ℕ)))
    (routeNGammaSewnProjectiveReflectedWeight t p)

theorem exp_two_mul_routeNGammaSewnProjectiveReflectedWeight
    (t : ℝ) (p : Nat.Primes) :
    Real.exp (2 * routeNGammaSewnProjectiveReflectedWeight t p) =
      (p : ℝ) ^ (2 * |t|) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  rw [routeNGammaSewnProjectiveReflectedWeight,
    routeNGammaSewnProjectiveWeight, Real.rpow_def_of_pos hp]
  congr 1
  ring

/-- Positive reflected projective weight is exactly the outward Route-N parity orientation. -/
theorem routeNGammaSewnProjectiveReflectedMarkedOdds_eq_outwardAdaptiveParityOdds
    (t : ℝ) (p : Nat.Primes) :
    routeNGammaSewnProjectiveReflectedMarkedOdds t p =
      routeNGammaSewnOutwardAdaptiveParityOdds t p := by
  have hp : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  rw [routeNGammaSewnProjectiveReflectedMarkedOdds, projNaturalMarkedOdds,
    exp_two_mul_routeNGammaSewnProjectiveReflectedWeight,
    projDeg_optionZMod, routeNGammaSewnOutwardAdaptiveParityOdds_eq,
    Real.rpow_sub hp, Real.rpow_one]

/-- Negative projective weight is exactly the inward Route-N parity orientation. -/
theorem routeNGammaSewnProjectiveMarkedOdds_eq_inwardAdaptiveParityOdds
    (t : ℝ) (p : Nat.Primes) :
    routeNGammaSewnProjectiveMarkedOdds t p =
      routeNGammaSewnInwardAdaptiveParityOdds t p := by
  exact routeNGammaSewnProjectiveMarkedOdds_eq_twistedSquarefreeParityOdds t p

/-- The non-equivariantly reconstructed outward class is the critical-reservoir reflection of
the inward class, coefficient by coefficient and prime by prime. -/
theorem routeNGammaSewnOutwardAdaptiveParityOdds_eq_criticalReflection
    (t : ℝ) (p : Nat.Primes) :
    routeNGammaSewnOutwardAdaptiveParityOdds t p =
      sourceHorizontalCriticalOddsReflection
        (routeNGammaSewnCriticalSquarefreeParityOdds p)
        (routeNGammaSewnInwardAdaptiveParityOdds t p) := by
  rfl

/-- Route-N reciprocal orientations negate one exact Route-P Julia/Cayley coordinate. -/
theorem routeNGammaSewnAdaptiveParityCayley_reflection
    (t : ℝ) (p : Nat.Primes) :
    sourceHorizontalCriticalOddsCayley
        (routeNGammaSewnCriticalSquarefreeParityOdds p)
        (routeNGammaSewnOutwardAdaptiveParityOdds t p) =
      -sourceHorizontalCriticalOddsCayley
        (routeNGammaSewnCriticalSquarefreeParityOdds p)
        (routeNGammaSewnInwardAdaptiveParityOdds t p) := by
  have hc : 0 < routeNGammaSewnCriticalSquarefreeParityOdds p := by
    rw [routeNGammaSewnCriticalSquarefreeParityOdds_eq,
      routeNGammaSewnUniversalCriticalChannelMass]
    exact Real.rpow_pos_of_pos (by exact_mod_cast p.2.pos) _
  have hi : 0 < routeNGammaSewnInwardAdaptiveParityOdds t p := by
    rw [routeNGammaSewnInwardAdaptiveParityOdds_eq]
    exact Real.rpow_pos_of_pos (by exact_mod_cast p.2.pos) _
  rw [routeNGammaSewnOutwardAdaptiveParityOdds_eq_criticalReflection]
  exact sourceHorizontalCriticalOddsCayley_reflection hc hi

/-- Equality of the two retained Route-N orientations is already neutral-grade rigidity. -/
theorem routeNGammaSewnOutwardAdaptiveParityOdds_eq_inward_iff
    (t : ℝ) (p : Nat.Primes) :
    routeNGammaSewnOutwardAdaptiveParityOdds t p =
        routeNGammaSewnInwardAdaptiveParityOdds t p ↔
      t = 0 := by
  have hp : (1 : ℝ) < p := by exact_mod_cast p.2.one_lt
  rw [routeNGammaSewnOutwardAdaptiveParityOdds_eq,
    routeNGammaSewnInwardAdaptiveParityOdds_eq]
  constructor
  · intro h
    have hexponent := (Real.strictMono_rpow_of_base_gt_one hp).injective h
    have habs : |t| = 0 := by linarith
    exact abs_eq_zero.mp habs
  · rintro rfl
    norm_num

/-! ## Route-P adjunction fracture classifies the missing producer -/

theorem routePProjectiveNaturalWeight_outward_eq_reflectedRouteN
    (t : ℝ) (p : Nat.Primes) :
    HedenmalmThetaSource.routePProjectiveNaturalWeight p (1 - 2 * |t|) =
      routeNGammaSewnProjectiveReflectedWeight t p := by
  rw [HedenmalmThetaSource.routePProjectiveNaturalWeight,
    routeNGammaSewnProjectiveReflectedWeight,
    routeNGammaSewnProjectiveWeight]
  ring

theorem routePProjectiveNaturalWeight_inward_eq_routeN
    (t : ℝ) (p : Nat.Primes) :
    HedenmalmThetaSource.routePProjectiveNaturalWeight p (1 + 2 * |t|) =
      routeNGammaSewnProjectiveWeight t p := by
  rw [HedenmalmThetaSource.routePProjectiveNaturalWeight,
    routeNGammaSewnProjectiveWeight]
  ring

/-- **Three-route fracture theorem.**  Route-P functional-equation duality supplies exactly the
opposite Route-N projective weight, but positive Weyl adjunction identifies the two states only at
zero Route-R rapidity.  This rules out every weight-preserving residue permutation as producer. -/
theorem routeNProjectiveAdjunction_eq_dual_iff_center
    (t : ℝ) (p : Nat.Primes) :
    HedenmalmThetaSource.routePProjectiveAdjointState p (1 - 2 * |t|) =
        HedenmalmThetaSource.routePProjectiveDualState p (1 - 2 * |t|) ↔
      t = 0 := by
  rw [HedenmalmThetaSource.routePProjectiveAdjointState_eq_dualState_iff]
  constructor
  · intro h
    have habs : |t| = 0 := by linarith
    exact abs_eq_zero.mp habs
  · rintro rfl
    norm_num

end

end RHTower
