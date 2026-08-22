import GaloisForLFunctions.RHTower.SourceHorizontalAdaptiveVacuumFusion
import GaloisForLFunctions.HTGeometry.AnnealedEscortSupport

/-!
# Annealed escort must precede arithmetic-vacuum fusion

The real escort flow extracted from annealed gradient descent has two inequivalent placements on
the source-horizontal Xi carrier.  Applied to the centered horizontal occupation before adjoining
the arithmetic vacuum, it sends grade `t` to `alpha * t` and preserves critical grade zero.
Applied after vacuum fusion, it also scales the fixed prime-vacuum exponent and sends
`t` to `1 + alpha * (t - 1)`.  Hence post-vacuum annealing fixes edge grade one, not critical
grade zero, and the two placements commute only at physical exponent one.

This is an unconditional staging obstruction and a positive source reduction.  Nontrivial
pre-vacuum temperature invariance on every actual Xi divisor is exactly RH; the paper's
post-normalization annealing cannot itself supply that invariance.
-/

namespace RHTower

open GaloisForLFunctions
open HTGeometry.ConstraintFrameRelativity

noncomputable section

/-- Route-local name for real escort transport. -/
abbrev sourceHorizontalRealEscort := realEscortMap

theorem sourceHorizontalRealEscort_odds {q : ℝ} (h0 : 0 < q) (h1 : q < 1) (alpha : ℝ) :
    probToOdds (sourceHorizontalRealEscort alpha q) = (probToOdds q) ^ alpha :=
  probToOdds_realEscortMap h0 h1 alpha

theorem sourceHorizontalRealEscort_mem {q : ℝ} (h0 : 0 < q) (h1 : q < 1) (alpha : ℝ) :
    0 < sourceHorizontalRealEscort alpha q ∧ sourceHorizontalRealEscort alpha q < 1 :=
  realEscortMap_mem h0 h1 alpha

theorem probToOdds_inj_of_lt_one {x y : ℝ} (hx : x < 1) (hy : y < 1)
    (h : probToOdds x = probToOdds y) : x = y := by
  calc
    x = oddsToProb (probToOdds x) := (oddsToProb_probToOdds hx).symm
    _ = oddsToProb (probToOdds y) := congrArg oddsToProb h
    _ = y := oddsToProb_probToOdds hy

theorem sourceHorizontalEqualFusion_mem {x y : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) (hy0 : 0 < y) (hy1 : y < 1) :
    0 < sourceHorizontalEqualFusion x y ∧ sourceHorizontalEqualFusion x y < 1 := by
  unfold sourceHorizontalEqualFusion
  have hxy : 0 < x * y := mul_pos hx0 hy0
  have hc : 0 < (1 - x) * (1 - y) := mul_pos (sub_pos.mpr hx1) (sub_pos.mpr hy1)
  constructor
  · positivity
  · exact (div_lt_one (add_pos hxy hc)).2 (by linarith)

theorem sourceHorizontalEqualFusion_odds {x y : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) (hy0 : 0 < y) (hy1 : y < 1) :
    probToOdds (sourceHorizontalEqualFusion x y) = probToOdds x * probToOdds y := by
  unfold probToOdds sourceHorizontalEqualFusion
  have hxy : 0 < x * y := mul_pos hx0 hy0
  have hc : 0 < (1 - x) * (1 - y) := mul_pos (sub_pos.mpr hx1) (sub_pos.mpr hy1)
  field_simp
  ring

theorem sourceHorizontalPrimeAdaptiveOccupation_injective (p : Nat.Primes) :
    Function.Injective (sourceHorizontalPrimeAdaptiveOccupation p) := by
  intro a b h
  have hpow : (p.1 : ℝ) ^ (a - 1) = (p.1 : ℝ) ^ (b - 1) := by
    calc
      (p.1 : ℝ) ^ (a - 1) =
          probToOdds (sourceHorizontalPrimeAdaptiveOccupation p a) := by
            simpa [probToOdds] using (sourceHorizontalPrimeAdaptiveOccupation_odds p a).symm
      _ = probToOdds (sourceHorizontalPrimeAdaptiveOccupation p b) := congrArg probToOdds h
      _ = (p.1 : ℝ) ^ (b - 1) := by
            simpa [probToOdds] using sourceHorizontalPrimeAdaptiveOccupation_odds p b
  have hexp := (Real.strictMono_rpow_of_base_gt_one
    (by exact_mod_cast p.2.one_lt)).injective hpow
  linarith

/-- Annealing the centered source before adjoining the arithmetic vacuum scales only horizontal
grade and preserves critical grade `t = 0`. -/
theorem sourceHorizontalEqualFusion_escort_centered_vacuum
    (p : Nat.Primes) (alpha t : ℝ) :
    sourceHorizontalEqualFusion
        (sourceHorizontalRealEscort alpha (sourceHorizontalPrimeCenteredOccupation p t))
        (sourceHorizontalPrimeVacuumOccupation p) =
      sourceHorizontalPrimeAdaptiveOccupation p (alpha * t) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hc0 := sourceHorizontalPrimeCenteredOccupation_pos p t
  have hc1 := sourceHorizontalPrimeCenteredOccupation_lt_one p t
  have hv0 := sourceHorizontalPrimeVacuumOccupation_pos p
  have hv1 := sourceHorizontalPrimeVacuumOccupation_lt_one p
  have hec := sourceHorizontalRealEscort_mem hc0 hc1 alpha
  have hfusion := sourceHorizontalEqualFusion_mem hec.1 hec.2 hv0 hv1
  have hcenter : probToOdds (sourceHorizontalPrimeCenteredOccupation p t) =
      (p.1 : ℝ) ^ t := by
    simpa [probToOdds] using sourceHorizontalPrimeCenteredOccupation_odds p t
  have hvac : probToOdds (sourceHorizontalPrimeVacuumOccupation p) =
      ((p.1 : ℝ))⁻¹ := by
    simpa [probToOdds] using sourceHorizontalPrimeVacuumOccupation_odds p
  apply probToOdds_inj_of_lt_one hfusion.2
    (sourceHorizontalPrimeAdaptiveOccupation_lt_one p (alpha * t))
  calc
    probToOdds (sourceHorizontalEqualFusion
        (sourceHorizontalRealEscort alpha (sourceHorizontalPrimeCenteredOccupation p t))
        (sourceHorizontalPrimeVacuumOccupation p)) =
        probToOdds (sourceHorizontalRealEscort alpha
          (sourceHorizontalPrimeCenteredOccupation p t)) *
          probToOdds (sourceHorizontalPrimeVacuumOccupation p) :=
      sourceHorizontalEqualFusion_odds hec.1 hec.2 hv0 hv1
    _ = (probToOdds (sourceHorizontalPrimeCenteredOccupation p t)) ^ alpha *
          probToOdds (sourceHorizontalPrimeVacuumOccupation p) := by
      rw [sourceHorizontalRealEscort_odds hc0 hc1]
    _ = (((p.1 : ℝ) ^ t) ^ alpha) * ((p.1 : ℝ)⁻¹) := by
      rw [hcenter, hvac]
    _ = (p.1 : ℝ) ^ (alpha * t - 1) := by
      rw [← Real.rpow_mul hp.le, Real.rpow_sub hp]
      rw [div_eq_mul_inv]
      congr 2
      · ring
      · simp
    _ = probToOdds (sourceHorizontalPrimeAdaptiveOccupation p (alpha * t)) := by
      simpa [probToOdds] using (sourceHorizontalPrimeAdaptiveOccupation_odds p (alpha * t)).symm

/-- Annealing after arithmetic-vacuum fusion scales the vacuum exponent too, shifting horizontal
grade from `t` to `1 + alpha * (t - 1)`. -/
theorem sourceHorizontalRealEscort_adaptiveOccupation
    (p : Nat.Primes) (alpha t : ℝ) :
    sourceHorizontalRealEscort alpha (sourceHorizontalPrimeAdaptiveOccupation p t) =
      sourceHorizontalPrimeAdaptiveOccupation p (1 + alpha * (t - 1)) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hq0 := sourceHorizontalPrimeAdaptiveOccupation_pos p t
  have hq1 := sourceHorizontalPrimeAdaptiveOccupation_lt_one p t
  have he := sourceHorizontalRealEscort_mem hq0 hq1 alpha
  apply probToOdds_inj_of_lt_one he.2
    (sourceHorizontalPrimeAdaptiveOccupation_lt_one p (1 + alpha * (t - 1)))
  calc
    probToOdds (sourceHorizontalRealEscort alpha
        (sourceHorizontalPrimeAdaptiveOccupation p t)) =
        (probToOdds (sourceHorizontalPrimeAdaptiveOccupation p t)) ^ alpha :=
      sourceHorizontalRealEscort_odds hq0 hq1 alpha
    _ = (((p.1 : ℝ) ^ (t - 1)) ^ alpha) := by
      rw [show probToOdds (sourceHorizontalPrimeAdaptiveOccupation p t) =
        (p : ℝ) ^ (t - 1) by
          simpa [probToOdds] using sourceHorizontalPrimeAdaptiveOccupation_odds p t]
    _ = (p.1 : ℝ) ^ (alpha * (t - 1)) := by
      rw [← Real.rpow_mul hp.le]
      congr 1
      ring
    _ = (p.1 : ℝ) ^ ((1 + alpha * (t - 1)) - 1) := by
      congr 1
      ring
    _ = probToOdds
        (sourceHorizontalPrimeAdaptiveOccupation p (1 + alpha * (t - 1))) := by
      simpa [probToOdds] using
        (sourceHorizontalPrimeAdaptiveOccupation_odds p (1 + alpha * (t - 1))).symm

/-- Pre-vacuum and post-vacuum annealing commute only at physical exponent `alpha = 1`.
The obstruction is independent of horizontal grade: it is exactly the arithmetic-vacuum exponent. -/
theorem sourceHorizontal_escort_vacuum_noncommutation_iff
    (p : Nat.Primes) (alpha t : ℝ) :
    sourceHorizontalRealEscort alpha
        (sourceHorizontalEqualFusion
          (sourceHorizontalPrimeCenteredOccupation p t)
          (sourceHorizontalPrimeVacuumOccupation p)) =
      sourceHorizontalEqualFusion
        (sourceHorizontalRealEscort alpha (sourceHorizontalPrimeCenteredOccupation p t))
        (sourceHorizontalPrimeVacuumOccupation p) ↔
      alpha = 1 := by
  rw [sourceHorizontalEqualFusion_centered_vacuum,
    sourceHorizontalRealEscort_adaptiveOccupation,
    sourceHorizontalEqualFusion_escort_centered_vacuum]
  constructor
  · intro h
    have hinj := sourceHorizontalPrimeAdaptiveOccupation_injective p h
    linarith
  · rintro rfl
    congr 2
    ring

/-- Post-vacuum annealing fixes edge grade `t = 1`, not critical grade `t = 0`. -/
theorem sourceHorizontalRealEscort_adaptive_fixed_iff
    (p : Nat.Primes) (alpha t : ℝ) (halpha : alpha ≠ 1) :
    sourceHorizontalRealEscort alpha (sourceHorizontalPrimeAdaptiveOccupation p t) =
      sourceHorizontalPrimeAdaptiveOccupation p t ↔ t = 1 := by
  rw [sourceHorizontalRealEscort_adaptiveOccupation]
  constructor
  · intro h
    have hinj := sourceHorizontalPrimeAdaptiveOccupation_injective p h
    have hprod : (alpha - 1) * (t - 1) = 0 := by nlinarith [hinj]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr halpha))
  · rintro rfl
    congr 2
    ring

/-- Pre-vacuum annealing fixes critical grade `t = 0` at every nontrivial exponent. -/
theorem sourceHorizontalEqualFusion_escort_centered_vacuum_fixed_iff
    (p : Nat.Primes) (alpha t : ℝ) (halpha : alpha ≠ 1) :
    sourceHorizontalEqualFusion
        (sourceHorizontalRealEscort alpha (sourceHorizontalPrimeCenteredOccupation p t))
        (sourceHorizontalPrimeVacuumOccupation p) =
      sourceHorizontalEqualFusion
        (sourceHorizontalPrimeCenteredOccupation p t)
        (sourceHorizontalPrimeVacuumOccupation p) ↔ t = 0 := by
  rw [sourceHorizontalEqualFusion_escort_centered_vacuum,
    sourceHorizontalEqualFusion_centered_vacuum]
  constructor
  · intro h
    have hinj := sourceHorizontalPrimeAdaptiveOccupation_injective p h
    have hprod : (alpha - 1) * t = 0 := by nlinarith [hinj]
    exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr halpha)
  · rintro rfl
    congr 2
    ring

/-- Every actual Xi divisor is fixed by a nontrivial pre-vacuum annealing stage. -/
def EveryXiPreVacuumAnnealedInvariant (p : Nat.Primes) (alpha : ℝ) : Prop :=
  ∀ rho : XiDivisorSupport,
    sourceHorizontalEqualFusion
        (sourceHorizontalRealEscort alpha
          (sourceHorizontalPrimeCenteredOccupation p
            (primeDepthBVWoldXiCenteredRate rho)))
        (sourceHorizontalPrimeVacuumOccupation p) =
      sourceHorizontalEqualFusion
        (sourceHorizontalPrimeCenteredOccupation p
          (primeDepthBVWoldXiCenteredRate rho))
        (sourceHorizontalPrimeVacuumOccupation p)

/-- Exact paper-to-RH reduction: nontrivial pre-vacuum temperature invariance is RH, not an
unconditional consequence of escort reweighting. -/
theorem everyXiPreVacuumAnnealedInvariant_iff_riemannHypothesis
    (p : Nat.Primes) (alpha : ℝ) (halpha : alpha ≠ 1) :
    EveryXiPreVacuumAnnealedInvariant p alpha ↔ RiemannHypothesis := by
  constructor
  · intro hinvariant
    apply riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half
    intro rho
    have hrate : primeDepthBVWoldXiCenteredRate rho = 0 :=
      (sourceHorizontalEqualFusion_escort_centered_vacuum_fixed_iff
        p alpha (primeDepthBVWoldXiCenteredRate rho) halpha).mp (hinvariant rho)
    exact (primeDepthBVWoldXiCenteredRate_eq_zero_iff rho).mp hrate
  · intro hRH rho
    apply (sourceHorizontalEqualFusion_escort_centered_vacuum_fixed_iff
      p alpha (primeDepthBVWoldXiCenteredRate rho) halpha).mpr
    exact (primeDepthBVWoldXiCenteredRate_eq_zero_iff rho).mpr
      (xi_divisor_support_re_eq_half_of_rh hRH rho)

/-- Under RH, nontrivial post-vacuum annealing necessarily moves every divisor packet: its fixed
grade is the wrong edge grade one. -/
theorem sourceHorizontalXi_postVacuumEscort_ne_of_riemannHypothesis
    (hRH : RiemannHypothesis) (rho : XiDivisorSupport)
    (p : Nat.Primes) (alpha : ℝ) (halpha : alpha ≠ 1) :
    sourceHorizontalRealEscort alpha
        (sourceHorizontalEqualFusion
          (sourceHorizontalPrimeCenteredOccupation p
            (primeDepthBVWoldXiCenteredRate rho))
          (sourceHorizontalPrimeVacuumOccupation p)) ≠
      sourceHorizontalEqualFusion
        (sourceHorizontalPrimeCenteredOccupation p
          (primeDepthBVWoldXiCenteredRate rho))
        (sourceHorizontalPrimeVacuumOccupation p) := by
  rw [sourceHorizontalEqualFusion_centered_vacuum]
  intro hfixed
  have hedge : primeDepthBVWoldXiCenteredRate rho = 1 :=
    (sourceHorizontalRealEscort_adaptive_fixed_iff p alpha
      (primeDepthBVWoldXiCenteredRate rho) halpha).mp hfixed
  have hzero : primeDepthBVWoldXiCenteredRate rho = 0 :=
    (primeDepthBVWoldXiCenteredRate_eq_zero_iff rho).mpr
      (xi_divisor_support_re_eq_half_of_rh hRH rho)
  linarith

end

end RHTower
