import GaloisForLFunctions.RHTower.FZZCigarPunctureFractionalNodalThreshold
import GaloisForLFunctions.RHTower.MellinHeadChart

/-!
# Critical logarithmic nodal threshold at FZZ puncture

The pure-power classification leaves one exact wall: source order `α=1/2`. This file resolves all
logarithmic corrections on that wall. For source

`x^(1/2) (1-log x)^(-β) 1_(0,1)`,

the continuum resolvent state is uniquely

`-x^(-1/2) (1-log x)^(-β) 1_(0,1)`

almost everywhere. It is in `L²` exactly when `β>1/2`. The change `x=e^{-u}` turns state energy
into `(1+u)^(-2β)`, exposing exact p-series threshold. Thus the double-critical point `β=1/2`
still fails, while any stronger logarithmic damping succeeds.

This refines FZZ local carrier boundary to regular variation: square-root source can survive only
with more-than-half logarithmic damping. As before, local viability is nonselective and cannot
locate zeta ordinates; literal FZZ/GFZZ dynamics must derive location and critical damping.

Underlying endpoint integral is classical. Exact FZZ source equation, unique-state classification,
and nested sharp boundary are route-specialized new content.

`[NEW] [CLASSIFICATION] [SHARP BOUNDARY] [POSITIVE SURVIVOR] [PAPER-PROVED] [LEAN-PROVED]`
-/

open Complex MeasureTheory Set
open scoped ENNReal

namespace RHTower

noncomputable section

/-- Translation of the standard power-tail integrability criterion from `(1,∞)` to `(0,∞)`. -/
theorem integrableOn_Ioi_one_add_rpow_iff (s : ℝ) :
    IntegrableOn (fun u : ℝ => (1 + u) ^ s) (Ioi (0 : ℝ)) volume ↔ s < -1 := by
  let phi : ℝ → ℝ := fun u => 1 + u
  have hphi : phi '' Ioi (0 : ℝ) = Ioi (1 : ℝ) := by
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      dsimp [phi]
      change 0 < u at hu
      change 1 < 1 + u
      linarith
    · intro hy
      change 1 < y at hy
      refine ⟨y - 1, by change 0 < y - 1; linarith, ?_⟩
      dsimp [phi]
      ring
  have hderiv : ∀ u ∈ Ioi (0 : ℝ), HasDerivWithinAt phi 1 (Ioi (0 : ℝ)) u := by
    intro u _
    dsimp [phi]
    exact ((hasDerivAt_id u).const_add 1).hasDerivWithinAt
  have hinj : Set.InjOn phi (Ioi (0 : ℝ)) := by
    intro x _ y _ h
    dsimp [phi] at h
    linarith
  have hchange := integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioi hderiv hinj (fun y : ℝ => y ^ s)
  rw [hphi] at hchange
  have hbase := integrableOn_Ioi_rpow_iff (s := s) (t := (1 : ℝ)) one_pos
  rw [hbase] at hchange
  simpa [phi, one_smul] using hchange.symm

/-- Squared resolvent-state energy density at square-root source wall. -/
def fzzPunctureCriticalLogEnergy (beta x : ℝ) : ℝ :=
  x ^ (-1 : ℝ) * (1 - Real.log x) ^ (-(2 * beta))

/-- Exact logarithmic endpoint integrability threshold. -/
theorem fzzPunctureCriticalLogEnergy_integrableOn_iff (beta : ℝ) :
    IntegrableOn (fzzPunctureCriticalLogEnergy beta) (Ioo (0 : ℝ) 1) volume ↔
      1 / 2 < beta := by
  rw [integrableOn_Ioo_expScaleNeg one_pos]
  have hfun : (fun u : ℝ => Real.exp (-u) •
      fzzPunctureCriticalLogEnergy beta (Real.exp (-u))) =
      fun u : ℝ => (1 + u) ^ (-(2 * beta)) := by
    funext u
    simp only [smul_eq_mul, fzzPunctureCriticalLogEnergy]
    rw [Real.log_exp]
    have hexp : 0 < Real.exp (-u) := Real.exp_pos _
    rw [Real.rpow_neg_one, inv_eq_one_div]
    field_simp
    congr 1
    ring
  simp only [one_mul]
  rw [hfun, integrableOn_Ioi_one_add_rpow_iff]
  constructor <;> intro h <;> linarith

/-- Square-root source with logarithmic critical damping. -/
def fzzPunctureCriticalLogFormFactor (beta x : ℝ) : ℂ :=
  (Ioo (0 : ℝ) 1).indicator
    (fun u => ((u ^ (1 / 2 : ℝ) * (1 - Real.log u) ^ (-beta) : ℝ) : ℂ)) x

/-- Unique formal resolvent state at square-root power wall. -/
def fzzPunctureCriticalLogFormalState (beta x : ℝ) : ℂ :=
  (Ioo (0 : ℝ) 1).indicator
    (fun u => -((u ^ (-1 / 2 : ℝ) * (1 - Real.log u) ^ (-beta) : ℝ) : ℂ)) x

theorem fzzPunctureCriticalLogFormalState_aeStronglyMeasurable (beta : ℝ) :
    AEStronglyMeasurable (fzzPunctureCriticalLogFormalState beta) volume := by
  change AEStronglyMeasurable
    ((Ioo (0 : ℝ) 1).indicator
      (fun u => -((u ^ (-1 / 2 : ℝ) * (1 - Real.log u) ^ (-beta) : ℝ) : ℂ))) volume
  rw [aestronglyMeasurable_indicator_iff measurableSet_Ioo]
  apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioo
  intro x hx
  have hx0 : x ≠ 0 := ne_of_gt hx.1
  have hlog : 0 < 1 - Real.log x := by
    have := Real.log_neg hx.1 hx.2
    linarith
  have hpow : ContinuousAt (fun y : ℝ => y ^ (-1 / 2 : ℝ)) x :=
    continuousAt_id.rpow_const (Or.inl hx0)
  have hlogBase : ContinuousAt (fun y : ℝ => 1 - Real.log y) x :=
    continuousAt_const.sub (Real.continuousAt_log hx0)
  have hlogPow : ContinuousAt (fun y : ℝ => (1 - Real.log y) ^ (-beta)) x :=
    hlogBase.rpow_const (Or.inl (ne_of_gt hlog))
  have hreal : ContinuousAt
      (fun y : ℝ => y ^ (-1 / 2 : ℝ) * (1 - Real.log y) ^ (-beta)) x :=
    hpow.mul hlogPow
  exact (Complex.continuous_ofReal.continuousAt.comp hreal).neg.continuousWithinAt

/-- Exact `L²` law for logarithmically corrected square-root state. -/
theorem fzzPunctureCriticalLogFormalState_memLp_iff (beta : ℝ) :
    MemLp (fzzPunctureCriticalLogFormalState beta) 2 volume ↔ 1 / 2 < beta := by
  rw [memLp_two_iff_integrable_sq_norm
    (fzzPunctureCriticalLogFormalState_aeStronglyMeasurable beta)]
  have hnorm : (fun x : ℝ => ‖fzzPunctureCriticalLogFormalState beta x‖ ^ 2) =
      (Ioo (0 : ℝ) 1).indicator (fzzPunctureCriticalLogEnergy beta) := by
    funext x
    by_cases hx : x ∈ Ioo (0 : ℝ) 1
    · have hx0 : 0 < x := hx.1
      have hlog : 0 < 1 - Real.log x := by
        have := Real.log_neg hx.1 hx.2
        linarith
      simp only [fzzPunctureCriticalLogFormalState, indicator_of_mem hx, norm_neg,
        Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_pos (mul_pos (Real.rpow_pos_of_pos hx0 _)
        (Real.rpow_pos_of_pos hlog _)), mul_pow]
      simp only [fzzPunctureCriticalLogEnergy]
      rw [← Real.rpow_two, ← Real.rpow_mul hx0.le,
        ← Real.rpow_two, ← Real.rpow_mul hlog.le]
      congr 2 <;> ring
    · simp [fzzPunctureCriticalLogFormalState, hx]
  rw [hnorm, integrable_indicator_iff measurableSet_Ioo,
    fzzPunctureCriticalLogEnergy_integrableOn_iff]

/-- Critical-log form factor cancels resolvent equation pointwise. -/
theorem fzzPunctureCriticalLogFormalState_equation (beta x : ℝ) :
    (x : ℂ) * fzzPunctureCriticalLogFormalState beta x +
      fzzPunctureCriticalLogFormFactor beta x = 0 := by
  by_cases hx : x ∈ Ioo (0 : ℝ) 1
  · have hx0 : 0 < x := hx.1
    simp only [fzzPunctureCriticalLogFormalState, fzzPunctureCriticalLogFormFactor,
      indicator_of_mem hx]
    have hxpow : x * x ^ (-1 / 2 : ℝ) = x ^ (1 / 2 : ℝ) := by
      calc
        x * x ^ (-1 / 2 : ℝ) = x ^ (1 : ℝ) * x ^ (-1 / 2 : ℝ) := by
          rw [Real.rpow_one]
        _ = x ^ ((1 : ℝ) + (-1 / 2 : ℝ)) := (Real.rpow_add hx0 _ _).symm
        _ = x ^ (1 / 2 : ℝ) := by congr 1; ring
    have hreal : x * (-(x ^ (-1 / 2 : ℝ) * (1 - Real.log x) ^ (-beta))) +
        x ^ (1 / 2 : ℝ) * (1 - Real.log x) ^ (-beta) = 0 := by
      rw [mul_neg, ← mul_assoc, hxpow]
      ring
    exact_mod_cast hreal
  · simp [fzzPunctureCriticalLogFormalState, fzzPunctureCriticalLogFormFactor, hx]

/-- Critical-log survivor is genuinely nonzero for every damping exponent. -/
theorem fzzPunctureCriticalLogFormalState_ne_ae_zero (beta : ℝ) :
    ¬ fzzPunctureCriticalLogFormalState beta =ᵐ[volume] (0 : ℝ → ℂ) := by
  intro hzero
  have hzero' : fzzPunctureCriticalLogFormalState beta =ᵐ[
      volume.restrict (Ioo (0 : ℝ) 1)] (0 : ℝ → ℂ) := ae_restrict_of_ae hzero
  have hfalse : ∀ᵐ x : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1), False := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hzero'] with x hx hxzero
    have hx0 : 0 < x := hx.1
    have hlog : 0 < 1 - Real.log x := by
      have := Real.log_neg hx.1 hx.2
      linarith
    have hprod : x ^ (-1 / 2 : ℝ) * (1 - Real.log x) ^ (-beta) ≠ 0 :=
      ne_of_gt (mul_pos (Real.rpow_pos_of_pos hx0 _) (Real.rpow_pos_of_pos hlog _))
    simp [fzzPunctureCriticalLogFormalState, hx] at hxzero
    exact hprod (mul_eq_zero.mpr hxzero)
  have hmeasure : (volume.restrict (Ioo (0 : ℝ) 1)) Set.univ = 0 := by
    simpa using ae_iff.mp hfalse
  have hinterval : volume (Ioo (0 : ℝ) 1) = 0 := by
    rw [Measure.restrict_apply_univ] at hmeasure
    exact hmeasure
  rw [Real.volume_Ioo] at hinterval
  norm_num at hinterval

/-- Critical-log continuum eigen-equation. -/
def fzzPunctureCriticalLogEigenEquation (beta : ℝ) (f : ℝ → ℂ) : Prop :=
  MemLp f 2 volume ∧
    ∀ᵐ x : ℝ ∂volume,
      (x : ℂ) * f x + fzzPunctureCriticalLogFormFactor beta x = 0

/-- Critical-log equation has one unique representative modulo null sets. -/
theorem fzzPunctureCriticalLogEigenEquation_state_unique (beta : ℝ) (f : ℝ → ℂ)
    (h : fzzPunctureCriticalLogEigenEquation beta f) :
    f =ᵐ[volume] fzzPunctureCriticalLogFormalState beta := by
  have hne : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := (volume : Measure ℝ).ae_ne 0
  filter_upwards [h.2, hne] with x hxeq hxne
  have hformal := fzzPunctureCriticalLogFormalState_equation beta x
  have hcoef : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hxne
  apply sub_eq_zero.mp
  apply (mul_eq_zero.mp ?_).resolve_left hcoef
  linear_combination hxeq - hformal

/-- Nonzero embedded mode at logarithmically corrected square-root wall. -/
def FZZPunctureCriticalLogPointMode (beta : ℝ) : Prop :=
  ∃ f : ℝ → ℂ,
    fzzPunctureCriticalLogEigenEquation beta f ∧
      ¬ f =ᵐ[volume] (0 : ℝ → ℂ)

/-- Exact critical-log occurrence law, with no assumptions. -/
theorem fzzPunctureCriticalLogPointMode_iff (beta : ℝ) :
    FZZPunctureCriticalLogPointMode beta ↔ 1 / 2 < beta := by
  constructor
  · rintro ⟨f, heq, -⟩
    have hstate := fzzPunctureCriticalLogEigenEquation_state_unique beta f heq
    exact (fzzPunctureCriticalLogFormalState_memLp_iff beta).mp
      ((memLp_congr_ae hstate).mp heq.1)
  · intro h
    refine ⟨fzzPunctureCriticalLogFormalState beta, ?_,
      fzzPunctureCriticalLogFormalState_ne_ae_zero beta⟩
    exact ⟨(fzzPunctureCriticalLogFormalState_memLp_iff beta).mpr h,
      Filter.Eventually.of_forall (fzzPunctureCriticalLogFormalState_equation beta)⟩

/-- Double-critical logarithmic exponent is exactly excluded. -/
theorem not_fzzPunctureCriticalLogPointMode_at_half :
    ¬ FZZPunctureCriticalLogPointMode (1 / 2) := by
  rw [fzzPunctureCriticalLogPointMode_iff]
  norm_num

/-- Strict logarithmic damping already realizes square-root source mode. -/
theorem fzzPunctureCriticalLogPointMode_three_quarters :
    FZZPunctureCriticalLogPointMode (3 / 4) := by
  rw [fzzPunctureCriticalLogPointMode_iff]
  norm_num

end

end RHTower
