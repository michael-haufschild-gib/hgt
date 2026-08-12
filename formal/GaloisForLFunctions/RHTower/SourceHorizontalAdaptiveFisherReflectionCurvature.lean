import GaloisForLFunctions.RHTower.SourceHorizontalGammaSixRelativeReflectionFraming
import GaloisForLFunctions.HTGeometry.ConstitutiveGlobalFormationInformationProperness

/-!
# Adaptive Fisher reflection curvature

A literal prime-horizontal character admits two coefficient-faithful readings on same source
carrier. Adaptive formation reads it as Bernoulli occupation with odds `p^(t-1)`; frozen
Gamma--Bockstein frame keeps neutral Fisher density `p/(p+1)^2` while transporting character.
These readings are not equal off center. Their exact Radon--Nikodym distortion is

`D_p(t) = ((p+p^t)(p+p^{-t}))/(p+1)^2
          = 1 + F_p * GammaSix(t log p)`.

Consequently frozen Hodge work is `D_p(t)` times adaptive Bernoulli Jeffreys work, with strictly
positive curvature reserve exactly when `t != 0`. This identifies retained horizontal class as
curvature of changing between adaptive statistical transport and frozen coefficient-faithful
source frame. Functional-equation reflection preserves both works, analytic multiplicity copies
remain explicit, and assembled Gauss--Hodge current factors through same adaptive information.

No source theorem is assumed forcing two frames to agree. Last theorem isolates exact producer:
global equality of frozen and adaptive readings on actual Xi divisor copies is equivalent to RH.
-/

open Complex

namespace RHTower

open GaloisForLFunctions

noncomputable section

/-- Adaptive occupation whose odds are the prime-horizontal character `p^(t-1)`. -/
def sourceHorizontalPrimeAdaptiveOccupation (p : Nat.Primes) (t : ℝ) : ℝ :=
  (p.1 : ℝ) ^ t / ((p.1 : ℝ) + (p.1 : ℝ) ^ t)

theorem sourceHorizontalPrimeAdaptiveOccupation_pos (p : Nat.Primes) (t : ℝ) :
    0 < sourceHorizontalPrimeAdaptiveOccupation p t := by
  unfold sourceHorizontalPrimeAdaptiveOccupation
  have hp : (0 : ℝ) < (p.1 : ℝ) := by exact_mod_cast p.2.pos
  positivity

theorem sourceHorizontalPrimeAdaptiveOccupation_lt_one (p : Nat.Primes) (t : ℝ) :
    sourceHorizontalPrimeAdaptiveOccupation p t < 1 := by
  unfold sourceHorizontalPrimeAdaptiveOccupation
  have hp : (0 : ℝ) < (p.1 : ℝ) := by exact_mod_cast p.2.pos
  apply (div_lt_one (by positivity)).2
  linarith

def sourceHorizontalPrimeAdaptiveOccupationUnit (p : Nat.Primes) (t : ℝ) : unitInterval :=
  ⟨sourceHorizontalPrimeAdaptiveOccupation p t, (sourceHorizontalPrimeAdaptiveOccupation_pos p t).le,
    (sourceHorizontalPrimeAdaptiveOccupation_lt_one p t).le⟩

@[simp] theorem sourceHorizontalPrimeAdaptiveOccupationUnit_coe (p : Nat.Primes) (t : ℝ) :
    (sourceHorizontalPrimeAdaptiveOccupationUnit p t : ℝ) = sourceHorizontalPrimeAdaptiveOccupation p t := rfl

/-- Change of Fisher frame between frozen neutral occupancy and adaptive occupancy. -/
def sourceHorizontalPrimeFisherFrameDistortion (p : Nat.Primes) (t : ℝ) : ℝ :=
  (((p.1 : ℝ) + (p.1 : ℝ) ^ t) *
    ((p.1 : ℝ) + (p.1 : ℝ) ^ (-t))) / ((p.1 : ℝ) + 1) ^ 2

theorem sourceHorizontalPrime_rpow_mul_reflected (p : Nat.Primes) (t : ℝ) :
    (p.1 : ℝ) ^ t * (p.1 : ℝ) ^ (-t) = 1 := by
  have hp : (0 : ℝ) < (p.1 : ℝ) := by exact_mod_cast p.2.pos
  rw [← Real.rpow_add hp]
  norm_num

theorem sourceHorizontalPrimeAdaptiveOccupation_sub_reflected (p : Nat.Primes) (t : ℝ) :
    sourceHorizontalPrimeAdaptiveOccupation p t - sourceHorizontalPrimeAdaptiveOccupation p (-t) =
      (p.1 : ℝ) * ((p.1 : ℝ) ^ t - (p.1 : ℝ) ^ (-t)) /
        (((p.1 : ℝ) + (p.1 : ℝ) ^ t) *
          ((p.1 : ℝ) + (p.1 : ℝ) ^ (-t))) := by
  have hpt : (0 : ℝ) < (p.1 : ℝ) ^ t := by
    exact Real.rpow_pos_of_pos (by exact_mod_cast p.2.pos) _
  have hpn : (0 : ℝ) < (p.1 : ℝ) ^ (-t) := by
    exact Real.rpow_pos_of_pos (by exact_mod_cast p.2.pos) _
  rw [sourceHorizontalPrimeAdaptiveOccupation, sourceHorizontalPrimeAdaptiveOccupation]
  field_simp
  ring

theorem sourceHorizontalFrozenBockstein_eq_distortion_mul_adaptive (p : Nat.Primes) (t : ℝ) :
    primeActivationOccupancyFisherDensity p *
        ((p.1 : ℝ) ^ t - (p.1 : ℝ) ^ (-t)) =
      sourceHorizontalPrimeFisherFrameDistortion p t *
        (sourceHorizontalPrimeAdaptiveOccupation p t - sourceHorizontalPrimeAdaptiveOccupation p (-t)) := by
  rw [primeActivationOccupancyFisherDensity_eq, sourceHorizontalPrimeAdaptiveOccupation_sub_reflected]
  unfold sourceHorizontalPrimeFisherFrameDistortion
  have hpt : (0 : ℝ) < (p.1 : ℝ) ^ t := by
    exact Real.rpow_pos_of_pos (by exact_mod_cast p.2.pos) _
  have hpn : (0 : ℝ) < (p.1 : ℝ) ^ (-t) := by
    exact Real.rpow_pos_of_pos (by exact_mod_cast p.2.pos) _
  have hp1 : (0 : ℝ) < (p.1 : ℝ) + 1 := by positivity
  field_simp

theorem sourceHorizontalGammaSixPrimeClockCurvature_eq_rpow (p : Nat.Primes) (t : ℝ) :
    sourceHorizontalGammaSixUnitOppositeBoundaryCurvature
        (Real.log (p : ℝ) * t) =
      (p.1 : ℝ) ^ t + (p.1 : ℝ) ^ (-t) - 2 := by
  have hp : (0 : ℝ) < (p.1 : ℝ) := by exact_mod_cast p.2.pos
  rw [sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq,
    Real.cosh_eq, Real.rpow_def_of_pos hp, Real.rpow_def_of_pos hp]
  ring

theorem sourceHorizontalPrimeFisherFrameDistortion_eq_one_add_curvature (p : Nat.Primes) (t : ℝ) :
    sourceHorizontalPrimeFisherFrameDistortion p t =
      1 + primeActivationOccupancyFisherDensity p *
        sourceHorizontalGammaSixUnitOppositeBoundaryCurvature
          (Real.log (p : ℝ) * t) := by
  rw [primeActivationOccupancyFisherDensity_eq, sourceHorizontalGammaSixPrimeClockCurvature_eq_rpow]
  unfold sourceHorizontalPrimeFisherFrameDistortion
  have hxy := sourceHorizontalPrime_rpow_mul_reflected p t
  have hp1 : (0 : ℝ) < (p.1 : ℝ) + 1 := by positivity
  field_simp
  nlinarith

theorem sourceHorizontalPrimeFisherFrameDistortion_eq_one_iff (p : Nat.Primes) (t : ℝ) :
    sourceHorizontalPrimeFisherFrameDistortion p t = 1 ↔ t = 0 := by
  rw [sourceHorizontalPrimeFisherFrameDistortion_eq_one_add_curvature]
  have hF : primeActivationOccupancyFisherDensity p ≠ 0 := by
    rw [primeActivationOccupancyFisherDensity_eq]
    have hp : (0 : ℝ) < (p.1 : ℝ) := by exact_mod_cast p.2.pos
    positivity
  have hlog : Real.log (p : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast p.2.one_lt)).ne'
  constructor
  · intro h
    have hc : sourceHorizontalGammaSixUnitOppositeBoundaryCurvature
        (Real.log (p : ℝ) * t) = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_left hF
      linarith
    exact (mul_eq_zero.mp
      ((sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq_zero_iff _).1 hc)).resolve_left hlog
  · rintro rfl
    simp [sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq]

theorem sourceHorizontalPrimeFisherFrameDistortion_pos (p : Nat.Primes) (t : ℝ) :
    0 < sourceHorizontalPrimeFisherFrameDistortion p t := by
  unfold sourceHorizontalPrimeFisherFrameDistortion
  have hp : (0 : ℝ) < (p.1 : ℝ) := by exact_mod_cast p.2.pos
  positivity

theorem sourceHorizontalPrimeAdaptiveOccupation_sub_reflected_eq_zero_iff (p : Nat.Primes) (t : ℝ) :
    sourceHorizontalPrimeAdaptiveOccupation p t - sourceHorizontalPrimeAdaptiveOccupation p (-t) = 0 ↔ t = 0 := by
  rw [sourceHorizontalPrimeAdaptiveOccupation_sub_reflected]
  have hp : (0 : ℝ) < (p.1 : ℝ) := by exact_mod_cast p.2.pos
  have hden : ((p.1 : ℝ) + (p.1 : ℝ) ^ t) *
      ((p.1 : ℝ) + (p.1 : ℝ) ^ (-t)) ≠ 0 := by positivity
  have hpne : (p.1 : ℝ) ≠ 0 := hp.ne'
  rw [div_eq_zero_iff, mul_eq_zero]
  simp only [hpne, false_or, hden, or_false, sub_eq_zero]
  constructor
  · intro h
    have := (Real.strictMono_rpow_of_base_gt_one
      (by exact_mod_cast p.2.one_lt)).injective h
    linarith
  · rintro rfl
    norm_num

theorem sourceHorizontalPrimeAdaptiveOccupation_complement (p : Nat.Primes) (t : ℝ) :
    1 - sourceHorizontalPrimeAdaptiveOccupation p t =
      (p.1 : ℝ) / ((p.1 : ℝ) + (p.1 : ℝ) ^ t) := by
  unfold sourceHorizontalPrimeAdaptiveOccupation
  have hp : (0 : ℝ) < (p.1 : ℝ) := by exact_mod_cast p.2.pos
  have hpt : (0 : ℝ) < (p.1 : ℝ) ^ t := Real.rpow_pos_of_pos hp _
  field_simp
  ring

/-- Exact coefficient-faithful odds: prime label and horizontal grade are both recoverable. -/
theorem sourceHorizontalPrimeAdaptiveOccupation_odds (p : Nat.Primes) (t : ℝ) :
    sourceHorizontalPrimeAdaptiveOccupation p t / (1 - sourceHorizontalPrimeAdaptiveOccupation p t) =
      (p.1 : ℝ) ^ (t - 1) := by
  rw [sourceHorizontalPrimeAdaptiveOccupation_complement]
  unfold sourceHorizontalPrimeAdaptiveOccupation
  have hp : (0 : ℝ) < (p.1 : ℝ) := by exact_mod_cast p.2.pos
  have hpt : (0 : ℝ) < (p.1 : ℝ) ^ t := Real.rpow_pos_of_pos hp _
  rw [Real.rpow_sub hp]
  norm_num
  field_simp

theorem sourceHorizontalPrimeAdaptiveLikelihoodRatio_mul_complementRatio (p : Nat.Primes) (t : ℝ) :
    (sourceHorizontalPrimeAdaptiveOccupation p t / sourceHorizontalPrimeAdaptiveOccupation p (-t)) *
        ((1 - sourceHorizontalPrimeAdaptiveOccupation p (-t)) / (1 - sourceHorizontalPrimeAdaptiveOccupation p t)) =
      (p.1 : ℝ) ^ t / (p.1 : ℝ) ^ (-t) := by
  rw [sourceHorizontalPrimeAdaptiveOccupation_complement, sourceHorizontalPrimeAdaptiveOccupation_complement]
  unfold sourceHorizontalPrimeAdaptiveOccupation
  have hp : (0 : ℝ) < (p.1 : ℝ) := by exact_mod_cast p.2.pos
  have hpt : (0 : ℝ) < (p.1 : ℝ) ^ t := Real.rpow_pos_of_pos hp _
  have hpn : (0 : ℝ) < (p.1 : ℝ) ^ (-t) := Real.rpow_pos_of_pos hp _
  field_simp

theorem sourceHorizontalPrimeAdaptiveLogOddsSeparation (p : Nat.Primes) (t : ℝ) :
    Real.log (sourceHorizontalPrimeAdaptiveOccupation p t / sourceHorizontalPrimeAdaptiveOccupation p (-t)) +
        Real.log ((1 - sourceHorizontalPrimeAdaptiveOccupation p (-t)) / (1 - sourceHorizontalPrimeAdaptiveOccupation p t)) =
      2 * t * Real.log (p : ℝ) := by
  have hp : (0 : ℝ) < (p.1 : ℝ) := by exact_mod_cast p.2.pos
  have hqtp := sourceHorizontalPrimeAdaptiveOccupation_pos p t
  have hqtn := sourceHorizontalPrimeAdaptiveOccupation_pos p (-t)
  have hct : 0 < 1 - sourceHorizontalPrimeAdaptiveOccupation p t := sub_pos.mpr (sourceHorizontalPrimeAdaptiveOccupation_lt_one p t)
  have hcn : 0 < 1 - sourceHorizontalPrimeAdaptiveOccupation p (-t) :=
    sub_pos.mpr (sourceHorizontalPrimeAdaptiveOccupation_lt_one p (-t))
  rw [← Real.log_mul (div_ne_zero hqtp.ne' hqtn.ne')
    (div_ne_zero hcn.ne' hct.ne'),
    sourceHorizontalPrimeAdaptiveLikelihoodRatio_mul_complementRatio,
    Real.log_div (Real.rpow_pos_of_pos hp _).ne'
      (Real.rpow_pos_of_pos hp _).ne',
    Real.log_rpow hp, Real.log_rpow hp]
  ring

def sourceHorizontalPrimeAdaptiveJeffreysWork (p : Nat.Primes) (t : ℝ) : ℝ :=
  2 * t * Real.log (p : ℝ) *
    (sourceHorizontalPrimeAdaptiveOccupation p t - sourceHorizontalPrimeAdaptiveOccupation p (-t))

theorem bernoulliJeffreysReal_sourceHorizontalPrimeAdaptive_eq (p : Nat.Primes) (t : ℝ) :
    GaloisForLFunctions.HTGeometry.bernoulliJeffreysReal
        (sourceHorizontalPrimeAdaptiveOccupationUnit p t) (sourceHorizontalPrimeAdaptiveOccupationUnit p (-t)) =
      sourceHorizontalPrimeAdaptiveJeffreysWork p t := by
  rw [GaloisForLFunctions.HTGeometry.bernoulliJeffreysReal_formula]
  · simp only [sourceHorizontalPrimeAdaptiveOccupationUnit_coe]
    rw [sourceHorizontalPrimeAdaptiveLogOddsSeparation]
    unfold sourceHorizontalPrimeAdaptiveJeffreysWork
    ring
  · exact sourceHorizontalPrimeAdaptiveOccupation_pos p t
  · exact sourceHorizontalPrimeAdaptiveOccupation_lt_one p t
  · exact sourceHorizontalPrimeAdaptiveOccupation_pos p (-t)
  · exact sourceHorizontalPrimeAdaptiveOccupation_lt_one p (-t)

def sourceHorizontalPrimeFrozenHodgeWork (p : Nat.Primes) (t : ℝ) : ℝ :=
  2 * Real.log (p : ℝ) * primeActivationOccupancyFisherDensity p *
    hodgeMassShape (p.1 : ℝ) t

theorem sourceHorizontalPrimeFrozenHodgeWork_eq_distortion_mul_adaptiveJeffreysWork
    (p : Nat.Primes) (t : ℝ) :
    sourceHorizontalPrimeFrozenHodgeWork p t =
      sourceHorizontalPrimeFisherFrameDistortion p t * sourceHorizontalPrimeAdaptiveJeffreysWork p t := by
  have hcore := sourceHorizontalFrozenBockstein_eq_distortion_mul_adaptive p t
  unfold sourceHorizontalPrimeFrozenHodgeWork sourceHorizontalPrimeAdaptiveJeffreysWork hodgeMassShape
  calc
    2 * Real.log (p : ℝ) * primeActivationOccupancyFisherDensity p *
          (t * ((p.1 : ℝ) ^ t - (p.1 : ℝ) ^ (-t))) =
        2 * t * Real.log (p : ℝ) *
          (primeActivationOccupancyFisherDensity p *
            ((p.1 : ℝ) ^ t - (p.1 : ℝ) ^ (-t))) := by ring
    _ = 2 * t * Real.log (p : ℝ) *
          (sourceHorizontalPrimeFisherFrameDistortion p t *
            (sourceHorizontalPrimeAdaptiveOccupation p t - sourceHorizontalPrimeAdaptiveOccupation p (-t))) := by rw [hcore]
    _ = sourceHorizontalPrimeFisherFrameDistortion p t *
          (2 * t * Real.log (p : ℝ) *
            (sourceHorizontalPrimeAdaptiveOccupation p t - sourceHorizontalPrimeAdaptiveOccupation p (-t))) := by ring

theorem sourceHorizontalPrimeAdaptiveJeffreysWork_eq_zero_iff (p : Nat.Primes) (t : ℝ) :
    sourceHorizontalPrimeAdaptiveJeffreysWork p t = 0 ↔ t = 0 := by
  have hlog : Real.log (p : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast p.2.one_lt)).ne'
  unfold sourceHorizontalPrimeAdaptiveJeffreysWork
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hconst | hdiff
    · rcases mul_eq_zero.mp hconst with htwo_t | hlog'
      · have : t = 0 := by linarith
        exact this
      · exact absurd hlog' hlog
    · exact (sourceHorizontalPrimeAdaptiveOccupation_sub_reflected_eq_zero_iff p t).1 hdiff
  · rintro rfl
    norm_num

theorem sourceHorizontalPrimeFrozenHodgeWork_pos_iff (p : Nat.Primes) (t : ℝ) :
    0 < sourceHorizontalPrimeFrozenHodgeWork p t ↔ t ≠ 0 := by
  unfold sourceHorizontalPrimeFrozenHodgeWork
  have hlog : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.2.one_lt)
  have hF : 0 < primeActivationOccupancyFisherDensity p := by
    rw [primeActivationOccupancyFisherDensity_eq]
    have hp : (0 : ℝ) < (p.1 : ℝ) := by exact_mod_cast p.2.pos
    positivity
  constructor
  · intro h ht
    subst ht
    simp [hodgeMassShape] at h
  · intro ht
    exact mul_pos (mul_pos (mul_pos (by norm_num) hlog) hF)
      (hodgeMassShape_pos (by exact_mod_cast p.2.one_lt) ht)

theorem sourceHorizontalPrimeAdaptiveJeffreysWork_pos_iff (p : Nat.Primes) (t : ℝ) :
    0 < sourceHorizontalPrimeAdaptiveJeffreysWork p t ↔ t ≠ 0 := by
  rw [← sourceHorizontalPrimeFrozenHodgeWork_pos_iff p t,
    sourceHorizontalPrimeFrozenHodgeWork_eq_distortion_mul_adaptiveJeffreysWork]
  exact (mul_pos_iff_of_pos_left (sourceHorizontalPrimeFisherFrameDistortion_pos p t)).symm

theorem sourceHorizontalPrimeFrozenHodgeWork_eq_adaptiveJeffreysWork_iff (p : Nat.Primes) (t : ℝ) :
    sourceHorizontalPrimeFrozenHodgeWork p t = sourceHorizontalPrimeAdaptiveJeffreysWork p t ↔ t = 0 := by
  rw [sourceHorizontalPrimeFrozenHodgeWork_eq_distortion_mul_adaptiveJeffreysWork]
  constructor
  · intro h
    have hprod : (sourceHorizontalPrimeFisherFrameDistortion p t - 1) * sourceHorizontalPrimeAdaptiveJeffreysWork p t = 0 := by
      linarith
    rcases mul_eq_zero.mp hprod with hframe | hwork
    · exact (sourceHorizontalPrimeFisherFrameDistortion_eq_one_iff p t).1 (by linarith)
    · exact (sourceHorizontalPrimeAdaptiveJeffreysWork_eq_zero_iff p t).1 hwork
  · rintro rfl
    norm_num [sourceHorizontalPrimeFrozenHodgeWork, sourceHorizontalPrimeAdaptiveJeffreysWork, hodgeMassShape]

theorem sourceHorizontalPrimeFrozen_sub_adaptive_eq_gammaSixCurvatureReserve (p : Nat.Primes) (t : ℝ) :
    sourceHorizontalPrimeFrozenHodgeWork p t - sourceHorizontalPrimeAdaptiveJeffreysWork p t =
      primeActivationOccupancyFisherDensity p *
        sourceHorizontalGammaSixUnitOppositeBoundaryCurvature
          (Real.log (p : ℝ) * t) * sourceHorizontalPrimeAdaptiveJeffreysWork p t := by
  rw [sourceHorizontalPrimeFrozenHodgeWork_eq_distortion_mul_adaptiveJeffreysWork,
    sourceHorizontalPrimeFisherFrameDistortion_eq_one_add_curvature]
  ring

theorem sourceHorizontalPrimeFrozen_sub_adaptive_pos_iff (p : Nat.Primes) (t : ℝ) :
    0 < sourceHorizontalPrimeFrozenHodgeWork p t - sourceHorizontalPrimeAdaptiveJeffreysWork p t ↔ t ≠ 0 := by
  rw [sourceHorizontalPrimeFrozen_sub_adaptive_eq_gammaSixCurvatureReserve]
  have hF : 0 < primeActivationOccupancyFisherDensity p := by
    rw [primeActivationOccupancyFisherDensity_eq]
    have hp : (0 : ℝ) < (p.1 : ℝ) := by exact_mod_cast p.2.pos
    positivity
  constructor
  · intro h ht
    subst ht
    simp [sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq] at h
  · intro ht
    have hlog : Real.log (p : ℝ) * t ≠ 0 :=
      mul_ne_zero (Real.log_pos (by exact_mod_cast p.2.one_lt)).ne' ht
    exact mul_pos (mul_pos hF
      ((sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_pos_iff _).2 hlog))
      ((sourceHorizontalPrimeAdaptiveJeffreysWork_pos_iff p t).2 ht)

theorem sourceHorizontalPrimeAdaptiveJeffreysWork_le_frozenHodgeWork (p : Nat.Primes) (t : ℝ) :
    sourceHorizontalPrimeAdaptiveJeffreysWork p t ≤ sourceHorizontalPrimeFrozenHodgeWork p t := by
  by_cases ht : t = 0
  · subst ht
    norm_num [sourceHorizontalPrimeAdaptiveJeffreysWork, sourceHorizontalPrimeFrozenHodgeWork, hodgeMassShape]
  · exact (sub_pos.mp ((sourceHorizontalPrimeFrozen_sub_adaptive_pos_iff p t).2 ht)).le

/-- Gauss--Hodge current is exactly adaptive information times frozen-frame curvature, with every
prime label and assembled residue retained. -/
theorem gaussHodgeMassCurrent_eq_adaptiveJeffreysCurvature_crossmultiplied
    (m : ℕ) (q : XiZeroCopy) (p : Nat.Primes) :
    4 * Real.log (p : ℝ) * gaussHodgeMassCurrent m q p =
      Real.log 2 * gaussChannelResidueCurrent m p *
        sourceHorizontalPrimeFisherFrameDistortion p (primeDepthBVWoldXiCenteredRate q.1) *
          sourceHorizontalPrimeAdaptiveJeffreysWork p (primeDepthBVWoldXiCenteredRate q.1) := by
  have hcore := sourceHorizontalPrimeFrozenHodgeWork_eq_distortion_mul_adaptiveJeffreysWork p
    (primeDepthBVWoldXiCenteredRate q.1)
  rw [gaussHodgeMassCurrent_eq_boost_square]
  calc
    4 * Real.log (p : ℝ) *
        (Real.log 2 / 2 * gaussChannelResidueCurrent m p *
          primeActivationOccupancyFisherDensity p *
            hodgeMassShape (p.1 : ℝ) (primeDepthBVWoldXiCenteredRate q.1)) =
      Real.log 2 * gaussChannelResidueCurrent m p *
        sourceHorizontalPrimeFrozenHodgeWork p (primeDepthBVWoldXiCenteredRate q.1) := by
          unfold sourceHorizontalPrimeFrozenHodgeWork
          ring
    _ = Real.log 2 * gaussChannelResidueCurrent m p *
        (sourceHorizontalPrimeFisherFrameDistortion p (primeDepthBVWoldXiCenteredRate q.1) *
          sourceHorizontalPrimeAdaptiveJeffreysWork p (primeDepthBVWoldXiCenteredRate q.1)) := by rw [hcore]
    _ = Real.log 2 * gaussChannelResidueCurrent m p *
        sourceHorizontalPrimeFisherFrameDistortion p (primeDepthBVWoldXiCenteredRate q.1) *
          sourceHorizontalPrimeAdaptiveJeffreysWork p (primeDepthBVWoldXiCenteredRate q.1) := by ring

theorem sourceHorizontalPrimeFisherFrameDistortion_even (p : Nat.Primes) (t : ℝ) :
    sourceHorizontalPrimeFisherFrameDistortion p (-t) = sourceHorizontalPrimeFisherFrameDistortion p t := by
  unfold sourceHorizontalPrimeFisherFrameDistortion
  ring

theorem sourceHorizontalPrimeAdaptiveJeffreysWork_even (p : Nat.Primes) (t : ℝ) :
    sourceHorizontalPrimeAdaptiveJeffreysWork p (-t) = sourceHorizontalPrimeAdaptiveJeffreysWork p t := by
  unfold sourceHorizontalPrimeAdaptiveJeffreysWork
  simp only [neg_neg]
  ring

theorem sourceHorizontalPrimeFrozenHodgeWork_even (p : Nat.Primes) (t : ℝ) :
    sourceHorizontalPrimeFrozenHodgeWork p (-t) = sourceHorizontalPrimeFrozenHodgeWork p t := by
  unfold sourceHorizontalPrimeFrozenHodgeWork
  rw [hodgeMassShape_even]


def sourceHorizontalXiAdaptiveJeffreysWork (q : XiZeroCopy) (p : Nat.Primes) : ℝ :=
  sourceHorizontalPrimeAdaptiveJeffreysWork p (primeDepthBVWoldXiCenteredRate q.1)

def sourceHorizontalXiFrozenHodgeWork (q : XiZeroCopy) (p : Nat.Primes) : ℝ :=
  sourceHorizontalPrimeFrozenHodgeWork p (primeDepthBVWoldXiCenteredRate q.1)

theorem sourceHorizontalXiFrozenHodgeWork_eq_adaptiveJeffreysWork_iff (q : XiZeroCopy) (p : Nat.Primes) :
    sourceHorizontalXiFrozenHodgeWork q p = sourceHorizontalXiAdaptiveJeffreysWork q p ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [sourceHorizontalXiFrozenHodgeWork, sourceHorizontalXiAdaptiveJeffreysWork, sourceHorizontalPrimeFrozenHodgeWork_eq_adaptiveJeffreysWork_iff,
    primeDepthBVWoldXiCenteredRate_eq_zero_iff]

/-- Reflection exchanges adaptive orientations but preserves their symmetric information work. -/
theorem sourceHorizontalXiAdaptiveJeffreysWork_reflection (q : XiZeroCopy) (p : Nat.Primes) :
    sourceHorizontalXiAdaptiveJeffreysWork (xiZeroCopyReflectEquiv q) p = sourceHorizontalXiAdaptiveJeffreysWork q p := by
  have hreflect : primeDepthBVWoldXiCenteredRate
      (xiZeroCopyReflectEquiv q).1 = -primeDepthBVWoldXiCenteredRate q.1 := by
    change primeDepthBVWoldXiCenteredRate (xiZeroReflectEquiv q.1) =
      -primeDepthBVWoldXiCenteredRate q.1
    rw [primeDepthBVWoldXiCenteredRate, primeDepthBVWoldXiCenteredRate,
      xiZeroReflectEquiv_apply]
    simp
    ring
  rw [sourceHorizontalXiAdaptiveJeffreysWork, sourceHorizontalXiAdaptiveJeffreysWork,
    hreflect,
    sourceHorizontalPrimeAdaptiveJeffreysWork_even]

theorem sourceHorizontalXiFrozenHodgeWork_reflection (q : XiZeroCopy) (p : Nat.Primes) :
    sourceHorizontalXiFrozenHodgeWork (xiZeroCopyReflectEquiv q) p = sourceHorizontalXiFrozenHodgeWork q p := by
  have hreflect : primeDepthBVWoldXiCenteredRate
      (xiZeroCopyReflectEquiv q).1 = -primeDepthBVWoldXiCenteredRate q.1 := by
    change primeDepthBVWoldXiCenteredRate (xiZeroReflectEquiv q.1) =
      -primeDepthBVWoldXiCenteredRate q.1
    rw [primeDepthBVWoldXiCenteredRate, primeDepthBVWoldXiCenteredRate,
      xiZeroReflectEquiv_apply]
    simp
    ring
  rw [sourceHorizontalXiFrozenHodgeWork, sourceHorizontalXiFrozenHodgeWork,
    hreflect,
    sourceHorizontalPrimeFrozenHodgeWork_even]

/-- Analytic multiplicity labels are retained: comparison is copied, never collapsed. -/
theorem sourceHorizontalXiWork_multiplicity_copy_independent
    (q r : XiZeroCopy) (hqr : q.1 = r.1) (p : Nat.Primes) :
    sourceHorizontalXiAdaptiveJeffreysWork q p = sourceHorizontalXiAdaptiveJeffreysWork r p ∧
      sourceHorizontalXiFrozenHodgeWork q p = sourceHorizontalXiFrozenHodgeWork r p := by
  unfold sourceHorizontalXiAdaptiveJeffreysWork sourceHorizontalXiFrozenHodgeWork
  rw [hqr]
  exact ⟨rfl, rfl⟩

theorem riemannHypothesis_iff_sourceHorizontalXi_frozenHodge_eq_adaptiveJeffreys :
    RiemannHypothesis ↔
      ∀ (q : XiZeroCopy) (p : Nat.Primes),
        sourceHorizontalXiFrozenHodgeWork q p = sourceHorizontalXiAdaptiveJeffreysWork q p := by
  constructor
  · intro hRH q p
    exact (sourceHorizontalXiFrozenHodgeWork_eq_adaptiveJeffreysWork_iff q p).2
      (xi_divisor_support_re_eq_half_of_rh hRH q.1)
  · intro h
    apply riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half
    intro q
    exact (sourceHorizontalXiFrozenHodgeWork_eq_adaptiveJeffreysWork_iff (xiFirstZeroCopy q)
      ⟨2, Nat.prime_two⟩).1 (h (xiFirstZeroCopy q) ⟨2, Nat.prime_two⟩)

end

end RHTower
