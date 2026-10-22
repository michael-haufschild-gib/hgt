import GaloisForLFunctions.HTGeometry.TranslatedStripBoundary
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCanonicalOrientationMultiplier

/-!
# Infinitely many forced singularities of the Hedenmalm orientation multiplier

The Xi divisor is infinite and lies in the open strip `0 < re z < 1`.  Under every positive real
translation it therefore has infinitely many left-boundary points: Xi zeros whose translated
predecessor is not a zero.  At each such point the corresponding completed logarithmic-flux
difference is nonanalytic, with nonremovability certified by the residue-filled completed-flux
germ.

The affine frequency coordinate transports these boundary points injectively to singularities of
the canonical Hedenmalm horizontal orientation multiplier.  Hence every positive aperture forces
an infinite, divisor-indexed singular carrier.  This is an unconditional carrier theorem, not a
positivity theorem and not a proof of RH.
-/

open Complex Set Metric Filter Topology

namespace RHTower

noncomputable section

def xiZeroSet : Set ℂ := {z : ℂ | xi z = 0}

theorem xiZeroSet_infinite : xiZeroSet.Infinite := by
  apply xiDivisorSupport_infinite.mono
  intro z hz
  exact xi_eq_zero_of_mem_divisor_support ⟨z, hz⟩

theorem xiZeroSet_mem_openUnitStrip {z : ℂ} (hz : z ∈ xiZeroSet) :
    0 < z.re ∧ z.re < 1 := by
  let q : XiDivisorSupport := ⟨z, mem_xi_divisor_support_of_eq_zero hz⟩
  exact xi_divisor_support_re_mem_open_unit q

def xiLeftShiftBoundary (h : ℝ) : Set ℂ :=
  leftShiftBoundary xiZeroSet h

theorem xiLeftShiftBoundary_infinite {h : ℝ} (hh : 0 < h) :
    (xiLeftShiftBoundary h).Infinite := by
  exact infinite_leftShiftBoundary_of_infinite_in_openUnitStrip
    xiZeroSet_infinite (fun z hz => xiZeroSet_mem_openUnitStrip hz) hh

def xiFluxShiftDifference (h : ℝ) (z : ℂ) : ℂ :=
  seamFluxCochain z - seamFluxCochain (z - (h : ℂ))

theorem not_analyticAt_xiFluxShiftDifference_of_leftBoundary
    {h : ℝ} {ρ : ℂ} (hρ : ρ ∈ xiLeftShiftBoundary h) :
    ¬ AnalyticAt ℂ (xiFluxShiftDifference h) ρ := by
  intro hanalytic
  have hzero : xi ρ = 0 := hρ.1
  have hshift : xi (ρ - (h : ℂ)) ≠ 0 := hρ.2
  have hshiftAn : AnalyticAt ℂ seamFluxCochain (ρ - (h : ℂ)) := by
    have hxi : AnalyticAt ℂ xi (ρ - (h : ℂ)) :=
      xi_analyticOnNhd_univ _ (Set.mem_univ _)
    change AnalyticAt ℂ (fun z => -logDeriv xi z) (ρ - (h : ℂ))
    exact (hxi.deriv.div hxi hshift).neg
  have hshiftComp : AnalyticAt ℂ
      (fun x : ℂ => seamFluxCochain ((ρ + x) - (h : ℂ))) 0 := by
    apply AnalyticAt.comp_of_eq hshiftAn
    · fun_prop
    · ring
  have hdiffComp : AnalyticAt ℂ
      (fun x : ℂ => xiFluxShiftDifference h (ρ + x)) 0 := by
    apply AnalyticAt.comp_of_eq hanalytic
    · fun_prop
    · simp
  have hrhs : AnalyticAt ℂ
      (fun x : ℂ => x *
        (xiFluxShiftDifference h (ρ + x) +
          seamFluxCochain ((ρ + x) - (h : ℂ)))) 0 :=
    analyticAt_id.mul (hdiffComp.add hshiftComp)
  have hnear : completedFluxGermAt ρ =ᶠ[𝓝[≠] 0]
      fun x : ℂ => x *
        (xiFluxShiftDifference h (ρ + x) +
          seamFluxCochain ((ρ + x) - (h : ℂ))) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    rw [completedFluxGermAt, if_neg hx0, xiFluxShiftDifference]
    ring
  have heq : completedFluxGermAt ρ =ᶠ[𝓝 0]
      fun x : ℂ => x *
        (xiFluxShiftDifference h (ρ + x) +
          seamFluxCochain ((ρ + x) - (h : ℂ))) :=
    ((completedFluxGermAt_analyticAt_zero ρ).frequently_eq_iff_eventually_eq hrhs).mp
      hnear.frequently
  have hval := heq.eq_of_nhds
  simp only [completedFluxGermAt_zero, zero_mul] at hval
  have hord : (analyticOrderAt xi ρ).toNat = 0 := by
    exact_mod_cast neg_eq_zero.mp hval
  exact (xi_order_toNat_ne_zero hzero) hord

def xiOrientationFrequencyOfPoint (a : ℝ) (z : ℂ) : ℂ :=
  -I * (z - ((1 : ℂ) / 2 + (a : ℂ)))

theorem xiOrientationFrequencyOfPoint_injective (a : ℝ) :
    Function.Injective (xiOrientationFrequencyOfPoint a) := by
  intro z w h
  have hz : ((1 : ℂ) / 2 + (a : ℂ)) +
      I * xiOrientationFrequencyOfPoint a z = z := by
    rw [xiOrientationFrequencyOfPoint]
    rw [← mul_assoc, show I * -I = (1 : ℂ) by simp]
    ring
  have hw : ((1 : ℂ) / 2 + (a : ℂ)) +
      I * xiOrientationFrequencyOfPoint a w = w := by
    rw [xiOrientationFrequencyOfPoint]
    rw [← mul_assoc, show I * -I = (1 : ℂ) by simp]
    ring
  rw [← hz, ← hw, h]

theorem xiFluxShiftDifference_eq_neg_canonicalOrientation
    (a : ℝ) (z : ℂ) :
    xiFluxShiftDifference (2 * a) z =
      -xiCanonicalHorizontalOrientationMultiplier a
        (xiOrientationFrequencyOfPoint a z) := by
  let c : ℂ := (1 : ℂ) / 2 + (a : ℂ)
  let b : ℂ := xiOrientationFrequencyOfPoint a z
  have hplus : c + b * I = z := by
    dsimp [b, c, xiOrientationFrequencyOfPoint]
    calc
      (1 : ℂ) / 2 + (a : ℂ) +
          -I * (z - ((1 : ℂ) / 2 + (a : ℂ))) * I =
        (1 : ℂ) / 2 + (a : ℂ) +
          ((-I) * I) * (z - ((1 : ℂ) / 2 + (a : ℂ))) := by ring
      _ = z := by rw [show (-I) * I = (1 : ℂ) by simp]; ring
  have hminus : c - b * I = 1 - (z - ((2 * a : ℝ) : ℂ)) := by
    dsimp [b, c, xiOrientationFrequencyOfPoint]
    push_cast
    calc
      (1 : ℂ) / 2 + (a : ℂ) -
          -I * (z - ((1 : ℂ) / 2 + (a : ℂ))) * I =
        (1 : ℂ) / 2 + (a : ℂ) -
          ((-I) * I) * (z - ((1 : ℂ) / 2 + (a : ℂ))) := by ring
      _ = 1 - (z - 2 * (a : ℂ)) := by
        rw [show (-I) * I = (1 : ℂ) by simp]
        ring
  change -logDeriv xi z - -logDeriv xi (z - ((2 * a : ℝ) : ℂ)) =
    -(logDeriv xi (c + b * I) + logDeriv xi (c - b * I))
  rw [hplus, hminus, logDeriv_xi_reciprocity]
  ring

theorem not_analyticAt_canonicalOrientation_of_xiLeftBoundary
    {a : ℝ} {ρ : ℂ} (hρ : ρ ∈ xiLeftShiftBoundary (2 * a)) :
    ¬ AnalyticAt ℂ (xiCanonicalHorizontalOrientationMultiplier a)
      (xiOrientationFrequencyOfPoint a ρ) := by
  intro hQ
  have hinner : AnalyticAt ℂ (xiOrientationFrequencyOfPoint a) ρ := by
    unfold xiOrientationFrequencyOfPoint
    fun_prop
  have hcomp : AnalyticAt ℂ
      (fun z => -xiCanonicalHorizontalOrientationMultiplier a
        (xiOrientationFrequencyOfPoint a z)) ρ :=
    (AnalyticAt.comp_of_eq hQ hinner rfl).neg
  have heq : (fun z => -xiCanonicalHorizontalOrientationMultiplier a
        (xiOrientationFrequencyOfPoint a z)) = xiFluxShiftDifference (2 * a) := by
    funext z
    exact (xiFluxShiftDifference_eq_neg_canonicalOrientation a z).symm
  rw [heq] at hcomp
  exact not_analyticAt_xiFluxShiftDifference_of_leftBoundary hρ hcomp

def xiCanonicalOrientationSingularSet (a : ℝ) : Set ℂ :=
  {b : ℂ | ¬ AnalyticAt ℂ (xiCanonicalHorizontalOrientationMultiplier a) b}

theorem xiCanonicalOrientationSingularSet_infinite
    {a : ℝ} (ha : 0 < a) :
    (xiCanonicalOrientationSingularSet a).Infinite := by
  have hboundary : (xiLeftShiftBoundary (2 * a)).Infinite :=
    xiLeftShiftBoundary_infinite (by linarith)
  let f : ℂ → ℂ := xiOrientationFrequencyOfPoint a
  have himage : (f '' xiLeftShiftBoundary (2 * a)).Infinite :=
    hboundary.image (xiOrientationFrequencyOfPoint_injective a).injOn
  apply himage.mono
  intro b hb
  obtain ⟨ρ, hρ, rfl⟩ := hb
  exact not_analyticAt_canonicalOrientation_of_xiLeftBoundary hρ

end

end RHTower
