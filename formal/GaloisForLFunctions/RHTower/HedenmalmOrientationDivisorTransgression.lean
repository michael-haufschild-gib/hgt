import GaloisForLFunctions.RHTower.HedenmalmOrientationResidues

/-!
# Multiplicity-exact divisor transgression of the Hedenmalm orientation multiplier

The canonical Hedenmalm orientation multiplier is a translated finite difference of the
completed Xi logarithmic current.  Multiplying that difference by a local coordinate gives an
analytic germ at every point, with center value

`ord_Xi(rho - h) - ord_Xi(rho)`.

Thus every nonzero discrete derivative of the Xi multiplicity function forces a nonremovable
orientation singularity.  The positive-translation boundary theorem supplies infinitely many
such order jumps for every positive aperture.  In Hedenmalm's affine frequency coordinate the
residue is the same integer difference multiplied by `-I`.

This strengthens support-only singularity detection: the singular carrier records the exact
discrete divisor derivative, including cancellation when the two local multiplicities agree.
-/

open Complex Set Metric Filter Topology

namespace RHTower

noncomputable section

/-- Removable germ of the translated logarithmic-current difference at an arbitrary point. -/
def xiFluxShiftDifferenceFullResidueGerm (h : ℝ) (rho x : ℂ) : ℂ :=
  completedFluxGermAt rho x -
    completedFluxGermAt (rho - (h : ℂ)) x

/-- The full translated-current residue germ is analytic even when both translated points are
Xi zeros. -/
theorem analyticAt_xiFluxShiftDifferenceFullResidueGerm
    (h : ℝ) (rho : ℂ) :
    AnalyticAt ℂ (xiFluxShiftDifferenceFullResidueGerm h rho) 0 :=
  (completedFluxGermAt_analyticAt_zero rho).sub
    (completedFluxGermAt_analyticAt_zero (rho - (h : ℂ)))

/-- **Divisor-transgression charge.**  The center value is the exact finite difference of Xi
multiplicities across the translation. -/
theorem xiFluxShiftDifferenceFullResidueGerm_zero
    (h : ℝ) (rho : ℂ) :
    xiFluxShiftDifferenceFullResidueGerm h rho 0 =
      (((analyticOrderAt xi (rho - (h : ℂ))).toNat : ℕ) : ℂ) -
        (((analyticOrderAt xi rho).toNat : ℕ) : ℂ) := by
  rw [xiFluxShiftDifferenceFullResidueGerm,
    completedFluxGermAt_zero, completedFluxGermAt_zero]
  ring_nf

/-- Off the center, the removable germ is the local coordinate times the literal translated
logarithmic-current difference. -/
theorem xiFluxShiftDifferenceFullResidueGerm_eventuallyEq
    (h : ℝ) (rho : ℂ) :
    xiFluxShiftDifferenceFullResidueGerm h rho =ᶠ[𝓝[≠] 0]
      fun x : ℂ => x * xiFluxShiftDifference h (rho + x) := by
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  rw [xiFluxShiftDifferenceFullResidueGerm,
    completedFluxGermAt, if_neg hx0,
    completedFluxGermAt, if_neg hx0,
    xiFluxShiftDifference]
  ring_nf

/-- A nonzero divisor-transgression charge is a nonremovable singularity. -/
theorem not_analyticAt_xiFluxShiftDifference_of_charge_ne_zero
    {h : ℝ} {rho : ℂ}
    (hcharge :
      (((analyticOrderAt xi (rho - (h : ℂ))).toNat : ℕ) : ℂ) -
          (((analyticOrderAt xi rho).toNat : ℕ) : ℂ) ≠ 0) :
    ¬ AnalyticAt ℂ (xiFluxShiftDifference h) rho := by
  intro hanalytic
  have hcomp : AnalyticAt ℂ
      (fun x : ℂ => xiFluxShiftDifference h (rho + x)) 0 := by
    apply AnalyticAt.comp_of_eq hanalytic
    · fun_prop
    · simp
  have hrhs : AnalyticAt ℂ
      (fun x : ℂ => x * xiFluxShiftDifference h (rho + x)) 0 :=
    analyticAt_id.mul hcomp
  have hnear := xiFluxShiftDifferenceFullResidueGerm_eventuallyEq h rho
  have hfull := analyticAt_xiFluxShiftDifferenceFullResidueGerm h rho
  have heq : xiFluxShiftDifferenceFullResidueGerm h rho =ᶠ[𝓝 0]
      fun x : ℂ => x * xiFluxShiftDifference h (rho + x) :=
    (hfull.frequently_eq_iff_eventually_eq hrhs).mp hnear.frequently
  have hval := heq.eq_of_nhds
  rw [xiFluxShiftDifferenceFullResidueGerm_zero] at hval
  simp only [zero_mul] at hval
  exact hcharge hval

/-- Different translated Xi multiplicities force nonanalyticity of the current difference. -/
theorem not_analyticAt_xiFluxShiftDifference_of_order_ne
    {h : ℝ} {rho : ℂ}
    (horder :
      (analyticOrderAt xi (rho - (h : ℂ))).toNat ≠
        (analyticOrderAt xi rho).toNat) :
    ¬ AnalyticAt ℂ (xiFluxShiftDifference h) rho := by
  apply not_analyticAt_xiFluxShiftDifference_of_charge_ne_zero
  exact sub_ne_zero.mpr (by exact_mod_cast horder)

/-- Support of the discrete Xi multiplicity derivative under real translation. -/
def xiTranslationOrderJumpSet (h : ℝ) : Set ℂ :=
  {rho : ℂ |
    (analyticOrderAt xi (rho - (h : ℂ))).toNat ≠
      (analyticOrderAt xi rho).toNat}

/-- Every support boundary point is an order jump: the current point has positive multiplicity
and its translated predecessor has multiplicity zero. -/
theorem xiLeftShiftBoundary_subset_translationOrderJumpSet
    (h : ℝ) :
    xiLeftShiftBoundary h ⊆ xiTranslationOrderJumpSet h := by
  intro rho hrho
  change (analyticOrderAt xi (rho - (h : ℂ))).toNat ≠
    (analyticOrderAt xi rho).toNat
  have hshiftOrder : analyticOrderAt xi (rho - (h : ℂ)) = 0 :=
    (xi_analyticOnNhd_univ _ (Set.mem_univ _)).analyticOrderAt_eq_zero.mpr hrho.2
  have hshift : (analyticOrderAt xi (rho - (h : ℂ))).toNat = 0 := by
    rw [hshiftOrder]
    rfl
  rw [hshift]
  exact Ne.symm (xi_order_toNat_ne_zero hrho.1)

/-- **Infinite divisor transgression.**  Every positive real translation has infinitely many Xi
multiplicity jumps. -/
theorem xiTranslationOrderJumpSet_infinite
    {h : ℝ} (hh : 0 < h) :
    (xiTranslationOrderJumpSet h).Infinite :=
  (xiLeftShiftBoundary_infinite hh).mono
    (xiLeftShiftBoundary_subset_translationOrderJumpSet h)

/-- Singular support of the translated Xi logarithmic current. -/
def xiFluxShiftDifferenceSingularSet (h : ℝ) : Set ℂ :=
  {rho : ℂ | ¬ AnalyticAt ℂ (xiFluxShiftDifference h) rho}

/-- Every multiplicity jump belongs to the singular support. -/
theorem xiTranslationOrderJumpSet_subset_fluxShiftDifferenceSingularSet
    (h : ℝ) :
    xiTranslationOrderJumpSet h ⊆ xiFluxShiftDifferenceSingularSet h := by
  intro rho hrho
  exact not_analyticAt_xiFluxShiftDifference_of_order_ne hrho

/-- Every positive translated Xi current has infinite singular support. -/
theorem xiFluxShiftDifferenceSingularSet_infinite
    {h : ℝ} (hh : 0 < h) :
    (xiFluxShiftDifferenceSingularSet h).Infinite :=
  (xiTranslationOrderJumpSet_infinite hh).mono
    (xiTranslationOrderJumpSet_subset_fluxShiftDifferenceSingularSet h)

/-- The multiplicity-exact residue germ in the affine Hedenmalm frequency coordinate. -/
def xiCanonicalOrientationDivisorTransgressionGerm
    (a : ℝ) (rho x : ℂ) : ℂ :=
  I * xiFluxShiftDifferenceFullResidueGerm (2 * a) rho x

theorem analyticAt_xiCanonicalOrientationDivisorTransgressionGerm
    (a : ℝ) (rho : ℂ) :
    AnalyticAt ℂ
      (xiCanonicalOrientationDivisorTransgressionGerm a rho) 0 :=
  analyticAt_const.mul
    (analyticAt_xiFluxShiftDifferenceFullResidueGerm (2 * a) rho)

/-- The Hedenmalm residue is `-I` times the exact translated multiplicity difference. -/
theorem xiCanonicalOrientationDivisorTransgressionGerm_zero
    (a : ℝ) (rho : ℂ) :
    xiCanonicalOrientationDivisorTransgressionGerm a rho 0 =
      -I *
        ((((analyticOrderAt xi rho).toNat : ℕ) : ℂ) -
          (((analyticOrderAt xi (rho - ((2 * a : ℝ) : ℂ))).toNat : ℕ) : ℂ)) := by
  rw [xiCanonicalOrientationDivisorTransgressionGerm,
    xiFluxShiftDifferenceFullResidueGerm_zero]
  ring_nf

/-- Punctured-neighborhood identification with the canonical orientation multiplier. -/
theorem xiCanonicalOrientationDivisorTransgressionGerm_eventuallyEq
    (a : ℝ) (rho : ℂ) :
    xiCanonicalOrientationDivisorTransgressionGerm a rho =ᶠ[𝓝[≠] 0]
      fun x : ℂ =>
        (xiOrientationFrequencyOfPoint a (rho + x) -
          xiOrientationFrequencyOfPoint a rho) *
            xiCanonicalHorizontalOrientationMultiplier a
              (xiOrientationFrequencyOfPoint a (rho + x)) := by
  filter_upwards
    [xiFluxShiftDifferenceFullResidueGerm_eventuallyEq (2 * a) rho]
      with x hx
  rw [xiCanonicalOrientationDivisorTransgressionGerm, hx,
    xiFluxShiftDifference_eq_neg_canonicalOrientation]
  have hfreq : xiOrientationFrequencyOfPoint a (rho + x) -
      xiOrientationFrequencyOfPoint a rho = -I * x := by
    unfold xiOrientationFrequencyOfPoint
    ring_nf
  rw [hfreq]
  ring_nf

/-- An order jump forces a singularity of the canonical Hedenmalm orientation multiplier. -/
theorem not_analyticAt_canonicalOrientation_of_order_ne
    {a : ℝ} {rho : ℂ}
    (horder :
      (analyticOrderAt xi (rho - ((2 * a : ℝ) : ℂ))).toNat ≠
        (analyticOrderAt xi rho).toNat) :
    ¬ AnalyticAt ℂ (xiCanonicalHorizontalOrientationMultiplier a)
      (xiOrientationFrequencyOfPoint a rho) := by
  intro hQ
  have hinner : AnalyticAt ℂ (xiOrientationFrequencyOfPoint a) rho := by
    unfold xiOrientationFrequencyOfPoint
    fun_prop
  have hcomp : AnalyticAt ℂ
      (fun z => -xiCanonicalHorizontalOrientationMultiplier a
        (xiOrientationFrequencyOfPoint a z)) rho :=
    (AnalyticAt.comp_of_eq hQ hinner rfl).neg
  have heq : (fun z => -xiCanonicalHorizontalOrientationMultiplier a
        (xiOrientationFrequencyOfPoint a z)) = xiFluxShiftDifference (2 * a) := by
    funext z
    exact (xiFluxShiftDifference_eq_neg_canonicalOrientation a z).symm
  rw [heq] at hcomp
  exact not_analyticAt_xiFluxShiftDifference_of_order_ne horder hcomp

/-- Affine frequency image of the complete translated multiplicity-jump carrier. -/
def xiCanonicalOrientationOrderJumpFrequencySet (a : ℝ) : Set ℂ :=
  xiOrientationFrequencyOfPoint a '' xiTranslationOrderJumpSet (2 * a)

/-- The multiplicity-jump frequency carrier is infinite at every positive aperture. -/
theorem xiCanonicalOrientationOrderJumpFrequencySet_infinite
    {a : ℝ} (ha : 0 < a) :
    (xiCanonicalOrientationOrderJumpFrequencySet a).Infinite := by
  apply (xiTranslationOrderJumpSet_infinite (show 0 < 2 * a by linarith)).image
  exact (xiOrientationFrequencyOfPoint_injective a).injOn

/-- Every order-jump frequency is a singular frequency of the canonical multiplier. -/
theorem xiCanonicalOrientationOrderJumpFrequencySet_subset_singularSet
    (a : ℝ) :
    xiCanonicalOrientationOrderJumpFrequencySet a ⊆
      xiCanonicalOrientationSingularSet a := by
  rintro b ⟨rho, horder, rfl⟩
  exact not_analyticAt_canonicalOrientation_of_order_ne horder

/-- The canonical multiplier has infinite singular support, now through the multiplicity-exact
transgression carrier rather than support boundary alone. -/
theorem xiCanonicalOrientationSingularSet_infinite_via_orderTransgression
    {a : ℝ} (ha : 0 < a) :
    (xiCanonicalOrientationSingularSet a).Infinite :=
  (xiCanonicalOrientationOrderJumpFrequencySet_infinite ha).mono
    (xiCanonicalOrientationOrderJumpFrequencySet_subset_singularSet a)

end

end RHTower
