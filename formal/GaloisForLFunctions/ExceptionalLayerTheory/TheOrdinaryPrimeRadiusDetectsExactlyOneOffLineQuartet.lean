import GaloisForLFunctions.ExceptionalLayerTheory.TwoIntervalQuartetAmplitudeAndOrdinaryPrimeObstruction
import GaloisForLFunctions.ExceptionalLayerTheory.WeightedPrimeIncrementsExcludeEveryLowerRightZero

/-!
# The ordinary-prime radius detects a single off-line quartet

A bounded trial pins the abscissa and forces a finite off-line divisor.
The finite-divisor amplitude classification then applies to every trial.
-/

noncomputable section
open RHTower Complex
open GaloisForLFunctions.ZeroConfigurationGeometry
open GaloisForLFunctions.ExclusionOfTheCriticalState
namespace GaloisForLFunctions.ExceptionalLayerTheory

private theorem backlund_finite_of_copies
    (hf : {q : XiZeroCopy | (q.1 : ℂ).re ≠ 1/2}.Finite) : BacklundConverse.FiniteOffLine := by
  apply hf.subset
  intro q hq he
  apply hq
  have him : (xiSpectralPoint q).im = 1/2-(q.1 : ℂ).re := by
    simp [xiSpectralPoint, Complex.mul_im]
  rw [him,he,sub_self]

private theorem finiteOffLine_of_bounded_trial {β γ : ℝ} {m : ℕ}
    (hβ : 1/2 < β) (hβ1 : β < 1) (hγ : γ ≠ 0) (hm : 1 ≤ m)
    (hb : ¬ IsLogSqrtSqUnbounded (thetaRadialDiscrepancy β γ m)) : BacklundConverse.FiniteOffLine := by
  have he : β = zetaZeroAbscissa := by
    by_contra hne
    exact hb (thetaRadial_unbounded_of_ne_zetaZeroAbscissa hβ hβ1 hγ hm hne)
  subst β
  exact backlund_finite_of_copies (finite_offLine_copies_of_bounded_radius hβ hγ hm hb)

/-- A bounded amplitude trial detects an actual single quartet with the
odd-harmonic frequency and multiplicity relation, for arbitrary zero divisors. -/
theorem not_radialUnbounded_iff_singleQuartet_alias {β γ : ℝ} {m : ℕ}
    (hβ : 1/2 < β) (hβ1 : β < 1) (hγ : 0 < γ) (hm : 1 ≤ m) :
    ¬ IsLogSqrtSqUnbounded (thetaRadialDiscrepancy β γ m) ↔
      ∃ k : ℕ, HasSingleOffLineQuartet ((β:ℂ)+I*(((2*(k:ℝ)+1)*γ:ℝ):ℂ)) ∧
        IsOddHarmonicPythagoreanAlias β γ m ((2*(k:ℝ)+1)*γ)
          (quartetCopyMult ((β:ℂ)+I*(((2*(k:ℝ)+1)*γ:ℝ):ℂ))) k := by
  constructor
  · intro hb
    exact (finiteOffLine_not_radialUnbounded_iff
      (finiteOffLine_of_bounded_trial hβ hβ1 hγ.ne' hm hb) hβ hβ1 hγ hm).mp hb
  · rintro ⟨k,hq,ha⟩
    exact (finiteOffLine_not_radialUnbounded_iff hq.finiteOffLine hβ hβ1 hγ hm).mpr ⟨k,hq,ha⟩

/-- Across arbitrary zero configurations, the full radial exclusion law is
equivalent to exclusion of an actual single off-line quartet. -/
theorem twoIntervalRadialExclusionLaw_iff_no_singleQuartet :
    TwoIntervalRadialExclusionLaw ↔ ∀ ρ : ℂ, ¬ HasSingleOffLineQuartet ρ := by
  constructor
  · intro hlaw
    exact (corollaries_of_twoIntervalRadialExclusionLaw hlaw).1
  · intro hno β γ m hβ hβ1 hγ hm
    by_contra hb
    have hf := finiteOffLine_of_bounded_trial hβ hβ1 hγ hm hb
    have h := (finiteOffLine_twoIntervalRadialExclusionLaw_iff hf).mpr
      (no_singleOffLineQuartet_iff_rh_or_four_le_rightZeros.mp hno)
    exact hb (h β γ m hβ hβ1 hγ hm)

#print axioms not_radialUnbounded_iff_singleQuartet_alias
#print axioms twoIntervalRadialExclusionLaw_iff_no_singleQuartet

end GaloisForLFunctions.ExceptionalLayerTheory
