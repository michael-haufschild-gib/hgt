import GaloisForLFunctions.RHTower.FokasLenellsCauchyLinfty
import GaloisForLFunctions.RHTower.FokasLenellsMixedOperator
import GaloisForLFunctions.RHTower.FokasLenellsSecondTimeMultiplier

/-!
# Actual scattering generators as ordinary L-infinity symbols

The existing uniform bounds put each genuine scalar generator in L-infinity.
Their Holder representations recover the existing operators and their exact
norms. All membership and boundedness proofs are supplied internally.
-/

open MeasureTheory
open scoped ENNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

private theorem actualMultiplier_eq_linfty (T : SoninL2 →L[ℂ] SoninL2)
    (φ : ℝ → ℂ) (g : Lp ℂ ∞ (volume : Measure ℝ))
    (hT : ∀ u : SoninL2, (T u : ℝ → ℂ) =ᵐ[volume] fun z => φ z*u z)
    (hg : (g : ℝ → ℂ) =ᵐ[volume] φ) : T = lineLinftyMultiplier g := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [hT u, lineLinftyMultiplier_ae g u, hg] with z h0 h1 h2
  rw [h0, h1, h2]

/-- The actual direct generator as an ordinary L-infinity equivalence class. -/
def directLinftySymbol (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    Lp ℂ ∞ (volume : Measure ℝ) :=
  (memLp_top_of_bound (directSymbol_measurable q t x reverse).aestronglyMeasurable
    ((1/3 : ℝ)) (.of_forall (directSymbol_bound q t x reverse))).toLp _

/-- The class retains the actual pointwise generator almost everywhere. -/
theorem directLinftySymbol_ae (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    (directLinftySymbol q t x reverse : ℝ → ℂ) =ᵐ[volume] directSymbol q t x reverse :=
  (memLp_top_of_bound (directSymbol_measurable q t x reverse).aestronglyMeasurable
    ((1/3 : ℝ)) (.of_forall (directSymbol_bound q t x reverse))).coeFn_toLp

/-- The existing direct multiplier is exactly the Holder representation of its symbol. -/
theorem directMultiplier_eq_lineLinftyMultiplier (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    directMultiplier q t x reverse = lineLinftyMultiplier (directLinftySymbol q t x reverse) :=
  actualMultiplier_eq_linfty _ _ _ (directMultiplier_ae q t x reverse) (directLinftySymbol_ae q t x reverse)

/-- The actual direct operator norm is exactly its symbol's essential-supremum norm. -/
theorem norm_directMultiplier_eq_linfty (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    ‖directMultiplier q t x reverse‖ = ‖directLinftySymbol q t x reverse‖ := by
  rw [directMultiplier_eq_lineLinftyMultiplier, norm_lineLinftyMultiplier]

/-- The actual directTime generator as an ordinary L-infinity equivalence class. -/
def directTimeLinftySymbol (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    Lp ℂ ∞ (volume : Measure ℝ) :=
  (memLp_top_of_bound (directTimeSymbol_measurable q t x reverse).aestronglyMeasurable
    (((1/2 : ℝ)*regularReflectionFrequencyBudget q)) (.of_forall (directTimeSymbol_bound q t x reverse))).toLp _

/-- The class retains the actual pointwise generator almost everywhere. -/
theorem directTimeLinftySymbol_ae (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    (directTimeLinftySymbol q t x reverse : ℝ → ℂ) =ᵐ[volume] directTimeSymbol q t x reverse :=
  (memLp_top_of_bound (directTimeSymbol_measurable q t x reverse).aestronglyMeasurable
    (((1/2 : ℝ)*regularReflectionFrequencyBudget q)) (.of_forall (directTimeSymbol_bound q t x reverse))).coeFn_toLp

/-- The existing directTime multiplier is exactly the Holder representation of its symbol. -/
theorem directTimeMultiplier_eq_lineLinftyMultiplier (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    directTimeMultiplier q t x reverse = lineLinftyMultiplier (directTimeLinftySymbol q t x reverse) :=
  actualMultiplier_eq_linfty _ _ _ (directTimeMultiplier_ae q t x reverse) (directTimeLinftySymbol_ae q t x reverse)

/-- The actual directTime operator norm is exactly its symbol's essential-supremum norm. -/
theorem norm_directTimeMultiplier_eq_linfty (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    ‖directTimeMultiplier q t x reverse‖ = ‖directTimeLinftySymbol q t x reverse‖ := by
  rw [directTimeMultiplier_eq_lineLinftyMultiplier, norm_lineLinftyMultiplier]

/-- The actual directSpace generator as an ordinary L-infinity equivalence class. -/
def directSpaceLinftySymbol (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    Lp ℂ ∞ (volume : Measure ℝ) :=
  (memLp_top_of_bound (directSpaceSymbol_measurable q t x reverse).aestronglyMeasurable
    (directSpaceOperatorBudget q) (.of_forall (directSpaceSymbol_uniform_bound q t x reverse))).toLp _

/-- The class retains the actual pointwise generator almost everywhere. -/
theorem directSpaceLinftySymbol_ae (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    (directSpaceLinftySymbol q t x reverse : ℝ → ℂ) =ᵐ[volume] directSpaceSymbol q t x reverse :=
  (memLp_top_of_bound (directSpaceSymbol_measurable q t x reverse).aestronglyMeasurable
    (directSpaceOperatorBudget q) (.of_forall (directSpaceSymbol_uniform_bound q t x reverse))).coeFn_toLp

/-- The existing directSpace multiplier is exactly the Holder representation of its symbol. -/
theorem directSpaceMultiplier_eq_lineLinftyMultiplier (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    directSpaceMultiplier q t x reverse = lineLinftyMultiplier (directSpaceLinftySymbol q t x reverse) :=
  actualMultiplier_eq_linfty _ _ _ (directSpaceMultiplier_ae q t x reverse) (directSpaceLinftySymbol_ae q t x reverse)

/-- The actual directSpace operator norm is exactly its symbol's essential-supremum norm. -/
theorem norm_directSpaceMultiplier_eq_linfty (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    ‖directSpaceMultiplier q t x reverse‖ = ‖directSpaceLinftySymbol q t x reverse‖ := by
  rw [directSpaceMultiplier_eq_lineLinftyMultiplier, norm_lineLinftyMultiplier]

/-- The actual compatibleSecondTime generator as an ordinary L-infinity equivalence class. -/
def compatibleSecondTimeLinftySymbol (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    Lp ℂ ∞ (volume : Measure ℝ) :=
  (memLp_top_of_bound (directSecondTimeSymbol_measurable (oddInitialPart q) t x reverse).aestronglyMeasurable
    (compatibleSecondTimeBudget q reverse) (.of_forall (directSecondTimeSymbol_oddInitialPart_bound q t x reverse))).toLp _

/-- The class retains the actual pointwise generator almost everywhere. -/
theorem compatibleSecondTimeLinftySymbol_ae (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    (compatibleSecondTimeLinftySymbol q t x reverse : ℝ → ℂ) =ᵐ[volume] directSecondTimeSymbol (oddInitialPart q) t x reverse :=
  (memLp_top_of_bound (directSecondTimeSymbol_measurable (oddInitialPart q) t x reverse).aestronglyMeasurable
    (compatibleSecondTimeBudget q reverse) (.of_forall (directSecondTimeSymbol_oddInitialPart_bound q t x reverse))).coeFn_toLp

/-- The existing compatibleSecondTime multiplier is exactly the Holder representation of its symbol. -/
theorem compatibleSecondTimeMultiplier_eq_lineLinftyMultiplier (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    compatibleSecondTimeMultiplier q t x reverse = lineLinftyMultiplier (compatibleSecondTimeLinftySymbol q t x reverse) :=
  actualMultiplier_eq_linfty _ _ _ (compatibleSecondTimeMultiplier_ae q t x reverse) (compatibleSecondTimeLinftySymbol_ae q t x reverse)

/-- The actual compatibleSecondTime operator norm is exactly its symbol's essential-supremum norm. -/
theorem norm_compatibleSecondTimeMultiplier_eq_linfty (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    ‖compatibleSecondTimeMultiplier q t x reverse‖ = ‖compatibleSecondTimeLinftySymbol q t x reverse‖ := by
  rw [compatibleSecondTimeMultiplier_eq_lineLinftyMultiplier, norm_lineLinftyMultiplier]

/-- Cauchy compression preserves the exact norm of this genuine scalar generator. -/
theorem norm_negativeCauchy_comp_directSpaceMultiplier (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    ‖negativeCauchy.comp (directSpaceMultiplier q t x reverse)‖ = ‖directSpaceMultiplier q t x reverse‖ := by
  rw [directSpaceMultiplier_eq_lineLinftyMultiplier,
    norm_negativeCauchy_comp_lineLinftyMultiplier, norm_lineLinftyMultiplier]

/-- Cauchy compression preserves the exact norm of this genuine scalar generator. -/
theorem norm_negativeCauchy_comp_compatibleSecondTimeMultiplier (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    ‖negativeCauchy.comp (compatibleSecondTimeMultiplier q t x reverse)‖ = ‖compatibleSecondTimeMultiplier q t x reverse‖ := by
  rw [compatibleSecondTimeMultiplier_eq_lineLinftyMultiplier,
    norm_negativeCauchy_comp_lineLinftyMultiplier, norm_lineLinftyMultiplier]

end
end RHTower.FokasLenells
