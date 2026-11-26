import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.GaussianDilation
import Mathlib.MeasureTheory.Integral.Prod

/-! # Gaussian comparison under expansion of a chosen set of couplings -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.BlockDilations
noncomputable section

private abbrev law (ι : Type*) [Fintype ι] := Measure.pi fun _ : ι => gaussianReal 0 1

private theorem first_factor {ι Y : Type*} [Fintype ι] [MeasurableSpace Y]
    (ν : Measure Y) [IsProbabilityMeasure ν] {a : ℝ} (ha : 1≤a)
    {E : Set ((ι→ℝ) × Y)} (hE : MeasurableSet E) :
    ((law ι).prod ν).real E ≤ a^(Fintype.card ι)*
      ((law ι).prod ν).real ((fun p => (a • p.1,p.2)) ⁻¹' E) := by
  let μ := law ι
  let F := (fun p : (ι→ℝ) × Y => (a • p.1,p.2)) ⁻¹' E
  have hF : MeasurableSet F := hE.preimage ((measurable_fst.const_smul a).prodMk measurable_snd)
  let c := a^(Fintype.card ι)
  have hc : 0≤c := pow_nonneg (zero_le_one.trans ha) _
  have h (y : Y) : μ ((fun x => (x,y)) ⁻¹' E) ≤
      ENNReal.ofReal c*μ ((fun x => (x,y)) ⁻¹' F) := by
    have hh := PrescribedTimes.gaussian_dilation_comparison ha ((fun x => (x,y)) ⁻¹' E)
      (hE.preimage (measurable_id.prodMk measurable_const))
    have hs := ENNReal.ofReal_le_ofReal hh
    change ENNReal.ofReal (μ ((fun x => (x,y)) ⁻¹' E)).toReal ≤
      ENNReal.ofReal (c*(μ ((fun x => (x,y)) ⁻¹' F)).toReal) at hs
    rwa [ENNReal.ofReal_mul hc,ENNReal.ofReal_toReal (measure_ne_top _ _),
      ENNReal.ofReal_toReal (measure_ne_top _ _)] at hs
  have hprod : μ.prod ν E ≤ ENNReal.ofReal c*(μ.prod ν F) := by
    rw [Measure.prod_apply_symm hE,Measure.prod_apply_symm hF,←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_mono h
  have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) hprod
  change (μ.prod ν E).toReal ≤ c*(μ.prod ν F).toReal
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal hc] using hh

/-- Multiply the specified coordinates by a common factor. -/
def expand {ι : Type*} [DecidableEq ι] (S : Finset ι) (a : ℝ) (x : ι→ℝ) (i : ι) : ℝ :=
  if i∈S then a*x i else x i

/-- Expanding any selected coordinates preserves at least the reciprocal
Jacobian fraction of the original mass of every measurable event. -/
theorem selected_gaussian_comparison {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) {a : ℝ} (ha : 1≤a) {E : Set (ι→ℝ)} (hE : MeasurableSet E) :
    (law ι).real E ≤ a^S.card*(law ι).real (expand S a ⁻¹' E) := by
  letI : Fintype ↥S := Subtype.fintype (fun i : ι => i∈S)
  letI : Fintype {i : ι // i∉S} := Subtype.fintype (fun i : ι => i∉S)
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) (·∈S)
  let B := e.symm ⁻¹' E
  have hB : MeasurableSet B := hE.preimage e.symm.measurable
  let D := fun p : (S→ℝ) × ({i : ι // i∉S}→ℝ) => (a • p.1,p.2)
  have hD : Measurable D := (measurable_fst.const_smul a).prodMk measurable_snd
  have hfun (x : ι→ℝ) : e (expand S a x)=D (e x) := by
    apply Prod.ext
    · funext i; exact if_pos i.2
    · funext i; exact if_neg i.2
  have hp := measurePreserving_piEquivPiSubtypeProd (fun _ : ι => gaussianReal 0 1) (·∈S)
  have h₁ := hp.measureReal_preimage hB.nullMeasurableSet
  have h₂ := hp.measureReal_preimage ((hB.preimage hD).nullMeasurableSet)
  have hpre : e ⁻¹' B=E := by ext x; change e.symm (e x)∈E ↔ _; rw [e.symm_apply_apply]
  have hpre' : e ⁻¹' (D ⁻¹' B)=expand S a ⁻¹' E := by
    ext x; change e.symm (D (e x))∈E ↔ _; rw [←hfun,e.symm_apply_apply]; rfl
  change (law ι).real (e ⁻¹' B)=_ at h₁
  change (law ι).real (e ⁻¹' (D ⁻¹' B))=_ at h₂
  rw [hpre] at h₁
  rw [hpre'] at h₂
  have hcard : Fintype.card ↥S=S.card := (Fintype.card_congr S.equivFin).trans (Fintype.card_fin _)
  rw [h₁,h₂]
  simpa only [law,D,hcard] using first_factor (ι:=↥S) (law {i : ι // i∉S}) ha hB

#print axioms selected_gaussian_comparison
end
end GaloisForLFunctions.HTGeometry.BlockDilations
