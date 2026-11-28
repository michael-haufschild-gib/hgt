import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrefixCouplings.Resampling
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-! # Disintegrating a finite Gaussian field along a unit direction -/

open MeasureTheory ProbabilityTheory WithLp Set
open scoped ENNReal InnerProductSpace
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.SpectralShape
noncomputable section

/-- Reflection turns a coordinate resampling into integration over lines of
arbitrary unit direction. The same base map works for every measurable event. -/
theorem gaussian_sections {I : Type*} [Fintype I] [DecidableEq I] (i : I)
    (v : EuclideanSpace ℝ I) (hv : ‖v‖=1) :
    ∃ Y : (I→ℝ) → EuclideanSpace ℝ I, ∀ S : Set (EuclideanSpace ℝ I), MeasurableSet S →
      stdGaussian (EuclideanSpace ℝ I) S =
        ∫⁻ h, gaussianReal 0 1 {x : ℝ | Y h+x • v∈S} ∂(Measure.pi fun _ => gaussianReal 0 1) := by
  let γ := gaussianReal 0 1
  let μ := Measure.pi (fun _ : I => γ)
  let E := EuclideanSpace ℝ I
  let e : E := EuclideanSpace.single i 1
  let R : E ≃ₗᵢ[ℝ] E := Submodule.reflection (ℝ ∙ (e-v))ᗮ
  have he : ‖e‖=1 :=
    (PiLp.norm_single 2 (fun _ : I => ℝ) i 1).trans (norm_one : ‖(1:ℝ)‖=1)
  have hRv : R e=v := Submodule.reflection_sub (he.trans hv.symm)
  have hT : MeasurePreserving (toLp 2 : (I→ℝ) → E) μ (stdGaussian E) :=
    ⟨(MeasurableEquiv.toLp 2 (I→ℝ)).measurable,map_pi_eq_stdGaussian⟩
  have hR : MeasurePreserving R (stdGaussian E) (stdGaussian E) :=
    ⟨R.continuous.measurable,stdGaussian_map R⟩
  have hU := PrefixCouplings.resample_preserving γ i
  simp only [Measure.infinitePi_eq_pi] at hU
  have hP := hR.comp (hT.comp hU)
  refine ⟨fun h => R (toLp 2 (Function.update h i 0)),?_⟩
  intro S hS
  rw [←hP.measure_preimage hS.nullMeasurableSet,Measure.prod_apply (hS.preimage hP.measurable)]
  apply lintegral_congr
  intro h
  have hsplit (x : ℝ) : toLp 2 (Function.update h i x) =
      toLp 2 (Function.update h i 0)+x • e := by
    ext j
    change Function.update h i x j = Function.update h i 0 j+x*((Pi.single i 1 : I → ℝ) j)
    by_cases hj : j=i
    · subst j
      simp
    · simp [hj]
  apply congrArg γ
  ext x
  change R (toLp 2 (Function.update h i x))∈S ↔ R (toLp 2 (Function.update h i 0))+x • v∈S
  rw [hsplit x,map_add,map_smul,hRv]

/-- A uniform line estimate retains the probability of every measurable
conditioning event invariant under translations in the chosen direction. -/
theorem conditional_line_bound {I : Type*} [Fintype I] [DecidableEq I] (i : I)
    (v : EuclideanSpace ℝ I) (hv : ‖v‖=1) (S B : Set (EuclideanSpace ℝ I))
    (hS : MeasurableSet S) (hB : MeasurableSet B) (b : ℝ≥0∞) (hb : b≠∞)
    (hinv : ∀ y : EuclideanSpace ℝ I, ∀ t : ℝ, y+t • v∈B ↔ y∈B)
    (hline : ∀ y∈B, gaussianReal 0 1 {x : ℝ | y+x • v∈S} ≤ b) :
    stdGaussian (EuclideanSpace ℝ I) (S ∩ B) ≤ b*stdGaussian (EuclideanSpace ℝ I) B := by
  obtain ⟨Y,hY⟩ := gaussian_sections i v hv
  rw [hY _ (hS.inter hB),hY _ hB,←lintegral_const_mul' b _ hb]
  apply lintegral_mono
  intro h
  dsimp only
  by_cases hy : Y h∈B
  · have hall : {x : ℝ | Y h+x • v∈B}=univ :=
      eq_univ_of_forall fun x => (hinv _ x).mpr hy
    rw [hall,measure_univ,mul_one]
    exact (measure_mono (fun _ hx => hx.1)).trans (hline (Y h) hy)
  · have hnone : {x : ℝ | Y h+x • v∈S ∩ B}=∅ :=
      eq_empty_iff_forall_notMem.mpr fun x hx => hy ((hinv _ x).mp hx.2)
    rw [hnone,measure_empty]
    exact zero_le

#print axioms conditional_line_bound
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.SpectralShape
