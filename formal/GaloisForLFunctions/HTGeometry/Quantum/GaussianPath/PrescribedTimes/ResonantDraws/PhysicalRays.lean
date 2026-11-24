import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.DilationAverage
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.CrossingOrigin

/-! # Sampling a single orbit from a covariant physical time origin -/
open MeasureTheory ProbabilityTheory Set
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws
noncomputable section

private theorem equal_interval_mass {a b : ℝ} {S T : Set ℝ}
    (h : ∀ u ∈ Icc a b, u ∈ S ↔ u ∈ T) :
    (volume.restrict (Icc a b)).real S = (volume.restrict (Icc a b)).real T := by
  have he : S ∩ Icc a b = T ∩ Icc a b := Set.ext fun u => by
    by_cases hu : u∈Icc a b
    · exact and_congr_left' (h u hu)
    · simp only [mem_inter_iff,hu,and_false]
  rw [measureReal_restrict_apply' measurableSet_Icc,measureReal_restrict_apply' measurableSet_Icc,he]

/-- Dilation from one to b samples the physical orbit at delays at.
The identity holds also when the origin is chosen from the same sample. -/
theorem rayMass_of_covariant_origin (n s : ℕ) (o : (PrefixIndex n → ℝ) → ℝ)
    (hcov : ∀ a > (0:ℝ), ∀ x, a*o (a • x)=o x) (x : PrefixIndex n → ℝ) (b t e : ℝ) :
    rayMass b {y | pathGateDistance n s y (o y+t) ≤ e} x =
      (volume.restrict (Icc 1 b)).real ((fun a : ℝ => a*t) ⁻¹'
        {v | pathGateDistance n s x (o x+v) ≤ e}) := by
  unfold rayMass
  apply equal_interval_mass
  intro a ha
  change (pathGateDistance n s (a • x) (o (a • x)+t) ≤ e) ↔
    pathGateDistance n s x (o x+a*t) ≤ e
  rw [distance_dilate,mul_add,hcov a (zero_lt_one.trans_le ha.1) x]

/-- A bounded occupation outside an exceptional set of outer mass β
has mean at most its good-set bound plus β. -/
theorem mean_of_exception {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : Measurable f) (h₀ : ∀ x, 0≤f x) (h₁ : ∀ x, f x≤1)
    (B : Set Ω) {q β : ℝ} (hq : 0≤q) (hb : μ B ≤ ENNReal.ofReal β) (hβ : 0≤β)
    (h : ∀ᵐ ω ∂μ, ω ∉ B → f ω≤q) : ∫ ω, f ω ∂μ ≤ q+β := by
  classical
  let S := {ω | q < f ω}
  have hS : MeasurableSet S := measurableSet_lt measurable_const hf
  have hm : μ S ≤ μ B := measure_mono_ae (h.mono fun ω hw hx => by
    by_contra hz; exact (hw hz).not_gt hx)
  have hs : μ.real S ≤ β := (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hm.trans hb)).trans_eq
    (ENNReal.toReal_ofReal hβ)
  let g := S.indicator (fun _ => (1:ℝ))
  have hg : Integrable g μ := (integrable_const _).indicator hS
  have hi : Integrable f μ := Integrable.of_bound hf.aestronglyMeasurable 1
    (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs,abs_of_nonneg (h₀ ω)] using h₁ ω)
  have hh := integral_mono hi ((integrable_const q).add hg) (fun ω => by
    change f ω ≤ q+g ω
    by_cases hω : ω∈S
    · rw [show g ω=1 from indicator_of_mem hω _]; linarith only [hq,h₁ ω]
    · rw [show g ω=0 from indicator_of_notMem hω _,add_zero]; exact le_of_not_gt hω)
  calc
    _ ≤ ∫ ω, q+g ω ∂μ := hh
    _ = q+μ.real S := by rw [integral_add (integrable_const _) hg,integral_const,probReal_univ,one_smul,
      show (∫ ω, g ω ∂μ)=μ.real S from integral_indicator_one hS]
    _ ≤ _ := add_le_add le_rfl hs

#print axioms rayMass_of_covariant_origin
#print axioms mean_of_exception
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws
