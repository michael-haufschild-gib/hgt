import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.CenteredOccupation.ResonanceGenerator
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.Weyl
import GaloisForLFunctions.HTGeometry.ActivePhaseLattice
import GaloisForLFunctions.HTGeometry.CompletedTimeBohrMean

/-! # A short transverse phase segment removes the unique clock resonance -/

open Filter MeasureTheory Real Topology
namespace GaloisForLFunctions.HTGeometry.AdaptiveSampling.CenteredOccupation
noncomputable section
variable {I : Type} [Fintype I]

def transverseLaw (v : I → ℝ) (B : ℝ) : ProbabilityMeasure (UnitAddTorus I) :=
  finiteClockSampledPhaseProbabilityMeasure (centeredUniformClockProbabilityMeasure (π/B)) v

private theorem transverse_character (m : I → ℤ) (v : I → ℝ) {B : ℝ} (hB : B≠0)
    (hdet : finiteTorusCharacterDetuning m v=B) {a : ℤ} (ha : a≠0) :
    ∫ x, UnitAddTorus.mFourier (fun i => a*m i) x ∂(transverseLaw v B : Measure _)=0 := by
  have hd : finiteTorusCharacterDetuning (fun i => a*m i) v=(a:ℝ)*B := by
    rw [←hdet]
    simp only [finiteTorusCharacterDetuning,Int.cast_mul,Finset.mul_sum,mul_assoc]
  rw [transverseLaw,finiteClockSampledPhaseProbabilityMeasure_mFourier_integral,
    charFun_centeredUniformClockProbabilityMeasure,hd]
  have he : π/B*((a:ℝ)*B)=(a:ℝ)*π := by field_simp
  rw [he,sinc_of_ne_zero (mul_ne_zero (by exact_mod_cast ha) pi_ne_zero),sin_int_mul_pi,
    zero_div,Complex.ofReal_zero]

/-- A tick perturbed along a segment of half-length π/B in direction v. -/
def perturbedLaw (ω : I → ℝ) (a τ : ℝ) (v : I → ℝ) (B : ℝ) (N : ℕ) : ProbabilityMeasure (UnitAddTorus I) :=
  let ν := integerClockPrefixLaw (fun n => finiteClockPhasePoint ω (a+(n:ℝ)*τ)) N
  ⟨(ν : Measure _) ∗ (transverseLaw v B : Measure _),inferInstance⟩

/-- One full turn in the unique resonant character restores Haar
distribution. The perturbation may be confined to a few coordinates. -/
theorem transverse_haar (ω : I → ℝ) (a τ : ℝ) (m : I → ℤ) (v : I → ℝ)
    {B : ℝ} (hB : B≠0) (hdet : finiteTorusCharacterDetuning m v=B)
    (hgen : ∀ (w : I → ℤ) (k : ℤ), τ*finiteTorusCharacterDetuning w ω=(k:ℝ)*(2*π) →
      ∃ l : ℤ, w=fun i => l*m i) :
    Tendsto (perturbedLaw ω a τ v B) atTop (𝓝 (finiteTorusHaarProbabilityMeasure I)) := by
  classical
  apply probabilityMeasure_tendsto_of_mFourier_integral_tendsto
  intro w
  rw [finiteTorusHaarProbabilityMeasure_mFourier_integral]
  by_cases hw : w=0
  · subst w
    simp [UnitAddTorus.mFourier_zero]
  rw [if_neg hw]
  let ν (N : ℕ) := integerClockPrefixLaw (fun n => finiteClockPhasePoint ω (a+(n:ℝ)*τ)) N
  have hc (N : ℕ) : (∫ x, UnitAddTorus.mFourier w x ∂(perturbedLaw ω a τ v B N : Measure _))=
      (∫ x, UnitAddTorus.mFourier w x ∂(ν N : Measure _))*
      (∫ x, UnitAddTorus.mFourier w x ∂(transverseLaw v B : Measure _)) := by
    rw [perturbedLaw,integral_conv (integrable_continuous_of_compactSpace _ (UnitAddTorus.mFourier w))]
    simp_rw [mFourier_add_point,integral_const_mul]
    exact integral_mul_const _ _
  simp_rw [hc]
  by_cases h : ∃ k : ℤ, τ*finiteTorusCharacterDetuning w ω=(k:ℝ)*(2*π)
  · obtain ⟨k,hk⟩ := h
    obtain ⟨l,hl⟩ := hgen w k hk
    have hne : l≠0 := by rintro rfl; exact hw (by simpa using hl)
    rw [hl,transverse_character m v hB hdet hne]
    simp only [mul_zero]
    exact tendsto_const_nhds
  · have hh := (off_resonance_character ω τ a w (fun k hk => h ⟨k,hk⟩)).mul_const
        (∫ x, UnitAddTorus.mFourier w x ∂(transverseLaw v B : Measure _))
    simpa only [zero_mul] using hh

#print axioms transverse_haar
end
end GaloisForLFunctions.HTGeometry.AdaptiveSampling.CenteredOccupation
