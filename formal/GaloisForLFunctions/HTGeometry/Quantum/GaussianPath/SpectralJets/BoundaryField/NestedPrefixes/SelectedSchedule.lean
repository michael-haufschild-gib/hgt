import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.NestedPrefixes.ConditionalLaw
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.JointHaar
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.SeparatedRealClock
import GaloisForLFunctions.HTGeometry.Quantum.IntegerClockPhaseEquidistribution

/-! # The full phase law on observation dates chosen by smaller prefixes -/

open MeasureTheory Filter Set Topology
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.NestedPrefixes
open AdaptiveSampling
noncomputable section

private theorem measurable_means (s : PathPauliDisorder → ℕ → ℝ) (hs : ∀ j, Measurable (fun η => s η j))
    (n : ℕ) : Measurable (fun p : PathPauliDisorder × ℝ => clockCharacterMean (s p.1) p.2 n) := by
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro j _
  exact Complex.continuous_exp.measurable.comp
    ((Complex.continuous_ofReal.measurable.comp (((hs j).comp measurable_fst).mul measurable_snd)).mul_const _)

/-- The empirical phase measures converge once every nonconstant character
has vanishing average along the observation dates. -/
theorem haar_of_clock_cancellation {I : Type*} [Fintype I] (f : I → ℝ) (t : ℕ → ℝ)
    (h : ∀ m : I → ℤ, m≠0 → Tendsto (clockCharacterMean t (finiteTorusCharacterDetuning m f))
      atTop (𝓝 0)) :
    Tendsto (integerClockPrefixLaw (fun j => finiteClockPhasePoint f (t j))) atTop
      (𝓝 (finiteTorusHaarProbabilityMeasure I)) := by
  classical
  apply probabilityMeasure_tendsto_of_mFourier_integral_tendsto
  intro m
  rw [finiteTorusHaarProbabilityMeasure_mFourier_integral]
  simp_rw [integral_integerClockPrefixLaw _ _ _ (UnitAddTorus.mFourier _).continuous.measurable,
    mFourier_finiteClockPhasePoint]
  by_cases h₀ : m=0
  · subst m
    have hd : finiteTorusCharacterDetuning (0 : I → ℤ) f=0 := by
      simp only [finiteTorusCharacterDetuning,Pi.zero_apply,Int.cast_zero,zero_mul,Finset.sum_const_zero]
    simp [hd,Nat.cast_add_one_ne_zero]
  rw [if_neg h₀]
  exact (h m h₀).comp (tendsto_add_atTop_nat 1)

/-- Almost every full draw passes every balanced spectral character test
on a prescribed schedule that can read all but its last longitudinal field. -/
theorem gaussian_selected_actions (k : ℕ) (s : PathPauliDisorder → ℕ → ℝ)
    (hs : ∀ j, Measurable (fun η => s η j)) (hsep : ∀ η j, s η j+1 ≤ s η (j+1)) :
    ∀ᵐ ω ∂pathPauliDisorderLaw,
      let E := (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))).isHermitian.eigenvalues
      ∀ m : Config k → ℤ, m≠0 → (∑ i, m i)=0 →
        Tendsto (clockCharacterMean (s (eraseTerminal k ω)) (∑ i, (m i:ℝ)*E i)) atTop (𝓝 0) := by
  classical
  let S := {p : PathPauliDisorder × ℝ | ¬ Tendsto (clockCharacterMean (s p.1) p.2) atTop (𝓝 0)}
  have hm : MeasurableSet S := (measurableSet_tendsto (𝓝 (0:ℂ)) (measurable_means s hs)).compl
  have hnull (η : PathPauliDisorder) : volume (Prod.mk η ⁻¹' S)=0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    exact (ae_separated_clock_exp (s η) (hsep η)).mono fun _ h => not_not_intro h
  filter_upwards [gaussian_native_null k S hm hnull] with ω hω
  intro E m hm₀ hb
  exact not_not.mp (hω m hm₀ hb)

/-- Any fixed measurable unit-separated schedule using the other couplings
samples the full projective phase law of the original larger register.
The dates can be real and depend on entire smaller-prefix trajectories. -/
theorem gaussian_selected_schedule (k : ℕ) (s : PathPauliDisorder → ℕ → ℝ)
    (hs : ∀ j, Measurable (fun η => s η j)) (hsep : ∀ η j, s η j+1 ≤ s η (j+1)) :
    ∀ᵐ ω ∂pathPauliDisorderLaw,
      let E := (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))).isHermitian.eigenvalues
      ∀ r : Config k, let f := projectiveFrequency (fun i => -E i) r
        Tendsto (integerClockPrefixLaw (fun j => finiteClockPhasePoint f (s (eraseTerminal k ω) j)))
          atTop (𝓝 (finiteTorusHaarProbabilityMeasure _)) := by
  classical
  filter_upwards [gaussian_selected_actions k s hs hsep] with ω hω
  intro E r f
  apply haar_of_clock_cancellation
  intro m hm
  let q (i : Config k) := -liftPacket r m i
  have hq : q≠0 := by
    intro h
    apply hm
    funext j
    simpa only [q,lift_off_anchor,Pi.zero_apply,neg_eq_zero] using congrFun h j.val
  have hb : (∑ i, q i)=0 := by
    change (∑ i, -liftPacket r m i)=0
    rw [Finset.sum_neg_distrib,lift_sum,neg_zero]
  have he : (∑ i, (q i:ℝ)*E i)=finiteTorusCharacterDetuning m f := calc
    _ = ∑ i, (liftPacket r m i:ℝ)*(-E i) := Finset.sum_congr rfl fun i _ => by
      simp only [q,Int.cast_neg,neg_mul,mul_neg]
    _ = _ := lift_energy r m (fun i => -E i)
  rw [←he]
  exact hω q hq hb

#print axioms gaussian_selected_actions
#print axioms gaussian_selected_schedule
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.NestedPrefixes
