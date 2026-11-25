import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.ShiftedWaits.RadialTransfer
import GaloisForLFunctions.HTGeometry.Quantum.IntegerClockPhaseEquidistribution
import GaloisForLFunctions.HTGeometry.SingleOrbitPlateauWindow

/-! # Phase distributions on a prescribed shift of a random clock -/

open Set Filter MeasureTheory Topology
namespace GaloisForLFunctions.HTGeometry.AdaptiveSampling.ShiftedWaits
noncomputable section

/-- Translating all observation dates translates the empirical phase law
and preserves its Haar limit. -/
theorem translate_phase_law {d : ℕ} (w : Fin d → ℝ) (t : ℕ → ℝ)
    (ht : Tendsto (integerClockPrefixLaw (fun i => finiteClockPhasePoint w (t i))) atTop
      (𝓝 (finiteTorusHaarProbabilityMeasure (Fin d)))) (a : ℝ) :
    Tendsto (integerClockPrefixLaw (fun i => finiteClockPhasePoint w (a+t i))) atTop
      (𝓝 (finiteTorusHaarProbabilityMeasure (Fin d))) := by
  let c := finiteClockPhasePoint w a
  let f := fun z : UnitAddTorus (Fin d) => c+z
  have hf : Continuous f := by dsimp only [f]; fun_prop
  let μ := finiteTorusHaarProbabilityMeasure (Fin d)
  have hμ : μ.map hf.measurable.aemeasurable=μ := by
    apply ProbabilityMeasure.toMeasure_injective
    rw [ProbabilityMeasure.toMeasure_map]
    change Measure.map f (finiteTorusHaarProbabilityMeasure (Fin d) : Measure _) = _
    rw [finiteTorusHaarProbabilityMeasure_toMeasure_eq_volume]
    exact (measurePreserving_add_left volume c).map_eq
  have h := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ μ ht hf
  rw [hμ] at h
  refine h.congr fun M => ?_
  apply ProbabilityMeasure.toMeasure_injective
  simp only [integerClockPrefixLaw,ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map hf.measurable (measurable_of_finite _)]
  congr 1
  funext i
  exact (finiteClockPhasePoint_add w a (t i.val)).symm

/-- For every prescribed injective integer schedule, shifting a
scale-covariant clock by a fixed nonzero amount restores the full Haar
law whenever the new step is positive and the frequencies are independent. -/
theorem shifted_phase_law {m d : ℕ} (b : ℕ → ℤ) (hb : Function.Injective b)
    (w : (Fin m → ℝ) → Fin d → ℝ) (hw : Measurable w)
    (hs : ∀ a : ℝ, 0<a → ∀ x i, w (a • x) i=a*w x i)
    (o : (Fin m → ℝ) → ℝ) (ho : Measurable o)
    (hc : ∀ a > (0:ℝ), ∀ x, a*o (a • x)=o x) {h : ℝ} (hh : h≠0) :
    ∀ᵐ x ∂(volume : Measure (Fin m → ℝ)), let τ := o x+h
      0<τ → RationallyIndependentFrequency (w x) → ∀ a : ℝ,
        Tendsto (integerClockPrefixLaw (fun j => finiteClockPhasePoint (w x) (a+(b j:ℝ)*τ))) atTop
          (𝓝 (finiteTorusHaarProbabilityMeasure (Fin d))) := by
  have ht := (radial_shift_volume o ho hc hh).ae (ae_homogeneous_integerClock_phaseLaw b hb w hw hs)
  filter_upwards [ht] with x hx
  intro τ hp hind a
  have hi : RationallyIndependentFrequency (w (τ • x)) := by
    intro n hn
    apply hind n
    have he : finiteTorusCharacterDetuning n (w (τ • x))=τ*finiteTorusCharacterDetuning n (w x) := by
      unfold finiteTorusCharacterDetuning
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [hs τ hp]; ring
    exact (mul_eq_zero.mp (he ▸ hn)).resolve_left hp.ne'
  apply translate_phase_law
  have he (j : ℕ) : finiteClockPhasePoint (w (τ • x)) (b j)=finiteClockPhasePoint (w x) ((b j:ℝ)*τ) := by
    funext i
    unfold finiteClockPhasePoint
    rw [hs τ hp, mul_assoc]
  have ht' : Tendsto (integerClockPrefixLaw (fun j => finiteClockPhasePoint (w (τ • x)) (b j)))
      atTop (𝓝 (finiteTorusHaarProbabilityMeasure (Fin d))) := hx hi
  simpa only [he] using ht'

#print axioms shifted_phase_law
end
end GaloisForLFunctions.HTGeometry.AdaptiveSampling.ShiftedWaits
