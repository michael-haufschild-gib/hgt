import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.PhysicalTimes.Eigenphases
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EigenlineSignals.AnalyticSignal
import GaloisForLFunctions.HTGeometry.CompletedObserverTimeTorus

/-! # Joint spectral observations of one Gaussian Hamiltonian -/
open Matrix MeasureTheory Filter Set
open scoped Topology Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.PhysicalTimes
open _root_.RHTower.PrimeCirclePeriodization
noncomputable section

private theorem amplitude_neg (ω : PathPauliDisorder) (n : ℕ) (s : ℝ) :
    amplitude ω n (-s)=star (amplitude ω n s) := by
  let H : selfAdjoint (Matrix (Fin (n+2) → Bool) (Fin (n+2) → Bool) ℂ) :=
    ⟨_,isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω n)⟩
  change (unitaryEvolution H.val (-s)).trace / (2:ℂ)^(n+2)=star ((unitaryEvolution H.val s).trace / _)
  rw [EigenlineSignals.adjoint_evolution,Matrix.star_eq_conjTranspose,Matrix.trace_conjTranspose]
  simp

/-- The trace at every fixed signed lag converges to the indicator of zero. -/
theorem gaussian_signed_amplitude :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ s : ℝ, Tendsto (fun n => amplitude ω n s) atTop
      (𝓝 (if s=0 then (1:ℂ) else 0)) := by
  filter_upwards [gaussian_trace_along_dates] with ω hω
  have hp (s : ℝ) (hs : 0<s) := hω s s hs (fun _ => s) (Eventually.of_forall fun _ => ⟨le_rfl,le_rfl⟩)
  intro s
  rcases lt_trichotomy s 0 with hs|rfl|hs
  · rw [if_neg hs.ne]
    have h := continuous_star.continuousAt.tendsto.comp (hp (-s) (neg_pos.mpr hs))
    simpa only [Function.comp_def,←amplitude_neg,neg_neg,star_zero] using h
  · simp [amplitude,unitaryEvolution]
  · simpa only [if_neg hs.ne'] using hp s hs

/-- Sample one common energy eigenline uniformly and observe its phase
at each date. The coordinates retain their original eigenline pairing. -/
def jointLaw {n d : ℕ} (u : PathShell n) (t : Fin d→ℝ) : ProbabilityMeasure (UnitAddTorus (Fin d)) :=
  let μ : ProbabilityMeasure (Fin (n+2)→Bool) := ⟨(PMF.uniformOfFintype _).toMeasure,inferInstance⟩
  μ.map (f:=fun i => finiteClockPhasePoint t (-((isSelfAdjoint_pathHamiltonian u).isHermitian.eigenvalues i)))
    (measurable_of_finite _).aemeasurable

theorem joint_moment (ω : PathPauliDisorder) {n d : ℕ} (t : Fin d→ℝ) (h : Fin d→ℤ) :
    (∫ x, UnitAddTorus.mFourier h x ∂(jointLaw (pathPauliDisorderShell ω n) t : Measure (UnitAddTorus (Fin d)))) =
      amplitude ω n (finiteTorusCharacterDetuning h t) := by
  let s := finiteTorusCharacterDetuning h t
  calc _ = ∫ z, fourier (1:ℤ) z ∂(eigenphaseLaw (pathPauliDisorderShell ω n) s : Measure (AddCircle (2*Real.pi))) := by
         simp only [jointLaw,eigenphaseLaw,ProbabilityMeasure.toMeasure_map]
         rw [integral_map (measurable_of_finite _).aemeasurable (UnitAddTorus.mFourier h).continuous.aestronglyMeasurable,
           integral_map (measurable_of_finite _).aemeasurable (fourier (1:ℤ)).continuous.aestronglyMeasurable]
         apply integral_congr_ae (Eventually.of_forall fun i => ?_)
         rw [mFourier_finiteClockPhasePoint,fourier_phase]
         congr 1
         dsimp only [s]
         push_cast
         ring
       _ = _ := by simpa only [Int.cast_one,one_mul] using eigenphase_moment ω n s 1

/-- For every finite list of physical dates, the joint empirical
eigenphases fill exactly the torus of their integer relations with Haar
probability. Its dimension is the rational rank of the dates. -/
theorem gaussian_joint_orbit_haar :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ d : ℕ, ∀ t : Fin d→ℝ, ∃ k : ℕ, ∃ M : Fin d→Fin k→ℤ,
      k=Module.finrank ℚ (Submodule.span ℚ (range t)) ∧ Function.Injective (torusIntegerHom M) ∧
      closure (range (finiteClockPhasePoint t))=range (torusIntegerHom M) ∧
      Tendsto (fun n => jointLaw (pathPauliDisorderShell ω n) t) atTop (𝓝 (orbitClosureHaar M)) := by
  filter_upwards [gaussian_signed_amplitude] with ω hω
  intro d t
  obtain ⟨k,g,M,A,hg,_,_,hM,hA,hr⟩ := exists_frequency_integer_basis t
  refine ⟨k,M,hr,torusIntegerHom_injective M A hA,closure_range_finiteClockPhasePoint_eq t g M hg hM,?_⟩
  apply probabilityMeasure_tendsto_of_mFourier_integral_tendsto
  intro h
  let b (j) := ∑ i, h i*M i j
  have he := finiteTorusCharacterDetuning_of_integer_presentation t g M hM h
  have hz : finiteTorusCharacterDetuning h t=0 ↔ b=0 := by
    rw [he]
    refine ⟨hg b,fun hh => ?_⟩
    change finiteTorusCharacterDetuning b g=0
    simp [hh,finiteTorusCharacterDetuning]
  simp only [joint_moment,orbitClosureHaar_mFourier_integral]
  change Tendsto _ _ (𝓝 (if b=0 then (1:ℂ) else 0))
  by_cases hb : b=0
  · simpa only [if_pos hb,if_pos (hz.mpr hb)] using hω (finiteTorusCharacterDetuning h t)
  · simpa only [if_neg hb,if_neg (mt hz.mp hb)] using hω (finiteTorusCharacterDetuning h t)

#print axioms gaussian_joint_orbit_haar
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.PhysicalTimes
