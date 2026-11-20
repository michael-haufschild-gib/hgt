import GaloisForLFunctions.HTGeometry.Quantum.MetricIntegerClock
import GaloisForLFunctions.HTGeometry.OneSidedCaptureDensity
import GaloisForLFunctions.HTGeometry.SortedEnsembleSpectrumScaling
import GaloisForLFunctions.HTGeometry.FintypeSortedSpectrum
import GaloisForLFunctions.HTGeometry.PauliBoundedHamiltonianLocalityLaw
import GaloisForLFunctions.RHTower.StaticChoiProjectiveComplexityPlateau
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Equidistribution on a prescribed integer observation clock

Almost every draw of a homogeneous frequency family samples its full phase
torus along a prescribed injective integer clock whenever its frequencies
have no integer relation.
-/
open MeasureTheory Filter Set
open scoped Topology

namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Empirical law of the first N+1 samples, counting every index once. -/
def integerClockPrefixLaw {X : Type*} [MeasurableSpace X] (x : ℕ → X) (N : ℕ) :
    ProbabilityMeasure X :=
  let u : ProbabilityMeasure (Fin (N+1)) := ⟨(PMF.uniformOfFintype _).toMeasure, inferInstance⟩
  u.map (f := fun i => x i.1) (measurable_of_finite _).aemeasurable

/-- The integral of a continuous character over an empirical law is its sample average. -/
private theorem integral_integerClockPrefixLaw {X : Type*} [MeasurableSpace X]
    (x : ℕ → X) (N : ℕ) (f : X → ℂ) (hf : Measurable f) :
    ∫ z, f z ∂(integerClockPrefixLaw x N : Measure X) =
      ((N+1:ℕ):ℂ)⁻¹ * ∑ j ∈ Finset.range (N+1), f (x j) := by
  rw [integerClockPrefixLaw,ProbabilityMeasure.toMeasure_map,
    integral_map (measurable_of_finite _).aemeasurable hf.aestronglyMeasurable]
  change (∫ i : Fin (N+1), f (x i.1) ∂(PMF.uniformOfFintype _).toMeasure) = _
  rw [PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply,Fintype.card_fin,ENNReal.toReal_inv,
    ENNReal.toReal_natCast,Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_natCast,
    ← Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun j => f (x j)) (N+1)]

/-- Countably many scalar metric Weyl tests give simultaneous weak convergence
of the complete phase distribution for a prescribed integer clock. -/
theorem ae_homogeneous_integerClock_phaseLaw {m d : ℕ}
    (b : ℕ → ℤ) (hb : Function.Injective b)
    (ω : (Fin m → ℝ) → Fin d → ℝ) (hω : Measurable ω)
    (hscale : ∀ a : ℝ, 0 < a → ∀ p i, ω (a • p) i = a * ω p i) :
    ∀ᵐ p ∂(volume : Measure (Fin m → ℝ)), RationallyIndependentFrequency (ω p) →
      Tendsto (integerClockPrefixLaw (fun j => finiteClockPhasePoint (ω p) (b j))) atTop
        (𝓝 (finiteTorusHaarProbabilityMeasure (Fin d))) := by
  let δ (h : Fin d → ℤ) (p : Fin m → ℝ) := finiteTorusCharacterDetuning h (ω p)
  have hm (h) : Measurable (δ h) := Finset.measurable_sum _ fun i _ =>
    measurable_const.mul ((measurable_pi_apply i).comp hω)
  have hh (h) (a : ℝ) (ha : 0<a) (p) : δ h (a • p) = a*δ h p := by
    dsimp only [δ,finiteTorusCharacterDetuning]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hscale a ha]; ring
  have htest (h) := homogeneous_observable_ae (δ h) (hm h) (hh h) (ae_integerClock_exp b hb)
  filter_upwards [ae_all_iff.mpr htest] with p hp
  intro hind
  apply probabilityMeasure_tendsto_of_mFourier_integral_tendsto
  intro h
  rw [finiteTorusHaarProbabilityMeasure_mFourier_integral]
  simp_rw [integral_integerClockPrefixLaw _ _ _ (UnitAddTorus.mFourier h).continuous.measurable,
    mFourier_finiteClockPhasePoint]
  by_cases h0 : h = 0
  · subst h
    have hz : finiteTorusCharacterDetuning (0 : Fin d → ℤ) (ω p) = 0 := by simp [finiteTorusCharacterDetuning]
    simp [hz,Nat.cast_add_one_ne_zero]
  · rw [if_neg h0]
    have hn : δ h p ≠ 0 := fun hδ => h0 (hind h hδ)
    exact (hp h hn).comp (tendsto_add_atTop_nat 1)

#print axioms ae_homogeneous_integerClock_phaseLaw
/-- Changing the row labels preserves all power traces, hence the entire
sorted eigenvalue tuple, including at collisions. -/
private theorem sorted_eigen_reindex_fin {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}
    (e : ι ≃ Fin D) {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    sortedTuple (hA.reindex e).eigenvalues = sortedTuple (hA.eigenvalues ∘ e.symm) := by
  refine eq_of_monotone_of_sum_pow_eq (monotone_sortedTuple _) (monotone_sortedTuple _) ?_
  intro l
  rw [sum_pow_sortedTuple,sum_pow_sortedTuple,sum_pow_eigenvalues_eq_trace_pow_re' (hA.reindex e) l,
    trace_pow_reindex, ← sum_pow_eigenvalues_eq_trace_pow_re' hA l]
  exact (Equiv.sum_comp e.symm fun i => hA.eigenvalues i ^ l).symm

/-- Equidistribution for a physical static Hermitian family on an integer
observation clock. The phase coordinates are ordered by energy; the eigenbasis
can be chosen after the draw. -/
theorem ae_static_integerClock_phaseLaw {m d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e₀ : ι ≃ Fin (d+1)) (A : (Fin m → ℝ) → Matrix ι ι ℂ)
    (hA : ∀ p, (A p).IsHermitian) (hc : Continuous A)
    (hs : ∀ (a : ℝ), 0 < a → ∀ p, A (a • p) = (a:ℂ) • A p)
    (b : ℕ → ℤ) (hb : Function.Injective b) :
    ∀ᵐ p ∂(volume : Measure (Fin m → ℝ)), MaximallyProjectiveEnergy (hA p).eigenvalues →
      ∃ e : ι ≃ Fin (d+1),
        Tendsto (integerClockPrefixLaw (fun j => finiteClockPhasePoint
          (RHTower.zeroProjectiveFrequency ((hA p).eigenvalues ∘ e.symm)) (b j))) atTop
          (𝓝 (finiteTorusHaarProbabilityMeasure (Fin d))) := by
  let K (p) := Matrix.reindex e₀ e₀ (A p)
  have hK (p) : (K p).IsHermitian := (hA p).reindex e₀
  let E (p) := sortedTuple (hK p).eigenvalues
  have hcont : Continuous E := continuous_sortedTuple_eigenvalues
    (continuous_pi fun i => continuous_pi fun j => (continuous_apply (e₀.symm j)).comp
      ((continuous_apply (e₀.symm i)).comp hc)) hK
  have hEs (a : ℝ) (ha : 0<a) (p) : E (a • p) = fun i => a*E p i := by
    have hmat : K (a • p) = (a:ℂ) • K p := by
      unfold K; rw [hs a ha p]; rfl
    have herm : ((a:ℂ) • K p).IsHermitian := hmat ▸ hK (a • p)
    have hev := ((hK (a • p)).eigenvalues_eq_eigenvalues_iff herm).mpr (congrArg Matrix.charpoly hmat)
    change sortedTuple (hK (a • p)).eigenvalues = _
    rw [hev]
    exact sortedTuple_eigenvalues_real_smul (hK p) ha herm
  let ω (p) := RHTower.zeroProjectiveFrequency (E p)
  have hω : Measurable ω := measurable_pi_lambda _ fun i =>
    ((measurable_pi_apply 0).comp hcont.measurable).sub
      ((measurable_pi_apply i.succ).comp hcont.measurable)
  have hωs (a : ℝ) (ha : 0<a) (p i) : ω (a • p) i = a*ω p i := by
    simp only [ω,RHTower.zeroProjectiveFrequency,hEs a ha,mul_sub]
  filter_upwards [ae_homogeneous_integerClock_phaseLaw b hb ω hω hωs] with p hp
  intro hmax
  let raw := (hA p).eigenvalues ∘ e₀.symm
  let e := e₀.trans (Tuple.sort raw).symm
  have he : E p = (hA p).eigenvalues ∘ e.symm := sorted_eigen_reindex_fin e₀ (hA p)
  refine ⟨e,?_⟩
  rw [← he]
  apply hp
  apply RHTower.maximallyProjectiveEnergy_zeroProjectiveFrequency_independent
  rw [he]
  exact hmax.comp_equiv e.symm

#print axioms ae_static_integerClock_phaseLaw
end
end GaloisForLFunctions.HTGeometry
