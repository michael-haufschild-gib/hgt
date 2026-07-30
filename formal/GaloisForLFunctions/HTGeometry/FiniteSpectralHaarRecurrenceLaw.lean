import GaloisForLFunctions.HTGeometry.FiniteTorusPhaseEnsembleLaw
import GaloisForLFunctions.HTGeometry.TorusFourierWeakConvergenceLaw
import GaloisForLFunctions.HTGeometry.ReplicaCollisionExtremality

/-!
# Haar recurrence law for rationally independent finite spectra

The centered uniform-time phase law of any finite rationally independent
frequency family converges weakly to normalized Haar measure on its complete
phase torus. Consequently every continuous completed-time statistic has its
exact Haar average.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Normalized product Haar probability measure on a finite unit torus. -/
def finiteTorusHaarProbabilityMeasure
    (d : Type*) [Fintype d] :
    ProbabilityMeasure (UnitAddTorus d) :=
  ⟨Measure.pi (fun _ => AddCircle.haarAddCircle), by infer_instance⟩

/-- Fourier transform of normalized product Haar measure. -/
theorem finiteTorusHaarProbabilityMeasure_mFourier_integral
    {d : Type*} [Fintype d] (n : d → ℤ) :
    (∫ x, UnitAddTorus.mFourier n x
        ∂(finiteTorusHaarProbabilityMeasure d :
          Measure (UnitAddTorus d))) =
      if n = 0 then 1 else 0 := by
  change
    (∫ x, UnitAddTorus.mFourier n x
        ∂Measure.pi (fun _ => AddCircle.haarAddCircle)) =
      if n = 0 then 1 else 0
  rw [UnitAddTorus.mFourier, ContinuousMap.coe_mk,
    MeasureTheory.integral_fintype_prod_eq_prod]
  by_cases hn : n = 0
  · subst n
    simp
  · rw [if_neg hn]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hn
    change n i ≠ 0 at hi
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    have h :=
      (orthonormal_iff_ite.mp
        (orthonormal_fourier (T := (1 : ℝ))))
        0 (n i)
    rw [ContinuousMap.inner_toLp AddCircle.haarAddCircle
      (fourier 0) (fourier (n i))] at h
    simp only [← fourier_neg, ← fourier_add] at h
    rw [if_neg hi.symm] at h
    simpa using h

/-- No nonzero integer character annihilates the finite frequency vector. -/
def RationallyIndependentFrequency
    {d : Type*} [Fintype d] (omega : d → ℝ) : Prop :=
  ∀ n : d → ℤ,
    finiteTorusCharacterDetuning n omega = 0 → n = 0

/-- Relative frequencies obtained by anchoring one energy level. -/
def projectiveFrequency
    {I : Type*} (energy : I → ℝ) (reference : I)
    (i : {i : I // i ≠ reference}) : ℝ :=
  energy i - energy reference

private theorem sum_two_point_ite
    {I M : Type*} [Fintype I] [DecidableEq I]
    [AddCommMonoid M]
    {a b : I} (hab : a ≠ b) (A B : M) :
    (∑ x : I,
      if x = a then A else if x = b then B else 0) =
      A + B := by
  have hsplit (x : I) :
      (if x = a then A else if x = b then B else 0) =
        (if x = a then A else 0) +
          (if x = b then B else 0) := by
    by_cases hxa : x = a
    · subst x
      simp [hab]
    · by_cases hxb : x = b <;> simp [hxa, hxb, hab.symm]
  simp_rw [hsplit, Finset.sum_add_distrib]
  simp

private theorem sum_subtype_indicator
    {I M : Type*} [Fintype I] [DecidableEq I]
    {p : I → Prop} [DecidablePred p]
    [AddCommMonoid M]
    (f : {x // p x} → M) (i : {x // p x}) :
    (∑ j : {x // p x}, if i.1 = j.1 then f j else 0) = f i := by
  classical
  simpa only [Subtype.ext_iff] using (Fintype.sum_ite_eq i f)

private theorem sum_two_point_ite_mul
    {I R : Type*} [Fintype I] [DecidableEq I]
    [Semiring R]
    {a b : I} (hab : a ≠ b) (A B : R) (f : I → R) :
    (∑ x : I,
      (if x = a then A else if x = b then B else 0) * f x) =
      A * f a + B * f b := by
  have hsplit (x : I) :
      (if x = a then A else if x = b then B else 0) * f x =
        if x = a then A * f a
        else if x = b then B * f b
        else 0 := by
    by_cases hxa : x = a
    · subst x
      simp
    · by_cases hxb : x = b <;> simp [hxa, hxb, hab.symm]
  simp_rw [hsplit]
  exact sum_two_point_ite hab (A * f a) (B * f b)

/-- A maximally projective finite spectrum has rationally independent
frequencies after anchoring any energy level. -/
theorem maximallyProjectiveEnergy_projectiveFrequency_independent
    {I : Type*} [Fintype I] [DecidableEq I]
    (energy : I → ℝ) (hmax : MaximallyProjectiveEnergy energy)
    (reference : I) :
    RationallyIndependentFrequency
      (projectiveFrequency energy reference) := by
  classical
  intro n hdetuning
  let k : I → ℤ :=
    fun j =>
      ∑ i : {i : I // i ≠ reference},
        if j = i.1 then n i
        else if j = reference then -n i
        else 0
  have hbalanced : SpectralCharacterBalanced k := by
    unfold SpectralCharacterBalanced k
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro i hi
    exact sum_two_point_ite i.2 (n i) (-n i) |>.trans (add_neg_cancel _)
  have henergy :
      (∑ j, (k j : ℝ) * energy j) = 0 := by
    unfold k
    push_cast
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    calc
      (∑ i : {i : I // i ≠ reference},
        ∑ j,
          (if j = i.1 then (n i : ℝ)
            else if j = reference then -(n i : ℝ)
            else 0) * energy j) =
          ∑ i : {i : I // i ≠ reference},
            (n i : ℝ) *
              (energy i.1 - energy reference) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [sum_two_point_ite_mul i.2]
              ring
      _ = finiteTorusCharacterDetuning n
          (projectiveFrequency energy reference) := by
            rfl
      _ = 0 := hdetuning
  have hk := hmax k hbalanced henergy
  funext i
  have hi := congrFun hk i.1
  change
    (∑ j : {j : I // j ≠ reference},
      if i.1 = j.1 then n j
      else if i.1 = reference then -n j
      else 0) = 0 at hi
  simp only [i.2, if_false] at hi
  rw [sum_subtype_indicator n i] at hi
  exact hi

/-- **Finite spectral Haar law.** A rationally independent deterministic
phase flow, sampled over centered windows whose radius tends to infinity,
converges weakly to normalized Haar measure on the full phase torus. -/
theorem finiteTorusPhaseProbabilityMeasure_tendsto_haar
    {d : Type*} [Fintype d]
    (omega : d → ℝ)
    (hindependent : RationallyIndependentFrequency omega) :
    Tendsto
      (finiteTorusPhaseProbabilityMeasure omega)
      atTop
      (𝓝 (finiteTorusHaarProbabilityMeasure d)) := by
  apply probabilityMeasure_tendsto_of_mFourier_integral_tendsto
  intro n
  rw [finiteTorusHaarProbabilityMeasure_mFourier_integral]
  by_cases hn : n = 0
  · subst n
    apply tendsto_const_nhds.congr'
    filter_upwards [] with A
    rw [finiteTorusPhaseProbabilityMeasure_mFourier_integral]
    simp [finiteTorusCharacterDetuning]
  · rw [if_neg hn]
    have hdet :
        finiteTorusCharacterDetuning n omega ≠ 0 :=
      fun h => hn (hindependent n h)
    have ht :=
      symmetricPhaseAverage_tendsto_resonanceIndicator
        (finiteTorusCharacterDetuning n omega)
    simp only [if_neg hdet] at ht
    apply ht.congr'
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with A hA
    rw [finiteTorusPhaseProbabilityMeasure_mFourier_integral,
      symmetricPhaseAverage_eq_sinc A
        (finiteTorusCharacterDetuning n omega) hA]

/-- Every complex continuous statistic of a rationally independent finite
phase flow has its exact normalized Haar completed-time average. -/
theorem integral_finiteTorusPhaseProbabilityMeasure_tendsto_haar
    {d : Type*} [Fintype d]
    (omega : d → ℝ)
    (hindependent : RationallyIndependentFrequency omega)
    (f : C(UnitAddTorus d, ℂ)) :
    Tendsto
      (fun A =>
        ∫ x, f x
          ∂(finiteTorusPhaseProbabilityMeasure omega A :
            Measure (UnitAddTorus d)))
      atTop
      (𝓝
        (∫ x, f x
          ∂(finiteTorusHaarProbabilityMeasure d :
            Measure (UnitAddTorus d)))) := by
  exact
    (continuous_integral_complex_continuousMap f).continuousAt.tendsto.comp
      (finiteTorusPhaseProbabilityMeasure_tendsto_haar
        omega hindependent)

/-- A maximally projective spectrum explores the full torus of relative
energy phases in completed time. -/
theorem projectivePhaseProbabilityMeasure_tendsto_haar
    {I : Type*} [Fintype I] [DecidableEq I]
    (energy : I → ℝ) (hmax : MaximallyProjectiveEnergy energy)
    (reference : I) :
    Tendsto
      (finiteTorusPhaseProbabilityMeasure
        (projectiveFrequency energy reference))
      atTop
      (𝓝
        (finiteTorusHaarProbabilityMeasure
          {i : I // i ≠ reference})) := by
  exact
    finiteTorusPhaseProbabilityMeasure_tendsto_haar
      (projectiveFrequency energy reference)
      (maximallyProjectiveEnergy_projectiveFrequency_independent
        energy hmax reference)

/-- Every continuous statistic of the relative phases of a maximally
projective finite spectrum has its normalized Haar completed-time average. -/
theorem integral_projectivePhaseProbabilityMeasure_tendsto_haar
    {I : Type*} [Fintype I] [DecidableEq I]
    (energy : I → ℝ) (hmax : MaximallyProjectiveEnergy energy)
    (reference : I)
    (f : C(UnitAddTorus {i : I // i ≠ reference}, ℂ)) :
    Tendsto
      (fun A =>
        ∫ x, f x
          ∂(finiteTorusPhaseProbabilityMeasure
            (projectiveFrequency energy reference) A :
            Measure (UnitAddTorus {i : I // i ≠ reference})))
      atTop
      (𝓝
        (∫ x, f x
          ∂(finiteTorusHaarProbabilityMeasure
            {i : I // i ≠ reference} :
            Measure (UnitAddTorus {i : I // i ≠ reference})))) := by
  exact
    integral_finiteTorusPhaseProbabilityMeasure_tendsto_haar
      (projectiveFrequency energy reference)
      (maximallyProjectiveEnergy_projectiveFrequency_independent
        energy hmax reference)
      f

end

end GaloisForLFunctions.HTGeometry
