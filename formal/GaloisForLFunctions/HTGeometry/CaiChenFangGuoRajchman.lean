import GaloisForLFunctions.HTGeometry.HarmonicLogEquidistribution
import GaloisForLFunctions.HTGeometry.PrimePoissonProductState
import GaloisForLFunctions.HTGeometry.FiniteSpectralHaarRecurrenceLaw
import GaloisForLFunctions.HTGeometry.CompletedObserverTimeTorus
import GaloisForLFunctions.HTGeometry.ResolvedRecurrenceRelationCompletenessLaw

/-!
# Rajchman transfer laws from critical circle chaos

This module transfers deterministic mechanisms isolated in Cai--Chen--Fang--Guo,
*Critical Gaussian Multiplicative Chaos on the Circle Is Rajchman* (arXiv:2608.28328),
to existing circle and torus measures in the corpus.

The source theorem concerns critical Gaussian multiplicative chaos.  Results below are mechanical
bridges: they identify already-constructed Haar, Poisson, orbit-closure, and spectral-relation
ensembles as Rajchman along their nonresonant directions.  No Gaussian-chaos claim is made.
-/

open Complex Filter MeasureTheory Set Submodule Topology
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Two-sided Fourier decay on the additive unit circle. -/
def IsAddCircleRajchman (μ : Measure UnitAddCircle) : Prop :=
  IsFiniteMeasure μ ∧
    Tendsto (fun n : ℕ => ∫ z, fourier (n : ℤ) z ∂μ) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => ∫ z, fourier (Int.negSucc n) z ∂μ) atTop (𝓝 0)

/-- Normalized circle Haar measure is Rajchman; every nonzero coefficient vanishes exactly. -/
theorem unitCircleHaar_isAddCircleRajchman :
    IsAddCircleRajchman GaloisForLFunctions.unitCircleHaar := by
  refine ⟨inferInstance, ?_, ?_⟩
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [GaloisForLFunctions.integral_fourier_unitCircleHaar, if_neg]
    omega
  · apply tendsto_const_nhds.congr'
    filter_upwards [] with n
    rw [GaloisForLFunctions.integral_fourier_unitCircleHaar, if_neg]
    omega

/-- Every circle Poisson law is Rajchman.  Its disk parameter packages the strict contraction that
forces both positive and negative Fourier powers to vanish. -/
theorem addCirclePoissonProbabilityMeasure_isAddCircleRajchman
    (a : CirclePoissonParameter) :
    IsAddCircleRajchman
      (addCirclePoissonProbabilityMeasure a : Measure UnitAddCircle) := by
  refine ⟨inferInstance, ?_, ?_⟩
  · simpa only [integral_fourier_addCirclePoissonProbabilityMeasure] using
      (tendsto_pow_atTop_nhds_zero_of_norm_lt_one
        (by simpa only [mem_ball_zero_iff] using a.2) :
        Tendsto (fun n : ℕ => (a : ℂ) ^ n) atTop (𝓝 0))
  · have hpow : Tendsto (fun n : ℕ => conj (a : ℂ) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one
        (by simpa only [norm_conj, mem_ball_zero_iff] using a.2)
    simpa only [integral_fourier_addCirclePoissonProbabilityMeasure, pow_succ, zero_mul] using
      hpow.mul_const (conj (a : ℂ))

/-- Coordinatewise two-sided Fourier decay on a product unit torus. -/
def IsInfiniteTorusCoordinateRajchman {I : Type*}
    (μ : Measure (I → UnitAddCircle)) (i : I) : Prop :=
  IsFiniteMeasure μ ∧
    Tendsto (fun n : ℕ =>
      ∫ x, infiniteTorusFourier (Finsupp.single i (n : ℤ)) x ∂μ) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ =>
      ∫ x, infiniteTorusFourier (Finsupp.single i (Int.negSucc n)) x ∂μ) atTop (𝓝 0)

/-- Every coordinate marginal of an arbitrary product Poisson state is Rajchman. -/
theorem torusPoissonMeasure_isInfiniteTorusCoordinateRajchman
    {I : Type*} (a : I → CirclePoissonParameter) (i : I) :
    IsInfiniteTorusCoordinateRajchman (torusPoissonMeasure a) i := by
  classical
  refine ⟨inferInstance, ?_, ?_⟩
  · have hpow : Tendsto (fun n : ℕ => (a i : ℂ) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one
        (by simpa only [mem_ball_zero_iff] using (a i).2)
    apply hpow.congr'
    filter_upwards [] with n
    rw [integral_infiniteTorusFourier_torusPoissonMeasure]
    simp [circlePoissonFourierMoment, Finsupp.prod_single_index]
  · have hpow : Tendsto (fun n : ℕ => conj (a i : ℂ) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one
        (by simpa only [norm_conj, mem_ball_zero_iff] using (a i).2)
    have hlim : Tendsto (fun n : ℕ => conj (a i : ℂ) ^ n * conj (a i : ℂ))
        atTop (𝓝 0) := by simpa only [zero_mul] using hpow.mul_const (conj (a i : ℂ))
    apply hlim.congr'
    filter_upwards [] with n
    rw [integral_infiniteTorusFourier_torusPoissonMeasure]
    simp [circlePoissonFourierMoment, Finsupp.prod_single_index, pow_succ]

/-- Every local prime phase in the ordinary-prime Poisson spectral law is Rajchman. -/
theorem primePoissonMeasure_isInfiniteTorusCoordinateRajchman
    (σ : {x : ℝ // 0 < x}) (t : ℝ) (p : Nat.Primes) :
    IsInfiniteTorusCoordinateRajchman
      (primePoissonMeasure σ t σ.2) p := by
  exact torusPoissonMeasure_isInfiniteTorusCoordinateRajchman
    (primePoissonParameter σ t σ.2) p

/-- Two-sided cancellation along integer multiples of a finite-torus character. -/
def IsFiniteTorusRayRajchman {d : Type*} [Fintype d]
    (μ : Measure (UnitAddTorus d)) (m : d → ℤ) : Prop :=
  IsFiniteMeasure μ ∧
    Tendsto (fun n : ℕ =>
      ∫ x, UnitAddTorus.mFourier (fun i => (n : ℤ) * m i) x ∂μ) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ =>
      ∫ x, UnitAddTorus.mFourier (fun i => Int.negSucc n * m i) x ∂μ) atTop (𝓝 0)

/-- Finite-torus Haar measure is Rajchman along every nonzero character ray. -/
theorem finiteTorusHaarProbabilityMeasure_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (m : {m : d → ℤ // m ≠ 0}) :
    IsFiniteTorusRayRajchman
      (finiteTorusHaarProbabilityMeasure d : Measure (UnitAddTorus d)) m := by
  classical
  refine ⟨inferInstance, ?_, ?_⟩
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [finiteTorusHaarProbabilityMeasure_mFourier_integral, if_neg]
    intro hzero
    apply m.2
    funext i
    have hi := congrFun hzero i
    simpa using (mul_eq_zero.mp hi).resolve_left (by omega : (n : ℤ) ≠ 0)
  · apply tendsto_const_nhds.congr'
    filter_upwards [] with n
    rw [finiteTorusHaarProbabilityMeasure_mFourier_integral, if_neg]
    intro hzero
    apply m.2
    funext i
    have hi := congrFun hzero i
    simpa using (mul_eq_zero.mp hi).resolve_left (by omega : Int.negSucc n ≠ 0)

/-- Integer scaling is linear for finite spectral detuning. -/
theorem finiteTorusCharacterDetuning_int_mul
    {d : Type*} [Fintype d] (c : ℤ) (m : d → ℤ) (energy : d → ℝ) :
    finiteTorusCharacterDetuning (fun i => c * m i) energy =
      (c : ℝ) * finiteTorusCharacterDetuning m energy := by
  unfold finiteTorusCharacterDetuning
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Integer scaling commutes with the transpose character map of a torus presentation. -/
theorem orbitClosureCharacter_int_mul
    {d k : Type*} [Fintype d] [Fintype k]
    (c : ℤ) (m : d → ℤ) (M : d → k → ℤ) :
    (fun j => ∑ i, (c * m i) * M i j) =
      fun j => c * ∑ i, m i * M i j := by
  funext j
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Character directions transverse to a presented orbit-closure torus. -/
def OrbitClosureTransverseDirection
    {d k : Type*} [Fintype d] [Fintype k] (M : d → k → ℤ) :=
  {m : d → ℤ // (fun j => ∑ i, m i * M i j) ≠ 0}

/-- Haar measure of a completed-time orbit closure is Rajchman on every transverse character ray.
The excluded kernel is exactly its resonance lattice. -/
theorem orbitClosureHaar_isFiniteTorusRayRajchman
    {d k : Type*} [Fintype d] [Fintype k]
    (M : d → k → ℤ) (m : OrbitClosureTransverseDirection M) :
    IsFiniteTorusRayRajchman
      (orbitClosureHaar M : Measure (UnitAddTorus d)) m.1 := by
  classical
  refine ⟨inferInstance, ?_, ?_⟩
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [orbitClosureHaar_mFourier_integral, if_neg]
    intro hzero
    apply m.2
    rw [orbitClosureCharacter_int_mul] at hzero
    funext j
    have hj := congrFun hzero j
    simpa using (mul_eq_zero.mp hj).resolve_left (by omega : (n : ℤ) ≠ 0)
  · apply tendsto_const_nhds.congr'
    filter_upwards [] with n
    rw [orbitClosureHaar_mFourier_integral, if_neg]
    intro hzero
    apply m.2
    rw [orbitClosureCharacter_int_mul] at hzero
    funext j
    have hj := congrFun hzero j
    simpa using (mul_eq_zero.mp hj).resolve_left (by omega : Int.negSucc n ≠ 0)

/-- Nonresonant characters of a finite spectral packet. -/
def NonresonantFiniteTorusCharacter
    {d : Type*} [Fintype d] (energy : d → ℝ) :=
  {m : d → ℤ // finiteTorusCharacterDetuning m energy ≠ 0}

/-- The canonical spectral-relation phase ensemble is Rajchman along every nonresonant ray. -/
theorem spectralRelationPhaseEnsemble_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (energy : d → ℝ)
    (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (spectralRelationPhaseEnsemble energy : Measure (UnitAddTorus d)) m.1 := by
  classical
  refine ⟨inferInstance, ?_, ?_⟩
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [spectralRelationPhaseEnsemble_mFourier_integral,
      spectralRelationIndicator, if_neg]
    rw [mem_spectralRelationLattice_iff]
    rw [finiteTorusCharacterDetuning_int_mul]
    exact mul_ne_zero (by exact_mod_cast (by omega : n ≠ 0)) m.2
  · apply tendsto_const_nhds.congr'
    filter_upwards [] with n
    rw [spectralRelationPhaseEnsemble_mFourier_integral,
      spectralRelationIndicator, if_neg]
    rw [mem_spectralRelationLattice_iff]
    rw [finiteTorusCharacterDetuning_int_mul]
    exact mul_ne_zero (by exact_mod_cast (by omega : Int.negSucc n ≠ 0)) m.2

/-- Complexified sinc along every nonzero natural ray vanishes. -/
theorem tendsto_complex_sinc_nat_mul
    (d : {x : ℝ // x ≠ 0}) :
    Tendsto (fun n : ℕ => (Real.sinc ((n : ℝ) * d) : ℂ)) atTop (𝓝 0) := by
  have harg : Tendsto (fun n : ℕ => (n : ℝ) * |(d : ℝ)|) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const (abs_pos.mpr d.2)
  have hs : Tendsto (fun n : ℕ => Real.sinc ((n : ℝ) * |(d : ℝ)|))
      atTop (𝓝 0) := tendsto_real_sinc_atTop_zero.comp harg
  have hs' : Tendsto (fun n : ℕ => (Real.sinc ((n : ℝ) * |(d : ℝ)|) : ℂ))
      atTop (𝓝 0) := Complex.continuous_ofReal.continuousAt.tendsto.comp hs
  apply hs'.congr'
  filter_upwards [] with n
  by_cases hd : 0 ≤ (d : ℝ)
  · rw [abs_of_nonneg hd]
  · rw [abs_of_nonpos (le_of_not_ge hd), ← Real.sinc_neg]
    congr 2
    ring

/-- A nonzero finite observation window already gives Rajchman decay along every nonresonant
character ray; the coefficient is an explicit sinc rather than an exact zero. -/
theorem finiteTorusPhaseProbabilityMeasure_isFiniteTorusRayRajchman
    {d : Type*} [Fintype d] (energy : d → ℝ)
    (A : {x : ℝ // x ≠ 0}) (m : NonresonantFiniteTorusCharacter energy) :
    IsFiniteTorusRayRajchman
      (finiteTorusPhaseProbabilityMeasure energy A : Measure (UnitAddTorus d)) m.1 := by
  classical
  let δ : {x : ℝ // x ≠ 0} :=
    ⟨(A : ℝ) * finiteTorusCharacterDetuning m.1 energy, mul_ne_zero A.2 m.2⟩
  have hpos := tendsto_complex_sinc_nat_mul δ
  refine ⟨inferInstance, ?_, ?_⟩
  · apply hpos.congr'
    filter_upwards [] with n
    rw [finiteTorusPhaseProbabilityMeasure_mFourier_integral,
      finiteTorusCharacterDetuning_int_mul]
    congr 2
    dsimp only [δ]
    push_cast
    ring
  · have hshift := hpos.comp (tendsto_add_atTop_nat 1)
    apply hshift.congr'
    filter_upwards [] with n
    rw [finiteTorusPhaseProbabilityMeasure_mFourier_integral,
      finiteTorusCharacterDetuning_int_mul]
    apply congrArg Complex.ofReal
    rw [← Real.sinc_neg]
    congr 2
    dsimp only [δ]
    push_cast
    ring

private theorem rajchman_tendsto_fourier_add_nat
    (M : {μ : Measure UnitAddCircle // IsAddCircleRajchman μ}) (j : ℤ) :
    Tendsto (fun n : ℕ => ∫ z, fourier (j + (n : ℤ)) z ∂(M : Measure UnitAddCircle))
      atTop (𝓝 0) := by
  rcases j with k | k
  · have h := M.2.2.1.comp (tendsto_add_atTop_nat k)
    apply h.congr'
    filter_upwards [] with n
    dsimp only [Function.comp_apply]
    have hidx : ((n + k : ℕ) : ℤ) = Int.ofNat k + (n : ℤ) := by
      simp only [Int.ofNat_eq_natCast]
      push_cast
      ring
    rw [hidx]
  · have h := M.2.2.1.comp (tendsto_sub_atTop_nat (k + 1))
    apply h.congr'
    filter_upwards [eventually_ge_atTop (k + 1)] with n hn
    dsimp only [Function.comp_apply]
    have hidx : Int.negSucc k + (n : ℤ) = (n - (k + 1) : ℕ) := by
      rw [Int.natCast_sub hn]
      simp only [Int.negSucc_eq]
      push_cast
      ring
    rw [hidx]

private theorem rajchman_tendsto_fourier_add_negSucc
    (M : {μ : Measure UnitAddCircle // IsAddCircleRajchman μ}) (j : ℤ) :
    Tendsto (fun n : ℕ => ∫ z, fourier (j + Int.negSucc n) z ∂(M : Measure UnitAddCircle))
      atTop (𝓝 0) := by
  rcases j with k | k
  · have h := M.2.2.2.comp (tendsto_sub_atTop_nat k)
    apply h.congr'
    filter_upwards [eventually_ge_atTop k] with n hn
    dsimp only [Function.comp_apply]
    have hidx : Int.ofNat k + Int.negSucc n = Int.negSucc (n - k) := by
      rw [Int.negSucc_eq, Int.negSucc_eq, Int.natCast_sub hn]
      simp only [Int.ofNat_eq_natCast]
      ring
    rw [hidx]
  · have h := M.2.2.2.comp (tendsto_add_atTop_nat (k + 1))
    apply h.congr'
    filter_upwards [] with n
    dsimp only [Function.comp_apply]
    have hidx : Int.negSucc k + Int.negSucc n = Int.negSucc (n + (k + 1)) := by
      simp only [Int.negSucc_eq]
      push_cast
      ring
    rw [hidx]

private theorem continuous_mul_fourier_integrable
    (M : {μ : Measure UnitAddCircle // IsAddCircleRajchman μ})
    (g : C(UnitAddCircle, ℂ)) (j : ℤ) :
    Integrable (fun z => g z * fourier j z) (M : Measure UnitAddCircle) := by
  letI : IsFiniteMeasure (M : Measure UnitAddCircle) := M.2.1
  apply Continuous.integrable_of_hasCompactSupport
  · fun_prop
  · exact HasCompactSupport.of_compactSpace _

private theorem rajchman_tendsto_continuous_weight_pos_span
    (M : {μ : Measure UnitAddCircle // IsAddCircleRajchman μ})
    {g : C(UnitAddCircle, ℂ)} (hg : g ∈ span ℂ (Set.range (@fourier (1 : ℝ)))) :
    Tendsto (fun n : ℕ => ∫ z, g z * fourier (n : ℤ) z ∂(M : Measure UnitAddCircle))
      atTop (𝓝 0) := by
  letI : IsFiniteMeasure (M : Measure UnitAddCircle) := M.2.1
  refine Submodule.span_induction (p := fun g _ => Tendsto
    (fun n : ℕ => ∫ z, g z * fourier (n : ℤ) z ∂(M : Measure UnitAddCircle))
    atTop (𝓝 0)) ?_ ?_ ?_ ?_ hg
  · rintro _ ⟨j, rfl⟩
    apply (rajchman_tendsto_fourier_add_nat M j).congr'
    filter_upwards [] with n
    apply integral_congr_ae
    filter_upwards [] with z
    exact fourier_add
  · simpa using tendsto_const_nhds
  · intro f g _ _ hf hg
    have h : Tendsto (fun n : ℕ =>
        (∫ z, f z * fourier (n : ℤ) z ∂(M : Measure UnitAddCircle)) +
        ∫ z, g z * fourier (n : ℤ) z ∂(M : Measure UnitAddCircle)) atTop (𝓝 0) := by
      simpa using hf.add hg
    apply h.congr'
    filter_upwards [] with n
    rw [← integral_add (continuous_mul_fourier_integrable M f (n : ℤ))
      (continuous_mul_fourier_integrable M g (n : ℤ))]
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [ContinuousMap.add_apply]
    ring
  · intro c f _ hf
    have h : Tendsto (fun n : ℕ =>
        c * ∫ z, f z * fourier (n : ℤ) z ∂(M : Measure UnitAddCircle))
        atTop (𝓝 0) := by
      simpa using hf.const_mul c
    apply h.congr'
    filter_upwards [] with n
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [ContinuousMap.smul_apply, smul_eq_mul]
    ring

private theorem rajchman_tendsto_continuous_weight_neg_span
    (M : {μ : Measure UnitAddCircle // IsAddCircleRajchman μ})
    {g : C(UnitAddCircle, ℂ)} (hg : g ∈ span ℂ (Set.range (@fourier (1 : ℝ)))) :
    Tendsto (fun n : ℕ => ∫ z, g z * fourier (Int.negSucc n) z ∂(M : Measure UnitAddCircle))
      atTop (𝓝 0) := by
  letI : IsFiniteMeasure (M : Measure UnitAddCircle) := M.2.1
  refine Submodule.span_induction (p := fun g _ => Tendsto
    (fun n : ℕ => ∫ z, g z * fourier (Int.negSucc n) z ∂(M : Measure UnitAddCircle))
    atTop (𝓝 0)) ?_ ?_ ?_ ?_ hg
  · rintro _ ⟨j, rfl⟩
    apply (rajchman_tendsto_fourier_add_negSucc M j).congr'
    filter_upwards [] with n
    apply integral_congr_ae
    filter_upwards [] with z
    exact fourier_add
  · simpa using tendsto_const_nhds
  · intro f g _ _ hf hg
    have h : Tendsto (fun n : ℕ =>
        (∫ z, f z * fourier (Int.negSucc n) z ∂(M : Measure UnitAddCircle)) +
        ∫ z, g z * fourier (Int.negSucc n) z ∂(M : Measure UnitAddCircle))
        atTop (𝓝 0) := by
      simpa using hf.add hg
    apply h.congr'
    filter_upwards [] with n
    rw [← integral_add (continuous_mul_fourier_integrable M f (Int.negSucc n))
      (continuous_mul_fourier_integrable M g (Int.negSucc n))]
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [ContinuousMap.add_apply]
    ring
  · intro c f _ hf
    have h : Tendsto (fun n : ℕ =>
        c * ∫ z, f z * fourier (Int.negSucc n) z ∂(M : Measure UnitAddCircle))
        atTop (𝓝 0) := by
      simpa using hf.const_mul c
    apply h.congr'
    filter_upwards [] with n
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [ContinuousMap.smul_apply, smul_eq_mul]
    ring

/-- Two-sided Fourier decay after multiplication by a continuous complex weight. -/
def IsAddCircleContinuousWeightRajchman (μ : Measure UnitAddCircle)
    (g : C(UnitAddCircle, ℂ)) : Prop :=
  Tendsto (fun n : ℕ => ∫ z, g z * fourier (n : ℤ) z ∂μ) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => ∫ z, g z * fourier (Int.negSucc n) z ∂μ) atTop (𝓝 0)

private theorem norm_weighted_fourier_integral_sub_le
    (M : {μ : Measure UnitAddCircle // IsAddCircleRajchman μ})
    (f g : C(UnitAddCircle, ℂ)) (j : ℤ) :
    ‖(∫ z, f z * fourier j z ∂(M : Measure UnitAddCircle)) -
        ∫ z, g z * fourier j z ∂(M : Measure UnitAddCircle)‖ ≤
      ‖f - g‖ * (M : Measure UnitAddCircle).real univ := by
  letI : IsFiniteMeasure (M : Measure UnitAddCircle) := M.2.1
  rw [← integral_sub (continuous_mul_fourier_integrable M f j)
    (continuous_mul_fourier_integrable M g j)]
  apply norm_integral_le_of_norm_le_const
  filter_upwards [] with z
  rw [← sub_mul, norm_mul, fourier_apply, Circle.norm_coe, mul_one]
  exact ContinuousMap.norm_coe_le_norm (f - g) z

private theorem rajchman_tendsto_continuous_weight_of_span
    (M : {μ : Measure UnitAddCircle // IsAddCircleRajchman μ})
    (g : C(UnitAddCircle, ℂ)) (index : ℕ → ℤ)
    (hspan : ∀ q : C(UnitAddCircle, ℂ), q ∈ span ℂ (Set.range (@fourier (1 : ℝ))) →
      Tendsto (fun n : ℕ =>
        ∫ z, q z * fourier (index n) z ∂(M : Measure UnitAddCircle)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      ∫ z, g z * fourier (index n) z ∂(M : Measure UnitAddCircle)) atTop (𝓝 0) := by
  letI : IsFiniteMeasure (M : Measure UnitAddCircle) := M.2.1
  rw [Metric.tendsto_atTop]
  intro ε hε
  let mass := (M : Measure UnitAddCircle).real univ
  have hmass : 0 ≤ mass := measureReal_nonneg
  have hclosure : g ∈ (span ℂ
      (Set.range (@fourier (1 : ℝ)))).topologicalClosure := by
    rw [span_fourier_closure_eq_top]
    exact Submodule.mem_top
  obtain ⟨q, hqspan, hgq⟩ := Metric.mem_closure_iff.mp hclosure
    (ε / (2 * (mass + 1))) (by positivity)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp (hspan q hqspan)) (ε / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_zero_right]
  have hqsmall : ‖∫ z, q z * fourier (index n) z
      ∂(M : Measure UnitAddCircle)‖ < ε / 2 := by
    simpa only [dist_zero_right] using hN n hn
  have herr : ‖(∫ z, g z * fourier (index n) z ∂(M : Measure UnitAddCircle)) -
      ∫ z, q z * fourier (index n) z ∂(M : Measure UnitAddCircle)‖ < ε / 2 := by
    refine (norm_weighted_fourier_integral_sub_le M g q (index n)).trans_lt ?_
    calc
      ‖g - q‖ * mass ≤ ‖g - q‖ * (mass + 1) := by
        exact mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
      _ < (ε / (2 * (mass + 1))) * (mass + 1) := by
        exact mul_lt_mul_of_pos_right (by simpa only [dist_eq_norm] using hgq) (by positivity)
      _ = ε / 2 := by field_simp
  calc
    ‖∫ z, g z * fourier (index n) z ∂(M : Measure UnitAddCircle)‖
        ≤ ‖(∫ z, g z * fourier (index n) z ∂(M : Measure UnitAddCircle)) -
            ∫ z, q z * fourier (index n) z ∂(M : Measure UnitAddCircle)‖ +
          ‖∫ z, q z * fourier (index n) z ∂(M : Measure UnitAddCircle)‖ := by
          simpa only [sub_add_cancel] using norm_add_le
            ((∫ z, g z * fourier (index n) z ∂(M : Measure UnitAddCircle)) -
              ∫ z, q z * fourier (index n) z ∂(M : Measure UnitAddCircle))
            (∫ z, q z * fourier (index n) z ∂(M : Measure UnitAddCircle))
    _ < ε := by linarith

/-- Cai--Chen--Fang--Guo's continuous-multiplier mechanism: every continuous observation weight
preserves two-sided Rajchman decay of a finite circle measure. -/
theorem addCircleRajchman_continuous_weight
    (M : {μ : Measure UnitAddCircle // IsAddCircleRajchman μ})
    (g : C(UnitAddCircle, ℂ)) :
    IsAddCircleContinuousWeightRajchman M g := by
  constructor
  · exact rajchman_tendsto_continuous_weight_of_span M g (fun n => (n : ℤ))
      (fun q hq => rajchman_tendsto_continuous_weight_pos_span M hq)
  · exact rajchman_tendsto_continuous_weight_of_span M g Int.negSucc
      (fun q hq => rajchman_tendsto_continuous_weight_neg_span M hq)

/-- A continuous nonnegative density on the unit circle. -/
def ContinuousNonnegativeCircleWeight :=
  {g : C(UnitAddCircle, ℝ) // ∀ z, 0 ≤ g z}

def ContinuousNonnegativeCircleWeight.complex
    (g : ContinuousNonnegativeCircleWeight) : C(UnitAddCircle, ℂ) :=
  ⟨fun z => (g.1 z : ℂ), Complex.continuous_ofReal.comp g.1.continuous⟩

/-- Reweight a Rajchman circle measure by a continuous nonnegative density. -/
def continuousWeightedCircleMeasure
    (M : {μ : Measure UnitAddCircle // IsAddCircleRajchman μ})
    (g : ContinuousNonnegativeCircleWeight) : Measure UnitAddCircle :=
  (M : Measure UnitAddCircle).withDensity (fun z => ENNReal.ofReal (g.1 z))

private theorem continuousNonnegativeCircleWeight_hasFiniteIntegral
    (M : {μ : Measure UnitAddCircle // IsAddCircleRajchman μ})
    (g : ContinuousNonnegativeCircleWeight) :
    HasFiniteIntegral (fun z => g.1 z) (M : Measure UnitAddCircle) := by
  letI : IsFiniteMeasure (M : Measure UnitAddCircle) := M.2.1
  exact (g.1.continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)).hasFiniteIntegral

private theorem integral_fourier_continuousWeightedCircleMeasure
    (M : {μ : Measure UnitAddCircle // IsAddCircleRajchman μ})
    (g : ContinuousNonnegativeCircleWeight) (j : ℤ) :
    ∫ z, fourier j z ∂continuousWeightedCircleMeasure M g =
      ∫ z, g.complex z * fourier j z ∂(M : Measure UnitAddCircle) := by
  letI : IsFiniteMeasure (M : Measure UnitAddCircle) := M.2.1
  rw [continuousWeightedCircleMeasure,
    integral_withDensity_eq_integral_toReal_smul
      (g.1.continuous.measurable.ennreal_ofReal)
      (Filter.Eventually.of_forall fun z => ENNReal.ofReal_lt_top) (fun z => fourier j z)]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [ENNReal.toReal_ofReal (g.2 z), ContinuousNonnegativeCircleWeight.complex,
    ContinuousMap.coe_mk, Complex.real_smul]

/-- Positive-measure form of the multiplier theorem: a continuous nonnegative density turns any
Rajchman circle measure into another finite Rajchman measure. -/
theorem continuousWeightedCircleMeasure_isAddCircleRajchman
    (M : {μ : Measure UnitAddCircle // IsAddCircleRajchman μ})
    (g : ContinuousNonnegativeCircleWeight) :
    IsAddCircleRajchman (continuousWeightedCircleMeasure M g) := by
  letI : IsFiniteMeasure (M : Measure UnitAddCircle) := M.2.1
  have hfinite : IsFiniteMeasure (continuousWeightedCircleMeasure M g) := by
    exact isFiniteMeasure_withDensity_ofReal
      (continuousNonnegativeCircleWeight_hasFiniteIntegral M g)
  have hweighted := addCircleRajchman_continuous_weight M g.complex
  refine ⟨hfinite, ?_, ?_⟩
  · apply hweighted.1.congr'
    filter_upwards [] with n
    exact (integral_fourier_continuousWeightedCircleMeasure M g (n : ℤ)).symm
  · apply hweighted.2.congr'
    filter_upwards [] with n
    exact (integral_fourier_continuousWeightedCircleMeasure M g (Int.negSucc n)).symm

end

end GaloisForLFunctions.HTGeometry
