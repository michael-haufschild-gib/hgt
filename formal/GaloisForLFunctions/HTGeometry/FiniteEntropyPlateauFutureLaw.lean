import GaloisForLFunctions.HTGeometry.FiniteAndersonProjectiveGenericityLaw
import GaloisForLFunctions.HTGeometry.FiniteSpectralHaarRecurrenceLaw
import GaloisForLFunctions.HTGeometry.PolynomialHermitianSpectrumGenericity
import GaloisForLFunctions.HTGeometry.ReplicaCollisionExtremality

/-!
# Finite-entropy plateau--future law

For a finite microcanonical spectrum, the completed-time survival-fidelity
plateau is at least the inverse Hilbert-space dimension.  Maximal projective
spectral independence attains this entropy floor, attains every higher
replica permutation floor, and makes the relative phase flow equidistribute
on the full projective torus.

The same conclusions hold generically in every polynomial Hermitian family
containing one maximally projective member.  For fixed finite Hermitian
hopping with arbitrary real onsite controls, no witness assumption is needed:
the good onsite potentials are dense, residual, and of full Lebesgue measure.
-/

open Set Filter Topology MeasureTheory
open scoped BigOperators Interval

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The order-one replica multiplicity packets are exactly the one-hot
packets. -/
theorem piAntidiag_one_eq_image_single
    {I : Type*} [Fintype I] [DecidableEq I] :
    Finset.univ.piAntidiag (1 : ℕ) =
      Finset.univ.image (fun i : I => fun j => if j = i then 1 else 0) := by
  ext p
  constructor
  · intro hp
    have hsum : ∑ i, p i = 1 := (Finset.mem_piAntidiag.mp hp).1
    let d : I →₀ ℕ := Finsupp.equivFunOnFinite.symm p
    have hdsum : d.sum (fun _ n => n) = 1 := by
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
      simpa [d] using hsum
    obtain ⟨i, hi⟩ := (Finsupp.sum_eq_one_iff d).mp hdsum
    rw [Finset.mem_image]
    refine ⟨i, Finset.mem_univ i, ?_⟩
    funext j
    have hj := congrArg (fun q : I →₀ ℕ => q j) hi
    simpa [d, Finsupp.single_apply, eq_comm] using hj.symm
  · intro hp
    rw [Finset.mem_image] at hp
    obtain ⟨i, -, rfl⟩ := hp
    rw [Finset.mem_piAntidiag]
    constructor <;> simp

/-- At replica order one, the unavoidable permutation contribution is the
sum of squared weights. -/
theorem fidelityReplicaPermutationFloor_one_eq_sum_sq
    {I : Type*} [Fintype I] [DecidableEq I]
    (weight : I → ℝ) :
    fidelityReplicaPermutationFloor weight 1 = ∑ i, weight i ^ 2 := by
  classical
  unfold fidelityReplicaPermutationFloor
  rw [piAntidiag_one_eq_image_single]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro i hi
    have honeHot :
        (fun j : I => if j = i then 1 else 0) = Pi.single i 1 := by
      funext j
      simp [Pi.single_apply, eq_comm]
    have hmult :
        Nat.multinomial Finset.univ
            (fun j : I => if j = i then 1 else 0) = 1 := by
      rw [honeHot]
      exact Nat.multinomial_single Finset.univ i 1
    unfold fidelityReplicaMultiplicityWeight
    rw [hmult]
    simp [pow_two]
  · intro i hi j hj hij
    by_contra hne
    have h := congrFun hij i
    simp [hne] at h

/-- Uniform microcanonical weight on a finite state space. -/
def microcanonicalWeight (I : Type*) [Fintype I] : I → ℝ :=
  fun _ => (Fintype.card I : ℝ)⁻¹

/-- Boltzmann-constant-free entropy of the uniform finite microcanonical
sector. -/
def finiteMicrocanonicalEntropy
    (I : Type*) [Fintype I] : ℝ :=
  Real.log (Fintype.card I : ℝ)

/-- The inverse dimension is exactly the exponential entropy floor. -/
theorem exp_neg_finiteMicrocanonicalEntropy_eq_card_inv
    (I : Type*) [Fintype I] [Nonempty I] :
    Real.exp (-finiteMicrocanonicalEntropy I) =
      (Fintype.card I : ℝ)⁻¹ := by
  rw [Real.exp_neg]
  rw [finiteMicrocanonicalEntropy, Real.exp_log]
  positivity

theorem sum_microcanonicalWeight_eq_one
    (I : Type*) [Fintype I] [Nonempty I] :
    ∑ i : I, microcanonicalWeight I i = 1 := by
  have hcard : (Fintype.card I : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [microcanonicalWeight, Finset.sum_const, nsmul_eq_mul, hcard]

theorem sum_microcanonicalWeight_sq
    (I : Type*) [Fintype I] [Nonempty I] :
    (∑ i : I, microcanonicalWeight I i ^ 2) =
      (Fintype.card I : ℝ)⁻¹ := by
  have hcard : (Fintype.card I : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [microcanonicalWeight, Finset.sum_const, nsmul_eq_mul]
  field_simp

theorem fidelityReplicaPermutationFloor_microcanonical_one
    (I : Type*) [Fintype I] [DecidableEq I] [Nonempty I] :
    fidelityReplicaPermutationFloor (microcanonicalWeight I) 1 =
      (Fintype.card I : ℝ)⁻¹ := by
  rw [fidelityReplicaPermutationFloor_one_eq_sum_sq]
  exact sum_microcanonicalWeight_sq I

theorem microcanonicalWeight_pos
    (I : Type*) [Fintype I] [Nonempty I] (i : I) :
    0 < microcanonicalWeight I i := by
  unfold microcanonicalWeight
  positivity

/-- Full-Haar completion of a finite phase flow is equivalent to rational
independence of its frequency vector. -/
theorem finiteTorusPhaseProbabilityMeasure_tendsto_haar_iff
    {d : Type*} [Fintype d]
    (omega : d → ℝ) :
    Tendsto
        (finiteTorusPhaseProbabilityMeasure omega)
        atTop
        (𝓝 (finiteTorusHaarProbabilityMeasure d)) ↔
      RationallyIndependentFrequency omega := by
  constructor
  · intro hconv n hdetuning
    by_contra hn
    have hIntegral :=
      (continuous_integral_complex_continuousMap
        (UnitAddTorus.mFourier n)).continuousAt.tendsto.comp hconv
    change
      Tendsto
        (fun A =>
          ∫ x, UnitAddTorus.mFourier n x
            ∂(finiteTorusPhaseProbabilityMeasure omega A :
              Measure (UnitAddTorus d)))
        atTop
        (𝓝
          (∫ x, UnitAddTorus.mFourier n x
            ∂(finiteTorusHaarProbabilityMeasure d :
              Measure (UnitAddTorus d)))) at hIntegral
    have hzero :
        Tendsto
          (fun A =>
            ∫ x, UnitAddTorus.mFourier n x
              ∂(finiteTorusPhaseProbabilityMeasure omega A :
                Measure (UnitAddTorus d)))
          atTop
          (𝓝 (0 : ℂ)) := by
      rw [finiteTorusHaarProbabilityMeasure_mFourier_integral] at hIntegral
      simpa [hn] using hIntegral
    have hone :
        Tendsto
          (fun A =>
            ∫ x, UnitAddTorus.mFourier n x
              ∂(finiteTorusPhaseProbabilityMeasure omega A :
                Measure (UnitAddTorus d)))
          atTop
          (𝓝 (1 : ℂ)) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [] with A
      rw [finiteTorusPhaseProbabilityMeasure_mFourier_integral,
        hdetuning]
      simp
    have : (0 : ℂ) = 1 := tendsto_nhds_unique hzero hone
    norm_num at this
  · exact finiteTorusPhaseProbabilityMeasure_tendsto_haar omega

/-- Projective spectral independence is exactly rational independence of
the relative frequency packet anchored at any chosen level. -/
theorem maximallyProjectiveEnergy_iff_projectiveFrequency_independent
    {I : Type*} [Fintype I] [DecidableEq I]
    (energy : I → ℝ) (reference : I) :
    MaximallyProjectiveEnergy energy ↔
      RationallyIndependentFrequency
        (projectiveFrequency energy reference) := by
  constructor
  · intro hmax
    exact maximallyProjectiveEnergy_projectiveFrequency_independent
      energy hmax reference
  · intro hindependent k hbalanced henergy
    let n : {i : I // i ≠ reference} → ℤ := fun i => k i.1
    have hbalancedSplit :
        k reference + ∑ i : {i : I // i ≠ reference}, k i.1 = 0 := by
      rw [← Fintype.sum_eq_add_sum_subtype_ne k reference]
      exact hbalanced
    have hbalancedReal :
        (k reference : ℝ) +
            ∑ i : {i : I // i ≠ reference}, (k i.1 : ℝ) = 0 := by
      exact_mod_cast hbalancedSplit
    have henergySplit :
        (k reference : ℝ) * energy reference +
            ∑ i : {i : I // i ≠ reference},
              (k i.1 : ℝ) * energy i.1 = 0 := by
      rw [← Fintype.sum_eq_add_sum_subtype_ne
        (fun i => (k i : ℝ) * energy i) reference]
      exact henergy
    have hdetuning :
        finiteTorusCharacterDetuning n
          (projectiveFrequency energy reference) = 0 := by
      unfold finiteTorusCharacterDetuning projectiveFrequency n
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
      linear_combination henergySplit - energy reference * hbalancedReal
    have hn : n = 0 := hindependent n hdetuning
    funext i
    by_cases hi : i = reference
    · subst i
      have hrest :
          ∑ j : {j : I // j ≠ reference}, k j.1 = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        have hjzero := congrFun hn j
        simpa [n] using hjzero
      simpa [hrest] using hbalancedSplit
    · let j : {j : I // j ≠ reference} := ⟨i, hi⟩
      have hjzero := congrFun hn j
      simpa [n, j] using hjzero

/-- **Finite-entropy plateau floor.** Every finite microcanonical spectrum
has completed-time order-one survival-fidelity mass at least the inverse
state-space dimension. -/
theorem microcanonical_plateau_floor_le
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (energy : I → ℝ) :
    (Fintype.card I : ℝ)⁻¹ ≤
      fidelityReplicaCollisionMass (microcanonicalWeight I) energy 1 := by
  rw [← fidelityReplicaPermutationFloor_microcanonical_one I]
  exact fidelityReplicaCollisionMass_floor_le
    (microcanonicalWeight_pos I) energy 1

/-- Entropic form of the finite microcanonical plateau floor. -/
theorem microcanonical_exp_neg_entropy_floor_le
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (energy : I → ℝ) :
    Real.exp (-finiteMicrocanonicalEntropy I) ≤
      fidelityReplicaCollisionMass (microcanonicalWeight I) energy 1 := by
  rw [exp_neg_finiteMicrocanonicalEntropy_eq_card_inv]
  exact microcanonical_plateau_floor_le energy

/-- A maximally projective finite spectrum attains the microcanonical
entropy floor exactly. -/
theorem maximallyProjective_microcanonical_plateau_eq_entropyFloor
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    {energy : I → ℝ} (hmax : MaximallyProjectiveEnergy energy) :
    fidelityReplicaCollisionMass (microcanonicalWeight I) energy 1 =
      (Fintype.card I : ℝ)⁻¹ := by
  have hall :=
    (all_fidelityReplicaCollisionMass_eq_floor_iff
      (microcanonicalWeight_pos I) energy).2 hmax
  rw [hall 1]
  exact fidelityReplicaPermutationFloor_microcanonical_one I

/-- A maximally projective finite spectrum attains the exponential entropy
floor exactly. -/
theorem maximallyProjective_microcanonical_plateau_eq_exp_neg_entropy
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    {energy : I → ℝ} (hmax : MaximallyProjectiveEnergy energy) :
    fidelityReplicaCollisionMass (microcanonicalWeight I) energy 1 =
      Real.exp (-finiteMicrocanonicalEntropy I) := by
  rw [maximallyProjective_microcanonical_plateau_eq_entropyFloor hmax,
    exp_neg_finiteMicrocanonicalEntropy_eq_card_inv]

/-- The normalized microcanonical spectral form factor converges in centered
time average to the inverse dimension for a maximally projective spectrum. -/
theorem maximallyProjective_microcanonicalSFFMean_tendsto_entropyFloor
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    {energy : I → ℝ} (hmax : MaximallyProjectiveEnergy energy) :
    Tendsto
      (finiteSpectralSurvivalFidelityMean
        (microcanonicalWeight I) energy 1)
      atTop
      (𝓝 ((Fintype.card I : ℝ)⁻¹ : ℂ)) := by
  have h := finiteSpectralSurvivalFidelityMean_tendsto_collisionMass
    (microcanonicalWeight I) energy 1
  simpa [maximallyProjective_microcanonical_plateau_eq_entropyFloor hmax]
    using h

/-- **Plateau hierarchy completeness law.** Every microcanonical spectral
form-factor moment attains its permutation floor exactly when the completed
relative phase flow equidistributes on the full projective torus. -/
theorem all_microcanonicalSFFMoments_floor_iff_projectivePhase_tendsto_haar
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (energy : I → ℝ) (reference : I) :
    (∀ n : ℕ,
        Tendsto
          (finiteSpectralSurvivalFidelityMean
            (microcanonicalWeight I) energy n)
          atTop
          (𝓝
            (fidelityReplicaPermutationFloor
              (microcanonicalWeight I) n : ℂ))) ↔
      Tendsto
        (finiteTorusPhaseProbabilityMeasure
          (projectiveFrequency energy reference))
        atTop
        (𝓝
          (finiteTorusHaarProbabilityMeasure
            {i : I // i ≠ reference})) := by
  rw [all_finiteSpectralSurvivalFidelityMean_tendsto_floor_iff
    (microcanonicalWeight_pos I) energy]
  rw [finiteTorusPhaseProbabilityMeasure_tendsto_haar_iff]
  exact maximallyProjectiveEnergy_iff_projectiveFrequency_independent
    energy reference

/-- Static collision-mass form of plateau hierarchy completeness. -/
theorem all_microcanonicalCollisionMass_floor_iff_projectivePhase_tendsto_haar
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (energy : I → ℝ) (reference : I) :
    (∀ n : ℕ,
        fidelityReplicaCollisionMass
          (microcanonicalWeight I) energy n =
        fidelityReplicaPermutationFloor
          (microcanonicalWeight I) n) ↔
      Tendsto
        (finiteTorusPhaseProbabilityMeasure
          (projectiveFrequency energy reference))
        atTop
        (𝓝
          (finiteTorusHaarProbabilityMeasure
            {i : I // i ≠ reference})) := by
  rw [all_fidelityReplicaCollisionMass_eq_floor_iff
    (microcanonicalWeight_pos I) energy]
  rw [finiteTorusPhaseProbabilityMeasure_tendsto_haar_iff]
  exact maximallyProjectiveEnergy_iff_projectiveFrequency_independent
    energy reference

/-- **Finite-entropy plateau--future law.** Minimal microcanonical plateau,
all replica permutation floors, and full-Haar projective recurrence are
simultaneous consequences of maximal projective spectral independence. -/
theorem finiteEntropyPlateauFutureLaw
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    {energy : I → ℝ} (hmax : MaximallyProjectiveEnergy energy) :
    Function.Injective energy ∧
      Tendsto
        (finiteSpectralSurvivalFidelityMean
          (microcanonicalWeight I) energy 1)
        atTop
        (𝓝 ((Fintype.card I : ℝ)⁻¹ : ℂ)) ∧
      (∀ n : ℕ,
        Tendsto
          (finiteSpectralSurvivalFidelityMean
            (microcanonicalWeight I) energy n)
          atTop
          (𝓝
            (fidelityReplicaPermutationFloor
              (microcanonicalWeight I) n : ℂ))) ∧
      ∀ reference : I,
        Tendsto
          (finiteTorusPhaseProbabilityMeasure
            (projectiveFrequency energy reference))
          atTop
          (𝓝
            (finiteTorusHaarProbabilityMeasure
              {i : I // i ≠ reference})) := by
  refine ⟨hmax.injective,
    maximallyProjective_microcanonicalSFFMean_tendsto_entropyFloor hmax,
    (all_finiteSpectralSurvivalFidelityMean_tendsto_floor_iff
      (microcanonicalWeight_pos I) energy).2 hmax,
    ?_⟩
  intro reference
  exact projectivePhaseProbabilityMeasure_tendsto_haar
    energy hmax reference

/-- In a polynomial Hermitian family containing one maximally projective
member, the finite-entropy plateau--future law holds on a dense, residual,
full-measure parameter set. -/
theorem polynomialHermitianMatrix_generic_finiteEntropyPlateauFutureLaw
    {m : ℕ} {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (M : Matrix I I (MvPolynomial (Fin m) ℂ))
    (hhermitian :
      ∀ p : Fin m → ℝ,
        (M.map
          (MvPolynomial.eval₂Hom (RingHom.id ℂ)
            (fun t => (p t : ℂ)))).IsHermitian)
    (p₀ : Fin m → ℝ)
    (hmax : MaximallyProjectiveEnergy
      (hhermitian p₀).eigenvalues) :
    Dense (polynomialHermitianMatrixMaximalSet M hhermitian) ∧
      polynomialHermitianMatrixMaximalSet M hhermitian ∈
        residual (Fin m → ℝ) ∧
      volume (polynomialHermitianMatrixMaximalSet M hhermitian)ᶜ = 0 ∧
      ∀ p ∈ polynomialHermitianMatrixMaximalSet M hhermitian,
        Function.Injective (hhermitian p).eigenvalues ∧
        Tendsto
          (finiteSpectralSurvivalFidelityMean
            (microcanonicalWeight I) (hhermitian p).eigenvalues 1)
          atTop
          (𝓝 ((Fintype.card I : ℝ)⁻¹ : ℂ)) ∧
        (∀ n : ℕ,
          Tendsto
            (finiteSpectralSurvivalFidelityMean
              (microcanonicalWeight I) (hhermitian p).eigenvalues n)
            atTop
            (𝓝
              (fidelityReplicaPermutationFloor
                (microcanonicalWeight I) n : ℂ))) ∧
        ∀ reference : I,
          Tendsto
            (finiteTorusPhaseProbabilityMeasure
              (projectiveFrequency
                (hhermitian p).eigenvalues reference))
            atTop
            (𝓝
              (finiteTorusHaarProbabilityMeasure
                {i : I // i ≠ reference})) := by
  obtain ⟨hdense, hresidual, hnull⟩ :=
    polynomialHermitianMatrixMaximalSet_dense_residual_fullMeasure
      M hhermitian p₀ hmax
  refine ⟨hdense, hresidual, hnull, ?_⟩
  intro p hp
  exact finiteEntropyPlateauFutureLaw hp

/-- **Fixed-hopping finite-entropy plateau--future law.** For every finite
Hermitian hopping matrix, the onsite potentials realizing the entropy-floor
plateau, every replica permutation floor, and full-Haar projective recurrence
form a dense, residual, full-Lebesgue-measure set. -/
theorem finiteAnderson_generic_finiteEntropyPlateauFutureLaw
    {n : ℕ} [Nonempty (Fin n)]
    (T : Matrix (Fin n) (Fin n) ℂ) (hT : T.IsHermitian) :
    Dense (finiteAndersonProjectiveMaximalSet T hT) ∧
      finiteAndersonProjectiveMaximalSet T hT ∈
        residual (Fin n → ℝ) ∧
      volume (finiteAndersonProjectiveMaximalSet T hT)ᶜ = 0 ∧
      ∀ onsite ∈ finiteAndersonProjectiveMaximalSet T hT,
        Function.Injective
          (finiteAndersonHamiltonian_isHermitian T hT onsite).eigenvalues ∧
        Tendsto
          (finiteSpectralSurvivalFidelityMean
            (microcanonicalWeight (Fin n))
            (finiteAndersonHamiltonian_isHermitian T hT onsite).eigenvalues
            1)
          atTop
          (𝓝 ((n : ℝ)⁻¹ : ℂ)) ∧
        (∀ replica : ℕ,
          Tendsto
            (finiteSpectralSurvivalFidelityMean
              (microcanonicalWeight (Fin n))
              (finiteAndersonHamiltonian_isHermitian
                T hT onsite).eigenvalues replica)
            atTop
            (𝓝
              (fidelityReplicaPermutationFloor
                (microcanonicalWeight (Fin n)) replica : ℂ))) ∧
        ∀ reference : Fin n,
          Tendsto
            (finiteTorusPhaseProbabilityMeasure
              (projectiveFrequency
                (finiteAndersonHamiltonian_isHermitian
                  T hT onsite).eigenvalues reference))
            atTop
            (𝓝
              (finiteTorusHaarProbabilityMeasure
                {i : Fin n // i ≠ reference})) := by
  obtain ⟨hdense, hresidual, hnull⟩ :=
    finiteAndersonProjectiveMaximalSet_dense_residual_fullMeasure T hT
  refine ⟨hdense, hresidual, hnull, ?_⟩
  intro onsite honsite
  simpa using
    (finiteEntropyPlateauFutureLaw honsite)

end

end GaloisForLFunctions.HTGeometry
