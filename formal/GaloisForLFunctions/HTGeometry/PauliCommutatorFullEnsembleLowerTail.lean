import GaloisForLFunctions.HTGeometry.PauliCommutatorActiveFanLowerTail
import GaloisForLFunctions.HTGeometry.ActivePauliShellSpectralLaw

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

def embeddingInactiveIndex {A I : Type*} (e : A ↪ I) :=
  {i : I // i ∉ Set.range e}

noncomputable instance embeddingInactiveIndexFintype
    {A I : Type*} [Fintype I] (e : A ↪ I) :
    Fintype (embeddingInactiveIndex e) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

def embeddingSplitIndexEquiv {A I : Type*} [Fintype A] [Fintype I]
    (e : A ↪ I) : embeddingInactiveIndex e ⊕ A ≃ I := by
  classical
  exact (Equiv.sumComm (embeddingInactiveIndex e) A).trans
    ((Equiv.sumCongr (Equiv.ofInjective e e.injective)
      (Equiv.refl (embeddingInactiveIndex e))).trans
        (Equiv.sumCompl fun i : I => i ∈ Set.range e))

@[simp] theorem embeddingSplitIndexEquiv_inl
    {A I : Type*} [Fintype A] [Fintype I]
    (e : A ↪ I) (i : embeddingInactiveIndex e) :
    embeddingSplitIndexEquiv e (Sum.inl i) = i.1 := by
  rfl

@[simp] theorem embeddingSplitIndexEquiv_inr
    {A I : Type*} [Fintype A] [Fintype I]
    (e : A ↪ I) (a : A) :
    embeddingSplitIndexEquiv e (Sum.inr a) = e a := by
  rfl

def embeddingCoefficientSplit {A I : Type*} [Fintype A] [Fintype I]
    (e : A ↪ I) :
    (I → ℝ) ≃ᵐ ((embeddingInactiveIndex e → ℝ) × (A → ℝ)) :=
  (MeasurableEquiv.piCongrLeft (fun _ : I => ℝ)
      (embeddingSplitIndexEquiv e)).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi
      (fun _ : embeddingInactiveIndex e ⊕ A => ℝ))

theorem embeddingCoefficientSplit_measurePreserving
    {A I : Type*} [Fintype A] [Fintype I] (e : A ↪ I) :
    MeasurePreserving (embeddingCoefficientSplit e)
      (Measure.pi fun _ : I => gaussianReal 0 1)
      ((Measure.pi fun _ : embeddingInactiveIndex e => gaussianReal 0 1).prod
        (Measure.pi fun _ : A => gaussianReal 0 1)) := by
  have hindexForward := MeasureTheory.measurePreserving_piCongrLeft
    (fun _ : I => gaussianReal 0 1) (embeddingSplitIndexEquiv e)
  have hindex := MeasureTheory.MeasurePreserving.symm
    (MeasurableEquiv.piCongrLeft (fun _ : I => ℝ)
      (embeddingSplitIndexEquiv e)) hindexForward
  have hsum := MeasureTheory.measurePreserving_sumPiEquivProdPi
    (fun _ : embeddingInactiveIndex e ⊕ A => gaussianReal 0 1)
  exact hsum.comp hindex

@[simp] theorem embeddingCoefficientSplit_inactive_apply
    {A I : Type*} [Fintype A] [Fintype I]
    (e : A ↪ I) (x : I → ℝ) (i : embeddingInactiveIndex e) :
    (embeddingCoefficientSplit e x).1 i = x i.1 := by
  rfl

@[simp] theorem embeddingCoefficientSplit_active_apply
    {A I : Type*} [Fintype A] [Fintype I]
    (e : A ↪ I) (x : I → ℝ) (a : A) :
    (embeddingCoefficientSplit e x).2 a = x (e a) := by
  rfl

def localPauliAnticommutingFanTracelessEmbedding
    {n q : ℕ} (hq : 2 ≤ q) (P : NonzeroPauliCharacter (Fin n)) :
    {j : Fin n // j ≠ firstActivePauliSite P} ↪ PauliTracelessLabel n q where
  toFun j := ⟨localPauliAnticommutingFanLabel P j, by
    constructor
    · rw [pauliWeight_localPauliAnticommutingFanLabel]
      omega
    · intro hidentity
      have hweight := congrArg pauliWeight hidentity
      rw [pauliWeight_localPauliAnticommutingFanLabel] at hweight
      simp [pauliWeight, pauliIdentityLabel] at hweight⟩
  inj' := by
    intro j k h
    exact localPauliAnticommutingFanLabel_injective P
      (congrArg Subtype.val h)

def localPauliAnticommutingFanInactiveHamiltonian
    {n q : ℕ} (hq : 2 ≤ q) (P : NonzeroPauliCharacter (Fin n))
    (y : embeddingInactiveIndex
      (localPauliAnticommutingFanTracelessEmbedding hq P) → ℝ) :
    Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ :=
  ∑ Q, (y Q : ℂ) • finitePauliMatrix Q.1.1

theorem activePauliHamiltonian_eq_fan_add_inactive
    {n q : ℕ} (hq : 2 ≤ q) (P : NonzeroPauliCharacter (Fin n))
    (J : PauliTracelessLabel n q → ℝ) :
    activePauliHamiltonian (fun Q => (J Q : ℂ)) =
      localPauliAnticommutingFanHamiltonian P
          (embeddingCoefficientSplit
            (localPauliAnticommutingFanTracelessEmbedding hq P) J).2 +
        localPauliAnticommutingFanInactiveHamiltonian hq P
          (embeddingCoefficientSplit
            (localPauliAnticommutingFanTracelessEmbedding hq P) J).1 := by
  let e := localPauliAnticommutingFanTracelessEmbedding hq P
  let f : PauliTracelessLabel n q →
      Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ :=
    fun Q => (J Q : ℂ) • finitePauliMatrix Q.1
  rw [activePauliHamiltonian, localPauliAnticommutingFanHamiltonian,
    localPauliAnticommutingFanInactiveHamiltonian]
  change (∑ Q, f Q) =
    (∑ a, (((embeddingCoefficientSplit e J).2 a : ℝ) : ℂ) •
      finitePauliMatrix (localPauliAnticommutingFanLabel P a)) +
    ∑ i, (((embeddingCoefficientSplit e J).1 i : ℝ) : ℂ) •
      finitePauliMatrix i.1.1
  rw [add_comm]
  calc
    (∑ Q, f Q) = ∑ z : embeddingInactiveIndex e ⊕
        {j : Fin n // j ≠ firstActivePauliSite P},
        f (embeddingSplitIndexEquiv e z) :=
      (Equiv.sum_comp (embeddingSplitIndexEquiv e) f).symm
    _ = (∑ i : embeddingInactiveIndex e,
          f (embeddingSplitIndexEquiv e (Sum.inl i))) +
        ∑ a : {j : Fin n // j ≠ firstActivePauliSite P},
          f (embeddingSplitIndexEquiv e (Sum.inr a)) := by
      rw [Fintype.sum_sum_type]
    _ = _ := by
      apply congrArg₂ (· + ·)
      · apply Finset.sum_congr rfl
        intro i _
        simp [f, e]
      · apply Finset.sum_congr rfl
        intro a _
        rw [embeddingSplitIndexEquiv_inr]
        change (J (e a) : ℂ) • finitePauliMatrix (e a).1 =
          ((embeddingCoefficientSplit e J).2 a : ℂ) •
            finitePauliMatrix (localPauliAnticommutingFanLabel P a)
        rw [embeddingCoefficientSplit_active_apply]
        rfl

def fullActivePauliCommutatorCoordinate
    {n q : ℕ} (P : NonzeroPauliCharacter (Fin n))
    (J : PauliTracelessLabel n q → ℝ)
    (k : {j : Fin n // j ≠ firstActivePauliSite P}) : ℂ :=
  Matrix.trace
    (finitePauliMatrix
        (optMulLabel (localPauliAnticommutingFanLabel P k) P.1) *
      (activePauliHamiltonian (fun Q => (J Q : ℂ)) * finitePauliMatrix P.1 -
        finitePauliMatrix P.1 * activePauliHamiltonian (fun Q => (J Q : ℂ))))

theorem fullActivePauliCommutatorCoordinate_eq_split
    {n q : ℕ} (hq : 2 ≤ q) (P : NonzeroPauliCharacter (Fin n))
    (J : PauliTracelessLabel n q → ℝ)
    (k : {j : Fin n // j ≠ firstActivePauliSite P}) :
    fullActivePauliCommutatorCoordinate P J k =
      localPauliAnticommutingFanCommutatorCoordinate P
        (localPauliAnticommutingFanInactiveHamiltonian hq P
          (embeddingCoefficientSplit
            (localPauliAnticommutingFanTracelessEmbedding hq P) J).1)
        (embeddingCoefficientSplit
          (localPauliAnticommutingFanTracelessEmbedding hq P) J).2 k := by
  rw [fullActivePauliCommutatorCoordinate,
    localPauliAnticommutingFanCommutatorCoordinate,
    activePauliHamiltonian_eq_fan_add_inactive hq P J]

theorem localPauliAnticommutingFanInactiveCommutatorDrift_eq_sum
    {n q : ℕ} (hq : 2 ≤ q) (P : NonzeroPauliCharacter (Fin n))
    (y : embeddingInactiveIndex
      (localPauliAnticommutingFanTracelessEmbedding hq P) → ℝ)
    (k : {j : Fin n // j ≠ firstActivePauliSite P}) :
    localPauliAnticommutingFanCommutatorDrift P
        (localPauliAnticommutingFanInactiveHamiltonian hq P y) k =
      ∑ Q, (y Q : ℂ) *
        ((optPhaseProd Q.1.1 P.1 - optPhaseProd P.1 Q.1.1) *
          (if optMulLabel (localPauliAnticommutingFanLabel P k) P.1 =
              optMulLabel Q.1.1 P.1 then (2 : ℂ) ^ n else 0)) := by
  have htrace := trace_pauli_commutator_sum
    (R := optMulLabel (localPauliAnticommutingFanLabel P k) P.1)
    (S := fun Q : embeddingInactiveIndex
      (localPauliAnticommutingFanTracelessEmbedding hq P) => Q.1.1)
    (T := fun _ : Unit => P.1)
    (h := fun Q => (y Q : ℂ)) (k := fun _ => 1)
  simpa [localPauliAnticommutingFanCommutatorDrift,
    localPauliAnticommutingFanInactiveHamiltonian,
    Fintype.sum_unique, one_smul, mul_assoc] using htrace

theorem measurable_localPauliAnticommutingFanInactiveCommutatorDrift
    {n q : ℕ} (hq : 2 ≤ q) (P : NonzeroPauliCharacter (Fin n))
    (k : {j : Fin n // j ≠ firstActivePauliSite P}) :
    Measurable fun y : embeddingInactiveIndex
        (localPauliAnticommutingFanTracelessEmbedding hq P) → ℝ =>
      localPauliAnticommutingFanCommutatorDrift P
        (localPauliAnticommutingFanInactiveHamiltonian hq P y) k := by
  simp_rw [localPauliAnticommutingFanInactiveCommutatorDrift_eq_sum hq P]
  refine Finset.measurable_sum _ fun Q _ => ?_
  exact (Complex.continuous_ofReal.measurable.comp
    (measurable_pi_apply Q)).mul measurable_const

def fullActivePauliCommutatorTube
    {n q : ℕ} (P : NonzeroPauliCharacter (Fin n)) (θ : ℝ) :
    Set (PauliTracelessLabel n q → ℝ) :=
  {J | ∑ k, ‖fullActivePauliCommutatorCoordinate P J k‖ ^ 2 ≤
    θ * ((n - 1 : ℕ) : ℝ) * (2 * (2 : ℝ) ^ n) ^ 2}

def splitActivePauliCommutatorTube
    {n q : ℕ} (hq : 2 ≤ q) (P : NonzeroPauliCharacter (Fin n))
    (θ : ℝ) :
    Set ((embeddingInactiveIndex
      (localPauliAnticommutingFanTracelessEmbedding hq P) → ℝ) ×
        ({j : Fin n // j ≠ firstActivePauliSite P} → ℝ)) :=
  {p | ∑ k,
      ‖localPauliAnticommutingFanCommutatorCoordinate P
        (localPauliAnticommutingFanInactiveHamiltonian hq P p.1) p.2 k‖ ^ 2 ≤
    θ * ((n - 1 : ℕ) : ℝ) * (2 * (2 : ℝ) ^ n) ^ 2}

theorem embeddingCoefficientSplit_preimage_splitActivePauliCommutatorTube
    {n q : ℕ} (hq : 2 ≤ q) (P : NonzeroPauliCharacter (Fin n))
    (θ : ℝ) :
    embeddingCoefficientSplit
        (localPauliAnticommutingFanTracelessEmbedding hq P) ⁻¹'
      splitActivePauliCommutatorTube hq P θ =
        fullActivePauliCommutatorTube P θ := by
  ext J
  simp only [mem_preimage, splitActivePauliCommutatorTube,
    fullActivePauliCommutatorTube, mem_setOf_eq]
  simp_rw [fullActivePauliCommutatorCoordinate_eq_split hq P J]

/-- Ordinary fixed-`q` local-Pauli ensemble bound.  One complete Gaussian
Hamiltonian draw has exponentially small commutator tube mass against every
fixed nonidentity Pauli target, uniformly after all non-fan coefficients are
retained. -/
theorem measure_fullActivePauliCommutatorTube_le
    {n q : ℕ} (hq : 2 ≤ q) (P : NonzeroPauliCharacter (Fin n))
    {θ : ℝ} (hθ : θ ≤ gaussianIntervalActivationMass) :
    (Measure.pi fun _ : PauliTracelessLabel n q => gaussianReal 0 1).real
        (fullActivePauliCommutatorTube P θ) ≤
      Real.exp
        (-2 * (gaussianIntervalActivationMass - θ) ^ 2 * (n - 1 : ℕ)) := by
  let e := localPauliAnticommutingFanTracelessEmbedding hq P
  have hmp := embeddingCoefficientSplit_measurePreserving e
  rw [← embeddingCoefficientSplit_preimage_splitActivePauliCommutatorTube hq P θ]
  change (Measure.pi fun _ : PauliTracelessLabel n q => gaussianReal 0 1).real
      ((embeddingCoefficientSplit e) ⁻¹'
        splitActivePauliCommutatorTube hq P θ) ≤ _
  rw [Measure.real]
  rw [← MeasurableEquiv.map_apply (embeddingCoefficientSplit e), hmp.map_eq]
  change ((Measure.pi fun _ : embeddingInactiveIndex e => gaussianReal 0 1).prod
      (Measure.pi fun _ : {j : Fin n // j ≠ firstActivePauliSite P} =>
        gaussianReal 0 1)).real
      (splitActivePauliCommutatorTube hq P θ) ≤ _
  exact measure_prod_localPauliAnticommutingFanCommutator_sq_sum_le P
    (localPauliAnticommutingFanInactiveHamiltonian hq P)
    (measurable_localPauliAnticommutingFanInactiveCommutatorDrift hq P) hθ

end

end GaloisForLFunctions.HTGeometry
