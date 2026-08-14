import GaloisForLFunctions.HTGeometry.StaticCircuitReplicaWordDictionary

/-!
# Concrete replica sectors of a static diagonal Hamiltonian and a gate dictionary

The abstract two-memory decomposition needs a nested pair of orthogonal projections, a unitary
evolution fixing the larger one, and a preparation channel fixing the smaller one.  This module
builds all four objects for a static diagonal Hamiltonian and a finite unitary gate alphabet on the
vectorized replica space, with no hypothesis beyond unitarity of the gates.

* the evolution is multiplication by the phase of the replica energy defect;
* the completed static projection is the coordinate projection onto zero replica energy defect;
* the universal sector consists of the gate-invariant vectors carried by that completed spectrum;
* the preparation channel is the one-gate replica moment channel.

The evolution carries the replica projector of a state to the replica projector of the phase-evolved
state, the two projections are nested, and the universal projection is invariant under the moment
channel.  Instantiating the abstract law therefore gives the exact three-sector decomposition of a
concrete circuit collision.
-/

open Matrix

open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section PhaseMultiplication

variable {ι : Type*} [Fintype ι]

/-- Multiplication of a finite Euclidean space by a unit-modulus function. -/
def phaseMultiplication (d : ι → ℂ) (hd : ∀ i, ‖d i‖ = 1) :
    EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι where
  toFun z := WithLp.toLp 2 fun i => d i * z.ofLp i
  map_add' z w := by
    refine WithLp.ofLp_injective (p := 2) ?_
    funext i
    simp [mul_add]
  map_smul' c z := by
    refine WithLp.ofLp_injective (p := 2) ?_
    funext i
    show d i * (c • z).ofLp i = ((RingHom.id ℂ) c • WithLp.toLp 2 fun i => d i * z.ofLp i).ofLp i
    simp only [RingHom.id_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
    ring
  invFun z := WithLp.toLp 2 fun i => conj (d i) * z.ofLp i
  left_inv z := by
    refine WithLp.ofLp_injective (p := 2) ?_
    funext i
    have hdi : conj (d i) * d i = 1 := by
      rw [← Complex.normSq_eq_conj_mul_self]
      norm_cast
      rw [Complex.normSq_eq_norm_sq, hd i]
      norm_num
    show conj (d i) * (d i * z.ofLp i) = z.ofLp i
    rw [← mul_assoc, hdi, one_mul]
  right_inv z := by
    refine WithLp.ofLp_injective (p := 2) ?_
    funext i
    have hdi : d i * conj (d i) = 1 := by
      rw [Complex.mul_conj]
      norm_cast
      rw [Complex.normSq_eq_norm_sq, hd i]
      norm_num
    show d i * (conj (d i) * z.ofLp i) = z.ofLp i
    rw [← mul_assoc, hdi, one_mul]
  norm_map' z := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    show ‖d i * z.ofLp i‖ ^ 2 = ‖z.ofLp i‖ ^ 2
    rw [norm_mul, hd i, one_mul]

theorem phaseMultiplication_apply (d : ι → ℂ) (hd : ∀ i, ‖d i‖ = 1)
    (z : EuclideanSpace ℂ ι) :
    (phaseMultiplication d hd z).ofLp = fun i => d i * z.ofLp i := rfl

end PhaseMultiplication

section MatrixOperator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem isSelfAdjoint_toEuclideanCLM {A : Matrix ι ι ℂ} (hA : Aᴴ = A) :
    IsSelfAdjoint (Matrix.toEuclideanCLM (𝕜 := ℂ) A) := by
  have : star (Matrix.toEuclideanCLM (𝕜 := ℂ) A) = Matrix.toEuclideanCLM (𝕜 := ℂ) (star A) :=
    (map_star (Matrix.toEuclideanCLM (𝕜 := ℂ)) A).symm
  rw [IsSelfAdjoint, this, Matrix.star_eq_conjTranspose, hA]

theorem toEuclideanCLM_mul_apply (A B : Matrix ι ι ℂ) (z : EuclideanSpace ℂ ι) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) (A * B) z =
      Matrix.toEuclideanCLM (𝕜 := ℂ) A (Matrix.toEuclideanCLM (𝕜 := ℂ) B z) := by
  rw [map_mul]
  rfl

end MatrixOperator

section StaticModel

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : Type*} [Fintype G]

/-- Replica energy defect of a vectorized coordinate of a diagonal Hamiltonian. -/
def replicaEnergyDefect (r : ℕ) (energy : α → ℝ) (p : (Fin r → α) × (Fin r → α)) : ℝ :=
  (∑ a, energy (p.1 a)) - ∑ a, energy (p.2 a)

/-- Time evolution of a state under a diagonal Hamiltonian. -/
def diagonalEvolvedState (energy : α → ℝ) (t : ℝ) (ψ : α → ℂ) : α → ℂ :=
  fun a => Complex.exp ((-(t * energy a) : ℝ) * Complex.I) * ψ a

omit [Fintype α] [DecidableEq α] in
theorem norm_replicaEvolutionPhase (r : ℕ) (energy : α → ℝ) (t : ℝ)
    (p : (Fin r → α) × (Fin r → α)) :
    ‖Complex.exp ((-(t * replicaEnergyDefect r energy p) : ℝ) * Complex.I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

/-- The adjoint action of a diagonal Hamiltonian on the vectorized replica space. -/
def staticReplicaFlow (r : ℕ) (energy : α → ℝ) (t : ℝ) :
    EuclideanSpace ℂ ((Fin r → α) × (Fin r → α)) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ ((Fin r → α) × (Fin r → α)) :=
  phaseMultiplication
    (fun p => Complex.exp ((-(t * replicaEnergyDefect r energy p) : ℝ) * Complex.I))
    (norm_replicaEvolutionPhase r energy t)

/-- Diagonal symbol of the completed static projection. -/
def completedStaticSymbol (r : ℕ) (energy : α → ℝ)
    (p : (Fin r → α) × (Fin r → α)) : ℂ :=
  if replicaEnergyDefect r energy p = 0 then 1 else 0

/-- Projection onto the completed static spectrum, i.e. onto zero replica energy defect. -/
def completedStaticProjection (r : ℕ) (energy : α → ℝ) :
    EuclideanSpace ℂ ((Fin r → α) × (Fin r → α)) →L[ℂ]
      EuclideanSpace ℂ ((Fin r → α) × (Fin r → α)) :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (Matrix.diagonal (completedStaticSymbol r energy))

theorem completedStaticProjection_apply (r : ℕ) (energy : α → ℝ)
    (z : EuclideanSpace ℂ ((Fin r → α) × (Fin r → α))) :
    (completedStaticProjection r energy z).ofLp =
      fun p => completedStaticSymbol r energy p * z.ofLp p := by
  have h := Matrix.toEuclideanCLM_toLp (𝕜 := ℂ)
    (Matrix.diagonal (completedStaticSymbol r energy)) z.ofLp
  rw [WithLp.toLp_ofLp] at h
  rw [completedStaticProjection, h, WithLp.ofLp_toLp]
  funext p
  simp [Matrix.mulVec_diagonal]

theorem isSelfAdjoint_completedStaticProjection (r : ℕ) (energy : α → ℝ) :
    IsSelfAdjoint (completedStaticProjection r energy) := by
  refine isSelfAdjoint_toEuclideanCLM ?_
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext p
  simp only [Pi.star_apply, completedStaticSymbol, RCLike.star_def]
  by_cases h : replicaEnergyDefect r energy p = 0 <;> simp [h]

theorem completedStaticProjection_idem (r : ℕ) (energy : α → ℝ)
    (z : EuclideanSpace ℂ ((Fin r → α) × (Fin r → α))) :
    completedStaticProjection r energy (completedStaticProjection r energy z) =
      completedStaticProjection r energy z := by
  refine WithLp.ofLp_injective (p := 2) ?_
  rw [completedStaticProjection_apply, completedStaticProjection_apply]
  funext p
  rw [← mul_assoc]
  congr 1
  simp only [completedStaticSymbol]
  by_cases h : replicaEnergyDefect r energy p = 0 <;> simp [h]

theorem completedStaticProjection_staticReplicaFlow (r : ℕ) (energy : α → ℝ) (t : ℝ)
    (z : EuclideanSpace ℂ ((Fin r → α) × (Fin r → α))) :
    completedStaticProjection r energy (staticReplicaFlow r energy t z) =
      completedStaticProjection r energy z := by
  refine WithLp.ofLp_injective (p := 2) ?_
  rw [completedStaticProjection_apply, completedStaticProjection_apply, staticReplicaFlow,
    phaseMultiplication_apply]
  funext p
  simp only [completedStaticSymbol]
  by_cases h : replicaEnergyDefect r energy p = 0
  · simp [h]
  · simp [h]

theorem staticReplicaFlow_completedStaticProjection (r : ℕ) (energy : α → ℝ) (t : ℝ)
    (z : EuclideanSpace ℂ ((Fin r → α) × (Fin r → α))) :
    staticReplicaFlow r energy t (completedStaticProjection r energy z) =
      completedStaticProjection r energy z := by
  refine WithLp.ofLp_injective (p := 2) ?_
  rw [staticReplicaFlow, phaseMultiplication_apply, completedStaticProjection_apply]
  funext p
  simp only [completedStaticSymbol]
  by_cases h : replicaEnergyDefect r energy p = 0
  · simp [h]
  · simp [h]

omit [DecidableEq α] in
theorem finitePureTensorPower_diagonalEvolvedState (r : ℕ) (energy : α → ℝ) (t : ℝ) (ψ : α → ℂ)
    (x : Fin r → α) :
    finitePureTensorPower r (diagonalEvolvedState energy t ψ) x =
      Complex.exp ((-(t * ∑ a, energy (x a)) : ℝ) * Complex.I) * finitePureTensorPower r ψ x := by
  simp only [finitePureTensorPower, diagonalEvolvedState]
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum, ← Finset.sum_mul]
  congr 3
  push_cast
  simp [Finset.mul_sum]

omit [DecidableEq α] in
/-- The evolution carries a replica projector to the replica projector of the evolved state. -/
theorem staticReplicaFlow_replicaProjector (r : ℕ) (energy : α → ℝ) (t : ℝ) (ψ : α → ℂ) :
    staticReplicaFlow r energy t
        (finitePureProjectorEuclidean (finitePureTensorPower r ψ)) =
      finitePureProjectorEuclidean
        (finitePureTensorPower r (diagonalEvolvedState energy t ψ)) := by
  refine WithLp.ofLp_injective (p := 2) ?_
  rw [staticReplicaFlow, phaseMultiplication_apply]
  funext p
  show Complex.exp ((-(t * replicaEnergyDefect r energy p) : ℝ) * Complex.I) *
      finitePureProjectorCoordinate (finitePureTensorPower r ψ) p =
    finitePureProjectorCoordinate
      (finitePureTensorPower r (diagonalEvolvedState energy t ψ)) p
  simp only [finitePureProjectorCoordinate, finitePureTensorPower_diagonalEvolvedState, map_mul]
  have hconj : conj (Complex.exp ((-(t * ∑ a, energy (p.2 a)) : ℝ) * Complex.I)) =
      Complex.exp (((t * ∑ a, energy (p.2 a)) : ℝ) * Complex.I) := by
    rw [← Complex.exp_conj]
    congr 1
    simp
  rw [hconj]
  have hsplit : Complex.exp ((-(t * replicaEnergyDefect r energy p) : ℝ) * Complex.I) =
      Complex.exp ((-(t * ∑ a, energy (p.1 a)) : ℝ) * Complex.I) *
        Complex.exp (((t * ∑ a, energy (p.2 a)) : ℝ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    simp only [replicaEnergyDefect]
    push_cast
    ring
  rw [hsplit]
  ring

/-! ### The universal sector and the concrete three-sector collision -/

/-- Vectorized conjugation by the replica power of one gate. -/
def replicaGateConjugation (r : ℕ) (A : Matrix α α ℂ) :
    EuclideanSpace ℂ ((Fin r → α) × (Fin r → α)) →L[ℂ]
      EuclideanSpace ℂ ((Fin r → α) × (Fin r → α)) :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (pureConjugationChannel (replicaTensorPowerMatrix r A))

/-- The one-gate replica moment channel as an operator on the vectorized replica space. -/
def replicaMomentChannel (r : ℕ) (gate : G → Matrix α α ℂ) :
    EuclideanSpace ℂ ((Fin r → α) × (Fin r → α)) →L[ℂ]
      EuclideanSpace ℂ ((Fin r → α) × (Fin r → α)) :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (replicaGateMomentChannel r gate)

theorem replicaGateConjugation_comp_conjTranspose (r : ℕ) {A : Matrix α α ℂ}
    (hA : Aᴴ * A = 1) (z : EuclideanSpace ℂ ((Fin r → α) × (Fin r → α))) :
    replicaGateConjugation r Aᴴ (replicaGateConjugation r A z) = z := by
  rw [replicaGateConjugation, replicaGateConjugation, ← toEuclideanCLM_mul_apply,
    pureConjugationChannel_mul, ← replicaTensorPowerMatrix_mul, hA,
    replicaTensorPowerMatrix_one, pureConjugationChannel_one, map_one]
  rfl

theorem adjoint_replicaGateConjugation (r : ℕ) (A : Matrix α α ℂ) :
    ContinuousLinearMap.adjoint (replicaGateConjugation r A) = replicaGateConjugation r Aᴴ := by
  rw [replicaGateConjugation, replicaGateConjugation]
  have : star (Matrix.toEuclideanCLM (𝕜 := ℂ)
      (pureConjugationChannel (replicaTensorPowerMatrix r A))) =
      Matrix.toEuclideanCLM (𝕜 := ℂ)
        (star (pureConjugationChannel (replicaTensorPowerMatrix r A))) :=
    (map_star (Matrix.toEuclideanCLM (𝕜 := ℂ)) _).symm
  rw [show ContinuousLinearMap.adjoint (Matrix.toEuclideanCLM (𝕜 := ℂ)
      (pureConjugationChannel (replicaTensorPowerMatrix r A))) =
      star (Matrix.toEuclideanCLM (𝕜 := ℂ)
        (pureConjugationChannel (replicaTensorPowerMatrix r A))) from rfl, this,
    Matrix.star_eq_conjTranspose, pureConjugationChannel_conjTranspose,
    replicaTensorPowerMatrix_conjTranspose]

theorem replicaMomentChannel_eq_average (r : ℕ) (gate : G → Matrix α α ℂ)
    (z : EuclideanSpace ℂ ((Fin r → α) × (Fin r → α))) :
    replicaMomentChannel r gate z =
      (Fintype.card G : ℂ)⁻¹ • ∑ g, replicaGateConjugation r (gate g) z := by
  rw [replicaMomentChannel, replicaGateMomentChannel, map_smul, map_sum]
  simp only [FunLike.coe_smul, Pi.smul_apply, FunLike.coe_sum, Finset.sum_apply]
  rfl

/-- Vectors fixed by every gate conjugation and carried by the completed static spectrum. -/
def circuitUniversalSector (r : ℕ) (energy : α → ℝ) (gate : G → Matrix α α ℂ) :
    Submodule ℂ (EuclideanSpace ℂ ((Fin r → α) × (Fin r → α))) where
  carrier := {z | (∀ g, replicaGateConjugation r (gate g) z = z) ∧
    completedStaticProjection r energy z = z}
  add_mem' := by
    rintro u v ⟨hu1, hu2⟩ ⟨hv1, hv2⟩
    exact ⟨fun g => by rw [map_add, hu1 g, hv1 g], by rw [map_add, hu2, hv2]⟩
  zero_mem' := ⟨fun g => by rw [map_zero], by rw [map_zero]⟩
  smul_mem' := by
    rintro c u ⟨hu1, hu2⟩
    exact ⟨fun g => by rw [map_smul, hu1 g], by rw [map_smul, hu2]⟩

omit [Fintype G] in
theorem mem_circuitUniversalSector_iff (r : ℕ) (energy : α → ℝ) (gate : G → Matrix α α ℂ)
    (z : EuclideanSpace ℂ ((Fin r → α) × (Fin r → α))) :
    z ∈ circuitUniversalSector r energy gate ↔
      (∀ g, replicaGateConjugation r (gate g) z = z) ∧
        completedStaticProjection r energy z = z := Iff.rfl

/-- Projection onto the universal sector. -/
def universalReplicaProjection (r : ℕ) (energy : α → ℝ) (gate : G → Matrix α α ℂ) :
    EuclideanSpace ℂ ((Fin r → α) × (Fin r → α)) →L[ℂ]
      EuclideanSpace ℂ ((Fin r → α) × (Fin r → α)) :=
  (circuitUniversalSector r energy gate).starProjection

omit [Fintype G] in
theorem isSelfAdjoint_universalReplicaProjection (r : ℕ) (energy : α → ℝ)
    (gate : G → Matrix α α ℂ) :
    IsSelfAdjoint (universalReplicaProjection r energy gate) :=
  isSelfAdjoint_starProjection _

omit [Fintype G] in
theorem universalReplicaProjection_idem (r : ℕ) (energy : α → ℝ) (gate : G → Matrix α α ℂ)
    (z : EuclideanSpace ℂ ((Fin r → α) × (Fin r → α))) :
    universalReplicaProjection r energy gate (universalReplicaProjection r energy gate z) =
      universalReplicaProjection r energy gate z :=
  Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ z)

omit [Fintype G] in
theorem completedStaticProjection_universalReplicaProjection (r : ℕ) (energy : α → ℝ)
    (gate : G → Matrix α α ℂ) (z : EuclideanSpace ℂ ((Fin r → α) × (Fin r → α))) :
    completedStaticProjection r energy (universalReplicaProjection r energy gate z) =
      universalReplicaProjection r energy gate z :=
  (Submodule.starProjection_apply_mem (circuitUniversalSector r energy gate) z).2

omit [Fintype G] in
/-- If an operator fixes the universal sector pointwise, the universal projection cannot see it. -/
theorem universalReplicaProjection_of_adjoint_fixes (r : ℕ) (energy : α → ℝ)
    (gate : G → Matrix α α ℂ)
    (T : EuclideanSpace ℂ ((Fin r → α) × (Fin r → α)) →L[ℂ]
      EuclideanSpace ℂ ((Fin r → α) × (Fin r → α)))
    (hT : ∀ w ∈ circuitUniversalSector r energy gate, ContinuousLinearMap.adjoint T w = w)
    (z : EuclideanSpace ℂ ((Fin r → α) × (Fin r → α))) :
    universalReplicaProjection r energy gate (T z) =
      universalReplicaProjection r energy gate z := by
  have hperp : T z - z ∈ (circuitUniversalSector r energy gate)ᗮ := by
    intro w hw
    rw [inner_sub_right, ← ContinuousLinearMap.adjoint_inner_left, hT w hw, sub_self]
  have hzero : universalReplicaProjection r energy gate (T z - z) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff _).mpr hperp
  rw [map_sub] at hzero
  exact sub_eq_zero.mp hzero

omit [Fintype G] in
theorem universalReplicaProjection_completedStaticProjection (r : ℕ) (energy : α → ℝ)
    (gate : G → Matrix α α ℂ) (z : EuclideanSpace ℂ ((Fin r → α) × (Fin r → α))) :
    universalReplicaProjection r energy gate (completedStaticProjection r energy z) =
      universalReplicaProjection r energy gate z := by
  refine universalReplicaProjection_of_adjoint_fixes r energy gate _ ?_ z
  intro w hw
  rw [(isSelfAdjoint_completedStaticProjection r energy).adjoint_eq]
  exact hw.2

/-- **Universal invariance of the preparation channel.**  The universal projection is unchanged by
one step of the moment channel of a unitary gate alphabet. -/
theorem universalReplicaProjection_replicaMomentChannel [Nonempty G] (r : ℕ) (energy : α → ℝ)
    (gate : G → Matrix α α ℂ) (hgate : ∀ g, (gate g)ᴴ * gate g = 1)
    (z : EuclideanSpace ℂ ((Fin r → α) × (Fin r → α))) :
    universalReplicaProjection r energy gate (replicaMomentChannel r gate z) =
      universalReplicaProjection r energy gate z := by
  refine universalReplicaProjection_of_adjoint_fixes r energy gate _ ?_ z
  intro w hw
  have hadj : ContinuousLinearMap.adjoint (replicaMomentChannel r gate) w =
      (Fintype.card G : ℂ)⁻¹ • ∑ g, replicaGateConjugation r ((gate g)ᴴ) w := by
    rw [replicaMomentChannel, replicaGateMomentChannel]
    have hstar : star (Matrix.toEuclideanCLM (𝕜 := ℂ)
        ((Fintype.card G : ℂ)⁻¹ •
          ∑ g, pureConjugationChannel (replicaTensorPowerMatrix r (gate g)))) =
        Matrix.toEuclideanCLM (𝕜 := ℂ)
          (star ((Fintype.card G : ℂ)⁻¹ •
            ∑ g, pureConjugationChannel (replicaTensorPowerMatrix r (gate g)))) :=
      (map_star (Matrix.toEuclideanCLM (𝕜 := ℂ)) _).symm
    rw [show ContinuousLinearMap.adjoint (Matrix.toEuclideanCLM (𝕜 := ℂ)
        ((Fintype.card G : ℂ)⁻¹ •
          ∑ g, pureConjugationChannel (replicaTensorPowerMatrix r (gate g)))) =
        star (Matrix.toEuclideanCLM (𝕜 := ℂ)
          ((Fintype.card G : ℂ)⁻¹ •
            ∑ g, pureConjugationChannel (replicaTensorPowerMatrix r (gate g)))) from rfl, hstar]
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_smul, Matrix.conjTranspose_sum]
    simp only [pureConjugationChannel_conjTranspose, replicaTensorPowerMatrix_conjTranspose,
      RCLike.star_def, map_inv₀, Complex.conj_natCast]
    rw [map_smul, map_sum]
    simp only [FunLike.coe_smul, Pi.smul_apply, FunLike.coe_sum, Finset.sum_apply]
    rfl
  rw [hadj]
  have hfix : ∀ g : G, replicaGateConjugation r ((gate g)ᴴ) w = w := fun g => by
    conv_lhs => rw [← hw.1 g]
    exact replicaGateConjugation_comp_conjTranspose r (hgate g) w
  simp only [hfix, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀, one_smul]
  exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero

end StaticModel

section Capstone

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : Type*} [Fintype G] [Nonempty G]

/-- The depth-`s` circuit preparation moment of a replica seed projector. -/
def replicaCircuitPreparationMoment (r s : ℕ) (gate : G → Matrix α α ℂ) (ψ : α → ℂ) :
    EuclideanSpace ℂ ((Fin r → α) × (Fin r → α)) :=
  ((replicaMomentChannel r gate) ^ s) (finitePureProjectorEuclidean (finitePureTensorPower r ψ))

omit [Nonempty G] in
theorem replicaCircuitPreparationMoment_ofLp (r s : ℕ) (gate : G → Matrix α α ℂ) (ψ : α → ℂ) :
    (replicaCircuitPreparationMoment r s gate ψ).ofLp =
      ((replicaGateMomentChannel r gate) ^ s).mulVec
        (finitePureProjectorCoordinate (finitePureTensorPower r ψ)) := by
  rw [replicaCircuitPreparationMoment, replicaMomentChannel, ← map_pow]
  rw [show finitePureProjectorEuclidean (finitePureTensorPower r ψ) =
    WithLp.toLp 2 (finitePureProjectorCoordinate (finitePureTensorPower r ψ)) from rfl,
    Matrix.toEuclideanCLM_toLp, WithLp.ofLp_toLp]

/-- **Exact circuit collision.**  Pairing the evolved replica projector with the depth-`s`
preparation moment gives the normalized replica collision of the depth-`s` fidelity dictionary. -/
theorem inner_staticReplicaFlow_replicaCircuitPreparationMoment
    (r s : ℕ) (energy : α → ℝ) (t : ℝ) (gate : G → Matrix α α ℂ) (ψ : α → ℂ) :
    inner ℂ (staticReplicaFlow r energy t
        (finitePureProjectorEuclidean (finitePureTensorPower r ψ)))
        (replicaCircuitPreparationMoment r s gate ψ) =
      ((finiteDictionaryReplicaCollision
        (fun w : Fin s → G => finitePureStateFidelity
          (diagonalEvolvedState energy t ψ) (wordPreparedState gate s w ψ)) r : ℝ) : ℂ) := by
  rw [staticReplicaFlow_replicaProjector]
  rw [show replicaCircuitPreparationMoment r s gate ψ =
    WithLp.toLp 2 (((replicaGateMomentChannel r gate) ^ s).mulVec
      (finitePureProjectorCoordinate (finitePureTensorPower r ψ))) by
    rw [← replicaCircuitPreparationMoment_ofLp, WithLp.toLp_ofLp]]
  rw [show finitePureProjectorEuclidean
      (finitePureTensorPower r (diagonalEvolvedState energy t ψ)) =
    WithLp.toLp 2 (finitePureProjectorCoordinate
      (finitePureTensorPower r (diagonalEvolvedState energy t ψ))) from rfl,
    inner_toLp_eq_finiteComplexInner,
    finiteComplexInner_replicaGateMomentChannel_pow_eq_dictionaryCollision]

/-- **Concrete three-sector circuit collision.**  For a static diagonal Hamiltonian and a unitary
gate alphabet, the depth-`s` circuit collision of the evolved replica seed splits into the
universal floor, the static-memory alignment and the dynamical-memory alignment. -/
theorem staticCircuitReplicaCollision_threeSector
    (r s : ℕ) (energy : α → ℝ) (t : ℝ) (gate : G → Matrix α α ℂ)
    (hgate : ∀ g, (gate g)ᴴ * gate g = 1) (ψ : α → ℂ) :
    ((finiteDictionaryReplicaCollision
        (fun w : Fin s → G => finitePureStateFidelity
          (diagonalEvolvedState energy t ψ) (wordPreparedState gate s w ψ)) r : ℝ) : ℂ) =
      inner ℂ
          (universalSector (universalReplicaProjection r energy gate)
            (finitePureProjectorEuclidean (finitePureTensorPower r ψ)))
          (universalSector (universalReplicaProjection r energy gate)
            (finitePureProjectorEuclidean (finitePureTensorPower r ψ))) +
        inner ℂ
          (staticMemory (universalReplicaProjection r energy gate)
            (completedStaticProjection r energy)
            (finitePureProjectorEuclidean (finitePureTensorPower r ψ)))
          (preparationMemory (universalReplicaProjection r energy gate)
            (finitePureProjectorEuclidean (finitePureTensorPower r ψ))
            (replicaCircuitPreparationMoment r s gate ψ)) +
        inner ℂ
          (dynamicMemory (completedStaticProjection r energy) (staticReplicaFlow r energy t)
            (finitePureProjectorEuclidean (finitePureTensorPower r ψ)))
          (preparationMemory (universalReplicaProjection r energy gate)
            (finitePureProjectorEuclidean (finitePureTensorPower r ψ))
            (replicaCircuitPreparationMoment r s gate ψ)) := by
  rw [← inner_staticReplicaFlow_replicaCircuitPreparationMoment r s energy t gate ψ]
  refine twoMemory_collision (universalReplicaProjection r energy gate)
    (completedStaticProjection r energy) (staticReplicaFlow r energy t) _ _
    (isSelfAdjoint_universalReplicaProjection r energy gate)
    (universalReplicaProjection_idem r energy gate)
    (universalReplicaProjection_completedStaticProjection r energy gate)
    (completedStaticProjection_staticReplicaFlow r energy t) ?_
  exact projection_preparation_pow_invariant (universalReplicaProjection r energy gate)
    (replicaMomentChannel r gate)
    (universalReplicaProjection_replicaMomentChannel r energy gate hgate) s _

/-- Universal floor of a concrete circuit collision at replica order `r`. -/
def staticCircuitUniversalFloor (r : ℕ) (energy : α → ℝ) (gate : G → Matrix α α ℂ)
    (ψ : α → ℂ) : ℂ :=
  inner ℂ
    (universalSector (universalReplicaProjection r energy gate)
      (finitePureProjectorEuclidean (finitePureTensorPower r ψ)))
    (universalSector (universalReplicaProjection r energy gate)
      (finitePureProjectorEuclidean (finitePureTensorPower r ψ)))

/-- Static-memory alignment of a concrete circuit collision at replica order `r`. -/
def staticCircuitStaticAlignment (r s : ℕ) (energy : α → ℝ) (gate : G → Matrix α α ℂ)
    (ψ : α → ℂ) : ℂ :=
  inner ℂ
    (staticMemory (universalReplicaProjection r energy gate)
      (completedStaticProjection r energy)
      (finitePureProjectorEuclidean (finitePureTensorPower r ψ)))
    (preparationMemory (universalReplicaProjection r energy gate)
      (finitePureProjectorEuclidean (finitePureTensorPower r ψ))
      (replicaCircuitPreparationMoment r s gate ψ))

/-- Dynamical-memory alignment of a concrete circuit collision at replica order `r`. -/
def staticCircuitDynamicAlignment (r s : ℕ) (energy : α → ℝ) (t : ℝ)
    (gate : G → Matrix α α ℂ) (ψ : α → ℂ) : ℂ :=
  inner ℂ
    (dynamicMemory (completedStaticProjection r energy) (staticReplicaFlow r energy t)
      (finitePureProjectorEuclidean (finitePureTensorPower r ψ)))
    (preparationMemory (universalReplicaProjection r energy gate)
      (finitePureProjectorEuclidean (finitePureTensorPower r ψ))
      (replicaCircuitPreparationMoment r s gate ψ))

theorem staticCircuitCollision_eq_threeSector
    (r s : ℕ) (energy : α → ℝ) (t : ℝ) (gate : G → Matrix α α ℂ)
    (hgate : ∀ g, (gate g)ᴴ * gate g = 1) (ψ : α → ℂ) :
    ((finiteDictionaryReplicaCollision
        (fun w : Fin s → G => finitePureStateFidelity
          (diagonalEvolvedState energy t ψ) (wordPreparedState gate s w ψ)) r : ℝ) : ℂ) =
      staticCircuitUniversalFloor r energy gate ψ +
        staticCircuitStaticAlignment r s energy gate ψ +
        staticCircuitDynamicAlignment r s energy t gate ψ :=
  staticCircuitReplicaCollision_threeSector r s energy t gate hgate ψ

/-- **All-replica memory-sector reconstruction.**  The `r`-th root of the three-sector circuit
collision converges to the best fidelity reachable by a depth-`s` word. -/
theorem tendsto_staticCircuitThreeSector_rpow_inv
    (s : ℕ) (energy : α → ℝ) (t : ℝ) (gate : G → Matrix α α ℂ)
    (hgate : ∀ g, (gate g)ᴴ * gate g = 1) (ψ : α → ℂ) :
    Filter.Tendsto
      (fun r : ℕ =>
        (staticCircuitUniversalFloor r energy gate ψ +
          staticCircuitStaticAlignment r s energy gate ψ +
          staticCircuitDynamicAlignment r s energy t gate ψ).re ^ ((r : ℝ)⁻¹))
      Filter.atTop
      (nhds (finiteDictionaryMax fun w : Fin s → G =>
        finitePureStateFidelity (diagonalEvolvedState energy t ψ)
          (wordPreparedState gate s w ψ))) := by
  have hval : ∀ r : ℕ,
      (staticCircuitUniversalFloor r energy gate ψ +
        staticCircuitStaticAlignment r s energy gate ψ +
        staticCircuitDynamicAlignment r s energy t gate ψ).re =
      finiteDictionaryReplicaCollision
        (fun w : Fin s → G => finitePureStateFidelity
          (diagonalEvolvedState energy t ψ) (wordPreparedState gate s w ψ)) r := by
    intro r
    rw [← staticCircuitCollision_eq_threeSector r s energy t gate hgate ψ, Complex.ofReal_re]
  simpa only [hval] using
    tendsto_circuitCollision_rpow_inv (G := G) s gate ψ (φ := diagonalEvolvedState energy t ψ)

end Capstone

end

end GaloisForLFunctions.HTGeometry
