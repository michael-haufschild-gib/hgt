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
    simp only [RingHom.id_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, WithLp.ofLp_toLp]
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
  rw [completedStaticProjection, Matrix.toEuclideanCLM_toLp' ]
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

/-- The evolution carries a replica projector to the replica projector of the evolved state. -/
theorem staticReplicaFlow_replicaProjector (r : ℕ) (energy : α → ℝ) (t : ℝ) (ψ : α → ℂ) :
    staticReplicaFlow r energy t
        (finitePureProjectorEuclidean (finitePureTensorPower r ψ)) =
      finitePureProjectorEuclidean
        (finitePureTensorPower r (diagonalEvolvedState energy t ψ)) := by
  refine WithLp.ofLp_injective (p := 2) ?_
  rw [staticReplicaFlow, phaseMultiplication_apply]
  funext p
  simp only [finitePureProjectorEuclidean, WithLp.ofLp_toLp, finitePureProjectorCoordinate,
    finitePureTensorPower, diagonalEvolvedState, Finset.prod_mul_distrib, map_mul, map_prod,
    replicaEnergyDefect]
  rw [← Complex.exp_sum, ← Complex.exp_sum]
  have hconj : conj (Complex.exp (∑ a, ((-(t * energy (p.2 a)) : ℝ) * Complex.I))) =
      Complex.exp (∑ a, ((t * energy (p.2 a) : ℝ) * Complex.I)) := by
    rw [← Complex.exp_conj]
    congr 1
    rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [Complex.ext_iff]
  rw [hconj, ← Complex.exp_add]
  congr 1
  push_cast
  rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  ring_nf
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  ring_nf

end StaticModel

end

end GaloisForLFunctions.HTGeometry
