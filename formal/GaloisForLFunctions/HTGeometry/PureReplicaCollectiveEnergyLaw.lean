import GaloisForLFunctions.HTGeometry.BoundedReplicaThresholdProjector
import GaloisForLFunctions.HTGeometry.AllReplicaCollectivePauliCasimir

/-!
# Pure-replica collective energy law

Worst-case operator norms make a collective one-copy action on `r` tensor factors look quadratic
in `r`.  On a normalized tensor-power boundary, its Gram form has a different exact law.  If the
one-copy expectation is centered, every off-diagonal replica pair vanishes and the collective
energy is exactly `r` times the one-copy energy.

Commutator representations are automatically centered on every Hermitian matrix by trace
cyclicity.  In particular, normalized rank-one projectors realize the linear branch for every
finite generator and every replica count.  No randomness, spectral gap, or asymptotic limit is
used.
-/

open Finset Matrix
open scoped ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Slot factors for a one-copy operator acting in one distinguished replica. -/
def replicaSlotFactors (r : ℕ) (A : Matrix n n ℂ) (j : Fin r) :
    Fin r → Matrix n n ℂ := fun i => if i = j then A else 1

/-- One-copy operator lifted to one distinguished replica slot. -/
def replicaSlotOp (r : ℕ) (A : Matrix n n ℂ) (j : Fin r) :
    Matrix (Fin r → n) (Fin r → n) ℂ :=
  replicaOp r (replicaSlotFactors r A j)

/-- Sum of the same one-copy operator over all replica slots. -/
def collectiveReplicaSlotOp (r : ℕ) (A : Matrix n n ℂ) :
    Matrix (Fin r → n) (Fin r → n) ℂ :=
  ∑ j : Fin r, replicaSlotOp r A j

/-- The coordinate quadratic form is linear over a finite matrix sum. -/
theorem quadForm_univ_sum
    {m ι : Type*} [Fintype m] [Fintype ι]
    (M : ι → Matrix m m ℂ) (w : m → ℂ) :
    boundedReplicaThresholdProjectorQuadForm (∑ i, M i) w =
      ∑ i, boundedReplicaThresholdProjectorQuadForm (M i) w := by
  simpa using quadForm_sum (Finset.univ : Finset ι) M w

/-- Centering makes distinct replica-slot actions orthogonal on a tensor-power vector. -/
theorem quadForm_replicaSlot_gram_centered
    (r : ℕ) (A : Matrix n n ℂ) (v : n → ℂ)
    (hv : hermInner v v = 1)
    (hcenter : boundedReplicaThresholdProjectorQuadForm A v = 0)
    (i j : Fin r) :
    boundedReplicaThresholdProjectorQuadForm
        ((replicaSlotOp r A i)ᴴ * replicaSlotOp r A j)
        (replicaVector r v) =
      if i = j then
        boundedReplicaThresholdProjectorQuadForm (Aᴴ * A) v
      else 0 := by
  rw [replicaSlotOp, replicaSlotOp, replicaOp_conjTranspose, replicaOp_mul,
    quadForm_replicaOp]
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    rw [Fintype.prod_eq_mul_prod_compl i]
    have hprod :
        ∏ x ∈ ({i}ᶜ : Finset (Fin r)),
            boundedReplicaThresholdProjectorQuadForm
              ((replicaSlotFactors r A i x)ᴴ * replicaSlotFactors r A i x) v = 1 := by
      apply Finset.prod_eq_one
      intro x hx
      have hxi : x ≠ i := by simpa using hx
      simp [replicaSlotFactors, hxi, quadForm_one, hv]
    rw [hprod, mul_one]
    simp [replicaSlotFactors]
  · rw [if_neg hij]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [replicaSlotFactors, Ne.symm hij, hcenter]

/-- Without unit normalization, centering still kills every distinct-slot Gram entry.  The
diagonal entry is multiplied by the mass of each untouched replica. -/
theorem quadForm_replicaSlot_gram_centered_unnormalized
    (r : ℕ) (A : Matrix n n ℂ) (v : n → ℂ)
    (hcenter : boundedReplicaThresholdProjectorQuadForm A v = 0)
    (i j : Fin r) :
    boundedReplicaThresholdProjectorQuadForm
        ((replicaSlotOp r A i)ᴴ * replicaSlotOp r A j)
        (replicaVector r v) =
      if i = j then
        boundedReplicaThresholdProjectorQuadForm (Aᴴ * A) v *
          hermInner v v ^ (r - 1)
      else 0 := by
  rw [replicaSlotOp, replicaSlotOp, replicaOp_conjTranspose, replicaOp_mul,
    quadForm_replicaOp]
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    rw [Fintype.prod_eq_mul_prod_compl i]
    have hprod :
        ∏ x ∈ ({i}ᶜ : Finset (Fin r)),
            boundedReplicaThresholdProjectorQuadForm
              ((replicaSlotFactors r A i x)ᴴ * replicaSlotFactors r A i x) v =
          hermInner v v ^ (r - 1) := by
      calc
        _ = ∏ _x ∈ ({i}ᶜ : Finset (Fin r)), hermInner v v := by
          apply Finset.prod_congr rfl
          intro x hx
          have hxi : x ≠ i := by simpa using hx
          simp [replicaSlotFactors, hxi, quadForm_one]
        _ = hermInner v v ^ (r - 1) := by
          rw [Finset.prod_const, Finset.card_compl]
          simp
    rw [hprod]
    simp [replicaSlotFactors]
  · rw [if_neg hij]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [replicaSlotFactors, Ne.symm hij, hcenter]

/-- **Centered collective replica energy law.**  The collective Gram energy is exactly linear,
not quadratic, in replica number. -/
theorem collectiveReplicaSlotOp_centered_energy
    (r : ℕ) (A : Matrix n n ℂ) (v : n → ℂ)
    (hv : hermInner v v = 1)
    (hcenter : boundedReplicaThresholdProjectorQuadForm A v = 0) :
    boundedReplicaThresholdProjectorQuadForm
        ((collectiveReplicaSlotOp r A)ᴴ * collectiveReplicaSlotOp r A)
        (replicaVector r v) =
      (r : ℂ) * boundedReplicaThresholdProjectorQuadForm (Aᴴ * A) v := by
  rw [collectiveReplicaSlotOp, Matrix.conjTranspose_sum, Finset.sum_mul_sum,
    quadForm_univ_sum]
  simp_rw [quadForm_univ_sum]
  simp_rw [quadForm_replicaSlot_gram_centered r A v hv hcenter]
  simp

/-- **Unnormalized centered collective energy law.**  A centered Hermitian cavity boundary keeps
the exact replica-linear factor, with only its untouched-copy mass `q^(r-1)`. -/
theorem collectiveReplicaSlotOp_centered_energy_unnormalized
    (r : ℕ) (A : Matrix n n ℂ) (v : n → ℂ)
    (hcenter : boundedReplicaThresholdProjectorQuadForm A v = 0) :
    boundedReplicaThresholdProjectorQuadForm
        ((collectiveReplicaSlotOp r A)ᴴ * collectiveReplicaSlotOp r A)
        (replicaVector r v) =
      (r : ℂ) * boundedReplicaThresholdProjectorQuadForm (Aᴴ * A) v *
        hermInner v v ^ (r - 1) := by
  rw [collectiveReplicaSlotOp, Matrix.conjTranspose_sum, Finset.sum_mul_sum,
    quadForm_univ_sum]
  simp_rw [quadForm_univ_sum]
  simp_rw [quadForm_replicaSlot_gram_centered_unnormalized r A v hcenter]
  simp
  ring

/-- The expectation of a commutator representation on a vectorized matrix is its trace pairing
with the literal commutator. -/
theorem quadForm_matrixCommutatorRepresentation_vec
    (G X : Matrix n n ℂ) :
    boundedReplicaThresholdProjectorQuadForm
        (matrixCommutatorRepresentation G) (Matrix.vec X) =
      (Xᴴ * ringCommutator G X).trace := by
  rw [boundedReplicaThresholdProjectorQuadForm,
    matrixCommutatorRepresentation_mulVec_vec]
  change (∑ p : n × n,
      star (X p.2 p.1) * ringCommutator G X p.2 p.1) =
    ∑ i, ∑ j, star (X j i) * ringCommutator G X j i
  rw [Fintype.sum_prod_type]

/-- Every commutator representation is centered on every Hermitian matrix. -/
theorem quadForm_matrixCommutatorRepresentation_vec_centered
    (G X : Matrix n n ℂ) (hX : Xᴴ = X) :
    boundedReplicaThresholdProjectorQuadForm
        (matrixCommutatorRepresentation G) (Matrix.vec X) = 0 := by
  rw [quadForm_matrixCommutatorRepresentation_vec, hX, ringCommutator,
    Matrix.mul_sub, Matrix.trace_sub]
  rw [Matrix.trace_mul_comm X (G * X), ← Matrix.mul_assoc X X G,
    Matrix.mul_assoc G X X, Matrix.trace_mul_comm G (X * X), sub_self]

/-- Every Hermitian matrix boundary, including a mixed or cavity-dressed one, obeys the exact
unnormalized replica-linear commutator law. -/
theorem hermitian_collectiveReplicaCommutator_energy_unnormalized
    (r : ℕ) (G X : Matrix n n ℂ) (hX : Xᴴ = X) :
    boundedReplicaThresholdProjectorQuadForm
        ((collectiveReplicaSlotOp r (matrixCommutatorRepresentation G))ᴴ *
          collectiveReplicaSlotOp r (matrixCommutatorRepresentation G))
        (replicaVector r (Matrix.vec X)) =
      (r : ℂ) * boundedReplicaThresholdProjectorQuadForm
        ((matrixCommutatorRepresentation G)ᴴ *
          matrixCommutatorRepresentation G) (Matrix.vec X) *
        hermInner (Matrix.vec X) (Matrix.vec X) ^ (r - 1) := by
  apply collectiveReplicaSlotOp_centered_energy_unnormalized
  exact quadForm_matrixCommutatorRepresentation_vec_centered G X hX

omit [DecidableEq n] in
theorem hermInner_vec_rankOne (ψ : n → ℂ) :
    hermInner (Matrix.vec (rankOne ψ)) (Matrix.vec (rankOne ψ)) =
      hermInner ψ ψ * hermInner ψ ψ := by
  simp only [hermInner, Matrix.vec, rankOne_apply, map_mul, Complex.conj_conj]
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- **Physical pure-state law.**  For every normalized rank-one state, every finite generator and
every replica number, the collective commutator energy is exactly replica-linear. -/
theorem pureProjector_collectiveReplicaCommutator_energy
    (r : ℕ) (G : Matrix n n ℂ) (ψ : n → ℂ)
    (hψ : hermInner ψ ψ = 1) :
    boundedReplicaThresholdProjectorQuadForm
        ((collectiveReplicaSlotOp r (matrixCommutatorRepresentation G))ᴴ *
          collectiveReplicaSlotOp r (matrixCommutatorRepresentation G))
        (replicaVector r (Matrix.vec (rankOne ψ))) =
      (r : ℂ) * boundedReplicaThresholdProjectorQuadForm
        ((matrixCommutatorRepresentation G)ᴴ *
          matrixCommutatorRepresentation G)
        (Matrix.vec (rankOne ψ)) := by
  apply collectiveReplicaSlotOp_centered_energy
  · rw [hermInner_vec_rankOne, hψ, one_mul]
  · apply quadForm_matrixCommutatorRepresentation_vec_centered
    exact rankOne_conjTranspose ψ

end

end GaloisForLFunctions.HTGeometry
