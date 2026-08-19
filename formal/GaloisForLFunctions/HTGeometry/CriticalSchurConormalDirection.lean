import GaloisForLFunctions.HTGeometry.CriticalRawCotangentBasis

/-!
# The conormal direction of the branch, in cotangent form

Ramification at the Schur place says the extended maximal ideal lies in the square of the maximal
ideal upstairs.  Leibniz turns that into a statement about coordinates: the differential of any
non-unit of the observation Schur place has every raw coordinate in the maximal ideal of the source
Schur place.

```text
repr_D_mem_maximalIdeal_of_mem_sq                 general form
criticalSchur_repr_D_observation_mem_maximalIdeal
```

Read through the observation Jacobian, this says the coordinate vector of the differential of a
uniformizer of the observation Schur place is killed by the reduced Jacobian — it spans the
conormal line of the branch.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open KaehlerDifferential IsLocalRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000

/-- **A differential of a square element has all coordinates in the maximal ideal.**  Leibniz turns
a product of two non-units into a combination of differentials with non-unit coefficients. -/
theorem repr_D_mem_maximalIdeal_of_mem_sq
    {k B : Type*} [CommRing k] [CommRing B] [Algebra k B] [IsLocalRing B]
    {ι : Type*} (b : Module.Basis ι B Ω[B⁄k]) {x : B} (hx : x ∈ (maximalIdeal B) ^ 2) (i : ι) :
    b.repr (KaehlerDifferential.D k B x) i ∈ maximalIdeal B := by
  rw [pow_two] at hx
  refine Submodule.mul_induction_on hx ?_ ?_
  · intro y hy z hz
    rw [Derivation.leibniz, map_add, Finsupp.add_apply, map_smul, map_smul,
      Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hy) (Ideal.mul_mem_right _ _ hz)
  · intro y z hy hz
    rw [map_add, map_add, Finsupp.add_apply]
    exact Ideal.add_mem _ hy hz

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}
variable [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]

/-- **The differential of a non-unit of the observation Schur place is non-unit in every raw
coordinate.**  This is the ramification statement `(R)` in cotangent form: the conormal direction
of the branch is visible in the raw basis with non-unit coordinates. -/
theorem criticalSchur_repr_D_observation_mem_maximalIdeal
    (δ : criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
    (hδ : δ ∈ maximalIdeal
      (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)))
    (t : Fin m ⊕ Fin n) :
    (criticalRawBlockCotangentBasis K (m := m) (n := n)).repr
        (KaehlerDifferential.D K
          (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
          (algebraMap
            (criticalSchurObservationValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n))
            (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) δ)) t
      ∈ maximalIdeal
          (criticalSchurSourceValuationSubring K (Fact.out : 0 < m) (Fact.out : 0 < n)) :=
  repr_D_mem_maximalIdeal_of_mem_sq _
    (criticalSchur_map_maximalIdeal_le_sq K (Ideal.mem_map_of_mem _ hδ)) t

end

end GaloisForLFunctions.HTGeometry
