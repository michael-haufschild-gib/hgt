import GaloisForLFunctions.HTGeometry.PureConjugationChannel
import GaloisForLFunctions.HTGeometry.StaticCircuitEnsembleZeroTemperature

/-!
# The replica word dictionary of a one-gate moment channel

A finite gate alphabet defines one moment channel on the vectorized replica space: the uniform
average of the vectorized conjugations by the replica powers of the gates.  Iterating it `s` times
on the replica projector of a seed state produces exactly the uniform average of the replica
projectors of the states prepared by the depth-`s` gate words.

Pairing that iterate with the replica projector of any state therefore gives the exact
normalized dictionary collision: the average over depth-`s` words of the `r`th power of pure-state
fidelity.  Consequently the collision is a normalized replica collision of a finite dictionary of
fidelities, and its `r`th root converges to the best fidelity reachable at depth `s`.
-/

open Matrix

open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {G : Type*} [Fintype G]

/-- One-gate replica moment channel of a finite gate alphabet. -/
def replicaGateMomentChannel (r : ℕ) (gate : G → Matrix α α ℂ) :
    Matrix ((Fin r → α) × (Fin r → α)) ((Fin r → α) × (Fin r → α)) ℂ :=
  (Fintype.card G : ℂ)⁻¹ • ∑ g, pureConjugationChannel (replicaTensorPowerMatrix r (gate g))

/-- The state prepared from a seed by a depth-`s` gate word, outermost gate first. -/
def wordPreparedState (gate : G → Matrix α α ℂ) : ∀ s : ℕ, (Fin s → G) → (α → ℂ) → α → ℂ
  | 0, _, ψ => ψ
  | (s + 1), w, ψ => (gate (w 0)).mulVec (wordPreparedState gate s (Fin.tail w) ψ)

omit [DecidableEq α] [Fintype G] in
theorem wordPreparedState_zero (gate : G → Matrix α α ℂ) (w : Fin 0 → G) (ψ : α → ℂ) :
    wordPreparedState gate 0 w ψ = ψ := rfl

omit [DecidableEq α] [Fintype G] in
theorem wordPreparedState_cons (gate : G → Matrix α α ℂ) (s : ℕ) (g : G) (w : Fin s → G)
    (ψ : α → ℂ) :
    wordPreparedState gate (s + 1) (Fin.cons g w) ψ =
      (gate g).mulVec (wordPreparedState gate s w ψ) := by
  rw [wordPreparedState, Fin.cons_zero, Fin.tail_cons]

omit [DecidableEq α] in
/-- One gate step on a replica projector. -/
theorem pureConjugationChannel_replica_mulVec_projector
    (r : ℕ) (A : Matrix α α ℂ) (ψ : α → ℂ) :
    (pureConjugationChannel (replicaTensorPowerMatrix r A)).mulVec
        (finitePureProjectorCoordinate (finitePureTensorPower r ψ)) =
      finitePureProjectorCoordinate (finitePureTensorPower r (A.mulVec ψ)) := by
  rw [pureConjugationChannel_mulVec_projector, replicaTensorPowerMatrix_mulVec]

/-- **Circuit word expansion.**  The depth-`s` iterate of the one-gate moment channel on a replica
seed projector is the uniform average of the replica projectors of the depth-`s` word states. -/
theorem replicaGateMomentChannel_pow_mulVec
    (r : ℕ) (gate : G → Matrix α α ℂ) (ψ : α → ℂ) (s : ℕ) :
    ((replicaGateMomentChannel r gate) ^ s).mulVec
        (finitePureProjectorCoordinate (finitePureTensorPower r ψ)) =
      (((Fintype.card G : ℂ) ^ s)⁻¹) • ∑ w : Fin s → G,
        finitePureProjectorCoordinate (finitePureTensorPower r (wordPreparedState gate s w ψ)) := by
  induction s with
  | zero =>
      simp [Matrix.one_mulVec, wordPreparedState_zero]
  | succ s ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, replicaGateMomentChannel,
        smul_mulVec, Matrix.mulVec_smul, Matrix.sum_mulVec]
      have hstep : ∀ g : G,
          (pureConjugationChannel (replicaTensorPowerMatrix r (gate g))).mulVec
              (∑ w : Fin s → G,
                finitePureProjectorCoordinate
                  (finitePureTensorPower r (wordPreparedState gate s w ψ))) =
            ∑ w : Fin s → G,
              finitePureProjectorCoordinate
                (finitePureTensorPower r (wordPreparedState gate (s + 1) (Fin.cons g w) ψ)) := by
        intro g
        rw [Matrix.mulVec_sum]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [wordPreparedState_cons, pureConjugationChannel_replica_mulVec_projector]
      simp only [hstep]
      rw [smul_smul]
      have hreindex :
          (∑ g : G, ∑ w : Fin s → G,
              finitePureProjectorCoordinate
                (finitePureTensorPower r (wordPreparedState gate (s + 1) (Fin.cons g w) ψ))) =
            ∑ v : Fin (s + 1) → G,
              finitePureProjectorCoordinate
                (finitePureTensorPower r (wordPreparedState gate (s + 1) v ψ)) := by
        have hequiv := Fintype.sum_equiv (Fin.consEquiv fun _ : Fin (s + 1) => G)
          (fun p : G × (Fin s → G) =>
            finitePureProjectorCoordinate
              (finitePureTensorPower r (wordPreparedState gate (s + 1) (Fin.cons p.1 p.2) ψ)))
          (fun v : Fin (s + 1) → G =>
            finitePureProjectorCoordinate
              (finitePureTensorPower r (wordPreparedState gate (s + 1) v ψ)))
          (fun _ => rfl)
        rw [Fintype.sum_prod_type] at hequiv
        exact hequiv
      rw [hreindex]
      congr 1
      rw [pow_succ]
      field_simp

/-- The exact collision of a replica projector with the depth-`s` circuit preparation moment. -/
theorem finiteComplexInner_replicaGateMomentChannel_pow
    (r s : ℕ) (gate : G → Matrix α α ℂ) (ψ φ : α → ℂ) :
    finiteComplexInner (finitePureProjectorCoordinate (finitePureTensorPower r φ))
        (((replicaGateMomentChannel r gate) ^ s).mulVec
          (finitePureProjectorCoordinate (finitePureTensorPower r ψ))) =
      (((Fintype.card G : ℂ) ^ s)⁻¹) * ∑ w : Fin s → G,
        ((finitePureStateFidelity φ (wordPreparedState gate s w ψ) ^ r : ℝ) : ℂ) := by
  rw [replicaGateMomentChannel_pow_mulVec]
  simp only [finiteComplexInner, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hfid : (∑ x, conj (finitePureProjectorCoordinate (finitePureTensorPower r φ) x) *
        finitePureProjectorCoordinate (finitePureTensorPower r (wordPreparedState gate s w ψ)) x) =
      ((finitePureStateFidelity φ (wordPreparedState gate s w ψ) ^ r : ℝ) : ℂ) := by
    have := inner_finitePureProjectorEuclidean (α := Fin r → α)
      (finitePureTensorPower r φ) (finitePureTensorPower r (wordPreparedState gate s w ψ))
    rw [inner_toLp_eq_finiteComplexInner] at this
    rw [finitePureStateFidelity_tensorPower] at this
    simpa only [finiteComplexInner, finitePureProjectorEuclidean] using this
  rw [← hfid, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => by ring

/-- The circuit collision is the normalized replica collision of the finite fidelity dictionary of
depth-`s` words. -/
theorem finiteComplexInner_replicaGateMomentChannel_pow_eq_dictionaryCollision
    [Nonempty G] (r s : ℕ) (gate : G → Matrix α α ℂ) (ψ φ : α → ℂ) :
    finiteComplexInner (finitePureProjectorCoordinate (finitePureTensorPower r φ))
        (((replicaGateMomentChannel r gate) ^ s).mulVec
          (finitePureProjectorCoordinate (finitePureTensorPower r ψ))) =
      ((finiteDictionaryReplicaCollision
        (fun w : Fin s → G => finitePureStateFidelity φ (wordPreparedState gate s w ψ)) r : ℝ) :
          ℂ) := by
  rw [finiteComplexInner_replicaGateMomentChannel_pow, finiteDictionaryReplicaCollision,
    Fintype.card_fun, Fintype.card_fin]
  push_cast
  ring

omit [DecidableEq α] in
/-- **Zero-temperature circuit reconstruction.**  The `r`th root of the depth-`s` circuit collision
converges to the best fidelity of a depth-`s` word. -/
theorem tendsto_circuitCollision_rpow_inv
    [Nonempty G] (s : ℕ) (gate : G → Matrix α α ℂ) (ψ φ : α → ℂ) :
    Filter.Tendsto
      (fun r : ℕ => finiteDictionaryReplicaCollision
        (fun w : Fin s → G => finitePureStateFidelity φ (wordPreparedState gate s w ψ)) r ^
          ((r : ℝ)⁻¹))
      Filter.atTop
      (nhds (finiteDictionaryMax
        fun w : Fin s → G => finitePureStateFidelity φ (wordPreparedState gate s w ψ))) :=
  tendsto_finiteDictionaryReplicaCollision_rpow_inv fun w => by
    simpa only [finitePureStateFidelity] using sq_nonneg
      ‖finiteComplexInner φ (wordPreparedState gate s w ψ)‖

end

end GaloisForLFunctions.HTGeometry
