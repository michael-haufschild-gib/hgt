import GaloisForLFunctions.HTGeometry.ReplicaObserverActionCrowding

/-!
# The ordered replica law and its multiplicity pushforward

A replica history is an ordered tuple of levels; its weight is the product of the single-level
weights and its observed data depend only on the multiplicity vector of the tuple.  Pushing the
ordered law forward along the multiplicity map turns every weighted sum over ordered tuples into
the multinomial-amplitude sum over multiplicity vectors, so the two descriptions of a replica
average agree exactly.

Only the one-step decomposition of a tuple into its first entry and its tail is used, matched
against the corpus's amplitude recursion; no combinatorial count of arrangements is needed.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The multiplicity vector of an ordered replica tuple. -/
def orderedReplicaMultiplicity {r : ℕ} (α : Fin r → I) : I → ℕ :=
  fun j => (Finset.univ.filter fun l => α l = j).card

/-- The product weight of an ordered replica tuple. -/
def orderedReplicaWeight (weight : I → ℝ) {r : ℕ} (α : Fin r → I) : ℝ := ∏ l, weight (α l)

@[simp] theorem orderedReplicaMultiplicity_zero (α : Fin 0 → I) :
    orderedReplicaMultiplicity α = 0 := by
  funext j
  rw [orderedReplicaMultiplicity]
  simp

@[simp] theorem orderedReplicaWeight_zero (weight : I → ℝ) (α : Fin 0 → I) :
    orderedReplicaWeight weight α = 1 := by
  rw [orderedReplicaWeight]
  simp

theorem orderedReplicaMultiplicity_cons {r : ℕ} (j : I) (β : Fin r → I) :
    orderedReplicaMultiplicity (Fin.cons j β) =
      Function.update (orderedReplicaMultiplicity β) j (orderedReplicaMultiplicity β j + 1) := by
  classical
  funext k
  rw [orderedReplicaMultiplicity, orderedReplicaMultiplicity, Finset.card_filter,
    Finset.card_filter, Fin.sum_univ_succ, Function.update_apply]
  simp only [Fin.cons_zero, Fin.cons_succ]
  by_cases hk : k = j
  · subst hk
    rw [if_pos rfl, if_pos rfl]
    ring
  · rw [if_neg (fun h => hk h.symm), if_neg hk, zero_add]

theorem orderedReplicaWeight_cons (weight : I → ℝ) {r : ℕ} (j : I) (β : Fin r → I) :
    orderedReplicaWeight weight (Fin.cons j β) = weight j * orderedReplicaWeight weight β := by
  rw [orderedReplicaWeight, orderedReplicaWeight, Fin.prod_cons]

theorem sum_fin_succ_pi {r : ℕ} {M : Type*} [AddCommMonoid M] (G : (Fin (r + 1) → I) → M) :
    ∑ α : Fin (r + 1) → I, G α = ∑ j : I, ∑ β : Fin r → I, G (Fin.cons j β) := by
  classical
  rw [← Fintype.sum_equiv (Fin.consEquiv fun _ : Fin (r + 1) => I)
    (fun x : I × (Fin r → I) => G (Fin.cons x.1 x.2)) G (fun x => rfl)]
  exact Fintype.sum_prod_type _

/-- The total ordered replica weight is the `r`-th power of the total single-level weight. -/
theorem sum_orderedReplicaWeight (f : I → ℝ) (r : ℕ) :
    ∑ α : Fin r → I, orderedReplicaWeight f α = (∑ j, f j) ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [sum_fin_succ_pi, pow_succ]
      have hstep : ∀ j : I, ∑ β : Fin r → I, orderedReplicaWeight f (Fin.cons j β) =
          f j * (∑ k, f k) ^ r := by
        intro j
        rw [Finset.sum_congr rfl fun β _ => orderedReplicaWeight_cons f j β, ← Finset.mul_sum, ih]
      rw [Finset.sum_congr rfl fun j _ => hstep j, ← Finset.sum_mul]
      ring

/-- **Theorem C: the ordered replica law pushes forward to the multiplicity amplitude law.**
Every weighted average over ordered replica histories equals the multinomial-amplitude average over
their multiplicity vectors. -/
theorem sum_orderedReplica_eq_replicaAmplitudeMoment (weight : I → ℝ) (r : ℕ)
    (Φ : (I → ℕ) → ℝ) :
    ∑ α : Fin r → I, orderedReplicaWeight weight α * Φ (orderedReplicaMultiplicity α)
      = replicaAmplitudeMoment weight r Φ := by
  classical
  induction r generalizing Φ with
  | zero =>
      rw [replicaAmplitudeMoment_zero]
      simp
  | succ r ih =>
      rw [sum_fin_succ_pi, replicaAmplitudeMoment_succ]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← ih (fun p => Φ (Function.update p j (p j + 1))), Finset.mul_sum]
      refine Finset.sum_congr rfl fun β _ => ?_
      rw [orderedReplicaWeight_cons, orderedReplicaMultiplicity_cons, mul_assoc]

/-- The ordered replica law of a probability weighting is a probability law. -/
theorem sum_orderedReplicaWeight_eq_one {weight : I → ℝ} (hw : ∑ i, weight i = 1) (r : ℕ) :
    ∑ α : Fin r → I, orderedReplicaWeight weight α = 1 := by
  rw [sum_orderedReplicaWeight, hw, one_pow]

/-- **Theorem C for ordered pairs**: forward and backward replica histories push forward to the
pair of multiplicity vectors. -/
theorem sum_orderedReplicaPair_eq (weight : I → ℝ) (r : ℕ) (Ψ : (I → ℕ) → (I → ℕ) → ℝ) :
    (∑ α : Fin r → I, ∑ β : Fin r → I,
        orderedReplicaWeight weight α * orderedReplicaWeight weight β *
          Ψ (orderedReplicaMultiplicity α) (orderedReplicaMultiplicity β))
      = ∑ p ∈ Finset.univ.piAntidiag r, ∑ q ∈ Finset.univ.piAntidiag r,
          fidelityReplicaMultiplicityAmplitude weight p *
            (fidelityReplicaMultiplicityAmplitude weight q * Ψ p q) := by
  classical
  have hinner : ∀ α : Fin r → I,
      (∑ β : Fin r → I, orderedReplicaWeight weight α * orderedReplicaWeight weight β *
          Ψ (orderedReplicaMultiplicity α) (orderedReplicaMultiplicity β))
        = orderedReplicaWeight weight α *
            replicaAmplitudeMoment weight r (Ψ (orderedReplicaMultiplicity α)) := by
    intro α
    rw [← sum_orderedReplica_eq_replicaAmplitudeMoment weight r
      (Ψ (orderedReplicaMultiplicity α)), Finset.mul_sum]
    exact Finset.sum_congr rfl fun β _ => by ring
  rw [Finset.sum_congr rfl fun α _ => hinner α,
    sum_orderedReplica_eq_replicaAmplitudeMoment weight r
      (fun p => replicaAmplitudeMoment weight r (Ψ p)), replicaAmplitudeMoment]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [replicaAmplitudeMoment, Finset.mul_sum]

end GaloisForLFunctions.HTGeometry
