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
  simp only [orderedReplicaMultiplicity, Function.update_apply, Finset.card_filter,
    Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  by_cases hk : k = j
  · subst hk
    rw [if_pos rfl, if_pos rfl]
    ring
  · rw [if_neg (fun h => hk h.symm), if_neg hk, zero_add]

theorem orderedReplicaWeight_cons (weight : I → ℝ) {r : ℕ} (j : I) (β : Fin r → I) :
    orderedReplicaWeight weight (Fin.cons j β) = weight j * orderedReplicaWeight weight β := by
  rw [orderedReplicaWeight, orderedReplicaWeight, Fin.prod_univ_succ]
  simp

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


/-! ## The observer character of the replica pair lift -/

section Monoid

variable {R : Type*} [CommMonoid R]

/-- The product of a single-level datum along an ordered replica history. -/
def orderedReplicaProduct (w : I → R) {r : ℕ} (α : Fin r → I) : R := ∏ l, w (α l)

theorem orderedReplicaProduct_cons (w : I → R) {r : ℕ} (j : I) (β : Fin r → I) :
    orderedReplicaProduct w (Fin.cons j β) = w j * orderedReplicaProduct w β := by
  rw [orderedReplicaProduct, orderedReplicaProduct, Fin.prod_univ_succ]
  simp

theorem orderedReplicaProduct_eq_prod_pow (w : I → R) {r : ℕ} (α : Fin r → I) :
    orderedReplicaProduct w α = ∏ j, w j ^ orderedReplicaMultiplicity α j := by
  classical
  rw [orderedReplicaProduct,
    ← Finset.prod_fiberwise_of_maps_to (g := α) (fun x _ => Finset.mem_univ (α x))
      (fun l => w (α l))]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [orderedReplicaMultiplicity, ← Finset.prod_const]
  exact Finset.prod_congr rfl fun l hl => by rw [(Finset.mem_filter.mp hl).2]

end Monoid

section Ring

variable {R : Type*} [CommSemiring R]

/-- **The replica generating identity.**  Summing the product datum over all ordered replica
histories gives the `r`-th power of the single-level total. -/
theorem sum_orderedReplicaProduct (w : I → R) (r : ℕ) :
    ∑ α : Fin r → I, orderedReplicaProduct w α = (∑ j, w j) ^ r := by
  induction r with
  | zero => simp [orderedReplicaProduct]
  | succ r ih =>
      rw [sum_fin_succ_pi, pow_succ]
      have hstep : ∀ j : I, ∑ β : Fin r → I, orderedReplicaProduct w (Fin.cons j β) =
          w j * (∑ k, w k) ^ r := by
        intro j
        rw [Finset.sum_congr rfl fun β _ => orderedReplicaProduct_cons w j β, ← Finset.mul_sum, ih]
      rw [Finset.sum_congr rfl fun j _ => hstep j, ← Finset.sum_mul]
      ring

end Ring

/-- **Theorem D, equation (29): the replica pair character.**  The forward–backward replica pair
sum of a complex single-level datum is the `r`-th power of the squared modulus of its total.  With
`g j = c̃_j exp(-i(t E_j + ⟨ξ, v_j⟩))` this is the card's observer character identity. -/
theorem orderedReplicaPair_character (g : I → ℂ) (r : ℕ) :
    (∑ α : Fin r → I, orderedReplicaProduct g α) *
        (starRingEnd ℂ) (∑ β : Fin r → I, orderedReplicaProduct g β)
      = ((Complex.normSq (∑ j, g j) : ℝ) : ℂ) ^ r := by
  rw [sum_orderedReplicaProduct, Complex.mul_conj, map_pow]
  push_cast
  ring

/-- **Theorem D, equation (31): the off-return total mass.**  For a probability weighting the mass
of ordered replica pairs with distinct multiplicity vectors is exactly one minus the collision
mass. -/
theorem sum_orderedReplicaPair_offDiagonal {weight : I → ℝ} (hw : ∑ i, weight i = 1) (r : ℕ) :
    (∑ α : Fin r → I, ∑ β : Fin r → I,
        if orderedReplicaMultiplicity α ≠ orderedReplicaMultiplicity β then
          orderedReplicaWeight weight α * orderedReplicaWeight weight β else 0)
      = 1 - ∑ p ∈ Finset.univ.piAntidiag r,
          fidelityReplicaMultiplicityAmplitude weight p ^ 2 := by
  classical
  have hrewrite : ∀ α β : Fin r → I,
      (if orderedReplicaMultiplicity α ≠ orderedReplicaMultiplicity β then
          orderedReplicaWeight weight α * orderedReplicaWeight weight β else 0) =
        orderedReplicaWeight weight α * orderedReplicaWeight weight β *
          (if orderedReplicaMultiplicity α ≠ orderedReplicaMultiplicity β then 1 else 0) := by
    intro α β
    by_cases h : orderedReplicaMultiplicity α ≠ orderedReplicaMultiplicity β
    · rw [if_pos h, if_pos h, mul_one]
    · rw [if_neg h, if_neg h, mul_zero]
  rw [Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => hrewrite α β,
    sum_orderedReplicaPair_eq weight r (fun p q => if p ≠ q then 1 else 0)]
  have hinner : ∀ p ∈ Finset.univ.piAntidiag r,
      (∑ q ∈ Finset.univ.piAntidiag r, fidelityReplicaMultiplicityAmplitude weight p *
          (fidelityReplicaMultiplicityAmplitude weight q * (if p ≠ q then 1 else 0)))
        = fidelityReplicaMultiplicityAmplitude weight p *
            (1 - fidelityReplicaMultiplicityAmplitude weight p) := by
    intro p hp
    have hsplit : ∀ q ∈ Finset.univ.piAntidiag r,
        fidelityReplicaMultiplicityAmplitude weight p *
            (fidelityReplicaMultiplicityAmplitude weight q * (if p ≠ q then 1 else 0)) =
          fidelityReplicaMultiplicityAmplitude weight p *
              fidelityReplicaMultiplicityAmplitude weight q -
            fidelityReplicaMultiplicityAmplitude weight p *
              (if q = p then fidelityReplicaMultiplicityAmplitude weight p else 0) := by
      intro q hq
      by_cases h : q = p
      · subst h
        rw [if_neg (by simp), if_pos rfl]
        ring
      · rw [if_pos (fun hc => h hc.symm), if_neg h]
        ring
    rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      replicaAmplitude_total_mass hw r, Finset.sum_ite_eq' (Finset.univ.piAntidiag r) p
        (fun _ => fidelityReplicaMultiplicityAmplitude weight p), if_pos hp]
    ring
  rw [Finset.sum_congr rfl hinner]
  have hexp : ∀ p ∈ Finset.univ.piAntidiag r,
      fidelityReplicaMultiplicityAmplitude weight p *
          (1 - fidelityReplicaMultiplicityAmplitude weight p) =
        fidelityReplicaMultiplicityAmplitude weight p -
          fidelityReplicaMultiplicityAmplitude weight p ^ 2 := fun p _ => by ring
  rw [Finset.sum_congr rfl hexp, Finset.sum_sub_distrib, replicaAmplitude_total_mass hw r]



/-! ## The pushforward over an arbitrary commutative semiring -/

theorem orderedReplicaMultiplicity_mem_piAntidiag {r : ℕ} (α : Fin r → I) :
    orderedReplicaMultiplicity α ∈ Finset.univ.piAntidiag r := by
  classical
  rw [Finset.mem_piAntidiag]
  refine ⟨?_, fun i _ => Finset.mem_univ i⟩
  have hcard := Finset.card_eq_sum_card_fiberwise
    (f := α) (s := (Finset.univ : Finset (Fin r))) (t := (Finset.univ : Finset I))
    (fun x _ => Finset.mem_univ (α x))
  rw [Finset.card_univ, Fintype.card_fin] at hcard
  exact hcard.symm

/-- The number of ordered replica histories with a given multiplicity vector is the multinomial
coefficient. -/
theorem card_fiber_orderedReplicaMultiplicity {r : ℕ} {p : I → ℕ}
    (hp : p ∈ Finset.univ.piAntidiag r) :
    (Finset.univ.filter fun α : Fin r → I => orderedReplicaMultiplicity α = p).card
      = Nat.multinomial Finset.univ p := by
  classical
  have hpush := sum_orderedReplica_eq_replicaAmplitudeMoment (fun _ : I => (1 : ℝ)) r
    (fun q => if q = p then 1 else 0)
  have hlhs : (∑ α : Fin r → I, orderedReplicaWeight (fun _ : I => (1 : ℝ)) α *
      (if orderedReplicaMultiplicity α = p then 1 else 0)) =
      ((Finset.univ.filter fun α : Fin r → I => orderedReplicaMultiplicity α = p).card : ℝ) := by
    rw [Finset.card_filter]
    push_cast
    exact Finset.sum_congr rfl fun α _ => by
      rw [orderedReplicaWeight]
      simp
  have hrhs : replicaAmplitudeMoment (fun _ : I => (1 : ℝ)) r (fun q => if q = p then 1 else 0)
      = (Nat.multinomial Finset.univ p : ℝ) := by
    rw [replicaAmplitudeMoment,
      Finset.sum_congr rfl (fun q _ => (mul_ite _ _ _ _).trans (by rw [mul_one, mul_zero])),
      Finset.sum_ite_eq' (Finset.univ.piAntidiag r) p
        (fidelityReplicaMultiplicityAmplitude (fun _ : I => (1 : ℝ))), if_pos hp,
      fidelityReplicaMultiplicityAmplitude]
    simp
  rw [hlhs, hrhs] at hpush
  exact_mod_cast hpush

/-- **Theorem C over an arbitrary commutative semiring.**  Every ordered replica sum is the
multinomial-amplitude sum over multiplicity vectors. -/
theorem sum_orderedReplicaProduct_pushforward {R : Type*} [CommSemiring R] (w : I → R) (r : ℕ)
    (Φ : (I → ℕ) → R) :
    ∑ α : Fin r → I, orderedReplicaProduct w α * Φ (orderedReplicaMultiplicity α)
      = ∑ p ∈ Finset.univ.piAntidiag r,
          (Nat.multinomial Finset.univ p : R) * (∏ j, w j ^ p j) * Φ p := by
  classical
  have hfib := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (Fin r → I))) (t := Finset.univ.piAntidiag r)
    (g := fun α : Fin r → I => orderedReplicaMultiplicity α)
    (f := fun α : Fin r → I => orderedReplicaProduct w α * Φ (orderedReplicaMultiplicity α))
    (fun α _ => orderedReplicaMultiplicity_mem_piAntidiag α)
  rw [← hfib]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hterm : ∀ α ∈ Finset.univ.filter fun α : Fin r → I => orderedReplicaMultiplicity α = p,
      orderedReplicaProduct w α * Φ (orderedReplicaMultiplicity α) = (∏ j, w j ^ p j) * Φ p := by
    intro α hα
    rw [Finset.mem_filter] at hα
    rw [orderedReplicaProduct_eq_prod_pow, hα.2]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, card_fiber_orderedReplicaMultiplicity hp,
    nsmul_eq_mul, mul_assoc]

/-- **Theorem D, equation (30): the return sector of the replica pair lift.**  The forward–backward
pair mass carried by coincident multiplicity vectors is the sum of the squared moduli of the
multinomial amplitudes. -/
theorem sum_orderedReplicaPair_return (g : I → ℂ) (r : ℕ) :
    (∑ α : Fin r → I, ∑ β : Fin r → I,
        if orderedReplicaMultiplicity α = orderedReplicaMultiplicity β then
          orderedReplicaProduct g α * (starRingEnd ℂ) (orderedReplicaProduct g β) else 0)
      = ∑ p ∈ Finset.univ.piAntidiag r,
          ((Complex.normSq ((Nat.multinomial Finset.univ p : ℂ) * ∏ j, g j ^ p j) : ℝ) : ℂ) := by
  classical
  have hconjprod : ∀ β : Fin r → I,
      orderedReplicaProduct (fun j => (starRingEnd ℂ) (g j)) β =
        (starRingEnd ℂ) (orderedReplicaProduct g β) := by
    intro β
    rw [orderedReplicaProduct, orderedReplicaProduct, map_prod]
  have hinner : ∀ α : Fin r → I,
      (∑ β : Fin r → I,
          if orderedReplicaMultiplicity α = orderedReplicaMultiplicity β then
            orderedReplicaProduct g α * (starRingEnd ℂ) (orderedReplicaProduct g β) else 0)
        = orderedReplicaProduct g α *
            ((Nat.multinomial Finset.univ (orderedReplicaMultiplicity α) : ℂ) *
              ∏ j, (starRingEnd ℂ) (g j) ^ orderedReplicaMultiplicity α j) := by
    intro α
    have hstep : (∑ β : Fin r → I,
        orderedReplicaProduct (fun j => (starRingEnd ℂ) (g j)) β *
          (if orderedReplicaMultiplicity α = orderedReplicaMultiplicity β then 1 else 0))
        = ∑ q ∈ Finset.univ.piAntidiag r,
            (Nat.multinomial Finset.univ q : ℂ) * (∏ j, (starRingEnd ℂ) (g j) ^ q j) *
              (if orderedReplicaMultiplicity α = q then 1 else 0) :=
      sum_orderedReplicaProduct_pushforward (fun j => (starRingEnd ℂ) (g j)) r
        (fun q => if orderedReplicaMultiplicity α = q then 1 else 0)
    have hcollapse : (∑ q ∈ Finset.univ.piAntidiag r,
        (Nat.multinomial Finset.univ q : ℂ) * (∏ j, (starRingEnd ℂ) (g j) ^ q j) *
          (if orderedReplicaMultiplicity α = q then 1 else 0))
        = (Nat.multinomial Finset.univ (orderedReplicaMultiplicity α) : ℂ) *
            ∏ j, (starRingEnd ℂ) (g j) ^ orderedReplicaMultiplicity α j := by
      rw [Finset.sum_congr rfl (fun q _ => (mul_ite _ _ _ _).trans (by rw [mul_one, mul_zero])),
        Finset.sum_ite_eq (Finset.univ.piAntidiag r) (orderedReplicaMultiplicity α)
          (fun q => (Nat.multinomial Finset.univ q : ℂ) * ∏ j, (starRingEnd ℂ) (g j) ^ q j),
        if_pos (orderedReplicaMultiplicity_mem_piAntidiag α)]
    rw [← hcollapse, ← hstep, Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    by_cases h : orderedReplicaMultiplicity α = orderedReplicaMultiplicity β
    · rw [if_pos h, hconjprod, if_pos h, mul_one]
    · rw [if_neg h, hconjprod, if_neg h, mul_zero, mul_zero]
  rw [Finset.sum_congr rfl fun α _ => hinner α,
    sum_orderedReplicaProduct_pushforward g r
      (fun p => (Nat.multinomial Finset.univ p : ℂ) * ∏ j, (starRingEnd ℂ) (g j) ^ p j)]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hA : (starRingEnd ℂ) ((Nat.multinomial Finset.univ p : ℂ) * ∏ j, g j ^ p j) =
      (Nat.multinomial Finset.univ p : ℂ) * ∏ j, (starRingEnd ℂ) (g j) ^ p j := by
    rw [map_mul, map_prod, map_natCast]
    exact congrArg _ (Finset.prod_congr rfl fun j _ => map_pow _ _ _)
  rw [← hA, Complex.mul_conj]

end GaloisForLFunctions.HTGeometry
